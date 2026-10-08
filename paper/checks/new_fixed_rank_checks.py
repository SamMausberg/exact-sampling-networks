"""Finite exact checks of the elementary cylindrical arrangement index.

These checks support the manuscript audit. They are not a proof, and do
not benchmark a sampler. All geometry uses fractions.Fraction exactly.
"""

import json
import random
from bisect import bisect_right
from fractions import Fraction as F
from itertools import product
from pathlib import Path


def value(form, point):
    return form[0] + sum(a * x for a, x in zip(form[1:], point))


def canonical(forms):
    answer = set()
    for form in forms:
        form = tuple(map(F, form))
        if not any(form[1:]):
            continue
        pivot = next(x for x in form if x)
        answer.add(tuple(x / pivot for x in form))
    return sorted(answer)


class Arrangement:
    def __init__(self, dimension, forms):
        self.dimension = dimension
        self.forms = canonical(forms)
        if dimension == 1:
            self.zeros = sorted(set(-f[0] / f[1] for f in self.forms))
            if not self.zeros:
                self.reps = [(F(0),)]
            else:
                self.reps = [(self.zeros[0] - 1,)]
                self.reps += [((a + b) / 2,) for a, b in zip(self.zeros, self.zeros[1:])]
                self.reps += [(self.zeros[-1] + 1,)]
            return
        vertical = [f[:-1] for f in self.forms if not f[-1]]
        self.thresholds = sorted(
            set(tuple(-a / f[-1] for a in f[:-1]) for f in self.forms if f[-1])
        )
        differences = [
            tuple(a - b for a, b in zip(f, g))
            for i, f in enumerate(self.thresholds)
            for g in self.thresholds[:i]
        ]
        self.child = Arrangement(dimension - 1, vertical + differences)
        self.orders = []
        self.reps = []
        self.lift = []
        for rep in self.child.reps:
            order = sorted(
                range(len(self.thresholds)), key=lambda i: value(self.thresholds[i], rep)
            )
            self.orders.append(order)
            vals = [value(self.thresholds[i], rep) for i in order]
            assert all(a < b for a, b in zip(vals, vals[1:]))
            if not vals:
                ys = [F(0)]
            else:
                ys = [vals[0] - 1]
                ys += [(a + b) / 2 for a, b in zip(vals, vals[1:])]
                ys += [vals[-1] + 1]
            self.lift.append(list(range(len(self.reps), len(self.reps) + len(ys))))
            self.reps += [rep + (y,) for y in ys]

    def locate(self, point):
        if self.dimension == 1:
            return bisect_right(self.zeros, point[0])
        child_id = self.child.locate(point[:-1])
        vals = [value(self.thresholds[i], point[:-1]) for i in self.orders[child_id]]
        assert all(a <= b for a, b in zip(vals, vals[1:]))
        gap = bisect_right(vals, point[-1])
        return self.lift[child_id][gap]


def main():
    rng = random.Random(20261008)
    counts = {
        "arrangements": 0,
        "stored_representatives": 0,
        "strict_sign_checks": 0,
        "query_sign_checks": 0,
        "stored_key_order_checks": 0,
        "count_bound_checks": 0,
    }
    for dimension in (1, 2, 3):
        for case in range(30):
            forms = [
                tuple(F(rng.randint(-2, 2)) for _ in range(dimension + 1))
                for _ in range(rng.randrange(0, 7))
            ]
            # Include coincident forms, reversed orientations, and empty forms.
            if forms:
                forms += [forms[0], tuple(-2 * x for x in forms[0])]
            forms += [tuple([F(1)] + [F(0)] * dimension)]
            arrangement = Arrangement(dimension, forms)
            counts["arrangements"] += 1
            counts["stored_representatives"] += len(arrangement.reps)
            h = len(arrangement.forms)
            assert len(arrangement.reps) <= (h + 1) ** (2**dimension - 1)
            counts["count_bound_checks"] += 1
            for rep in arrangement.reps:
                for form in arrangement.forms:
                    assert value(form, rep) != 0
                    counts["strict_sign_checks"] += 1
            points = list(product((F(-1), F(0), F(1)), repeat=dimension))
            points += [
                tuple(F(rng.randint(-8, 8), rng.randint(1, 5)) for _ in range(dimension))
                for _ in range(30)
            ]
            # Add actual threshold intersections and points on input hyperplanes.
            for form in arrangement.forms:
                point = [F(0)] * dimension
                pivot = next(i for i, x in enumerate(form[1:]) if x)
                point[pivot] = -form[0] / form[pivot + 1]
                points.append(tuple(point))
            for point in points:
                rep = arrangement.reps[arrangement.locate(point)]
                for form in arrangement.forms:
                    assert value(form, rep) * value(form, point) >= 0
                    counts["query_sign_checks"] += 1

        # Check the actual homogeneous score arrangement and stored permutations.
        for case in range(20):
            keys = [tuple(F(rng.randint(-3, 3)) for _ in range(dimension)) for _ in range(5)]
            forms = [
                tuple([F(0)] + [a - b for a, b in zip(k, ell)])
                for i, k in enumerate(keys)
                for ell in keys[:i]
            ]
            arrangement = Arrangement(dimension, forms)
            orders = [
                sorted(
                    range(len(keys)),
                    key=lambda j: sum(a * b for a, b in zip(keys[j], rep)),
                    reverse=True,
                )
                for rep in arrangement.reps
            ]
            for point in product((F(-1), F(0), F(1)), repeat=dimension):
                order = orders[arrangement.locate(point)]
                vals = [sum(a * b for a, b in zip(keys[j], point)) for j in order]
                assert all(a >= b for a, b in zip(vals, vals[1:]))
                counts["stored_key_order_checks"] += 1
    result = {
        "status": "all finite exact checks passed",
        "arithmetic": "fractions.Fraction, no floating point",
        "seed": 20261008,
        "counts": counts,
        "scope": "dimensions 1, 2, 3; degeneracies and boundary queries included",
        "limitations": "finite checks are not a proof or a sampler benchmark",
    }
    path = Path(__file__).with_suffix(".json")
    path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
