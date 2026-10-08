"""Finite exact checks of the corrected Bernstein construction.

This is a mathematical consistency check, not a sampler benchmark or proof.
"""

import json
import random
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path


def evaluate(coefficients, x, derivative=0):
    return sum(
        c * F(factorial(i), factorial(i - derivative)) * x ** (i - derivative)
        for i, c in enumerate(coefficients)
        if i >= derivative
    )


def derivative_bound(coefficients, derivative):
    return sum(
        abs(c) * F(factorial(i), factorial(i - derivative))
        for i, c in enumerate(coefficients)
        if i >= derivative
    )


def hypergeom(m, k):
    return [
        (j, F(comb(m, j) * comb(m, k - j), comb(2 * m, k)))
        for j in range(max(0, k - m), min(m, k) + 1)
    ]


def g(coefficients, m, x):
    return evaluate(coefficients, x) - x * (1 - x) * evaluate(coefficients, x, 2) / (2 * m)


def difference(coefficients, m, k):
    return g(coefficients, 2 * m, F(k, 2 * m)) - sum(
        probability * g(coefficients, m, F(j, m)) for j, probability in hypergeom(m, k)
    )


def bernstein(values, p):
    m = len(values) - 1
    return sum(F(comb(m, j)) * p**j * (1 - p) ** (m - j) * v for j, v in enumerate(values))


def main():
    rng = random.Random(20261008)
    counts = {
        "hypergeometric_moment_cases": 0,
        "outward_ratio_checks": 0,
        "coefficient_bounds": 0,
        "elevation_identities": 0,
        "mass_bounds": 0,
        "quotient_constants": 0,
    }
    for m in range(1, 25):
        for k in range(2 * m + 1):
            distribution = hypergeom(m, k)
            p = F(k, 2 * m)
            assert sum(prob for _, prob in distribution) == 1
            moments = [
                sum(prob * (F(j, m) - p) ** r for j, prob in distribution) for r in range(1, 5)
            ]
            assert moments[0] == moments[2] == 0
            assert moments[1] == p * (1 - p) / (2 * m - 1)
            assert moments[3] <= F(1, m * m)
            counts["hypergeometric_moment_cases"] += 1
            mode = k // 2
            weights = dict(distribution)
            for j, prob in distribution:
                if j >= mode and j + 1 in weights:
                    ratio = F((m - j) * (k - j), (j + 1) * (m - k + j + 1))
                    assert weights[j + 1] / prob == ratio <= 1
                    counts["outward_ratio_checks"] += 1
                if j <= mode and j - 1 in weights:
                    assert weights[j - 1] / prob <= 1
                    counts["outward_ratio_checks"] += 1

    for case in range(40):
        coefficients = [F(rng.randint(-4, 4), 100) for _ in range(rng.randint(2, 7))]
        assert sum(map(abs, coefficients)) < F(4, 5)
        m2, m3, m4 = [derivative_bound(coefficients, r) for r in (2, 3, 4)]
        a = m2 + m3 + m4
        m0 = 1
        while m0 < 2 * m2 or m0 * m0 < 4 * a:
            m0 *= 2
        assert F(4, 5) + m2 / (8 * m0) < F(7, 8)
        assert a / (3 * m0 * m0) <= F(1, 12)
        counts["mass_bounds"] += 1
        for m in range(1, 10):
            ds = [difference(coefficients, m, k) for k in range(2 * m + 1)]
            for d in ds:
                assert abs(d) <= a / (4 * m * m)
                counts["coefficient_bounds"] += 1
            if m <= 4:
                for p in (F(0), F(1, 3), F(1, 2), F(2, 3), F(1)):
                    lhs = bernstein(
                        [g(coefficients, 2 * m, F(k, 2 * m)) for k in range(2 * m + 1)], p
                    )
                    lhs -= bernstein([g(coefficients, m, F(k, m)) for k in range(m + 1)], p)
                    assert lhs == bernstein(ds, p)
                    counts["elevation_identities"] += 1

    constants = [1]
    for k in range(1, 5):
        constants.append(1 + sum(comb(k, j) * constants[k - j] for j in range(1, k + 1)))
        counts["quotient_constants"] += 1
    assert constants == [1, 2, 6, 26, 150]
    result = {
        "status": "all finite exact checks passed",
        "seed": 20261008,
        "arithmetic": "fractions.Fraction, no floating point",
        "counts": counts,
        "limitations": "finite identities and bounds, not a sampler benchmark or proof",
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
