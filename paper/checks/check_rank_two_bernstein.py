"""Exact rational checks only. These computations are not a proof."""

import json
from fractions import Fraction as F
from math import comb
from pathlib import Path


def add(p, q):
    r = dict(p)
    for k, v in q.items():
        r[k] = r.get(k, F(0)) + v
    return {k: v for k, v in r.items() if v}


def scale(p, a):
    return {k: a * v for k, v in p.items() if a * v}


def derivative(p, i, k=1):
    r = dict(p)
    for _ in range(k):
        s = {}
        for key, val in r.items():
            if key[i]:
                new = list(key)
                new[i] -= 1
                s[tuple(new)] = val * key[i]
        r = s
    return r


def multiply_variable(p, i, power):
    r = {}
    for key, val in p.items():
        new = list(key)
        new[i] += power
        r[tuple(new)] = val
    return r


def op_a(p, i):
    d = derivative(p, i, 2)
    return scale(add(multiply_variable(d, i, 1), scale(multiply_variable(d, i, 2), F(-1))), F(1, 2))


def correct(p, i, m):
    return add(p, scale(op_a(p, i), -F(1, m)))


def evaluate(p, x, y):
    return sum((v * x ** k[0] * y ** k[1] for k, v in p.items()), F(0))


def binomial_weights(m, p):
    return [F(comb(m, k)) * p**k * (1 - p) ** (m - k) for k in range(m + 1)]


def tensor_bernstein(p, m1, m2, x, y):
    a, b = binomial_weights(m1, x), binomial_weights(m2, y)
    return sum(
        (
            a[i] * b[j] * evaluate(p, F(i, m1), F(j, m2))
            for i in range(m1 + 1)
            for j in range(m2 + 1)
        ),
        F(0),
    )


def corrected_tensor(p, m, x, y):
    return tensor_bernstein(correct(correct(p, 0, m), 1, m), m, m, x, y)


def scalar_coefficient(p, axis, m, total, other):
    fine = correct(p, axis, 2 * m)
    coarse = correct(p, axis, m)
    loc = [F(total, 2 * m), other] if axis == 0 else [other, F(total, 2 * m)]
    value = evaluate(fine, *loc)
    denominator = comb(2 * m, total)
    average = F(0)
    for j in range(max(0, total - m), min(m, total) + 1):
        weight = F(comb(m, j) * comb(m, total - j), denominator)
        loc[axis] = F(j, m)
        average += weight * evaluate(coarse, *loc)
    return value - average


def expected_corrections(p, m, x, y):
    a, b = binomial_weights(2 * m, x), binomial_weights(2 * m, y)
    g1 = correct(p, 1, 2 * m)
    first = sum(
        (
            a[i] * b[j] * scalar_coefficient(g1, 0, m, i, F(j, 2 * m))
            for i in range(2 * m + 1)
            for j in range(2 * m + 1)
        ),
        F(0),
    )
    a = binomial_weights(m, x)
    g2 = correct(p, 0, m)
    second = sum(
        (
            a[i] * b[j] * scalar_coefficient(g2, 1, m, j, F(i, m))
            for i in range(m + 1)
            for j in range(2 * m + 1)
        ),
        F(0),
    )
    return first + second


def derivative_bound(p, k):
    return sum(
        (
            F(comb(k, j))
            * sum((abs(v) for v in derivative(derivative(p, 0, j), 1, k - j).values()), F(0))
            for j in range(k + 1)
        ),
        F(0),
    )


def main():
    polynomials = [
        {(i, j): F((-1) ** i, 2)}
        for i, j in [
            (0, 0),
            (1, 0),
            (0, 1),
            (2, 0),
            (0, 2),
            (1, 1),
            (2, 2),
            (3, 2),
            (2, 3),
            (4, 2),
            (3, 3),
            (2, 4),
        ]
    ]
    polynomials += [{(0, 0): F(1, 8), (1, 1): F(-1, 8), (2, 2): F(1, 16), (3, 3): F(-1, 32)}]
    identity_cases = 0
    coefficient_cases = 0
    worst_ratio = F(0)
    for p in polynomials:
        for m in [2, 3, 4]:
            for x, y in [(F(1, 3), F(2, 5)), (F(0), F(1)), (F(1, 2), F(1, 2))]:
                left = corrected_tensor(p, 2 * m, x, y) - corrected_tensor(p, m, x, y)
                right = expected_corrections(p, m, x, y)
                assert left == right, (p, m, x, y, left - right)
                identity_cases += 1
            bounds = {k: derivative_bound(p, k) for k in range(2, 7)}
            abar = sum((bounds[k] for k in [2, 3, 4]), F(0)) + sum(
                (bounds[k] for k in [4, 5, 6]), F(0)
            ) / (8 * m)
            for axis, other_degree in [(0, 2 * m), (1, m)]:
                g = correct(p, 1 - axis, other_degree)
                for total in range(2 * m + 1):
                    for k in range(other_degree + 1):
                        d = abs(scalar_coefficient(g, axis, m, total, F(k, other_degree)))
                        assert d <= abar / (4 * m * m), (p, m, axis, total, k, d, abar)
                        if abar:
                            worst_ratio = max(worst_ratio, d * 4 * m * m / abar)
                        coefficient_cases += 1

    moment_cases = 0
    for m in range(2, 31):
        for k in range(2 * m + 1):
            p = F(k, 2 * m)
            v = p * (1 - p)
            actual = sum(
                (
                    F(comb(m, j) * comb(m, k - j), comb(2 * m, k)) * (F(j, m) - p) ** 4
                    for j in range(max(0, k - m), min(m, k) + 1)
                ),
                F(0),
            )
            formula = v * (3 * v - F(1, m)) / ((2 * m - 1) * (2 * m - 3))
            assert actual == formula
            moment_cases += 1

    output = {
        "status": "all exact-rational checks passed; not a formal verification",
        "operator_identity_cases": identity_cases,
        "coefficient_bound_cases": coefficient_cases,
        "hypergeometric_fourth_moment_cases": moment_cases,
        "largest_coefficient_bound_ratio": str(worst_ratio),
        "uses_floating_point": False,
    }
    out = Path(__file__).with_suffix(".json")
    out.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
