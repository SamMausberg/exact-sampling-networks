"""Exact rational rank-three identities. Checks only, not a formal proof."""

import json
from fractions import Fraction as F
from itertools import product
from math import comb, factorial
from pathlib import Path

RANK = 3


def add(p, q):
    r = dict(p)
    for key, val in q.items():
        r[key] = r.get(key, F(0)) + val
    return {key: val for key, val in r.items() if val}


def scale(p, a):
    return {key: a * val for key, val in p.items() if a * val}


def derivative(p, axis):
    result = {}
    for key, val in p.items():
        if key[axis]:
            new = list(key)
            new[axis] -= 1
            result[tuple(new)] = val * key[axis]
    return result


def shift(p, axis, power):
    result = {}
    for key, val in p.items():
        new = list(key)
        new[axis] += power
        result[tuple(new)] = val
    return result


def op_a(p, axis):
    d = derivative(derivative(p, axis), axis)
    return scale(add(shift(d, axis, 1), scale(shift(d, axis, 2), -1)), F(1, 2))


def correct(p, axis, m):
    return add(p, scale(op_a(p, axis), -F(1, m)))


def evaluate(p, point):
    result = F(0)
    for key, val in p.items():
        term = val
        for x, power in zip(point, key):
            term *= x**power
        result += term
    return result


def weights(m, p):
    return [F(comb(m, k)) * p**k * (1 - p) ** (m - k) for k in range(m + 1)]


def corrected_tensor(p, m, point):
    g = p
    for axis in range(RANK):
        g = correct(g, axis, m)
    ws = [weights(m, x) for x in point]
    result = F(0)
    for totals in product(range(m + 1), repeat=RANK):
        prob = F(1)
        for axis, k in enumerate(totals):
            prob *= ws[axis][k]
        result += prob * evaluate(g, [F(k, m) for k in totals])
    return result


def scalar_coefficient(g, axis, m, total, empirical):
    fine = correct(g, axis, 2 * m)
    coarse = correct(g, axis, m)
    point = list(empirical)
    point[axis] = F(total, 2 * m)
    result = evaluate(fine, point)
    den = comb(2 * m, total)
    for j in range(max(0, total - m), min(m, total) + 1):
        point[axis] = F(j, m)
        result -= F(comb(m, j) * comb(m, total - j), den) * evaluate(coarse, point)
    return result


def correction(p, axis, m, point, abar):
    ds = [m if i < axis else 2 * m for i in range(RANK)]
    g = p
    for i in range(RANK):
        if i != axis:
            g = correct(g, i, ds[i])
    ws = [weights(ds[i], point[i]) for i in range(RANK)]
    result = F(0)
    count = 0
    worst = F(0)
    for totals in product(*[range(d + 1) for d in ds]):
        empirical = [F(totals[i], ds[i]) for i in range(RANK)]
        d = scalar_coefficient(g, axis, m, totals[axis], empirical)
        assert abs(d) <= abar / (4 * m * m), (p, axis, m, totals, d, abar)
        if abar:
            worst = max(worst, abs(d) * 4 * m * m / abar)
        prob = F(1)
        for i, k in enumerate(totals):
            prob *= ws[i][k]
        result += prob * d
        count += 1
    return result, count, worst


def derivative_bound(p, k):
    return sum(
        (
            abs(v) * F(factorial(sum(key)), factorial(sum(key) - k))
            for key, v in p.items()
            if sum(key) >= k
        ),
        F(0),
    )


def matrix_product(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(2)) for j in range(2)] for i in range(2)]


def seven_product(a, b):
    a11, a12, a21, a22 = a[0][0], a[0][1], a[1][0], a[1][1]
    b11, b12, b21, b22 = b[0][0], b[0][1], b[1][0], b[1][1]
    q1 = (a11 + a22) * (b11 + b22)
    q2 = (a21 + a22) * b11
    q3 = a11 * (b12 - b22)
    q4 = a22 * (b21 - b11)
    q5 = (a11 + a12) * b22
    q6 = (a21 - a11) * (b11 + b12)
    q7 = (a12 - a22) * (b21 + b22)
    return [[q1 + q4 - q5 + q7, q3 + q5], [q2 + q4, q1 - q2 + q3 + q6]]


def main():
    polynomials = [
        {(0, 0, 0): F(1, 2)},
        {(1, 0, 0): F(1, 2)},
        {(2, 0, 0): F(1, 2)},
        {(2, 2, 0): F(-1, 2)},
        {(2, 2, 2): F(1, 2)},
        {(3, 2, 1): F(-1, 2)},
        {(4, 2, 2): F(1, 2)},
        {(0, 0, 0): F(1, 8), (1, 1, 1): F(-1, 8), (2, 2, 2): F(1, 16)},
    ]
    identities = 0
    coefficients = 0
    worst = F(0)
    for p in polynomials:
        ms = {k: derivative_bound(p, k) for k in range(2, 9)}
        for m in [2, 3]:
            abar = sum(
                (sum((ms[k + 2 * l] for k in [2, 3, 4]), F(0)) / ((8 * m) ** l) for l in range(3)),
                F(0),
            )
            for point in [(F(1, 3), F(2, 5), F(3, 7)), (F(0), F(1), F(1, 2))]:
                lhs = corrected_tensor(p, 2 * m, point) - corrected_tensor(p, m, point)
                rhs = F(0)
                for axis in range(3):
                    value, count, ratio = correction(p, axis, m, point, abar)
                    rhs += value
                    coefficients += count
                    worst = max(worst, ratio)
                assert lhs == rhs, (p, m, point, lhs - rhs)
                identities += 1
    strassen_cases = 0
    for entries_a in product([-1, 0, 1], repeat=4):
        a = [list(entries_a[:2]), list(entries_a[2:])]
        for entries_b in product([-1, 0, 1], repeat=4):
            b = [list(entries_b[:2]), list(entries_b[2:])]
            assert seven_product(a, b) == matrix_product(a, b)
            strassen_cases += 1
    result = {
        "status": "all exact-rational checks passed; not a formal verification",
        "rank_three_operator_identity_cases": identities,
        "rank_three_coefficient_bound_cases": coefficients,
        "seven_product_identity_cases": strassen_cases,
        "largest_coefficient_bound_ratio": str(worst),
        "uses_floating_point": False,
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
