#!/usr/bin/env python3
"""Finite exact-rational checks, not a proof or formal verification.

This script reproduces algebra checks for the bounded-column-envelope
sampler.  It uses only Python's standard library and fractions.Fraction.
It does not simulate the full neural sampler, establish any complexity
bound, or replace the mathematical proof.
"""

from __future__ import annotations

import argparse
import json
import random
from fractions import Fraction as F
from functools import cache
from itertools import combinations, product
from pathlib import Path


def mean(rows):
    return tuple(sum(row[i] for row in rows) / len(rows) for i in range(len(rows[0])))


def subtract(a, b):
    return tuple(x - y for x, y in zip(a, b))


def covariance(rows):
    z = mean(rows)
    r = len(z)
    return tuple(
        tuple(
            sum((row[i] - z[i]) * (row[j] - z[j]) for row in rows) / (len(rows) - 1)
            for j in range(r)
        )
        for i in range(r)
    )


def contract(a, b):
    return sum(a[i][j] * b[i][j] for i in range(len(a)) for j in range(len(a)))


def pair_covariance(rows):
    r = len(rows[0])
    pairs = list(combinations(rows, 2))
    return tuple(
        tuple(
            sum((a[i] - b[i]) * (a[j] - b[j]) for a, b in pairs) / (2 * len(pairs))
            for j in range(r)
        )
        for i in range(r)
    )


def make_polynomial(r, rng):
    coefficients = {
        powers: F(rng.randint(-7, 7), 8)
        for powers in product(range(6), repeat=r)
        if sum(powers) <= 5
    }

    @cache
    def derivative(x, indices=()):
        total = F(0)
        for powers, coefficient in coefficients.items():
            remaining = list(powers)
            scalar = coefficient
            for i in indices:
                scalar *= remaining[i]
                remaining[i] -= 1
                if not scalar:
                    break
            if not scalar:
                continue
            for i in range(r):
                scalar *= x[i] ** remaining[i]
            total += scalar
        return total

    def hessian(x):
        return tuple(tuple(derivative(x, (i, j)) for j in range(r)) for i in range(r))

    def third(x):
        return tuple(
            tuple(tuple(derivative(x, (i, j, k)) for k in range(r)) for j in range(r))
            for i in range(r)
        )

    return derivative, hessian, third


def check_empirical_identity():
    rng = random.Random(20261008)
    populations = 0
    pair_identities = 0
    centered_third_identities = 0
    for r in (1, 2, 3):
        for m in (2, 3, 4):
            for _ in range(3):
                rows = tuple(
                    tuple(F(rng.randint(-4, 4), 4) for _ in range(r)) for _ in range(2 * m)
                )
                function, hessian, third = make_polynomial(r, rng)
                z = mean(rows)
                V = covariance(rows)
                H = hessian(z)
                T = third(z)
                G_full = function(z) - contract(V, H) / (4 * m)
                half_values = []
                remainders = []
                covariance_delta = [[[F(0) for _ in range(r)] for _ in range(r)] for _ in range(r)]
                splits = list(combinations(range(2 * m), m))
                for selected in splits:
                    selected_set = set(selected)
                    A = tuple(rows[i] for i in selected)
                    B = tuple(rows[i] for i in range(2 * m) if i not in selected_set)
                    za, zb = mean(A), mean(B)
                    VA, VB = covariance(A), covariance(B)
                    assert VA == pair_covariance(A)
                    assert VB == pair_covariance(B)
                    pair_identities += 2
                    delta = subtract(za, z)
                    assert subtract(z, zb) == delta
                    HA, HB = hessian(za), hessian(zb)
                    Tdelta = tuple(
                        tuple(sum(T[i][j][k] * delta[k] for k in range(r)) for j in range(r))
                        for i in range(r)
                    )
                    Hdelta2 = sum(H[i][j] * delta[i] * delta[j] for i in range(r) for j in range(r))
                    R4 = (function(za) + function(zb)) / 2 - function(z) - Hdelta2 / 2
                    plus = tuple(
                        tuple(HA[i][j] - H[i][j] - Tdelta[i][j] for j in range(r)) for i in range(r)
                    )
                    minus = tuple(
                        tuple(HB[i][j] - H[i][j] + Tdelta[i][j] for j in range(r)) for i in range(r)
                    )
                    RH = (contract(VA, plus) + contract(VB, minus)) / 2
                    half_values.append(function(za) - contract(VA, HA) / (2 * m))
                    remainders.append(RH / (2 * m) - R4)
                    for i, j, k in product(range(r), repeat=3):
                        covariance_delta[i][j][k] += VA[i][j] * delta[k]
                centered = tuple(subtract(row, z) for row in rows)
                cubic_numerator = F(0)
                for i, j, k in product(range(r), repeat=3):
                    moment = sum(v[i] * v[j] * v[k] for v in centered)
                    cubic_numerator += T[i][j][k] * moment
                    assert covariance_delta[i][j][k] / len(splits) == moment / (
                        2 * (m - 1) * (2 * m - 1)
                    )
                    centered_third_identities += 1
                c3 = cubic_numerator / (4 * m * (m - 1) * (2 * m - 1))
                assert G_full - sum(half_values) / len(splits) == c3 + sum(remainders) / len(splits)
                populations += 1
    return {
        "rational_populations": populations,
        "full_antithetic_identities": populations,
        "within_half_pair_covariance_identities": pair_identities,
        "centered_covariance_third_moment_entries": centered_third_identities,
        "dimensions": [1, 2, 3],
        "half_sample_sizes": [2, 3, 4],
        "maximum_polynomial_degree": 5,
        "maximum_exact_residual": "0",
    }


def conditional_moment(s, remaining, order):
    v = sum((d**2 for d in remaining), F(0))
    if order == 2:
        return s**2 + v
    u = sum((d**4 for d in remaining), F(0))
    return s**4 + 6 * s**2 * v + 3 * v**2 - 2 * u


def doob_probability(increments, signs, order):
    value = F(1)
    s = F(0)
    for j, (d, sign) in enumerate(zip(increments, signs)):
        parent = conditional_moment(s, increments[j:], order)
        if parent == 0:
            return F(0)
        plus = conditional_moment(s + d, increments[j + 1 :], order)
        minus = conditional_moment(s - d, increments[j + 1 :], order)
        assert plus >= 0 and minus >= 0
        assert plus + minus == 2 * parent
        numerator = plus if sign == 1 else minus
        value *= numerator / (2 * parent)
        s += sign * d
    return value


def check_doob_tilts():
    rng = random.Random(20261009)
    laws = 0
    endpoints = 0
    for m in range(2, 7):
        for _ in range(9):
            increments = tuple(F(rng.choice((-1, 1)) * rng.randint(1, 4), 4 * m) for _ in range(m))
            for order in (2, 4):
                normalizer = conditional_moment(F(0), increments, order)
                assert normalizer > 0
                accept = m * normalizer if order == 2 else F(m * m, 3) * normalizer
                assert 0 <= accept <= 1
                total = F(0)
                for signs in product((-1, 1), repeat=m):
                    delta = sum(sign * d for sign, d in zip(signs, increments))
                    probability = doob_probability(increments, signs, order)
                    target = delta**order / (2**m * normalizer)
                    assert probability == target
                    expected_accepted = (
                        F(m, 2**m) * delta**2 if order == 2 else F(m * m, 3 * 2**m) * delta**4
                    )
                    assert accept * probability == expected_accepted
                    total += probability
                    endpoints += 1
                assert total == 1
                laws += 1
    return {
        "nondegenerate_exact_tilt_laws": laws,
        "enumerated_signed_endpoints": endpoints,
        "orders": [2, 4],
        "sign_counts": [2, 3, 4, 5, 6],
        "all_distributions_sum_to": "1",
        "maximum_exact_residual": "0",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = {
        "status": "FINITE EXACT CHECKS; NOT A PROOF OR FORMAL VERIFICATION",
        "arithmetic": "Python fractions.Fraction; no floating-point arithmetic",
        "empirical_correction": check_empirical_identity(),
        "doob_tilts": check_doob_tilts(),
        "limitations": [
            "No full-network sampling run is performed.",
            "These finite examples do not establish the derivative majorants.",
            "These finite examples do not establish a stopping or complexity bound.",
            "The manuscript's complete mathematical proof justifies the theorem.",
        ],
    }
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
