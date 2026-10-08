"""Exact rational recurrence checks and 120-digit bound checks."""

import json
from fractions import Fraction as F
from pathlib import Path

import mpmath as mp

mp.mp.dps = 120


def real(x):
    return mp.mpf(x.numerator) / x.denominator


count = 0
for depth in range(1, 21):
    for seed in range(20):
        U = [F((seed + 3 * j) % 11, 2 ** (j % 4)) for j in range(depth)]
        m = [F((3 * seed + j) % 17, 4) for j in range(depth)]
        L = [F((seed + 7 * j) % 13, 3) for j in range(depth)]
        R = P = F(1)
        majorant = F(2)
        closed = F(2)
        old_terms = []
        for j in range(depth):
            Rold = R
            R += U[j]
            majorant = (1 + U[j] * m[j] / Rold) * majorant + U[j] * (1 + L[j])
            P *= 1 + U[j] * m[j] / Rold
            closed += U[j] * (1 + L[j]) / P
            assert majorant == P * closed
            count += 1
        M = max(F(1), max(m))
        A = max(L)
        bound = (2 + real(A)) * (1 + mp.log(real(R))) * real(R) ** (real(M) - 1)
        assert real(majorant / R) <= bound + mp.mpf("1e-105")
        count += 1
result = dict(
    all_checks_passed=True,
    total_cases=count,
    precision_decimal_digits=120,
    status="exact rational identities and deterministic numerical inequalities only",
)
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result))
