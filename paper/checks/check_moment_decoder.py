#!/usr/bin/env python3
"""Supplementary numerical and exact-integer checks, not a proof or benchmark.
Run: python check_moment_decoder.py
The paper establishes certification and exact sampling; this script checks the
moment identity, analytic truncation estimate, and background replay schedule.
"""

import json
import math
import random
from fractions import Fraction as F
from pathlib import Path

import mpmath as mp

mp.mp.dps = 120
rng = random.Random(20261008)


def mm(x):
    return mp.mpf(x.numerator) / x.denominator if isinstance(x, F) else mp.mpf(x)


def indices(r, m):
    if r == 1:
        return [(j,) for j in range(m + 1)]
    return [(i, j) for i in range(m + 1) for j in range(m + 1 - i)]


A = [
    [F(1), F(0)],
    [F(0), F(1)],
    [F(1, 2), F(1, 2)],
    [F(-1, 2), F(1)],
    [F(1), F(-1)],
    [F(1, 4), F(-1, 2)],
]
n = len(A)
records = []
for t in range(1, 129):
    zz = [rng.randrange(-4, 5), rng.randrange(-4, 5)]
    vv = [rng.randrange(-8, 9) for _ in range(3)]
    records.append((zz, vv))
checks = 0
max_identity = mp.mpf(0)
max_trunc_ratio = mp.mpf(0)
min_poly_mass = mp.inf
for m in (8, 16, 32):
    nus = indices(2, m)
    S = [0] * len(nus)
    M = [[0] * len(nus) for _ in range(3)]
    for T, (zz, vv) in enumerate(records, 1):
        powers = [[pow(z, k) for k in range(m + 1)] for z in zz]
        for h, nu in enumerate(nus):
            mon = powers[0][nu[0]] * powers[1][nu[1]] * (1 << (3 * (m - sum(nu))))
            S[h] += mon
            for i in range(3):
                M[i][h] += mon * vv[i]
        if T not in (1, 2, 7, 32, 64, 128):
            continue
        for beta in (mp.mpf(1) / 2, mp.sqrt(n)):
            q = [F(rng.randrange(-8, 9), 8) for _ in range(n)]
            tt = [beta / n * sum(mm(q[i] * A[i][a]) for i in range(n)) for a in range(2)]
            H = sum(abs(t) for t in tt)
            coeff = [
                mp.fprod(tt[a] ** nu[a] / math.factorial(nu[a]) for a in range(2)) for nu in nus
            ]
            zm = sum(coeff[h] * S[h] for h in range(len(nus))) / mp.mpf(2) ** (3 * m)
            nm = [
                sum(coeff[h] * M[i][h] for h in range(len(nus))) / mp.mpf(2) ** (3 * m + 3)
                for i in range(3)
            ]
            ztrue = mp.mpf(0)
            ntrue = [mp.mpf(0)] * 3
            zpoly = mp.mpf(0)
            npoly = [mp.mpf(0)] * 3
            for zz0, vv0 in records[:T]:
                a = sum(tt[i] * mp.mpf(zz0[i]) / 8 for i in range(2))
                w = mp.exp(a)
                wpoly = sum(a**k / math.factorial(k) for k in range(m + 1))
                ztrue += w
                zpoly += wpoly
                for i in range(3):
                    ntrue[i] += w * mp.mpf(vv0[i]) / 8
                    npoly[i] += wpoly * mp.mpf(vv0[i]) / 8
            ident = max([abs(zm - zpoly)] + [abs(nm[i] - npoly[i]) for i in range(3)])
            max_identity = max(max_identity, ident)
            assert ident < mp.mpf("1e-105")
            tail = mp.exp(H) * H ** (m + 1) / math.factorial(m + 1)
            assert tail < mp.exp(-H) / 2
            bound = 4 * mp.exp(H) * tail
            for i in range(3):
                error = abs(nm[i] / zm - ntrue[i] / ztrue)
                assert error <= bound
                max_trunc_ratio = max(max_trunc_ratio, error / bound)
                checks += 1
            min_poly_mass = min(min_poly_mass, zm / T)

# Integer schedule only: future cache performs at most two token replays per step.
schedule_checks = []
for T0 in (0, 1, 3, 7, 31, 1000, 1023, 1000000):
    N = 1
    while N <= T0:
        N *= 2
    phase = N
    cursor = None
    switches = 0
    mx = 0
    # Inspect two completed rebuilds; large prefill has no immediate rebuild charge.
    stop = 4 * N
    for T in range(T0 + 1, stop + 1):
        if cursor is not None:
            todo = min(2, T - cursor)
            cursor += todo
            mx = max(mx, todo)
        if T == 2 * phase and cursor is not None:
            assert cursor == T
            switches += 1
            phase *= 2
            cursor = 0
        elif T == phase and cursor is None:
            cursor = 0
        assert cursor is None or 0 <= cursor <= T
    assert switches >= 1 and mx <= 2
    schedule_checks.append(
        {"prefill": T0, "initial_phase": N, "switches": switches, "max_replayed_per_append": mx}
    )

# Check the explicit geometric moment bound used for precision refinement.
geom = []
for k in range(13):
    for P in (1, 2, 17, 100):
        total = mp.fsum(mp.mpf(2) ** (-j) * (P + j) ** k for j in range(4096))
        bound = mp.mpf(2) ** (k + 1) * math.factorial(k) * P**k
        assert total <= bound * (1 + mp.mpf("1e-110"))
        geom.append((k, P))

out = {
    "status": "supplementary checks only; no exact sampler implementation or speed benchmark",
    "decimal_precision": mp.mp.dps,
    "moment_attention_coordinate_checks": checks,
    "maximum_moment_identity_error": mp.nstr(max_identity, 16),
    "maximum_observed_error_over_analytic_bound": mp.nstr(max_trunc_ratio, 16),
    "minimum_average_polynomial_kernel_mass": mp.nstr(min_poly_mass, 16),
    "background_replay_schedules": schedule_checks,
    "geometric_moment_checks": len(geom),
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
