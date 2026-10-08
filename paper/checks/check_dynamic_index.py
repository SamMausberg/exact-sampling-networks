#!/usr/bin/env python3
"""Deterministic supplementary checks for dynamic_index.md.

Exact rational arithmetic checks geometry, reconstruction, and insertion
invariants. High precision arithmetic checks displayed rejection masses.
These are checks, not a proof or an implementation benchmark.
"""

import json
import random
from fractions import Fraction as F
from itertools import combinations
from math import factorial
from pathlib import Path

import mpmath as mp

mp.mp.dps = 120
RNG = random.Random(81973421)
OUT = Path(__file__).with_name("dynamic_index_checks.json")


def dot(a, b):
    return sum((x * y for x, y in zip(a, b)), F(0))


def det(a):
    if not a:
        return F(1)
    z = [list(row) for row in a]
    ans = F(1)
    for i in range(len(z)):
        p = next((j for j in range(i, len(z)) if z[j][i]), None)
        if p is None:
            return F(0)
        if p != i:
            z[i], z[p] = z[p], z[i]
            ans = -ans
        t = z[i][i]
        ans *= t
        for j in range(i + 1, len(z)):
            c = z[j][i] / t
            for k in range(i + 1, len(z)):
                z[j][k] -= c * z[i][k]
    return ans


def inv(a):
    d = len(a)
    z = [list(row) + [F(i == j) for j in range(d)] for i, row in enumerate(a)]
    for i in range(d):
        p = next(j for j in range(i, d) if z[j][i])
        z[i], z[p] = z[p], z[i]
        t = z[i][i]
        z[i] = [v / t for v in z[i]]
        for j in range(d):
            if j != i:
                t = z[j][i]
                z[j] = [x - t * y for x, y in zip(z[j], z[i])]
    return [row[d:] for row in z]


def matmul(a, b):
    bt = list(zip(*b))
    return [[dot(row, col) for col in bt] for row in a]


def maxvol_chart(u):
    n, d = len(u), len(u[0])
    indices = next(list(ii) for ii in combinations(range(n), d) if det([u[i] for i in ii]))
    denominators = [v.denominator for row in u for v in row]
    scale = max(denominators)
    assert all(scale % t == 0 for t in denominators)
    height = max(abs(int(v * scale)) for row in u for v in row)
    volume_ceiling = factorial(d) * height**d
    swap_bound = volume_ceiling.bit_length()
    swaps = []
    while True:
        minor = [u[i] for i in indices]
        a = matmul(u, inv(minor))
        i, b = max(
            ((i, b) for i in range(n) for b in range(d)), key=lambda ib: abs(a[ib[0]][ib[1]])
        )
        if abs(a[i][b]) <= 2:
            break
        before = abs(det(minor))
        coefficient = a[i][b]
        indices[b] = i
        after = abs(det([u[ii] for ii in indices]))
        assert after == abs(coefficient) * before
        assert after > 2 * before
        swaps.append((before, after))
        assert len(swaps) <= swap_bound
    assert matmul(a, [u[i] for i in indices]) == u
    assert all(abs(v) <= 2 for row in a for v in row)
    assert [a[i] for i in indices] == [[F(i == j) for j in range(d)] for i in range(d)]
    return indices, a, len(swaps), swap_bound


def ceil_log2(x):
    x = F(x)
    if x <= 1:
        return 0
    m = max(0, x.numerator.bit_length() - x.denominator.bit_length())
    while F(2) ** m < x:
        m += 1
    while m and F(2) ** (m - 1) >= x:
        m -= 1
    return m


class EpochStream:
    def __init__(self, n, r, beta_bar, K=F(1), Q=F(1)):
        self.n, self.r = n, r
        self.beta_bar, self.K, self.Q = F(beta_bar), K, Q
        self.m = ceil_log2(max(F(1), 8 * r * self.beta_bar * Q * K))
        self.delta = K / 2**self.m
        self.c = None
        self.u = [[] for _ in range(n)]
        self.epochs = []
        self.records = []
        self.max_swaps = 0

    def append(self, k):
        assert all(abs(v) <= self.K for v in k)
        if self.c is None:
            self.c = list(k)
            self.epochs.append({"I": [], "A": [[] for _ in k], "c0": list(k), "cells": {}})
        current = self.epochs[-1]
        y = [k[i] for i in current["I"]]
        reconstruction = [current["c0"][i] + dot(current["A"][i], y) for i in range(self.n)]
        if list(k) != reconstruction:
            for i in range(self.n):
                self.u[i].append(k[i] - self.c[i])
            assert len(self.u[0]) <= self.r
            ii, a, swaps, _ = maxvol_chart(self.u)
            self.max_swaps = max(self.max_swaps, swaps)
            ci = [self.c[i] for i in ii]
            c0 = [self.c[i] - dot(a[i], ci) for i in range(self.n)]
            current = {"I": ii, "A": a, "c0": c0, "cells": {}}
            self.epochs.append(current)
            y = [k[i] for i in ii]
        cell = tuple(v // self.delta for v in y)
        record_id = len(self.records)
        current["cells"].setdefault(cell, []).append(record_id)
        self.records.append({"key": list(k), "epoch": len(self.epochs) - 1, "cell": cell})

    def check(self, queries):
        assert len(self.epochs) <= self.r + 1
        total_cells = sum(len(e["cells"]) for e in self.epochs)
        G = 5 + 32 * self.r * self.beta_bar * self.Q * self.K
        assert total_cells <= min(len(self.records), (self.r + 1) * G**self.r)
        pair_checks = 0
        for d, e in enumerate(self.epochs):
            assert len(e["I"]) == d
            for cell, members in e["cells"].items():
                for j in members:
                    rec = self.records[j]
                    assert rec["epoch"] == d and rec["cell"] == cell
                    y = [rec["key"][i] for i in e["I"]]
                    assert rec["key"] == [e["c0"][i] + dot(e["A"][i], y) for i in range(self.n)]
                candidates = members if len(members) <= 20 else members[:10] + members[-10:]
                for q in queries:
                    assert all(abs(v) <= self.Q for v in q)
                    v = [sum(q[i] * e["A"][i][b] for i in range(self.n)) for b in range(d)]
                    assert all(abs(t) <= 2 * self.n * self.Q for t in v)
                    rep = self.records[members[0]]["key"]
                    for j in candidates:
                        k = self.records[j]["key"]
                        assert self.beta_bar * abs(
                            dot(q, [x - y for x, y in zip(k, rep)])
                        ) / self.n <= F(1, 4)
                        pair_checks += 1
        return total_cells, pair_checks


def mpf(x):
    x = F(x)
    return mp.mpf(x.numerator) / x.denominator


def envelope_check(groups, keys, proxies, q, beta):
    n, T = len(q), len(keys)
    aa = [beta * sum(mpf(q[i]) * mpf(k[i]) for i in range(n)) / n for k in keys]
    pc = [beta * sum(mpf(q[i]) * mpf(k[i]) for i in range(n)) / n for k in proxies]
    a0 = max(pc)
    ww = [mp.exp(a - a0 - mp.mpf(1) / 4) for a in aa]
    Z = sum(ww)
    p = ceil_log2(F(64 * T))
    unit = mp.mpf(2) ** (-p)
    uu = [mp.ceil((mp.exp(a - a0) + unit / 4) / unit) * unit + unit for a in pc]
    W = sum(len(g) * u for g, u in zip(groups, uu))
    assert Z > mp.mpf(1) / 2 - mp.mpf("1e-110")
    assert W / Z < mp.mpf(17) / 8
    error = mp.mpf(0)
    for group, u in zip(groups, uu):
        for j in group:
            assert ww[j] <= u + mp.mpf("1e-110")
            accepted = (len(group) * u / W) * (mp.mpf(1) / len(group)) * (ww[j] / u)
            normalized = accepted / (Z / W)
            target = ww[j] / Z
            error = max(error, abs(normalized - target))
    assert error < mp.mpf("1e-110")
    return mp.nstr(W / Z, 30), mp.nstr(error, 8)


def run():
    chart_cases = 0
    max_swaps = 0
    for d in (1, 2, 3, 4):
        n = 2 * d + 5
        for exponent in (1, 30, 120):
            tiny = F(1, 2**exponent)
            base = [F(RNG.choice((-1, 1)), 4) for _ in range(n)]
            u = [[base[i] + (tiny if i == b else 0) for b in range(d)] for i in range(n)]
            _, _, swaps, _ = maxvol_chart(u)
            chart_cases += 1
            max_swaps = max(max_swaps, swaps)
    # Force repeated improvements from tiny initial coordinate rows.
    for d in (1, 2, 3):
        u = [[F(i == b, 2**120) for b in range(d)] for i in range(d)]
        u += [[F(i == b) for b in range(d)] for i in range(d)]
        _, _, swaps, _ = maxvol_chart(u)
        assert swaps == d
        chart_cases += 1
        max_swaps = max(max_swaps, swaps)

    stream_results = []
    total_pairs = 0
    for n, r, beta_bar in ((8, 3, F(4)), (13, 2, F(4)), (4, 1, F(2**30)), (5, 2, F(0))):
        stream = EpochStream(n, r, beta_bar)
        zero = [F(0)] * n
        for _ in range(4096):
            stream.append(zero)
        old_epoch_assignment = [rec["epoch"] for rec in stream.records]
        for d in range(r):
            k = [F(0)] * n
            k[d] = F(1, 2)
            stream.append(k)
            for _ in range(80):
                k = [F(0)] * n
                for i in range(d + 1):
                    # Dyadic boundaries and adjacent values both occur.
                    raw = F(RNG.choice((-1, 0, 1)), 2)
                    offset = RNG.choice((F(0), F(1, 2**40), -F(1, 2**40)))
                    k[i] = raw + offset
                stream.append(k)
        assert [rec["epoch"] for rec in stream.records[:4096]] == old_epoch_assignment
        queries = [[F(RNG.choice((-1, 1))) for _ in range(n)] for _ in range(10)]
        queries += [[F(0)] * n]
        cells, pairs = stream.check(queries)
        total_pairs += pairs
        groups, proxies = [], []
        for epoch in stream.epochs:
            for members in epoch["cells"].values():
                groups.append(members)
                proxies.append(stream.records[members[0]]["key"])
        beta = mp.sqrt(n) if beta_bar and beta_bar < 100 else mpf(beta_bar)
        ratio, error = envelope_check(
            groups, [r["key"] for r in stream.records], proxies, queries[0], beta
        )
        stream_results.append(
            {
                "n": n,
                "rank_bound": r,
                "T": len(stream.records),
                "epochs": len(stream.epochs),
                "occupied_cells": cells,
                "old_record_migrations": 0,
                "proposal_ratio": ratio,
                "mass_identity_max_error": error,
            }
        )

    # A known rank-two chart with genuine residuals in the remaining coordinates.
    n, r, beta_bar = 11, 2, F(4)
    A = [[F(1), F(0)], [F(0), F(1)]] + [
        [F(RNG.choice((-2, -1, 0, 1, 2))), F(RNG.choice((-2, -1, 0, 1, 2)))] for _ in range(n - 2)
    ]
    eta = F(1, 8 * beta_bar)
    m = ceil_log2(F(16 * r) * beta_bar)
    delta = F(1, 2**m)
    keys, approx, buckets = [], [], {}
    for j in range(200):
        # Several pairs lie on opposite sides of a grid boundary.
        y = [
            F(RNG.randrange(-16, 17), 128) + RNG.choice((F(0), F(1, 2**50), -F(1, 2**50)))
            for _ in range(r)
        ]
        projected = [dot(row, y) for row in A]
        error = [F(0), F(0)] + [RNG.choice((-eta, F(0), eta)) for _ in range(n - 2)]
        k = [x + e for x, e in zip(projected, error)]
        assert all(abs(x) <= 1 for x in k)
        assert max(abs(k[i] - projected[i]) for i in range(n)) <= eta
        assert k[:2] == y
        cell = tuple(v // delta for v in y)
        buckets.setdefault(cell, []).append(j)
        keys.append(k)
        approx.append(projected)
    q = [F(RNG.choice((-1, 1))) for _ in range(n)]
    groups, proxies = list(buckets.values()), []
    for members in groups:
        proxy = approx[members[0]]
        proxies.append(proxy)
        for j in members:
            assert beta_bar * abs(dot(q, [x - y for x, y in zip(keys[j], proxy)])) / n <= F(1, 4)
    ratio, error = envelope_check(groups, keys, proxies, q, mp.sqrt(n))
    # A chart with coefficients exactly two approaches the analytic 1/4 bound.
    n_tight, beta_tight = 128, F(4)
    tight = EpochStream(n_tight, 1, beta_tight)
    tight.append([F(0)] * n_tight)
    y1 = tight.delta / 2**30
    y2 = tight.delta * (1 - F(1, 2**30))
    direction = [F(1)] + [F(2)] * (n_tight - 1)
    tight.append([y1 * x for x in direction])
    tight.append([y2 * x for x in direction])
    tight.check([[F(1)] * n_tight])
    tight_oscillation = beta_tight * sum((y2 - y1) * x for x in direction) / n_tight
    assert F(249, 1000) < tight_oscillation < F(1, 4)
    result = {
        "status": "all checks passed",
        "evidence_type": "exact rational invariant checks and 120-digit numerical checks, not proofs",
        "seed": 81973421,
        "chart_cases": chart_cases,
        "maximum_row_swaps_observed": max_swaps,
        "within_cell_score_checks": total_pairs,
        "streams": stream_results,
        "near_subspace_case": {
            "n": n,
            "rank": r,
            "T": len(keys),
            "eta": str(eta),
            "occupied_cells": len(groups),
            "proposal_ratio": ratio,
            "mass_identity_max_error": error,
        },
        "near_extremal_cell_oscillation": str(tight_oscillation),
        "near_extremal_cell_oscillation_decimal": str(float(tight_oscillation)),
        "uncompiled_lean": True,
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    run()
