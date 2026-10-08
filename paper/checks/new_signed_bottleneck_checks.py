#!/usr/bin/env python3
"""120-digit non-interval checks for the signed scalar-bottleneck theorem.
Formula checks and finite examples only; no sampler benchmark or proof.
"""

import json
import random
from pathlib import Path

import mpmath as mp

mp.mp.dps = 120
ORDER = 40
counts = {}
resids = {}
ratios = {}


def check(g, v):
    counts[g] = counts.get(g, 0) + 1
    assert v, g


def eq(g, r):
    counts[g] = counts.get(g, 0) + 1
    resids[g] = max(resids.get(g, mp.mpf(0)), abs(r))
    assert abs(r) < mp.mpf("1e-95"), (g, mp.nstr(r, 25))


def expser(a):
    e = [mp.exp(a[0])]
    for k in range(1, ORDER + 1):
        e.append(mp.fsum(j * a[j] * e[k - j] for j in range(1, k + 1)) / k)
    return e


def invser(a):
    r = [1 / a[0]]
    for k in range(1, ORDER + 1):
        r.append(-mp.fsum(a[j] * r[k - j] for j in range(1, k + 1)) / a[0])
    return r


def tanhser(a):
    e = expser([2 * x for x in a])
    e[0] += 1
    r = invser(e)
    return [1 - 2 * r[0]] + [-2 * x for x in r[1:]]


N = 4
for seed in [3, 11, 37]:
    for D in [1, 2, 4, 8, 16]:
        rng = random.Random(seed + D)
        avec = [mp.mpf(rng.choice([-1, 1]) * (j + 1)) / N for j in range(N)]
        layers = []
        for ell in range(1, D):
            mat = []
            for i in range(N):
                cuts = [0] + sorted(rng.sample(range(1, 32), N - 1)) + [32]
                mat.append(
                    [mp.mpf(rng.choice([-1, 1]) * (cuts[j + 1] - cuts[j])) / 32 for j in range(N)]
                )
            layers.append(mat)

        def F(z, all_layers=False):
            h = [mp.tanh(ai * z) for ai in avec]
            ret = [h]
            for mat in layers:
                h = [mp.tanh(mp.fsum(row[j] * h[j] for j in range(N))) for row in mat]
                ret.append(h)
            return ret if all_layers else h[0]

        rho = mp.sqrt(mp.mpf(3) / (2 * D + 3))
        q = mp.mpf(1)
        if 2 * rho < 1:
            while q / 2 >= 2 * rho:
                q /= 2
        check("gate_range", q <= 5 / mp.sqrt(D + 1) and q >= min(1, 2 / mp.sqrt(D + 1)))
        M2 = 16 * (D + 1)
        M3 = 256 * (D + 1) ** 2
        M4 = 8192 * (D + 1) ** 2
        A = M2 + M3 + M4
        m0 = 1
        while m0 < max(1, 2 * M2, 2 * mp.sqrt(A)):
            m0 *= 2
        check("source_constant", q * (mp.mpf(7) / 8 * m0 + mp.mpf(A) / m0) <= 1840 * mp.sqrt(D + 1))
        for p in map(mp.mpf, ["0", "0.1", "0.25", "0.5", "0.75", "0.9", "1"]):
            f = lambda p: F(2 * p - 1) / q
            check("normalized_radius", abs(f(p)) <= mp.mpf(4) / 5)
            for j, bound in [(2, M2), (3, M3), (4, M4)]:
                check("derivative_bounds", abs(mp.diff(f, p, j)) <= bound)
        for real in map(mp.mpf, ["-2", "-1", "-0.5", "0", "0.5", "1", "2"]):
            for frac in map(mp.mpf, ["-1", "-0.5", "0.5", "1"]):
                y = frac / (4 * mp.sqrt(D))
                ll = F(real + 1j * y, True)
                for ell, h in enumerate(ll, 1):
                    bound = abs(y) / mp.sqrt(1 - ell * y * y)
                    check("strip_imaginary", max(abs(mp.im(v)) for v in h) <= bound)
                    check("strip_modulus", max(abs(v) for v in h) < 2)
        d = 1
        while d * d < D:
            d *= 2
        a = mp.mpf(1) / (32 * d)
        for center in map(mp.mpf, ["-1", "-0.5", "0", "0.5", "1"]):
            initial = [center, 2 * a] + [mp.mpf(0)] * (ORDER - 1)
            hs = [tanhser([ai * x for x in initial]) for ai in avec]
            for mat in layers:
                hs = [
                    tanhser(
                        [mp.fsum(row[j] * hs[j][k] for j in range(N)) for k in range(ORDER + 1)]
                    )
                    for row in mat
                ]
            coeff = hs[0]
            eq("taylor_constant", coeff[0] - F(center))
            eq("taylor_first", coeff[1] - 2 * a * mp.diff(F, center))
            eq("taylor_second", 2 * coeff[2] - (2 * a) ** 2 * mp.diff(F, center, 2))
            for u in map(mp.mpf, ["0.1", "0.25", "0.5"]):
                poly = mp.fsum(coeff[k] * u**k for k in range(ORDER + 1))
                poly2 = mp.fsum(k * (k - 1) * coeff[k] * u ** (k - 2) for k in range(2, ORDER + 1))
                value_error = abs(poly - F(center + 2 * a * u))
                derivative_error = abs(poly2 - (2 * a) ** 2 * mp.diff(F, center + 2 * a * u, 2))
                bv = 4 * mp.power(4, -ORDER)
                bd = 32 * (ORDER + 2) ** 2 * mp.power(4, -ORDER)
                check("taylor_value_tail", value_error <= bv)
                check("taylor_second_tail", derivative_error <= bd)
                ratios["value_tail"] = max(ratios.get("value_tail", 0), value_error / bv)
                ratios["second_tail"] = max(ratios.get("second_tail", 0), derivative_error / bd)
# Exact algebra behind cancellation of mixture mass and cache-miss probability.
for A in map(mp.mpf, ["1", "10", "100", "10000"]):
    for eps in map(mp.mpf, ["0.0001", "0.00000001"]):
        for m in [1, 2, 4, 16, 256, 65536]:
            c = A / (4 * m * m)
            eq("cache_miss_cancellation", c * min(1, eps / c) * m - min(c, eps) * m)
out = {
    "precision_decimal_digits": 120,
    "total_checks": sum(counts.values()),
    "counts": counts,
    "max_absolute_identity_residuals": {k: mp.nstr(v, 16) for k, v in resids.items()},
    "largest_truncation_error_over_proved_bound": {k: mp.nstr(v, 16) for k, v in ratios.items()},
    "status": "passed; finite deterministic checks; not interval certified; no sampler benchmark",
}
path = Path(__file__).with_suffix(".json")
path.write_text(json.dumps(out, indent=2) + "\n")
print(
    json.dumps(
        {
            "total_checks": out["total_checks"],
            "output": str(path),
            "status": out["status"],
            "max_identity_residual": mp.nstr(max(resids.values()), 12),
        },
        indent=2,
    )
)
