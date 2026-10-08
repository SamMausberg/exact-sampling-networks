#!/usr/bin/env python3
"""120-digit deterministic checks for the scalar-bottleneck theorem.
Not interval certified. Checks formulas, coefficient signs, and bounds;
does not benchmark or formally verify the exact sampler.
"""

import json
import random
from pathlib import Path

import mpmath as mp

mp.mp.dps = 120
N = 4
ORDER = 49
checks = {}
residuals = {}


def rec(group, residual):
    checks[group] = checks.get(group, 0) + 1
    residuals[group] = max(residuals.get(group, mp.mpf(0)), abs(residual))
    assert abs(residual) < mp.mpf("1e-90"), (group, mp.nstr(residual, 30))


def inequality(group, truth):
    checks[group] = checks.get(group, 0) + 1
    assert truth, group


def mul(a, b):
    return [mp.fsum(a[j] * b[k - j] for j in range(k + 1)) for k in range(ORDER + 1)]


def expseries(a):
    e = [mp.exp(a[0])]
    for k in range(1, ORDER + 1):
        e.append(mp.fsum(j * a[j] * e[k - j] for j in range(1, k + 1)) / k)
    return e


def invseries(a):
    r = [1 / a[0]]
    for k in range(1, ORDER + 1):
        r.append(-mp.fsum(a[j] * r[k - j] for j in range(1, k + 1)) / a[0])
    return r


def tanhseries(a):
    e = expseries([2 * x for x in a])
    e[0] += 1
    r = invseries(e)
    return [1 - 2 * r[0]] + [-2 * x for x in r[1:]]


sq = [mp.mpf(1)]
for j in range(1, ORDER + 1):
    sq.append(sq[-1] * (mp.mpf(j) - mp.mpf("1.5")) / j)
results = []
for seed in [1, 7, 29]:
    for depth in [1, 2, 4, 8, 16]:
        rng = random.Random(seed)
        a = [mp.mpf(i + 1) / N for i in range(N)]
        layers = []
        for ell in range(1, depth):
            matrix = []
            for i in range(N):
                cuts = [0] + sorted(rng.sample(range(1, 32), N - 1)) + [32]
                matrix.append([mp.mpf(cuts[j + 1] - cuts[j]) / 32 for j in range(N)])
            layers.append(matrix)

        def F(z, imaginary=False):
            phi = mp.tan if imaginary else mp.tanh
            h = [phi(ai * z) for ai in a]
            for matrix in layers:
                h = [phi(mp.fsum(row[j] * h[j] for j in range(N))) for row in matrix]
            return h[0]

        lambdas = a[:]
        for matrix in layers:
            lambdas = [mp.fsum(row[j] * lambdas[j] for j in range(N)) for row in matrix]
        lam = lambdas[0]
        h = [tanhseries([ai * x for x in sq]) for ai in a]
        for matrix in layers:
            h = [
                tanhseries([mp.fsum(row[j] * h[j][k] for j in range(N)) for k in range(ORDER + 1)])
                for row in matrix
            ]
        derivative = [(k + 1) * h[0][k + 1] for k in range(ORDER)] + [mp.mpf(0)]
        ds = [-2 * x for x in mul(sq, derivative)][:-1]
        inequality("coefficient_positivity", min(ds) > -mp.mpf("1e-100"))
        rec("derivative_at_one", ds[0] - mp.diff(F, 1))
        V = 1 + mp.mpf(1) / (8 * depth)
        cutoff = mp.fsum(ds[k] * V**k for k in range(len(ds)))
        imag = mp.diff(lambda y: F(y, True), 1 / mp.sqrt(8 * depth))
        inequality("weighted_coefficient_bound", cutoff <= imag + mp.mpf("1e-95"))
        inequality("imaginary_derivative_bound", imag <= mp.mpf(8) / 7 * lam)
        mass = mp.fsum(ds[k] / ((2 * k + 1) * mp.binomial(2 * k, k) / 4**k) for k in range(len(ds)))
        arity = mp.fsum(
            (2 * k + 1) * ds[k] / ((2 * k + 1) * mp.binomial(2 * k, k) / 4**k)
            for k in range(len(ds))
        )
        inequality("partial_mass_bound", mass <= F(1) + mp.mpf("1e-95"))
        inequality("partial_arity_bound", arity <= 2 * lam * mp.sqrt(depth))
        for z in map(mp.mpf, ["0", "0.01", "0.1", "0.25", "0.5", "0.9", "1"]):
            d = mp.diff(F, z)
            inequality("derivative_loss", lam - d <= lam * min(1, depth * z * z) + mp.mpf("1e-100"))
            inequality("monotone_derivative", -mp.mpf("1e-100") <= d <= lam + mp.mpf("1e-100"))
            inequality("range_bound", abs(F(z)) <= z + mp.mpf("1e-100"))
        results.append(
            {
                "seed": seed,
                "depth": depth,
                "lambda": mp.nstr(lam, 25),
                "range": mp.nstr(F(1), 25),
                "partial_arity_49": mp.nstr(arity, 25),
                "arity_bound": mp.nstr(2 * lam * mp.sqrt(depth), 25),
                "imaginary_derivative_ratio": mp.nstr(imag / lam, 25),
            }
        )
# Direct check of the arity beta-integral and majority recursion identities.
for k in [0, 1, 2, 3, 8, 24, 48]:
    C = (2 * k + 1) * mp.binomial(2 * k, k) / 4**k
    integ = (
        mp.mpf(0)
        if not k
        else mp.quad(lambda z: -mp.expm1(k * mp.log1p(-z * z)) / (z * z) if z else k, [0, 1])
    )
    rec("arity_integral", 1 + integ - (2 * k + 1) / C)
    for z in map(mp.mpf, ["-0.9", "-0.5", "-0.1", "0", "0.1", "0.5", "0.9"]):
        poly = z * mp.fsum(mp.binomial(2 * j, j) / 4**j * (1 - z * z) ** j for j in range(k + 1))
        direct = 1 - 2 * mp.betainc(k + 1, k + 1, 0, (1 - z) / 2, regularized=True)
        rec("majority_recurrence", poly - direct)
for n in [2, 4, 8, 32, 1024]:
    for depth in [1, 2, 8, 32]:
        p0 = int(mp.ceil(mp.log(256 * n * n * depth, 2)))
        K = 32 * depth * p0
        delta = mp.power(2, -p0)
        inequality(
            "explicit_tail_cutoff",
            mp.mpf(8) / 7 * mp.exp(-mp.mpf(K + 1) / (16 * depth)) <= delta / 16,
        )
        P = p0 + int(mp.ceil(mp.log(64 * (K + 1), 2)))
        inequality("explicit_rounding_mass", (K + 1) * mp.power(2, -P) <= delta / 64)
out = {
    "precision_decimal_digits": 120,
    "total_checks": sum(checks.values()),
    "counts": checks,
    "max_absolute_residuals": {k: mp.nstr(v, 16) for k, v in residuals.items()},
    "network_checks": results,
    "status": "passed; deterministic identities and inequalities; not interval certified; no sampler benchmark",
}
path = Path(__file__).with_suffix(".json")
path.write_text(json.dumps(out, indent=2) + "\n")
print(
    json.dumps(
        {
            "total_checks": out["total_checks"],
            "status": out["status"],
            "max_residual": mp.nstr(max(residuals.values()), 12),
            "output": str(path),
        },
        indent=2,
    )
)
