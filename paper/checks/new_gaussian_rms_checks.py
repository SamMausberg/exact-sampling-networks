#!/usr/bin/env python3
"""Deterministic formula checks at 120 decimal digits; not a sampler benchmark.

Run with mpmath installed.  The script checks identities, a rigorously
specified series truncation bound numerically, and explicit inequalities.
Its arithmetic is high precision, not interval-certified.
"""

import json
from pathlib import Path

import mpmath as mp

mp.mp.dps = 120
counts = {}
max_residual = {}
worst = {}


def record(group, residual, detail):
    counts[group] = counts.get(group, 0) + 1
    residual = abs(residual)
    if residual > max_residual.get(group, mp.mpf(0)):
        max_residual[group] = residual
        worst[group] = detail
    assert residual < mp.mpf("1e-95"), (group, detail, mp.nstr(residual, 30))


def A(k):
    return (2 * k + 1) * mp.binomial(2 * k, k) / mp.power(4, k)


def majority(k, z):
    if z == 0:
        return mp.mpf(0)
    if z == 1:
        return mp.mpf(1)
    if z == -1:
        return mp.mpf(-1)
    if z < 0:
        return -majority(k, -z)
    return 1 - 2 * mp.betainc(k + 1, k + 1, 0, (1 - z) / 2, regularized=True)


cs = [
    mp.mpf(0),
    mp.mpf("0.01"),
    mp.mpf("0.1"),
    mp.mpf(1) / 3,
    mp.mpf("0.5"),
    mp.mpf(1),
    mp.mpf(2),
    mp.mpf(4),
    mp.mpf(8),
]
zs = [
    mp.mpf(x)
    for x in [
        "-1",
        "-0.99",
        "-0.75",
        "-0.5",
        "-0.25",
        "-0.1",
        "0",
        "0.1",
        "0.25",
        "0.5",
        "0.75",
        "0.99",
        "1",
    ]
]
truncations = []
for c in cs:
    if not c:
        for z in zs:
            record("erf_majority", 0, [str(c), str(z)])
        continue
    cutoff = int(mp.ceil(c * c + 50 * c + 180))
    pref = 2 * c / mp.sqrt(mp.pi) * mp.exp(-c * c)
    coeffs = [pref * mp.power(c, 2 * k) / (mp.factorial(k) * A(k)) for k in range(cutoff + 1)]
    # A_k >= 1.  Beyond cutoff, Poisson successive ratios decrease and
    # the tail is bounded by its first term divided by 1-c^2/(cutoff+2).
    bound = (
        pref * mp.power(c, 2 * (cutoff + 1)) / mp.factorial(cutoff + 1) / (1 - c * c / (cutoff + 2))
    )
    assert bound < mp.mpf("1e-105")
    truncations.append({"c": str(c), "cutoff": cutoff, "tail_bound": mp.nstr(bound, 12)})
    for z in zs:
        value = mp.fsum(coeffs[k] * majority(k, z) for k in range(cutoff + 1))
        record("erf_majority", value - mp.erf(c * z), [str(c), str(z)])
    record("erf_mass", mp.fsum(coeffs) - mp.erf(c), str(c))
    record(
        "erf_arity",
        mp.fsum((2 * k + 1) * coeffs[k] for k in range(cutoff + 1))
        - (2 * c * c * mp.erf(c) + 2 * c / mp.sqrt(mp.pi) * mp.exp(-c * c)),
        str(c),
    )
    for k in [0, 1, 2, 3, 10, 25]:
        v = (
            2
            / mp.sqrt(mp.pi)
            * mp.quad(
                lambda y: (
                    mp.exp(-y * y)
                    * mp.exp(-(c * c - y * y))
                    * mp.power(c * c - y * y, k)
                    / mp.factorial(k)
                ),
                [0, c],
            )
        )
        record("gaussian_poisson_weight", v - coeffs[k], [str(c), k])

c0 = mp.pi / 2
sin_weights = [mp.power(c0, 2 * k + 1) / (4 * mp.factorial(2 * k + 1)) for k in range(120)]
for z in zs:
    val = mp.fsum(((-1) ** k) * sin_weights[k] * mp.power(z, 2 * k + 1) for k in range(120))
    record("sine_series", val - mp.sin(mp.pi * z / 2) / 4, str(z))
record("sine_mass", mp.fsum(sin_weights) - mp.sinh(c0) / 4, "all")
record(
    "sine_arity",
    mp.fsum((2 * k + 1) * sin_weights[k] for k in range(120)) - mp.pi / 8 * mp.cosh(c0),
    "all",
)
assert mp.pi / 8 * mp.cosh(c0) < 1
v = mp.mpf(11) / 7
cosh_bound = (
    1
    + v * v / 2
    + v**4 / mp.factorial(4)
    + v**6 / mp.factorial(6)
    + v**8 / (mp.factorial(8) * (1 - v * v / 90))
)
assert mp.cosh(v) <= cosh_bound < mp.mpf(101) / 40

for u in map(
    mp.mpf, ["-0.999", "-0.95", "-0.75", "-0.5", "-0.1", "0", "0.1", "0.5", "0.75", "0.95", "0.999"]
):
    fac = u / mp.sqrt(2 * (1 - u * u))
    val = (
        2
        / mp.sqrt(2 * mp.pi)
        * mp.quad(lambda x: mp.exp(-x * x / 2) * mp.erf(fac * x), [0, 1, 4, mp.inf])
    )
    record("gaussian_arcsine", val - 2 / mp.pi * mp.asin(u), str(u))

for n in [1, 2, 3, 8, 32]:
    for eps in map(mp.mpf, ["0.0001", "0.01", "0.1", "1", "10", "100"]):
        for offset in [0, 1, 2, 3]:
            a = [mp.sin((j + 1) * (offset + 1)) for j in range(n)]
            squares = mp.fsum(x * x for x in a)
            for i in sorted(set([0, n - 1])):
                u = a[i] / mp.sqrt(squares + n * eps)
                mu = 2 / mp.pi * mp.asin(u)
                actual = mp.sin(mp.pi * mu / 2) / 4
                target = a[i] / (4 * mp.sqrt(n) * mp.sqrt(eps + squares / n))
                record("rms_exactness", actual - target, [n, str(eps), offset, i])
            kappa = 1 / eps
            c2 = kappa * (1 + 2 * (n - 1) / mp.pi) / 2
            es2 = n + 2 * n * (n - 1) / mp.pi
            record("gaussian_second_moment", c2 - kappa * es2 / (2 * n), [n, str(eps)])
            assert (mp.pi / 8 * mp.cosh(c0)) * (1 + 2 * c2) <= 1 + n * kappa
            assert 1 + 2 * c2 + mp.mpf(3) / 4 * n * n * kappa * kappa <= (1 + n * kappa) ** 2

out = {
    "precision_decimal_digits": 120,
    "method": "deterministic non-interval high-precision formula checks",
    "counts": counts,
    "total_checks": sum(counts.values()),
    "max_absolute_residuals": {k: mp.nstr(v, 16) for k, v in max_residual.items()},
    "worst_parameters": worst,
    "erf_series_truncations": truncations,
    "C_sin": mp.nstr(mp.pi / 8 * mp.cosh(c0), 50),
    "sine_mass": mp.nstr(mp.sinh(c0) / 4, 50),
    "cosh_rational_upper": mp.nstr(cosh_bound, 50),
    "status": "passed; not interval certified; not a stochastic sampler benchmark",
}
path = Path(__file__).with_suffix(".json")
path.write_text(json.dumps(out, indent=2) + "\n")
print(
    json.dumps(
        {
            "total_checks": out["total_checks"],
            "status": out["status"],
            "output": str(path),
            "max_residual": mp.nstr(max(max_residual.values()), 12),
        },
        indent=2,
    )
)
