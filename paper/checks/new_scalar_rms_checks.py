#!/usr/bin/env python3
"""120-digit deterministic identities for the scalar RMS amplitude theorem.
These checks are not interval-certified and do not establish the theorem.
No stochastic sampling benchmark is performed.
"""

import json
from pathlib import Path

import mpmath as mp

mp.mp.dps = 120
counts = {}
residuals = {}


def record(group, residual):
    counts[group] = counts.get(group, 0) + 1
    residuals[group] = max(residuals.get(group, mp.mpf(0)), abs(residual))
    assert abs(residual) < mp.mpf("1e-95"), (group, mp.nstr(residual, 30))


def f(kappa, amplitude, z):
    return z / (amplitude * mp.sqrt(1 / kappa + z * z))


def f2(kappa, amplitude, z):
    return -3 * z / kappa / (amplitude * mp.power(1 / kappa + z * z, mp.mpf("2.5")))


zs = list(map(mp.mpf, ["-1", "-0.9", "-0.5", "-0.1", "0", "0.1", "0.5", "0.9", "1"]))
kappas = list(map(mp.mpf, ["0.0001", "0.01", "0.1", "0.25", "0.5", "1", "2", "4", "10"]))
cutoffs = []
for kap in kappas:
    rho = kap / (1 + kap)
    cutoff = int(mp.ceil(mp.log(mp.mpf("1e-108")) / mp.log(rho)))
    cutoffs.append(
        {"kappa": str(kap), "cutoff": cutoff, "tail_bound": mp.nstr(rho ** (cutoff + 1), 16)}
    )
    for z in zs:
        majority = z
        term = z
        weight = 1 - rho
        total = weight * majority
        mass = weight
        arity = weight
        for j in range(1, cutoff + 1):
            term *= mp.mpf(2 * j - 1) / (2 * j) * (1 - z * z)
            majority += term
            weight *= rho
            total += weight * majority
            mass += weight
            arity += (2 * j + 1) * weight
        expected = z * mp.sqrt(1 + 1 / kap) / mp.sqrt(1 / kap + z * z)
        record("geometric_majority", total - expected)
        record("geometric_mass", mass - 1)
        # The tail bound for the arity has an extra polynomial factor.
        record("geometric_arity", arity - (1 + 2 * kap))
        for amp in map(mp.mpf, ["1", "2", "4", "17", "100"]):
            gate = 1 / (amp * mp.sqrt(1 + 1 / kap))
            record("gated_exactness", gate * expected - f(kap, amp, z))
            record("second_derivative", mp.diff(lambda x: f(kap, amp, x), z, 2) - f2(kap, amp, z))
            upper = gate * (1 + 2 * kap)
            scale = (mp.sqrt(kap) + kap) / amp
            assert upper <= 3 * scale
            assert upper >= scale / 8
        if kap >= 1:
            test = 1 / (2 * mp.sqrt(kap))
            record("curvature_constant", abs(f2(kap, 1, test)) - 48 * kap / (25 * mp.sqrt(5)))
            assert (1 - test * test) * abs(f2(kap, 1, test)) / 2 >= kap / 4
        else:
            assert f(kap, 1, 1) >= (mp.sqrt(kap) + kap) / 8

# Check the coefficient and finite-difference formula for H_m'' directly
# against differentiation of the finite Bernstein polynomial.
for m in [2, 3, 8, 16, 32]:
    for kap in map(mp.mpf, ["0.1", "1", "10"]):
        values = [f(kap, 4, mp.mpf(2 * j) / m - 1) for j in range(m + 1)]

        def H(t):
            p = (1 + t) / 2
            return mp.fsum(
                mp.binomial(m, j) * p**j * (1 - p) ** (m - j) * values[j] for j in range(m + 1)
            )

        for t in map(mp.mpf, ["-0.75", "-0.25", "0", "0.25", "0.75"]):
            p = (1 + t) / 2
            fd = (
                mp.mpf(m * (m - 1))
                / 4
                * mp.fsum(
                    mp.binomial(m - 2, j)
                    * p**j
                    * (1 - p) ** (m - 2 - j)
                    * (values[j + 2] - 2 * values[j + 1] + values[j])
                    for j in range(m - 1)
                )
            )
            record("bernstein_second_derivative", mp.diff(H, t, 2) - fd)

for n in [1, 2, 3, 8, 32, 100]:
    for mult in map(mp.mpf, ["4", "10", "100", "10000"]):
        kap = n * mult
        gate = 2 * mp.sqrt(n / kap)
        for z in zs:
            record("vector_radius_thinning", gate * z / (4 * mp.sqrt(n)) - z / (2 * mp.sqrt(kap)))
        assert gate <= 1
        assert gate * n * (1 + kap) <= 4 * n ** mp.mpf("1.5") * mp.sqrt(kap)

out = {
    "precision_decimal_digits": 120,
    "total_checks": sum(counts.values()),
    "counts": counts,
    "max_absolute_residuals": {k: mp.nstr(v, 16) for k, v in residuals.items()},
    "geometric_truncations": cutoffs,
    "status": "passed; deterministic formula checks; not interval certified; no sampler benchmark",
}
path = Path(__file__).with_suffix(".json")
path.write_text(json.dumps(out, indent=2) + "\n")
print(
    json.dumps(
        {
            "total_checks": out["total_checks"],
            "max_residual": mp.nstr(max(residuals.values()), 12),
            "output": str(path),
            "status": out["status"],
        },
        indent=2,
    )
)
