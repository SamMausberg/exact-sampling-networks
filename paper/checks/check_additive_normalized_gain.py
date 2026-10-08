"""Supplementary binary64 checks for the new additive lower bound.

These checks are not proofs and do not certify the theorem or Lean code.
Run with Python 3. The JSON output records the fixed random seed.
"""

from __future__ import annotations

import json
import math
import random
from pathlib import Path

SEED = 731908
rng = random.Random(SEED)
c = math.tanh(1.0)
A0 = c * c / 2.0
A1 = 4.0 + c * (1.0 - c)
gamma0 = 3.0 * c * c / (12.0 + (1.0 + c) ** 2)
counts: dict[str, int] = {}
worst: dict[str, float] = {}


def check_ge(name: str, lhs: float, rhs: float, tol: float = 3e-12) -> None:
    scale = max(1.0, abs(lhs), abs(rhs))
    error = (rhs - lhs) / scale
    counts[name] = counts.get(name, 0) + 1
    worst[name] = max(worst.get(name, -math.inf), error)
    if error > tol:
        raise AssertionError((name, lhs, rhs, error))


# The exact completed-square floor identity, also at its minimizing scale.
for theta in [0.25, 0.3, 0.5]:
    A = 3.0 + theta * (1.0 + c) ** 2
    floor = 3.0 * theta * c * c / A
    tau_min = A / (theta * c * (1.0 + c)) - 1.0
    for tau in [0.0, 1.0, tau_min] + [2.0**k for k in range(-20, 31)]:
        left = 3.0 + theta * (c * tau - 1.0) ** 2
        check_ge("carrier_floor", left, floor * (1.0 + tau) ** 2)
        check_ge("floor_at_least_one_twelfth", left, (1.0 + tau) ** 2 / 12.0)


# Near the normalized-gain threshold, the constants can be large, but
# the local comparison remains well defined. These tests use logarithmic
# radii instead of simulating an impractically long burn-in.
for s in [0.53857421875, 0.5390625, 0.5625, 0.75, 1.0, 1.125, 2.0, 4.0]:
    kappa = s / math.sqrt(A0)
    nu = kappa - 1.0
    if nu <= 0.0:
        continue
    K = kappa * A1 / (2.0 * A0)
    Rstar = math.ceil(max(4.0, 2.0 * K / nu))
    C = kappa * (s * s + 0.5) / (A0 * nu)
    for radius in [float(Rstar), Rstar + 1.0, 2.0 * Rstar, 1e3 * Rstar, 1e9 * Rstar]:
        t = s / math.sqrt(A0 + A1 / radius)
        check_ge("gain_discrepancy", K / radius, kappa - t)
        check_ge("post_burnin_gain", t - 1.0, nu / 2.0)
        for step in [0.0, 2.0**-20, 0.125, 1.0]:
            q = step / (radius + step)
            g = 1.0 + (t - 1.0) * q
            B = (s * s + 0.5) / (A0 + A1 / radius)
            d = q * t * B / g
            check_ge("reciprocal_coefficient", C * (g * g - 1.0), d, tol=2e-10)
            for u in [0.0, 2.0**-20, 0.125, 0.5, 1.0]:
                mixture = (1.0 - q) * u + q * t * u / math.sqrt(1.0 + B * u * u)
                comparison = g * u / math.sqrt(1.0 + d * u * u)
                check_ge("convexity_comparison", mixture, comparison)


scenarios = []
for n in [4, 5, 7, 8, 13, 16, 31, 64, 127]:
    N = 1 << ((n // 2).bit_length() - 1)
    eta = N / n
    for s in [0.75, 1.0, 1.125, 2.0]:
        for schedule_kind in ["unit", "small", "sparse_dyadic"]:
            D = 512
            if schedule_kind == "unit":
                steps = [1.0] * D
            elif schedule_kind == "small":
                steps = [0.125] * D
            else:
                steps = [rng.randrange(9) / 8.0 if rng.randrange(3) else 0.0 for _ in range(D)]
            scenarios.append((n, eta, s, schedule_kind, steps))

for n, eta, s, schedule_kind, steps in scenarios:
    kappa = s / math.sqrt(A0)
    nu = kappa - 1.0
    K = kappa * A1 / (2.0 * A0)
    Rstar = math.ceil(max(4.0, 2.0 * K / nu))
    Mstar = Rstar + 1.0
    C = kappa * (s * s + 0.5) / (A0 * nu)
    Estar = (nu + K + nu * nu / 2.0) / Rstar
    for z in [2.0**-20, 2.0**-10, 0.125, 0.5, 1.0]:
        F, tau = z, 0.0
        reached = False
        logG = 0.0
        radius0 = None
        sumq = sumq2 = sumqr = 0.0
        for step in steps:
            radius = 1.0 + tau
            if not reached and radius >= Rstar:
                reached = True
                radius0 = radius
            variance = 4.0 - eta - eta * z * z + eta * F * F + eta * (1.0 + c * tau) ** 2
            Fnext = F + step * math.tanh(s * F / math.sqrt(variance))
            if reached:
                q = step / (radius + step)
                t = s / math.sqrt(A0 + A1 / radius)
                logG += math.log1p((t - 1.0) * q)
                sumq += q
                sumq2 += q * q
                sumqr += q / radius
                inverse_gain2 = math.exp(-2.0 * logG)
                initial = z / Mstar
                comparison = initial / math.sqrt(
                    inverse_gain2 + C * (1.0 - inverse_gain2) * initial * initial
                )
                check_ge("full_reciprocal_comparison", Fnext / (radius + step), comparison)
            F, tau = Fnext, tau + step
        radius = 1.0 + tau
        variance = 4.0 - eta - eta * z * z + eta * F * F + eta * (1.0 + c * tau) ** 2
        L = 4.0 * math.sqrt(variance)
        output_mean = (
            (1.0 + z) * math.tanh((F - z + 1.0) / L) + (1.0 - z) * math.tanh((F - z - 1.0) / L)
        ) / 2.0
        check_ge("coordinate_head", output_mean, F / (32.0 * radius))
        check_ge("actual_floor", variance, gamma0 * radius * radius)
        if reached:
            check_ge("gain_product", logG, nu * math.log(radius / Mstar) - Estar)
            check_ge("schedule_square_sum", 1.0 / radius0, sumq2)
            check_ge("schedule_log_sum", sumq, math.log(radius / radius0) - 1.0 / radius0)
            check_ge("schedule_reciprocal_sum", 1.0 / radius0, sumqr)

result = {
    "description": "Supplementary binary64 checks only; not a proof or formal verification.",
    "seed": SEED,
    "c": c,
    "gamma0": gamma0,
    "scenarios": len(scenarios),
    "counts": counts,
    "worst_scaled_rhs_minus_lhs": worst,
    "all_checks_passed": True,
}
destination = Path(__file__).with_suffix(".json")
destination.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
