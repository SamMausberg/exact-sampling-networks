#!/usr/bin/env python3
"""Finite deterministic checks for normalization_floor.tex and normalization_obstruction.tex. These are not proofs.

No sampler is benchmarked. All arithmetic below uses 120 decimal digits.
The geometric-majority truncation is compared with its explicit probability
tail, independently of the numerical residual.
"""

import json
import math
from pathlib import Path

import mpmath as mp

mp.mp.dps = 120


def mean_function(m, eps, c):
    w = m / (mp.sqrt(2) * mp.sqrt(2 * eps + c * c + m * m))
    return mp.tanh(mp.tanh(w))


def exact_binomial_derivative(T, eps):
    c = mp.mpf(2) ** (-math.ceil(math.log2(T)))
    total = mp.mpf(0)
    for k in range(T + 1):
        m = mp.mpf(2 * k - T) / T
        probability = mp.mpf(math.comb(T, k)) / (mp.mpf(2) ** T)
        total += T * probability * m * mean_function(m, eps, c)
    lower = 1 / (8 * mp.sqrt(2 * eps + c * c + mp.mpf(3) / T))
    scale = mp.mpf(T) if eps == 0 else min(mp.mpf(T), 1 / eps)
    assert total >= lower
    assert total * total >= scale / 384
    return total / lower, total * total / scale


def fixed_grid_derivative(T, eps):
    total = mp.mpf(0)
    c = mp.mpf(1) / T
    for k in range(T + 1):
        m = mp.mpf(2 * k - T) / T
        probability = mp.mpf(math.comb(T, k)) / (mp.mpf(2) ** T)
        w = m / mp.sqrt(4 * eps + c * c + m * m)
        total += T * probability * m * mp.tanh(mp.tanh(w))
    lower = 1 / (4 * mp.sqrt(4 * eps + c * c + mp.mpf(3) / T))
    scale = mp.mpf(T) if eps == 0 else min(mp.mpf(T), 1 / eps)
    assert total >= lower
    assert total * total >= scale / 128
    return total / lower, total * total / scale


def geometric_majority(theta, z):
    p = theta / (1 + theta)
    t = 1 / (1 + theta)
    tolerance = mp.mpf("1e-90")
    count = max(2, int(mp.ceil(mp.log(tolerance) / mp.log(t))))
    central = mp.mpf(1)
    majority = z
    p_mass = p
    total = p_mass * majority
    one_minus_z2_power = mp.mpf(1)
    for k in range(1, count + 1):
        central *= mp.mpf(2 * k - 1) / (2 * k)
        one_minus_z2_power *= 1 - z * z
        majority += central * z * one_minus_z2_power
        p_mass *= t
        total += p_mass * majority
    closed = z * mp.sqrt(1 + theta) / mp.sqrt(theta + z * z)
    tail = t ** (count + 1)
    residual = abs(total - closed)
    assert residual <= tail + mp.mpf("1e-110")
    return residual, tail, count


def inverse_sqrt_identity(R2, eps, lam, m):
    U = eps + R2
    d = lam / (2 * U)
    C = 2 * R2 / (U - lam / 2)
    q = (1 - m / R2) / 2
    r = C * q
    slack = lam / (2 * U - lam)
    assert r >= 0
    assert r <= 1 - slack + mp.mpf("1e-115")
    direct = mp.sqrt(lam) / (2 * mp.sqrt(eps + m))
    pgf = mp.sqrt(d / (1 - (1 - d) * r)) / mp.sqrt(2)
    assert abs(direct - pgf) < mp.mpf("1e-110")
    return abs(direct - pgf)


def run():
    derivative_cases = []
    min_derivative_ratio = mp.inf
    min_scale_ratio = mp.inf
    min_fixed_grid_derivative_ratio = mp.inf
    min_fixed_grid_scale_ratio = mp.inf
    for T in (2, 3, 4, 8, 16, 32, 64, 128, 256):
        eps_values = (
            mp.mpf(0),
            mp.mpf(2) ** -20,
            mp.mpf(1) / T,
            1 / mp.sqrt(T),
            mp.mpf("0.01"),
            mp.mpf(1),
        )
        for eps in eps_values:
            derivative_ratio, scale_ratio = exact_binomial_derivative(T, eps)
            min_derivative_ratio = min(min_derivative_ratio, derivative_ratio)
            min_scale_ratio = min(min_scale_ratio, scale_ratio)
            fixed_d, fixed_s = fixed_grid_derivative(T, eps)
            min_fixed_grid_derivative_ratio = min(min_fixed_grid_derivative_ratio, fixed_d)
            min_fixed_grid_scale_ratio = min(min_fixed_grid_scale_ratio, fixed_s)
            derivative_cases.append({"T": T, "epsilon": str(eps)})

    max_majority_error = mp.mpf(0)
    max_terms = 0
    majority_cases = 0
    for theta in (mp.mpf(1) / 64, mp.mpf(1) / 8, mp.mpf(1) / 2, mp.mpf(1), mp.mpf(4), mp.mpf(128)):
        for z in (mp.mpf(-1), mp.mpf("-0.7"), mp.mpf(0), mp.mpf("0.3"), mp.mpf(1)):
            error, tail, terms = geometric_majority(theta, z)
            max_majority_error = max(max_majority_error, error)
            max_terms = max(max_terms, terms)
            majority_cases += 1

    floor_cases = 0
    max_floor_error = mp.mpf(0)
    for R2 in (mp.mpf(1) / 16, mp.mpf(1), mp.mpf(16)):
        for eps in (mp.mpf(0), R2 / 256, R2 / 4, R2, 4 * R2):
            for floor_fraction in (mp.mpf(1) / 16, mp.mpf(1) / 2, mp.mpf(1)):
                lam = max(eps, floor_fraction * (eps + R2))
                lower_m = max(mp.mpf(0), lam - eps)
                for interpolation in (mp.mpf(0), mp.mpf(1) / 3, mp.mpf(1)):
                    m = lower_m + interpolation * (R2 - lower_m)
                    error = inverse_sqrt_identity(R2, eps, lam, m)
                    max_floor_error = max(max_floor_error, error)
                    floor_cases += 1

    results = {
        "status": "all finite checks passed",
        "decimal_precision": mp.mp.dps,
        "scope": "deterministic finite formula checks; no proof or sampler benchmark",
        "finite_population_derivative_cases": len(derivative_cases),
        "minimum_derivative_over_proved_lower_bound": mp.nstr(min_derivative_ratio, 50),
        "minimum_score_lower_certificate_over_min_T_inverse_epsilon": mp.nstr(min_scale_ratio, 50),
        "fixed_grid_width_four_score_cases": len(derivative_cases),
        "minimum_fixed_grid_derivative_over_proved_lower_bound": mp.nstr(
            min_fixed_grid_derivative_ratio, 50
        ),
        "minimum_fixed_grid_score_certificate_over_min_T_inverse_epsilon": mp.nstr(
            min_fixed_grid_scale_ratio, 50
        ),
        "geometric_majority_cases": majority_cases,
        "maximum_geometric_majority_truncation_error": mp.nstr(max_majority_error, 50),
        "maximum_terms_in_geometric_majority_check": max_terms,
        "floor_factory_algebra_cases": floor_cases,
        "maximum_floor_factory_algebra_residual": mp.nstr(max_floor_error, 50),
    }
    destination = Path(__file__).with_suffix(".json")
    destination.write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    run()
