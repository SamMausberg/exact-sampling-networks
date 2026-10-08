"""Supplementary finite-rational checks; not a proof or decoder benchmark."""

import json
from fractions import Fraction
from pathlib import Path

import mpmath as mp

mp.mp.dps = 450


def down(x, bits):
    return Fraction(int(mp.floor(x * mp.mpf(2) ** bits)), 1 << bits)


def up(x, bits):
    return Fraction(int(mp.ceil(x * mp.mpf(2) ** bits)), 1 << bits)


def mpq(x):
    return mp.mpf(x.numerator) / x.denominator


def ceil_log2_integer(x):
    return (x - 1).bit_length()


frequencies = [
    ("one_third", mp.mpf(1) / 3, 2),
    ("negative", -mp.mpf(11) / 9, 3),
    ("sqrt_two", mp.sqrt(2), 3),
    ("two_pi", 2 * mp.pi, 8),
    ("negative_two_pi", -2 * mp.pi, 8),
    ("large_rational", mp.mpf(1000001) / 7, 142859),
]
positions = [1, 2, 17, 10**6, 1 << 80, (1 << 200) + 123]
precisions = [2, 32, 120]
checks = []
nontrue_period_quotients = 0
max_error_ratio = mp.mpf(0)
for name, omega, c in frequencies:
    for t in positions:
        for p in precisions:
            omega_bits = p + 10 + ceil_log2_integer(t + 1)
            pi_bits = p + 10 + ceil_log2_integer(c * (t + 1))
            omega0 = down(omega, omega_bits)
            theta0 = t * omega0
            pi0 = up(mp.pi, pi_bits)
            k = theta0 // (2 * pi0)
            u0 = theta0 - 2 * k * pi0
            assert 0 <= u0 < 8
            assert abs(k) <= c * (t + 1)
            u = t * omega - 2 * k * mp.pi
            phase_error = abs(u - mpq(u0))
            delta = mp.mpf(2) ** (-p - 10)
            assert phase_error <= 3 * delta + mp.mpf("1e-300")
            sine_error = abs(mp.sin(t * omega) - mp.sin(mpq(u0)))
            cosine_error = abs(mp.cos(t * omega) - mp.cos(mpq(u0)))
            assert max(sine_error, cosine_error) <= 3 * delta + mp.mpf("1e-300")
            ratio = phase_error / delta
            max_error_ratio = max(max_error_ratio, ratio)
            if name == "two_pi" and k != t:
                nontrue_period_quotients += 1
            if name == "negative_two_pi" and k != -t:
                nontrue_period_quotients += 1
            checks.append(
                {
                    "frequency": name,
                    "position_bits": t.bit_length(),
                    "precision": p,
                    "phase_error_over_delta": mp.nstr(ratio, 20),
                }
            )
result = {
    "status": "all passed",
    "kind": "supplementary invariant checks, not proof or benchmark",
    "mpmath_decimal_precision": mp.mp.dps,
    "cases": len(checks),
    "period_boundary_cases_with_nontrue_quotient": nontrue_period_quotients,
    "max_phase_error_over_delta": mp.nstr(max_error_ratio, 40),
    "proven_bound_phase_error_over_delta": 3,
    "checks": checks,
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: v for k, v in result.items() if k != "checks"}, indent=2))
