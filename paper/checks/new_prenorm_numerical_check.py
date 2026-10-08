"""Deterministic checks at 120 decimal digits. Not a proof or benchmark."""

import json
import math
from fractions import Fraction
from pathlib import Path

import mpmath as mp

mp.mp.dps = 120
results = {
    "precision_decimal_digits": mp.mp.dps,
    "status": "deterministic consistency checks only",
    "formalization": "Lean file is uncompiled",
}
count = {
    "growth_inequalities": 0,
    "mean_amplification": 0,
    "score_lower_bounds": 0,
    "origin_mass": 0,
    "composition_products": 0,
    "bit_charge_recurrence": 0,
    "relative_parameters": 0,
}


def demand(test, label):
    if not test:
        raise AssertionError(label)


def increment(y, family):
    denominator = mp.sqrt(3 + y * y) if family == "query" else mp.sqrt(mp.mpf(11) / 3 + y * y / 3)
    return mp.tanh(y / denominator)


for family in ("query", "context"):
    for i in range(1001):
        y = mp.mpf(i) / 1000
        demand(increment(y, family) + mp.mpf("1e-110") >= y / 4, (family, "small", str(y)))
        count["growth_inequalities"] += 1
    for y in map(mp.mpf, [1, 2, 3, 5, 10, 100, 10000]):
        demand(increment(y, family) >= mp.mpf(1) / 4, (family, "large", str(y)))
        count["growth_inequalities"] += 1

summary = []
for N in (2, 3, 4, 8, 16, 32, 64, 128, 256, 512):
    k = int(mp.ceil(mp.log(2 * mp.sqrt(N)) / mp.log(mp.mpf(5) / 4)))
    d = 1 << (2 * k - 1).bit_length()
    for family in ("query", "context"):

        def F(z):
            for _ in range(d):
                z += increment(z, family)
            return z

        threshold = mp.mpf(1) / (2 * mp.sqrt(N))
        Fthreshold = F(threshold)
        demand(Fthreshold >= mp.mpf(d) / 8, (family, N, "threshold"))
        count["mean_amplification"] += 1
        derivative = mp.mpf(0)
        for positive in range(N + 1):
            z = mp.mpf(2 * positive - N) / N
            v = F(z)
            demand(abs(v) <= 2 * d, (family, N, "bounded logits"))
            g = mp.tanh(v / (2 * d))
            if z >= threshold:
                demand(g >= mp.mpf(1) / 32, (family, N, "gate amplitude"))
            derivative += mp.mpf(math.comb(N, positive)) / mp.mpf(2) ** N * N * z * g
            count["mean_amplification"] += 1
        bound = 3 * mp.sqrt(N) / 1024
        demand(derivative >= bound, (family, N, "score"))
        demand(derivative**2 >= mp.mpf(N) / 2**17, (family, N, "queries"))
        count["score_lower_bounds"] += 1
        summary.append(
            {
                "family": family,
                "input_bits": N,
                "amplification_steps": d,
                "score_derivative": mp.nstr(derivative, 35),
                "score_query_lower": mp.nstr(derivative**2, 35),
                "proved_query_lower": mp.nstr(mp.mpf(N) / 2**17, 35),
            }
        )

for length in (1, 2, 3, 10, 100):
    for scale in (Fraction(1, 8), Fraction(1), Fraction(4)):
        updates = [scale * Fraction(1 + j % 3, 1 + j % 5) for j in range(length)]
        radii = [Fraction(1)]
        for u in updates:
            radii.append(radii[-1] + u)
        for j in range(1, length + 1):
            weights = [Fraction(1, radii[j])] + [u / radii[j] for u in updates[:j]]
            demand(sum(weights) == 1, (length, str(scale), j, "origin mass"))
            for k in range(1, j + 1):
                identity = Fraction(1)
                for r in range(k + 1, j + 1):
                    identity *= radii[r - 1] / radii[r]
                demand(
                    identity * updates[k - 1] / radii[k] == updates[k - 1] / radii[j],
                    "origin telescope",
                )
            count["origin_mass"] += 1
        for m in (Fraction(1), Fraction(3, 2), Fraction(2), Fraction(11)):
            L = Fraction(3, 2)
            c = m + L + 1
            P = Fraction(1)
            leaf = Fraction(1)
            costs = [Fraction(1)]
            for j in range(1, length + 1):
                P *= 1 + updates[j - 1] * c / radii[j - 1]
                leaf *= (radii[j - 1] + updates[j - 1] * m) / radii[j]
                # C0=B=1, one prefix draw plus terminal probe and update work.
                work = Fraction(1) + Fraction(1, radii[j])
                work += sum(
                    updates[k - 1] / radii[j] * (L + m * costs[k - 1]) for k in range(1, j + 1)
                )
                costs.append(work)
                demand(work <= 2 * P / radii[j], "bit charge induction")
                count["bit_charge_recurrence"] += 1

            def val(x):
                return mp.mpf(x.numerator) / x.denominator

            demand(
                mp.log(val(leaf)) <= (val(m) - 1) * mp.log(val(radii[-1])) + mp.mpf("1e-110"),
                "leaf power",
            )
            demand(
                mp.log(val(P)) <= val(c) * mp.log(val(radii[-1])) + mp.mpf("1e-110"), "work power"
            )
            count["composition_products"] += 1

for gamma in (mp.mpf(1), mp.mpf(1) / 2, mp.mpf(1) / 4, mp.mpf(1) / 100):
    G = mp.mpf(2) ** int(mp.ceil(mp.log(2 / mp.sqrt(gamma), 2)))
    demand(2 / mp.sqrt(gamma) <= G < 4 / mp.sqrt(gamma), "radius dyadic rounding")
    for s in (mp.mpf(0), mp.mpf(1) / 4, mp.mpf(1), mp.mpf(4)):
        for beta in (mp.mpf(0), mp.mpf(1) / 8, mp.mpf(1) / 2, mp.mpf(1)):
            k = 1 / gamma
            K = 1 + 228 * k * k
            E = mp.exp(2 * beta * s * s * G * G)
            rho = s * G
            mA = (2 * E - 1) * K
            LA = 4 * E * (1 + k**3)
            mF = 2 * rho * (1 + rho) * K
            LF = 4 * (1 + rho) ** 2 * (1 + k**3)
            demand(LA >= E + (2 * E - 1) * (1 + k**3), "attention local absorption")
            demand(LF >= (1 + rho) ** 2 + 2 * rho * (1 + rho) * (1 + k**3), "tanh local absorption")
            count["relative_parameters"] += 1

results["case_counts"] = count
results["total_cases"] = sum(count.values())
results["score_cases"] = summary
results["all_checks_passed"] = True
out = Path(__file__).with_suffix(".json")
out.write_text(json.dumps(results, indent=2) + "\n")
print(
    json.dumps(
        {"all_checks_passed": True, "total_cases": results["total_cases"], "case_counts": count}
    )
)
