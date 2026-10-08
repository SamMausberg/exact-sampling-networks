"""120-digit checks for uniform-step, fixed-epsilon additive lower bounds.
These finite checks are not proof certificates or sampler benchmarks.
"""

import json
import math
from pathlib import Path

import mpmath as mp

mp.mp.dps = 120
margin = mp.mpf("1e-108")
counts = {
    "full_domain_floor": 0,
    "normalized_comparison": 0,
    "conditional_head": 0,
    "score_bound": 0,
    "growth_product": 0,
}


def req(b, m):
    if not b:
        raise AssertionError(m)


t0 = mp.tanh(1)
for i in range(1001):
    tau = mp.mpf(i) / 20
    R = 1 + tau
    least_abs = max(mp.mpf(0), tau * t0 - 1)
    req(3 + least_abs**2 / 2 >= R * R / 12, ("full floor", str(tau)))
    counts["full_domain_floor"] += 1
records = []
for alpha in map(mp.mpf, ["1", "0.5", "0.25", "0.0625"]):
    for tau in map(mp.mpf, [4, 8, 16]):
        D = int(tau / alpha)
        j0 = int(mp.ceil(2 / alpha))
        RD = 1 + alpha * D
        L = mp.mpf(2) ** int(mp.ceil(mp.log(RD, 2)))
        for s in map(mp.mpf, ["1.25", "2", "4"]):
            delta = s - 1
            C = s * (s * s + mp.mpf(".5")) / (2 * delta)
            G = mp.mpf(1)
            for j in range(j0, D):
                G *= 1 + delta * alpha / (1 + alpha * (j + 1))
            lowerG = mp.exp(-delta * delta / 6) * ((1 + tau) / 5) ** delta
            req(G + margin >= lowerG, "G lower")
            counts["growth_product"] += 1

            def update(z):
                F = z
                carrier = mp.mpf(-1)
                for j in range(D):
                    v = 3 + (1 - z * z + F * F + carrier * carrier) / 2
                    F += alpha * mp.tanh(s * F / mp.sqrt(v))
                    carrier -= alpha * t0
                v = 3 + (1 - z * z + F * F + carrier * carrier) / 2
                return F, carrier, v

            for z in map(mp.mpf, ["0", ".00001", ".01", ".1", ".5", "1"]):
                F, carrier, v = update(z)
                u = F / RD
                lower = G * z / (4 * mp.sqrt(1 + C * (G * G - 1) * z * z / 16))
                req(u + margin >= lower, "normalized comparison")
                counts["normalized_comparison"] += 1
                for mode in ("coordinate", "final_norm"):
                    denom = L if mode == "coordinate" else 4 * mp.sqrt(v)
                    A = (F - z) / denom
                    k = 1 / denom
                    out = (1 + z) / 2 * mp.tanh(A + k) + (1 - z) / 2 * mp.tanh(A - k)
                    req(out + margin >= u / (8 if mode == "coordinate" else 32), "head comparison")
                    counts["conditional_head"] += 1
            for N in (2, 4, 8, 16):
                derivatives = {"coordinate": mp.mpf(0), "final_norm": mp.mpf(0)}
                for pos in range(N + 1):
                    z = mp.mpf(2 * pos - N) / N
                    F, carrier, v = update(z)
                    probability = mp.mpf(math.comb(N, pos)) / mp.mpf(2) ** N
                    for mode in derivatives:
                        denom = L if mode == "coordinate" else 4 * mp.sqrt(v)
                        A = (F - z) / denom
                        k = 1 / denom
                        out = (1 + z) / 2 * mp.tanh(A + k) + (1 - z) / 2 * mp.tanh(A - k)
                        derivatives[mode] += probability * N * z * out
                for mode, derivative in derivatives.items():
                    pref = 32 if mode == "coordinate" else 128
                    bound = G / (pref * mp.sqrt(1 + 3 * C * G * G / (16 * N)))
                    req(derivative + margin >= bound, "score derivative")
                    counts["score_bound"] += 1
                    records.append(
                        {
                            "alpha": str(alpha),
                            "effective_depth": str(tau),
                            "gain": str(s),
                            "input_bits": N,
                            "head": mode,
                            "actual_score": mp.nstr(derivative, 25),
                            "proved_score": mp.nstr(bound, 25),
                        }
                    )
result = {
    "precision_decimal_digits": 120,
    "status": "deterministic consistency checks only",
    "all_checks_passed": True,
    "case_counts": counts,
    "total_cases": sum(counts.values()),
    "scores": records,
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: v for k, v in result.items() if k != "scores"}))
