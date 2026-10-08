"""120-digit consistency checks for the fixed-epsilon energy carrier.
The comparisons are deterministic numerical checks, not proof certificates.
"""

import json
import math
from pathlib import Path

import mpmath as mp

mp.mp.dps = 120
counts = {"comparison_and_floor_cases": 0, "score_cases": 0, "product_cases": 0}
margin = mp.mpf("1e-110")


def require(condition, label):
    if not condition:
        raise AssertionError(label)


def recurrence(z, D, s, eta):
    F = z
    carrier = mp.mpf(-1)
    t0 = mp.tanh(1)
    for j in range(D):
        R = j + 1
        if eta == mp.mpf(1) / 3:
            v = 3 + (1 + F * F + carrier * carrier) / 3
            floor = mp.mpf(R * R) / 12
        else:
            v = 3 + (F * F + carrier * carrier) / 2
            floor = mp.mpf(R * R) / 8
        require(v + margin >= floor, "relative floor")
        require(abs(F) <= R + margin and abs(carrier) <= R + margin, "radius")
        F += mp.tanh(s * F / mp.sqrt(v))
        carrier -= t0
    return F / (D + 1)


scores = []
for eta in (mp.mpf(1) / 3, mp.mpf(1) / 2):
    for s in (mp.mpf(4), mp.mpf(5), mp.mpf(8)):
        delta = s - 1
        C = s * (s * s + eta) / (2 * delta)
        for D in (2, 3, 7, 15, 31):
            G = mp.mpf(1)
            for j in range(2, D):
                G *= 1 + delta / (j + 2)
            lowerG = mp.exp(-delta * delta / 2) * ((mp.mpf(D) + 2) / 4) ** delta
            require(G + margin >= lowerG, "harmonic product")
            counts["product_cases"] += 1
            for z in map(mp.mpf, ["0", "0.000001", "0.001", "0.01", "0.1", "0.25", "0.5", "1"]):
                u = recurrence(z, D, s, eta)
                lower = G * (z / 3) / mp.sqrt(1 + C * (G * G - 1) * (z / 3) ** 2)
                require(u + margin >= lower, ("comparison", str(eta), str(s), D, str(z)))
                require(abs(u) <= 1 + margin, "head radius")
                counts["comparison_and_floor_cases"] += 1
            for N in (2, 4, 8, 16, 32, 64):
                derivative = mp.mpf(0)
                for pos in range(N + 1):
                    z = mp.mpf(2 * pos - N) / N
                    mean = mp.tanh(recurrence(z, D, s, eta))
                    derivative += N * z * mean * mp.mpf(math.comb(N, pos)) / mp.mpf(2) ** N
                proved = G / (6 * mp.sqrt(1 + C * G * G / (3 * N)))
                require(derivative + margin >= proved, "score derivative")
                bound = G * G / (36 * (1 + C * G * G / (3 * N)))
                require(derivative * derivative + margin >= bound, "query bound")
                weaker = min(G * G, N) / (36 * (1 + C / 3))
                require(bound + margin >= weaker, "minimum form")
                counts["score_cases"] += 1
                scores.append(
                    {
                        "eta": mp.nstr(eta, 15),
                        "gain": int(s),
                        "steps": D,
                        "input_bits": N,
                        "actual_score": mp.nstr(derivative, 30),
                        "proved_score": mp.nstr(proved, 30),
                    }
                )
result = {
    "precision_decimal_digits": 120,
    "all_checks_passed": True,
    "case_counts": counts,
    "total_cases": sum(counts.values()),
    "status": "deterministic consistency checks only",
    "scores": scores,
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: v for k, v in result.items() if k != "scores"}))
