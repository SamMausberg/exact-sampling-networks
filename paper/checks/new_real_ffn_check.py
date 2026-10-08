"""120-digit deterministic checks; not proof certificates or benchmarks."""

import json
import math
from pathlib import Path

import mpmath as mp

mp.mp.dps = 120
eps = mp.mpf("1e-106")
counts = dict(
    activation_identity=0,
    affine_identity=0,
    normalized_comparison=0,
    head_comparison=0,
    score_bound=0,
    full_cube_floor=0,
)


def require(test, message):
    if not test:
        raise AssertionError(message)


def gelu(x):
    return x * (1 + mp.erf(x / mp.sqrt(2))) / 2


def silu(x):
    return x / (1 + mp.exp(-x))


for name, phi in [("gelu", gelu), ("silu", silu)]:
    for k in range(-100, 101):
        x = mp.mpf(k) / 13
        require(abs(phi(x) - phi(-x) - x) < eps, ("activation identity", name, k))
        counts["activation_identity"] += 1
for C in map(mp.mpf, ["1.01", "1.5", "2", "10", "1000"]):
    a = (C - 1) / (2 * C)
    D = 2 * C / (C + 1)
    E = (C + 1) / 2
    for k in range(-50, 51):
        z = mp.mpf(k) / (100 * C)
        p = (1 + z) / 2
        r = 1 - D * (1 - p)
        require(abs(E * r - (1 + C * z) / 2) < eps, "two Huber identity")
        require(D * (1 - p) <= 1 - 1 / (2 * (C + 1)) + eps, "first Huber slack")
        require(mp.mpf(".25") - eps <= E * r <= mp.mpf(".75") + eps, "second Huber slack")
        counts["affine_identity"] += 1
records = []
for name, phi in [("gelu", gelu), ("silu", silu)]:
    carrier_speed = phi(1)
    for alpha in map(mp.mpf, ["1", ".25", ".0625"]):
        for tau in map(mp.mpf, [4, 8, 16]):
            depth = int(tau / alpha)
            j0 = int(mp.ceil(3 / alpha))
            radius = 1 + tau
            for gain in map(mp.mpf, [2, 4]):
                delta = gain - 1
                C = gain / (4 * delta)
                G = mp.mpf(1)
                for j in range(j0, depth):
                    G *= 1 + delta * alpha / (1 + alpha * (j + 1))
                require(G + eps >= mp.exp(-(delta**2) / 8) * (radius / 6) ** delta, "product bound")
                for width in [4, 7, 16]:
                    N = 2 ** int(math.floor(math.log2(width / 2)))
                    eta = mp.mpf(N) / width

                    def recurrence(z):
                        F = z
                        carrier = mp.mpf(-1)
                        for j in range(depth):
                            v = 3 + eta * (1 - z * z + F * F) + (1 - eta) * carrier * carrier
                            F += alpha * gain * F / mp.sqrt(v)
                            carrier -= alpha * carrier_speed
                        v = 3 + eta * (1 - z * z + F * F) + (1 - eta) * carrier * carrier
                        return F, v

                    for z in map(mp.mpf, ["0", ".000001", ".01", ".1", ".5", "1"]):
                        F, v = recurrence(z)
                        u = F / radius
                        bound = G * z / (5 * mp.sqrt(1 + C * (G * G - 1) * z * z / 25))
                        require(u + eps >= bound, ("growth", name, alpha, tau, gain, width, z))
                        counts["normalized_comparison"] += 1
                        L = 4 * mp.sqrt(v)
                        A = (F - z) / L
                        k = 1 / L
                        out = (1 + z) / 2 * mp.tanh(A + k) + (1 - z) / 2 * mp.tanh(A - k)
                        require(
                            out + eps >= u / (32 * (gain + 1)),
                            ("head", name, alpha, tau, gain, width, z),
                        )
                        require(
                            abs(A + k) <= 1 + eps and abs(A - k) <= 1 + eps, "head argument bound"
                        )
                        counts["head_comparison"] += 1
                    score = mp.mpf(0)
                    for positive in range(N + 1):
                        z = mp.mpf(2 * positive - N) / N
                        F, v = recurrence(z)
                        L = 4 * mp.sqrt(v)
                        A = (F - z) / L
                        k = 1 / L
                        out = (1 + z) / 2 * mp.tanh(A + k) + (1 - z) / 2 * mp.tanh(A - k)
                        prob = mp.mpf(math.comb(N, positive)) / mp.mpf(2) ** N
                        score += prob * N * z * out
                    lower = G / (160 * (gain + 1) * mp.sqrt(1 + 3 * C * G * G / (25 * N)))
                    require(score + eps >= lower, ("score", name, alpha, tau, gain, width))
                    counts["score_bound"] += 1
                    records.append(
                        dict(
                            activation=name,
                            alpha=str(alpha),
                            effective_depth=str(tau),
                            gain=str(gain),
                            width=width,
                            actual_score=mp.nstr(score, 25),
                            proved_score=mp.nstr(lower, 25),
                        )
                    )
    for i in range(1001):
        tau = mp.mpf(i) / 20
        carrier_abs = max(mp.mpf(0), tau * carrier_speed - 1)
        require(3 + carrier_abs**2 / 2 >= (1 + tau) ** 2 / 12, "whole cube floor")
        counts["full_cube_floor"] += 1
result = dict(
    precision_decimal_digits=120,
    all_checks_passed=True,
    status="deterministic consistency checks only",
    case_counts=counts,
    total_cases=sum(counts.values()),
    scores=records,
)
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: v for k, v in result.items() if k != "scores"}))
