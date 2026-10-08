"""Deterministic interval-mass checks at 120 digits; not a proof."""

import json
from pathlib import Path

import mpmath as mp

mp.mp.dps = 120
count = 0
for V in [2, 3, 5, 17, 64]:
    for multiple in [1, 4, 64, 4096]:
        H = V * multiple
        delta = mp.mpf(2) ** (-int(mp.ceil(mp.log(4 * H, 2))))
        for seed in range(10):
            logits = [mp.sin(mp.mpf((seed + 1) * (k + 1))) for k in range(V)]
            masses = [mp.exp(z) for z in logits]
            total = sum(masses)
            p = [v / total for v in masses]
            t = int(mp.ceil(mp.log(V / delta, 2))) + 2
            grid = mp.mpf(2) ** t
            lower = [mp.floor(grid * v) / grid for v in p]
            a = [(1 - delta) * v for v in lower]
            r = 1 - sum(a)
            assert delta <= r <= 2 * delta
            assert r * H <= mp.mpf(".5")
            residual = [(p[k] - a[k]) / r for k in range(V)]
            assert abs(sum(residual) - 1) < mp.mpf("1e-105")
            for k in range(V):
                assert a[k] <= p[k]
                assert abs(a[k] + r * residual[k] - p[k]) < mp.mpf("1e-105")
                count += 1
            for j in range(8):
                prec = int(mp.ceil(mp.log(16 * V * V / delta, 2))) + j
                width = V * mp.mpf(2) ** (-prec) / r
                assert width <= mp.mpf(2) ** (-j) / (16 * V)
                count += 1
result = dict(
    precision_decimal_digits=120,
    all_checks_passed=True,
    total_cases=count,
    status="deterministic consistency checks only",
)
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result))
