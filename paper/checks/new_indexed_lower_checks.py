"""Deterministic checks of indexed-attention reduction identities.

These are finite formula checks, not proofs, certified interval arithmetic,
an implementation of an exact sampler, or a runtime benchmark.
Requires mpmath.  Run beside the accompanying .json output.
"""

import json
import random
from fractions import Fraction
from pathlib import Path

import mpmath as mp

mp.mp.dps = 120
rng = random.Random(20261008)
counts = {
    "ov_score_identities": 0,
    "hamming_score_identities": 0,
    "network_map_identities": 0,
    "token_gap_checks": 0,
    "bucket_exponent_checks": 0,
    "prenorm_checks": 0,
}
max_error = mp.mpf(0)


def log2ceil_int(x):
    return (x - 1).bit_length()


def token(u):
    return (1 + mp.tanh(mp.tanh(u))) / 2


# All binary pairs through dimension eight.  Arithmetic here is exact.
for d in range(1, 9):
    m = 2**d + 3
    L = log2ceil_int(16 * m)
    root_n = d * L
    repeat = d * L * L
    assert d * repeat == root_n * root_n
    for a in range(2**d):
        for b in range(2**d):
            overlap = (a & b).bit_count()
            assert Fraction(-repeat * overlap, root_n) == -L * overlap
            counts["ov_score_identities"] += 1

# Literal source-row realization of the OV construction, including the
# current position's zero key and negative dummy value.
for d in range(1, 17):
    for _ in range(40):
        a = [rng.choice([0, 1]) for _ in range(d)]
        b = [rng.choice([0, 1]) for _ in range(d)]
        cache = [2 * x - 1 for x in a] + [-1] * d + [1, 1]
        query = [-1] * d + [2 * x - 1 for x in b] + [1, -1]
        key = [Fraction(-cache[i] - cache[2 * d], 2) for i in range(d)]
        query_key = [Fraction(-query[i] - query[2 * d], 2) for i in range(d)]
        q = [Fraction(query[d + i] + query[2 * d], 2) for i in range(d)]
        assert key == [-x for x in a]
        assert query_key == [0] * d
        assert q == b
        assert cache[-1] == 1 and query[-1] == -1
        counts["network_map_identities"] += 1

# Hamming gap construction.  Both the threshold padding and the standard
# scaling identities are evaluated exactly with Fraction.
for d in range(2, 65):
    for _ in range(80):
        a = [rng.choice([0, 1]) for _ in range(d)]
        b = [rng.choice([0, 1]) for _ in range(d)]
        t = rng.randrange(0, d + 1)
        H = rng.randrange(1, 12)
        base_k = [2 * x - 1 for x in a] + [1] * t + [-1] * (d - t)
        base_q = [2 * x - 1 for x in b] + [1] * d
        distance = sum(x != y for x, y in zip(a, b))
        dot = sum(x * y for x, y in zip(base_k, base_q))
        assert dot == 2 * (t - distance)
        repeat, root_n = 2 * d * H * H, 2 * d * H
        assert 2 * d * repeat == root_n * root_n
        assert Fraction(repeat * dot, root_n) == 2 * H * (t - distance)
        counts["hamming_score_identities"] += 1

# 120-digit checks of weights and final-token separation.  Include actual
# collections and the extremal upper bound W = 1/16.
for m in [1, 2, 3, 7, 16, 63, 257, 1024, 65537]:
    L = log2ceil_int(16 * m)
    worst_no = mp.mpf(m) * mp.exp(-L)
    assert worst_no <= mp.mpf(1) / 16
    for W in [mp.mpf(0), worst_no, mp.mpf(1) / 16, mp.mpf(1), mp.mpf(2), mp.mpf(m + 1)]:
        u = (W - 1) / (W + 1)
        p = token(u)
        if W <= mp.mpf(1) / 16:
            assert u <= -mp.mpf(15) / 17
            assert p <= mp.mpf(1) / 2 - mp.mpf(15) / 136
        if W >= 1:
            assert u >= 0 and p >= mp.mpf(1) / 2
        # Formula from a direct two-logit softmax.
        z = mp.tanh(u)
        direct = mp.exp(z) / (mp.exp(z) + mp.exp(-z))
        max_error = max(max_error, abs(direct - p))
        assert abs(direct - p) < mp.mpf("1e-115")
        counts["token_gap_checks"] += 1

# Positive stabilizers and the additive head preserve a constant gap.
for eps in [mp.mpf(0), mp.mpf("0.00001"), mp.mpf("0.1"), mp.mpf(1)]:
    scale = 1 / mp.sqrt(1 + eps)
    for W in [mp.mpf(0), mp.mpf(1) / 32, mp.mpf(1) / 16, mp.mpf(1), mp.mpf(2)]:
        u = scale * (W - 1) / (W + 1)
        head = ((-1 + u) + 1) / 4
        p = (1 + mp.tanh(head)) / 2
        assert abs(head - u / 4) < mp.mpf("1e-115")
        if W <= mp.mpf(1) / 16:
            assert p < mp.mpf(7) / 16
        if W >= 1:
            assert p >= mp.mpf(1) / 2
        counts["prenorm_checks"] += 1

# Exact rational exponent comparisons used to absorb polynomial prefill.
for a in range(1, 33):
    gamma = Fraction(1, 2 * (a + 1))
    for eps in [Fraction(1, 100), Fraction(1, 8), Fraction(1, 2), Fraction(99, 100)]:
        pre = 1 + gamma * (a - 1)
        query = 2 - gamma * eps
        final = 2 - gamma * eps / 2
        assert pre < Fraction(3, 2) < query < final < 2
        counts["bucket_exponent_checks"] += 1

report = {
    "status": "all deterministic checks passed",
    "precision_decimal_digits": mp.mp.dps,
    "random_seed_for_fixed_case_selection": 20261008,
    "counts": counts,
    "total_checks": sum(counts.values()),
    "largest_recorded_softmax_identity_error": str(max_error),
    "boundary_no_token_probability": str(token(-mp.mpf(15) / 17)),
    "boundary_yes_token_probability": "0.5",
    "scope": "finite formula checks; not proofs or sampler benchmarks",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
