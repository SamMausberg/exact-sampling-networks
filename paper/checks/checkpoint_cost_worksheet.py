#!/usr/bin/env python3
"""Construction-size worksheet for the exact-sampling paper.

This is not a sampler, a checkpoint verifier, or a timing model.
All supplied "certificate" bounds remain assumptions. The bundled input
is illustrative and contains no measurements from a trained model.

Usage:
  python checkpoint_cost_worksheet.py checkpoint_illustrative_input.json
  python checkpoint_cost_worksheet.py checkpoint_hadamard_input.json

Decimal strings and "numerator/denominator" strings are read exactly.
The feature and counter counts are exact integers. Reported logarithms
are display approximations. Rank-dependent proof constants are omitted
from the coarse work proxy, so that proxy is not a numerical runtime
upper bound or a prediction of seconds. The JSON key "product_Pi"
records the indexed additive product P_j in the paper.

An optional critical_tanh record reports supplied zero-bias and unit-row
certificates, and symbolic critical-sampling growth proxies. It can also
be supplied alone, with residual_width, depth, and parameter_bits at the
top level. Boolean zero_bias means a supplied certificate, not a check
performed by this program. Family-wide fixed-rank or fixed-envelope
certificates cannot be inferred from a single numerical instance.
"""

from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction
from pathlib import Path


def rational(value: object) -> Fraction:
    if isinstance(value, float):
        raise ValueError("Use a decimal string, not a binary JSON float.")
    return Fraction(str(value))


def ceil_fraction(value: Fraction) -> int:
    return -(-value.numerator // value.denominator)


def ceil_log2(value: Fraction | int) -> int:
    value = Fraction(value)
    if value <= 0:
        raise ValueError("A logarithm argument must be positive.")
    num, den = value.numerator, value.denominator
    exponent = num.bit_length() - den.bit_length()
    if exponent >= 0:
        return exponent + (num > den << exponent)
    return exponent + (num << (-exponent) > den)


def power_of_two(exponent: int) -> Fraction:
    return Fraction(1 << exponent) if exponent >= 0 else Fraction(1, 1 << -exponent)


def power_two_exponent(value: Fraction) -> int:
    def is_power_of_two(x: int) -> bool:
        return x > 0 and x & (x - 1) == 0

    if not (is_power_of_two(value.numerator) and is_power_of_two(value.denominator)):
        raise ValueError("Key and value scales must be positive powers of two.")
    return value.numerator.bit_length() - value.denominator.bit_length()


def sqrt_power_two_upper(value: Fraction) -> Fraction:
    return power_of_two(-(-ceil_log2(value) // 2))


def integer_summary(value: int) -> dict[str, object]:
    if value < 0:
        raise ValueError("Construction counts cannot be negative.")
    if value == 0:
        return {"exact": 0, "bit_length": 0}
    bits = value.bit_length()
    shift = max(0, bits - 60)
    log2_display = math.log2(value >> shift) + shift
    result: dict[str, object] = {
        "bit_length": bits,
        "log10_display_approx": log2_display / math.log2(10),
    }
    if bits <= 900:
        result["exact"] = str(value)
    return result


def exact_positive_integer(value: object, name: str, minimum: int = 1) -> int:
    if isinstance(value, bool):
        raise ValueError(f"{name} must be an integer, not a Boolean.")
    parsed = rational(value)
    if parsed.denominator != 1 or parsed < minimum:
        raise ValueError(f"{name} must be an integer at least {minimum}.")
    return parsed.numerator


def rational_radical_proxy(coefficient: Fraction, radicand: int) -> dict[str, object]:
    """Retain the exact algebraic expression; decimals are display only."""
    log10_value = (
        math.log10(coefficient.numerator)
        - math.log10(coefficient.denominator)
        + math.log10(radicand) / 2
    )
    result: dict[str, object] = {
        "rational_coefficient_exact": str(coefficient),
        "square_root_radicand_exact": radicand,
        "squared_value_exact": str(coefficient**2 * radicand),
        "log10_display_approx": log10_value,
    }
    if -300 < log10_value < 300:
        result["value_display_approx"] = 10**log10_value
    return result


def power_radical_proxy(
    base: int, exponent: int, radicand: int, prefactor: Fraction = Fraction(1)
) -> dict[str, object]:
    """Avoid constructing an enormous B**r integer just to display its size."""
    log10_value = (
        math.log10(prefactor.numerator)
        - math.log10(prefactor.denominator)
        + exponent * math.log10(base)
        + math.log10(radicand) / 2
    )
    result: dict[str, object] = {
        "integer_base_B": base,
        "integer_exponent": exponent,
        "square_root_radicand_exact": radicand,
        "rational_prefactor_exact": str(prefactor),
        "coefficient_exact_expression": f"({prefactor})*{base}^{exponent}",
        "log10_display_approx": log10_value,
    }
    if exponent * base.bit_length() <= 900:
        result["coefficient_exact"] = str(prefactor * base**exponent)
    if -300 < log10_value < 300:
        result["value_display_approx"] = 10**log10_value
    return result


def critical_tanh_summary(data: dict[str, object]) -> dict[str, object]:
    record = data["critical_tanh"]
    if not isinstance(record, dict):
        raise ValueError("critical_tanh must be a JSON object.")
    n = exact_positive_integer(record.get("n", data.get("residual_width")), "n", 2)
    depth = exact_positive_integer(record.get("D", data.get("depth")), "D")
    bits = exact_positive_integer(
        record.get("parameter_bits", data.get("parameter_bits")), "parameter_bits"
    )
    rank = exact_positive_integer(record["first_layer_rank"], "first_layer_rank", 0)
    if rank > n:
        raise ValueError("The square first-layer rank cannot exceed n.")
    zero_bias = record["zero_bias"]
    if not isinstance(zero_bias, bool):
        raise ValueError("zero_bias must be a Boolean supplied certificate.")
    row_norm = rational(record["row_norm_max"])
    column_envelope = rational(record["column_envelope"])
    if min(row_norm, column_envelope) < 0:
        raise ValueError("Row-norm and column-envelope bounds must be nonnegative.")
    family_flags = {}
    for key in ("first_layer_rank_is_uniform_constant", "column_envelope_is_uniform_constant"):
        flag = record.get(key)
        if flag is not None and not isinstance(flag, bool):
            raise ValueError(f"{key} must be Boolean when supplied.")
        family_flags[key] = flag
    conditions_hold = zero_bias and row_norm <= 1
    critical_bits = 16 + bits + ceil_log2(n * depth + 2)
    probe_factor = max(Fraction(1), column_envelope**2)
    probe_proxy = rational_radical_proxy(probe_factor, depth + 1)
    probe_proxy["formula"] = "max(1,C_col^2)*sqrt(D+1)"
    probe_proxy["omitted_constant"] = "An absolute proof constant; unfitted."
    choose_column = probe_factor**2 <= depth + 1
    selected_probe_proxy = (
        rational_radical_proxy(probe_factor, depth + 1)
        if choose_column
        else rational_radical_proxy(Fraction(depth + 1), 1)
    )
    selected_probe_proxy["formula"] = "min(D+1,max(1,C_col)^2*sqrt(D+1))"
    selected_probe_proxy["selected_construction"] = (
        "column-envelope sampler" if choose_column else "generic zero-bias sampler"
    )
    selected_probe_proxy["selection_comparison"] = {
        "K_col_fourth_power_exact": str(probe_factor**2),
        "D_plus_one": depth + 1,
    }
    selected_probe_proxy["omitted_constant"] = (
        "Absolute proof constants are unfitted; this compares asymptotic probe "
        "envelopes, not measured times or optimal instance complexity."
    )
    rank_exponent = max(4, rank + 2)
    fixed_rank_proxy = power_radical_proxy(critical_bits, rank_exponent, depth + 1)
    fixed_rank_proxy["formula"] = "sqrt(D+1)*B^max(4,r+2)"
    fixed_rank_proxy["omitted_constant"] = (
        "The rank-dependent proof constant C_r is omitted and unfitted. "
        "This is a uniform bound in width only with a family-wide fixed-rank certificate."
    )
    column_proxy = power_radical_proxy(critical_bits, 40, depth + 1)
    column_proxy["formula"] = "sqrt(D+1)*B^40"
    column_proxy["omitted_constant"] = (
        "The fixed-envelope factor and remaining absolute proof constant are omitted and "
        "unfitted. A family-wide bounded-envelope certificate is needed to omit K_col^7."
    )
    uniform_column_proxy = power_radical_proxy(
        critical_bits, 40, depth + 1, max(Fraction(1), column_envelope) ** 7
    )
    uniform_column_proxy["formula"] = "max(1,C_col)^7*sqrt(D+1)*B^40"
    uniform_column_proxy["omitted_constant"] = (
        "An absolute proof constant is omitted and unfitted. The arbitrary-radius majority "
        "implementation gives the displayed polynomial dependence on the column envelope."
    )
    result: dict[str, object] = {
        "certificate_status": record.get("certificate_status", "Unverified supplied certificates"),
        "interpretation": (
            "Symbolic sufficient upper-bound growth proxies, not an instance complexity law, "
            "a numerical work upper bound with fitted constants, or a practical runtime forecast."
        ),
        "n": n,
        "D": depth,
        "parameter_bits": bits,
        "first_layer_rank": rank,
        "row_norm_max_exact": str(row_norm),
        "column_envelope_exact": str(column_envelope),
        "supplied_zero_bias_certificate": zero_bias,
        "supplied_unit_row_certificate_holds": row_norm <= 1,
        "unit_row_zero_bias_conditions_hold": conditions_hold,
        "proxy_applicability": (
            "The supplied zero-bias and unit-row conditions hold; further theorem scope applies."
            if conditions_hold
            else "Inapplicable as critical-tanh bounds: the supplied zero-bias or unit-row condition fails."
        ),
        "depth_equals_ceil_log2_n": depth == ceil_log2(n),
        "preprocessing_scope": (
            "The stated original preprocessing budget uses D=ceil(log2 n) and b=O(log n). "
            "A single supplied b does not certify a family-wide asymptotic precision bound."
        ),
        "family_certificates": family_flags,
        "B": critical_bits,
        "B_definition": "16+b+ceil(log2(n*D+2))",
        "probe_envelope_without_absolute_constant": probe_proxy,
        "selected_probe_growth_proxy": selected_probe_proxy,
        "fixed_rank_bit_growth_proxy": fixed_rank_proxy,
        "bounded_column_bit_growth_proxy": column_proxy,
        "uniform_column_bit_growth_proxy": uniform_column_proxy,
    }
    if "descriptor" in record:
        result["illustrative_descriptor"] = record["descriptor"]
    return result


def calculate(data: dict[str, object]) -> dict[str, object]:
    if "critical_tanh" in data and "heads" not in data:
        return {
            "input_scope": data.get("scope", "Unverified supplied parameters"),
            "interpretation": (
                "Critical-tanh certificate arithmetic only. No checkpoint was verified "
                "and no timing is predicted."
            ),
            "critical_tanh": critical_tanh_summary(data),
        }
    n, depth, vocab, tokens, bits = (
        exact_positive_integer(data[key], key)
        for key in ("residual_width", "depth", "vocabulary_size", "cache_length", "parameter_bits")
    )
    if min(n, depth, vocab, tokens, bits) < 1:
        raise ValueError("All model-size inputs must be positive.")
    horizon = 1 << (tokens - 1).bit_length()
    p_token = ceil_log2(64 * vocab * (horizon + 2) ** 3)
    stages = [rational(x) for x in data["stage_error_factors_upper"]]
    if not stages or any(x < 0 for x in stages):
        raise ValueError("Supply the nonnegative stage error-factor certificates.")
    guard = (
        ceil_log2(len(stages) + 1)
        + sum(ceil_log2(max(Fraction(1), factor)) for factor in stages)
        + 10
    )
    precision = p_token + guard
    head_outputs = []
    all_counters = 0
    largest_degree = 0
    largest_rank = 0
    largest_grid = precision
    dimension_sum = n + vocab + 1
    for head in data["heads"]:
        d = exact_positive_integer(head["key_dimension"], "key_dimension")
        a = exact_positive_integer(head["value_dimension"], "value_dimension")
        rank = exact_positive_integer(head["certified_rank"], "certified_rank", 0)
        q, k, u, beta_upper = (
            rational(head[key])
            for key in ("query_bound", "key_scale", "value_scale", "temperature_upper")
        )
        if min(d, a) < 1 or not 0 <= rank <= d:
            raise ValueError("Invalid head dimensions or rank.")
        if min(q, k, u) <= 0 or beta_upper < 0:
            raise ValueError("Invalid coordinate bounds or temperature.")
        if head.get("standard_scaling", False):
            if not d <= beta_upper * beta_upper <= 4 * d:
                raise ValueError("temperature_upper must lie between sqrt(d) and 2sqrt(d).")
        k_exponent, u_exponent = power_two_exponent(k), power_two_exponent(u)
        coefficient_bound = ceil_fraction(max(Fraction(1), 2 * rank * beta_upper * q * k))
        attention_precision = precision + ceil_log2(max(Fraction(1), u)) + 4
        degree = 8 * (attention_precision + 3 * coefficient_bound + 7)
        feature_count = math.comb(degree + rank, rank)
        counters = (a + 1) * feature_count
        grid_precision = precision + bits + abs(k_exponent) + abs(u_exponent)
        numerator_bits_proxy = grid_precision * (degree + 1) + ceil_log2(tokens + 2) + 2
        if beta_upper == 0 or rank == 0:
            cell_bound = 1
        else:
            cell_bound = min(
                tokens, ceil_fraction((rank + 1) * (5 + 32 * rank * beta_upper * q * k) ** rank)
            )
        head_output = {
            "name": head.get("name", "unnamed illustrative head"),
            "certificate_status": head.get("certificate_status", "unverified input"),
            "H_upper": coefficient_bound,
            "attention_precision": attention_precision,
            "degree_m": degree,
            "features_N_m": integer_summary(feature_count),
            "integer_counters_per_precision_index": integer_summary(counters),
            "counter_numerator_bits_proxy": numerator_bits_proxy,
            "cell_count_upper": cell_bound,
            "query_size_proxy_without_B4_or_rank_constant": d + cell_bound + ceil_log2(tokens + 2),
        }
        if "finite_record_bits" in head:
            record_bits = int(head["finite_record_bits"])
            if record_bits < 1:
                raise ValueError("finite_record_bits must be positive.")
            index_bits = 16 + record_bits + ceil_log2(tokens + d + a + rank + 2)
            head_output["finite_cache_B"] = index_bits
            head_output["finite_cache_query_proxy_without_rank_constant"] = integer_summary(
                (d + cell_bound + ceil_log2(tokens + 2)) * index_bits**4
            )
            head_output["finite_cache_vector_append_proxy_without_rank_constant"] = integer_summary(
                (d + a + ceil_log2(tokens + 2)) * index_bits**3
            )
        else:
            head_output["finite_cache_B"] = "Supply the finite record encoding length separately."
        if "projection_residual_eta" in head:
            residual = rational(head["projection_residual_eta"])
            if residual < 0:
                raise ValueError("A residual bound must be nonnegative.")
            head_output["supplied_residual_meets_index_threshold"] = (
                beta_upper * q * residual <= Fraction(1, 8)
            )
            head_output["residual_threshold_scope"] = (
                "The arithmetic condition only; the supplied residual certificate was not verified."
            )
        head_outputs.append(head_output)
        all_counters += counters
        largest_degree = max(largest_degree, degree)
        largest_rank = max(largest_rank, rank)
        largest_grid = max(largest_grid, grid_precision)
        dimension_sum += d + a
    dimension_sum += sum(int(x) for x in data.get("feedforward_widths", []))
    length_base = (
        largest_degree
        * (largest_grid + bits + ceil_log2(dimension_sum + largest_degree + depth + 2))
        + ceil_log2(tokens + 2)
        + 1
    )
    coarse_proxy = (
        (depth + 1)
        * dimension_sum**2
        * (largest_degree + 1) ** (2 * largest_rank + 4)
        * length_base**4
    )
    output: dict[str, object] = {
        "input_scope": data.get("scope", "Unverified supplied parameters"),
        "interpretation": (
            "Construction sizes and an asymptotic growth proxy only. "
            "No checkpoint certificate has been verified and no timing is predicted."
        ),
        "precision_horizon": horizon,
        "routine_categorical_precision": p_token,
        "stage_guard_bits": guard,
        "working_precision_P": precision,
        "heads": head_outputs,
        "total_counters_per_precision_index": integer_summary(all_counters),
        "coarse_tanh_work_proxy": integer_summary(coarse_proxy),
        "omitted_proof_factor": (
            "The rank-dependent constants C_r in the token and integer-length bounds; "
            "routine and rare-replay factors still need the implementation's actual cost."
        ),
        "fixed_tanh_precision_polynomial_degree": 2 * largest_rank + 12,
        "routine_token_passes_per_step_upper": 3,
    }
    if "normalization" in data:
        norm = data["normalization"]
        radius, epsilon, floor = (
            rational(norm[key]) for key in ("input_radius", "epsilon", "certified_squared_floor")
        )
        if radius <= 0 or epsilon <= 0 or floor <= 0:
            raise ValueError("This worksheet uses positive RMS parameters.")
        floor = max(floor, epsilon)
        if floor > epsilon + radius**2:
            raise ValueError(
                "The supplied floor exceeds the possible denominator-square upper bound."
            )
        kappa = max(Fraction(1), radius**2 / floor)
        ceil_sqrt_n = math.isqrt(n) + (math.isqrt(n) ** 2 < n)
        output["normalization"] = {
            "certificate_status": norm.get("certificate_status", "unverified input"),
            "kappa": str(kappa),
            "relative_floor_gamma": str(floor / radius**2),
            "floor_factory_source_bound": str(1 + 228 * kappa**2),
            "floor_factory_radius_power_two_upper": str(
                sqrt_power_two_upper(4 * radius**2 / floor)
            ),
            "rms_error_factor_power_two_upper": str(
                sqrt_power_two_upper(Fraction((1 + ceil_sqrt_n) ** 2) / floor)
            ),
        }
    if "additive_updates" in data:
        initial_radius = rational(data.get("additive_initial_radius", "1"))
        if initial_radius <= 0:
            raise ValueError("The additive initial radius must be positive.")
        radius, product, work_sum = initial_radius, Fraction(1), 2 * initial_radius
        for update in data["additive_updates"]:
            increment, sources, local = (
                rational(update[key])
                for key in ("radius_increment", "source_bound", "local_arithmetic_factor")
            )
            if min(increment, sources, local) < 0:
                raise ValueError("Additive work certificates must be nonnegative.")
            product *= 1 + increment * sources / radius
            radius += increment
            work_sum += increment * (1 + local) / product
        output["additive"] = {
            "radius_R": str(radius),
            "product_Pi": str(product),
            "source_leaf_bound": str(initial_radius * product / radius),
            "bit_work_factor_before_C0_B4_and_head": str(product * work_sum / radius),
        }
    if "critical_tanh" in data:
        output["critical_tanh"] = critical_tanh_summary(data)
    return output


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input_json", type=Path)
    args = parser.parse_args()
    print(json.dumps(calculate(json.loads(args.input_json.read_text())), indent=2))
