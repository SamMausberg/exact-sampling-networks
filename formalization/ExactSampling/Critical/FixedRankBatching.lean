import Mathlib

/-!
# Rectangular batching at a fixed first-layer rank

This module formalizes the counting arithmetic of
`lem:fixed-rank-rectangular-batching` and `thm:fixed-rank-critical`
(tanh_fixed_rank_batching.tex), which underlie `thm:main-bottleneck`
(exact_sampling_networks.tex).

Formalized:
* the reordering of sums that accumulates certified block identities (a
  `Finset.sum_comm` step; the bilinear certificates themselves are hypotheses),
  and the denominator bookkeeping `Δ^{2j} Δ^j = Δ^{3j}`;
* the equivalence of the certificate test `R^{8r} ≤ q^{16r+1}` with
  `R ≤ q^{2+ε}`, `ε = 1/(8r)`, in `eq:fixed-rank-base-parameters`;
* the tensor-power recursion `T_j ≤ R T_{j-1} + c q^{2j}` giving
  `T_j ≤ c (j+1) R^j ≤ c (j+1) u^{2+ε}`, `u = q^j`;
* the choice of the least `j` with `w^j ≥ C`: `u ≤ q C^4`, `w^j ≤ w C`,
  `2^{j-1} < C`;
* the block count `h^2 u^{2+ε} ≤ 2(n^2 u^ε + u^{2+ε})` and the resulting
  powers `C^{4ε} = C^{1/(2r)}`, `C^{8+4ε}` of `eq:fixed-rank-rectangular-work`;
* the count `binom(K+r, r) ≤ (K+1)^r` of Taylor coefficients per center;
* the logarithmic exponents `19/4`, `3 + 5r/2`, `4 + r/2`, `12r + 19/4` of the
  preprocessing bound `eq:fixed-rank-general-preprocessing`, and the
  domination `n (log n)^e = O(n^2 (log n)^7)`.

Not formalized: Le Gall's rectangular exponent bound (the existence of base
parameters satisfying `eq:fixed-rank-base-parameters`; it enters only as the
hypotheses of the lemmas that use `q`, `w`, `R`), the flattening bound
`R ≥ q^2` and the inequality `w^4 ≥ q` for `w = ⌊q^{0.30}⌋` (both taken as
hypotheses, `hqR` and `hw4`), the certificate search, the
recursive algorithm as a program, the Taylor-table construction, and the
online factory.
-/

open Finset Filter Asymptotics

namespace ExactSampling.FixedRankBatching

/-! ## Exactness of certified block identities -/

/-- Paper: `lem:fixed-rank-rectangular-batching` (tanh_fixed_rank_batching.tex),
proof: exact rational bilinear identities remain exact when block outputs are
accumulated. The hypothesis `h` stands for a verified base certificate. -/
theorem sum_of_certified_blocks {ι κ : Type*} [Fintype ι] [Fintype κ]
    (target : ι → ℚ) (left right coefficient : ι → κ → ℚ)
    (h : ∀ i, target i = ∑ k, coefficient i k * (left i k * right i k)) :
    (∑ i, target i) = ∑ k, ∑ i, coefficient i k * (left i k * right i k) := by
  calc (∑ i, target i) = ∑ i, ∑ k, coefficient i k * (left i k * right i k) :=
        Finset.sum_congr rfl (fun i _ => h i)
    _ = _ := Finset.sum_comm

/-- Paper: `lem:fixed-rank-rectangular-batching` (tanh_fixed_rank_batching.tex),
proof: input transformations contribute `Δ^j` to each input, leaf products
`Δ^{2j}`, and output recombination raises the exponent by `j`. -/
theorem denominator_power (delta : ℚ) (j : ℕ) :
    delta ^ (2 * j) * delta ^ j = delta ^ (3 * j) := by
  rw [← pow_add]
  congr 1
  omega

/-- Paper: `lem:fixed-rank-rectangular-batching` (tanh_fixed_rank_batching.tex),
proof: a product of two inputs over fixed denominators is the product of the
cleared numerators over the product denominator; no reduction by a greatest
common divisor is needed. -/
theorem clear_input_denominators (a b u v : ℚ) :
    (a / u) * (b / v) = (a * b) / (u * v) := by
  rw [div_mul_div_comm]

/-- Paper: `lem:fixed-rank-rectangular-batching` (tanh_fixed_rank_batching.tex),
proof: if every level multiplies magnitudes by at most `2^g`, after `j` levels
and a sum of at most `2^l` blocks an input of at most `2^m` stays below
`2^{l + gj + m}`; so integers have `O_r(m + j + log n)` bits. -/
theorem magnitude_bits (x n G B : ℕ) (g l m j : ℕ) (hG : G ≤ 2 ^ g) (hn : n ≤ 2 ^ l)
    (hB : B ≤ 2 ^ m) (hx : x ≤ n * G ^ j * B) : x ≤ 2 ^ (l + g * j + m) := by
  have h1 : G ^ j ≤ (2 ^ g) ^ j := Nat.pow_le_pow_left hG j
  calc x ≤ n * G ^ j * B := hx
    _ ≤ 2 ^ l * (2 ^ g) ^ j * 2 ^ m := by gcongr
    _ = 2 ^ (l + g * j + m) := by rw [← pow_mul, ← pow_add, ← pow_add]

/-! ## Base parameters and the tensor-power recursion -/

/-- Paper: `eq:fixed-rank-base-parameters` (tanh_fixed_rank_batching.tex): the
rational certificate test `R^{8r} ≤ q^{16r+1}` is the exponent condition
`R ≤ q^{2+ε}` with `ε = 1/(8r)`. -/
theorem base_test_iff (r : ℕ) (hr : 1 ≤ r) (q R : ℝ) (hq : 0 < q) (hR : 0 ≤ R) :
    R ^ (8 * r) ≤ q ^ (16 * r + 1) ↔ R ≤ q ^ ((2 : ℝ) + 1 / (8 * r)) := by
  have hqp : 0 ≤ q ^ ((2 : ℝ) + 1 / (8 * r)) := Real.rpow_nonneg hq.le _
  have e : (q ^ ((2 : ℝ) + 1 / (8 * r))) ^ (8 * r) = q ^ (16 * r + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    field_simp
    ring
  have h8 : 8 * r ≠ 0 := by omega
  rw [← e]
  exact pow_le_pow_iff_left₀ hR hqp h8

/-- Paper: `lem:fixed-rank-rectangular-batching` (tanh_fixed_rank_batching.tex),
proof: if `q^2 ≤ R`, `T_0 ≤ c` and `T_j ≤ R T_{j-1} + c q^{2j}`, then
`T_j ≤ c (j+1) R^j`; the factor `j+1` covers the case `R = q^2`. -/
theorem tensor_power_recursion (T : ℕ → ℝ) (R q c : ℝ) (hc : 0 ≤ c)
    (hqR : q ^ 2 ≤ R) (h0 : T 0 ≤ c)
    (hstep : ∀ j, T (j + 1) ≤ R * T j + c * q ^ (2 * (j + 1))) (j : ℕ) :
    T j ≤ c * (j + 1) * R ^ j := by
  have hR : 0 ≤ R := le_trans (sq_nonneg q) hqR
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    have hpow : q ^ (2 * (j + 1)) ≤ R ^ (j + 1) := by
      rw [pow_mul]; exact pow_le_pow_left₀ (sq_nonneg q) hqR _
    calc T (j + 1) ≤ R * T j + c * q ^ (2 * (j + 1)) := hstep j
      _ ≤ R * (c * (j + 1) * R ^ j) + c * R ^ (j + 1) := by
          gcongr
      _ = c * ((j + 1 : ℕ) + 1) * R ^ (j + 1) := by push_cast; ring

/-- Paper: `lem:fixed-rank-rectangular-batching` (tanh_fixed_rank_batching.tex),
proof: `R ≤ q^{2+ε}` gives `R^j ≤ u^{2+ε}` with `u = q^j`, hence
`T_j = O_r((j+1) u^{2+ε})`. -/
theorem power_le_rpow (q R ε : ℝ) (hq : 0 < q) (hR : 0 ≤ R) (h : R ≤ q ^ (2 + ε)) (j : ℕ) :
    R ^ j ≤ (q ^ j) ^ (2 + ε) := by
  calc R ^ j ≤ (q ^ (2 + ε)) ^ j := pow_le_pow_left₀ hR h j
    _ = (q ^ j) ^ (2 + ε) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, ← Real.rpow_natCast q j,
          ← Real.rpow_mul hq.le, mul_comm]

/-- Paper: `lem:fixed-rank-rectangular-batching` (tanh_fixed_rank_batching.tex),
proof: let `j` be the least exponent with `w^j ≥ C`. If `w^4 ≥ q`, then
`u = q^j ≤ q C^4` and the padded column count obeys `w^j ≤ w C`. -/
theorem least_level_bounds (q w C j : ℕ) (hq : 1 ≤ q) (hw : 1 ≤ w) (hC : 1 ≤ C)
    (hw4 : q ≤ w ^ 4) (hmin : j = 0 ∨ w ^ (j - 1) < C) :
    q ^ j ≤ q * C ^ 4 ∧ w ^ j ≤ w * C := by
  rcases hmin with h0 | h1
  · subst h0
    simp only [pow_zero]
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by positivity)),
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))⟩
  · rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      simp only [pow_zero]
      exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by positivity)),
        Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))⟩
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at h1
      constructor
      · have h2 : q ^ i ≤ (w ^ 4) ^ i := Nat.pow_le_pow_left hw4 i
        have h3 : (w ^ 4) ^ i = (w ^ i) ^ 4 := by rw [← pow_mul, ← pow_mul, mul_comm]
        have h4 : (w ^ i) ^ 4 ≤ C ^ 4 := Nat.pow_le_pow_left h1.le 4
        rw [pow_succ, mul_comm]
        exact Nat.mul_le_mul_left q (h2.trans (h3 ▸ h4))
      · rw [pow_succ, mul_comm]
        exact Nat.mul_le_mul_left w h1.le

/-- Paper: `lem:fixed-rank-rectangular-batching` (tanh_fixed_rank_batching.tex),
proof: for the least such `j ≥ 1` and `w ≥ 2`, `2^{j-1} < C`, so
`j + 1 = O(log(C + 2))`. -/
theorem least_level_log (w C j : ℕ) (hw : 2 ≤ w) (h1 : w ^ (j - 1) < C) :
    2 ^ (j - 1) < C :=
  lt_of_le_of_lt (Nat.pow_le_pow_left hw _) h1

/-- Paper: `lem:fixed-rank-rectangular-batching` (tanh_fixed_rank_batching.tex),
proof: with `h ≤ n/u + 1` blocks per side, the `h^2` block products cost
`h^2 u^{2+ε} ≤ 2 (n^2 u^ε + u^{2+ε})`. -/
theorem block_count (n u h ε : ℝ) (hu : 0 < u) (hh0 : 0 ≤ h)
    (hh : h ≤ n / u + 1) :
    h ^ 2 * u ^ (2 + ε) ≤ 2 * (n ^ 2 * u ^ ε + u ^ (2 + ε)) := by
  have hsplit : u ^ (2 + ε) = u ^ 2 * u ^ ε := by
    rw [Real.rpow_add hu, Real.rpow_two]
  have hue : 0 < u ^ ε := Real.rpow_pos_of_pos hu ε
  have h2 : h ^ 2 ≤ 2 * ((n / u) ^ 2 + 1) := by
    have h3 : h ^ 2 ≤ (n / u + 1) ^ 2 := pow_le_pow_left₀ hh0 hh 2
    nlinarith [sq_nonneg (n / u - 1)]
  have e : 2 * ((n / u) ^ 2 + 1) * u ^ (2 + ε) = 2 * (n ^ 2 * u ^ ε + u ^ (2 + ε)) := by
    rw [hsplit]; field_simp
  calc h ^ 2 * u ^ (2 + ε) ≤ 2 * ((n / u) ^ 2 + 1) * u ^ (2 + ε) :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hu.le _)
    _ = _ := e

/-- Paper: `lem:fixed-rank-rectangular-batching` (tanh_fixed_rank_batching.tex),
proof: `u ≤ q C^4` gives `u^ε ≤ q^ε C^{4ε}` and
`u^{2+ε} ≤ q^{2+ε} C^{8+4ε}`. -/
theorem padded_powers (u q C ε : ℝ) (hu : 0 < u) (hq : 0 < q) (hC : 0 < C) (hε : 0 ≤ ε)
    (h : u ≤ q * C ^ 4) :
    u ^ ε ≤ q ^ ε * C ^ (4 * ε) ∧ u ^ (2 + ε) ≤ q ^ (2 + ε) * C ^ (8 + 4 * ε) := by
  have hC4 : (C ^ 4) ^ ε = C ^ (4 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hC.le]; norm_num
  have hC8 : (C ^ 4) ^ (2 + ε) = C ^ (8 + 4 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hC.le]; congr 1; push_cast; ring
  constructor
  · calc u ^ ε ≤ (q * C ^ 4) ^ ε := Real.rpow_le_rpow hu.le h hε
      _ = q ^ ε * C ^ (4 * ε) := by rw [Real.mul_rpow hq.le (by positivity), hC4]
  · calc u ^ (2 + ε) ≤ (q * C ^ 4) ^ (2 + ε) := Real.rpow_le_rpow hu.le h (by linarith)
      _ = q ^ (2 + ε) * C ^ (8 + 4 * ε) := by rw [Real.mul_rpow hq.le (by positivity), hC8]

/-- Paper: `lem:fixed-rank-rectangular-batching` (tanh_fixed_rank_batching.tex):
with `ε = 1/(8r)`, `4ε = 1/(2r)`, the exponent in
`eq:fixed-rank-rectangular-work`. -/
theorem rectangular_excess (r : ℝ) (hr : r ≠ 0) : 4 * (1 / (8 * r)) = 1 / (2 * r) := by
  field_simp
  ring

/-! ## Table size and logarithmic exponents -/

/-- Paper: `thm:fixed-rank-critical` (tanh_fixed_rank_batching.tex): the number
of total-degree-`K` coefficients in `r` variables is
`N_K = binom(K+r, r) ≤ (K+1)^r = O_r(K^r)`. -/
theorem coefficient_count (K r : ℕ) : (K + r).choose r ≤ (K + 1) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h := Nat.add_one_mul_choose_eq (K + r) r
    have h2 : (K + r + 1) * (K + r).choose r ≤ (K + r + 1) * (K + 1) ^ r :=
      Nat.mul_le_mul_left _ ih
    have h3 : K + r + 1 ≤ (r + 1) * (K + 1) := by nlinarith
    have h4 : (K + (r + 1)).choose (r + 1) * (r + 1) ≤ (K + 1) ^ (r + 1) * (r + 1) := by
      calc (K + (r + 1)).choose (r + 1) * (r + 1) = (K + r + 1) * (K + r).choose r := by
            rw [h]; ring_nf
        _ ≤ (K + r + 1) * (K + 1) ^ r := h2
        _ ≤ (r + 1) * (K + 1) * (K + 1) ^ r := Nat.mul_le_mul_right _ h3
        _ = (K + 1) ^ (r + 1) * (r + 1) := by ring
    exact Nat.le_of_mul_le_mul_right h4 (by omega)

/-- Paper: `thm:fixed-rank-critical` (tanh_fixed_rank_batching.tex): with
`J = D^{r/2}` centers and `N_K = K^r` coefficients, the column count
`C = J N_K` has logarithmic exponent `r/2 + r = 3r/2` when `D, K = O(v)`. -/
theorem column_exponent (r : ℝ) : r / 2 + r = 3 * r / 2 := by ring

/-- Paper: `thm:fixed-rank-critical` (tanh_fixed_rank_batching.tex): the dense
contribution has one depth factor, two precision factors, `C^{1/(2r)}` with
`C = O_r(v^{3r/2})`, and one factor `log(C+2)`: exponent `19/4`. -/
theorem dense_logarithmic_exponent (r : ℝ) (hr : r ≠ 0) :
    3 + (3 * r / 2) * (1 / (2 * r)) + 1 = 19 / 4 := by
  field_simp
  ring

/-- Paper: `thm:fixed-rank-critical` (tanh_fixed_rank_batching.tex): `19/4 < 7`. -/
theorem dense_exponent_fits_budget : (19 : ℚ) / 4 < 7 := by
  norm_num

/-- Paper: `thm:fixed-rank-critical` (tanh_fixed_rank_batching.tex): the padding
term `log(C+2) C^{8+1/(2r)}` contributes exponent `12r + 19/4`. -/
theorem padding_logarithmic_exponent (r : ℝ) (hr : r ≠ 0) :
    3 + (3 * r / 2) * (8 + 1 / (2 * r)) + 1 = 12 * r + 19 / 4 := by
  field_simp
  ring

/-- Paper: `thm:fixed-rank-critical` (tanh_fixed_rank_batching.tex): the
nonlinear term `D · n D^{r/2} K^{2r} · M^2` has exponent `3 + 5r/2`. -/
theorem nonlinear_logarithmic_exponent (r : ℝ) : 1 + r / 2 + 2 * r + 2 = 3 + 5 * r / 2 := by
  ring

/-- Paper: `thm:fixed-rank-critical` (tanh_fixed_rank_batching.tex): the constant
exponentials `D · n D^{r/2} M · M^2` have exponent `4 + r/2`. -/
theorem exponential_logarithmic_exponent (r : ℝ) : 1 + r / 2 + 1 + 2 = 4 + r / 2 := by
  ring

/-- Paper: `thm:fixed-rank-critical` (tanh_fixed_rank_batching.tex): a fixed power
of `log n` is dominated by any fixed positive power of `n`; in particular
`n (log n)^e = O(n^2 (log n)^7)` for every real `e`. -/
theorem polylog_absorbed (e : ℝ) :
    (fun x : ℝ => x * Real.log x ^ e) =O[atTop] (fun x : ℝ => x ^ 2 * Real.log x ^ (7 : ℝ)) := by
  have h := (isLittleO_log_rpow_rpow_atTop e (by norm_num : (0 : ℝ) < 1)).bound
    (by norm_num : (0 : ℝ) < 1)
  refine IsBigO.of_bound 1 ?_
  filter_upwards [h, eventually_ge_atTop (Real.exp 1)] with x hx hxe
  have hx1 : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hlog0 : 0 ≤ Real.log x := by linarith
  have hl7 : 1 ≤ Real.log x ^ (7 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hle : 0 ≤ Real.log x ^ e := Real.rpow_nonneg hlog0 e
  rw [Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg hle,
    abs_of_pos hxpos] at hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul,
    abs_of_nonneg (mul_nonneg hxpos.le hle),
    abs_of_nonneg (mul_nonneg (sq_nonneg x) (Real.rpow_nonneg hlog0 (7 : ℝ)))]
  calc x * Real.log x ^ e ≤ x * x := mul_le_mul_of_nonneg_left hx hxpos.le
    _ = x ^ 2 * 1 := by ring
    _ ≤ x ^ 2 * Real.log x ^ (7 : ℝ) := mul_le_mul_of_nonneg_left hl7 (by positivity)

end ExactSampling.FixedRankBatching
