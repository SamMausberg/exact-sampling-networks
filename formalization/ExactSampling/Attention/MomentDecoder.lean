import Mathlib

/-!
# The fixed-rank moment decoder: moment index and depth stability

This module formalizes quantitative steps of `attention_moment_decoder.tex`
(`thm:momentdecoder`; summarized in `main_decoder.tex` as `thm:main-decoder`):

* `lem:finitemomentindex`: the uniform Taylor error `|E_m(x) - e^x| ≤ 2^{-q}` on `|x| ≤ H`
  for `m ≥ 8(H+q+1)` (`eq:momenttaylorerror`); the multinomial expansion showing that the
  truncated numerator and denominator are exact linear combinations of stored monomial moments;
  exact append updates and the bound `|S_ν| ≤ T`; the normalized-ratio error
  `2δ/(Z-δ) ≤ 4δe^H ≤ 2^{-p-4}`; and the assembled accuracy `moment_index_accuracy` for records
  `z_j ∈ [-1,1]^r`, values `|u_j| ≤ 1`, and `‖t‖₁ ≤ H`.
* `lem:prefixstability`: softmax is Lipschitz from `ℓ∞` scores to `ℓ1` probabilities with
  constant two for every number of positions (proved by differentiating along a segment);
  the attention-mean bound `eq:attentionstabilitymoment`; the score perturbation bound; the
  coordinate bound of affine maps of normalized vectors; the coefficient bound
  `‖t‖₁ ≤ 2rβK²`; and the depth recurrence `e_J ≤ J L₀^J δ` (also for actual Lipschitz stages)
  with the precision choice.
* `cor:affineheadmoment`: the residual range recursion, the shifted softmax denominator
  `S ≥ e^{-1/4} > 1/2`, and the interval division width `≤ 16δ/(3S) < 11δ`.
* `cor:momentgeluswiglu`: the sigmoid derivative and the SwiGLU range and derivative bounds;
  for GELU, the bounds `|uΦ| ≤ K` and `|Φ + uφ| ≤ 1 + K` for arbitrary `Φ, φ ∈ [0,1]` (the
  identity `g' = Φ + uφ` is not proved here), and `φ ≤ 1` for the standard normal density.
* `cor:fixedpositionalrotation`: the row-sum bound `√2` of a rotation, the period index bound
  `|k| ≤ C_ω(T+1)`, the reduced-argument error, its range, and the numerical Taylor remainder
  bound.
* `cor:fixedmodelcontext`: the exponent bookkeeping `(m+1)^{2r+4} L^4 = O(log^{2r+12})`.

Not formalized here: the bit-complexity model and the explicit polynomial `F_r`, the certified
evaluation routines themselves, and the Lagrange remainder bound for sine and cosine (only its
numerical value is checked). The Lipschitz bound of the normalization map is in
`ExactSampling.CheckpointCertificates` (`lem:checkpoint-rms-lipschitz`).

Stronger forms elsewhere in the library: the count `N_m = binom(m+r, r)` is
`ExactSampling.Moments.card_multiIdx`; the standard-scaling parity split is
`ExactSampling.Moments.parity_split`; the composition of the network stages on prefix arrays is
`ExactSampling.Stability.error_induction` and `ExactSampling.Stability.prefix_network_error`;
the fixed-model expected cost `O(log^{2r+12})` is
`ExactSampling.FixedModel.fixedModel_expected_isBigO`.
-/

open Finset Filter
open scoped BigOperators Topology Nat

namespace ExactSampling.MomentDecoder

/-! ## The moment index (`lem:finitemomentindex`) -/

section MomentIndex

/-- Auxiliary: `e^{1/2} < 2`. Supports the factorial estimate in the proof of
`lem:finitemomentindex` (attention_moment_decoder.tex). -/
lemma exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h := Real.add_one_lt_exp (show (-(1 / 2 : ℝ)) ≠ 0 by norm_num)
  have hpos := Real.exp_pos (1 / 2 : ℝ)
  have hmul : Real.exp (-(1 / 2)) * Real.exp (1 / 2) = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith

/-- `H^N / N! ≤ 2^{-N}` whenever `N ≥ 8H`, from `(4H)^N/N! ≤ e^{4H} ≤ e^{N/2} ≤ 2^N`.
Paper: `lem:finitemomentindex` (attention_moment_decoder.tex), the factorial estimate in the
proof of `eq:momenttaylorerror`. -/
theorem pow_div_factorial_le (H : ℝ) (N : ℕ) (hH : 0 ≤ H) (hN : 8 * H ≤ N) :
    H ^ N / N ! ≤ (2 : ℝ)⁻¹ ^ N := by
  have h1 := Real.pow_div_factorial_le_exp (4 * H) (by linarith) N
  have h2 : Real.exp (4 * H) ≤ Real.exp (1 / 2) ^ N := by
    rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (1 / 2) ^ N ≤ 2 ^ N :=
    pow_le_pow_left₀ (Real.exp_pos _).le exp_half_lt_two.le N
  have hfac : (0 : ℝ) < N ! := by exact_mod_cast Nat.factorial_pos N
  have h4 : (4 * H) ^ N / N ! = 4 ^ N * (H ^ N / N !) := by rw [mul_pow]; ring
  rw [h4] at h1
  have h4pos : (0 : ℝ) < 4 ^ N := by positivity
  have : H ^ N / N ! ≤ 2 ^ N / 4 ^ N := by
    rw [le_div_iff₀ h4pos]; nlinarith
  calc H ^ N / N ! ≤ 2 ^ N / 4 ^ N := this
    _ = (2 : ℝ)⁻¹ ^ N := by
        rw [show (4 : ℝ) ^ N = 2 ^ N * 2 ^ N by rw [← mul_pow]; norm_num]
        rw [inv_pow]; field_simp

/-- Uniform Taylor error of the exponential: if `m ≥ 8(H+q+1)` (for instance
`m = ⌈8(H+q+1)⌉`), then `|E_m(x) - e^x| ≤ 2^{-q}` for all `|x| ≤ H`, where
`E_m(x) = ∑_{d ≤ m} x^d/d!`.
Paper: `lem:finitemomentindex`, display `eq:momenttaylorerror` (attention_moment_decoder.tex). -/
theorem taylor_exp_error (H : ℝ) (q m : ℕ) (hH : 0 ≤ H) (hm : 8 * (H + q + 1) ≤ m)
    (x : ℝ) (hx : |x| ≤ H) :
    |Real.exp x - ∑ d ∈ Finset.range (m + 1), x ^ d / d !| ≤ (2 : ℝ)⁻¹ ^ q := by
  have hq : (q : ℝ) ≤ m := by nlinarith
  have hcond : ‖(x : ℂ)‖ / ((m + 1).succ : ℕ) ≤ 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ (by positivity)]
    push_cast
    nlinarith [abs_nonneg x]
  have hb := Complex.exp_bound' hcond
  have hcast : Complex.exp (x : ℂ) - ∑ d ∈ Finset.range (m + 1), (x : ℂ) ^ d / (d ! : ℂ) =
      ((Real.exp x - ∑ d ∈ Finset.range (m + 1), x ^ d / d ! : ℝ) : ℂ) := by
    push_cast [Complex.ofReal_exp]; rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs] at hb
  have hpow : |x| ^ (m + 1) / ((m + 1) ! : ℝ) ≤ H ^ (m + 1) / ((m + 1) ! : ℝ) := by
    gcongr
  have hfac := pow_div_factorial_le H (m + 1) hH (by push_cast; nlinarith)
  calc |Real.exp x - ∑ d ∈ Finset.range (m + 1), x ^ d / d !|
      ≤ |x| ^ (m + 1) / ((m + 1) ! : ℝ) * 2 := hb
    _ ≤ (2 : ℝ)⁻¹ ^ (m + 1) * 2 := by nlinarith
    _ = (2 : ℝ)⁻¹ ^ m := by rw [pow_succ]; ring
    _ ≤ (2 : ℝ)⁻¹ ^ q := by
        apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
        exact_mod_cast hq

/-- The multinomial theorem for one truncated exponential:
`E_m(⟨t,z⟩) = ∑_{|ν| ≤ m} (t^ν/ν!) z^ν`.
Paper: `lem:finitemomentindex` (attention_moment_decoder.tex). -/
theorem taylor_multinomial {r : ℕ} (t z : Fin r → ℝ) (m : ℕ) :
    ∑ d ∈ Finset.range (m + 1), (∑ i, t i * z i) ^ d / d ! =
      ∑ d ∈ Finset.range (m + 1), ∑ k ∈ Finset.univ.piAntidiag d,
        (∏ i, t i ^ k i / (k i)!) * ∏ i, z i ^ k i := by
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_pow_eq_sum_piAntidiag, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_piAntidiag] at hk
  have hspec := Nat.multinomial_spec Finset.univ k
  rw [hk.1] at hspec
  have hprodpos : (0 : ℝ) < ∏ i, ((k i)! : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _
  have hspec' : (∏ i, ((k i)! : ℝ)) * (Nat.multinomial Finset.univ k : ℝ) = (d ! : ℝ) := by
    exact_mod_cast (by simpa using hspec)
  have hd : (0 : ℝ) < d ! := by exact_mod_cast Nat.factorial_pos d
  rw [Finset.prod_div_distrib]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  field_simp
  rw [← hspec']
  ring

/-- Exactness of the moment index: the truncated value-weighted sum
`∑_j E_m(⟨t, z_j⟩) u_j` equals `∑_{|ν| ≤ m} (t^ν/ν!) M_ν`, where `M_ν = ∑_j z_j^ν u_j` are
the stored moments. The denominator is the case `u ≡ 1`.
Paper: `lem:finitemomentindex` (attention_moment_decoder.tex). -/
theorem moment_index_exact {ι : Type*} (T : Finset ι) {r : ℕ} (t : Fin r → ℝ)
    (z : ι → Fin r → ℝ) (u : ι → ℝ) (m : ℕ) :
    ∑ j ∈ T, (∑ d ∈ Finset.range (m + 1), (∑ i, t i * z j i) ^ d / d !) * u j =
      ∑ d ∈ Finset.range (m + 1), ∑ k ∈ Finset.univ.piAntidiag d,
        (∏ i, t i ^ k i / (k i)!) * ∑ j ∈ T, (∏ i, z j i ^ k i) * u j := by
  simp_rw [taylor_multinomial, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- An insertion adds exactly the new record's monomial increment to every stored moment;
there is no rounding during insertions.
Paper: `lem:finitemomentindex` (attention_moment_decoder.tex). -/
theorem moment_append {ι : Type*} [DecidableEq ι] (T : Finset ι) (new : ι) (hnew : new ∉ T)
    {r : ℕ} (z : ι → Fin r → ℝ) (u : ι → ℝ) (k : Fin r → ℕ) :
    ∑ j ∈ insert new T, (∏ i, z j i ^ k i) * u j =
      ∑ j ∈ T, (∏ i, z j i ^ k i) * u j + (∏ i, z new i ^ k i) * u new := by
  rw [Finset.sum_insert hnew, add_comm]

/-- Every stored moment has absolute value at most the number of records `T`, since
`z_j ∈ [-1,1]^r` and `|u_j| ≤ 1`.
Paper: `lem:finitemomentindex` (attention_moment_decoder.tex). -/
theorem moment_bound {ι : Type*} (T : Finset ι) {r : ℕ} (z : ι → Fin r → ℝ) (u : ι → ℝ)
    (k : Fin r → ℕ) (hz : ∀ j i, |z j i| ≤ 1) (hu : ∀ j, |u j| ≤ 1) :
    |∑ j ∈ T, (∏ i, z j i ^ k i) * u j| ≤ T.card := by
  calc |∑ j ∈ T, (∏ i, z j i ^ k i) * u j| ≤ ∑ j ∈ T, |(∏ i, z j i ^ k i) * u j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ T, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, Finset.abs_prod]
        have h1 : ∏ i, |z j i ^ k i| ≤ 1 := by
          apply Finset.prod_le_one₀ (fun i _ => abs_nonneg _)
          intro i _
          rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hz j i)
        calc (∏ i, |z j i ^ k i|) * |u j| ≤ 1 * 1 :=
              mul_le_mul h1 (hu j) (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    _ = T.card := by simp

/-- The normalized truncated attention mean: with `Z ≥ e^{-H}`, `|N| ≤ Z`, and numerator and
denominator errors at most `δ = 2^{-q}`, `q = p + 2H + 6`, the truncated denominator is
positive and `|Ñ/Z̃ - N/Z| ≤ 2δ/(Z-δ) ≤ 4δe^H ≤ 2^{-p-4}`.
Paper: `lem:finitemomentindex` (attention_moment_decoder.tex). -/
theorem moment_ratio_error (Z Zt N Nt : ℝ) (H p : ℕ)
    (hZ : Real.exp (-(H : ℝ)) ≤ Z) (hN : |N| ≤ Z)
    (hZt : |Z - Zt| ≤ (2 : ℝ)⁻¹ ^ (p + 2 * H + 6))
    (hNt : |N - Nt| ≤ (2 : ℝ)⁻¹ ^ (p + 2 * H + 6)) :
    0 < Zt ∧
      |Nt / Zt - N / Z| ≤ 2 * (2 : ℝ)⁻¹ ^ (p + 2 * H + 6) / (Z - (2 : ℝ)⁻¹ ^ (p + 2 * H + 6)) ∧
      2 * (2 : ℝ)⁻¹ ^ (p + 2 * H + 6) / (Z - (2 : ℝ)⁻¹ ^ (p + 2 * H + 6)) ≤
        4 * (2 : ℝ)⁻¹ ^ (p + 2 * H + 6) * Real.exp H ∧
      4 * (2 : ℝ)⁻¹ ^ (p + 2 * H + 6) * Real.exp H ≤ (2 : ℝ)⁻¹ ^ (p + 4) := by
  set δ := (2 : ℝ)⁻¹ ^ (p + 2 * H + 6) with hδdef
  have hδpos : 0 < δ := by positivity
  have he1 : Real.exp 1 < 4 := by
    have := Real.exp_one_lt_d9; norm_num at this; linarith
  have heH : Real.exp H ≤ 4 ^ H := by
    rw [show (H : ℝ) = H * 1 by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le he1.le H
  have hexpH : Real.exp (-(H : ℝ)) * Real.exp H = 1 := by rw [← Real.exp_add]; simp
  have hZpos : 0 < Z := lt_of_lt_of_le (Real.exp_pos _) hZ
  have hZeH : 1 ≤ Z * Real.exp H := by
    have := mul_le_mul_of_nonneg_right hZ (Real.exp_pos (H : ℝ)).le
    linarith
  -- 4 δ e^H ≤ 2^{-p-4}
  have hkey : 4 * δ * Real.exp H ≤ (2 : ℝ)⁻¹ ^ (p + 4) := by
    have h4 : (4 : ℝ) ^ H = 2 ^ (2 * H) := by rw [pow_mul]; norm_num
    have hδ' : δ * 4 ^ H = (2 : ℝ)⁻¹ ^ (p + 6) := by
      rw [hδdef, h4, show p + 2 * H + 6 = (p + 6) + 2 * H by ring, pow_add, inv_pow (2 : ℝ),
        inv_pow (2 : ℝ) (2 * H), mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
    calc 4 * δ * Real.exp H ≤ 4 * δ * 4 ^ H := by gcongr
      _ = 4 * (2 : ℝ)⁻¹ ^ (p + 6) := by rw [mul_assoc, hδ']
      _ = (2 : ℝ)⁻¹ ^ (p + 4) := by
          rw [show p + 6 = (p + 4) + 2 by ring, pow_add]; ring
      _ ≤ (2 : ℝ)⁻¹ ^ (p + 4) := le_rfl
  have hδZ : δ ≤ Z / 2 := by
    have : δ * Real.exp H ≤ 1 / 64 := by
      have h := hkey
      have : (2 : ℝ)⁻¹ ^ (p + 4) ≤ 1 / 16 := by
        rw [pow_add]; norm_num
        exact pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    have hE : 0 < Real.exp H := Real.exp_pos _
    nlinarith
  have hZt' := abs_le.mp hZt
  have hZtpos : 0 < Zt := by linarith
  refine ⟨hZtpos, ?_, ?_, hkey⟩
  · have hdiff : |Nt / Zt - N / Z| = |(Nt - N) * Z + N * (Z - Zt)| / (Zt * Z) := by
      rw [div_sub_div _ _ hZtpos.ne' hZpos.ne', abs_div, abs_of_pos (mul_pos hZtpos hZpos)]
      congr 1; ring_nf
    rw [hdiff, div_le_div_iff₀ (mul_pos hZtpos hZpos) (by linarith)]
    have hnum : |(Nt - N) * Z + N * (Z - Zt)| ≤ 2 * δ * Z := by
      calc |(Nt - N) * Z + N * (Z - Zt)| ≤ |(Nt - N) * Z| + |N * (Z - Zt)| := abs_add_le _ _
        _ = |Nt - N| * Z + |N| * |Z - Zt| := by
            rw [abs_mul, abs_mul, abs_of_pos hZpos]
        _ ≤ δ * Z + Z * δ := by
            gcongr
            · rw [abs_sub_comm]; exact hNt
        _ = 2 * δ * Z := by ring
    have hZt2 : Z - δ ≤ Zt := by linarith
    have hpos2 : 0 ≤ Z - δ := by linarith
    have hmul := mul_le_mul_of_nonneg_left hZt2 (by positivity : (0 : ℝ) ≤ 2 * δ * Z)
    calc |(Nt - N) * Z + N * (Z - Zt)| * (Z - δ) ≤ (2 * δ * Z) * (Z - δ) := by gcongr
      _ ≤ 2 * δ * Z * Zt := hmul
      _ = 2 * δ * (Zt * Z) := by ring
  · rw [div_le_iff₀ (by linarith)]
    have : 2 ≤ 4 * Real.exp H * (Z - δ) := by nlinarith [Real.exp_pos (H : ℝ)]
    nlinarith

/-- Coefficient bound in a bounded chart: with `|q_i| ≤ K` and `|A_{ia}| ≤ 2`, the vector
`t = (βK/n) qᵀA` has `‖t‖₁ ≤ 2rβK²`.
Paper: `lem:prefixstability` (attention_moment_decoder.tex), display for `‖t‖₁`. -/
theorem chart_coefficient_bound {n r : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (A : Fin n → Fin r → ℝ) (β K : ℝ) (hβ : 0 ≤ β) (hK : 0 ≤ K) (hq : ∀ i, |q i| ≤ K)
    (hA : ∀ i a, |A i a| ≤ 2) :
    ∑ a, |β * K / n * ∑ i, q i * A i a| ≤ 2 * r * β * K ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hcol : ∀ a, |β * K / n * ∑ i, q i * A i a| ≤ 2 * β * K ^ 2 := by
    intro a
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have hs : |∑ i, q i * A i a| ≤ n * (K * 2) := by
      calc |∑ i, q i * A i a| ≤ ∑ i, |q i * A i a| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, K * 2 := by
            apply Finset.sum_le_sum; intro i _
            rw [abs_mul]; exact mul_le_mul (hq i) (hA i a) (abs_nonneg _) hK
        _ = n * (K * 2) := by simp
    calc β * K / n * |∑ i, q i * A i a| ≤ β * K / n * (n * (K * 2)) := by gcongr
      _ = 2 * β * K ^ 2 := by field_simp
  calc ∑ a, |β * K / n * ∑ i, q i * A i a| ≤ ∑ _a : Fin r, 2 * β * K ^ 2 :=
        Finset.sum_le_sum fun a _ => hcol a
    _ = 2 * r * β * K ^ 2 := by simp; ring

/-- The assembled moment-index accuracy. For records `z_j ∈ [-1,1]^r` with values `|u_j| ≤ 1`
(a nonempty finite set) and coefficients with `‖t‖₁ ≤ H`, let `Z, N` be the average exact
denominator and numerator and `Z̃, Ñ` their degree-`m` truncations, where
`m ≥ 8(H + q + 1)` and `q = p + 2H + 6`. Then `Z̃ > 0` and `|Ñ/Z̃ - N/Z| ≤ 2^{-p-4}`. The
truncated sums are exact combinations of the stored moments (`moment_index_exact`).
Paper: `lem:finitemomentindex` (attention_moment_decoder.tex). -/
theorem moment_index_accuracy {ι : Type*} (s : Finset ι) (hs : s.Nonempty) {r : ℕ}
    (t : Fin r → ℝ) (z : ι → Fin r → ℝ) (u : ι → ℝ) (H p m : ℕ) (ht : ∑ i, |t i| ≤ H)
    (hz : ∀ j i, |z j i| ≤ 1) (hu : ∀ j, |u j| ≤ 1)
    (hm : 8 * ((H : ℝ) + ((p + 2 * H + 6 : ℕ) : ℝ) + 1) ≤ m) :
    let E : ℝ → ℝ := fun x => ∑ d ∈ Finset.range (m + 1), x ^ d / (d.factorial : ℝ)
    let x : ι → ℝ := fun j => ∑ i, t i * z j i
    let Z := (∑ j ∈ s, Real.exp (x j)) / s.card
    let N := (∑ j ∈ s, Real.exp (x j) * u j) / s.card
    let Zt := (∑ j ∈ s, E (x j)) / s.card
    let Nt := (∑ j ∈ s, E (x j) * u j) / s.card
    0 < Zt ∧ |Nt / Zt - N / Z| ≤ (2 : ℝ)⁻¹ ^ (p + 4) := by
  intro E x Z N Zt Nt
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hx : ∀ j, |x j| ≤ H := by
    intro j
    calc |x j| ≤ ∑ i, |t i * z j i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |t i| := by
          apply Finset.sum_le_sum; intro i _
          rw [abs_mul]
          calc |t i| * |z j i| ≤ |t i| * 1 := by gcongr; exact hz j i
            _ = |t i| := mul_one _
      _ ≤ H := ht
  have htay : ∀ j, |Real.exp (x j) - E (x j)| ≤ (2 : ℝ)⁻¹ ^ (p + 2 * H + 6) := fun j =>
    taylor_exp_error H (p + 2 * H + 6) m (Nat.cast_nonneg _) hm (x j) (hx j)
  have hZ : Real.exp (-(H : ℝ)) ≤ Z := by
    show Real.exp (-(H : ℝ)) ≤ (∑ j ∈ s, Real.exp (x j)) / s.card
    rw [le_div_iff₀ hcard]
    calc Real.exp (-(H : ℝ)) * s.card = ∑ _j ∈ s, Real.exp (-(H : ℝ)) := by simp; ring
      _ ≤ ∑ j ∈ s, Real.exp (x j) := by
          apply Finset.sum_le_sum; intro j _
          exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hx j)).1])
  have hN : |N| ≤ Z := by
    show |(∑ j ∈ s, Real.exp (x j) * u j) / s.card| ≤ (∑ j ∈ s, Real.exp (x j)) / s.card
    rw [abs_div, abs_of_pos hcard]
    apply div_le_div_of_nonneg_right _ hcard.le
    calc |∑ j ∈ s, Real.exp (x j) * u j| ≤ ∑ j ∈ s, |Real.exp (x j) * u j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ s, Real.exp (x j) := by
          apply Finset.sum_le_sum; intro j _
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          calc Real.exp (x j) * |u j| ≤ Real.exp (x j) * 1 := by gcongr; exact hu j
            _ = Real.exp (x j) := mul_one _
  have havg : ∀ g : ι → ℝ, (∀ j, |g j| ≤ (2 : ℝ)⁻¹ ^ (p + 2 * H + 6)) →
      |(∑ j ∈ s, g j) / s.card| ≤ (2 : ℝ)⁻¹ ^ (p + 2 * H + 6) := by
    intro g hg
    rw [abs_div, abs_of_pos hcard, div_le_iff₀ hcard]
    calc |∑ j ∈ s, g j| ≤ ∑ j ∈ s, |g j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ s, (2 : ℝ)⁻¹ ^ (p + 2 * H + 6) := Finset.sum_le_sum fun j _ => hg j
      _ = (2 : ℝ)⁻¹ ^ (p + 2 * H + 6) * s.card := by simp; ring
  have hZt : |Z - Zt| ≤ (2 : ℝ)⁻¹ ^ (p + 2 * H + 6) := by
    have : Z - Zt = (∑ j ∈ s, (Real.exp (x j) - E (x j))) / s.card := by
      simp only [Z, Zt]; rw [Finset.sum_sub_distrib, sub_div]
    rw [this]; exact havg _ htay
  have hNt : |N - Nt| ≤ (2 : ℝ)⁻¹ ^ (p + 2 * H + 6) := by
    have : N - Nt = (∑ j ∈ s, (Real.exp (x j) - E (x j)) * u j) / s.card := by
      simp only [N, Nt]; rw [← sub_div, ← Finset.sum_sub_distrib]
      congr 1; refine Finset.sum_congr rfl fun j _ => ?_; ring
    rw [this]
    apply havg
    intro j
    rw [abs_mul]
    calc |Real.exp (x j) - E (x j)| * |u j| ≤ (2 : ℝ)⁻¹ ^ (p + 2 * H + 6) * 1 :=
          mul_le_mul (htay j) (hu j) (abs_nonneg _) (by positivity)
      _ = _ := mul_one _
  obtain ⟨h1, h2, h3, h4⟩ := moment_ratio_error Z Zt N Nt H p hZ hN hZt hNt
  exact ⟨h1, h2.trans (h3.trans h4)⟩

end MomentIndex

/-! ## Stability over a causal prefix (`lem:prefixstability`) -/

section Stability

variable {ι : Type*} [Fintype ι]

/-- The softmax probabilities `p_j(a) = e^{a_j} / ∑_i e^{a_i}`. -/
noncomputable def softmax (a : ι → ℝ) (j : ι) : ℝ := Real.exp (a j) / ∑ i, Real.exp (a i)

/-- Auxiliary: softmax probabilities are nonnegative. Supports `lem:prefixstability`
(attention_moment_decoder.tex). -/
lemma softmax_nonneg (a : ι → ℝ) (j : ι) : 0 ≤ softmax a j :=
  div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)

/-- Auxiliary: softmax probabilities sum to one. Supports `lem:prefixstability`
(attention_moment_decoder.tex). -/
lemma softmax_sum [Nonempty ι] (a : ι → ℝ) : ∑ j, softmax a j = 1 := by
  unfold softmax
  rw [← Finset.sum_div, div_self]
  exact (Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty).ne'

/-- Auxiliary: `|∑_j s_j p_j(δ_j - ∑_i p_i δ_i)| ≤ 2‖δ‖_∞` for a probability vector `p` and
`|s_j| ≤ 1`; this bounds the derivative of softmax along a segment. Supports the proof of
`lem:prefixstability` (attention_moment_decoder.tex). -/
lemma weighted_centered_bound [Nonempty ι] (p δ s : ι → ℝ) (ε : ℝ) (hp : ∀ j, 0 ≤ p j)
    (hsum : ∑ j, p j = 1) (hδ : ∀ j, |δ j| ≤ ε) (hs : ∀ j, |s j| ≤ 1) :
    |∑ j, s j * (p j * (δ j - ∑ i, p i * δ i))| ≤ 2 * ε := by
  have hm : |∑ i, p i * δ i| ≤ ε := by
    calc |∑ i, p i * δ i| ≤ ∑ i, |p i * δ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, p i * ε := by
          apply Finset.sum_le_sum; intro i _
          rw [abs_mul, abs_of_nonneg (hp i)]; exact mul_le_mul_of_nonneg_left (hδ i) (hp i)
      _ = ε := by rw [← Finset.sum_mul, hsum, one_mul]
  calc |∑ j, s j * (p j * (δ j - ∑ i, p i * δ i))|
      ≤ ∑ j, |s j * (p j * (δ j - ∑ i, p i * δ i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, p j * (2 * ε) := by
        apply Finset.sum_le_sum; intro j _
        rw [abs_mul, abs_mul, abs_of_nonneg (hp j)]
        have h1 : |δ j - ∑ i, p i * δ i| ≤ 2 * ε := by
          calc |δ j - ∑ i, p i * δ i| ≤ |δ j| + |∑ i, p i * δ i| := abs_sub _ _
            _ ≤ 2 * ε := by linarith [hδ j]
        have h2 : p j * |δ j - ∑ i, p i * δ i| ≤ p j * (2 * ε) :=
          mul_le_mul_of_nonneg_left h1 (hp j)
        calc |s j| * (p j * |δ j - ∑ i, p i * δ i|) ≤ 1 * (p j * (2 * ε)) :=
              mul_le_mul (hs j) h2 (mul_nonneg (hp j) (abs_nonneg _)) zero_le_one
          _ = p j * (2 * ε) := one_mul _
    _ = 2 * ε := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Softmax is Lipschitz from `ℓ∞` scores to `ℓ1` probabilities with constant two, for every
number of positions: `∑_j |p_j(a') - p_j(a)| ≤ 2 ‖a' - a‖_∞`.
Paper: `lem:prefixstability` (attention_moment_decoder.tex), derived from
`d p_j/dt = p_j(ȧ_j - ∑_i p_i ȧ_i)` along a segment. -/
theorem softmax_l1_lipschitz [Nonempty ι] (a a' : ι → ℝ) (ε : ℝ)
    (h : ∀ j, |a' j - a j| ≤ ε) : ∑ j, |softmax a' j - softmax a j| ≤ 2 * ε := by
  classical
  set δ : ι → ℝ := fun j => a' j - a j with hδ
  set s : ι → ℝ := fun j => if 0 ≤ softmax a' j - softmax a j then 1 else -1 with hsdef
  set E : ι → ℝ → ℝ := fun j t => Real.exp (a j + t * δ j) with hEdef
  have hSpos : ∀ t, 0 < ∑ i, E i t := fun t =>
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hE : ∀ j t, HasDerivAt (E j) (E j t * δ j) t := by
    intro j t
    have h1 := (((hasDerivAt_id t).mul_const (δ j)).const_add (a j)).exp
    simpa [hEdef] using h1
  have hS : ∀ t, HasDerivAt (fun t => ∑ i, E i t) (∑ i, E i t * δ i) t := fun t =>
    HasDerivAt.fun_sum fun i _ => hE i t
  set g : ℝ → ℝ := fun t => ∑ j, s j * (E j t / ∑ i, E i t) with hgdef
  set g' : ℝ → ℝ := fun t => ∑ j, s j *
    ((E j t * δ j * (∑ i, E i t) - E j t * ∑ i, E i t * δ i) / (∑ i, E i t) ^ 2) with hg'def
  have hg : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    apply HasDerivAt.fun_sum
    intro j _
    exact ((hE j t).div (hS t) (hSpos t).ne').const_mul (s j)
  have hbound : ∀ t, ‖g' t‖ ≤ 2 * ε := by
    intro t
    have hS0 := hSpos t
    set p : ι → ℝ := fun j => E j t / ∑ i, E i t with hpdef
    have hp0 : ∀ j, 0 ≤ p j := fun j => div_nonneg (Real.exp_pos _).le hS0.le
    have hp1 : ∑ j, p j = 1 := by rw [hpdef, ← Finset.sum_div, div_self hS0.ne']
    have hform : g' t = ∑ j, s j * (p j * (δ j - ∑ i, p i * δ i)) := by
      rw [hg'def]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      rw [hpdef]
      simp only
      have hsd : ∑ x, E x t / (∑ i, E i t) * δ x = (∑ i, E i t * δ i) / ∑ i, E i t := by
        rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => ?_; ring
      rw [hsd]
      field_simp
    rw [Real.norm_eq_abs, hform]
    apply weighted_centered_bound p δ s ε hp0 hp1 (fun j => h j)
    intro j; rw [hsdef]; simp only; split_ifs <;> simp
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g) (f' := g')
    (s := Set.univ) (x := 0) (y := 1) (fun x _ => (hg x).hasDerivWithinAt)
    (fun x _ => hbound x) convex_univ trivial trivial
  have hE1 : ∀ j, E j 1 = Real.exp (a' j) := by intro j; rw [hEdef, hδ]; simp
  have hE0 : ∀ j, E j 0 = Real.exp (a j) := by intro j; rw [hEdef]; simp
  have hdiff : g 1 - g 0 = ∑ j, |softmax a' j - softmax a j| := by
    have hg1 : g 1 = ∑ j, s j * softmax a' j := by
      rw [hgdef]; simp only [hE1]; rfl
    have hg0 : g 0 = ∑ j, s j * softmax a j := by
      rw [hgdef]; simp only [hE0]; rfl
    rw [hg1, hg0, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_sub, hsdef]
    simp only
    split_ifs with hc
    · rw [abs_of_nonneg hc]; ring
    · rw [abs_of_neg (not_le.mp hc)]; ring
  rw [hdiff, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)]
    at hmvt
  simpa using hmvt

/-- The score perturbation separates value error from probability error:
`|∑ p_i v_i - ∑ q_i w_i| ≤ δ + V ∑ |p_i - q_i|`.
Paper: `lem:prefixstability` (attention_moment_decoder.tex). -/
theorem attention_mean_perturbation (p q v w : ι → ℝ) (V δ : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hvw : ∀ i, |v i - w i| ≤ δ)
    (hw : ∀ i, |w i| ≤ V) :
    |∑ i, p i * v i - ∑ i, q i * w i| ≤ δ + V * ∑ i, |p i - q i| := by
  have hid : (∑ i, p i * v i - ∑ i, q i * w i) =
      (∑ i, p i * (v i - w i)) + (∑ i, (p i - q i) * w i) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hid]
  calc |(∑ i, p i * (v i - w i)) + ∑ i, (p i - q i) * w i|
      ≤ |∑ i, p i * (v i - w i)| + |∑ i, (p i - q i) * w i| := abs_add_le _ _
    _ ≤ (∑ i, p i * δ) + ∑ i, |p i - q i| * V := by
        apply add_le_add
        · calc |∑ i, p i * (v i - w i)| ≤ ∑ i, |p i * (v i - w i)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ i, p i * δ := by
                apply Finset.sum_le_sum
                intro i _
                rw [abs_mul, abs_of_nonneg (hp i)]
                exact mul_le_mul_of_nonneg_left (hvw i) (hp i)
        · calc |∑ i, (p i - q i) * w i| ≤ ∑ i, |(p i - q i) * w i| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ i, |p i - q i| * V := by
                apply Finset.sum_le_sum
                intro i _
                rw [abs_mul]
                exact mul_le_mul_of_nonneg_left (hw i) (abs_nonneg _)
    _ = δ + V * ∑ i, |p i - q i| := by
        rw [← Finset.sum_mul, hsum, one_mul, ← Finset.sum_mul]
        ring

/-- Attention is stable in the largest coordinate error, independently of the number of keys:
`|F(a,v) - F(a',v')| ≤ ‖v - v'‖_∞ + 2K‖a - a'‖_∞` when `|v'_j| ≤ K`.
Paper: `lem:prefixstability`, display `eq:attentionstabilitymoment`
(attention_moment_decoder.tex); summarized after `thm:main-decoder` (main_decoder.tex). -/
theorem attention_stability [Nonempty ι] (a a' v v' : ι → ℝ) (K εv εa : ℝ)
    (hv : ∀ j, |v j - v' j| ≤ εv) (hK : ∀ j, |v' j| ≤ K) (ha : ∀ j, |a' j - a j| ≤ εa) :
    |∑ j, softmax a j * v j - ∑ j, softmax a' j * v' j| ≤ εv + 2 * K * εa := by
  have h1 := attention_mean_perturbation (softmax a) (softmax a') v v' K εv
    (softmax_nonneg a) (softmax_sum a) hv hK
  have h2 := softmax_l1_lipschitz a a' εa ha
  have h3 : ∑ j, |softmax a j - softmax a' j| ≤ 2 * εa := by
    simpa [abs_sub_comm] using h2
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK (Classical.arbitrary ι))
  nlinarith

/-- Score perturbation: if `|q_i|, |q'_i|, |k_i|, |k'_i| ≤ K`, `|q_i - q'_i| ≤ δ_q`, and
`|k_i - k'_i| ≤ δ_k`, then the score `β⟨q,k⟩/n` changes by at most `βK(δ_q + δ_k)`.
Paper: `lem:prefixstability` (attention_moment_decoder.tex). -/
theorem score_perturbation {n : ℕ} (hn : 0 < n) (q q' k k' : Fin n → ℝ) (β K δq δk : ℝ)
    (hβ : 0 ≤ β) (hk : ∀ i, |k i| ≤ K) (hq' : ∀ i, |q' i| ≤ K)
    (hdq : ∀ i, |q i - q' i| ≤ δq) (hdk : ∀ i, |k i - k' i| ≤ δk) :
    |β / n * ∑ i, q i * k i - β / n * ∑ i, q' i * k' i| ≤ β * K * (δq + δk) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hk ⟨0, hn⟩)
  rw [← mul_sub, abs_mul, abs_of_nonneg (div_nonneg hβ hnpos.le), ← Finset.sum_sub_distrib]
  have hsum : |∑ i, (q i * k i - q' i * k' i)| ≤ n * (K * (δq + δk)) := by
    calc |∑ i, (q i * k i - q' i * k' i)| ≤ ∑ i, |q i * k i - q' i * k' i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, K * (δq + δk) := by
          apply Finset.sum_le_sum; intro i _
          have e : q i * k i - q' i * k' i = (q i - q' i) * k i + q' i * (k i - k' i) := by ring
          rw [e]
          calc |(q i - q' i) * k i + q' i * (k i - k' i)|
              ≤ |(q i - q' i) * k i| + |q' i * (k i - k' i)| := abs_add_le _ _
            _ = |q i - q' i| * |k i| + |q' i| * |k i - k' i| := by rw [abs_mul, abs_mul]
            _ ≤ δq * K + K * δk := by
                have hδq0 : 0 ≤ δq := le_trans (abs_nonneg _) (hdq i)
                exact add_le_add (mul_le_mul (hdq i) (hk i) (abs_nonneg _) hδq0)
                  (mul_le_mul (hq' i) (hdk i) (abs_nonneg _) hK)
            _ = K * (δq + δk) := by ring
      _ = n * (K * (δq + δk)) := by simp
  calc β / n * |∑ i, (q i * k i - q' i * k' i)| ≤ β / n * (n * (K * (δq + δk))) := by gcongr
    _ = β * K * (δq + δk) := by field_simp

/-- Affine maps of normalized vectors are bounded: with absolute row sum and bias at most `s`
and coordinates at most `X` (for normalized vectors `X = √n`), every output coordinate is at
most `sX + s`; in particular it is at most the power of two `K ≥ s(⌈√n⌉ + 1)`.
Paper: `lem:prefixstability` (attention_moment_decoder.tex). -/
theorem affine_coordinate_bound {n : ℕ} (w x : Fin n → ℝ) (b s X : ℝ) (hX : 0 ≤ X)
    (hw : ∑ j, |w j| ≤ s) (hb : |b| ≤ s) (hx : ∀ j, |x j| ≤ X) :
    |∑ j, w j * x j + b| ≤ s * X + s := by
  calc |∑ j, w j * x j + b| ≤ |∑ j, w j * x j| + |b| := abs_add_le _ _
    _ ≤ ∑ j, |w j| * X + s := by
        gcongr
        calc |∑ j, w j * x j| ≤ ∑ j, |w j * x j| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j, |w j| * X := by
              apply Finset.sum_le_sum; intro j _
              rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _)
    _ ≤ s * X + s := by rw [← Finset.sum_mul]; gcongr

/-- Depth recurrence: if every stage has Lipschitz bound `L ≥ 1` and local error at most `δ`,
then `e_J ≤ J L^J δ`. (For the assembled network on prefix arrays see
`ExactSampling.Stability.error_induction` and `ExactSampling.Stability.prefix_network_error`.)
Paper: `lem:prefixstability` (attention_moment_decoder.tex), "induction bounds the final error
by `J L₀^J δ`". -/
theorem depth_error (e : ℕ → ℝ) (L δ : ℝ) (hL : 1 ≤ L) (hδ : 0 ≤ δ) (h0 : e 0 = 0)
    (hstep : ∀ j, e (j + 1) ≤ L * e j + δ) (J : ℕ) : e J ≤ J * L ^ J * δ := by
  induction J with
  | zero => simp [h0]
  | succ J ih =>
    have hLJ : 1 ≤ L ^ J := one_le_pow₀ hL
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    calc e (J + 1) ≤ L * e J + δ := hstep J
      _ ≤ L * (J * L ^ J * δ) + δ := by gcongr
      _ ≤ L * (J * L ^ J * δ) + L ^ (J + 1) * δ := by
          have : 1 ≤ L ^ (J + 1) := one_le_pow₀ hL
          nlinarith
      _ = ((J + 1 : ℕ) : ℝ) * L ^ (J + 1) * δ := by push_cast; ring

/-- Depth induction for actual stages: exact states `x_{j+1} = f_j(x_j)` with `L`-Lipschitz
stages (`L ≥ 1`) on any pseudometric space and computed states with local error at most `δ` after
each stage, from the same input, satisfy `dist(y_J, x_J) ≤ J L^J δ`.
Paper: `lem:prefixstability` (attention_moment_decoder.tex). -/
theorem depth_error_of_lipschitz {X : Type*} [PseudoMetricSpace X] (f : ℕ → X → X) (L : NNReal)
    (hL : 1 ≤ (L : ℝ)) (hf : ∀ j, LipschitzWith L (f j)) (x y : ℕ → X) (δ : ℝ) (hδ : 0 ≤ δ)
    (hx : ∀ j, x (j + 1) = f j (x j)) (hy0 : y 0 = x 0)
    (hy : ∀ j, dist (y (j + 1)) (f j (y j)) ≤ δ) (J : ℕ) :
    dist (y J) (x J) ≤ J * (L : ℝ) ^ J * δ := by
  apply depth_error (fun j => dist (y j) (x j)) L δ hL hδ (by simp [hy0])
  intro j
  calc dist (y (j + 1)) (x (j + 1)) ≤ dist (y (j + 1)) (f j (y j)) + dist (f j (y j)) (x (j + 1)) :=
        dist_triangle _ _ _
    _ ≤ δ + L * dist (y j) (x j) := by
        rw [hx j]; exact add_le_add (hy j) ((hf j).dist_le_mul _ _)
    _ = L * dist (y j) (x j) + δ := by ring

/-- The precision guard: if `J + 1 ≤ 2^a`, `L ≤ 2^c`, and `P ≥ p + a + Jc + 10`, then the depth
error `J L^J 2^{-P}` is below `2^{-p-10}`.
Paper: `lem:prefixstability` (attention_moment_decoder.tex), the choice
`P ≥ p + ⌈log₂(J+1)⌉ + J⌈log₂ L₀⌉ + 10`. -/
theorem depth_precision (J p a c P : ℕ) (L : ℝ) (hL : 1 ≤ L) (ha : (J : ℝ) + 1 ≤ 2 ^ a)
    (hc : L ≤ 2 ^ c) (hP : p + a + J * c + 10 ≤ P) :
    J * L ^ J * (2 : ℝ)⁻¹ ^ P ≤ (2 : ℝ)⁻¹ ^ (p + 10) := by
  have hJ : (J : ℝ) ≤ 2 ^ a := by linarith
  have hLJ : L ^ J ≤ (2 : ℝ) ^ (J * c) := by
    rw [mul_comm, pow_mul]; exact pow_le_pow_left₀ (by linarith) hc J
  have h2 : (2 : ℝ)⁻¹ ^ P ≤ (2 : ℝ)⁻¹ ^ (p + a + J * c + 10) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hP
  calc J * L ^ J * (2 : ℝ)⁻¹ ^ P ≤ 2 ^ a * 2 ^ (J * c) * (2 : ℝ)⁻¹ ^ (p + a + J * c + 10) := by
        gcongr
    _ = (2 : ℝ)⁻¹ ^ (p + 10) := by
        rw [show p + a + J * c + 10 = (p + 10) + a + J * c by ring, pow_add, pow_add,
          inv_pow (2 : ℝ) a, inv_pow (2 : ℝ) (J * c)]
        field_simp

end Stability

/-! ## The affine head (`cor:affineheadmoment`) -/

section AffineHead

/-- Residual range after `D` blocks: if the embedding range is at most `s` and each block adds
at most `sK + s + 1` (attention output map and tanh update), then the range is at most
`R_D = s + D(sK + s + 1)`. Paper: `cor:affineheadmoment` (attention_moment_decoder.tex). -/
theorem residual_range (R : ℕ → ℝ) (s K : ℝ) (h0 : R 0 ≤ s)
    (hstep : ∀ j, R (j + 1) ≤ R j + (s * K + s + 1)) (D : ℕ) :
    R D ≤ s + D * (s * K + s + 1) := by
  induction D with
  | zero => simpa using h0
  | succ D ih => have := hstep D; push_cast; linarith

/-- After subtracting the largest rational upper endpoint `A` of logit enclosures of width at
most `1/4`, the shifted softmax denominator is `S = ∑ e^{z_i - A} ≥ e^{-1/4} > 1/2`.
Paper: `cor:affineheadmoment` (attention_moment_decoder.tex). -/
theorem shifted_denominator {V : Type*} [Fintype V] (z : V → ℝ) (A : ℝ) (i0 : V)
    (hi0 : -(1 / 4) ≤ z i0 - A) :
    Real.exp (-(1 / 4)) ≤ ∑ i, Real.exp (z i - A) ∧ (1 / 2 : ℝ) < Real.exp (-(1 / 4)) := by
  constructor
  · calc Real.exp (-(1 / 4)) ≤ Real.exp (z i0 - A) := Real.exp_le_exp.mpr hi0
      _ ≤ ∑ i, Real.exp (z i - A) :=
        Finset.single_le_sum (f := fun i => Real.exp (z i - A))
          (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ i0)
  · have := Real.add_one_lt_exp (show (-(1 / 4 : ℝ)) ≠ 0 by norm_num)
    linarith

/-- Outward interval division: with `N ≤ S`, `S > 1/2`, and errors `δ ≤ S/2`, the quotient
enclosure has width `(N+δ)/(S-δ) - (N-δ)/(S+δ) ≤ 16δ/(3S) ≤ 11δ`; for `δ = 2^{-p}/64` this is
below `2^{-p-2}`. Paper: `cor:affineheadmoment` (attention_moment_decoder.tex). -/
theorem division_width (N S δ : ℝ) (hS : 1 / 2 < S) (hNS : N ≤ S)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ S / 2) :
    (N + δ) / (S - δ) - (N - δ) / (S + δ) ≤ 16 * δ / (3 * S) ∧ 16 * δ / (3 * S) ≤ 11 * δ := by
  have hSpos : 0 < S := by linarith
  have h1 : 0 < S - δ := by linarith
  have h2 : 0 < S + δ := by linarith
  constructor
  · rw [div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (mul_pos h1 h2) (by positivity)]
    have hden : 3 * S ^ 2 / 4 ≤ (S - δ) * (S + δ) := by nlinarith
    have hnum : (N + δ) * (S + δ) - (S - δ) * (N - δ) = 2 * δ * (N + S) := by ring
    rw [hnum]
    nlinarith [mul_nonneg hδ0 hSpos.le]
  · rw [div_le_iff₀ (by positivity)]; nlinarith

/-- With `δ = 2^{-p}/64`, the width bound `11δ` is below `2^{-p-2}`.
Paper: `cor:affineheadmoment` (attention_moment_decoder.tex). -/
theorem division_width_precision (p : ℕ) :
    11 * ((2 : ℝ)⁻¹ ^ p / 64) < (2 : ℝ)⁻¹ ^ (p + 2) := by
  rw [pow_add]; have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ p := by positivity
  nlinarith

end AffineHead

/-! ## Specified feedforward families (`cor:momentgeluswiglu`) -/

section Feedforward

/-- The logistic sigmoid `σ(v) = 1/(1 + e^{-v})`. -/
noncomputable def sigmoid (v : ℝ) : ℝ := 1 / (1 + Real.exp (-v))

/-- Auxiliary: `σ > 0`. Supports `cor:momentgeluswiglu` (attention_moment_decoder.tex). -/
lemma sigmoid_pos (v : ℝ) : 0 < sigmoid v := by unfold sigmoid; positivity

/-- Auxiliary: `σ < 1`. Supports `cor:momentgeluswiglu` (attention_moment_decoder.tex). -/
lemma sigmoid_lt_one (v : ℝ) : sigmoid v < 1 := by
  unfold sigmoid
  rw [div_lt_one (by positivity)]
  linarith [Real.exp_pos (-v)]

/-- `σ' = σ(1 - σ)`. Paper: `cor:momentgeluswiglu` (attention_moment_decoder.tex). -/
theorem hasDerivAt_sigmoid (v : ℝ) :
    HasDerivAt sigmoid (sigmoid v * (1 - sigmoid v)) v := by
  have h1 : HasDerivAt (fun v => 1 + Real.exp (-v)) (-Real.exp (-v)) v := by
    have := ((hasDerivAt_neg v).exp).const_add 1
    simpa using this
  have h2 := (hasDerivAt_const v (1 : ℝ)).div h1 (by positivity)
  have hfun : ((fun _ : ℝ => (1 : ℝ)) / fun v => 1 + Real.exp (-v)) = sigmoid := by
    funext x; simp [sigmoid]
  rw [hfun] at h2
  convert h2 using 1
  unfold sigmoid
  field_simp
  ring

/-- `0 ≤ σ' ≤ 1/4`. Paper: `cor:momentgeluswiglu` (attention_moment_decoder.tex). -/
theorem sigmoid_deriv_bounds (v : ℝ) :
    0 ≤ sigmoid v * (1 - sigmoid v) ∧ sigmoid v * (1 - sigmoid v) ≤ 1 / 4 := by
  have h0 := sigmoid_pos v
  have h1 := sigmoid_lt_one v
  constructor
  · exact mul_nonneg h0.le (by linarith)
  · nlinarith [sq_nonneg (sigmoid v - 1 / 2)]

/-- SwiGLU coordinate `w(u,v) = u v σ(v)`: on `|u|, |v| ≤ K` one has `|w| ≤ K²`,
`|∂_u w| ≤ K`, and `|∂_v w| = |u(σ(v) + vσ'(v))| ≤ K(1 + K/4)`; hence its Lipschitz constant
for the two-coordinate maximum norm is at most `2K + K²/4`.
Paper: `cor:momentgeluswiglu` (attention_moment_decoder.tex). -/
theorem swiglu_bounds (u v K : ℝ) (hu : |u| ≤ K) (hv : |v| ≤ K) :
    |u * v * sigmoid v| ≤ K ^ 2 ∧ |v * sigmoid v| ≤ K ∧
      |u * (sigmoid v + v * (sigmoid v * (1 - sigmoid v)))| ≤ K * (1 + K / 4) ∧
      |v * sigmoid v| + |u * (sigmoid v + v * (sigmoid v * (1 - sigmoid v)))| ≤
        2 * K + K ^ 2 / 4 := by
  have hσ0 := sigmoid_pos v
  have hσ1 := sigmoid_lt_one v
  obtain ⟨hd0, hd1⟩ := sigmoid_deriv_bounds v
  have hK : 0 ≤ K := le_trans (abs_nonneg _) hu
  have hσabs : |sigmoid v| ≤ 1 := by rw [abs_of_pos hσ0]; exact hσ1.le
  have hA : |v * sigmoid v| ≤ K := by
    rw [abs_mul]; calc |v| * |sigmoid v| ≤ K * 1 := by gcongr
      _ = K := mul_one K
  have hB : |sigmoid v + v * (sigmoid v * (1 - sigmoid v))| ≤ 1 + K / 4 := by
    calc |sigmoid v + v * (sigmoid v * (1 - sigmoid v))|
        ≤ |sigmoid v| + |v * (sigmoid v * (1 - sigmoid v))| := abs_add_le _ _
      _ = |sigmoid v| + |v| * (sigmoid v * (1 - sigmoid v)) := by
          rw [abs_mul, abs_of_nonneg hd0]
      _ ≤ 1 + K * (1 / 4) := by gcongr
      _ = 1 + K / 4 := by ring
  have hC : |u * (sigmoid v + v * (sigmoid v * (1 - sigmoid v)))| ≤ K * (1 + K / 4) := by
    rw [abs_mul]; gcongr
  refine ⟨?_, hA, hC, ?_⟩
  · rw [mul_assoc, abs_mul]
    calc |u| * |v * sigmoid v| ≤ K * K := by gcongr
      _ = K ^ 2 := by ring
  · nlinarith

/-- The partial derivative of `w(u,v) = u v σ(v)` in `v` is `u(σ(v) + vσ'(v))`.
Paper: `cor:momentgeluswiglu` (attention_moment_decoder.tex). -/
theorem hasDerivAt_swiglu_v (u v : ℝ) :
    HasDerivAt (fun v => u * v * sigmoid v)
      (u * (sigmoid v + v * (sigmoid v * (1 - sigmoid v)))) v := by
  have h := ((hasDerivAt_id v).const_mul u).mul (hasDerivAt_sigmoid v)
  have hfun : ((fun y => u * id y) * sigmoid) = fun v => u * v * sigmoid v := by
    funext y; simp
  rw [hfun] at h
  convert h using 1
  simp; ring

/-- The standard normal density is at most one: `(2π)^{-1/2} e^{-u²/2} ≤ 1`.
Paper: `cor:momentgeluswiglu` (attention_moment_decoder.tex), "`0 ≤ φ ≤ 1`". -/
theorem normal_density_le_one (u : ℝ) :
    0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(u ^ 2) / 2) ∧
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(u ^ 2) / 2) ≤ 1 := by
  have hpi : 1 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.one_le_sqrt]; nlinarith [Real.pi_gt_three]
  have he : Real.exp (-(u ^ 2) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u])
  constructor
  · positivity
  · calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(u ^ 2) / 2) ≤ 1 * 1 := by
          gcongr
          · exact inv_le_one_of_one_le₀ hpi
      _ = 1 := one_mul 1

/-- GELU bounds on `|u| ≤ K`: for any `cdf ∈ [0,1]` (the value `Φ(u)`) and `dens ∈ [0,1]` (the
value `φ(u)`), `|u·cdf| ≤ K` and `|cdf + u·dens| ≤ 1 + K`; with `g' = Φ + uφ` (not proved here)
these are the range and derivative bounds of `g(u) = uΦ(u)`.
Paper: `cor:momentgeluswiglu` (attention_moment_decoder.tex). -/
theorem gelu_bounds (u K cdf dens : ℝ) (hu : |u| ≤ K) (hΦ0 : 0 ≤ cdf) (hΦ1 : cdf ≤ 1)
    (hφ0 : 0 ≤ dens) (hφ1 : dens ≤ 1) : |u * cdf| ≤ K ∧ |cdf + u * dens| ≤ 1 + K := by
  have hK : 0 ≤ K := le_trans (abs_nonneg _) hu
  constructor
  · rw [abs_mul, abs_of_nonneg hΦ0]
    calc |u| * cdf ≤ K * 1 := by gcongr
      _ = K := mul_one K
  · calc |cdf + u * dens| ≤ |cdf| + |u * dens| := abs_add_le _ _
      _ = cdf + |u| * dens := by rw [abs_of_nonneg hΦ0, abs_mul, abs_of_nonneg hφ0]
      _ ≤ 1 + K * 1 := by gcongr
      _ = 1 + K := by ring

end Feedforward

/-! ## Fixed positional rotations (`cor:fixedpositionalrotation`) -/

section Rotation

/-- A coordinate-pair rotation has maximum absolute row sum at most `√2`, uniformly in the
angle. Paper: `cor:fixedpositionalrotation` (attention_moment_decoder.tex). -/
theorem rotation_row_sum (θ : ℝ) : |Real.cos θ| + |Real.sin θ| ≤ Real.sqrt 2 := by
  apply Real.le_sqrt_of_sq_le
  have h := Real.cos_sq_add_sin_sq θ
  have hc := sq_abs (Real.cos θ)
  have hs := sq_abs (Real.sin θ)
  nlinarith [sq_nonneg (|Real.cos θ| - |Real.sin θ|)]

/-- The period index is bounded: if `|θ₀| ≤ T|ω| + 1`, `π₀ ≥ 3`, `T ≥ 1` (positions are at least
one), and `C ≥ 1 + |ω|`, then `k = ⌊θ₀/(2π₀)⌋` satisfies `|k| ≤ C(T+1)`.
Paper: `cor:fixedpositionalrotation` (attention_moment_decoder.tex). -/
theorem reduced_index_bound (θ0 π0 ω C T : ℝ) (hθ : |θ0| ≤ T * |ω| + 1) (hπ : 3 ≤ π0)
    (hT : 1 ≤ T) (hC : 1 + |ω| ≤ C) : |((⌊θ0 / (2 * π0)⌋ : ℤ) : ℝ)| ≤ C * (T + 1) := by
  have hpos : 0 < 2 * π0 := by linarith
  set x := θ0 / (2 * π0)
  have hx : |x| ≤ (T * |ω| + 1) / 6 := by
    rw [abs_div, abs_of_pos hpos, div_le_div_iff₀ hpos (by norm_num)]
    have := abs_nonneg θ0
    nlinarith [abs_nonneg ω]
  have hfl : |((⌊x⌋ : ℤ) : ℝ)| ≤ |x| + 1 := by
    have h1 := Int.floor_le x
    have h2 := Int.lt_floor_add_one x
    rw [abs_le]; constructor <;> linarith [abs_le.mp (le_refl |x|), neg_abs_le x, le_abs_self x]
  have hω := abs_nonneg ω
  have : (T * |ω| + 1) / 6 + 1 ≤ (1 + |ω|) * (T + 1) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ T) hω]
  calc |((⌊x⌋ : ℤ) : ℝ)| ≤ |x| + 1 := hfl
    _ ≤ (T * |ω| + 1) / 6 + 1 := by linarith
    _ ≤ (1 + |ω|) * (T + 1) := this
    _ ≤ C * (T + 1) := by gcongr

/-- Reduced-argument error: with `|tω - θ₀| ≤ 2^{-p-10}`, `|k| ≤ C(T+1)` (derived in
`reduced_index_bound`), and `|π - π₀| ≤ 2^{-p-10}/(C(T+1))`, the reduced argument
`u = tω - 2kπ` differs from `u₀ = θ₀ - 2kπ₀` by at most `3·2^{-p-10}`.
Paper: `cor:fixedpositionalrotation` (attention_moment_decoder.tex). -/
theorem reduced_argument_error (tω θ0 π0 C T : ℝ) (k : ℤ) (p : ℕ) (hCT : 0 < C * (T + 1))
    (hθ : |tω - θ0| ≤ (2 : ℝ)⁻¹ ^ (p + 10)) (hk : |(k : ℝ)| ≤ C * (T + 1))
    (hπ : |Real.pi - π0| ≤ (2 : ℝ)⁻¹ ^ (p + 10) / (C * (T + 1))) :
    |(tω - 2 * k * Real.pi) - (θ0 - 2 * k * π0)| ≤ 3 * (2 : ℝ)⁻¹ ^ (p + 10) := by
  have e : (tω - 2 * k * Real.pi) - (θ0 - 2 * k * π0) =
      (tω - θ0) - 2 * k * (Real.pi - π0) := by ring
  rw [e]
  have h2 : |2 * (k : ℝ) * (Real.pi - π0)| ≤ 2 * (2 : ℝ)⁻¹ ^ (p + 10) := by
    rw [abs_mul, abs_mul, abs_two]
    calc 2 * |(k : ℝ)| * |Real.pi - π0|
        ≤ 2 * (C * (T + 1)) * ((2 : ℝ)⁻¹ ^ (p + 10) / (C * (T + 1))) := by gcongr
      _ = 2 * (2 : ℝ)⁻¹ ^ (p + 10) := by
          have hne : C * (T + 1) ≠ 0 := hCT.ne'
          rw [mul_assoc, mul_div_assoc', mul_comm (C * (T + 1)), mul_div_assoc, div_self hne,
            mul_one]
  calc |(tω - θ0) - 2 * k * (Real.pi - π0)| ≤ |tω - θ0| + |2 * (k : ℝ) * (Real.pi - π0)| :=
        abs_sub _ _
    _ ≤ 3 * (2 : ℝ)⁻¹ ^ (p + 10) := by linarith

/-- With `k = ⌊θ₀/(2π₀)⌋` and `π₀ ∈ [3,4]`, the reduced dyadic argument
`u₀ = θ₀ - 2kπ₀` lies in `[0, 8)`. Paper: `cor:fixedpositionalrotation`
(attention_moment_decoder.tex). -/
theorem reduced_argument_range (θ0 π0 : ℝ) (hπ0 : 3 ≤ π0 ∧ π0 ≤ 4) :
    0 ≤ θ0 - 2 * ⌊θ0 / (2 * π0)⌋ * π0 ∧ θ0 - 2 * ⌊θ0 / (2 * π0)⌋ * π0 < 8 := by
  have hpos : 0 < 2 * π0 := by linarith
  have h1 := Int.floor_le (θ0 / (2 * π0))
  have h2 := Int.lt_floor_add_one (θ0 / (2 * π0))
  have e1 : (⌊θ0 / (2 * π0)⌋ : ℝ) * (2 * π0) ≤ θ0 := by
    have := mul_le_mul_of_nonneg_right h1 hpos.le
    rwa [div_mul_cancel₀ _ hpos.ne'] at this
  have e2 : θ0 < ((⌊θ0 / (2 * π0)⌋ : ℝ) + 1) * (2 * π0) := by
    have := mul_lt_mul_of_pos_right h2 hpos
    rwa [div_mul_cancel₀ _ hpos.ne'] at this
  constructor <;> nlinarith

/-- The numerical Taylor remainder for sine and cosine on `[0,8]` at degree `N = 32(p+8)`:
`8^{N+1}/(N+1)! < 2^{-p-6}`. Paper: `cor:fixedpositionalrotation`
(attention_moment_decoder.tex). -/
theorem rotation_taylor_remainder (p : ℕ) :
    (8 : ℝ) ^ (32 * (p + 8) + 1) / (32 * (p + 8) + 1)! < (2 : ℝ)⁻¹ ^ (p + 6) := by
  obtain ⟨n, hn⟩ : ∃ n, n = 32 * (p + 8) + 1 := ⟨_, rfl⟩
  rw [← hn]
  have h1 := Real.pow_div_factorial_le_exp (32 : ℝ) (by norm_num) n
  have he : Real.exp 32 < 2 ^ 47 := by
    have h := Real.exp_one_lt_d9
    have : Real.exp 32 = Real.exp 1 ^ 32 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc Real.exp 1 ^ 32 < (2.7182818286 : ℝ) ^ 32 := by
          gcongr
      _ < 2 ^ 47 := by norm_num
  have h32 : (32 : ℝ) ^ n = 4 ^ n * 8 ^ n := by rw [← mul_pow]; norm_num
  rw [h32] at h1
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have hle : (8 : ℝ) ^ n / n ! ≤ Real.exp 32 / 4 ^ n := by
    rw [le_div_iff₀ h4]
    calc 8 ^ n / (n ! : ℝ) * 4 ^ n = 4 ^ n * 8 ^ n / n ! := by ring
      _ ≤ Real.exp 32 := h1
  calc (8 : ℝ) ^ n / n ! ≤ Real.exp 32 / 4 ^ n := hle
    _ < 2 ^ 47 / 4 ^ n := by gcongr
    _ ≤ (2 : ℝ)⁻¹ ^ (p + 6) := by
        have h4n : (4 : ℝ) ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
        rw [h4n, inv_pow, div_le_iff₀ (by positivity), ← div_eq_inv_mul,
          le_div_iff₀ (by positivity), ← pow_add]
        exact pow_le_pow_right₀ (by norm_num) (by omega)

end Rotation

/-! ## A completely fixed model (`cor:fixedmodelcontext`) -/

/-- Exponent bookkeeping for a fixed model: if `m ≤ cℓ` and `L ≤ cℓ²` with `ℓ = log(T+2) ≥ 1`,
then `(m+1)^{2r+4} L^4 ≤ (c+1)^{2r+4} c^4 ℓ^{2r+12}`. (The expected-cost statement itself is
`ExactSampling.FixedModel.fixedModel_expected_isBigO`.)
Paper: `cor:fixedmodelcontext` (attention_moment_decoder.tex), exponent `2r + 12`; also stated
after `thm:main-decoder` (main_decoder.tex). -/
theorem fixed_model_exponent (r : ℕ) (m L c ℓ : ℝ) (hm0 : 0 ≤ m) (hL0 : 0 ≤ L) (hc : 0 ≤ c)
    (hℓ : 1 ≤ ℓ) (hm : m ≤ c * ℓ) (hL : L ≤ c * ℓ ^ 2) :
    (m + 1) ^ (2 * r + 4) * L ^ 4 ≤ (c + 1) ^ (2 * r + 4) * c ^ 4 * ℓ ^ (2 * r + 12) := by
  have h1 : m + 1 ≤ (c + 1) * ℓ := by nlinarith
  have h2 : (m + 1) ^ (2 * r + 4) ≤ ((c + 1) * ℓ) ^ (2 * r + 4) :=
    pow_le_pow_left₀ (by linarith) h1 _
  have h3 : L ^ 4 ≤ (c * ℓ ^ 2) ^ 4 := pow_le_pow_left₀ hL0 hL 4
  calc (m + 1) ^ (2 * r + 4) * L ^ 4 ≤ ((c + 1) * ℓ) ^ (2 * r + 4) * (c * ℓ ^ 2) ^ 4 := by
        gcongr
    _ = (c + 1) ^ (2 * r + 4) * c ^ 4 * ℓ ^ (2 * r + 12) := by
        rw [mul_pow, mul_pow, ← pow_mul]; ring

end ExactSampling.MomentDecoder
