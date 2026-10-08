import Mathlib

/-!
# GELU and sigmoid-gated feed-forward rows

This module formalizes the quantitative content of `sec:practical-feedforward`
(normalization_ffn.tex): `lem:gelu-swiglu`, `lem:bipolar-amplification`,
`cor:radius-reduction`, and the activation-level steps of `thm:real-ffn-lower` and
`cor:real-ffn-scheduled`.

Formalized here:
* the logistic function `σ(v) = 1/(1 + e^{-v})`, `σ(v) + σ(-v) = 1`, `σ(v) = (1 + tanh(v/2))/2`,
  and the antisymmetric identity `SiLU(v) - SiLU(-v) = v`;
* the error function `erf x = (2/√π)∫₀ˣ e^{-t²} dt`, its oddness, `GELU(v) = (v/2)(1 + erf(v/√2))`,
  the identity `GELU(v) - GELU(-v) = v`, and `1/2 < φ(1) < 1` for both activations;
* the exact sign factories of `lem:gelu-swiglu`: the GELU half-mixture, the gated GELU product,
  the SwiGLU gate `σ(v) = (1 + tanh(v/2))/2`, their means and expected request counts
  `3/2 + A²/2`, `5/2 + A²/2` and `2 + 2ρ(1+ρ)` (the last given the tanh-factory count
  `2ρ(1+ρ)` of `cor:comptanhrow`), the row radius `A = 1 + sG`, the tanh radius `ρ = sG/2`,
  and the affine projection radius `b₀ + s₀U`;
* `lem:bipolar-amplification`: the two affine Bernoulli changes, their slack, the output bias
  `(1 + Cz)/2 ∈ [1/4, 3/4]`, and the request count `722C(C+1) ≤ 1444C²` from Huber's `9.5C/e`;
* `cor:radius-reduction`: thinning when `R ≤ 2U`, amplification by `C = R/(2U)` otherwise, and the
  count `max{1, 361(R/U)²}`;
* in `thm:real-ffn-lower`: the hidden-unit construction (features gain `y = sF/√v`, carriers move
  by `-c`), the bound `|mean| ≤ √(v/η)` and the update radius `s/√η ≤ 2s`, the row norms, the
  readout bound `|logit| ≤ 1/√3 < 1`, the full-cube floor identity, and the supplied radii
  `R_j ≤ 4s r_j` with the floor `γ_* = 1/(192 s²)`.

Not formalized: the randomized factories themselves (Huber's linear factory, the erf factory of
`lem:erffactory`, the tanh factory of `cor:comptanhrow`); their request counts enter only as the
numbers they supply (Huber's `9.5C/e`, the erf count `1 + 2c²`, the tanh count `2ρ(1+ρ)`). The
bit-complexity estimates are not formalized. The depth recurrences and the query bounds of
`thm:real-ffn-lower` and `cor:real-ffn-scheduled` are formalized in
`ExactSampling.AdditiveNormalizedGain` (`ffn_lower`, `ffn_scheduled_lower`).
-/

open Real Finset MeasureTheory
open scoped BigOperators

namespace ExactSampling.FeedForward

/-! ## The logistic function and SiLU -/

/-- The logistic function `σ(v) = 1/(1 + e^{-v})`.
Paper: `sec:practical-feedforward` (normalization_ffn.tex). -/
noncomputable def sigma (v : ℝ) : ℝ := 1 / (1 + exp (-v))

/-- `SiLU(v) = v σ(v)`. -/
noncomputable def silu (v : ℝ) : ℝ := v * sigma v

/-- `σ(v) + σ(-v) = 1`.
Paper: proof of `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem sigma_add_sigma_neg (v : ℝ) : sigma v + sigma (-v) = 1 := by
  unfold sigma
  have h1 : 0 < 1 + exp (-v) := by positivity
  have h2 : 0 < 1 + exp (- -v) := by positivity
  rw [neg_neg] at h2 ⊢
  have hm : exp (-v) * exp v = 1 := by rw [← exp_add]; simp
  field_simp
  linear_combination (-1 : ℝ) * hm

/-- The logistic gate is the positive outcome of a `tanh(v/2)` sign: `σ(v) = (1 + tanh(v/2))/2`.
Paper: proof of `lem:gelu-swiglu` (normalization_ffn.tex). -/
theorem sigma_eq_tanh (v : ℝ) : sigma v = (1 + tanh (v / 2)) / 2 := by
  unfold sigma
  rw [tanh_eq]
  have hp := exp_pos (v / 2)
  have hn := exp_pos (-(v / 2))
  have h1 : exp (-v) = exp (-(v / 2)) * exp (-(v / 2)) := by rw [← exp_add]; ring_nf
  have h2 : exp (v / 2) * exp (-(v / 2)) = 1 := by rw [← exp_add]; simp
  rw [h1]
  field_simp
  nlinarith [h2]

/-- The identity used by a pair of sigmoid-gated hidden units, after substituting the logistic
symmetry: `z p - (-z(1 - p)) = z`.
Paper: proof of `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem sigmoid_pair_identity (z p : ℝ) : z * p - (-z * (1 - p)) = z := by
  ring

/-- `SiLU(v) - SiLU(-v) = v`.
Paper: proof of `thm:real-ffn-lower` (normalization_ffn.tex); `sec:additive-main`
(main_normalization.tex). -/
theorem silu_antisymmetric (v : ℝ) : silu v - silu (-v) = v := by
  unfold silu
  have h := sigma_add_sigma_neg v
  rw [show sigma (-v) = 1 - sigma v by linarith]
  exact sigmoid_pair_identity v (sigma v)

/-- `1/2 < SiLU(1) = σ(1) < 1`.
Paper: proof of `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem silu_one_mem : 1 / 2 < silu 1 ∧ silu 1 < 1 := by
  unfold silu sigma
  rw [one_mul]
  have h := exp_pos (-1 : ℝ)
  have h1 : exp (-1 : ℝ) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
  constructor
  · rw [lt_div_iff₀ (by positivity)]; linarith
  · rw [div_lt_one (by positivity)]; linarith

/-! ## The error function and GELU -/

/-- `erf x = (2/√π) ∫₀ˣ e^{-t²} dt`.
Paper: `sec:practical-feedforward` (normalization_ffn.tex), with `sec:gaussianrms`
(normalization_gaussian.tex). -/
noncomputable def erf (x : ℝ) : ℝ := 2 / √π * ∫ t in (0 : ℝ)..x, exp (-t ^ 2)

/-- `GELU(v) = (v/2)(1 + erf(v/√2)) = vΦ(v)`.
Paper: `sec:practical-feedforward` (normalization_ffn.tex). -/
noncomputable def gelu (v : ℝ) : ℝ := v / 2 * (1 + erf (v / √2))

/-- The error function is odd.
Paper: proof of `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem erf_neg (x : ℝ) : erf (-x) = -erf x := by
  unfold erf
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := x) (fun t : ℝ => exp (-t ^ 2))
  simp only [neg_sq, neg_zero] at h
  have h2 : ∫ t in (0 : ℝ)..-x, exp (-t ^ 2) = -∫ t in (-x)..0, exp (-t ^ 2) :=
    intervalIntegral.integral_symm _ _
  rw [h2, ← h]
  ring

/-- The identity used by paired GELU hidden units, after the oddness of `erf`:
`z(1+e)/2 - (-z(1-e)/2) = z`.
Paper: proof of `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem gelu_pair_identity (z e : ℝ) : z * (1 + e) / 2 - (-z * (1 - e) / 2) = z := by
  ring

/-- `GELU(v) - GELU(-v) = v`.
Paper: proof of `thm:real-ffn-lower` (normalization_ffn.tex); `sec:additive-main`
(main_normalization.tex). -/
theorem gelu_antisymmetric (v : ℝ) : gelu v - gelu (-v) = v := by
  unfold gelu
  rw [show -v / √2 = -(v / √2) by ring, erf_neg]
  have := gelu_pair_identity v (erf (v / √2))
  linarith

/-- For `c > 0`, `0 < erf c ≤ (2/√π) c`. -/
theorem erf_bounds {c : ℝ} (hc : 0 < c) : 0 < erf c ∧ erf c ≤ 2 / √π * c := by
  unfold erf
  have hs : 0 < √π := sqrt_pos.2 pi_pos
  have hlow : c * exp (-c ^ 2) ≤ ∫ t in (0 : ℝ)..c, exp (-t ^ 2) := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hc.le
      (f := fun _ => exp (-c ^ 2)) (g := fun t => exp (-t ^ 2))
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
      (fun t ht => by
        apply exp_le_exp.2
        have := ht.1; have := ht.2
        nlinarith)
    simpa using h
  have hup : ∫ t in (0 : ℝ)..c, exp (-t ^ 2) ≤ c := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hc.le
      (f := fun t => exp (-t ^ 2)) (g := fun _ => (1 : ℝ))
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
      (fun t _ => by rw [Real.exp_le_one_iff]; nlinarith)
    simpa using h
  constructor
  · have : 0 < c * exp (-c ^ 2) := by positivity
    have : 0 < ∫ t in (0 : ℝ)..c, exp (-t ^ 2) := by linarith
    positivity
  · exact mul_le_mul_of_nonneg_left hup (by positivity)

/-- `1/2 < GELU(1) < 1`, since `0 < erf(1/√2) ≤ √(2/π) < 1`.
Paper: proof of `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem gelu_one_mem : 1 / 2 < gelu 1 ∧ gelu 1 < 1 := by
  have h2 : (0 : ℝ) < √2 := by positivity
  have hc : (0 : ℝ) < 1 / √2 := by positivity
  obtain ⟨h0, h1⟩ := erf_bounds hc
  have hs : 0 < √π := sqrt_pos.2 pi_pos
  have hlt : 2 / √π * (1 / √2) < 1 := by
    rw [div_mul_div_comm, mul_one, div_lt_one (by positivity), ← sqrt_mul pi_pos.le]
    have : (2 : ℝ) = √4 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]
    rw [this]
    exact sqrt_lt_sqrt (by norm_num) (by nlinarith [pi_gt_three])
  unfold gelu
  rw [one_div (√2)] at h0 h1 hlt
  rw [show (1 : ℝ) / √2 = (√2)⁻¹ by ring]
  constructor <;> nlinarith

/-! ## Exact GELU and gated-product interfaces (`lem:gelu-swiglu`) -/

/-- The GELU half-mixture: with probability one half return a `v/A` sign, otherwise the product
of an independent `v/A` sign and an `erf(v/√2)` sign. The mean is `GELU(v)/A`.
Paper: proof of `lem:gelu-swiglu` (normalization_ffn.tex). -/
theorem gelu_mixture_identity (v A : ℝ) (hA : A ≠ 0) :
    (1 / 2 : ℝ) * (v / A) + (1 / 2 : ℝ) * ((v / A) * erf (v / √2)) = gelu v / A := by
  unfold gelu; field_simp

/-- The argument of the erf factory: `c z = v/√2` for `c = A/√2` and `z = v/A`, and its source
count `1 + 2c² = 1 + A²`.
Paper: proof of `lem:gelu-swiglu` (normalization_ffn.tex). -/
theorem gelu_erf_argument (v A : ℝ) (hA : A ≠ 0) :
    A / √2 * (v / A) = v / √2 ∧ 1 + 2 * (A / √2) ^ 2 = 1 + A ^ 2 := by
  have h2 : (0 : ℝ) < √2 := by positivity
  constructor
  · field_simp
  · rw [div_pow, sq_sqrt (by norm_num)]; ring

/-- The expected request counts of `lem:gelu-swiglu` for GELU rows: with an erf factory of
count at most `1 + A²`, `1/2 + (1/2)(1 + (1 + A²)) = 3/2 + A²/2` for `GELU(v)`, and one more
request for `u GELU(v)`.
Paper: `lem:gelu-swiglu` (normalization_ffn.tex), the table. -/
theorem gelu_counts (A : ℝ) :
    1 / 2 * 1 + 1 / 2 * (1 + (1 + A ^ 2)) = 3 / 2 + A ^ 2 / 2 ∧
      1 + (3 / 2 + A ^ 2 / 2) = 5 / 2 + A ^ 2 / 2 := by
  constructor <;> ring

/-- The gated GELU product: an independent `u/A` sign times a `GELU(v)/A` sign has mean
`u GELU(v)/A²`, at radius `A²`.
Paper: proof of `lem:gelu-swiglu` (normalization_ffn.tex). -/
theorem gated_gelu_mean (u v A : ℝ) (hA : A ≠ 0) : (u / A) * (gelu v / A) = u * gelu v / A ^ 2 := by
  field_simp

/-- Exactness of a fresh gated product with a fair closed branch: a gate of probability
`g` opening onto independent `u/A` and `v/A` signs has mean `uvg/A²`.
Paper: proof of `lem:gelu-swiglu` (normalization_ffn.tex). -/
theorem gated_product_identity (u v gate A : ℝ) (hA : A ≠ 0) :
    gate * ((u / A) * (v / A)) + (1 - gate) * 0 = (u * v * gate) / A ^ 2 := by
  rw [mul_zero, add_zero]
  field_simp

/-- The logistic gate is a probability: `0 < σ(v) < 1`. -/
theorem sigma_mem (v : ℝ) : 0 < sigma v ∧ sigma v < 1 := by
  unfold sigma
  have h := exp_pos (-v)
  exact ⟨by positivity, by rw [div_lt_one (by positivity)]; linarith⟩

/-- **The SwiGLU factory.** The positive outcome of a `tanh(v/2)` sign is a gate of probability
`(1 + tanh(v/2))/2 = σ(v)`; on the open gate the product of independent `u/A` and `v/A` signs,
and a fair sign on the closed gate, give mean `uvσ(v)/A²`.
Paper: proof of `lem:gelu-swiglu` (normalization_ffn.tex). -/
theorem swiglu_gate_mean (u v A : ℝ) (hA : A ≠ 0) :
    (1 + tanh (v / 2)) / 2 * ((u / A) * (v / A)) + (1 - (1 + tanh (v / 2)) / 2) * 0
      = u * v * sigma v / A ^ 2 := by
  rw [← sigma_eq_tanh]
  exact gated_product_identity u v (sigma v) A hA

/-- The SwiGLU request count: if the tanh factory for `tanh(v/2)` uses at most `2ρ(1+ρ)`
requests (`cor:comptanhrow`, tanh_large_radius.tex) and the gate opens with probability
`g ∈ [0,1]` onto two further requests, the expected count is at most `2 + 2ρ(1+ρ)`.
Paper: `lem:gelu-swiglu` (normalization_ffn.tex), the table. -/
theorem swiglu_count {T g ρ : ℝ} (hT : T ≤ 2 * ρ * (1 + ρ)) (hg1 : g ≤ 1) :
    T + 2 * g ≤ 2 + 2 * ρ * (1 + ρ) := by
  linarith

/-- The affine radius: if `|b| ≤ b₀`, `∑|w_k| ≤ s₀` and `|a_k| ≤ U`, then
`|b + ∑ w_k a_k| ≤ b₀ + s₀U`. With `b₀ = 1`, `s₀ = s`, `U = G` this is the row radius
`A = 1 + sG`; for a following projection it is the radius `b₀ + s₀U`.
Paper: `lem:gelu-swiglu` (normalization_ffn.tex). -/
theorem affine_row_bound {b b0 s0 U : ℝ} (n : ℕ) (w a : Fin n → ℝ) (hb : |b| ≤ b0)
    (hw : ∑ k, |w k| ≤ s0) (ha : ∀ k, |a k| ≤ U) (hU : 0 ≤ U) :
    |b + ∑ k, w k * a k| ≤ b0 + s0 * U := by
  have h1 : |∑ k, w k * a k| ≤ ∑ k, |w k| * U := by
    refine le_trans (abs_sum_le_sum_abs _ _) (sum_le_sum (fun k _ => ?_))
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (ha k) (abs_nonneg _)
  have h2 : ∑ k, |w k| * U ≤ s0 * U := by
    rw [← sum_mul]; exact mul_le_mul_of_nonneg_right hw hU
  calc |b + ∑ k, w k * a k| ≤ |b| + |∑ k, w k * a k| := abs_add_le _ _
    _ ≤ b0 + s0 * U := by linarith

/-- The tanh radius of the SwiGLU gate: `tanh(v/2)` is the biased tanh row with bias `b/2`,
`|b/2| ≤ 1`, and weights `w_k/2` on coordinates bounded by `G`, so its radius is
`ρ = ∑|w_k/2| G ≤ sG/2`.
Paper: proof of `lem:gelu-swiglu` (normalization_ffn.tex), with `cor:comptanhrow`
(tanh_large_radius.tex). -/
theorem tanh_half_radius {b s G : ℝ} (n : ℕ) (w : Fin n → ℝ) (hb : |b| ≤ 1)
    (hw : ∑ k, |w k| ≤ s) (hG : 0 ≤ G) :
    |b / 2| ≤ 1 ∧ (∑ k, |w k / 2|) * G ≤ s * G / 2 := by
  constructor
  · rw [abs_div, abs_two]; linarith [abs_nonneg b]
  · have : ∑ k, |w k / 2| = (∑ k, |w k|) / 2 := by
      rw [sum_div]; apply sum_congr rfl; intro k _; rw [abs_div, abs_two]
    rw [this]
    have := mul_le_mul_of_nonneg_right hw hG
    linarith

/-- A fair completion has mean zero: thinning a source of mean `F/R` by `R/(2U)` gives
`F/(2U)`.
Paper: proof of `cor:radius-reduction` (normalization_ffn.tex). -/
theorem thinning_identity (F R U : ℝ) (hR : R ≠ 0) (hU : U ≠ 0) :
    (R / (2 * U)) * (F / R) + (1 - R / (2 * U)) * 0 = F / (2 * U) := by
  rw [mul_zero, add_zero]
  field_simp

/-! ## Amplifying a sign mean with a fixed margin (`lem:bipolar-amplification`) -/

/-- Two exact linear Bernoulli factories compose to the desired affine probability:
`((C+1)/2)(1 - (2C/(C+1))(1 - p)) = (1 + C(2p - 1))/2`.
Paper: proof of `lem:bipolar-amplification` (normalization_ffn.tex). -/
theorem bipolar_factory_identity (C p : ℝ) (hC : C + 1 ≠ 0) :
    ((C + 1) / 2) * (1 - (2 * C / (C + 1)) * (1 - p)) = (1 + C * (2 * p - 1)) / 2 := by
  field_simp
  ring

/-- The slack of the first factory: with `p = (1+z)/2`, `|z| ≤ 1/(2C)` and `C ≥ 1`,
`D(1 - p) ≤ 1 - 1/(2(C+1))` for `D = 2C/(C+1)`; and the complemented bias is
`r = 1 - D(1-p) = (p - a)/(1 - a)` with `a = (C-1)/(2C)`.
Paper: proof of `lem:bipolar-amplification` (normalization_ffn.tex). -/
theorem bipolar_first_stage {C z : ℝ} (hC : 1 ≤ C) (hz : |z| ≤ 1 / (2 * C)) :
    2 * C / (C + 1) * (1 - (1 + z) / 2) ≤ 1 - 1 / (2 * (C + 1)) ∧
      1 - 2 * C / (C + 1) * (1 - (1 + z) / 2)
        = ((1 + z) / 2 - (C - 1) / (2 * C)) / (1 - (C - 1) / (2 * C)) := by
  have hC0 : 0 < C := by linarith
  have hz' : -z ≤ 1 / (2 * C) := by linarith [neg_abs_le z]
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    have : C * (-z) ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left hz' hC0.le
      rw [show C * (1 / (2 * C)) = 1 / 2 by field_simp] at this
      exact this
    have e : (1 - 1 / (2 * (C + 1))) * (C + 1) = C + 1 / 2 := by field_simp; ring
    rw [e]
    nlinarith
  · have hden : 1 - (C - 1) / (2 * C) = (C + 1) / (2 * C) := by field_simp; ring
    have hC1 : C + 1 ≠ 0 := by linarith
    rw [hden]
    field_simp
    ring

/-- The second factory: `E r = C(p - a) = (1 + Cz)/2 ∈ [1/4, 3/4]` with `E = (C+1)/2`.
Paper: proof of `lem:bipolar-amplification` (normalization_ffn.tex). -/
theorem bipolar_second_stage {C z : ℝ} (hC : 1 ≤ C) (hz : |z| ≤ 1 / (2 * C)) :
    (C + 1) / 2 * (((1 + z) / 2 - (C - 1) / (2 * C)) / (1 - (C - 1) / (2 * C)))
        = (1 + C * z) / 2 ∧
      1 / 4 ≤ (1 + C * z) / 2 ∧ (1 + C * z) / 2 ≤ 3 / 4 := by
  have hC0 : 0 < C := by linarith
  have hCz : |C * z| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hC0]
    have := mul_le_mul_of_nonneg_left hz hC0.le
    rwa [show C * (1 / (2 * C)) = 1 / 2 by field_simp] at this
  have h := abs_le.1 hCz
  refine ⟨?_, by linarith, by linarith⟩
  have hden : 1 - (C - 1) / (2 * C) = (C + 1) / (2 * C) := by field_simp; ring
  have hC1 : C + 1 ≠ 0 := by linarith
  rw [hden]
  field_simp
  ring

/-- The request count: Huber's `9.5 M/e` gives `38C` source requests per `r`-coin (multiplier
`2C/(C+1)`, slack `1/(2(C+1))`) and `19(C+1)` `r`-coins (multiplier `(C+1)/2`, slack `1/4`);
their product is `722C(C+1) ≤ 1444C²`.
Paper: `lem:bipolar-amplification` (normalization_ffn.tex). -/
theorem bipolar_count {C : ℝ} (hC : 1 ≤ C) :
    9.5 * (2 * C / (C + 1)) / (1 / (2 * (C + 1))) = 38 * C ∧
      9.5 * ((C + 1) / 2) / (1 / 4) = 19 * (C + 1) ∧
      38 * C * (19 * (C + 1)) = 722 * C * (C + 1) ∧ 722 * C * (C + 1) ≤ 1444 * C ^ 2 := by
  have hC1 : C + 1 ≠ 0 := by linarith
  refine ⟨by field_simp; ring, by ring, by ring, by nlinarith⟩

/-! ## Reducing a supplied radius (`cor:radius-reduction`) -/

/-- The premise of the amplification lemma: with `C = R/(2U) > 1` and `|F| ≤ U`, the source mean
`z = F/R` satisfies `|z| ≤ 1/(2C)`, and the amplified mean is `Cz = F/(2U)`.
Paper: proof of `cor:radius-reduction` (normalization_ffn.tex). -/
theorem radius_reduction_premise {F R U : ℝ} (hR : 0 < R) (hU : 0 < U) (hF : |F| ≤ U) :
    |F / R| ≤ 1 / (2 * (R / (2 * U))) ∧ R / (2 * U) * (F / R) = F / (2 * U) := by
  constructor
  · rw [abs_div, abs_of_pos hR, show 1 / (2 * (R / (2 * U))) = U / R by field_simp]
    exact div_le_div_of_nonneg_right hF hR.le
  · field_simp

/-- The request count of `cor:radius-reduction`: `1444 C² = 361 (R/U)²` for `C = R/(2U)`; and a
single request suffices when `R ≤ 2U`; altogether at most `max{1, 361(R/U)²}`.
Paper: `cor:radius-reduction` (normalization_ffn.tex). -/
theorem radius_reduction_count {R U : ℝ} (hU : 0 < U) :
    1444 * (R / (2 * U)) ^ 2 = 361 * (R / U) ^ 2 ∧
      1 ≤ max 1 (361 * (R / U) ^ 2) ∧ 361 * (R / U) ^ 2 ≤ max 1 (361 * (R / U) ^ 2) := by
  refine ⟨by field_simp; ring, le_max_left _ _, le_max_right _ _⟩

/-! ## The GELU/SwiGLU construction (`thm:real-ffn-lower`) -/

/-- The three hidden units: with preactivations `y`, `-y` and `1`, a feature projection row
`(1, -1, 0)` adds `φ(y) - φ(-y) = y`, and a carrier row `(0, 0, -1)` adds `-φ(1)`. For GELU and
SiLU the feature update is linear.
Paper: proof of `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem hidden_units (y : ℝ) :
    (1 * gelu y + (-1) * gelu (-y) + 0 * gelu 1 = y) ∧
      (0 * gelu y + 0 * gelu (-y) + (-1) * gelu 1 = -gelu 1) ∧
      (1 * silu y + (-1) * silu (-y) + 0 * silu 1 = y) ∧
      (0 * silu y + 0 * silu (-y) + (-1) * silu 1 = -silu 1) := by
  have h1 := gelu_antisymmetric y
  have h2 := silu_antisymmetric y
  refine ⟨by linarith, by ring, by linarith, by ring⟩

/-- In the SwiGLU case `u v σ(v)`, setting the ungated factor `u` to the constant one gives
exactly the SiLU unit `v σ(v)`.
Paper: proof of `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem swiglu_unit (v : ℝ) : 1 * v * sigma v = silu v := by
  unfold silu; ring

/-- The feature mean is bounded through the RMS denominator: if `v ≥ η · N⁻¹ ∑ h_i²` then
`(N⁻¹ ∑ h_i)² ≤ v/η`; with `η ≥ 1/4` the feature update `s · mean/√v` has magnitude at most
`s/√η ≤ 2s`.
Paper: proof of `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem feature_mean_bound {N : ℕ} (hN : 0 < N) (h : Fin N → ℝ) {v η s : ℝ} (hη : 1 / 4 ≤ η)
    (hs : 0 ≤ s) (hv : η * ((1 / (N : ℝ)) * ∑ i, h i ^ 2) ≤ v) (hv0 : 0 < v) :
    ((1 / (N : ℝ)) * ∑ i, h i) ^ 2 ≤ v / η ∧
      |s * ((1 / (N : ℝ)) * ∑ i, h i) / √v| ≤ 2 * s := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hη0 : 0 < η := by linarith
  have hcs : (∑ i, h i) ^ 2 ≤ N * ∑ i, h i ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin N))) (f := h)
    simpa using this
  have h1 : ((1 / (N : ℝ)) * ∑ i, h i) ^ 2 ≤ (1 / (N : ℝ)) * ∑ i, h i ^ 2 := by
    rw [mul_pow, div_pow, one_pow]
    rw [show 1 / (N : ℝ) ^ 2 * (∑ i, h i) ^ 2 = (∑ i, h i) ^ 2 / N / N by field_simp]
    rw [show 1 / (N : ℝ) * ∑ i, h i ^ 2 = (N * ∑ i, h i ^ 2) / N / N by field_simp]
    apply div_le_div_of_nonneg_right _ hN'.le
    exact div_le_div_of_nonneg_right hcs hN'.le
  have h2 : (1 / (N : ℝ)) * ∑ i, h i ^ 2 ≤ v / η := by rw [le_div_iff₀ hη0]; linarith
  refine ⟨le_trans h1 h2, ?_⟩
  set m := (1 / (N : ℝ)) * ∑ i, h i
  have hm : m ^ 2 ≤ 4 * v := by
    have : v / η ≤ 4 * v := by rw [div_le_iff₀ hη0]; nlinarith
    linarith [le_trans h1 h2]
  have hsv : 0 < √v := sqrt_pos.2 hv0
  rw [abs_div, abs_mul, abs_of_nonneg hs, abs_of_pos hsv, div_le_iff₀ hsv]
  have : |m| ≤ 2 * √v := by
    have h4 : |m| ≤ √(4 * v) := Real.abs_le_sqrt hm
    rwa [sqrt_mul (by norm_num), show √(4 : ℝ) = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]] at h4
  nlinarith

/-- The row norms: each input row `±(s/N, …, s/N)` has `ℓ₁` norm `s`, and the projection rows
`(1, -1, 0)` and `(0, 0, -1)` have norms `2 ≤ s` and `1`.
Paper: proof of `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem ffn_row_norms {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 2 ≤ s) :
    ∑ _i : Fin N, |s / N| = s ∧ |(1 : ℝ)| + |(-1 : ℝ)| + |(0 : ℝ)| ≤ s ∧
      |(0 : ℝ)| + |(0 : ℝ)| + |(-1 : ℝ)| = 1 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨?_, by norm_num; linarith, by norm_num⟩
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, abs_of_nonneg (by positivity)]
  field_simp

/-- The coordinate bound: the feature update has magnitude at most `2s` and the carrier update
below one, so `|h_{j,i}| ≤ 1 + 2sαj`.
Paper: proof of `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem coordinate_growth {s α : ℝ} (h : ℕ → ℝ) (h0 : |h 0| ≤ 1)
    (hstep : ∀ j, |h (j + 1) - h j| ≤ α * (2 * s)) (j : ℕ) : |h j| ≤ 1 + 2 * s * α * j := by
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    have := hstep j
    calc |h (j + 1)| = |h j + (h (j + 1) - h j)| := by ring_nf
      _ ≤ |h j| + |h (j + 1) - h j| := abs_add_le _ _
      _ ≤ 1 + 2 * s * α * j + α * (2 * s) := add_le_add ih this
      _ = 1 + 2 * s * α * ((j + 1 : ℕ) : ℝ) := by push_cast; ring

/-- The exact polynomial identity behind the whole-domain final-head bound:
`(16/3)(3 + F²/4) - (F + 2)² = (F - 6)²/3`.
Paper: the readout calculation in the proof of `thm:pn-normalized-gain` (normalization_gain.tex),
as used in the proof of `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem final_head_square_identity (F : ℝ) :
    (16 : ℝ) / 3 * (3 + F ^ 2 / 4) - (F + 2) ^ 2 = (F - 6) ^ 2 / 3 := by
  ring

/-- `(F + 2)² ≤ (16/3)(3 + F²/4)`; see `final_logit_bound`.
Paper: the readout calculation in the proof of `thm:pn-normalized-gain` (normalization_gain.tex),
as used in the proof of `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem final_head_square_bound (F : ℝ) : (F + 2) ^ 2 ≤ (16 : ℝ) / 3 * (3 + F ^ 2 / 4) := by
  have hid := final_head_square_identity F
  have hsq := sq_nonneg (F - 6)
  nlinarith

/-- The carrier lower envelope supplies a floor on every sign input once the effective residual
time exceeds two: `12(3 + (τ/2 - 1)²/2) - (1+τ)² = (τ - 8)²/2 + 9`.
Paper: proofs of `thm:pn-scaled-lower` (normalization_depth_lower.tex) and `thm:real-ffn-lower`
(normalization_ffn.tex), the full-cube floor `v_j ≥ r_j²/12`. -/
theorem carrier_floor_identity (tau : ℝ) :
    12 * (3 + (tau / 2 - 1) ^ 2 / 2) - (1 + tau) ^ 2 = (tau - 8) ^ 2 / 2 + 9 := by
  ring

/-- `(1+τ)²/12 ≤ 3 + (τ/2 - 1)²/2`.
Paper: proofs of `thm:pn-scaled-lower` (normalization_depth_lower.tex) and `thm:real-ffn-lower`
(normalization_ffn.tex). -/
theorem carrier_floor_bound (tau : ℝ) : (1 + tau) ^ 2 / 12 ≤ 3 + (tau / 2 - 1) ^ 2 / 2 := by
  have hid := carrier_floor_identity tau
  have hsq := sq_nonneg (tau - 8)
  nlinarith

/-- The relative floor of the supplied radii: `R_j = 1 + 4sαj ≤ 4s r_j` for `s ≥ 1/4`, so the
floor `v_j ≥ r_j²/12` gives `v_j ≥ R_j²/(192 s²) = γ_* R_j²`.
Paper: `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem gamma_star {s α j v : ℝ} (hs : 1 / 4 ≤ s) (hα : 0 ≤ α) (hj : 0 ≤ j)
    (hv : (1 + α * j) ^ 2 / 12 ≤ v) :
    1 + 4 * s * α * j ≤ 4 * s * (1 + α * j) ∧ (1 + 4 * s * α * j) ^ 2 / (192 * s ^ 2) ≤ v := by
  have hR : 1 + 4 * s * α * j ≤ 4 * s * (1 + α * j) := by nlinarith [mul_nonneg hα hj]
  refine ⟨hR, ?_⟩
  have hR0 : 0 ≤ 1 + 4 * s * α * j := by
    have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * s) hα) hj
    linarith
  have hsq := pow_le_pow_left₀ hR0 hR 2
  have hs0 : 0 < s := by linarith
  rw [div_le_iff₀ (by positivity)]
  have e : (4 * s * (1 + α * j)) ^ 2 = 16 * s ^ 2 * (1 + α * j) ^ 2 := by ring
  have : (1 + α * j) ^ 2 ≤ 12 * v := by linarith
  nlinarith [sq_nonneg s]

/-- **The fixed readout.** If `|h| ≤ |F| + 2` and `v ≥ 3 + F²/4`, then the logit `h/(4√v)` has
absolute value at most `1/√3 < 1`.
Paper: the readout calculation in the proof of `thm:pn-normalized-gain` (normalization_gain.tex),
as used in the proof of `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem final_logit_bound {h F v : ℝ} (hh : |h| ≤ |F| + 2) (hv : 3 + F ^ 2 / 4 ≤ v) :
    |h / (4 * √v)| ≤ 1 / √3 ∧ 1 / √3 < 1 := by
  have hv0 : 0 < v := by nlinarith [sq_nonneg F]
  have hs : 0 < √v := sqrt_pos.2 hv0
  have h3 : (0 : ℝ) < √3 := by positivity
  have h31 : 1 < √3 := by
    have := sqrt_lt_sqrt (by norm_num) (show (1 : ℝ) < 3 by norm_num); rwa [sqrt_one] at this
  refine ⟨?_, by rw [div_lt_one h3]; exact h31⟩
  have key : (|F| + 2) ^ 2 ≤ (4 * √v / √3) ^ 2 := by
    rw [div_pow, mul_pow, sq_sqrt hv0.le, sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    have h := final_head_square_bound |F|
    rw [sq_abs] at h
    nlinarith
  have key2 : |F| + 2 ≤ 4 * √v / √3 := (abs_le_of_sq_le_sq' key (by positivity)).2
  have h4 : 0 < 4 * √v := by positivity
  rw [abs_div, abs_of_pos h4, div_le_div_iff₀ h4 h3]
  have : |h| ≤ 4 * √v / √3 := le_trans hh key2
  rw [le_div_iff₀ h3] at this
  linarith

end ExactSampling.FeedForward
