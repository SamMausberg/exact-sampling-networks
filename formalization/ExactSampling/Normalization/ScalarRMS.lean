import Mathlib

/-!
# Scalar normalization at a specified output radius

This module formalizes the quantitative content of `sec:scalar-rms-amplitude`
(normalization_scalar.tex): `thm:scalar-rms-amplitude` (also `eq:main-scalar-rms-law` in
main_normalization.tex), the algebraic steps of `lem:new-curvature-transfer`, and
`cor:gaussian-large-radius` (normalization_gaussian.tex).

Formalized here, for `f_{κ,A}(z) = z / (A √(κ⁻¹ + z²))`:
* the upper construction: the gate identity `q G_θ = f_{κ,A}` with `θ = κ⁻¹`,
  `q = 1/(A√(1+θ)) ≤ 1`, the geometric mean `𝔼K = κ`, the source count
  `q(1 + 2κ) = (1 + 2κ)/(A√(1+κ⁻¹)) ≤ 3(√κ + κ)/A`, and the gate factor of the bit bound;
* the lower bound: the first and second derivatives of `f_{κ,A}`, the value
  `|f''(1/(2√κ))| = 48κ/(25√5 A)`, the weight `1 - t² ≥ 3/4`, the constant comparison
  `18κ/(25√5 A) > κ/(4A) ≥ (√κ + κ)/(8A)` for `κ ≥ 1`, and the two-point bound
  `f_{κ,A}(1) ≥ √κ/(√2 A) ≥ (√κ + κ)/(8A)` for `κ ≤ 1`; the assembled lower bound;
* in `lem:new-curvature-transfer`: the Bernstein second-derivative coefficient
  `(m(m-1)/4)(2/m)² = 1 - 1/m`, the mean `t - 2t/m` and the variance bound of the argument, and
  the pointwise score bound used by the transcript lemma;
* `cor:gaussian-large-radius`: the gate `p = 2√(n/κ) ≤ 1`, the radius `2√κ`, the source count
  `p(1 + nκ)` given the count `1 + nκ` of the Gaussian factory, and the bit factor
  `p n (1 + κ) ≤ 4 n^{3/2} √κ`.

Stand-in hypotheses (used only in `scalar_lower_bound`): the conclusion of
`lem:new-curvature-transfer`, `K ≥ ½ (1 - t²)|f''(t)|` for `|t| < 1`, whose proof needs the
transcript lemma `lem:transcript` and a Bernstein limit; and the endpoint coupling bound
`K ≥ f_{κ,A}(1)` of `lem:attentioncoupling` (attention_primitives.tex): the total variation
between the output laws at source means `±1`.

Not formalized: the geometric-majority identity itself (formalized in the module
`ExactSampling.RMSContextLaw` as `geometric_majority_identity`), the finite transcript bound,
the Bernstein limit, the matching lower bound of order `κ` at the fixed radius `A = 4`, and the
bit-complexity estimates beyond the arithmetic factors `gate_bit_factor` and
`large_radius_bit_factor` (the conditional bit costs are not modeled).
-/

open Real Finset
open scoped BigOperators

namespace ExactSampling.ScalarRMS

/-- The scalar target `f_{κ,A}(z) = z / (A √(κ⁻¹ + z²))`.
Paper: `thm:scalar-rms-amplitude` (normalization_scalar.tex). -/
noncomputable def target (κ A z : ℝ) : ℝ := z / (A * √(κ⁻¹ + z ^ 2))

/-! ## The upper construction -/

/-- A known gate of probability `q = 1/(A√(1+θ))` applied before the normalized geometric
majority `G_θ(z) = z√(1+θ)/√(θ+z²)` gives `z/(A√(θ+z²))`.
Paper: proof of `thm:scalar-rms-amplitude` (normalization_scalar.tex). -/
theorem gated_normalization_exactness (z A θ : ℝ) (hA : A ≠ 0) (hθ : 0 < θ) :
    (1 / (A * √(1 + θ))) * (z * √(1 + θ) / √(θ + z ^ 2)) = z / (A * √(θ + z ^ 2)) := by
  have hs : √(1 + θ) ≠ 0 := ne_of_gt (sqrt_pos.2 (by linarith))
  have ht : √(θ + z ^ 2) ≠ 0 := ne_of_gt (sqrt_pos.2 (by nlinarith [sq_nonneg z]))
  field_simp

/-- With `θ = κ⁻¹`, the gated majority has mean `f_{κ,A}(z)`; the closed branch returns a fair
sign.
Paper: proof of `thm:scalar-rms-amplitude` (normalization_scalar.tex). -/
theorem gated_target {κ A z : ℝ} (hκ : 0 < κ) (hA : A ≠ 0) :
    (1 / (A * √(1 + κ⁻¹))) * (z * √(1 + κ⁻¹) / √(κ⁻¹ + z ^ 2))
        + (1 - 1 / (A * √(1 + κ⁻¹))) * 0 = target κ A z := by
  rw [mul_zero, add_zero, gated_normalization_exactness z A κ⁻¹ hA (by positivity)]
  rfl

/-- The gate is a probability: `0 < q ≤ 1` for `A ≥ 1`.
Paper: proof of `thm:scalar-rms-amplitude` (normalization_scalar.tex). -/
theorem gate_mem {κ A : ℝ} (hκ : 0 < κ) (hA : 1 ≤ A) :
    0 < 1 / (A * √(1 + κ⁻¹)) ∧ 1 / (A * √(1 + κ⁻¹)) ≤ 1 := by
  have hs : 1 ≤ √(1 + κ⁻¹) := by
    have : √1 ≤ √(1 + κ⁻¹) := sqrt_le_sqrt (by have := inv_pos.2 hκ; linarith)
    rwa [sqrt_one] at this
  have hA0 : 0 < A := by linarith
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]
  nlinarith

/-- The geometric law `Pr(K = k) = θ/(1+θ) (1+θ)^{-k}` with `θ = κ⁻¹` has mean `κ`.
Paper: proof of `thm:scalar-rms-amplitude` (normalization_scalar.tex), `𝔼K = κ`. -/
theorem geometric_mean_kappa {κ : ℝ} (hκ : 0 < κ) :
    HasSum (fun k : ℕ => (k : ℝ) * (κ⁻¹ / (1 + κ⁻¹) * (1 / (1 + κ⁻¹)) ^ k)) κ := by
  have hθ : 0 < κ⁻¹ := inv_pos.2 hκ
  have h1θ : 0 < 1 + κ⁻¹ := by linarith
  have hr : ‖1 / (1 + κ⁻¹)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_lt_one h1θ]; linarith
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hr).mul_left (κ⁻¹ / (1 + κ⁻¹))
  convert h using 1
  · funext k; ring
  · have : 1 - 1 / (1 + κ⁻¹) = κ⁻¹ / (1 + κ⁻¹) := by field_simp; ring
    rw [this]
    field_simp

/-- Expected complete-majority work includes both the gate and the odd arity:
`q (2κ + 1) = q + 2qκ`.
Paper: proof of `thm:scalar-rms-amplitude` (normalization_scalar.tex). -/
theorem gated_majority_cost (q κ : ℝ) : q * (2 * κ + 1) = q + 2 * q * κ := by ring

/-- **The upper bound.** For `κ > 0` and `A > 0`, `(1+2κ)/(A√(1+κ⁻¹)) ≤ 3(√κ + κ)/A`: if
`κ ≤ 1`, use `q ≤ √κ/A` and `1 + 2κ ≤ 3`; if `κ ≥ 1`, use `q ≤ 1/A` and `1 + 2κ ≤ 3κ`.
Paper: `eq:scalar-rms-amplitude-law` (normalization_scalar.tex); `eq:main-scalar-rms-law`
(main_normalization.tex). -/
theorem upper_bound_le {κ A : ℝ} (hκ : 0 < κ) (hA : 0 < A) :
    (1 + 2 * κ) / (A * √(1 + κ⁻¹)) ≤ 3 * (√κ + κ) / A := by
  have hsκ : 0 < √κ := sqrt_pos.2 hκ
  have hs1 : 0 < √(1 + κ⁻¹) := sqrt_pos.2 (by have := inv_pos.2 hκ; linarith)
  rw [div_le_div_iff₀ (by positivity) hA]
  suffices h : 1 + 2 * κ ≤ 3 * (√κ + κ) * √(1 + κ⁻¹) by
    have := mul_le_mul_of_nonneg_right h hA.le
    nlinarith
  have hk0 : 0 ≤ κ * √(1 + κ⁻¹) := by positivity
  rcases le_total κ 1 with h1 | h1
  · have hq : 1 ≤ √κ * √(1 + κ⁻¹) := by
      rw [← sqrt_mul hκ.le]
      have : 1 ≤ κ * (1 + κ⁻¹) := by rw [mul_add, mul_inv_cancel₀ hκ.ne']; linarith
      have := sqrt_le_sqrt this
      rwa [sqrt_one] at this
    nlinarith
  · have hq : 1 ≤ √(1 + κ⁻¹) := by
      have : √1 ≤ √(1 + κ⁻¹) := sqrt_le_sqrt (by have := inv_pos.2 hκ; linarith)
      rwa [sqrt_one] at this
    have hk1 : 0 ≤ √κ * √(1 + κ⁻¹) := by positivity
    nlinarith

/-- The previously available scalar geometric-majority interface at radius `A = 4`:
`(1 + 2κ)/(4√(1 + κ⁻¹)) ≤ (1 + 2κ)/4`, so at this fixed radius the cost is `O(κ)`. Only this
upper bound is stated here.
Paper: discussion after `thm:scalar-rms-amplitude` (normalization_scalar.tex). -/
theorem scalar_geometric_majority_cost (κ : ℝ) (hκ : 0 < κ) :
    (1 + 2 * κ) / (4 * √(1 + 1 / κ)) ≤ (1 + 2 * κ) / 4 := by
  have hk0 : 0 ≤ 1 / κ := le_of_lt (one_div_pos.2 hκ)
  have hs : 1 ≤ √(1 + 1 / κ) := by
    have h : √1 ≤ √(1 + 1 / κ) := sqrt_le_sqrt (by linarith)
    simpa using h
  have hden : 0 < 4 * √(1 + 1 / κ) := by positivity
  apply (div_le_iff₀ hden).2
  nlinarith [mul_nonneg (le_of_lt hκ) (sub_nonneg.2 hs)]

/-- At the floor radius `A = 2√κ` (`κ = R²/ε ≥ 1`), the upper construction costs at most `3√κ`.
Paper: discussion after `thm:scalar-rms-amplitude` (normalization_scalar.tex). -/
theorem floor_radius_cost {κ : ℝ} (hκ : 1 ≤ κ) :
    (1 + 2 * κ) / (2 * √κ * √(1 + κ⁻¹)) ≤ 3 * √κ := by
  have hκ0 : 0 < κ := by linarith
  have hsκ : 0 < √κ := sqrt_pos.2 hκ0
  have h := upper_bound_le hκ0 (A := 2 * √κ) (by positivity)
  have hsq : √κ ^ 2 = κ := sq_sqrt hκ0.le
  have hk : 1 ≤ √κ := by have := sqrt_le_sqrt hκ; rwa [sqrt_one] at this
  calc (1 + 2 * κ) / (2 * √κ * √(1 + κ⁻¹)) ≤ 3 * (√κ + κ) / (2 * √κ) := h
    _ ≤ 3 * √κ := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith

/-- The gate factor of the bit bound: `q (1 + κ) ≤ 2(√κ + κ)/A`.
Paper: proof of `thm:scalar-rms-amplitude` (normalization_scalar.tex), the bit bound. -/
theorem gate_bit_factor {κ A : ℝ} (hκ : 0 < κ) (hA : 0 < A) :
    (1 + κ) / (A * √(1 + κ⁻¹)) ≤ 2 * (√κ + κ) / A := by
  have hsκ : 0 < √κ := sqrt_pos.2 hκ
  have hs1 : 0 < √(1 + κ⁻¹) := sqrt_pos.2 (by have := inv_pos.2 hκ; linarith)
  rw [div_le_div_iff₀ (by positivity) hA]
  suffices h : 1 + κ ≤ 2 * (√κ + κ) * √(1 + κ⁻¹) by
    have := mul_le_mul_of_nonneg_right h hA.le
    nlinarith
  have hk0 : 0 ≤ κ * √(1 + κ⁻¹) := by positivity
  rcases le_total κ 1 with h1 | h1
  · have hq : 1 ≤ √κ * √(1 + κ⁻¹) := by
      rw [← sqrt_mul hκ.le]
      have : 1 ≤ κ * (1 + κ⁻¹) := by rw [mul_add, mul_inv_cancel₀ hκ.ne']; linarith
      have := sqrt_le_sqrt this
      rwa [sqrt_one] at this
    nlinarith
  · have hq : 1 ≤ √(1 + κ⁻¹) := by
      have : √1 ≤ √(1 + κ⁻¹) := sqrt_le_sqrt (by have := inv_pos.2 hκ; linarith)
      rwa [sqrt_one] at this
    have hk1 : 0 ≤ √κ * √(1 + κ⁻¹) := by positivity
    nlinarith

/-! ## Derivatives of the target -/

/-- The derivative of `z/(A√(θ+z²))` for a general `θ > 0`. -/
theorem hasDerivAt_target_aux {θ A : ℝ} (hθ : 0 < θ) (hA : A ≠ 0) (z : ℝ) :
    HasDerivAt (fun z => z / (A * √(θ + z ^ 2))) (θ / (A * ((θ + z ^ 2) * √(θ + z ^ 2)))) z := by
  have hpos : 0 < θ + z ^ 2 := by positivity
  have hs : 0 < √(θ + z ^ 2) := sqrt_pos.2 hpos
  have h1 : HasDerivAt (fun z : ℝ => θ + z ^ 2) (2 * z) z := by
    simpa using (hasDerivAt_pow 2 z).const_add θ
  have h2 := (h1.sqrt hpos.ne').const_mul A
  have h3 := (hasDerivAt_id z).div h2 (mul_ne_zero hA hs.ne')
  have hsq : √(θ + z ^ 2) ^ 2 = θ + z ^ 2 := sq_sqrt hpos.le
  convert h3 using 1
  · funext y; simp
  · generalize √(θ + z ^ 2) = r at *
    rw [← hsq]
    field_simp
    simp only [id]
    linear_combination (-1 : ℝ) * hsq

/-- `f_{κ,A}'(z) = θ / (A (θ + z²)^{3/2})` with `θ = κ⁻¹`.
Paper: proof of `thm:scalar-rms-amplitude` (normalization_scalar.tex). -/
theorem hasDerivAt_target {κ A : ℝ} (hκ : 0 < κ) (hA : A ≠ 0) (z : ℝ) :
    HasDerivAt (target κ A) (κ⁻¹ / (A * ((κ⁻¹ + z ^ 2) * √(κ⁻¹ + z ^ 2)))) z :=
  hasDerivAt_target_aux (inv_pos.2 hκ) hA z

/-- The second derivative of `z/(A√(θ+z²))` for a general `θ > 0`. -/
theorem hasDerivAt_target_deriv_aux {θ A : ℝ} (hθ : 0 < θ) (hA : A ≠ 0) (z : ℝ) :
    HasDerivAt (fun z => θ / (A * ((θ + z ^ 2) * √(θ + z ^ 2))))
      (-(3 * θ * z) / (A * ((θ + z ^ 2) ^ 2 * √(θ + z ^ 2)))) z := by
  have hpos : 0 < θ + z ^ 2 := by positivity
  have hs : 0 < √(θ + z ^ 2) := sqrt_pos.2 hpos
  have hsq : √(θ + z ^ 2) ^ 2 = θ + z ^ 2 := sq_sqrt hpos.le
  have h1 : HasDerivAt (fun z : ℝ => θ + z ^ 2) (2 * z) z := by
    simpa using (hasDerivAt_pow 2 z).const_add θ
  have h2 : HasDerivAt (fun y : ℝ => A * ((θ + y ^ 2) * √(θ + y ^ 2)))
      (A * (3 * z * √(θ + z ^ 2))) z := by
    have := (h1.mul (h1.sqrt hpos.ne')).const_mul A
    convert this using 1
    congr 1
    generalize √(θ + z ^ 2) = r at *
    rw [← hsq]
    field_simp
    ring
  have h4 := (hasDerivAt_const z θ).div h2 (mul_ne_zero hA (by positivity))
  convert h4 using 1
  generalize √(θ + z ^ 2) = r at *
  rw [← hsq]
  field_simp
  ring

/-- `f_{κ,A}''(z) = -3θz / (A (θ + z²)^{5/2})` with `θ = κ⁻¹`.
Paper: proof of `thm:scalar-rms-amplitude` (normalization_scalar.tex). -/
theorem hasDerivAt_target_deriv {κ A : ℝ} (hκ : 0 < κ) (hA : A ≠ 0) (z : ℝ) :
    HasDerivAt (fun z => κ⁻¹ / (A * ((κ⁻¹ + z ^ 2) * √(κ⁻¹ + z ^ 2))))
      (-(3 * κ⁻¹ * z) / (A * ((κ⁻¹ + z ^ 2) ^ 2 * √(κ⁻¹ + z ^ 2)))) z :=
  hasDerivAt_target_deriv_aux (inv_pos.2 hκ) hA z

/-- The second derivative of the target, as an iterated `deriv`:
`f_{κ,A}''(t) = -3θt / (A (θ + t²)^{5/2})`.
Paper: proof of `thm:scalar-rms-amplitude` (normalization_scalar.tex). -/
theorem deriv_deriv_target {κ A : ℝ} (hκ : 0 < κ) (hA : A ≠ 0) (t : ℝ) :
    deriv (deriv (target κ A)) t
      = -(3 * κ⁻¹ * t) / (A * ((κ⁻¹ + t ^ 2) ^ 2 * √(κ⁻¹ + t ^ 2))) := by
  have h1 : deriv (target κ A) = fun z => κ⁻¹ / (A * ((κ⁻¹ + z ^ 2) * √(κ⁻¹ + z ^ 2))) := by
    funext z; exact (hasDerivAt_target hκ hA z).deriv
  rw [h1]
  exact (hasDerivAt_target_deriv hκ hA t).deriv

/-- The curvature at the test point `t = 1/(2√κ)`: `|f''(t)| = 48κ/(25√5 A)`.
Paper: proof of `thm:scalar-rms-amplitude` (normalization_scalar.tex). -/
theorem curvature_value {κ A : ℝ} (hκ : 0 < κ) (hA : 0 < A) :
    |-(3 * κ⁻¹ * (1 / (2 * √κ))) / (A * ((κ⁻¹ + (1 / (2 * √κ)) ^ 2) ^ 2
        * √(κ⁻¹ + (1 / (2 * √κ)) ^ 2)))| = 48 * κ / (25 * √5 * A) := by
  have hsκ : 0 < √κ := sqrt_pos.2 hκ
  have hsq : √κ ^ 2 = κ := sq_sqrt hκ.le
  have hsum : κ⁻¹ + (1 / (2 * √κ)) ^ 2 = 5 / (4 * κ) := by
    rw [div_pow, mul_pow, hsq]; field_simp; ring
  have hroot : √(5 / (4 * κ)) = √5 / (2 * √κ) := by
    rw [sqrt_div (by norm_num), sqrt_mul (by norm_num),
      show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
  rw [hsum, hroot]
  have h5 : 0 < √(5 : ℝ) := by positivity
  rw [abs_div, abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  field_simp
  norm_num

/-- The chosen curvature test point remains uniformly inside the interval:
`1 - (1/(2√κ))² ≥ 3/4` for `κ ≥ 1`.
Paper: proof of `thm:scalar-rms-amplitude` (normalization_scalar.tex). -/
theorem curvature_point_weight (κ : ℝ) (hκ : 1 ≤ κ) :
    (3 / 4 : ℝ) ≤ 1 - (1 / (2 * √κ)) ^ 2 := by
  have hk : 0 < κ := by linarith
  have hh : (1 / (2 * √κ)) ^ 2 = 1 / (4 * κ) := by
    rw [div_pow, mul_pow, sq_sqrt (le_of_lt hk)]
    norm_num
  rw [hh]
  have hd : 0 < 4 * κ := by positivity
  have hu : 1 / (4 * κ) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ hd).2
    nlinarith
  linarith

/-- The explicit curvature constant dominates one quarter: `1/4 < 18/(25√5)`, by squaring
`72 > 25√5`.
Paper: proof of `thm:scalar-rms-amplitude` (normalization_scalar.tex). -/
theorem scalar_curvature_constant : (1 / 4 : ℝ) < 18 / (25 * √5) := by
  have hs : 0 < √(5 : ℝ) := sqrt_pos.2 (by norm_num)
  have he : (√(5 : ℝ)) ^ 2 = 5 := sq_sqrt (by norm_num)
  have hb : 25 * √(5 : ℝ) < 72 := by nlinarith
  apply (lt_div_iff₀ (by positivity : 0 < 25 * √(5 : ℝ))).2
  nlinarith

/-- For `κ ≥ 1` the combined scale is at most twice `κ`: `√κ + κ ≤ 2κ`.
Paper: proof of `thm:scalar-rms-amplitude` (normalization_scalar.tex). -/
theorem high_kappa_scale (κ : ℝ) (hκ : 1 ≤ κ) : √κ + κ ≤ 2 * κ := by
  have hk : 0 ≤ κ := by linarith
  have hs : 0 ≤ √κ := sqrt_nonneg κ
  have he : (√κ) ^ 2 = κ := sq_sqrt hk
  nlinarith

/-- The curvature lower bound for `κ ≥ 1`: `½ · (3/4) · 48κ/(25√5 A) = 18κ/(25√5 A)`, which is
more than `κ/(4A) ≥ (√κ + κ)/(8A)`.
Paper: proof of `thm:scalar-rms-amplitude` (normalization_scalar.tex). -/
theorem curvature_lower_chain {κ A : ℝ} (hκ : 1 ≤ κ) (hA : 0 < A) :
    (√κ + κ) / (8 * A) ≤ κ / (4 * A) ∧ κ / (4 * A) < 18 * κ / (25 * √5 * A) ∧
      1 / 2 * (3 / 4) * (48 * κ / (25 * √5 * A)) = 18 * κ / (25 * √5 * A) := by
  have hκ0 : 0 < κ := by linarith
  have h5 : 0 < √(5 : ℝ) := by positivity
  refine ⟨?_, ?_, by field_simp; ring⟩
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [high_kappa_scale κ hκ]
  · have h := scalar_curvature_constant
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)] at h
    have hkA : 0 < κ * A := mul_pos hκ0 hA
    nlinarith [mul_lt_mul_of_pos_left h hkA]

/-- The two-point bound for `κ ≤ 1`: `f_{κ,A}(1) = √κ/(A√(1+κ)) ≥ √κ/(√2 A) ≥ (√κ + κ)/(8A)`.
Paper: proof of `thm:scalar-rms-amplitude` (normalization_scalar.tex). -/
theorem two_point_lower {κ A : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hA : 0 < A) :
    target κ A 1 = √κ / (A * √(1 + κ)) ∧ √κ / (√2 * A) ≤ target κ A 1 ∧
      (√κ + κ) / (8 * A) ≤ √κ / (√2 * A) := by
  have hsκ : 0 < √κ := sqrt_pos.2 hκ
  have hs2 : 0 < √(2 : ℝ) := by positivity
  have h1κ : 0 < √(1 + κ) := sqrt_pos.2 (by linarith)
  have hval : target κ A 1 = √κ / (A * √(1 + κ)) := by
    unfold target
    have : κ⁻¹ + 1 ^ 2 = (1 + κ) / κ := by field_simp
    rw [this, sqrt_div (by linarith)]
    field_simp
  refine ⟨hval, ?_, ?_⟩
  · rw [hval]
    apply div_le_div_of_nonneg_left hsκ.le (by positivity)
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ hA.le
    exact sqrt_le_sqrt (by linarith)
  · have hk : κ ≤ √κ := by
      have h := sqrt_le_sqrt hκ1
      rw [sqrt_one] at h
      have hsq := sq_sqrt hκ.le
      nlinarith
    have h2 : √(2 : ℝ) ≤ 2 := by rw [sqrt_le_left (by norm_num)]; norm_num
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : (√κ + κ) * √2 ≤ (2 * √κ) * 2 :=
      mul_le_mul (by linarith) h2 (by positivity) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right h3 hA.le]

/-- **The lower bound of `eq:scalar-rms-amplitude-law` (normalization_scalar.tex).** Let `K` be a
uniform expected source count of an exact factory for `f_{κ,A}`, `κ > 0`, `A > 0`. Assume the
conclusion of `lem:new-curvature-transfer` (normalization_scalar.tex),
`K ≥ ½(1 - t²)|f''(t)|` for `|t| < 1`, and the endpoint coupling
bound `K ≥ f_{κ,A}(1)` of `lem:attentioncoupling` (attention_primitives.tex).
Then `K ≥ (√κ + κ)/(8A)`.
Paper: `thm:scalar-rms-amplitude`, `eq:scalar-rms-amplitude-law` (normalization_scalar.tex);
`eq:main-scalar-rms-law` (main_normalization.tex). -/
theorem scalar_lower_bound {κ A K : ℝ} (hκ : 0 < κ) (hA : 0 < A)
    (hcurv : ∀ t : ℝ, |t| < 1 → 1 / 2 * (1 - t ^ 2) * |deriv (deriv (target κ A)) t| ≤ K)
    (hcouple : target κ A 1 ≤ K) :
    (√κ + κ) / (8 * A) ≤ K := by
  have hcurv' : ∀ t : ℝ, |t| < 1 → 1 / 2 * (1 - t ^ 2) *
      |-(3 * κ⁻¹ * t) / (A * ((κ⁻¹ + t ^ 2) ^ 2 * √(κ⁻¹ + t ^ 2)))| ≤ K := by
    intro t ht
    rw [← deriv_deriv_target hκ hA.ne' t]
    exact hcurv t ht
  rcases le_total 1 κ with h1 | h1
  · set t := 1 / (2 * √κ) with ht
    have hsκ : 1 ≤ √κ := by have := sqrt_le_sqrt h1; rwa [sqrt_one] at this
    have ht1 : |t| < 1 := by
      rw [ht, abs_of_pos (by positivity), div_lt_one (by positivity)]; linarith
    have hK := hcurv' t ht1
    rw [curvature_value hκ hA] at hK
    have hw := curvature_point_weight κ h1
    obtain ⟨c1, c2, c3⟩ := curvature_lower_chain h1 hA
    have hpos : 0 ≤ 48 * κ / (25 * √5 * A) := by positivity
    have : 1 / 2 * (3 / 4) * (48 * κ / (25 * √5 * A))
        ≤ 1 / 2 * (1 - t ^ 2) * (48 * κ / (25 * √5 * A)) := by
      apply mul_le_mul_of_nonneg_right _ hpos; linarith
    linarith
  · obtain ⟨_, c2, c3⟩ := two_point_lower hκ h1 hA
    linarith

/-! ## The curvature transfer (`lem:new-curvature-transfer`) -/

/-- The finite-difference coefficient in the Bernstein second derivative:
`(m(m-1)/4)(2/m)² = 1 - 1/m`.
Paper: proof of `lem:new-curvature-transfer` (normalization_scalar.tex). -/
theorem bernstein_second_coefficient (m : ℝ) (hm : m ≠ 0) :
    (m * (m - 1) / 4) * (2 / m) ^ 2 = 1 - 1 / m := by
  field_simp
  ring

/-- The mean of the Bernstein argument `2J/m - 1 + 2(U+V)/m`, with `𝔼J = (m-2)p`,
`𝔼U = 𝔼V = 1/2` and `p = (1+t)/2`, is `t - 2t/m`.
Paper: proof of `lem:new-curvature-transfer` (normalization_scalar.tex). -/
theorem bernstein_argument_mean (m t : ℝ) (hm : m ≠ 0) :
    2 * ((m - 2) * ((1 + t) / 2)) / m - 1 + 2 * (1 / 2 + 1 / 2) / m = t - 2 * t / m := by
  field_simp
  ring

/-- The variance of the Bernstein argument is `(4/m²)((m-2)p(1-p) + 1/6) ≤ 1/m` for `m ≥ 2`,
using `Var U = Var V = 1/12` and `p(1-p) ≤ 1/4`.
Paper: proof of `lem:new-curvature-transfer` (normalization_scalar.tex), variance `O(1/m)`. -/
theorem bernstein_argument_variance_le {m p : ℝ} (hm : 2 ≤ m) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    4 / m ^ 2 * ((m - 2) * (p * (1 - p)) + 1 / 12 + 1 / 12) ≤ 1 / m := by
  have hm0 : 0 < m := by linarith
  have hpq : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have hpq0 : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hm0]
  have h1 := mul_le_mul_of_nonneg_left hpq (by linarith : (0 : ℝ) ≤ m - 2)
  nlinarith

/-- The finite-input score expression is bounded pointwise by its two energies:
`|y (z² - v)| ≤ z² + v` for `|y| ≤ 1`, `v ≥ 0`; this gives `|H''| ≤ 𝔼(Z² + A)`.
Paper: `lem:transcript` (tanh_lower.tex), as used in `lem:new-curvature-transfer`
(normalization_scalar.tex). -/
theorem pointwise_curvature_score_bound (y z v : ℝ) (hy : |y| ≤ 1) (hv : 0 ≤ v) :
    |y * (z ^ 2 - v)| ≤ z ^ 2 + v := by
  rw [abs_mul]
  calc |y| * |z ^ 2 - v| ≤ 1 * |z ^ 2 - v| := mul_le_mul_of_nonneg_right hy (abs_nonneg _)
    _ = |z ^ 2 - v| := one_mul _
    _ ≤ |z ^ 2| + |v| := abs_sub _ _
    _ = z ^ 2 + v := by rw [abs_of_nonneg (sq_nonneg z), abs_of_nonneg hv]

/-! ## Thinning the vector Gaussian interface (`cor:gaussian-large-radius`) -/

/-- The radius-adjustment gate `p = 2√(n/κ)` is a probability when `κ ≥ 4n`, and the new
radius is `(4√n)/p = 2√κ`.
Paper: proof of `cor:gaussian-large-radius` (normalization_gaussian.tex). -/
theorem large_radius_gate {n κ : ℝ} (hn : 0 < n) (hκ : 4 * n ≤ κ) :
    0 < 2 * √(n / κ) ∧ 2 * √(n / κ) ≤ 1 ∧ 4 * √n / (2 * √(n / κ)) = 2 * √κ := by
  have hκ0 : 0 < κ := by linarith
  have hsn : 0 < √n := sqrt_pos.2 hn
  have hsk : 0 < √κ := sqrt_pos.2 hκ0
  refine ⟨by positivity, ?_, ?_⟩
  · have : n / κ ≤ 1 / 4 := by rw [div_le_iff₀ hκ0]; linarith
    have h := sqrt_le_sqrt this
    rw [show √(1 / 4 : ℝ) = 1 / 2 by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, sqrt_sq (by norm_num)]] at h
    linarith
  · rw [sqrt_div hn.le]
    field_simp
    norm_num

/-- Increasing the output radius thins before the source requests: the gate times the
Gaussian mean `x/(4√n)` is `x/(2√κ)`.
Paper: proof of `cor:gaussian-large-radius` (normalization_gaussian.tex). -/
theorem gaussian_to_floor_radius (x n κ : ℝ) (hn : 0 < n) (hκ : 0 < κ) :
    (2 * (√n / √κ)) * (x / (4 * √n)) = x / (2 * √κ) := by
  have hs : √n ≠ 0 := ne_of_gt (sqrt_pos.2 hn)
  have ht : √κ ≠ 0 := ne_of_gt (sqrt_pos.2 hκ)
  field_simp
  ring

/-- The source count of `cor:gaussian-large-radius`: if the Gaussian factory at radius `4√n`
uses at most `1 + nκ` expected source requests, the gated procedure (open branch with
probability `p = 2√(n/κ)`, a fair sign without requests otherwise) uses at most
`2√(n/κ)(1 + nκ)`.
Paper: `cor:gaussian-large-radius` (normalization_gaussian.tex). -/
theorem large_radius_source_count {n κ C : ℝ} (hn : 0 < n) (hκ : 4 * n ≤ κ)
    (hC : C ≤ 1 + n * κ) :
    2 * √(n / κ) * C + (1 - 2 * √(n / κ)) * 0 ≤ 2 * √(n / κ) * (1 + n * κ) := by
  rw [mul_zero, add_zero]
  exact mul_le_mul_of_nonneg_left hC (large_radius_gate hn hκ).1.le

/-- The bit factor of `cor:gaussian-large-radius`: for `κ ≥ 4n ≥ 4`, the gate probability
`p = 2√(n/κ)` times the conditional factor `n(1 + κ)` is at most `4 n^{3/2} √κ`.
Paper: `cor:gaussian-large-radius` (normalization_gaussian.tex). -/
theorem large_radius_bit_factor {n κ : ℝ} (hn : 1 ≤ n) (hκ : 4 * n ≤ κ) :
    2 * √(n / κ) * (n * (1 + κ)) ≤ 4 * (n * √n) * √κ := by
  have hn0 : 0 < n := by linarith
  have hκ0 : 0 < κ := by linarith
  have hsn : 0 < √n := sqrt_pos.2 hn0
  have hsk : 0 < √κ := sqrt_pos.2 hκ0
  have hsq : √κ ^ 2 = κ := sq_sqrt hκ0.le
  rw [sqrt_div hn0.le]
  have e : 2 * (√n / √κ) * (n * (1 + κ)) = (2 * √n * n * (1 + κ)) / √κ := by field_simp
  rw [e, div_le_iff₀ hsk]
  have hk1 : 1 + κ ≤ 2 * κ := by linarith
  have h1 := mul_le_mul_of_nonneg_left hk1 (by positivity : (0 : ℝ) ≤ 2 * √n * n)
  have hkk : √κ * √κ = κ := mul_self_sqrt hκ0.le
  calc 2 * √n * n * (1 + κ) ≤ 2 * √n * n * (2 * κ) := h1
    _ = 4 * (n * √n) * √κ * √κ := by rw [mul_assoc (4 * (n * √n)) √κ √κ, hkk]; ring

end ExactSampling.ScalarRMS
