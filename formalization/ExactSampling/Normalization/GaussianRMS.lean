import Mathlib

/-!
# The Gaussian construction for regularized normalization

This module formalizes the quantitative content of `sec:gaussianrms` (normalization_gaussian.tex):
`lem:erffactory`, `lem:sinequarter`, `thm:gaussianrms`, `cor:gelulayernorm` and
`lem:gaussianrmsbits`. Together they are the second construction of `thm:main-rms`
(main_normalization.tex).

Formalized here:
* the error function `erf x = (2/√π) ∫₀ˣ e^{-t²} dt`, its derivative, and `0 ≤ erf c ≤ 1`;
* the identity `eq:erfmajority`
  `erf(cz) = ∑_k (2c/√π) e^{-c²} c^{2k} / (k! A_k) · M_k(z)` for `c ≥ 0`, `|z| ≤ 1`, where
  `M_k` is the mean of the majority of `2k+1` independent signs (defined from the binomial law)
  and `A_k = (2k+1) C(2k,k) 4^{-k}`; the coefficients sum to `erf c`;
* the implementation of `lem:erffactory`: `∫₀¹ (1-u²)^k du = 1/A_k`, the branch probabilities of
  the truncated-Gaussian/Poisson draw, the Poisson arity `1 + 2μ`, and the exact expected count
  `q(c) = 2c² erf(c) + (2c/√π) e^{-c²} ≤ 1 + 2c²`;
* `lem:sinequarter`: the series for the mean `sin(πz/2)/4`, the gate mass `sinh(π/2)/4`, the
  expected degree `C_sin = (π/8) cosh(π/2)`, and the explicit check `C_sin < 1`;
* `thm:gaussianrms`: the projected source mean, the erf argument, the correlation bound
  `|u| ≤ 1`, the angle identity `1 - 2θ/π = (2/π) arcsin(cos θ)`, the closing step (if the
  intermediate sign has mean `(2/π) arcsin u` with `u = a_i/√(∑ a_j² + nε)`, the quarter-sine
  factory returns mean `a_i/(4√n √(ε + n⁻¹ ∑ a_j²))`), the standard Gaussian moments
  `𝔼 G² = 1`, `𝔼|G| = √(2/π)`, `𝔼 G⁴ = 3` (computed from Mathlib's `gaussianReal`), the scaling
  step for `2𝔼c²`, and the source bound `eq:gaussianrmscost`;
* `cor:gelulayernorm`: the centering mixture, the radius `2R` and the count `1 + 4nR²/ε`;
* `lem:gaussianrmsbits`: `S⁴ ≤ n³ ∑ G_j⁴`, `𝔼c⁴ ≤ (3/4) n² κ²`, `𝔼(1+c²)² ≤ (1+nκ)²`, the integer
  envelope (`|G_j| ≤ u_j ≤ |G_j| + 2h`, `U ≤ 9S/8`, at most `66n` units, acceptance `≥ 8/9`), the
  Poisson bulk/residual split, and the thinning to the integer radius `4⌈√n⌉`.

Not formalized: the probability space (Gaussian vectors, the law of `|G|/√2`, Poisson
superposition, Tonelli/conditional charging); in the proof of `thm:gaussianrms`, the
conditional mean `sgn G_i erf(∑_j G_j a_j/√(2nε))` of the intermediate sign, the
representation `erf(x/√(2nε)) = 𝔼 sgn(x + √(nε) G₀)`, the covariance computation giving the
correlation `u = a_i/√(∑ a_j² + nε)`, and the arcsine law `𝔼[sgn X sgn Y] = (2/π) arcsin u`
(only its angle identity is formalized); the expansions `𝔼(∑|G_j|)² = n𝔼G² + n(n-1)(𝔼|G|)²`
and `𝔼(∑|G_j|)⁴ ≤ n³ ∑ 𝔼 G_j⁴`, which use independence and integration; and the bit-work
accounting of `lem:gaussianrmsbits` (its arithmetic steps listed above are formalized, the bit
costs themselves are not modeled).
-/

open Real Finset Polynomial MeasureTheory
open scoped BigOperators

namespace ExactSampling.GaussianRMS

/-! ## Majority means -/

/-- The probability that the majority of `2k+1` independent coins of bias `p` is one, as the
polynomial `∑_{j ≥ k+1} C(2k+1, j) p^j (1-p)^{2k+1-j}`. -/
noncomputable def majPoly (k : ℕ) : ℝ[X] :=
  ∑ ν ∈ range (k + 1), bernsteinPolynomial ℝ (2 * k + 1) (k + 1 + ν)

/-- The mean `M_k(z)` of the majority of `2k+1` independent signs of mean `z`. -/
noncomputable def majMean (k : ℕ) (z : ℝ) : ℝ := 2 * (majPoly k).eval ((1 + z) / 2) - 1

/-- `A_k = (2k+1) C(2k,k) 4^{-k}`.
Paper: `sec:gaussianrms` (normalization_gaussian.tex), definition before `eq:erfmajority`. -/
noncomputable def Ak (k : ℕ) : ℝ := (2 * k + 1) * (Nat.centralBinom k : ℝ) / 4 ^ k

/-- `A_k > 0`. -/
theorem Ak_pos (k : ℕ) : 0 < Ak k := by
  unfold Ak; have := Nat.centralBinom_pos k; positivity

/-- `A_{k+1} = A_k (2k+3)/(2k+2)`; supports the Wallis integral in `lem:erffactory`. -/
theorem Ak_succ (k : ℕ) : Ak (k + 1) = Ak k * ((2 * k + 3) / (2 * k + 2)) := by
  have h1 := Nat.succ_mul_centralBinom_succ k
  have h2 : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ)
      = 2 * (2 * k + 1) * Nat.centralBinom k := by exact_mod_cast h1
  unfold Ak
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  rw [div_eq_iff (by positivity), pow_succ]
  push_cast
  field_simp
  linear_combination (2 * (k : ℝ) + 3) * 2 * h2

/-- The derivative of the majority polynomial: `P_k' = (2k+1) b_{2k,k}`, by telescoping the
Bernstein derivatives.
Paper: `sec:gaussianrms` (normalization_gaussian.tex), before `eq:erfmajority`. -/
theorem majPoly_derivative (k : ℕ) :
    derivative (majPoly k) = ((2 * k + 1 : ℕ) : ℝ[X]) * bernsteinPolynomial ℝ (2 * k) k := by
  unfold majPoly
  rw [derivative_sum]
  have h : ∀ ν ∈ range (k + 1), derivative (bernsteinPolynomial ℝ (2 * k + 1) (k + 1 + ν))
      = ((2 * k + 1 : ℕ) : ℝ[X]) * (bernsteinPolynomial ℝ (2 * k) (k + ν)
          - bernsteinPolynomial ℝ (2 * k) (k + ν + 1)) := by
    intro ν _
    rw [show k + 1 + ν = (k + ν) + 1 by ring, bernsteinPolynomial.derivative_succ]
    simp
  rw [sum_congr rfl h, ← mul_sum]
  congr 1
  have := sum_range_sub' (fun ν => bernsteinPolynomial ℝ (2 * k) (k + ν)) (k + 1)
  simp only [add_zero, ← add_assoc] at this
  rw [this, bernsteinPolynomial.eq_zero_of_lt ℝ (by omega : 2 * k < k + k + 1), sub_zero]

/-- `M_k'(z) = A_k (1 - z²)^k`.
Paper: `sec:gaussianrms` (normalization_gaussian.tex), before `eq:erfmajority`. -/
theorem hasDerivAt_majMean (k : ℕ) (z : ℝ) :
    HasDerivAt (majMean k) (Ak k * (1 - z ^ 2) ^ k) z := by
  have h1 : HasDerivAt (fun z : ℝ => (1 + z) / 2) (1 / 2) z := by
    simpa using ((hasDerivAt_id z).const_add 1).div_const 2
  have h2 := (Polynomial.hasDerivAt (majPoly k) ((1 + z) / 2)).comp z h1
  have h3 := (h2.const_mul 2).sub_const 1
  unfold majMean
  convert h3 using 1
  · rfl
  rw [majPoly_derivative]
  simp only [eval_mul, eval_natCast, bernsteinPolynomial, eval_pow, eval_X, eval_sub, eval_one]
  rw [show 2 * k - k = k by omega]
  unfold Ak
  rw [Nat.centralBinom_eq_two_mul_choose]
  push_cast
  have : (1 - z ^ 2) ^ k = 4 ^ k * (((1 + z) / 2) ^ k * (1 - (1 + z) / 2) ^ k) := by
    rw [← mul_pow, ← mul_pow]; congr 1; ring
  rw [this]
  field_simp

/-- Symmetry of the majority: `P(1 - p) = 1 - P(p)`. -/
theorem majPoly_eval_one_sub (k : ℕ) (p : ℝ) :
    (majPoly k).eval (1 - p) = 1 - (majPoly k).eval p := by
  have hflip : ∀ j ≤ 2 * k + 1, (bernsteinPolynomial ℝ (2 * k + 1) j).eval (1 - p)
      = (bernsteinPolynomial ℝ (2 * k + 1) (2 * k + 1 - j)).eval p := by
    intro j hj
    rw [← bernsteinPolynomial.flip ℝ (2 * k + 1) j hj, eval_comp]
    simp
  have htot := congrArg (eval p) (bernsteinPolynomial.sum ℝ (2 * k + 1))
  rw [eval_finsetSum, eval_one, show 2 * k + 1 + 1 = (k + 1) + (k + 1) by ring,
    sum_range_add] at htot
  unfold majPoly
  rw [eval_finsetSum, eval_finsetSum]
  have h1 : ∑ ν ∈ range (k + 1), eval (1 - p) (bernsteinPolynomial ℝ (2 * k + 1) (k + 1 + ν))
      = ∑ ν ∈ range (k + 1), eval p (bernsteinPolynomial ℝ (2 * k + 1) (k + 1 - 1 - ν)) := by
    apply sum_congr rfl
    intro ν hν
    rw [mem_range] at hν
    rw [hflip _ (by omega)]
    congr 2; omega
  rw [h1, sum_range_reflect (fun ν => eval p (bernsteinPolynomial ℝ (2 * k + 1) ν)) (k + 1)]
  linarith

/-- The majority mean is odd: `M_k(-z) = -M_k(z)`; in particular `M_k(0) = 0`. -/
theorem majMean_neg (k : ℕ) (z : ℝ) : majMean k (-z) = -majMean k z := by
  unfold majMean
  rw [show (1 + -z) / 2 = 1 - (1 + z) / 2 by ring, majPoly_eval_one_sub]
  ring

/-- `M_k(0) = 0`. -/
theorem majMean_zero (k : ℕ) : majMean k 0 = 0 := by
  have := majMean_neg k 0
  rw [neg_zero] at this
  linarith

/-! ## The error function -/

/-- `erf x = (2/√π) ∫₀ˣ e^{-t²} dt`.
Paper: `sec:gaussianrms` (normalization_gaussian.tex). -/
noncomputable def erf (x : ℝ) : ℝ := 2 / √π * ∫ t in (0 : ℝ)..x, exp (-t ^ 2)

/-- `erf 0 = 0`. -/
theorem erf_zero : erf 0 = 0 := by simp [erf]

/-- `erf' = (2/√π) e^{-x²}`, by the fundamental theorem of calculus. -/
theorem hasDerivAt_erf (x : ℝ) : HasDerivAt erf (2 / √π * exp (-x ^ 2)) x := by
  have h : Continuous (fun t : ℝ => exp (-t ^ 2)) := by fun_prop
  exact ((h.integral_hasStrictDerivAt 0 x).hasDerivAt).const_mul (2 / √π)

/-- `d/dz erf(cz) = (2c/√π) e^{-c²z²}`. -/
theorem hasDerivAt_erf_mul (c z : ℝ) :
    HasDerivAt (fun z => erf (c * z)) (2 * c / √π * exp (-(c ^ 2 * z ^ 2))) z := by
  have h := (hasDerivAt_erf (c * z)).comp z ((hasDerivAt_id z).const_mul c)
  convert h using 1
  · rfl
  · rw [mul_pow]; ring

/-- `∫₀ᶜ e^{-t²} dt ≤ √π/2` for `c ≥ 0`. -/
theorem integral_gaussian_le {c : ℝ} (hc : 0 ≤ c) : ∫ t in (0 : ℝ)..c, exp (-t ^ 2) ≤ √π / 2 := by
  rw [intervalIntegral.integral_of_le hc]
  have hI := integral_gaussian_Ioi 1
  simp only [neg_mul, one_mul, div_one] at hI
  rw [← hI]
  apply setIntegral_mono_set
  · exact (integrable_exp_neg_mul_sq (b := 1) one_pos).integrableOn.congr_fun
      (fun x _ => by simp) measurableSet_Ioi
  · exact Filter.Eventually.of_forall (fun x => (exp_pos _).le)
  · exact Filter.Eventually.of_forall (fun x hx => by
      simp only [Set.mem_Ioc, Set.mem_Ioi] at hx ⊢; exact hx.1)

/-- `0 ≤ erf c ≤ 1` for `c ≥ 0`. -/
theorem erf_mem {c : ℝ} (hc : 0 ≤ c) : 0 ≤ erf c ∧ erf c ≤ 1 := by
  unfold erf
  have hs : 0 < √π := sqrt_pos.2 pi_pos
  constructor
  · exact mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg hc (fun t _ => (exp_pos _).le))
  · calc 2 / √π * ∫ t in (0 : ℝ)..c, exp (-t ^ 2) ≤ 2 / √π * (√π / 2) :=
          mul_le_mul_of_nonneg_left (integral_gaussian_le hc) (by positivity)
      _ = 1 := by field_simp

/-! ## The error-function mixture of majorities (`eq:erfmajority`) -/

/-- The mixture weight `(2c/√π) e^{-c²} c^{2k} / (k! A_k)`. -/
noncomputable def erfWeight (c : ℝ) (k : ℕ) : ℝ :=
  2 * c / √π * exp (-c ^ 2) * (c ^ (2 * k) / ((k.factorial : ℝ) * Ak k))

/-- The mixture weights are nonnegative for `c ≥ 0`.
Paper: after `eq:erfmajority` (normalization_gaussian.tex). -/
theorem erfWeight_nonneg {c : ℝ} (hc : 0 ≤ c) (k : ℕ) : 0 ≤ erfWeight c k := by
  unfold erfWeight
  have := Ak_pos k
  positivity

/-- The exponential series `∑ xⁿ/n! = eˣ`. -/
theorem hasSum_pow_div_factorial (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (exp x) := by
  have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x
  rwa [← Real.exp_eq_exp_ℝ] at this

/-- **The error-function mixture.** For `c ≥ 0` and `|z| ≤ 1`,
`erf(cz) = ∑_k (2c/√π) e^{-c²} c^{2k} / (k! A_k) · M_k(z)`.
Paper: `eq:erfmajority` (normalization_gaussian.tex) and the proof of `lem:erffactory`. -/
theorem erf_majority_identity {c z : ℝ} (hc : 0 ≤ c) (hz : |z| ≤ 1) :
    HasSum (fun k => erfWeight c k * majMean k z) (erf (c * z)) := by
  have htopen : IsOpen (Set.Ioo (-(7 / 5 : ℝ)) (7 / 5)) := isOpen_Ioo
  have htconn : IsPreconnected (Set.Ioo (-(7 / 5 : ℝ)) (7 / 5)) := isPreconnected_Ioo
  have hbound : ∀ y ∈ Set.Ioo (-(7 / 5 : ℝ)) (7 / 5), |1 - y ^ 2| ≤ 1 := by
    intro y hy
    rw [Set.mem_Ioo] at hy
    rw [abs_le]; constructor <;> nlinarith
  set K := 2 * c / √π * exp (-c ^ 2) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  -- derivative terms
  have hderiv_term : ∀ k (y : ℝ), erfWeight c k * (Ak k * (1 - y ^ 2) ^ k)
      = K * ((c ^ 2 * (1 - y ^ 2)) ^ k / (k.factorial : ℝ)) := by
    intro k y
    rw [hK]
    unfold erfWeight
    have := (Ak_pos k).ne'
    rw [mul_pow, ← pow_mul]
    field_simp
  have hu : Summable (fun k : ℕ => K * ((c ^ 2) ^ k / (k.factorial : ℝ))) :=
    ((hasSum_pow_div_factorial (c ^ 2)).mul_left K).summable
  have hg : ∀ k y, y ∈ Set.Ioo (-(7 / 5 : ℝ)) (7 / 5) →
      HasDerivAt (fun z => erfWeight c k * majMean k z)
        (erfWeight c k * (Ak k * (1 - y ^ 2) ^ k)) y :=
    fun k y _ => (hasDerivAt_majMean k y).const_mul _
  have hg' : ∀ k y, y ∈ Set.Ioo (-(7 / 5 : ℝ)) (7 / 5) →
      ‖erfWeight c k * (Ak k * (1 - y ^ 2) ^ k)‖ ≤ K * ((c ^ 2) ^ k / (k.factorial : ℝ)) := by
    intro k y hy
    rw [hderiv_term, Real.norm_eq_abs, abs_mul, abs_of_nonneg hK0]
    apply mul_le_mul_of_nonneg_left _ hK0
    rw [abs_div, abs_pow, Nat.abs_cast, abs_mul, abs_of_nonneg (sq_nonneg c), mul_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h1 : |1 - y ^ 2| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg _) (hbound y hy)
    have h0 : 0 ≤ (c ^ 2) ^ k := by positivity
    calc (c ^ 2) ^ k * |1 - y ^ 2| ^ k ≤ (c ^ 2) ^ k * 1 := mul_le_mul_of_nonneg_left h1 h0
      _ = (c ^ 2) ^ k := mul_one _
  have h0t : (0 : ℝ) ∈ Set.Ioo (-(7 / 5 : ℝ)) (7 / 5) := by rw [Set.mem_Ioo]; norm_num
  have hg0 : Summable (fun k => erfWeight c k * majMean k 0) := by
    simp only [majMean_zero, mul_zero]; exact summable_zero
  have hzt : z ∈ Set.Ioo (-(7 / 5 : ℝ)) (7 / 5) := by
    rw [Set.mem_Ioo]; constructor <;> linarith [(abs_le.1 hz).1, (abs_le.1 hz).2]
  have hsum : Summable (fun k => erfWeight c k * majMean k z) :=
    summable_of_summable_hasDerivAt_of_isPreconnected
      (g := fun k z => erfWeight c k * majMean k z)
      (g' := fun k y => erfWeight c k * (Ak k * (1 - y ^ 2) ^ k)) hu htopen htconn hg hg' h0t
      hg0 hzt
  refine hsum.hasSum_iff.2 ?_
  have hsumd : ∀ y : ℝ, HasSum (fun k => erfWeight c k * (Ak k * (1 - y ^ 2) ^ k))
      (2 * c / √π * exp (-(c ^ 2 * y ^ 2))) := by
    intro y
    simp only [hderiv_term]
    have := (hasSum_pow_div_factorial (c ^ 2 * (1 - y ^ 2))).mul_left K
    convert this using 1
    rw [hK, mul_assoc, ← exp_add]
    congr 2; ring
  have hderiv : ∀ y ∈ Set.Ioo (-(7 / 5 : ℝ)) (7 / 5),
      HasDerivAt (fun z => ∑' k, erfWeight c k * majMean k z)
        (2 * c / √π * exp (-(c ^ 2 * y ^ 2))) y := by
    intro y hy
    have := hasDerivAt_tsum_of_isPreconnected
      (g := fun k z => erfWeight c k * majMean k z)
      (g' := fun k y => erfWeight c k * (Ak k * (1 - y ^ 2) ^ k)) hu htopen htconn hg hg' h0t
      hg0 hy
    rwa [(hsumd y).tsum_eq] at this
  let D : ℝ → ℝ := fun z => (∑' k, erfWeight c k * majMean k z) - erf (c * z)
  have hDd : ∀ y ∈ Set.Ioo (-(7 / 5 : ℝ)) (7 / 5), HasDerivAt D 0 y := by
    intro y hy
    have := (hderiv y hy).sub (hasDerivAt_erf_mul c y)
    rw [sub_self] at this
    exact this
  have hdiff : DifferentiableOn ℝ D (Set.Ioo (-(7 / 5 : ℝ)) (7 / 5)) :=
    fun y hy => (hDd y hy).differentiableAt.differentiableWithinAt
  have hzero : Set.EqOn (deriv D) 0 (Set.Ioo (-(7 / 5 : ℝ)) (7 / 5)) :=
    fun y hy => (hDd y hy).deriv
  have hconst : D z = D 0 := htopen.is_const_of_deriv_eq_zero htconn hdiff hzero hzt h0t
  have hD0 : D 0 = 0 := by
    show (∑' k, erfWeight c k * majMean k 0) - erf (c * 0) = 0
    simp [majMean_zero, erf_zero]
  have h' : (∑' k, erfWeight c k * majMean k z) - erf (c * z) = 0 := hconst.trans hD0
  show (∑' k, erfWeight c k * majMean k z) = erf (c * z)
  linarith

/-- The mixture coefficients are nonnegative and sum to `erf c`: every majority of `+1` signs
returns `+1`.
Paper: after `eq:erfmajority` (normalization_gaussian.tex). -/
theorem erfWeight_hasSum {c : ℝ} (hc : 0 ≤ c) : HasSum (erfWeight c) (erf c) := by
  have h := erf_majority_identity hc (z := 1) (by norm_num)
  have h1 : ∀ k, majMean k 1 = 1 := by
    intro k
    unfold majMean
    have : (majPoly k).eval 1 = 1 := by
      unfold majPoly
      rw [eval_finsetSum, sum_range_succ, sum_eq_zero]
      · rw [bernsteinPolynomial.eval_at_1]; simp; omega
      · intro ν hν
        rw [bernsteinPolynomial.eval_at_1]
        simp at hν
        simp; omega
    norm_num [this]
  simp only [h1, mul_one] at h
  exact h

/-! ## The implementation of the erf factory (`lem:erffactory`) -/

/-- `∫₀¹ (1 - u²)^k du = 1/A_k`, by integration by parts.
Paper: proof of `lem:erffactory` (normalization_gaussian.tex). -/
theorem integral_one_sub_sq_pow (k : ℕ) : ∫ u in (0 : ℝ)..1, (1 - u ^ 2) ^ k = 1 / Ak k := by
  induction k with
  | zero => simp [Ak]
  | succ k ih =>
    have hd : ∀ u ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun u : ℝ => u * (1 - u ^ 2) ^ (k + 1))
        ((2 * k + 3) * (1 - u ^ 2) ^ (k + 1) - (2 * k + 2) * (1 - u ^ 2) ^ k) u := by
      intro u _
      have h1 : HasDerivAt (fun u : ℝ => 1 - u ^ 2) (-(2 * u)) u := by
        simpa using (hasDerivAt_pow 2 u).const_sub 1
      have h2 := (hasDerivAt_id u).mul (h1.pow (k + 1))
      convert h2 using 1
      · funext v; simp
      · simp only [Pi.pow_apply, id, Nat.add_sub_cancel]
        push_cast
        ring
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
      apply Continuous.intervalIntegrable; fun_prop)
    simp at hint
    rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ih] at hint
    have hC := Ak_pos k
    rw [Ak_succ]
    have hI : (2 * (k : ℝ) + 3) * (∫ u in (0 : ℝ)..1, (1 - u ^ 2) ^ (k + 1))
        = (2 * k + 2) * (1 / Ak k) := by linarith
    have : ∫ u in (0 : ℝ)..1, (1 - u ^ 2) ^ (k + 1) = (2 * k + 2) / (2 * k + 3) * (1 / Ak k) := by
      field_simp
      field_simp at hI
      linarith
    rw [this]
    field_simp

/-- `∫₀ᶜ (c² - y²)^k dy = c^{2k+1} / A_k`, by the substitution `y = cu`. -/
theorem integral_sq_sub_sq_pow (c : ℝ) (k : ℕ) :
    ∫ y in (0 : ℝ)..c, (c ^ 2 - y ^ 2) ^ k = c ^ (2 * k + 1) / Ak k := by
  have h := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
    (fun y : ℝ => (c ^ 2 - y ^ 2) ^ k) c
  simp only [mul_zero, mul_one, smul_eq_mul] at h
  rw [← h]
  have : ∀ u : ℝ, (c ^ 2 - (c * u) ^ 2) ^ k = c ^ (2 * k) * (1 - u ^ 2) ^ k := by
    intro u; rw [pow_mul, ← mul_pow]; ring
  simp only [this, intervalIntegral.integral_const_mul, integral_one_sub_sq_pow]
  rw [pow_succ]; ring

/-- The branch probabilities of the truncated Gaussian draw. With `Y = |G|/√2` of density
`(2/√π) e^{-y²}` on `y ≥ 0`, the majority branch opens when `Y ≤ c`, and then `K` is Poisson
with mean `c² - Y²`. The probability of opening and selecting `k` is the mixture weight of
`eq:erfmajority`.
Paper: proof of `lem:erffactory` (normalization_gaussian.tex). -/
theorem branch_probability {c : ℝ} (k : ℕ) :
    2 / √π * ∫ y in (0 : ℝ)..c,
        exp (-y ^ 2) * (exp (-(c ^ 2 - y ^ 2)) * (c ^ 2 - y ^ 2) ^ k / (k.factorial : ℝ))
      = erfWeight c k := by
  have : ∀ y : ℝ, exp (-y ^ 2) * (exp (-(c ^ 2 - y ^ 2)) * (c ^ 2 - y ^ 2) ^ k
      / (k.factorial : ℝ)) = exp (-c ^ 2) / (k.factorial : ℝ) * (c ^ 2 - y ^ 2) ^ k := by
    intro y
    rw [show exp (-y ^ 2) * (exp (-(c ^ 2 - y ^ 2)) * (c ^ 2 - y ^ 2) ^ k / (k.factorial : ℝ))
        = (exp (-y ^ 2) * exp (-(c ^ 2 - y ^ 2))) * (c ^ 2 - y ^ 2) ^ k / (k.factorial : ℝ) by
      ring, ← exp_add]
    ring_nf
  simp only [this, intervalIntegral.integral_const_mul, integral_sq_sub_sq_pow]
  unfold erfWeight
  have := (Ak_pos k).ne'
  rw [pow_succ]
  field_simp
  ring

/-- A Poisson variable of mean `μ` is a probability law with `𝔼[2K+1] = 1 + 2μ`: the
expected size of the complete majority on the open branch.
Paper: proof of `lem:erffactory` (normalization_gaussian.tex). -/
theorem poisson_arity (μ : ℝ) :
    HasSum (fun k : ℕ => exp (-μ) * μ ^ k / (k.factorial : ℝ)) 1 ∧
      HasSum (fun k : ℕ => (2 * k + 1 : ℝ) * (exp (-μ) * μ ^ k / (k.factorial : ℝ)))
        (1 + 2 * μ) := by
  have h0 := (hasSum_pow_div_factorial μ).mul_left (exp (-μ))
  have hone : exp (-μ) * exp μ = 1 := by rw [← exp_add]; simp
  have hP : HasSum (fun k : ℕ => exp (-μ) * μ ^ k / (k.factorial : ℝ)) 1 := by
    rw [← hone]; convert h0 using 1; funext k; ring
  -- the mean: shift by one
  let f : ℕ → ℝ := fun k => (k : ℝ) * (exp (-μ) * μ ^ k / (k.factorial : ℝ))
  have hshift : HasSum (fun k : ℕ => f (k + 1)) μ := by
    have := hP.mul_left μ
    convert this using 1
    · funext k
      simp only [f]
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · ring
  have hf0 : ∑ i ∈ range 1, f i = 0 := by simp [f]
  have hmean : HasSum f μ :=
    (hasSum_nat_add_iff' 1 (f := f) (g := μ)).mp (by rw [hf0, sub_zero]; exact hshift)
  refine ⟨hP, ?_⟩
  have := (hmean.mul_left 2).add hP
  convert this using 1
  · funext k; ring
  · ring

/-- The exact expected input count of the erf factory:
`(2/√π) ∫₀ᶜ e^{-y²}(1 + 2c² - 2y²) dy = 2c² erf(c) + (2c/√π) e^{-c²}`.
Paper: `lem:erffactory` (normalization_gaussian.tex). -/
theorem erf_count (c : ℝ) :
    2 / √π * ∫ y in (0 : ℝ)..c, exp (-y ^ 2) * (1 + 2 * c ^ 2 - 2 * y ^ 2)
      = 2 * c ^ 2 * erf c + 2 * c / √π * exp (-c ^ 2) := by
  have hd : ∀ y ∈ Set.uIcc (0 : ℝ) c, HasDerivAt (fun y => y * exp (-y ^ 2))
      (exp (-y ^ 2) * (1 - 2 * y ^ 2)) y := by
    intro y _
    have h1 : HasDerivAt (fun y : ℝ => -y ^ 2) (-(2 * y)) y := by
      have := (hasDerivAt_pow 2 y).fun_neg
      simpa using this
    have := (hasDerivAt_id y).mul h1.exp
    convert this using 1
    · rfl
    · simp only [id]; ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)
  have hsplit : ∫ y in (0 : ℝ)..c, exp (-y ^ 2) * (1 + 2 * c ^ 2 - 2 * y ^ 2)
      = (∫ y in (0 : ℝ)..c, exp (-y ^ 2) * (1 - 2 * y ^ 2))
        + 2 * c ^ 2 * ∫ y in (0 : ℝ)..c, exp (-y ^ 2) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    congr 1; funext y; ring
  rw [hsplit, hFTC]
  unfold erf
  have hs : 0 < √π := sqrt_pos.2 pi_pos
  simp
  field_simp
  ring

/-- The expected input count is at most `1 + 2c²`.
Paper: `lem:erffactory` (normalization_gaussian.tex). -/
theorem erf_count_le {c : ℝ} (hc : 0 ≤ c) :
    2 * c ^ 2 * erf c + 2 * c / √π * exp (-c ^ 2) ≤ 1 + 2 * c ^ 2 := by
  rw [← erf_count]
  have hs : 0 < √π := sqrt_pos.2 pi_pos
  have hle : ∫ y in (0 : ℝ)..c, exp (-y ^ 2) * (1 + 2 * c ^ 2 - 2 * y ^ 2)
      ≤ ∫ y in (0 : ℝ)..c, (1 + 2 * c ^ 2) * exp (-y ^ 2) := by
    apply intervalIntegral.integral_mono_on hc
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
    intro y _
    have := exp_pos (-y ^ 2)
    nlinarith [sq_nonneg y]
  rw [intervalIntegral.integral_const_mul] at hle
  have h1 := (erf_mem hc).2
  unfold erf at h1
  calc 2 / √π * ∫ y in (0 : ℝ)..c, exp (-y ^ 2) * (1 + 2 * c ^ 2 - 2 * y ^ 2)
      ≤ 2 / √π * ((1 + 2 * c ^ 2) * ∫ y in (0 : ℝ)..c, exp (-y ^ 2)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (1 + 2 * c ^ 2) * (2 / √π * ∫ y in (0 : ℝ)..c, exp (-y ^ 2)) := by ring
    _ ≤ (1 + 2 * c ^ 2) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 + 2 * c ^ 2 := mul_one _

/-! ## The sine factory (`lem:sinequarter`) -/

/-- `e^{11/14} ≤ 2.194`, from the Taylor bound `Real.exp_bound`. -/
theorem exp_11_14_le : exp (11 / 14 : ℝ) ≤ 2.194 := by
  have h := Real.exp_bound (x := 11 / 14) (by norm_num [abs_of_pos]) (n := 8) (by norm_num)
  rw [abs_le] at h
  have hs : ∑ m ∈ range 8, (11 / 14 : ℝ) ^ m / (m.factorial : ℝ) ≤ 2.19398 := by
    simp [sum_range_succ, Nat.factorial]; norm_num
  have he : |(11 / 14 : ℝ)| ^ 8 * ((Nat.succ 8 : ℕ) / ((Nat.factorial 8 : ℕ) * (8 : ℕ)) : ℝ)
      ≤ 0.00001 := by
    norm_num [abs_of_pos, Nat.factorial]
  linarith [h.2]

/-- `e^{11/7} ≤ 4.814`. -/
theorem exp_11_7_le : exp (11 / 7 : ℝ) ≤ 4.814 := by
  have h : exp (11 / 7 : ℝ) = exp (11 / 14) ^ 2 := by rw [← exp_nat_mul]; norm_num
  rw [h]
  have := exp_11_14_le
  have h0 := exp_pos (11 / 14 : ℝ)
  nlinarith

/-- `e^{11/7} ≥ 4.8`. -/
theorem exp_11_7_ge : (4.8 : ℝ) ≤ exp (11 / 7) := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 11 / 7 by norm_num) 8
  have hs : (4.8 : ℝ) ≤ ∑ i ∈ range 8, (11 / 7 : ℝ) ^ i / (i.factorial : ℝ) := by
    simp [sum_range_succ, Nat.factorial]; norm_num
  linarith

/-- `cosh(11/7) < 101/40`.
Paper: proof of `lem:sinequarter` (normalization_gaussian.tex), the rational check. -/
theorem cosh_11_7_lt : cosh (11 / 7 : ℝ) < 101 / 40 := by
  rw [cosh_eq]
  have h1 := exp_11_7_le
  have h2 := exp_11_7_ge
  have h3 : exp (-(11 / 7 : ℝ)) ≤ 1 / 4.8 := by
    rw [exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h2
  norm_num at h3 ⊢
  linarith

/-- `π < 22/7`. -/
theorem pi_lt_22_7 : π < 22 / 7 := by
  have := Real.pi_lt_d4; norm_num at this ⊢; linarith

/-- `cosh(π/2) < 101/40`, since `π/2 < 11/7`.
Paper: proof of `lem:sinequarter` (normalization_gaussian.tex). -/
theorem cosh_pi_div_two_lt : cosh (π / 2) < 101 / 40 := by
  have h : cosh (π / 2) ≤ cosh (11 / 7) := by
    rw [cosh_le_cosh, abs_of_pos (by positivity), abs_of_pos (by norm_num)]
    linarith [pi_lt_22_7]
  linarith [cosh_11_7_lt]

/-- The rational bounds used for `C_sin < 1`: if `0 ≤ p ≤ 22/7` and `0 ≤ c ≤ 101/40`, then
`p/8 · c < 1`.
Paper: proof of `lem:sinequarter` (normalization_gaussian.tex). -/
theorem sine_constant_rational_bound (p c : ℝ) (hc0 : 0 ≤ c) (hp : p ≤ 22 / 7)
    (hc : c ≤ 101 / 40) : p / 8 * c < 1 := by
  have hm : p * c ≤ (22 / 7 : ℝ) * (101 / 40) := mul_le_mul hp hc hc0 (by norm_num)
  nlinarith

/-- **The sine-factory constant.** `C_sin = (π/8) cosh(π/2) < 1`, and the gate mass satisfies
`sinh(π/2)/4 < cosh(π/2)/4 < 101/160 < 1`.
Paper: `lem:sinequarter` (normalization_gaussian.tex). -/
theorem sine_constant_lt_one :
    π / 8 * cosh (π / 2) < 1 ∧ sinh (π / 2) / 4 < cosh (π / 2) / 4 ∧
      cosh (π / 2) / 4 < 101 / 160 := by
  have h1 := cosh_pi_div_two_lt
  have hc : 0 < cosh (π / 2) := cosh_pos _
  refine ⟨?_, ?_, by linarith⟩
  · have : π / 8 * cosh (π / 2) < 22 / 7 / 8 * (101 / 40) :=
      mul_lt_mul'' (by linarith [pi_lt_22_7]) h1 (by positivity) hc.le
    norm_num at this ⊢
    linarith
  · have : sinh (π / 2) < cosh (π / 2) := sinh_lt_cosh _
    linarith

/-- The sine series realizes the mean: choosing degree `2k+1` with probability
`c₀^{2k+1}/(4(2k+1)!)` and returning `(-1)^k` times the product of `2k+1` signs of mean `z`
gives mean `sin(c₀ z)/4` (the fair-sign remainder contributes zero).
Paper: proof of `lem:sinequarter` (normalization_gaussian.tex). -/
theorem sine_series_mean (c0 z : ℝ) :
    HasSum (fun k : ℕ => c0 ^ (2 * k + 1) / (4 * ((2 * k + 1).factorial : ℝ))
      * ((-1) ^ k * z ^ (2 * k + 1))) (sin (c0 * z) / 4) := by
  have h := (Real.hasSum_sin (c0 * z)).div_const 4
  convert h using 1
  funext k
  rw [mul_pow]
  field_simp

/-- The total specified mass of the sine series is `sinh(c₀)/4`.
Paper: proof of `lem:sinequarter` (normalization_gaussian.tex). -/
theorem sine_series_mass (c0 : ℝ) :
    HasSum (fun k : ℕ => c0 ^ (2 * k + 1) / (4 * ((2 * k + 1).factorial : ℝ))) (sinh c0 / 4) := by
  have h := (Real.hasSum_sinh c0).div_const 4
  convert h using 1
  funext k
  field_simp

/-- The weighted degree sum of the sine series is `c₀ cosh(c₀)/4`; at `c₀ = π/2` this is
`C_sin`.
Paper: proof of `lem:sinequarter` (normalization_gaussian.tex). -/
theorem sine_series_degree (c0 : ℝ) :
    HasSum (fun k : ℕ => (2 * k + 1 : ℝ) * (c0 ^ (2 * k + 1) / (4 * ((2 * k + 1).factorial : ℝ))))
      (c0 * cosh c0 / 4) := by
  have h := ((Real.hasSum_cosh c0).mul_left c0).div_const 4
  convert h using 1
  funext k
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- Applying the quarter-sine factory after the arcsine sign identity:
`(1/4) sin((π/2) · (2/π) arcsin u) = u/4` for `|u| ≤ 1`.
Paper: proof of `thm:gaussianrms` (normalization_gaussian.tex). -/
theorem quarter_sine_after_arcsine (u : ℝ) (hlo : -1 ≤ u) (hhi : u ≤ 1) :
    (1 / 4 : ℝ) * sin (π / 2 * ((2 / π) * arcsin u)) = u / 4 := by
  have hp : π ≠ 0 := ne_of_gt pi_pos
  have harg : π / 2 * ((2 / π) * arcsin u) = arcsin u := by field_simp
  rw [harg, sin_arcsin hlo hhi]
  ring

/-! ## The intrinsic-radius factory (`thm:gaussianrms`) -/

/-- The angle identity in the Gaussian sign identity: `1 - 2θ/π = (2/π) arcsin(cos θ)` for
`θ ∈ [0, π]`. In the paper, two Gaussian signs with correlation `u = cos θ` disagree on sectors
of total angle `2θ`, so their product has mean `1 - 2θ/π`; that geometric step is not
formalized here.
Paper: proof of `thm:gaussianrms` (normalization_gaussian.tex). -/
theorem sign_product_angle {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π) :
    1 - 2 * θ / π = (2 / π) * arcsin (cos θ) := by
  have hc : cos θ = sin (π / 2 - θ) := (sin_pi_div_two_sub θ).symm
  rw [hc, arcsin_sin (by linarith) (by linarith)]
  have hp : π ≠ 0 := ne_of_gt pi_pos
  field_simp

/-- The projected source sign: selecting `j` with probability `|G_j|/S`, `S = ∑|G_j| > 0`, and
multiplying a sign of mean `a_j/R` by `sgn G_j` has mean `z = ∑ G_j a_j / (R S)`.
Paper: proof of `thm:gaussianrms` (normalization_gaussian.tex). -/
theorem projected_source_mean {n : ℕ} (G a : Fin n → ℝ) {R : ℝ} :
    ∑ j, (|G j| / ∑ l, |G l|) * ((SignType.sign (G j) : ℝ) * (a j / R))
      = (∑ j, G j * a j) / (R * ∑ l, |G l|) := by
  rw [div_mul_eq_div_div, sum_div, sum_div]
  apply sum_congr rfl
  intro j _
  have h : (SignType.sign (G j) : ℝ) * |G j| = G j := sign_mul_abs (G j)
  rw [show (|G j| / ∑ l, |G l|) * ((SignType.sign (G j) : ℝ) * (a j / R))
      = ((SignType.sign (G j) : ℝ) * |G j|) * a j / R / ∑ l, |G l| by ring, h]

/-- The erf argument: with `A = R ∑|G_j|` and `c = A/√(2nε)`, `c z = ∑ G_j a_j / √(2nε)`.
Paper: proof of `thm:gaussianrms` (normalization_gaussian.tex). -/
theorem projected_erf_argument (A a n ε : ℝ) (hA : A ≠ 0) :
    (A / √(2 * n * ε)) * (a / A) = a / √(2 * n * ε) := by
  by_cases ht : √(2 * n * ε) = 0
  · simp [ht]
  · field_simp

/-- The Gaussian correlation denominator equals the RMS denominator times `√n`.
Paper: proof of `thm:gaussianrms` (normalization_gaussian.tex). -/
theorem gaussian_rms_denominator (n ε q : ℝ) (hn : 0 < n) :
    √(q + n * ε) = √n * √(ε + q / n) := by
  have hn0 : n ≠ 0 := ne_of_gt hn
  have halg : q + n * ε = n * (ε + q / n) := by field_simp; ring
  rw [halg, sqrt_mul (le_of_lt hn)]

/-- The correlation `u = a_i / √(∑ a_j² + nε)` lies in `[-1, 1]`.
Paper: proof of `thm:gaussianrms` (normalization_gaussian.tex). -/
theorem correlation_mem {n : ℕ} (a : Fin n → ℝ) (i : Fin n) {ε : ℝ} (hε : 0 < ε) :
    |a i / √(∑ j, a j ^ 2 + n * ε)| ≤ 1 := by
  have hn : (0 : ℝ) < n := by
    have : 0 < n := Fin.pos i
    exact_mod_cast this
  have hpos : 0 < ∑ j, a j ^ 2 + n * ε := by
    have := sum_nonneg (fun j (_ : j ∈ univ) => sq_nonneg (a j)); positivity
  rw [abs_div, abs_of_pos (sqrt_pos.2 hpos), div_le_one (sqrt_pos.2 hpos), ← sqrt_sq_eq_abs]
  apply sqrt_le_sqrt
  have : a i ^ 2 ≤ ∑ j, a j ^ 2 :=
    single_le_sum (f := fun j => a j ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)
  nlinarith

/-- **The closing step of the intrinsic-radius factory.** If the intermediate sign has mean
`(2/π) arcsin u` with `u = a_i/√(∑ a_j² + nε)`, the quarter-sine factory (mean
`(1/4) sin((π/2) z)` on inputs of mean `z`) returns mean `a_i / (4 √n √(ε + n⁻¹ ∑ a_j²))`.
The intermediate mean itself (conditional erf mean, `G₀` representation, covariance, arcsine
law) is not formalized.
Paper: `thm:gaussianrms` (normalization_gaussian.tex); second part of `thm:main-rms`
(main_normalization.tex). -/
theorem gaussian_rms_output_mean {n : ℕ} (a : Fin n → ℝ) (i : Fin n) {ε : ℝ} (hε : 0 < ε) :
    (1 / 4 : ℝ) * sin (π / 2 * ((2 / π) * arcsin (a i / √(∑ j, a j ^ 2 + n * ε))))
      = a i / (4 * √n * √(ε + (1 / n) * ∑ j, a j ^ 2)) := by
  have hm := correlation_mem a i hε
  rw [quarter_sine_after_arcsine _ (abs_le.1 hm).1 (abs_le.1 hm).2]
  have hn : (0 : ℝ) < n := by
    have : 0 < n := Fin.pos i
    exact_mod_cast this
  rw [gaussian_rms_denominator n ε _ hn]
  rw [show (∑ j, a j ^ 2) / n = (1 / n) * ∑ j, a j ^ 2 by ring]
  ring

/-- The closing step through the sine series: with `c₀ = π/2` and inputs of mean
`z = (2/π) arcsin u`, `u = a_i/√(∑ a_j² + nε)`, the degree-`(2k+1)` branches of the sine factory
(probability `c₀^{2k+1}/(4(2k+1)!)`, output `(-1)^k` times a product of `2k+1` inputs) sum to
`a_i / (4 √n √(ε + n⁻¹ ∑ a_j²))`.
Paper: proof of `thm:gaussianrms`, with `lem:sinequarter` (normalization_gaussian.tex). -/
theorem gaussian_rms_output_series {n : ℕ} (a : Fin n → ℝ) (i : Fin n) {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun k : ℕ => (π / 2) ^ (2 * k + 1) / (4 * ((2 * k + 1).factorial : ℝ))
      * ((-1) ^ k * ((2 / π) * arcsin (a i / √(∑ j, a j ^ 2 + n * ε))) ^ (2 * k + 1)))
      (a i / (4 * √n * √(ε + (1 / n) * ∑ j, a j ^ 2))) := by
  have h := sine_series_mean (π / 2) ((2 / π) * arcsin (a i / √(∑ j, a j ^ 2 + n * ε)))
  rw [← gaussian_rms_output_mean a i hε]
  convert h using 1
  ring

/-! ### Moments of a standard Gaussian -/

/-- `𝔼 G² = 1` for a standard Gaussian `G`.
Paper: proof of `thm:gaussianrms` (normalization_gaussian.tex). -/
theorem gaussian_second_moment : ∫ x, x ^ 2 ∂ProbabilityTheory.gaussianReal 0 1 = 1 := by
  have h := ProbabilityTheory.variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [ProbabilityTheory.variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

/-- `∫₀^∞ x e^{-x²/2} dx = 1`; supports `gaussian_abs_moment`.
Paper: proof of `thm:gaussianrms` (normalization_gaussian.tex). -/
theorem integral_mul_exp_half :
    ∫ x in Set.Ioi (0 : ℝ), x * exp (-1 / 2 * x ^ 2) = 1 := by
  have A : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt (fun x : ℝ => -exp (-1 / 2 * x ^ 2))
      (x * exp (-1 / 2 * x ^ 2)) x := by
    intro x _
    have := (((hasDerivAt_pow 2 x).const_mul (-1 / 2 : ℝ)).exp).neg
    convert this using 1; push_cast; ring
  have B : Filter.Tendsto (fun x : ℝ => -exp (-1 / 2 * x ^ 2)) Filter.atTop (nhds (-0)) := by
    refine Filter.Tendsto.neg ?_
    exact tendsto_exp_atBot.comp
      ((Filter.tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by norm_num))
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' A
    (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2) |>.integrableOn |>.congr_fun
      (fun x _ => by ring_nf) measurableSet_Ioi) B]
  simp

/-- `𝔼|G| = √(2/π)` for a standard Gaussian `G`.
Paper: proof of `thm:gaussianrms` (normalization_gaussian.tex). -/
theorem gaussian_abs_moment : ∫ x, |x| ∂ProbabilityTheory.gaussianReal 0 1 = √(2 / π) := by
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul one_ne_zero]
  have e : ∀ x : ℝ, ProbabilityTheory.gaussianPDFReal 0 1 x • |x|
      = (fun y : ℝ => (√(2 * π))⁻¹ * (y * exp (-1 / 2 * y ^ 2))) |x| := by
    intro x
    simp only [ProbabilityTheory.gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one,
      sub_zero, sq_abs]
    ring_nf
  rw [show (fun x : ℝ => ProbabilityTheory.gaussianPDFReal 0 1 x • |x|)
      = fun x => (fun y : ℝ => (√(2 * π))⁻¹ * (y * exp (-1 / 2 * y ^ 2))) |x| from funext e,
    integral_comp_abs (f := fun y : ℝ => (√(2 * π))⁻¹ * (y * exp (-1 / 2 * y ^ 2))),
    integral_const_mul, integral_mul_exp_half, mul_one]
  have hp : 0 < π := pi_pos
  rw [show (2 : ℝ) * (√(2 * π))⁻¹ = 2 / √(2 * π) by ring, sqrt_div (by norm_num),
    sqrt_mul (by norm_num)]
  have h2 : (0 : ℝ) < √2 := by positivity
  have hs : √2 * √2 = 2 := mul_self_sqrt (by norm_num)
  field_simp
  linear_combination (-1 : ℝ) * hs

/-- `𝔼 G⁴ = 3` for a standard Gaussian `G`, from the fourth derivative of `e^{t²/2}` at `0`.
Paper: proof of `lem:gaussianrmsbits` (normalization_gaussian.tex). -/
theorem gaussian_fourth_moment : ∫ x, x ^ 4 ∂ProbabilityTheory.gaussianReal 0 1 = 3 := by
  have h := ProbabilityTheory.iteratedDeriv_mgf_zero (X := fun x : ℝ => x)
    (μ := ProbabilityTheory.gaussianReal 0 1) (by simp) 4
  rw [ProbabilityTheory.mgf_fun_id_gaussianReal] at h
  simp only [Pi.pow_apply] at h
  rw [← h]
  have e : ∀ t : ℝ, exp (0 * t + ((1 : NNReal) : ℝ) * t ^ 2 / 2) = exp (t ^ 2 / 2) := by
    intro t; push_cast; ring_nf
  simp only [e]
  have d1 : deriv (fun t : ℝ => exp (t ^ 2 / 2)) = fun t => t * exp (t ^ 2 / 2) := by
    funext t
    exact ((((hasDerivAt_pow 2 t).div_const 2).exp)).deriv.trans (by ring)
  have d2 : deriv (fun t : ℝ => t * exp (t ^ 2 / 2))
      = fun t => (1 + t ^ 2) * exp (t ^ 2 / 2) := by
    funext t
    exact ((hasDerivAt_id t).mul (((hasDerivAt_pow 2 t).div_const 2).exp)).deriv.trans
      (by simp; ring)
  have d3 : deriv (fun t : ℝ => (1 + t ^ 2) * exp (t ^ 2 / 2))
      = fun t => (3 * t + t ^ 3) * exp (t ^ 2 / 2) := by
    funext t
    exact ((((hasDerivAt_pow 2 t).const_add 1)).mul
      (((hasDerivAt_pow 2 t).div_const 2).exp)).deriv.trans (by simp; ring)
  have d4 : deriv (fun t : ℝ => (3 * t + t ^ 3) * exp (t ^ 2 / 2))
      = fun t => (3 + 6 * t ^ 2 + t ^ 4) * exp (t ^ 2 / 2) := by
    funext t
    exact ((((hasDerivAt_id t).const_mul 3).add (hasDerivAt_pow 3 t)).mul
      (((hasDerivAt_pow 2 t).div_const 2).exp)).deriv.trans (by simp; ring)
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, d1, d2, d3,
    d4]
  simp

/-- The scaling step for `2𝔼c²`: inserting `𝔼 G² = 1` and `𝔼|G| = √(2/π)` (proved above for
`gaussianReal 0 1`) into `𝔼(∑|G_j|)² = n𝔼G² + n(n-1)(𝔼|G|)²` and multiplying by `κ/n` gives
`κ(1 + 2(n-1)/π)`. The expansion of `𝔼(∑|G_j|)²` by independence is not formalized.
Paper: proof of `thm:gaussianrms` (normalization_gaussian.tex). -/
theorem gaussian_second_moment_cost (n κ : ℝ) (hn : n ≠ 0) :
    κ / n * (n * ∫ x, x ^ 2 ∂ProbabilityTheory.gaussianReal 0 1
        + n * (n - 1) * (∫ x, |x| ∂ProbabilityTheory.gaussianReal 0 1) ^ 2)
      = κ * (1 + 2 * (n - 1) / π) := by
  rw [gaussian_second_moment, gaussian_abs_moment, sq_sqrt (by positivity)]
  field_simp

/-- `2 c² = (R²/(nε)) (∑|G_j|)²` for `c = R ∑|G_j| / √(2nε)`.
Paper: proof of `thm:gaussianrms` (normalization_gaussian.tex). -/
theorem two_c_sq (R S n ε : ℝ) (hn : 0 < n) (hε : 0 < ε) :
    2 * (R * S / √(2 * n * ε)) ^ 2 = R ^ 2 / (n * ε) * S ^ 2 := by
  rw [div_pow, mul_pow, sq_sqrt (by positivity)]
  field_simp

/-- **The source bound `eq:gaussianrmscost`.** With `κ = R²/ε`, `n ≥ 1` and `C_sin < 1`,
`C_sin (1 + κ[1 + 2(n-1)/π]) ≤ 1 + nκ`.
Paper: `eq:gaussianrmscost` in `thm:gaussianrms` (normalization_gaussian.tex). -/
theorem gaussian_rms_cost {n κ : ℝ} (hn : 1 ≤ n) (hκ : 0 ≤ κ) :
    π / 8 * cosh (π / 2) * (1 + κ * (1 + 2 * (n - 1) / π)) ≤ 1 + n * κ := by
  have hC := sine_constant_lt_one.1
  have hC0 : 0 < π / 8 * cosh (π / 2) := by have := cosh_pos (π / 2); positivity
  have hpi : 3 < π := pi_gt_three
  have h2 : 2 * (n - 1) / π ≤ n - 1 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hX : 0 ≤ 1 + κ * (1 + 2 * (n - 1) / π) := by
    have : 0 ≤ 2 * (n - 1) / π := div_nonneg (by linarith) (by positivity)
    positivity
  calc π / 8 * cosh (π / 2) * (1 + κ * (1 + 2 * (n - 1) / π))
      ≤ 1 * (1 + κ * (1 + 2 * (n - 1) / π)) := mul_le_mul_of_nonneg_right hC.le hX
    _ ≤ 1 + n * κ := by nlinarith

/-! ## Centered normalization (`cor:gelulayernorm`) -/

/-- A fair choice between an `a_i/R` sign and the negative of a uniformly chosen coordinate sign
has mean `(a_i - μ)/(2R)`.
Paper: proof of `cor:gelulayernorm` (normalization_gaussian.tex). -/
theorem centered_mixture {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (i : Fin n) (R : ℝ) :
    (1 / 2) * (a i / R) + (1 / 2) * (-((1 / (n : ℝ)) * ∑ j, a j / R))
      = (a i - (1 / (n : ℝ)) * ∑ j, a j) / (2 * R) := by
  rw [← sum_div]
  by_cases hR : R = 0
  · simp [hR]
  · have : (n : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-- The centered coordinates are bounded by `2R`.
Paper: proof of `cor:gelulayernorm` (normalization_gaussian.tex). -/
theorem centered_bound {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) {R : ℝ} (ha : ∀ j, |a j| ≤ R)
    (i : Fin n) : |a i - (1 / (n : ℝ)) * ∑ j, a j| ≤ 2 * R := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmean : |(1 / (n : ℝ)) * ∑ j, a j| ≤ R := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 1 / (n : ℝ) * |∑ j, a j| ≤ 1 / n * ∑ j, |a j| :=
          mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
      _ ≤ 1 / n * ∑ _j : Fin n, R :=
          mul_le_mul_of_nonneg_left (sum_le_sum (fun j _ => ha j)) (by positivity)
      _ = R := by simp; field_simp
  calc |a i - (1 / (n : ℝ)) * ∑ j, a j| ≤ |a i| + |(1 / (n : ℝ)) * ∑ j, a j| := abs_sub _ _
    _ ≤ R + R := add_le_add (ha i) hmean
    _ = 2 * R := by ring

/-- The arithmetic of the count in `cor:gelulayernorm`: the bound `1 + nR'²/ε` of
`thm:gaussianrms` at the coordinate bound `R' = 2R` equals `1 + 4nR²/ε`.
Paper: `cor:gelulayernorm` (normalization_gaussian.tex); `thm:main-rms`
(main_normalization.tex), regularized LayerNorm. -/
theorem centered_cost (n R ε : ℝ) : 1 + n * ((2 * R) ^ 2 / ε) = 1 + 4 * n * R ^ 2 / ε := by
  ring

/-! ## Finite-bit implementation (`lem:gaussianrmsbits`) -/

/-- `(∑|G_j|)⁴ ≤ n³ ∑ G_j⁴`.
Paper: proof of `lem:gaussianrmsbits` (normalization_gaussian.tex). -/
theorem sum_abs_pow_four_le {n : ℕ} (G : Fin n → ℝ) :
    (∑ j, |G j|) ^ 4 ≤ (n : ℝ) ^ 3 * ∑ j, G j ^ 4 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have h := pow_sum_div_card_le_sum_pow (s := (univ : Finset (Fin n))) (f := fun j => |G j|)
    (fun j _ => abs_nonneg _) 3
  simp only [card_univ, Fintype.card_fin] at h
  norm_num at h
  have e : ∀ j, |G j| ^ 4 = G j ^ 4 := fun j => by
    rw [pow_abs, abs_of_nonneg (by positivity)]
  simp only [e] at h
  have hn' : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  rw [div_le_iff₀ hn'] at h
  linarith

/-- `c⁴ = κ² S⁴ / (4n²)` for `c = R S/√(2nε)` and `κ = R²/ε`.
Paper: proof of `lem:gaussianrmsbits` (normalization_gaussian.tex). -/
theorem c_fourth (R S n ε : ℝ) (hn : 0 < n) (hε : 0 < ε) :
    (R * S / √(2 * n * ε)) ^ 4 = (R ^ 2 / ε) ^ 2 / (4 * n ^ 2) * S ^ 4 := by
  have h : (R * S / √(2 * n * ε)) ^ 4 = ((R * S / √(2 * n * ε)) ^ 2) ^ 2 := by ring
  rw [h, div_pow, mul_pow, sq_sqrt (by positivity)]
  field_simp
  ring

/-- The scaling step for `𝔼c⁴`: if `𝔼 S⁴ ≤ n³ ∑_j 𝔼 G_j⁴` (the integrated form of
`sum_abs_pow_four_le`, not formalized), then `𝔼 G⁴ = 3` (`gaussian_fourth_moment`) and
`c⁴ = κ² S⁴/(4n²)` give `𝔼 c⁴ ≤ (3/4) n² κ²`.
Paper: proof of `lem:gaussianrmsbits` (normalization_gaussian.tex). -/
theorem c_fourth_moment_le {n κ ES4 : ℝ} (hn : 0 < n)
    (hES : ES4 ≤ n ^ 3 * (n * ∫ x, x ^ 4 ∂ProbabilityTheory.gaussianReal 0 1)) :
    κ ^ 2 / (4 * n ^ 2) * ES4 ≤ 3 / 4 * n ^ 2 * κ ^ 2 := by
  rw [gaussian_fourth_moment] at hES
  have h0 : 0 ≤ κ ^ 2 / (4 * n ^ 2) := by positivity
  calc κ ^ 2 / (4 * n ^ 2) * ES4 ≤ κ ^ 2 / (4 * n ^ 2) * (n ^ 3 * (n * 3)) :=
        mul_le_mul_of_nonneg_left hES h0
    _ = 3 / 4 * n ^ 2 * κ ^ 2 := by field_simp

/-- `2 𝔼 c² ≤ nκ`, from the exact value `κ(1 + 2(n-1)/π)`.
Paper: proof of `lem:gaussianrmsbits` (normalization_gaussian.tex). -/
theorem two_c_sq_mean_le {n κ : ℝ} (hn : 1 ≤ n) (hκ : 0 ≤ κ) :
    κ * (1 + 2 * (n - 1) / π) ≤ n * κ := by
  have hpi : 3 < π := pi_gt_three
  have h2 : 2 * (n - 1) / π ≤ n - 1 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  nlinarith

/-- A mean bound and a fourth-moment bound control the correlated precision cost:
`𝔼(1+c²)² = 1 + 2𝔼c² + 𝔼c⁴ ≤ (1 + nκ)²` with `x = nκ`.
Paper: proof of `lem:gaussianrmsbits` (normalization_gaussian.tex). -/
theorem second_moment_envelope (x m2 m4 : ℝ) (hx : 0 ≤ x) (hm2 : m2 ≤ x / 2)
    (hm4 : m4 ≤ (3 / 4 : ℝ) * x ^ 2) : 1 + 2 * m2 + m4 ≤ (1 + x) ^ 2 := by
  nlinarith [sq_nonneg x]

/-- The triangle inequality in `L²`, in the form used for `{𝔼(n+1+c²)²}^{1/2}`: if
`𝔼X ≤ √(𝔼X²)` then `𝔼(m+X)² ≤ (m + √(𝔼X²))²`.
Paper: proof of `lem:gaussianrmsbits` (normalization_gaussian.tex). -/
theorem l2_shift (m m1 m2 : ℝ) (hm : 0 ≤ m) (hm2 : 0 ≤ m2) (h1 : m1 ≤ √m2) :
    m ^ 2 + 2 * m * m1 + m2 ≤ (m + √m2) ^ 2 := by
  have := sq_sqrt hm2
  nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ 2 * m)]

/-- The integer envelope weight `u = h max{1, ⌈b/h⌉}` of a Gaussian magnitude `g = |G_j|`,
where `b` is the upper end of an enclosure of width at most `h/4`: `g ≤ u ≤ g + 2h`, `u ≥ h`.
Paper: proof of `lem:gaussianrmsbits` (normalization_gaussian.tex). -/
theorem envelope_weight {g b h : ℝ} (hh : 0 < h) (hg : 0 ≤ g) (hb1 : g ≤ b) (hb2 : b ≤ g + h / 4) :
    g ≤ h * max 1 (⌈b / h⌉ : ℝ) ∧ h * max 1 (⌈b / h⌉ : ℝ) ≤ g + 2 * h ∧
      h ≤ h * max 1 (⌈b / h⌉ : ℝ) := by
  have hc1 : b / h ≤ (⌈b / h⌉ : ℝ) := Int.le_ceil _
  have hc2 : (⌈b / h⌉ : ℝ) < b / h + 1 := Int.ceil_lt_add_one _
  refine ⟨?_, ?_, ?_⟩
  · calc g ≤ b := hb1
      _ = h * (b / h) := by field_simp
      _ ≤ h * (⌈b / h⌉ : ℝ) := mul_le_mul_of_nonneg_left hc1 hh.le
      _ ≤ h * max 1 (⌈b / h⌉ : ℝ) := mul_le_mul_of_nonneg_left (le_max_right _ _) hh.le
  · rcases max_cases 1 (⌈b / h⌉ : ℝ) with ⟨hm, _⟩ | ⟨hm, _⟩
    · rw [hm]; linarith
    · rw [hm]
      have : h * (⌈b / h⌉ : ℝ) ≤ h * (b / h + 1) := mul_le_mul_of_nonneg_left hc2.le hh.le
      have e : h * (b / h + 1) = b + h := by field_simp
      linarith
  · calc h = h * 1 := (mul_one h).symm
      _ ≤ h * max 1 (⌈b / h⌉ : ℝ) := mul_le_mul_of_nonneg_left (le_max_left _ _) hh.le

/-- The proposal envelope has total `U ≤ S + 2nh ≤ (9/8) S` when `σ ≤ S` and `h ≤ σ/(16n)`.
Paper: proof of `lem:gaussianrmsbits` (normalization_gaussian.tex). -/
theorem envelope_total_bound (S sigma n h U : ℝ) (hn : 0 < n) (hS : sigma ≤ S)
    (hh : h ≤ sigma / (16 * n)) (hU : U ≤ S + 2 * n * h) : U ≤ (9 : ℝ) / 8 * S := by
  have hscale := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 * n)
  have hid : (2 * n) * (sigma / (16 * n)) = sigma / 8 := by field_simp; ring
  rw [hid] at hscale
  linarith

/-- The integer weights `u_j/h` sum to at most `66n` when `S ≤ 2σ` and `σ/(32n) ≤ h`.
Paper: proof of `lem:gaussianrmsbits` (normalization_gaussian.tex). -/
theorem envelope_unit_count (S sigma n h U : ℝ) (hn : 0 < n) (hh0 : 0 < h) (hS : S ≤ 2 * sigma)
    (hh : sigma / (32 * n) ≤ h) (hU : U ≤ S + 2 * n * h) : U / h ≤ 66 * n := by
  rw [div_le_iff₀ hh0]
  have : sigma ≤ 32 * n * h := by rw [div_le_iff₀ (by positivity)] at hh; linarith
  nlinarith

/-- The accepted coordinate has law proportional to `|G_j|`, and the acceptance probability
`S/U` is at least `8/9`; the mean number of proposals is at most `9/8`.
Paper: proof of `lem:gaussianrmsbits` (normalization_gaussian.tex). -/
theorem envelope_acceptance {S U : ℝ} (hS : 0 < S) (hU : U ≤ (9 : ℝ) / 8 * S) (hU0 : 0 < U) :
    8 / 9 ≤ S / U ∧ U / S ≤ 9 / 8 := by
  constructor
  · rw [le_div_iff₀ hU0]; linarith
  · rw [div_le_iff₀ hS]; linarith

/-- The Poisson bulk and residual: if `μ ∈ [ℓ₀, ℓ₀ + 1/4]` and `0 ≤ μ ≤ c²`, then
`ℓ = max{0, ℓ₀}` satisfies `0 ≤ ℓ ≤ μ ≤ c²` and `0 ≤ μ - ℓ ≤ 1/4`.
Paper: proof of `lem:gaussianrmsbits` (normalization_gaussian.tex). -/
theorem poisson_split {μ l0 c : ℝ} (hμ0 : 0 ≤ μ) (hμc : μ ≤ c ^ 2) (h1 : l0 ≤ μ)
    (h2 : μ ≤ l0 + 1 / 4) :
    0 ≤ max 0 l0 ∧ max 0 l0 ≤ μ ∧ μ ≤ c ^ 2 ∧ 0 ≤ μ - max 0 l0 ∧ μ - max 0 l0 ≤ 1 / 4 := by
  have hm1 : max 0 l0 ≤ μ := max_le hμ0 h1
  refine ⟨le_max_left _ _, hm1, hμc, by linarith, ?_⟩
  have := le_max_right 0 l0
  linarith

/-- Rounding the intrinsic radius up to `4m`, `m = ⌈√n⌉`, by thinning with probability `√n/m`.
Paper: `lem:gaussianrmsbits` (normalization_gaussian.tex), last paragraph. -/
theorem rms_radius_thinning (a v n m : ℝ) (hn : 0 < n) (hm : m ≠ 0) :
    (√n / m) * (a / (4 * √n * √v)) = a / (4 * m * √v) := by
  have hs : √n ≠ 0 := ne_of_gt (sqrt_pos.2 hn)
  by_cases hv : √v = 0
  · simp [hv]
  · field_simp

/-- The thinning probability `√n/⌈√n⌉` lies in `(0, 1]`.
Paper: `lem:gaussianrmsbits` (normalization_gaussian.tex), last paragraph. -/
theorem integer_radius_prob {n : ℝ} (hn : 0 < n) :
    0 < √n / (⌈√n⌉₊ : ℝ) ∧ √n / (⌈√n⌉₊ : ℝ) ≤ 1 := by
  have hs : 0 < √n := sqrt_pos.2 hn
  have hc : √n ≤ (⌈√n⌉₊ : ℝ) := Nat.le_ceil _
  have hc0 : 0 < (⌈√n⌉₊ : ℝ) := lt_of_lt_of_le hs hc
  exact ⟨div_pos hs hc0, (div_le_one hc0).2 hc⟩

end ExactSampling.GaussianRMS
