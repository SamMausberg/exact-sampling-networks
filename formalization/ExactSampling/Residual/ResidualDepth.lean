import Mathlib

/-!
# Residual radii, range comparison, and the critical sums

This module formalizes the analytic estimates of `tanh_residual.tex` and
`tanh_residual_fused.tex` that control the residual sampler:

* the reciprocal-square inequalities `u^{-2} + 2/3 ≤ coth^2 u ≤ u^{-2} + 1` (the
  first is `eq:cothradius` of `lem:radius` in `tanh_rates.tex`; both are used in
  `tanh_mean.tex` and throughout the residual analysis), proved from the power
  series of `cosh`, and their consequences `tanh r ≤ r (1 - r^2/5)` on `[0, 1]` and
  `tanh y ≤ y (1 - y^2/10)` on `[0, 2]`;
* the residual range lemma `lem:resrange`;
* for the ideal radii `R_j`: the critical bound `R_j^2 ≤ (1 + 2αj/5)^{-1}`, the
  bound `R_j ≥ (1 + αj)^{-1/2}` of `eq:resradiuslower` (the comparison `r_j ≥ R_j`
  belongs to the rounding lemma and is not formalized), and the supercritical
  envelope `lem:residualsuperradius`;
* the logarithmic step `eq:reslogproduct`, the sum estimates `eq:resintegrals`
  (from the declared rounding stand-ins), the ideal part `25/(4J^2) + 25/(4J)` of
  `eq:rescutoffbounds`, and the supercritical fourth-power sum in the proof of
  `thm:residualupper`;
* the radial comparison `lem:resradial` in full (`eq:reschicritical` and
  `eq:reschisuper`), with `χ_g` as defined in `sec:residual`;
* for the residual mean network of `thm:resmeanlaw`: the derivative product
  formula for `F_D'`, the loss bound `0 ≤ λ - F_D'(z) ≤ λ min{1, Az^2}`, and the
  full-majority bound `Q ≤ 2λ√(1+A)`; and the bound `Q_u ≤ 2 max{u, u^2}` of
  `lem:comptanharity` used in `prop:largerow`.

Not formalized: the rounding lemma `eq:resroundingerror` (`r_j ≥ R_j`,
`r_j - R_j ≤ 3jαε`, which enter `resintegrals` as declared stand-ins); the parts
`r_j^2 ≤ 3/J` and `α ∑ r_j^4 ≤ 14/J` of `eq:rescutoffbounds`; the supercritical
half of `thm:residualupper` (`eq:ressuperupper`: the constant `10 e^{30}`, the factor
`e^{6025 δ α (D-k)}`, `R^{(g)}_j ≤ a^j R^{(1)}_j`, and `α ∑ r_j^5 ≤ 4 e^{5δτ}`); the
expected-offspring bound `lem:offspring` behind the definition of `χ_g`; the complete
monotonicity in `lem:resglobalmajority`; the integration-by-parts formulas that
express the full-majority counts as integrals (the left-hand sides of
`resmean_majority_cost` and `majority_count_le`); the choice of strategy behind
`Q* ≤ 3Ξ`; and the probabilistic recursion. These enter only through the displayed
hypotheses.
-/

open Real Finset

namespace ExactSampling.ResidualDepth

/-! ## Elementary facts about `tanh` -/

/-- Auxiliary: `tanh' = 1/cosh^2`. -/
theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have hfun : Real.sinh / Real.cosh = Real.tanh := by
    funext y
    rw [Pi.div_apply, Real.tanh_eq_sinh_div_cosh]
  rw [hfun] at h
  convert h using 1
  have := Real.cosh_sq x
  field_simp
  linarith

/-- Auxiliary: `1/cosh^2 = 1 - tanh^2`. -/
theorem one_div_cosh_sq_eq (x : ℝ) : 1 / Real.cosh x ^ 2 = 1 - Real.tanh x ^ 2 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc := Real.cosh_pos x
  have := Real.cosh_sq x
  field_simp
  linarith

/-- Auxiliary: `tanh` is monotone. -/
theorem tanh_monotone : Monotone Real.tanh := by
  refine monotone_of_deriv_nonneg (fun x => (hasDerivAt_tanh x).differentiableAt)
    fun x => ?_
  rw [(hasDerivAt_tanh x).deriv]
  positivity

/-- Auxiliary for `lem:resradial` and `lem:residualsuperradius`: the map
`x ↦ x - tanh x` is monotone, so `tanh` is `1`-Lipschitz. -/
theorem sub_tanh_monotone : Monotone (fun x => x - Real.tanh x) := by
  have hd : ∀ x, HasDerivAt (fun x => x - Real.tanh x) (1 - 1 / Real.cosh x ^ 2) x :=
    fun x => (hasDerivAt_id x).sub (hasDerivAt_tanh x)
  refine monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt) fun x => ?_
  rw [(hd x).deriv]
  have h1 : 1 ≤ Real.cosh x ^ 2 := by nlinarith [Real.one_le_cosh x]
  rw [sub_nonneg, div_le_one (by positivity)]
  exact h1

/-- Auxiliary: `tanh y - tanh x ≤ y - x` for `x ≤ y` (unit Lipschitz bound). -/
theorem tanh_sub_le (x y : ℝ) (h : x ≤ y) : Real.tanh y - Real.tanh x ≤ y - x := by
  have := sub_tanh_monotone h
  simp only at this
  linarith

/-- Auxiliary: `tanh x ≥ 0` for `x ≥ 0`. -/
theorem tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  have := tanh_monotone hx
  rwa [Real.tanh_zero] at this

/-- Auxiliary: `tanh x ≤ x` for `x ≥ 0`. -/
theorem tanh_le_self {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  have := tanh_sub_le 0 x hx
  rwa [Real.tanh_zero, sub_zero, sub_zero] at this

/-- Auxiliary for the reciprocal-square inequalities: `cosh y (12 - y^2) ≤ 12 + 5 y^2`,
from the power series of `cosh`. -/
theorem cosh_mul_twelve_sub_le (y : ℝ) : Real.cosh y * (12 - y ^ 2) ≤ 12 + 5 * y ^ 2 := by
  set f : ℕ → ℝ := fun n => y ^ (2 * n) / ((2 * n).factorial : ℝ) with hf
  have hs : HasSum f (Real.cosh y) := Real.hasSum_cosh y
  have hs1 : HasSum (fun n => f (n + 1)) (Real.cosh y - 1) := by
    have := (hasSum_nat_add_iff' 1).mpr hs
    simpa [hf] using this
  have hg : HasSum (fun n => 12 * f (n + 1) - y ^ 2 * f n)
      (12 * (Real.cosh y - 1) - y ^ 2 * Real.cosh y) :=
    (hs1.mul_left 12).sub (hs.mul_left (y ^ 2))
  have hfac : ∀ n : ℕ, y ^ 2 * f n = ((2 * n + 2) * (2 * n + 1) : ℝ) * f (n + 1) := by
    intro n
    simp only [hf]
    have e1 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [e1, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    have : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
    rw [pow_succ, pow_succ]
    field_simp
    ring
  have hterm : ∀ n : ℕ, 12 * f (n + 1) - y ^ 2 * f n ≤
      if n = 0 then 5 * y ^ 2 else 0 := by
    intro n
    rw [hfac n]
    have hf1 : 0 ≤ f (n + 1) := by
      simp only [hf]
      have : y ^ (2 * (n + 1)) = (y ^ 2) ^ (n + 1) := by rw [pow_mul]
      rw [this]
      positivity
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp [hf]
      ring_nf
      rfl
    · simp only [hpos.ne', ite_false]
      have hn : (1 : ℝ) ≤ n := by exact_mod_cast hpos
      have : (12 : ℝ) - (2 * n + 2) * (2 * n + 1) ≤ 0 := by nlinarith
      nlinarith
  have hb : HasSum (fun n : ℕ => if n = 0 then 5 * y ^ 2 else 0) (5 * y ^ 2) :=
    hasSum_ite_eq 0 (5 * y ^ 2)
  have := hasSum_le hterm hg hb
  linarith

/-- Paper: proofs of `lem:resrange` and `eq:resradiuslower` (tanh_residual.tex): the
reciprocal-square upper bound `coth^2 u ≤ u^{-2} + 1` (also used in `tanh_mean.tex`),
in the form `u^2/(1+u^2) ≤ tanh^2 u`. -/
theorem sq_div_le_sq_tanh (u : ℝ) : u ^ 2 / (1 + u ^ 2) ≤ Real.tanh u ^ 2 := by
  rw [Real.tanh_eq_sinh_div_cosh, div_pow, div_le_div_iff₀ (by positivity)
    (by positivity [Real.cosh_pos u])]
  have hc := Real.cosh_sq u
  have hs : u ^ 2 ≤ Real.sinh u ^ 2 := by
    rcases le_total 0 u with hu | hu
    · have := Real.self_le_sinh_iff.mpr hu
      nlinarith
    · have h1 := Real.self_le_sinh_iff.mpr (neg_nonneg.mpr hu)
      rw [Real.sinh_neg] at h1
      nlinarith
  rw [hc]
  nlinarith

/-- Paper: `eq:cothradius` of `lem:radius` (tanh_rates.tex), used in the proofs of
`lem:resrange` and `thm:residualupper`: the reciprocal-square lower bound
`u^{-2} + 2/3 ≤ coth^2 u`, in the form `tanh^2 u ≤ u^2/(1 + 2u^2/3)`. -/
theorem sq_tanh_le_sq_div (u : ℝ) : Real.tanh u ^ 2 ≤ u ^ 2 / (1 + 2 * u ^ 2 / 3) := by
  rw [Real.tanh_eq_sinh_div_cosh, div_pow, div_le_div_iff₀ (by positivity [Real.cosh_pos u])
    (by positivity)]
  have h := cosh_mul_twelve_sub_le (2 * u)
  rw [Real.cosh_two_mul] at h
  have hc := Real.cosh_sq u
  nlinarith

/-- Paper: `eq:resradiuslower` and `lem:resrange` (tanh_residual.tex), the
tanh lower bound `tanh u ≥ u/√(1+u^2)` for `u ≥ 0`, in squared-ratio form:
`(tanh u / u)^2 ≥ 1/(1+u^2)`. -/
theorem tanh_ge_div_sqrt {u : ℝ} (hu : 0 ≤ u) :
    u / Real.sqrt (1 + u ^ 2) ≤ Real.tanh u := by
  have hs : 0 < Real.sqrt (1 + u ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + u ^ 2)
  have h := sq_div_le_sq_tanh u
  have ht := tanh_nonneg hu
  apply le_of_sq_le_sq _ ht
  rw [div_pow, hs2]
  exact h

/-- Paper: proof of `thm:residualupper` (tanh_residual.tex):
`tanh r / r ≤ (1 + 2r^2/3)^{-1/2} ≤ 1 - r^2/5` on `[0, 1]`. -/
theorem tanh_le_mul_one_sub_fifth {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.tanh r ≤ r * (1 - r ^ 2 / 5) := by
  have h := sq_tanh_le_sq_div r
  have ht := tanh_nonneg hr0
  have hpos : 0 ≤ r * (1 - r ^ 2 / 5) := by
    have : r ^ 2 ≤ 1 := by nlinarith
    nlinarith
  apply le_of_sq_le_sq _ hpos
  refine h.trans ?_
  rw [div_le_iff₀ (by positivity)]
  have hw0 : 0 ≤ r ^ 2 := sq_nonneg r
  have hw1 : r ^ 2 ≤ 1 := by nlinarith
  have : 1 ≤ (1 - r ^ 2 / 5) ^ 2 * (1 + 2 * r ^ 2 / 3) := by
    nlinarith [mul_nonneg hw0 hw0, mul_nonneg (mul_nonneg hw0 hw0) hw0]
  nlinarith [mul_le_mul_of_nonneg_left this hw0]

/-- Paper: proof of `lem:resrange` (tanh_residual.tex):
`tanh y / y ≤ (1 + 2y^2/3)^{-1/2} ≤ 1 - y^2/10` on `[0, 2]`. -/
theorem tanh_le_mul_one_sub_tenth {y : ℝ} (hy0 : 0 ≤ y) (hy2 : y ≤ 2) :
    Real.tanh y ≤ y * (1 - y ^ 2 / 10) := by
  have h := sq_tanh_le_sq_div y
  have ht := tanh_nonneg hy0
  have hw0 : 0 ≤ y ^ 2 := sq_nonneg y
  have hw1 : y ^ 2 ≤ 4 := by nlinarith
  have hpos : 0 ≤ y * (1 - y ^ 2 / 10) := by nlinarith
  apply le_of_sq_le_sq _ hpos
  refine h.trans ?_
  rw [div_le_iff₀ (by positivity)]
  have : 1 ≤ (1 - y ^ 2 / 10) ^ 2 * (1 + 2 * y ^ 2 / 3) := by
    nlinarith [mul_nonneg hw0 hw0, mul_nonneg (mul_nonneg hw0 hw0) hw0,
      mul_nonneg (mul_nonneg hw0 hw0) (by linarith : (0 : ℝ) ≤ 4 - y ^ 2)]
  nlinarith [mul_le_mul_of_nonneg_left this hw0]

/-- Auxiliary for `lem:resrange` and `eq:resradiuslower` (tanh_residual.tex):
convexity of `u ↦ (1+u)^{-1/2}` in the form
`(1 + v w)^{-1/2} ≤ (1-v) + v (1+w)^{-1/2}` for `v ∈ [0,1]`, `w ≥ 0`. -/
theorem inv_sqrt_convex (v w : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hw : 0 ≤ w) :
    1 / Real.sqrt (1 + v * w) ≤ (1 - v) + v / Real.sqrt (1 + w) := by
  set S := Real.sqrt (1 + w) with hS
  set T := Real.sqrt (1 + v * w) with hT
  have hS1 : 1 ≤ S := by
    rw [hS]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + w) := Real.sqrt_le_sqrt (by linarith)
  have hS2 : S ^ 2 = 1 + w := Real.sq_sqrt (by linarith)
  have hT0 : 0 < T := Real.sqrt_pos.mpr (by positivity)
  have hT2 : T ^ 2 = 1 + v * w := Real.sq_sqrt (by positivity)
  have hS0 : 0 < S := by linarith
  have hrhs : (1 - v) + v / S = (S - v * S + v) / S := by field_simp
  rw [hrhs, div_le_div_iff₀ hT0 hS0, one_mul]
  have hN : 0 ≤ S - v * S + v := by nlinarith
  have key : S ^ 2 ≤ ((S - v * S + v) * T) ^ 2 := by
    rw [mul_pow]
    rw [hT2, show w = S ^ 2 - 1 by linarith]
    have hd : 0 ≤ S - 1 := by linarith
    have hprod : 0 ≤ (1 - v) * v * (S - 1) ^ 2 * (3 + 2 * (S - 1) + (1 - v) * (S - 1) *
        (S + 1)) := by
      apply mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hv0) (sq_nonneg _))
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - v) hd)
        (by linarith : (0 : ℝ) ≤ S + 1)]
    nlinarith [hprod]
  exact le_of_sq_le_sq key (mul_nonneg hN hT0.le)

/-! ## The scalar residual chain and the range lemma -/

/-- The scalar residual chain `F_0 = z`, `F_{j+1} = (1-α) F_j + α tanh(s F_j)`
of `eq:reschainparameters`; with `z = 1` it is the ideal radius recurrence
`R_{j+1} = f_{α,s}(R_j)` of `eq:resrounded`. -/
noncomputable def chain (α s z : ℝ) : ℕ → ℝ
  | 0 => z
  | j + 1 => (1 - α) * chain α s z j + α * Real.tanh (s * chain α s z j)

/-- Paper: proof of `lem:resrange` (tanh_residual.tex), "every iterate remains in
`[0, 1]`". -/
theorem chain_mem_Icc (α s z : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hs : 0 ≤ s)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (j : ℕ) : 0 ≤ chain α s z j ∧ chain α s z j ≤ 1 := by
  induction j with
  | zero => exact ⟨hz0, hz1⟩
  | succ j ih =>
      simp only [chain]
      have ht0 := tanh_nonneg (mul_nonneg hs ih.1)
      have ht1 := (Real.tanh_lt_one (s * chain α s z j)).le
      constructor
      · have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - α) ih.1
        nlinarith
      · nlinarith

/-- Auxiliary for `lem:resrange`: the lower one-step ratio bound
`f(F)^2 (1 + θF^2) ≥ a^2 F^2`, from the tanh lower bound and convexity. -/
theorem step_lower (α s F : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hs : 0 < s)
    (hF : 0 ≤ F) :
    (1 - α + α * s) ^ 2 * F ^ 2 ≤ ((1 - α) * F + α * Real.tanh (s * F)) ^ 2 *
      (1 + α * s ^ 3 / (1 - α + α * s) * F ^ 2) := by
  set a := 1 - α + α * s with ha
  have ha0 : 0 < a := by
    rcases lt_or_ge α 1 with h | h
    · nlinarith
    · nlinarith
  set v := α * s / a with hv
  have hv0 : 0 ≤ v := by positivity
  have hv1 : v ≤ 1 := by
    rw [hv, div_le_one ha0]
    linarith
  have hw : 0 ≤ s ^ 2 * F ^ 2 := by positivity
  have hconv := inv_sqrt_convex v (s ^ 2 * F ^ 2) hv0 hv1 hw
  have htl := tanh_ge_div_sqrt (mul_nonneg hs.le hF)
  have hS : 0 < Real.sqrt (1 + (s * F) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  set T := Real.sqrt (1 + v * (s ^ 2 * F ^ 2)) with hT
  have hT0 : 0 < T := Real.sqrt_pos.mpr (by positivity)
  have hT2 : T ^ 2 = 1 + v * (s ^ 2 * F ^ 2) := Real.sq_sqrt (by positivity)
  -- `f(F) ≥ a F / T`
  have hf : a * F / T ≤ (1 - α) * F + α * Real.tanh (s * F) := by
    have e1 : (1 - α) * F + α * (s * F / Real.sqrt (1 + (s * F) ^ 2)) ≤
        (1 - α) * F + α * Real.tanh (s * F) := by
      have := mul_le_mul_of_nonneg_left htl hα0
      linarith
    have e2 : a * F / T ≤ a * F * ((1 - v) + v / Real.sqrt (1 + s ^ 2 * F ^ 2)) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hconv (by positivity)
    have e3 : a * F * ((1 - v) + v / Real.sqrt (1 + s ^ 2 * F ^ 2)) =
        (1 - α) * F + α * (s * F / Real.sqrt (1 + (s * F) ^ 2)) := by
      rw [hv, mul_pow]
      field_simp
      ring
    linarith
  have hθ : α * s ^ 3 / a * F ^ 2 = v * (s ^ 2 * F ^ 2) := by
    rw [hv]
    field_simp
  rw [hθ, ← hT2]
  have hpos : 0 ≤ a * F / T := by positivity
  have := pow_le_pow_left₀ hpos hf 2
  rw [div_pow] at this
  rw [div_le_iff₀ (by positivity)] at this
  linarith

/-- Auxiliary for `lem:resrange`: the upper one-step ratio bound
`f(F)^2 (1 + θF^2/5) ≤ a^2 F^2` for `0 < s ≤ 2` and `0 ≤ F ≤ 1`. -/
theorem step_upper (α s F : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hs : 0 < s) (hs2 : s ≤ 2)
    (hF : 0 ≤ F) (hF1 : F ≤ 1) :
    ((1 - α) * F + α * Real.tanh (s * F)) ^ 2 *
      (1 + α * s ^ 3 / (1 - α + α * s) * F ^ 2 / 5) ≤ (1 - α + α * s) ^ 2 * F ^ 2 := by
  set a := 1 - α + α * s with ha
  have ha0 : 0 < a := by
    rcases lt_or_ge α 1 with h | h
    · nlinarith
    · nlinarith
  set x := α * s ^ 3 / a * F ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hsF : s * F ≤ 2 := by nlinarith
  have hup := tanh_le_mul_one_sub_tenth (mul_nonneg hs.le hF) hsF
  have ht0 := tanh_nonneg (mul_nonneg hs.le hF)
  -- `f(F) ≤ a F (1 - x/10)`
  have hf : (1 - α) * F + α * Real.tanh (s * F) ≤ a * F * (1 - x / 10) := by
    have e1 := mul_le_mul_of_nonneg_left hup hα0
    have e2 : a * F * (1 - x / 10) = (1 - α) * F + α * (s * F * (1 - (s * F) ^ 2 / 10)) := by
      rw [hx]
      field_simp
      ring
    linarith
  have hf0 : 0 ≤ (1 - α) * F + α * Real.tanh (s * F) := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - α) hF
    nlinarith
  rcases le_or_gt (x / 10) 1 with hx10 | hx10
  · have hsq := pow_le_pow_left₀ hf0 hf 2
    have key : (1 - x / 10) ^ 2 * (1 + x / 5) ≤ 1 := by
      nlinarith [mul_nonneg hx0 hx0, mul_nonneg (mul_nonneg hx0 hx0) hx0]
    calc ((1 - α) * F + α * Real.tanh (s * F)) ^ 2 * (1 + x / 5)
        ≤ (a * F * (1 - x / 10)) ^ 2 * (1 + x / 5) :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = (a * F) ^ 2 * ((1 - x / 10) ^ 2 * (1 + x / 5)) := by ring
      _ ≤ (a * F) ^ 2 * 1 := mul_le_mul_of_nonneg_left key (by positivity)
      _ = a ^ 2 * F ^ 2 := by ring
  · -- here `f(F) ≤ 0`, so `f(F) = 0`
    have hneg : a * F * (1 - x / 10) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have hz : (1 - α) * F + α * Real.tanh (s * F) = 0 := by linarith
    rw [hz]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    positivity

/-- Paper: `lem:resrange` (tanh_residual.tex). For `0 ≤ α ≤ 1`, `0 < s ≤ 2`,
`a = 1 - α + α s`, `λ = a^D`, `A = (α s^3/a) ∑_{j<D} a^{2j}` and `0 ≤ z ≤ 1`,
`λ z / √(1 + A z^2) ≤ F_D(z) ≤ λ z / √(1 + A z^2 / 5)`. -/
theorem resrange (α s z : ℝ) (D : ℕ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hs : 0 < s)
    (hs2 : s ≤ 2) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (1 - α + α * s) ^ D * z / Real.sqrt (1 + α * s ^ 3 / (1 - α + α * s) *
        (∑ j ∈ range D, (1 - α + α * s) ^ (2 * j)) * z ^ 2) ≤ chain α s z D ∧
      chain α s z D ≤ (1 - α + α * s) ^ D * z / Real.sqrt (1 + α * s ^ 3 /
        (1 - α + α * s) * (∑ j ∈ range D, (1 - α + α * s) ^ (2 * j)) * z ^ 2 / 5) := by
  set a := 1 - α + α * s with ha
  have ha0 : 0 < a := by
    rcases lt_or_ge α 1 with h | h
    · nlinarith
    · nlinarith
  set θ := α * s ^ 3 / a with hθ
  have hθ0 : 0 ≤ θ := by positivity
  obtain ⟨A, hA⟩ : ∃ A, A = θ * ∑ j ∈ range D, a ^ (2 * j) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  rw [← hA]
  have hmem := chain_mem_Icc α s z hα0 hα1 hs.le hz0 hz1
  rcases eq_or_lt_of_le hz0 with hz | hz
  · -- `z = 0`: the chain stays at zero
    subst hz
    have h0 : ∀ j, chain α s 0 j = 0 := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => simp [chain, ih]
    simp [h0]
  -- positivity of the chain
  have hpos : ∀ j, 0 < chain α s z j := by
    intro j
    induction j with
    | zero => exact hz
    | succ j ih =>
        have h := step_lower α s (chain α s z j) hα0 hα1 hs (hmem j).1
        have hl : 0 < a ^ 2 * chain α s z j ^ 2 := by positivity
        have hne : chain α s z (j + 1) ≠ 0 := by
          intro h0
          simp only [chain] at h0
          rw [h0] at h
          simp at h
          linarith
        exact lt_of_le_of_ne (hmem (j + 1)).1 (Ne.symm hne)
  -- reciprocal-square recurrences
  have hlow : ∀ j, a ^ (2 * j) / chain α s z j ^ 2 ≤
      1 / z ^ 2 + θ * ∑ i ∈ range j, a ^ (2 * i) := by
    intro j
    induction j with
    | zero => simp [chain]
    | succ j ih =>
        have h := step_lower α s (chain α s z j) hα0 hα1 hs (hmem j).1
        have hFj := hpos j
        have hFj1 := hpos (j + 1)
        simp only [chain] at hFj1
        have step : a ^ (2 * (j + 1)) / chain α s z (j + 1) ^ 2 ≤
            a ^ (2 * j) / chain α s z j ^ 2 + θ * a ^ (2 * j) := by
          simp only [chain]
          rw [div_le_iff₀ (by positivity)]
          have e : (a ^ (2 * j) / chain α s z j ^ 2 + θ * a ^ (2 * j)) *
              ((1 - α) * chain α s z j + α * Real.tanh (s * chain α s z j)) ^ 2 =
              a ^ (2 * j) / (a ^ 2 * chain α s z j ^ 2) *
              (((1 - α) * chain α s z j + α * Real.tanh (s * chain α s z j)) ^ 2 *
                (1 + θ * chain α s z j ^ 2)) * a ^ 2 := by
            field_simp
          rw [e]
          have e2 : a ^ (2 * (j + 1)) = a ^ (2 * j) / (a ^ 2 * chain α s z j ^ 2) *
              (a ^ 2 * chain α s z j ^ 2) * a ^ 2 := by
            field_simp
            ring
          rw [e2]
          gcongr
        rw [sum_range_succ]
        have e3 := mul_add θ (∑ i ∈ range j, a ^ (2 * i)) (a ^ (2 * j))
        linarith
  have hupp : ∀ j, 1 / z ^ 2 + θ / 5 * ∑ i ∈ range j, a ^ (2 * i) ≤
      a ^ (2 * j) / chain α s z j ^ 2 := by
    intro j
    induction j with
    | zero => simp [chain]
    | succ j ih =>
        have h := step_upper α s (chain α s z j) hα0 hα1 hs hs2 (hmem j).1 (hmem j).2
        have hFj := hpos j
        have hFj1 := hpos (j + 1)
        simp only [chain] at hFj1
        have step : a ^ (2 * j) / chain α s z j ^ 2 + θ / 5 * a ^ (2 * j) ≤
            a ^ (2 * (j + 1)) / chain α s z (j + 1) ^ 2 := by
          simp only [chain]
          rw [le_div_iff₀ (by positivity)]
          have e : (a ^ (2 * j) / chain α s z j ^ 2 + θ / 5 * a ^ (2 * j)) *
              ((1 - α) * chain α s z j + α * Real.tanh (s * chain α s z j)) ^ 2 =
              a ^ (2 * j) / (a ^ 2 * chain α s z j ^ 2) *
              (((1 - α) * chain α s z j + α * Real.tanh (s * chain α s z j)) ^ 2 *
                (1 + θ * chain α s z j ^ 2 / 5)) * a ^ 2 := by
            field_simp
          rw [e]
          have e2 : a ^ (2 * (j + 1)) = a ^ (2 * j) / (a ^ 2 * chain α s z j ^ 2) *
              (a ^ 2 * chain α s z j ^ 2) * a ^ 2 := by
            field_simp
            ring
          rw [e2]
          gcongr
        rw [sum_range_succ]
        have e3 := mul_add (θ / 5) (∑ i ∈ range j, a ^ (2 * i)) (a ^ (2 * j))
        linarith
  have hFD := hpos D
  have hlamD : 0 < a ^ D := pow_pos ha0 D
  have hpow : a ^ (2 * D) = (a ^ D) ^ 2 := by rw [pow_mul, ← pow_mul, mul_comm, pow_mul]
  constructor
  · -- lower bound
    have h := hlow D
    rw [← hA] at h
    have hden : 0 < Real.sqrt (1 + A * z ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have hden2 : Real.sqrt (1 + A * z ^ 2) ^ 2 = 1 + A * z ^ 2 := Real.sq_sqrt (by positivity)
    have hsq : (a ^ D * z / Real.sqrt (1 + A * z ^ 2)) ^ 2 ≤ chain α s z D ^ 2 := by
      rw [div_pow, hden2, mul_pow, div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity), hpow] at h
      have e : (1 / z ^ 2 + A) * chain α s z D ^ 2 * z ^ 2 =
          chain α s z D ^ 2 * (1 + A * z ^ 2) := by
        field_simp
      nlinarith
    exact le_of_sq_le_sq hsq (hpos D).le
  · -- upper bound
    have h := hupp D
    have hA5 : θ / 5 * ∑ i ∈ range D, a ^ (2 * i) = A / 5 := by rw [hA]; ring
    rw [hA5] at h
    have hden : 0 < Real.sqrt (1 + A * z ^ 2 / 5) := Real.sqrt_pos.mpr (by positivity)
    have hden2 : Real.sqrt (1 + A * z ^ 2 / 5) ^ 2 = 1 + A * z ^ 2 / 5 :=
      Real.sq_sqrt (by positivity)
    have hsq : chain α s z D ^ 2 ≤ (a ^ D * z / Real.sqrt (1 + A * z ^ 2 / 5)) ^ 2 := by
      rw [div_pow, hden2, mul_pow, le_div_iff₀ (by positivity)]
      rw [le_div_iff₀ (by positivity), hpow] at h
      have e : (1 / z ^ 2 + A / 5) * chain α s z D ^ 2 * z ^ 2 =
          chain α s z D ^ 2 * (1 + A * z ^ 2 / 5) := by
        field_simp
      nlinarith
    have hrhs : 0 ≤ a ^ D * z / Real.sqrt (1 + A * z ^ 2 / 5) := by positivity
    exact le_of_sq_le_sq hsq hrhs

/-! ## Ideal radius recurrences -/

/-- Paper: `eq:resradiuslower` (tanh_residual.tex) at reference gain one:
the ideal radii `R_{j+1} = f_{α,1}(R_j)`, `R_0 = 1`, satisfy
`R_j ≥ (1 + α j)^{-1/2}`. This is `lem:resrange` at `s = z = 1`. -/
theorem ideal_radius_lower (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (j : ℕ) :
    1 / Real.sqrt (1 + α * j) ≤ chain α 1 1 j := by
  have h := (resrange α 1 1 j hα0 hα1 one_pos (by norm_num) zero_le_one le_rfl).1
  simpa [mul_comm] using h

/-- Paper: `eq:resradiuslower` (tanh_residual.tex), "monotonicity in `g`":
for `g ≥ 1` the ideal radii dominate those at gain one. -/
theorem chain_gain_mono (α g : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hg : 1 ≤ g) (j : ℕ) :
    chain α 1 1 j ≤ chain α g 1 j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
      simp only [chain]
      have h0 := (chain_mem_Icc α 1 1 hα0 hα1 zero_le_one zero_le_one le_rfl j).1
      have h1 : Real.tanh (1 * chain α 1 1 j) ≤ Real.tanh (g * chain α g 1 j) := by
        apply tanh_monotone
        nlinarith
      have h2 := mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ 1 - α)
      have h3 := mul_le_mul_of_nonneg_left h1 hα0
      linarith

/-- Paper: proof of `thm:residualupper` (tanh_residual.tex), "the ideal critical
recurrence obeys `R_j ≤ (1 + 2αj/5)^{-1/2}`", in squared form. -/
theorem ideal_radius_upper (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (j : ℕ) :
    chain α 1 1 j ^ 2 ≤ 1 / (1 + 2 * α * j / 5) := by
  have hpos : ∀ i, 0 < chain α 1 1 i := fun i =>
    lt_of_lt_of_le (by positivity) (ideal_radius_lower α hα0 hα1 i)
  have hmem := chain_mem_Icc α 1 1 hα0 hα1 zero_le_one zero_le_one le_rfl
  have key : ∀ i, 1 + 2 * α * i / 5 ≤ 1 / chain α 1 1 i ^ 2 := by
    intro i
    induction i with
    | zero => simp [chain]
    | succ i ih =>
        set r := chain α 1 1 i with hr
        have hr0 := hpos i
        have hr1 := (hmem i).2
        have ht := tanh_le_mul_one_sub_fifth hr0.le hr1
        have hf0 := (hmem (i + 1)).1
        have hfpos := hpos (i + 1)
        simp only [chain, one_mul] at hf0 hfpos ⊢
        rw [← hr] at hf0 hfpos ⊢
        -- `f(r) ≤ r (1 - α r^2/5)`
        have hf : (1 - α) * r + α * Real.tanh r ≤ r * (1 - α * r ^ 2 / 5) := by
          have := mul_le_mul_of_nonneg_left ht hα0
          nlinarith
        have hx0 : 0 ≤ α * r ^ 2 / 5 := by positivity
        have hx1 : α * r ^ 2 / 5 ≤ 1 / 5 := by
          have : r ^ 2 ≤ 1 := by nlinarith
          have : α * r ^ 2 ≤ 1 := by nlinarith
          linarith
        have hsq : ((1 - α) * r + α * Real.tanh r) ^ 2 * (1 + 2 * (α * r ^ 2 / 5)) ≤ r ^ 2 := by
          have e1 := pow_le_pow_left₀ hf0 hf 2
          have key2 : (1 - α * r ^ 2 / 5) ^ 2 * (1 + 2 * (α * r ^ 2 / 5)) ≤ 1 := by
            nlinarith [mul_nonneg hx0 hx0, mul_nonneg (mul_nonneg hx0 hx0) hx0]
          calc ((1 - α) * r + α * Real.tanh r) ^ 2 * (1 + 2 * (α * r ^ 2 / 5))
              ≤ (r * (1 - α * r ^ 2 / 5)) ^ 2 * (1 + 2 * (α * r ^ 2 / 5)) :=
                mul_le_mul_of_nonneg_right e1 (by positivity)
            _ = r ^ 2 * ((1 - α * r ^ 2 / 5) ^ 2 * (1 + 2 * (α * r ^ 2 / 5))) := by ring
            _ ≤ r ^ 2 * 1 := mul_le_mul_of_nonneg_left key2 (by positivity)
            _ = r ^ 2 := mul_one _
        rw [le_div_iff₀ (by positivity)]
        have e : (1 + 2 * α * ((i : ℝ) + 1) / 5) =
            (1 + 2 * α * i / 5) + 2 * α / 5 := by ring
        push_cast
        rw [e]
        have ih' : (1 + 2 * α * i / 5) * r ^ 2 ≤ 1 := by
          rwa [le_div_iff₀ (by positivity)] at ih
        set L := ((1 - α) * r + α * Real.tanh r) ^ 2 with hL
        set K := 1 + 2 * α * i / 5 + 2 * α / 5 with hK
        have hK0 : 0 ≤ K := by positivity
        have h1 : K * (L * (1 + 2 * (α * r ^ 2 / 5))) ≤ K * r ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hK0
        have h2 : K * r ^ 2 ≤ 1 + 2 * (α * r ^ 2 / 5) := by
          rw [hK]
          nlinarith
        have h3 : (K * L) * (1 + 2 * (α * r ^ 2 / 5)) ≤ 1 * (1 + 2 * (α * r ^ 2 / 5)) := by
          nlinarith
        exact le_of_mul_le_mul_right h3 (by positivity)
  have h := key j
  have hp := hpos j
  rw [le_div_iff₀ (by positivity)] at h
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- Auxiliary for `lem:residualsuperradius`: the one-step bound
`f_{α,1+δ}(r) ≤ r (1 + αδ - α r^2/5)` on `[0, 1]`, from the unit Lipschitz bound
and the critical radius inequality. -/
theorem super_step (α δ r : ℝ) (hα0 : 0 ≤ α) (hδ : 0 ≤ δ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (1 - α) * r + α * Real.tanh ((1 + δ) * r) ≤ r * (1 + α * δ - α * r ^ 2 / 5) := by
  have h1 := tanh_sub_le r ((1 + δ) * r) (by nlinarith)
  have h2 := tanh_le_mul_one_sub_fifth hr0 hr1
  have h3 : Real.tanh ((1 + δ) * r) ≤ r * (1 - r ^ 2 / 5) + δ * r := by linarith
  have := mul_le_mul_of_nonneg_left h3 hα0
  nlinarith

/-- Paper: `lem:residualsuperradius` (tanh_residual_fused.tex). For
`s = 1 + δ`, `δ ≥ 0` (the paper assumes `δ ≤ 1`, which is not needed), the ideal
radii `R_0 = 1`, `R_{j+1} = f_{α,s}(R_j)`
satisfy `R_j^2 ≤ 10 δ + (1 + α j/5)^{-1}`. -/
theorem super_radius (α δ : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hδ0 : 0 ≤ δ) (j : ℕ) :
    chain α (1 + δ) 1 j ^ 2 ≤ 10 * δ + 1 / (1 + α * j / 5) := by
  have hmem := chain_mem_Icc α (1 + δ) 1 hα0 hα1 (by linarith) zero_le_one le_rfl
  set w : ℕ → ℝ := fun i => max (chain α (1 + δ) 1 i ^ 2 - 10 * δ) 0 with hw
  -- monotonicity of the one-step map
  have hmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y →
      (1 - α) * x + α * Real.tanh ((1 + δ) * x) ≤
        (1 - α) * y + α * Real.tanh ((1 + δ) * y) := by
    intro x y hx hxy
    have h1 := tanh_monotone (mul_le_mul_of_nonneg_left hxy (by linarith : (0 : ℝ) ≤ 1 + δ))
    have h2 := mul_le_mul_of_nonneg_left hxy (by linarith : (0 : ℝ) ≤ 1 - α)
    have h3 := mul_le_mul_of_nonneg_left h1 hα0
    linarith
  -- the one-step recurrence for `w`
  have hstep : ∀ i, w (i + 1) ≤ w i / (1 + α * w i / 5) := by
    intro i
    set r := chain α (1 + δ) 1 i with hr
    have hr0 := (hmem i).1
    have hr1 := (hmem i).2
    have hnext : chain α (1 + δ) 1 (i + 1) = (1 - α) * r + α * Real.tanh ((1 + δ) * r) := rfl
    have hn0 := (hmem (i + 1)).1
    rcases le_or_gt (r ^ 2) (10 * δ) with hsmall | hbig
    · -- `w i = 0` and `w (i+1) = 0`
      have hwi : w i = 0 := by simp only [hw]; rw [← hr]; exact max_eq_right (by linarith)
      have hwi1 : w (i + 1) = 0 := by
        simp only [hw]
        apply max_eq_right
        rcases le_or_gt 1 (10 * δ) with hδ10 | hδ10
        · have := (hmem (i + 1)).2
          nlinarith
        · set ρ := Real.sqrt (10 * δ) with hρ
          have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
          have hρ2 : ρ ^ 2 = 10 * δ := Real.sq_sqrt (by linarith)
          have hρ1 : ρ ≤ 1 := by nlinarith
          have hrρ : r ≤ ρ := by nlinarith
          have e1 := hmono r ρ hr0 hrρ
          have e2 := super_step α δ ρ hα0 hδ0 hρ0 hρ1
          have e3 : ρ * (1 + α * δ - α * ρ ^ 2 / 5) ≤ ρ := by
            rw [hρ2]
            nlinarith [mul_nonneg (mul_nonneg hρ0 hα0) hδ0]
          rw [hnext]
          have e4 : (1 - α) * r + α * Real.tanh ((1 + δ) * r) ≤ ρ := by linarith
          have := pow_le_pow_left₀ (by rw [← hnext]; exact hn0) e4 2
          linarith
      rw [hwi, hwi1]
      simp
    · -- the reciprocal-square recurrence
      set v := r ^ 2 with hv
      have hwi : w i = v - 10 * δ := by
        simp only [hw]; rw [← hr]; exact max_eq_left (by linarith)
      have hv1 : v ≤ 1 := by nlinarith
      have hstep1 := super_step α δ r hα0 hδ0 hr0 hr1
      have hf : (1 - α) * r + α * Real.tanh ((1 + δ) * r) ≤ r * (1 - α * v / 10) := by
        have : α * δ ≤ α * v / 10 := by nlinarith
        nlinarith
      have hx0 : 0 ≤ α * v / 10 := by positivity
      have hx1 : α * v / 10 ≤ 1 / 10 := by nlinarith
      have hsq : chain α (1 + δ) 1 (i + 1) ^ 2 ≤ v / (1 + α * v / 5) := by
        rw [le_div_iff₀ (by positivity), hnext]
        have e1 := pow_le_pow_left₀ (by rw [← hnext]; exact hn0) hf 2
        have key2 : (1 - α * v / 10) ^ 2 * (1 + 2 * (α * v / 10)) ≤ 1 := by
          nlinarith [mul_nonneg hx0 hx0, mul_nonneg (mul_nonneg hx0 hx0) hx0]
        calc ((1 - α) * r + α * Real.tanh ((1 + δ) * r)) ^ 2 * (1 + α * v / 5)
            ≤ (r * (1 - α * v / 10)) ^ 2 * (1 + α * v / 5) :=
              mul_le_mul_of_nonneg_right e1 (by positivity)
          _ = v * ((1 - α * v / 10) ^ 2 * (1 + 2 * (α * v / 10))) := by rw [hv]; ring
          _ ≤ v * 1 := mul_le_mul_of_nonneg_left key2 (by positivity)
          _ = v := mul_one v
      -- `v/(1 + c v) - 10δ ≤ (v - 10δ)/(1 + c (v - 10δ))`
      have hlip : v / (1 + α * v / 5) - 10 * δ ≤
          (v - 10 * δ) / (1 + α * (v - 10 * δ) / 5) := by
        have hu : 0 ≤ v - 10 * δ := by linarith
        have d1 : 0 < 1 + α * v / 5 := by positivity
        have d2 : 0 < 1 + α * (v - 10 * δ) / 5 := by positivity
        rw [div_sub' d1.ne', div_le_div_iff₀ d1 d2]
        nlinarith [mul_nonneg (mul_nonneg hα0 hδ0) hu, mul_nonneg hα0 hδ0,
          mul_nonneg (mul_nonneg (mul_nonneg hα0 hδ0) hu) (mul_nonneg hα0 (by linarith : 0 ≤ v))]
      rw [hwi]
      simp only [hw]
      apply max_le _ (by positivity)
      linarith
  -- induction for `w`
  have hwbound : ∀ i, w i ≤ 1 / (1 + α * i / 5) := by
    intro i
    induction i with
    | zero =>
        simp only [hw, chain]
        norm_num
        exact hδ0
    | succ i ih =>
        have hw0 : 0 ≤ w i := le_max_right _ _
        refine (hstep i).trans ?_
        have d0 : 0 < 1 + α * i / 5 := by positivity
        have d1 : 0 < 1 + α * w i / 5 := by positivity
        rw [div_le_div_iff₀ d1 (by positivity)]
        rw [le_div_iff₀ d0] at ih
        push_cast
        nlinarith [mul_nonneg hα0 hw0]
  have := hwbound j
  have hmax : chain α (1 + δ) 1 j ^ 2 - 10 * δ ≤ w j := le_max_left _ _
  linarith

/-! ## The critical sums `eq:resintegrals` -/

/-- Auxiliary for `eq:resintegrals`: the telescoping estimate
`∑_{j=K}^{K+n} (1 + cj)^{-2} ≤ (1 + cK)^{-2} + (1/c)((1 + cK)^{-1} - (1 + c(K+n))^{-1})`,
the discrete form of the integral bound. -/
theorem sum_inv_sq_telescope (c : ℝ) (hc : 0 < c) (K n : ℕ) :
    ∑ j ∈ Ico K (K + n + 1), (1 / (1 + c * j)) ^ 2 ≤
      (1 / (1 + c * K)) ^ 2 + 1 / c * (1 / (1 + c * K) - 1 / (1 + c * (K + n : ℕ))) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show K + (n + 1) + 1 = K + n + 1 + 1 by ring, sum_Ico_succ_top (by omega)]
      have hm0 : (0 : ℝ) ≤ (K + n : ℕ) := Nat.cast_nonneg _
      have d1 : 0 < 1 + c * ((K + n : ℕ) : ℝ) := by positivity
      have d2 : 0 < 1 + c * ((K + n + 1 : ℕ) : ℝ) := by positivity
      have step : (1 / (1 + c * ((K + n + 1 : ℕ) : ℝ))) ^ 2 ≤
          1 / c * (1 / (1 + c * ((K + n : ℕ) : ℝ)) - 1 / (1 + c * ((K + n + 1 : ℕ) : ℝ))) := by
        push_cast at d1 d2 ⊢
        rw [div_pow, one_pow, div_sub_div _ _ d1.ne' d2.ne', one_div_mul_eq_div,
          div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos hc d1, mul_pos (mul_pos hc d1) d2]
      have e : K + (n + 1) = K + n + 1 := by ring
      rw [e]
      push_cast at ih step ⊢
      linarith

/-- Auxiliary for `eq:resintegrals`: the per-step inequality behind the
fifth-power sum. If `a^2 - b^2 = c a^2 b^2` and `0 < b ≤ a`, then
`3 c b^5 ≤ 2 (a^3 - b^3)`. -/
theorem fifth_power_step (a b c : ℝ) (hb : 0 < b) (hab : b ≤ a)
    (hc : a ^ 2 - b ^ 2 = c * a ^ 2 * b ^ 2) : 3 * c * b ^ 5 ≤ 2 * (a ^ 3 - b ^ 3) := by
  have ha : 0 < a := lt_of_lt_of_le hb hab
  have hpoly : 3 * (a ^ 2 - b ^ 2) * b ^ 3 ≤ 2 * a ^ 2 * (a ^ 3 - b ^ 3) := by
    have h1 : 0 ≤ a - b := by linarith
    have h2 : 0 ≤ 2 * a ^ 4 + 2 * a ^ 3 * b + 2 * a ^ 2 * b ^ 2 - 3 * a * b ^ 3 - 3 * b ^ 4 := by
      nlinarith [mul_nonneg (mul_nonneg hb.le hb.le) (mul_nonneg hb.le h1),
        mul_nonneg (mul_nonneg ha.le ha.le) (mul_nonneg ha.le h1),
        mul_nonneg (mul_nonneg ha.le hb.le) (mul_nonneg hb.le h1),
        mul_nonneg (mul_nonneg ha.le ha.le) (mul_nonneg hb.le h1)]
    nlinarith [mul_nonneg h1 h2]
  have e : a ^ 2 * (3 * c * b ^ 5) = 3 * (a ^ 2 - b ^ 2) * b ^ 3 := by rw [hc]; ring
  have : a ^ 2 * (3 * c * b ^ 5) ≤ a ^ 2 * (2 * (a ^ 3 - b ^ 3)) := by
    rw [e]
    linarith
  exact le_of_mul_le_mul_left this (by positivity)

/-- Paper: `eq:resintegrals` (proof of `thm:residualupper`, tanh_residual.tex).
If the ideal radii satisfy `R_j^2 ≤ (1 + 2αj/5)^{-1}` and the stored radii obey
`R_j ≤ r_j ≤ 1` and `r_j - R_j ≤ 3 j α ε` with `ε ≤ [100(D+1)^4]^{-1}`, then
`α ∑_{j<D} r_j^4 ≤ 4` and `α ∑_{j=1}^D r_j^5 ≤ 3`. -/
theorem resintegrals (α ε : ℝ) (D : ℕ) (R r : ℕ → ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / (100 * ((D : ℝ) + 1) ^ 4)) (hR0 : ∀ j, 0 ≤ R j)
    (hRr : ∀ j, R j ≤ r j) (hr1 : ∀ j, r j ≤ 1)
    (hRsq : ∀ j : ℕ, R j ^ 2 ≤ 1 / (1 + 2 * α * j / 5))
    (hround : ∀ j : ℕ, r j - R j ≤ 3 * j * α * ε) :
    α * ∑ j ∈ range D, r j ^ 4 ≤ 4 ∧ α * ∑ j ∈ Icc 1 D, r j ^ 5 ≤ 3 := by
  set c := 2 * α / 5 with hc
  have hc0 : 0 < c := by positivity
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  -- the rounding budget
  have hεD : ε * (D : ℝ) ^ 2 ≤ 1 / 100 := by
    have h1 : (D : ℝ) ^ 2 ≤ ((D : ℝ) + 1) ^ 4 := by nlinarith
    have h2 : ε * (D : ℝ) ^ 2 ≤ 1 / (100 * ((D : ℝ) + 1) ^ 4) * ((D : ℝ) + 1) ^ 4 :=
      mul_le_mul hε h1 (by positivity) (by positivity)
    have h3 : 1 / (100 * ((D : ℝ) + 1) ^ 4) * ((D : ℝ) + 1) ^ 4 = 1 / 100 := by
      field_simp
    linarith
  have hroundj : ∀ j ∈ range D, r j - R j ≤ 3 * D * α * ε := by
    intro j hj
    have hj : (j : ℝ) ≤ D := by exact_mod_cast (mem_range.mp hj).le
    have := hround j
    nlinarith [mul_nonneg hα0.le hε0]
  have hroundj' : ∀ j ∈ Icc 1 D, r j - R j ≤ 3 * D * α * ε := by
    intro j hj
    have hj : (j : ℝ) ≤ D := by exact_mod_cast (mem_Icc.mp hj).2
    have := hround j
    nlinarith [mul_nonneg hα0.le hε0]
  have hxsq : ∀ j : ℕ, 1 / (1 + 2 * α * j / 5) = 1 / (1 + c * j) := by
    intro j
    rw [hc]
    ring
  constructor
  · -- fourth powers
    have hR4 : ∀ j : ℕ, R j ^ 4 ≤ (1 / (1 + c * j)) ^ 2 := by
      intro j
      have h := hRsq j
      rw [hxsq] at h
      have : R j ^ 4 = (R j ^ 2) ^ 2 := by ring
      rw [this]
      exact pow_le_pow_left₀ (by positivity) h 2
    have hr4 : ∀ j ∈ range D, r j ^ 4 ≤ (1 / (1 + c * j)) ^ 2 + 12 * D * α * ε := by
      intro j hj
      have h0 := hR0 j
      have h1 := hRr j
      have h2 := hr1 j
      have h3 := hroundj j hj
      have hdiff : r j ^ 4 - R j ^ 4 ≤ 4 * (r j - R j) := by
        have e : r j ^ 4 - R j ^ 4 = (r j - R j) *
            (r j ^ 3 + r j ^ 2 * R j + r j * R j ^ 2 + R j ^ 3) := by ring
        rw [e]
        have hs : r j ^ 3 + r j ^ 2 * R j + r j * R j ^ 2 + R j ^ 3 ≤ 4 := by
          have hr0 : 0 ≤ r j := le_trans h0 h1
          have a1 : r j ^ 3 ≤ 1 := pow_le_one₀ hr0 h2
          have a2 : r j ^ 2 * R j ≤ 1 := by
            have := pow_le_one₀ hr0 h2 (n := 2)
            nlinarith
          have a3 : r j * R j ^ 2 ≤ 1 := by
            have := pow_le_one₀ h0 (le_trans h1 h2) (n := 2)
            nlinarith
          have a4 : R j ^ 3 ≤ 1 := pow_le_one₀ h0 (le_trans h1 h2)
          linarith
        have := mul_le_mul_of_nonneg_left hs (by linarith : (0 : ℝ) ≤ r j - R j)
        linarith
      have := hR4 j
      linarith
    have hideal : ∑ j ∈ range D, (1 / (1 + c * j)) ^ 2 ≤ 1 + 1 / c := by
      rcases Nat.eq_zero_or_pos D with h0 | hpos
      · subst h0
        simp
        positivity
      · have h := sum_inv_sq_telescope c hc0 0 (D - 1)
        rw [show 0 + (D - 1) + 1 = D by omega, ← range_eq_Ico] at h
        refine h.trans ?_
        simp only [Nat.cast_zero, mul_zero, add_zero, div_one, one_pow]
        have : 0 ≤ 1 / (1 + c * ((0 + (D - 1) : ℕ) : ℝ)) := by positivity
        have : 1 / c * (1 - 1 / (1 + c * ((0 + (D - 1) : ℕ) : ℝ))) ≤ 1 / c * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith
    have hsum : ∑ j ∈ range D, r j ^ 4 ≤ 1 + 1 / c + D * (12 * D * α * ε) := by
      have := sum_le_sum hr4
      rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at this
      linarith
    have hfin : α * (1 + 1 / c) = α + 5 / 2 := by rw [hc]; field_simp
    have hround2 : α * (D * (12 * D * α * ε)) ≤ 12 / 100 := by
      have : α * (D * (12 * D * α * ε)) = 12 * α ^ 2 * (ε * (D : ℝ) ^ 2) := by ring
      rw [this]
      have hα2 : α ^ 2 ≤ 1 := by nlinarith
      have hεD0 : 0 ≤ ε * (D : ℝ) ^ 2 := by positivity
      nlinarith
    have := mul_le_mul_of_nonneg_left hsum hα0.le
    nlinarith
  · -- fifth powers
    set x : ℕ → ℝ := fun j => 1 / Real.sqrt (1 + c * j) with hx
    have hxpos : ∀ j, 0 < x j := fun j => by
      simp only [hx]
      have : 0 < Real.sqrt (1 + c * j) := Real.sqrt_pos.mpr (by positivity)
      positivity
    have hx2 : ∀ j : ℕ, x j ^ 2 = 1 / (1 + c * j) := by
      intro j
      simp only [hx]
      rw [div_pow, Real.sq_sqrt (by positivity), one_pow]
    have hRx : ∀ j : ℕ, R j ≤ x j := by
      intro j
      apply le_of_sq_le_sq _ (hxpos j).le
      rw [hx2, ← hxsq]
      exact hRsq j
    have hstep : ∀ j : ℕ, 3 * c * x (j + 1) ^ 5 ≤ 2 * (x j ^ 3 - x (j + 1) ^ 3) := by
      intro j
      apply fifth_power_step _ _ _ (hxpos _)
      · apply le_of_sq_le_sq _ (hxpos _).le
        rw [hx2, hx2]
        apply one_div_le_one_div_of_le (by positivity)
        push_cast
        nlinarith
      · rw [hx2, hx2]
        push_cast
        have d1 : 0 < 1 + c * j := by positivity
        have d2 : 0 < 1 + c * (j + 1) := by positivity
        field_simp
        ring
    have htel : ∀ n : ℕ, 3 * c * ∑ j ∈ Icc 1 n, x j ^ 5 ≤ 2 * (x 0 ^ 3 - x n ^ 3) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [sum_Icc_succ_top (by omega), mul_add]
          have := hstep n
          linarith
    have hx0 : x 0 = 1 := by simp [hx]
    have hideal : α * ∑ j ∈ Icc 1 D, x j ^ 5 ≤ 5 / 3 := by
      have h := htel D
      rw [hx0] at h
      have hxD : 0 ≤ x D ^ 3 := by have := hxpos D; positivity
      have h2 : 3 * c * ∑ j ∈ Icc 1 D, x j ^ 5 ≤ 2 := by nlinarith
      have e : α * ∑ j ∈ Icc 1 D, x j ^ 5 = 5 / 6 * (3 * c * ∑ j ∈ Icc 1 D, x j ^ 5) := by
        rw [hc]; ring
      rw [e]
      linarith
    have hr5 : ∀ j ∈ Icc 1 D, r j ^ 5 ≤ x j ^ 5 + 15 * D * α * ε := by
      intro j hj
      have h0 := hR0 j
      have h1 := hRr j
      have h2 := hr1 j
      have h3 := hroundj' j hj
      have hr0 : 0 ≤ r j := le_trans h0 h1
      have hdiff : r j ^ 5 - R j ^ 5 ≤ 5 * (r j - R j) := by
        have e : r j ^ 5 - R j ^ 5 = (r j - R j) * (r j ^ 4 + r j ^ 3 * R j +
            r j ^ 2 * R j ^ 2 + r j * R j ^ 3 + R j ^ 4) := by ring
        rw [e]
        have hR1 : R j ≤ 1 := le_trans h1 h2
        have hs : r j ^ 4 + r j ^ 3 * R j + r j ^ 2 * R j ^ 2 + r j * R j ^ 3 + R j ^ 4 ≤ 5 := by
          have b1 := pow_le_one₀ hr0 h2 (n := 4)
          have b2 := pow_le_one₀ hr0 h2 (n := 3)
          have b3 := pow_le_one₀ hr0 h2 (n := 2)
          have c2 := pow_le_one₀ h0 hR1 (n := 2)
          have c3 := pow_le_one₀ h0 hR1 (n := 3)
          have c4 := pow_le_one₀ h0 hR1 (n := 4)
          have e1 : r j ^ 3 * R j ≤ 1 := by nlinarith
          have e2 : r j ^ 2 * R j ^ 2 ≤ 1 := by nlinarith
          have e3 : r j * R j ^ 3 ≤ 1 := by nlinarith
          linarith
        have := mul_le_mul_of_nonneg_left hs (by linarith : (0 : ℝ) ≤ r j - R j)
        linarith
      have h5 : R j ^ 5 ≤ x j ^ 5 := pow_le_pow_left₀ h0 (hRx j) 5
      linarith
    have hsum : ∑ j ∈ Icc 1 D, r j ^ 5 ≤ ∑ j ∈ Icc 1 D, x j ^ 5 + D * (15 * D * α * ε) := by
      have := sum_le_sum hr5
      rw [sum_add_distrib, sum_const, Nat.card_Icc, nsmul_eq_mul] at this
      simpa using this
    have hround2 : α * (D * (15 * D * α * ε)) ≤ 15 / 100 := by
      have : α * (D * (15 * D * α * ε)) = 15 * α ^ 2 * (ε * (D : ℝ) ^ 2) := by ring
      rw [this]
      have hα2 : α ^ 2 ≤ 1 := by nlinarith
      have hεD0 : 0 ≤ ε * (D : ℝ) ^ 2 := by positivity
      nlinarith
    have := mul_le_mul_of_nonneg_left hsum hα0.le
    nlinarith

/-- Paper: `eq:rescutoffbounds` (proof of `thm:residualfused`,
tanh_residual_fused.tex): above a cutoff `K` with `α K ≥ J > 0`, the ideal
fourth-power suffix sum is at most `25/(4J^2) + 25/(4J)`. -/
theorem cutoff_ideal_sum (α J : ℝ) (K n : ℕ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hJ : 0 < J)
    (hK : J ≤ α * K) :
    α * ∑ j ∈ Ico K (K + n + 1), (1 / (1 + 2 * α / 5 * j)) ^ 2 ≤
      25 / (4 * J ^ 2) + 25 / (4 * J) := by
  set c := 2 * α / 5 with hc
  have hc0 : 0 < c := by positivity
  have h := sum_inv_sq_telescope c hc0 K n
  have hK0 : (0 : ℝ) < K := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · subst h0
      simp at hK
      linarith
    · exact_mod_cast h0
  have hcK : 2 * J / 5 ≤ c * K := by rw [hc]; nlinarith
  have hd : 0 < 1 + c * K := by positivity
  have t1 : α * (1 / (1 + c * K)) ^ 2 ≤ 25 / (4 * J ^ 2) := by
    rw [div_pow, one_pow, ← div_eq_mul_one_div, div_le_div_iff₀ (by positivity)
      (by positivity)]
    have : (2 * J / 5) ^ 2 ≤ (1 + c * K) ^ 2 := pow_le_pow_left₀ (by positivity)
      (by linarith) 2
    nlinarith
  have t2 : α * (1 / c * (1 / (1 + c * K) - 1 / (1 + c * (K + n : ℕ)))) ≤ 25 / (4 * J) := by
    have e1 : 0 ≤ 1 / (1 + c * (K + n : ℕ)) := by positivity
    have e2 : α * (1 / c) = 5 / 2 := by rw [hc]; field_simp
    have e3 : 1 / (1 + c * K) ≤ 5 / (2 * J) := by
      rw [div_le_div_iff₀ hd (by positivity)]
      nlinarith
    have : α * (1 / c * (1 / (1 + c * K) - 1 / (1 + c * (K + n : ℕ)))) ≤ 5 / 2 * (5 / (2 * J)) := by
      rw [← mul_assoc, e2]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      linarith
    calc _ ≤ 5 / 2 * (5 / (2 * J)) := this
      _ = 25 / (4 * J) := by field_simp; ring
  have := mul_le_mul_of_nonneg_left h hα0.le
  rw [mul_add] at this
  linarith

/-! ## The logarithmic step and the supercritical fourth-power sum -/

/-- Paper: `eq:reslogproduct` (proof of `thm:residualupper`, tanh_residual.tex).
Let `F = r (1 - αd)` and `r' = F + e` with `0 ≤ e ≤ 3αε`. If
`G = 1 - α + α χ` and `χ ≤ 1 + 4d + 5r^4 + 6000(g-1)` (Lemma `lem:resradial`),
then `log G ≤ 4 log(r/r') + 5αr^4 + 6000α(g-1) + 12αε/F`. -/
theorem reslogproduct_step (α r d e χ ε g : ℝ) (hα0 : 0 ≤ α) (hr : 0 < r)
    (hαd : α * d < 1) (he0 : 0 ≤ e) (he : e ≤ 3 * α * ε)
    (hχ : χ ≤ 1 + 4 * d + 5 * r ^ 4 + 6000 * (g - 1)) (hG : 0 < 1 - α + α * χ) :
    Real.log (1 - α + α * χ) ≤ 4 * Real.log (r / (r * (1 - α * d) + e)) +
      5 * α * r ^ 4 + 6000 * α * (g - 1) + 12 * α * ε / (r * (1 - α * d)) := by
  set F := r * (1 - α * d) with hF
  have hF0 : 0 < F := mul_pos hr (by linarith)
  have hFe : 0 < F + e := by linarith
  -- `log G ≤ G - 1`
  have h1 : Real.log (1 - α + α * χ) ≤ α * (4 * d + 5 * r ^ 4 + 6000 * (g - 1)) := by
    have := Real.log_le_sub_one_of_pos hG
    have h2 : α * χ ≤ α * (1 + 4 * d + 5 * r ^ 4 + 6000 * (g - 1)) :=
      mul_le_mul_of_nonneg_left hχ hα0
    linarith
  -- `αd ≤ log(r/F)`
  have h2 : α * d ≤ Real.log (r / F) := by
    have := Real.one_sub_inv_le_log_of_pos (div_pos hr hF0)
    rw [inv_div, hF] at this
    have e : r * (1 - α * d) / r = 1 - α * d := by field_simp
    rw [e] at this
    linarith
  -- `log(r/F) ≤ log(r/(F+e)) + e/F`
  have h3 : Real.log (r / F) ≤ Real.log (r / (F + e)) + e / F := by
    have e1 : r / F = r / (F + e) * ((F + e) / F) := by field_simp
    rw [e1, Real.log_mul (div_pos hr hFe).ne' (div_pos hFe hF0).ne']
    have := Real.log_le_sub_one_of_pos (div_pos hFe hF0)
    have e2 : (F + e) / F - 1 = e / F := by field_simp; ring
    linarith
  have h4 : e / F ≤ 3 * α * ε / F := div_le_div_of_nonneg_right he hF0.le
  have h5 : 12 * α * ε / F = 4 * (3 * α * ε / F) := by ring
  nlinarith

/-- Paper: proof of `thm:residualupper` (tanh_residual.tex), supercritical case:
from `d_j ≥ r_j^2/5 - δ`, `α r_j^2 d_j ≤ r_j^2 - F_j^2 ≤ r_j^2 - r_{j+1}^2 + 2 e_{j+1}`,
one gets `α ∑_{j=k}^{D-1} r_j^4 ≤ 5 + 5δα(D-k) + 30α(D-k)ε`. -/
theorem super_fourth_sum (α δ ε : ℝ) (k D : ℕ) (hkD : k ≤ D) (r d e : ℕ → ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hδ : 0 ≤ δ) (hr0 : ∀ j, 0 ≤ r j) (hr1 : ∀ j, r j ≤ 1)
    (hd0 : ∀ j, 0 ≤ d j) (hd1 : ∀ j, d j ≤ 1) (hdlow : ∀ j, r j ^ 2 / 5 - δ ≤ d j)
    (hnext : ∀ j, r (j + 1) = r j * (1 - α * d j) + e (j + 1))
    (he0 : ∀ j, 0 ≤ e j) (he : ∀ j, e j ≤ 3 * α * ε) :
    α * ∑ j ∈ Ico k D, r j ^ 4 ≤ 5 + 5 * δ * α * (D - k) + 30 * α * (D - k) * ε := by
  have hstep : ∀ j, α * r j ^ 4 / 5 ≤ r j ^ 2 - r (j + 1) ^ 2 + 6 * α * ε + α * δ := by
    intro j
    set F := r j * (1 - α * d j) with hF
    have hαd : α * d j ≤ 1 := by nlinarith [hd1 j]
    have hαd0 : 0 ≤ α * d j := mul_nonneg hα0 (hd0 j)
    have hF0 : 0 ≤ F := mul_nonneg (hr0 j) (by linarith)
    have hdec : α * r j ^ 2 * d j ≤ r j ^ 2 - F ^ 2 := by
      rw [hF]
      have : 0 ≤ r j ^ 2 * (α * d j) * (1 - α * d j) := by
        apply mul_nonneg (mul_nonneg (sq_nonneg _) hαd0) (by linarith)
      nlinarith
    have hsq : r (j + 1) ^ 2 ≤ F ^ 2 + 2 * e (j + 1) := by
      rw [hnext j]
      have h1 := hr1 (j + 1)
      rw [hnext j] at h1
      have := he0 (j + 1)
      nlinarith
    have hlow : α * r j ^ 4 / 5 - α * δ * r j ^ 2 ≤ α * r j ^ 2 * d j := by
      have := mul_le_mul_of_nonneg_left (hdlow j) (mul_nonneg hα0 (sq_nonneg (r j)))
      nlinarith
    have hr2 : r j ^ 2 ≤ 1 := by nlinarith [hr0 j, hr1 j]
    have hαδ : α * δ * r j ^ 2 ≤ α * δ := by nlinarith [mul_nonneg hα0 hδ]
    have := he (j + 1)
    linarith
  have hsum : ∀ n, α * ∑ j ∈ Ico k (k + n), r j ^ 4 / 5 ≤
      r k ^ 2 - r (k + n) ^ 2 + n * (6 * α * ε + α * δ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [← add_assoc, sum_Ico_succ_top (by omega), mul_add]
        have := hstep (k + n)
        have e : α * (r (k + n) ^ 4 / 5) = α * r (k + n) ^ 4 / 5 := by ring
        push_cast
        linarith
  have h := hsum (D - k)
  rw [Nat.add_sub_cancel' hkD] at h
  have hDk : ((D - k : ℕ) : ℝ) = (D : ℝ) - k := by push_cast [Nat.cast_sub hkD]; ring
  rw [hDk] at h
  have hk2 : 0 ≤ r D ^ 2 := sq_nonneg _
  have hk1 : r k ^ 2 ≤ 1 := by nlinarith [hr0 k, hr1 k]
  have e : α * ∑ j ∈ Ico k D, r j ^ 4 / 5 = (α * ∑ j ∈ Ico k D, r j ^ 4) / 5 := by
    rw [← sum_div, mul_div_assoc]
  rw [e] at h
  nlinarith

/-! ## The critical radial comparison `lem:resradial` -/

/-- Auxiliary: a polynomial upper bound for `exp` on `[0, 1]` from the Taylor
remainder, `exp x ≤ ∑_{m<6} x^m/m! + 7 x^6/4320`. -/
theorem exp_le_poly6 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 +
      7 * x ^ 6 / 4320 := by
  have h := Real.exp_bound (x := x) (by rw [abs_of_nonneg hx0]; exact hx1) (n := 6)
    (by norm_num)
  rw [abs_of_nonneg hx0] at h
  have hs : ∑ m ∈ range 6, x ^ m / (m.factorial : ℝ) =
      1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 := by
    simp [sum_range_succ, Nat.factorial]
  rw [hs] at h
  have := (abs_le.mp h).2
  norm_num at this
  linarith

/-- Paper: proof of `lem:resradial` (tanh_residual.tex): on `0 ≤ t ≤ 2/5`,
`E(t) = exp(5t/3 + t^2) ≤ 1 + 5t/3 + 4t^2`. -/
theorem exp_quadratic_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 2 / 5) :
    Real.exp (5 / 3 * t + t ^ 2) ≤ 1 + 5 / 3 * t + 4 * t ^ 2 := by
  set x := 5 / 3 * t + t ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 62 / 75 := by nlinarith
  have hxt : x ≤ 31 / 15 * t := by nlinarith
  have h := exp_le_poly6 hx0 (by linarith)
  have h2 : x ^ 2 ≤ (31 / 15) ^ 2 * t ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hx0 hxt 2
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have h3 : x ^ 3 ≤ 62 / 75 * x ^ 2 := by
    rw [pow_succ]
    nlinarith
  have h4 : x ^ 4 ≤ (62 / 75) ^ 2 * x ^ 2 := by
    have : x ^ 4 = x ^ 2 * x * x := by ring
    rw [this]
    have e1 : x ^ 2 * x ≤ x ^ 2 * (62 / 75) := mul_le_mul_of_nonneg_left hx1 hx2
    have e2 : x ^ 2 * x * x ≤ x ^ 2 * (62 / 75) * (62 / 75) :=
      mul_le_mul e1 hx1 hx0 (by positivity)
    nlinarith
  have h5 : x ^ 5 ≤ (62 / 75) ^ 3 * x ^ 2 := by
    have : x ^ 5 = x ^ 4 * x := by ring
    rw [this]
    have := mul_le_mul h4 hx1 hx0 (by positivity)
    nlinarith
  have h6 : x ^ 6 ≤ (62 / 75) ^ 4 * x ^ 2 := by
    have : x ^ 6 = x ^ 5 * x := by ring
    rw [this]
    have := mul_le_mul h5 hx1 hx0 (by positivity)
    nlinarith
  nlinarith

/-- Paper: proof of `lem:resradial` (tanh_residual.tex), "positivity of the
series for `(1+t)e^t`": `(1+t) e^t ≤ 1 + 2t + (5/2)t^2` on `[0, 1]`. -/
theorem one_add_mul_exp_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 + t) * Real.exp t ≤ 1 + 2 * t + 5 / 2 * t ^ 2 := by
  have h := exp_le_poly6 ht0 ht1
  have hm := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 1 + t)
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  have p3 : t ^ 3 ≤ t ^ 2 := by rw [pow_succ]; nlinarith
  have p4 : t ^ 4 ≤ t ^ 2 := by
    have : t ^ 4 = t ^ 2 * t ^ 2 := by ring
    rw [this]; nlinarith
  have p5 : t ^ 5 ≤ t ^ 2 := by
    have : t ^ 5 = t ^ 2 * t ^ 3 := by ring
    rw [this]
    have : t ^ 3 ≤ 1 := pow_le_one₀ ht0 ht1
    nlinarith
  have p6 : t ^ 6 ≤ t ^ 2 := by
    have : t ^ 6 = t ^ 2 * t ^ 4 := by ring
    rw [this]
    have : t ^ 4 ≤ 1 := pow_le_one₀ ht0 ht1
    nlinarith
  have p7 : t ^ 7 ≤ t ^ 2 := by
    have : t ^ 7 = t ^ 2 * t ^ 5 := by ring
    rw [this]
    have : t ^ 5 ≤ 1 := pow_le_one₀ ht0 ht1
    nlinarith
  have p3' : t ^ 3 ≤ t ^ 2 := p3
  nlinarith

/-- Paper: proof of `lem:resradial` (tanh_residual.tex): `d_1(r) ≥ r^2/3 - r^4/5`,
in the form `tanh r ≤ r (1 - r^2/3 + r^4/5)` on `[0, 1]`. -/
theorem tanh_le_quintic {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.tanh r ≤ r * (1 - r ^ 2 / 3 + r ^ 4 / 5) := by
  have h := sq_tanh_le_sq_div r
  have ht := tanh_nonneg hr0
  have hw0 : 0 ≤ r ^ 2 := sq_nonneg r
  have hw1 : r ^ 2 ≤ 1 := by nlinarith
  have hq : 0 ≤ 1 - r ^ 2 / 3 + r ^ 4 / 5 := by nlinarith
  have hpos : 0 ≤ r * (1 - r ^ 2 / 3 + r ^ 4 / 5) := mul_nonneg hr0 hq
  apply le_of_sq_le_sq _ hpos
  refine h.trans ?_
  rw [div_le_iff₀ (by positivity)]
  set w := r ^ 2 with hw
  have hr4 : r ^ 4 = w ^ 2 := by rw [hw]; ring
  have key : 1 ≤ (1 - w / 3 + w ^ 2 / 5) ^ 2 * (1 + 2 * w / 3) := by
    nlinarith [mul_nonneg hw0 hw0, mul_nonneg (mul_nonneg hw0 hw0) hw0,
      mul_nonneg (mul_nonneg hw0 hw0) (by linarith : (0 : ℝ) ≤ 1 - w),
      mul_nonneg (mul_nonneg (mul_nonneg hw0 hw0) hw0) hw0]
  rw [mul_pow, hr4]
  nlinarith [mul_le_mul_of_nonneg_left key hw0]

/-- Paper: `lem:resradial` (tanh_residual.tex), the polynomial step: from
`E ≤ 1 + 5t/3 + 4t^2` and `d ≥ t/3 - t^2/5` with `0 ≤ d ≤ 1`,
`(1 - d) E ≤ 1 + 4d + 5t^2`. -/
theorem radial_poly (t d E : ℝ) (ht : 0 ≤ t) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hlower : t / 3 - t ^ 2 / 5 ≤ d) (hE : E ≤ 1 + 5 * t / 3 + 4 * t ^ 2) :
    (1 - d) * E ≤ 1 + 4 * d + 5 * t ^ 2 := by
  have hmult := mul_le_mul_of_nonneg_left hE (by linarith : 0 ≤ 1 - d)
  have hp := mul_nonneg hd0 (by positivity : (0 : ℝ) ≤ 5 * t / 3 + 4 * t ^ 2)
  nlinarith

/-- The offspring factor of `sec:residual` (tanh_residual.tex):
`χ_g(r) = min{ (tanh(gr)/r) exp(5g^2r^2/3 + g^4r^4), g(1 + g^2r^2) e^{g^2r^2} }`. -/
noncomputable def chi (g r : ℝ) : ℝ :=
  min (Real.tanh (g * r) / r * Real.exp (5 / 3 * g ^ 2 * r ^ 2 + g ^ 4 * r ^ 4))
    (g * (1 + g ^ 2 * r ^ 2) * Real.exp (g ^ 2 * r ^ 2))

/-- Paper: `eq:reschicritical` in `lem:resradial` (tanh_residual.tex): for
`0 < r ≤ 1`, `χ_1(r) ≤ 1 + 4 d_1(r) + 5 r^4` with `d_1(r) = 1 - tanh r / r`. -/
theorem reschicritical {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    chi 1 r ≤ 1 + 4 * (1 - Real.tanh r / r) + 5 * r ^ 4 := by
  set t := r ^ 2 with htdef
  set d := 1 - Real.tanh r / r with hd
  have ht0 : 0 ≤ t := sq_nonneg r
  have ht1 : t ≤ 1 := by nlinarith
  have htanh0 := tanh_nonneg hr0.le
  have htanh1 := tanh_le_self hr0.le
  have hd0 : 0 ≤ d := by
    rw [hd, sub_nonneg, div_le_one hr0]
    exact htanh1
  have hd1 : d ≤ 1 := by
    rw [hd]
    have : 0 ≤ Real.tanh r / r := div_nonneg htanh0 hr0.le
    linarith
  have hdlow : t / 3 - t ^ 2 / 5 ≤ d := by
    have h := tanh_le_quintic hr0.le hr1
    rw [hd, htdef]
    have : Real.tanh r / r ≤ 1 - r ^ 2 / 3 + r ^ 4 / 5 := by
      rw [div_le_iff₀ hr0]
      linarith
    have e : (r ^ 2) ^ 2 = r ^ 4 := by ring
    rw [e]
    linarith
  have hr4 : r ^ 4 = t ^ 2 := by rw [htdef]; ring
  rw [hr4]
  rcases le_total t (2 / 5) with hsmall | hlarge
  · have hfirst : chi 1 r ≤ (1 - d) * Real.exp (5 / 3 * t + t ^ 2) := by
      refine (min_le_left _ _).trans (le_of_eq ?_)
      rw [hd, htdef]
      ring_nf
    have hE := exp_quadratic_le ht0 hsmall
    have := radial_poly t d (Real.exp (5 / 3 * t + t ^ 2)) ht0 hd0 hd1 hdlow (by linarith)
    linarith
  · have hsecond : chi 1 r ≤ (1 + t) * Real.exp t := by
      refine (min_le_right _ _).trans (le_of_eq ?_)
      rw [htdef]
      ring_nf
    have h := one_add_mul_exp_le ht0 ht1
    nlinarith

/-- Paper: proof of `thm:residualfused` (tanh_residual_fused.tex), "since
`χ_1(r) ≤ 1 + 4d_1(r) + 5r^4 ≤ 10`". -/
theorem chi_one_le_ten {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) : chi 1 r ≤ 10 := by
  have h := reschicritical hr0 hr1
  have ht0 := tanh_nonneg hr0.le
  have : 0 ≤ Real.tanh r / r := div_nonneg ht0 hr0.le
  have hr4 : r ^ 4 ≤ 1 := pow_le_one₀ hr0.le hr1
  linarith

/-- Auxiliary: `e^4 < 60`. -/
theorem exp_four_lt : Real.exp 4 < 60 := by
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  have e : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [e]
  have : Real.exp 1 ^ 4 < 2.7182818286 ^ 4 := pow_lt_pow_left₀ h h0.le (by norm_num)
  linarith [show (2.7182818286 : ℝ) ^ 4 < 60 by norm_num]

/-- Paper: `eq:reschisuper` in `lem:resradial` (tanh_residual.tex), the case
`δ = g - 1 ≥ 1/10`: the second expression gives `χ_g(r) ≤ 10 e^4 < 600`. -/
theorem reschisuper_large {g r : ℝ} (hg1 : 11 / 10 ≤ g) (hg2 : g ≤ 2) (hr0 : 0 < r)
    (hr1 : r ≤ 1) (hd : 0 ≤ 1 - Real.tanh (g * r) / r) :
    chi g r ≤ 1 + 4 * (1 - Real.tanh (g * r) / r) + 5 * r ^ 4 + 6000 * (g - 1) := by
  have hgr : g ^ 2 * r ^ 2 ≤ 4 := by
    have : g * r ≤ 2 := by nlinarith
    have : 0 ≤ g * r := by positivity
    nlinarith
  have hsecond : chi g r ≤ 2 * (1 + 4) * Real.exp 4 := by
    refine (min_le_right _ _).trans ?_
    have e1 : Real.exp (g ^ 2 * r ^ 2) ≤ Real.exp 4 := Real.exp_le_exp.mpr hgr
    have e2 : 0 ≤ 1 + g ^ 2 * r ^ 2 := by positivity
    have e3 : g * (1 + g ^ 2 * r ^ 2) ≤ 2 * (1 + 4) := by nlinarith
    exact mul_le_mul e3 e1 (Real.exp_pos _).le (by norm_num)
  have h4 := exp_four_lt
  have : 0 ≤ r ^ 4 := by positivity
  nlinarith

/-- Auxiliary: `e^{7/2} < 36`. -/
theorem exp_seven_halves_lt : Real.exp (7 / 2) < 36 := by
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  have hhalf : Real.exp (1 / 2) < 1.65 := by
    have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have hpos := Real.exp_pos (1 / 2)
    nlinarith
  have e : Real.exp (7 / 2) = Real.exp 1 ^ 3 * Real.exp (1 / 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    norm_num
  rw [e]
  have h3 : Real.exp 1 ^ 3 < 2.7182818286 ^ 3 := pow_lt_pow_left₀ h h0.le (by norm_num)
  have hp : 0 < Real.exp 1 ^ 3 := by positivity
  have := mul_lt_mul h3 hhalf.le (Real.exp_pos _) (by norm_num)
  linarith [show (2.7182818286 : ℝ) ^ 3 * 1.65 < 36 by norm_num]

/-- Auxiliary for `lem:resradial`: the derivative in `g` of the first expression
defining `χ_g(r)`. -/
theorem hasDerivAt_chiA (r g : ℝ) :
    HasDerivAt (fun g => Real.tanh (g * r) / r * Real.exp (5 / 3 * g ^ 2 * r ^ 2 + g ^ 4 * r ^ 4))
      ((1 - Real.tanh (g * r) ^ 2) * r / r * Real.exp (5 / 3 * g ^ 2 * r ^ 2 + g ^ 4 * r ^ 4) +
        Real.tanh (g * r) / r * (Real.exp (5 / 3 * g ^ 2 * r ^ 2 + g ^ 4 * r ^ 4) *
          (10 / 3 * g * r ^ 2 + 4 * g ^ 3 * r ^ 4))) g := by
  have h1 : HasDerivAt (fun g => Real.tanh (g * r)) ((1 - Real.tanh (g * r) ^ 2) * r) g := by
    have := (hasDerivAt_tanh (g * r)).comp g (hasDerivAt_mul_const r)
    rw [one_div_cosh_sq_eq] at this
    exact this
  have h2 : HasDerivAt (fun g : ℝ => 5 / 3 * g ^ 2 * r ^ 2 + g ^ 4 * r ^ 4)
      (10 / 3 * g * r ^ 2 + 4 * g ^ 3 * r ^ 4) g := by
    have a1 := (((hasDerivAt_pow 2 g).const_mul (5 / 3 : ℝ)).mul_const (r ^ 2))
    have a2 := ((hasDerivAt_pow 4 g).mul_const (r ^ 4))
    refine (a1.add a2).congr_deriv ?_
    push_cast
    ring
  have h3 := (Real.hasDerivAt_exp _).comp g h2
  exact (h1.div_const r).mul h3

/-- Auxiliary for `lem:resradial`: the derivative in `g` of the second
expression defining `χ_g(r)`. -/
theorem hasDerivAt_chiB (r g : ℝ) :
    HasDerivAt (fun g => g * (1 + g ^ 2 * r ^ 2) * Real.exp (g ^ 2 * r ^ 2))
      (Real.exp (g ^ 2 * r ^ 2) * (1 + 5 * g ^ 2 * r ^ 2 + 2 * g ^ 4 * r ^ 4)) g := by
  have h1 : HasDerivAt (fun g : ℝ => g * (1 + g ^ 2 * r ^ 2)) (1 + 3 * g ^ 2 * r ^ 2) g := by
    have a := (hasDerivAt_id' g).mul (((hasDerivAt_pow 2 g).mul_const (r ^ 2)).const_add 1)
    refine a.congr_deriv ?_
    push_cast
    ring
  have h2 : HasDerivAt (fun g : ℝ => g ^ 2 * r ^ 2) (2 * g * r ^ 2) g := by
    refine ((hasDerivAt_pow 2 g).mul_const (r ^ 2)).congr_deriv ?_
    push_cast
    ring
  have h3 := (Real.hasDerivAt_exp _).comp g h2
  refine (h1.mul h3).congr_deriv ?_
  simp only [Function.comp_apply]
  ring

/-- Paper: `eq:reschisuper` in `lem:resradial` (tanh_residual.tex), the case
`δ = g - 1 ≤ 1/10`: both expressions defining `χ_g` are `400`-Lipschitz in `g`,
so `χ_g(r) ≤ χ_1(r) + 400(g - 1)`. -/
theorem chi_lipschitz {g r : ℝ} (hg1 : 1 ≤ g) (hg : g ≤ 11 / 10) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    chi g r ≤ chi 1 r + 400 * (g - 1) := by
  set D := Set.Icc (1 : ℝ) (11 / 10) with hD
  have hint : interior D = Set.Ioo 1 (11 / 10) := interior_Icc
  -- first expression
  have hA : Real.tanh (g * r) / r * Real.exp (5 / 3 * g ^ 2 * r ^ 2 + g ^ 4 * r ^ 4) -
      Real.tanh (1 * r) / r * Real.exp (5 / 3 * 1 ^ 2 * r ^ 2 + 1 ^ 4 * r ^ 4) ≤
      400 * (g - 1) := by
    refine (convex_Icc (1 : ℝ) (11 / 10)).image_sub_le_mul_sub_of_deriv_le
      (fun x _ => (hasDerivAt_chiA r x).continuousAt.continuousWithinAt)
      (fun x _ => (hasDerivAt_chiA r x).differentiableAt.differentiableWithinAt)
      (fun x hx => ?_) 1 ⟨le_rfl, by norm_num⟩ g ⟨hg1, hg⟩ hg1
    rw [hint] at hx
    rw [(hasDerivAt_chiA r x).deriv]
    obtain ⟨hx1, hx2⟩ := hx
    have hxr : x * r ≤ 11 / 10 := by nlinarith
    have hxr0 : 0 ≤ x * r := by nlinarith
    have hE : 5 / 3 * x ^ 2 * r ^ 2 + x ^ 4 * r ^ 4 ≤ 7 / 2 := by
      have h2 : (x * r) ^ 2 ≤ (11 / 10) ^ 2 := pow_le_pow_left₀ hxr0 hxr 2
      have h4 : (x * r) ^ 4 ≤ (11 / 10) ^ 4 := pow_le_pow_left₀ hxr0 hxr 4
      nlinarith
    have hexp : Real.exp (5 / 3 * x ^ 2 * r ^ 2 + x ^ 4 * r ^ 4) < 36 :=
      lt_of_le_of_lt (Real.exp_le_exp.mpr hE) exp_seven_halves_lt
    have hexp0 := Real.exp_pos (5 / 3 * x ^ 2 * r ^ 2 + x ^ 4 * r ^ 4)
    have ht0 := tanh_nonneg hxr0
    have ht1 := tanh_le_self hxr0
    have hsq : 0 ≤ Real.tanh (x * r) ^ 2 := sq_nonneg _
    have hq : Real.tanh (x * r) / r ≤ 11 / 10 := by
      rw [div_le_iff₀ hr0]
      nlinarith
    have hq0 : 0 ≤ Real.tanh (x * r) / r := div_nonneg ht0 hr0.le
    have hP : 10 / 3 * x * r ^ 2 + 4 * x ^ 3 * r ^ 4 ≤ 9 := by
      have hr2 : r ^ 2 ≤ 1 := by nlinarith
      have hr4 : r ^ 4 ≤ 1 := by nlinarith
      have hx3 : x ^ 3 ≤ (11 / 10) ^ 3 := pow_le_pow_left₀ (by linarith) hx2.le 3
      have p1 : x * r ^ 2 ≤ 11 / 10 * 1 := mul_le_mul hx2.le hr2 (sq_nonneg r) (by norm_num)
      have p2 : x ^ 3 * r ^ 4 ≤ (11 / 10) ^ 3 * 1 :=
        mul_le_mul hx3 hr4 (by positivity) (by norm_num)
      nlinarith
    have hP0 : 0 ≤ 10 / 3 * x * r ^ 2 + 4 * x ^ 3 * r ^ 4 := by positivity
    have t1 : (1 - Real.tanh (x * r) ^ 2) * r / r * Real.exp (5 / 3 * x ^ 2 * r ^ 2 + x ^ 4 * r ^ 4)
        ≤ 36 := by
      rw [mul_div_assoc, div_self hr0.ne', mul_one]
      have : 1 - Real.tanh (x * r) ^ 2 ≤ 1 := by linarith
      have h1t : 0 ≤ 1 - Real.tanh (x * r) ^ 2 := by
        have := Real.abs_tanh_lt_one (x * r)
        nlinarith [sq_abs (Real.tanh (x * r)), abs_nonneg (Real.tanh (x * r))]
      nlinarith
    have t2 : Real.tanh (x * r) / r * (Real.exp (5 / 3 * x ^ 2 * r ^ 2 + x ^ 4 * r ^ 4) *
        (10 / 3 * x * r ^ 2 + 4 * x ^ 3 * r ^ 4)) ≤ 11 / 10 * (36 * 9) := by
      apply mul_le_mul hq _ (by positivity) (by norm_num)
      exact mul_le_mul hexp.le hP hP0 (by norm_num)
    linarith
  -- second expression
  have hB : g * (1 + g ^ 2 * r ^ 2) * Real.exp (g ^ 2 * r ^ 2) -
      1 * (1 + 1 ^ 2 * r ^ 2) * Real.exp (1 ^ 2 * r ^ 2) ≤ 400 * (g - 1) := by
    refine (convex_Icc (1 : ℝ) (11 / 10)).image_sub_le_mul_sub_of_deriv_le
      (fun x _ => (hasDerivAt_chiB r x).continuousAt.continuousWithinAt)
      (fun x _ => (hasDerivAt_chiB r x).differentiableAt.differentiableWithinAt)
      (fun x hx => ?_) 1 ⟨le_rfl, by norm_num⟩ g ⟨hg1, hg⟩ hg1
    rw [hint] at hx
    rw [(hasDerivAt_chiB r x).deriv]
    obtain ⟨hx1, hx2⟩ := hx
    have hxr : x * r ≤ 11 / 10 := by nlinarith
    have hxr0 : 0 ≤ x * r := by nlinarith
    have h2 : (x * r) ^ 2 ≤ (11 / 10) ^ 2 := pow_le_pow_left₀ hxr0 hxr 2
    have h4 : (x * r) ^ 4 ≤ (11 / 10) ^ 4 := pow_le_pow_left₀ hxr0 hxr 4
    have hexp : Real.exp (x ^ 2 * r ^ 2) ≤ Real.exp 2 :=
      Real.exp_le_exp.mpr (by nlinarith)
    have he2 : Real.exp 2 < 8 := by
      have h := Real.exp_one_lt_d9
      have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      have : Real.exp 1 ^ 2 < 2.7182818286 ^ 2 :=
        pow_lt_pow_left₀ h (Real.exp_pos 1).le (by norm_num)
      linarith [show (2.7182818286 : ℝ) ^ 2 < 8 by norm_num]
    have hP : 1 + 5 * x ^ 2 * r ^ 2 + 2 * x ^ 4 * r ^ 4 ≤ 10 := by nlinarith
    have hP0 : 0 ≤ 1 + 5 * x ^ 2 * r ^ 2 + 2 * x ^ 4 * r ^ 4 := by positivity
    have := mul_le_mul (hexp.trans he2.le) hP hP0 (by norm_num)
    linarith
  -- combine the minima
  unfold chi
  simp only [one_mul, one_pow, mul_one] at hA hB ⊢
  rcases le_total (Real.tanh r / r * Real.exp (5 / 3 * r ^ 2 + r ^ 4))
      ((1 + r ^ 2) * Real.exp (r ^ 2)) with h | h
  · rw [min_eq_left h]
    have := min_le_left (Real.tanh (g * r) / r * Real.exp (5 / 3 * g ^ 2 * r ^ 2 + g ^ 4 * r ^ 4))
      (g * (1 + g ^ 2 * r ^ 2) * Real.exp (g ^ 2 * r ^ 2))
    have e : 5 / 3 * r ^ 2 + r ^ 4 = 5 / 3 * 1 ^ 2 * r ^ 2 + 1 ^ 4 * r ^ 4 := by ring
    linarith
  · rw [min_eq_right h]
    have := min_le_right (Real.tanh (g * r) / r * Real.exp (5 / 3 * g ^ 2 * r ^ 2 + g ^ 4 * r ^ 4))
      (g * (1 + g ^ 2 * r ^ 2) * Real.exp (g ^ 2 * r ^ 2))
    linarith

/-- Paper: `eq:reschisuper` in `lem:resradial` (tanh_residual.tex): whenever
`0 < r ≤ 1`, `1 ≤ g ≤ 2` and `d_g(r) ≥ 0`,
`χ_g(r) ≤ 1 + 4 d_g(r) + 5r^4 + 6000(g-1)`; the case `g ≤ 11/10` gives `404` in place
of `6000`. -/
theorem reschisuper {g r : ℝ} (hg1 : 1 ≤ g) (hg2 : g ≤ 2) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hd : 0 ≤ 1 - Real.tanh (g * r) / r) :
    chi g r ≤ 1 + 4 * (1 - Real.tanh (g * r) / r) + 5 * r ^ 4 + 6000 * (g - 1) := by
  rcases le_total g (11 / 10) with hsmall | hlarge
  · have h1 := chi_lipschitz hg1 hsmall hr0 hr1
    have h2 := reschicritical hr0 hr1
    -- `d_1(r) ≤ d_g(r) + (g - 1)`
    have h3 : Real.tanh (g * r) - Real.tanh r ≤ g * r - r := tanh_sub_le r (g * r) (by nlinarith)
    have h4 : 1 - Real.tanh r / r ≤ 1 - Real.tanh (g * r) / r + (g - 1) := by
      have : (Real.tanh (g * r) - Real.tanh r) / r ≤ (g * r - r) / r :=
        div_le_div_of_nonneg_right h3 hr0.le
      rw [sub_div, sub_div, mul_div_assoc, div_self hr0.ne', mul_one] at this
      linarith
    nlinarith
  · exact reschisuper_large hlarge hg2 hr0 hr1 hd

/-! ## The global majority cost (`thm:resmeanlaw`, `prop:largerow`) -/

/-- Paper: upper bounds of `thm:resmeanlaw` (tanh_residual.tex): the derivative
of the residual chain is the product `F_D'(z) = ∏_{j<D} (p + α s sech^2(s F_j(z)))`. -/
theorem hasDerivAt_chain (α s z : ℝ) (D : ℕ) :
    HasDerivAt (fun x => chain α s x D)
      (∏ j ∈ range D, (1 - α + α * s * (1 - Real.tanh (s * chain α s z j) ^ 2))) z := by
  induction D with
  | zero => simpa [chain] using hasDerivAt_id' z
  | succ D ih =>
      have ht := (hasDerivAt_tanh (s * chain α s z D)).comp z (ih.const_mul s)
      have h := (ih.const_mul (1 - α)).add (ht.const_mul α)
      rw [prod_range_succ]
      refine h.congr_deriv ?_
      rw [one_div_cosh_sq_eq]
      ring

/-- Auxiliary: `0 ≤ ∏ (1 - u_j) ≤ 1` and `1 - ∏_{j<n} (1 - u_j) ≤ ∑_{j<n} u_j` for
`u_j ∈ [0, 1]`. -/
theorem one_sub_prod_le_sum (u : ℕ → ℝ) (h0 : ∀ j, 0 ≤ u j) (h1 : ∀ j, u j ≤ 1) (n : ℕ) :
    0 ≤ ∏ j ∈ range n, (1 - u j) ∧ ∏ j ∈ range n, (1 - u j) ≤ 1 ∧
      1 - ∏ j ∈ range n, (1 - u j) ≤ ∑ j ∈ range n, u j := by
  induction n with
  | zero => simp
  | succ n ih =>
      obtain ⟨a, b, c⟩ := ih
      rw [prod_range_succ, sum_range_succ]
      have hu0 := h0 n
      have hu1 := h1 n
      refine ⟨mul_nonneg a (by linarith), ?_, ?_⟩
      · nlinarith
      · nlinarith

/-- Paper: upper bounds of `thm:resmeanlaw` (tanh_residual.tex): for
`0 ≤ z ≤ 1`, `F_j(z) ≤ a^j z`, and the loss satisfies
`0 ≤ λ - F_D'(z) ≤ λ min{1, A z^2}` with `λ = a^D`,
`A = (α s^3/a) ∑_{j<D} a^{2j}`. -/
theorem resmean_loss (α s z : ℝ) (D : ℕ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hs : 0 < s)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ (1 - α + α * s) ^ D -
        ∏ j ∈ range D, (1 - α + α * s * (1 - Real.tanh (s * chain α s z j) ^ 2)) ∧
      (1 - α + α * s) ^ D -
        ∏ j ∈ range D, (1 - α + α * s * (1 - Real.tanh (s * chain α s z j) ^ 2)) ≤
        (1 - α + α * s) ^ D * min 1 (α * s ^ 3 / (1 - α + α * s) *
          (∑ j ∈ range D, (1 - α + α * s) ^ (2 * j)) * z ^ 2) := by
  set a := 1 - α + α * s with ha
  have ha0 : 0 < a := by
    rcases lt_or_ge α 1 with h | h
    · nlinarith
    · nlinarith
  set v := α * s / a with hv
  have hv0 : 0 ≤ v := by positivity
  have hv1 : v ≤ 1 := by rw [hv, div_le_one ha0]; linarith
  have hmem := chain_mem_Icc α s z hα0 hα1 hs.le hz0 hz1
  -- `F_j ≤ a^j z`
  have hFa : ∀ j, chain α s z j ≤ a ^ j * z := by
    intro j
    induction j with
    | zero => simp [chain]
    | succ j ih =>
        simp only [chain]
        have ht := tanh_le_self (mul_nonneg hs.le (hmem j).1)
        have e1 : (1 - α) * chain α s z j + α * Real.tanh (s * chain α s z j) ≤
            a * chain α s z j := by
          have := mul_le_mul_of_nonneg_left ht hα0
          rw [ha]
          nlinarith
        have e2 : a * chain α s z j ≤ a * (a ^ j * z) := mul_le_mul_of_nonneg_left ih ha0.le
        rw [pow_succ]
        nlinarith
  set u : ℕ → ℝ := fun j => v * Real.tanh (s * chain α s z j) ^ 2 with hu
  have hu0 : ∀ j, 0 ≤ u j := fun j => by simp only [hu]; positivity
  have hu1 : ∀ j, u j ≤ 1 := fun j => by
    simp only [hu]
    have : Real.tanh (s * chain α s z j) ^ 2 ≤ 1 := by
      have := Real.abs_tanh_lt_one (s * chain α s z j)
      nlinarith [sq_abs (Real.tanh (s * chain α s z j)), abs_nonneg (Real.tanh (s * chain α s z j))]
    nlinarith
  have hfac : ∀ j ∈ range D, 1 - α + α * s * (1 - Real.tanh (s * chain α s z j) ^ 2) =
      a * (1 - u j) := by
    intro j _
    simp only [hu, hv]
    field_simp
    ring
  rw [prod_congr rfl hfac, prod_mul_distrib, prod_const, card_range]
  obtain ⟨p0, p1, p2⟩ := one_sub_prod_le_sum u hu0 hu1 D
  have hlam0 : 0 ≤ a ^ D := by positivity
  -- `∑ u_j ≤ A z^2`
  have husum : ∑ j ∈ range D, u j ≤ α * s ^ 3 / a * (∑ j ∈ range D, a ^ (2 * j)) * z ^ 2 := by
    have hterm : ∀ j ∈ range D, u j ≤ α * s ^ 3 / a * (a ^ (2 * j) * z ^ 2) := by
      intro j _
      simp only [hu, hv]
      have hF0 := (hmem j).1
      have ht0 := tanh_nonneg (mul_nonneg hs.le hF0)
      have ht := tanh_le_self (mul_nonneg hs.le hF0)
      have h1 : Real.tanh (s * chain α s z j) ^ 2 ≤ (s * chain α s z j) ^ 2 :=
        pow_le_pow_left₀ ht0 ht 2
      have h2 : (s * chain α s z j) ^ 2 ≤ (s * (a ^ j * z)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (hFa j) hs.le) 2
      have e : α * s ^ 3 / a * (a ^ (2 * j) * z ^ 2) = α * s / a * (s * (a ^ j * z)) ^ 2 := by
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (h1.trans h2) hv0
    have := sum_le_sum hterm
    have e : ∑ i ∈ range D, α * s ^ 3 / a * (a ^ (2 * i) * z ^ 2) =
        α * s ^ 3 / a * (∑ j ∈ range D, a ^ (2 * j)) * z ^ 2 := by
      rw [mul_assoc, sum_mul, mul_sum]
    linarith
  constructor
  · nlinarith
  · have e : a ^ D - a ^ D * ∏ j ∈ range D, (1 - u j) = a ^ D * (1 - ∏ j ∈ range D, (1 - u j)) := by
      ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ hlam0
    exact le_min (by linarith) (p2.trans husum)

/-- Auxiliary for `eq:chainQ` and `lem:comptanharity`: if `0 ≤ f ≤ A` on `[0, 1]`
and `f(z) ≤ 1/z^2` on `(0, 1]`, then `∫_0^1 f ≤ 2√A - 1` for `A ≥ 1`
(the integral of `min{A, z^{-2}}`). -/
theorem integral_le_two_sqrt_sub_one (A : ℝ) (hA : 1 ≤ A) (f : ℝ → ℝ)
    (hf0 : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f z) (hfA : ∀ z ∈ Set.Icc (0 : ℝ) 1, f z ≤ A)
    (hfz : ∀ z ∈ Set.Ioc (0 : ℝ) 1, f z ≤ 1 / z ^ 2) :
    ∫ z in (0 : ℝ)..1, f z ≤ 2 * Real.sqrt A - 1 := by
  set a := 1 / Real.sqrt A with ha
  have hsA : 1 ≤ Real.sqrt A := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hA
  have hsA2 : Real.sqrt A ^ 2 = A := Real.sq_sqrt (by linarith)
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by rw [ha, div_le_one (by linarith)]; exact hsA
  have haA : 1 / a ^ 2 = A := by rw [ha, div_pow, one_pow, hsA2]; field_simp
  set g : ℝ → ℝ := fun z => if z ≤ a then A else 1 / z ^ 2 with hg
  have hgmeas : Measurable g :=
    Measurable.ite measurableSet_Iic measurable_const (by fun_prop)
  have hgle : ∀ z, g z ≤ A := by
    intro z
    simp only [hg]
    split_ifs with h
    · exact le_rfl
    · push Not at h
      rw [← haA]
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ ha0.le h.le 2)
  have hg0 : ∀ z, 0 ≤ g z := by
    intro z
    simp only [hg]
    split_ifs <;> positivity
  have hgint : ∀ b c : ℝ, IntervalIntegrable g MeasureTheory.volume b c := by
    intro b c
    refine (intervalIntegrable_const (c := A)).mono_fun hgmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun z => ?_
    have hA0 : (0 : ℝ) ≤ A := by linarith
    simp only [Real.norm_eq_abs, abs_of_nonneg (hg0 z), abs_of_nonneg hA0]
    exact hgle z
  -- `∫ f ≤ ∫ g`
  have hfg : ∫ z in (0 : ℝ)..1, f z ≤ ∫ z in (0 : ℝ)..1, g z := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
    apply MeasureTheory.integral_mono_of_nonneg
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun z hz => hf0 z ⟨hz.1.le, hz.2⟩)
    · exact (hgint 0 1).1
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun z hz => ?_)
      simp only [hg]
      split_ifs with h
      · exact hfA z ⟨hz.1.le, hz.2⟩
      · exact hfz z hz
  -- compute `∫ g`
  have h1 : ∫ z in (0 : ℝ)..a, g z = a * A := by
    rw [intervalIntegral.integral_congr (g := fun _ => A)]
    · simp
    · intro z hz
      rw [Set.uIcc_of_le ha0.le] at hz
      show (if z ≤ a then A else 1 / z ^ 2) = A
      simp [hz.2]
  have h2 : ∫ z in a..1, g z = 1 / a - 1 := by
    rw [intervalIntegral.integral_congr (g := fun z => 1 / z ^ 2)]
    · have hd : ∀ z ∈ Set.uIcc a 1, HasDerivAt (fun z : ℝ => -(1 / z)) (1 / z ^ 2) z := by
        intro z hz
        rw [Set.uIcc_of_le ha1] at hz
        have hz0 : z ≠ 0 := by linarith [hz.1]
        have := (hasDerivAt_inv hz0).neg
        convert this using 1
        · funext y
          simp
        · field_simp
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
      · ring
      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.div continuousOn_const (continuousOn_pow 2)
        intro z hz
        rw [Set.uIcc_of_le ha1] at hz
        have : 0 < z := by linarith [hz.1]
        positivity
    · intro z hz
      rw [Set.uIcc_of_le ha1] at hz
      simp only [hg]
      split_ifs with h
      · have : z = a := le_antisymm h hz.1
        rw [this, haA]
      · rfl
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hgint 0 a) (hgint a 1)
  rw [h1, h2] at hsplit
  have e1 : a * A = Real.sqrt A := by
    have hm : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt (by linarith)
    rw [ha, one_div_mul_eq_div, div_eq_iff (by positivity)]
    linarith
  have e2 : 1 / a = Real.sqrt A := by rw [ha, one_div_one_div]
  rw [e1, e2] at hsplit
  linarith

/-- Paper: upper bounds of `thm:resmeanlaw` (tanh_residual.tex): the
full-majority source count `Q = λ + ∫_0^1 (λ - F_D'(z))/z^2 dz` of the global
mixture satisfies `Q ≤ 2λ√(1+A)`. -/
theorem resmean_majority_cost (α s : ℝ) (D : ℕ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hs : 0 < s) :
    (1 - α + α * s) ^ D + ∫ z in (0 : ℝ)..1, ((1 - α + α * s) ^ D -
        ∏ j ∈ range D, (1 - α + α * s * (1 - Real.tanh (s * chain α s z j) ^ 2))) / z ^ 2 ≤
      2 * (1 - α + α * s) ^ D * Real.sqrt (1 + α * s ^ 3 / (1 - α + α * s) *
        ∑ j ∈ range D, (1 - α + α * s) ^ (2 * j)) := by
  set a := 1 - α + α * s with ha
  have ha0 : 0 < a := by
    rcases lt_or_ge α 1 with h | h
    · nlinarith
    · nlinarith
  set lam := a ^ D with hlam
  have hlam0 : 0 < lam := by positivity
  obtain ⟨A, hA⟩ : ∃ A, A = α * s ^ 3 / a * ∑ j ∈ range D, a ^ (2 * j) := ⟨_, rfl⟩
  rw [← hA]
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  set f : ℝ → ℝ := fun z => (lam - ∏ j ∈ range D,
    (1 - α + α * s * (1 - Real.tanh (s * chain α s z j) ^ 2))) / z ^ 2 with hf
  have hloss := fun z (hz : z ∈ Set.Icc (0 : ℝ) 1) => resmean_loss α s z D hα0 hα1 hs hz.1 hz.2
  have hf0 : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f z / lam := by
    intro z hz
    simp only [hf]
    have := (hloss z hz).1
    positivity
  have hfA : ∀ z ∈ Set.Icc (0 : ℝ) 1, f z / lam ≤ A := by
    intro z hz
    simp only [hf]
    have h2 := (hloss z hz).2
    rw [← hA] at h2
    rcases eq_or_lt_of_le hz.1 with h0 | hpos
    · rw [← h0]
      simp
      exact hA0
    · rw [div_div, div_le_iff₀ (by positivity)]
      have : lam * min 1 (A * z ^ 2) ≤ lam * (A * z ^ 2) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hlam0.le
      nlinarith
  have hfz : ∀ z ∈ Set.Ioc (0 : ℝ) 1, f z / lam ≤ 1 / z ^ 2 := by
    intro z hz
    simp only [hf]
    have h2 := (hloss z ⟨hz.1.le, hz.2⟩).2
    rw [← hA] at h2
    have : lam * min 1 (A * z ^ 2) ≤ lam * 1 :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hlam0.le
    rw [div_div, div_le_div_iff₀ (by have := hz.1; positivity) (by have := hz.1; positivity)]
    nlinarith [sq_nonneg z]
  have hint : ∫ z in (0 : ℝ)..1, f z = lam * ∫ z in (0 : ℝ)..1, f z / lam := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext z
    field_simp
  show lam + ∫ z in (0 : ℝ)..1, f z ≤ 2 * lam * Real.sqrt (1 + A)
  rw [hint]
  have hs1 : 1 ≤ Real.sqrt (1 + A) := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + A) := Real.sqrt_le_sqrt (by linarith)
  have hs2 : Real.sqrt (1 + A) ^ 2 = 1 + A := Real.sq_sqrt (by linarith)
  rcases le_total 1 A with hA1 | hA1
  · have h := integral_le_two_sqrt_sub_one A hA1 _ hf0 hfA hfz
    have hsA : Real.sqrt A ≤ Real.sqrt (1 + A) := Real.sqrt_le_sqrt (by linarith)
    nlinarith
  · have h : ∫ z in (0 : ℝ)..1, f z / lam ≤ A := by
      by_cases hi : IntervalIntegrable (fun z => f z / lam) MeasureTheory.volume 0 1
      · have h3 := intervalIntegral.integral_mono_on zero_le_one hi intervalIntegrable_const hfA
        simpa using h3
      · rw [intervalIntegral.integral_undef hi]
        exact hA0
    -- `1 + A ≤ 2 √(1+A)` for `A ≤ 3`
    have : 1 + A ≤ 2 * Real.sqrt (1 + A) := by nlinarith
    nlinarith

/-- Paper: `lem:comptanharity` (tanh_large_radius.tex), used in `prop:largerow`
(tanh_residual.tex): the full-majority source count
`Q_u = u + ∫_0^1 u tanh^2(uz)/z^2 dz` satisfies `Q_u ≤ 2 max{u, u^2}`. -/
theorem majority_count_le (u : ℝ) (hu : 0 < u) :
    u + ∫ z in (0 : ℝ)..1, u * Real.tanh (u * z) ^ 2 / z ^ 2 ≤ 2 * max u (u ^ 2) := by
  set f : ℝ → ℝ := fun z => Real.tanh (u * z) ^ 2 / z ^ 2 with hf
  have hf0 : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f z := fun z _ => by simp only [hf]; positivity
  have hfA : ∀ z ∈ Set.Icc (0 : ℝ) 1, f z ≤ u ^ 2 := by
    intro z hz
    simp only [hf]
    rcases eq_or_lt_of_le hz.1 with h0 | hpos
    · rw [← h0]; simp; positivity
    · rw [div_le_iff₀ (by positivity)]
      have ht0 := tanh_nonneg (mul_nonneg hu.le hz.1)
      have ht := tanh_le_self (mul_nonneg hu.le hz.1)
      have := pow_le_pow_left₀ ht0 ht 2
      nlinarith
  have hfz : ∀ z ∈ Set.Ioc (0 : ℝ) 1, f z ≤ 1 / z ^ 2 := by
    intro z hz
    simp only [hf]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := Real.abs_tanh_lt_one (u * z)
    nlinarith [sq_abs (Real.tanh (u * z)), abs_nonneg (Real.tanh (u * z))]
  have hint : ∫ z in (0 : ℝ)..1, u * Real.tanh (u * z) ^ 2 / z ^ 2 =
      u * ∫ z in (0 : ℝ)..1, f z := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext z
    simp only [hf]
    ring
  rw [hint]
  rcases le_total u 1 with hu1 | hu1
  · have h : ∫ z in (0 : ℝ)..1, f z ≤ u ^ 2 := by
      by_cases hi : IntervalIntegrable f MeasureTheory.volume 0 1
      · have h3 := intervalIntegral.integral_mono_on zero_le_one hi intervalIntegrable_const hfA
        simpa using h3
      · rw [intervalIntegral.integral_undef hi]
        positivity
    rw [max_eq_left (by nlinarith)]
    nlinarith
  · have h := integral_le_two_sqrt_sub_one (u ^ 2) (by nlinarith) f hf0 hfA hfz
    rw [Real.sqrt_sq hu.le] at h
    rw [max_eq_right (by nlinarith)]
    nlinarith

end ExactSampling.ResidualDepth
