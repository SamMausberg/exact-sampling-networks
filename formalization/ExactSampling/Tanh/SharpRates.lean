import Mathlib

/-!
# Radius decay, rounding stability, the recursion size, and the scalar mean chain

This module formalizes the quantitative depth analysis of the recursive tanh sampler in
`tanh_rates.tex` (Section `sec:cost`) and the scalar mean chain of `tanh_mean.tex`
(Section `sec:wholechain`):

* the hyperbolic inequalities `coth² u ≥ u⁻² + 2/3` (`eq:cothradius`), `u coth u ≤ 1 + u²/3`
  (proof of `lem:nearcriticalgap`), and `coth² u ≤ u⁻² + 1` (used in `eq:chainrange`), each
  proved from the power series of `cosh` and `sinh`;
* `lem:radius`: the critical bound `R_j² ≤ 3/(2j+3)`, the supercritical bound
  `eq:superradius`, the monotone rational map `Φ_g`, and `R_j ≤ g^j R_j^{(1)}`;
* `lem:rounding`: the one-sided Lipschitz property of `tanh (g ·)` above the ideal radius, the
  error propagation `0 ≤ r_j - R_j ≤ 3jε`, the precision choice `eq:precision`, the `29/200`
  budget, and both final-radius bounds;
* the call bound `eq:maincall` of `thm:upper`, in the form: the right side of the generation
  bound `eq:generalcost` is at most `80 (D+1)²` for `g ≤ 1` and at most `80 (D+1)² e^{51 δ D}`
  for `1 ≤ g ≤ 2`, with `eq:qsums`;
* from `prop:fixedrate`: the bounds `3(s-1) ≤ u_*² ≤ (3/2)(s² - 1)` at any positive fixed point,
  `0 < λ < 1`, `eq:psibound`, and its converse; and `lem:nearcriticalgap`;
* the scalar mean chain: the product formula `F_{s,D}' = s^D Π_j (1 - F_{s,j}²)`, the range
  comparison `eq:chainrange`, the cost bounds `eq:chainQ`, the upper bounds of
  `thm:uniformchain` and `thm:chainphase`, and their lower bounds from the paper's coupling and
  score inequalities.

Stand-in hypotheses, each named in the statement that uses it:
* the generation bound `eq:generalcost` enters `maincall_critical` and `maincall_super` as the
  quantity being bounded (its derivation by conditional expectation over the recursion tree is
  not formalized);
* the cost `Q_{D,s}` of the global mixture is the integral formula `eq:chainarity`;
* the lower bounds of the scalar chain assume the endpoint coupling inequality `R ≤ M` and the
  score inequalities `eq:unknownlower` for the target, which the paper derives from the
  transcript identities `lem:transcript`.

Not formalized: the probabilistic derivation of `eq:generalcost`; the composition form
`eq:chainH` and the complete monotonicity argument behind `eq:chainmixture`; the remark on
subcritical work; from `prop:fixedrate`, its main claim `E N_calls ≤ C_s e^{D Ψ_s}`, the
existence and uniqueness of the positive fixed point `r_*` (it is a hypothesis of the fixed-point
lemmas), the geometric convergence `0 ≤ R_j - r_* ≤ λ^j (1 - r_*)`, the excess sum `A_s`, and the
prefactor `C_s`; and the finite-input theorems `thm:finitejoint` and `thm:finitecritical`.
-/

namespace ExactSampling.SharpRates

open Real Finset

/-! ### Hyperbolic inequalities from power series -/

/-- Termwise comparison behind `eq:cothradius`. -/
theorem cosh_series_term_le (u : ℝ) (n : ℕ) :
    3 * ((2 * u) ^ (2 * (n + 2)) / ((2 * (n + 2)).factorial : ℝ)) ≤
      u ^ 2 * ((2 * u) ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ)) := by
  have hf : ((2 * (n + 2)).factorial : ℝ) =
      (2 * n + 4) * (2 * n + 3) * ((2 * (n + 1)).factorial : ℝ) := by
    rw [show 2 * (n + 2) = (2 * (n + 1) + 1) + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    ring
  have hp : (2 * u) ^ (2 * (n + 2)) = (2 * u) ^ (2 * (n + 1)) * (4 * u ^ 2) := by
    rw [show 2 * (n + 2) = 2 * (n + 1) + 2 by ring, pow_add]
    ring
  have hF : 0 < ((2 * (n + 1)).factorial : ℝ) := by positivity
  have hX : 0 ≤ (2 * u) ^ (2 * (n + 1)) := by rw [pow_mul]; positivity
  have hn : (12 : ℝ) ≤ (2 * n + 4) * (2 * n + 3) := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  rw [hf, hp]
  have key : 3 * ((2 * u) ^ (2 * (n + 1)) * (4 * u ^ 2) /
      ((2 * n + 4) * (2 * n + 3) * ((2 * (n + 1)).factorial : ℝ))) =
      u ^ 2 * ((2 * u) ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ)) *
        (12 / ((2 * n + 4) * (2 * n + 3))) := by
    field_simp
    ring
  rw [key]
  apply mul_le_of_le_one_right (by positivity)
  rw [div_le_one (by linarith)]
  exact hn

/-- The coefficientwise inequality `u² - sinh² u + (u²/3) sinh² u ≥ 0`, scaled by three.
Paper: `lem:radius` (`tanh_rates.tex`), proof of `eq:cothradius`. -/
theorem sinh_sq_series_ineq (u : ℝ) : 0 ≤ 3 * u ^ 2 - 3 * sinh u ^ 2 + u ^ 2 * sinh u ^ 2 := by
  set a : ℕ → ℝ := fun n => (2 * u) ^ (2 * n) / ((2 * n).factorial : ℝ) with ha
  have hC : HasSum a (cosh (2 * u)) := hasSum_cosh (2 * u)
  have hC1 : HasSum (fun n => a (n + 1)) (cosh (2 * u) - 1) := by
    have := (hasSum_nat_add_iff' 1).mpr hC
    simpa [ha] using this
  have hf : HasSum (fun n => u ^ 2 * a n - 3 * a (n + 1))
      (u ^ 2 * cosh (2 * u) - 3 * (cosh (2 * u) - 1)) :=
    (hC.mul_left (u ^ 2)).sub (hC1.mul_left 3)
  have hf1 : HasSum (fun n => u ^ 2 * a (n + 1) - 3 * a (n + 2))
      (u ^ 2 * cosh (2 * u) - 3 * (cosh (2 * u) - 1) + 5 * u ^ 2) := by
    have := (hasSum_nat_add_iff' 1).mpr hf
    convert this using 1
    simp [ha]
    ring
  have hnn : 0 ≤ u ^ 2 * cosh (2 * u) - 3 * (cosh (2 * u) - 1) + 5 * u ^ 2 := by
    apply hf1.nonneg
    intro n
    have := cosh_series_term_le u n
    simp only [ha]
    linarith
  have hc2 : cosh (2 * u) = 1 + 2 * sinh u ^ 2 := by
    rw [cosh_two_mul, cosh_sq']; ring
  rw [hc2] at hnn
  nlinarith [hnn]

/-- The reciprocal-square inequality `coth² u ≥ u⁻² + 2/3`.
Paper: `eq:cothradius` in `lem:radius` (`tanh_rates.tex`). Stated for every `u ≠ 0`. -/
theorem coth_sq_ge {u : ℝ} (hu : u ≠ 0) : 1 / u ^ 2 + 2 / 3 ≤ 1 / tanh u ^ 2 := by
  have hs : sinh u ≠ 0 := by
    intro h; exact hu (sinh_eq_zero.mp h)
  have hs2 : 0 < sinh u ^ 2 := by positivity
  have hu2 : 0 < u ^ 2 := by positivity
  have hc := cosh_pos u
  have key := sinh_sq_series_ineq u
  have hcs := cosh_sq' u
  rw [tanh_eq_sinh_div_cosh, div_pow, one_div_div, div_add_div _ _ hu2.ne' (by norm_num),
    div_le_div_iff₀ (by positivity) hs2]
  nlinarith

/-- `tanh² x ≤ x² / (1 + 2x²/3)`, the form of `eq:cothradius` used for the radius map. -/
theorem tanh_sq_le (x : ℝ) : tanh x ^ 2 ≤ x ^ 2 / (1 + 2 / 3 * x ^ 2) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h := coth_sq_ge hx
  have hx2 : 0 < x ^ 2 := by positivity
  have ht : tanh x ≠ 0 := by
    intro h0
    have := tanh_artanh (x := 0) (by norm_num)
    rw [Real.artanh_zero] at this
    have h1 : tanh x = tanh 0 := by rw [h0, this]
    exact hx (tanh_injective h1)
  have ht2 : 0 < tanh x ^ 2 := by positivity
  rw [le_div_iff₀ (by positivity)]
  rw [div_add' _ _ _ hx2.ne', div_le_div_iff₀ hx2 ht2] at h
  nlinarith

/-- `tanh² x ≤ x²`, equivalently `sech² x ≥ 1 - x²`. Used in `lem:arity`
(`tanh_scalar.tex`) and `lem:rounding`. -/
theorem tanh_sq_le_sq (x : ℝ) : tanh x ^ 2 ≤ x ^ 2 := by
  refine (tanh_sq_le x).trans ?_
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]

/-- Termwise comparison behind `u coth u ≤ 1 + u²/3`. Auxiliary for `lem:nearcriticalgap`
(`tanh_rates.tex`). -/
theorem sinh_cosh_series_term_nonneg {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    0 ≤ u ^ 2 / 3 * (u ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) +
      u ^ (2 * (n + 1) + 1) / ((2 * (n + 1) + 1).factorial : ℝ) -
      u * (u ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ)) := by
  have hf1 : ((2 * (n + 1)).factorial : ℝ) = (2 * n + 2) * ((2 * n + 1).factorial : ℝ) := by
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Nat.factorial_succ]
    push_cast; ring
  have hf2 : ((2 * (n + 1) + 1).factorial : ℝ) =
      (2 * n + 3) * (2 * n + 2) * ((2 * n + 1).factorial : ℝ) := by
    rw [show 2 * (n + 1) + 1 = ((2 * n + 1) + 1) + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast; ring
  have hp1 : u ^ (2 * (n + 1) + 1) = u ^ (2 * n + 1) * u ^ 2 := by
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, pow_add]
  have hp2 : u ^ (2 * (n + 1)) = u ^ (2 * n + 1) * u := by
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, pow_succ]
  rw [hf1, hf2, hp1, hp2]
  have hF : 0 < ((2 * n + 1).factorial : ℝ) := by positivity
  have hU : 0 ≤ u ^ (2 * n + 1) * u ^ 2 := by positivity
  have key : u ^ 2 / 3 * (u ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) +
      u ^ (2 * n + 1) * u ^ 2 / ((2 * n + 3) * (2 * n + 2) * ((2 * n + 1).factorial : ℝ)) -
      u * (u ^ (2 * n + 1) * u / ((2 * n + 2) * ((2 * n + 1).factorial : ℝ))) =
      u ^ (2 * n + 1) * u ^ 2 / ((2 * n + 1).factorial : ℝ) *
        ((2 * n) / (3 * (2 * n + 3))) := by
    field_simp
    ring
  rw [key]
  positivity

/-- `u cosh u ≤ (1 + u²/3) sinh u` for `u ≥ 0`.
Paper: `lem:nearcriticalgap` (`tanh_rates.tex`), and `lem:arity` (`tanh_scalar.tex`). -/
theorem mul_cosh_le {u : ℝ} (hu : 0 ≤ u) : u * cosh u ≤ (1 + u ^ 2 / 3) * sinh u := by
  set b : ℕ → ℝ := fun n => u ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) with hb
  set c : ℕ → ℝ := fun n => u ^ (2 * n) / ((2 * n).factorial : ℝ) with hc
  have hS : HasSum b (sinh u) := hasSum_sinh u
  have hC : HasSum c (cosh u) := hasSum_cosh u
  have hS1 : HasSum (fun n => b (n + 1)) (sinh u - u) := by
    have := (hasSum_nat_add_iff' 1).mpr hS
    simpa [hb] using this
  have hC1 : HasSum (fun n => c (n + 1)) (cosh u - 1) := by
    have := (hasSum_nat_add_iff' 1).mpr hC
    simpa [hc] using this
  have hsum : HasSum (fun n => u ^ 2 / 3 * b n + b (n + 1) - u * c (n + 1))
      (u ^ 2 / 3 * sinh u + (sinh u - u) - u * (cosh u - 1)) :=
    ((hS.mul_left (u ^ 2 / 3)).add hS1).sub (hC1.mul_left u)
  have hnn : 0 ≤ u ^ 2 / 3 * sinh u + (sinh u - u) - u * (cosh u - 1) := by
    apply hsum.nonneg
    intro n
    exact sinh_cosh_series_term_nonneg hu n
  nlinarith [hnn]

/-- `u coth u ≤ 1 + u²/3` for `u > 0`. Paper: `lem:nearcriticalgap` (`tanh_rates.tex`). -/
theorem mul_coth_le {u : ℝ} (hu : 0 < u) : u / tanh u ≤ 1 + u ^ 2 / 3 := by
  have hs : 0 < sinh u := sinh_pos_iff.mpr hu
  have hc := cosh_pos u
  rw [tanh_eq_sinh_div_cosh, div_div_eq_mul_div, div_le_iff₀ hs]
  exact mul_cosh_le hu.le

/-- The upper reciprocal-square inequality `coth² u ≤ u⁻² + 1`: the right inequality of the
displayed pair `u⁻² + 2/3 ≤ coth² u ≤ u⁻² + 1` in the proof of the lower bound of
`thm:uniformchain` (`tanh_mean.tex`), used for `eq:chainrange` and `eq:tanhlower`. -/
theorem coth_sq_le {u : ℝ} (hu : u ≠ 0) : 1 / tanh u ^ 2 ≤ 1 / u ^ 2 + 1 := by
  have hs : sinh u ≠ 0 := by
    intro h; exact hu (sinh_eq_zero.mp h)
  have hs2 : 0 < sinh u ^ 2 := by positivity
  have hu2 : 0 < u ^ 2 := by positivity
  have hc := cosh_pos u
  have hsinh : u ^ 2 ≤ sinh u ^ 2 := by
    rcases le_or_gt 0 u with h | h
    · have := self_le_sinh_iff.mpr h
      nlinarith
    · have := sinh_le_self_iff.mpr h.le
      have h2 : sinh u ≤ 0 := sinh_nonpos_iff.mpr h.le
      nlinarith
  have hcs := cosh_sq' u
  rw [tanh_eq_sinh_div_cosh, div_pow, one_div_div, div_add_one hu2.ne',
    div_le_div_iff₀ hs2 hu2]
  nlinarith

/-! ### Elementary tanh facts -/

/-- `tanh` is monotone. Auxiliary for `lem:radius` and `lem:rounding` (`tanh_rates.tex`). -/
theorem tanh_le_tanh {x y : ℝ} (h : x ≤ y) : tanh x ≤ tanh y := by
  by_contra hlt
  have hlt : tanh y < tanh x := lt_of_not_ge hlt
  have := artanh_lt_artanh (neg_one_lt_tanh y) (tanh_lt_one x) hlt
  rw [artanh_tanh, artanh_tanh] at this
  linarith

/-- `tanh` is nonnegative on `[0, ∞)`. Auxiliary for `lem:radius` (`tanh_rates.tex`). -/
theorem tanh_nonneg_of_nonneg {x : ℝ} (h : 0 ≤ x) : 0 ≤ tanh x := by
  simpa using tanh_le_tanh h

/-- `tanh` is positive on `(0, ∞)`. Auxiliary for `lem:radius` (`tanh_rates.tex`). -/
theorem tanh_pos_of_pos {x : ℝ} (h : 0 < x) : 0 < tanh x := by
  rw [tanh_eq_sinh_div_cosh]
  exact div_pos (sinh_pos_iff.mpr h) (cosh_pos x)

/-- The derivative of `tanh` is `1 / cosh²`. Auxiliary for `lem:rounding` (`tanh_rates.tex`). -/
theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt tanh (1 / cosh x ^ 2) x := by
  have h := (hasDerivAt_sinh x).div (hasDerivAt_cosh x) (cosh_pos x).ne'
  have e : (sinh / cosh : ℝ → ℝ) = tanh := by
    funext y; rw [Pi.div_apply, tanh_eq_sinh_div_cosh]
  rw [e] at h
  convert h using 1
  have hc := cosh_pos x
  have := cosh_sq_sub_sinh_sq x
  field_simp
  linarith

/-! ### Radius decay -/

/-- The ideal reference radii `R_0 = 1`, `R_{j+1} = tanh (g R_j)` of Section `sec:cost`
(`tanh_rates.tex`). -/
noncomputable def idealRadius (g : ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => tanh (g * idealRadius g j)

/-- The comparison sequence `q_j = 3 / (2j + 3)` of Section `sec:cost` (`tanh_rates.tex`). -/
noncomputable def qSeq (j : ℕ) : ℝ := 3 / (2 * j + 3)

/-- The rational map `Φ_g(v) = g² v / (1 + (2/3) g² v)` of the proof of `lem:radius`,
written with `σ = g²`. -/
noncomputable def radiusMap (σ v : ℝ) : ℝ := σ * v / (1 + 2 / 3 * σ * v)

/-- The supercritical offset `A = (3/2)(1 - g⁻²)` of `eq:superradius`, written with
`σ = g²`. -/
noncomputable def radiusFixed (σ : ℝ) : ℝ := 3 / 2 * (1 - 1 / σ)

/-- `q_j > 0`. Auxiliary for `lem:radius` (`tanh_rates.tex`). -/
theorem qSeq_pos (j : ℕ) : 0 < qSeq j := by unfold qSeq; positivity

/-- `q_j ≤ 1`. Auxiliary for `lem:radius` and the call bound (`tanh_rates.tex`). -/
theorem qSeq_le_one (j : ℕ) : qSeq j ≤ 1 := by
  unfold qSeq
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

/-- The ideal radii are nonnegative. Auxiliary for `lem:radius` (`tanh_rates.tex`). -/
theorem idealRadius_nonneg {g : ℝ} (hg : 0 ≤ g) : ∀ j, 0 ≤ idealRadius g j
  | 0 => by simp [idealRadius]
  | j + 1 => tanh_nonneg_of_nonneg (mul_nonneg hg (idealRadius_nonneg hg j))

/-- The ideal radii are positive for `g > 0`. Auxiliary for `lem:rounding`
(`tanh_rates.tex`). -/
theorem idealRadius_pos {g : ℝ} (hg : 0 < g) : ∀ j, 0 < idealRadius g j
  | 0 => by simp [idealRadius]
  | j + 1 => tanh_pos_of_pos (mul_pos hg (idealRadius_pos hg j))

/-- The ideal radii are at most one. Auxiliary for `lem:rounding` (`tanh_rates.tex`). -/
theorem idealRadius_le_one (g : ℝ) : ∀ j, idealRadius g j ≤ 1
  | 0 => by simp [idealRadius]
  | j + 1 => (tanh_lt_one _).le

/-- The ideal radii decrease. Paper: `lem:rounding` (`tanh_rates.tex`), first line of the
proof. -/
theorem idealRadius_succ_le {g : ℝ} (hg : 0 ≤ g) : ∀ j, idealRadius g (j + 1) ≤ idealRadius g j
  | 0 => by simp only [idealRadius, mul_one]; exact (tanh_lt_one g).le
  | j + 1 => by
      show tanh (g * idealRadius g (j + 1)) ≤ tanh (g * idealRadius g j)
      exact tanh_le_tanh (mul_le_mul_of_nonneg_left (idealRadius_succ_le hg j) hg)

/-- Monotonicity of `Φ_g`. Paper: `lem:radius` (`tanh_rates.tex`). -/
theorem radiusMap_mono {σ v w : ℝ} (hs : 0 ≤ σ) (hv : 0 ≤ v) (hvw : v ≤ w) :
    radiusMap σ v ≤ radiusMap σ w := by
  have hw : 0 ≤ w := le_trans hv hvw
  have hdv : 0 < 1 + 2 / 3 * σ * v := by positivity
  have hdw : 0 < 1 + 2 / 3 * σ * w := by positivity
  unfold radiusMap
  rw [div_le_div_iff₀ hdv hdw]
  have hmul : σ * v ≤ σ * w := mul_le_mul_of_nonneg_left hvw hs
  nlinarith

/-- One radius step: `R_{j+1}² ≤ Φ_g(R_j²)`. Paper: `lem:radius` (`tanh_rates.tex`), from
`eq:cothradius`. -/
theorem tanh_sq_le_radiusMap (g R : ℝ) : tanh (g * R) ^ 2 ≤ radiusMap (g ^ 2) (R ^ 2) := by
  have h := tanh_sq_le (g * R)
  unfold radiusMap
  rw [mul_pow] at h
  calc tanh (g * R) ^ 2 ≤ g ^ 2 * R ^ 2 / (1 + 2 / 3 * (g ^ 2 * R ^ 2)) := h
    _ = g ^ 2 * R ^ 2 / (1 + 2 / 3 * g ^ 2 * R ^ 2) := by ring_nf

/-- `Φ_1(q_j) = q_{j+1}`, i.e. `q_{j+1} = q_j / (1 + 2q_j/3)`. Paper: `lem:radius`
(`tanh_rates.tex`). -/
theorem radiusMap_one_qSeq (j : ℕ) : radiusMap 1 (qSeq j) = qSeq (j + 1) := by
  unfold radiusMap qSeq
  push_cast
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  field_simp
  ring

/-- `Φ_g ≤ Φ_1` for `g ≤ 1`: monotonicity in the gain. Paper: `lem:radius` (`tanh_rates.tex`),
"monotonicity handles `g < 1`". -/
theorem radiusMap_le_one_of_le {σ v : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hv : 0 ≤ v) :
    radiusMap σ v ≤ radiusMap 1 v := by
  unfold radiusMap
  have h1 : 0 < 1 + 2 / 3 * σ * v := by positivity
  have h2 : 0 < 1 + 2 / 3 * 1 * v := by positivity
  rw [div_le_div_iff₀ h1 h2]
  have : σ * v ≤ v := by nlinarith
  nlinarith

/-- Critical and subcritical radius decay `R_j² ≤ q_j = 3/(2j+3)` for `0 ≤ g ≤ 1`.
Paper: `lem:radius` (`tanh_rates.tex`). -/
theorem idealRadius_sq_le {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    ∀ j, idealRadius g j ^ 2 ≤ qSeq j
  | 0 => by simp [idealRadius, qSeq]
  | j + 1 => by
      have ih := idealRadius_sq_le hg0 hg1 j
      have hR := sq_nonneg (idealRadius g j)
      have hg2 : g ^ 2 ≤ 1 := by nlinarith
      calc idealRadius g (j + 1) ^ 2 = tanh (g * idealRadius g j) ^ 2 := rfl
        _ ≤ radiusMap (g ^ 2) (idealRadius g j ^ 2) := tanh_sq_le_radiusMap _ _
        _ ≤ radiusMap 1 (idealRadius g j ^ 2) :=
            radiusMap_le_one_of_le (sq_nonneg g) hg2 hR
        _ ≤ radiusMap 1 (qSeq j) := radiusMap_mono zero_le_one hR ih
        _ = qSeq (j + 1) := radiusMap_one_qSeq j

/-- At criticality the reciprocal square grows by `2/3` per layer: `R_j⁻² ≥ 1 + 2j/3`.
Paper: `lem:radius` (`tanh_rates.tex`), the telescoped form at `g = 1`. -/
theorem one_add_le_inv_idealRadius_sq (j : ℕ) :
    1 + 2 / 3 * (j : ℝ) ≤ 1 / idealRadius 1 j ^ 2 := by
  have hpos := idealRadius_pos zero_lt_one j
  have h := idealRadius_sq_le zero_le_one le_rfl j
  have hR2 : 0 < idealRadius 1 j ^ 2 := by positivity
  rw [le_div_iff₀ hR2]
  unfold qSeq at h
  rw [le_div_iff₀ (by positivity)] at h
  nlinarith

/-- The exact shifted update of `Φ_g` around the offset `A`.
Paper: `lem:radius` (`tanh_rates.tex`), supercritical step. -/
theorem radiusMap_shift_identity {σ q : ℝ} (hs : 0 < σ) (hq : 0 ≤ q) :
    radiusMap σ (radiusFixed σ + q) - radiusFixed σ = q / (σ * (1 + 2 / 3 * q)) := by
  have hs0 : σ ≠ 0 := ne_of_gt hs
  have hqden : 1 + 2 / 3 * q ≠ 0 := by positivity
  have hden : 1 + 2 / 3 * σ * (radiusFixed σ + q) = σ * (1 + 2 / 3 * q) := by
    unfold radiusFixed
    field_simp
    ring
  have hden0 : 1 + 2 / 3 * σ * (radiusFixed σ + q) ≠ 0 := by
    rw [hden]
    exact mul_ne_zero hs0 hqden
  unfold radiusMap
  rw [hden]
  unfold radiusFixed
  field_simp
  ring

/-- Above criticality the shifted radius contracts at least as fast as the critical
comparison sequence. Paper: `lem:radius` (`tanh_rates.tex`). -/
theorem radiusMap_shift_bound {σ q : ℝ} (hs : 1 ≤ σ) (hq : 0 ≤ q) :
    radiusMap σ (radiusFixed σ + q) - radiusFixed σ ≤ q / (1 + 2 / 3 * q) := by
  have hspos : 0 < σ := by linarith
  rw [radiusMap_shift_identity hspos hq]
  have hd : 0 < 1 + 2 / 3 * q := by positivity
  rw [div_le_div_iff₀ (mul_pos hspos hd) hd]
  have hp := mul_nonneg hq (mul_nonneg (sub_nonneg.mpr hs) hd.le)
  nlinarith

/-- The offset `A = (3/2)(1 - g⁻²)` is nonnegative for `g ≥ 1`. Auxiliary for `eq:superradius`
(`tanh_rates.tex`). -/
theorem radiusFixed_nonneg {σ : ℝ} (hs : 1 ≤ σ) : 0 ≤ radiusFixed σ := by
  unfold radiusFixed
  have : 1 / σ ≤ 1 := by rw [div_le_one (by linarith)]; exact hs
  linarith

/-- Supercritical radius decay `R_j² ≤ (3/2)(1 - g⁻²) + q_j` for `g ≥ 1`.
Paper: `eq:superradius` in `lem:radius` (`tanh_rates.tex`), stated there for `1 ≤ g ≤ 2`. -/
theorem idealRadius_sq_le_super {g : ℝ} (hg : 1 ≤ g) :
    ∀ j, idealRadius g j ^ 2 ≤ radiusFixed (g ^ 2) + qSeq j
  | 0 => by
      have := radiusFixed_nonneg (show (1 : ℝ) ≤ g ^ 2 by nlinarith)
      simp [idealRadius, qSeq]
      linarith
  | j + 1 => by
      have ih := idealRadius_sq_le_super hg j
      have hσ : (1 : ℝ) ≤ g ^ 2 := by nlinarith
      have hR := sq_nonneg (idealRadius g j)
      have hA := radiusFixed_nonneg hσ
      have hq := (qSeq_pos j).le
      have hshift := radiusMap_shift_bound hσ hq
      have hqs : qSeq j / (1 + 2 / 3 * qSeq j) = qSeq (j + 1) := by
        rw [← radiusMap_one_qSeq]; unfold radiusMap; ring_nf
      calc idealRadius g (j + 1) ^ 2 = tanh (g * idealRadius g j) ^ 2 := rfl
        _ ≤ radiusMap (g ^ 2) (idealRadius g j ^ 2) := tanh_sq_le_radiusMap _ _
        _ ≤ radiusMap (g ^ 2) (radiusFixed (g ^ 2) + qSeq j) :=
            radiusMap_mono (by positivity) hR ih
        _ ≤ radiusFixed (g ^ 2) + qSeq (j + 1) := by linarith

/-! ### Rounding stability -/

/-- `tanh (g ·)` is `1`-Lipschitz above any positive point `y` with `tanh (g y) ≤ y`.
Paper: `lem:rounding` (`tanh_rates.tex`), the concavity step `f'(R_j) ≤ R_{j+1}/R_j ≤ 1`. -/
theorem tanh_sub_tanh_le {g x y : ℝ} (hg : 0 ≤ g) (hy : 0 < y) (hyx : y ≤ x)
    (hfix : tanh (g * y) ≤ y) : tanh (g * x) - tanh (g * y) ≤ x - y := by
  rcases eq_or_lt_of_le hyx with h | hlt
  · rw [h]; simp
  -- the derivative at `y` is at most one
  have hgy : g / cosh (g * y) ^ 2 ≤ 1 := by
    have hv : 0 ≤ g * y := mul_nonneg hg hy.le
    have hc := cosh_pos (g * y)
    have hsc : g * y ≤ sinh (g * y) * cosh (g * y) := by
      have := self_le_sinh_iff.mpr (show 0 ≤ 2 * (g * y) by linarith)
      rw [sinh_two_mul] at this
      linarith
    have ht : tanh (g * y) = sinh (g * y) / cosh (g * y) := tanh_eq_sinh_div_cosh _
    rw [div_le_one (by positivity)]
    have h1 : g * y ≤ cosh (g * y) ^ 2 * tanh (g * y) := by
      rw [ht]; field_simp; nlinarith
    have h2 : cosh (g * y) ^ 2 * tanh (g * y) ≤ cosh (g * y) ^ 2 * y :=
      mul_le_mul_of_nonneg_left hfix (by positivity)
    nlinarith
  have hderiv : ∀ t ∈ Set.Ioo y x,
      HasDerivAt (fun t => tanh (g * t) - t) (g * (1 / cosh (g * t) ^ 2) - 1) t := by
    intro t _
    have h1 : HasDerivAt (fun t => g * t) g t := by
      simpa using (hasDerivAt_id t).const_mul g
    have h2 := (hasDerivAt_tanh (g * t)).comp t h1
    have h3 : HasDerivAt (fun t => tanh (g * t) - t) (1 / cosh (g * t) ^ 2 * g - 1) t :=
      h2.sub (hasDerivAt_id t)
    convert h3 using 1
    ring
  have hcont : ContinuousOn (fun t => tanh (g * t) - t) (Set.Icc y x) := by
    apply Continuous.continuousOn
    have : Continuous tanh := by
      have e : tanh = fun y => sinh y / cosh y := funext tanh_eq_sinh_div_cosh
      rw [e]
      exact continuous_sinh.div continuous_cosh (fun y => (cosh_pos y).ne')
    fun_prop
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope _ _ hlt hcont hderiv
  have hcy : cosh (g * y) ^ 2 ≤ cosh (g * c) ^ 2 := by
    have : cosh (g * y) ≤ cosh (g * c) := by
      rw [cosh_le_cosh, abs_of_nonneg (mul_nonneg hg hy.le),
        abs_of_nonneg (mul_nonneg hg (by linarith [hc.1]))]
      exact mul_le_mul_of_nonneg_left hc.1.le hg
    exact pow_le_pow_left₀ (cosh_pos _).le this 2
  have hdc : g * (1 / cosh (g * c) ^ 2) - 1 ≤ 0 := by
    have hpos := cosh_pos (g * y)
    have : g * (1 / cosh (g * c) ^ 2) ≤ g / cosh (g * y) ^ 2 := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_left hg (by positivity) hcy
    linarith
  rw [hslope] at hdc
  have hxy : 0 < x - y := by linarith
  have := (div_nonpos_iff.mp hdc)
  rcases this with ⟨_, h⟩ | ⟨h, _⟩
  · linarith
  · linarith

/-- Error propagation for stored radii obeying `eq:rounded`:
`0 ≤ r_j - R_j ≤ 3 j ε`. Paper: `lem:rounding` (`tanh_rates.tex`). -/
theorem rounding_error {g ε : ℝ} (hg : 0 ≤ g) (hε : 0 ≤ ε) (r : ℕ → ℝ) (hr0 : r 0 = 1)
    (hlow : ∀ j, tanh (g * r j) + 2 * ε ≤ r (j + 1))
    (hup : ∀ j, r (j + 1) ≤ tanh (g * r j) + 3 * ε) :
    ∀ j, 0 ≤ r j - idealRadius g j ∧ r j - idealRadius g j ≤ 3 * j * ε := by
  intro j
  induction j with
  | zero => simp [hr0, idealRadius]
  | succ j ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hmono : tanh (g * idealRadius g j) ≤ tanh (g * r j) :=
        tanh_le_tanh (mul_le_mul_of_nonneg_left (by linarith) hg)
      have hlip : tanh (g * r j) - tanh (g * idealRadius g j) ≤ r j - idealRadius g j := by
        rcases eq_or_lt_of_le hg with h0 | hpos
        · subst h0; simp; linarith
        · exact tanh_sub_tanh_le hg (idealRadius_pos hpos j) (by linarith)
            (idealRadius_succ_le hg j)
      have e : idealRadius g (j + 1) = tanh (g * idealRadius g j) := rfl
      constructor
      · rw [e]; linarith [hlow j]
      · rw [e]; push_cast; linarith [hup j]

/-- `tanh 2 < 40/41`, from `e < 3`. Paper: `lem:rounding` (`tanh_rates.tex`). -/
theorem tanh_two_lt : tanh 2 < 40 / 41 := by
  have he : exp 1 < 3 := lt_trans exp_one_lt_d9 (by norm_num)
  have h4 : exp 4 < 81 := by
    have : exp 4 = exp 1 ^ 4 := by rw [← exp_nat_mul]; norm_num
    rw [this]
    have h0 := exp_pos 1
    calc exp 1 ^ 4 < 3 ^ 4 := by gcongr
      _ = 81 := by norm_num
  have hp := exp_pos 4
  rw [tanh_eq, show exp 2 = exp 4 / exp 2 by rw [← exp_sub]; norm_num, exp_neg]
  have h2 := exp_pos 2
  have e2 : exp 2 * exp 2 = exp 4 := by rw [← exp_add]; norm_num
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  field_simp
  nlinarith

/-- Stored radii stay in `(0, 1]` for reference gain `g ≤ 2` and `0 < ε ≤ 1/1600`.
Paper: `lem:rounding` (`tanh_rates.tex`). -/
theorem stored_radius_mem {g ε : ℝ} (hg0 : 0 ≤ g) (hg2 : g ≤ 2) (hε0 : 0 < ε)
    (hε : ε ≤ 1 / 1600) (r : ℕ → ℝ) (hr0 : r 0 = 1)
    (hlow : ∀ j, tanh (g * r j) + 2 * ε ≤ r (j + 1))
    (hup : ∀ j, r (j + 1) ≤ tanh (g * r j) + 3 * ε) :
    ∀ j, 0 < r j ∧ r j ≤ 1 := by
  intro j
  induction j with
  | zero => simp [hr0]
  | succ j ih =>
      obtain ⟨h0, h1⟩ := ih
      have hnn := tanh_nonneg_of_nonneg (mul_nonneg hg0 h0.le)
      have hle : g * r j ≤ 2 := by nlinarith
      have ht := tanh_le_tanh hle
      have h2 := tanh_two_lt
      constructor
      · linarith [hlow j]
      · linarith [hup j]

/-- The precision choice `P = b + 4⌈log₂(D+1)⌉ + 8` of `eq:precision` gives
`ε = 2^{-P} ≤ 1 / (100 (D+1)⁴)`. Paper: `lem:rounding` (`tanh_rates.tex`). -/
theorem precision_eps_le (b D : ℕ) :
    1 / (2 : ℝ) ^ (b + 4 * Nat.clog 2 (D + 1) + 8) ≤ 1 / (100 * ((D : ℝ) + 1) ^ 4) := by
  have hc : D + 1 ≤ 2 ^ Nat.clog 2 (D + 1) := Nat.le_pow_clog (by norm_num) _
  have hc' : ((D : ℝ) + 1) ≤ (2 : ℝ) ^ Nat.clog 2 (D + 1) := by exact_mod_cast hc
  have h4 : ((D : ℝ) + 1) ^ 4 ≤ (2 : ℝ) ^ (4 * Nat.clog 2 (D + 1)) := by
    rw [pow_mul']
    exact pow_le_pow_left₀ (by positivity) hc' 4
  have hb : (1 : ℝ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  have hpow : (2 : ℝ) ^ (b + 4 * Nat.clog 2 (D + 1) + 8) =
      2 ^ b * 2 ^ (4 * Nat.clog 2 (D + 1)) * 256 := by
    rw [pow_add, pow_add]; norm_num
  apply one_div_le_one_div_of_le (by positivity)
  rw [hpow]
  have h0 : (0 : ℝ) ≤ 2 ^ (4 * Nat.clog 2 (D + 1)) := by positivity
  nlinarith

/-- `D² / (D+1)⁴ ≤ 1/16`, from `D / (D+1)² ≤ 1/4`. Paper: `lem:rounding`
(`tanh_rates.tex`). -/
theorem depth_square_ratio_le (d : ℝ) (hd : 0 ≤ d) : d ^ 2 / (d + 1) ^ 4 ≤ 1 / 16 := by
  have hden : 0 < (d + 1) ^ 4 := by positivity
  rw [div_le_iff₀ hden]
  have hprod : 0 ≤ (d - 1) ^ 2 * ((d + 1) ^ 2 + 4 * d) := by positivity
  nlinarith

/-- The total log perturbation `D · (29/3) · 4 · (6 D ε) ≤ 29/200` when
`ε ≤ 1 / (100 (D+1)⁴)`. Paper: `lem:rounding` (`tanh_rates.tex`). -/
theorem rounding_log_budget (D : ℕ) {ε : ℝ}
    (hε : ε ≤ 1 / (100 * ((D : ℝ) + 1) ^ 4)) :
    (D : ℝ) * (29 / 3) * 4 * (6 * D * ε) ≤ 29 / 200 := by
  have hd : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hratio := depth_square_ratio_le (D : ℝ) hd
  have hden : 0 < ((D : ℝ) + 1) ^ 4 := by positivity
  have h1 : (D : ℝ) ^ 2 * ε ≤ (D : ℝ) ^ 2 / (100 * ((D : ℝ) + 1) ^ 4) := by
    calc (D : ℝ) ^ 2 * ε ≤ (D : ℝ) ^ 2 * (1 / (100 * ((D : ℝ) + 1) ^ 4)) :=
          mul_le_mul_of_nonneg_left hε (sq_nonneg _)
      _ = (D : ℝ) ^ 2 / (100 * ((D : ℝ) + 1) ^ 4) := by ring
  have h2 : (D : ℝ) ^ 2 / (100 * ((D : ℝ) + 1) ^ 4) ≤ 1 / 1600 := by
    rw [show (D : ℝ) ^ 2 / (100 * ((D : ℝ) + 1) ^ 4) = (D : ℝ) ^ 2 / ((D : ℝ) + 1) ^ 4 / 100
      by field_simp]
    linarith
  nlinarith

/-- The offspring exponent `φ(v) = 5v/3 + v²` of `lem:offspring`, as a function of the squared
row radius. -/
noncomputable def phiCost (v : ℝ) : ℝ := 5 / 3 * v + v ^ 2

/-- `φ` is monotone on `[0, ∞)`. Auxiliary for the call bound (`tanh_rates.tex`). -/
theorem phiCost_mono {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) : phiCost v ≤ phiCost w := by
  unfold phiCost; nlinarith

/-- On `[0, 4]` the derivative of `φ` is at most `29/3`. Paper: `lem:rounding`
(`tanh_rates.tex`). -/
theorem phiCost_sub_le {v w : ℝ} (hwv : w ≤ v) (hv : v ≤ 4) :
    phiCost v - phiCost w ≤ 29 / 3 * (v - w) := by
  unfold phiCost; nlinarith

/-- Replacing ideal radii by stored radii changes the logarithm of any offspring product by at
most `29/200`, for every reference gain `0 ≤ g ≤ 2`. The hypotheses on the stored radii are
`eq:rounded`, `r_0 = 1`, and the precision bound produced by `eq:precision`.
Paper: `lem:rounding` (`tanh_rates.tex`). -/
theorem rounding_log_perturbation {g ε : ℝ} (hg0 : 0 ≤ g) (hg2 : g ≤ 2) (hε0 : 0 < ε)
    (D : ℕ) (hε : ε ≤ 1 / (100 * ((D : ℝ) + 1) ^ 4)) (r : ℕ → ℝ) (hr0 : r 0 = 1)
    (hlow : ∀ j, tanh (g * r j) + 2 * ε ≤ r (j + 1))
    (hup : ∀ j, r (j + 1) ≤ tanh (g * r j) + 3 * ε) (k : ℕ) :
    ∑ j ∈ Finset.Ico k D, phiCost ((g * r j) ^ 2) ≤
      29 / 200 + ∑ j ∈ Finset.Ico k D, phiCost ((g * idealRadius g j) ^ 2) := by
  rcases Nat.eq_zero_or_pos D with hD0 | hD
  · subst hD0; simp only [Finset.Ico_eq_empty_of_le (Nat.zero_le k), Finset.sum_empty]
    norm_num
  have hε1600 : ε ≤ 1 / 1600 := by
    refine hε.trans ?_
    apply one_div_le_one_div_of_le (by norm_num)
    have h2 : (2 : ℝ) ≤ (D : ℝ) + 1 := by
      have : (1 : ℝ) ≤ D := by exact_mod_cast hD
      linarith
    have : (16 : ℝ) ≤ ((D : ℝ) + 1) ^ 4 := by
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ ((D : ℝ) + 1) ^ 4 := pow_le_pow_left₀ (by norm_num) h2 4
    linarith
  have herr := rounding_error hg0 hε0.le r hr0 hlow hup
  have hmem := stored_radius_mem hg0 hg2 hε0 hε1600 r hr0 hlow hup
  have hterm : ∀ j ∈ Finset.Ico k D, phiCost ((g * r j) ^ 2) ≤
      phiCost ((g * idealRadius g j) ^ 2) + 29 / 3 * (4 * (6 * D * ε)) := by
    intro j hj
    have hjD : (j : ℝ) ≤ D := by exact_mod_cast (Finset.mem_Ico.mp hj).2.le
    obtain ⟨e1, e2⟩ := herr j
    obtain ⟨m1, m2⟩ := hmem j
    have hR0 := idealRadius_nonneg hg0 j
    have hRr : idealRadius g j ≤ r j := by linarith
    have hsq : r j ^ 2 - idealRadius g j ^ 2 ≤ 6 * D * ε := by
      have : r j ^ 2 - idealRadius g j ^ 2 = (r j - idealRadius g j) * (r j + idealRadius g j)
        := by ring
      rw [this]
      have h3 : r j + idealRadius g j ≤ 2 := by linarith
      calc (r j - idealRadius g j) * (r j + idealRadius g j) ≤ (3 * j * ε) * 2 :=
            mul_le_mul e2 h3 (by linarith) (by positivity)
        _ ≤ 6 * D * ε := by nlinarith
    have hg2' : g ^ 2 ≤ 4 := by nlinarith
    have hv : (g * r j) ^ 2 ≤ 4 := by
      rw [mul_pow]; nlinarith [sq_nonneg (r j), pow_le_one₀ m1.le m2 (n := 2)]
    have hw : (g * idealRadius g j) ^ 2 ≤ (g * r j) ^ 2 := by
      apply pow_le_pow_left₀ (mul_nonneg hg0 hR0)
      exact mul_le_mul_of_nonneg_left hRr hg0
    have hdiff : (g * r j) ^ 2 - (g * idealRadius g j) ^ 2 ≤ 4 * (6 * D * ε) := by
      rw [mul_pow, mul_pow, ← mul_sub]
      apply mul_le_mul hg2' hsq (by nlinarith) (by norm_num)
    have := phiCost_sub_le hw hv
    nlinarith
  calc ∑ j ∈ Finset.Ico k D, phiCost ((g * r j) ^ 2)
      ≤ ∑ j ∈ Finset.Ico k D, (phiCost ((g * idealRadius g j) ^ 2) +
          29 / 3 * (4 * (6 * D * ε))) := Finset.sum_le_sum hterm
    _ = ∑ j ∈ Finset.Ico k D, phiCost ((g * idealRadius g j) ^ 2) +
          (Finset.Ico k D).card * (29 / 3 * (4 * (6 * D * ε))) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 29 / 200 + ∑ j ∈ Finset.Ico k D, phiCost ((g * idealRadius g j) ^ 2) := by
        have hcard : ((Finset.Ico k D).card : ℝ) ≤ D := by
          rw [Nat.card_Ico]; exact_mod_cast Nat.sub_le D k
        have hbudget := rounding_log_budget D hε
        have hnn : 0 ≤ 29 / 3 * (4 * (6 * (D : ℝ) * ε)) := by positivity
        nlinarith

/-! ### The call bound at criticality -/

/-- Telescoping over `Ico`. Auxiliary for `eq:qsums` (`tanh_rates.tex`). -/
theorem sum_Ico_telescope (f : ℕ → ℝ) {k D : ℕ} (h : k ≤ D) :
    ∑ j ∈ Finset.Ico k D, (f j - f (j + 1)) = f k - f D := by
  induction D, h using Nat.le_induction with
  | base => simp
  | succ D hkD ih => rw [Finset.sum_Ico_succ_top hkD, ih]; ring

/-- `q_j ≤ (3/2) log((j+2)/(j+1))`, the midpoint convexity estimate for `1/x`.
Paper: `eq:qsums` (`tanh_rates.tex`). -/
theorem qSeq_le_log (j : ℕ) :
    qSeq j ≤ 3 / 2 * (log ((j : ℝ) + 2) - log ((j : ℝ) + 1)) := by
  have ha : (0 : ℝ) < j + 1 := by positivity
  have hs := Real.hasSum_log_one_add_inv ha
  have h0 := le_hasSum hs 0 (fun i _ => by positivity)
  have e : 1 + ((j : ℝ) + 1)⁻¹ = ((j : ℝ) + 2) / ((j : ℝ) + 1) := by field_simp; ring
  rw [e, log_div (by positivity) (by positivity)] at h0
  unfold qSeq
  have e2 : (2 : ℝ) * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * (1 / (2 * ((j : ℝ) + 1) + 1)) ^ (2 * 0 + 1)
      = 2 / (2 * j + 3) := by
    push_cast; field_simp; ring
  rw [e2] at h0
  have e3 : (3 : ℝ) / (2 * j + 3) = 3 / 2 * (2 / (2 * j + 3)) := by field_simp
  rw [e3]
  linarith

/-- `Σ_{j=k}^{D-1} q_j ≤ (3/2) log((D+1)/(k+1))`. Paper: `eq:qsums` (`tanh_rates.tex`). -/
theorem sum_qSeq_le {k D : ℕ} (h : k ≤ D) :
    ∑ j ∈ Finset.Ico k D, qSeq j ≤ 3 / 2 * log (((D : ℝ) + 1) / ((k : ℝ) + 1)) := by
  have htel := sum_Ico_telescope (fun j => -log ((j : ℝ) + 1)) h
  calc ∑ j ∈ Finset.Ico k D, qSeq j
      ≤ ∑ j ∈ Finset.Ico k D, 3 / 2 * (-log ((j : ℝ) + 1) - -log (((j + 1 : ℕ) : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro j _
        have := qSeq_le_log j
        push_cast
        rw [show (j : ℝ) + 1 + 1 = j + 2 by ring]
        linarith
    _ = 3 / 2 * (log ((D : ℝ) + 1) - log ((k : ℝ) + 1)) := by
        rw [← Finset.mul_sum, htel]; ring
    _ = 3 / 2 * log (((D : ℝ) + 1) / ((k : ℝ) + 1)) := by
        rw [log_div (by positivity) (by positivity)]

/-- `Σ_{j=k}^{D-1} q_j² ≤ 9 / (4(k+1))`. Paper: `eq:qsums` (`tanh_rates.tex`). -/
theorem sum_qSeq_sq_le {k D : ℕ} (h : k ≤ D) :
    ∑ j ∈ Finset.Ico k D, qSeq j ^ 2 ≤ 9 / (4 * ((k : ℝ) + 1)) := by
  have htel := sum_Ico_telescope (fun j => 9 / 4 * (1 / ((j : ℝ) + 1))) h
  calc ∑ j ∈ Finset.Ico k D, qSeq j ^ 2
      ≤ ∑ j ∈ Finset.Ico k D,
          (9 / 4 * (1 / ((j : ℝ) + 1)) - 9 / 4 * (1 / (((j + 1 : ℕ) : ℝ) + 1))) := by
        apply Finset.sum_le_sum
        intro j _
        unfold qSeq
        push_cast
        have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        rw [div_pow, show 9 / 4 * (1 / ((j : ℝ) + 1)) - 9 / 4 * (1 / ((j : ℝ) + 1 + 1)) =
          9 / (4 * ((j + 1) * (j + 2))) by field_simp; ring]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    _ = 9 / 4 * (1 / ((k : ℝ) + 1)) - 9 / 4 * (1 / ((D : ℝ) + 1)) := htel
    _ ≤ 9 / (4 * ((k : ℝ) + 1)) := by
        have : 0 ≤ 9 / 4 * (1 / ((D : ℝ) + 1)) := by positivity
        rw [show 9 / (4 * ((k : ℝ) + 1)) = 9 / 4 * (1 / ((k : ℝ) + 1)) by field_simp]
        linarith

/-- `exp ((5/2) log y) = y² √y`. Auxiliary for the call bound of `thm:upper`
(`tanh_rates.tex`). -/
theorem exp_five_halves_log {y : ℝ} (hy : 0 < y) : exp (5 / 2 * log y) = y ^ 2 * √y := by
  rw [sqrt_eq_rpow, rpow_def_of_pos hy]
  have h2 : y ^ 2 = exp (2 * log y) := by
    rw [show (2 : ℝ) * log y = ((2 : ℕ) : ℝ) * log y by norm_num, exp_nat_mul, exp_log hy]
  rw [h2, ← exp_add]
  ring_nf

/-- The terms `(k+1)^{-5/2}` of the generation sum have total at most `5/3`.
Paper: proof of the call bound in `thm:upper` (`tanh_rates.tex`), "`Σ_{j≥1} j^{-5/2} ≤ 5/3`". -/
theorem sum_inv_pow_five_halves_le (D : ℕ) :
    ∑ k ∈ Finset.range D, 1 / (((k : ℝ) + 1) ^ 2 * √((k : ℝ) + 1)) ≤ 5 / 3 := by
  set t : ℕ → ℝ := fun k => 1 / (((k : ℝ) + 1) ^ 2 * √((k : ℝ) + 1)) with ht
  have t0 : t 0 = 1 := by simp [ht]
  have t1 : t 1 ≤ 1 / 5 := by
    simp only [ht]
    norm_num
    have hs : (5 : ℝ) / 4 ≤ √2 := by
      rw [le_sqrt (by norm_num) (by norm_num)]; norm_num
    calc (√2)⁻¹ * (1 / 4) ≤ (5 / 4)⁻¹ * (1 / 4) := by gcongr
      _ = 1 / 5 := by norm_num
  have tk : ∀ k, 2 ≤ k → t k ≤ 2 / 3 * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) := by
    intro k hk
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hs : (3 : ℝ) / 2 ≤ √((k : ℝ) + 1) := by
      rw [le_sqrt (by norm_num) (by positivity)]; nlinarith
    simp only [ht]
    rw [show 2 / 3 * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) = 2 / (3 * (k * (k + 1))) by
      field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have key : ∀ D, 2 ≤ D → ∑ k ∈ Finset.range D, t k ≤ 6 / 5 + 2 / 3 * (1 / 2 - 1 / (D : ℝ)) := by
    intro D hD
    induction D, hD using Nat.le_induction with
    | base =>
        rw [Finset.sum_range_succ, Finset.sum_range_one, t0]
        norm_num
        linarith
    | succ D hD ih =>
        rw [Finset.sum_range_succ]
        have := tk D hD
        push_cast
        linarith
  rcases lt_or_ge D 2 with hD | hD
  · interval_cases D
    · simp only [Finset.range_zero, Finset.sum_empty]; norm_num
    · simp [t0]; norm_num
  · have h := key D hD
    have : (0 : ℝ) ≤ 1 / (D : ℝ) := by positivity
    linarith

/-- The generation factor: `exp (29/200 + Σ_{j=k}^{D-1} φ(q_j)) ≤ e³ ((D+1)/(k+1))^{5/2}`.
Paper: proof of the call bound in `thm:upper` (`tanh_rates.tex`). -/
theorem generation_factor_le {k D : ℕ} (h : k ≤ D) :
    exp (29 / 200 + ∑ j ∈ Finset.Ico k D, phiCost (qSeq j)) ≤
      exp 3 * ((((D : ℝ) + 1) / ((k : ℝ) + 1)) ^ 2 * √(((D : ℝ) + 1) / ((k : ℝ) + 1))) := by
  have h1 := sum_qSeq_le h
  have h2 := sum_qSeq_sq_le h
  have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have h3 : 9 / (4 * ((k : ℝ) + 1)) ≤ 9 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hsum : ∑ j ∈ Finset.Ico k D, phiCost (qSeq j) =
      5 / 3 * ∑ j ∈ Finset.Ico k D, qSeq j + ∑ j ∈ Finset.Ico k D, qSeq j ^ 2 := by
    unfold phiCost; rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hy : 0 < ((D : ℝ) + 1) / ((k : ℝ) + 1) := by positivity
  rw [← exp_five_halves_log hy, ← exp_add]
  apply exp_le_exp.mpr
  rw [hsum]
  linarith

/-- The call bound `E N_calls ≤ 80 (D+1)²` of `eq:maincall`, starting from the generation
bound `eq:generalcost`. Here `S k` is the exponent of the generation-`k` offspring product, the
hypothesis `hx` is the conclusion of `lem:rounding` combined with `lem:radius` (see
`maincall_critical`), and `rD ≤ 2/√(D+1)` is the final-radius bound of `lem:rounding`.
Paper: `thm:upper` (`tanh_model.tex`), proof of the call bound (`tanh_rates.tex`), with
`eq:generalcost` and `eq:qsums`. -/
theorem call_bound_of_exponents (D : ℕ) (rD : ℝ) (S : ℕ → ℝ)
    (hrD : rD ≤ 2 / √((D : ℝ) + 1))
    (hx : ∀ k ≤ D, S k ≤ 29 / 200 + ∑ j ∈ Finset.Ico k D, phiCost (qSeq j)) :
    1 + rD * ∑ k ∈ Finset.range D, exp (S k) ≤ 80 * ((D : ℝ) + 1) ^ 2 := by
  have hD1 : (1 : ℝ) ≤ (D : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) D]
  have hsD : 0 < √((D : ℝ) + 1) := sqrt_pos.mpr (by positivity)
  have he3 : exp 3 < 21 := by
    have he : exp 1 < 2.72 := lt_trans exp_one_lt_d9 (by norm_num)
    have : exp 3 = exp 1 ^ 3 := by rw [← exp_nat_mul]; norm_num
    rw [this]
    have h0 := exp_pos 1
    calc exp 1 ^ 3 < 2.72 ^ 3 := by gcongr
      _ < 21 := by norm_num
  have hterm : ∀ k ∈ Finset.range D, rD * exp (S k) ≤
      2 * exp 3 * ((D : ℝ) + 1) ^ 2 * (1 / (((k : ℝ) + 1) ^ 2 * √((k : ℝ) + 1))) := by
    intro k hk
    have hkD : k ≤ D := (Finset.mem_range.mp hk).le
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hsk : 0 < √((k : ℝ) + 1) := sqrt_pos.mpr hk1
    have hg := generation_factor_le hkD
    have hexp : exp (S k) ≤ exp (29 / 200 + ∑ j ∈ Finset.Ico k D, phiCost (qSeq j)) :=
      exp_le_exp.mpr (hx k hkD)
    rw [sqrt_div (by positivity)] at hg
    calc rD * exp (S k)
        ≤ 2 / √((D : ℝ) + 1) * (exp 3 * ((((D : ℝ) + 1) / ((k : ℝ) + 1)) ^ 2 *
            (√((D : ℝ) + 1) / √((k : ℝ) + 1)))) :=
          mul_le_mul hrD (hexp.trans hg) (exp_pos _).le (by positivity)
      _ = 2 * exp 3 * ((D : ℝ) + 1) ^ 2 * (1 / (((k : ℝ) + 1) ^ 2 * √((k : ℝ) + 1))) := by
          field_simp
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have h53 := sum_inv_pow_five_halves_le D
  have hpos : 0 ≤ 2 * exp 3 * ((D : ℝ) + 1) ^ 2 := by positivity
  have hfin : 2 * exp 3 * ((D : ℝ) + 1) ^ 2 *
      ∑ k ∈ Finset.range D, 1 / (((k : ℝ) + 1) ^ 2 * √((k : ℝ) + 1)) ≤
      2 * exp 3 * ((D : ℝ) + 1) ^ 2 * (5 / 3) := mul_le_mul_of_nonneg_left h53 hpos
  have hD2 : (1 : ℝ) ≤ ((D : ℝ) + 1) ^ 2 := by nlinarith
  nlinarith

/-- The call bound in terms of the scaled squared radii `x j = (g r_j)²`.
Paper: `thm:upper` (`tanh_model.tex`), proof of the call bound (`tanh_rates.tex`). -/
theorem call_bound_of_generation (D : ℕ) (rD : ℝ) (x : ℕ → ℝ)
    (hrD : rD ≤ 2 / √((D : ℝ) + 1))
    (hx : ∀ k ≤ D, ∑ j ∈ Finset.Ico k D, phiCost (x j) ≤
      29 / 200 + ∑ j ∈ Finset.Ico k D, phiCost (qSeq j)) :
    1 + rD * ∑ k ∈ Finset.range D, exp (∑ j ∈ Finset.Ico k D, phiCost (x j)) ≤
      80 * ((D : ℝ) + 1) ^ 2 :=
  call_bound_of_exponents D rD (fun k => ∑ j ∈ Finset.Ico k D, phiCost (x j)) hrD hx

/-- The final stored radius at reference gain `g ≤ 1` satisfies `r_D ≤ 2/√(D+1)`.
Paper: `lem:rounding` (`tanh_rates.tex`), first final-radius bound. -/
theorem final_radius_le {g ε : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hε0 : 0 ≤ ε) (D : ℕ)
    (hε : ε ≤ 1 / (100 * ((D : ℝ) + 1) ^ 4)) (r : ℕ → ℝ) (hr0 : r 0 = 1)
    (hlow : ∀ j, tanh (g * r j) + 2 * ε ≤ r (j + 1))
    (hup : ∀ j, r (j + 1) ≤ tanh (g * r j) + 3 * ε) :
    r D ≤ 2 / √((D : ℝ) + 1) := by
  have herr := (rounding_error hg0 hε0 r hr0 hlow hup D).2
  have hR := idealRadius_sq_le hg0 hg1 D
  have hR0 := idealRadius_nonneg hg0 D
  have hd : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hs := sqrt_pos.mpr (show (0 : ℝ) < (D : ℝ) + 1 by positivity)
  have hss : √((D : ℝ) + 1) ^ 2 = (D : ℝ) + 1 := sq_sqrt (by positivity)
  rw [le_div_iff₀ hs]
  -- the ideal part
  have h1 : (idealRadius g D * √((D : ℝ) + 1)) ^ 2 ≤ 3 / 2 := by
    rw [mul_pow, hss]
    unfold qSeq at hR
    rw [le_div_iff₀ (by positivity)] at hR
    nlinarith
  have h1' : idealRadius g D * √((D : ℝ) + 1) ≤ 5 / 4 := by
    nlinarith [mul_nonneg hR0 hs.le]
  -- the rounding part
  have hsle : √((D : ℝ) + 1) ≤ (D : ℝ) + 1 := by
    rw [sqrt_le_left (by positivity)]; nlinarith
  have hden : 0 < ((D : ℝ) + 1) ^ 4 := by positivity
  have h2 : 3 * D * ε * √((D : ℝ) + 1) ≤ 3 / 100 := by
    have hεD : ε * ((D : ℝ) + 1) ^ 4 ≤ 1 / 100 := by
      calc ε * ((D : ℝ) + 1) ^ 4 ≤ 1 / (100 * ((D : ℝ) + 1) ^ 4) * ((D : ℝ) + 1) ^ 4 :=
            mul_le_mul_of_nonneg_right hε hden.le
        _ = 1 / 100 := by field_simp
    have hDle : (D : ℝ) * √((D : ℝ) + 1) ≤ ((D : ℝ) + 1) ^ 4 := by
      have h3 : (D : ℝ) * √((D : ℝ) + 1) ≤ ((D : ℝ) + 1) * ((D : ℝ) + 1) :=
        mul_le_mul (by linarith) hsle hs.le (by positivity)
      have h4 : ((D : ℝ) + 1) ^ 2 ≤ ((D : ℝ) + 1) ^ 4 :=
        pow_le_pow_right₀ (by linarith) (by norm_num)
      nlinarith
    nlinarith
  have hrD : r D ≤ idealRadius g D + 3 * D * ε := by linarith
  calc r D * √((D : ℝ) + 1) ≤ (idealRadius g D + 3 * D * ε) * √((D : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hrD hs.le
    _ = idealRadius g D * √((D : ℝ) + 1) + 3 * D * ε * √((D : ℝ) + 1) := by ring
    _ ≤ 2 := by linarith

/-- The call bound `E N_calls ≤ 80 (D+1)²` of `eq:maincall` for reference gain `0 ≤ g ≤ 1`,
from the generation bound `eq:generalcost` with stored radii obeying `eq:rounded` and the
precision bound of `eq:precision`. The left side is the right side of `eq:generalcost` (that
inequality is not derived here).
Paper: `thm:upper` (`tanh_model.tex`), `eq:maincall`; proof in `tanh_rates.tex`. -/
theorem maincall_critical {g ε : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hε0 : 0 < ε) (D : ℕ)
    (hε : ε ≤ 1 / (100 * ((D : ℝ) + 1) ^ 4)) (r : ℕ → ℝ) (hr0 : r 0 = 1)
    (hlow : ∀ j, tanh (g * r j) + 2 * ε ≤ r (j + 1))
    (hup : ∀ j, r (j + 1) ≤ tanh (g * r j) + 3 * ε) :
    1 + r D * ∑ k ∈ Finset.range D,
        exp (∑ j ∈ Finset.Ico k D, (5 / 3 * (g * r j) ^ 2 + (g * r j) ^ 4)) ≤
      80 * ((D : ℝ) + 1) ^ 2 := by
  have hx : ∀ k ≤ D, ∑ j ∈ Finset.Ico k D, phiCost ((g * r j) ^ 2) ≤
      29 / 200 + ∑ j ∈ Finset.Ico k D, phiCost (qSeq j) := by
    intro k _
    have hp := rounding_log_perturbation hg0 (by linarith) hε0 D hε r hr0 hlow hup k
    have hq : ∑ j ∈ Finset.Ico k D, phiCost ((g * idealRadius g j) ^ 2) ≤
        ∑ j ∈ Finset.Ico k D, phiCost (qSeq j) := by
      apply Finset.sum_le_sum
      intro j _
      apply phiCost_mono (sq_nonneg _)
      have hR := idealRadius_sq_le hg0 hg1 j
      have hR0 := idealRadius_nonneg hg0 j
      rw [mul_pow]
      have : g ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (idealRadius g j)]
    linarith
  have hfin := call_bound_of_generation D (r D) (fun j => (g * r j) ^ 2)
    (final_radius_le hg0 hg1 hε0.le D hε r hr0 hlow hup) hx
  have e : ∀ j, phiCost ((g * r j) ^ 2) = 5 / 3 * (g * r j) ^ 2 + (g * r j) ^ 4 := by
    intro j; unfold phiCost; ring
  simpa only [e] using hfin

/-! ### The supercritical call bound -/

/-- Concavity of `tanh` on `[0, ∞)` in the form `tanh (c u) ≤ c tanh u` for `c ≥ 1`, `u ≥ 0`.
Paper: `lem:radius` (`tanh_rates.tex`), last sentence of the proof. -/
theorem tanh_mul_le {c u : ℝ} (hc : 1 ≤ c) (hu : 0 ≤ u) : tanh (c * u) ≤ c * tanh u := by
  rcases eq_or_lt_of_le hc with h | h
  · rw [← h]; simp
  set f : ℝ → ℝ := fun x => x * tanh u - tanh (x * u) with hf
  have hderiv : ∀ x, HasDerivAt f (tanh u - 1 / cosh (x * u) ^ 2 * u) x := by
    intro x
    have h1 : HasDerivAt (fun x => x * u) u x := by
      simpa using (hasDerivAt_id x).mul_const u
    have h2 := (hasDerivAt_tanh (x * u)).comp x h1
    have h3 := ((hasDerivAt_id x).mul_const (tanh u)).sub h2
    refine h3.congr_deriv ?_
    simp
  have hct : Continuous tanh := by
    have e : tanh = fun y => sinh y / cosh y := funext tanh_eq_sinh_div_cosh
    rw [e]
    exact continuous_sinh.div continuous_cosh (fun y => (cosh_pos y).ne')
  have hcont : ContinuousOn f (Set.Icc 1 c) := by
    apply Continuous.continuousOn
    exact (continuous_id.mul continuous_const).sub
      (hct.comp (continuous_id.mul continuous_const))
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f _ h hcont (fun x _ => hderiv x)
  -- the derivative is nonnegative for `ξ ≥ 1`
  have hcu : cosh u ≤ cosh (ξ * u) := by
    rw [cosh_le_cosh, abs_of_nonneg hu, abs_of_nonneg (by nlinarith [hξ.1])]
    nlinarith [hξ.1]
  have hcu2 : cosh u ^ 2 ≤ cosh (ξ * u) ^ 2 := pow_le_pow_left₀ (cosh_pos u).le hcu 2
  have hsc : u ≤ sinh u * cosh u := by
    have := self_le_sinh_iff.mpr (show 0 ≤ 2 * u by linarith)
    rw [sinh_two_mul] at this
    linarith
  have htu : u / cosh u ^ 2 ≤ tanh u := by
    have hc0 := cosh_pos u
    rw [tanh_eq_sinh_div_cosh, div_le_div_iff₀ (by positivity) hc0]
    nlinarith
  have hd : 0 ≤ tanh u - 1 / cosh (ξ * u) ^ 2 * u := by
    have : 1 / cosh (ξ * u) ^ 2 * u ≤ u / cosh u ^ 2 := by
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_left hu (by have := cosh_pos u; positivity) hcu2
    linarith
  rw [hslope] at hd
  have hpos : 0 < c - 1 := by linarith
  have hf1 : f 1 = 0 := by simp [hf]
  rw [hf1, sub_zero] at hd
  have : 0 ≤ f c := by
    rcases (div_nonneg_iff.mp hd) with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact h1
    · linarith
  simp only [hf] at this
  linarith

/-- Above criticality the ideal radii obey `R_j ≤ g^j R_j^{(1)}`, where `R^{(1)}` is the
critical sequence. Paper: `lem:radius` (`tanh_rates.tex`), final assertion. -/
theorem idealRadius_le_pow_mul {g : ℝ} (hg : 1 ≤ g) :
    ∀ j, idealRadius g j ≤ g ^ j * idealRadius 1 j
  | 0 => by simp [idealRadius]
  | j + 1 => by
      have ih := idealRadius_le_pow_mul hg j
      have h0 := idealRadius_nonneg zero_le_one j
      have hgj : 1 ≤ g ^ (j + 1) := one_le_pow₀ hg
      calc idealRadius g (j + 1) = tanh (g * idealRadius g j) := rfl
        _ ≤ tanh (g * (g ^ j * idealRadius 1 j)) :=
            tanh_le_tanh (mul_le_mul_of_nonneg_left ih (by linarith))
        _ = tanh (g ^ (j + 1) * idealRadius 1 j) := by rw [pow_succ]; ring_nf
        _ ≤ g ^ (j + 1) * tanh (idealRadius 1 j) := tanh_mul_le hgj h0
        _ = g ^ (j + 1) * idealRadius 1 (j + 1) := by simp [idealRadius]

/-- A radius `R` with `R² ≤ q_D` plus the accumulated rounding error `3Dε` is at most
`2 / √(D+1)`. Auxiliary for the final-radius bounds of `lem:rounding` (`tanh_rates.tex`). -/
theorem radius_plus_error_le {R ε : ℝ} (D : ℕ) (hR : R ^ 2 ≤ qSeq D)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / (100 * ((D : ℝ) + 1) ^ 4)) :
    (R + 3 * D * ε) * √((D : ℝ) + 1) ≤ 2 := by
  have hd : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hs := sqrt_pos.mpr (show (0 : ℝ) < (D : ℝ) + 1 by positivity)
  have hss : √((D : ℝ) + 1) ^ 2 = (D : ℝ) + 1 := sq_sqrt (by positivity)
  have h1 : (R * √((D : ℝ) + 1)) ^ 2 ≤ 3 / 2 := by
    rw [mul_pow, hss]
    unfold qSeq at hR
    rw [le_div_iff₀ (by positivity)] at hR
    nlinarith
  have h1' : R * √((D : ℝ) + 1) ≤ 5 / 4 := by nlinarith
  have hsle : √((D : ℝ) + 1) ≤ (D : ℝ) + 1 := by
    rw [sqrt_le_left (by positivity)]; nlinarith
  have hden : 0 < ((D : ℝ) + 1) ^ 4 := by positivity
  have hεD : ε * ((D : ℝ) + 1) ^ 4 ≤ 1 / 100 := by
    calc ε * ((D : ℝ) + 1) ^ 4 ≤ 1 / (100 * ((D : ℝ) + 1) ^ 4) * ((D : ℝ) + 1) ^ 4 :=
          mul_le_mul_of_nonneg_right hε hden.le
      _ = 1 / 100 := by field_simp
  have hDle : (D : ℝ) * √((D : ℝ) + 1) ≤ ((D : ℝ) + 1) ^ 4 := by
    have h3 : (D : ℝ) * √((D : ℝ) + 1) ≤ ((D : ℝ) + 1) * ((D : ℝ) + 1) :=
      mul_le_mul (by linarith) hsle hs.le (by positivity)
    have h4 : ((D : ℝ) + 1) ^ 2 ≤ ((D : ℝ) + 1) ^ 4 :=
      pow_le_pow_right₀ (by linarith) (by norm_num)
    nlinarith
  have h2 : 3 * D * ε * √((D : ℝ) + 1) ≤ 3 / 100 := by nlinarith
  nlinarith

/-- The supercritical final-radius bound `r_D ≤ 2 e^{(g-1)D} / √(D+1)` for `1 ≤ g ≤ 2`.
Paper: `lem:rounding` (`tanh_rates.tex`), second final-radius bound. -/
theorem final_radius_le_super {g ε : ℝ} (hg1 : 1 ≤ g) (hε0 : 0 ≤ ε) (D : ℕ)
    (hε : ε ≤ 1 / (100 * ((D : ℝ) + 1) ^ 4)) (r : ℕ → ℝ) (hr0 : r 0 = 1)
    (hlow : ∀ j, tanh (g * r j) + 2 * ε ≤ r (j + 1))
    (hup : ∀ j, r (j + 1) ≤ tanh (g * r j) + 3 * ε) :
    r D ≤ 2 * exp ((g - 1) * D) / √((D : ℝ) + 1) := by
  have herr := (rounding_error (by linarith) hε0 r hr0 hlow hup D).2
  have hR := idealRadius_le_pow_mul hg1 D
  have hR1 := idealRadius_sq_le zero_le_one le_rfl D
  have hR0 := idealRadius_nonneg zero_le_one D
  have hgD : g ^ D ≤ exp ((g - 1) * D) := by
    have h := add_one_le_exp (g - 1)
    calc g ^ D ≤ exp (g - 1) ^ D := pow_le_pow_left₀ (by linarith) (by linarith) D
      _ = exp ((g - 1) * D) := by rw [← exp_nat_mul]; ring_nf
  have hE1 : 1 ≤ exp ((g - 1) * D) := one_le_exp (by
    have : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    nlinarith)
  have hbase := radius_plus_error_le D hR1 hε0 hε
  have hs := sqrt_pos.mpr (show (0 : ℝ) < (D : ℝ) + 1 by positivity)
  have hεD : 0 ≤ 3 * (D : ℝ) * ε := by positivity
  rw [le_div_iff₀ hs]
  have hgpos : 0 ≤ g ^ D := by positivity
  calc r D * √((D : ℝ) + 1) ≤ (g ^ D * idealRadius 1 D + 3 * D * ε) * √((D : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_right _ hs.le; linarith
    _ ≤ (exp ((g - 1) * D) * (idealRadius 1 D + 3 * D * ε)) * √((D : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_right _ hs.le
        nlinarith [mul_le_mul_of_nonneg_right hgD hR0]
    _ = exp ((g - 1) * D) * ((idealRadius 1 D + 3 * D * ε) * √((D : ℝ) + 1)) := by ring
    _ ≤ exp ((g - 1) * D) * 2 := mul_le_mul_of_nonneg_left hbase (exp_pos _).le
    _ = 2 * exp ((g - 1) * D) := by ring

/-- The per-layer supercritical offspring exponent: with `δ = g - 1 ∈ [0, 1]`,
`φ((g R_j)²) ≤ φ(q_j) + 50 δ`. Paper: proof of the call bound in `thm:upper`
(`tanh_rates.tex`), supercritical case. -/
theorem phiCost_super_le {g : ℝ} (hg1 : 1 ≤ g) (hg2 : g ≤ 2) (j : ℕ) :
    phiCost ((g * idealRadius g j) ^ 2) ≤ phiCost (qSeq j) + 50 * (g - 1) := by
  have hR := idealRadius_sq_le_super hg1 j
  have hR0 := idealRadius_nonneg (g := g) (by linarith) j
  have hR1 := idealRadius_le_one g j
  have hq0 := (qSeq_pos j).le
  have hq1 := qSeq_le_one j
  set x := (g * idealRadius g j) ^ 2 with hx
  set q := qSeq j
  have hg2' : 0 < g ^ 2 := by positivity
  have hx0 : 0 ≤ x := sq_nonneg _
  have hx4 : x ≤ 4 := by
    rw [hx, mul_pow]
    have : idealRadius g j ^ 2 ≤ 1 := pow_le_one₀ hR0 hR1
    nlinarith
  have hxq : x ≤ q + 15 / 2 * (g - 1) := by
    rw [hx, mul_pow]
    unfold radiusFixed at hR
    have h1 : g ^ 2 * idealRadius g j ^ 2 ≤ 3 / 2 * (g ^ 2 - 1) + g ^ 2 * q := by
      have := mul_le_mul_of_nonneg_left hR hg2'.le
      have e : g ^ 2 * (3 / 2 * (1 - 1 / g ^ 2) + q) = 3 / 2 * (g ^ 2 - 1) + g ^ 2 * q := by
        field_simp
      linarith
    have h2 : g ^ 2 * q ≤ q + (g ^ 2 - 1) := by
      have hg21 : 0 ≤ g ^ 2 - 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hq1 hg21]
    nlinarith
  unfold phiCost
  rcases le_total x q with h | h
  · nlinarith
  · nlinarith

/-- The call bound `E N_calls ≤ 80 (D+1)² e^{51 δ D}` of `eq:maincall` for reference gain
`1 ≤ g ≤ 2`, `δ = g - 1`, from the generation bound `eq:generalcost` with stored radii obeying
`eq:rounded` and the precision bound of `eq:precision`. The left side is the right side of
`eq:generalcost` (that inequality is not derived here). Together with `maincall_critical`
this is `eq:maincall` for every `S ≤ 2` with `g = max {1, S}`. Paper: `thm:upper`
(`tanh_model.tex`), `eq:maincall`; proof in `tanh_rates.tex`. -/
theorem maincall_super {g ε : ℝ} (hg1 : 1 ≤ g) (hg2 : g ≤ 2) (hε0 : 0 < ε) (D : ℕ)
    (hε : ε ≤ 1 / (100 * ((D : ℝ) + 1) ^ 4)) (r : ℕ → ℝ) (hr0 : r 0 = 1)
    (hlow : ∀ j, tanh (g * r j) + 2 * ε ≤ r (j + 1))
    (hup : ∀ j, r (j + 1) ≤ tanh (g * r j) + 3 * ε) :
    1 + r D * ∑ k ∈ Finset.range D,
        exp (∑ j ∈ Finset.Ico k D, (5 / 3 * (g * r j) ^ 2 + (g * r j) ^ 4)) ≤
      80 * ((D : ℝ) + 1) ^ 2 * exp (51 * (g - 1) * D) := by
  set δ := g - 1 with hδ
  have hδ0 : 0 ≤ δ := by linarith
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  set S : ℕ → ℝ := fun k => ∑ j ∈ Finset.Ico k D, phiCost ((g * r j) ^ 2) - 50 * δ * D
    with hS
  have hSle : ∀ k ≤ D, S k ≤ 29 / 200 + ∑ j ∈ Finset.Ico k D, phiCost (qSeq j) := by
    intro k _
    have hp := rounding_log_perturbation (by linarith) hg2 hε0 D hε r hr0 hlow hup k
    have hq : ∑ j ∈ Finset.Ico k D, phiCost ((g * idealRadius g j) ^ 2) ≤
        ∑ j ∈ Finset.Ico k D, (phiCost (qSeq j) + 50 * δ) :=
      Finset.sum_le_sum (fun j _ => phiCost_super_le hg1 hg2 j)
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hq
    have hcard : ((Finset.Ico k D).card : ℝ) ≤ D := by
      rw [Nat.card_Ico]; exact_mod_cast Nat.sub_le D k
    have : ((Finset.Ico k D).card : ℝ) * (50 * δ) ≤ D * (50 * δ) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    simp only [hS]
    nlinarith
  set rD' := r D * exp (-(δ * D)) with hrD'
  have hrD : rD' ≤ 2 / √((D : ℝ) + 1) := by
    have h := final_radius_le_super hg1 hε0.le D hε r hr0 hlow hup
    have he := exp_pos (-(δ * D))
    have hinv : exp (δ * D) * exp (-(δ * D)) = 1 := by rw [← exp_add]; simp
    calc rD' = r D * exp (-(δ * D)) := rfl
      _ ≤ 2 * exp (δ * D) / √((D : ℝ) + 1) * exp (-(δ * D)) :=
          mul_le_mul_of_nonneg_right (by rw [hδ]; exact h) he.le
      _ = 2 / √((D : ℝ) + 1) := by
          rw [div_mul_eq_mul_div, mul_assoc, hinv, mul_one]
  have hbound := call_bound_of_exponents D rD' S hrD hSle
  have hE1 : 1 ≤ exp (51 * δ * D) := one_le_exp (by positivity)
  have e : ∀ k, exp (∑ j ∈ Finset.Ico k D, (5 / 3 * (g * r j) ^ 2 + (g * r j) ^ 4)) =
      exp (S k) * exp (50 * δ * D) := by
    intro k
    rw [← exp_add]
    congr 1
    simp only [hS, phiCost]
    rw [sub_add_cancel]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsum : r D * ∑ k ∈ Finset.range D,
      exp (∑ j ∈ Finset.Ico k D, (5 / 3 * (g * r j) ^ 2 + (g * r j) ^ 4)) =
      exp (51 * δ * D) * (rD' * ∑ k ∈ Finset.range D, exp (S k)) := by
    simp only [e, ← Finset.sum_mul]
    rw [hrD']
    have h1 : exp (51 * δ * D) = exp (δ * D) * exp (50 * δ * D) := by rw [← exp_add]; ring_nf
    have h2 : exp (δ * D) * exp (-(δ * D)) = 1 := by rw [← exp_add]; simp
    rw [h1]
    calc r D * ((∑ k ∈ Finset.range D, exp (S k)) * exp (50 * δ * D))
        = r D * (exp (δ * D) * exp (-(δ * D))) *
            ((∑ k ∈ Finset.range D, exp (S k)) * exp (50 * δ * D)) := by rw [h2, mul_one]
      _ = exp (δ * D) * exp (50 * δ * D) *
            (r D * exp (-(δ * D)) * ∑ k ∈ Finset.range D, exp (S k)) := by ring
  rw [hsum]
  have : 1 + exp (51 * δ * D) * (rD' * ∑ k ∈ Finset.range D, exp (S k)) ≤
      exp (51 * δ * D) * (1 + rD' * ∑ k ∈ Finset.range D, exp (S k)) := by nlinarith
  calc 1 + exp (51 * δ * D) * (rD' * ∑ k ∈ Finset.range D, exp (S k))
      ≤ exp (51 * δ * D) * (1 + rD' * ∑ k ∈ Finset.range D, exp (S k)) := this
    _ ≤ exp (51 * δ * D) * (80 * ((D : ℝ) + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hbound (exp_pos _).le
    _ = 80 * ((D : ℝ) + 1) ^ 2 * exp (51 * (g - 1) * D) := by rw [hδ]; ring

/-! ### The supercritical fixed point -/

/-- At a positive fixed point `r = tanh (s r)`, the scaled fixed point `u = s r` satisfies
`3 (s - 1) ≤ u² ≤ (3/2)(s² - 1)`. The upper bound is the limit of `eq:superradius`; here it
follows directly from `eq:cothradius`. Paper: `prop:fixedrate` and `lem:nearcriticalgap`
(`tanh_rates.tex`). -/
theorem fixed_point_bounds {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (hfix : r = tanh (s * r)) :
    3 * (s - 1) ≤ (s * r) ^ 2 ∧ (s * r) ^ 2 ≤ 3 / 2 * (s ^ 2 - 1) := by
  have hu : 0 < s * r := mul_pos hs hr
  have ht : tanh (s * r) = r := hfix.symm
  constructor
  · have h := mul_coth_le hu
    rw [ht, mul_div_assoc, div_self hr.ne', mul_one] at h
    nlinarith
  · have h := coth_sq_ge hu.ne'
    rw [ht] at h
    have hr2 : 0 < r ^ 2 := by positivity
    rw [mul_pow, div_add' _ _ _ (by positivity), div_le_div_iff₀ (by positivity) hr2] at h
    nlinarith

/-- The contraction factor `λ = s (1 - r_*²)` at the positive fixed point lies in `(0, 1)`.
Paper: `prop:fixedrate` (`tanh_rates.tex`), "`0 < λ < 1`". -/
theorem fixed_point_lambda_mem {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (hfix : r = tanh (s * r)) :
    0 < s * (1 - r ^ 2) ∧ s * (1 - r ^ 2) < 1 := by
  have hu : 0 < s * r := mul_pos hs hr
  have hr1 : r < 1 := by rw [hfix]; exact tanh_lt_one _
  constructor
  · have : r ^ 2 < 1 := by nlinarith
    have : 0 < 1 - r ^ 2 := by linarith
    positivity
  · -- `s = u coth u` and `u < sinh u cosh u`
    set u := s * r with hudef
    have hsh : 0 < sinh u := sinh_pos_iff.mpr hu
    have hc := cosh_pos u
    have htu : r = sinh u / cosh u := by rw [hfix, tanh_eq_sinh_div_cosh]
    have h2u : 2 * u < sinh (2 * u) := self_lt_sinh_iff.mpr (by linarith)
    rw [sinh_two_mul] at h2u
    have hcs := cosh_sq_sub_sinh_sq u
    have hs' : s = u * cosh u / sinh u := by
      rw [htu] at hudef
      field_simp at hudef ⊢
      linarith
    rw [hs', htu]
    rw [show u * cosh u / sinh u * (1 - (sinh u / cosh u) ^ 2) = u / (sinh u * cosh u) by
      field_simp; nlinarith]
    rw [div_lt_one (by positivity)]
    linarith

/-- The fixed-norm rate bound `Ψ_s ≤ 5δ + 91δ²/4` for `δ = s - 1 ∈ (0, 1]`, where
`Ψ_s = 5(s r_*)²/3 + (s r_*)⁴`. Paper: `eq:psibound` in `prop:fixedrate`
(`tanh_rates.tex`). -/
theorem psi_upper {s r : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 2) (hr : 0 < r) (hfix : r = tanh (s * r)) :
    5 / 3 * (s * r) ^ 2 + (s * r) ^ 4 ≤ 5 * (s - 1) + 91 / 4 * (s - 1) ^ 2 := by
  have hb := (fixed_point_bounds (by linarith) hr hfix).2
  set δ := s - 1 with hδ
  have hs : s = 1 + δ := by rw [hδ]; ring
  have hδ0 : 0 < δ := by linarith
  have hδ1 : δ ≤ 1 := by linarith
  have hu2 : (s * r) ^ 2 ≤ 3 * δ + 3 / 2 * δ ^ 2 := by rw [hs] at hb; nlinarith
  have hu0 : 0 ≤ (s * r) ^ 2 := sq_nonneg _
  have h4 : (s * r) ^ 4 = ((s * r) ^ 2) ^ 2 := by ring
  rw [h4]
  have hsq : ((s * r) ^ 2) ^ 2 ≤ (3 * δ + 3 / 2 * δ ^ 2) ^ 2 :=
    pow_le_pow_left₀ hu0 hu2 2
  nlinarith [pow_pos hδ0 3, pow_pos hδ0 4]

/-- The converse rate bound `5δ + 9δ² ≤ Ψ_s`, from `u coth u ≤ 1 + u²/3`.
Paper: `prop:fixedrate` (`tanh_rates.tex`), last paragraph of the proof. -/
theorem psi_lower {s r : ℝ} (hs1 : 1 < s) (hr : 0 < r) (hfix : r = tanh (s * r)) :
    5 * (s - 1) + 9 * (s - 1) ^ 2 ≤ 5 / 3 * (s * r) ^ 2 + (s * r) ^ 4 := by
  have hb := (fixed_point_bounds (by linarith) hr hfix).1
  have h4 : (s * r) ^ 4 = ((s * r) ^ 2) ^ 2 := by ring
  rw [h4]
  have h0 : 0 ≤ 3 * (s - 1) := by linarith
  have hsq : (3 * (s - 1)) ^ 2 ≤ ((s * r) ^ 2) ^ 2 := pow_le_pow_left₀ h0 hb 2
  nlinarith

/-- The near-critical fixed-point gap: for `s = 1 + δ`, `0 < δ ≤ 1/2`,
`3δ ≤ u_*² ≤ 3δ + 3δ²/2` and `1 - λ ≥ δ`.
Paper: `lem:nearcriticalgap` (`tanh_rates.tex`). -/
theorem nearcritical_gap {δ r : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hr : 0 < r)
    (hfix : r = tanh ((1 + δ) * r)) :
    3 * δ ≤ ((1 + δ) * r) ^ 2 ∧ ((1 + δ) * r) ^ 2 ≤ 3 * δ + 3 / 2 * δ ^ 2 ∧
      δ ≤ 1 - (1 + δ) * (1 - r ^ 2) := by
  obtain ⟨h1, h2⟩ := fixed_point_bounds (by linarith) hr hfix
  refine ⟨by linarith, by nlinarith, ?_⟩
  -- `1 - λ = -δ + u²/s ≥ δ (3/s - 1) ≥ δ`
  have hs : 0 < 1 + δ := by linarith
  have hu : 3 * δ ≤ (1 + δ) ^ 2 * r ^ 2 := by nlinarith
  have : 3 * δ ≤ (1 + δ) * ((1 + δ) * r ^ 2) := by nlinarith
  nlinarith

/-! ### The scalar mean chain (`tanh_mean.tex`) -/

/-- `tanh` is continuous. Auxiliary for `eq:chainQ` (`tanh_mean.tex`). -/
theorem continuous_tanh : Continuous tanh := by
  have e : tanh = fun y => sinh y / cosh y := funext tanh_eq_sinh_div_cosh
  rw [e]
  exact continuous_sinh.div continuous_cosh (fun y => (cosh_pos y).ne')

/-- `tanh x ≤ x` for `x ≥ 0`. Auxiliary for `eq:chainQ` (`tanh_mean.tex`). -/
theorem tanh_le_self {x : ℝ} (hx : 0 ≤ x) : tanh x ≤ x := by
  have h := tanh_sq_le_sq x
  have h0 := tanh_nonneg_of_nonneg hx
  nlinarith

/-- `tanh u ≥ u / (1 + u)` for `u ≥ 0`, from `e^{2u} ≥ 1 + 2u`.
Paper: proof of `thm:chainphase` (`tanh_mean.tex`), subcritical lower bound. -/
theorem div_one_add_le_tanh {u : ℝ} (hu : 0 ≤ u) : u / (1 + u) ≤ tanh u := by
  have h := add_one_le_exp (2 * u)
  have he := exp_pos (2 * u)
  have e : exp u * exp u = exp (2 * u) := by rw [← exp_add]; ring_nf
  have hexpu := exp_pos u
  rw [tanh_eq, exp_neg]
  rw [div_le_div_iff₀ (by linarith) (by positivity)]
  field_simp
  nlinarith

/-- The mean chain `F_{s,0}(z) = z`, `F_{s,d+1}(z) = tanh (s F_{s,d}(z))` of
Section `sec:wholechain` (`tanh_mean.tex`). -/
noncomputable def chainF (s : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun z => z
  | d + 1 => fun z => tanh (s * chainF s d z)

/-- `A_D(s) = Σ_{j=1}^{D} s^{2j}`, as in `thm:uniformchain` (`tanh_mean.tex`). -/
noncomputable def chainA (s : ℝ) (D : ℕ) : ℝ := ∑ j ∈ Finset.range D, s ^ (2 * (j + 1))

/-- The derivative `F_{s,D}'(z) = s^D Π_{j=1}^{D} (1 - F_{s,j}(z)²)`, as in Section
`sec:wholechain` (`tanh_mean.tex`). -/
noncomputable def chainDeriv (s : ℝ) (D : ℕ) (z : ℝ) : ℝ :=
  s ^ D * ∏ j ∈ Finset.range D, (1 - chainF s (j + 1) z ^ 2)

/-- At `z = 1` the chain is the ideal radius sequence: `F_{s,D}(1) = R_D` with gain `s`.
This links `R = F_{s,D}(1)` of `tanh_mean.tex` with `lem:radius` (`tanh_rates.tex`). -/
theorem chainF_one (s : ℝ) : ∀ D, chainF s D 1 = idealRadius s D
  | 0 => rfl
  | D + 1 => by simp only [chainF, idealRadius, chainF_one s D]

/-- The chain is nonnegative on `[0, ∞)`. Auxiliary for `eq:chainQ` (`tanh_mean.tex`). -/
theorem chainF_nonneg {s z : ℝ} (hs : 0 ≤ s) (hz : 0 ≤ z) : ∀ D, 0 ≤ chainF s D z
  | 0 => hz
  | D + 1 => tanh_nonneg_of_nonneg (mul_nonneg hs (chainF_nonneg hs hz D))

/-- `F_{s,j}(z) ≤ s^j z` for `z ≥ 0`. Paper: Section `sec:wholechain` (`tanh_mean.tex`), the
cost of the global mixture. -/
theorem chainF_le {s z : ℝ} (hs : 0 ≤ s) (hz : 0 ≤ z) : ∀ D, chainF s D z ≤ s ^ D * z
  | 0 => by simp [chainF]
  | D + 1 => by
      have ih := chainF_le hs hz D
      have h0 := chainF_nonneg hs hz D
      calc chainF s (D + 1) z = tanh (s * chainF s D z) := rfl
        _ ≤ s * chainF s D z := tanh_le_self (mul_nonneg hs h0)
        _ ≤ s * (s ^ D * z) := mul_le_mul_of_nonneg_left ih hs
        _ = s ^ (D + 1) * z := by ring

/-- The chain is continuous. Auxiliary for `eq:chainQ` (`tanh_mean.tex`). -/
theorem continuous_chainF (s : ℝ) : ∀ D, Continuous (chainF s D)
  | 0 => continuous_id
  | D + 1 => continuous_tanh.comp (continuous_const.mul (continuous_chainF s D))

/-- The chain rule for the whole composition: `F_{s,D}' = s^D Π_{j ≤ D} (1 - F_{s,j}²)`.
Paper: the unlabeled product formula for `F_{s,D}'/s^D` in Section `sec:wholechain`
(`tanh_mean.tex`), "the cost of the global mixture". The composition form `eq:chainH` and its
complete monotonicity are not formalized. -/
theorem hasDerivAt_chainF (s : ℝ) : ∀ (D : ℕ) (z : ℝ),
    HasDerivAt (chainF s D) (chainDeriv s D z) z
  | 0, z => by
      refine (hasDerivAt_id' z).congr_deriv ?_
      simp [chainDeriv]
  | D + 1, z => by
      have ih := (hasDerivAt_chainF s D z).const_mul s
      have h := (hasDerivAt_tanh (s * chainF s D z)).comp z ih
      refine h.congr_deriv ?_
      unfold chainDeriv
      rw [Finset.prod_range_succ, pow_succ s D]
      have e : 1 / cosh (s * chainF s D z) ^ 2 = 1 - chainF s (D + 1) z ^ 2 := by
        show 1 / cosh (s * chainF s D z) ^ 2 = 1 - tanh (s * chainF s D z) ^ 2
        have hc := cosh_pos (s * chainF s D z)
        rw [tanh_eq_sinh_div_cosh]
        have := cosh_sq_sub_sinh_sq (s * chainF s D z)
        field_simp
        linarith
      rw [e]
      ring

/-- The chain derivative is continuous. Auxiliary for `eq:chainQ` (`tanh_mean.tex`). -/
theorem continuous_chainDeriv (s : ℝ) (D : ℕ) : Continuous (chainDeriv s D) := by
  unfold chainDeriv
  apply continuous_const.mul
  exact continuous_finsetProd _ (fun j _ => continuous_const.sub
    ((continuous_chainF s (j + 1)).pow 2))

/-- `1 - Π_j (1 - u_j) ≤ Σ_j u_j` for `u_j ∈ [0, 1]`, and the product lies in `[0, 1]`.
Paper: Section `sec:wholechain` (`tanh_mean.tex`), the cost of the global mixture. -/
theorem one_sub_prod_le_sum (u : ℕ → ℝ) (h0 : ∀ j, 0 ≤ u j) (h1 : ∀ j, u j ≤ 1) :
    ∀ D, 0 ≤ ∏ j ∈ Finset.range D, (1 - u j) ∧ ∏ j ∈ Finset.range D, (1 - u j) ≤ 1 ∧
      1 - ∏ j ∈ Finset.range D, (1 - u j) ≤ ∑ j ∈ Finset.range D, u j := by
  intro D
  induction D with
  | zero => simp
  | succ D ih =>
      obtain ⟨a, b, c⟩ := ih
      rw [Finset.prod_range_succ, Finset.sum_range_succ]
      have hu0 := h0 D
      have hu1 := h1 D
      refine ⟨mul_nonneg a (by linarith), ?_, ?_⟩
      · nlinarith
      · nlinarith

/-- `0 ≤ s^D - F_{s,D}'(z) ≤ s^D min {1, A_D(s) z²}` for `z ∈ [0, 1]`, `s > 0`.
Paper: Section `sec:wholechain` (`tanh_mean.tex`), display before `eq:chainQ`. -/
theorem chainDeriv_gap {s z : ℝ} (hs : 0 < s) (hz : 0 ≤ z) (D : ℕ) :
    0 ≤ s ^ D - chainDeriv s D z ∧ s ^ D - chainDeriv s D z ≤ s ^ D ∧
      s ^ D - chainDeriv s D z ≤ s ^ D * (chainA s D * z ^ 2) := by
  set u : ℕ → ℝ := fun j => chainF s (j + 1) z ^ 2 with hu
  have hu0 : ∀ j, 0 ≤ u j := fun j => sq_nonneg _
  have hu1 : ∀ j, u j ≤ 1 := fun j => by
    simp only [hu, chainF]
    exact (tanh_sq_lt_one _).le
  obtain ⟨p0, p1, p2⟩ := one_sub_prod_le_sum u hu0 hu1 D
  have hsD : 0 < s ^ D := pow_pos hs D
  have hsum : ∑ j ∈ Finset.range D, u j ≤ chainA s D * z ^ 2 := by
    unfold chainA
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    simp only [hu]
    have h1 := chainF_le hs.le hz (j + 1)
    have h0 := chainF_nonneg hs.le hz (j + 1)
    calc chainF s (j + 1) z ^ 2 ≤ (s ^ (j + 1) * z) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = s ^ (2 * (j + 1)) * z ^ 2 := by rw [mul_pow, ← pow_mul, mul_comm (j + 1) 2]
  unfold chainDeriv
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

/-- The chain range `λ/√(1+A) ≤ R ≤ λ/√(1 + 2A/3)`, with `R = F_{s,D}(1)` and `λ = s^D`, in
reciprocal-square form: `1 + 2A/3 ≤ λ²/R² ≤ 1 + A`. Paper: `eq:chainrange`
(`tanh_mean.tex`). -/
theorem chain_range {s : ℝ} (hs : 0 < s) (D : ℕ) :
    0 < chainF s D 1 ∧
      1 + 2 / 3 * chainA s D ≤ (s ^ D) ^ 2 / chainF s D 1 ^ 2 ∧
      (s ^ D) ^ 2 / chainF s D 1 ^ 2 ≤ 1 + chainA s D := by
  induction D with
  | zero => simp [chainF, chainA]
  | succ D ih =>
      obtain ⟨hR, hlo, hhi⟩ := ih
      set R := chainF s D 1 with hRdef
      have hu : s * R ≠ 0 := (mul_pos hs hR).ne'
      have hR1 : chainF s (D + 1) 1 = tanh (s * R) := rfl
      have hpos : 0 < tanh (s * R) := tanh_pos_of_pos (mul_pos hs hR)
      have c1 := coth_sq_ge hu
      have c2 := coth_sq_le hu
      have hA : chainA s (D + 1) = chainA s D + s ^ (2 * (D + 1)) := by
        unfold chainA; rw [Finset.sum_range_succ]
      have hsD2 : (s ^ (D + 1)) ^ 2 = s ^ (2 * (D + 1)) := by rw [← pow_mul, mul_comm]
      have key : (s ^ (D + 1)) ^ 2 / tanh (s * R) ^ 2 =
          (s ^ (D + 1)) ^ 2 * (1 / tanh (s * R) ^ 2) := by ring
      have key2 : (s ^ (D + 1)) ^ 2 * (1 / (s * R) ^ 2) = (s ^ D) ^ 2 / R ^ 2 := by
        field_simp
        ring
      have hsq : 0 ≤ (s ^ (D + 1)) ^ 2 := sq_nonneg _
      refine ⟨by rw [hR1]; exact hpos, ?_, ?_⟩
      · rw [hR1, key, hA, ← hsD2]
        have := mul_le_mul_of_nonneg_left c1 hsq
        rw [mul_add, key2] at this
        linarith
      · rw [hR1, key, hA, ← hsD2]
        have := mul_le_mul_of_nonneg_left c2 hsq
        rw [mul_add, key2] at this
        linarith

/-- `A_D(s)` for `s < 1`: `1 + A_D(s) ≤ (1 - s²)⁻¹`. Paper: proof of `thm:chainphase`
(`tanh_mean.tex`). -/
theorem one_add_chainA_le_sub {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (D : ℕ) :
    1 + chainA s D ≤ 1 / (1 - s ^ 2) := by
  have hs2 : s ^ 2 < 1 := by nlinarith
  have hpos : 0 < 1 - s ^ 2 := by linarith
  have hgeom : 1 + chainA s D = ∑ j ∈ Finset.range (D + 1), (s ^ 2) ^ j := by
    unfold chainA
    rw [Finset.sum_range_succ']
    simp only [pow_zero, ← pow_mul]
    ring
  rw [hgeom, le_div_iff₀ hpos]
  have := geom_sum_mul_neg (s ^ 2) (D + 1)
  rw [this]
  have : 0 ≤ (s ^ 2) ^ (D + 1) := by positivity
  linarith

/-- `A_D(1) = D`. Paper: proof of `thm:chainphase` (`tanh_mean.tex`). -/
theorem chainA_one (D : ℕ) : chainA 1 D = D := by simp [chainA]

/-- `A_D(s) ≤ s² s^{2D} / (s² - 1)` for `s > 1`. Paper: proof of `thm:chainphase`
(`tanh_mean.tex`). -/
theorem chainA_le_super {s : ℝ} (hs : 1 < s) (D : ℕ) :
    chainA s D ≤ s ^ 2 * s ^ (2 * D) / (s ^ 2 - 1) := by
  have hs2 : 1 < s ^ 2 := by nlinarith
  have hpos : 0 < s ^ 2 - 1 := by linarith
  have hgeom : chainA s D * (s ^ 2 - 1) = s ^ 2 * ((s ^ 2) ^ D - 1) := by
    unfold chainA
    induction D with
    | zero => simp
    | succ D ih =>
        rw [Finset.sum_range_succ, add_mul, ih, pow_succ, show 2 * (D + 1) = 2 * D + 2 by ring,
          pow_add, pow_mul]
        ring
  rw [le_div_iff₀ hpos, hgeom, pow_mul]
  have : 0 < s ^ 2 := by positivity
  nlinarith

/-- The cost of the global mixture, `Q = s^D + ∫_0^1 (s^D - F_{s,D}'(z)) / z² dz`
(`eq:chainarity`), satisfies `Q ≤ s^D (1 + A_D(s))`. Paper: `eq:chainQ` (`tanh_mean.tex`),
first bound. -/
theorem chain_cost_le_one_add {s : ℝ} (hs : 0 < s) (D : ℕ) :
    s ^ D + ∫ z in (0 : ℝ)..1, (s ^ D - chainDeriv s D z) / z ^ 2 ≤ s ^ D * (1 + chainA s D) := by
  set f : ℝ → ℝ := fun z => (s ^ D - chainDeriv s D z) / z ^ 2 with hf
  have hbound : ∀ z ∈ Set.Icc (0 : ℝ) 1, f z ≤ s ^ D * chainA s D := by
    intro z hz
    obtain ⟨_, _, h3⟩ := chainDeriv_gap hs hz.1 D
    simp only [hf]
    rcases eq_or_lt_of_le hz.1 with h | h
    · rw [← h]; simp
      have : 0 ≤ chainA s D := Finset.sum_nonneg (fun j _ => by positivity)
      positivity
    · rw [div_le_iff₀ (by positivity)]; nlinarith
  by_cases hint : IntervalIntegrable f MeasureTheory.volume 0 1
  · have hI : ∫ z in (0 : ℝ)..1, f z ≤ s ^ D * chainA s D := by
      calc ∫ z in (0 : ℝ)..1, f z ≤ ∫ _z in (0 : ℝ)..1, s ^ D * chainA s D :=
            intervalIntegral.integral_mono_on (by norm_num) hint intervalIntegrable_const hbound
        _ = s ^ D * chainA s D := by simp
    linarith
  · rw [intervalIntegral.integral_undef hint]
    have : 0 ≤ chainA s D := Finset.sum_nonneg (fun j _ => by positivity)
    have : 0 ≤ s ^ D := by positivity
    nlinarith

/-- The second bound of `eq:chainQ`: `Q ≤ 2 s^D √(A_D(s))` when `A_D(s) ≥ 1`.
Paper: `eq:chainQ` (`tanh_mean.tex`). -/
theorem chain_cost_le_sqrt {s : ℝ} (hs : 0 < s) (D : ℕ) (hA : 1 ≤ chainA s D) :
    s ^ D + ∫ z in (0 : ℝ)..1, (s ^ D - chainDeriv s D z) / z ^ 2 ≤
      2 * s ^ D * √(chainA s D) := by
  set A := chainA s D with hAdef
  set f : ℝ → ℝ := fun z => (s ^ D - chainDeriv s D z) / z ^ 2 with hf
  have hsD : 0 < s ^ D := pow_pos hs D
  have hcont : Continuous (fun z => s ^ D - chainDeriv s D z) :=
    continuous_const.sub (continuous_chainDeriv s D)
  have hmeas : Measurable f :=
    hcont.measurable.div (measurable_id.pow_const 2)
  -- a global bound on `[0, 1]` and integrability
  have hbound : ∀ z ∈ Set.Icc (0 : ℝ) 1, f z ≤ s ^ D * A := by
    intro z hz
    obtain ⟨_, _, h3⟩ := chainDeriv_gap hs hz.1 D
    simp only [hf]
    rcases eq_or_lt_of_le hz.1 with h | h
    · rw [← h]; simp; positivity
    · rw [div_le_iff₀ (by positivity)]; nlinarith
  have hnn : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f z := by
    intro z hz
    obtain ⟨h1, _, _⟩ := chainDeriv_gap hs hz.1 D
    simp only [hf]; positivity
  have hint : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      IntervalIntegrable f MeasureTheory.volume a b := by
    intro a b ha hab hb
    refine IntervalIntegrable.mono_fun' (g := fun _ => s ^ D * A) intervalIntegrable_const
      hmeas.aestronglyMeasurable ?_
    rw [Set.uIoc_of_le hab]
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall (fun z hz => ?_))
    have hz : z ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hz.1], by linarith [hz.2]⟩
    show ‖f z‖ ≤ s ^ D * A
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn z hz)]
    exact hbound z hz
  set a := 1 / √A with ha
  have hsA : 0 < √A := sqrt_pos.mpr (by linarith)
  have hsA1 : 1 ≤ √A := by rw [le_sqrt (by norm_num) (by linarith)]; linarith
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by rw [ha, div_le_one hsA]; exact hsA1
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hint 0 a le_rfl ha0.le ha1) (hint a 1 ha0.le ha1 le_rfl)
  have hI1 : ∫ z in (0 : ℝ)..a, f z ≤ s ^ D * √A := by
    calc ∫ z in (0 : ℝ)..a, f z ≤ ∫ _z in (0 : ℝ)..a, s ^ D * A :=
          intervalIntegral.integral_mono_on ha0.le (hint 0 a le_rfl ha0.le ha1)
            intervalIntegrable_const
            (fun z hz => hbound z ⟨hz.1, by linarith [hz.2]⟩)
      _ = s ^ D * √A := by
          simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, ha]
          have hsq : √A ^ 2 = A := sq_sqrt (by linarith)
          field_simp
          linarith
  have hgcont : ContinuousOn (fun z : ℝ => s ^ D / z ^ 2) (Set.uIcc a 1) := by
    apply ContinuousOn.div continuousOn_const (continuous_pow 2).continuousOn
    intro z hz
    rw [Set.uIcc_of_le ha1] at hz
    have : 0 < z := lt_of_lt_of_le ha0 hz.1
    positivity
  have hI2 : ∫ z in a..1, f z ≤ s ^ D * (√A - 1) := by
    calc ∫ z in a..1, f z ≤ ∫ z in a..1, s ^ D / z ^ 2 := by
          apply intervalIntegral.integral_mono_on ha1 (hint a 1 ha0.le ha1 le_rfl)
            hgcont.intervalIntegrable
          intro z hz
          have hz0 : 0 < z := lt_of_lt_of_le ha0 hz.1
          obtain ⟨_, h2, _⟩ := chainDeriv_gap hs hz0.le D
          simp only [hf]
          exact div_le_div_of_nonneg_right h2 (by positivity)
      _ = s ^ D * (√A - 1) := by
          have hderiv : ∀ x ∈ Set.uIcc a 1,
              HasDerivAt (fun z : ℝ => -s ^ D / z) (s ^ D / x ^ 2) x := by
            intro x hx
            rw [Set.uIcc_of_le ha1] at hx
            have hx0 : x ≠ 0 := (lt_of_lt_of_le ha0 hx.1).ne'
            have := (hasDerivAt_inv hx0).const_mul (-s ^ D)
            refine (this.congr_deriv (by field_simp)).congr_of_eventuallyEq ?_
            exact Filter.Eventually.of_forall (fun z => by simp [div_eq_mul_inv])
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hgcont.intervalIntegrable]
          simp only [ha]
          field_simp
          ring
  have htot : ∫ z in (0 : ℝ)..1, f z ≤ s ^ D * √A + s ^ D * (√A - 1) := by
    rw [← hsplit]; linarith
  simp only [hf] at htot
  linarith

/-- The uniform upper bound `Q ≤ 2 λ √(1 + A)` of `eq:uniformchain`, `λ = s^D`.
Paper: `thm:uniformchain` (`tanh_mean.tex`), upper bound; the cost `Q` is given by
`eq:chainarity`. -/
theorem chain_cost_le_uniform {s : ℝ} (hs : 0 < s) (D : ℕ) :
    s ^ D + ∫ z in (0 : ℝ)..1, (s ^ D - chainDeriv s D z) / z ^ 2 ≤
      2 * s ^ D * √(1 + chainA s D) := by
  have hA0 : 0 ≤ chainA s D := Finset.sum_nonneg (fun j _ => by positivity)
  have hsD : 0 < s ^ D := pow_pos hs D
  rcases le_total (chainA s D) 1 with h | h
  · have h1 := chain_cost_le_one_add hs D
    have hsq : 1 + chainA s D ≤ 2 * √(1 + chainA s D) := by
      have hs1 : 1 ≤ √(1 + chainA s D) := by
        rw [le_sqrt (by norm_num) (by linarith)]; linarith
      have hss : √(1 + chainA s D) ^ 2 = 1 + chainA s D := sq_sqrt (by linarith)
      have hs2 : √(1 + chainA s D) ≤ 2 := by
        rw [sqrt_le_left (by norm_num)]; linarith
      nlinarith
    nlinarith
  · have h1 := chain_cost_le_sqrt hs D h
    have : √(chainA s D) ≤ √(1 + chainA s D) := sqrt_le_sqrt (by linarith)
    nlinarith

/-- The upper bounds of the scalar phase diagram: `Q ≤ s^D / (1 - s²)` for `s < 1`,
`Q ≤ 2 √D` at `s = 1`, and `Q ≤ (2s/√(s² - 1)) s^{2D}` for `s > 1`.
Paper: `thm:chainphase` (`tanh_mean.tex`), `eq:chainsub`, `eq:chaincritical`,
`eq:chainsuper` (upper bounds). -/
theorem chain_phase_upper (D : ℕ) (hD : 1 ≤ D) :
    (∀ s, 0 < s → s < 1 →
      s ^ D + ∫ z in (0 : ℝ)..1, (s ^ D - chainDeriv s D z) / z ^ 2 ≤ s ^ D / (1 - s ^ 2)) ∧
    ((1 : ℝ) ^ D + ∫ z in (0 : ℝ)..1, ((1 : ℝ) ^ D - chainDeriv 1 D z) / z ^ 2 ≤
      2 * √(D : ℝ)) ∧
    (∀ s, 1 < s →
      s ^ D + ∫ z in (0 : ℝ)..1, (s ^ D - chainDeriv s D z) / z ^ 2 ≤
        2 * s / √(s ^ 2 - 1) * s ^ (2 * D)) := by
  refine ⟨fun s hs0 hs1 => ?_, ?_, fun s hs => ?_⟩
  · have h1 := chain_cost_le_one_add hs0 D
    have h2 := one_add_chainA_le_sub hs0.le hs1 D
    have hsD : 0 < s ^ D := pow_pos hs0 D
    calc _ ≤ s ^ D * (1 + chainA s D) := h1
      _ ≤ s ^ D * (1 / (1 - s ^ 2)) := mul_le_mul_of_nonneg_left h2 hsD.le
      _ = s ^ D / (1 - s ^ 2) := by ring
  · have hA : 1 ≤ chainA 1 D := by rw [chainA_one]; exact_mod_cast hD
    have h := chain_cost_le_sqrt zero_lt_one D hA
    rw [chainA_one] at h
    simpa using h
  · have hs0 : 0 < s := by linarith
    have hs2 : 0 < s ^ 2 - 1 := by nlinarith
    have hA1 : 1 ≤ chainA s D := by
      unfold chainA
      obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
      rw [Finset.sum_range_succ']
      have : 1 ≤ s ^ (2 * (0 + 1)) := one_le_pow₀ hs.le
      have : 0 ≤ ∑ j ∈ Finset.range D', s ^ (2 * (j + 1 + 1)) :=
        Finset.sum_nonneg (fun j _ => by positivity)
      linarith
    have h := chain_cost_le_sqrt hs0 D hA1
    have hA := chainA_le_super hs D
    have hsqrt : √(chainA s D) ≤ s * s ^ D / √(s ^ 2 - 1) := by
      rw [sqrt_le_left (by positivity), div_pow, sq_sqrt hs2.le, mul_pow, ← pow_mul,
        mul_comm D 2]
      exact hA
    have hsD : 0 < s ^ D := pow_pos hs0 D
    calc _ ≤ 2 * s ^ D * √(chainA s D) := h
      _ ≤ 2 * s ^ D * (s * s ^ D / √(s ^ 2 - 1)) :=
          mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ = 2 * s / √(s ^ 2 - 1) * s ^ (2 * D) := by rw [two_mul D, pow_add]; ring

/-! ### Lower bounds for the scalar mean chain -/

/-- `F_{s,D}(0) = 0`. Auxiliary for `thm:chainphase` (`tanh_mean.tex`). -/
theorem chainF_zero (s : ℝ) : ∀ D, chainF s D 0 = 0
  | 0 => rfl
  | D + 1 => by simp only [chainF, chainF_zero s D, mul_zero, tanh_zero]

/-- `F_{s,D}'(0) = s^D`, the derivative at zero used in `thm:uniformchain` and
`thm:chainphase` (`tanh_mean.tex`). -/
theorem chainDeriv_zero (s : ℝ) (D : ℕ) : chainDeriv s D 0 = s ^ D := by
  simp [chainDeriv, chainF_zero]

/-- The chain is nondecreasing: `F_{s,D}' ≥ 0`. Auxiliary for `thm:uniformchain`
(`tanh_mean.tex`). -/
theorem chainDeriv_nonneg {s : ℝ} (hs : 0 ≤ s) (D : ℕ) (z : ℝ) : 0 ≤ chainDeriv s D z := by
  unfold chainDeriv
  apply mul_nonneg (pow_nonneg hs D)
  apply Finset.prod_nonneg
  intro j _
  have : chainF s (j + 1) z ^ 2 < 1 := tanh_sq_lt_one _
  linarith

/-- The chain is differentiable. Auxiliary for `thm:chainphase` (`tanh_mean.tex`). -/
theorem differentiable_chainF (s : ℝ) (D : ℕ) : Differentiable ℝ (chainF s D) :=
  fun z => (hasDerivAt_chainF s D z).differentiableAt

/-- The chain derivative is differentiable. Auxiliary for `thm:chainphase` and
`thm:uniformchain` (`tanh_mean.tex`). -/
theorem differentiable_chainDeriv (s : ℝ) (D : ℕ) : Differentiable ℝ (chainDeriv s D) := by
  have hF : ∀ j, Differentiable ℝ (chainF s j) := differentiable_chainF s
  unfold chainDeriv
  fun_prop

/-- `deriv F_{s,D} = F_{s,D}'`. Auxiliary for `thm:chainphase` (`tanh_mean.tex`). -/
theorem deriv_chainF (s : ℝ) (D : ℕ) : deriv (chainF s D) = chainDeriv s D :=
  funext fun z => (hasDerivAt_chainF s D z).deriv

/-- The subcritical range bound `R = F_{s,D}(1) ≥ (1 - s) s^D` for `0 < s < 1`, from
`s^{j+1}/R_{j+1} ≤ s^j/R_j + s^{j+1}`. Paper: proof of `thm:chainphase` (`tanh_mean.tex`),
subcritical lower bound. -/
theorem chain_sub_range {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (D : ℕ) :
    (1 - s) * s ^ D ≤ chainF s D 1 := by
  have hinv : ∀ D, 0 < chainF s D 1 ∧
      s ^ D / chainF s D 1 ≤ ∑ j ∈ Finset.range (D + 1), s ^ j := by
    intro D
    induction D with
    | zero => simp [chainF]
    | succ D ih =>
        obtain ⟨hR, hle⟩ := ih
        set R := chainF s D 1
        have hu : 0 < s * R := mul_pos hs0 hR
        have ht := div_one_add_le_tanh hu.le
        have htpos : 0 < tanh (s * R) := tanh_pos_of_pos hu
        refine ⟨htpos, ?_⟩
        show s ^ (D + 1) / tanh (s * R) ≤ _
        rw [Finset.sum_range_succ]
        have h1 : 1 / tanh (s * R) ≤ (1 + s * R) / (s * R) := by
          rw [div_le_div_iff₀ htpos hu]
          rw [div_le_iff₀ (by linarith)] at ht
          linarith
        have h2 : s ^ (D + 1) / tanh (s * R) ≤ s ^ D / R + s ^ (D + 1) := by
          calc s ^ (D + 1) / tanh (s * R) = s ^ (D + 1) * (1 / tanh (s * R)) := by ring
            _ ≤ s ^ (D + 1) * ((1 + s * R) / (s * R)) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = s ^ D / R + s ^ (D + 1) := by field_simp; ring
        linarith
  obtain ⟨hR, hle⟩ := hinv D
  have hgeom : (∑ j ∈ Finset.range (D + 1), s ^ j) * (1 - s) ≤ 1 := by
    have := geom_sum_mul_neg s (D + 1)
    rw [this]
    have : 0 ≤ s ^ (D + 1) := by positivity
    linarith
  rw [div_le_iff₀ hR] at hle
  have hpos : 0 ≤ 1 - s := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hle hpos]

/-- The subcritical lower bound `(1 - s) s^D ≤ U_D(s)`: an exact factory whose worst-mean
expected source count is `M` satisfies `M ≥ R` by endpoint coupling (hypothesis `hcouple`,
the coupling argument of the paper). Paper: `eq:chainsub` in `thm:chainphase`
(`tanh_mean.tex`). -/
theorem chain_sub_lower {s M : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (D : ℕ)
    (hcouple : chainF s D 1 ≤ M) : (1 - s) * s ^ D ≤ M :=
  (chain_sub_range hs0 hs1 D).trans hcouple

/-- The supercritical lower bound `s^{2D} ≤ U_D(s)`, from the first-score inequality
`M ≥ (1 - z²) f'(z)²` of `eq:unknownlower` for the target `f = F_{s,D}` (hypothesis `hscore`,
which the paper derives from the transcript identities `lem:transcript`), evaluated at `z = 0`
where `f'(0) = s^D`. Paper: `eq:chainsuper` in `thm:chainphase` (`tanh_mean.tex`). -/
theorem chain_super_lower {s M : ℝ} (D : ℕ)
    (hscore : ∀ z ∈ Set.Ioo (-1 : ℝ) 1, (1 - z ^ 2) * deriv (chainF s D) z ^ 2 ≤ M) :
    s ^ (2 * D) ≤ M := by
  have h := hscore 0 ⟨by norm_num, by norm_num⟩
  rw [deriv_chainF, chainDeriv_zero] at h
  simpa [pow_mul, ← pow_mul, mul_comm] using h

/-- The critical reciprocal growth `F_{1,j}(z)⁻² ≤ z⁻² + j` for `z > 0`.
Paper: `eq:tanhlower` (`tanh_lower.tex`), used in `tanh_mean.tex`. -/
theorem inv_chainF_sq_le {z : ℝ} (hz : 0 < z) :
    ∀ j, 0 < chainF 1 j z ∧ 1 / chainF 1 j z ^ 2 ≤ 1 / z ^ 2 + j
  | 0 => by simp [chainF, hz]
  | j + 1 => by
      obtain ⟨hpos, hle⟩ := inv_chainF_sq_le hz j
      have hF : chainF 1 (j + 1) z = tanh (chainF 1 j z) := by simp [chainF]
      have h := coth_sq_le hpos.ne'
      rw [hF]
      refine ⟨tanh_pos_of_pos hpos, ?_⟩
      push_cast
      linarith

/-- The critical lower bound `√D / 8 ≤ U_D(1)`. The hypothesis `hcurv` is the second-score
inequality `M ≥ (1 - z²) |f''(z)| / 2` of `eq:unknownlower` for the target `f = F_{1,D}`,
which the paper derives from the transcript identities (`lem:transcript`).
Paper: `eq:chaincritical` in `thm:chainphase` (`tanh_mean.tex`), lower bound. -/
theorem chain_critical_lower (D : ℕ) (hD : 1 ≤ D) (M : ℝ)
    (hcurv : ∀ z ∈ Set.Ioo (-1 : ℝ) 1,
      (1 - z ^ 2) / 2 * |deriv (deriv (chainF 1 D)) z| ≤ M) :
    √(D : ℝ) / 8 ≤ M := by
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hsD : 0 < √(D : ℝ) := sqrt_pos.mpr (by linarith)
  have hsD2 : √(D : ℝ) ^ 2 = D := sq_sqrt (by linarith)
  have hsD1 : 1 ≤ √(D : ℝ) := by rw [le_sqrt (by norm_num) (by linarith)]; linarith
  set z0 := 1 / (2 * √(D : ℝ)) with hz0
  have hz0pos : 0 < z0 := by positivity
  have hz0half : z0 ≤ 1 / 2 := by
    rw [hz0, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set g := chainDeriv 1 D with hg
  have hg0 : g 0 = 1 := by simp [hg, chainDeriv_zero]
  -- `g z0 ≤ 5/6`
  have hgz0 : g z0 ≤ 5 / 6 := by
    have hterm : ∀ j ∈ Finset.range D, 1 - chainF 1 (j + 1) z0 ^ 2 ≤ 1 - 1 / (5 * D) := by
      intro j hj
      have hjD : ((j : ℝ) + 1) ≤ D := by
        have := Finset.mem_range.mp hj; exact_mod_cast this
      obtain ⟨hpos, hle⟩ := inv_chainF_sq_le hz0pos (j + 1)
      have hz02 : 1 / z0 ^ 2 = 4 * D := by
        rw [hz0, div_pow, mul_pow, hsD2]; field_simp; norm_num
      rw [hz02] at hle
      push_cast at hle
      have hF2 : 0 < chainF 1 (j + 1) z0 ^ 2 := by positivity
      have : 1 / (5 * (D : ℝ)) ≤ chainF 1 (j + 1) z0 ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_le_iff₀ hF2] at hle
        nlinarith
      linarith
    have hnn : ∀ j ∈ Finset.range D, 0 ≤ 1 - chainF 1 (j + 1) z0 ^ 2 := by
      intro j _
      have : chainF 1 (j + 1) z0 ^ 2 < 1 := tanh_sq_lt_one _
      linarith
    have hprod : ∏ j ∈ Finset.range D, (1 - chainF 1 (j + 1) z0 ^ 2) ≤
        (1 - 1 / (5 * (D : ℝ))) ^ D := by
      calc ∏ j ∈ Finset.range D, (1 - chainF 1 (j + 1) z0 ^ 2)
          ≤ ∏ _j ∈ Finset.range D, (1 - 1 / (5 * (D : ℝ))) :=
            Finset.prod_le_prod₀ hnn hterm
        _ = (1 - 1 / (5 * (D : ℝ))) ^ D := by rw [Finset.prod_const, Finset.card_range]
    have hexp : (1 - 1 / (5 * (D : ℝ))) ^ D ≤ exp (-1 / 5) := by
      have h1 : 0 ≤ 1 - 1 / (5 * (D : ℝ)) := by
        rw [sub_nonneg, div_le_one (by positivity)]; linarith
      calc (1 - 1 / (5 * (D : ℝ))) ^ D ≤ exp (-(1 / (5 * (D : ℝ)))) ^ D :=
            pow_le_pow_left₀ h1 (one_sub_le_exp_neg _) D
        _ = exp (-1 / 5) := by
            rw [← exp_nat_mul]; congr 1; field_simp
    have h56 : exp (-1 / 5) ≤ 5 / 6 := by
      have := add_one_le_exp (1 / 5)
      rw [show (-1 / 5 : ℝ) = -(1 / 5) by ring, exp_neg]
      rw [inv_le_comm₀ (exp_pos _) (by norm_num)]
      linarith
    simp only [hg, chainDeriv, one_pow, one_mul]
    linarith
  -- mean value theorem for `g = F'` on `[0, z0]`
  have hgd : Differentiable ℝ g := differentiable_chainDeriv 1 D
  obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope g hz0pos hgd.continuous.continuousOn
    hgd.differentiableOn
  have hc1 : c < 1 / 2 := lt_of_lt_of_le hc.2 hz0half
  have hderiv : deriv g c ≤ -(√(D : ℝ) / 3) := by
    rw [hslope, hg0, sub_zero, div_le_iff₀ hz0pos]
    have : -(√(D : ℝ) / 3) * z0 = -(1 / 6) := by rw [hz0]; field_simp; ring
    linarith
  have hM := hcurv c ⟨by linarith [hc.1], by linarith⟩
  rw [deriv_chainF] at hM
  have habs : √(D : ℝ) / 3 ≤ |deriv g c| := by
    rw [abs_of_neg (by linarith)]; linarith
  have hc2 : 3 / 4 ≤ 1 - c ^ 2 := by nlinarith [hc.1]
  calc √(D : ℝ) / 8 = 3 / 4 / 2 * (√(D : ℝ) / 3) := by ring
    _ ≤ (1 - c ^ 2) / 2 * |deriv g c| := by
        apply mul_le_mul (by linarith) habs (by positivity) (by nlinarith)
    _ ≤ M := hM

/-- The uniform lower bound `λ √(1 + A) / 25 ≤ U_D(s)` of `eq:uniformchain`, `λ = s^D`.
Hypotheses (from the paper's lower-bound machinery): endpoint coupling `R ≤ M` (`hcouple`)
and the second-score inequality of `eq:unknownlower` (`hcurv`). The bending step uses two
mean-value steps, which give `|F''| ≥ λ²/(4R)` instead of the Taylor constant `λ²/(2R)`;
this still yields the constant `1/25`. Paper: `thm:uniformchain` (`tanh_mean.tex`),
lower bound, with `eq:chainrange`. -/
theorem chain_uniform_lower {s M : ℝ} (hs : 0 < s) (D : ℕ)
    (hcouple : chainF s D 1 ≤ M)
    (hcurv : ∀ z ∈ Set.Ioo (-1 : ℝ) 1,
      (1 - z ^ 2) / 2 * |deriv (deriv (chainF s D)) z| ≤ M) :
    s ^ D * √(1 + chainA s D) / 25 ≤ M := by
  obtain ⟨hR, hlo, hhi⟩ := chain_range hs D
  set R := chainF s D 1 with hRdef
  set A := chainA s D with hAdef
  set lam := s ^ D with hlam
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun j _ => by positivity)
  have hlam0 : 0 < lam := pow_pos hs D
  have hM0 : 0 ≤ M := le_trans hR.le hcouple
  have hR2 : 0 < R ^ 2 := by positivity
  -- reduce to squares
  have hgoal : (lam * √(1 + A) / 25) ^ 2 ≤ M ^ 2 → lam * √(1 + A) / 25 ≤ M := fun h =>
    (pow_le_pow_iff_left₀ (by positivity) hM0 two_ne_zero).mp h
  apply hgoal
  have hsq : (lam * √(1 + A) / 25) ^ 2 = lam ^ 2 * (1 + A) / 625 := by
    rw [div_pow, mul_pow, sq_sqrt (by linarith)]; norm_num
  rw [hsq]
  rcases lt_or_ge A 24 with hA | hA
  · -- `M ≥ R ≥ λ/√(1+A)`
    have h1 : lam ^ 2 / (1 + A) ≤ R ^ 2 := by
      rw [div_le_iff₀ hR2] at hhi
      rw [div_le_iff₀ (by linarith)]
      linarith
    have h2 : lam ^ 2 * (1 + A) / 625 ≤ lam ^ 2 / (1 + A) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      have : (1 + A) * (1 + A) ≤ 625 := by nlinarith
      nlinarith [sq_nonneg lam]
    have h3 : R ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hR.le hcouple 2
    linarith
  · -- bending: `T = 2R/λ < 1/2`
    set T := 2 * R / lam with hT
    have hT0 : 0 < T := by positivity
    have hRlam : 17 * R ^ 2 ≤ lam ^ 2 := by
      rw [le_div_iff₀ hR2] at hlo
      nlinarith
    have hT2 : T ^ 2 ≤ 4 / 17 := by
      rw [hT, div_pow, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hThalf : T < 1 / 2 := by nlinarith
    have hTR : lam / 2 * T = R := by rw [hT]; field_simp
    -- first mean value step on `F` over `[0, T]`
    obtain ⟨c1, hc1, hs1⟩ := exists_hasDerivAt_eq_slope (chainF s D) (chainDeriv s D) hT0
      (differentiable_chainF s D).continuous.continuousOn
      (fun x _ => hasDerivAt_chainF s D x)
    have hmono : Monotone (chainF s D) :=
      monotone_of_deriv_nonneg (differentiable_chainF s D)
        (fun x => by rw [deriv_chainF]; exact chainDeriv_nonneg hs.le D x)
    have hFT : chainF s D T ≤ R := hmono (by linarith)
    rw [chainF_zero, sub_zero, sub_zero] at hs1
    have hgc1 : chainDeriv s D c1 ≤ lam / 2 := by
      rw [hs1, div_le_iff₀ hT0, hTR]
      exact hFT
    -- second mean value step on `F'` over `[0, c1]`
    have hgd : Differentiable ℝ (chainDeriv s D) := differentiable_chainDeriv s D
    obtain ⟨c2, hc2, hs2⟩ := exists_deriv_eq_slope (chainDeriv s D) hc1.1
      hgd.continuous.continuousOn hgd.differentiableOn
    rw [chainDeriv_zero, sub_zero, ← hlam] at hs2
    have hc10 : 0 < c1 := hc1.1
    have hd2 : deriv (chainDeriv s D) c2 ≤ -(lam / (2 * c1)) := by
      rw [hs2, div_le_iff₀ hc10]
      have e : -(lam / (2 * c1)) * c1 = -(lam / 2) := by field_simp
      rw [e]
      linarith
    have hbig : lam ^ 2 / (4 * R) ≤ |deriv (chainDeriv s D) c2| := by
      have hpos : 0 < lam / (2 * c1) := by positivity
      rw [abs_of_neg (by linarith)]
      have h1 : lam / (2 * T) ≤ lam / (2 * c1) :=
        div_le_div_of_nonneg_left hlam0.le (by positivity) (by linarith [hc1.2])
      have h2 : lam / (2 * T) = lam ^ 2 / (4 * R) := by rw [hT]; field_simp; ring
      linarith
    have hc2' : c2 < 1 / 2 := by linarith [hc2.2, hc1.2]
    have hM := hcurv c2 ⟨by linarith [hc2.1], by linarith⟩
    rw [deriv_chainF] at hM
    have h34 : 3 / 4 ≤ 1 - c2 ^ 2 := by nlinarith [hc2.1]
    have hMR : 3 * lam ^ 2 / (32 * R) ≤ M := by
      have habs0 : 0 ≤ lam ^ 2 / (4 * R) := by positivity
      calc 3 * lam ^ 2 / (32 * R) = 3 / 4 / 2 * (lam ^ 2 / (4 * R)) := by field_simp; ring
        _ ≤ (1 - c2 ^ 2) / 2 * |deriv (chainDeriv s D) c2| :=
            mul_le_mul (by linarith) hbig habs0 (by linarith)
        _ ≤ M := hM
    have hsqM : (3 * lam ^ 2 / (32 * R)) ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (by positivity) hMR 2
    have e1 : (3 * lam ^ 2 / (32 * R)) ^ 2 = 9 * lam ^ 2 / 1024 * (lam ^ 2 / R ^ 2) := by
      field_simp; ring
    have hl2 : 0 ≤ 9 * lam ^ 2 / 1024 := by positivity
    have hc : (1 + A) / 625 ≤ 9 / 1024 * (1 + 2 / 3 * A) := by linarith
    have hkey : lam ^ 2 * (1 + A) / 625 ≤ (3 * lam ^ 2 / (32 * R)) ^ 2 := by
      rw [e1]
      calc lam ^ 2 * (1 + A) / 625 = lam ^ 2 * ((1 + A) / 625) := by ring
        _ ≤ lam ^ 2 * (9 / 1024 * (1 + 2 / 3 * A)) :=
            mul_le_mul_of_nonneg_left hc (sq_nonneg lam)
        _ = 9 * lam ^ 2 / 1024 * (1 + 2 / 3 * A) := by ring
        _ ≤ 9 * lam ^ 2 / 1024 * (lam ^ 2 / R ^ 2) := mul_le_mul_of_nonneg_left hlo hl2
    linarith

end ExactSampling.SharpRates
