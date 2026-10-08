import Mathlib

/-!
# Exact residual sampling: mixtures, invariants, and counting identities

This module formalizes the exactness and counting identities behind the residual
samplers of `tanh_residual.tex` (section `sec:residual`, Theorem
`thm:residualupper`, Proposition `prop:largerow`, Proposition
`prop:residuallargeslower`, Theorem `thm:resmeanlaw`),
`tanh_residual_large_bits.tex` (Corollary `cor:largeresidualsharpbits`), and
`tanh_residual_fused.tex` (the raw-root identity `eq:resrawrootidentity`).

Formalized here:
* the interval invariant `eq:resinvariant` for one residual layer, including the
  projection of the approximate center;
* exactness of the normalized residual mixture (`eq:resskip`) and of the root gate;
* the non-skip hazard bounds `α/2 ≤ 1 - p_ℓ ≤ 2α`, with the `tanh` inequalities
  `tanh(gr) ≥ (3/4) r` (for `g ≥ 1`, `r ≤ 1`) and, at gain `g ≤ 1`, `tanh(gr) ≤ r`
  proved here, and the one-layer Bernoulli thinning identity;
* the telescoping of radius factors and the generation bound behind
  `eq:resproduct`; the critical bound `eq:rescriticalupper` with prefactor
  `9 e^{21}` and `τ = αD` (`critical_bound`), including the rounding sum
  `∑ 12αε/F_j ≤ 1`;
* the raw-root identity `eq:resrawrootidentity` with its reverse geometric masses;
* the mean-network identity `eq:resmeanidentity` for the actual uniform network;
* the arithmetic of `prop:largerow`, `cor:largeresidualsharpbits`, the lower
  bounds of `prop:residuallargeslower`, and the case analyses of the lower bounds in
  `thm:resmeanlaw` and `cor:reslower`.

Not formalized here: the probability space of the recursive sampler and its
predictable charging; the transcript, bending and coupling inequalities; the
rounding lemma `eq:resroundingerror` (`r_j ≥ R_j` and `r_j - R_j ≤ 3jαε`); the
inequality `tanh(g r_j) ≤ r_j` for `g > 1` (from the decrease of the ideal radii); the
supercritical half of `thm:residualupper` (`eq:ressuperupper`: the constant
`10 e^{30}`, the factor `e^{6025 δ α (D-k)}`, `R^{(g)}_j ≤ a^j R^{(1)}_j`, and
`α ∑ r_j^5 ≤ 4 e^{5δτ}`); the choice of strategy behind `Q* ≤ 3Ξ` in
`thm:resmeanlaw`; the upper bounds of `prop:residuallargeslower`; and the
bit-operation model. Where a proof in the paper invokes such a fact, the
corresponding inequality is an explicit hypothesis. Several hypotheses are proved in
`ExactSampling.ResidualDepth` (`lem:resrange`, `eq:resintegrals`, `lem:resradial`,
`eq:reslogproduct`); each docstring names them.
-/

open Finset Real

namespace ExactSampling.ResidualSampling

/-! ## The interval invariant and the normalized mixture -/

/-- Projection onto `[-1 + r, 1 - r]`, used for the residual centers. -/
def projectCenter (r x : ℝ) : ℝ := max (-1 + r) (min x (1 - r))

/-- Paper: `eq:resinvariant` (tanh_residual.tex). Suppose the previous layer
satisfies the invariant, the tanh output `y` lies in its interval `[m - R, m + R]`
with `|m| + R ≤ 1`, the new radius satisfies `V + α ε ≤ r ≤ 1` with
`V = (1-α) r' + α R`, and `ct` approximates the midpoint `M` within `α ε`.
Then the projected center `c` satisfies `|h - c| ≤ r`, `|c| + r ≤ 1`, and also
`|M - c| ≤ r - V`, which makes the constant masses of the normalized mixture
nonnegative. -/
theorem interval_invariant_step (α r' c' h' m R y r ε ct : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hprev : |h' - c'| ≤ r') (hprevc : |c'| + r' ≤ 1)
    (hy : |y - m| ≤ R) (hmR : |m| + R ≤ 1)
    (hr : (1 - α) * r' + α * R + α * ε ≤ r) (hr1 : r ≤ 1)
    (hct : |ct - ((1 - α) * c' + α * m)| ≤ α * ε) :
    |((1 - α) * h' + α * y) - projectCenter r ct| ≤ r ∧
      |projectCenter r ct| + r ≤ 1 ∧
      |((1 - α) * c' + α * m) - projectCenter r ct| ≤ r - ((1 - α) * r' + α * R) := by
  set M := (1 - α) * c' + α * m with hM
  set V := (1 - α) * r' + α * R with hV
  set c := projectCenter r ct with hc
  have hp : 0 ≤ 1 - α := by linarith
  rw [abs_le] at hprev hy hct
  have hc'1 := neg_abs_le c'
  have hc'2 := le_abs_self c'
  have hm1 := neg_abs_le m
  have hm2 := le_abs_self m
  -- endpoints of the residual interval stay in `[-1, 1]`
  have hlowM : -1 ≤ M - V := by
    have h1 : (1 - α) * (-1) ≤ (1 - α) * (c' - r') :=
      mul_le_mul_of_nonneg_left (by linarith) hp
    have h2 : α * (-1) ≤ α * (m - R) := mul_le_mul_of_nonneg_left (by linarith) hα0
    nlinarith
  have hhighM : M + V ≤ 1 := by
    have h1 : (1 - α) * (c' + r') ≤ (1 - α) * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) hp
    have h2 : α * (m + R) ≤ α * 1 := mul_le_mul_of_nonneg_left (by linarith) hα0
    nlinarith
  -- the output lies in `[M - V, M + V]`
  have hhM : |((1 - α) * h' + α * y) - M| ≤ V := by
    rw [abs_le]
    have h1 := mul_le_mul_of_nonneg_left hprev.1 hp
    have h2 := mul_le_mul_of_nonneg_left hprev.2 hp
    have h3 := mul_le_mul_of_nonneg_left hy.1 hα0
    have h4 := mul_le_mul_of_nonneg_left hy.2 hα0
    constructor <;> nlinarith
  -- the projected center lies in `[M + V - r, M - V + r] ∩ [-1 + r, 1 - r]`
  have hc1 : -1 + r ≤ c := le_max_left _ _
  have hc2 : c ≤ 1 - r := max_le (by linarith) (min_le_right _ _)
  have hc3 : c ≤ M - V + r := max_le (by linarith) ((min_le_left _ _).trans (by linarith))
  have hc4 : M + V - r ≤ c := le_max_of_le_right (le_min (by linarith) (by linarith))
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_le] at hhM ⊢
    constructor <;> linarith
  · rcases abs_cases c with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  · rw [abs_le]
    constructor <;> linarith

/-- Paper: `eq:resskip` and the following paragraph (tanh_residual.tex). The
normalized residual sampler chooses the same-coordinate skip with probability
`(1-α) r'/r`, the centered tanh factory with probability `α R / r`, and two
constant signs whose masses carry mean `(M - c)/r`. All masses are valid, they
sum to one, and the mixture mean is the normalized residual mean `(h - c)/r`.
Here `u'` is the previous normalized mean and `G` the centered factory mean. -/
theorem normalized_step_mixture (α r' r R m c c' h' y u' G : ℝ)
    (hr : 0 < r) (hr' : 0 ≤ r') (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hR : 0 ≤ R)
    (hh' : h' = c' + r' * u') (hy : y = m + R * G)
    (hmass : |((1 - α) * c' + α * m) - c| ≤ r - ((1 - α) * r' + α * R)) :
    let ps := (1 - α) * r' / r
    let pf := α * R / r
    let κ := ((1 - α) * c' + α * m - c) / r
    0 ≤ ps ∧ 0 ≤ pf ∧ 0 ≤ (1 - ps - pf + κ) / 2 ∧ 0 ≤ (1 - ps - pf - κ) / 2 ∧
      ps + pf + (1 - ps - pf + κ) / 2 + (1 - ps - pf - κ) / 2 = 1 ∧
      ps * u' + pf * G + (1 - ps - pf + κ) / 2 - (1 - ps - pf - κ) / 2 =
        ((1 - α) * h' + α * y - c) / r := by
  intro ps pf κ
  have hp : 0 ≤ 1 - α := by linarith
  rw [abs_le] at hmass
  have hkey1 : ps + pf - κ ≤ 1 := by
    simp only [ps, pf, κ]
    rw [← add_div, ← sub_div, div_le_one hr]
    linarith
  have hkey2 : ps + pf + κ ≤ 1 := by
    simp only [ps, pf, κ]
    rw [← add_div, ← add_div, div_le_one hr]
    linarith
  refine ⟨by positivity, by positivity, by linarith, by linarith, by ring, ?_⟩
  simp only [ps, pf, κ]
  rw [hh', hy]
  field_simp
  ring

/-- Paper: the root gate of `sec:residual` (tanh_residual.tex), the analogue of
`eq:topmixture` (tanh_scalar.tex). Open the normalized sampler with probability
`r_D`, otherwise use constant masses `(1 - r_D ± c)/2`. The second invariant in
`eq:resinvariant` makes the masses valid and the mean is `h`. -/
theorem root_gate (h c r : ℝ) (hr : 0 < r) (hc : |c| + r ≤ 1) :
    0 ≤ (1 - r + c) / 2 ∧ 0 ≤ (1 - r - c) / 2 ∧
      r * ((h - c) / r) + (1 - r + c) / 2 - (1 - r - c) / 2 = h := by
  have h1 := neg_abs_le c
  have h2 := le_abs_self c
  refine ⟨by linarith, by linarith, ?_⟩
  field_simp
  ring

/-! ## Hazards and geometric thinning -/

/-- Paper: the display before `h = min{2α, 1}` in `sec:residual`
(tanh_residual.tex): `1 - p_ℓ = α + p (r_ℓ - r_{ℓ-1}) / r_ℓ`. -/
theorem hazard_identity (α r' r : ℝ) (hr : r ≠ 0) :
    1 - (1 - α) * r' / r = α + (1 - α) * (r - r') / r := by
  field_simp
  ring

/-- Paper: `sec:residual` (tanh_residual.tex), the bound `1 - p_ℓ ≤ 2α`. The
hypotheses are the upper rounding bound in `eq:resrounded`, the inequality
`tanh(g r) ≤ r` proved there, and `3 ε ≤ r_ℓ`, which follows from
`eq:resradiuslower` and the choice of `ε`. -/
theorem hazard_le_two_mul (α g r' r ε : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hr : 0 < r) (hε0 : 0 ≤ ε)
    (hround : r ≤ (1 - α) * r' + α * Real.tanh (g * r') + 3 * α * ε)
    (htanh : Real.tanh (g * r') ≤ r') (hε : 3 * ε ≤ r) :
    1 - (1 - α) * r' / r ≤ 2 * α := by
  rw [hazard_identity α r' r hr.ne', add_comm]
  have hp : 0 ≤ 1 - α := by linarith
  have hαε : 0 ≤ 3 * α * ε := by positivity
  have h1 : (1 - α) * (r - r') ≤ 3 * α * ε := by
    have h0 : α * Real.tanh (g * r') ≤ α * r' := mul_le_mul_of_nonneg_left htanh hα0
    have : r - r' ≤ 3 * α * ε := by linarith
    rcases le_or_gt (r - r') 0 with h' | h'
    · nlinarith
    · calc (1 - α) * (r - r') ≤ 1 * (3 * α * ε) :=
            mul_le_mul (by linarith) this h'.le (by norm_num)
        _ = 3 * α * ε := one_mul _
  have h2 : 3 * α * ε / r ≤ α := by
    rw [div_le_iff₀ hr]
    nlinarith
  have h3 : (1 - α) * (r - r') / r ≤ 3 * α * ε / r :=
    div_le_div_of_nonneg_right h1 hr.le
  linarith

/-- Paper: proof of `thm:residualupper` (tanh_residual.tex), "the hazard ratio
introduces no small-`α` division": `1 - p_ℓ ≥ α/2` once `tanh(g r) ≥ (3/4) r`
and `r_ℓ` is at least the ideal update. -/
theorem half_mul_le_hazard (α g r' r : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hr' : 0 ≤ r') (hr : 0 < r) (hround : (1 - α) * r' + α * Real.tanh (g * r') ≤ r)
    (htanh : 3 / 4 * r' ≤ Real.tanh (g * r')) :
    α / 2 ≤ 1 - (1 - α) * r' / r := by
  have hlow : r' * (1 - α / 4) ≤ r := by nlinarith
  have hfrac : (1 - α) * r' / r ≤ 1 - α / 2 := by
    rw [div_le_iff₀ hr]
    have : (1 - α) * r' ≤ (1 - α / 2) * (r' * (1 - α / 4)) := by
      nlinarith [mul_nonneg hr' hα0, mul_nonneg (mul_nonneg hr' hα0) hα0]
    nlinarith
  linarith

/-- Paper: `sec:residual` (tanh_residual.tex), the one-layer step of "independent
geometric waiting times and thinning reproduce the original skip probabilities
exactly": a proposal of probability `h` retained with probability `q/h` is a
non-skip of probability `q`, and otherwise the layer is skipped, with probability
`1 - q`; the retention probability is valid whenever `0 ≤ q ≤ h`. The identification
of the geometric waiting times with independent per-layer proposals is not
formalized. -/
theorem thinning_exact (h q : ℝ) (hh : 0 < h) (hq0 : 0 ≤ q) (hqh : q ≤ h) :
    0 ≤ q / h ∧ q / h ≤ 1 ∧ h * (q / h) = q ∧ (1 - h) + h * (1 - q / h) = 1 - q := by
  refine ⟨by positivity, (div_le_one hh).mpr hqh, ?_, ?_⟩
  · field_simp
  · field_simp
    ring

/-! ## The two `tanh` inequalities behind the hazards -/

/-- Auxiliary: `tanh` is monotone, since `tanh y - tanh x = sinh(y - x)/(cosh x cosh y)`. -/
theorem tanh_le_tanh {x y : ℝ} (h : x ≤ y) : Real.tanh x ≤ Real.tanh y := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    div_le_div_iff₀ (Real.cosh_pos x) (Real.cosh_pos y)]
  have e := Real.sinh_sub y x
  have h0 : 0 ≤ Real.sinh (y - x) := Real.sinh_nonneg_iff.mpr (by linarith)
  nlinarith

/-- Auxiliary: the series `sinh x = ∑ T_n` and `x cosh x = ∑ (2n+1) T_n` with
`T_n = x^{2n+1}/(2n+1)!`. -/
theorem hasSum_sinh_cosh (x : ℝ) :
    HasSum (fun n : ℕ => x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) (Real.sinh x) ∧
      HasSum (fun n : ℕ => (2 * (n : ℝ) + 1) * (x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)))
        (x * Real.cosh x) := by
  refine ⟨Real.hasSum_sinh x, ?_⟩
  have := (Real.hasSum_cosh x).mul_left x
  convert this using 1
  funext n
  rw [Nat.factorial_succ]
  push_cast
  have : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp

/-- Auxiliary: `tanh x ≤ x` for `x ≥ 0`, from `x cosh x - sinh x = ∑ 2n T_n ≥ 0`. -/
theorem tanh_le_self {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  obtain ⟨hs, hc⟩ := hasSum_sinh_cosh x
  have h := (hc.sub hs).nonneg fun n => by
    have hT : 0 ≤ x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by positivity
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ (Real.cosh_pos x)]
  linarith

/-- Paper: proof of `thm:residualupper` (tanh_residual.tex), "`tanh 1 > 3/4`". -/
theorem three_quarters_lt_tanh_one : (3 : ℝ) / 4 < Real.tanh 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, lt_div_iff₀ (Real.cosh_pos 1), Real.sinh_eq, Real.cosh_eq]
  have he := Real.exp_one_gt_d9
  have hm : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  have hpos := Real.exp_pos (-1)
  nlinarith

/-- Paper: proof of `thm:residualupper` (tanh_residual.tex): `tanh r ≥ (3/4) r` on
`[0, 1]`, the form of "`tanh(gr)/r ≥ tanh 1 > 3/4`" used for the hazard. The proof
compares the series of `sinh r - (3/4) r cosh r` with its value at `r = 1`. -/
theorem three_quarter_le_tanh {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    3 / 4 * r ≤ Real.tanh r := by
  set c : ℕ → ℝ := fun n => 1 - 3 / 4 * (2 * (n : ℝ) + 1) with hc
  have hk : ∀ x : ℝ, HasSum (fun n : ℕ => c n * (x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)))
      (Real.sinh x - 3 / 4 * (x * Real.cosh x)) := by
    intro x
    obtain ⟨hs, hcosh⟩ := hasSum_sinh_cosh x
    convert hs.sub (hcosh.mul_left (3 / 4)) using 1
    funext n
    simp only [hc]
    ring
  -- `k(r) ≥ r k(1)`
  have hdiff := (hk r).sub ((hk 1).mul_left r)
  have hnn := hdiff.nonneg fun n => by
    have e : c n * (r ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) -
        r * (c n * ((1 : ℝ) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ))) =
        c n * ((r ^ (2 * n + 1) - r) / ((2 * n + 1).factorial : ℝ)) := by
      rw [one_pow]
      ring
    rw [e]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp
    · have hn : (1 : ℝ) ≤ n := by exact_mod_cast hpos
      have hcn : c n ≤ 0 := by simp only [hc]; linarith
      have hpow : r ^ (2 * n + 1) ≤ r := by
        calc r ^ (2 * n + 1) = r * r ^ (2 * n) := by rw [pow_succ, mul_comm]
          _ ≤ r * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hr0 hr1) hr0
          _ = r := mul_one r
      have : (r ^ (2 * n + 1) - r) / ((2 * n + 1).factorial : ℝ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      nlinarith
  -- `k(1) > 0` is `tanh 1 > 3/4`
  have hk1 : 0 < Real.sinh 1 - 3 / 4 * (1 * Real.cosh 1) := by
    have h := three_quarters_lt_tanh_one
    rw [Real.tanh_eq_sinh_div_cosh, lt_div_iff₀ (Real.cosh_pos 1)] at h
    linarith
  have hkr : 0 ≤ Real.sinh r - 3 / 4 * (r * Real.cosh r) := by nlinarith
  rw [Real.tanh_eq_sinh_div_cosh, le_div_iff₀ (Real.cosh_pos r)]
  linarith

/-- Paper: proof of `thm:residualupper` (tanh_residual.tex): for gain `g ≥ 1` and
`0 ≤ r ≤ 1`, `tanh(g r) ≥ tanh r ≥ (3/4) r`. -/
theorem three_quarter_le_tanh_gain {g r : ℝ} (hg : 1 ≤ g) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    3 / 4 * r ≤ Real.tanh (g * r) :=
  (three_quarter_le_tanh hr0 hr1).trans (tanh_le_tanh (by nlinarith))

/-- Paper: proof of `thm:residualupper` (tanh_residual.tex), "`1 - p_ℓ ≥ α/2`
under the chosen rounding precision", with the `tanh` hypothesis of
`half_mul_le_hazard` discharged for `g ≥ 1` and `0 ≤ r' ≤ 1`. -/
theorem half_mul_le_hazard_gain (α g r' r : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hg : 1 ≤ g)
    (hr' : 0 ≤ r') (hr'1 : r' ≤ 1) (hr : 0 < r)
    (hround : (1 - α) * r' + α * Real.tanh (g * r') ≤ r) :
    α / 2 ≤ 1 - (1 - α) * r' / r :=
  half_mul_le_hazard α g r' r hα0 hα1 hr' hr hround (three_quarter_le_tanh_gain hg hr' hr'1)

/-- Paper: `sec:residual` (tanh_residual.tex), the bound `1 - p_ℓ ≤ 2α` at
reference gain `g ≤ 1` (the critical case `g = 1` of `thm:residualupper`), where the
inequality `tanh(g r) ≤ r` holds for every `r ≥ 0`. For `g > 1` the paper derives
`tanh(g r_j) ≤ r_j` from the decrease of the ideal radii; that case is the declared
stand-in `htanh` of `hazard_le_two_mul`. -/
theorem hazard_le_two_mul_critical (α g r' r ε : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hr' : 0 ≤ r') (hr : 0 < r) (hε0 : 0 ≤ ε)
    (hround : r ≤ (1 - α) * r' + α * Real.tanh (g * r') + 3 * α * ε) (hε : 3 * ε ≤ r) :
    1 - (1 - α) * r' / r ≤ 2 * α := by
  have ht : Real.tanh (g * r') ≤ r' :=
    (tanh_le_self (mul_nonneg hg0 hr')).trans (by nlinarith)
  exact hazard_le_two_mul α g r' r ε hα0 hα1 hr hε0 hround ht hε

/-! ## Telescoping radius factors and generation counts -/

/-- Paper: `eq:resproduct` (tanh_residual.tex): the radius factors
`r_j / r_{j+1}` of the expected normalized children telescope. -/
theorem offspring_product_telescope (r G : ℕ → ℝ) (hr : ∀ j, r j ≠ 0) (k : ℕ) :
    ∀ n, ∏ j ∈ Ico k (k + n), (r j / r (j + 1)) * G j =
      (r k / r (k + n)) * ∏ j ∈ Ico k (k + n), G j := by
  intro n
  induction n with
  | zero => simp [hr k]
  | succ n ih =>
      rw [← add_assoc, prod_Ico_succ_top (by omega), prod_Ico_succ_top (by omega), ih]
      have h1 := hr (k + n)
      have h2 := hr (k + n + 1)
      field_simp

/-- Paper: `sec:residual` (tanh_residual.tex): along a chain of `n` skips from
layer `k`, the skip probabilities `p r_j / r_{j+1}` telescope to `p^n r_k / r_{k+n}`. -/
theorem skip_chain_probability (p : ℝ) (r : ℕ → ℝ) (hr : ∀ j, r j ≠ 0) (k n : ℕ) :
    ∏ j ∈ Ico k (k + n), p * r j / r (j + 1) = p ^ n * (r k / r (k + n)) := by
  have h := offspring_product_telescope r (fun _ => p) hr k n
  simp only [prod_const, Nat.card_Ico, Nat.add_sub_cancel_left] at h
  rw [mul_comm (p ^ n), ← h]
  refine prod_congr rfl fun j _ => ?_
  ring

/-- Paper: `eq:resproduct` (tanh_residual.tex), "after the root gate, the
expected number of reached uncompressed calls at layer `k` is at most
`r_k ∏_{j=k}^{D-1} G_j`". The hypotheses are the root gate `n_D ≤ r_D` and the
expected offspring bound `(r_j / r_{j+1}) G_j` per reached call, which the paper
obtains by predictable charging. -/
theorem generation_mean_le (r G n : ℕ → ℝ) (D : ℕ) (hr : ∀ j, 0 < r j)
    (hG : ∀ j, 0 ≤ G j) (htop : n D ≤ r D)
    (hstep : ∀ k < D, n k ≤ n (k + 1) * ((r k / r (k + 1)) * G k)) :
    ∀ k ≤ D, n k ≤ r k * ∏ j ∈ Ico k D, G j := by
  have key : ∀ i, i ≤ D → n (D - i) ≤ r (D - i) * ∏ j ∈ Ico (D - i) D, G j := by
    intro i
    induction i with
    | zero => intro _; simpa using htop
    | succ i ih =>
        intro hi
        have hk : D - (i + 1) < D := by omega
        have hsucc : D - (i + 1) + 1 = D - i := by omega
        have hstep' := hstep (D - (i + 1)) hk
        rw [hsucc] at hstep'
        have ih' := ih (by omega)
        have hfac : 0 ≤ (r (D - (i + 1)) / r (D - i)) * G (D - (i + 1)) :=
          mul_nonneg (div_nonneg (hr _).le (hr _).le) (hG _)
        calc n (D - (i + 1)) ≤ n (D - i) * ((r (D - (i + 1)) / r (D - i)) *
              G (D - (i + 1))) := hstep'
          _ ≤ (r (D - i) * ∏ j ∈ Ico (D - i) D, G j) *
              ((r (D - (i + 1)) / r (D - i)) * G (D - (i + 1))) :=
              mul_le_mul_of_nonneg_right ih' hfac
          _ = r (D - (i + 1)) * ∏ j ∈ Ico (D - (i + 1)) D, G j := by
              rw [prod_eq_prod_Ico_succ_bot hk, hsucc]
              have := (hr (D - i)).ne'
              field_simp
  intro k hk
  have := key (D - k) (by omega)
  rwa [Nat.sub_sub_self hk] at this

/-- Paper: `eq:resproduct` (tanh_residual.tex). Leaves are the calls reached at
layer zero, and every reached call at a layer `k ≥ 1` is a proposal with
probability `h ≤ 2α`. With `r_0 = 1`, the generation bound gives
`E(J - 1) ≤ ∏_{j<D} G_j + 2α ∑_{k=1}^D r_k ∏_{j=k}^{D-1} G_j`. -/
theorem resproduct_bound (r G n : ℕ → ℝ) (D : ℕ) (α h : ℝ) (hr : ∀ j, 0 < r j)
    (hr0 : r 0 = 1) (hG : ∀ j, 0 ≤ G j) (hn : ∀ j, 0 ≤ n j) (htop : n D ≤ r D)
    (hstep : ∀ k < D, n k ≤ n (k + 1) * ((r k / r (k + 1)) * G k))
    (hh0 : 0 ≤ h) (hh : h ≤ 2 * α) :
    n 0 + h * ∑ k ∈ Icc 1 D, n k ≤
      ∏ j ∈ range D, G j + 2 * α * ∑ k ∈ Icc 1 D, r k * ∏ j ∈ Ico k D, G j := by
  have hgen := generation_mean_le r G n D hr hG htop hstep
  have h0 : n 0 ≤ ∏ j ∈ range D, G j := by
    have := hgen 0 (Nat.zero_le _)
    rwa [hr0, one_mul, ← range_eq_Ico] at this
  have hsum : ∑ k ∈ Icc 1 D, n k ≤ ∑ k ∈ Icc 1 D, r k * ∏ j ∈ Ico k D, G j :=
    sum_le_sum fun k hk => hgen k (mem_Icc.mp hk).2
  have hnn : 0 ≤ ∑ k ∈ Icc 1 D, n k := sum_nonneg fun k _ => hn k
  have h2 : h * ∑ k ∈ Icc 1 D, n k ≤ 2 * α * ∑ k ∈ Icc 1 D, r k * ∏ j ∈ Ico k D, G j :=
    mul_le_mul hh hsum hnn (by linarith)
  linarith

/-- Paper: proof of `thm:residualupper` (tanh_residual.tex). Summing the
per-layer logarithmic bound `log G_j ≤ 4 log (r_j / r_{j+1}) + a_j`, where the
remaining terms total at most `21` (here `4 · 5 = 20` from `eq:resintegrals` and
one for the rounding terms), gives `∏_{j=k}^{D-1} G_j ≤ e^{21} (r_k / r_D)^4`. -/
theorem log_product_bound (r G a : ℕ → ℝ) (k D : ℕ) (hkD : k ≤ D)
    (hr : ∀ j, 0 < r j) (hG : ∀ j, 0 < G j)
    (hstep : ∀ j ∈ Ico k D, Real.log (G j) ≤ 4 * Real.log (r j / r (j + 1)) + a j)
    (ha : ∑ j ∈ Ico k D, a j ≤ 21) :
    ∏ j ∈ Ico k D, G j ≤ Real.exp 21 * (r k / r D) ^ 4 := by
  have htel : ∀ n, ∑ j ∈ Ico k (k + n), Real.log (r j / r (j + 1)) =
      Real.log (r k / r (k + n)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [← add_assoc, sum_Ico_succ_top (by omega), ih,
          ← Real.log_mul (div_pos (hr _) (hr _)).ne' (div_pos (hr _) (hr _)).ne']
        congr 1
        have := (hr (k + n)).ne'
        field_simp
  have hpos : 0 < ∏ j ∈ Ico k D, G j := prod_pos fun j _ => hG j
  have hlog : Real.log (∏ j ∈ Ico k D, G j) ≤ 4 * Real.log (r k / r D) + 21 := by
    rw [Real.log_prod (fun j _ => (hG j).ne')]
    have h1 := sum_le_sum hstep
    rw [sum_add_distrib, ← mul_sum] at h1
    have h2 := htel (D - k)
    rw [Nat.add_sub_cancel' hkD] at h2
    linarith
  have hrat : 0 < r k / r D := div_pos (hr k) (hr D)
  calc ∏ j ∈ Ico k D, G j = Real.exp (Real.log (∏ j ∈ Ico k D, G j)) :=
        (Real.exp_log hpos).symm
    _ ≤ Real.exp (4 * Real.log (r k / r D) + 21) := Real.exp_le_exp.mpr hlog
    _ = Real.exp 21 * (r k / r D) ^ 4 := by
        rw [Real.exp_add, mul_comm,
          show 4 * Real.log (r k / r D) = Real.log ((r k / r D) ^ 4) by
            rw [Real.log_pow]; norm_num,
          Real.exp_log (pow_pos hrat 4)]

/-- Paper: proof of `thm:residualupper` (tanh_residual.tex): with `τ = αD`, the
radius bound `r_D ≥ (1 + αD)^{-1/2}` (`eq:resradiuslower` with `r_D ≥ R_D`) gives
`r_D^{-4} ≤ (1 + τ)^2`. -/
theorem inv_radius_pow_le (r : ℝ) (α : ℝ) (D : ℕ) (hα : 0 ≤ α)
    (h : 1 / Real.sqrt (1 + α * D) ≤ r) : r⁻¹ ^ 4 ≤ (1 + α * D) ^ 2 := by
  have hS : 0 < Real.sqrt (1 + α * D) := Real.sqrt_pos.mpr (by positivity)
  have hS2 : Real.sqrt (1 + α * D) ^ 2 = 1 + α * D := Real.sq_sqrt (by positivity)
  have hr : 0 < r := lt_of_lt_of_le (by positivity) h
  have hinv : r⁻¹ ≤ Real.sqrt (1 + α * D) := by
    rw [inv_le_comm₀ hr hS]
    simpa [one_div] using h
  calc r⁻¹ ^ 4 ≤ Real.sqrt (1 + α * D) ^ 4 := pow_le_pow_left₀ (by positivity) hinv 4
    _ = (1 + α * D) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hS2]

/-- Paper: `eq:rescriticalupper` with the prefactor `9 e^{21}` (proof of
`thm:residualupper`, tanh_residual.tex), with `τ = αD`. Insert the product bound
`hprod` (the conclusion of `log_product_bound`) into `eq:resproduct` (`hEJ`, see
`resproduct_bound`), use `α ∑_{k=1}^D r_k^5 ≤ 3` (`hfive`, proved as
`ExactSampling.ResidualDepth.resintegrals`) and `r_D ≥ (1 + αD)^{-1/2}`
(`hrD`, `eq:resradiuslower` with `r_D ≥ R_D`); adding the root operation gives
`E J ≤ 9 e^{21} (1 + αD)^2`. -/
theorem critical_assembly (r G : ℕ → ℝ) (D : ℕ) (α EJ : ℝ) (hr : ∀ j, 0 < r j)
    (hr0 : r 0 = 1) (hα : 0 ≤ α)
    (hprod : ∀ k ≤ D, ∏ j ∈ Ico k D, G j ≤ Real.exp 21 * (r k / r D) ^ 4)
    (hfive : α * ∑ k ∈ Icc 1 D, r k ^ 5 ≤ 3)
    (hrD : 1 / Real.sqrt (1 + α * D) ≤ r D)
    (hEJ : EJ ≤ 1 + (∏ j ∈ range D, G j +
      2 * α * ∑ k ∈ Icc 1 D, r k * ∏ j ∈ Ico k D, G j)) :
    EJ ≤ 9 * Real.exp 21 * (1 + α * D) ^ 2 := by
  have hE : 0 < Real.exp 21 := Real.exp_pos 21
  have hrD4 := inv_radius_pow_le (r D) α D hα hrD
  have hτ : (0 : ℝ) ≤ α * D := by positivity
  have h0 : ∏ j ∈ range D, G j ≤ Real.exp 21 * (r D)⁻¹ ^ 4 := by
    have := hprod 0 (Nat.zero_le _)
    rwa [← range_eq_Ico, hr0, one_div, ] at this
  have hk : ∀ k ∈ Icc 1 D, r k * ∏ j ∈ Ico k D, G j ≤
      Real.exp 21 * (r D)⁻¹ ^ 4 * r k ^ 5 := by
    intro k hk
    have hpk := hprod k (mem_Icc.mp hk).2
    calc r k * ∏ j ∈ Ico k D, G j ≤ r k * (Real.exp 21 * (r k / r D) ^ 4) :=
          mul_le_mul_of_nonneg_left hpk (hr k).le
      _ = Real.exp 21 * (r D)⁻¹ ^ 4 * r k ^ 5 := by
          rw [div_eq_mul_inv, mul_pow]
          ring
  have hsum : ∑ k ∈ Icc 1 D, r k * ∏ j ∈ Ico k D, G j ≤
      Real.exp 21 * (r D)⁻¹ ^ 4 * ∑ k ∈ Icc 1 D, r k ^ 5 := by
    rw [mul_sum]
    exact sum_le_sum hk
  have hX : 0 ≤ Real.exp 21 * (r D)⁻¹ ^ 4 := by positivity
  have hmid : ∏ j ∈ range D, G j + 2 * α * ∑ k ∈ Icc 1 D, r k * ∏ j ∈ Ico k D, G j ≤
      7 * (Real.exp 21 * (r D)⁻¹ ^ 4) := by
    have h2 : 2 * α * ∑ k ∈ Icc 1 D, r k * ∏ j ∈ Ico k D, G j ≤
        2 * (Real.exp 21 * (r D)⁻¹ ^ 4) * (α * ∑ k ∈ Icc 1 D, r k ^ 5) := by
      have := mul_le_mul_of_nonneg_left hsum (by linarith : 0 ≤ 2 * α)
      linarith [this]
    have h3 : 2 * (Real.exp 21 * (r D)⁻¹ ^ 4) * (α * ∑ k ∈ Icc 1 D, r k ^ 5) ≤
        2 * (Real.exp 21 * (r D)⁻¹ ^ 4) * 3 :=
      mul_le_mul_of_nonneg_left hfive (by linarith)
    linarith
  have hfin : 7 * (Real.exp 21 * (r D)⁻¹ ^ 4) ≤ 7 * (Real.exp 21 * (1 + α * D) ^ 2) := by
    have := mul_le_mul_of_nonneg_left hrD4 hE.le
    linarith
  have hone : 1 ≤ Real.exp 21 * (1 + α * D) ^ 2 := by
    have h1 : 1 ≤ Real.exp 21 := Real.one_le_exp (by norm_num)
    have h2 : 1 ≤ (1 + α * D) ^ 2 := by nlinarith
    nlinarith
  nlinarith

/-- Paper: proof of `thm:residualupper` (tanh_residual.tex), the rounding terms of
`eq:reslogproduct`: "by `eq:resradiuslower`, its sum over all layers is less than
one". If `r_j ≥ (1 + αD)^{-1/2}` for `j ≤ D` and `F_j ≥ r_{j+1} - 3αε`, with
`ε ≤ [100(D+1)^4]^{-1}`, then every `F_j ≥ 1/(2√(D+1))` and
`∑_{j<D} 12αε/F_j ≤ 1`. -/
theorem rounding_sum_le_one (α ε : ℝ) (D : ℕ) (r F : ℕ → ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / (100 * ((D : ℝ) + 1) ^ 4))
    (hrad : ∀ j, j ≤ D → 1 / Real.sqrt (1 + α * D) ≤ r j)
    (hF : ∀ j, j < D → r (j + 1) - 3 * α * ε ≤ F j) :
    (∀ j, j < D → 1 / (2 * Real.sqrt ((D : ℝ) + 1)) ≤ F j) ∧
      ∑ j ∈ range D, 12 * α * ε / F j ≤ 1 := by
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hN : (0 : ℝ) < D + 1 := by linarith
  have hs : 0 < Real.sqrt ((D : ℝ) + 1) := Real.sqrt_pos.mpr hN
  have hs2 : Real.sqrt ((D : ℝ) + 1) ^ 2 = D + 1 := Real.sq_sqrt hN.le
  have hs1 : 1 ≤ Real.sqrt ((D : ℝ) + 1) := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt ((D : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  have hsle : Real.sqrt ((D : ℝ) + 1) ≤ D + 1 := by nlinarith
  have hεD : ε * ((D : ℝ) + 1) ^ 4 ≤ 1 / 100 := by
    rw [le_div_iff₀ (by positivity)] at hε
    linarith
  -- `1/√(1+αD) ≥ 1/√(D+1)`
  have hrad' : 1 / Real.sqrt ((D : ℝ) + 1) ≤ 1 / Real.sqrt (1 + α * D) := by
    apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity))
    exact Real.sqrt_le_sqrt (by nlinarith)
  -- `3αε ≤ 1/(2√(D+1))`
  have h3 : 3 * α * ε ≤ 1 / (2 * Real.sqrt ((D : ℝ) + 1)) := by
    rw [le_div_iff₀ (by positivity)]
    have hp : ((D : ℝ) + 1) ≤ ((D : ℝ) + 1) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
    have : ε * ((D : ℝ) + 1) ≤ 1 / 100 := le_trans (mul_le_mul_of_nonneg_left hp hε0) hεD
    have hαε : α * ε ≤ ε := by nlinarith
    nlinarith
  have hFlow : ∀ j, j < D → 1 / (2 * Real.sqrt ((D : ℝ) + 1)) ≤ F j := by
    intro j hj
    have h1 := hF j hj
    have h2 := hrad (j + 1) (by omega)
    have e : 1 / Real.sqrt ((D : ℝ) + 1) = 2 * (1 / (2 * Real.sqrt ((D : ℝ) + 1))) := by
      field_simp
    linarith
  refine ⟨hFlow, ?_⟩
  have hterm : ∀ j ∈ range D, 12 * α * ε / F j ≤ 12 * ε * (2 * Real.sqrt ((D : ℝ) + 1)) := by
    intro j hj
    have hFj := hFlow j (mem_range.mp hj)
    have hF0 : 0 < F j := lt_of_lt_of_le (by positivity) hFj
    rw [div_le_iff₀ hF0]
    have : 1 ≤ 2 * Real.sqrt ((D : ℝ) + 1) * F j := by
      rw [div_le_iff₀ (by positivity)] at hFj
      linarith
    have h12 : 12 * α * ε ≤ 12 * ε := by nlinarith
    have : 0 ≤ 12 * ε * (2 * Real.sqrt ((D : ℝ) + 1)) := by positivity
    nlinarith
  calc ∑ j ∈ range D, 12 * α * ε / F j
      ≤ ∑ _j ∈ range D, 12 * ε * (2 * Real.sqrt ((D : ℝ) + 1)) := sum_le_sum hterm
    _ = (D : ℝ) * (12 * ε * (2 * Real.sqrt ((D : ℝ) + 1))) := by
        rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ 1 := by
        have h1 : (D : ℝ) * Real.sqrt ((D : ℝ) + 1) ≤ ((D : ℝ) + 1) ^ 4 := by
          have : (D : ℝ) * Real.sqrt ((D : ℝ) + 1) ≤ ((D : ℝ) + 1) * ((D : ℝ) + 1) :=
            mul_le_mul (by linarith) hsle hs.le (by linarith)
          have h24 : ((D : ℝ) + 1) ^ 2 ≤ ((D : ℝ) + 1) ^ 4 :=
            pow_le_pow_right₀ (by linarith) (by norm_num)
          nlinarith
        have h2 : ε * ((D : ℝ) * Real.sqrt ((D : ℝ) + 1)) ≤ 1 / 100 :=
          le_trans (mul_le_mul_of_nonneg_left h1 hε0) hεD
        nlinarith

/-- Paper: `eq:rescriticalupper` (proof of `thm:residualupper`, tanh_residual.tex),
composed from the per-layer bound `eq:reslogproduct` (`hstep`, proved as
`ExactSampling.ResidualDepth.reslogproduct_step` with
`ExactSampling.ResidualDepth.reschicritical`), the sums `eq:resintegrals` (`hfour`,
`hfive`, proved as `ExactSampling.ResidualDepth.resintegrals`), the radius bound
`r_j ≥ (1 + αD)^{-1/2}` (`hrad`: `eq:resradiuslower` with `r_j ≥ R_j`, which is the
rounding lemma `eq:resroundingerror`, a declared stand-in), `F_j ≥ r_{j+1} - 3αε`
(`hF`, `eq:resrounded`), and `eq:resproduct` (`hEJ`, from `resproduct_bound` and
predictable charging). Conclusion: `E J ≤ 9 e^{21} (1 + αD)^2`. -/
theorem critical_bound (r G F : ℕ → ℝ) (D : ℕ) (α ε EJ : ℝ) (hr : ∀ j, 0 < r j)
    (hr0 : r 0 = 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / (100 * ((D : ℝ) + 1) ^ 4)) (hG : ∀ j, 0 < G j)
    (hstep : ∀ j, j < D → Real.log (G j) ≤
      4 * Real.log (r j / r (j + 1)) + (5 * α * r j ^ 4 + 12 * α * ε / F j))
    (hrad : ∀ j, j ≤ D → 1 / Real.sqrt (1 + α * D) ≤ r j)
    (hF : ∀ j, j < D → r (j + 1) - 3 * α * ε ≤ F j)
    (hfour : α * ∑ j ∈ range D, r j ^ 4 ≤ 4) (hfive : α * ∑ k ∈ Icc 1 D, r k ^ 5 ≤ 3)
    (hEJ : EJ ≤ 1 + (∏ j ∈ range D, G j +
      2 * α * ∑ k ∈ Icc 1 D, r k * ∏ j ∈ Ico k D, G j)) :
    EJ ≤ 9 * Real.exp 21 * (1 + α * D) ^ 2 := by
  obtain ⟨hFlow, hround⟩ := rounding_sum_le_one α ε D r F hα0 hα1 hε0 hε hrad hF
  have hFpos : ∀ j, j < D → 0 < F j := fun j hj =>
    lt_of_lt_of_le (by have := Real.sqrt_nonneg ((D : ℝ) + 1); positivity) (hFlow j hj)
  have hprod : ∀ k ≤ D, ∏ j ∈ Ico k D, G j ≤ Real.exp 21 * (r k / r D) ^ 4 := by
    intro k hk
    refine log_product_bound r G (fun j => 5 * α * r j ^ 4 + 12 * α * ε / F j) k D hk hr hG
      (fun j hj => hstep j (mem_Ico.mp hj).2) ?_
    have hsub : Ico k D ⊆ range D := fun j hj => mem_range.mpr (mem_Ico.mp hj).2
    have hnn4 : ∀ j ∈ range D, 0 ≤ α * r j ^ 4 := fun j _ => by positivity
    have hnnF : ∀ j ∈ range D, 0 ≤ 12 * α * ε / F j := fun j hj =>
      div_nonneg (by positivity) (hFpos j (mem_range.mp hj)).le
    have h1 : ∑ j ∈ Ico k D, α * r j ^ 4 ≤ ∑ j ∈ range D, α * r j ^ 4 :=
      sum_le_sum_of_subset_of_nonneg hsub fun j hj _ => hnn4 j hj
    have h2 : ∑ j ∈ Ico k D, 12 * α * ε / F j ≤ ∑ j ∈ range D, 12 * α * ε / F j :=
      sum_le_sum_of_subset_of_nonneg hsub fun j hj _ => hnnF j hj
    rw [sum_add_distrib]
    have e1 : ∑ j ∈ Ico k D, 5 * α * r j ^ 4 = 5 * ∑ j ∈ Ico k D, α * r j ^ 4 := by
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by ring
    have e2 : ∑ j ∈ range D, α * r j ^ 4 = α * ∑ j ∈ range D, r j ^ 4 := by rw [mul_sum]
    linarith
  exact critical_assembly r G D α EJ hr hr0 hα0 hprod hfive (hrad D le_rfl) hEJ

/-! ## The raw root and the reverse geometric choice -/

/-- Paper: `eq:resrawrootidentity` (tanh_residual_fused.tex). Unrolling
`h_j = (1-α) h_{j-1} + α t_j` gives
`h_D = (1-α)^D h_0 + α ∑_{j=1}^D (1-α)^{D-j} t_j`. -/
theorem raw_root_unroll (α : ℝ) (h t : ℕ → ℝ)
    (hstep : ∀ j, h (j + 1) = (1 - α) * h j + α * t (j + 1)) (D : ℕ) :
    h D = (1 - α) ^ D * h 0 + α * ∑ j ∈ Icc 1 D, (1 - α) ^ (D - j) * t j := by
  induction D with
  | zero => simp
  | succ D ih =>
      rw [hstep, ih, sum_Icc_succ_top (by omega : 1 ≤ D + 1), Nat.sub_self, pow_zero,
        one_mul]
      have hs : ∑ j ∈ Icc 1 D, (1 - α) ^ (D + 1 - j) * t j =
          (1 - α) * ∑ j ∈ Icc 1 D, (1 - α) ^ (D - j) * t j := by
        rw [mul_sum]
        refine sum_congr rfl fun j hj => ?_
        have : D + 1 - j = (D - j) + 1 := by have := (mem_Icc.mp hj).2; omega
        rw [this, pow_succ]
        ring
      rw [hs, pow_succ]
      ring

/-- Paper: the reverse geometric choice in `tanh_residual_fused.tex` and the
proof of `thm:residualfused`. The last active layer is `j ∈ [1, D]` with
probability `α (1-α)^{D-j}`, and no layer is active with probability `(1-α)^D`;
these masses sum to one, and the root mixture (raw tanh sampler of mean `t_j` at
the last active layer, or `x` itself) has mean `h_D`. -/
theorem reverse_geometric_root (α x : ℝ) (t : ℕ → ℝ) (D : ℕ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    0 ≤ (1 - α) ^ D ∧ (∀ j ∈ Icc 1 D, 0 ≤ α * (1 - α) ^ (D - j)) ∧
      (1 - α) ^ D + ∑ j ∈ Icc 1 D, α * (1 - α) ^ (D - j) = 1 ∧
      (1 - α) ^ D * x + ∑ j ∈ Icc 1 D, α * (1 - α) ^ (D - j) * t j =
        (1 - α) ^ D * x + α * ∑ j ∈ Icc 1 D, (1 - α) ^ (D - j) * t j := by
  have hp : 0 ≤ 1 - α := by linarith
  refine ⟨pow_nonneg hp D, fun j _ => mul_nonneg hα0 (pow_nonneg hp _), ?_, ?_⟩
  · induction D with
    | zero => simp
    | succ D ih =>
        rw [sum_Icc_succ_top (by omega), Nat.sub_self, pow_zero]
        have hs : ∑ j ∈ Icc 1 D, α * (1 - α) ^ (D + 1 - j) =
            (1 - α) * ∑ j ∈ Icc 1 D, α * (1 - α) ^ (D - j) := by
          rw [mul_sum]
          refine sum_congr rfl fun j hj => ?_
          have : D + 1 - j = (D - j) + 1 := by have := (mem_Icc.mp hj).2; omega
          rw [this, pow_succ]
          ring
        rw [hs, pow_succ]
        linear_combination (1 - α) * ih
  · rw [mul_sum]
    congr 1
    exact sum_congr rfl fun j _ => by ring

/-! ## The residual mean network -/

/-- The scalar residual chain `F_{j+1} = p F_j + α tanh(s F_j)` of
`eq:reschainparameters`. -/
noncomputable def chain (α s z : ℝ) : ℕ → ℝ
  | 0 => z
  | j + 1 => (1 - α) * chain α s z j + α * Real.tanh (s * chain α s z j)

/-- The empirical mean of `m` coordinates. -/
noncomputable def meanOf {m : ℕ} (x : Fin m → ℝ) : ℝ := (∑ i, x i) / m

/-- The residual mean network: every row reads the mean of the same `m` relevant
coordinates with weight `s/m` and zero bias. -/
noncomputable def meanNet (α s : ℝ) {m : ℕ} (x : Fin m → ℝ) : ℕ → Fin m → ℝ
  | 0 => x
  | D + 1 => fun i => (1 - α) * meanNet α s x D i +
      α * Real.tanh (s * meanOf (meanNet α s x D))

/-- Auxiliary for `eq:resmeanidentity`: the mean of the residual network
follows the scalar chain. -/
theorem meanOf_meanNet (α s : ℝ) {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ) (D : ℕ) :
    meanOf (meanNet α s x D) = chain α s (meanOf x) D := by
  induction D with
  | zero => rfl
  | succ D ih =>
      simp only [meanNet, chain, meanOf] at ih ⊢
      rw [← ih, sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      field_simp

/-- Paper: `eq:resmeanidentity` (tanh_residual.tex): for the uniform residual
mean network, `h_{D,i} = F_D(M) + p^D (x_i - M)` with `M` the input mean. -/
theorem resmeanidentity (α s : ℝ) {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ) (D : ℕ)
    (i : Fin m) :
    meanNet α s x D i = chain α s (meanOf x) D + (1 - α) ^ D * (x i - meanOf x) := by
  induction D with
  | zero => simp [meanNet, chain]
  | succ D ih =>
      simp only [meanNet, chain]
      rw [ih, meanOf_meanNet α s hm x D, pow_succ]
      ring

/-- Paper: `thm:resmeanlaw` (tanh_residual.tex): a uniform-coordinate request has
mean `M`, so the centered deviations `x_i - M` average to zero over the `m`
relevant coordinates. -/
theorem sum_centered_deviation {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ) (c : ℝ) :
    ∑ i, c * (x i - meanOf x) = 0 := by
  rw [← mul_sum, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold meanOf
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  ring

/-- Paper: `cor:reslower` (tanh_residual.tex): "at `s = 1`, `a = λ = 1` and
`A = αD`". -/
theorem critical_A (α : ℝ) (D : ℕ) :
    (1 - α + α * 1) ^ D = 1 ∧
      α * 1 ^ 3 / (1 - α + α * 1) * ∑ j ∈ range D, (1 - α + α * 1) ^ (2 * j) = α * D := by
  have h : (1 : ℝ) - α + α * 1 = 1 := by ring
  rw [h]
  simp

/-- Paper: upper bounds of `thm:resmeanlaw` (tanh_residual.tex): replacing mass
`p^D` of a uniform-coordinate request (mean `M`) by a request for `x_1` changes the
mean by exactly `p^D (x_1 - M)` (a linear identity of mixture means). -/
theorem replace_uniform_request (w pD M x₁ rest : ℝ) :
    (w - pD) * M + pD * x₁ + rest = (w * M + rest) + pD * (x₁ - M) := by
  ring

/-! ## Arbitrary row norms -/

/-- Paper: `prop:largerow` (tanh_residual.tex). With `u = σ + |b_0|`,
`|b_0| ≤ 1`, and the majority count `Q_u ≤ 2 max{u, u^2}` of `lem:comptanharity`,
the expected child requests `(σ/u) Q_u` are at most `2σ max{1,u} ≤ 2σ(1+σ)`. -/
theorem child_requests_le (σ b₀ Q : ℝ) (hσ : 0 ≤ σ) (hb : |b₀| ≤ 1)
    (hu : 0 < σ + |b₀|) (hQ : Q ≤ 2 * max (σ + |b₀|) ((σ + |b₀|) ^ 2)) :
    σ / (σ + |b₀|) * Q ≤ 2 * σ * (1 + σ) := by
  set u := σ + |b₀| with hu_def
  have hfrac : 0 ≤ σ / u := div_nonneg hσ hu.le
  have hb0 : 0 ≤ |b₀| := abs_nonneg _
  calc σ / u * Q ≤ σ / u * (2 * max u (u ^ 2)) := mul_le_mul_of_nonneg_left hQ hfrac
    _ = 2 * σ * max 1 u := by
        rcases le_total u 1 with h | h
        · rw [max_eq_left (by nlinarith), max_eq_left h]
          field_simp
        · rw [max_eq_right (by nlinarith), max_eq_right h]
          field_simp
    _ ≤ 2 * σ * (1 + σ) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact max_le (by linarith) (by linarith)

/-- Auxiliary for `prop:largerow` and `cor:largeresidualsharpbits`: with
`b = 1 - α + α C`, `α (C - 1) ∑_{j<D} b^j = b^D - 1`. -/
theorem geom_sum_identity (α C : ℝ) (D : ℕ) :
    α * (C - 1) * ∑ j ∈ range D, (1 - α + α * C) ^ j = (1 - α + α * C) ^ D - 1 := by
  have h := mul_geom_sum (1 - α + α * C) D
  have : 1 - α + α * C - 1 = α * (C - 1) := by ring
  rw [this] at h
  rw [← h]

/-- Paper: `prop:largerow` (tanh_residual.tex): for `s ≥ 1`,
`b_s^D + α ∑_{j<D} b_s^j ≤ 4 b_s^D / 3`, with `C_s = 2 s (1+s)` and
`b_s = 1 - α + α C_s`. -/
theorem largeresidual_le (α s : ℝ) (D : ℕ) (hα0 : 0 ≤ α) (hs : 1 ≤ s) :
    (1 - α + α * (2 * s * (1 + s))) ^ D +
        α * ∑ j ∈ range D, (1 - α + α * (2 * s * (1 + s))) ^ j ≤
      4 / 3 * (1 - α + α * (2 * s * (1 + s))) ^ D := by
  set C := 2 * s * (1 + s) with hC
  set b := 1 - α + α * C with hb
  have hC4 : 4 ≤ C := by nlinarith
  have hid := geom_sum_identity α C D
  have hsum0 : 0 ≤ ∑ j ∈ range D, b ^ j :=
    sum_nonneg fun j _ => pow_nonneg
      (by nlinarith [mul_nonneg hα0 (by linarith : (0 : ℝ) ≤ C - 1)]) j
  have h3 : 3 * (α * ∑ j ∈ range D, b ^ j) ≤ b ^ D - 1 := by
    have : 3 * (α * ∑ j ∈ range D, b ^ j) ≤ (C - 1) * (α * ∑ j ∈ range D, b ^ j) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hα0 hsum0)
    linarith
  linarith

/-- Paper: `cor:largeresidualsharpbits` (tanh_residual_large_bits.tex):
`(1+s)^2 ≤ (4/3)(C_s - 1)` for `s ≥ 1`. -/
theorem residual_cost_absorption (s : ℝ) (hs : 1 ≤ s) :
    (1 + s) ^ 2 ≤ 4 / 3 * (2 * s * (1 + s) - 1) := by
  nlinarith

/-- Paper: `cor:largeresidualsharpbits` (tanh_residual_large_bits.tex):
`(1+s)^2 α ∑_{j<D} b_s^j ≤ (4/3)(b_s^D - 1)` for `s ≥ 1`, including `α = 0`. -/
theorem sharpbits_absorption (α s : ℝ) (D : ℕ) (hα0 : 0 ≤ α) (hs : 1 ≤ s) :
    (1 + s) ^ 2 * (α * ∑ j ∈ range D, (1 - α + α * (2 * s * (1 + s))) ^ j) ≤
      4 / 3 * ((1 - α + α * (2 * s * (1 + s))) ^ D - 1) := by
  set C := 2 * s * (1 + s) with hC
  have hid := geom_sum_identity α C D
  have hsum0 : 0 ≤ α * ∑ j ∈ range D, (1 - α + α * C) ^ j :=
    mul_nonneg hα0 (sum_nonneg fun j _ => pow_nonneg
      (by nlinarith [mul_nonneg hα0 (by nlinarith : (0 : ℝ) ≤ C - 1)]) j)
  have habs := residual_cost_absorption s hs
  have := mul_le_mul_of_nonneg_right habs hsum0
  nlinarith

/-- Paper: `cor:largeresidualsharpbits` (tanh_residual_large_bits.tex):
`C_s - 1 ≤ 4 s^2` and `b_s^D ≤ exp(4 α s^2 D)`. -/
theorem bs_pow_le_exp (α s : ℝ) (D : ℕ) (hα0 : 0 ≤ α) (hs : 1 ≤ s) :
    2 * s * (1 + s) - 1 ≤ 4 * s ^ 2 ∧
      (1 - α + α * (2 * s * (1 + s))) ^ D ≤ Real.exp (4 * α * s ^ 2 * D) := by
  have hC : 2 * s * (1 + s) - 1 ≤ 4 * s ^ 2 := by nlinarith
  refine ⟨hC, ?_⟩
  have hb0 : 0 ≤ 1 - α + α * (2 * s * (1 + s)) := by nlinarith
  have hb : 1 - α + α * (2 * s * (1 + s)) ≤ Real.exp (4 * α * s ^ 2) := by
    have := Real.add_one_le_exp (4 * α * s ^ 2)
    have h2 : α * (2 * s * (1 + s) - 1) ≤ α * (4 * s ^ 2) :=
      mul_le_mul_of_nonneg_left hC hα0
    nlinarith
  calc (1 - α + α * (2 * s * (1 + s))) ^ D ≤ Real.exp (4 * α * s ^ 2) ^ D :=
        pow_le_pow_left₀ hb0 hb D
    _ = Real.exp (4 * α * s ^ 2 * D) := by
        rw [← Real.exp_nat_mul]
        ring_nf

/-- Paper: proof of `prop:residuallargeslower` (tanh_residual.tex):
`tanh 1 ≥ 1/2` and `sech^2 1 ≥ 1/4`. -/
theorem tanh_one_sech_one : 1 / 2 ≤ Real.tanh 1 ∧ 1 / 4 ≤ 1 / Real.cosh 1 ^ 2 := by
  have he := Real.exp_one_gt_d9
  have he' := Real.exp_one_lt_d9
  have hpos := Real.exp_pos 1
  have hinv : Real.exp (-1) = 1 / Real.exp 1 := by rw [Real.exp_neg, one_div]
  have hc : Real.cosh 1 = (Real.exp 1 + Real.exp (-1)) / 2 := by rw [Real.cosh_eq]
  have hs : Real.sinh 1 = (Real.exp 1 - Real.exp (-1)) / 2 := by rw [Real.sinh_eq]
  have hcpos := Real.cosh_pos 1
  have hm : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  have hm0 : 0 < Real.exp (-1) := Real.exp_pos _
  constructor
  · rw [Real.tanh_eq_sinh_div_cosh, le_div_iff₀ hcpos, hc, hs]
    nlinarith
  · have h1 : Real.exp (-1) < 1 / 2 := by
      rw [hinv, div_lt_iff₀ hpos]
      linarith
    have h2 : (Real.exp 1 + Real.exp (-1)) / 2 < 2 := by linarith
    have h3 : 0 < (Real.exp 1 + Real.exp (-1)) / 2 := by positivity
    rw [div_le_div_iff₀ (by norm_num) (by positivity), one_mul, hc]
    nlinarith

/-- Paper: `prop:residuallargeslower` (tanh_residual.tex), the unknown-source
lower bound. From `U ≥ 1/2` (endpoint coupling) and the transcript bound
`U ≥ ((1 - s^{-2})/2) 2 α s^2 tanh 1 sech^2 1` (the second transcript inequality at
`z = 1/s`), one gets `U ≥ (3/64)(1 + α s^2)` for `s ≥ 2`. -/
theorem largeslower_unknown (α s U : ℝ) (hα0 : 0 ≤ α) (hs : 2 ≤ s) (hU1 : 1 / 2 ≤ U)
    (hU2 : (1 - s⁻¹ ^ 2) / 2 * (2 * α * s ^ 2) * Real.tanh 1 * (1 / Real.cosh 1 ^ 2) ≤ U) :
    3 / 64 * (1 + α * s ^ 2) ≤ U := by
  set th := Real.tanh 1
  set sc := 1 / Real.cosh 1 ^ 2
  have hth : 1 / 2 ≤ th := tanh_one_sech_one.1
  have hsc : 1 / 4 ≤ sc := tanh_one_sech_one.2
  have hs0 : 0 < s := by linarith
  have hinv : s⁻¹ ^ 2 ≤ 1 / 4 := by
    rw [inv_pow, ← one_div]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hx : 0 ≤ α * s ^ 2 := by positivity
  have h1 : 3 / 8 ≤ (1 - s⁻¹ ^ 2) / 2 := by linarith
  have h2 : 3 * α * s ^ 2 / 32 ≤ U := by
    have hA : 0 ≤ 2 * α * s ^ 2 := by positivity
    have e1 : 3 / 8 * (2 * α * s ^ 2) ≤ (1 - s⁻¹ ^ 2) / 2 * (2 * α * s ^ 2) :=
      mul_le_mul_of_nonneg_right h1 hA
    have e2 : 3 / 8 * (2 * α * s ^ 2) * (1 / 2) ≤
        (1 - s⁻¹ ^ 2) / 2 * (2 * α * s ^ 2) * th :=
      mul_le_mul e1 hth (by norm_num) (by nlinarith)
    have e3 : 3 / 8 * (2 * α * s ^ 2) * (1 / 2) * (1 / 4) ≤
        (1 - s⁻¹ ^ 2) / 2 * (2 * α * s ^ 2) * th * sc :=
      mul_le_mul e2 hsc (by norm_num) (by nlinarith)
    nlinarith
  nlinarith

/-- Paper: `prop:residuallargeslower` (tanh_residual.tex), the finite-network
lower bound. Let `q₀ = min{s^2, m}`. The bending and transcript argument (a declared
stand-in) gives `Q* ≥ 3 α h^2 / (16 R)` whenever `T = 2R/h ≤ 1/2`; with `h^2 ≥ q₀/4`
and `R ≤ 1`, the theorem checks `T ≤ 1/2` when `q₀ ≥ 64`. Together with
`Q* ≥ 1/2` this gives `Q* ≥ (1 + α q₀)/130` in all cases. -/
theorem largeslower_finite (α q₀ h R Q : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hq : 0 ≤ q₀) (hQ1 : 1 / 2 ≤ Q) (hR0 : 0 < R) (hR1 : R ≤ 1) (hh0 : 0 ≤ h)
    (hh : q₀ / 4 ≤ h ^ 2) (hbend : 2 * R / h ≤ 1 / 2 → 3 * α * h ^ 2 / (16 * R) ≤ Q) :
    (1 + α * q₀) / 130 ≤ Q := by
  rcases lt_or_ge q₀ 64 with hq64 | hq64
  · have : α * q₀ ≤ 64 := by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - α) hq]
    linarith
  · have hh4 : 4 ≤ h := by nlinarith
    have hT : 2 * R / h ≤ 1 / 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hb := hbend hT
    have h1 : 3 * α * q₀ / 64 ≤ 3 * α * h ^ 2 / (16 * R) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [mul_nonneg hα0 (by linarith : (0 : ℝ) ≤ 4 * h ^ 2 - q₀),
        mul_nonneg (mul_nonneg hα0 hq) (by linarith : (0 : ℝ) ≤ 1 - R)]
    have : α * q₀ ≥ 0 := by positivity
    nlinarith

/-- Paper: `prop:residuallargeslower` (tanh_residual.tex): the derivative bound
`h ≥ s / √(1 + 3 s^2/m)` implies `h^2 ≥ min{s^2, m}/4`. -/
theorem h_sq_ge_min (s m h : ℝ) (hm : 0 < m)
    (hh : s ^ 2 / (1 + 3 * s ^ 2 / m) ≤ h ^ 2) : min (s ^ 2) m / 4 ≤ h ^ 2 := by
  have hd : 0 < 1 + 3 * s ^ 2 / m := by positivity
  refine le_trans ?_ hh
  rw [le_div_iff₀ hd]
  rcases le_total (s ^ 2) m with h1 | h1
  · rw [min_eq_left h1]
    have : 3 * s ^ 2 / m ≤ 3 := by rw [div_le_iff₀ hm]; linarith
    nlinarith [sq_nonneg s]
  · rw [min_eq_right h1]
    have : m / 4 * (3 * s ^ 2 / m) = 3 * s ^ 2 / 4 := by field_simp
    nlinarith

/-- Paper: unknown-source lower bound in `thm:resmeanlaw` (tanh_residual.tex).
Endpoint coupling gives `U ≥ R`, the range lemma `lem:resrange` gives
`λ/√(1+A) ≤ R ≤ λ/√(1+A/5)`, and the bending and transcript argument (a declared
stand-in) gives `U ≥ 3 λ^2 / (16 R)` whenever `T = 2R/λ ≤ 1/2`; the theorem checks
`T ≤ 1/2` for `A ≥ 80`. Then `U ≥ λ √(1+A) / 81`. -/
theorem resmean_unknown_lower (lam A R U : ℝ) (hlam : 0 < lam) (hA : 0 ≤ A)
    (hRlow : lam / Real.sqrt (1 + A) ≤ R) (hRup : R ≤ lam / Real.sqrt (1 + A / 5))
    (hUR : R ≤ U) (hbend : 2 * R / lam ≤ 1 / 2 → 3 * lam ^ 2 / (16 * R) ≤ U) :
    lam * Real.sqrt (1 + A) / 81 ≤ U := by
  have hs : 0 < Real.sqrt (1 + A) := Real.sqrt_pos.mpr (by linarith)
  have hsq := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 + A)
  have hR0 : 0 < R := lt_of_lt_of_le (div_pos hlam hs) hRlow
  rcases lt_or_ge A 80 with hA80 | hA80
  · have hs9 : Real.sqrt (1 + A) ≤ 9 := by nlinarith
    have : lam * Real.sqrt (1 + A) / 81 ≤ lam / Real.sqrt (1 + A) := by
      rw [div_le_div_iff₀ (by norm_num) hs]
      nlinarith
    linarith
  · have hs5 : 0 < Real.sqrt (1 + A / 5) := Real.sqrt_pos.mpr (by linarith)
    have hsq5 := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 + A / 5)
    have hs54 : 4 ≤ Real.sqrt (1 + A / 5) := by nlinarith
    have hT : 2 * R / lam ≤ 1 / 2 := by
      rw [div_le_iff₀ hlam]
      have : R * Real.sqrt (1 + A / 5) ≤ lam := by
        rw [le_div_iff₀ hs5] at hRup
        exact hRup
      nlinarith
    have hb := hbend hT
    -- `3 λ^2/(16 R) ≥ 3 λ √(1 + A/5) / 16`
    have h1 : 3 * lam * Real.sqrt (1 + A / 5) / 16 ≤ 3 * lam ^ 2 / (16 * R) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      have : R * Real.sqrt (1 + A / 5) ≤ lam := by
        rw [le_div_iff₀ hs5] at hRup
        exact hRup
      nlinarith
    -- `√(1+A) ≤ √5 √(1 + A/5) ≤ (9/4) √(1 + A/5)`
    have h2 : Real.sqrt (1 + A) ≤ 9 / 4 * Real.sqrt (1 + A / 5) := by
      rw [show (1 + A) = 5 * (1 + A / 5) - 4 by ring]
      have : Real.sqrt (5 * (1 + A / 5) - 4) ≤ Real.sqrt (5 * (1 + A / 5)) :=
        Real.sqrt_le_sqrt (by linarith)
      rw [Real.sqrt_mul (by norm_num)] at this
      have h5 : Real.sqrt 5 ≤ 9 / 4 := by
        rw [show (9 / 4 : ℝ) = Real.sqrt ((9 / 4) ^ 2) by
          rw [Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num)
      nlinarith
    nlinarith

/-- Auxiliary: `√5 ≤ 9/4`. -/
theorem sqrt_five_le : Real.sqrt 5 ≤ 9 / 4 := by
  rw [show (9 / 4 : ℝ) = Real.sqrt ((9 / 4) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- Paper: finite-input lower bound in `thm:resmeanlaw` (tanh_residual.tex),
the case analysis giving `Q* ≥ Ξ/512` with `Ξ = λ min{√(1+A), m/√(1+A)}`. The
inputs are endpoint coupling `Q* ≥ R`, the range lemma `lem:resrange`, the
derivative bound `eq:resfinitehprime` `h ≥ λ/√(1+3A/m)`, the bending and
transcript bound `Q* ≥ 3 h^2/(16 R)` whenever `T = 2R/h ≤ 1/2`, and the
balanced-input coupling bound `Q* ≥ λ/√(1 + 4A/m^2)`. The theorem checks that
`T ≤ 1/2` in the case `A, m ≥ 400` and that every case gives the constant
`1/512`. -/
theorem resmean_finite_lower (lam A m R h Q : ℝ) (hlam : 0 < lam) (hA : 0 ≤ A)
    (hm : 1 ≤ m) (hRlow : lam / Real.sqrt (1 + A) ≤ R)
    (hRup : R ≤ lam / Real.sqrt (1 + A / 5)) (hQR : R ≤ Q)
    (hh : lam / Real.sqrt (1 + 3 * A / m) ≤ h)
    (hbend : 2 * R / h ≤ 1 / 2 → 3 * h ^ 2 / (16 * R) ≤ Q)
    (hbal : lam / Real.sqrt (1 + 4 * A / m ^ 2) ≤ Q) :
    lam * min (Real.sqrt (1 + A)) (m / Real.sqrt (1 + A)) / 512 ≤ Q := by
  set S := Real.sqrt (1 + A) with hS
  have hS0 : 0 < S := Real.sqrt_pos.mpr (by linarith)
  have hS2 : S ^ 2 = 1 + A := Real.sq_sqrt (by linarith)
  have hm0 : 0 < m := by linarith
  have hmin1 : min S (m / S) ≤ S := min_le_left _ _
  have hmin2 : min S (m / S) ≤ m / S := min_le_right _ _
  have hmin0 : 0 ≤ min S (m / S) := le_min hS0.le (by positivity)
  have hR0 : 0 < R := lt_of_lt_of_le (div_pos hlam hS0) hRlow
  rcases lt_or_ge A 400 with hA4 | hA4
  · -- endpoint coupling suffices
    have h1 : lam * min S (m / S) / 512 ≤ lam / S := by
      rw [div_le_div_iff₀ (by norm_num) hS0]
      have : lam * min S (m / S) * S ≤ lam * S * S :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin1 hlam.le) hS0.le
      nlinarith
    linarith
  rcases le_or_gt 400 m with hm4 | hm4
  · -- the bending interval is short and the transcript bound applies
    set S5 := Real.sqrt (1 + A / 5) with hS5
    set Sm := Real.sqrt (1 + 3 * A / m) with hSm
    have hS50 : 0 < S5 := Real.sqrt_pos.mpr (by linarith)
    have hSm0 : 0 < Sm := Real.sqrt_pos.mpr (by positivity)
    have hS52 : S5 ^ 2 = 1 + A / 5 := Real.sq_sqrt (by linarith)
    have hSm2 : Sm ^ 2 = 1 + 3 * A / m := Real.sq_sqrt (by positivity)
    have hAm : 3 * A / m ≤ 3 * A / 400 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) hm4
    have h4 : 4 * Sm ≤ S5 := by
      have : (4 * Sm) ^ 2 ≤ S5 ^ 2 := by
        rw [mul_pow, hSm2, hS52]
        linarith
      exact le_of_sq_le_sq this hS50.le
    have e1 : R * S5 ≤ lam := by rwa [le_div_iff₀ hS50] at hRup
    have e2 : lam ≤ h * Sm := by rwa [div_le_iff₀ hSm0] at hh
    have hh0 : 0 < h := lt_of_lt_of_le (div_pos hlam hSm0) hh
    have hT : 2 * R / h ≤ 1 / 2 := by
      rw [div_le_iff₀ hh0]
      have e3 : R * (4 * Sm) ≤ R * S5 := mul_le_mul_of_nonneg_left h4 hR0.le
      have e4 : 4 * R * Sm ≤ h * Sm := by linarith
      have e5 : 4 * R ≤ h := le_of_mul_le_mul_right e4 hSm0
      linarith
    have hQ := hbend hT
    have hq1 : 3 * lam * S5 / (16 * Sm ^ 2) ≤ 3 * h ^ 2 / (16 * R) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have e3 : lam ^ 2 ≤ h ^ 2 * Sm ^ 2 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ hlam.le e2 2
      have e4 : 3 * lam * S5 * (16 * R) = 48 * lam * (R * S5) := by ring
      have e5 : 48 * lam * (R * S5) ≤ 48 * lam * lam :=
        mul_le_mul_of_nonneg_left e1 (by positivity)
      have e6 : 48 * lam * lam ≤ 48 * (h ^ 2 * Sm ^ 2) := by nlinarith
      nlinarith
    have hK : 3 * lam * S5 / (16 * Sm ^ 2) ≤ Q := le_trans hq1 hQ
    have hSS5 : S ≤ 9 / 4 * S5 := by
      have : S ^ 2 ≤ (9 / 4 * S5) ^ 2 := by
        rw [mul_pow, hS2, hS52]
        linarith
      exact le_of_sq_le_sq this (by positivity)
    rcases le_total (S ^ 2) m with hSm' | hSm'
    · have hd : 16 * Sm ^ 2 ≤ 64 := by
        rw [hSm2]
        have : 3 * A / m ≤ 3 := by
          rw [div_le_iff₀ hm0]
          linarith
        linarith
      have hK2 : 3 * lam * S5 / 64 ≤ 3 * lam * S5 / (16 * Sm ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hd
      have e1 : lam * min S (m / S) ≤ lam * S := mul_le_mul_of_nonneg_left hmin1 hlam.le
      have e2 : lam * S ≤ lam * (9 / 4 * S5) := mul_le_mul_of_nonneg_left hSS5 hlam.le
      have e3 : 0 ≤ lam * S5 := by positivity
      linarith
    · have hd : 16 * Sm ^ 2 ≤ 64 * S ^ 2 / m := by
        rw [hSm2, le_div_iff₀ hm0]
        have : (1 + 3 * A / m) * m = m + 3 * A := by field_simp
        nlinarith
      have hK2 : 3 * lam * S5 / (64 * S ^ 2 / m) ≤ 3 * lam * S5 / (16 * Sm ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hd
      have hK3 : 3 * lam * S5 / (64 * S ^ 2 / m) = 3 * lam * S5 * m / (64 * S ^ 2) := by
        field_simp
      have e1 : lam * min S (m / S) ≤ lam * (m / S) :=
        mul_le_mul_of_nonneg_left hmin2 hlam.le
      have e2 : lam * (m / S) / 512 ≤ 3 * lam * S5 * m / (64 * S ^ 2) := by
        rw [mul_div_assoc', div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have e3 : lam * m * S ≤ lam * m * (9 / 4 * S5) :=
          mul_le_mul_of_nonneg_left hSS5 (by positivity)
        have e4 : lam * m * (64 * S ^ 2) = 64 * S * (lam * m * S) := by ring
        have e5 : 3 * lam * S5 * m * (S * 512) = 64 * S * (24 * (lam * m * S5)) := by ring
        rw [e4, e5]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : 0 ≤ lam * m * S5 := by positivity
        linarith
      linarith
  · -- few inputs: the balanced-input coupling bound
    set Sb := Real.sqrt (1 + 4 * A / m ^ 2) with hSb
    have hSb0 : 0 < Sb := Real.sqrt_pos.mpr (by positivity)
    have hSb2 : Sb ^ 2 = 1 + 4 * A / m ^ 2 := Real.sq_sqrt (by positivity)
    rcases le_total A (m ^ 2) with hAm | hAm
    · have hb : Sb ≤ 9 / 4 := by
        have : Sb ^ 2 ≤ (9 / 4) ^ 2 := by
          rw [hSb2]
          have : 4 * A / m ^ 2 ≤ 4 := by
            rw [div_le_iff₀ (by positivity)]
            linarith
          norm_num
          linarith
        exact le_of_sq_le_sq this (by norm_num)
      have hq : 4 / 9 * lam ≤ Q := by
        refine le_trans ?_ hbal
        rw [le_div_iff₀ hSb0]
        have : 4 / 9 * lam * Sb ≤ 4 / 9 * lam * (9 / 4) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
        linarith
      have hmin20 : min S (m / S) ≤ 20 := by
        have e : min S (m / S) ^ 2 ≤ 20 ^ 2 := by
          have : min S (m / S) ^ 2 ≤ S * (m / S) := by
            rw [sq]
            exact mul_le_mul hmin1 hmin2 hmin0 hS0.le
          have e : S * (m / S) = m := by field_simp
          linarith
        exact le_of_sq_le_sq e (by norm_num)
      have : lam * min S (m / S) ≤ lam * 20 := mul_le_mul_of_nonneg_left hmin20 hlam.le
      linarith
    · have hb : Sb ≤ 9 / 4 * S / m := by
        have : Sb ^ 2 ≤ (9 / 4 * S / m) ^ 2 := by
          rw [hSb2, div_pow, mul_pow, hS2, le_div_iff₀ (by positivity)]
          have : (1 + 4 * A / m ^ 2) * m ^ 2 = m ^ 2 + 4 * A := by field_simp
          rw [this]
          linarith
        exact le_of_sq_le_sq this (by positivity)
      have hq : 4 / 9 * (lam * m / S) ≤ Q := by
        refine le_trans ?_ hbal
        rw [le_div_iff₀ hSb0]
        calc 4 / 9 * (lam * m / S) * Sb ≤ 4 / 9 * (lam * m / S) * (9 / 4 * S / m) :=
              mul_le_mul_of_nonneg_left hb (by positivity)
          _ = lam := by field_simp
      have : lam * min S (m / S) ≤ lam * m / S := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hmin2 hlam.le
      have : 0 ≤ lam * m / S := by positivity
      linarith

/-- Paper: `cor:reslower` (tanh_residual.tex): for `α > 0` and `s = 1 + δ > 1`,
`A = (α s^3 / a) ∑_{j<D} a^{2j} ≤ s^3 λ^2 / (2δ)` with `a = 1 - α + α s` and
`λ = a^D`. -/
theorem reslower_A_le (α s : ℝ) (D : ℕ) (hα : 0 < α) (hs : 1 < s) :
    α * s ^ 3 / (1 - α + α * s) * ∑ j ∈ range D, (1 - α + α * s) ^ (2 * j) ≤
      s ^ 3 * ((1 - α + α * s) ^ D) ^ 2 / (2 * (s - 1)) := by
  set a := 1 - α + α * s with ha
  have ha1 : 1 ≤ a := by nlinarith
  have ha0 : 0 < a := by linarith
  have hδ : 0 < s - 1 := by linarith
  have hgeom : (a ^ 2 - 1) * ∑ j ∈ range D, (a ^ 2) ^ j = (a ^ 2) ^ D - 1 :=
    mul_geom_sum (a ^ 2) D
  have hpow : ∀ j, a ^ (2 * j) = (a ^ 2) ^ j := fun j => pow_mul a 2 j
  simp_rw [hpow]
  have hfac : a ^ 2 - 1 = α * (s - 1) * (a + 1) := by rw [ha]; ring
  have hsum0 : 0 ≤ ∑ j ∈ range D, (a ^ 2) ^ j := sum_nonneg fun j _ => by positivity
  have hlam : ((a ^ 2) ^ D) = (a ^ D) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [div_mul_eq_mul_div, div_le_div_iff₀ ha0 (by positivity)]
  have hkey : α * (s - 1) * (∑ j ∈ range D, (a ^ 2) ^ j) * (a + 1) =
      (a ^ D) ^ 2 - 1 := by
    rw [← hlam, ← hgeom, hfac]
    ring
  have hs3 : 0 < s ^ 3 := by positivity
  have hX : 0 ≤ (a ^ D) ^ 2 := by positivity
  have h2 : 2 ≤ a * (a + 1) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg hs3.le hX)]

/-- Paper: `eq:ressuperlower` in `cor:reslower` (tanh_residual.tex). From
`Q ≥ λ^2 / (1 + (3m-2) A / m^2)` and `A ≤ s^3 λ^2 / (2δ)`, the elementary
minimum inequality gives `Q ≥ (2δ/(2δ + 3s^3)) min{λ^2, m}`; here
`λ = (1 + αδ)^D`. -/
theorem ressuperlower (lam2 A m δ s Q : ℝ) (hl : 0 ≤ lam2) (hA : 0 ≤ A) (hm : 1 ≤ m)
    (hδ : 0 < δ) (hs : 0 < s)
    (hQ : lam2 / (1 + (3 * m - 2) * A / m ^ 2) ≤ Q) (hAle : A ≤ s ^ 3 * lam2 / (2 * δ)) :
    2 * δ / (2 * δ + 3 * s ^ 3) * min lam2 m ≤ Q := by
  have hm0 : 0 < m := by linarith
  have hden : 1 + (3 * m - 2) * A / m ^ 2 ≤ 1 + 3 * s ^ 3 * lam2 / (2 * δ * m) := by
    have e1 : (3 * m - 2) * A / m ^ 2 ≤ 3 * A / m := by
      rw [div_le_div_iff₀ (by positivity) hm0]
      nlinarith
    have e2 : 3 * A / m ≤ 3 * s ^ 3 * lam2 / (2 * δ * m) := by
      rw [div_le_div_iff₀ hm0 (by positivity)]
      have := mul_le_mul_of_nonneg_left hAle (by positivity : (0 : ℝ) ≤ 3 * (2 * δ * m))
      have e3 : 3 * (2 * δ * m) * (s ^ 3 * lam2 / (2 * δ)) = 3 * s ^ 3 * lam2 * m := by
        field_simp
      nlinarith
    linarith
  have hpos : 0 < 1 + (3 * m - 2) * A / m ^ 2 := by
    have : 0 ≤ (3 * m - 2) * A / m ^ 2 := by
      apply div_nonneg _ (by positivity)
      exact mul_nonneg (by linarith) hA
    linarith
  have hQ' : lam2 / (1 + 3 * s ^ 3 * lam2 / (2 * δ * m)) ≤ Q :=
    le_trans (div_le_div_of_nonneg_left hl hpos hden) hQ
  refine le_trans ?_ hQ'
  set c := 3 * s ^ 3 / (2 * δ) with hc
  have hc0 : 0 < c := by positivity
  have hfrac : 2 * δ / (2 * δ + 3 * s ^ 3) = 1 / (1 + c) := by
    rw [hc]
    field_simp
  have hrw : 1 + 3 * s ^ 3 * lam2 / (2 * δ * m) = 1 + c * lam2 / m := by
    rw [hc]
    field_simp
  rw [hfrac, hrw]
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  rcases le_total lam2 m with h1 | h1
  · rw [min_eq_left h1]
    have : c * lam2 / m ≤ c := by
      rw [div_le_iff₀ hm0]
      nlinarith
    nlinarith
  · rw [min_eq_right h1]
    have : c * lam2 / m * m = c * lam2 := by field_simp
    nlinarith

/-- Paper: the comparison of the exponential scales after `thm:residualupper`
(tanh_residual.tex): `x/2 ≤ log(1 + x) ≤ x` for `0 ≤ x ≤ 1`, with `x = α(s-1)`. -/
theorem half_le_log_one_add (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ Real.log (1 + x) ∧ Real.log (1 + x) ≤ x := by
  constructor
  · rw [Real.le_log_iff_exp_le (by linarith)]
    have h := Real.exp_bound_div_one_sub_of_interval (x := x / 2) (by linarith)
      (by linarith)
    refine h.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · have := Real.add_one_le_exp x
    rw [Real.log_le_iff_le_exp (by linarith)]
    linarith

end ExactSampling.ResidualSampling
