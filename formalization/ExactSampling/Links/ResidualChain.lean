import ExactSampling.Residual.ResidualSampling
import ExactSampling.Residual.ResidualDepth
import ExactSampling.Residual.Potential

/-!
# The critical residual bound and the residual mean-network bounds, assembled

Paper: `tanh_residual.tex`, Theorem `thm:residualupper` (`eq:rescriticalupper`, with
`eq:resrounded`, `eq:resroundingerror`, `eq:resradiuslower`, `eq:resproduct`,
`eq:reslogproduct`, `eq:resintegrals` and Lemma `lem:resradial`), Proposition `prop:largerow`,
Theorem `thm:resmeanlaw` with Lemma `lem:resrange`; `tanh_residual_fused.tex`, the local step
of the proof of `thm:residualfused`.

`ExactSampling.ResidualSampling` states several results with hypotheses that are proved in
`ExactSampling.ResidualDepth`; `ExactSampling.Potential` takes two facts as declared
stand-ins. This module composes them.

## The critical bound

`critical_bound_rounded` is `ResidualSampling.critical_bound` for the stored radii of
`eq:resrounded` at gain `g = 1` (row norms at most one): `r_0 = 1`,
`r_{j+1} = f_{α,1}(r_j) + e_{j+1}` with `f_{α,1}(r) = (1-α) r + α tanh r` and
`0 ≤ e_{j+1} ≤ 3αε`, and offspring factors `G_j = 1 - α + α χ_1(r_j)`. All of its inputs except
`eq:resproduct` are discharged:
* the rounding lemma `eq:resroundingerror` (`R_j ≤ r_j ≤ 1`, `r_j - R_j ≤ 3jαε` for the ideal
  radii `R_j = ResidualDepth.chain α 1 1 j`) is proved here (`radii_rounding`), by the
  argument the paper refers to: `f_{α,1}` is monotone and `1`-Lipschitz, and
  `f_{α,1}(1) + 3αε ≤ 1`. In both imported modules this lemma is a declared stand-in;
* `eq:resradiuslower` (`radius_lower`) from `ResidualDepth.ideal_radius_lower`;
* the per-layer bound `eq:reslogproduct` from `ResidualDepth.reslogproduct_step` and
  `ResidualDepth.reschicritical` (`eq:reschicritical` of `lem:resradial`);
* `eq:resintegrals` from `ResidualDepth.resintegrals` and `ResidualDepth.ideal_radius_upper`;
* `F_j ≥ r_{j+1} - 3αε` from the recursion.
The remaining hypothesis `hEJ` is `eq:resproduct`, which rests on the probabilistic recursion
and predictable charging (not formalized).

## Other compositions

* `child_requests_formula`: `ResidualSampling.child_requests_le` (`prop:largerow`) with the
  count bound `Q_u ≤ 2 max{u, u²}` supplied by `ResidualDepth.majority_count_le`
  (`lem:comptanharity`), for the integral formula of `Q_u`.
* `resmean_unknown_lower_range`, `resmean_finite_lower_range`: the lower bounds of
  `thm:resmeanlaw` with the range bounds of `lem:resrange` (`ResidualDepth.resrange`) supplied
  for `R = F_D(1)`, and, in the finite case, the balanced-input bound `λ/√(1 + 4A/m²)` derived
  from the coupling estimate `Q* ≥ (m/2) F_D(2/m)` and `lem:resrange` at `z = 2/m`.
* `weighted_local_step_radius`, `rpow_neg_le_radius`: the two declared stand-ins of
  `ExactSampling.Potential` in the proof of `thm:residualfused` (`d_j ≥ r_j²/3 - r_j⁴/5` and
  `r_j ≥ (1 + αD)^{-1/2}`), discharged by `ResidualDepth.tanh_le_quintic` and
  `radius_lower_depth`.

## Not formalized

`eq:resproduct` and its probabilistic setting; the endpoint coupling, bending and transcript
bounds and `eq:resfinitehprime` in `thm:resmeanlaw` (hypotheses, as in `ResidualSampling`);
the identification of the integral formula `Q_u` with the expected full-majority count; the
supercritical case `g > 1` of the rounding lemma.
-/

namespace ExactSampling.Links.ResidualChain

open Finset

/-! ## The critical residual step and the rounding lemma -/

/-- The critical residual map `f_{α,1}(r) = (1-α) r + α tanh r` of `eq:resrounded`
(tanh_residual.tex). -/
noncomputable def fcrit (α r : ℝ) : ℝ := (1 - α) * r + α * Real.tanh r

/-- The ideal radii are the iterates of `f_{α,1}`: `R_{j+1} = f_{α,1}(R_j)`. Paper:
`thm:residualupper` (tanh_residual.tex), "Let `R_0 = 1` and `R_{j+1} = f_{α,g}(R_j)`". -/
theorem chain_succ (α : ℝ) (j : ℕ) :
    ResidualDepth.chain α 1 1 (j + 1) = fcrit α (ResidualDepth.chain α 1 1 j) := by
  simp [ResidualDepth.chain, fcrit]

/-- `f_{α,1}` is monotone. Auxiliary for `eq:resroundingerror` (tanh_residual.tex). -/
theorem fcrit_mono {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {x y : ℝ} (h : x ≤ y) :
    fcrit α x ≤ fcrit α y := by
  unfold fcrit
  have h1 := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 1 - α)
  have h2 := mul_le_mul_of_nonneg_left (ResidualDepth.tanh_monotone h) hα0
  linarith

/-- `f_{α,1}` is `1`-Lipschitz: `f(y) - f(x) ≤ y - x` for `x ≤ y`. Auxiliary for
`eq:resroundingerror` (tanh_residual.tex), "the proof of Lemma `lem:rounding` applies with
per-step error `3αε`". -/
theorem fcrit_sub_le {α : ℝ} (hα0 : 0 ≤ α) {x y : ℝ} (h : x ≤ y) :
    fcrit α y - fcrit α x ≤ y - x := by
  unfold fcrit
  have h1 := mul_le_mul_of_nonneg_left (ResidualDepth.tanh_sub_le x y h) hα0
  nlinarith

/-- `f_{α,1}(1) ≤ 1 - α/5`, from `tanh 1 ≤ 4/5`. Auxiliary for `eq:resroundingerror`
(tanh_residual.tex), "The upper bound one follows from `f_{α,g}(1) + 3αε < 1`". -/
theorem fcrit_one_le {α : ℝ} (hα0 : 0 ≤ α) : fcrit α 1 ≤ 1 - α / 5 := by
  unfold fcrit
  have h := ResidualDepth.tanh_le_mul_one_sub_fifth (r := 1) zero_le_one le_rfl
  have h' : Real.tanh 1 ≤ 4 / 5 := by norm_num at h; linarith
  nlinarith

/-- Paper: `eq:resroundingerror` (tanh_residual.tex) at gain `g = 1`: if the stored radii
satisfy `eq:resrounded` in the form `r_0 = 1`, `r_{j+1} = f_{α,1}(r_j) + e_{j+1}` with
`0 ≤ e_{j+1} ≤ 3αε` and `ε ≤ 1/15` (the precision of the paper gives `ε ≤ [100(D+1)^4]^{-1}`),
then `R_j ≤ r_j ≤ 1` and `r_j - R_j ≤ 3jαε` for the ideal radii `R_j`. -/
theorem radii_rounding {α ε : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hε : ε ≤ 1 / 15) (r e : ℕ → ℝ)
    (hr0 : r 0 = 1)
    (hrec : ∀ j, r (j + 1) = fcrit α (r j) + e (j + 1))
    (he : ∀ j, 0 ≤ e j ∧ e j ≤ 3 * α * ε) (j : ℕ) :
    ResidualDepth.chain α 1 1 j ≤ r j ∧ r j ≤ 1 ∧
      r j - ResidualDepth.chain α 1 1 j ≤ 3 * j * α * ε := by
  induction j with
  | zero => simp [ResidualDepth.chain, hr0]
  | succ j ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    obtain ⟨he0, he1⟩ := he (j + 1)
    rw [chain_succ, hrec]
    have hm := fcrit_mono hα0 hα1 h1
    have hm1 := fcrit_mono hα0 hα1 h2
    have hone := fcrit_one_le hα0
    have hlip := fcrit_sub_le hα0 h1
    have hαε : 3 * α * ε ≤ α / 5 := by nlinarith
    refine ⟨by linarith, by linarith, ?_⟩
    push_cast
    nlinarith

/-- Paper: `eq:resradiuslower` (tanh_residual.tex) at gain `g = 1`: the stored radii of
`eq:resrounded` satisfy `r_j ≥ R_j ≥ (1 + αj)^{-1/2}`. From `radii_rounding` and
`ResidualDepth.ideal_radius_lower`. -/
theorem radius_lower {α ε : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hε : ε ≤ 1 / 15) (r e : ℕ → ℝ)
    (hr0 : r 0 = 1)
    (hrec : ∀ j, r (j + 1) = fcrit α (r j) + e (j + 1))
    (he : ∀ j, 0 ≤ e j ∧ e j ≤ 3 * α * ε) (j : ℕ) :
    1 / Real.sqrt (1 + α * j) ≤ r j :=
  (ResidualDepth.ideal_radius_lower α hα0 hα1 j).trans
    (radii_rounding hα0 hα1 hε r e hr0 hrec he j).1

/-- Paper: `eq:resradiuslower` (tanh_residual.tex), in the form used with `τ = αD`: for
`j ≤ D`, `r_j ≥ (1 + αD)^{-1/2}`. -/
theorem radius_lower_depth {α ε : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hε : ε ≤ 1 / 15) (r e : ℕ → ℝ)
    (hr0 : r 0 = 1)
    (hrec : ∀ j, r (j + 1) = fcrit α (r j) + e (j + 1))
    (he : ∀ j, 0 ≤ e j ∧ e j ≤ 3 * α * ε) {D j : ℕ} (hj : j ≤ D) :
    1 / Real.sqrt (1 + α * D) ≤ r j := by
  refine le_trans ?_ (radius_lower hα0 hα1 hε r e hr0 hrec he j)
  have hj' : (j : ℝ) ≤ D := by exact_mod_cast hj
  apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity))
  exact Real.sqrt_le_sqrt (by nlinarith)

/-- `ε ≤ [100(D+1)^4]^{-1}` implies `ε ≤ 1/15`. Auxiliary for `thm:residualupper`
(tanh_residual.tex). -/
theorem eps_le_of_precision {ε : ℝ} {D : ℕ} (hε : ε ≤ 1 / (100 * ((D : ℝ) + 1) ^ 4)) :
    ε ≤ 1 / 15 := by
  have h1 : (1 : ℝ) ≤ ((D : ℝ) + 1) ^ 4 :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
  refine hε.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-! ## The critical bound -/

/-- `tanh x > 0` for `x > 0`. Auxiliary. -/
theorem tanh_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hx) (Real.cosh_pos x)

/-- `χ_1(r) > 0` for `r > 0`. Auxiliary for `thm:residualupper` (tanh_residual.tex). -/
theorem chi_one_pos {x : ℝ} (hx : 0 < x) : 0 < ResidualDepth.chi 1 x := by
  unfold ResidualDepth.chi
  have h := tanh_pos (by simpa using hx : 0 < 1 * x)
  exact lt_min (by positivity) (by positivity)

/-- The offspring factor `G_j = 1 - α + α χ_1(r_j)` of the compressed recursion at gain one.
Paper: `thm:residualupper` (tanh_residual.tex), the product bound. -/
noncomputable def offspringFactor (α : ℝ) (r : ℕ → ℝ) (j : ℕ) : ℝ :=
  1 - α + α * ResidualDepth.chi 1 (r j)

/-- Paper: `eq:rescriticalupper` of `thm:residualupper` (tanh_residual.tex), with the
explicit prefactor `9 e^{21}` and `τ = αD`: for row norms at most one (`g = 1`), `0 < α ≤ 1`,
`ε ≤ [100(D+1)^4]^{-1}`, stored radii given by `eq:resrounded`
(`r_0 = 1`, `r_{j+1} = f_{α,1}(r_j) + e_{j+1}`, `0 ≤ e_{j+1} ≤ 3αε`), and the product bound
`eq:resproduct` for the expected count `E J` (hypothesis `hEJ`, a stand-in for the
probabilistic recursion and predictable charging), `E J ≤ 9 e^{21} (1 + αD)^2`.
This is `ResidualSampling.critical_bound` with all its other inputs discharged: the rounding
lemma `eq:resroundingerror` (`radii_rounding`), `eq:resradiuslower` (`radius_lower_depth`),
`eq:reslogproduct` (`ResidualDepth.reslogproduct_step` with `ResidualDepth.reschicritical`),
and `eq:resintegrals` (`ResidualDepth.resintegrals` with `ResidualDepth.ideal_radius_upper`). -/
theorem critical_bound_rounded (D : ℕ) {α ε EJ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / (100 * ((D : ℝ) + 1) ^ 4)) (r e : ℕ → ℝ) (hr0 : r 0 = 1)
    (hrec : ∀ j, r (j + 1) = fcrit α (r j) + e (j + 1))
    (he : ∀ j, 0 ≤ e j ∧ e j ≤ 3 * α * ε)
    (hEJ : EJ ≤ 1 + (∏ j ∈ range D, offspringFactor α r j +
      2 * α * ∑ k ∈ Icc 1 D, r k * ∏ j ∈ Ico k D, offspringFactor α r j)) :
    EJ ≤ 9 * Real.exp 21 * (1 + α * D) ^ 2 := by
  have hε' := eps_le_of_precision hε
  have hround := radii_rounding hα0.le hα1 hε' r e hr0 hrec he
  have hRpos : ∀ j, 0 < ResidualDepth.chain α 1 1 j := fun j =>
    lt_of_lt_of_le (by positivity) (ResidualDepth.ideal_radius_lower α hα0.le hα1 j)
  have hr : ∀ j, 0 < r j := fun j => (hRpos j).trans_le (hround j).1
  have hr1 : ∀ j, r j ≤ 1 := fun j => (hround j).2.1
  have hG : ∀ j, 0 < offspringFactor α r j := fun j => by
    unfold offspringFactor
    have := mul_pos hα0 (chi_one_pos (hr j))
    linarith
  set F : ℕ → ℝ := fun j => r j * (1 - α * (1 - Real.tanh (r j) / r j)) with hFdef
  have hFeq : ∀ j, F j = fcrit α (r j) := fun j => by
    simp only [hFdef, fcrit]
    field_simp [(hr j).ne']
    ring
  have hstep : ∀ j, j < D → Real.log (offspringFactor α r j) ≤
      4 * Real.log (r j / r (j + 1)) + (5 * α * r j ^ 4 + 12 * α * ε / F j) := by
    intro j _
    have htr : Real.tanh (r j) / r j ≤ 1 := by
      rw [div_le_one (hr j)]
      exact ResidualDepth.tanh_le_self (hr j).le
    have htp : 0 < Real.tanh (r j) / r j := div_pos (tanh_pos (hr j)) (hr j)
    have hαd : α * (1 - Real.tanh (r j) / r j) < 1 := by nlinarith
    have hχ : ResidualDepth.chi 1 (r j) ≤
        1 + 4 * (1 - Real.tanh (r j) / r j) + 5 * r j ^ 4 + 6000 * (1 - 1) := by
      rw [sub_self, mul_zero, add_zero]
      exact ResidualDepth.reschicritical (hr j) (hr1 j)
    have h := ResidualDepth.reslogproduct_step α (r j) (1 - Real.tanh (r j) / r j)
      (e (j + 1)) (ResidualDepth.chi 1 (r j)) ε 1 hα0.le (hr j) hαd (he (j + 1)).1
      (he (j + 1)).2 hχ (hG j)
    have hnext : r j * (1 - α * (1 - Real.tanh (r j) / r j)) + e (j + 1) = r (j + 1) := by
      rw [hrec j, ← hFeq j]
    rw [hnext] at h
    simp only [sub_self, mul_zero, add_zero] at h
    unfold offspringFactor
    simp only [hFdef]
    linarith
  have hrad : ∀ j, j ≤ D → 1 / Real.sqrt (1 + α * D) ≤ r j := fun j hj =>
    radius_lower_depth hα0.le hα1 hε' r e hr0 hrec he hj
  have hF : ∀ j, j < D → r (j + 1) - 3 * α * ε ≤ F j := fun j _ => by
    rw [hrec j, hFeq j]
    linarith [(he (j + 1)).2]
  obtain ⟨hfour, hfive⟩ := ResidualDepth.resintegrals α ε D (ResidualDepth.chain α 1 1) r hα0
    hα1 hε0 hε (fun j => (hRpos j).le) (fun j => (hround j).1) hr1
    (ResidualDepth.ideal_radius_upper α hα0.le hα1) (fun j => (hround j).2.2)
  exact ResidualSampling.critical_bound r (offspringFactor α r) F D α ε EJ hr hr0 hα0.le hα1
    hε0 hε hG hstep hrad hF hfour hfive hEJ

/-! ## Arbitrary row norms -/

/-- Paper: `prop:largerow` (tanh_residual.tex), the row sampler of `cor:comptanhrow`
(tanh_large_radius.tex): with `u = σ + |b_0|`, `|b_0| ≤ 1`, the expected child requests
`(σ/u) Q_u`, where `Q_u = u + ∫_0^1 u tanh²(uz)/z² dz` is the full-majority count formula of
`lem:comptanharity`, are at most `2σ(1+σ)`. `ResidualSampling.child_requests_le` with its
hypothesis `Q_u ≤ 2 max{u, u²}` supplied by `ResidualDepth.majority_count_le`. -/
theorem child_requests_formula (σ b₀ : ℝ) (hσ : 0 ≤ σ) (hb : |b₀| ≤ 1)
    (hu : 0 < σ + |b₀|) :
    σ / (σ + |b₀|) * ((σ + |b₀|) +
        ∫ z in (0 : ℝ)..1, (σ + |b₀|) * Real.tanh ((σ + |b₀|) * z) ^ 2 / z ^ 2) ≤
      2 * σ * (1 + σ) :=
  ResidualSampling.child_requests_le σ b₀ _ hσ hb hu (ResidualDepth.majority_count_le _ hu)

/-! ## The residual mean network -/

/-- `λ = a^D` with `a = 1 - α + αs` (`eq:reschainparameters`, tanh_residual.tex). -/
noncomputable def resLam (α s : ℝ) (D : ℕ) : ℝ := (1 - α + α * s) ^ D

/-- `A = (α s³/a) ∑_{j<D} a^{2j}` (`eq:reschainparameters`, tanh_residual.tex). -/
noncomputable def resA (α s : ℝ) (D : ℕ) : ℝ :=
  α * s ^ 3 / (1 - α + α * s) * ∑ j ∈ range D, (1 - α + α * s) ^ (2 * j)

/-- `a = 1 - α + αs > 0` for `0 ≤ α ≤ 1`, `s > 0`. Paper: `eq:reschainparameters`
(tanh_residual.tex), "Here `0 < s ≤ 2`, so `a > 0`". -/
theorem resBase_pos {α s : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hs : 0 < s) :
    0 < 1 - α + α * s := by
  rcases le_total s 1 with h | h
  · nlinarith [mul_nonneg hα0 (by linarith : (0 : ℝ) ≤ 1 - s)]
  · nlinarith [mul_nonneg hα0 (by linarith : (0 : ℝ) ≤ s - 1)]

/-- `λ > 0` and `A ≥ 0`. Auxiliary for `thm:resmeanlaw` (tanh_residual.tex). -/
theorem resLam_pos_resA_nonneg {α s : ℝ} (D : ℕ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hs : 0 < s) :
    0 < resLam α s D ∧ 0 ≤ resA α s D := by
  have ha := resBase_pos hα0 hα1 hs
  refine ⟨pow_pos ha D, ?_⟩
  unfold resA
  have : 0 ≤ ∑ j ∈ range D, (1 - α + α * s) ^ (2 * j) :=
    sum_nonneg fun j _ => pow_nonneg ha.le _
  positivity

/-- Paper: `lem:resrange` (tanh_residual.tex), `eq:resrangesandwich` at `z = 1`:
`λ/√(1+A) ≤ R ≤ λ/√(1+A/5)` for the endpoint value `R = F_D(1)`. From
`ResidualDepth.resrange`. -/
theorem endpoint_range {α s : ℝ} (D : ℕ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hs : 0 < s)
    (hs2 : s ≤ 2) :
    resLam α s D / Real.sqrt (1 + resA α s D) ≤ ResidualDepth.chain α s 1 D ∧
      ResidualDepth.chain α s 1 D ≤ resLam α s D / Real.sqrt (1 + resA α s D / 5) := by
  have h := ResidualDepth.resrange α s 1 D hα0 hα1 hs hs2 zero_le_one le_rfl
  simp only [mul_one, one_pow] at h
  exact h

/-- Paper: unknown-source lower bound of `thm:resmeanlaw` (tanh_residual.tex),
`eq:resunknownlaw`: `U ≥ λ√(1+A)/81`. This is `ResidualSampling.resmean_unknown_lower` with
`R = F_D(1)` and its range hypotheses supplied by `lem:resrange` (`endpoint_range`). The
remaining hypotheses are the endpoint coupling `U ≥ R` and the bending and transcript bound
`U ≥ 3λ²/(16R)` when `2R/λ ≤ 1/2`, both stand-ins as in `ResidualSampling`. -/
theorem resmean_unknown_lower_range (α s U : ℝ) (D : ℕ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hs : 0 < s) (hs2 : s ≤ 2) (hUR : ResidualDepth.chain α s 1 D ≤ U)
    (hbend : 2 * ResidualDepth.chain α s 1 D / resLam α s D ≤ 1 / 2 →
      3 * resLam α s D ^ 2 / (16 * ResidualDepth.chain α s 1 D) ≤ U) :
    resLam α s D * Real.sqrt (1 + resA α s D) / 81 ≤ U := by
  obtain ⟨hlam, hA⟩ := resLam_pos_resA_nonneg D hα0 hα1 hs
  obtain ⟨h1, h2⟩ := endpoint_range D hα0 hα1 hs hs2
  exact ResidualSampling.resmean_unknown_lower _ _ _ U hlam hA h1 h2 hUR hbend

/-- Paper: the balanced-input step of the lower bound in `thm:resmeanlaw` (tanh_residual.tex):
`(m/2) F_D(2/m) ≥ λ/√(1 + 4A/m²)` for `m ≥ 2`, from `lem:resrange` at `z = 2/m`. -/
theorem balanced_range {α s m : ℝ} (D : ℕ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hs : 0 < s)
    (hs2 : s ≤ 2) (hm : 2 ≤ m) :
    resLam α s D / Real.sqrt (1 + 4 * resA α s D / m ^ 2) ≤
      m / 2 * ResidualDepth.chain α s (2 / m) D := by
  have hm0 : 0 < m := by linarith
  have hz0 : 0 ≤ 2 / m := by positivity
  have hz1 : 2 / m ≤ 1 := by rw [div_le_one hm0]; exact hm
  have h := (ResidualDepth.resrange α s (2 / m) D hα0 hα1 hs hs2 hz0 hz1).1
  have e : 1 + α * s ^ 3 / (1 - α + α * s) * (∑ j ∈ range D, (1 - α + α * s) ^ (2 * j)) *
      (2 / m) ^ 2 = 1 + 4 * resA α s D / m ^ 2 := by
    unfold resA
    field_simp
    ring
  rw [e] at h
  have hS : 0 < Real.sqrt (1 + 4 * resA α s D / m ^ 2) := by
    have := (resLam_pos_resA_nonneg D hα0 hα1 hs).2
    exact Real.sqrt_pos.mpr (by positivity)
  calc resLam α s D / Real.sqrt (1 + 4 * resA α s D / m ^ 2)
      = m / 2 * ((1 - α + α * s) ^ D * (2 / m) / Real.sqrt (1 + 4 * resA α s D / m ^ 2)) := by
        unfold resLam
        field_simp
    _ ≤ m / 2 * ResidualDepth.chain α s (2 / m) D :=
        mul_le_mul_of_nonneg_left h (by positivity)

/-- Paper: finite-input lower bound of `thm:resmeanlaw` (tanh_residual.tex), `eq:resmeanlaw`:
`Q* ≥ Ξ/512` with `Ξ = λ min{√(1+A), m/√(1+A)}`, for even `m ≥ 2` (here `m ≥ 2`). This is
`ResidualSampling.resmean_finite_lower` with `R = F_D(1)`, the range hypotheses supplied by
`lem:resrange` (`endpoint_range`), and the balanced-input bound `Q* ≥ λ/√(1 + 4A/m²)` derived
from the coupling estimate `Q* ≥ (m/2) F_D(2/m)` (`hcoup`, from `lem:attentioncoupling` in
attention_primitives.tex) by `balanced_range`. Remaining stand-ins, as in `ResidualSampling`:
endpoint coupling `Q* ≥ R` (`hQR`), the derivative bound `eq:resfinitehprime` (`hh`), the
bending and transcript bound (`hbend`), and `hcoup`. -/
theorem resmean_finite_lower_range (α s m h Q : ℝ) (D : ℕ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hs : 0 < s) (hs2 : s ≤ 2) (hm : 2 ≤ m) (hQR : ResidualDepth.chain α s 1 D ≤ Q)
    (hh : resLam α s D / Real.sqrt (1 + 3 * resA α s D / m) ≤ h)
    (hbend : 2 * ResidualDepth.chain α s 1 D / h ≤ 1 / 2 →
      3 * h ^ 2 / (16 * ResidualDepth.chain α s 1 D) ≤ Q)
    (hcoup : m / 2 * ResidualDepth.chain α s (2 / m) D ≤ Q) :
    resLam α s D * min (Real.sqrt (1 + resA α s D)) (m / Real.sqrt (1 + resA α s D)) / 512 ≤
      Q := by
  obtain ⟨hlam, hA⟩ := resLam_pos_resA_nonneg D hα0 hα1 hs
  obtain ⟨h1, h2⟩ := endpoint_range D hα0 hα1 hs hs2
  have hbal := (balanced_range D hα0 hα1 hs hs2 hm).trans hcoup
  exact ResidualSampling.resmean_finite_lower _ _ m _ h Q hlam hA (by linarith) h1 h2 hQR hh
    hbend hbal

/-! ## The local step of the fused residual sampler -/

/-- Paper: proof of `thm:residualfused` (tanh_residual_fused.tex): with `d = 1 - tanh r / r`
and `0 < r ≤ 1`, `α c_0 r² ≤ κ α d + (κ/5) α r⁴` with `κ = 3c_0`. This is
`Potential.weighted_local_step` with its declared stand-in `d ≥ r²/3 - r⁴/5` supplied by
`ResidualDepth.tanh_le_quintic` ("Since `d_j ≥ r_j²/3 - r_j⁴/5`"). -/
theorem weighted_local_step_radius (α c₀ r : ℝ) (hα : 0 ≤ α) (hc : 0 ≤ c₀) (hr0 : 0 < r)
    (hr1 : r ≤ 1) :
    α * c₀ * r ^ 2 ≤ 3 * c₀ * α * (1 - Real.tanh r / r) + 3 * c₀ / 5 * α * r ^ 4 := by
  refine Potential.weighted_local_step α c₀ r _ hα hc ?_
  have h := ResidualDepth.tanh_le_quintic hr0.le hr1
  have h' : Real.tanh r / r ≤ 1 - r ^ 2 / 3 + r ^ 4 / 5 := by
    rw [div_le_iff₀ hr0]
    linarith
  linarith

/-- Paper: proof of `thm:residualfused` (tanh_residual_fused.tex): for the stored radii of
`eq:resrounded` at gain one and `j ≤ D`, `r_j^{-p} ≤ (1 + αD)^{p/2}` for `p ≥ 0`; with
`p = κ - 1 = 35/16` this is `r^{1-κ} ≤ (1 + αD)^{35/32}`. This is
`Potential.rpow_neg_le_of_radius` with its declared stand-in `r_j ≥ (1 + αD)^{-1/2}`
(`eq:resradiuslower` with `r_j ≥ R_j`) supplied by `radius_lower_depth`. -/
theorem rpow_neg_le_radius {α ε p : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hε : ε ≤ 1 / 15)
    (hp : 0 ≤ p) (r e : ℕ → ℝ) (hr0 : r 0 = 1)
    (hrec : ∀ j, r (j + 1) = fcrit α (r j) + e (j + 1))
    (he : ∀ j, 0 ≤ e j ∧ e j ≤ 3 * α * ε) {D j : ℕ} (hj : j ≤ D) :
    r j ^ (-p) ≤ (1 + α * D) ^ (p / 2) :=
  Potential.rpow_neg_le_of_radius (by positivity) hp
    (radius_lower_depth hα0 hα1 hε r e hr0 hrec he hj)

end ExactSampling.Links.ResidualChain
