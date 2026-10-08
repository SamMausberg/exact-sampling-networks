import Mathlib

/-!
# Predictable charging of stopped work

This module formalizes the stopping lemma used throughout the recursive constructions of the
full version:

* `lem:stopping` (`tanh_scalar.tex`, Section `sec:bias`): if reaching trial `j` is determined
  by the history before that trial's fresh randomness, and the conditional expected
  nonnegative cost of a reached trial is at most `B`, then the expected total work is at most
  `B Σ_j P(T ≥ j) = B E T`; for independent trials of success probability `σ > 0`,
  `E T = 1 / σ`.

The probability space is an arbitrary measure space; the history before trial `j` is a
sub-σ-algebra `F j`; "reaching trial `j`" is the event `{j < T}` for a stopping index
`T : Ω → ℕ∞` (no almost sure termination is assumed). The conditional cost bound is stated in
its defining form `∫_A C_j ≤ B μ(A)` for every history event `A`; the lemma
`setLIntegral_le_of_condExp_le` shows that this form follows from the conditional-expectation
inequality `E[C_j | F_j] ≤ B` for real integrable costs. No independence between the
duration of a trial and its outcome is assumed, and no finite expectation is assumed in
advance: the bounds are inequalities in `[0, ∞]`.

The module also records the truncation identity for expected trial counts and the stage-cost
bound of the exact comparison with a computable probability (`lem:lazy`, `tanh_bits.tex`):
if stage `t` is reached with probability at most `8 · 2^{-t}` (stage `t` is reached only after
an undecided stage `t - 1`, of probability at most `4 · 2^{1-t}`) and costs `C (B + t)^d`, the
expected work is at most `2^{d+4} d! C (B + 1)^d`, within the paper's `2^{d+5} d! C (B+1)^d`.
The geometric survival law of independent trials enters `stopped_work_le_div` as a hypothesis.

Not formalized: the construction of the samplers' probability spaces themselves, and the
probability bound for an undecided lazy comparison (only the interval length is computed here).
-/

namespace ExactSampling.StoppedWork

open MeasureTheory
open scoped ENNReal

/-- The core charging inequality: if each reach event `reach j` carries expected cost at most
`B μ(reach j)`, the expected total over all reached trials is at most `B Σ_j μ(reach j)`.
Paper: `lem:stopping` (`tanh_scalar.tex`), the inequality in `eq:stoppedcost`. -/
theorem stopped_work_le_of_reach {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)
    (reach : ℕ → Set Ω) (C : ℕ → Ω → ℝ≥0∞) (B : ℝ≥0∞)
    (hreach : ∀ j, MeasurableSet (reach j)) (hC : ∀ j, AEMeasurable (C j) μ)
    (hcost : ∀ j, ∫⁻ ω in reach j, C j ω ∂μ ≤ B * μ (reach j)) :
    ∫⁻ ω, ∑' j, (reach j).indicator (C j) ω ∂μ ≤ B * ∑' j, μ (reach j) := by
  rw [lintegral_tsum (fun j => (hC j).indicator (hreach j))]
  calc ∑' j, ∫⁻ ω, (reach j).indicator (C j) ω ∂μ = ∑' j, ∫⁻ ω in reach j, C j ω ∂μ := by
        congr 1; funext j; exact lintegral_indicator (hreach j) _
    _ ≤ ∑' j, B * μ (reach j) := ENNReal.tsum_le_tsum hcost
    _ = B * ∑' j, μ (reach j) := ENNReal.tsum_mul_left

/-- Predictable charging of stopped work. The history before trial `j` is the sub-σ-algebra
`F j`; reaching trial `j` (the event `j < T`) is an `F j`-event; and the cost `C j` of trial `j`
has conditional mean at most `B` given `F j`, in the defining form `∫_A C_j ≤ B μ(A)` for
`A ∈ F j`. Then `E Σ_{j < T} C_j ≤ B Σ_j P(j < T)`.
Paper: `lem:stopping` (`tanh_scalar.tex`), `eq:stoppedcost`. -/
theorem stopped_work_le {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)
    (F : ℕ → MeasurableSpace Ω) (hF : ∀ j, F j ≤ m) (T : Ω → ℕ∞) (C : ℕ → Ω → ℝ≥0∞)
    (B : ℝ≥0∞) (hC : ∀ j, AEMeasurable (C j) μ)
    (hreach : ∀ j : ℕ, MeasurableSet[F j] {ω | (j : ℕ∞) < T ω})
    (hcond : ∀ j (A : Set Ω), MeasurableSet[F j] A → ∫⁻ ω in A, C j ω ∂μ ≤ B * μ A) :
    ∫⁻ ω, ∑' j : ℕ, {ω | (j : ℕ∞) < T ω}.indicator (C j) ω ∂μ ≤
      B * ∑' j : ℕ, μ {ω | (j : ℕ∞) < T ω} :=
  stopped_work_le_of_reach μ (fun j => {ω | (j : ℕ∞) < T ω}) C B
    (fun j => hF j _ (hreach j)) hC (fun j => hcond j _ (hreach j))

/-- Pointwise tail sum: `n = Σ_{j ≥ 0} 1{j < n}` in `[0, ∞]`, for `n ∈ ℕ ∪ {∞}`. -/
theorem coe_eq_tsum_indicator (n : ℕ∞) :
    (n : ℝ≥0∞) = ∑' j : ℕ, if (j : ℕ∞) < n then (1 : ℝ≥0∞) else 0 := by
  induction n using ENat.recTopCoe with
  | top =>
      simp only [ENat.natCast_lt_top, ite_true, ENat.toENNReal_top]
      exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
  | coe m =>
      rw [ENat.toENNReal_coe, tsum_eq_sum (s := Finset.range m)]
      · rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]
        · simp
        · intro j hj
          simp [Finset.mem_range.mp hj]
      · intro j hj
        simp only [Finset.mem_range, not_lt] at hj
        simp [not_lt.mpr hj]

/-- The tail-sum formula `Σ_{j ≥ 0} P(T > j) = E T` for a stopping index `T` with values in
`ℕ ∪ {∞}` (no termination is assumed; both sides may be infinite).
Paper: `lem:stopping` (`tanh_scalar.tex`), the equality in `eq:stoppedcost`. -/
theorem tsum_measure_lt_eq_lintegral {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)
    (T : Ω → ℕ∞) (hT : ∀ j : ℕ, MeasurableSet {ω | (j : ℕ∞) < T ω}) :
    ∑' j : ℕ, μ {ω | (j : ℕ∞) < T ω} = ∫⁻ ω, (T ω : ℝ≥0∞) ∂μ := by
  have hpt : ∀ ω, (T ω : ℝ≥0∞) =
      ∑' j : ℕ, {ω | (j : ℕ∞) < T ω}.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    rw [coe_eq_tsum_indicator (T ω)]
    congr 1
    funext j
    simp [Set.indicator_apply]
  simp_rw [hpt]
  rw [lintegral_tsum (fun j => (measurable_const.indicator (hT j)).aemeasurable)]
  congr 1
  funext j
  rw [lintegral_indicator (hT j), setLIntegral_const, one_mul]

/-- Predictable charging in the form `E Σ_{j < T} C_j ≤ B E T`, for a stopping index with values
in `ℕ ∪ {∞}`. Paper: `lem:stopping` (`tanh_scalar.tex`), `eq:stoppedcost`. -/
theorem stopped_work_le_mul_expectation {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)
    (F : ℕ → MeasurableSpace Ω) (hF : ∀ j, F j ≤ m) (T : Ω → ℕ∞)
    (C : ℕ → Ω → ℝ≥0∞) (B : ℝ≥0∞) (hC : ∀ j, AEMeasurable (C j) μ)
    (hreach : ∀ j : ℕ, MeasurableSet[F j] {ω | (j : ℕ∞) < T ω})
    (hcond : ∀ j (A : Set Ω), MeasurableSet[F j] A → ∫⁻ ω in A, C j ω ∂μ ≤ B * μ A) :
    ∫⁻ ω, ∑' j : ℕ, {ω | (j : ℕ∞) < T ω}.indicator (C j) ω ∂μ ≤
      B * ∫⁻ ω, (T ω : ℝ≥0∞) ∂μ := by
  rw [← tsum_measure_lt_eq_lintegral μ T (fun j => hF j _ (hreach j))]
  exact stopped_work_le μ F hF T C B hC hreach hcond

/-- For independent trials of success probability `σ ∈ (0, 1]`, `P(T > j) = (1 - σ)^j` and
`E T = Σ_j (1 - σ)^j = 1/σ`. Paper: `lem:stopping` (`tanh_scalar.tex`), last sentence. -/
theorem tsum_geometric_survival {σ : ℝ≥0∞} (hσ : σ ≤ 1) :
    ∑' j : ℕ, (1 - σ) ^ j = σ⁻¹ := by
  rw [ENNReal.tsum_geometric, ENNReal.sub_sub_cancel ENNReal.one_ne_top hσ]

/-- Predictable charging with a geometric survival law: under the hypothesis `hsurv` that trial
`j` is reached with probability `(1 - σ)^j` (which holds for independent trials of success
probability `σ`; the hypothesis is not derived here), the expected stopped work is at most
`B / σ`. Paper: `lem:stopping` (`tanh_scalar.tex`). -/
theorem stopped_work_le_div {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)
    (F : ℕ → MeasurableSpace Ω) (hF : ∀ j, F j ≤ m) (T : Ω → ℕ∞) (C : ℕ → Ω → ℝ≥0∞)
    (B σ : ℝ≥0∞) (hσ : σ ≤ 1) (hC : ∀ j, AEMeasurable (C j) μ)
    (hreach : ∀ j : ℕ, MeasurableSet[F j] {ω | (j : ℕ∞) < T ω})
    (hcond : ∀ j (A : Set Ω), MeasurableSet[F j] A → ∫⁻ ω in A, C j ω ∂μ ≤ B * μ A)
    (hsurv : ∀ j : ℕ, μ {ω | (j : ℕ∞) < T ω} = (1 - σ) ^ j) :
    ∫⁻ ω, ∑' j : ℕ, {ω | (j : ℕ∞) < T ω}.indicator (C j) ω ∂μ ≤ B / σ := by
  have h := stopped_work_le μ F hF T C B hC hreach hcond
  simp_rw [hsurv] at h
  rw [tsum_geometric_survival hσ] at h
  exact h

/-- A dominated survival function `P(reach j) ≤ r^j` gives total stopped cost at most
`B / (1 - r)`, with no summability assumption. Paper: `lem:stopping` (`tanh_scalar.tex`), in the
form with a geometrically dominated reach probability. -/
theorem predictable_cost_tsum_bound (costMean survival : ℕ → ℝ≥0∞) (B r : ℝ≥0∞)
    (hcost : ∀ k, costMean k ≤ B * survival k) (htail : ∀ k, survival k ≤ r ^ k) :
    (∑' k : ℕ, costMean k) ≤ B / (1 - r) := by
  calc (∑' k : ℕ, costMean k) ≤ ∑' k : ℕ, B * r ^ k := by
        apply ENNReal.tsum_le_tsum
        intro k
        exact (hcost k).trans (mul_le_mul_right (htail k) B)
    _ = B * (∑' k : ℕ, r ^ k) := ENNReal.tsum_mul_left
    _ = B * (1 - r)⁻¹ := by rw [ENNReal.tsum_geometric]
    _ = B / (1 - r) := rfl

/-- The conditional-expectation form of the cost hypothesis: for a real, integrable,
nonnegative trial cost `f` whose conditional expectation given the history `F` is at most `B`,
every history event `A` satisfies `∫_A f ≤ B μ(A)`. This derives the hypothesis `hcond` of
`stopped_work_le` from `E[C_j | F_j] ≤ B`. Paper: `lem:stopping` (`tanh_scalar.tex`),
"conditional expected nonnegative cost at most `B`". -/
theorem setLIntegral_le_of_condExp_le {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {F : MeasurableSpace Ω} (hF : F ≤ m0) [SigmaFinite (μ.trim hF)]
    {f : Ω → ℝ} (hf : Integrable f μ) (hf0 : 0 ≤ᵐ[μ] f) {B : ℝ}
    (hce : μ[f | F] ≤ᵐ[μ] fun _ => B) {A : Set Ω} (hA : MeasurableSet[F] A) :
    ∫⁻ ω in A, ENNReal.ofReal (f ω) ∂μ ≤ ENNReal.ofReal B * μ A := by
  have hint : ∫ ω in A, f ω ∂μ ≤ μ.real A * B := by
    rw [← setIntegral_condExp hF hf hA]
    calc ∫ ω in A, (μ[f | F]) ω ∂μ ≤ ∫ ω in A, B ∂μ :=
          setIntegral_mono_ae integrable_condExp.integrableOn (integrable_const B).integrableOn
            hce
      _ = μ.real A * B := by rw [setIntegral_const, smul_eq_mul]
  have hrestr : ENNReal.ofReal (∫ ω in A, f ω ∂μ) = ∫⁻ ω in A, ENNReal.ofReal (f ω) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hf.integrableOn (ae_restrict_of_ae hf0)
  rw [← hrestr]
  calc ENNReal.ofReal (∫ ω in A, f ω ∂μ) ≤ ENNReal.ofReal (μ.real A * B) :=
        ENNReal.ofReal_le_ofReal hint
    _ = ENNReal.ofReal B * μ A := by
        rw [ENNReal.ofReal_mul measureReal_nonneg, mul_comm, measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top μ A)]

/-- The expected number of trials truncated after `N` trials obeys `e_{N+1} = 1 + r e_N`, hence
`e_N = Σ_{k<N} r^k`, without assuming a finite mean in advance. Paper: Section
"Exactness and stopping" (`exact_sampling_networks.tex`), truncation followed by monotone
convergence; used for `lem:stopping` (`tanh_scalar.tex`). -/
theorem truncated_trials_eq_geometric (e : ℕ → ℝ) (r : ℝ) (hzero : e 0 = 0)
    (hstep : ∀ N, e (N + 1) = 1 + r * e N) (N : ℕ) :
    e N = ∑ k ∈ Finset.range N, r ^ k := by
  induction N with
  | zero => simpa using hzero
  | succ N ih =>
      rw [hstep N, ih, Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_succ, pow_zero]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- The interval `[p - δ, p + δ]` has length `2δ`. This is only the volume computation behind
the bound `4 · 2^{-m}` on an undecided comparison at stage `m` (`|U - p| ≤ 2^{1-m}`); the
probabilistic statement about the lazy comparison is not derived here (it is formalized in
`ExactSampling/Stopping/StoppedCost.lean`). Paper: `lem:lazy` (`tanh_bits.tex`). -/
theorem comparison_failure_measure (p δ : ℝ) :
    MeasureTheory.volume (Set.Icc (p - δ) (p + δ)) = ENNReal.ofReal (2 * δ) := by
  rw [Real.volume_Icc]
  congr 1
  ring

/-- `(t + 1)^d ≤ d! · C(t + d, d)`. Auxiliary for `lem:lazy` (`tanh_bits.tex`). -/
theorem pow_le_factorial_mul_choose (t d : ℕ) :
    ((t : ℝ) + 1) ^ d ≤ (d.factorial : ℝ) * ((t + d).choose d : ℝ) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have h := Nat.add_one_mul_choose_eq (t + d) d
      have hr : ((t + d : ℕ) + 1 : ℝ) * ((t + d).choose d : ℝ) =
          ((t + d + 1).choose (d + 1) : ℝ) * ((d : ℝ) + 1) := by exact_mod_cast h
      rw [show t + (d + 1) = t + d + 1 by ring, Nat.factorial_succ, pow_succ]
      push_cast at hr ⊢
      have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have hF : (0 : ℝ) ≤ (d.factorial : ℝ) := by positivity
      calc ((t : ℝ) + 1) ^ d * ((t : ℝ) + 1)
          ≤ (d.factorial : ℝ) * ((t + d).choose d : ℝ) * ((t : ℝ) + d + 1) :=
            mul_le_mul ih (by linarith) (by positivity) (by positivity)
        _ = ((d : ℝ) + 1) * (d.factorial : ℝ) * ((t + d + 1).choose (d + 1) : ℝ) := by
            linear_combination (d.factorial : ℝ) * hr

/-- The expected work of the exact comparison with a computable probability. Stage `t + 1` is
reached only if stage `t` is undecided, which has probability at most `4 · 2^{-t}`; hence stage
`t` is reached with probability at most `min {1, 8 · 2^{-t}}`. If stage `t` costs
`C (B + t)^d`, the total expected work is at most `2^{d+4} d! C (B + 1)^d`, within the bound
`2^{d+5} d! C (B+1)^d` of the paper. Paper: `lem:lazy` (`tanh_bits.tex`) and Section
"Exactness and stopping" (`exact_sampling_networks.tex`). -/
theorem lazy_comparison_work (C B : ℝ) (d : ℕ) (hC : 0 ≤ C) (hB : 0 ≤ B) (reach : ℕ → ℝ)
    (hreach0 : ∀ t, 0 ≤ reach t) (hreach : ∀ t, reach t ≤ 8 * (1 / 2 : ℝ) ^ t) :
    Summable (fun t : ℕ => C * (B + t) ^ d * reach t) ∧
      ∑' t : ℕ, C * (B + t) ^ d * reach t ≤
        2 ^ (d + 4) * (d.factorial : ℝ) * C * (B + 1) ^ d := by
  have hgeo := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) d
    (r := 1 / 2) (by norm_num)
  set g : ℕ → ℝ := fun t => C * (B + 1) ^ d * (d.factorial : ℝ) * 8 *
    (((t + d).choose d : ℝ) * (1 / 2 : ℝ) ^ t) with hg
  have hgsum : HasSum g (C * (B + 1) ^ d * (d.factorial : ℝ) * 8 * (1 / (1 - 1 / 2) ^ (d + 1))) :=
    hgeo.mul_left _
  have hle : ∀ t : ℕ, C * (B + t) ^ d * reach t ≤ g t := by
    intro t
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have h1 : (B + t) ^ d ≤ (B + 1) ^ d * ((t : ℝ) + 1) ^ d := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith
    have h2 := pow_le_factorial_mul_choose t d
    have hp : 0 ≤ (1 / 2 : ℝ) ^ t := by positivity
    have hB1 : 0 ≤ (B + 1) ^ d := by positivity
    calc C * (B + t) ^ d * reach t ≤ C * ((B + 1) ^ d * ((t : ℝ) + 1) ^ d) *
          (8 * (1 / 2 : ℝ) ^ t) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hC) (hreach t) (hreach0 t) (by positivity)
      _ ≤ C * ((B + 1) ^ d * ((d.factorial : ℝ) * ((t + d).choose d : ℝ))) *
          (8 * (1 / 2 : ℝ) ^ t) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hB1) hC
      _ = g t := by simp only [hg]; ring
  have hnn : ∀ t : ℕ, 0 ≤ C * (B + t) ^ d * reach t := fun t => by
    have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    exact mul_nonneg (mul_nonneg hC (by positivity)) (hreach0 t)
  have hsum : Summable (fun t : ℕ => C * (B + t) ^ d * reach t) :=
    Summable.of_nonneg_of_le hnn hle hgsum.summable
  refine ⟨hsum, ?_⟩
  calc ∑' t : ℕ, C * (B + t) ^ d * reach t ≤ ∑' t : ℕ, g t := hsum.tsum_le_tsum hle hgsum.summable
    _ = C * (B + 1) ^ d * (d.factorial : ℝ) * 8 * (1 / (1 - 1 / 2) ^ (d + 1)) := hgsum.tsum_eq
    _ = 2 ^ (d + 4) * (d.factorial : ℝ) * C * (B + 1) ^ d := by
        rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, one_div_pow, one_div_one_div, pow_add,
          pow_add]
        ring

end ExactSampling.StoppedWork
