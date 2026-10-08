import Mathlib

/-!
# Repeated independent trials: the first-success law and the renewal cost

Paper: `conference.tex`, the repeated-trial arguments in Section `sec:conf-scalar` (proof of
`prop:conf-row`: "renewal gives at most `2Ae^A` requests", "each trial succeeds with probability
`1/256` and the accepted `K` is Poisson", and the exact attention law after it) and in Section
`sec:conf-grid` (proof of `thm:conf-grid`: "the accepted mass is exactly `w_j/W`, so the result
has the target law and the expected number of proposals is below `17/8`"). Full version
`exact_sampling_networks.tex`: proofs of `lem:attentionraceexact` and
`lem:smallpoissonattention` (`attention_primitives.tex`) and of `lem:dynamiccellenvelope`
(`attention_dynamic_index.tex`).

The trial records `Y m : Ω → β` are mutually independent and identically distributed on a
probability space; a measurable set `S ⊆ β` of records counts as success. Trial `m` is reached
when all earlier trials failed. The companion modules on the row factory and on the grid index
compute the success masses of one trial and evaluate the resulting series
`∑ₘ (1 - s)^m α = α / s`; this module proves that series from independence.

## What is formalized

* `P(trial m is reached) = (1 - s)^m` with `s = P(Y₀ ∈ S)`.
* `P(trial m is reached and Y_m ∈ E) = (1 - s)^m P(Y₀ ∈ E)` for `E ⊆ S`.
* The first-success law: `P(the accepted record lies in E) = P(Y₀ ∈ E) / s`.
* Almost-sure termination when `s > 0`.
* The renewal identity: for a measurable per-trial cost `c`, the expected total cost of all
  reached trials is `E[c(Y₀)] / s`; with `c ≡ 1` the expected number of trials is `1 / s`.

## What is not formalized

Nothing beyond the generic probability statement: the specific trial records (Poisson tests,
geometric proposals, cell envelopes) are treated in the companion modules.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace ExactSampling.RejectionLoop

variable {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] {P : Measure Ω}

/-- Trial `m` is reached: all earlier trials failed. Paper: the repeated-trial arguments in the
proofs of `prop:conf-row` and `thm:conf-grid` (conference.tex). -/
def Reached (Y : ℕ → Ω → β) (S : Set β) (m : ℕ) : Set Ω := {ω | ∀ k < m, Y k ω ∉ S}

omit [MeasurableSpace Ω] [MeasurableSpace β] in
/-- `Reached` as a finite intersection of preimages. Auxiliary for the repeated-trial arguments
in the proofs of `prop:conf-row` and `thm:conf-grid` (conference.tex). -/
theorem reached_eq (Y : ℕ → Ω → β) (S : Set β) (m : ℕ) :
    Reached Y S m = ⋂ k ∈ Finset.range m, Y k ⁻¹' Sᶜ := by
  ext ω
  simp [Reached]

/-- `Reached` is measurable. Auxiliary for the repeated-trial arguments in the proofs of
`prop:conf-row` and `thm:conf-grid` (conference.tex). -/
theorem measurableSet_reached {Y : ℕ → Ω → β} (hmeas : ∀ m, Measurable (Y m)) {S : Set β}
    (hS : MeasurableSet S) (m : ℕ) : MeasurableSet (Reached Y S m) := by
  rw [reached_eq]
  exact Finset.measurableSet_biInter _ fun k _ => hmeas k hS.compl

/-- Probability of reaching trial `m`: `(1 - s)^m`, written as `P(Y₀ ∉ S)^m`. Paper: the
repeated-trial arguments in the proofs of `prop:conf-row` and `thm:conf-grid`
(conference.tex); full version: proof of `lem:attentionraceexact`
(attention_primitives.tex). -/
theorem measure_reached (Y : ℕ → Ω → β) (hY : iIndepFun Y P)
    (hid : ∀ m, P.map (Y m) = P.map (Y 0)) (hmeas : ∀ m, Measurable (Y m)) {S : Set β}
    (hS : MeasurableSet S) (m : ℕ) :
    P (Reached Y S m) = P (Y 0 ⁻¹' Sᶜ) ^ m := by
  rw [reached_eq, hY.meas_biInter (fun k _ => ⟨Sᶜ, hS.compl, rfl⟩)]
  have : ∀ k, P (Y k ⁻¹' Sᶜ) = P (Y 0 ⁻¹' Sᶜ) := by
    intro k
    rw [← Measure.map_apply (hmeas k) hS.compl, hid k, Measure.map_apply (hmeas 0) hS.compl]
  rw [Finset.prod_congr rfl (fun k _ => this k), Finset.prod_const, Finset.card_range]

/-- First success at trial `m` with record in `E ⊆ S`: probability `P(Y₀ ∉ S)^m P(Y₀ ∈ E)`.
Paper: the repeated-trial arguments in the proofs of `prop:conf-row` and `thm:conf-grid`
(conference.tex); full version: proof of `lem:attentionraceexact`
(attention_primitives.tex). -/
theorem measure_first_success (Y : ℕ → Ω → β) (hY : iIndepFun Y P)
    (hid : ∀ m, P.map (Y m) = P.map (Y 0)) (hmeas : ∀ m, Measurable (Y m)) {S E : Set β}
    (hS : MeasurableSet S) (hE : MeasurableSet E) (m : ℕ) :
    P (Reached Y S m ∩ Y m ⁻¹' E) = P (Y 0 ⁻¹' Sᶜ) ^ m * P (Y 0 ⁻¹' E) := by
  classical
  let s : ℕ → Set Ω := fun k => if k < m then Y k ⁻¹' Sᶜ else Y k ⁻¹' E
  have hset : Reached Y S m ∩ Y m ⁻¹' E = ⋂ k ∈ Finset.range (m + 1), s k := by
    ext ω
    simp only [Reached, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_iInter, Finset.mem_range, s]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      split_ifs with hkm
      · exact h1 k hkm
      · have : k = m := by omega
        subst this; exact h2
    · intro h
      refine ⟨fun k hk => ?_, ?_⟩
      · have := h k (by omega)
        rw [ite_eq_left hk] at this
        exact this
      · have := h m (by omega)
        rw [ite_eq_right (lt_irrefl m)] at this
        exact this
  have hs : ∀ k ∈ Finset.range (m + 1),
      MeasurableSet[(inferInstance : MeasurableSpace β).comap (Y k)] (s k) := by
    intro k _
    simp only [s]
    split_ifs
    · exact ⟨Sᶜ, hS.compl, rfl⟩
    · exact ⟨E, hE, rfl⟩
  rw [hset, hY.meas_biInter hs, Finset.prod_range_succ]
  have hc : ∀ k, P (Y k ⁻¹' Sᶜ) = P (Y 0 ⁻¹' Sᶜ) := by
    intro k
    rw [← Measure.map_apply (hmeas k) hS.compl, hid k, Measure.map_apply (hmeas 0) hS.compl]
  have he : P (Y m ⁻¹' E) = P (Y 0 ⁻¹' E) := by
    rw [← Measure.map_apply (hmeas m) hE, hid m, Measure.map_apply (hmeas 0) hE]
  have hprod : ∏ k ∈ Finset.range m, P (s k) = P (Y 0 ⁻¹' Sᶜ) ^ m := by
    rw [Finset.prod_congr rfl (fun k hk => by
      simp only [s, ite_eq_left (Finset.mem_range.mp hk)]; exact hc k)]
    simp
  rw [hprod]
  simp only [s, lt_irrefl, ite_false, he]

/-- The first-success law: the accepted record lies in `E ⊆ S` with probability
`P(Y₀ ∈ E) / P(Y₀ ∈ S)`, i.e. the accepted record has the conditional law of one trial given
success. Paper: proof of `prop:conf-row` (conference.tex), "the accepted `K` is Poisson", the
exact attention law after it, and proof of `thm:conf-grid`, "the accepted mass is exactly
`w_j/W`, so the result has the target law"; full version: proofs of `lem:attentionraceexact`,
`lem:smallpoissonattention` (attention_primitives.tex) and `lem:dynamiccellenvelope`
(attention_dynamic_index.tex). -/
theorem first_success_law [IsProbabilityMeasure P] (Y : ℕ → Ω → β) (hY : iIndepFun Y P)
    (hid : ∀ m, P.map (Y m) = P.map (Y 0)) (hmeas : ∀ m, Measurable (Y m)) {S E : Set β}
    (hS : MeasurableSet S) (hE : MeasurableSet E) (hES : E ⊆ S) :
    P {ω | ∃ m, ω ∈ Reached Y S m ∧ Y m ω ∈ E} = P (Y 0 ⁻¹' E) / P (Y 0 ⁻¹' S) := by
  have hunion : {ω | ∃ m, ω ∈ Reached Y S m ∧ Y m ω ∈ E}
      = ⋃ m, Reached Y S m ∩ Y m ⁻¹' E := by
    ext ω; simp
  have hdisj : Pairwise (Function.onFun Disjoint fun m => Reached Y S m ∩ Y m ⁻¹' E) := by
    intro m m' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨hm, hmE⟩ ⟨hm', hm'E⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact hm' m h (hES hmE)
    · exact hm m' h (hES hm'E)
  rw [hunion, measure_iUnion hdisj (fun m => (measurableSet_reached hmeas hS m).inter
    (hmeas m hE))]
  simp_rw [measure_first_success Y hY hid hmeas hS hE]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, Set.preimage_compl,
    prob_compl_eq_one_sub (hmeas 0 hS), ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one,
    div_eq_mul_inv, mul_comm]

/-- Almost-sure termination: if one trial succeeds with positive probability, then with
probability one some trial succeeds. Paper: the repeated-trial arguments in the proofs of
`prop:conf-row` and `thm:conf-grid` (conference.tex); full version: proof of
`lem:attentionraceexact` (attention_primitives.tex), "the procedure terminates almost
surely". -/
theorem never_success_null [IsProbabilityMeasure P] (Y : ℕ → Ω → β) (hY : iIndepFun Y P)
    (hid : ∀ m, P.map (Y m) = P.map (Y 0)) (hmeas : ∀ m, Measurable (Y m)) {S : Set β}
    (hS : MeasurableSet S) (hpos : 0 < P (Y 0 ⁻¹' S)) :
    P {ω | ∀ m, Y m ω ∉ S} = 0 := by
  have hq : P (Y 0 ⁻¹' Sᶜ) < 1 := by
    rw [Set.preimage_compl, prob_compl_eq_one_sub (hmeas 0 hS)]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos.ne'
  have hle : ∀ m, P {ω | ∀ m, Y m ω ∉ S} ≤ P (Y 0 ⁻¹' Sᶜ) ^ m := by
    intro m
    rw [← measure_reached Y hY hid hmeas hS m]
    exact measure_mono fun ω h k _ => h k
  exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq) hle)
    zero_le

/-- The renewal identity: if trial `m` costs `c(Y_m)` and is charged only when reached, the
expected total cost is `E[c(Y₀)] / P(Y₀ ∈ S)`. The proof uses independence of `Y_m` from the
earlier trials, so the cost may be correlated with the success of its own trial. Paper: proof
of `prop:conf-row` (conference.tex), "renewal gives at most `2Ae^A` requests"; full version:
child-request bound in `thm:attentionprimitive` (attention_primitives.tex) and
`lem:dynamiccellenvelope` (attention_dynamic_index.tex). -/
theorem renewal_cost [IsProbabilityMeasure P] (Y : ℕ → Ω → β) (hY : iIndepFun Y P)
    (hid : ∀ m, P.map (Y m) = P.map (Y 0)) (hmeas : ∀ m, Measurable (Y m)) {S : Set β}
    (hS : MeasurableSet S) (c : β → ℝ≥0∞) (hc : Measurable c) :
    ∫⁻ ω, ∑' m, (Reached Y S m).indicator (fun ω => c (Y m ω)) ω ∂P
      = (∫⁻ ω, c (Y 0 ω) ∂P) / P (Y 0 ⁻¹' S) := by
  have hterm : ∀ m, ∫⁻ ω, (Reached Y S m).indicator (fun ω => c (Y m ω)) ω ∂P
      = P (Y 0 ⁻¹' Sᶜ) ^ m * ∫⁻ ω, c (Y 0 ω) ∂P := by
    intro m
    -- independence of the earlier trials and trial `m`
    have hind := hY.indepFun_finset (Finset.range m) {m}
      (Finset.disjoint_singleton_right.mpr Finset.notMem_range_self) hmeas
    let φ : (Finset.range m → β) → ℝ≥0∞ :=
      Set.indicator {z | ∀ i, z i ∉ S} 1
    let ψ : (({m} : Finset ℕ) → β) → ℝ≥0∞ := fun z => c (z ⟨m, Finset.mem_singleton_self m⟩)
    have hφ : Measurable φ := by
      apply measurable_one.indicator
      have : {z : Finset.range m → β | ∀ i, z i ∉ S} = ⋂ i, (fun z => z i) ⁻¹' Sᶜ := by
        ext z; simp
      rw [this]
      exact MeasurableSet.iInter fun i => measurable_pi_apply i hS.compl
    have hψ : Measurable ψ := hc.comp (measurable_pi_apply _)
    have hind' := hind.comp hφ hψ
    have heq : (Reached Y S m).indicator (fun ω => c (Y m ω))
        = (φ ∘ fun ω (i : Finset.range m) => Y i ω) * (ψ ∘ fun ω (i : ({m} : Finset ℕ)) =>
          Y i ω) := by
      funext ω
      simp only [Pi.mul_apply, Function.comp_apply, φ, ψ]
      by_cases h : ω ∈ Reached Y S m
      · have h' : (fun i : Finset.range m => Y i ω) ∈ {z : Finset.range m → β | ∀ i, z i ∉ S} :=
          fun i => h i (Finset.mem_range.mp i.2)
        rw [Set.indicator_of_mem h, Set.indicator_of_mem h', Pi.one_apply, one_mul]
      · have h' : (fun i : Finset.range m => Y i ω) ∉ {z : Finset.range m → β | ∀ i, z i ∉ S} :=
          fun h'' => h fun k hk => h'' ⟨k, Finset.mem_range.mpr hk⟩
        rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h', zero_mul]
    rw [heq, lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
      (hφ.comp (measurable_pi_iff.mpr fun i => hmeas i))
      (hψ.comp (measurable_pi_iff.mpr fun i => hmeas i)) hind']
    have h1 : ∫⁻ ω, (φ ∘ fun ω (i : Finset.range m) => Y i ω) ω ∂P = P (Reached Y S m) := by
      have : (φ ∘ fun ω (i : Finset.range m) => Y i ω) = (Reached Y S m).indicator 1 := by
        funext ω
        simp only [Function.comp_apply, φ]
        by_cases h : ω ∈ Reached Y S m
        · have h' : (fun i : Finset.range m => Y i ω)
              ∈ {z : Finset.range m → β | ∀ i, z i ∉ S} :=
            fun i => h i (Finset.mem_range.mp i.2)
          rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
          rfl
        · have h' : (fun i : Finset.range m => Y i ω)
              ∉ {z : Finset.range m → β | ∀ i, z i ∉ S} :=
            fun h'' => h fun k hk => h'' ⟨k, Finset.mem_range.mpr hk⟩
          rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
      rw [this, lintegral_indicator_one (measurableSet_reached hmeas hS m)]
    have h2 : ∫⁻ ω, (ψ ∘ fun ω (i : ({m} : Finset ℕ)) => Y i ω) ω ∂P
        = ∫⁻ ω, c (Y 0 ω) ∂P := by
      simp only [Function.comp_apply, ψ]
      rw [← lintegral_map hc (hmeas m), hid m, lintegral_map hc (hmeas 0)]
    rw [h1, h2, measure_reached Y hY hid hmeas hS m]
  rw [lintegral_tsum (f := fun m ω => (Reached Y S m).indicator (fun ω => c (Y m ω)) ω)
    (fun m => ((hc.comp (hmeas m)).indicator (measurableSet_reached hmeas hS m)).aemeasurable)]
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, Set.preimage_compl,
    prob_compl_eq_one_sub (hmeas 0 hS), ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one,
    div_eq_mul_inv, mul_comm]

/-- The expected number of trials is `1 / P(Y₀ ∈ S)`. Paper: proof of `prop:conf-row`
(conference.tex), renewal count, and proof of `thm:conf-grid`, "the expected number of
proposals is below `17/8`"; full version: `lem:dynamiccellenvelope`
(attention_dynamic_index.tex). -/
theorem expected_trials [IsProbabilityMeasure P] (Y : ℕ → Ω → β) (hY : iIndepFun Y P)
    (hid : ∀ m, P.map (Y m) = P.map (Y 0)) (hmeas : ∀ m, Measurable (Y m)) {S : Set β}
    (hS : MeasurableSet S) :
    ∫⁻ ω, ∑' m, (Reached Y S m).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P
      = 1 / P (Y 0 ⁻¹' S) := by
  rw [renewal_cost Y hY hid hmeas hS (fun _ => 1) measurable_const]
  simp

end ExactSampling.RejectionLoop
