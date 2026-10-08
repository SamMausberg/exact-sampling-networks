import Mathlib

/-!
# Exactness and stopping

Three facts behind the exact samplers (`exact_sampling_networks.tex`, subsection
"Exactness and stopping"; `tanh_scalar.tex`; `tanh_residual.tex`;
`attention_finite_bits.tex`; `conference.tex`).

* `cached_residual_exactness`: a cached center `c` and radius `r` with
  `|c| + r ≤ 1` and `|h - c| ≤ r` give a valid gated mixture of mean `h`.
* `stopped_work_le`: by Tonelli's theorem, the expected work of the reached
  trials is at most the per-trial charges weighted by the probabilities of
  reaching the trials. Neither the work nor `T` is assumed integrable.
* `nontermination_null`: a geometric precision tail gives zero
  nontermination probability.

The algorithms and their probability spaces are not formalized. The charging
hypothesis `hcharge` and the tail hypothesis `htail` are the probability
obligations that the paper discharges from fresh randomness and from certified
interval comparisons.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ExactSampling.ExactnessStopping

/-- Paper: `eq:topmixture` and `eq:internalmixture` (tanh_scalar.tex), with the
cached centers and radii of `eq:resinvariant` (tanh_residual.tex).
Open a gate with probability `r` and return a sign of mean `(h - c) / r`;
otherwise return `+1` or `-1` with masses `(1 - r + c) / 2` and
`(1 - r - c) / 2`. The masses are valid, the normalized mean is a sign mean,
and the mixture has mean exactly `h`. -/
theorem cached_residual_exactness (h c r : ℝ) (hr : 0 < r)
    (hc : |c| + r ≤ 1) (hh : |h - c| ≤ r) :
    0 ≤ (1 - r + c) / 2 ∧ 0 ≤ (1 - r - c) / 2 ∧ |(h - c) / r| ≤ 1 ∧
      r + (1 - r + c) / 2 + (1 - r - c) / 2 = 1 ∧
      r * ((h - c) / r) + (1 - r + c) / 2 - (1 - r - c) / 2 = h := by
  have h1 := neg_abs_le c
  have h2 := le_abs_self c
  refine ⟨by linarith, by linarith, ?_, by ring, ?_⟩
  · rw [abs_div, abs_of_pos hr, div_le_one hr]
    exact hh
  · field_simp
    ring

/-- Paper: `lem:stopping` (tanh_scalar.tex), `eq:stoppedcost`; also the
summation of stage costs in `lem:newprecisionstop` (attention_finite_bits.tex)
and `lem:conf-replay` (conference.tex). Trial `j`, counted from zero, is
reached when `j < T`. If its cost on that event has mean at most `B j` times
the probability of reaching it, then the expected stopped work is at most
`∑ j, B j * P(j < T)`. -/
theorem stopped_work_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : Ω → ℕ) (hT : Measurable T) (C : ℕ → Ω → ℝ≥0∞)
    (hC : ∀ j, Measurable (C j)) (B : ℕ → ℝ≥0∞)
    (hcharge : ∀ j, ∫⁻ ω in {ω | j < T ω}, C j ω ∂μ ≤ B j * μ {ω | j < T ω}) :
    ∫⁻ ω, ∑ j ∈ Finset.range (T ω), C j ω ∂μ ≤
      ∑' j, B j * μ {ω | j < T ω} := by
  have hset : ∀ j, MeasurableSet {ω | j < T ω} := fun j =>
    measurableSet_lt measurable_const hT
  have hsum : ∀ ω, ∑ j ∈ Finset.range (T ω), C j ω =
      ∑' j, Set.indicator {ω | j < T ω} (C j) ω := by
    intro ω
    rw [tsum_eq_sum (s := Finset.range (T ω))]
    · refine Finset.sum_congr rfl fun j hj => ?_
      simp [Set.indicator, Finset.mem_range.mp hj]
    · intro j hj
      simp only [Finset.mem_range, not_lt] at hj
      simp [Set.indicator, not_lt.mpr hj]
  simp_rw [hsum]
  rw [lintegral_tsum fun j => ((hC j).indicator (hset j)).aemeasurable]
  refine ENNReal.tsum_le_tsum fun j => ?_
  rw [lintegral_indicator (hset j)]
  exact hcharge j

/-- Paper: `lem:stopping` (tanh_scalar.tex), the identity
`∑ j ≥ 1, P(T ≥ j) = E T` in `eq:stoppedcost`. -/
theorem lintegral_count_eq_tsum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℕ) (hT : Measurable T) :
    ∫⁻ ω, (T ω : ℝ≥0∞) ∂μ = ∑' j, μ {ω | j < T ω} := by
  have hset : ∀ j, MeasurableSet {ω | j < T ω} := fun j =>
    measurableSet_lt measurable_const hT
  have hpt : ∀ ω, (T ω : ℝ≥0∞) = ∑' j, Set.indicator {ω | j < T ω} 1 ω := by
    intro ω
    rw [tsum_eq_sum (s := Finset.range (T ω))]
    · calc (T ω : ℝ≥0∞) = ∑ _j ∈ Finset.range (T ω), (1 : ℝ≥0∞) := by simp
        _ = _ := Finset.sum_congr rfl fun j hj => by
          simp [Set.indicator, Finset.mem_range.mp hj]
    · intro j hj
      simp only [Finset.mem_range, not_lt] at hj
      simp [Set.indicator, not_lt.mpr hj]
  simp_rw [hpt]
  rw [lintegral_tsum fun j => (measurable_one.indicator (hset j)).aemeasurable]
  exact tsum_congr fun j => lintegral_indicator_one (hset j)

/-- Paper: `lem:stopping` (tanh_scalar.tex), `eq:stoppedcost` with a uniform
charge: `E ∑_{j < T} C_j ≤ B E T`. -/
theorem stopped_work_le_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : Ω → ℕ) (hT : Measurable T) (C : ℕ → Ω → ℝ≥0∞)
    (hC : ∀ j, Measurable (C j)) (B : ℝ≥0∞)
    (hcharge : ∀ j, ∫⁻ ω in {ω | j < T ω}, C j ω ∂μ ≤ B * μ {ω | j < T ω}) :
    ∫⁻ ω, ∑ j ∈ Finset.range (T ω), C j ω ∂μ ≤ B * ∫⁻ ω, (T ω : ℝ≥0∞) ∂μ := by
  rw [lintegral_count_eq_tsum μ T hT, ← ENNReal.tsum_mul_left]
  exact stopped_work_le μ T hT C hC (fun _ => B) hcharge

/-- Paper: `lem:newprecisionstop` (attention_finite_bits.tex), `lem:lazy`
(tanh_bits.tex), and `eq:conf-tail` with `lem:conf-replay` (conference.tex).
If the nontermination event `N` lies in every undecided event `U t`, and
`P(U t) ≤ K 2^{-t}` with `K` finite, then `N` has probability zero. -/
theorem nontermination_null {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Set Ω) (U : ℕ → Set Ω) (hN : ∀ t, N ⊆ U t) (K : ℝ≥0∞) (hK : K ≠ ∞)
    (htail : ∀ t, μ (U t) ≤ K * 2⁻¹ ^ t) : μ N = 0 := by
  have hpow : Tendsto (fun t : ℕ => (2⁻¹ : ℝ≥0∞) ^ t) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have hlim : Tendsto (fun t : ℕ => K * 2⁻¹ ^ t) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hpow (Or.inr hK)
  exact le_antisymm
    (ge_of_tendsto' hlim fun t => (measure_mono (hN t)).trans (htail t)) zero_le

end ExactSampling.ExactnessStopping
