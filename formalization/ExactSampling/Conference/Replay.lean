import Mathlib

/-!
# Exact decisions while precision grows

This file formalizes the probabilistic and arithmetic content of the replay lemma
`lem:conf-replay` (Section `sec:conf-replay` of `paper/conference.tex`; full version
`lem:replayexactsampling` in `paper/attention_moment_decoder.tex`), together with the step of
the proof of `thm:conf-decoder` (full version `thm:momentdecoder`) that applies it.

## Setting

A next-token law on `V` tokens is given by exact cumulative boundaries
`0 = F 0 ≤ F 1 ≤ ... ≤ F V = 1` (`Boundaries`). Paper token `i ∈ {1, ..., V}` is
`i - 1 : Fin V` here, with categorical interval `[F i.castSucc, F i.succ)`. A certified
evaluator at accuracy `p` returns enclosures `lo k ≤ F k ≤ hi k` of width at most `2⁻ᵖ`,
exact at `F 0 = 0` and `F V = 1` (`Enclosure`). The uniform number `U` has law `uniform`,
Lebesgue measure restricted to `[0, 1)`; its first `p` binary digits give the dyadic cell
`[cellLo p U, cellHi p U)`.

## Formalized

* The decision rule agrees with the inverse CDF, also for non-nested replay intervals
  (`decides_invCDF`, `decides_consistent`).
* The tail bound `eq:conf-tail`, in the sharper form `4 (V - 1) 2⁻ᵖ`
  (`undecided_near_boundary`, `volume_undecided_le`, `uniform_undecided_le`).
* Almost-sure termination and the exact output law (`nonterminating_subset`,
  `ae_output_eq`, `uniform_output_none`, `uniform_output_eq_some`).
* The expected temporary replay work as a Lebesgue integral over the events that reach each
  precision (`expected_replayWork_le`), the series inequality
  `∑ 2^{-j} (P + j)^k ≤ P^k ∑ 2^{-j} (j + 1)^k ≤ 2^{k+1} k! P^k`, the prefactor bound
  `8 V T 2^{-p_R} ≤ 1 / (8 (R + 2)^2)`, the expected random bits, the growth
  `p_{2R} ≤ p_R + 3`, and the per-token bound `O_k(A S^k + S)` with explicit constants
  (`expected_token_work_le`).
* The charges match the sampler: on a realized `U` whose first deciding index is `j*`, the
  reach events are exactly `j < j*`, the replay charge is the finite sum over the replays at
  accuracies `p0 + 1, ..., p0 + j*`, and the extra random bits number `j*`
  (`mem_reachSet_iff`, `replayWork_eq_sum`, `extraBits_eq`).
* The prefill cost `T0 · G(p_{2N} + log₂(T0 + 2)) ≤ T0 · 16^k A S0^k` (`prefill_work_le`).
* The autoregressive joint law: fresh uniforms at each step give the product of the
  conditional laws (`replay_joint_law`, `replay_joint_law_prob`).

## Composition with the background schedule

`ReplaySchedule.lean` proves the schedule invariants `len_le_horizon` (`T ≤ 2N`) and
`Inv.N_le_two_len` (`N ≤ 2T`), and `firstHorizon_lt` (`N < 2 T0`). The modules cannot import
each other, so they are composed through matching hypotheses: `expected_token_work_le_schedule`
takes `T ≤ 2N` and `N ≤ 2T`, and `prefill_work_le` takes `N ≤ 2 T0`.

## Stand-ins

* The maintained evaluator of `lem:conf-stability` is represented by an arbitrary family of
  enclosures `E p : Enclosure F p`, one for every precision `p` (and every history in the
  joint-law statements), all enclosing the same exact boundaries.
* Its cost is represented by a function `G` with `G u ≤ A u^k` for `u ≥ 1`: a replay of a
  length-`T` history at accuracy `p` is charged `T * G(p + L)` and a routine token evaluation
  `G(p + L)`, where `L = log₂(T + 2)`.

## Not formalized

The bit-complexity model (that these charges are the actual bit costs), the construction of
the evaluator, and the space bound. The cost bounds are proved for one fixed history (the
expectation is over the fresh uniform of that step only); the conditional expected cost of step
`t` inside the `n`-step product space `Measure.pi` is not stated as such. Likewise, the
assumption that each precision computes its own states without reusing another precision's
approximate states is not expressible here; what is assumed is that the enclosures are a
deterministic function of the history and the precision and enclose the exact boundaries.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace ExactSampling.Replay

variable {V : ℕ}

/-- Exact cumulative boundaries `0 = F 0 ≤ F 1 ≤ ... ≤ F V = 1` of a next-token law on `V` tokens.
Paper: proof of `lem:conf-replay` (conference.tex), the boundaries `F_i` with exact `F_0 = 0` and
`F_V = 1`. -/
structure Boundaries (V : ℕ) where
  /-- The cumulative probabilities. -/
  F : Fin (V + 1) → ℝ
  /-- Cumulative probabilities are nondecreasing. -/
  mono : Monotone F
  /-- `F_0 = 0`. -/
  zero : F 0 = 0
  /-- `F_V = 1`. -/
  last : F (Fin.last V) = 1

/-- Certified enclosures `[lo k, hi k]` of the cumulative boundaries `F k` at accuracy `p`: width at
most `2⁻ᵖ`, exact at the two endpoints.
Paper: proof of `lem:conf-replay` (conference.tex), the intervals `[lower F_i, upper F_i]` "using
exact `F_0 = 0, F_V = 1`"; `lem:replayexactsampling` (attention_moment_decoder.tex). -/
structure Enclosure (F : Fin (V + 1) → ℝ) (p : ℕ) where
  /-- Lower enclosures. -/
  lo : Fin (V + 1) → ℝ
  /-- Upper enclosures. -/
  hi : Fin (V + 1) → ℝ
  /-- Each lower enclosure is below the exact boundary. -/
  lo_le : ∀ k, lo k ≤ F k
  /-- Each upper enclosure is above the exact boundary. -/
  le_hi : ∀ k, F k ≤ hi k
  /-- Certified width at most `2⁻ᵖ`. -/
  width : ∀ k, hi k - lo k ≤ 1 / 2 ^ p
  /-- Exact endpoint `F_0 = 0`. -/
  hi_zero : hi 0 = 0
  /-- Exact endpoint `F_V = 1`. -/
  lo_last : lo (Fin.last V) = 1

/-- The exact enclosure `lo = hi = F` is an enclosure at every precision, so the hypotheses of
`Enclosure` are satisfiable. -/
def Enclosure.exact (B : Boundaries V) (p : ℕ) : Enclosure B.F p where
  lo := B.F
  hi := B.F
  lo_le := fun _ => le_rfl
  le_hi := fun _ => le_rfl
  width := fun _ => by
    rw [sub_self]
    positivity
  hi_zero := B.zero
  lo_last := B.last

/-! ## Dyadic cells -/

/-- Left endpoint `a` of the dyadic cell of width `2⁻ᵖ` containing `U`, i.e. the number given by the
first `p` binary digits of `U`.
Paper: proof of `lem:conf-replay` (conference.tex), the dyadic cell `[a,b]`. -/
noncomputable def cellLo (p : ℕ) (U : ℝ) : ℝ := (⌊(2 : ℝ) ^ p * U⌋ : ℝ) / 2 ^ p

/-- Right endpoint `b = a + 2⁻ᵖ` of the dyadic cell of precision `p` containing `U`.
Paper: proof of `lem:conf-replay` (conference.tex). -/
noncomputable def cellHi (p : ℕ) (U : ℝ) : ℝ := cellLo p U + 1 / 2 ^ p

/-- The cell contains `U` on the left: `a ≤ U`. Auxiliary for the proof of `lem:conf-replay`
(conference.tex). -/
lemma cellLo_le (p : ℕ) (U : ℝ) : cellLo p U ≤ U := by
  unfold cellLo
  have h2 : (0 : ℝ) < 2 ^ p := by positivity
  rw [div_le_iff₀ h2, mul_comm]
  exact Int.floor_le _

/-- The cell contains `U` on the right: `U < b`. Auxiliary for the proof of `lem:conf-replay`
(conference.tex). -/
lemma lt_cellHi (p : ℕ) (U : ℝ) : U < cellHi p U := by
  unfold cellHi cellLo
  have h2 : (0 : ℝ) < 2 ^ p := by positivity
  have := Int.lt_floor_add_one ((2 : ℝ) ^ p * U)
  rw [← add_div, lt_div_iff₀ h2, mul_comm]
  exact this

/-- `U - 2⁻ᵖ < a`. Auxiliary for the tail bound `eq:conf-tail` (conference.tex). -/
lemma sub_lt_cellLo (p : ℕ) (U : ℝ) : U - 1 / 2 ^ p < cellLo p U := by
  have := lt_cellHi p U
  unfold cellHi at this
  linarith

/-- The dyadic cell has width exactly `2⁻ᵖ`. Auxiliary for the proof of `lem:conf-replay`
(conference.tex). -/
lemma cellHi_sub_cellLo (p : ℕ) (U : ℝ) : cellHi p U - cellLo p U = 1 / 2 ^ p := by
  unfold cellHi; ring

/-- For `U ≥ 0` the cell starts at or after `0`. Auxiliary for `eq:conf-tail` (conference.tex): the
exact endpoint `F_0 = 0` never blocks a decision. -/
lemma cellLo_nonneg (p : ℕ) {U : ℝ} (hU : 0 ≤ U) : 0 ≤ cellLo p U := by
  unfold cellLo
  apply div_nonneg _ (by positivity)
  exact_mod_cast Int.floor_nonneg.mpr (by positivity)

/-- For `U < 1` the cell ends at or before `1`. Auxiliary for `eq:conf-tail` (conference.tex): the
exact endpoint `F_V = 1` never blocks a decision. -/
lemma cellHi_le_one (p : ℕ) {U : ℝ} (hU : U < 1) : cellHi p U ≤ 1 := by
  unfold cellHi cellLo
  have h2 : (0 : ℝ) < 2 ^ p := by positivity
  have hlt : ⌊(2 : ℝ) ^ p * U⌋ < ((2 ^ p : ℕ) : ℤ) := by
    rw [Int.floor_lt]
    push_cast
    nlinarith
  have hle : (⌊(2 : ℝ) ^ p * U⌋ : ℝ) + 1 ≤ 2 ^ p := by
    have := Int.add_one_le_of_lt hlt
    exact_mod_cast this
  rw [← add_div, div_le_one h2]
  exact hle

/-- Revealing one more uniform bit refines the cell: the left endpoint does not decrease.
Paper: proof of `lem:conf-replay` (conference.tex), "reveal the next uniform bit". -/
lemma cellLo_le_succ (p : ℕ) (U : ℝ) : cellLo p U ≤ cellLo (p + 1) U := by
  unfold cellLo
  have e : (2 : ℝ) ^ (p + 1) * U = 2 * ((2 : ℝ) ^ p * U) := by ring
  have e2 : (2 : ℝ) ^ (p + 1) = 2 * 2 ^ p := by ring
  rw [e, e2]
  have h2 : (0 : ℝ) < 2 ^ p := by positivity
  have hfl : (2 : ℝ) * ⌊(2 : ℝ) ^ p * U⌋ ≤ ⌊2 * ((2 : ℝ) ^ p * U)⌋ := by
    have : 2 * ⌊(2 : ℝ) ^ p * U⌋ ≤ ⌊2 * ((2 : ℝ) ^ p * U)⌋ := by
      rw [Int.le_floor]
      push_cast
      linarith [Int.floor_le ((2 : ℝ) ^ p * U)]
    exact_mod_cast this
  rw [div_le_div_iff₀ h2 (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hfl h2.le]

/-- Revealing one more uniform bit refines the cell: the right endpoint does not increase.
Paper: proof of `lem:conf-replay` (conference.tex), "reveal the next uniform bit". -/
lemma cellHi_succ_le (p : ℕ) (U : ℝ) : cellHi (p + 1) U ≤ cellHi p U := by
  unfold cellHi cellLo
  have e : (2 : ℝ) ^ (p + 1) * U = 2 * ((2 : ℝ) ^ p * U) := by ring
  have e2 : (2 : ℝ) ^ (p + 1) = 2 * 2 ^ p := by ring
  rw [e, e2]
  have h2 : (0 : ℝ) < 2 ^ p := by positivity
  have hfl : (⌊2 * ((2 : ℝ) ^ p * U)⌋ : ℝ) + 1 ≤ 2 * ⌊(2 : ℝ) ^ p * U⌋ + 2 := by
    have h1 : ⌊2 * ((2 : ℝ) ^ p * U)⌋ < 2 * ⌊(2 : ℝ) ^ p * U⌋ + 2 := by
      rw [Int.floor_lt]
      push_cast
      linarith [Int.lt_floor_add_one ((2 : ℝ) ^ p * U)]
    have : ⌊2 * ((2 : ℝ) ^ p * U)⌋ + 1 ≤ 2 * ⌊(2 : ℝ) ^ p * U⌋ + 2 := by omega
    exact_mod_cast this
  rw [← add_div, ← add_div, div_le_div_iff₀ (by positivity) h2]
  nlinarith [mul_le_mul_of_nonneg_right hfl h2.le]

/-! ## The decision rule -/

/-- The decision rule. In paper indexing, token `i ∈ {1, ..., V}` is output from the cell `[a, b]`
when `upper F_{i-1} ≤ a` and `b ≤ lower F_i`; here token `i : Fin V` (paper token `i + 1`) is
output when `hi i.castSucc ≤ a` and `b ≤ lo i.succ`. Equality at a cell endpoint is permitted.
Paper: proof of `lem:conf-replay` (conference.tex); `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
def Decides (lo hi : Fin (V + 1) → ℝ) (a b : ℝ) (i : Fin V) : Prop :=
  hi i.castSucc ≤ a ∧ b ≤ lo i.succ

/-- The inverse-CDF output: `U` lies in the categorical interval `[F i.castSucc, F i.succ)`.
Paper: proof of `lem:conf-replay` (conference.tex), "the inverse-CDF law". -/
def InvCDF (F : Fin (V + 1) → ℝ) (U : ℝ) (i : Fin V) : Prop :=
  F i.castSucc ≤ U ∧ U < F i.succ

/-- Exactness of the decision rule: if the cell `[a, b)` containing `U` is decided as token `i` by
any enclosures of the exact boundaries, then `U` lies in `[F_{i-1}, F_i)`.
Paper: proof of `lem:conf-replay` (conference.tex); `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
theorem decides_invCDF {F lo hi : Fin (V + 1) → ℝ} (hlo : ∀ k, lo k ≤ F k)
    (hhi : ∀ k, F k ≤ hi k) {a b U : ℝ} (ha : a ≤ U) (hb : U < b) {i : Fin V}
    (h : Decides lo hi a b i) : InvCDF F U i :=
  ⟨(hhi _).trans (h.1.trans ha), hb.trans_le (h.2.trans (hlo _))⟩

/-- The categorical intervals are disjoint, so the inverse-CDF output is unique. Auxiliary for the
proof of `lem:conf-replay` (conference.tex). -/
theorem invCDF_unique {F : Fin (V + 1) → ℝ} (hF : Monotone F) {U : ℝ} {i j : Fin V}
    (hi : InvCDF F U i) (hj : InvCDF F U j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have : F i.succ ≤ F j.castSucc := hF (Fin.succ_le_castSucc_iff.mpr h)
    linarith [hi.2, hj.1]
  · have : F j.succ ≤ F i.castSucc := hF (Fin.succ_le_castSucc_iff.mpr h)
    linarith [hj.2, hi.1]

/-- Every `U ∈ [0, 1)` lies in some categorical interval. Auxiliary for the proof of
`lem:conf-replay` (conference.tex). -/
theorem invCDF_exists (B : Boundaries V) {U : ℝ} (hU : U ∈ Ico (0 : ℝ) 1) :
    ∃ i, InvCDF B.F U i := by
  classical
  let S : Finset (Fin (V + 1)) := Finset.univ.filter (fun k => U < B.F k)
  have hS : S.Nonempty := ⟨Fin.last V, by simp [S, B.last, hU.2]⟩
  have hkS : S.min' hS ∈ S := S.min'_mem hS
  have hUk : U < B.F (S.min' hS) := (Finset.mem_filter.mp hkS).2
  have hk0 : S.min' hS ≠ 0 := by
    intro h0
    rw [h0, B.zero] at hUk
    linarith [hU.1]
  obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr hk0
  refine ⟨i, ?_, hi ▸ hUk⟩
  by_contra hlt
  push Not at hlt
  have hmem : i.castSucc ∈ S := by simp [S, hlt]
  have := S.min'_le _ hmem
  rw [← hi] at this
  exact absurd this (not_le.mpr (Fin.castSucc_lt_succ (i := i)))

/-- The boundary conditions force `V ≥ 1`. Auxiliary for `eq:conf-tail` (conference.tex). -/
lemma Boundaries.one_le (B : Boundaries V) : 1 ≤ V := by
  rcases Nat.eq_zero_or_pos V with h | h
  · subst h
    have h1 := B.last
    have h0 := B.zero
    have : (Fin.last 0) = (0 : Fin 1) := rfl
    rw [this, h0] at h1
    norm_num at h1
  · exact h

/-- Cumulative boundaries are nonnegative. Auxiliary for the proof of `lem:conf-replay`
(conference.tex). -/
lemma Boundaries.nonneg (B : Boundaries V) (k : Fin (V + 1)) : 0 ≤ B.F k := by
  rw [← B.zero]; exact B.mono (Fin.zero_le k)

/-- Cumulative boundaries are at most one. Auxiliary for the proof of `lem:conf-replay`
(conference.tex). -/
lemma Boundaries.le_one (B : Boundaries V) (k : Fin (V + 1)) : B.F k ≤ 1 := by
  rw [← B.last]; exact B.mono (Fin.le_last k)

/-- An upper enclosure exceeds the boundary by at most the width. Auxiliary for `eq:conf-tail`
(conference.tex). -/
lemma Enclosure.hi_le {F : Fin (V + 1) → ℝ} {p : ℕ} (E : Enclosure F p) (k : Fin (V + 1)) :
    E.hi k ≤ F k + 1 / 2 ^ p := by
  linarith [E.width k, E.lo_le k]

/-- A lower enclosure falls short of the boundary by at most the width. Auxiliary for `eq:conf-tail`
(conference.tex). -/
lemma Enclosure.le_lo {F : Fin (V + 1) → ℝ} {p : ℕ} (E : Enclosure F p) (k : Fin (V + 1)) :
    F k - 1 / 2 ^ p ≤ E.lo k := by
  linarith [E.width k, E.le_hi k]

/-- The precision-`p` comparison is undecided: no token is decided from the dyadic cell of `U` with
the enclosures `E`.
Paper: proof of `lem:conf-replay` (conference.tex), `eq:conf-tail`. -/
def Undecided {F : Fin (V + 1) → ℝ} {p : ℕ} (E : Enclosure F p) (U : ℝ) : Prop :=
  ∀ i, ¬ Decides E.lo E.hi (cellLo p U) (cellHi p U) i

/-- Different replay intervals need not be nested: decisions from any two enclosures of the same
exact boundaries, at any two precisions, name the same token.
Paper: proof of `lem:conf-replay` (conference.tex), "Different replay intervals need not be nested";
`lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem decides_consistent {F : Fin (V + 1) → ℝ} (hF : Monotone F) {p p' : ℕ}
    (E : Enclosure F p) (E' : Enclosure F p') {U : ℝ} {i j : Fin V}
    (h : Decides E.lo E.hi (cellLo p U) (cellHi p U) i)
    (h' : Decides E'.lo E'.hi (cellLo p' U) (cellHi p' U) j) : i = j :=
  invCDF_unique hF (decides_invCDF E.lo_le E.le_hi (cellLo_le p U) (lt_cellHi p U) h)
    (decides_invCDF E'.lo_le E'.le_hi (cellLo_le p' U) (lt_cellHi p' U) h')

/-! ## The undecided tail `eq:conf-tail` -/

/-- If the precision-`p` comparison is undecided, then `U` lies within `2^{1-p}` of one of the
`V - 1` interior boundaries `F_1, ..., F_{V-1}`.
Paper: proof of `lem:conf-replay` (conference.tex), the sentence before `eq:conf-tail`
(conference.tex); full version before `eq:replayuncertainty` (attention_moment_decoder.tex). -/
theorem undecided_near_boundary (B : Boundaries V) {p : ℕ} (E : Enclosure B.F p) {U : ℝ}
    (hU : U ∈ Ico (0 : ℝ) 1) (h : Undecided E U) :
    ∃ k : Fin (V + 1), 0 < (k : ℕ) ∧ (k : ℕ) < V ∧ |U - B.F k| < 2 / 2 ^ p := by
  obtain ⟨i, hi1, hi2⟩ := invCDF_exists B hU
  have hcell := sub_lt_cellLo p U
  have hcellLo := cellLo_le p U
  have hb : cellHi p U = cellLo p U + 1 / 2 ^ p := rfl
  have hq : 2 / (2 : ℝ) ^ p = 2 * (1 / 2 ^ p) := by ring
  have hpos : 0 < 1 / (2 : ℝ) ^ p := by positivity
  by_cases h1 : E.hi i.castSucc ≤ cellLo p U
  · have h2 : E.lo i.succ < cellHi p U := by
      by_contra h2
      exact h i ⟨h1, not_lt.mp h2⟩
    have hlo := E.le_lo i.succ
    refine ⟨i.succ, by simp, ?_, ?_⟩
    · by_contra hV
      have hlast : i.succ = Fin.last V := Fin.ext (by simp at hV ⊢; omega)
      rw [hlast, E.lo_last] at h2
      linarith [cellHi_le_one p hU.2]
    · rw [abs_lt]
      constructor <;> linarith
  · push Not at h1
    have hhi := E.hi_le i.castSucc
    refine ⟨i.castSucc, ?_, by simp, ?_⟩
    · by_contra h0
      have hz : i.castSucc = 0 := Fin.ext (by simp at h0 ⊢; omega)
      rw [hz, E.hi_zero] at h1
      linarith [cellLo_nonneg p hU.1]
    · rw [abs_lt]
      constructor <;> linarith

/-- The uniform law of `U` on `[0, 1)`: Lebesgue measure restricted to `[0, 1)`.
Paper: proof of `lem:conf-replay` (conference.tex), the fresh uniform binary expansion `U`. -/
noncomputable def uniform : Measure ℝ := volume.restrict (Ico (0 : ℝ) 1)

/-- The uniform law on `[0, 1)` is a probability measure. -/
instance : IsProbabilityMeasure uniform :=
  ⟨by simp [uniform, Measure.restrict_apply MeasurableSet.univ]⟩

/-- Tail bound `eq:conf-tail` in the sharper form `4 (V - 1) 2⁻ᵖ`: the Lebesgue measure of the set
of `U ∈ [0, 1)` whose precision-`p` comparison is undecided.
Paper: `eq:conf-tail` in `lem:conf-replay` (conference.tex); `eq:replayuncertainty` in
`lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem volume_undecided_le (B : Boundaries V) {p : ℕ} (E : Enclosure B.F p) :
    volume {U | U ∈ Ico (0 : ℝ) 1 ∧ Undecided E U}
      ≤ ENNReal.ofReal (4 * ((V : ℝ) - 1) / 2 ^ p) := by
  have hV := B.one_le
  have hsub : {U | U ∈ Ico (0 : ℝ) 1 ∧ Undecided E U} ⊆ ⋃ j : Fin (V - 1),
      Ioo (B.F ⟨j + 1, by have := j.isLt; omega⟩ - 2 / 2 ^ p)
        (B.F ⟨j + 1, by have := j.isLt; omega⟩ + 2 / 2 ^ p) := by
    rintro U ⟨hU, hund⟩
    obtain ⟨k, hk0, hkV, hk⟩ := undecided_near_boundary B E hU hund
    refine mem_iUnion.mpr ⟨⟨(k : ℕ) - 1, by omega⟩, ?_⟩
    have hk' : (⟨(k : ℕ) - 1 + 1, by omega⟩ : Fin (V + 1)) = k := Fin.ext (by simp; omega)
    simp only [hk']
    rw [abs_lt] at hk
    constructor <;> linarith [hk.1, hk.2]
  calc volume {U | U ∈ Ico (0 : ℝ) 1 ∧ Undecided E U}
      ≤ volume (⋃ j : Fin (V - 1),
          Ioo (B.F ⟨j + 1, by have := j.isLt; omega⟩ - 2 / 2 ^ p)
            (B.F ⟨j + 1, by have := j.isLt; omega⟩ + 2 / 2 ^ p)) := measure_mono hsub
    _ ≤ ∑ j : Fin (V - 1), volume
          (Ioo (B.F ⟨j + 1, by have := j.isLt; omega⟩ - 2 / 2 ^ p)
            (B.F ⟨j + 1, by have := j.isLt; omega⟩ + 2 / 2 ^ p)) :=
        measure_iUnion_fintype_le _ _
    _ = ∑ _j : Fin (V - 1), ENNReal.ofReal (4 / 2 ^ p) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Real.volume_Ioo]
        congr 1
        ring
    _ = ENNReal.ofReal (4 * ((V : ℝ) - 1) / 2 ^ p) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Nat.cast_sub hV]
        push_cast
        ring

/-- Tail bound `eq:conf-tail`: under the uniform law, `P(undecided at precision p) ≤ 4 V 2⁻ᵖ`.
Paper: `eq:conf-tail` in `lem:conf-replay` (conference.tex); `eq:replayuncertainty` in
`lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem uniform_undecided_le (B : Boundaries V) {p : ℕ} (E : Enclosure B.F p) :
    uniform {U | Undecided E U} ≤ ENNReal.ofReal (4 * V / 2 ^ p) := by
  rw [uniform, Measure.restrict_apply' measurableSet_Ico]
  calc volume ({U | Undecided E U} ∩ Ico 0 1)
      = volume {U | U ∈ Ico (0 : ℝ) 1 ∧ Undecided E U} := by
        congr 1; ext U; simp [and_comm]
    _ ≤ ENNReal.ofReal (4 * ((V : ℝ) - 1) / 2 ^ p) := volume_undecided_le B E
    _ ≤ ENNReal.ofReal (4 * V / 2 ^ p) := by
        apply ENNReal.ofReal_le_ofReal
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith

/-! ## Almost-sure termination and the exact output law -/

/-- Decision at precision `p` with the replay enclosures `E p` of that precision.
Paper: proof of `lem:conf-replay` (conference.tex). -/
def DecidedAt {F : Fin (V + 1) → ℝ} (E : ∀ p, Enclosure F p) (p : ℕ) (U : ℝ) (i : Fin V) :
    Prop :=
  Decides (E p).lo (E p).hi (cellLo p U) (cellHi p U) i

open Classical in
/-- The replay sampler started at routine precision `p0`: it compares the cells at precisions
`p0, p0 + 1, ...` with the enclosures of the same precision and returns the token decided at the
first precision where one is decided, or `none` if no precision decides.
Paper: proof of `lem:conf-replay` (conference.tex); `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
noncomputable def output {F : Fin (V + 1) → ℝ} (E : ∀ p, Enclosure F p) (p0 : ℕ) (U : ℝ) :
    Option (Fin V) :=
  if h : ∃ j i, DecidedAt E (p0 + j) U i then some (Classical.choose (Nat.find_spec h))
  else none

/-- If `U` is at distance at least `2^{1-p}` from both boundaries of its categorical interval, then
the precision-`p` comparison decides it. Auxiliary for the termination claim in the proof of
`lem:conf-replay` (conference.tex). -/
theorem decidedAt_of_separated (B : Boundaries V) (E : ∀ p, Enclosure B.F p) {U : ℝ} {i : Fin V}
    {p : ℕ} (h1 : B.F i.castSucc + 2 / 2 ^ p ≤ U) (h2 : U + 2 / 2 ^ p ≤ B.F i.succ) :
    DecidedAt E p U i := by
  have hq : 2 / (2 : ℝ) ^ p = 2 * (1 / 2 ^ p) := by ring
  have hcell := sub_lt_cellLo p U
  have hcellLo := cellLo_le p U
  have hb : cellHi p U = cellLo p U + 1 / 2 ^ p := rfl
  have hhi := (E p).hi_le i.castSucc
  have hlo := (E p).le_lo i.succ
  constructor <;> linarith

/-- Outside the finite set of true boundaries, the dyadic cell and the enclosure errors eventually
fit within one categorical interval: all sufficiently fine precisions decide the inverse-CDF token.
Paper: proof of `lem:conf-replay` (conference.tex), "Outside the finite set of true boundaries ...";
`lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem eventually_decidedAt (B : Boundaries V) (E : ∀ p, Enclosure B.F p) {U : ℝ}
    (hU : U ∈ Ico (0 : ℝ) 1) (hUF : U ∉ range B.F) :
    ∃ i, InvCDF B.F U i ∧ ∀ᶠ p in atTop, DecidedAt E p U i := by
  obtain ⟨i, hi1, hi2⟩ := invCDF_exists B hU
  have hne1 : B.F i.castSucc ≠ U := fun h => hUF ⟨_, h⟩
  have hlt1 : B.F i.castSucc < U := lt_of_le_of_ne hi1 hne1
  set δ := min (U - B.F i.castSucc) (B.F i.succ - U) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hlim : Tendsto (fun p : ℕ => 2 / (2 : ℝ) ^ p) atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_mul 2
    simp only [mul_zero] at h
    refine h.congr fun p => ?_
    rw [one_div_pow, mul_one_div]
  refine ⟨i, ⟨hi1, hi2⟩, ?_⟩
  filter_upwards [(hlim.eventually (ge_mem_nhds hδpos))] with p hp
  apply decidedAt_of_separated B E
  · have := min_le_left (U - B.F i.castSucc) (B.F i.succ - U)
    linarith
  · have := min_le_right (U - B.F i.castSucc) (B.F i.succ - U)
    linarith

/-- Whenever the replay sampler returns a token, it is the inverse-CDF token.
Paper: proof of `lem:conf-replay` (conference.tex); `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
theorem output_invCDF (B : Boundaries V) (E : ∀ p, Enclosure B.F p) (p0 : ℕ) {U : ℝ}
    {i : Fin V} (h : output E p0 U = some i) : InvCDF B.F U i := by
  classical
  unfold output at h
  split_ifs at h with hex
  obtain rfl := Option.some.inj h
  have hspec := Classical.choose_spec (Nat.find_spec hex)
  exact decides_invCDF (E _).lo_le (E _).le_hi (cellLo_le _ U) (lt_cellHi _ U) hspec

/-- Outside the boundaries the replay sampler stops and returns the inverse-CDF token.
Paper: proof of `lem:conf-replay` (conference.tex); `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
theorem output_eq_some_of_not_mem (B : Boundaries V) (E : ∀ p, Enclosure B.F p) (p0 : ℕ)
    {U : ℝ} (hU : U ∈ Ico (0 : ℝ) 1) (hUF : U ∉ range B.F) :
    ∃ i, InvCDF B.F U i ∧ output E p0 U = some i := by
  obtain ⟨i, hi, hev⟩ := eventually_decidedAt B E hU hUF
  obtain ⟨P, hP⟩ := eventually_atTop.mp hev
  have hex : ∃ j i, DecidedAt E (p0 + j) U i := ⟨P, i, hP _ (by omega)⟩
  have hsome : ∃ i', output E p0 U = some i' := by
    unfold output
    split_ifs
    exact ⟨_, rfl⟩
  obtain ⟨i', hi'⟩ := hsome
  exact ⟨i', output_invCDF B E p0 hi', hi'⟩

/-- The set of `U ∈ [0, 1)` on which no finite precision decides is contained in the finite set of
true boundaries.
Paper: proof of `lem:conf-replay` (conference.tex), "the procedure therefore stops almost surely";
`lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem nonterminating_subset (B : Boundaries V) (E : ∀ p, Enclosure B.F p) (p0 : ℕ) :
    {U | U ∈ Ico (0 : ℝ) 1 ∧ output E p0 U = none} ⊆ range B.F := by
  rintro U ⟨hU, hnone⟩
  by_contra hUF
  obtain ⟨i, -, hi⟩ := output_eq_some_of_not_mem B E p0 hU hUF
  rw [hi] at hnone
  exact Option.some_ne_none _ hnone

/-- Almost surely the replay output equals the inverse-CDF output.
Paper: proof of `lem:conf-replay` (conference.tex), "gives exactly the inverse-CDF law";
`lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem ae_output_eq (B : Boundaries V) (E : ∀ p, Enclosure B.F p) (p0 : ℕ) :
    ∀ᵐ U ∂uniform, ∀ i, output E p0 U = some i ↔ InvCDF B.F U i := by
  have hnull : volume (range B.F) = 0 := (finite_range B.F).measure_zero volume
  have hae : ∀ᵐ U ∂volume, U ∉ range B.F := measure_eq_zero_iff_ae_notMem.mp hnull
  rw [uniform, ae_restrict_iff' measurableSet_Ico]
  filter_upwards [hae] with U hUF hU i
  obtain ⟨j, hj, hout⟩ := output_eq_some_of_not_mem B E p0 hU hUF
  rw [hout]
  constructor
  · intro h
    rw [Option.some.inj h] at hj
    exact hj
  · intro h
    rw [invCDF_unique B.mono hj h]

/-- The replay sampler stops almost surely.
Paper: proof of `lem:conf-replay` (conference.tex); `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
theorem uniform_output_none (B : Boundaries V) (E : ∀ p, Enclosure B.F p) (p0 : ℕ) :
    uniform {U | output E p0 U = none} = 0 := by
  rw [uniform, Measure.restrict_apply' measurableSet_Ico]
  apply measure_mono_null _ ((finite_range B.F).measure_zero volume)
  rintro U ⟨hnone, hU⟩
  exact nonterminating_subset B E p0 ⟨hU, hnone⟩

/-- Exact output law: the replay sampler returns token `i` with probability
`F i.succ - F i.castSucc` (paper: `F_i - F_{i-1}`).
Paper: proof of `lem:conf-replay` (conference.tex); `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
theorem uniform_output_eq_some (B : Boundaries V) (E : ∀ p, Enclosure B.F p) (p0 : ℕ)
    (i : Fin V) :
    uniform {U | output E p0 U = some i} = ENNReal.ofReal (B.F i.succ - B.F i.castSucc) := by
  have hae : {U | output E p0 U = some i} =ᵐ[uniform] Ico (B.F i.castSucc) (B.F i.succ) := by
    rw [eventuallyEqSet_iff]
    filter_upwards [ae_output_eq B E p0] with U hU
    exact hU i
  rw [measure_congr hae, uniform, Measure.restrict_apply' measurableSet_Ico]
  have hsub : Ico (B.F i.castSucc) (B.F i.succ) ⊆ Ico 0 1 :=
    Ico_subset_Ico (B.nonneg _) (B.le_one _)
  rw [inter_eq_left.mpr hsub, Real.volume_Ico]

/-- Cumulative probabilities `F_k = ∑_{i < k} p_i` of a probability vector.
Paper: proof of `lem:conf-replay` (conference.tex), the cumulative boundaries `F_i`. -/
noncomputable def cumProb (prob : Fin V → ℝ) (k : Fin (V + 1)) : ℝ :=
  ∑ i : Fin V, if (i : ℕ) < (k : ℕ) then prob i else 0

/-- `F_i - F_{i-1} = p_i` for the cumulative probabilities. Auxiliary for the proof of
`lem:conf-replay` (conference.tex). -/
lemma cumProb_succ_sub (prob : Fin V → ℝ) (i : Fin V) :
    cumProb prob i.succ - cumProb prob i.castSucc = prob i := by
  unfold cumProb
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hji' : (j : ℕ) ≠ i := fun h => hji (Fin.ext h)
    simp only [Fin.val_succ, Fin.val_castSucc]
    split_ifs with h1 h2 h2
    · exact sub_self _
    · exfalso; omega
    · exfalso; omega
    · exact sub_self _
  · simp

/-- The exact cumulative boundaries of a probability vector on `V` tokens.
Paper: proof of `lem:conf-replay` (conference.tex). -/
noncomputable def Boundaries.ofProb (prob : Fin V → ℝ) (hnn : ∀ i, 0 ≤ prob i)
    (hsum : ∑ i, prob i = 1) : Boundaries V where
  F := cumProb prob
  mono := by
    intro a b hab
    refine Finset.sum_le_sum fun i _ => ?_
    have hab' : (a : ℕ) ≤ b := hab
    split_ifs with h1 h2 h2
    · exact le_rfl
    · omega
    · exact hnn i
    · exact le_rfl
  zero := by simp [cumProb]
  last := by simp [cumProb, hsum]

/-- Exact output law in terms of the next-token probabilities: the replay sampler returns token `i`
with probability exactly `p_i`.
Paper: proof of `lem:conf-replay` (conference.tex); `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
theorem uniform_output_eq_prob (prob : Fin V → ℝ) (hnn : ∀ i, 0 ≤ prob i)
    (hsum : ∑ i, prob i = 1) (E : ∀ p, Enclosure (Boundaries.ofProb prob hnn hsum).F p)
    (p0 : ℕ) (i : Fin V) :
    uniform {U | output E p0 U = some i} = ENNReal.ofReal (prob i) := by
  rw [uniform_output_eq_some (Boundaries.ofProb prob hnn hsum) E p0 i]
  exact congrArg ENNReal.ofReal (cumProb_succ_sub prob i)

/-! ## Expected temporary replay work -/

/-- Measurability of the cell endpoint. Auxiliary for the expected-work bound in the proof of
`lem:conf-replay` (conference.tex). -/
lemma measurable_cellLo (p : ℕ) : Measurable (cellLo p) := by
  unfold cellLo
  fun_prop

/-- Measurability of the cell endpoint. Auxiliary for the expected-work bound in the proof of
`lem:conf-replay` (conference.tex). -/
lemma measurable_cellHi (p : ℕ) : Measurable (cellHi p) := by
  unfold cellHi
  exact (measurable_cellLo p).add_const _

/-- The undecided event is measurable. Auxiliary for the expected-work bound in the proof of
`lem:conf-replay` (conference.tex). -/
lemma measurableSet_undecided {F : Fin (V + 1) → ℝ} {p : ℕ} (E : Enclosure F p) :
    MeasurableSet {U | Undecided E U} := by
  simp only [Undecided, Decides, ofPred_forall]
  refine MeasurableSet.iInter fun i => ?_
  refine MeasurableSet.compl ?_
  exact (measurableSet_le measurable_const (measurable_cellLo p)).inter
    (measurableSet_le (measurable_cellHi p) measurable_const)

/-- The event that the sampler reaches the replay at accuracy `p0 + j + 1`: the comparisons at
precisions `p0, ..., p0 + j` were all undecided.
Paper: proof of `lem:conf-replay` (conference.tex), "summing costs on the events that reach each
precision". -/
def ReachSet {F : Fin (V + 1) → ℝ} (E : ∀ p, Enclosure F p) (p0 j : ℕ) : Set ℝ :=
  {U | ∀ j' ≤ j, Undecided (E (p0 + j')) U}

/-- The reach events are measurable. Auxiliary for the proof of `lem:conf-replay` (conference.tex).
-/
lemma measurableSet_reachSet {F : Fin (V + 1) → ℝ} (E : ∀ p, Enclosure F p) (p0 j : ℕ) :
    MeasurableSet (ReachSet E p0 j) := by
  simp only [ReachSet, ofPred_forall]
  exact MeasurableSet.iInter fun j' => MeasurableSet.iInter fun _ => measurableSet_undecided _

/-- Reaching the replay at accuracy `p0 + j + 1` requires an undecided comparison at precision
`p0 + j`. Auxiliary for the proof of `lem:conf-replay` (conference.tex). -/
lemma reachSet_subset {F : Fin (V + 1) → ℝ} (E : ∀ p, Enclosure F p) (p0 j : ℕ) :
    ReachSet E p0 j ⊆ {U | Undecided (E (p0 + j)) U} :=
  fun _ hU => hU j le_rfl

/-- Summing nonnegative costs `c j` over the events that reach each precision: the expectation is at
most `∑ c j · 4 V 2^{-(p0 + j)}`. No finiteness of the expected stopping time is assumed. The same
bound applies to any per-precision charge (work, random bits, space).
Paper: proof of `lem:conf-replay` (conference.tex), "Summing costs on the events that reach each
precision proves finite expected work without assuming finite expected stopping time first";
`lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem lintegral_reach_le (B : Boundaries V) (E : ∀ p, Enclosure B.F p) (p0 : ℕ)
    (c : ℕ → ℝ≥0∞) :
    ∫⁻ U, ∑' j, (ReachSet E p0 j).indicator (fun _ => c j) U ∂uniform
      ≤ ∑' j, c j * ENNReal.ofReal (4 * V / 2 ^ (p0 + j)) := by
  rw [lintegral_tsum fun j =>
    (measurable_const.indicator (measurableSet_reachSet E p0 j)).aemeasurable]
  refine ENNReal.tsum_le_tsum fun j => ?_
  rw [lintegral_indicator_const (measurableSet_reachSet E p0 j)]
  gcongr
  exact (measure_mono (reachSet_subset E p0 j)).trans (uniform_undecided_le B (E (p0 + j)))

/-- Temporary replay work for one token: when the comparison is undecided at precisions
`p0, ..., p0 + j`, the length-`T` history is replayed at accuracy `p0 + j + 1`, charged
`T * G(p0 + j + 1 + L)`, where `L` stands for `log(T + 2)`.
Paper: proof of `lem:conf-replay` (conference.tex). -/
noncomputable def replayWork {F : Fin (V + 1) → ℝ} (E : ∀ p, Enclosure F p) (p0 T : ℕ)
    (G : ℝ → ℝ) (L U : ℝ) : ℝ≥0∞ :=
  ∑' j, (ReachSet E p0 j).indicator
    (fun _ => ENNReal.ofReal (T * G ((p0 : ℝ) + ((j + 1 : ℕ) : ℝ) + L))) U

/-- The expected temporary replay work is at most `8 V T 2^{-p0} ∑_{j ≥ 0} 2^{-j} G(p0 + j + L)`.
Paper: proof of `lem:conf-replay` (conference.tex), the displayed replay-work bound;
`lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem expected_replayWork_le (B : Boundaries V) (E : ∀ p, Enclosure B.F p) (p0 T : ℕ)
    (G : ℝ → ℝ) (L : ℝ) :
    ∫⁻ U, replayWork E p0 T G L U ∂uniform
      ≤ ENNReal.ofReal (8 * V * T / 2 ^ p0)
        * ∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j * G ((p0 : ℝ) + (j : ℝ) + L)) := by
  set f : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal ((1 / 2 : ℝ) ^ j * G ((p0 : ℝ) + (j : ℝ) + L))
    with hf
  calc ∫⁻ U, replayWork E p0 T G L U ∂uniform
      ≤ ∑' j : ℕ, ENNReal.ofReal (T * G ((p0 : ℝ) + ((j + 1 : ℕ) : ℝ) + L))
          * ENNReal.ofReal (4 * V / 2 ^ (p0 + j)) := lintegral_reach_le B E p0 _
    _ = ∑' j : ℕ, ENNReal.ofReal (8 * V * T / 2 ^ p0) * f (j + 1) := by
        refine tsum_congr fun j => ?_
        rw [hf, ← ENNReal.ofReal_mul' (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [one_div_pow]
        rw [pow_add, pow_succ]
        field_simp
        ring
    _ = ENNReal.ofReal (8 * V * T / 2 ^ p0) * ∑' j : ℕ, f (j + 1) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (8 * V * T / 2 ^ p0) * ∑' j : ℕ, f j := by
        exact mul_le_mul_right (ENNReal.tsum_comp_le_tsum_of_injective Nat.succ_injective f) _

/-! ## The geometric moment series -/

/-- `(j + 1)^k ≤ k! · binom(j + k, k)`.
Paper: proof of `lem:conf-replay` (conference.tex), "(j+1)^k ≤ k! binom(j+k,k)". -/
lemma succ_pow_le_factorial_mul_choose (j k : ℕ) :
    ((j : ℝ) + 1) ^ k ≤ (k.factorial : ℝ) * ((j + k).choose k : ℝ) := by
  have h := Nat.pow_succ_le_ascFactorial (j + 1) k
  rw [Nat.ascFactorial_eq_factorial_mul_choose] at h
  exact_mod_cast h

/-- Summability of the binomial series at `x = 1/2`. Auxiliary for the proof of `lem:conf-replay`
(conference.tex). -/
lemma summable_choose_half (k : ℕ) :
    Summable (fun j : ℕ => ((j + k).choose k : ℝ) * (1 / 2 : ℝ) ^ j) :=
  summable_choose_mul_geometric_of_norm_lt_one k (by norm_num)

/-- The binomial generating function at `x = 1/2`:
`∑_j binom(j + k, k) 2^{-j} = (1 - 1/2)^{-(k+1)} = 2^{k+1}`.
Paper: proof of `lem:conf-replay` (conference.tex), "the binomial generating function". -/
lemma tsum_choose_half (k : ℕ) :
    ∑' j : ℕ, ((j + k).choose k : ℝ) * (1 / 2 : ℝ) ^ j = 2 ^ (k + 1) := by
  rw [tsum_choose_mul_geometric_of_norm_lt_one k (by norm_num)]
  norm_num
  rw [one_div_pow, one_div, inv_inv]

/-- Summability of `∑ 2^{-j} (j + 1)^k`. Auxiliary for the proof of `lem:conf-replay`
(conference.tex). -/
lemma summable_half_mul_succ_pow (k : ℕ) :
    Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j * ((j : ℝ) + 1) ^ k) := by
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    ((summable_choose_half k).mul_left (k.factorial : ℝ))
  calc (1 / 2 : ℝ) ^ j * ((j : ℝ) + 1) ^ k
      ≤ (1 / 2 : ℝ) ^ j * ((k.factorial : ℝ) * ((j + k).choose k : ℝ)) := by
        gcongr
        exact succ_pow_le_factorial_mul_choose j k
    _ = (k.factorial : ℝ) * (((j + k).choose k : ℝ) * (1 / 2 : ℝ) ^ j) := by ring

/-- `∑_{j ≥ 0} 2^{-j} (j + 1)^k ≤ 2^{k+1} k!`.
Paper: proof of `lem:conf-replay` (conference.tex), the second displayed inequality. -/
theorem tsum_half_mul_succ_pow_le (k : ℕ) :
    Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j * ((j : ℝ) + 1) ^ k) ∧
      ∑' j : ℕ, (1 / 2 : ℝ) ^ j * ((j : ℝ) + 1) ^ k ≤ 2 ^ (k + 1) * k.factorial := by
  refine ⟨summable_half_mul_succ_pow k, ?_⟩
  calc ∑' j : ℕ, (1 / 2 : ℝ) ^ j * ((j : ℝ) + 1) ^ k
      ≤ ∑' j : ℕ, (k.factorial : ℝ) * (((j + k).choose k : ℝ) * (1 / 2 : ℝ) ^ j) := by
        refine (summable_half_mul_succ_pow k).tsum_le_tsum (fun j => ?_)
          ((summable_choose_half k).mul_left _)
        calc (1 / 2 : ℝ) ^ j * ((j : ℝ) + 1) ^ k
            ≤ (1 / 2 : ℝ) ^ j * ((k.factorial : ℝ) * ((j + k).choose k : ℝ)) := by
              gcongr
              exact succ_pow_le_factorial_mul_choose j k
          _ = (k.factorial : ℝ) * (((j + k).choose k : ℝ) * (1 / 2 : ℝ) ^ j) := by ring
    _ = 2 ^ (k + 1) * k.factorial := by
        rw [tsum_mul_left, tsum_choose_half]
        ring

/-- `(P + j)^k ≤ P^k (j + 1)^k` for `P ≥ 1`. Auxiliary for the proof of `lem:conf-replay`
(conference.tex). -/
lemma add_pow_le_pow_mul_succ_pow (k j : ℕ) {P : ℝ} (hP : 1 ≤ P) :
    (P + j) ^ k ≤ P ^ k * ((j : ℝ) + 1) ^ k := by
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

/-- Summability of `∑ 2^{-j} (P + j)^k`. Auxiliary for the proof of `lem:conf-replay`
(conference.tex). -/
lemma summable_half_mul_add_pow (k : ℕ) {P : ℝ} (hP : 1 ≤ P) :
    Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j * (P + j) ^ k) := by
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    ((summable_half_mul_succ_pow k).mul_left (P ^ k))
  calc (1 / 2 : ℝ) ^ j * (P + j) ^ k ≤ (1 / 2 : ℝ) ^ j * (P ^ k * ((j : ℝ) + 1) ^ k) := by
        gcongr
        exact add_pow_le_pow_mul_succ_pow k j hP
    _ = P ^ k * ((1 / 2 : ℝ) ^ j * ((j : ℝ) + 1) ^ k) := by ring

/-- `∑_{j ≥ 0} 2^{-j} (P + j)^k ≤ P^k ∑_{j ≥ 0} 2^{-j} (j + 1)^k` for `P ≥ 1`.
Paper: proof of `lem:conf-replay` (conference.tex), the first displayed inequality. -/
theorem tsum_half_mul_add_pow_le_left (k : ℕ) {P : ℝ} (hP : 1 ≤ P) :
    Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j * (P + j) ^ k) ∧
      ∑' j : ℕ, (1 / 2 : ℝ) ^ j * (P + j) ^ k
        ≤ P ^ k * ∑' j : ℕ, (1 / 2 : ℝ) ^ j * ((j : ℝ) + 1) ^ k := by
  refine ⟨summable_half_mul_add_pow k hP, ?_⟩
  rw [← tsum_mul_left]
  refine (summable_half_mul_add_pow k hP).tsum_le_tsum (fun j => ?_)
    ((summable_half_mul_succ_pow k).mul_left _)
  calc (1 / 2 : ℝ) ^ j * (P + j) ^ k ≤ (1 / 2 : ℝ) ^ j * (P ^ k * ((j : ℝ) + 1) ^ k) := by
        gcongr
        exact add_pow_le_pow_mul_succ_pow k j hP
    _ = P ^ k * ((1 / 2 : ℝ) ^ j * ((j : ℝ) + 1) ^ k) := by ring

/-- `∑_{j ≥ 0} 2^{-j} (P + j)^k ≤ 2^{k+1} k! P^k` for `P ≥ 1`.
Paper: proof of `lem:conf-replay` (conference.tex), the displayed chain; `lem:replayexactsampling`
(attention_moment_decoder.tex), "One explicit inequality". -/
theorem tsum_half_mul_add_pow_le (k : ℕ) {P : ℝ} (hP : 1 ≤ P) :
    Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j * (P + j) ^ k) ∧
      ∑' j : ℕ, (1 / 2 : ℝ) ^ j * (P + j) ^ k ≤ 2 ^ (k + 1) * k.factorial * P ^ k := by
  refine ⟨summable_half_mul_add_pow k hP, ?_⟩
  calc ∑' j : ℕ, (1 / 2 : ℝ) ^ j * (P + j) ^ k
      ≤ P ^ k * ∑' j : ℕ, (1 / 2 : ℝ) ^ j * ((j : ℝ) + 1) ^ k :=
        (tsum_half_mul_add_pow_le_left k hP).2
    _ ≤ P ^ k * (2 ^ (k + 1) * k.factorial) := by
        gcongr
        exact (tsum_half_mul_succ_pow_le k).2
    _ = 2 ^ (k + 1) * k.factorial * P ^ k := by ring

/-- If `G u ≤ A u^k` for `u ≥ 1`, the geometric sum of `G` in the replay-work bound is at most
`A 2^{k+1} k! P^k` for `P ≥ 1` (the degree in routine precision is preserved).
Paper: proof of `lem:conf-replay` (conference.tex); proof of `thm:conf-decoder` (conference.tex),
"Its geometric moment bound preserves the degree in routine precision". -/
theorem tsum_half_mul_G_le {G : ℝ → ℝ} {A : ℝ} {k : ℕ}
    (hG : ∀ u, 1 ≤ u → G u ≤ A * u ^ k) {P : ℝ} (hP : 1 ≤ P) :
    ∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j * G (P + j))
      ≤ ENNReal.ofReal (A * (2 ^ (k + 1) * k.factorial * P ^ k)) := by
  by_cases hA : 0 ≤ A
  · calc ∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j * G (P + j))
        ≤ ∑' j : ℕ, ENNReal.ofReal (A * ((1 / 2 : ℝ) ^ j * (P + j) ^ k)) := by
          refine ENNReal.tsum_le_tsum fun j => ENNReal.ofReal_le_ofReal ?_
          have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          have := hG (P + j) (by linarith)
          calc (1 / 2 : ℝ) ^ j * G (P + j) ≤ (1 / 2 : ℝ) ^ j * (A * (P + j) ^ k) := by
                gcongr
            _ = A * ((1 / 2 : ℝ) ^ j * (P + j) ^ k) := by ring
      _ = ENNReal.ofReal (∑' j : ℕ, A * ((1 / 2 : ℝ) ^ j * (P + j) ^ k)) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun j => by
            have : (0 : ℝ) ≤ P := by linarith
            positivity) ((summable_half_mul_add_pow k hP).mul_left A)).symm
      _ ≤ ENNReal.ofReal (A * (2 ^ (k + 1) * k.factorial * P ^ k)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [tsum_mul_left]
          gcongr
          exact (tsum_half_mul_add_pow_le k hP).2
  · push Not at hA
    have h0 : ∀ j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j * G (P + j)) = 0 := by
      intro j
      apply ENNReal.ofReal_eq_zero.mpr
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hGj := hG (P + j) (by linarith)
      have hpow : 0 < (P + j) ^ k := pow_pos (by linarith) k
      have hneg : G (P + j) ≤ 0 := by nlinarith
      have hhalf : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
      nlinarith
    calc ∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j * G (P + j)) = ∑' _j : ℕ, (0 : ℝ≥0∞) :=
          tsum_congr h0
      _ = 0 := tsum_zero
      _ ≤ _ := zero_le

/-! ## Routine precision and the per-token bound -/

/-- Routine precision at a power-of-two horizon `R`: `p_R = ⌈log₂(64 V (R + 2)^3)⌉`.
Paper: proof of `lem:conf-replay` (conference.tex); `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
noncomputable def pR (V R : ℕ) : ℕ := ⌈Real.logb 2 (64 * V * ((R : ℝ) + 2) ^ 3)⌉₊

/-- `64 V (R + 2)^3 ≤ 2^{p_R}`. Auxiliary for the prefactor bound in the proof of `lem:conf-replay`
(conference.tex). -/
lemma le_two_pow_pR {V : ℕ} (R : ℕ) (hV : 1 ≤ V) :
    64 * (V : ℝ) * ((R : ℝ) + 2) ^ 3 ≤ 2 ^ pR V R := by
  have hx : (0 : ℝ) < 64 * V * ((R : ℝ) + 2) ^ 3 := by
    have : (1 : ℝ) ≤ V := by exact_mod_cast hV
    positivity
  calc 64 * (V : ℝ) * ((R : ℝ) + 2) ^ 3
      = (2 : ℝ) ^ (Real.logb 2 (64 * V * ((R : ℝ) + 2) ^ 3)) :=
        (Real.rpow_logb (by norm_num) (by norm_num) hx).symm
    _ ≤ (2 : ℝ) ^ ((pR V R : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    _ = 2 ^ pR V R := Real.rpow_natCast 2 _

/-- For `T ≤ R` the prefactor satisfies `8 V T 2^{-p_R} ≤ 1 / (8 (R + 2)^2)`, an explicit form of
`O((R + 2)^{-2})`.
Paper: proof of `lem:conf-replay` (conference.tex), "For T ≤ R, the prefactor is O((R+2)^{-2})";
`lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem prefactor_le {V : ℕ} (hV : 1 ≤ V) {T R : ℕ} (hTR : T ≤ R) :
    8 * (V : ℝ) * T / 2 ^ pR V R ≤ 1 / (8 * ((R : ℝ) + 2) ^ 2) := by
  have hV' : (1 : ℝ) ≤ V := by exact_mod_cast hV
  have hT : (T : ℝ) ≤ R := by exact_mod_cast hTR
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hpos : (0 : ℝ) < 64 * V * ((R : ℝ) + 2) ^ 3 := by positivity
  calc 8 * (V : ℝ) * T / 2 ^ pR V R ≤ 8 * (V : ℝ) * T / (64 * V * ((R : ℝ) + 2) ^ 3) :=
        div_le_div_of_nonneg_left (by positivity) hpos (le_two_pow_pR R hV)
    _ ≤ 1 / (8 * ((R : ℝ) + 2) ^ 2) := by
        rw [div_le_div_iff₀ hpos (by positivity)]
        have h2 : (0 : ℝ) < ((R : ℝ) + 2) ^ 2 := by positivity
        have hV0 : (0 : ℝ) < V := by linarith
        nlinarith [mul_pos hV0 h2]

/-- `log₂ 8 = 3`. Auxiliary arithmetic for the routine precision in the proof of `lem:conf-replay`
(conference.tex). -/
lemma logb_two_eight : Real.logb 2 8 = 3 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  norm_num

/-- `log₂ 64 = 6`. Auxiliary arithmetic for the routine precision in the proof of `lem:conf-replay`
(conference.tex). -/
lemma logb_two_sixtyfour : Real.logb 2 64 = 6 := by
  rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  norm_num

/-- `64 V (R + 2)^3 ≥ 1`. Auxiliary for the proof of `lem:conf-replay` (conference.tex). -/
lemma one_le_pR_arg {V : ℕ} (hV : 1 ≤ V) (R : ℕ) : 1 ≤ 64 * (V : ℝ) * ((R : ℝ) + 2) ^ 3 := by
  have hV' : (1 : ℝ) ≤ V := by exact_mod_cast hV
  have hR : (1 : ℝ) ≤ ((R : ℝ) + 2) ^ 3 :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg R : (0:ℝ) ≤ R)])
  nlinarith

/-- The routine precision is at least one bit. Auxiliary for the proof of `lem:conf-replay`
(conference.tex). -/
lemma one_le_pR {V : ℕ} (hV : 1 ≤ V) (R : ℕ) : 1 ≤ pR V R := by
  unfold pR
  apply Nat.one_le_iff_ne_zero.mpr
  apply Nat.pos_iff_ne_zero.mp
  apply Nat.ceil_pos.mpr
  have h := one_le_pR_arg hV R
  have : (64 : ℝ) ≤ 64 * (V : ℝ) * ((R : ℝ) + 2) ^ 3 := by
    have hV' : (1 : ℝ) ≤ V := by exact_mod_cast hV
    have hR : (1 : ℝ) ≤ ((R : ℝ) + 2) ^ 3 :=
      one_le_pow₀ (by linarith [(Nat.cast_nonneg R : (0:ℝ) ≤ R)])
    nlinarith
  calc (0 : ℝ) < Real.logb 2 64 := by rw [logb_two_sixtyfour]; norm_num
    _ ≤ _ := Real.logb_le_logb_of_le (by norm_num) (by norm_num) this

/-- `log₂(64 V (R + 2)^3) = 6 + log₂ V + 3 log₂(R + 2)`. Auxiliary for the proof of
`lem:conf-replay` (conference.tex). -/
lemma logb_pR_arg {V : ℕ} (hV : 1 ≤ V) (R : ℕ) :
    Real.logb 2 (64 * (V : ℝ) * ((R : ℝ) + 2) ^ 3)
      = 6 + Real.logb 2 V + 3 * Real.logb 2 ((R : ℝ) + 2) := by
  have hV' : (0 : ℝ) < V := by exact_mod_cast hV
  have hR : (0 : ℝ) < (R : ℝ) + 2 := by positivity
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by norm_num) hV'.ne',
    Real.logb_pow, logb_two_sixtyfour]
  push_cast
  ring

/-- `p_R < 7 + log₂ V + 3 log₂(R + 2)`, so the initial uniform cell costs `p_R = O(S)` random bits.
Paper: proof of `lem:conf-replay` (conference.tex), "The initial uniform cell costs p_R = O(S)
random bits". -/
theorem pR_lt {V : ℕ} (hV : 1 ≤ V) (R : ℕ) :
    (pR V R : ℝ) < 7 + Real.logb 2 V + 3 * Real.logb 2 ((R : ℝ) + 2) := by
  unfold pR
  have h0 : 0 ≤ Real.logb 2 (64 * (V : ℝ) * ((R : ℝ) + 2) ^ 3) :=
    Real.logb_nonneg (by norm_num) (one_le_pR_arg hV R)
  have := Nat.ceil_lt_add_one h0
  rw [logb_pR_arg hV R] at this ⊢
  linarith

/-- Doubling the horizon raises the routine precision by at most three bits: `p_{2R} ≤ p_R + 3`; in
particular the future accuracy `p_{4N}` exceeds the current accuracy `p_{2N}` by at most three bits.
Paper: proof of `lem:conf-replay` (conference.tex), "The future accuracy exceeds the current one by
only a constant number of bits"; `lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem pR_two_mul_le {V : ℕ} (hV : 1 ≤ V) (R : ℕ) : pR V (2 * R) ≤ pR V R + 3 := by
  unfold pR
  have hpos : (0 : ℝ) < 64 * (V : ℝ) * (((2 * R : ℕ) : ℝ) + 2) ^ 3 := by
    have hV' : (0 : ℝ) < V := by exact_mod_cast hV
    positivity
  have hx := one_le_pR_arg hV R
  have hle : 64 * (V : ℝ) * (((2 * R : ℕ) : ℝ) + 2) ^ 3
      ≤ 8 * (64 * (V : ℝ) * ((R : ℝ) + 2) ^ 3) := by
    have hV' : (0 : ℝ) ≤ V := Nat.cast_nonneg V
    have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    push_cast
    have h1 : (2 * (R : ℝ) + 2) ^ 3 ≤ 8 * ((R : ℝ) + 2) ^ 3 := by
      have : (2 * (R : ℝ) + 2) ≤ 2 * ((R : ℝ) + 2) := by linarith
      calc (2 * (R : ℝ) + 2) ^ 3 ≤ (2 * ((R : ℝ) + 2)) ^ 3 := by gcongr
        _ = 8 * ((R : ℝ) + 2) ^ 3 := by ring
    nlinarith
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos hle
  have h8 : Real.logb 2 (8 * (64 * (V : ℝ) * ((R : ℝ) + 2) ^ 3))
      = Real.logb 2 8 + Real.logb 2 (64 * (V : ℝ) * ((R : ℝ) + 2) ^ 3) :=
    Real.logb_mul (by norm_num) (by linarith)
  rw [h8, logb_two_eight] at hlog
  have h0 : 0 ≤ Real.logb 2 (64 * (V : ℝ) * ((R : ℝ) + 2) ^ 3) :=
    Real.logb_nonneg (by norm_num) hx
  calc ⌈Real.logb 2 (64 * (V : ℝ) * (((2 * R : ℕ) : ℝ) + 2) ^ 3)⌉₊
      ≤ ⌈Real.logb 2 (64 * (V : ℝ) * ((R : ℝ) + 2) ^ 3) + ((3 : ℕ) : ℝ)⌉₊ := by
        apply Nat.ceil_mono
        push_cast at hlog ⊢
        linarith
    _ = _ := Nat.ceil_add_natCast h0 3

/-- Expected temporary replay work at the routine precision `p_R` with `T ≤ R`, for `G u ≤ A u^k`
(`u ≥ 1`) and `L ≥ 0` standing for `log(T + 2)`: at most `A 2^{k+1} k! (p_R + L)^k / (8 (R + 2)^2)`.
Paper: proof of `lem:conf-replay` (conference.tex); `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
theorem expected_replayWork_le_pR (B : Boundaries V) (E : ∀ p, Enclosure B.F p) {T R : ℕ}
    (hTR : T ≤ R) {G : ℝ → ℝ} {A : ℝ} {k : ℕ} (hG : ∀ u, 1 ≤ u → G u ≤ A * u ^ k)
    {L : ℝ} (hL : 0 ≤ L) :
    ∫⁻ U, replayWork E (pR V R) T G L U ∂uniform
      ≤ ENNReal.ofReal (A * (2 ^ (k + 1) * k.factorial * ((pR V R : ℝ) + L) ^ k)
          / (8 * ((R : ℝ) + 2) ^ 2)) := by
  have hV := B.one_le
  have hP : 1 ≤ (pR V R : ℝ) + L := by
    have : (1 : ℝ) ≤ pR V R := by exact_mod_cast one_le_pR hV R
    linarith
  calc ∫⁻ U, replayWork E (pR V R) T G L U ∂uniform
      ≤ ENNReal.ofReal (8 * V * T / 2 ^ pR V R)
        * ∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j * G ((pR V R : ℝ) + (j : ℝ) + L)) :=
        expected_replayWork_le B E (pR V R) T G L
    _ ≤ ENNReal.ofReal (1 / (8 * ((R : ℝ) + 2) ^ 2))
        * ENNReal.ofReal (A * (2 ^ (k + 1) * k.factorial * ((pR V R : ℝ) + L) ^ k)) := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal (prefactor_le hV hTR)) ?_
        have h := tsum_half_mul_G_le hG hP
        exact le_of_eq_of_le (tsum_congr fun j => by rw [add_right_comm]) h
    _ = ENNReal.ofReal (A * (2 ^ (k + 1) * k.factorial * ((pR V R : ℝ) + L) ^ k)
          / (8 * ((R : ℝ) + 2) ^ 2)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- Random bits revealed after the initial cell: one per reached refinement.
Paper: proof of `lem:conf-replay` (conference.tex), "the same tail charges all additional random
bits". -/
noncomputable def extraBits {F : Fin (V + 1) → ℝ} (E : ∀ p, Enclosure F p) (p0 : ℕ) (U : ℝ) :
    ℝ≥0∞ :=
  ∑' j, (ReachSet E p0 j).indicator (fun _ => 1) U

/-- Expected random bits per token: at most `p0 + 8 V 2^{-p0}`.
Paper: proof of `lem:conf-replay` (conference.tex), "The initial uniform cell costs p_R = O(S)
random bits; the same tail charges all additional random bits"; `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
theorem expected_bits_le (B : Boundaries V) (E : ∀ p, Enclosure B.F p) (p0 : ℕ) :
    (p0 : ℝ≥0∞) + ∫⁻ U, extraBits E p0 U ∂uniform ≤ ENNReal.ofReal (p0 + 8 * V / 2 ^ p0) := by
  have h := lintegral_reach_le B E p0 (fun _ => 1)
  have hsum : ∑' j : ℕ, (1 : ℝ≥0∞) * ENNReal.ofReal (4 * V / 2 ^ (p0 + j))
      = ENNReal.ofReal (8 * V / 2 ^ p0) := by
    have hs : Summable (fun j : ℕ => 4 * (V : ℝ) / 2 ^ p0 * (1 / 2 : ℝ) ^ j) :=
      (summable_geometric_two).mul_left _
    calc ∑' j : ℕ, (1 : ℝ≥0∞) * ENNReal.ofReal (4 * V / 2 ^ (p0 + j))
        = ∑' j : ℕ, ENNReal.ofReal (4 * (V : ℝ) / 2 ^ p0 * (1 / 2 : ℝ) ^ j) := by
          refine tsum_congr fun j => ?_
          rw [one_mul]
          congr 1
          rw [pow_add, one_div_pow]
          field_simp
      _ = ENNReal.ofReal (∑' j : ℕ, 4 * (V : ℝ) / 2 ^ p0 * (1 / 2 : ℝ) ^ j) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hs).symm
      _ = ENNReal.ofReal (8 * V / 2 ^ p0) := by
          rw [tsum_mul_left, tsum_geometric_two]
          congr 1
          ring
  calc (p0 : ℝ≥0∞) + ∫⁻ U, extraBits E p0 U ∂uniform
      ≤ (p0 : ℝ≥0∞) + ENNReal.ofReal (8 * V / 2 ^ p0) := by
        gcongr
        exact h.trans_eq hsum
    _ = ENNReal.ofReal (p0 + 8 * V / 2 ^ p0) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_natCast]

open Classical in
/-- The charges count exactly the refinements that `output` performs: if the first deciding
index is `j*` (the comparison at precision `p0 + j*` decides), then `U` lies in the reach event
`ReachSet E p0 j` if and only if `j < j*`.
Paper: proof of `lem:conf-replay` (conference.tex), "If undecided, replay the actual history at
accuracy p_R+1, reveal the next uniform bit, and try again; continue similarly". -/
theorem mem_reachSet_iff {F : Fin (V + 1) → ℝ} (E : ∀ p, Enclosure F p) (p0 : ℕ) {U : ℝ}
    (hex : ∃ j i, DecidedAt E (p0 + j) U i) (j : ℕ) :
    U ∈ ReachSet E p0 j ↔ j < Nat.find hex := by
  constructor
  · intro hU
    by_contra hle
    push Not at hle
    obtain ⟨i, hi⟩ := Nat.find_spec hex
    exact hU (Nat.find hex) hle i hi
  · intro hj j' hj' i hi
    exact Nat.find_min hex (lt_of_le_of_lt hj' hj) ⟨i, hi⟩

open Classical in
/-- The first deciding index is the precision at which `output` decides: `output` returns a
token decided at precision `p0 + j*`.
Paper: proof of `lem:conf-replay` (conference.tex). -/
theorem output_decidedAt_find {F : Fin (V + 1) → ℝ} (E : ∀ p, Enclosure F p) (p0 : ℕ) {U : ℝ}
    (hex : ∃ j i, DecidedAt E (p0 + j) U i) :
    ∃ i, output E p0 U = some i ∧ DecidedAt E (p0 + Nat.find hex) U i := by
  unfold output
  split_ifs
  exact ⟨_, rfl, Classical.choose_spec (Nat.find_spec hex)⟩

/-- If no precision decides, every reach event contains `U` (this happens only on the null set
of `uniform_output_none`).
Paper: proof of `lem:conf-replay` (conference.tex). -/
theorem mem_reachSet_of_not_exists {F : Fin (V + 1) → ℝ} (E : ∀ p, Enclosure F p) (p0 : ℕ)
    {U : ℝ} (hne : ¬ ∃ j i, DecidedAt E (p0 + j) U i) (j : ℕ) : U ∈ ReachSet E p0 j :=
  fun j' _ i hi => hne ⟨j', i, hi⟩

open Classical in
/-- On a realized `U` with first deciding index `j*`, the replay charge is the finite sum of the
costs of the replays at accuracies `p0 + 1, ..., p0 + j*`, exactly those performed by `output`.
Paper: proof of `lem:conf-replay` (conference.tex). -/
theorem replayWork_eq_sum {F : Fin (V + 1) → ℝ} (E : ∀ p, Enclosure F p) (p0 T : ℕ)
    (G : ℝ → ℝ) (L : ℝ) {U : ℝ} (hex : ∃ j i, DecidedAt E (p0 + j) U i) :
    replayWork E p0 T G L U = ∑ j ∈ Finset.range (Nat.find hex),
      ENNReal.ofReal (T * G ((p0 : ℝ) + ((j + 1 : ℕ) : ℝ) + L)) := by
  unfold replayWork
  rw [tsum_eq_sum (s := Finset.range (Nat.find hex)) fun j hj => ?_]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    exact indicator_of_mem ((mem_reachSet_iff E p0 hex j).mpr hj) _
  · rw [Finset.mem_range] at hj
    exact indicator_of_notMem (fun h => hj ((mem_reachSet_iff E p0 hex j).mp h)) _

open Classical in
/-- On a realized `U` with first deciding index `j*`, the additional random bits number exactly
`j*`, one per revealed bit after the initial cell.
Paper: proof of `lem:conf-replay` (conference.tex), "reveal the next uniform bit". -/
theorem extraBits_eq {F : Fin (V + 1) → ℝ} (E : ∀ p, Enclosure F p) (p0 : ℕ) {U : ℝ}
    (hex : ∃ j i, DecidedAt E (p0 + j) U i) :
    extraBits E p0 U = (Nat.find hex : ℝ≥0∞) := by
  unfold extraBits
  rw [tsum_eq_sum (s := Finset.range (Nat.find hex)) fun j hj => ?_]
  · rw [Finset.sum_congr rfl fun j hj => indicator_of_mem
      ((mem_reachSet_iff E p0 hex j).mpr (Finset.mem_range.mp hj)) _]
    simp
  · rw [Finset.mem_range] at hj
    exact indicator_of_notMem (fun h => hj ((mem_reachSet_iff E p0 hex j).mp h)) _

/-- `log₂(R + 2) ≤ 3 + log₂(T + 2)` when `R ≤ 8 T`. Auxiliary for the bound `O_k(AS^k + S)` in
`lem:conf-replay` (conference.tex). -/
lemma logb_horizon_le {R T : ℕ} (hR : R ≤ 8 * T) :
    Real.logb 2 ((R : ℝ) + 2) ≤ 3 + Real.logb 2 ((T : ℝ) + 2) := by
  have hR' : (R : ℝ) ≤ 8 * T := by exact_mod_cast hR
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  calc Real.logb 2 ((R : ℝ) + 2) ≤ Real.logb 2 (8 * ((T : ℝ) + 2)) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
    _ = 3 + Real.logb 2 ((T : ℝ) + 2) := by
        rw [Real.logb_mul (by norm_num) (by positivity), logb_two_eight]

/-- `p_R + log₂(T + 2) ≤ 16 S` with `S = 1 + log₂(V + 2) + log₂(T + 2)` when `R ≤ 8 T`. Auxiliary
for the bound `O_k(AS^k + S)` in `lem:conf-replay` (conference.tex). -/
lemma pR_add_log_le {V : ℕ} (hV : 1 ≤ V) {R T : ℕ} (hR : R ≤ 8 * T) :
    (pR V R : ℝ) + Real.logb 2 ((T : ℝ) + 2)
      ≤ 16 * (1 + Real.logb 2 ((V : ℝ) + 2) + Real.logb 2 ((T : ℝ) + 2)) := by
  have h1 := pR_lt hV R
  have h2 := logb_horizon_le hR
  have hV0 : (0 : ℝ) < V := by exact_mod_cast hV
  have h3 : Real.logb 2 (V : ℝ) ≤ Real.logb 2 ((V : ℝ) + 2) :=
    Real.logb_le_logb_of_le (by norm_num) hV0 (by linarith)
  have h4 : 0 ≤ Real.logb 2 ((V : ℝ) + 2) := Real.logb_nonneg (by norm_num) (by linarith)
  have h5 : 0 ≤ Real.logb 2 ((T : ℝ) + 2) :=
    Real.logb_nonneg (by norm_num) (by linarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)])
  linarith

/-- Per-token expected work `O_k(A S^k + S)` with explicit constants, where
`S = 1 + log₂(V + 2) + log₂(T + 2)`. The charges are: one routine evaluation at the current
precision `p_R` and two at the future precision `p_{R'}` (each `G(p + log₂(T + 2))`), the temporary
replays, the initial cell and the additional random bits. The horizons satisfy `T ≤ R ≤ 8 T` and
`R' ≤ 8 T`, as the background schedule guarantees (`ReplaySchedule.lean`). The hypothesis `0 ≤ A`
holds because `G` has nonnegative coefficients, so `0 ≤ G 1 ≤ A`.
Paper: statement of `lem:conf-replay` (conference.tex), "Its expected total bit work is
O_k(AS^k+S)"; proof of `thm:conf-decoder` (conference.tex) and of `thm:momentdecoder`
(attention_moment_decoder.tex), the application of the replay lemma. -/
theorem expected_token_work_le (B : Boundaries V) (E : ∀ p, Enclosure B.F p) {T R R' : ℕ}
    (hTR : T ≤ R) (hR : R ≤ 8 * T) (hR' : R' ≤ 8 * T) {G : ℝ → ℝ} {A : ℝ} {k : ℕ}
    (hA : 0 ≤ A) (hG : ∀ u, 1 ≤ u → G u ≤ A * u ^ k) :
    ENNReal.ofReal (G ((pR V R : ℝ) + Real.logb 2 ((T : ℝ) + 2)))
      + 2 * ENNReal.ofReal (G ((pR V R' : ℝ) + Real.logb 2 ((T : ℝ) + 2)))
      + ∫⁻ U, replayWork E (pR V R) T G (Real.logb 2 ((T : ℝ) + 2)) U ∂uniform
      + ((pR V R : ℝ≥0∞) + ∫⁻ U, extraBits E (pR V R) U ∂uniform)
      ≤ ENNReal.ofReal ((3 * 16 ^ k + 2 ^ k * k.factorial * 16 ^ k) * A
          * (1 + Real.logb 2 ((V : ℝ) + 2) + Real.logb 2 ((T : ℝ) + 2)) ^ k
          + 17 * (1 + Real.logb 2 ((V : ℝ) + 2) + Real.logb 2 ((T : ℝ) + 2))) := by
  have hV := B.one_le
  set L := Real.logb 2 ((T : ℝ) + 2) with hLdef
  set S := 1 + Real.logb 2 ((V : ℝ) + 2) + Real.logb 2 ((T : ℝ) + 2) with hSdef
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num)
    (by linarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)])
  have hV0 : (1 : ℝ) ≤ V := by exact_mod_cast hV
  have hS1 : 1 ≤ S := by
    have : 0 ≤ Real.logb 2 ((V : ℝ) + 2) := Real.logb_nonneg (by norm_num) (by linarith)
    linarith
  have hpR1 : (1 : ℝ) ≤ pR V R := by exact_mod_cast one_le_pR hV R
  have hpR1' : (1 : ℝ) ≤ pR V R' := by exact_mod_cast one_le_pR hV R'
  have hP := pR_add_log_le hV hR
  have hP' := pR_add_log_le hV hR'
  -- a single routine evaluation
  have hroutine : ∀ Q : ℕ, (1 : ℝ) ≤ Q → (Q : ℝ) + L ≤ 16 * S →
      ENNReal.ofReal (G ((Q : ℝ) + L)) ≤ ENNReal.ofReal (16 ^ k * A * S ^ k) := by
    intro Q hQ hQS
    apply ENNReal.ofReal_le_ofReal
    calc G ((Q : ℝ) + L) ≤ A * ((Q : ℝ) + L) ^ k := hG _ (by linarith)
      _ ≤ A * (16 * S) ^ k := by gcongr
      _ = 16 ^ k * A * S ^ k := by rw [mul_pow]; ring
  have hr1 := hroutine (pR V R) hpR1 hP
  have hr2 := hroutine (pR V R') hpR1' hP'
  -- temporary replays
  have hrep : ∫⁻ U, replayWork E (pR V R) T G L U ∂uniform
      ≤ ENNReal.ofReal (2 ^ k * k.factorial * 16 ^ k * A * S ^ k) := by
    refine (expected_replayWork_le_pR B E hTR hG hL).trans (ENNReal.ofReal_le_ofReal ?_)
    have hR2 : (32 : ℝ) ≤ 8 * ((R : ℝ) + 2) ^ 2 := by
      have : (2 : ℝ) ≤ (R : ℝ) + 2 := by linarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)]
      nlinarith
    have hnum : 0 ≤ A * (2 ^ (k + 1) * k.factorial * ((pR V R : ℝ) + L) ^ k) := by
      have : (0 : ℝ) ≤ (pR V R : ℝ) + L := by linarith
      positivity
    calc A * (2 ^ (k + 1) * k.factorial * ((pR V R : ℝ) + L) ^ k) / (8 * ((R : ℝ) + 2) ^ 2)
        ≤ A * (2 ^ (k + 1) * k.factorial * ((pR V R : ℝ) + L) ^ k) / 32 :=
          div_le_div_of_nonneg_left hnum (by norm_num) hR2
      _ ≤ A * (2 ^ (k + 1) * k.factorial * (16 * S) ^ k) / 32 := by
          gcongr
      _ ≤ 2 ^ k * k.factorial * 16 ^ k * A * S ^ k := by
          rw [pow_succ, mul_pow]
          have : (0 : ℝ) ≤ 2 ^ k * k.factorial * 16 ^ k * A * S ^ k := by positivity
          nlinarith
  -- random bits
  have hbits : (pR V R : ℝ≥0∞) + ∫⁻ U, extraBits E (pR V R) U ∂uniform
      ≤ ENNReal.ofReal (17 * S) := by
    refine (expected_bits_le B E (pR V R)).trans (ENNReal.ofReal_le_ofReal ?_)
    have h8 : 8 * (V : ℝ) / 2 ^ pR V R ≤ 1 := by
      have h64 := le_two_pow_pR R hV
      have hpos : (0 : ℝ) < 2 ^ pR V R := by positivity
      rw [div_le_one hpos]
      have : (1 : ℝ) ≤ ((R : ℝ) + 2) ^ 3 :=
        one_le_pow₀ (by linarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)])
      nlinarith
    linarith
  calc ENNReal.ofReal (G ((pR V R : ℝ) + L)) + 2 * ENNReal.ofReal (G ((pR V R' : ℝ) + L))
        + ∫⁻ U, replayWork E (pR V R) T G L U ∂uniform
        + ((pR V R : ℝ≥0∞) + ∫⁻ U, extraBits E (pR V R) U ∂uniform)
      ≤ ENNReal.ofReal (16 ^ k * A * S ^ k) + 2 * ENNReal.ofReal (16 ^ k * A * S ^ k)
        + ENNReal.ofReal (2 ^ k * k.factorial * 16 ^ k * A * S ^ k)
        + ENNReal.ofReal (17 * S) := by
        gcongr
    _ = ENNReal.ofReal ((3 * 16 ^ k + 2 ^ k * k.factorial * 16 ^ k) * A * S ^ k + 17 * S) := by
        have h0 : (0 : ℝ) ≤ 16 ^ k * A * S ^ k := by positivity
        have h1 : (0 : ℝ) ≤ 2 ^ k * k.factorial * 16 ^ k * A * S ^ k := by positivity
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add h0 (by positivity), ← ENNReal.ofReal_add (by positivity) h1,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- Per-token bound in terms of the schedule parameter `N`: the current routine horizon is
`R = 2N` and the future horizon is `R' = 4N`. The hypotheses `T ≤ 2N` and `N ≤ 2T` are the
schedule invariants `len_le_horizon` and `Inv.N_le_two_len` of `ReplaySchedule.lean`; the two
modules are composed through these matching hypotheses.
Paper: statement of `lem:conf-replay` (conference.tex), "Its expected total bit work is
O_k(AS^k+S)", with the precisions `p_{2N}` and `p_{4N}` of the background schedule in its proof;
`lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem expected_token_work_le_schedule (B : Boundaries V) (E : ∀ p, Enclosure B.F p)
    {T N : ℕ} (hTN : T ≤ 2 * N) (hNT : N ≤ 2 * T) {G : ℝ → ℝ} {A : ℝ} {k : ℕ}
    (hA : 0 ≤ A) (hG : ∀ u, 1 ≤ u → G u ≤ A * u ^ k) :
    ENNReal.ofReal (G ((pR V (2 * N) : ℝ) + Real.logb 2 ((T : ℝ) + 2)))
      + 2 * ENNReal.ofReal (G ((pR V (4 * N) : ℝ) + Real.logb 2 ((T : ℝ) + 2)))
      + ∫⁻ U, replayWork E (pR V (2 * N)) T G (Real.logb 2 ((T : ℝ) + 2)) U ∂uniform
      + ((pR V (2 * N) : ℝ≥0∞) + ∫⁻ U, extraBits E (pR V (2 * N)) U ∂uniform)
      ≤ ENNReal.ofReal ((3 * 16 ^ k + 2 ^ k * k.factorial * 16 ^ k) * A
          * (1 + Real.logb 2 ((V : ℝ) + 2) + Real.logb 2 ((T : ℝ) + 2)) ^ k
          + 17 * (1 + Real.logb 2 ((V : ℝ) + 2) + Real.logb 2 ((T : ℝ) + 2))) :=
  expected_token_work_le B E hTN (by omega) (by omega) hA hG

/-- Prefill cost: building the routine evaluator at precision `p_{2N}` on the `T0` prompt
tokens costs at most `T0 · G(p_{2N} + log₂(T0 + 2)) ≤ T0 · 16^k A S0^k`, where
`S0 = 1 + log₂(V + 2) + log₂(T0 + 2)`. The hypothesis `N ≤ 2 T0` holds for the least power of
two at least `T0` (`firstHorizon_lt` in `ReplaySchedule.lean`); `0 ≤ A` holds because `G` has
nonnegative coefficients.
Paper: `thm:conf-decoder` (conference.tex), the prefill cost `T_0 F_r(n,D,V,b,s,β,log(T_0+2))`;
proof of `lem:conf-replay` (conference.tex), "During prefill build the routine evaluator at
p_{2N}". -/
theorem prefill_work_le {T0 N : ℕ} (hN : N ≤ 2 * T0) (hV : 1 ≤ V) {G : ℝ → ℝ} {A : ℝ}
    {k : ℕ} (hA : 0 ≤ A) (hG : ∀ u, 1 ≤ u → G u ≤ A * u ^ k) :
    (T0 : ℝ) * G ((pR V (2 * N) : ℝ) + Real.logb 2 ((T0 : ℝ) + 2))
      ≤ T0 * (16 ^ k * A * (1 + Real.logb 2 ((V : ℝ) + 2) + Real.logb 2 ((T0 : ℝ) + 2)) ^ k) := by
  have hP := pR_add_log_le hV (R := 2 * N) (T := T0) (by omega)
  have hpR : (1 : ℝ) ≤ pR V (2 * N) := by exact_mod_cast one_le_pR hV (2 * N)
  have hL : 0 ≤ Real.logb 2 ((T0 : ℝ) + 2) := Real.logb_nonneg (by norm_num)
    (by linarith [(Nat.cast_nonneg T0 : (0 : ℝ) ≤ T0)])
  have hG' := hG _ (by linarith : (1 : ℝ) ≤ (pR V (2 * N) : ℝ) + Real.logb 2 ((T0 : ℝ) + 2))
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg T0)
  calc G ((pR V (2 * N) : ℝ) + Real.logb 2 ((T0 : ℝ) + 2))
      ≤ A * ((pR V (2 * N) : ℝ) + Real.logb 2 ((T0 : ℝ) + 2)) ^ k := hG'
    _ ≤ A * (16 * (1 + Real.logb 2 ((V : ℝ) + 2) + Real.logb 2 ((T0 : ℝ) + 2))) ^ k := by
        gcongr
    _ = 16 ^ k * A * (1 + Real.logb 2 ((V : ℝ) + 2) + Real.logb 2 ((T0 : ℝ) + 2)) ^ k := by
        rw [mul_pow]
        ring

/-! ## The autoregressive joint law -/

section Joint

variable {α : Type*}

/-- Sequential sampling of `n` tokens with a fresh input `ω t` at step `t`: the step sampler is
applied to the realized history, and the produced token is appended. The result is `none` if some
step does not stop.
Paper: proof of `lem:conf-replay` (conference.tex), "Fresh uniform bits give that conditional law,
and induction gives the whole autoregressive joint law". -/
def run (step : List (Fin V) → α → Option (Fin V)) :
    (n : ℕ) → List (Fin V) → (Fin n → α) → Option (List (Fin V))
  | 0, _, _ => some []
  | n + 1, h, ω =>
    match step h (ω 0) with
    | none => none
    | some x => (run step n (h ++ [x]) (Fin.tail ω)).map (x :: ·)

/-- Autoregressive probability of the continuation `xs` after the history `h`: the product of the
conditional probabilities `q (h ++ x₁ ... x_{t-1}) x_t`.
Paper: proof of `lem:conf-replay` (conference.tex), "the whole autoregressive joint law". -/
noncomputable def arProb (q : List (Fin V) → Fin V → ℝ≥0∞) : List (Fin V) → List (Fin V) → ℝ≥0∞
  | _, [] => 1
  | h, x :: xs => q h x * arProb q (h ++ [x]) xs

/-- Unfolding one step of sequential sampling. Auxiliary for the joint-law claim in the proof of
`lem:conf-replay` (conference.tex). -/
lemma run_succ_eq_some (step : List (Fin V) → α → Option (Fin V)) (n : ℕ) (h : List (Fin V))
    (ω : Fin (n + 1) → α) (x : Fin V) (xs : List (Fin V)) :
    run step (n + 1) h ω = some (x :: xs) ↔
      step h (ω 0) = some x ∧ run step n (h ++ [x]) (Fin.tail ω) = some xs := by
  simp only [run]
  rcases hs : step h (ω 0) with _ | y
  · simp
  · simp only [Option.some.injEq]
    constructor
    · intro hm
      obtain ⟨ys, hys, hyx⟩ := Option.map_eq_some_iff.mp hm
      simp only [List.cons.injEq] at hyx
      obtain ⟨rfl, rfl⟩ := hyx
      exact ⟨rfl, hys⟩
    · rintro ⟨rfl, hr⟩
      rw [hr]
      rfl

/-- Splitting off the first fresh input. Auxiliary for the joint-law claim in the proof of
`lem:conf-replay` (conference.tex). -/
lemma piFinSuccAbove_zero_apply [MeasurableSpace α] {n : ℕ} (ω : Fin (n + 1) → α) :
    MeasurableEquiv.piFinSuccAbove (fun _ => α) 0 ω = (ω 0, Fin.tail ω) := by
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]

/-- Induction over steps: if every step, given the realized history `h`, returns `x` with
probability `q h x` under a fresh input, then `n` steps with independent fresh inputs return the
continuation `xs` with the autoregressive probability `arProb q h xs`.
Paper: proof of `lem:conf-replay` (conference.tex), "Fresh uniform bits give that conditional law,
and induction gives the whole autoregressive joint law"; `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
theorem run_law [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (step : List (Fin V) → α → Option (Fin V)) (q : List (Fin V) → Fin V → ℝ≥0∞)
    (hstep : ∀ h x, μ {u | step h u = some x} = q h x) :
    ∀ (n : ℕ) (h xs : List (Fin V)), xs.length = n →
      Measure.pi (fun _ : Fin n => μ) {ω | run step n h ω = some xs} = arProb q h xs := by
  intro n
  induction n with
  | zero =>
    intro h xs hxs
    rw [List.length_eq_zero_iff] at hxs
    subst hxs
    simp [run, arProb]
  | succ n ih =>
    intro h xs hxs
    obtain ⟨x, xs, rfl⟩ : ∃ x xs', xs = x :: xs' := by
      cases xs with
      | nil => simp at hxs
      | cons x xs' => exact ⟨x, xs', rfl⟩
    simp only [List.length_cons, add_left_inj] at hxs
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
    have hset : {ω : Fin (n + 1) → α | run step (n + 1) h ω = some (x :: xs)} =
        MeasurableEquiv.piFinSuccAbove (fun _ => α) 0 ⁻¹'
          ({u | step h u = some x} ×ˢ {w | run step n (h ++ [x]) w = some xs}) := by
      ext ω
      simp only [mem_ofPred_eq, mem_preimage, piFinSuccAbove_zero_apply, mem_prod]
      exact run_succ_eq_some step n h ω x xs
    rw [hset, hmp.measure_preimage_equiv, Measure.prod_prod, hstep]
    rw [ih (h ++ [x]) xs hxs]
    rfl

/-- Unfolding one step of sequential sampling for the nonstopping event. Auxiliary for the proof of
`lem:conf-replay` (conference.tex). -/
lemma run_succ_eq_none (step : List (Fin V) → α → Option (Fin V)) (n : ℕ) (h : List (Fin V))
    (ω : Fin (n + 1) → α) :
    run step (n + 1) h ω = none ↔
      step h (ω 0) = none ∨
        ∃ x, step h (ω 0) = some x ∧ run step n (h ++ [x]) (Fin.tail ω) = none := by
  simp only [run]
  rcases hs : step h (ω 0) with _ | y
  · simp
  · simp

/-- If every step stops almost surely, then `n` sequential steps stop almost surely.
Paper: proof of `lem:conf-replay` (conference.tex); `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
theorem run_none [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (step : List (Fin V) → α → Option (Fin V)) (hnone : ∀ h, μ {u | step h u = none} = 0) :
    ∀ (n : ℕ) (h : List (Fin V)),
      Measure.pi (fun _ : Fin n => μ) {ω | run step n h ω = none} = 0 := by
  intro n
  induction n with
  | zero => intro h; simp [run]
  | succ n ih =>
    intro h
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
    have hset : {ω : Fin (n + 1) → α | run step (n + 1) h ω = none} =
        MeasurableEquiv.piFinSuccAbove (fun _ => α) 0 ⁻¹'
          ({u | step h u = none} ×ˢ univ ∪
            ⋃ x, {u | step h u = some x} ×ˢ {w | run step n (h ++ [x]) w = none}) := by
      ext ω
      simp only [mem_ofPred_eq, mem_preimage, piFinSuccAbove_zero_apply, mem_union, mem_prod,
        mem_univ, and_true, mem_iUnion]
      exact run_succ_eq_none step n h ω
    rw [hset, hmp.measure_preimage_equiv]
    refine measure_union_null ?_ (measure_iUnion_null fun x => ?_)
    · rw [Measure.prod_prod, hnone, zero_mul]
    · rw [Measure.prod_prod, ih, mul_zero]

/-- The autoregressive probability is the product of the conditionals,
`∏_t q (h ++ xs.take t) xs_t`.
Paper: proof of `lem:conf-replay` (conference.tex), "the whole autoregressive joint law". -/
theorem arProb_eq_prod (q : List (Fin V) → Fin V → ℝ≥0∞) :
    ∀ (h xs : List (Fin V)),
      arProb q h xs = ∏ t : Fin xs.length, q (h ++ xs.take t) (xs.get t) := by
  intro h xs
  induction xs generalizing h with
  | nil => simp [arProb]
  | cons x xs ih =>
    rw [arProb, ih]
    show _ = ∏ t : Fin (xs.length + 1), q (h ++ (x :: xs).take t) ((x :: xs).get t)
    rw [Fin.prod_univ_succ]
    simp

end Joint

/-- Exact autoregressive joint law of the replay sampler. The assumption is that the enclosures
`E h p` are a fixed (deterministic) function of the realized history `h` and the precision `p`,
and that each encloses the exact boundaries `B h` of the true next-token law after `h`. Then `n`
fresh uniforms produce the continuation `xs` with probability `∏_t (F_{x_t} - F_{x_t - 1})`,
taken at the realized prefixes.
Paper: proof of `lem:conf-replay` (conference.tex), last paragraph; `lem:replayexactsampling`
(attention_moment_decoder.tex), last paragraph; `thm:conf-decoder` (conference.tex), "The
conditional law is the original model's law for every realized token history". -/
theorem replay_joint_law (B : List (Fin V) → Boundaries V)
    (E : ∀ h p, Enclosure (B h).F p) (p0 : List (Fin V) → ℕ) (n : ℕ) (h0 xs : List (Fin V))
    (hxs : xs.length = n) :
    Measure.pi (fun _ : Fin n => uniform)
        {ω | run (fun h U => output (E h) (p0 h) U) n h0 ω = some xs}
      = ∏ t : Fin xs.length, ENNReal.ofReal
          ((B (h0 ++ xs.take t)).F (xs.get t).succ
            - (B (h0 ++ xs.take t)).F (xs.get t).castSucc) := by
  rw [run_law uniform _ (fun h x => ENNReal.ofReal ((B h).F x.succ - (B h).F x.castSucc))
    (fun h x => uniform_output_eq_some (B h) (E h) (p0 h) x) n h0 xs hxs, arProb_eq_prod]

/-- The `n`-step replay sampler stops almost surely.
Paper: proof of `lem:conf-replay` (conference.tex); `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
theorem replay_joint_law_none (B : List (Fin V) → Boundaries V)
    (E : ∀ h p, Enclosure (B h).F p) (p0 : List (Fin V) → ℕ) (n : ℕ) (h0 : List (Fin V)) :
    Measure.pi (fun _ : Fin n => uniform)
        {ω | run (fun h U => output (E h) (p0 h) U) n h0 ω = none} = 0 :=
  run_none uniform _ (fun h => uniform_output_none (B h) (E h) (p0 h)) n h0

/-- Exact autoregressive joint law in terms of the model's next-token probabilities `prob h`: the
replay sampler produces `xs` with probability `∏_t prob (h ++ xs.take t) xs_t`.
Paper: proof of `lem:conf-replay` (conference.tex), last paragraph; `thm:conf-decoder`
(conference.tex), "The conditional law is the original model's law for every realized token
history"; `thm:momentdecoder` (attention_moment_decoder.tex). -/
theorem replay_joint_law_prob (prob : List (Fin V) → Fin V → ℝ)
    (hnn : ∀ h i, 0 ≤ prob h i) (hsum : ∀ h, ∑ i, prob h i = 1)
    (E : ∀ h p, Enclosure (Boundaries.ofProb (prob h) (hnn h) (hsum h)).F p)
    (p0 : List (Fin V) → ℕ) (n : ℕ) (h0 xs : List (Fin V)) (hxs : xs.length = n) :
    Measure.pi (fun _ : Fin n => uniform)
        {ω | run (fun h U => output (E h) (p0 h) U) n h0 ω = some xs}
      = ∏ t : Fin xs.length, ENNReal.ofReal (prob (h0 ++ xs.take t) (xs.get t)) := by
  rw [replay_joint_law (fun h => Boundaries.ofProb (prob h) (hnn h) (hsum h)) E p0 n h0 xs hxs]
  refine Finset.prod_congr rfl fun t _ => ?_
  exact congrArg ENNReal.ofReal (cumProb_succ_sub _ _)

end ExactSampling.Replay
