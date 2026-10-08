import ExactSampling.Conference.Replay
import ExactSampling.Conference.ReplaySchedule
import ExactSampling.Conference.FixedModel
import ExactSampling.Conference.Stability
import ExactSampling.Links.ChartBasis

/-!
# The fixed-model corollary for the replay sampler, and the bounded chart in the stability proof

Paper: `conference.tex`, Corollary `cor:conf-fixed-model` (end of Section `sec:conf-replay`),
Lemma `lem:conf-replay`, the proof of `thm:conf-decoder`, and the chart step of the proof of
`lem:conf-stability`. Full version (`attention_moment_decoder.tex`): `cor:fixedmodelcontext`,
`lem:replayexactsampling`, `thm:momentdecoder` and `lem:prefixstability`.

## The replay stand-in of the fixed-model corollary

`ExactSampling.FixedModel.fixedModel_expected_isBigO` takes `lem:conf-replay` as its
hypothesis `hreplay`. Here the expected cost is the actual expected work of the replay sampler
of `ExactSampling.Replay`, with every deterministic evaluation charged the fixed-model cost
`eq:conf-explicit` (`FixedModel.fixedCost`): one routine evaluation at the current precision
`p_{2N}`, two at the future precision `p_{4N}`, a replay of the length-`T` history at each
reached accuracy `p_{2N} + j + 1` (charged `T` times the cost at that accuracy), the initial
uniform cell of `p_{2N}` bits, and the additional random bits. The comparison of the uniform
cell with the `V` cumulative intervals, which `lem:conf-replay` includes in `G` ("a scan costs
`O(V(p+1))` bits"), is charged separately: `V(p+1)` at the routine precision and at every
reached refinement (`compareWork`, `expected_compareWork_le`). The total is `tokenWork`. For
each length `T` the expected cost `worstWork` is the largest of these expectations over all
histories of length `T`, an extended real; `expectedWork` is its real value.
`replay_hypothesis` bounds `worstWork` by `C_k (A S^k + S)` (so it is finite) and proves the
hypothesis `hreplay` for `expectedWork` from `Replay.expected_token_work_le_schedule`. Hence
`fixedModel_replay_isBigO` states, for the replay sampler itself and with no remaining stand-in
for `lem:conf-replay`, that the worst-case expected work is finite at every length and is
`O(log^(2r+12)(T+2))`. `fixedModel_schedule_isBigO` instantiates the horizon with the background
schedule of `ExactSampling.ReplaySchedule` (`step^[T - T0] (init T0)` at length `T ≥ T0`).

The two modules measure logarithms differently: `FixedModel` uses `log(T+2)` with the natural
logarithm, `Replay` uses `log₂(T+2)`. The bridge uses `ln x ≤ log₂ x ≤ 2 ln x` for `x ≥ 1`.

## The chart stand-in of the stability proof

`ExactSampling.Stability.chart_coeff_l1` assumes chart coefficients with `|A_{ij}| ≤ 2`, the
conclusion of `lem:conf-chart`. `key_chart_attention` builds the chart from a column basis of
the key matrix `W_K` (`ExactSampling.Links.ChartBasis`, using `Chart.exists_bounded_chart`
and `Chart.chart_repr`) and then applies `chart_coeff_l1`, `chart_coord_le_one` and
`attn_chart_eq` to the keys `k = W_K x + b_K` themselves.

## Still not formalized

Everything listed as not formalized in `ExactSampling.Replay`, `ExactSampling.FixedModel`
and `ExactSampling.Stability` remains so: in particular the bit-complexity model (that the
charges are the bit costs of the evaluator), the operation count that produces
`eq:conf-explicit`, and the construction of the evaluator. The expected work is the expectation
over the fresh uniform of one step for a fixed history, as in `Replay`.
-/

namespace ExactSampling.Links.ConferenceDecoder

open MeasureTheory Filter Asymptotics Matrix Module
open scoped ENNReal

/-! ## Natural and binary logarithms -/

/-- `ln(T+2) ≤ log₂(T+2)`. Auxiliary for `cor:conf-fixed-model` (conference.tex), comparing the
logarithms of `lem:conf-replay` in the two modules. -/
theorem lg_le_logb (T : ℕ) : FixedModel.lg T ≤ Real.logb 2 ((T : ℝ) + 2) := by
  unfold FixedModel.lg
  have h1 : 0 ≤ Real.log ((T : ℝ) + 2) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)])
  have h2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have h3 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [Real.logb, le_div_iff₀ h3]
  nlinarith

/-- `log₂ x ≤ 2 ln x` for `x ≥ 1`. Auxiliary for `cor:conf-fixed-model` (conference.tex). -/
theorem logb_le_two_mul_log {x : ℝ} (hx : 1 ≤ x) : Real.logb 2 x ≤ 2 * Real.log x := by
  have h0 := Real.log_nonneg hx
  have h2 : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  rw [Real.logb, div_le_iff₀ (by linarith)]
  nlinarith

/-- The binary form `S₂ = 1 + log₂(V+2) + log₂(T+2)` of the quantity `S` of `lem:conf-replay`
is at most twice the natural form `S = 1 + ln(V+2) + ln(T+2)` (`FixedModel.replayS`).
Auxiliary for `cor:conf-fixed-model` (conference.tex). -/
theorem replayS_two_le (V T : ℕ) :
    1 + Real.logb 2 ((V : ℝ) + 2) + Real.logb 2 ((T : ℝ) + 2) ≤
      2 * FixedModel.replayS V T := by
  have hV : (1 : ℝ) ≤ (V : ℝ) + 2 := by linarith [(Nat.cast_nonneg V : (0 : ℝ) ≤ V)]
  have hT : (1 : ℝ) ≤ (T : ℝ) + 2 := by linarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)]
  have h1 := logb_le_two_mul_log hV
  have h2 := logb_le_two_mul_log hT
  unfold FixedModel.replayS FixedModel.lg
  linarith

/-- `S = 1 + ln(V+2) + ln(T+2) ≥ 1`. Auxiliary for `cor:conf-fixed-model` (conference.tex). -/
theorem one_le_replayS (V T : ℕ) : 1 ≤ FixedModel.replayS V T := by
  unfold FixedModel.replayS
  have h1 : 0 ≤ Real.log ((V : ℝ) + 2) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg V : (0 : ℝ) ≤ V)])
  have h2 := (FixedModel.lg_pos T).le
  linarith

/-- `S₂ = 1 + log₂(V+2) + log₂(T+2) ≥ 1`. Auxiliary for `cor:conf-fixed-model`
(conference.tex). -/
theorem one_le_replayS_two (V T : ℕ) :
    1 ≤ 1 + Real.logb 2 ((V : ℝ) + 2) + Real.logb 2 ((T : ℝ) + 2) := by
  have h1 : 0 ≤ Real.logb 2 ((V : ℝ) + 2) :=
    Real.logb_nonneg (by norm_num) (by linarith [(Nat.cast_nonneg V : (0 : ℝ) ≤ V)])
  have h2 : 0 ≤ Real.logb 2 ((T : ℝ) + 2) :=
    Real.logb_nonneg (by norm_num) (by linarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)])
  linarith

/-! ## The fixed model and its charges -/

/-- The fixed parameters of `cor:conf-fixed-model` (conference.tex) that enter
`eq:conf-explicit`: the rank-dependent constant `C_r`, the bit length `b`, the width `n`, the
depth `D`, the key rank `r`, the rescaling bits `κ`, the Taylor parameter `H` and the guard
`G₀` (working precision `P = p + G₀`). The vocabulary size is the `V` of the sampler. -/
structure FixedParams where
  /-- The rank-dependent constant `C_r`. -/
  Cr : ℝ
  /-- The bit length `b`. -/
  b : ℝ
  /-- The width `n`. -/
  n : ℝ
  /-- The depth `D`. -/
  D : ℝ
  /-- The key rank `r`. -/
  r : ℕ
  /-- The rescaling bits `κ`. -/
  κ : ℕ
  /-- The Taylor parameter `H`. -/
  H : ℕ
  /-- The precision guard `G₀`. -/
  G₀ : ℕ
  /-- `C_r ≥ 0`. -/
  Cr_nonneg : 0 ≤ Cr
  /-- `b ≥ 0`. -/
  b_nonneg : 0 ≤ b
  /-- `n ≥ 0`. -/
  n_nonneg : 0 ≤ n
  /-- `D ≥ 0`. -/
  D_nonneg : 0 ≤ D

namespace FixedParams

/-- The cost `eq:conf-explicit` (conference.tex) of one deterministic token evaluation of the
fixed model at accuracy `p` and context length `T`, for vocabulary size `V`. -/
noncomputable def cost (M : FixedParams) (V : ℝ) (p T : ℕ) : ℝ :=
  FixedModel.fixedCost M.Cr M.b M.n M.D V M.r M.κ M.H M.G₀ p T

/-- The cost `eq:conf-explicit` (conference.tex) is nonnegative. -/
theorem cost_nonneg (M : FixedParams) {V : ℝ} (p T : ℕ) : 0 ≤ M.cost V p T := by
  unfold cost FixedModel.fixedCost
  have hC := M.Cr_nonneg
  have hD : 0 ≤ M.D + 1 := by linarith [M.D_nonneg]
  have hm : (0 : ℝ) ≤ (FixedModel.taylorDegree M.κ M.H (p + M.G₀) : ℝ) + 1 := by positivity
  have h1 : 0 ≤ M.Cr * (M.D + 1) * (M.n + V + 1) ^ 2 :=
    mul_nonneg (mul_nonneg hC hD) (sq_nonneg _)
  have h2 := pow_nonneg hm (2 * M.r + 4)
  exact mul_nonneg (mul_nonneg h1 h2) (Even.pow_nonneg (by decide) _)

/-- If the fixed-model cost is bounded by `G(p + ln(T+2))` and `G(u) ≤ A u^k` for `u ≥ 1` (the
hypotheses of `lem:conf-replay` in `FixedModel`), then `A ≥ 0` and the cost is at most
`A (p + log₂(T+2))^k`, the form of the charges in `Replay`. Auxiliary for
`cor:conf-fixed-model` (conference.tex). -/
theorem cost_le_pow_logb (M : FixedParams) {V : ℝ} {G : ℝ → ℝ} {A : ℝ} {k : ℕ}
    (hG : ∀ u, 1 ≤ u → G u ≤ A * u ^ k)
    (hc : ∀ p T, 1 ≤ p → M.cost V p T ≤ G ((p : ℝ) + FixedModel.lg T)) :
    0 ≤ A ∧ ∀ p T, 1 ≤ p → M.cost V p T ≤ A * ((p : ℝ) + Real.logb 2 ((T : ℝ) + 2)) ^ k := by
  have hstep : ∀ p T, 1 ≤ p → M.cost V p T ≤ A * ((p : ℝ) + FixedModel.lg T) ^ k := by
    intro p T hp
    have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
    exact (hc p T hp).trans (hG _ (by linarith [FixedModel.lg_pos T]))
  have hA : 0 ≤ A := by
    have h := (M.cost_nonneg 1 0).trans (hstep 1 0 le_rfl)
    have hpos : 0 < ((1 : ℕ) + FixedModel.lg 0 : ℝ) ^ k := by
      have := FixedModel.lg_pos 0
      positivity
    by_contra hneg
    push Not at hneg
    have : A * ((1 : ℕ) + FixedModel.lg 0 : ℝ) ^ k < 0 := mul_neg_of_neg_of_pos hneg hpos
    linarith
  refine ⟨hA, fun p T hp => (hstep p T hp).trans ?_⟩
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hu : 0 ≤ (p : ℝ) + FixedModel.lg T := by linarith [FixedModel.lg_pos T]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu (by linarith [lg_le_logb T]) k) hA

end FixedParams

variable {V : ℕ}

/-- The temporary replay work of the fixed model for one token: when the comparisons at
precisions `p0, ..., p0 + j` are undecided, the length-`T` history is replayed at accuracy
`p0 + j + 1`, charged `T` times the cost `eq:conf-explicit` at that accuracy. This is
`Replay.replayWork` with the actual fixed-model charges in place of `G`.
Paper: proof of `lem:conf-replay` (conference.tex), "If undecided, replay the actual history at
accuracy `p_R+1`"; `cor:conf-fixed-model` (conference.tex). -/
noncomputable def fixedReplayWork (M : FixedParams) {F : Fin (V + 1) → ℝ}
    (E : ∀ p, Replay.Enclosure F p) (p0 T : ℕ) (U : ℝ) : ℝ≥0∞ :=
  ∑' j, (Replay.ReachSet E p0 j).indicator
    (fun _ => ENNReal.ofReal (T * M.cost V (p0 + (j + 1)) T)) U

/-- The comparison work of the reached refinements for one token: when the comparisons at
precisions `p0, ..., p0 + j` are undecided, the uniform cell is compared again at precision
`p0 + j + 1`, charged `V (p0 + j + 2)`, the size of a scan of the `V` cumulative intervals at
that precision. Paper: `lem:conf-replay` (conference.tex), "Include in `G` the work of
comparing a `p`-bit uniform cell with those cumulative intervals; a scan costs `O(V(p+1))`
bits". -/
noncomputable def compareWork {F : Fin (V + 1) → ℝ} (E : ∀ p, Replay.Enclosure F p) (p0 : ℕ)
    (U : ℝ) : ℝ≥0∞ :=
  ∑' j, (Replay.ReachSet E p0 j).indicator
    (fun _ => ENNReal.ofReal (V * (((p0 + (j + 1) : ℕ) : ℝ) + 1))) U

/-- The expected comparison work of the refinements at the routine precision `p_R` is at most
`V p_R`. Paper: proof of `lem:conf-replay` (conference.tex), "Summing costs on the events that
reach each precision", applied to the scan cost `O(V(p+1))`. -/
theorem expected_compareWork_le (B : Replay.Boundaries V) (E : ∀ p, Replay.Enclosure B.F p)
    (R : ℕ) :
    ∫⁻ U, compareWork E (Replay.pR V R) U ∂(Replay.uniform) ≤
      ENNReal.ofReal (V * Replay.pR V R) := by
  have hV := B.one_le
  have hV0 : (0 : ℝ) ≤ V := Nat.cast_nonneg V
  set p0 := Replay.pR V R with hp0
  have hp1 : (1 : ℝ) ≤ p0 := by exact_mod_cast Replay.one_le_pR hV R
  have h2p : (512 : ℝ) * V ≤ 2 ^ p0 := by
    have h := Replay.le_two_pow_pR R hV
    have h2 : (2 : ℝ) ≤ (R : ℝ) + 2 := by linarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)]
    have h8 : (8 : ℝ) ≤ ((R : ℝ) + 2) ^ 3 := by
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ ((R : ℝ) + 2) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
    nlinarith
  have hG : ∀ u, 1 ≤ u → (fun u : ℝ => (V : ℝ) * (u + 2)) u ≤ (3 * V) * u ^ 1 := by
    intro u hu
    simp only [pow_one]
    nlinarith
  calc ∫⁻ U, compareWork E p0 U ∂(Replay.uniform)
      ≤ ∑' j : ℕ, ENNReal.ofReal (V * (((p0 + (j + 1) : ℕ) : ℝ) + 1))
          * ENNReal.ofReal (4 * V / 2 ^ (p0 + j)) := Replay.lintegral_reach_le B E p0 _
    _ = ∑' j : ℕ, ENNReal.ofReal (4 * V / 2 ^ p0) * ENNReal.ofReal
          ((1 / 2 : ℝ) ^ j * (fun u : ℝ => (V : ℝ) * (u + 2)) ((p0 : ℝ) + j)) := by
        refine tsum_congr fun j => ?_
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        push_cast
        rw [pow_add, _root_.one_div_pow]
        field_simp
        ring
    _ = ENNReal.ofReal (4 * V / 2 ^ p0) * ∑' j : ℕ, ENNReal.ofReal
          ((1 / 2 : ℝ) ^ j * (fun u : ℝ => (V : ℝ) * (u + 2)) ((p0 : ℝ) + j)) :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (4 * V / 2 ^ p0) *
          ENNReal.ofReal (3 * V * (2 ^ (1 + 1) * (Nat.factorial 1) * (p0 : ℝ) ^ 1)) :=
        mul_le_mul_right (Replay.tsum_half_mul_G_le hG hp1) _
    _ ≤ ENNReal.ofReal (V * p0) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hpos : (0 : ℝ) < 2 ^ p0 := by positivity
        rw [Nat.factorial_one, div_mul_eq_mul_div, div_le_iff₀ hpos]
        push_cast
        have hVp : 0 ≤ (V : ℝ) * p0 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h2p hVp]

/-- The evaluation and random-bit part of the expected work of the replay sampler of the fixed
model for one token, at history length `T` and schedule parameter `N` (routine horizon `2N`,
future horizon `4N`): one routine evaluation at `p_{2N}`, two future evaluations at `p_{4N}`,
the expected temporary replays, the initial cell of `p_{2N}` random bits and the expected
additional random bits. Every evaluation is charged the cost `eq:conf-explicit` at context
length `T` (the two future evaluations replay earlier history tokens, so this is an upper bound
for them, as in `Replay.expected_token_work_le`). Paper: proof of `lem:conf-replay`
(conference.tex); `cor:conf-fixed-model` (conference.tex). -/
noncomputable def evalWork (M : FixedParams) (B : Replay.Boundaries V)
    (E : ∀ p, Replay.Enclosure B.F p) (T N : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (M.cost V (Replay.pR V (2 * N)) T)
    + 2 * ENNReal.ofReal (M.cost V (Replay.pR V (4 * N)) T)
    + ∫⁻ U, fixedReplayWork M E (Replay.pR V (2 * N)) T U ∂(Replay.uniform)
    + ((Replay.pR V (2 * N) : ℝ≥0∞)
      + ∫⁻ U, Replay.extraBits E (Replay.pR V (2 * N)) U ∂(Replay.uniform))

/-- The expected work of the replay sampler of the fixed model for one token: `evalWork` plus
the comparison of the uniform cell with the cumulative intervals at the routine precision
(charged `V (p_{2N} + 1)`) and at every reached refinement (`compareWork`). Paper: proof of
`lem:conf-replay` (conference.tex), with the scan cost `O(V(p+1))` charged separately from the
evaluator cost; `cor:conf-fixed-model` (conference.tex). -/
noncomputable def tokenWork (M : FixedParams) (B : Replay.Boundaries V)
    (E : ∀ p, Replay.Enclosure B.F p) (T N : ℕ) : ℝ≥0∞ :=
  evalWork M B E T N
    + (ENNReal.ofReal (V * ((Replay.pR V (2 * N) : ℝ) + 1))
      + ∫⁻ U, compareWork E (Replay.pR V (2 * N)) U ∂(Replay.uniform))

/-- The fixed-model evaluation work is at most the work charged in `Replay` with
`G(u) = A u^k`, when the cost `eq:conf-explicit` is at most `A (p + log₂(T+2))^k`. Auxiliary for
`cor:conf-fixed-model` (conference.tex). -/
theorem evalWork_le_replay (M : FixedParams) (B : Replay.Boundaries V)
    (E : ∀ p, Replay.Enclosure B.F p) (T N : ℕ) {A : ℝ} {k : ℕ}
    (hc : ∀ p T, 1 ≤ p → M.cost V p T ≤ A * ((p : ℝ) + Real.logb 2 ((T : ℝ) + 2)) ^ k) :
    evalWork M B E T N ≤
      ENNReal.ofReal ((fun u => A * u ^ k)
          ((Replay.pR V (2 * N) : ℝ) + Real.logb 2 ((T : ℝ) + 2)))
        + 2 * ENNReal.ofReal ((fun u => A * u ^ k)
          ((Replay.pR V (4 * N) : ℝ) + Real.logb 2 ((T : ℝ) + 2)))
        + ∫⁻ U, Replay.replayWork E (Replay.pR V (2 * N)) T (fun u => A * u ^ k)
            (Real.logb 2 ((T : ℝ) + 2)) U ∂(Replay.uniform)
        + ((Replay.pR V (2 * N) : ℝ≥0∞)
          + ∫⁻ U, Replay.extraBits E (Replay.pR V (2 * N)) U ∂(Replay.uniform)) := by
  have hV := B.one_le
  unfold evalWork
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) le_rfl
  · exact ENNReal.ofReal_le_ofReal (hc _ T (Replay.one_le_pR hV _))
  · exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hc _ T (Replay.one_le_pR hV _))) 2
  · refine lintegral_mono fun U => ENNReal.tsum_le_tsum fun j => ?_
    refine Set.indicator_le_indicator ?_
    apply ENNReal.ofReal_le_ofReal
    have h := hc (Replay.pR V (2 * N) + (j + 1)) T (by omega)
    have hcast : ((Replay.pR V (2 * N) + (j + 1) : ℕ) : ℝ) =
        (Replay.pR V (2 * N) : ℝ) + ((j + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast] at h
    exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg T)

/-- Per-token expected work of the replay sampler of the fixed model, from
`Replay.expected_token_work_le_schedule` and `expected_compareWork_le`: if the cost
`eq:conf-explicit` is at most `A (p + log₂(T+2))^k` and the schedule satisfies `T ≤ 2N ≤ 4T`,
the expected work is at most `(3·16^k + 2^k k! 16^k) A S₂^k + 17 S₂ + 33 V S₂` with
`S₂ = 1 + log₂(V+2) + log₂(T+2)`; the last term is the comparison work.
Paper: `lem:conf-replay` (conference.tex), "Its expected total bit work is `O_k(AS^k+S)`",
applied as in the proof of `thm:conf-decoder` and `cor:conf-fixed-model` (conference.tex);
`lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem tokenWork_le (M : FixedParams) (B : Replay.Boundaries V)
    (E : ∀ p, Replay.Enclosure B.F p) {T N : ℕ} (hTN : T ≤ 2 * N) (hNT : N ≤ 2 * T)
    {A : ℝ} {k : ℕ} (hA : 0 ≤ A)
    (hc : ∀ p T, 1 ≤ p → M.cost V p T ≤ A * ((p : ℝ) + Real.logb 2 ((T : ℝ) + 2)) ^ k) :
    tokenWork M B E T N ≤
      ENNReal.ofReal ((3 * 16 ^ k + 2 ^ k * k.factorial * 16 ^ k) * A
          * (1 + Real.logb 2 ((V : ℝ) + 2) + Real.logb 2 ((T : ℝ) + 2)) ^ k
          + 17 * (1 + Real.logb 2 ((V : ℝ) + 2) + Real.logb 2 ((T : ℝ) + 2))
          + 33 * V * (1 + Real.logb 2 ((V : ℝ) + 2) + Real.logb 2 ((T : ℝ) + 2))) := by
  have hV := B.one_le
  set S2 := 1 + Real.logb 2 ((V : ℝ) + 2) + Real.logb 2 ((T : ℝ) + 2) with hS2
  have hS21 : 1 ≤ S2 := one_le_replayS_two V T
  have hV0 : (0 : ℝ) ≤ V := Nat.cast_nonneg V
  have heval := (evalWork_le_replay M B E T N hc).trans
    (Replay.expected_token_work_le_schedule B E hTN hNT hA (fun _ _ => le_rfl))
  have hp := Replay.pR_add_log_le hV (R := 2 * N) (T := T) (by omega)
  have hL : 0 ≤ Real.logb 2 ((T : ℝ) + 2) := Real.logb_nonneg (by norm_num)
    (by linarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)])
  have hp16 : (Replay.pR V (2 * N) : ℝ) ≤ 16 * S2 := by linarith
  have hcmp : ENNReal.ofReal (V * ((Replay.pR V (2 * N) : ℝ) + 1))
      + ∫⁻ U, compareWork E (Replay.pR V (2 * N)) U ∂(Replay.uniform) ≤
        ENNReal.ofReal (33 * V * S2) := by
    refine (add_le_add le_rfl (expected_compareWork_le B E (2 * N))).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  unfold tokenWork
  refine (add_le_add heval hcmp).trans ?_
  have h0 : (0 : ℝ) ≤ (3 * 16 ^ k + 2 ^ k * k.factorial * 16 ^ k) * A * S2 ^ k + 17 * S2 := by
    positivity
  rw [← ENNReal.ofReal_add h0 (by positivity)]

/-- The largest expected per-token work of the replay sampler over all histories of length `T`.
For each history `h` the sampler uses exact boundaries `B h` and the evaluator's enclosures
`E h p` at every precision; `N T` is the schedule parameter at length `T`.
Paper: `lem:conf-replay` (conference.tex), "The expectation conditions on every realized
history"; `cor:conf-fixed-model` (conference.tex). -/
noncomputable def worstWork (M : FixedParams) (B : List (Fin V) → Replay.Boundaries V)
    (E : ∀ h p, Replay.Enclosure (B h).F p) (N : ℕ → ℕ) (T : ℕ) : ℝ≥0∞ :=
  ⨆ h : {h : List (Fin V) // h.length = T}, tokenWork M (B h.1) (E h.1) T (N T)

/-- The worst-case expected per-token work as a real number. Paper: `cor:conf-fixed-model`
(conference.tex), "the expected per-token cost". The headline theorems also state that
`worstWork` is finite, so that this real number is the expectation itself. -/
noncomputable def expectedWork (M : FixedParams) (B : List (Fin V) → Replay.Boundaries V)
    (E : ∀ h p, Replay.Enclosure (B h).F p) (N : ℕ → ℕ) (T : ℕ) : ℝ :=
  (worstWork M B E N T).toReal

/-- The constant `C_k = 2^k (3·16^k + 2^k k! 16^k) + 34 + 66 V` of `lem:conf-replay` in the
natural-log normalization of `FixedModel`, for vocabulary size `V`; the term `66 V` absorbs the
comparison scans. -/
noncomputable def replayConst (V k : ℕ) : ℝ :=
  2 ^ k * (3 * 16 ^ k + 2 ^ k * k.factorial * 16 ^ k) + 34 + 66 * V

/-- The replay stand-in `hreplay` of `FixedModel.fixedModel_expected_isBigO` holds for the
replay sampler, together with finiteness: for every `G` with `G(u) ≤ A u^k` (`u ≥ 1`) that
bounds the cost `eq:conf-explicit` by `G(p + ln(T+2))`, the worst-case expected per-token work
is at most `C_k (A S^k + S)` with `S = 1 + ln(V+2) + ln(T+2)`, both as an extended real (so it is
finite) and as a real number. The schedule `N` only has to satisfy the invariants
`T ≤ 2N(T) ≤ 4T` of `ReplaySchedule` (`len_le_horizon`, `Inv.N_le_two_len`).
Paper: `lem:conf-replay` (conference.tex), "Summing costs on the events that reach each
precision proves finite expected work", as used in the proof of `cor:conf-fixed-model`
(conference.tex), "Lemma `lem:conf-replay` preserves it"; `lem:replayexactsampling` and
`cor:fixedmodelcontext` (attention_moment_decoder.tex). -/
theorem replay_hypothesis (M : FixedParams) (B : List (Fin V) → Replay.Boundaries V)
    (E : ∀ h p, Replay.Enclosure (B h).F p) (N : ℕ → ℕ)
    (hN : ∀ T, T ≤ 2 * N T ∧ N T ≤ 2 * T) :
    ∀ (G : ℝ → ℝ) (A : ℝ) (k : ℕ), (∀ u, 1 ≤ u → G u ≤ A * u ^ k) →
      (∀ p T, 1 ≤ p → FixedModel.fixedCost M.Cr M.b M.n M.D V M.r M.κ M.H M.G₀ p T ≤
        G ((p : ℝ) + FixedModel.lg T)) →
      ∀ T, worstWork M B E N T ≤ ENNReal.ofReal
          (replayConst V k * (A * FixedModel.replayS V T ^ k + FixedModel.replayS V T)) ∧
        expectedWork M B E N T ≤
          replayConst V k * (A * FixedModel.replayS V T ^ k + FixedModel.replayS V T) := by
  intro G A k hG hcost T
  obtain ⟨hA, hc⟩ := M.cost_le_pow_logb hG hcost
  set S2 := 1 + Real.logb 2 ((V : ℝ) + 2) + Real.logb 2 ((T : ℝ) + 2) with hS2
  set S := FixedModel.replayS V T with hS
  set c1 : ℝ := 3 * 16 ^ k + 2 ^ k * k.factorial * 16 ^ k with hc1
  have hc10 : 0 ≤ c1 := by positivity
  have hV0 : (0 : ℝ) ≤ V := Nat.cast_nonneg V
  have hS21 : 1 ≤ S2 := one_le_replayS_two V T
  have hS1 : 1 ≤ S := one_le_replayS V T
  have hS2S : S2 ≤ 2 * S := replayS_two_le V T
  have hsup : worstWork M B E N T ≤
      ENNReal.ofReal (c1 * A * S2 ^ k + 17 * S2 + 33 * V * S2) :=
    iSup_le fun h => tokenWork_le M (B h.1) (E h.1) (hN T).1 (hN T).2 hA hc
  have hpow : S2 ^ k ≤ 2 ^ k * S ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) hS2S k
  have hX : 0 ≤ A * S ^ k := by positivity
  have h1 : c1 * A * S2 ^ k ≤ 2 ^ k * c1 * (A * S ^ k) := by
    calc c1 * A * S2 ^ k ≤ c1 * A * (2 ^ k * S ^ k) :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg hc10 hA)
      _ = 2 ^ k * c1 * (A * S ^ k) := by ring
  have h2 : (0 : ℝ) ≤ 2 ^ k * c1 := by positivity
  have hVS : V * S2 ≤ V * (2 * S) := mul_le_mul_of_nonneg_left hS2S hV0
  have hle : c1 * A * S2 ^ k + 17 * S2 + 33 * V * S2 ≤
      replayConst V k * (A * S ^ k + S) := by
    calc c1 * A * S2 ^ k + 17 * S2 + 33 * V * S2
        ≤ 2 ^ k * c1 * (A * S ^ k) + (34 + 66 * V) * S := by nlinarith
      _ ≤ replayConst V k * (A * S ^ k + S) := by
          unfold replayConst
          rw [← hc1]
          nlinarith
  have hsup' := hsup.trans (ENNReal.ofReal_le_ofReal hle)
  refine ⟨hsup', ?_⟩
  have hC : 0 ≤ replayConst V k := by unfold replayConst; positivity
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC (by positivity)) hsup'

/-- For the fixed model, the cost `eq:conf-explicit` is at most
`A_M (p + log₂(T+2))^(2r+12)` with the model constant `A_M = FixedModel.fixedCostCoeff ≥ 0`.
From `FixedModel.fixedCost_le_pow`. Paper: `cor:conf-fixed-model` (conference.tex). -/
theorem cost_le_coeff_pow (M : FixedParams) (V : ℕ) :
    0 ≤ FixedModel.fixedCostCoeff M.Cr M.b M.n M.D V M.r M.κ M.H M.G₀ ∧
      ∀ p T, 1 ≤ p → M.cost V p T ≤
        FixedModel.fixedCostCoeff M.Cr M.b M.n M.D V M.r M.κ M.H M.G₀ *
          ((p : ℝ) + Real.logb 2 ((T : ℝ) + 2)) ^ (2 * M.r + 12) :=
  M.cost_le_pow_logb (G := fun u =>
      FixedModel.fixedCostCoeff M.Cr M.b M.n M.D V M.r M.κ M.H M.G₀ * u ^ (2 * M.r + 12))
    (fun _ _ => le_rfl)
    (fun p T hp => FixedModel.fixedCost_le_pow M.Cr M.b M.n M.D V M.Cr_nonneg M.b_nonneg
      M.n_nonneg M.D_nonneg (Nat.cast_nonneg V) M.r M.κ M.H M.G₀ p T hp)

/-- Paper: `lem:conf-replay` (conference.tex), "proves finite expected work", for the fixed
model: the worst-case expected per-token work is at most `C_k (A_M S^k + S)` with
`k = 2r + 12` and the model constant `A_M`; in particular it is finite. -/
theorem worstWork_le_fixed (M : FixedParams) (B : List (Fin V) → Replay.Boundaries V)
    (E : ∀ h p, Replay.Enclosure (B h).F p) (N : ℕ → ℕ)
    (hN : ∀ T, T ≤ 2 * N T ∧ N T ≤ 2 * T) (T : ℕ) :
    worstWork M B E N T ≤ ENNReal.ofReal (replayConst V (2 * M.r + 12) *
      (FixedModel.fixedCostCoeff M.Cr M.b M.n M.D V M.r M.κ M.H M.G₀ *
        FixedModel.replayS V T ^ (2 * M.r + 12) + FixedModel.replayS V T)) :=
  (replay_hypothesis M B E N hN (fun u =>
      FixedModel.fixedCostCoeff M.Cr M.b M.n M.D V M.r M.κ M.H M.G₀ * u ^ (2 * M.r + 12))
    _ (2 * M.r + 12) (fun _ _ => le_rfl)
    (fun p T hp => FixedModel.fixedCost_le_pow M.Cr M.b M.n M.D V M.Cr_nonneg M.b_nonneg
      M.n_nonneg M.D_nonneg (Nat.cast_nonneg V) M.r M.κ M.H M.G₀ p T hp) T).1

/-- Paper: `cor:conf-fixed-model` (conference.tex, "A fixed finite model"), with
`lem:conf-replay` discharged: for a fixed model, the worst-case expected per-token work of the
replay sampler, with every evaluation charged the cost `eq:conf-explicit` and every comparison
the scan cost `V(p+1)`, is finite at every length and is `O(log^(2r+12)(T+2))`. The schedule
`N` is any horizon with `T ≤ 2N(T) ≤ 4T`; the background schedule is
`fixedModel_schedule_isBigO`. The asymptotic part is `FixedModel.fixedModel_expected_isBigO`
with its hypothesis `hreplay` supplied by `replay_hypothesis`. Full version
`cor:fixedmodelcontext` (attention_moment_decoder.tex). -/
theorem fixedModel_replay_isBigO (M : FixedParams) (B : List (Fin V) → Replay.Boundaries V)
    (E : ∀ h p, Replay.Enclosure (B h).F p) (N : ℕ → ℕ)
    (hN : ∀ T, T ≤ 2 * N T ∧ N T ≤ 2 * T) :
    (∀ T, worstWork M B E N T < ⊤) ∧
      expectedWork M B E N =O[atTop] (fun T => FixedModel.lg T ^ (2 * M.r + 12)) :=
  ⟨fun T => (worstWork_le_fixed M B E N hN T).trans_lt ENNReal.ofReal_lt_top,
    FixedModel.fixedModel_expected_isBigO M.Cr M.b M.n M.D V M.Cr_nonneg M.b_nonneg M.n_nonneg
      M.D_nonneg (Nat.cast_nonneg V) M.r M.κ M.H M.G₀ (expectedWork M B E N) (replayConst V)
      (fun _ => ENNReal.toReal_nonneg)
      (fun G A k hG hc T => (replay_hypothesis M B E N hN G A k hG hc T).2)⟩

/-! ## The background schedule -/

/-- The schedule parameter at length `T` for prompt length `T0`: the parameter `N` of the state
`step^[T - T0] (init T0)` of `ReplaySchedule` when `T ≥ T0`. Lengths below the prompt length are
not decoding steps; there the value `T` is used. Auxiliary for `cor:conf-fixed-model`
(conference.tex). -/
noncomputable def schedN (T0 T : ℕ) : ℕ :=
  if T0 ≤ T then (ReplaySchedule.step^[T - T0] (ReplaySchedule.init T0)).N else T

/-- At length `T ≥ T0` the schedule state `step^[T - T0] (init T0)` has history length `T`.
Paper: proof of `lem:conf-replay` (conference.tex), "After `j` appends, the true history has
length `N+j`". -/
theorem sched_len {T0 T : ℕ} (h : T0 ≤ T) :
    (ReplaySchedule.step^[T - T0] (ReplaySchedule.init T0)).len = T := by
  rw [ReplaySchedule.len_iterate]
  omega

/-- The schedule invariants `T ≤ 2N ≤ 4T` at every length. Paper: proof of `lem:conf-replay`
(conference.tex), "For `T ≤ R`" and the schedule paragraph. -/
theorem schedN_spec {T0 : ℕ} (hT0 : 1 ≤ T0) (T : ℕ) :
    T ≤ 2 * schedN T0 T ∧ schedN T0 T ≤ 2 * T := by
  unfold schedN
  split_ifs with h
  · have hinv := ReplaySchedule.inv_iterate hT0 (T - T0)
    have h1 := ReplaySchedule.len_le_horizon hinv
    have h2 := hinv.N_le_two_len
    rw [sched_len h] at h1 h2
    exact ⟨h1, h2⟩
  · omega

/-- Paper: `cor:conf-fixed-model` (conference.tex), for the replay sampler run with the
background schedule of the proof of `lem:conf-replay`: for prompt length `T0 ≥ 1`, at each
length `T ≥ T0` the sampler uses the schedule parameter of the state
`step^[T - T0] (init T0)`; its worst-case expected per-token work, with every evaluation
charged the cost `eq:conf-explicit` and every comparison the scan cost `V(p+1)`, is finite at
every length `T ≥ T0` and is `O(log^(2r+12)(T+2))`. Full version `cor:fixedmodelcontext`
(attention_moment_decoder.tex). -/
theorem fixedModel_schedule_isBigO (M : FixedParams) (B : List (Fin V) → Replay.Boundaries V)
    (E : ∀ h p, Replay.Enclosure (B h).F p) {T0 : ℕ} (hT0 : 1 ≤ T0) :
    (∀ T, T0 ≤ T → (⨆ h : {h : List (Fin V) // h.length = T},
        tokenWork M (B h.1) (E h.1) T
          (ReplaySchedule.step^[T - T0] (ReplaySchedule.init T0)).N) < ⊤) ∧
    (fun T => (⨆ h : {h : List (Fin V) // h.length = T},
        tokenWork M (B h.1) (E h.1) T
          (ReplaySchedule.step^[T - T0] (ReplaySchedule.init T0)).N).toReal)
      =O[atTop] (fun T => FixedModel.lg T ^ (2 * M.r + 12)) := by
  obtain ⟨hfin, hO⟩ := fixedModel_replay_isBigO M B E (schedN T0) (schedN_spec hT0)
  refine ⟨fun T hT => ?_, hO.congr' ?_ EventuallyEq.rfl⟩
  · have := hfin T
    simpa only [worstWork, schedN, hT, ↓reduceIte] using this
  · filter_upwards [eventually_ge_atTop T0] with T hT
    simp only [expectedWork, worstWork, schedN, hT, ↓reduceIte]

/-- Paper: `thm:conf-decoder` (conference.tex), the prefill cost of the fixed model: building
the routine evaluator at `p_{2N}` on the `T0` prompt tokens, with `N` the least power of two
at least `T0`, costs at most `T0 · 16^k A_M S0₂^k` with `k = 2r + 12`, the model constant
`A_M = FixedModel.fixedCostCoeff` and `S0₂ = 1 + log₂(V+2) + log₂(T0+2)`. From
`cost_le_coeff_pow`, `Replay.prefill_work_le` and `ReplaySchedule.firstHorizon_lt`. -/
theorem fixed_prefill_le (M : FixedParams) {T0 : ℕ} (hT0 : 1 ≤ T0) (hV : 1 ≤ V) :
    (T0 : ℝ) * M.cost V (Replay.pR V (2 * ReplaySchedule.firstHorizon T0)) T0 ≤
      T0 * (16 ^ (2 * M.r + 12) * FixedModel.fixedCostCoeff M.Cr M.b M.n M.D V M.r M.κ M.H M.G₀
        * (1 + Real.logb 2 ((V : ℝ) + 2) + Real.logb 2 ((T0 : ℝ) + 2)) ^ (2 * M.r + 12)) := by
  obtain ⟨hA, hc⟩ := cost_le_coeff_pow M V
  have h := Replay.prefill_work_le (V := V) (T0 := T0) (N := ReplaySchedule.firstHorizon T0)
    (ReplaySchedule.firstHorizon_lt T0 hT0).le hV hA
    (G := fun u => FixedModel.fixedCostCoeff M.Cr M.b M.n M.D V M.r M.κ M.H M.G₀ *
      u ^ (2 * M.r + 12)) (fun _ _ => le_rfl)
  refine le_trans ?_ h
  exact mul_le_mul_of_nonneg_left (hc _ T0 (Replay.one_le_pR hV _)) (Nat.cast_nonneg T0)

/-! ## The bounded chart in the stability proof -/

/-- Paper: proof of `lem:conf-stability` (conference.tex), "Apply Lemma `lem:conf-chart` to a
column basis of `W_K`. The common affine key space has coordinates `k = c₀ + A k_I` with
`|A_{ij}| ≤ 2`. Put `z_j = (k_j)_I / K`. The common score offset cancels, and the remaining
coefficients are `t = (βK/n) qᵀA`, `‖t‖₁ ≤ 2rβK²`"; full version `lem:prefixstability`
(attention_moment_decoder.tex).

The keys are `k_j = W_K x_j + b_K` for a key matrix of rank at most `r`, queries and keys are
bounded by `K`. The chart is built by `ChartBasis.exists_bounded_chart` (from
`Chart.exists_bounded_chart` and `Chart.chart_repr`) on the column space of `W_K`; this
discharges the hypothesis `|A_{ij}| ≤ 2` of `Stability.chart_coeff_l1`. The conclusions are:
the chart bound, the chart representation of every key, `‖t‖₁ ≤ 2rβK²`, chart coordinates in
`[-1, 1]` (`Stability.chart_coord_le_one`), and the identity of the attention mean over the
actual keys with the ratio `A(t)` of `lem:conf-moments` (`Stability.attn_chart_eq`). -/
theorem key_chart_attention {ι κ : Type*} [Fintype ι] {n m r : ℕ}
    (W : Matrix (Fin n) (Fin m) ℝ) (hW : W.rank ≤ r) (bK : Fin n → ℝ) (x : ι → Fin m → ℝ)
    (q : Fin n → ℝ) {β K : ℝ} (hβ : 0 ≤ β) (hK : 0 < K) (hq : ∀ i, |q i| ≤ K)
    (hk : ∀ j i, |(W *ᵥ x j + bK) i| ≤ K) (v : ι → κ → ℝ) :
    ∃ I : Fin (finrank ℝ (LinearMap.range W.mulVecLin)) → Fin n,
      let A := Chart.coeff (ChartBasis.basisMatrix (LinearMap.range W.mulVecLin)) I
      let c₀ := bK - A *ᵥ (fun l => bK (I l))
      (∀ i l, |A i l| ≤ 2) ∧
      (∀ j, W *ᵥ x j + bK = c₀ + A *ᵥ (fun l => (W *ᵥ x j + bK) (I l))) ∧
      ∑ l, |β * K / n * ∑ i, q i * A i l| ≤ 2 * r * β * K ^ 2 ∧
      (∀ j l, |(W *ᵥ x j + bK) (I l) / K| ≤ 1) ∧
      ∀ c, Stability.attn (fun j => β / n * ∑ i, q i * (W *ᵥ x j + bK) i) v c =
        (∑ j, Real.exp (∑ l, (β * K / n * ∑ i, q i * A i l) * ((W *ᵥ x j + bK) (I l) / K))
            * v j c) /
          ∑ j, Real.exp (∑ l, (β * K / n * ∑ i, q i * A i l) * ((W *ᵥ x j + bK) (I l) / K)) := by
  set S := LinearMap.range W.mulVecLin with hS
  obtain ⟨I, -, -, -, -, h2, hrepr⟩ := ChartBasis.exists_bounded_chart S
  refine ⟨I, ?_⟩
  intro A c₀
  set k : ι → Fin n → ℝ := fun j => W *ᵥ x j + bK with hkdef
  have hmem : ∀ j, k j - bK ∈ S := fun j => by
    refine ⟨x j, ?_⟩
    simp [hkdef]
  have hkrep : ∀ j, k j = c₀ + A *ᵥ (fun l => k j (I l)) := fun j => hrepr bK (k j) (hmem j)
  have hdr : (finrank ℝ S : ℝ) ≤ r := by exact_mod_cast hW
  refine ⟨h2, hkrep, ?_, fun j l => Stability.chart_coord_le_one hK _ (fun l => hk j (I l)) l,
    fun c => ?_⟩
  · refine (Stability.chart_coeff_l1 hβ q A hq h2).trans ?_
    have : 0 ≤ 2 * β * K ^ 2 := by positivity
    nlinarith
  · have hscore : (fun j => β / n * ∑ i, q i * k j i) =
        fun j => β / n * ∑ i, q i * (c₀ i + ∑ l, A i l * k j (I l)) := by
      funext j
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have h := congrFun (hkrep j) i
      simp only [Pi.add_apply, mulVec, dotProduct] at h
      rw [← h]
    have := Stability.attn_chart_eq β K hK.ne' q c₀ A (fun j l => k j (I l)) v c
    rw [← hscore] at this
    exact this

end ExactSampling.Links.ConferenceDecoder
