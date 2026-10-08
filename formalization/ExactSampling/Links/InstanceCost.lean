import ExactSampling.Instance.BooleanGates
import ExactSampling.Instance.RelayGates
import ExactSampling.Instance.ScoreCertificate
import ExactSampling.Lower.TranscriptLowerBounds

/-!
# Cost gaps and score certificates of the hardness networks

Paper: `instance_hardness.tex`, the cost gap in the proofs of
`prop:instance-hardness-eight` and `thm:instance-hardness`, and the proof of
`cor:score-certificate-hardness`.

The gate modules prove the amplitude factorization of the network output on literal parity
inputs, `f(x, y) = A(x) ∏ᵢ yᵢ` (`BooleanGates.output_factorizes` for row norm eight with
`A(x) ≥ tanh 1` on satisfying assignments, `RelayGates.outputC_factorizes` for every row bound
`a = 1 + 2^{-R}` with `A(x) ≥ c/4`). `TranscriptLowerBounds.parity_cost_gap` bounds the probe
cost of an exact sampler given as a finite mixture of decision trees whose target has parity
correlation at least `α`, and
`ScoreCertificate.parity_certificate_term` bounds the first certificate term of an exact
parity factor `α ∏ᵢ yᵢ`. These were connected only in prose; here they are composed:

* `norm_eight_cost_gap`: at a satisfying assignment, every bounded exact sampler of the
  norm-eight network's output (as a function of the `m = 2^r` parity signs), given as a finite
  mixture of decision trees (`TranscriptLowerBounds.Sampler`), has an input with expected
  distinct-probe cost at least `m/2`;
* `relay_cost_gap`: the same with `c m/4` for the relayed network, again for bounded exact
  samplers given as finite mixtures of decision trees;
* `relay_certificate`: the first certificate term of the relayed network at a satisfying
  assignment is at least `c² m/48`.

Not formalized (as in the imported modules): the step "giving the assignment to the sampler
for free can only help", the limit in which the means of the assignment coordinates approach
a satisfying assignment, and the complexity-theoretic conclusions.
-/

namespace ExactSampling.Links.InstanceCost

open Finset

/-- The squares of the three sign conventions agree: `∏ᵢ s(yᵢ) ∏ᵢ s'(yᵢ) = 1` for the `±1`
signs of `TranscriptLowerBounds` and `BooleanGates`. Auxiliary. -/
theorem parity_mul_prod_sgn {m : ℕ} (y : Fin m → Bool) :
    TranscriptLowerBounds.parity y * ∏ i, BooleanGates.sgn (y i) = 1 := by
  unfold TranscriptLowerBounds.parity
  rw [← prod_mul_distrib]
  refine prod_eq_one fun i _ => ?_
  cases y i <;> simp [TranscriptLowerBounds.sgn, BooleanGates.sgn]

/-- The same identity for the signs of `RelayGates`. Auxiliary. -/
theorem parity_mul_prod_sgnC {m : ℕ} (y : Fin m → Bool) :
    TranscriptLowerBounds.parity y * ∏ i, RelayGates.sgn (y i) = 1 := by
  unfold TranscriptLowerBounds.parity
  rw [← prod_mul_distrib]
  refine prod_eq_one fun i _ => ?_
  cases y i <;> simp [TranscriptLowerBounds.sgn, RelayGates.sgn]

/-- Paper: the cost gap in the proof of `prop:instance-hardness-eight` (instance_hardness.tex):
at a satisfying assignment (formula value `V` encoding true), `χ(y) f_φ(x*, y) ≥ tanh 1 ≥ 1/2`
(`eq:SAT-parity-output`), so every bounded exact sampler of the network output on the
`m = 2^r` parity signs, given as a finite mixture of decision trees, has an input `y` with
expected distinct-probe cost at least `m/2`. Composition of `BooleanGates.output_factorizes` with
`TranscriptLowerBounds.parity_cost_gap`. -/
theorem norm_eight_cost_gap (r : ℕ) {V : ℝ} (hV : BooleanGates.Enc true V) {ι : Type*}
    [Fintype ι] (S : TranscriptLowerBounds.Sampler (2 ^ r) ι) (hB : S.Bounded)
    (hf : S.Exact (fun y => BooleanGates.finalOut V
      (BooleanGates.parityTree r (fun i => BooleanGates.litPair (y i))))) :
    ∃ y, 1 / 2 * ((2 ^ r : ℕ) : ℝ) ≤ S.cost y := by
  refine TranscriptLowerBounds.parity_cost_gap S hB hf (fun y => ?_)
  obtain ⟨hfac, -, htrue⟩ := BooleanGates.output_factorizes r V y
  rw [hfac, mul_left_comm, parity_mul_prod_sgn, mul_one]
  exact BooleanGates.half_le_tanh_one.trans (htrue hV)

/-- Paper: the cost gap in the proof of `thm:instance-hardness` (instance_hardness.tex), "The
parity transcript argument now yields `Q^*(W_φ) ≥ cm/4` in the satisfiable case": for the
relayed network with row bound `a = 1 + 2^{-R}`, at a satisfying assignment every bounded
exact sampler of the output on the `m = 2^r` parity signs, given as a finite mixture of decision
trees, has an input with expected distinct-probe cost at least `c m/4`. Composition of
`RelayGates.outputC_factorizes` with `TranscriptLowerBounds.parity_cost_gap`. -/
theorem relay_cost_gap (R r : ℕ) {V : ℝ} (hV : RelayGates.EncC R true V) {ι : Type*}
    [Fintype ι] (S : TranscriptLowerBounds.Sampler (2 ^ r) ι) (hB : S.Bounded)
    (hf : S.Exact (fun y => RelayGates.finalC R V
      (RelayGates.parityTreeC R r (fun i => RelayGates.litPair (y i))))) :
    ∃ y, RelayGates.c R / 4 * ((2 ^ r : ℕ) : ℝ) ≤ S.cost y := by
  refine TranscriptLowerBounds.parity_cost_gap S hB hf (fun y => ?_)
  obtain ⟨hfac, -, htrue⟩ := RelayGates.outputC_factorizes R r V y
  rw [hfac, mul_left_comm, parity_mul_prod_sgnC, mul_one]
  exact htrue hV

/-- Paper: proof of `cor:score-certificate-hardness` (instance_hardness.tex): for the relayed
network with row bound `a = 1 + 2^{-R}`, at a satisfying assignment, with every parity
coordinate at mean `t = √(1 - 1/m)` (`m = 2^r ≥ 2`), the first certificate term of the output
as a function of the parity signs satisfies `I ≥ α² m/3 ≥ c² m/48`. The output is the exact
parity factor `α ∏ᵢ yᵢ` with `α = A(x*) ∈ [c/4, 1)` (`RelayGates.outputC_factorizes`), and
`ScoreCertificate.parity_certificate_term` and `ScoreCertificate.certificate_gap` give the
bound. -/
theorem relay_certificate (R r : ℕ) (hr : 1 ≤ r) {V : ℝ} (hV : RelayGates.EncC R true V) :
    let g : (Fin (2 ^ r) → Bool) → ℝ := fun y =>
      RelayGates.finalC R V (RelayGates.parityTreeC R r (fun i => RelayGates.litPair (y i)))
    let t := Real.sqrt (1 - 1 / ((2 ^ r : ℕ) : ℝ))
    RelayGates.c R ^ 2 * ((2 ^ r : ℕ) : ℝ) / 48 ≤
      (∑ i : Fin (2 ^ r), Real.sqrt (1 - t ^ 2) *
          |ScoreCertificate.partialDeriv g (fun _ => t) i|) ^ 2 /
        (1 - ScoreCertificate.prodExp (fun _ : Fin (2 ^ r) => t) g ^ 2) := by
  intro g t
  set α := Real.tanh (RelayGates.a R / 2 * RelayGates.andR R V (RelayGates.amplC R r)) with hα
  have hg : g = fun y => α * ScoreCertificate.parity y := by
    funext y
    exact (RelayGates.outputC_factorizes R r V y).1
  have hαc : RelayGates.c R / 4 ≤ α := (RelayGates.outputC_factorizes R r V
    (fun _ => true)).2.2 hV
  have hc := RelayGates.c_pos R
  have hα0 : 0 < α := lt_of_lt_of_le (by positivity) hαc
  have hα1 : α ≤ 1 := (Real.tanh_lt_one _).le
  have hm : 2 ≤ 2 ^ r := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  have h := ScoreCertificate.parity_certificate_term hm hα0 hα1
  rw [hg]
  exact (ScoreCertificate.certificate_gap hc.le (Nat.cast_nonneg _) hαc).trans h

end ExactSampling.Links.InstanceCost
