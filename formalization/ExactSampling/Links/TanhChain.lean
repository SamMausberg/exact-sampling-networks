import ExactSampling.Tanh.TanhFactory
import ExactSampling.Tanh.MajorityArity

/-!
# The offspring bound with the sequential majority cost of `lem:arity`

Paper: `tanh_scalar.tex`, Lemma `lem:arity` (`eq:sequentialarity`, `eq:arityintegral`) and
Lemma `lem:offspring` (`eq:offspring`, `eq:jointcost`), with the mixture weights of
`lem:majority`.

`ExactSampling.TanhFactory.offspring_bound` and `root_offspring_bound` (and their complemented
forms) take the conclusion of `lem:arity`, `A ≤ 1 + (1 - z²/3) ρ² + ρ⁴`, as the hypothesis `hA`.
`ExactSampling.MajorityArity.sequential_arity_bound` proves that conclusion. Here the two are
composed: the source count `A` in the offspring bound is the expected sequential majority
cost `A_seq = ∑_k π_k cost_k` under the arity law `π_k = (ρ / tanh ρ) d_k / C_k` of
`lem:majority`, and no hypothesis on `A` remains.

Stand-ins kept from `ExactSampling.MajorityArity` (named in the statements):
* `hd0`: `d_k ≥ 0`, the first assertion of `lem:majority` (derived in the paper from the cosh
  product);
* `hd1`: the coefficient `d_1 = ρ tanh ρ sech² ρ` of `F_ρ(v) = sech²(ρ √(1 - v))`;
* `harity`: the identity `eq:arityintegral`, `∑_k π_k (2k+1) = (ρ/q)(1 + ∫_0^1 tanh²(ρv)/v² dv)`
  with `q = tanh ρ`, for the full-majority cost (integration by parts, not formalized).

Modelled inputs (also named in the statements): the sequential majority enters through its
expected source counts `cost k` for the majority of `2k + 1` signs, with the hypotheses
`hcost0` (they are nonnegative), `hcost` (at most `2k + 1`) and `hcost1` (for `k = 1` the
majority stops after two agreeing signs, so the count is `2(p² + (1-p)²) + 3·2p(1-p)` with
`p = (1 + z)/2`; `MajorityArity.majority_three_expected_cost` turns this into `5/2 - z²/2`).

Not formalized: the stopping-time model of the sequential majority (the counts are given by
their values), and everything listed as not formalized in the two imported modules.
-/

namespace ExactSampling.Links.TanhChain

open Real

/-- The arity law `π_k = (ρ / tanh ρ) d_k / C_k` of `lem:majority` (`tanh_scalar.tex`). -/
noncomputable def arityWeight (ρ : ℝ) (d : ℕ → ℝ) (k : ℕ) : ℝ :=
  ρ / tanh ρ * d k / MajorityArity.majC k

/-- The expected sequential majority cost `A_seq = ∑_k π_k cost_k` under the arity law.
Paper: `lem:arity` (`tanh_scalar.tex`), "Sample `K` from `π`, then request signs until one sign
has occurred `K+1` times". -/
noncomputable def seqCost (ρ : ℝ) (d cost : ℕ → ℝ) : ℝ :=
  ∑' k, arityWeight ρ d k * cost k

/-- Paper: `lem:arity` (`tanh_scalar.tex`), `eq:sequentialarity`: the expected sequential
majority cost satisfies `A_seq ≤ 1 + (1 - z²/3) ρ² + ρ⁴`, and the series defining it converges.
From `MajorityArity.sequential_arity_bound` with `π_k ≥ 0` (from the stand-in `hd0`),
`π_1 = (2/3) ρ² sech² ρ` (`MajorityArity.pi_one_eq`, from the stand-in `hd1`), the index-one
cost `5/2 - z²/2` (`MajorityArity.majority_three_expected_cost`), and the stand-in `harity`
for `eq:arityintegral`. The sequential majority enters through its modelled expected source
counts `cost k`, given by the hypotheses `hcost0` (nonnegative), `hcost` (at most `2k + 1`) and
`hcost1` (the stopping rule for `k = 1`); their derivation from the stopping time is not
formalized. -/
theorem seqCost_bound {ρ z : ℝ} (hρ : 0 < ρ) (hz : |z| ≤ 1) (d : ℕ → ℝ)
    (hd0 : ∀ k, 0 ≤ d k) (hd1 : d 1 = ρ * tanh ρ * (1 - tanh ρ ^ 2))
    (harity : HasSum (fun k : ℕ => arityWeight ρ d k * (2 * k + 1))
      (ρ / tanh ρ * (1 + ∫ v in (0 : ℝ)..1, tanh (ρ * v) ^ 2 / v ^ 2)))
    (cost : ℕ → ℝ) (hcost0 : ∀ k, 0 ≤ cost k) (hcost : ∀ k : ℕ, cost k ≤ 2 * k + 1)
    (hcost1 : cost 1 = 2 * (((1 + z) / 2) ^ 2 + (1 - (1 + z) / 2) ^ 2) +
      3 * (2 * ((1 + z) / 2) * (1 - (1 + z) / 2))) :
    HasSum (fun k => arityWeight ρ d k * cost k) (seqCost ρ d cost) ∧
      seqCost ρ d cost ≤ 1 + (1 - z ^ 2 / 3) * ρ ^ 2 + ρ ^ 4 := by
  have hq : 0 < tanh ρ := TanhFactory.tanh_pos_of_pos hρ
  have hw0 : ∀ k, 0 ≤ arityWeight ρ d k := fun k =>
    div_nonneg (mul_nonneg (div_pos hρ hq).le (hd0 k)) (MajorityArity.majC_pos k).le
  have hsum : Summable (fun k => arityWeight ρ d k * cost k) := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (hw0 k) (hcost0 k)) (fun k => ?_)
      harity.summable
    exact mul_le_mul_of_nonneg_left (hcost k) (hw0 k)
  have hseq : HasSum (fun k => arityWeight ρ d k * cost k) (seqCost ρ d cost) :=
    hsum.hasSum
  refine ⟨hseq, ?_⟩
  have hw1 : arityWeight ρ d 1 = 2 / 3 * ρ ^ 2 * (1 - tanh ρ ^ 2) :=
    MajorityArity.pi_one_eq hρ (d 1) hd1
  have hc1 : cost 1 = 5 / 2 - z ^ 2 / 2 := by
    rw [hcost1, MajorityArity.majority_three_expected_cost]
    ring
  have hz2 : z ^ 2 ≤ 1 := by
    have h := abs_le.mp hz
    nlinarith
  exact MajorityArity.sequential_arity_bound hρ hz2 (arityWeight ρ d) cost _ _ hw0 hw1
    harity rfl hcost hc1 hseq

/-- Paper: `lem:offspring` (`tanh_scalar.tex`), `eq:offspring` with `eq:jointcost`, for the race
with `θ = t q` (nonnegative stored bias): a normalized call has expected children at most
`(tanh ρ / r_ℓ) exp(5ρ²/3 + ρ⁴)`, where the mean source count of a reached trial is the
expected sequential majority cost `A_seq` of `lem:arity`. This is
`TanhFactory.offspring_bound` with its hypothesis on `A` discharged by `seqCost_bound`; the
stand-ins `hd0`, `hd1` and `harity` (`eq:arityintegral`) remain, and the sequential majority
enters through its modelled counts `cost k` (`hcost0`, `hcost`, `hcost1`). -/
theorem offspring_bound_seq (a ρ z r : ℝ) (hρ : 0 < ρ) (hz : |z| ≤ 1) (hr : 0 < r)
    (d : ℕ → ℝ) (hd0 : ∀ k, 0 ≤ d k) (hd1 : d 1 = ρ * tanh ρ * (1 - tanh ρ ^ 2))
    (harity : HasSum (fun k : ℕ => arityWeight ρ d k * (2 * k + 1))
      (ρ / tanh ρ * (1 + ∫ v in (0 : ℝ)..1, tanh (ρ * v) ^ 2 / v ^ 2)))
    (cost : ℕ → ℝ) (hcost0 : ∀ k, 0 ≤ cost k) (hcost : ∀ k : ℕ, cost k ≤ 2 * k + 1)
    (hcost1 : cost 1 = 2 * (((1 + z) / 2) ^ 2 + (1 - (1 + z) / 2) ^ 2) +
      3 * (2 * ((1 + z) / 2) * (1 - (1 + z) / 2))) :
    TanhFactory.imgRadius (tanh a) (tanh ρ) / r * seqCost ρ d cost *
        (1 / TanhFactory.raceSuccess (tanh a * tanh ρ) ((1 + tanh (ρ * z) / tanh ρ) / 2)) ≤
      tanh ρ / r * exp (5 / 3 * ρ ^ 2 + ρ ^ 4) :=
  TanhFactory.offspring_bound a ρ z r _ hρ hz hr
    (seqCost_bound hρ hz d hd0 hd1 harity cost hcost0 hcost hcost1).2

/-- Paper: `lem:offspring` (`tanh_scalar.tex`), "for negative `t`, replace `z` by `-z`": the
offspring bound for the complemented race, with the sequential majority cost `A_seq` of
`lem:arity`. From `TanhFactory.offspring_bound_complement` and `seqCost_bound`; the stand-ins
`hd0`, `hd1`, `harity` and the modelled counts `cost k` (`hcost0`, `hcost`, `hcost1`) remain as
in `offspring_bound_seq`. -/
theorem offspring_bound_seq_complement (a ρ z r : ℝ) (hρ : 0 < ρ) (hz : |z| ≤ 1) (hr : 0 < r)
    (d : ℕ → ℝ) (hd0 : ∀ k, 0 ≤ d k) (hd1 : d 1 = ρ * tanh ρ * (1 - tanh ρ ^ 2))
    (harity : HasSum (fun k : ℕ => arityWeight ρ d k * (2 * k + 1))
      (ρ / tanh ρ * (1 + ∫ v in (0 : ℝ)..1, tanh (ρ * v) ^ 2 / v ^ 2)))
    (cost : ℕ → ℝ) (hcost0 : ∀ k, 0 ≤ cost k) (hcost : ∀ k : ℕ, cost k ≤ 2 * k + 1)
    (hcost1 : cost 1 = 2 * (((1 + z) / 2) ^ 2 + (1 - (1 + z) / 2) ^ 2) +
      3 * (2 * ((1 + z) / 2) * (1 - (1 + z) / 2))) :
    TanhFactory.imgRadius (tanh a) (tanh ρ) / r * seqCost ρ d cost *
        (1 / TanhFactory.raceSuccess (-(tanh a * tanh ρ)) ((1 - tanh (ρ * z) / tanh ρ) / 2)) ≤
      tanh ρ / r * exp (5 / 3 * ρ ^ 2 + ρ ^ 4) :=
  TanhFactory.offspring_bound_complement a ρ z r _ hρ hz hr
    (seqCost_bound hρ hz d hd0 hd1 harity cost hcost0 hcost hcost1).2

/-- Paper: `lem:offspring` (`tanh_scalar.tex`), "The root's expected children are at most
`r_D B_D`", with the sequential majority cost `A_seq` of `lem:arity`: given `ρ ≤ x = g r_{D-1}`
and `tanh ρ ≤ r_D`, the root's expected children are at most `r_D exp(5x²/3 + x⁴)`. From
`TanhFactory.root_offspring_bound` and `seqCost_bound`; the stand-ins `hd0`, `hd1`, `harity`
and the modelled counts `cost k` (`hcost0`, `hcost`, `hcost1`) remain as in
`offspring_bound_seq`. -/
theorem root_offspring_bound_seq (a ρ z x rD : ℝ) (hρ : 0 < ρ) (hz : |z| ≤ 1) (hρx : ρ ≤ x)
    (hq : tanh ρ ≤ rD) (d : ℕ → ℝ) (hd0 : ∀ k, 0 ≤ d k)
    (hd1 : d 1 = ρ * tanh ρ * (1 - tanh ρ ^ 2))
    (harity : HasSum (fun k : ℕ => arityWeight ρ d k * (2 * k + 1))
      (ρ / tanh ρ * (1 + ∫ v in (0 : ℝ)..1, tanh (ρ * v) ^ 2 / v ^ 2)))
    (cost : ℕ → ℝ) (hcost0 : ∀ k, 0 ≤ cost k) (hcost : ∀ k : ℕ, cost k ≤ 2 * k + 1)
    (hcost1 : cost 1 = 2 * (((1 + z) / 2) ^ 2 + (1 - (1 + z) / 2) ^ 2) +
      3 * (2 * ((1 + z) / 2) * (1 - (1 + z) / 2))) :
    TanhFactory.imgRadius (tanh a) (tanh ρ) * seqCost ρ d cost *
        (1 / TanhFactory.raceSuccess (tanh a * tanh ρ) ((1 + tanh (ρ * z) / tanh ρ) / 2)) ≤
      rD * exp (5 / 3 * x ^ 2 + x ^ 4) :=
  TanhFactory.root_offspring_bound a ρ z _ x rD hρ hz
    (seqCost_bound hρ hz d hd0 hd1 harity cost hcost0 hcost hcost1).2 hρx hq

/-- Paper: `lem:offspring` (`tanh_scalar.tex`), root bound for the complemented race, with the
sequential majority cost `A_seq` of `lem:arity`. From
`TanhFactory.root_offspring_bound_complement` and `seqCost_bound`; the stand-ins `hd0`, `hd1`,
`harity` and the modelled counts `cost k` (`hcost0`, `hcost`, `hcost1`) remain as in
`offspring_bound_seq`. -/
theorem root_offspring_bound_seq_complement (a ρ z x rD : ℝ) (hρ : 0 < ρ) (hz : |z| ≤ 1)
    (hρx : ρ ≤ x) (hq : tanh ρ ≤ rD) (d : ℕ → ℝ) (hd0 : ∀ k, 0 ≤ d k)
    (hd1 : d 1 = ρ * tanh ρ * (1 - tanh ρ ^ 2))
    (harity : HasSum (fun k : ℕ => arityWeight ρ d k * (2 * k + 1))
      (ρ / tanh ρ * (1 + ∫ v in (0 : ℝ)..1, tanh (ρ * v) ^ 2 / v ^ 2)))
    (cost : ℕ → ℝ) (hcost0 : ∀ k, 0 ≤ cost k) (hcost : ∀ k : ℕ, cost k ≤ 2 * k + 1)
    (hcost1 : cost 1 = 2 * (((1 + z) / 2) ^ 2 + (1 - (1 + z) / 2) ^ 2) +
      3 * (2 * ((1 + z) / 2) * (1 - (1 + z) / 2))) :
    TanhFactory.imgRadius (tanh a) (tanh ρ) * seqCost ρ d cost *
        (1 / TanhFactory.raceSuccess (-(tanh a * tanh ρ)) ((1 - tanh (ρ * z) / tanh ρ) / 2)) ≤
      rD * exp (5 / 3 * x ^ 2 + x ^ 4) :=
  TanhFactory.root_offspring_bound_complement a ρ z _ x rD hρ hz
    (seqCost_bound hρ hz d hd0 hd1 harity cost hcost0 hcost hcost1).2 hρx hq

end ExactSampling.Links.TanhChain
