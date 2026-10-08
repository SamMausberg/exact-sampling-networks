import Mathlib

/-!
# Stopped cost and precision tails

This module formalizes the stopping and precision-tail estimates that the paper
uses whenever a known probability is compared with a uniform binary expansion.

* `lem:newprecisionstop` (attention_finite_bits.tex) and `lem:lazy`
  (tanh_bits.tex). We model the comparison of the length-`2^{-t}` dyadic cell of
  a uniform `U` with certified intervals `[lo t, hi t] ∋ p` of width at most
  `2^{-t}`. We prove that a decided stage returns exactly `1{U < p}`, that an
  undecided stage forces `|U - p| ≤ 2^{1-t}`, that this has probability at most
  `2^{2-t}`, that the comparison stops almost surely (its nontermination event has
  probability zero), and the expected-work bound
  `2^{d+5} d! C (B+1)^d` when stage `t` costs at most `C (B+t)^d`.
* The negative-binomial estimate `∑_t 2^{-t} (t+1)^d ≤ d! 2^{d+1}` and its forms
  used in `lem:newprecisionstop`, `lem:newexactification`
  (attention_finite_bits.tex) and `lem:conf-replay` (conference.tex).
* `lem:stopping` (tanh_scalar.tex): the predictable charge of a trial whose
  reaching event is determined before its fresh randomness, and the geometric sum
  `∑_j (1-σ)^j = 1/σ` of the survival probabilities.
* The union bound behind `eq:conf-tail` (conference.tex).

Not formalized: the bit-operation model (the stage cost is a hypothesis), the
interval-arithmetic routines that produce certified intervals, the additive
`O(B+1)` term for the random prefix (it has the same form with `d = 0`), and the
construction of the product space of all fresh random tapes.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ExactSampling.StoppedCost

/-! ## The negative-binomial estimate -/

/-- Auxiliary for `lem:newprecisionstop` (attention_finite_bits.tex): the
inequality `(t+1)^d ≤ d! (t+d choose d)`. -/
theorem pow_succ_le_factorial_mul_choose (t d : ℕ) :
    ((t : ℝ) + 1) ^ d ≤ (d.factorial : ℝ) * ((t + d).choose d : ℝ) := by
  have h := Nat.pow_succ_le_ascFactorial (t + 1) d
  rw [Nat.ascFactorial_eq_factorial_mul_choose] at h
  exact_mod_cast h

/-- Auxiliary for `lem:newprecisionstop` (attention_finite_bits.tex): the
negative-binomial generating function at `1/2`. -/
theorem hasSum_choose_half (d : ℕ) :
    HasSum (fun t : ℕ => ((t + d).choose d : ℝ) * (1 / 2) ^ t) (2 ^ (d + 1)) := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) d (r := 1 / 2)
    (by norm_num)
  convert h using 1
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  simp

/-- Auxiliary for `lem:newprecisionstop` (attention_finite_bits.tex):
summability of `2^{-t} (t+1)^d`. -/
theorem summable_pow_mul_half (d : ℕ) :
    Summable (fun t : ℕ => ((t : ℝ) + 1) ^ d * (1 / 2) ^ t) := by
  refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_)
    ((hasSum_choose_half d).summable.mul_left (d.factorial : ℝ))
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (pow_succ_le_factorial_mul_choose t d) (by positivity)

/-- Paper: `lem:newprecisionstop` (attention_finite_bits.tex), the estimate
`∑_{t ≥ 0} 2^{-t} (t+1)^d ≤ d! 2^{d+1}`; the same inequality closes
`lem:conf-replay` (conference.tex). -/
theorem tsum_pow_mul_half_le (d : ℕ) :
    ∑' t : ℕ, ((t : ℝ) + 1) ^ d * (1 / 2) ^ t ≤ d.factorial * 2 ^ (d + 1) := by
  calc ∑' t : ℕ, ((t : ℝ) + 1) ^ d * (1 / 2) ^ t
      ≤ ∑' t : ℕ, (d.factorial : ℝ) * (((t + d).choose d : ℝ) * (1 / 2) ^ t) := by
        refine Summable.tsum_le_tsum (fun t => ?_) (summable_pow_mul_half d)
          ((hasSum_choose_half d).summable.mul_left _)
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (pow_succ_le_factorial_mul_choose t d)
          (by positivity)
    _ = d.factorial * 2 ^ (d + 1) := by
        rw [tsum_mul_left, (hasSum_choose_half d).tsum_eq]

/-- Paper: `lem:conf-replay` (conference.tex): for `P ≥ 1`,
`∑_{j ≥ 0} 2^{-j} (P+j)^k ≤ P^k ∑_{j ≥ 0} 2^{-j} (j+1)^k ≤ 2^{k+1} k! P^k`. -/
theorem replay_sum_le (P : ℝ) (hP : 1 ≤ P) (k : ℕ) :
    Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j * (P + j) ^ k) ∧
      ∑' j : ℕ, (1 / 2 : ℝ) ^ j * (P + j) ^ k ≤ 2 ^ (k + 1) * k.factorial * P ^ k := by
  have hle : ∀ j : ℕ, (1 / 2 : ℝ) ^ j * (P + j) ^ k ≤
      P ^ k * (((j : ℝ) + 1) ^ k * (1 / 2) ^ j) := by
    intro j
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h1 : P + j ≤ P * (j + 1) := by nlinarith
    have h2 : (P + j) ^ k ≤ (P * (j + 1)) ^ k :=
      pow_le_pow_left₀ (by linarith) h1 k
    rw [mul_pow] at h2
    have h3 : (0 : ℝ) ≤ (1 / 2) ^ j := by positivity
    nlinarith
  have hs : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j * (P + j) ^ k) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hle
      ((summable_pow_mul_half k).mul_left _)
  refine ⟨hs, ?_⟩
  calc ∑' j : ℕ, (1 / 2 : ℝ) ^ j * (P + j) ^ k
      ≤ ∑' j : ℕ, P ^ k * (((j : ℝ) + 1) ^ k * (1 / 2) ^ j) :=
        Summable.tsum_le_tsum hle hs ((summable_pow_mul_half k).mul_left _)
    _ = P ^ k * ∑' j : ℕ, ((j : ℝ) + 1) ^ k * (1 / 2) ^ j := tsum_mul_left
    _ ≤ P ^ k * (k.factorial * 2 ^ (k + 1)) :=
        mul_le_mul_of_nonneg_left (tsum_pow_mul_half_le k) (by positivity)
    _ = 2 ^ (k + 1) * k.factorial * P ^ k := by ring

/-- Paper: `lem:newexactification` (attention_finite_bits.tex). Stage `m + r`,
`r ≥ 1`, of the fallback is reached with probability at most `2^{3-m-r}` and
costs at most `H (B+m+r)^d`; the resulting expected fallback cost
`8 2^{-m} H ∑_{r ≥ 1} 2^{-r} (B+m+r)^d` is at most
`2^{d+5} d! 2^{-m} H (B+m+1)^d`. The sum is indexed by `r + 1`. -/
theorem fallback_sum_le (B H : ℝ) (m d : ℕ) (hB : 0 ≤ B) (hH : 0 ≤ H) :
    8 * (1 / 2) ^ m * H *
        ∑' r : ℕ, (1 / 2 : ℝ) ^ (r + 1) * (B + m + (r + 1)) ^ d ≤
      2 ^ (d + 5) * d.factorial * (1 / 2) ^ m * H * (B + m + 1) ^ d := by
  set Q : ℝ := B + m + 1 with hQ
  have hQ1 : 1 ≤ Q := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hle : ∀ r : ℕ, (1 / 2 : ℝ) ^ (r + 1) * (B + m + (r + 1)) ^ d ≤
      (1 / 2) * (Q ^ d * (((r : ℝ) + 1) ^ d * (1 / 2) ^ r)) := by
    intro r
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have h1 : B + m + (r + 1) ≤ Q * (r + 1) := by nlinarith
    have h2 : (B + m + (r + 1)) ^ d ≤ (Q * (r + 1)) ^ d :=
      pow_le_pow_left₀ (by positivity) h1 d
    rw [mul_pow] at h2
    have h3 : (0 : ℝ) ≤ (1 / 2) ^ r := by positivity
    rw [pow_succ]
    nlinarith
  have hs2 : Summable (fun r : ℕ => (1 / 2 : ℝ) * (Q ^ d * (((r : ℝ) + 1) ^ d *
      (1 / 2) ^ r))) := ((summable_pow_mul_half d).mul_left _).mul_left _
  have hs : Summable (fun r : ℕ => (1 / 2 : ℝ) ^ (r + 1) * (B + m + (r + 1)) ^ d) :=
    Summable.of_nonneg_of_le (fun r => by positivity) hle hs2
  have hsum : ∑' r : ℕ, (1 / 2 : ℝ) ^ (r + 1) * (B + m + (r + 1)) ^ d ≤
      (1 / 2) * (Q ^ d * (d.factorial * 2 ^ (d + 1))) := by
    calc ∑' r : ℕ, (1 / 2 : ℝ) ^ (r + 1) * (B + m + (r + 1)) ^ d
        ≤ ∑' r : ℕ, (1 / 2 : ℝ) * (Q ^ d * (((r : ℝ) + 1) ^ d * (1 / 2) ^ r)) :=
          Summable.tsum_le_tsum hle hs hs2
      _ = (1 / 2) * (Q ^ d * ∑' r : ℕ, ((r : ℝ) + 1) ^ d * (1 / 2) ^ r) := by
          rw [tsum_mul_left, tsum_mul_left]
      _ ≤ (1 / 2) * (Q ^ d * (d.factorial * 2 ^ (d + 1))) := by
          gcongr
          exact tsum_pow_mul_half_le d
  have hpre : 0 ≤ 8 * (1 / 2 : ℝ) ^ m * H := by positivity
  calc 8 * (1 / 2) ^ m * H *
        ∑' r : ℕ, (1 / 2 : ℝ) ^ (r + 1) * (B + m + (r + 1)) ^ d
      ≤ 8 * (1 / 2) ^ m * H * ((1 / 2) * (Q ^ d * (d.factorial * 2 ^ (d + 1)))) :=
        mul_le_mul_of_nonneg_left hsum hpre
    _ = 2 ^ (d + 3) * d.factorial * (1 / 2) ^ m * H * Q ^ d := by ring
    _ ≤ 2 ^ (d + 5) * d.factorial * (1 / 2) ^ m * H * Q ^ d := by
        have : (2 : ℝ) ^ (d + 3) ≤ 2 ^ (d + 5) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have h0 : 0 ≤ (d.factorial : ℝ) * (1 / 2) ^ m * H * Q ^ d := by positivity
        nlinarith

/-! ## Comparison of a uniform expansion with certified intervals -/

/-- The left endpoint of the length-`2^{-t}` dyadic cell that contains `U`. -/
noncomputable def cellLow (t : ℕ) (U : ℝ) : ℝ := ⌊U * 2 ^ t⌋ / 2 ^ t

/-- Auxiliary for `lem:newprecisionstop`: the dyadic cell contains `U`. -/
theorem cellLow_le (t : ℕ) (U : ℝ) : cellLow t U ≤ U := by
  unfold cellLow
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

/-- Auxiliary for `lem:newprecisionstop`: the dyadic cell has length `2^{-t}`. -/
theorem lt_cellLow_add (t : ℕ) (U : ℝ) : U < cellLow t U + (1 / 2) ^ t := by
  unfold cellLow
  have h := Int.lt_floor_add_one (U * 2 ^ t)
  have h2 : (0 : ℝ) < 2 ^ t := by positivity
  have he : (⌊U * 2 ^ t⌋ : ℝ) / 2 ^ t + (1 / 2) ^ t =
      ((⌊U * 2 ^ t⌋ : ℝ) + 1) / 2 ^ t := by
    rw [one_div_pow, add_div]
  rw [he, lt_div_iff₀ h2]
  exact h

/-- Auxiliary for `lem:newprecisionstop`: measurability of the cell endpoint. -/
theorem measurable_cellLow (t : ℕ) : Measurable (cellLow t) := by
  unfold cellLow
  have h : Measurable (fun U : ℝ => ⌊U * 2 ^ t⌋) :=
    Int.measurable_floor.comp (measurable_id.mul_const _)
  exact (measurable_from_top.comp h).div_const _

/-- Stage `t` is undecided when the closed dyadic cell of `U` meets the
certified interval `[lo t, hi t]`. -/
def Undecided (lo hi : ℕ → ℝ) (t : ℕ) (U : ℝ) : Prop :=
  lo t ≤ cellLow t U + (1 / 2) ^ t ∧ cellLow t U ≤ hi t

/-- Auxiliary for `lem:newprecisionstop`: the undecided events are measurable. -/
theorem measurableSet_undecided (lo hi : ℕ → ℝ) (t : ℕ) :
    MeasurableSet {U : ℝ | Undecided lo hi t U} := by
  have h := measurable_cellLow t
  exact (measurableSet_le measurable_const (h.add_const _)).inter
    (measurableSet_le h measurable_const)

/-- Paper: `lem:newprecisionstop` (attention_finite_bits.tex), "every decision
agrees with the comparison against `p`". When stage `t` is decided, the cell lies
entirely below or entirely above the certified interval, and the returned bit
"cell below the interval" is exactly `1{U < p}`. -/
theorem decided_bit_eq (lo hi : ℕ → ℝ) (p : ℝ) (t : ℕ) (U : ℝ)
    (hlo : lo t ≤ p) (hhi : p ≤ hi t) (hU : ¬ Undecided lo hi t U) :
    (cellLow t U + (1 / 2) ^ t < lo t ↔ U < p) := by
  have h1 := cellLow_le t U
  have h2 := lt_cellLow_add t U
  have hw : (0 : ℝ) < (1 / 2) ^ t := by positivity
  unfold Undecided at hU
  rw [not_and_or, not_le, not_le] at hU
  rcases hU with h | h
  · exact ⟨fun _ => by linarith, fun _ => h⟩
  · constructor
    · intro h'
      linarith
    · intro h'
      linarith

/-- Paper: `lem:newprecisionstop` (attention_finite_bits.tex) and `lem:lazy`
(tanh_bits.tex): if the intervals overlap at stage `t`, then
`|U - p| ≤ 2^{1-t}`. -/
theorem undecided_abs_sub_le (lo hi : ℕ → ℝ) (p : ℝ) (t : ℕ) (U : ℝ)
    (hlo : lo t ≤ p) (hhi : p ≤ hi t) (hw : hi t - lo t ≤ (1 / 2) ^ t)
    (hU : Undecided lo hi t U) : |U - p| ≤ 2 * (1 / 2) ^ t := by
  obtain ⟨ha, hb⟩ := hU
  have h1 := cellLow_le t U
  have h2 := lt_cellLow_add t U
  rw [abs_le]
  constructor <;> linarith

/-- Paper: `lem:newprecisionstop` (attention_finite_bits.tex), "the overlap
event has probability at most `2^{2-t}`"; here `4 (1/2)^t = 2^{2-t}`. The bound
holds for Lebesgue measure on the line, hence for a uniform `U` on `[0, 1]`. -/
theorem volume_undecided_le (lo hi : ℕ → ℝ) (p : ℝ) (t : ℕ)
    (hlo : lo t ≤ p) (hhi : p ≤ hi t) (hw : hi t - lo t ≤ (1 / 2) ^ t) :
    volume {U : ℝ | Undecided lo hi t U} ≤ ENNReal.ofReal (4 * (1 / 2) ^ t) := by
  calc volume {U : ℝ | Undecided lo hi t U}
      ≤ volume (Icc (p - 2 * (1 / 2) ^ t) (p + 2 * (1 / 2) ^ t)) := by
        refine measure_mono fun U hU => ?_
        have h := undecided_abs_sub_le lo hi p t U hlo hhi hw hU
        rw [abs_le] at h
        exact ⟨by linarith, by linarith⟩
    _ = ENNReal.ofReal (4 * (1 / 2) ^ t) := by
        rw [Real.volume_Icc]
        ring_nf

/-- Stage `n` (which uses precision `n + 1`) is performed when stages
`1, ..., n` were all undecided. -/
def Performed (lo hi : ℕ → ℝ) (n : ℕ) (U : ℝ) : Prop :=
  ∀ k < n, Undecided lo hi (k + 1) U

/-- Auxiliary for `lem:newprecisionstop`: the events of reaching a stage are
measurable. -/
theorem measurableSet_performed (lo hi : ℕ → ℝ) (n : ℕ) :
    MeasurableSet {U : ℝ | Performed lo hi n U} := by
  have : {U : ℝ | Performed lo hi n U} =
      ⋂ k ∈ Finset.range n, {U : ℝ | Undecided lo hi (k + 1) U} := by
    ext U
    simp [Performed]
  rw [this]
  exact Finset.measurableSet_biInter _ fun k _ => measurableSet_undecided lo hi (k + 1)

/-- Paper: `lem:newprecisionstop` (attention_finite_bits.tex) and `lem:lazy`
(tanh_bits.tex): "their intersection can persist forever only when `U = p`, an
event of probability zero". The nontermination event of the comparison, on which
every stage is performed, has probability zero; this includes `p` dyadic or equal
to `0` or `1`. -/
theorem volume_never_terminates (lo hi : ℕ → ℝ) (p : ℝ) (hlo : ∀ t, lo t ≤ p)
    (hhi : ∀ t, p ≤ hi t) (hw : ∀ t, hi t - lo t ≤ (1 / 2) ^ t) :
    volume {U : ℝ | ∀ n, Performed lo hi n U} = 0 := by
  refine measure_mono_null (t := {p}) (fun U hU => ?_) (Real.volume_singleton)
  have hlim : Tendsto (fun t : ℕ => 2 * (1 / 2 : ℝ) ^ (t + 1)) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul 2
    have h2 := this.comp (tendsto_add_atTop_nat 1)
    rw [mul_zero] at h2
    exact h2
  have hle : |U - p| ≤ 0 := ge_of_tendsto' hlim fun t =>
    undecided_abs_sub_le lo hi p (t + 1) U (hlo _) (hhi _) (hw _)
      (hU (t + 1) t (Nat.lt_succ_self t))
  have h0 : U - p = 0 := abs_nonpos_iff.mp hle
  simp only [mem_singleton_iff]
  linarith

/-- Auxiliary for `lem:newprecisionstop`: the probability that stage `n` is
performed is at most `4 (1/2)^n`, for a uniform `U` on `[0, 1]`. -/
theorem uniform_performed_le (lo hi : ℕ → ℝ) (p : ℝ) (hlo : ∀ t, lo t ≤ p)
    (hhi : ∀ t, p ≤ hi t) (hw : ∀ t, hi t - lo t ≤ (1 / 2) ^ t) (n : ℕ) :
    (volume.restrict (Icc (0 : ℝ) 1)) {U : ℝ | Performed lo hi n U} ≤
      ENNReal.ofReal (4 * (1 / 2) ^ n) := by
  cases n with
  | zero =>
      calc (volume.restrict (Icc (0 : ℝ) 1)) {U : ℝ | Performed lo hi 0 U}
          ≤ (volume.restrict (Icc (0 : ℝ) 1)) univ := measure_mono (subset_univ _)
        _ = 1 := by simp
        _ ≤ ENNReal.ofReal (4 * (1 / 2) ^ 0) := by norm_num
  | succ k =>
      calc (volume.restrict (Icc (0 : ℝ) 1)) {U : ℝ | Performed lo hi (k + 1) U}
          ≤ volume {U : ℝ | Performed lo hi (k + 1) U} :=
            Measure.restrict_le_self _
        _ ≤ volume {U : ℝ | Undecided lo hi (k + 1) U} :=
            measure_mono fun U hU => hU k (Nat.lt_succ_self k)
        _ ≤ ENNReal.ofReal (4 * (1 / 2) ^ (k + 1)) :=
            volume_undecided_le lo hi p (k + 1) (hlo _) (hhi _) (hw _)

/-- Auxiliary for `lem:newprecisionstop`: the real stage-cost sum
`∑_n 4 C (B+n+1)^d 2^{-n} ≤ 2^{d+3} d! C (B+1)^d`. -/
theorem stage_cost_tsum_le (C B : ℝ) (d : ℕ) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    Summable (fun n : ℕ => C * (B + n + 1) ^ d * (4 * (1 / 2) ^ n)) ∧
      ∑' n : ℕ, C * (B + n + 1) ^ d * (4 * (1 / 2) ^ n) ≤
        2 ^ (d + 3) * d.factorial * C * (B + 1) ^ d := by
  have hle : ∀ n : ℕ, C * (B + n + 1) ^ d * (4 * (1 / 2) ^ n) ≤
      4 * C * (B + 1) ^ d * (((n : ℝ) + 1) ^ d * (1 / 2) ^ n) := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : B + n + 1 ≤ (B + 1) * (n + 1) := by nlinarith
    have h2 : (B + n + 1) ^ d ≤ ((B + 1) * (n + 1)) ^ d :=
      pow_le_pow_left₀ (by positivity) h1 d
    rw [mul_pow] at h2
    have h3 : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
    have h4 : 0 ≤ C * (1 / 2) ^ n := by positivity
    nlinarith
  have hs2 := (summable_pow_mul_half d).mul_left (4 * C * (B + 1) ^ d)
  have hs : Summable (fun n : ℕ => C * (B + n + 1) ^ d * (4 * (1 / 2) ^ n)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hle hs2
  refine ⟨hs, ?_⟩
  calc ∑' n : ℕ, C * (B + n + 1) ^ d * (4 * (1 / 2) ^ n)
      ≤ ∑' n : ℕ, 4 * C * (B + 1) ^ d * (((n : ℝ) + 1) ^ d * (1 / 2) ^ n) :=
        Summable.tsum_le_tsum hle hs hs2
    _ = 4 * C * (B + 1) ^ d * ∑' n : ℕ, ((n : ℝ) + 1) ^ d * (1 / 2) ^ n :=
        tsum_mul_left
    _ ≤ 4 * C * (B + 1) ^ d * (d.factorial * 2 ^ (d + 1)) :=
        mul_le_mul_of_nonneg_left (tsum_pow_mul_half_le d) (by positivity)
    _ = 2 ^ (d + 3) * d.factorial * C * (B + 1) ^ d := by ring

/-- Paper: `lem:newprecisionstop` (attention_finite_bits.tex), the expected-work
bound. Let `U` be uniform on `[0, 1]` and let stage `n` (precision `n + 1`) cost
at most `C (B+n+1)^d`. The expected total cost of the performed stages is at most
`2^{d+5} d! C (B+1)^d`; the proof gives the factor `2^{d+3}`. Tonelli's theorem
sums the stage costs against the probabilities of reaching them; no finite
expected stopping time is assumed. -/
theorem precision_stop_expected_work (lo hi : ℕ → ℝ) (p : ℝ)
    (hlo : ∀ t, lo t ≤ p) (hhi : ∀ t, p ≤ hi t)
    (hw : ∀ t, hi t - lo t ≤ (1 / 2) ^ t) (C B : ℝ) (d : ℕ) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (cost : ℕ → ℝ≥0∞)
    (hcost : ∀ n, cost n ≤ ENNReal.ofReal (C * (B + n + 1) ^ d)) :
    ∫⁻ U, ∑' n, Set.indicator {U | Performed lo hi n U} (fun _ => cost n) U
        ∂(volume.restrict (Icc (0 : ℝ) 1)) ≤
      ENNReal.ofReal (2 ^ (d + 5) * d.factorial * C * (B + 1) ^ d) := by
  set μ := volume.restrict (Icc (0 : ℝ) 1)
  obtain ⟨hs, hsum⟩ := stage_cost_tsum_le C B d hC hB
  rw [lintegral_tsum fun n =>
    (measurable_const.indicator (measurableSet_performed lo hi n)).aemeasurable]
  calc ∑' n, ∫⁻ U, Set.indicator {U | Performed lo hi n U} (fun _ => cost n) U ∂μ
      = ∑' n, cost n * μ {U | Performed lo hi n U} := by
        refine tsum_congr fun n => ?_
        rw [lintegral_indicator (measurableSet_performed lo hi n), setLIntegral_const]
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (C * (B + n + 1) ^ d * (4 * (1 / 2) ^ n)) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        rw [ENNReal.ofReal_mul (by positivity)]
        exact mul_le_mul' (hcost n) (uniform_performed_le lo hi p hlo hhi hw n)
    _ = ENNReal.ofReal (∑' n : ℕ, C * (B + n + 1) ^ d * (4 * (1 / 2) ^ n)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs).symm
    _ ≤ ENNReal.ofReal (2 ^ (d + 5) * d.factorial * C * (B + 1) ^ d) := by
        refine ENNReal.ofReal_le_ofReal (hsum.trans ?_)
        have : (2 : ℝ) ^ (d + 3) ≤ 2 ^ (d + 5) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have h0 : 0 ≤ (d.factorial : ℝ) * C * (B + 1) ^ d := by positivity
        nlinarith

/-- Paper: `eq:conf-tail` (conference.tex): the union bound over finitely many
boundaries. If an undecided comparison puts `U` within `ε` of one of the
boundaries `b i`, `i ∈ s`, that event has probability at most `|s| 2ε`; with
`V - 1` boundaries and `ε = 2^{1-p}` this is at most `4 V 2^{-p}`. -/
theorem volume_near_finset_le {ι : Type*} (s : Finset ι) (b : ι → ℝ) (ε : ℝ) :
    volume {U : ℝ | ∃ i ∈ s, |U - b i| ≤ ε} ≤ s.card * ENNReal.ofReal (2 * ε) := by
  calc volume {U : ℝ | ∃ i ∈ s, |U - b i| ≤ ε}
      ≤ volume (⋃ i ∈ s, Icc (b i - ε) (b i + ε)) := by
        refine measure_mono fun U hU => ?_
        obtain ⟨i, hi, h⟩ := hU
        rw [abs_le] at h
        exact mem_biUnion hi ⟨by linarith, by linarith⟩
    _ ≤ ∑ i ∈ s, volume (Icc (b i - ε) (b i + ε)) := measure_biUnion_finset_le _ _
    _ = s.card * ENNReal.ofReal (2 * ε) := by
        have h : ∀ i, volume (Icc (b i - ε) (b i + ε)) = ENNReal.ofReal (2 * ε) :=
          fun i => by
            rw [Real.volume_Icc]
            ring_nf
        simp only [h, Finset.sum_const, nsmul_eq_mul]

/-! ## Predictable charging -/

/-- Paper: `lem:stopping` (tanh_scalar.tex), "reaching trial `j` is determined
before its fresh randomness". Write the sample space as a history `H` times a fresh
tape `W` with law `ν`. If the reaching event depends on the history only and the
trial cost has conditional mean at most `B` given every reaching history, then the
cost on the reaching event has mean at most `B` times its probability. This is the
charging hypothesis of the stopped-work theorem. -/
theorem predictable_charge {H W : Type*} [MeasurableSpace H] [MeasurableSpace W]
    (μ : Measure H) (ν : Measure W) [SFinite μ] [IsProbabilityMeasure ν]
    (S : Set H) (hS : MeasurableSet S) (c : H × W → ℝ≥0∞) (hc : Measurable c)
    (B : ℝ≥0∞) (hfresh : ∀ h ∈ S, ∫⁻ w, c (h, w) ∂ν ≤ B) :
    ∫⁻ x in S ×ˢ univ, c x ∂(μ.prod ν) ≤ B * (μ.prod ν) (S ×ˢ univ) := by
  rw [← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod _ hc.aemeasurable, Measure.prod_prod, measure_univ, mul_one]
  calc ∫⁻ h, ∫⁻ w, c (h, w) ∂ν ∂(μ.restrict S)
      ≤ ∫⁻ _h, B ∂(μ.restrict S) := by
        refine lintegral_mono_ae ?_
        exact (ae_restrict_iff' hS).mpr (Eventually.of_forall hfresh)
    _ = B * μ S := by rw [lintegral_const, Measure.restrict_apply_univ]

/-- Paper: `lem:stopping` (tanh_scalar.tex), the last step of `E T = 1/σ` for
independent trials: the survival probabilities `P(T > j) = (1 - σ)^j` sum to `1/σ`.
Only this geometric series is proved; the survival law of independent trials is
not formalized. -/
theorem tsum_survival_geometric (σ : ℝ≥0∞) (hσ : σ ≤ 1) :
    ∑' j : ℕ, (1 - σ) ^ j = σ⁻¹ := by
  rw [ENNReal.tsum_geometric, ENNReal.sub_sub_cancel ENNReal.one_ne_top hσ]

end ExactSampling.StoppedCost
