import Mathlib

/-!
# Score orders on an affine line

This module formalizes the order steps of the exact index for a cache on one affine line,
`thm:newrankone` (`attention_rank_one.tex`), which is reused by `cor:dynamicrankone`
(`attention_dynamic_index.tex`):
* the affine-line verification identity and the reconstruction `k_j = c + ξ_j u` with
  `ξ_j = (k_{j,r} - c_r)/u_r`;
* the shift `a_j - a_1 = βv(ξ_j - ξ_1)/n`, computed from the single projection `v = ⟨q,u⟩`;
* the order selection: with the keys sorted by their pivot coordinate `k_{j,r}`, the sign of
  `v/u_r` decides whether the stored permutation is used forward or reversed (all scores coincide
  when `v = 0`), and a nonnegative temperature does not change this order.

Not formalized: sorting, the stored permutation and its bit costs, and the dyadic envelope on the
sorted keys (the envelope bounds are in `ExactSampling.DynamicIndex`).
-/

open Finset Filter
open scoped BigOperators Topology

namespace ExactSampling.FixedRank

/-! ## The affine line (`thm:newrankone`) -/

section RankOne

/-- Affine-line verification: with pivot `u_r ≠ 0`, the key `k` lies on the line `c + ℝu` iff
`u_r (k_i - c_i) = u_i (k_r - c_r)` for every coordinate `i`; then `k = c + ξu` with
`ξ = (k_r - c_r)/u_r`. Paper: `thm:newrankone` (attention_rank_one.tex). -/
theorem affine_line_test {n : ℕ} (c u k : Fin n → ℝ) (r : Fin n) (hr : u r ≠ 0) :
    (∀ i, u r * (k i - c i) = u i * (k r - c r)) ↔ ∃ ξ : ℝ, ∀ i, k i = c i + ξ * u i := by
  constructor
  · intro h
    refine ⟨(k r - c r) / u r, fun i => ?_⟩
    have := h i
    field_simp
    linarith
  · rintro ⟨ξ, hξ⟩ i
    rw [hξ i, hξ r]; ring

/-- The score shift on a line: with `k_j = c + ξ_j u` and `v = ⟨q,u⟩`, the score difference is
`a_j - a_1 = βv(ξ_j - ξ_1)/n`, computed from the single projection `v`.
Paper: `thm:newrankone` (attention_rank_one.tex). -/
theorem line_score_shift {n : ℕ} (q c u : Fin n → ℝ) (β ξj ξ1 : ℝ) :
    β / n * ∑ i, q i * (c i + ξj * u i) - β / n * ∑ i, q i * (c i + ξ1 * u i) =
      β * (∑ i, q i * u i) * (ξj - ξ1) / n := by
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have : ∀ i, q i * (c i + ξj * u i) - q i * (c i + ξ1 * u i) = (ξj - ξ1) * (q i * u i) := by
    intro i; ring
  simp_rw [this]
  rw [← Finset.mul_sum]
  ring

/-- The sign of `v/u_r` selects the direction of the stored pivot order. For keys
`k_j = c + ξ_j u` on the line with pivot `u_r ≠ 0`, the scores `a_j = (β/n)⟨q, k_j⟩` satisfy
`a_j - a_l = (β/n)(v/u_r)(k_{j,r} - k_{l,r})` with `v = ⟨q,u⟩`. Hence, for `β ≥ 0`, if
`v/u_r ≥ 0` the scores are nondecreasing along the order of the pivot coordinates (the stored
permutation read in reverse is descending), if `v/u_r ≤ 0` they are nonincreasing (the stored
permutation is descending), and if `v = 0` all scores coincide.
Paper: `thm:newrankone` (attention_rank_one.tex), "compute `v = ⟨q,u⟩` once and the sign of
`v/u_r`. It determines the order of all projected keys". -/
theorem pivot_order_direction {n : ℕ} (hn : 0 < n) (q c u : Fin n → ℝ) (r : Fin n)
    (hr : u r ≠ 0) (β ξj ξl : ℝ) (hβ : 0 ≤ β) :
    let v := ∑ i, q i * u i
    let a : ℝ → ℝ := fun ξ => β / n * ∑ i, q i * (c i + ξ * u i)
    let kr : ℝ → ℝ := fun ξ => c r + ξ * u r
    a ξj - a ξl = β / n * (v / u r) * (kr ξj - kr ξl) ∧
      (0 ≤ v / u r → kr ξj ≤ kr ξl → a ξj ≤ a ξl) ∧
      (v / u r ≤ 0 → kr ξj ≤ kr ξl → a ξl ≤ a ξj) ∧
      (v = 0 → a ξj = a ξl) := by
  intro v a kr
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hid : a ξj - a ξl = β / n * (v / u r) * (kr ξj - kr ξl) := by
    have h := line_score_shift q c u β ξj ξl
    simp only [a, kr]
    rw [h]
    field_simp
    ring
  have hc : 0 ≤ β / n := div_nonneg hβ hnpos.le
  refine ⟨hid, fun hv h => ?_, fun hv h => ?_, fun hv => ?_⟩
  · have : 0 ≤ β / n * (v / u r) * (kr ξl - kr ξj) :=
      mul_nonneg (mul_nonneg hc hv) (by linarith)
    nlinarith
  · have : β / n * (v / u r) * (kr ξl - kr ξj) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hc hv) (by linarith)
    nlinarith
  · have : a ξj - a ξl = 0 := by rw [hid]; simp [v] at hv ⊢; simp [hv]
    linarith

/-- Nonnegative temperature preserves the descending key order.
Paper: `thm:newrankone` (attention_rank_one.tex), "These bounds hold at every numerical
temperature". -/
theorem scale_preserves_order {a b c t : ℝ} (ht : 0 ≤ t) (hab : b ≤ a) :
    c + t * b ≤ c + t * a := by
  have := mul_le_mul_of_nonneg_left hab ht
  linarith

end RankOne

end ExactSampling.FixedRank
