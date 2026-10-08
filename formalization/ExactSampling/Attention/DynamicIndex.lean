import Mathlib

/-!
# Appendable fixed-rank attention: envelopes, grids, and charts

This module formalizes the quantitative steps behind the appendable fixed-rank attention index
of `attention_dynamic_index.tex` (`thm:dynamicfixedrank`, restated in `main_attention.tex` as
`thm:main-fixed-rank`) and the monotone envelope of `attention_rank_one.tex`
(`lem:newmonotoneenvelope`, used in `thm:newrankone` and `cor:dynamicrankone`).

Formalized here:
* `lem:dynamiccellenvelope`: the member and cell weights, `Z ≤ W₀ < 2Z`, `Z > 1/2`, the
  dyadic rounding of an enclosure into an envelope weight, `Z ≤ W < 2Z + 3/64`,
  `W < (67/32) Z < (17/8) Z`, the accepted mass `w_j / W` of one trial, the exact output law of
  repeated trials (as a geometric series), and the expected proposal count `W / Z < 17/8`.
* `lem:newmonotoneenvelope`: for decreasing positive weights and the geometric blocks
  `{1}, {2}, {3,4}, {5,…,8}, …`, the envelope satisfies `Z ≤ W ≤ 2Z`; with the dyadic
  floors of `thm:newrankone` the rounded envelope is at most `(17/8) Z`.
* `thm:dynamicfixedrank`: projected coefficients `|v_i| ≤ 2nQ`, the within-cell score
  variation `≤ 1/4`, the range of integer cell indices, the count `2^(m+1)+1 ≤ 5 + 32 r β̄ Q K`,
  the cell-tuple count per epoch, and the assembled occupied-cell bound
  `M_T ≤ min{T, (r+1)(5 + 32 r β̄ Q K)^r}` (`occupied_cell_bound`).
* `lem:dynamicchart`: the row-replacement determinant identity, the doubling argument bounding
  the number of replacements, Hadamard's crude bound `d! H^d`, and the chart identities
  `A_I = I_d`, `k = c₀ + A k_I` for a given nonsingular selection.
* `cor:dynamicapproximatespace`: the split of the score allowance and its cell bound.
* `lem:newnegativeexp`: the immediate enclosure of very negative arguments, the `1`-Lipschitz
  bound of `exp` on the negative half-line, and the alternating remainder `1/(K+1)! ≤ 2^{-K}`.
* Almost-sure stopping and the predictable-charging (Tonelli) bound for stopped work.

Not formalized here: the data structures (search trees, appendable arrays) and their bit costs,
the bit-complexity model, and the fixed-point error propagation of the negative-exponential
routine (`lem:newnegativeexp`). In this module the sampler's exactness is stated as identities of
the corresponding series of probabilities, and the charging step for an abstract measure with
explicit hypotheses.

Stronger forms elsewhere in the library: the probability space of the cell sampler, with
independent trials and the first-success law, is `ExactSampling.GridIndex.rejection_sampler_iid`
(built on `ExactSampling.RejectionLoop.first_success_law`); the existence of a chart with
`|A_ij| ≤ 2` is `ExactSampling.Chart.exists_bounded_chart`.
-/

open MeasureTheory Filter Finset
open scoped BigOperators ENNReal Topology

namespace ExactSampling.DynamicIndex

/-! ## The finite cell envelope (`lem:dynamiccellenvelope`) -/

section CellEnvelope

variable {ι κ : Type*}

/-- Ideal member weight `w_j = exp(a_j - a₀ - 1/4)`.
Paper: `lem:dynamiccellenvelope` (attention_dynamic_index.tex). -/
noncomputable def memberWeight (a : ι → ℝ) (a0 : ℝ) (j : ι) : ℝ := Real.exp (a j - a0 - 1 / 4)

/-- Ideal cell weight `e_C = exp(a_C - a₀)`.
Paper: `lem:dynamiccellenvelope` (attention_dynamic_index.tex). -/
noncomputable def cellWeight (aC : κ → ℝ) (a0 : ℝ) (C : κ) : ℝ := Real.exp (aC C - a0)

/-- Auxiliary: `e^{1/2} < 2`. Supports the proof of `lem:dynamiccellenvelope`
(attention_dynamic_index.tex). -/
lemma exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h := Real.add_one_lt_exp (show (-(1 / 2 : ℝ)) ≠ 0 by norm_num)
  have hpos := Real.exp_pos (1 / 2 : ℝ)
  have hmul : Real.exp (-(1 / 2)) * Real.exp (1 / 2) = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith

/-- Auxiliary: `e^{-1/2} > 1/2`. Supports the proof of `lem:dynamiccellenvelope`
(attention_dynamic_index.tex). -/
lemma half_lt_exp_neg_half : (1 / 2 : ℝ) < Real.exp (-(1 / 2)) := by
  have h := Real.add_one_lt_exp (show (-(1 / 2 : ℝ)) ≠ 0 by norm_num)
  linarith

/-- For a member of cell `C`, `w_j ≤ e_C ≤ e^{1/2} w_j < 2 w_j`.
Paper: `lem:dynamiccellenvelope` (attention_dynamic_index.tex), first display of the proof. -/
theorem member_cell_bounds (a : ι → ℝ) (aC : κ → ℝ) (cell : ι → κ) (a0 : ℝ)
    (hcell : ∀ j, |a j - aC (cell j)| ≤ 1 / 4) (j : ι) :
    memberWeight a a0 j ≤ cellWeight aC a0 (cell j) ∧
      cellWeight aC a0 (cell j) ≤ Real.exp (1 / 2) * memberWeight a a0 j ∧
      Real.exp (1 / 2) * memberWeight a a0 j < 2 * memberWeight a a0 j := by
  have h := abs_le.mp (hcell j)
  refine ⟨?_, ?_, ?_⟩
  · unfold memberWeight cellWeight
    exact Real.exp_le_exp.mpr (by linarith)
  · unfold memberWeight cellWeight
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  · have hw : 0 < memberWeight a a0 j := Real.exp_pos _
    nlinarith [exp_half_lt_two]

/-- Every defining exponent is nonpositive: `w_j ≤ 1` and `e_C ≤ 1` when `a₀` is the largest
proxy. Paper: `lem:dynamiccellenvelope` (attention_dynamic_index.tex). -/
theorem weights_le_one (a : ι → ℝ) (aC : κ → ℝ) (cell : ι → κ) (a0 : ℝ)
    (hcell : ∀ j, |a j - aC (cell j)| ≤ 1 / 4) (hmax : ∀ j, aC (cell j) ≤ a0) (j : ι) :
    memberWeight a a0 j ≤ 1 ∧ cellWeight aC a0 (cell j) ≤ 1 := by
  have h := abs_le.mp (hcell j)
  have h2 := hmax j
  constructor
  · unfold memberWeight; exact Real.exp_le_one_iff.mpr (by linarith)
  · unfold cellWeight; exact Real.exp_le_one_iff.mpr (by linarith)

/-- The ideal envelope satisfies `Z ≤ W₀ < 2Z`, where `W₀ = ∑_C |C| e_C = ∑_j e_{C(j)}`.
Paper: `lem:dynamiccellenvelope` (attention_dynamic_index.tex). -/
theorem ideal_envelope_bounds [Fintype ι] [Nonempty ι] (a : ι → ℝ) (aC : κ → ℝ) (cell : ι → κ)
    (a0 : ℝ)
    (hcell : ∀ j, |a j - aC (cell j)| ≤ 1 / 4) :
    ∑ j, memberWeight a a0 j ≤ ∑ j, cellWeight aC a0 (cell j) ∧
      ∑ j, cellWeight aC a0 (cell j) < 2 * ∑ j, memberWeight a a0 j := by
  constructor
  · exact Finset.sum_le_sum fun j _ => (member_cell_bounds a aC cell a0 hcell j).1
  · rw [Finset.mul_sum]
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro j _
    obtain ⟨_, h2, h3⟩ := member_cell_bounds a aC cell a0 hcell j
    linarith

/-- A member of a cell whose proxy equals the maximum `a₀` has weight above `1/2`, hence
`Z > 1/2`. Paper: `lem:dynamiccellenvelope` (attention_dynamic_index.tex). -/
theorem total_weight_gt_half [Fintype ι] (a : ι → ℝ) (aC : κ → ℝ) (cell : ι → κ) (a0 : ℝ)
    (hcell : ∀ j, |a j - aC (cell j)| ≤ 1 / 4) (j0 : ι) (hj0 : aC (cell j0) = a0) :
    (1 / 2 : ℝ) < ∑ j, memberWeight a a0 j := by
  have hj := abs_le.mp (hcell j0)
  have h1 : (1 / 2 : ℝ) < memberWeight a a0 j0 := by
    unfold memberWeight
    calc (1 / 2 : ℝ) < Real.exp (-(1 / 2)) := half_lt_exp_neg_half
      _ ≤ Real.exp (a j0 - a0 - 1 / 4) := Real.exp_le_exp.mpr (by linarith)
  calc (1 / 2 : ℝ) < memberWeight a a0 j0 := h1
    _ ≤ ∑ j, memberWeight a a0 j :=
      Finset.single_le_sum (f := fun j => memberWeight a a0 j)
        (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ j0)

/-- Dyadic envelope weight from an enclosure: if `lo ≤ e ≤ hi`, `hi - lo ≤ 2^{-p-2}`, and
`e > 0`, then `u = (⌈2^p hi⌉ + 1) / 2^p` is a dyadic number on the grid `2^{-p}` with
`2^{-p} ≤ u` and `e ≤ u ≤ e + 3·2^{-p}`.
Paper: `lem:dynamiccellenvelope` (attention_dynamic_index.tex), the rounding step. -/
theorem dyadic_envelope_weight (e lo hi : ℝ) (p : ℕ) (he : 0 < e) (hlo : lo ≤ e)
    (hhi : e ≤ hi) (hw : hi - lo ≤ (2 : ℝ)⁻¹ ^ (p + 2)) :
    let u := ((⌈hi * 2 ^ p⌉ : ℝ) + 1) / 2 ^ p
    (2 : ℝ)⁻¹ ^ p ≤ u ∧ e ≤ u ∧ u ≤ e + 3 * (2 : ℝ)⁻¹ ^ p := by
  intro u
  have h2p : (0 : ℝ) < 2 ^ p := by positivity
  have hinv : (2 : ℝ)⁻¹ ^ p = 1 / 2 ^ p := by rw [inv_pow, one_div]
  have hceil1 : hi * 2 ^ p ≤ (⌈hi * 2 ^ p⌉ : ℝ) := Int.le_ceil _
  have hceil2 : (⌈hi * 2 ^ p⌉ : ℝ) < hi * 2 ^ p + 1 := Int.ceil_lt_add_one _
  have hhi0 : 0 ≤ hi * 2 ^ p := mul_nonneg (by linarith) h2p.le
  have hw' : hi - e ≤ (1 / 4) * (1 / 2 ^ p) := by
    have : (2 : ℝ)⁻¹ ^ (p + 2) = (1 / 4) * (1 / 2 ^ p) := by
      rw [pow_add, inv_pow, inv_pow]; norm_num; ring
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hinv]
    show 1 / 2 ^ p ≤ ((⌈hi * 2 ^ p⌉ : ℝ) + 1) / 2 ^ p
    apply div_le_div_of_nonneg_right _ h2p.le
    linarith
  · show e ≤ ((⌈hi * 2 ^ p⌉ : ℝ) + 1) / 2 ^ p
    rw [le_div_iff₀ h2p]
    nlinarith
  · show ((⌈hi * 2 ^ p⌉ : ℝ) + 1) / 2 ^ p ≤ e + 3 * (2 : ℝ)⁻¹ ^ p
    rw [hinv, div_le_iff₀ h2p]
    have : (hi - e) * 2 ^ p ≤ 1 / 4 := by
      have := mul_le_mul_of_nonneg_right hw' h2p.le
      rwa [mul_assoc, one_div_mul_cancel h2p.ne', mul_one] at this
    have h3 : (e + 3 * (1 / 2 ^ p)) * 2 ^ p = e * 2 ^ p + 3 := by
      field_simp
    rw [h3]
    nlinarith

/-- The rounded envelope satisfies `Z ≤ W < 2Z + 3/64`, `W < (67/32) Z`, and `W < (17/8) Z`,
whenever `e_C ≤ u_C ≤ e_C + 3·2^{-p}` and `64 T ≤ 2^p`.
Paper: `lem:dynamiccellenvelope` (attention_dynamic_index.tex), the displayed chain
`Z ≤ W < 2Z + 3/64 ≤ (67/32) Z < (17/8) Z`. -/
theorem rounded_envelope_bounds [Fintype ι] [Nonempty ι] (a : ι → ℝ) (aC : κ → ℝ) (cell : ι → κ)
    (a0 : ℝ) (u : κ → ℝ) (p : ℕ)
    (hcell : ∀ j, |a j - aC (cell j)| ≤ 1 / 4) (j0 : ι) (hj0 : aC (cell j0) = a0)
    (hu_lo : ∀ j, cellWeight aC a0 (cell j) ≤ u (cell j))
    (hu_hi : ∀ j, u (cell j) ≤ cellWeight aC a0 (cell j) + 3 * (2 : ℝ)⁻¹ ^ p)
    (hp : 64 * (Fintype.card ι : ℝ) ≤ 2 ^ p) :
    let Z := ∑ j, memberWeight a a0 j
    let W := ∑ j, u (cell j)
    Z ≤ W ∧ W < 2 * Z + 3 / 64 ∧ W < 67 / 32 * Z ∧ W < 17 / 8 * Z := by
  intro Z W
  obtain ⟨hZW0, hW02Z⟩ := ideal_envelope_bounds a aC cell a0 hcell
  have hZ := total_weight_gt_half a aC cell a0 hcell j0 hj0
  have hWW0 : W ≤ ∑ j, cellWeight aC a0 (cell j) + Fintype.card ι * (3 * (2 : ℝ)⁻¹ ^ p) := by
    have : W ≤ ∑ j, (cellWeight aC a0 (cell j) + 3 * (2 : ℝ)⁻¹ ^ p) :=
      Finset.sum_le_sum fun j _ => hu_hi j
    rw [Finset.sum_add_distrib] at this
    simpa using this
  have hround : (Fintype.card ι : ℝ) * (3 * (2 : ℝ)⁻¹ ^ p) ≤ 3 / 64 := by
    have h2p : (0 : ℝ) < 2 ^ p := by positivity
    rw [inv_pow]
    have : (Fintype.card ι : ℝ) * (3 * (2 ^ p)⁻¹) = 3 * (Fintype.card ι / 2 ^ p) := by ring
    rw [this]
    have : (Fintype.card ι : ℝ) / 2 ^ p ≤ 1 / 64 := by
      rw [div_le_iff₀ h2p]; linarith
    linarith
  have hZW : Z ≤ W := by
    calc Z ≤ ∑ j, cellWeight aC a0 (cell j) := hZW0
      _ ≤ W := Finset.sum_le_sum fun j _ => hu_lo j
  refine ⟨hZW, by linarith, by linarith, by linarith⟩

/-- Dyadic acceptance precision: since `u_C ≥ 2^{-p}`, an enclosure of `w_j` of width
`2^{-p-t-3}` gives an enclosure of the acceptance probability `w_j / u_C` of width `2^{-t-3}`.
Paper: `lem:dynamiccellenvelope` (attention_dynamic_index.tex), final paragraph. -/
theorem acceptance_enclosure_width (lo hi uC : ℝ) (p t : ℕ) (hu : (2 : ℝ)⁻¹ ^ p ≤ uC)
    (hw : hi - lo ≤ (2 : ℝ)⁻¹ ^ (p + t + 3)) :
    hi / uC - lo / uC ≤ (2 : ℝ)⁻¹ ^ (t + 3) := by
  have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ p := by positivity
  have huC : 0 < uC := lt_of_lt_of_le hpos hu
  rw [← sub_div, div_le_iff₀ huC]
  have : (2 : ℝ)⁻¹ ^ (p + t + 3) = (2 : ℝ)⁻¹ ^ (t + 3) * (2 : ℝ)⁻¹ ^ p := by
    rw [← pow_add]; ring_nf
  calc hi - lo ≤ (2 : ℝ)⁻¹ ^ (t + 3) * (2 : ℝ)⁻¹ ^ p := this ▸ hw
    _ ≤ (2 : ℝ)⁻¹ ^ (t + 3) * uC := by gcongr

/-- A cell proposal of probability `|C| u_C / W`, a uniform member, and the acceptance coin
`w_j / u_C` give accepted mass `w_j / W`.
Paper: `lem:dynamiccellenvelope` (attention_dynamic_index.tex), the accepted-mass display. -/
theorem accepted_member_mass (m u W w : ℝ) (hm : m ≠ 0) (hu : u ≠ 0) :
    (m * u / W) * (1 / m) * (w / u) = w / W := by
  field_simp

/-- Grouping members by cells: `∑_C |C| u_C = ∑_j u_{C(j)}`, so the cell distribution with
masses `|C| u_C / W` is normalized by the same `W`.
Paper: `lem:dynamiccellenvelope` (attention_dynamic_index.tex). -/
theorem envelope_by_cells [Fintype ι] [DecidableEq κ] (cell : ι → κ) (u : κ → ℝ) :
    ∑ C ∈ Finset.univ.image cell,
        ((Finset.univ.filter fun j => cell j = C).card : ℝ) * u C =
      ∑ j, u (cell j) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := cell) (t := Finset.univ.image cell)
    (fun j _ => Finset.mem_image_of_mem cell (Finset.mem_univ j))]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2])]
  simp

/-- Conditioning the accepted mass on success gives the target law: `(w/W)/(Z/W) = w/Z`.
Paper: `lem:dynamiccellenvelope` (attention_dynamic_index.tex). -/
theorem retry_normalization (w W Z : ℝ) (hW : W ≠ 0) (hZ : Z ≠ 0) :
    (w / W) / (Z / W) = w / Z := by
  field_simp

/-- Exactness of independent retries: if one trial accepts member `j` with probability
`w_j / W` and succeeds with probability `Z / W ∈ (0,1]`, then the probability that the first
success returns `j` is `∑_m (1 - Z/W)^m w_j / W = w_j / Z`.
Paper: `lem:dynamiccellenvelope` (attention_dynamic_index.tex); also `lem:newmonotoneenvelope`
(attention_rank_one.tex). -/
theorem retry_law (w W Z : ℝ) (hZ : 0 < Z) (hZW : Z ≤ W) :
    HasSum (fun m : ℕ => (1 - Z / W) ^ m * (w / W)) (w / Z) := by
  have hW : 0 < W := lt_of_lt_of_le hZ hZW
  have hs : 0 < Z / W := div_pos hZ hW
  have hs1 : Z / W ≤ 1 := (div_le_one hW).mpr hZW
  have hgeom := hasSum_geometric_of_lt_one (r := 1 - Z / W) (by linarith) (by linarith)
  have h := hgeom.mul_right (w / W)
  have hval : (1 - (1 - Z / W))⁻¹ * (w / W) = w / Z := by
    rw [sub_sub_cancel]; field_simp
  rwa [hval] at h

/-- The expected number of proposals of the retry loop is `1 / s = W / Z`, where `s = Z / W`
is the success probability of a trial.
Paper: `lem:dynamiccellenvelope` (attention_dynamic_index.tex); `lem:newmonotoneenvelope`
(attention_rank_one.tex). -/
theorem expected_proposals (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    HasSum (fun m : ℕ => ((m : ℝ) + 1) * (1 - s) ^ m * s) (1 / s) := by
  have hr : ‖(1 - s : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hr
  have h2 := hasSum_geometric_of_lt_one (r := 1 - s) (by linarith) (by linarith)
  have h3 := (h1.add h2).mul_right s
  have hval : ((1 - s) / (1 - (1 - s)) ^ 2 + (1 - (1 - s))⁻¹) * s = 1 / s := by
    rw [sub_sub_cancel]; field_simp; ring
  rw [hval] at h3
  convert h3 using 1
  funext m; ring

/-- Exactness of the cell sampler. Draw a cell `C` with probability `|C| u_C / W`, a uniform
member of `C`, and accept member `j` with probability `w_j / u_C`. Then one trial accepts `j`
with probability `w_j / W`, a trial succeeds with probability `Z / W`, and independent retries
return `j` with probability `w_j / Z`. (The same law on an explicit probability space with
independent trials is `ExactSampling.GridIndex.rejection_sampler_iid`.)
Paper: `lem:dynamiccellenvelope` (attention_dynamic_index.tex). -/
theorem cell_envelope_exact [Fintype ι] [DecidableEq κ] [Nonempty ι] (a : ι → ℝ) (aC : κ → ℝ)
    (cell : ι → κ) (a0 : ℝ) (u : κ → ℝ) (hcell : ∀ j, |a j - aC (cell j)| ≤ 1 / 4)
    (j0 : ι) (hj0 : aC (cell j0) = a0) (hu_lo : ∀ j, cellWeight aC a0 (cell j) ≤ u (cell j)) :
    let W := ∑ j, u (cell j)
    let Z := ∑ j, memberWeight a a0 j
    let N : κ → ℝ := fun C => ((Finset.univ.filter fun j => cell j = C).card : ℝ)
    (∀ j, (N (cell j) * u (cell j) / W) * (1 / N (cell j)) * (memberWeight a a0 j / u (cell j)) =
        memberWeight a a0 j / W) ∧
      (∀ j, 0 ≤ memberWeight a a0 j / u (cell j) ∧ memberWeight a a0 j / u (cell j) ≤ 1) ∧
      ∑ j, memberWeight a a0 j / W = Z / W ∧
      ∀ j, HasSum (fun m : ℕ => (1 - Z / W) ^ m * (memberWeight a a0 j / W))
        (memberWeight a a0 j / Z) := by
  intro W Z N
  have hupos : ∀ j, 0 < u (cell j) := fun j => lt_of_lt_of_le (Real.exp_pos _) (hu_lo j)
  have hN : ∀ j, N (cell j) ≠ 0 := by
    intro j
    have : 0 < (Finset.univ.filter fun i => cell i = cell j).card :=
      Finset.card_pos.mpr ⟨j, by simp⟩
    simp only [N]; positivity
  have hZ : 0 < Z := lt_trans (by norm_num) (total_weight_gt_half a aC cell a0 hcell j0 hj0)
  have hZW : Z ≤ W := by
    calc Z ≤ ∑ j, cellWeight aC a0 (cell j) := (ideal_envelope_bounds a aC cell a0 hcell).1
      _ ≤ W := Finset.sum_le_sum fun j _ => hu_lo j
  refine ⟨fun j => accepted_member_mass _ _ _ _ (hN j) (hupos j).ne', fun j => ⟨?_, ?_⟩, ?_,
    fun j => retry_law _ _ _ hZ hZW⟩
  · exact div_nonneg (Real.exp_pos _).le (hupos j).le
  · rw [div_le_one (hupos j)]
    exact le_trans (member_cell_bounds a aC cell a0 hcell j).1 (hu_lo j)
  · rw [← Finset.sum_div]

/-- With the rounded cell envelope, independent trials use fewer than `17/8` proposals in
expectation and succeed with probability more than `8/17`.
Paper: `lem:dynamiccellenvelope` (attention_dynamic_index.tex); `thm:dynamicfixedrank` and
`thm:main-fixed-rank` (main_attention.tex). -/
theorem cell_envelope_proposals [Fintype ι] [Nonempty ι] (a : ι → ℝ) (aC : κ → ℝ) (cell : ι → κ)
    (a0 : ℝ) (u : κ → ℝ) (p : ℕ)
    (hcell : ∀ j, |a j - aC (cell j)| ≤ 1 / 4) (j0 : ι) (hj0 : aC (cell j0) = a0)
    (hu_lo : ∀ j, cellWeight aC a0 (cell j) ≤ u (cell j))
    (hu_hi : ∀ j, u (cell j) ≤ cellWeight aC a0 (cell j) + 3 * (2 : ℝ)⁻¹ ^ p)
    (hp : 64 * (Fintype.card ι : ℝ) ≤ 2 ^ p) :
    let Z := ∑ j, memberWeight a a0 j
    let W := ∑ j, u (cell j)
    HasSum (fun m : ℕ => ((m : ℝ) + 1) * (1 - Z / W) ^ m * (Z / W)) (W / Z) ∧
      W / Z < 17 / 8 ∧ (8 : ℝ) / 17 < Z / W := by
  intro Z W
  obtain ⟨hZW, -, -, hW⟩ :=
    rounded_envelope_bounds a aC cell a0 u p hcell j0 hj0 hu_lo hu_hi hp
  have hZ : 0 < Z := lt_trans (by norm_num) (total_weight_gt_half a aC cell a0 hcell j0 hj0)
  have hWpos : 0 < W := lt_of_lt_of_le hZ hZW
  have hs0 : 0 < Z / W := div_pos hZ hWpos
  have hs1 : Z / W ≤ 1 := (div_le_one hWpos).mpr hZW
  refine ⟨?_, ?_, ?_⟩
  · have := expected_proposals (Z / W) hs0 hs1
    convert this using 1
    field_simp
  · rw [div_lt_iff₀ hZ]; linarith
  · rw [lt_div_iff₀ hWpos]; linarith

/-- The chained 17/8 bound: rounding enclosures of width `2^{-p-2}` of every occupied cell
weight by the rule of `dyadic_envelope_weight`, with `64T ≤ 2^p`, gives `W/Z < 17/8`.
Paper: `lem:dynamiccellenvelope` (attention_dynamic_index.tex); `thm:main-fixed-rank`
(main_attention.tex). -/
theorem rounded_cells_proposals [Fintype ι] [Nonempty ι] (a : ι → ℝ) (aC : κ → ℝ)
    (cell : ι → κ) (a0 : ℝ) (lo hi : κ → ℝ) (p : ℕ)
    (hcell : ∀ j, |a j - aC (cell j)| ≤ 1 / 4) (j0 : ι) (hj0 : aC (cell j0) = a0)
    (hlo : ∀ j, lo (cell j) ≤ cellWeight aC a0 (cell j))
    (hhi : ∀ j, cellWeight aC a0 (cell j) ≤ hi (cell j))
    (hw : ∀ j, hi (cell j) - lo (cell j) ≤ (2 : ℝ)⁻¹ ^ (p + 2))
    (hp : 64 * (Fintype.card ι : ℝ) ≤ 2 ^ p) :
    let u : κ → ℝ := fun C => ((⌈hi C * 2 ^ p⌉ : ℝ) + 1) / 2 ^ p
    (∑ j, u (cell j)) / (∑ j, memberWeight a a0 j) < 17 / 8 := by
  intro u
  have h := fun j => dyadic_envelope_weight _ _ _ p (Real.exp_pos _) (hlo j) (hhi j) (hw j)
  exact (cell_envelope_proposals a aC cell a0 u p hcell j0 hj0 (fun j => (h j).2.1)
    (fun j => (h j).2.2) hp).2.1

/-- The trial bound in non-strict form: `Z ≥ 1/2` and `W ≤ 2Z + 3/64` give `W/Z ≤ 17/8`.
Paper: `lem:dynamiccellenvelope` (attention_dynamic_index.tex). -/
theorem envelope_trials_bound (Z W : ℝ) (hZ : (1 : ℝ) / 2 ≤ Z) (hW : W ≤ 2 * Z + 3 / 64) :
    W / Z ≤ (17 : ℝ) / 8 := by
  have hZpos : 0 < Z := by linarith
  rw [div_le_iff₀ hZpos]
  nlinarith

/-- The same envelope succeeds with probability at least `8/17`.
Paper: `lem:dynamiccellenvelope` (attention_dynamic_index.tex). -/
theorem envelope_success_bound (Z W : ℝ) (hZ : (1 : ℝ) / 2 ≤ Z) (hZW : Z ≤ W)
    (hW : W ≤ 2 * Z + 3 / 64) : (8 : ℝ) / 17 ≤ Z / W := by
  have hWpos : 0 < W := by linarith
  rw [le_div_iff₀ hWpos]
  nlinarith

end CellEnvelope

/-! ## The geometric envelope for decreasing weights (`lem:newmonotoneenvelope`) -/

section Monotone

/-- First member of the geometric block containing position `j ≥ 1`: blocks are
`G₀ = {1}` and `G_ℓ = {2^{ℓ-1}+1, …, 2^ℓ}`, so the first member is `2^{⌊log₂(j-1)⌋} + 1`
for `j ≥ 2`. Paper: `lem:newmonotoneenvelope` (attention_rank_one.tex). -/
def blockStart (j : ℕ) : ℕ := if j ≤ 1 then 1 else 2 ^ Nat.log 2 (j - 1) + 1

/-- Auxiliary: every member's block starts at or before the member. Supports the proof of
`lem:newmonotoneenvelope` (attention_rank_one.tex). -/
lemma blockStart_le {j : ℕ} (hj : 1 ≤ j) : blockStart j ≤ j := by
  unfold blockStart
  split_ifs with h
  · exact hj
  · have := Nat.pow_log_le_self 2 (show j - 1 ≠ 0 by omega)
    omega

/-- Auxiliary: block starts are positions. Supports the proof of `lem:newmonotoneenvelope`
(attention_rank_one.tex). -/
lemma one_le_blockStart (j : ℕ) : 1 ≤ blockStart j := by
  unfold blockStart
  split_ifs
  · exact le_rfl
  · exact Nat.le_add_left 1 _

/-- `⌈j/2⌉ < blockStart j` for `j ≥ 2`: the preceding block lies strictly before the first
member of the block of `j`. Paper: `lem:newmonotoneenvelope` (attention_rank_one.tex). -/
lemma half_lt_blockStart {j : ℕ} (hj : 2 ≤ j) : (j + 1) / 2 < blockStart j := by
  unfold blockStart
  split_ifs with h
  · omega
  · have h' : j - 1 < 2 ^ Nat.log 2 (j - 1) * 2 := by
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (j - 1)
      rwa [pow_succ] at this
    omega

/-- The block start agrees with the paper's blocks: if `2^{ℓ-1} < j ≤ 2^ℓ` with `ℓ ≥ 1`, then
the block of `j` starts at `2^{ℓ-1} + 1`.
Paper: `lem:newmonotoneenvelope` (attention_rank_one.tex). -/
lemma blockStart_of_mem_block {ℓ j : ℕ} (hℓ : 1 ≤ ℓ) (h1 : 2 ^ (ℓ - 1) < j)
    (h2 : j ≤ 2 ^ ℓ) : blockStart j = 2 ^ (ℓ - 1) + 1 := by
  have hpow : 2 ^ ℓ = 2 ^ (ℓ - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  have hlog : Nat.log 2 (j - 1) = ℓ - 1 := by
    have hpos : 1 ≤ 2 ^ (ℓ - 1) := Nat.one_le_two_pow
    have hj1 : j - 1 ≠ 0 := by omega
    rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, hj1⟩), pow_succ]
    generalize 2 ^ (ℓ - 1) = N at *
    omega
  unfold blockStart
  have hpos : 1 ≤ 2 ^ (ℓ - 1) := Nat.one_le_two_pow
  split_ifs with h
  · generalize 2 ^ (ℓ - 1) = N at *
    omega
  · rw [hlog]

/-- Auxiliary charging step: the map `j ↦ ⌈j/2⌉` from `{2,…,T}` is at most two-to-one and hits
`1` once. Supports the proof of `lem:newmonotoneenvelope` (attention_rank_one.tex). -/
lemma sum_half_le (f : ℕ → ℝ) (T : ℕ) (hT1 : 1 ≤ T) (hf : ∀ k, 1 ≤ k → k ≤ T → 0 ≤ f k) :
    ∑ j ∈ Finset.Icc 2 T, f ((j + 1) / 2) ≤ f 1 + 2 * ∑ k ∈ Finset.Icc 2 T, f k := by
  classical
  have hmaps : ∀ j ∈ Finset.Icc 2 T, (j + 1) / 2 ∈ Finset.Icc 1 T := by
    intro j hj
    rw [Finset.mem_Icc] at hj ⊢
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ k ∈ Finset.Icc 1 T,
      ∑ j ∈ (Finset.Icc 2 T).filter (fun j => (j + 1) / 2 = k), f ((j + 1) / 2) =
        ((Finset.Icc 2 T).filter (fun j => (j + 1) / 2 = k)).card * f k := by
    intro k _
    rw [Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2])]
    simp
  rw [Finset.sum_congr rfl hfib]
  have hcard : ∀ k, ((Finset.Icc 2 T).filter (fun j => (j + 1) / 2 = k)).card ≤
      (if k = 1 then 1 else 2) := by
    intro k
    split_ifs with hk
    · apply Finset.card_le_one.mpr
      intro x hx y hy
      simp only [Finset.mem_filter, Finset.mem_Icc] at hx hy
      omega
    · calc ((Finset.Icc 2 T).filter (fun j => (j + 1) / 2 = k)).card
          ≤ ({2 * k - 1, 2 * k} : Finset ℕ).card := by
            apply Finset.card_le_card
            intro x hx
            simp only [Finset.mem_filter, Finset.mem_Icc] at hx
            simp only [Finset.mem_insert, Finset.mem_singleton]
            omega
        _ ≤ 2 := Finset.card_le_two
  have hsplit : Finset.Icc 1 T = insert 1 (Finset.Icc 2 T) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hsplit]
  · rw [Finset.sum_insert (by simp)]
    have h1 : (((Finset.Icc 2 T).filter (fun j => (j + 1) / 2 = 1)).card : ℝ) * f 1 ≤ f 1 := by
      have := hcard 1
      simp only [↓reduceIte] at this
      have : (((Finset.Icc 2 T).filter (fun j => (j + 1) / 2 = 1)).card : ℝ) ≤ 1 := by
        exact_mod_cast this
      nlinarith [hf 1 le_rfl hT1]
    have h2 : ∑ k ∈ Finset.Icc 2 T,
        (((Finset.Icc 2 T).filter (fun j => (j + 1) / 2 = k)).card : ℝ) * f k ≤
          2 * ∑ k ∈ Finset.Icc 2 T, f k := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      have hk1 : k ≠ 1 := by rw [Finset.mem_Icc] at hk; omega
      have hk' := Finset.mem_Icc.mp hk
      have := hcard k
      simp only [hk1, ↓reduceIte] at this
      have : (((Finset.Icc 2 T).filter (fun j => (j + 1) / 2 = k)).card : ℝ) ≤ 2 := by
        exact_mod_cast this
      nlinarith [hf k (by omega) hk'.2]
    linarith

/-- The geometric partition of decreasing weights: for `w₁ ≥ ⋯ ≥ w_T > 0`, the envelope
`W = ∑_ℓ N_ℓ w_{m_ℓ} = ∑_{j ≤ T} w_{m(j)}` satisfies `Z ≤ W ≤ 2Z`.
Paper: `lem:newmonotoneenvelope` (attention_rank_one.tex). -/
theorem monotone_envelope (w : ℕ → ℝ) (T : ℕ)
    (hanti : ∀ i j, 1 ≤ i → i ≤ j → j ≤ T → w j ≤ w i)
    (hpos : ∀ j, 1 ≤ j → j ≤ T → 0 < w j) :
    ∑ j ∈ Finset.Icc 1 T, w j ≤ ∑ j ∈ Finset.Icc 1 T, w (blockStart j) ∧
      ∑ j ∈ Finset.Icc 1 T, w (blockStart j) ≤ 2 * ∑ j ∈ Finset.Icc 1 T, w j := by
  constructor
  · apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact hanti _ _ (one_le_blockStart j) (blockStart_le hj.1) hj.2
  · rcases Nat.eq_zero_or_pos T with hT | hT
    · subst hT; simp
    have hsplit : Finset.Icc 1 T = insert 1 (Finset.Icc 2 T) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
    have hb1 : blockStart 1 = 1 := by simp [blockStart]
    rw [hb1]
    have hstep : ∑ j ∈ Finset.Icc 2 T, w (blockStart j) ≤
        ∑ j ∈ Finset.Icc 2 T, w ((j + 1) / 2) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_Icc] at hj
      have := half_lt_blockStart hj.1
      exact hanti _ _ (by omega) this.le (le_trans (blockStart_le (by omega)) hj.2)
    have := sum_half_le w T hT (fun k hk1 hkT => (hpos k hk1 hkT).le)
    linarith

/-- Rounded geometric envelope at every temperature: if `w₁ = 1`, the weight of every block
start `m(j)` is replaced by a dyadic `u` with `w ≤ u ≤ w + 2^{1-P}`, and `16T ≤ 2^P`, then
`Z ≤ W' ≤ 2Z + 1/8 ≤ (17/8) Z`.
Paper: `thm:newrankone` (attention_rank_one.tex), the display `Z ≤ W' ≤ 2Z + T 2^{1-P}`;
reused in `cor:dynamicrankone` (attention_dynamic_index.tex). -/
theorem rounded_monotone_envelope (w u : ℕ → ℝ) (T P : ℕ)
    (hanti : ∀ i j, 1 ≤ i → i ≤ j → j ≤ T → w j ≤ w i)
    (hpos : ∀ j, 1 ≤ j → j ≤ T → 0 < w j)
    (hT : 1 ≤ T) (hw1 : w 1 = 1)
    (hu_lo : ∀ j ∈ Finset.Icc 1 T, w (blockStart j) ≤ u (blockStart j))
    (hu_hi : ∀ j ∈ Finset.Icc 1 T, u (blockStart j) ≤ w (blockStart j) + 2 * (2 : ℝ)⁻¹ ^ P)
    (hP : 16 * (T : ℝ) ≤ 2 ^ P) :
    let Z := ∑ j ∈ Finset.Icc 1 T, w j
    let W' := ∑ j ∈ Finset.Icc 1 T, u (blockStart j)
    Z ≤ W' ∧ W' ≤ 2 * Z + 1 / 8 ∧ W' ≤ 17 / 8 * Z := by
  intro Z W'
  obtain ⟨h1, h2⟩ := monotone_envelope w T hanti hpos
  have hZ1 : 1 ≤ Z := by
    have : w 1 ≤ Z := Finset.single_le_sum (f := w)
      (fun j hj => (hpos j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2).le)
      (Finset.mem_Icc.mpr ⟨le_rfl, hT⟩)
    linarith
  have hround : W' ≤ ∑ j ∈ Finset.Icc 1 T, w (blockStart j) +
      T * (2 * (2 : ℝ)⁻¹ ^ P) := by
    have : W' ≤ ∑ j ∈ Finset.Icc 1 T, (w (blockStart j) + 2 * (2 : ℝ)⁻¹ ^ P) :=
      Finset.sum_le_sum fun j hj => hu_hi j hj
    rw [Finset.sum_add_distrib] at this
    simpa using this
  have hsmall : (T : ℝ) * (2 * (2 : ℝ)⁻¹ ^ P) ≤ 1 / 8 := by
    have h2P : (0 : ℝ) < 2 ^ P := by positivity
    rw [inv_pow]
    have : (T : ℝ) * (2 * (2 ^ P)⁻¹) = 2 * (T / 2 ^ P) := by ring
    rw [this]
    have : (T : ℝ) / 2 ^ P ≤ 1 / 16 := by rw [div_le_iff₀ h2P]; linarith
    linarith
  have hlo : Z ≤ W' :=
    le_trans h1 (Finset.sum_le_sum fun j hj => hu_lo j hj)
  exact ⟨hlo, by linarith, by linarith⟩

end Monotone

/-! ## The grid of a bounded chart (`thm:dynamicfixedrank`) -/

section Grid

/-- With `|A_{ij}| ≤ 2` and `|q_i| ≤ Q`, every projected coefficient `v = qᵀA` obeys
`|v_i| ≤ 2nQ`. Paper: `thm:dynamicfixedrank` (attention_dynamic_index.tex). -/
theorem projected_coeff_bound {n d : ℕ} (q : Fin n → ℝ) (A : Fin n → Fin d → ℝ) (Q : ℝ)
    (hq : ∀ k, |q k| ≤ Q) (hA : ∀ k i, |A k i| ≤ 2) (i : Fin d) :
    |∑ k, q k * A k i| ≤ 2 * n * Q := by
  calc |∑ k, q k * A k i| ≤ ∑ k, |q k * A k i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, Q * 2 := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (hq k) (hA k i) (abs_nonneg _) (le_trans (abs_nonneg _) (hq k))
    _ = 2 * n * Q := by simp; ring

/-- Coordinatewise error gives the residual score bound before scaling:
`|∑ q_i e_i| ≤ n Q η`. Paper: `cor:dynamicapproximatespace` (attention_dynamic_index.tex). -/
theorem dot_error_bound {n : ℕ} (q e : Fin n → ℝ) (Q η : ℝ) (hQ : 0 ≤ Q)
    (hq : ∀ i, |q i| ≤ Q) (he : ∀ i, |e i| ≤ η) :
    |∑ i, q i * e i| ≤ (n : ℝ) * Q * η := by
  calc |∑ i, q i * e i| ≤ ∑ i, |q i * e i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, Q * η := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (hq i) (he i) (abs_nonneg _) hQ
    _ = (n : ℝ) * Q * η := by simp [mul_assoc]

/-- Two coordinates with the same cell index `⌊y/Δ⌋` differ by less than `Δ`.
Paper: `thm:dynamicfixedrank` (attention_dynamic_index.tex). -/
theorem same_cell_close (y y' Δ : ℝ) (hΔ : 0 < Δ) (h : ⌊y / Δ⌋ = ⌊y' / Δ⌋) :
    |y - y'| < Δ := by
  have h1 := Int.floor_le (y / Δ)
  have h2 := Int.lt_floor_add_one (y / Δ)
  have h3 := Int.floor_le (y' / Δ)
  have h4 := Int.lt_floor_add_one (y' / Δ)
  rw [h] at h1 h2
  have : |y / Δ - y' / Δ| < 1 := by rw [abs_lt]; constructor <;> linarith
  rw [← sub_div, abs_div, abs_of_pos hΔ, div_lt_one hΔ] at this
  exact this

/-- General within-cell score variation: if `|v_i| ≤ 2nQ`, the selected coordinates differ by at
most `Δ = K/2^m`, `d ≤ r`, and `0 ≤ β ≤ β̄`, then
`|(β/n) ∑ v_i (y_i - y'_i)| ≤ 2 β̄ r Q K / 2^m`.
Paper: `thm:dynamicfixedrank` (attention_dynamic_index.tex). -/
theorem cell_score_variation_general {n d r m : ℕ} (hn : 0 < n) (v y y' : Fin d → ℝ)
    (β βbar Q K : ℝ) (hd : d ≤ r) (hβ : 0 ≤ β) (hββ : β ≤ βbar) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hv : ∀ i, |v i| ≤ 2 * n * Q) (hy : ∀ i, |y i - y' i| ≤ K / 2 ^ m) :
    |β / n * ∑ i, v i * (y i - y' i)| ≤ 2 * βbar * r * Q * K / 2 ^ m := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : |∑ i, v i * (y i - y' i)| ≤ d * (2 * n * Q) * (K / 2 ^ m) :=
    dot_error_bound v (fun i => y i - y' i) (2 * n * Q) (K / 2 ^ m) (by positivity) hv hy
  rw [abs_mul, abs_of_nonneg (div_nonneg hβ hnpos.le)]
  have hdr : (d : ℝ) ≤ r := by exact_mod_cast hd
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  calc β / n * |∑ i, v i * (y i - y' i)| ≤ β / n * (d * (2 * n * Q) * (K / 2 ^ m)) := by
        gcongr
    _ = 2 * β * d * Q * K / 2 ^ m := by field_simp
    _ ≤ 2 * βbar * r * Q * K / 2 ^ m := by
        apply div_le_div_of_nonneg_right _ h2m.le
        have : 0 ≤ Q * K := mul_nonneg hQ hK
        have h1 : β * d ≤ βbar * r := mul_le_mul hββ hdr (Nat.cast_nonneg _) (by linarith)
        nlinarith

/-- Within-cell score variation is at most `1/4` when `8 r β̄ Q K ≤ 2^m`.
Paper: `thm:dynamicfixedrank` (attention_dynamic_index.tex), the display
`(β/n) ∑ |v_i| Δ ≤ 2βrQΔ ≤ 1/4`. -/
theorem cell_score_variation {n d r m : ℕ} (hn : 0 < n) (v y y' : Fin d → ℝ)
    (β βbar Q K : ℝ) (hd : d ≤ r) (hβ : 0 ≤ β) (hββ : β ≤ βbar) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hm : 8 * r * βbar * Q * K ≤ 2 ^ m)
    (hv : ∀ i, |v i| ≤ 2 * n * Q) (hy : ∀ i, |y i - y' i| ≤ K / 2 ^ m) :
    |β / n * ∑ i, v i * (y i - y' i)| ≤ 1 / 4 := by
  have h := cell_score_variation_general hn v y y' β βbar Q K hd hβ hββ hQ hK hv hy
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  refine le_trans h ?_
  rw [div_le_iff₀ h2m]
  linarith

/-- A power of two between `x` and `2x` exists for `x ≥ 1`; this is the choice
`m = ⌈log₂ max{1, 8 r β̄ Q K}⌉`. Paper: `thm:dynamicfixedrank` (attention_dynamic_index.tex). -/
theorem exists_pow_two_between (x : ℝ) (hx : 1 ≤ x) :
    ∃ m : ℕ, x ≤ 2 ^ m ∧ (2 : ℝ) ^ m ≤ 2 * x := by
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  by_cases h : x = 2 ^ n
  · exact ⟨n, h.le, by rw [h]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]⟩
  · refine ⟨n + 1, hn2.le, ?_⟩
    rw [pow_succ]; linarith

/-- A coordinate in `[-K, K]` has an integer cell index in `[-2^m, 2^m]`.
Paper: `thm:dynamicfixedrank` (attention_dynamic_index.tex). -/
theorem cell_index_range (y K : ℝ) (m : ℕ) (hK : 0 < K) (hy : |y| ≤ K) :
    -(2 : ℤ) ^ m ≤ ⌊y / (K / 2 ^ m)⌋ ∧ ⌊y / (K / 2 ^ m)⌋ ≤ (2 : ℤ) ^ m := by
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hdiv : y / (K / 2 ^ m) = y * 2 ^ m / K := by field_simp
  have hy' := abs_le.mp hy
  have hlo : -(2 : ℝ) ^ m ≤ y * 2 ^ m / K := by
    rw [le_div_iff₀ hK]; nlinarith
  have hhi : y * 2 ^ m / K ≤ (2 : ℝ) ^ m := by
    rw [div_le_iff₀ hK]; nlinarith
  rw [hdiv]
  constructor
  · apply Int.le_floor.mpr; push_cast; exact hlo
  · have := Int.floor_le (y * 2 ^ m / K)
    have h' : ((⌊y * 2 ^ m / K⌋ : ℤ) : ℝ) ≤ ((2 : ℤ) ^ m : ℤ) := by push_cast; linarith
    exact_mod_cast h'

/-- The number of integer cell indices in one coordinate is `2^{m+1} + 1`.
Paper: `thm:dynamicfixedrank` (attention_dynamic_index.tex). -/
theorem cell_index_count (m : ℕ) :
    (Finset.Icc (-(2 : ℤ) ^ m) ((2 : ℤ) ^ m)).card = 2 ^ (m + 1) + 1 := by
  rw [Int.card_Icc]
  have : (2 : ℤ) ^ m + 1 - -(2 : ℤ) ^ m = ((2 ^ (m + 1) + 1 : ℕ) : ℤ) := by
    push_cast; ring
  rw [this, Int.toNat_natCast]

/-- With `2^m ≤ 2 max{1, 8 r β̄ Q K}`, the per-coordinate cell count obeys
`2^{m+1} + 1 ≤ 5 + 32 r β̄ Q K`.
Paper: `thm:dynamicfixedrank` (attention_dynamic_index.tex). -/
theorem cell_count_per_coordinate (m : ℕ) (X : ℝ) (hX : 0 ≤ X)
    (hm : (2 : ℝ) ^ m ≤ 2 * max 1 (8 * X)) :
    ((2 ^ (m + 1) + 1 : ℕ) : ℝ) ≤ 5 + 32 * X := by
  push_cast
  rw [pow_succ]
  have : max 1 (8 * X) ≤ 1 + 8 * X := max_le (by linarith) (by linarith)
  nlinarith

/-- Occupied cell tuples of one epoch of dimension `d` lie in a box with
`(2^{m+1}+1)^d` integer points. Paper: `thm:dynamicfixedrank` (attention_dynamic_index.tex). -/
theorem cell_tuple_count {ι : Type*} [Fintype ι] {d : ℕ} (y : ι → Fin d → ℝ) (K : ℝ) (m : ℕ)
    (hK : 0 < K) (hy : ∀ j i, |y j i| ≤ K) :
    (Finset.univ.image fun j => fun i => ⌊y j i / (K / 2 ^ m)⌋).card ≤ (2 ^ (m + 1) + 1) ^ d := by
  classical
  have hsub : (Finset.univ.image fun j => fun i => ⌊y j i / (K / 2 ^ m)⌋) ⊆
      Fintype.piFinset fun _ : Fin d => Finset.Icc (-(2 : ℤ) ^ m) ((2 : ℤ) ^ m) := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨j, _, rfl⟩ := hc
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    exact cell_index_range (y j i) K m hK (hy j i)
  calc _ ≤ (Fintype.piFinset fun _ : Fin d =>
        Finset.Icc (-(2 : ℤ) ^ m) ((2 : ℤ) ^ m)).card := Finset.card_le_card hsub
    _ = (2 ^ (m + 1) + 1) ^ d := by
        rw [Fintype.card_piFinset, Finset.prod_const, cell_index_count]; simp

/-- Summing over epochs of dimensions `0, …, r`: `∑_{d ≤ r} G^d ≤ (r+1) G^r` for `G ≥ 1`.
Paper: `thm:dynamicfixedrank` (attention_dynamic_index.tex), the bound on `M_T`. -/
theorem epoch_cell_sum (G : ℝ) (hG : 1 ≤ G) (r : ℕ) :
    ∑ d ∈ Finset.range (r + 1), G ^ d ≤ (r + 1) * G ^ r := by
  calc ∑ d ∈ Finset.range (r + 1), G ^ d ≤ ∑ _d ∈ Finset.range (r + 1), G ^ r := by
        apply Finset.sum_le_sum
        intro d hd
        exact pow_le_pow_right₀ hG (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd))
    _ = (r + 1) * G ^ r := by simp

/-- Every occupied cell contains a member, so the number of occupied cells is at most `T`.
Paper: `thm:dynamicfixedrank` (attention_dynamic_index.tex), `M_T ≤ T`. -/
theorem occupied_cells_le_members {ι κ : Type*} [Fintype ι] [DecidableEq κ] (cell : ι → κ) :
    (Finset.univ.image cell).card ≤ Fintype.card ι :=
  Finset.card_image_le.trans (by simp)

/-- The assembled cell bound: members carry an epoch dimension `d ≤ r` and selected coordinates
in `[-K, K]^d`, and their cell is the epoch together with the integer tuple `⌊y/Δ⌋`,
`Δ = K/2^m`. If `2^m ≤ 2 max{1, 8X}` (the choice `m = ⌈log₂ max{1, 8X}⌉`, with
`X = r β̄ Q K`), then the number of occupied cells satisfies
`M_T ≤ min{T, (r+1)(5 + 32X)^r}`.
Paper: `thm:dynamicfixedrank` (attention_dynamic_index.tex), and `M_T` in `thm:main-fixed-rank`
(main_attention.tex). -/
theorem occupied_cell_bound {ι : Type*} [Fintype ι] (r m : ℕ) (K X : ℝ) (hK : 0 < K)
    (hX : 0 ≤ X) (hm : (2 : ℝ) ^ m ≤ 2 * max 1 (8 * X)) (epoch : ι → Fin (r + 1))
    (y : (j : ι) → Fin (epoch j) → ℝ) (hy : ∀ j i, |y j i| ≤ K) :
    let cell : ι → (Σ d : Fin (r + 1), (Fin d → ℤ)) :=
      fun j => ⟨epoch j, fun i => ⌊y j i / (K / 2 ^ m)⌋⟩
    ((Finset.univ.image cell).card : ℝ) ≤
      min (Fintype.card ι : ℝ) ((r + 1) * (5 + 32 * X) ^ r) := by
  classical
  intro cell
  refine le_min (by exact_mod_cast occupied_cells_le_members cell) ?_
  have hsub : Finset.univ.image cell ⊆ (Finset.univ : Finset (Fin (r + 1))).sigma
      (fun d => Fintype.piFinset fun _ : Fin d => Finset.Icc (-(2 : ℤ) ^ m) ((2 : ℤ) ^ m)) := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨j, _, rfl⟩ := hc
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    exact cell_index_range (y j i) K m hK (hy j i)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_sigma] at hcard
  simp only [Fintype.card_piFinset, Finset.prod_const, cell_index_count, Finset.card_univ,
    Fintype.card_fin] at hcard
  have hG := cell_count_per_coordinate m X hX hm
  have hG1 : (1 : ℝ) ≤ 5 + 32 * X := by linarith
  have hsum : ((∑ d : Fin (r + 1), (2 ^ (m + 1) + 1) ^ (d : ℕ) : ℕ) : ℝ) ≤
      ∑ d ∈ Finset.range (r + 1), (5 + 32 * X) ^ d := by
    push_cast
    rw [Fin.sum_univ_eq_sum_range (fun d => ((2 : ℝ) ^ (m + 1) + 1) ^ d) (r + 1)]
    apply Finset.sum_le_sum
    intro d _
    have : ((2 : ℝ) ^ (m + 1) + 1) ≤ 5 + 32 * X := by exact_mod_cast hG
    exact pow_le_pow_left₀ (by positivity) this d
  calc ((Finset.univ.image cell).card : ℝ)
      ≤ ((∑ d : Fin (r + 1), (2 ^ (m + 1) + 1) ^ (d : ℕ) : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ d ∈ Finset.range (r + 1), (5 + 32 * X) ^ d := hsum
    _ ≤ (r + 1) * (5 + 32 * X) ^ r := epoch_cell_sum _ hG1 r

/-- Counting epochs: a set of epoch dimensions, each at most `r`, has at most `r + 1` elements.
(Each epoch starts at a distinct rank of the growing span, so this bounds the number of epochs.)
Paper: `thm:dynamicfixedrank` (attention_dynamic_index.tex). -/
theorem epoch_count_bound (r : ℕ) (epochs : Finset ℕ) (hrank : ∀ d ∈ epochs, d ≤ r) :
    epochs.card ≤ r + 1 := by
  have hsub : epochs ⊆ Finset.range (r + 1) := by
    intro d hd
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hrank d hd))
  simpa using Finset.card_le_card hsub

/-- Certified neighborhood of a key space: with `m` chosen so that `16 r β̄ Q K ≤ 2^m`, the
projected variation in a cell is at most `1/8`; together with a residual score error at most
`β Q η ≤ 1/8` the proxy is within `1/4` of every actual member score.
Paper: `cor:dynamicapproximatespace` (attention_dynamic_index.tex). -/
theorem approximate_space_allowance {n d r m : ℕ} (hn : 0 < n) (v y y' : Fin d → ℝ)
    (q e : Fin n → ℝ) (β βbar Q K η : ℝ) (hd : d ≤ r) (hβ : 0 ≤ β) (hββ : β ≤ βbar)
    (hQ : 0 ≤ Q) (hK : 0 ≤ K) (hm : 16 * r * βbar * Q * K ≤ 2 ^ m)
    (hv : ∀ i, |v i| ≤ 2 * n * Q) (hy : ∀ i, |y i - y' i| ≤ K / 2 ^ m)
    (hq : ∀ i, |q i| ≤ Q) (he : ∀ i, |e i| ≤ η) (hη : βbar * Q * η ≤ 1 / 8) :
    |β / n * ∑ i, v i * (y i - y' i)| + |β / n * ∑ i, q i * e i| ≤ 1 / 4 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := cell_score_variation_general hn v y y' β βbar Q K hd hβ hββ hQ hK hv hy
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have h1' : 2 * βbar * r * Q * K / 2 ^ m ≤ 1 / 8 := by
    rw [div_le_iff₀ h2m]; linarith
  have h2 : |β / n * ∑ i, q i * e i| ≤ βbar * Q * η := by
    rw [abs_mul, abs_of_nonneg (div_nonneg hβ hnpos.le)]
    have hη0 : 0 ≤ η := le_trans (abs_nonneg _) (he ⟨0, hn⟩)
    calc β / n * |∑ i, q i * e i| ≤ β / n * (n * Q * η) := by
          gcongr; exact dot_error_bound q e Q η hQ hq he
      _ = β * Q * η := by field_simp
      _ ≤ βbar * Q * η := by gcongr
  linarith

/-- Proxy error from a projected score and the within-cell error.
Paper: `cor:dynamicapproximatespace` (attention_dynamic_index.tex). -/
theorem proxy_error (a projected proxy ε δ : ℝ) (h1 : |a - projected| ≤ ε)
    (h2 : |projected - proxy| ≤ δ) : |a - proxy| ≤ ε + δ := by
  calc |a - proxy| ≤ |a - projected| + |projected - proxy| := abs_sub_le a projected proxy
    _ ≤ ε + δ := add_le_add h1 h2

/-- With `2^m ≤ 2 max{1, 16 r β̄ Q K}`, the per-coordinate count in the approximate-space
corollary is `2^{m+1} + 1 ≤ 5 + 64 r β̄ Q K`.
Paper: `cor:dynamicapproximatespace` (attention_dynamic_index.tex). -/
theorem approximate_space_cell_count (m : ℕ) (X : ℝ) (hX : 0 ≤ X)
    (hm : (2 : ℝ) ^ m ≤ 2 * max 1 (16 * X)) :
    ((2 ^ (m + 1) + 1 : ℕ) : ℝ) ≤ 5 + 64 * X := by
  push_cast
  rw [pow_succ]
  have : max 1 (16 * X) ≤ 1 + 16 * X := max_le (by linarith) (by linarith)
  nlinarith

/-- The cell bound of the approximate-space index: with one fixed chart of dimension `r`,
selected coordinates in `[-K,K]^r`, and `2^m ≤ 2 max{1, 16X}` (the choice
`m = ⌈log₂ max{1, 16 r β̄ Q K}⌉`, `X = r β̄ Q K`), the number of occupied cells satisfies
`M_T ≤ min{T, (5 + 64X)^r}`.
Paper: `cor:dynamicapproximatespace` (attention_dynamic_index.tex); also the cell bound of
`prop:checkpoint-key-residual` (checkpoint_certificates.tex). -/
theorem approximate_space_cell_bound {ι : Type*} [Fintype ι] (r m : ℕ) (K X : ℝ) (hK : 0 < K)
    (hX : 0 ≤ X) (hm : (2 : ℝ) ^ m ≤ 2 * max 1 (16 * X)) (y : ι → Fin r → ℝ)
    (hy : ∀ j i, |y j i| ≤ K) :
    ((Finset.univ.image fun j => fun i => ⌊y j i / (K / 2 ^ m)⌋).card : ℝ) ≤
      min (Fintype.card ι : ℝ) ((5 + 64 * X) ^ r) := by
  classical
  refine le_min (by exact_mod_cast occupied_cells_le_members _) ?_
  have h1 := cell_tuple_count y K m hK hy
  have h2 := approximate_space_cell_count m X hX hm
  calc ((Finset.univ.image fun j => fun i => ⌊y j i / (K / 2 ^ m)⌋).card : ℝ)
      ≤ ((2 ^ (m + 1) + 1) ^ r : ℕ) := by exact_mod_cast h1
    _ = ((2 ^ (m + 1) + 1 : ℕ) : ℝ) ^ r := by push_cast; ring
    _ ≤ (5 + 64 * X) ^ r := pow_le_pow_left₀ (by positivity) h2 r

end Grid

/-! ## Bounded rational charts (`lem:dynamicchart`) -/

section Chart

/-- Row replacement: if row `i` of the matrix equals `∑_k C_{ik}` times the selected rows, then
replacing selected row `j` by it multiplies the selected minor by `C_{ij}`.
Paper: `lem:dynamicchart` (attention_dynamic_index.tex). -/
theorem row_replacement_det {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (j : Fin d)
    (row c : Fin d → ℝ) (hrow : row = ∑ k, c k • M k) :
    (M.updateRow j row).det = c j * M.det := by
  rw [hrow, Matrix.det_updateRow_sum, smul_eq_mul]

/-- A coefficient of magnitude above two more than doubles the nonzero selected minor.
Paper: `lem:dynamicchart` (attention_dynamic_index.tex). -/
theorem row_replacement_doubles {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (j : Fin d)
    (row c : Fin d → ℝ) (hrow : row = ∑ k, c k • M k) (hdet : M.det ≠ 0) (hc : 2 < |c j|) :
    2 * |M.det| < |(M.updateRow j row).det| := by
  rw [row_replacement_det M j row c hrow, abs_mul]
  have : 0 < |M.det| := abs_pos.mpr hdet
  nlinarith

/-- Coefficient bound from a non-doubling replacement: if the replacement determinant equals
`c · det` with `det ≠ 0` and its absolute value is at most `2|det|`, then `|c| ≤ 2`.
Paper: `lem:dynamicchart` (attention_dynamic_index.tex). -/
theorem determinant_coefficient_bound (det replacement c : ℝ) (hd : det ≠ 0)
    (hidentity : replacement = c * det) (hvolume : |replacement| ≤ 2 * |det|) : |c| ≤ 2 := by
  have hdpos : 0 < |det| := abs_pos.mpr hd
  rw [hidentity, abs_mul] at hvolume
  exact le_of_mul_le_mul_right hvolume hdpos

/-- Termination of the replacements: nonzero integer determinants that more than double at
each of `s` steps and stay bounded by `M` satisfy `2^s ≤ M`; hence `s ≤ log₂ M`.
Paper: `lem:dynamicchart` (attention_dynamic_index.tex). -/
theorem replacement_count (D : ℕ → ℤ) (s : ℕ) (M : ℝ) (h0 : D 0 ≠ 0)
    (hstep : ∀ k < s, 2 * |D k| < |D (k + 1)|) (hbound : |(D s : ℝ)| ≤ M) :
    (2 : ℝ) ^ s ≤ M := by
  have key : ∀ k ≤ s, (2 : ℤ) ^ k ≤ |D k| := by
    intro k
    induction k with
    | zero => intro _; simp only [pow_zero]; exact Int.one_le_abs h0
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := hstep k (by omega)
      rw [pow_succ]; linarith
  have := key s le_rfl
  have : ((2 : ℤ) ^ s : ℝ) ≤ |(D s : ℝ)| := by exact_mod_cast this
  push_cast at this
  linarith

/-- Hadamard-type crude bound used for the replacement count: a `d × d` minor with entries of
magnitude at most `H` has `|det| ≤ d! H^d`.
Paper: `lem:dynamicchart` (attention_dynamic_index.tex). -/
theorem minor_bound {d : ℕ} (M : Matrix (Fin d) (Fin d) ℤ) (H : ℤ) (hM : ∀ i j, |M i j| ≤ H) :
    |M.det| ≤ d.factorial * H ^ d := by
  have := Matrix.det_le (abv := AbsoluteValue.abs) hM
  simpa [Fintype.card_fin, nsmul_eq_mul] using this

/-- The chart `A = U (U_I)^{-1}` satisfies `A_I = I_d`.
Paper: `lem:dynamicchart` (attention_dynamic_index.tex). -/
theorem chart_selected_rows {n d : ℕ} (U : Matrix (Fin n) (Fin d) ℝ) (I : Fin d → Fin n)
    (hI : (U.submatrix I id).det ≠ 0) :
    (U * (U.submatrix I id)⁻¹).submatrix I id = 1 := by
  have hunit : IsUnit (U.submatrix I id).det := isUnit_iff_ne_zero.mpr hI
  have : (U * (U.submatrix I id)⁻¹).submatrix I id =
      U.submatrix I id * (U.submatrix I id)⁻¹ := by
    ext a b; simp [Matrix.mul_apply]
  rw [this, Matrix.mul_nonsing_inv _ hunit]

/-- Every key of the epoch is reconstructed from its selected coordinates:
if `k - c = U x`, then `k = c₀ + A k_I` with `c₀ = c - A c_I` and `A = U (U_I)^{-1}`.
Paper: `lem:dynamicchart` and `thm:dynamicfixedrank` (attention_dynamic_index.tex). -/
theorem chart_reconstruction {n d : ℕ} (U : Matrix (Fin n) (Fin d) ℝ) (I : Fin d → Fin n)
    (hI : (U.submatrix I id).det ≠ 0) (c k : Fin n → ℝ) (x : Fin d → ℝ)
    (hk : k - c = U.mulVec x) :
    let A := U * (U.submatrix I id)⁻¹
    k = (c - A.mulVec (c ∘ I)) + A.mulVec (k ∘ I) := by
  intro A
  have hunit : IsUnit (U.submatrix I id).det := isUnit_iff_ne_zero.mpr hI
  have hsel : k ∘ I - c ∘ I = (U.submatrix I id).mulVec x := by
    ext a
    have := congrFun hk (I a)
    simp only [Pi.sub_apply] at this
    simp [this, Matrix.mulVec, dotProduct]
  have hx : x = (U.submatrix I id)⁻¹.mulVec (k ∘ I - c ∘ I) := by
    rw [hsel, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  have : A.mulVec (k ∘ I) - A.mulVec (c ∘ I) = U.mulVec x := by
    rw [← Matrix.mulVec_sub, hx, Matrix.mulVec_mulVec]
  have h2 : k = c + U.mulVec x := by rw [← hk]; abel
  calc k = c + U.mulVec x := h2
    _ = c + (A.mulVec (k ∘ I) - A.mulVec (c ∘ I)) := by rw [this]
    _ = (c - A.mulVec (c ∘ I)) + A.mulVec (k ∘ I) := by abel

end Chart

/-! ## Negative exponentials (`lem:newnegativeexp`) -/

section NegativeExp

/-- A very negative argument can be enclosed immediately: if `x ≤ -(p+2)`, then
`0 < e^x ≤ 2^{-(p+2)}`, because `e > 2`. Paper: `lem:newnegativeexp` (attention_rank_one.tex). -/
theorem negexp_small (x : ℝ) (p : ℕ) (hx : x ≤ -((p : ℝ) + 2)) :
    0 < Real.exp x ∧ Real.exp x ≤ (2 : ℝ)⁻¹ ^ (p + 2) := by
  refine ⟨Real.exp_pos x, ?_⟩
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have h1 : Real.exp x ≤ Real.exp (-((p + 2 : ℕ) : ℝ)) :=
    Real.exp_le_exp.mpr (by push_cast; linarith)
  have h2 : (2 : ℝ) ^ (p + 2) ≤ Real.exp ((p + 2 : ℕ) : ℝ) := by
    rw [show (((p + 2 : ℕ) : ℝ)) = ((p + 2 : ℕ) : ℝ) * 1 by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) he _
  rw [Real.exp_neg] at h1
  rw [inv_pow]
  calc Real.exp x ≤ (Real.exp ((p + 2 : ℕ) : ℝ))⁻¹ := h1
    _ ≤ ((2 : ℝ) ^ (p + 2))⁻¹ := inv_anti₀ (by positivity) h2

/-- On the negative half-line the exponential is `1`-Lipschitz: `|e^x - e^y| ≤ |x - y|` for
`x, y ≤ 0`, so an input enclosure error passes to the output without amplification.
Paper: `lem:newnegativeexp` (attention_rank_one.tex). -/
theorem negexp_lipschitz (x y : ℝ) (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Real.exp) (f' := Real.exp)
    (s := Set.Iic 0) (x := y) (y := x) (C := 1)
    (fun z _ => (Real.hasDerivAt_exp z).hasDerivWithinAt)
    (fun z hz => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos z)]
      exact Real.exp_le_one_iff.mpr hz)
    (convex_Iic 0) hy hx
  simpa [Real.norm_eq_abs] using h

/-- The alternating Taylor remainder: `1/(K+1)! ≤ 2^{-K}`.
Paper: `lem:newnegativeexp` (attention_rank_one.tex). -/
theorem factorial_tail (K : ℕ) : (1 : ℝ) / (K + 1).factorial ≤ (2 : ℝ)⁻¹ ^ K := by
  have h : 2 ^ K ≤ (K + 1).factorial := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Nat.factorial_succ, pow_succ]
      have : 2 ≤ K + 1 + 1 := by omega
      calc 2 ^ K * 2 ≤ (K + 1).factorial * (K + 1 + 1) := Nat.mul_le_mul ih this
        _ = (K + 1 + 1) * (K + 1).factorial := Nat.mul_comm _ _
  have h' : (2 : ℝ) ^ K ≤ (K + 1).factorial := by exact_mod_cast h
  rw [inv_pow, one_div]
  exact inv_anti₀ (by positivity) h'

end NegativeExp

/-! ## Stopping and charging -/

section Stopping

/-- Fresh rejection trials fail with probability at most `9/17` each; a probability bounded by
every geometric tail is zero, so the sampler stops almost surely.
Paper: `lem:dynamiccellenvelope` (attention_dynamic_index.tex), almost-sure stopping. -/
theorem zero_of_trial_tail (p : ℝ) (hp : 0 ≤ p) (htail : ∀ k : ℕ, p ≤ ((9 : ℝ) / 17) ^ k) :
    p = 0 := by
  have hpow : Tendsto (fun k : ℕ => ((9 : ℝ) / 17) ^ k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hle : p ≤ 0 := ge_of_tendsto hpow (Filter.Eventually.of_forall htail)
  linarith

/-- Expected stopped work follows from a predictable cost bound and Tonelli: if the work charged
to trial `k` has mean at most `C` times the probability `survival k` of reaching trial `k`,
and `survival k ≤ ρ^k`, then the total expected work is at most `C / (1 - ρ)`.
The application sets `cost k` to zero unless trial `k` is reached; fresh trial randomness
gives the hypothesis `hcost`.
Paper: `lem:dynamiccellenvelope` (attention_dynamic_index.tex), "This stopping argument charges
the actual work of every reached precision stage"; `thm:dynamicfixedrank`. -/
theorem expected_stopped_work {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (cost : ℕ → Ω → ℝ≥0∞) (survival : ℕ → ℝ≥0∞) (C ρ : ℝ≥0∞)
    (hmeas : ∀ k, AEMeasurable (cost k) μ)
    (hcost : ∀ k, (∫⁻ ω, cost k ω ∂μ) ≤ C * survival k)
    (htail : ∀ k, survival k ≤ ρ ^ k) :
    (∫⁻ ω, ∑' k : ℕ, cost k ω ∂μ) ≤ C / (1 - ρ) := by
  rw [MeasureTheory.lintegral_tsum hmeas]
  calc (∑' k : ℕ, ∫⁻ ω, cost k ω ∂μ) ≤ ∑' k : ℕ, C * ρ ^ k := by
        apply ENNReal.tsum_le_tsum
        intro k
        exact (hcost k).trans (by gcongr; exact htail k)
    _ = C * (∑' k : ℕ, ρ ^ k) := ENNReal.tsum_mul_left
    _ = C * (1 - ρ)⁻¹ := by rw [ENNReal.tsum_geometric]
    _ = C / (1 - ρ) := rfl

end Stopping

end ExactSampling.DynamicIndex
