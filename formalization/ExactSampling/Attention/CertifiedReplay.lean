import Mathlib

/-!
# Certified decisions, precision tails, and background replay

This module formalizes the exactness and stopping arguments that turn certified enclosures into
exact samples, as used by the maintained decoder of `attention_moment_decoder.tex`
(`lem:replayexactsampling`, used for `thm:momentdecoder`; summarized in `main_decoder.tex`
as `thm:main-decoder`) and by the finite-cache lemmas of `attention_finite_bits.tex`
(`lem:newprecisionstop`, `lem:newexactification`).

Formalized here:
* CDF decision exactness: a certified decision returns the inverse-CDF token, and the token is
  unique away from the finitely many boundaries.
* Separation implies decision, and the Lebesgue measure of the uniforms whose precision-`p`
  comparison is unresolved is at most `4 V 2^{-p}` (`eq:replayuncertainty`).
* The single-probability comparison: overlap forces `|U - p| ≤ 2^{1-t}`, whose measure is
  `2^{2-t}`, and the overlap events shrink to a null set.
* The geometric moment inequalities `∑_j 2^{-j}(j+1)^k ≤ 2^{k+1} k!` and
  `∑_j 2^{-j}(P+j)^k ≤ 2^{k+1} k! P^k` (`P ≥ 1`).
* The expected-work bounds of `lem:newprecisionstop` and of the fallback branch in
  `lem:newexactification`.
* The replay prefactor `8VT 2^{-p_R} ≤ 1/(8(R+2)^2)` for `T ≤ R`, the routine precision
  `p_R = ⌈log₂(64V(R+2)^3)⌉` and the bound `p_{2R} ≤ p_R + 3`.
* Invariants of the background replay schedule: phases, availability of replay tokens,
  catching up exactly at the phase boundary, and the horizon of the routine index.

Not formalized here: the bit-complexity model and the deterministic causal evaluator itself. In
this module the uniform random number is modelled by Lebesgue measure on `[0,1]` and costs by
nonnegative reals.

Stronger forms elsewhere in the library: the exact output law of the replay sampler and the
autoregressive joint law are `ExactSampling.Replay.uniform_output_eq_prob` and
`ExactSampling.Replay.replay_joint_law`; the expected temporary replay work on the probability
space is `ExactSampling.Replay.expected_replayWork_le`; the background schedule as a state
machine started at the prompt (including the phase before `N₀`) is
`ExactSampling.ReplaySchedule`.
-/

open MeasureTheory Filter Finset Set
open scoped BigOperators ENNReal Topology

namespace ExactSampling.CertifiedReplay

/-! ## Certified categorical decisions (`lem:replayexactsampling`) -/

section Decision

/-- A certified uniform cell contained between CDF enclosures is safe: if
`\overline F_{i-1} ≤ a`, `b ≤ \underline F_i`, and the enclosures contain the true boundaries,
then `F_{i-1} ≤ U ≤ F_i`.
Paper: `lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem certified_category (U a b Fleft Fright hiLeft loRight : ℝ)
    (hua : a ≤ U) (hub : U ≤ b) (hl : Fleft ≤ hiLeft) (hr : loRight ≤ Fright)
    (ha : hiLeft ≤ a) (hb : b ≤ loRight) : Fleft ≤ U ∧ U ≤ Fright := by
  constructor <;> linarith

/-- Uniqueness of the inverse-CDF token for monotone boundaries: if `U` lies strictly between
`F_{i-1}` and `F_i` and between `F_{i'-1}` and `F_{i'}`, then `i = i'`. Hence every certified
decision returns the inverse-CDF sample whenever `U` avoids the finitely many boundaries.
Paper: `lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem inverse_cdf_unique (F : ℕ → ℝ) (hF : Monotone F) (U : ℝ) (i i' : ℕ)
    (hi : 1 ≤ i) (hi' : 1 ≤ i') (h1 : F (i - 1) < U ∧ U < F i)
    (h2 : F (i' - 1) < U ∧ U < F i') : i = i' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : F i ≤ F (i' - 1) := hF (by omega)
    linarith [h1.2, h2.1]
  · have : F i' ≤ F (i - 1) := hF (by omega)
    linarith [h1.1, h2.2]

/-- Left endpoint `a = ⌊2^p U⌋ / 2^p` of the dyadic cell `[a, a + 2^{-p}]` containing `U` at
precision `p`. -/
noncomputable def cellLeft (p : ℕ) (U : ℝ) : ℝ := ⌊U * 2 ^ p⌋ / 2 ^ p

/-- Auxiliary: the dyadic cell of `U` starts at or below `U`. Supports the proof of
`lem:replayexactsampling` (attention_moment_decoder.tex). -/
lemma cellLeft_le (p : ℕ) (U : ℝ) : cellLeft p U ≤ U := by
  unfold cellLeft
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

/-- Auxiliary: the dyadic cell of `U` at precision `p` has width `2^{-p}` and contains `U`.
Supports the proof of `lem:replayexactsampling` (attention_moment_decoder.tex). -/
lemma lt_cellLeft_add (p : ℕ) (U : ℝ) : U < cellLeft p U + (2 : ℝ)⁻¹ ^ p := by
  unfold cellLeft
  have h2p : (0 : ℝ) < 2 ^ p := by positivity
  have := Int.lt_floor_add_one (U * 2 ^ p)
  have heq : (⌊U * 2 ^ p⌋ : ℝ) / 2 ^ p + (2 : ℝ)⁻¹ ^ p = ((⌊U * 2 ^ p⌋ : ℝ) + 1) / 2 ^ p := by
    rw [inv_pow]; field_simp
  rw [heq, lt_div_iff₀ h2p]
  exact this

/-- Auxiliary: the dyadic cell of `U ∈ [0,1)` starts at a nonnegative point. Supports the proof of
`lem:replayexactsampling` (attention_moment_decoder.tex). -/
lemma cellLeft_nonneg (p : ℕ) {U : ℝ} (hU : 0 ≤ U) : 0 ≤ cellLeft p U := by
  unfold cellLeft
  apply div_nonneg _ (by positivity)
  exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg hU (by positivity))

/-- Auxiliary: the dyadic cell of `U < 1` ends at or below `1`. Supports the proof of
`lem:replayexactsampling` (attention_moment_decoder.tex). -/
lemma cellRight_le_one (p : ℕ) {U : ℝ} (hU : U < 1) : cellLeft p U + (2 : ℝ)⁻¹ ^ p ≤ 1 := by
  unfold cellLeft
  have h2p : (0 : ℝ) < 2 ^ p := by positivity
  have hfl : ⌊U * 2 ^ p⌋ < (2 : ℤ) ^ p := by
    rw [Int.floor_lt]; push_cast; nlinarith
  have hfl' : ((⌊U * 2 ^ p⌋ : ℤ) : ℝ) + 1 ≤ (2 : ℝ) ^ p := by
    have : ⌊U * 2 ^ p⌋ + 1 ≤ (2 : ℤ) ^ p := hfl
    exact_mod_cast this
  have heq : (⌊U * 2 ^ p⌋ : ℝ) / 2 ^ p + (2 : ℝ)⁻¹ ^ p = ((⌊U * 2 ^ p⌋ : ℝ) + 1) / 2 ^ p := by
    rw [inv_pow]; field_simp
  rw [heq, div_le_one h2p]
  exact hfl'

/-- The comparison at precision `p` is decided for token `i` when
`\overline F_{i-1} ≤ a` and `b ≤ \underline F_i`, where `[a, b]` is the dyadic cell of `U`. -/
def Decided (lo hi : ℕ → ℝ) (p : ℕ) (U : ℝ) (i : ℕ) : Prop :=
  hi (i - 1) ≤ cellLeft p U ∧ cellLeft p U + (2 : ℝ)⁻¹ ^ p ≤ lo i

/-- Separation implies a decision: if the endpoints `F_0 = 0` and `F_V = 1` are exact, every
interior enclosure has width at most `2^{-p}`, and `U ∈ [0,1)` is farther than `2^{1-p}` from
every interior boundary, then some token `i ∈ [1, V]` is decided.
Paper: `lem:replayexactsampling` (attention_moment_decoder.tex); the contrapositive is the
statement that an unresolved comparison puts `U` within `2^{1-p}` of a boundary. -/
theorem separated_decided (F lo hi : ℕ → ℝ) (V p : ℕ) (U : ℝ)
    (hF0 : F 0 = 0) (hFV : F V = 1) (hlo0 : hi 0 = 0) (hloV : lo V = 1)
    (hcert : ∀ k, 1 ≤ k → k < V → lo k ≤ F k ∧ F k ≤ hi k ∧ hi k - lo k ≤ (2 : ℝ)⁻¹ ^ p)
    (hU0 : 0 ≤ U) (hU1 : U < 1)
    (hsep : ∀ k, 1 ≤ k → k < V → 2 * (2 : ℝ)⁻¹ ^ p < |U - F k|) :
    ∃ i, 1 ≤ i ∧ i ≤ V ∧ Decided lo hi p U i := by
  classical
  have hex : ∃ k, U < F k := ⟨V, by rw [hFV]; exact hU1⟩
  let i := Nat.find hex
  have hiU : U < F i := Nat.find_spec hex
  have hi1 : 1 ≤ i := by
    by_contra h
    have : i = 0 := by omega
    rw [this, hF0] at hiU; linarith
  have hiV : i ≤ V := Nat.find_min' hex (by rw [hFV]; exact hU1)
  have hprev : F (i - 1) ≤ U := by
    have := Nat.find_min hex (show i - 1 < i by omega)
    exact not_lt.mp this
  have hcellL := cellLeft_le p U
  have hcellR := lt_cellLeft_add p U
  have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ p := by positivity
  refine ⟨i, hi1, hiV, ?_, ?_⟩
  · -- left boundary
    rcases Nat.eq_or_lt_of_le hi1 with h | h
    · rw [← h, Nat.sub_self, hlo0]; exact cellLeft_nonneg p hU0
    · have hk1 : 1 ≤ i - 1 := by omega
      have hkV : i - 1 < V := by omega
      obtain ⟨hl, hh, hw⟩ := hcert (i - 1) hk1 hkV
      have hs := hsep (i - 1) hk1 hkV
      rw [abs_of_nonneg (by linarith)] at hs
      linarith
  · -- right boundary
    rcases Nat.lt_or_ge i V with h | h
    · obtain ⟨hl, hh, hw⟩ := hcert i hi1 h
      have hs := hsep i hi1 h
      rw [abs_of_neg (by linarith)] at hs
      linarith
    · have : i = V := le_antisymm hiV h
      rw [this, hloV]; exact cellRight_le_one p hU1

/-- The unresolved comparisons have small measure: the set of `U ∈ [0,1)` for which no token is
decided at precision `p` has Lebesgue measure at most `4 V 2^{-p}`.
Paper: `lem:replayexactsampling`, display `eq:replayuncertainty`
(attention_moment_decoder.tex); also stated after `thm:main-decoder` (main_decoder.tex) and in
`checkpoint_certificates.tex` (`app:checkpoint`). -/
theorem unresolved_measure (F lo hi : ℕ → ℝ) (V p : ℕ)
    (hF0 : F 0 = 0) (hFV : F V = 1) (hlo0 : hi 0 = 0) (hloV : lo V = 1)
    (hcert : ∀ k, 1 ≤ k → k < V → lo k ≤ F k ∧ F k ≤ hi k ∧ hi k - lo k ≤ (2 : ℝ)⁻¹ ^ p) :
    volume {U : ℝ | U ∈ Set.Ico 0 1 ∧ ¬ ∃ i, 1 ≤ i ∧ i ≤ V ∧ Decided lo hi p U i} ≤
      ENNReal.ofReal (4 * V * (2 : ℝ)⁻¹ ^ p) := by
  have hsub : {U : ℝ | U ∈ Set.Ico 0 1 ∧ ¬ ∃ i, 1 ≤ i ∧ i ≤ V ∧ Decided lo hi p U i} ⊆
      ⋃ k ∈ Finset.Ico 1 V, Set.Icc (F k - 2 * (2 : ℝ)⁻¹ ^ p) (F k + 2 * (2 : ℝ)⁻¹ ^ p) := by
    intro U hU
    obtain ⟨⟨hU0, hU1⟩, hnot⟩ := hU
    by_contra hcon
    apply hnot
    apply separated_decided F lo hi V p U hF0 hFV hlo0 hloV hcert hU0 hU1
    intro k hk1 hkV
    by_contra hle'
    have hle := not_lt.mp hle'
    apply hcon
    rw [Set.mem_iUnion₂]
    refine ⟨k, Finset.mem_Ico.mpr ⟨hk1, hkV⟩, ?_⟩
    rw [Set.mem_Icc]
    constructor <;> linarith [abs_le.mp hle]
  calc volume {U : ℝ | U ∈ Set.Ico 0 1 ∧ ¬ ∃ i, 1 ≤ i ∧ i ≤ V ∧ Decided lo hi p U i}
      ≤ volume (⋃ k ∈ Finset.Ico 1 V,
          Set.Icc (F k - 2 * (2 : ℝ)⁻¹ ^ p) (F k + 2 * (2 : ℝ)⁻¹ ^ p)) := measure_mono hsub
    _ ≤ ∑ k ∈ Finset.Ico 1 V,
          volume (Set.Icc (F k - 2 * (2 : ℝ)⁻¹ ^ p) (F k + 2 * (2 : ℝ)⁻¹ ^ p)) :=
        measure_biUnion_finset_le _ _
    _ = ∑ _k ∈ Finset.Ico 1 V, ENNReal.ofReal (4 * (2 : ℝ)⁻¹ ^ p) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Real.volume_Icc]; congr 1; ring
    _ = ENNReal.ofReal ((V - 1 : ℕ) * (4 * (2 : ℝ)⁻¹ ^ p)) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (4 * V * (2 : ℝ)⁻¹ ^ p) := by
        apply ENNReal.ofReal_le_ofReal
        have : ((V - 1 : ℕ) : ℝ) ≤ V := by exact_mod_cast Nat.sub_le V 1
        have hpos : (0 : ℝ) ≤ 4 * (2 : ℝ)⁻¹ ^ p := by positivity
        nlinarith

/-- Away from both true boundaries, the uniform cell is decided (the two-sided form used for a
single token). Paper: `lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem separated_cell_is_decided (u a b left right leftUpper rightLower δ : ℝ)
    (ha : u - δ ≤ a) (hb : b ≤ u + δ) (hl : leftUpper ≤ left + δ)
    (hr : right - δ ≤ rightLower) (hleft : left + 2 * δ < u) (hright : u < right - 2 * δ) :
    leftUpper ≤ a ∧ b ≤ rightLower := by
  constructor <;> linarith

end Decision

/-! ## One Bernoulli comparison (`lem:newprecisionstop`) -/

section Comparison

/-- If the uniform's prefix interval (width `2^{-t}`) and a certified interval for `p`
(width at most `2^{-t}`) overlap, then `|U - p| ≤ 2^{1-t}`.
Paper: `lem:newprecisionstop` (attention_finite_bits.tex). -/
theorem overlap_close (U p a lo hi : ℝ) (t : ℕ) (hU : a ≤ U ∧ U ≤ a + (2 : ℝ)⁻¹ ^ t)
    (hp : lo ≤ p ∧ p ≤ hi) (hw : hi - lo ≤ (2 : ℝ)⁻¹ ^ t)
    (hover : lo ≤ a + (2 : ℝ)⁻¹ ^ t ∧ a ≤ hi) : |U - p| ≤ 2 * (2 : ℝ)⁻¹ ^ t := by
  rw [abs_le]; constructor <;> linarith [hU.1, hU.2, hp.1, hp.2, hover.1, hover.2]

/-- A separated comparison is correct: if the uniform's prefix interval lies below the certified
lower endpoint then `U ≤ p`, and if it lies above the upper endpoint then `p ≤ U`. Hence the
returned bit equals `1{U < p}` except on the null event `U = p` (`overlap_null`).
Paper: `lem:newprecisionstop` (attention_finite_bits.tex). -/
theorem comparison_exact (U p a lo hi : ℝ) (t : ℕ) (hU : a ≤ U ∧ U ≤ a + (2 : ℝ)⁻¹ ^ t)
    (hp : lo ≤ p ∧ p ≤ hi) :
    (a + (2 : ℝ)⁻¹ ^ t ≤ lo → U ≤ p) ∧ (hi ≤ a → p ≤ U) := by
  constructor <;> intro h <;> linarith [hU.1, hU.2, hp.1, hp.2]

/-- The overlap event at precision `t` has probability at most `2^{2-t}`.
Paper: `lem:newprecisionstop` (attention_finite_bits.tex). -/
theorem overlap_measure (p : ℝ) (t : ℕ) :
    volume {U : ℝ | |U - p| ≤ 2 * (2 : ℝ)⁻¹ ^ t} = ENNReal.ofReal (4 * (2 : ℝ)⁻¹ ^ t) := by
  have : {U : ℝ | |U - p| ≤ 2 * (2 : ℝ)⁻¹ ^ t} =
      Set.Icc (p - 2 * (2 : ℝ)⁻¹ ^ t) (p + 2 * (2 : ℝ)⁻¹ ^ t) := by
    ext U
    show |U - p| ≤ 2 * (2 : ℝ)⁻¹ ^ t ↔ U ∈ Set.Icc _ _
    rw [Set.mem_Icc, abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [this, Real.volume_Icc]; congr 1; ring

/-- The overlap events shrink to the null set `{p}`, so the comparison stops almost surely.
Paper: `lem:newprecisionstop` (attention_finite_bits.tex). -/
theorem overlap_null (p : ℝ) :
    volume (⋂ t : ℕ, {U : ℝ | |U - p| ≤ 2 * (2 : ℝ)⁻¹ ^ t}) = 0 := by
  have hsub : (⋂ t : ℕ, {U : ℝ | |U - p| ≤ 2 * (2 : ℝ)⁻¹ ^ t}) ⊆ {p} := by
    intro U hU
    rw [Set.mem_iInter] at hU
    have hlim : Tendsto (fun t : ℕ => 2 * (2 : ℝ)⁻¹ ^ t) atTop (𝓝 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num)
        (by norm_num)
      simpa using this.const_mul 2
    have : |U - p| ≤ 0 := ge_of_tendsto hlim (Filter.Eventually.of_forall hU)
    have : U - p = 0 := abs_nonpos_iff.mp this
    simp only [Set.mem_singleton_iff]; linarith
  exact measure_mono_null hsub (Real.volume_singleton)

/-- A probability bounded by every geometric precision tail is zero.
Paper: `lem:newprecisionstop` (attention_finite_bits.tex); `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
theorem no_nontermination_mass (p C : ℝ) (hp : 0 ≤ p)
    (htail : ∀ k : ℕ, p ≤ C * ((1 : ℝ) / 2) ^ k) : p = 0 := by
  have hpow : Tendsto (fun k : ℕ => ((1 : ℝ) / 2) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Tendsto (fun k : ℕ => C * ((1 : ℝ) / 2) ^ k) atTop (𝓝 0) := by
    simpa using hpow.const_mul C
  have hnonpos : p ≤ 0 := ge_of_tendsto hlim (Filter.Eventually.of_forall htail)
  linarith

end Comparison

/-! ## Geometric moments and expected refinement work -/

section Moments

/-- `∑_{j ≥ 0} 2^{-j} (j+1)^k ≤ 2^{k+1} k!`, via `(j+1)^k ≤ k! \binom{j+k}{k}` and the
negative-binomial generating function.
Paper: `lem:newprecisionstop` (attention_finite_bits.tex); `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
theorem geometric_moment_unit (k : ℕ) :
    Summable (fun j : ℕ => (2 : ℝ)⁻¹ ^ j * ((j : ℝ) + 1) ^ k) ∧
      ∑' j : ℕ, (2 : ℝ)⁻¹ ^ j * ((j : ℝ) + 1) ^ k ≤ 2 ^ (k + 1) * k.factorial := by
  have hbound : ∀ j : ℕ, (2 : ℝ)⁻¹ ^ j * ((j : ℝ) + 1) ^ k ≤
      (k.factorial : ℝ) * (((j + k).choose k : ℝ) * (2 : ℝ)⁻¹ ^ j) := by
    intro j
    have h1 : (j + 1) ^ k ≤ (j + 1).ascFactorial k := Nat.pow_succ_le_ascFactorial (j + 1) k
    rw [Nat.ascFactorial_eq_factorial_mul_choose] at h1
    have h2 : ((j : ℝ) + 1) ^ k ≤ (k.factorial : ℝ) * ((j + k).choose k : ℝ) := by
      exact_mod_cast h1
    have h3 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ j := by positivity
    nlinarith
  have hs := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) k (r := (2 : ℝ)⁻¹)
    (by norm_num)
  have hs' := hs.mul_left (k.factorial : ℝ)
  have hsum : Summable (fun j : ℕ => (2 : ℝ)⁻¹ ^ j * ((j : ℝ) + 1) ^ k) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hbound hs'.summable
  refine ⟨hsum, ?_⟩
  have := hasSum_le hbound hsum.hasSum hs'
  calc _ ≤ _ := this
    _ = 2 ^ (k + 1) * k.factorial := by
        have : (1 : ℝ) - 2⁻¹ = 2⁻¹ := by norm_num
        rw [this, one_div, inv_pow, inv_inv]; ring

/-- `∑_{j ≥ 0} 2^{-j} (P+j)^k ≤ 2^{k+1} k! P^k` for `P ≥ 1`.
Paper: `lem:replayexactsampling` (attention_moment_decoder.tex), the explicit geometric-moment
inequality; restated in `checkpoint_certificates.tex` (`app:checkpoint`). -/
theorem geometric_moment (k : ℕ) (P : ℝ) (hP : 1 ≤ P) :
    Summable (fun j : ℕ => (2 : ℝ)⁻¹ ^ j * (P + j) ^ k) ∧
      ∑' j : ℕ, (2 : ℝ)⁻¹ ^ j * (P + j) ^ k ≤ 2 ^ (k + 1) * k.factorial * P ^ k := by
  obtain ⟨hs, hle⟩ := geometric_moment_unit k
  have hbound : ∀ j : ℕ, (2 : ℝ)⁻¹ ^ j * (P + j) ^ k ≤
      P ^ k * ((2 : ℝ)⁻¹ ^ j * ((j : ℝ) + 1) ^ k) := by
    intro j
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h1 : P + j ≤ P * (j + 1) := by nlinarith
    have h2 : (P + j) ^ k ≤ (P * (j + 1)) ^ k :=
      pow_le_pow_left₀ (by linarith) h1 k
    rw [mul_pow] at h2
    have h3 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ j := by positivity
    nlinarith
  have hs' := hs.mul_left (P ^ k)
  have hsum : Summable (fun j : ℕ => (2 : ℝ)⁻¹ ^ j * (P + j) ^ k) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (by positivity)
      (pow_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j]) _)) hbound hs'
  refine ⟨hsum, ?_⟩
  calc ∑' j : ℕ, (2 : ℝ)⁻¹ ^ j * (P + j) ^ k
      ≤ ∑' j : ℕ, P ^ k * ((2 : ℝ)⁻¹ ^ j * ((j : ℝ) + 1) ^ k) :=
        Summable.tsum_le_tsum hbound hsum hs'
    _ = P ^ k * ∑' j : ℕ, (2 : ℝ)⁻¹ ^ j * ((j : ℝ) + 1) ^ k := tsum_mul_left
    _ ≤ P ^ k * (2 ^ (k + 1) * k.factorial) := by
        gcongr
    _ = 2 ^ (k + 1) * k.factorial * P ^ k := by ring

/-- Expected work of the precision-stopping comparison: if stage `1` is always reached, stage
`t ≥ 2` is reached with probability at most `8·2^{-t} = 2^{3-t}`, and stage `t` costs at most
`C (B+t)^d` with `B ≥ 1`, then the expected total cost is at most `2^{d+5} d! C (B+1)^d`.
Paper: `lem:newprecisionstop` (attention_finite_bits.tex). -/
theorem precision_stop_work (C B : ℝ) (d : ℕ) (hC : 0 ≤ C) (hB : 1 ≤ B)
    (reach cost : ℕ → ℝ) (hr0 : ∀ t, 0 ≤ reach t) (hr1 : reach 1 ≤ 1)
    (hr : ∀ t, 2 ≤ t → reach t ≤ 8 * (2 : ℝ)⁻¹ ^ t) (hc0 : ∀ t, 0 ≤ cost t)
    (hc : ∀ t, 1 ≤ t → cost t ≤ C * (B + t) ^ d) :
    Summable (fun t : ℕ => reach (t + 1) * cost (t + 1)) ∧
      ∑' t : ℕ, reach (t + 1) * cost (t + 1) ≤ 2 ^ (d + 5) * d.factorial * C * (B + 1) ^ d := by
  obtain ⟨hs, hle⟩ := geometric_moment d (B + 1) (by linarith)
  have hbound : ∀ t : ℕ, reach (t + 1) * cost (t + 1) ≤
      4 * C * ((2 : ℝ)⁻¹ ^ t * (B + 1 + t) ^ d) := by
    intro t
    have hct : cost (t + 1) ≤ C * (B + 1 + t) ^ d := by
      have := hc (t + 1) (by omega)
      push_cast at this
      calc cost (t + 1) ≤ C * (B + (t + 1)) ^ d := this
        _ = C * (B + 1 + t) ^ d := by ring_nf
    have hrt : reach (t + 1) ≤ 4 * (2 : ℝ)⁻¹ ^ t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h; simp only [zero_add, pow_zero, mul_one]; linarith
      · have := hr (t + 1) (by omega)
        calc reach (t + 1) ≤ 8 * (2 : ℝ)⁻¹ ^ (t + 1) := this
          _ = 4 * (2 : ℝ)⁻¹ ^ t := by rw [pow_succ]; ring
    have hBt : (0 : ℝ) ≤ (B + 1 + t) ^ d := by positivity
    calc reach (t + 1) * cost (t + 1) ≤ (4 * (2 : ℝ)⁻¹ ^ t) * (C * (B + 1 + t) ^ d) :=
          mul_le_mul hrt hct (hc0 _) (by positivity)
      _ = 4 * C * ((2 : ℝ)⁻¹ ^ t * (B + 1 + t) ^ d) := by ring
  have hs' := hs.mul_left (4 * C)
  have hsum : Summable (fun t : ℕ => reach (t + 1) * cost (t + 1)) :=
    Summable.of_nonneg_of_le (fun t => mul_nonneg (hr0 _) (hc0 _)) hbound hs'
  refine ⟨hsum, ?_⟩
  calc ∑' t : ℕ, reach (t + 1) * cost (t + 1)
      ≤ ∑' t : ℕ, 4 * C * ((2 : ℝ)⁻¹ ^ t * (B + 1 + t) ^ d) :=
        Summable.tsum_le_tsum hbound hsum hs'
    _ = 4 * C * ∑' t : ℕ, (2 : ℝ)⁻¹ ^ t * (B + 1 + t) ^ d := tsum_mul_left
    _ ≤ 4 * C * (2 ^ (d + 1) * d.factorial * (B + 1) ^ d) := by gcongr
    _ ≤ 2 ^ (d + 5) * d.factorial * C * (B + 1) ^ d := by
        have h1 : (0 : ℝ) ≤ d.factorial * C * (B + 1) ^ d := by positivity
        have h2 : (2 : ℝ) ^ (d + 5) = 16 * 2 ^ (d + 1) := by ring
        rw [h2]
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (d + 1)]

/-- The series in the fallback bound of the exactification lemma:
`8·2^{-m} H ∑_{r≥1} 2^{-r}(B+m+r)^d ≤ 2^{d+5} d! 2^{-m} H (B+m+1)^d`.
Paper: `lem:newexactification` (attention_finite_bits.tex). -/
theorem exactification_series (H B : ℝ) (m d : ℕ) (hH : 0 ≤ H) (hB : 0 ≤ B) :
    Summable (fun r : ℕ => (2 : ℝ)⁻¹ ^ (r + 1) * (B + m + (r + 1)) ^ d) ∧
      8 * (2 : ℝ)⁻¹ ^ m * H * ∑' r : ℕ, (2 : ℝ)⁻¹ ^ (r + 1) * (B + m + (r + 1)) ^ d ≤
        2 ^ (d + 5) * d.factorial * (2 : ℝ)⁻¹ ^ m * H * (B + m + 1) ^ d := by
  obtain ⟨hs, hle⟩ := geometric_moment d (B + m + 1)
    (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hfun : (fun r : ℕ => (2 : ℝ)⁻¹ ^ (r + 1) * (B + m + (r + 1)) ^ d) =
      fun r : ℕ => 2⁻¹ * ((2 : ℝ)⁻¹ ^ r * (B + m + 1 + r) ^ d) := by
    funext r; rw [pow_succ]; ring_nf
  rw [hfun]
  have hs' := hs.mul_left 2⁻¹
  refine ⟨hs', ?_⟩
  rw [tsum_mul_left]
  have hpos : (0 : ℝ) ≤ 8 * (2 : ℝ)⁻¹ ^ m * H := by positivity
  calc 8 * (2 : ℝ)⁻¹ ^ m * H * (2⁻¹ * ∑' r : ℕ, (2 : ℝ)⁻¹ ^ r * (B + m + 1 + r) ^ d)
      ≤ 8 * (2 : ℝ)⁻¹ ^ m * H * (2⁻¹ * (2 ^ (d + 1) * d.factorial * (B + m + 1) ^ d)) := by
        gcongr
    _ ≤ 2 ^ (d + 5) * d.factorial * (2 : ℝ)⁻¹ ^ m * H * (B + m + 1) ^ d := by
        have h1 : (0 : ℝ) ≤ d.factorial * (2 : ℝ)⁻¹ ^ m * H * (B + m + 1) ^ d := by positivity
        have h2 : (2 : ℝ) ^ (d + 5) = 8 * 2 ^ (d + 2) := by ring
        have h3 : (2 : ℝ) ^ (d + 2) = 2 * 2 ^ (d + 1) := by ring
        rw [h2, h3]
        have h4 : (0 : ℝ) < 2 ^ (d + 1) := by positivity
        nlinarith

/-- The fallback branch of the exactification lemma: if stage `m + r` (`r ≥ 1`) is reached with
probability at most `2^{3-m-r}` and costs at most `H (B+m+r)^d`, then the expected fallback cost
`∑_{r≥1} reach_r · cost_r` is finite and at most `2^{d+5} d! 2^{-m} H (B+m+1)^d`.
Paper: `lem:newexactification` (attention_finite_bits.tex). -/
theorem exactification_fallback (H B : ℝ) (m d : ℕ) (hH : 0 ≤ H) (hB : 0 ≤ B)
    (reach cost : ℕ → ℝ) (hr0 : ∀ r, 0 ≤ reach r)
    (hr : ∀ r, 1 ≤ r → reach r ≤ 8 * (2 : ℝ)⁻¹ ^ (m + r))
    (hc0 : ∀ r, 0 ≤ cost r) (hc : ∀ r, 1 ≤ r → cost r ≤ H * (B + m + r) ^ d) :
    Summable (fun r : ℕ => reach (r + 1) * cost (r + 1)) ∧
      ∑' r : ℕ, reach (r + 1) * cost (r + 1) ≤
        2 ^ (d + 5) * d.factorial * (2 : ℝ)⁻¹ ^ m * H * (B + m + 1) ^ d := by
  obtain ⟨hs, hle⟩ := exactification_series H B m d hH hB
  have hbound : ∀ r : ℕ, reach (r + 1) * cost (r + 1) ≤
      8 * (2 : ℝ)⁻¹ ^ m * H * ((2 : ℝ)⁻¹ ^ (r + 1) * (B + m + (r + 1)) ^ d) := by
    intro r
    have h1 := hr (r + 1) (by omega)
    have h2 := hc (r + 1) (by omega)
    push_cast at h2
    rw [pow_add] at h1
    calc reach (r + 1) * cost (r + 1)
        ≤ (8 * ((2 : ℝ)⁻¹ ^ m * (2 : ℝ)⁻¹ ^ (r + 1))) * (H * (B + m + (r + 1)) ^ d) :=
          mul_le_mul h1 h2 (hc0 _) (by positivity)
      _ = 8 * (2 : ℝ)⁻¹ ^ m * H * ((2 : ℝ)⁻¹ ^ (r + 1) * (B + m + (r + 1)) ^ d) := by ring
  have hs' := hs.mul_left (8 * (2 : ℝ)⁻¹ ^ m * H)
  have hsum : Summable (fun r : ℕ => reach (r + 1) * cost (r + 1)) :=
    Summable.of_nonneg_of_le (fun r => mul_nonneg (hr0 _) (hc0 _)) hbound hs'
  refine ⟨hsum, ?_⟩
  calc ∑' r : ℕ, reach (r + 1) * cost (r + 1)
      ≤ ∑' r : ℕ, 8 * (2 : ℝ)⁻¹ ^ m * H * ((2 : ℝ)⁻¹ ^ (r + 1) * (B + m + (r + 1)) ^ d) :=
        Summable.tsum_le_tsum hbound hsum hs'
    _ = 8 * (2 : ℝ)⁻¹ ^ m * H * ∑' r : ℕ, (2 : ℝ)⁻¹ ^ (r + 1) * (B + m + (r + 1)) ^ d :=
        tsum_mul_left
    _ ≤ _ := hle

/-- Choosing `2^m ≥ H` makes the fallback factor `2^{-m} H` at most one.
Paper: `lem:newexactification` (attention_finite_bits.tex). -/
theorem fallback_factor_le_one (H : ℝ) (m : ℕ) (hm : H ≤ 2 ^ m) : (2 : ℝ)⁻¹ ^ m * H ≤ 1 := by
  rw [inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
  exact hm

end Moments

/-! ## The replay precision and its prefactor (`lem:replayexactsampling`) -/

section Replay

/-- Routine precision `p_R = ⌈log₂(64 V (R+2)^3)⌉` for a horizon `R`.
Paper: `lem:replayexactsampling` (attention_moment_decoder.tex). -/
def routinePrecision (V R : ℕ) : ℕ := Nat.clog 2 (64 * V * (R + 2) ^ 3)

/-- Auxiliary: `2^{p_R} ≥ 64 V (R+2)^3`. Supports `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
lemma routinePrecision_spec (V R : ℕ) : 64 * V * (R + 2) ^ 3 ≤ 2 ^ routinePrecision V R :=
  Nat.le_pow_clog (by norm_num) _

/-- Doubling the horizon raises the routine precision by at most three bits.
Paper: `lem:replayexactsampling` (attention_moment_decoder.tex), "The future precision differs
from the current precision by only a constant number of bits". -/
theorem routinePrecision_double (V R : ℕ) :
    routinePrecision V (2 * R) ≤ routinePrecision V R + 3 := by
  unfold routinePrecision
  apply Nat.clog_le_of_le_pow
  have h := routinePrecision_spec V R
  unfold routinePrecision at h
  have h2 : (2 * R + 2) ^ 3 ≤ 8 * (R + 2) ^ 3 := by
    have : 2 * R + 2 ≤ 2 * (R + 2) := by omega
    calc (2 * R + 2) ^ 3 ≤ (2 * (R + 2)) ^ 3 := Nat.pow_le_pow_left this 3
      _ = 8 * (R + 2) ^ 3 := by ring
  calc 64 * V * (2 * R + 2) ^ 3 ≤ 64 * V * (8 * (R + 2) ^ 3) := Nat.mul_le_mul_left _ h2
    _ = 8 * (64 * V * (R + 2) ^ 3) := by ring
    _ ≤ 8 * 2 ^ Nat.clog 2 (64 * V * (R + 2) ^ 3) := Nat.mul_le_mul_left _ h
    _ = 2 ^ (Nat.clog 2 (64 * V * (R + 2) ^ 3) + 3) := by ring

/-- The prefactor of the temporary-replay cost: if `2^p ≥ 64 V (R+2)^3` and `T ≤ R`, then
`8 V T 2^{-p} ≤ 1/(8(R+2)^2)`.
Paper: `lem:replayexactsampling` (attention_moment_decoder.tex), "its prefactor is at most a
constant times `(R+2)^{-2}`". -/
theorem replay_prefactor (V T R p : ℕ) (hp : 64 * (V : ℝ) * (R + 2) ^ 3 ≤ 2 ^ p)
    (hT : T ≤ R) : 8 * (V : ℝ) * T * (2 : ℝ)⁻¹ ^ p ≤ 1 / (8 * ((R : ℝ) + 2) ^ 2) := by
  have h2p : (0 : ℝ) < 2 ^ p := by positivity
  have hR : (0 : ℝ) < (R : ℝ) + 2 := by positivity
  have hTR : (T : ℝ) ≤ R := by exact_mod_cast hT
  rw [inv_pow, ← div_eq_mul_inv, div_le_div_iff₀ h2p (by positivity), one_mul]
  have hV : (0 : ℝ) ≤ V := Nat.cast_nonneg V
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  calc 8 * (V : ℝ) * T * (8 * ((R : ℝ) + 2) ^ 2)
      ≤ 8 * (V : ℝ) * ((R : ℝ) + 2) * (8 * ((R : ℝ) + 2) ^ 2) := by
        gcongr; linarith
    _ = 64 * (V : ℝ) * ((R : ℝ) + 2) ^ 3 := by ring
    _ ≤ 2 ^ p := hp

/-- Temporary replays have expected cost at most a constant times
`(R+2)^{-2} 2^{k+1} k! P^k` when the replay cost at precision `P + j` is at most `c (P+j)^k`; the
series is summable.
Paper: `lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem replay_expected_work (V T R p k : ℕ) (c P : ℝ) (hc : 0 ≤ c) (hP : 1 ≤ P)
    (hp : 64 * (V : ℝ) * (R + 2) ^ 3 ≤ 2 ^ p) (hT : T ≤ R) :
    Summable (fun j : ℕ => (2 : ℝ)⁻¹ ^ j * (c * (P + j) ^ k)) ∧
    8 * (V : ℝ) * T * (2 : ℝ)⁻¹ ^ p * ∑' j : ℕ, (2 : ℝ)⁻¹ ^ j * (c * (P + j) ^ k) ≤
      1 / (8 * ((R : ℝ) + 2) ^ 2) * (c * (2 ^ (k + 1) * k.factorial * P ^ k)) := by
  obtain ⟨hsm, hle⟩ := geometric_moment k P hP
  refine ⟨?_, ?_⟩
  · have := hsm.mul_left c
    convert this using 1; funext j; ring
  have hpre := replay_prefactor V T R p hp hT
  have hsum_eq : ∑' j : ℕ, (2 : ℝ)⁻¹ ^ j * (c * (P + j) ^ k) =
      c * ∑' j : ℕ, (2 : ℝ)⁻¹ ^ j * (P + j) ^ k := by
    rw [← tsum_mul_left]; congr 1; funext j; ring
  rw [hsum_eq]
  have h0 : (0 : ℝ) ≤ ∑' j : ℕ, (2 : ℝ)⁻¹ ^ j * (P + j) ^ k :=
    tsum_nonneg fun j => mul_nonneg (by positivity)
      (pow_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j]) _)
  have hpre0 : 0 ≤ 8 * (V : ℝ) * T * (2 : ℝ)⁻¹ ^ p := by positivity
  calc 8 * (V : ℝ) * T * (2 : ℝ)⁻¹ ^ p * (c * ∑' j : ℕ, (2 : ℝ)⁻¹ ^ j * (P + j) ^ k)
      ≤ 8 * (V : ℝ) * T * (2 : ℝ)⁻¹ ^ p * (c * (2 ^ (k + 1) * k.factorial * P ^ k)) := by
        gcongr
    _ ≤ 1 / (8 * ((R : ℝ) + 2) ^ 2) * (c * (2 ^ (k + 1) * k.factorial * P ^ k)) := by
        gcongr

end Replay

/-! ## The background replay schedule (`lem:replayexactsampling`)

The paper builds the routine index at precision `p_{2N₀}`, where `N₀` is the least power of two
at least the prompt length `T₀`, uses it alone while `T < N₀`, and from `T = N₀` on runs phases
`[N, 2N)`. The functions below describe the phase structure at history length `T`; they agree
with the paper's schedule for `T ≥ N₀` (`phaseStart_ge`, `schedule_from_prompt`). The complete
state machine from the prompt on is `ExactSampling.ReplaySchedule` (stronger form). -/

section Schedule

/-- Start `N` of the current phase at history length `T`: the largest power of two at most
`T`. Paper: `lem:replayexactsampling` (attention_moment_decoder.tex). -/
def phaseStart (T : ℕ) : ℕ := 2 ^ Nat.log 2 T

/-- Number of history tokens already replayed into the future index at history length `T`:
two per append since the phase started. Paper: `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
def futureReplayed (T : ℕ) : ℕ := 2 * (T - phaseStart T)

/-- Auxiliary: the phase start is at most the history length. Supports the background schedule in
the proof of `lem:replayexactsampling` (attention_moment_decoder.tex). -/
lemma phaseStart_le {T : ℕ} (hT : 1 ≤ T) : phaseStart T ≤ T :=
  Nat.pow_log_le_self 2 (by omega)

/-- Auxiliary: the history is shorter than twice the phase start. Supports the background
schedule in the proof of `lem:replayexactsampling` (attention_moment_decoder.tex). -/
lemma lt_two_mul_phaseStart (T : ℕ) : T < 2 * phaseStart T := by
  have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) T
  unfold phaseStart; rw [pow_succ] at this; linarith

/-- The current routine index, built for horizon `2N`, covers the present history:
`N ≤ T < 2N`. Paper: `lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem phase_horizon {T : ℕ} (hT : 1 ≤ T) : phaseStart T ≤ T ∧ T < 2 * phaseStart T :=
  ⟨phaseStart_le hT, lt_two_mul_phaseStart T⟩

/-- Phases started after the prompt are powers of two at least the initial one: if
`N₀ = 2^a ≤ T`, then `N₀ ≤ phaseStart T`. Paper: `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
theorem phaseStart_ge (a T : ℕ) (h : 2 ^ a ≤ T) : 2 ^ a ≤ phaseStart T := by
  unfold phaseStart
  apply Nat.pow_le_pow_right (by norm_num)
  exact (Nat.le_log_iff_pow_le (by norm_num) (by
    have : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    omega)).mpr h

/-- A one-line fact: the initial index built at precision `p_{2N₀}` with `N₀ ≥ T₀` has horizon at
least `2T₀`, so the first append does not force a rebuild.
Paper: `lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem initial_horizon (T0 N0 : ℕ) (h : T0 ≤ N0) : 2 * T0 ≤ 2 * N0 := by omega

/-- Replay tokens are available: `2j ≤ N + j` for `j ≤ N`, i.e. the future index never runs
ahead of the history. Paper: `lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem futureReplayed_le {T : ℕ} (hT : 1 ≤ T) : futureReplayed T ≤ T := by
  have h1 := phaseStart_le hT
  have h2 := lt_two_mul_phaseStart T
  unfold futureReplayed
  omega

/-- The two replay tokens needed at the next append exist: `futureReplayed T + 2 ≤ T + 1`.
Paper: `lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem next_replay_available {T : ℕ} (hT : 1 ≤ T) : futureReplayed T + 2 ≤ T + 1 := by
  have h1 := phaseStart_le hT
  have h2 := lt_two_mul_phaseStart T
  unfold futureReplayed
  omega

/-- Within a phase, an append keeps the phase and replays two more tokens.
Paper: `lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem append_within_phase {T : ℕ} (hT : 1 ≤ T) (h : T + 1 < 2 * phaseStart T) :
    phaseStart (T + 1) = phaseStart T ∧ futureReplayed (T + 1) = futureReplayed T + 2 := by
  have h1 := phaseStart_le hT
  have hlog : Nat.log 2 (T + 1) = Nat.log 2 T := by
    rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, by omega⟩)]
    unfold phaseStart at h h1
    constructor
    · omega
    · rw [pow_succ]; omega
  have hps : phaseStart (T + 1) = phaseStart T := by unfold phaseStart; rw [hlog]
  refine ⟨hps, ?_⟩
  unfold futureReplayed
  rw [hps]
  omega

/-- At the phase boundary `T + 1 = 2N`, the future index has replayed exactly the whole
history (`2j = N + j` at `j = N`); the switch then starts a new phase at `2N` with an empty
future index. Paper: `lem:replayexactsampling` (attention_moment_decoder.tex); summarized after
`thm:main-decoder` (main_decoder.tex). -/
theorem catch_up {T : ℕ} (hT : 1 ≤ T) (h : T + 1 = 2 * phaseStart T) :
    futureReplayed T + 2 = T + 1 ∧ phaseStart (T + 1) = T + 1 ∧
      futureReplayed (T + 1) = 0 := by
  have h1 := phaseStart_le hT
  refine ⟨?_, ?_, ?_⟩
  · unfold futureReplayed; omega
  · unfold phaseStart at h ⊢
    rw [h, ← pow_succ', Nat.log_pow (by norm_num)]
  · have : phaseStart (T + 1) = T + 1 := by
      unfold phaseStart at h ⊢
      rw [h, ← pow_succ', Nat.log_pow (by norm_num)]
    unfold futureReplayed; rw [this]; simp

/-- A one-line fact, the availability invariant in phase coordinates: `2k ≤ N + k` for `k ≤ N`.
Paper: `lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem background_replay_available (N k : ℕ) (hk : k ≤ N) : 2 * k ≤ N + k := by omega

/-- A one-line fact, catching up in phase coordinates: after `N` appends of two replays each,
`2N = N + N`.
Paper: `lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem background_replay_catches_up (N : ℕ) : 2 * N = N + N := by omega

/-- The schedule after the first phase starts: if `N₀ = 2^a ≤ T` (with `N₀` the least power of
two at least the prompt length), then the current phase start `N` satisfies `N₀ ≤ N ≤ T < 2N`,
the future index has replayed at most `T` tokens, and the two replay tokens of the next append
exist. (Remark: the phase before `N₀`, where the initial index is used alone, is covered by the
state machine `ExactSampling.ReplaySchedule`.)
Paper: `lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem schedule_from_prompt (a T : ℕ) (hT : 2 ^ a ≤ T) :
    2 ^ a ≤ phaseStart T ∧ phaseStart T ≤ T ∧ T < 2 * phaseStart T ∧ futureReplayed T ≤ T ∧
      futureReplayed T + 2 ≤ T + 1 := by
  have h1 : 1 ≤ T := le_trans Nat.one_le_two_pow hT
  exact ⟨phaseStart_ge a T hT, phaseStart_le h1, lt_two_mul_phaseStart T, futureReplayed_le h1,
    next_replay_available h1⟩

end Schedule

end ExactSampling.CertifiedReplay
