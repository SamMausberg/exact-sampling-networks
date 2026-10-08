import Mathlib

/-!
# Indexed attention lower bound: the gadget and its algebra

This module formalizes the unconditional parts of the indexed-attention lower bound of
`attention_indexed_lower.tex` (`thm:indexedlower`, `thm:indexedlowerlogtwo`; restated as
`thm:main-index-hard` in `main_attention.tex`).

Formalized here:
* elementary `tanh` inequalities with `Real.tanh`: monotonicity, `tanh x ≥ x/2` and
  `tanh(tanh x) ≥ x/4` on `[0,1]`, and `tanh x ≥ (7/8)x` on `[0,1/4]`;
* the dummy-key gap: with a zero dummy key of value `-1` and real keys of value `+1`, the
  attention output is `u = (W-1)/(W+1)`; a nonnegative real score forces `π ≥ 1/2`, and real
  scores at most `-L` with `m e^{-L} ≤ 1/16` force `π ≤ 1/2 - 15/136 < 7/16`;
* `lem:indexedgadget` in full: the repeated `{0,-1}` keys and `{0,1}` query of width
  `n = (dL)²`, the score identity `⟨q,k_j⟩/√n = -L⟨a_j,b⟩`, and the token gap;
* the Hamming-gap gadget of `thm:indexedlowerlogtwo` in full: the bipolar identity
  `⟨q̂_b, k̂_a⟩ = 2(t - dist_H(a,b))` with `hammingDist`, the repetition to width `(2dH)²`, the
  score `2H(t - dist_H)`, and the token gap under the promise;
* the amplification arithmetic (thresholds `31/64`, `29/64`, `15/32`, the Hoeffding exponent
  with `K = 2048⌈log₂(24N²)⌉`, Markov's inequality, the total error `1/12`), the exponent
  algebra for every fixed preprocessing degree, and absorption of the logarithmic factor;
* `cor:indexedblock` and `cor:indexedlogtwoblock`: the role-gate rows; `cor:indexedprenorm`:
  `RMS₀(h) = h` on sign vectors, the floor `(n-1)/n`, the readout range, the token gap
  `1/2 - 105/1088 < 7/16`, and the stabilized variant for `0 ≤ ε₀ ≤ 1`;
* the remark translating entry bounds into width (score identity and rounding error).

Stand-ins and omissions: randomized OVH, Rubinstein's gap-Hamming reduction
(`lem:gaphamminghardness`), and Hoeffding's inequality are not formalized; the reduction itself,
the bit-complexity model, and the simulation with logging are described in prose only. The
corresponding statements below are the finite algebra used in those arguments.
-/

open Finset Filter MeasureTheory
open scoped BigOperators Topology ENNReal

namespace ExactSampling.IndexedLower

/-! ## Elementary `tanh` inequalities -/

section Tanh

/-- Auxiliary: `tanh x = (e^{2x}-1)/(e^{2x}+1)`. Supports the `tanh` inequalities in the proof of
`lem:indexedgadget` (attention_indexed_lower.tex). -/
lemma tanh_eq_exp (x : ℝ) : Real.tanh x = (Real.exp (2 * x) - 1) / (Real.exp (2 * x) + 1) := by
  rw [Real.tanh_eq]
  have hx : 0 < Real.exp x := Real.exp_pos x
  have h2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by rw [← Real.exp_add]; ring_nf
  have hn : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
  rw [h2, hn]
  field_simp

/-- Auxiliary: `tanh x = 1 - 2/(e^{2x}+1)`. Supports the monotonicity used in the proof of
`lem:indexedgadget` (attention_indexed_lower.tex). -/
lemma tanh_eq_one_sub (x : ℝ) : Real.tanh x = 1 - 2 / (Real.exp (2 * x) + 1) := by
  rw [tanh_eq_exp]
  have : 0 < Real.exp (2 * x) + 1 := by positivity
  field_simp; ring

/-- `tanh` is monotone. Supports `lem:indexedgadget` (attention_indexed_lower.tex). -/
theorem tanh_monotone : Monotone Real.tanh := by
  intro x y hxy
  rw [tanh_eq_one_sub, tanh_eq_one_sub]
  have h1 : Real.exp (2 * x) ≤ Real.exp (2 * y) := Real.exp_le_exp.mpr (by linarith)
  have h2 : 0 < Real.exp (2 * x) + 1 := by positivity
  have : 2 / (Real.exp (2 * y) + 1) ≤ 2 / (Real.exp (2 * x) + 1) :=
    div_le_div_of_nonneg_left (by norm_num) h2 (by linarith)
  linarith

/-- Auxiliary: `tanh x ≥ 0` for `x ≥ 0`. Supports the proof of `lem:indexedgadget`
(attention_indexed_lower.tex). -/
lemma tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  rw [tanh_eq_exp]
  apply div_nonneg _ (by positivity)
  have : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
  linarith

/-- `tanh x ≥ x/2` on `[0,1]`.
Paper: `lem:indexedgadget` (attention_indexed_lower.tex). -/
theorem tanh_ge_half {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x / 2 ≤ Real.tanh x := by
  rw [tanh_eq_exp]
  have he := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * x by linarith)
  have hpos : 0 < Real.exp (2 * x) + 1 := by positivity
  rw [le_div_iff₀ hpos]
  nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1), mul_nonneg hx0 hx0]

/-- `tanh(tanh x) ≥ x/4` on `[0,1]`.
Paper: `lem:indexedgadget` (attention_indexed_lower.tex), and the remark translating entry
bounds into width. -/
theorem tanh_tanh_ge_quarter {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 4 ≤ Real.tanh (Real.tanh x) := by
  have h1 := tanh_ge_half hx0 hx1
  have h2 : 0 ≤ Real.tanh x := tanh_nonneg hx0
  have h3 : Real.tanh x ≤ 1 := (Real.tanh_lt_one x).le
  have h4 := tanh_ge_half h2 h3
  linarith

/-- `tanh x ≥ (7/8)x` on `[0,1/4]`.
Paper: `cor:indexedprenorm` (attention_indexed_lower.tex). -/
theorem tanh_ge_seven_eighths {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 4) :
    7 / 8 * x ≤ Real.tanh x := by
  rw [tanh_eq_exp]
  have he := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * x by linarith)
  have hpos : 0 < Real.exp (2 * x) + 1 := by positivity
  rw [le_div_iff₀ hpos]
  nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1), mul_nonneg hx0 hx0,
    mul_nonneg (mul_nonneg hx0 hx0) (sub_nonneg.mpr hx1)]

end Tanh

/-! ## The dummy-key gap -/

section Dummy

/-- The scalar attention coordinate `∑_i e^{s_i} v_i / ∑_i e^{s_i}` over positions `P`. -/
noncomputable def attentionMean {P : Type*} [Fintype P] (score val : P → ℝ) : ℝ :=
  (∑ i, Real.exp (score i) * val i) / ∑ i, Real.exp (score i)

/-- The binary token probability `π = (1 + tanh(tanh u))/2` of `eq:indexedtarget`. -/
noncomputable def tokenProb (u : ℝ) : ℝ := (1 + Real.tanh (Real.tanh u)) / 2

/-- Scores and values with a zero dummy key of value `-1` and real keys of value `+1`. -/
def dummyScore {m : ℕ} (s : Fin m → ℝ) : Option (Fin m) → ℝ
  | none => 0
  | some j => s j

/-- Values with a dummy of value `-1` and real values `+1`. -/
def dummyVal {m : ℕ} : Option (Fin m) → ℝ
  | none => -1
  | some _ => 1

/-- With a dummy of weight one, the attention output is `u = (W - 1)/(W + 1)`, where
`W = ∑_j e^{s_j}`. Paper: `lem:indexedgadget` (attention_indexed_lower.tex). -/
theorem dummy_attention {m : ℕ} (s : Fin m → ℝ) :
    attentionMean (dummyScore s) dummyVal =
      (∑ j, Real.exp (s j) - 1) / (∑ j, Real.exp (s j) + 1) := by
  unfold attentionMean
  rw [Fintype.sum_option, Fintype.sum_option]
  simp only [dummyScore, dummyVal, Real.exp_zero, mul_one]
  ring_nf

/-- The dummy mean `(W-1)/(W+1)` is nonnegative for `W ≥ 1`. Supports `lem:indexedgadget`
(attention_indexed_lower.tex). -/
theorem dummy_yes (w : ℝ) (hw : 1 ≤ w) : 0 ≤ (w - 1) / (w + 1) :=
  div_nonneg (by linarith) (by linarith)

/-- The dummy mean is at most `-15/17` for `0 ≤ W ≤ 1/16`. Supports `lem:indexedgadget`
(attention_indexed_lower.tex). -/
theorem dummy_no (w : ℝ) (hw0 : 0 ≤ w) (hw : w ≤ 1 / 16) : (w - 1) / (w + 1) ≤ -(15 / 17 : ℝ) := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- The dummy mean lies in `[-1, 1]`. Supports `lem:indexedgadget` (attention_indexed_lower.tex). -/
theorem dummy_in_interval (w : ℝ) (hw : 0 ≤ w) :
    -1 ≤ (w - 1) / (w + 1) ∧ (w - 1) / (w + 1) ≤ 1 := by
  have hd : 0 < w + 1 := by linarith
  constructor
  · rw [le_div_iff₀ hd]; nlinarith
  · rw [div_le_iff₀ hd]; nlinarith

/-- Yes case of the dummy-key gap: one real score at least zero gives `π ≥ 1/2`.
Paper: `lem:indexedgadget` (attention_indexed_lower.tex). -/
theorem dummy_gap_yes {m : ℕ} (s : Fin m → ℝ) (j : Fin m) (hj : 0 ≤ s j) :
    1 / 2 ≤ tokenProb (attentionMean (dummyScore s) dummyVal) := by
  rw [dummy_attention]
  have hW : 1 ≤ ∑ j, Real.exp (s j) := by
    calc (1 : ℝ) ≤ Real.exp (s j) := Real.one_le_exp hj
      _ ≤ ∑ j, Real.exp (s j) :=
        Finset.single_le_sum (f := fun j => Real.exp (s j)) (fun i _ => (Real.exp_pos _).le)
          (Finset.mem_univ j)
  have hu := dummy_yes _ hW
  unfold tokenProb
  have := tanh_nonneg (tanh_nonneg hu)
  linarith

/-- No case of the dummy-key gap: if every real score is at most `-L` and `m e^{-L} ≤ 1/16`,
then `π ≤ 1/2 - 15/136 < 7/16`.
Paper: `lem:indexedgadget` (attention_indexed_lower.tex). -/
theorem dummy_gap_no {m : ℕ} (s : Fin m → ℝ) (L : ℝ) (hs : ∀ j, s j ≤ -L)
    (hmL : m * Real.exp (-L) ≤ 1 / 16) :
    tokenProb (attentionMean (dummyScore s) dummyVal) ≤ 1 / 2 - 15 / 136 ∧
      (1 / 2 - 15 / 136 : ℝ) < 7 / 16 := by
  refine ⟨?_, by norm_num⟩
  rw [dummy_attention]
  set W := ∑ j, Real.exp (s j) with hWdef
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun j _ => (Real.exp_pos _).le
  have hW : W ≤ 1 / 16 := by
    calc W ≤ ∑ _j : Fin m, Real.exp (-L) :=
          Finset.sum_le_sum fun j _ => Real.exp_le_exp.mpr (hs j)
      _ = m * Real.exp (-L) := by simp
      _ ≤ 1 / 16 := hmL
  have hu := dummy_no W hW0 hW
  have hu1 := (dummy_in_interval W hW0).1
  set u := (W - 1) / (W + 1)
  have h1 := tanh_tanh_ge_quarter (x := -u) (by linarith) (by linarith)
  rw [Real.tanh_neg, Real.tanh_neg] at h1
  unfold tokenProb
  linarith

/-- `e^{-L} ≤ 2^{-L}`, so `m e^{-L} ≤ 1/16` once `2^L ≥ 16m`.
Paper: `lem:indexedgadget` (attention_indexed_lower.tex), `m e^{-L} ≤ m 2^{-L} ≤ 1/16`. -/
theorem weight_budget (m L : ℕ) (hL : 16 * m ≤ 2 ^ L) : (m : ℝ) * Real.exp (-(L : ℝ)) ≤ 1 / 16 := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hexp : (2 : ℝ) ^ L ≤ Real.exp L := by
    rw [show (L : ℝ) = L * 1 by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) he L
  have hL' : (16 * m : ℝ) ≤ 2 ^ L := by exact_mod_cast hL
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  linarith

end Dummy

/-! ## The orthogonality gadget (`lem:indexedgadget`) -/

section Gadget

/-- The `{0,1}` inner product `⟨a, b⟩ = #{i : a_i ∧ b_i}`. -/
def boolDot {d : ℕ} (a b : Fin d → Bool) : ℕ := (Finset.univ.filter fun i => a i && b i).card

/-- Repeating every coordinate `r` times multiplies a coordinate sum by `r`. Supports
`lem:indexedgadget` (attention_indexed_lower.tex). -/
lemma sum_repeat {ι : Type*} [Fintype ι] (r : ℕ) (f : ι → ℝ) :
    ∑ ik : ι × Fin r, f ik.1 = r * ∑ i, f i := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- Auxiliary: the `{0,1}` inner product as a real sum. Supports the score identity of
`lem:indexedgadget` (attention_indexed_lower.tex). -/
lemma boolDot_eq_sum {d : ℕ} (a b : Fin d → Bool) :
    ((boolDot a b : ℕ) : ℝ) = ∑ i, (if a i then (1 : ℝ) else 0) * (if b i then 1 else 0) := by
  unfold boolDot
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  cases a i <;> cases b i <;> simp

/-- The dummy-key gadget: with `L = ⌈log₂(16m)⌉`, `r = dL²`, width `n = d·r = (dL)²`, keys
repeating `-a_j` and the query repeating `b`, the standard-scaled scores are
`⟨q, k_j⟩/√n = -L⟨a_j, b⟩`; an orthogonal pair gives `π ≥ 1/2`, and otherwise
`π ≤ 1/2 - 15/136 < 7/16`. Paper: `lem:indexedgadget` (attention_indexed_lower.tex). -/
theorem indexed_gadget (m d : ℕ) (hd : 1 ≤ d) (A : Fin m → Fin d → Bool) (b : Fin d → Bool) :
    let L := Nat.clog 2 (16 * m)
    let r := d * L ^ 2
    let q : Fin d × Fin r → ℝ := fun ik => if b ik.1 then 1 else 0
    let key : Fin m → Fin d × Fin r → ℝ := fun j ik => if A j ik.1 then -1 else 0
    let score : Fin m → ℝ := fun j =>
      (∑ ik, q ik * key j ik) / Real.sqrt (Fintype.card (Fin d × Fin r))
    (Fintype.card (Fin d × Fin r) = (d * L) ^ 2) ∧
      (∀ j, score j = -(L : ℝ) * boolDot (A j) b) ∧
      ((∃ j, boolDot (A j) b = 0) → 1 / 2 ≤ tokenProb (attentionMean (dummyScore score) dummyVal)) ∧
      ((∀ j, boolDot (A j) b ≠ 0) →
        tokenProb (attentionMean (dummyScore score) dummyVal) ≤ 1 / 2 - 15 / 136) := by
  intro L r q key score
  have hcard : Fintype.card (Fin d × Fin r) = (d * L) ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_fin, r]; ring
  have hsum : ∀ j, ∑ ik, q ik * key j ik = -(r : ℝ) * boolDot (A j) b := by
    intro j
    have := sum_repeat r (fun i => (if b i then (1 : ℝ) else 0) * (if A j i then -1 else 0))
    simp only [q, key]
    rw [this, boolDot_eq_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases ha : A j i <;> by_cases hb : b i <;> simp [ha, hb]
  have hsqrt : Real.sqrt (Fintype.card (Fin d × Fin r) : ℝ) = d * L := by
    rw [hcard]; push_cast; exact Real.sqrt_sq (by positivity)
  have hscore : ∀ j, score j = -(L : ℝ) * boolDot (A j) b := by
    intro j
    show (∑ ik, q ik * key j ik) / Real.sqrt (Fintype.card (Fin d × Fin r)) = _
    rw [hsum, hsqrt]
    rcases Nat.eq_zero_or_pos L with hL | hL
    · simp [r, hL]
    · have hdL : (d : ℝ) * L ≠ 0 := by
        have : (0 : ℝ) < d := by exact_mod_cast hd
        have : (0 : ℝ) < L := by exact_mod_cast hL
        positivity
      field_simp
      simp only [r]; push_cast; ring
  refine ⟨hcard, hscore, ?_, ?_⟩
  · rintro ⟨j, hj⟩
    apply dummy_gap_yes score j
    rw [hscore j, hj]; simp
  · intro hno
    have hbudget := weight_budget m L (Nat.le_pow_clog (by norm_num) _)
    refine (dummy_gap_no score L ?_ hbudget).1
    intro j
    rw [hscore j]
    have h1 : (1 : ℝ) ≤ boolDot (A j) b := by
      have := Nat.one_le_iff_ne_zero.mpr (hno j); exact_mod_cast this
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    nlinarith

end Gadget

/-! ## The Hamming-gap gadget (`thm:indexedlowerlogtwo`) -/

section Hamming

/-- Bipolar encoding `0 ↦ -1`, `1 ↦ +1`. -/
def bip (x : Bool) : ℝ := if x then 1 else -1

/-- `∑_i (2a_i - 1)(2b_i - 1) = d - 2 dist_H(a,b)`.
Paper: `thm:indexedlowerlogtwo`, display `eq:gaphammingdot` (attention_indexed_lower.tex). -/
theorem bipolar_dot {d : ℕ} (a b : Fin d → Bool) :
    ∑ i, bip (b i) * bip (a i) = d - 2 * (hammingDist a b : ℝ) := by
  have h : ∀ i, bip (b i) * bip (a i) = 1 - 2 * (if a i ≠ b i then (1 : ℝ) else 0) := by
    intro i; by_cases ha : a i <;> by_cases hb : b i <;> simp [bip, ha, hb] <;> norm_num
  simp_rw [h]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  simp [hammingDist]

/-- With padding `c_t` satisfying `∑ c_t = 2t - d`, the gap-Hamming dot product is
`⟨q̂_b, k̂_a⟩ = d - 2 dist_H(a,b) + (2t - d) = 2(t - dist_H(a,b))`.
Paper: `thm:indexedlowerlogtwo`, display `eq:gaphammingdot` (attention_indexed_lower.tex). -/
theorem gap_hamming_dot {d t : ℕ} (a b : Fin d → Bool) (c : Fin d → ℝ)
    (hc : ∑ i, c i = 2 * t - d) :
    ∑ i, bip (b i) * bip (a i) + ∑ i, 1 * c i = 2 * ((t : ℝ) - hammingDist a b) := by
  rw [bipolar_dot]; simp only [one_mul]; rw [hc]; ring

/-- The Hamming-gap gadget: with `r = 2dH²` repetitions of the `2d` coordinates of
`k̂_a = (2a-1, c_t)` and `q̂_b = (2b-1, 1)`, the width is `n = (2dH)²` and the standard-scaled
score is `2H(t - dist_H(a,b))`. In a yes pair (`dist_H ≤ t` for some key) `π ≥ 1/2`; if every
key has `dist_H ≥ (1+ζ)t`, `L ≤ 2Hζt`, and `16m ≤ 2^L`, then `π ≤ 1/2 - 15/136`.
Paper: `thm:indexedlowerlogtwo` (attention_indexed_lower.tex). -/
theorem hamming_gadget (m d t H L : ℕ) (hd : 1 ≤ d) (hH : 1 ≤ H) (A : Fin m → Fin d → Bool)
    (b : Fin d → Bool) (c : Fin d → ℝ) (hc : ∑ i, c i = 2 * t - d) (ζ : ℝ) :
    let r := 2 * d * H ^ 2
    let key : Fin m → (Fin d ⊕ Fin d) × Fin r → ℝ := fun j ik =>
      Sum.elim (fun i => bip (A j i)) c ik.1
    let q : (Fin d ⊕ Fin d) × Fin r → ℝ := fun ik => Sum.elim (fun i => bip (b i)) (fun _ => 1) ik.1
    let score : Fin m → ℝ := fun j =>
      (∑ ik, q ik * key j ik) / Real.sqrt (Fintype.card ((Fin d ⊕ Fin d) × Fin r))
    (Fintype.card ((Fin d ⊕ Fin d) × Fin r) = (2 * d * H) ^ 2) ∧
      (∀ j, score j = 2 * H * ((t : ℝ) - hammingDist (A j) b)) ∧
      ((∃ j, hammingDist (A j) b ≤ t) →
        1 / 2 ≤ tokenProb (attentionMean (dummyScore score) dummyVal)) ∧
      ((∀ j, (1 + ζ) * t ≤ hammingDist (A j) b) → (L : ℝ) ≤ 2 * H * ζ * t → 16 * m ≤ 2 ^ L →
        tokenProb (attentionMean (dummyScore score) dummyVal) ≤ 1 / 2 - 15 / 136) := by
  intro r key q score
  have hcard : Fintype.card ((Fin d ⊕ Fin d) × Fin r) = (2 * d * H) ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, r]; ring
  have hsum : ∀ j, ∑ ik, q ik * key j ik = r * (2 * ((t : ℝ) - hammingDist (A j) b)) := by
    intro j
    have := sum_repeat r (fun s => Sum.elim (fun i => bip (b i)) (fun _ => (1 : ℝ)) s *
      Sum.elim (fun i => bip (A j i)) c s)
    simp only [q, key]
    rw [this, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [gap_hamming_dot (A j) b c hc]
  have hsqrt : Real.sqrt (Fintype.card ((Fin d ⊕ Fin d) × Fin r) : ℝ) = 2 * d * H := by
    rw [hcard]; push_cast; exact Real.sqrt_sq (by positivity)
  have hscore : ∀ j, score j = 2 * H * ((t : ℝ) - hammingDist (A j) b) := by
    intro j
    show (∑ ik, q ik * key j ik) / Real.sqrt (Fintype.card ((Fin d ⊕ Fin d) × Fin r)) = _
    rw [hsum, hsqrt]
    have hdH : (2 : ℝ) * d * H ≠ 0 := by
      have : (0 : ℝ) < d := by exact_mod_cast hd
      have : (0 : ℝ) < H := by exact_mod_cast hH
      positivity
    field_simp
    simp only [r]; push_cast; ring
  refine ⟨hcard, hscore, ?_, ?_⟩
  · rintro ⟨j, hj⟩
    apply dummy_gap_yes score j
    rw [hscore j]
    have : (hammingDist (A j) b : ℝ) ≤ t := by exact_mod_cast hj
    have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
    nlinarith
  · intro hno hLH hL
    refine (dummy_gap_no score L ?_ (weight_budget m L hL)).1
    intro j
    rw [hscore j]
    have h1 := hno j
    have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
    nlinarith

/-- A far pair has score at most `-L` when `L ≤ 2Hζt`.
Paper: `thm:indexedlowerlogtwo` (attention_indexed_lower.tex). -/
theorem far_score_bound (H ζ t distance L : ℝ) (hH : 0 ≤ H) (hfar : (1 + ζ) * t ≤ distance)
    (hscale : L ≤ 2 * H * ζ * t) : 2 * H * (t - distance) ≤ -L := by
  have hp : 0 ≤ H * (distance - (1 + ζ) * t) := mul_nonneg hH (sub_nonneg.mpr hfar)
  nlinarith

/-- A near pair has nonnegative score.
Paper: `thm:indexedlowerlogtwo` (attention_indexed_lower.tex). -/
theorem near_score_nonnegative (H t distance : ℝ) (hH : 0 ≤ H) (hnear : distance ≤ t) :
    0 ≤ 2 * H * (t - distance) := by
  have hsub : 0 ≤ t - distance := sub_nonneg.mpr hnear
  positivity

end Hamming

/-! ## Amplification and exponents (`thm:indexedlower`) -/

section Amplification

/-- With total-variation error `1/64`, a yes output succeeds with probability at least `31/64`.
Paper: `thm:indexedlower` (attention_indexed_lower.tex). -/
theorem tv_yes_threshold (target actual : ℝ) (ht : 1 / 2 ≤ target)
    (herr : |actual - target| ≤ 1 / 64) : 31 / 64 ≤ actual := by
  have h := (abs_le.mp herr).1
  linarith

/-- With total-variation error `1/64`, a no output succeeds with probability at most `29/64`.
Paper: `thm:indexedlower` (attention_indexed_lower.tex). -/
theorem tv_no_threshold (target actual : ℝ) (ht : target ≤ 7 / 16)
    (herr : |actual - target| ≤ 1 / 64) : actual ≤ 29 / 64 := by
  have h := (abs_le.mp herr).2
  linarith

/-- The threshold `15/32` lies at distance `1/64` from both success bounds.
Paper: `thm:indexedlower` (attention_indexed_lower.tex). -/
theorem classification_margin :
    (15 / 32 - 29 / 64 : ℝ) = 1 / 64 ∧ (31 / 64 - 15 / 32 : ℝ) = 1 / 64 := by norm_num

/-- The Hoeffding exponent: `2K(1/64)² = K/2048`.
Paper: `thm:indexedlower` (attention_indexed_lower.tex). -/
theorem hoeffding_exponent (K : ℝ) : 2 * K * (1 / 64 : ℝ) ^ 2 = K / 2048 := by ring

/-- With `K = 2048 ⌈log₂(24N²)⌉` independent copies, the Hoeffding bound is
`exp(-2K(1/64)²) ≤ 1/(24N²)`.
Paper: `thm:indexedlower` (attention_indexed_lower.tex). -/
theorem hoeffding_copies (N : ℕ) (hN : 1 ≤ N) :
    Real.exp (-(2 * (2048 * Nat.clog 2 (24 * N ^ 2) : ℕ) * (1 / 64 : ℝ) ^ 2)) ≤
      1 / (24 * (N : ℝ) ^ 2) := by
  set c := Nat.clog 2 (24 * N ^ 2)
  have hc : 24 * N ^ 2 ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) _
  have hc' : (24 * (N : ℝ) ^ 2) ≤ 2 ^ c := by exact_mod_cast hc
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hexp : (2 : ℝ) ^ c ≤ Real.exp c := by
    rw [show (c : ℝ) = c * 1 by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) he c
  have heq : -(2 * ((2048 * c : ℕ) : ℝ) * (1 / 64 : ℝ) ^ 2) = -(c : ℝ) := by push_cast; ring
  rw [heq, Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

/-- Union bound over at most `N²` bucket-query pairs plus the Markov truncation error:
`N² · 1/(24N²) + 1/24 = 1/12 < 1/3`.
Paper: `thm:indexedlower` (attention_indexed_lower.tex). -/
theorem total_error (N : ℝ) (hN : 0 < N) :
    N ^ 2 * (1 / (24 * N ^ 2)) + 1 / 24 = 1 / 12 ∧ (1 / 12 : ℝ) < 1 / 3 := by
  constructor
  · field_simp; ring
  · norm_num

/-- Markov's inequality for the runtime cutoff: a nonnegative work variable with mean at most
`F > 0` exceeds `24F` with probability at most `1/24`.
Paper: `thm:indexedlower` (attention_indexed_lower.tex). -/
theorem runtime_cutoff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (work : Ω → ℝ≥0∞)
    (hw : AEMeasurable work μ) (F : ℝ≥0∞) (hF0 : F ≠ 0) (hFtop : F ≠ ⊤)
    (hmean : ∫⁻ ω, work ω ∂μ ≤ F) : μ {ω | 24 * F ≤ work ω} ≤ 1 / 24 := by
  have h24 : (24 : ℝ≥0∞) * F ≠ 0 := mul_ne_zero (by norm_num) hF0
  calc μ {ω | 24 * F ≤ work ω} ≤ (∫⁻ ω, work ω ∂μ) / (24 * F) :=
        meas_ge_le_lintegral_div hw h24 (ENNReal.mul_ne_top (by norm_num) hFtop)
    _ ≤ F / (24 * F) := by gcongr
    _ = 1 / 24 := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
          mul_comm, mul_left_comm, ENNReal.mul_inv_cancel hF0 hFtop, mul_one, one_div]

/-- Exponent algebra for fixed preprocessing degree `a ≥ 1` and query saving `0 < ε < 1`, with
`γ = 1/(2(a+1))`: `γ(a-1) < 1/2`, `γε < 1/4`, and both the preprocessing exponent
`1 + γ(a-1)` and the query exponent `2 - γε` are below `2 - 3γε/4`.
Paper: `thm:indexedlower` (attention_indexed_lower.tex). -/
theorem exponent_algebra (a ε : ℝ) (ha : 1 ≤ a) (hε0 : 0 < ε) (hε1 : ε < 1) :
    let γ := 1 / (2 * (a + 1))
    γ * (a - 1) < 1 / 2 ∧ γ * ε < 1 / 4 ∧ 1 + γ * (a - 1) < 2 - 3 * γ * ε / 4 ∧
      2 - γ * ε < 2 - 3 * γ * ε / 4 := by
  intro γ
  have hγ : 0 < γ := by positivity
  have hγa : γ * (2 * (a + 1)) = 1 := by
    show 1 / (2 * (a + 1)) * (2 * (a + 1)) = 1
    field_simp
  have hγ4 : γ ≤ 1 / 4 := by
    rw [show γ = 1 / (2 * (a + 1)) from rfl, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- Bucketing costs: with bucket size `m = N^γ`, preprocessing `(N/m) m^a = N^{1+γ(a-1)}` and
queries `N² m^{-1} m^{1-ε} = N^{2-γε}`.
Paper: `thm:indexedlower` (attention_indexed_lower.tex). -/
theorem bucket_exponents (N γ a ε : ℝ) (hN : 0 < N) :
    N ^ (1 - γ) * (N ^ γ) ^ a = N ^ (1 + γ * (a - 1)) ∧
      N ^ (2 - γ) * (N ^ γ) ^ (1 - ε) = N ^ (2 - γ * ε) := by
  constructor
  · rw [← Real.rpow_mul hN.le, ← Real.rpow_add hN]; ring_nf
  · rw [← Real.rpow_mul hN.le, ← Real.rpow_add hN]; ring_nf

/-- The logarithmic overhead of the bounded simulation is absorbed:
`N^{2-3γε/4} log N ≤ N^{2-γε/2}` for all sufficiently large `N`.
Paper: `thm:indexedlower` (attention_indexed_lower.tex). -/
theorem log_absorption (γ ε : ℝ) (hγε : 0 < γ * ε) :
    ∀ᶠ N : ℝ in atTop, N ^ (2 - 3 * γ * ε / 4) * Real.log N ≤ N ^ (2 - γ * ε / 2) := by
  have ho := (isLittleO_log_rpow_atTop (show 0 < γ * ε / 4 by linarith)).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [ho, eventually_gt_atTop 1] with N hN hN1
  have hNpos : 0 < N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1.le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog,
    abs_of_pos (Real.rpow_pos_of_pos hNpos _), one_mul] at hN
  calc N ^ (2 - 3 * γ * ε / 4) * Real.log N ≤ N ^ (2 - 3 * γ * ε / 4) * N ^ (γ * ε / 4) := by
        gcongr
    _ = N ^ (2 - γ * ε / 2) := by rw [← Real.rpow_add hNpos]; ring_nf

/-- The preprocessing saving: `γ·2(a+1) = 1` gives `1 + γ(a-1) < 3/2`.
Paper: `thm:indexedlower` (attention_indexed_lower.tex). -/
theorem preprocessing_exponent_saving (a γ : ℝ) (hγ : 0 < γ)
    (hscale : γ * (2 * (a + 1)) = 1) : 1 + γ * (a - 1) < 3 / 2 := by
  nlinarith

/-- The query saving `2 - γε < 2`. Paper: `thm:indexedlower` (attention_indexed_lower.tex). -/
theorem query_exponent_saving (γ ε : ℝ) (hγ : 0 < γ) (hε : 0 < ε) : 2 - γ * ε < (2 : ℝ) := by
  nlinarith [mul_pos hγ hε]

/-- Reserving half of the query saving: `2 - γε < 2 - γε/2`. Paper: `thm:indexedlower`
(attention_indexed_lower.tex). -/
theorem reserve_half_exponent (γ ε : ℝ) (hγ : 0 < γ) (hε : 0 < ε) :
    2 - γ * ε < 2 - γ * ε / 2 := by
  nlinarith [mul_pos hγ hε]

end Amplification

/-! ## Legal block realizations (`cor:indexedblock`, `cor:indexedprenorm`) -/

section Realization

/-- Role gates of the one-block realization: the half-sum query row reads `b` at the query
position and `0` at cache positions; the negated half-sum key row reads `-a` at cache positions
and `0` at the query position. Each row has absolute sum one.
Paper: `cor:indexedblock` (attention_indexed_lower.tex). -/
theorem role_gates (a b : ℝ) :
    ((-1 : ℝ) + 1) / 2 = 0 ∧ -(((2 * a - 1) + 1) / 2) = -a ∧ ((2 * b - 1) + 1) / 2 = b ∧
      -(((-1 : ℝ) + 1) / 2) = 0 ∧ |(1 : ℝ) / 2| + |(1 : ℝ) / 2| = 1 := by
  refine ⟨by norm_num, by ring, by ring, by norm_num, by norm_num⟩

/-- Opposite sign pairs: half the difference of `(x, -x)` is `x`, and of `(1, 1)` is `0`; the
padding rows `c_i (c + v)/2` and `(c - v)/2` select the cache and query roles.
Paper: `cor:indexedlogtwoblock` (attention_indexed_lower.tex). -/
theorem pair_gates (x ci : ℝ) :
    (x - (-x)) / 2 = x ∧ ((1 : ℝ) - 1) / 2 = 0 ∧ ci * ((1 + 1) / 2) = ci ∧
      ci * ((1 + -1) / 2) = 0 ∧ ((1 : ℝ) - 1) / 2 = 0 ∧ ((1 : ℝ) - -1) / 2 = 1 := by
  refine ⟨by ring, by norm_num, by ring, by ring, by norm_num, by norm_num⟩

/-- `RMS₀(h) = h` on sign vectors: the mean squared coordinate is one.
Paper: `cor:indexedprenorm` (attention_indexed_lower.tex). -/
theorem rms_sign {n : ℕ} (hn : 0 < n) (h : Fin n → ℝ) (hs : ∀ i, h i ^ 2 = 1) :
    (fun i => h i / Real.sqrt (∑ j, h j ^ 2 / n)) = h := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have : ∑ j, h j ^ 2 / n = 1 := by
    simp only [hs]; rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  funext i
  rw [this, Real.sqrt_one, div_one]

/-- After one coordinate is updated, the mean square stays at least `(n-1)/n`.
Paper: `cor:indexedprenorm` (attention_indexed_lower.tex). -/
theorem known_floor_after_one_update (n altered : ℝ) (hn : 0 < n) :
    (n - 1) / n ≤ ((n - 1) + altered ^ 2) / n := by
  apply div_le_div_of_nonneg_right _ hn.le
  nlinarith [sq_nonneg altered]

/-- The readout `((-1 + u) + 1)/4 = u/4`.
Paper: `cor:indexedprenorm` (attention_indexed_lower.tex). -/
theorem additive_head_identity (u : ℝ) : ((-1 + u) + 1) / 4 = u / 4 := by ring

/-- On the whole sign cube the quarter-sum readout lies in `[-3/4, 3/4]`.
Paper: `cor:indexedprenorm` (attention_indexed_lower.tex). -/
theorem additive_global_head_range (marker constant update : ℝ)
    (hm0 : -1 ≤ marker) (hm1 : marker ≤ 1) (hc0 : -1 ≤ constant) (hc1 : constant ≤ 1)
    (hu0 : -1 ≤ update) (hu1 : update ≤ 1) :
    -(3 / 4 : ℝ) ≤ (marker + update + constant) / 4 ∧
      (marker + update + constant) / 4 ≤ 3 / 4 := by
  constructor <;> linarith

/-- The pre-norm token gap: with readout `u/4`, the yes case `u ≥ 0` has
`(1 + tanh(u/4))/2 ≥ 1/2`, and the no case `-1 ≤ u ≤ -15/17` has
`(1 + tanh(u/4))/2 ≤ 1/2 - 105/1088 < 7/16`.
Paper: `cor:indexedprenorm` (attention_indexed_lower.tex). -/
theorem prenorm_gap (u : ℝ) :
    (0 ≤ u → 1 / 2 ≤ (1 + Real.tanh (u / 4)) / 2) ∧
      (-1 ≤ u → u ≤ -(15 / 17) → (1 + Real.tanh (u / 4)) / 2 ≤ 1 / 2 - 105 / 1088) ∧
      (1 / 2 - 105 / 1088 : ℝ) < 7 / 16 := by
  refine ⟨fun hu => ?_, fun hu1 hu2 => ?_, by norm_num⟩
  · have := tanh_nonneg (show 0 ≤ u / 4 by linarith); linarith
  · have h := tanh_ge_seven_eighths (x := -(u / 4)) (by linarith) (by linarith)
    rw [Real.tanh_neg] at h
    linarith

/-- A fixed stabilizer `0 ≤ ε₀ ≤ 1` keeps the displayed thresholds: the readout becomes
`u/(4√(1+ε₀))`, and for `-1 ≤ u ≤ -15/17` the token probability is at most `7/16`.
Paper: `cor:indexedprenorm` (attention_indexed_lower.tex), the paragraph on a positive
stabilizer. -/
theorem stabilized_gap (u ε0 : ℝ) (hε0 : 0 ≤ ε0) (hε1 : ε0 ≤ 1) (hu1 : -1 ≤ u)
    (hu2 : u ≤ -(15 / 17)) : (1 + Real.tanh (u / (4 * Real.sqrt (1 + ε0)))) / 2 ≤ 7 / 16 := by
  have hs1 : 1 ≤ Real.sqrt (1 + ε0) := by rw [Real.one_le_sqrt]; linarith
  have hs2 : Real.sqrt (1 + ε0) ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  set s := Real.sqrt (1 + ε0)
  have h4s : 0 < 4 * s := by linarith
  have hx1 : -u / (4 * s) ≤ 1 / 4 := by
    rw [div_le_iff₀ h4s]; nlinarith
  have hx2 : 5 / 34 ≤ -u / (4 * s) := by
    rw [le_div_iff₀ h4s]; nlinarith
  have ht := tanh_ge_seven_eighths (x := -u / (4 * s)) (by linarith) hx1
  have hneg : u / (4 * s) = -(-u / (4 * s)) := by ring
  rw [hneg, Real.tanh_neg]
  linarith

/-- Changing the stabilized score scale: normalized queries and keys give `⟨q,k⟩/(1+ε₀)`, and a
penalty `L' ≥ (1+ε₀)L` restores the score gap `-L`.
Paper: `cor:indexedprenorm` (attention_indexed_lower.tex). -/
theorem stabilized_score (L L' ε0 dot : ℝ) (hε0 : 0 ≤ ε0) (hL : (1 + ε0) * L ≤ L')
    (hdot : 1 ≤ dot) (hL0 : 0 ≤ L) : -L' * dot / (1 + ε0) ≤ -L := by
  rw [div_le_iff₀ (by linarith)]
  have hL'0 : 0 ≤ L' := le_trans (mul_nonneg (by linarith) hL0) hL
  nlinarith [mul_nonneg hL'0 (sub_nonneg.mpr hdot)]

end Realization

/-! ## Translating entry bounds into width (remark after `thm:indexedlower`) -/

section Translation

/-- Repetition by `dH²` after scaling by `1/√(dH)` turns the standard-scaled score at width
`n = (dH)²` into the old score `⟨q,k⟩/d`.
Paper: remark "Translating entry bounds into width" after `thm:indexedlower`
(attention_indexed_lower.tex). -/
theorem entry_translation {d : ℕ} (H : ℕ) (hd : 1 ≤ d) (hH : 1 ≤ H) (q k : Fin d → ℝ) :
    (∑ ik : Fin d × Fin (d * H ^ 2), (q ik.1 / Real.sqrt (d * H)) * (k ik.1 / Real.sqrt (d * H)))
        / Real.sqrt (((d * H) ^ 2 : ℕ) : ℝ) = (∑ i, q i * k i) / d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hsq : Real.sqrt ((d : ℝ) * H) ^ 2 = d * H := Real.sq_sqrt (by positivity)
  have hspos : 0 < Real.sqrt ((d : ℝ) * H) := Real.sqrt_pos.mpr (by positivity)
  rw [sum_repeat (d * H ^ 2) (fun i => (q i / Real.sqrt (d * H)) * (k i / Real.sqrt (d * H)))]
  have hn : Real.sqrt (((d * H) ^ 2 : ℕ) : ℝ) = d * H := by
    push_cast; exact Real.sqrt_sq (by positivity)
  rw [hn]
  have : ∀ i, (q i / Real.sqrt (d * H)) * (k i / Real.sqrt (d * H)) = q i * k i / (d * H) := by
    intro i; rw [div_mul_div_comm, ← sq, hsq]
  simp_rw [this]
  rw [← Finset.sum_div]
  push_cast
  field_simp

/-- Rounding new coordinates within `η ≤ 1/(100√n)` while keeping them in `[-1,1]` changes every
standard-scaled score by at most `√n(2η + η²) ≤ 0.03`.
Paper: remark "Translating entry bounds into width" (attention_indexed_lower.tex). -/
theorem rounding_score_error {n : ℕ} (hn : 1 ≤ n) (q k q' k' : Fin n → ℝ) (η : ℝ) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / (100 * Real.sqrt n)) (hq : ∀ i, |q i| ≤ 1) (hk : ∀ i, |k i| ≤ 1)
    (hdq : ∀ i, |q' i - q i| ≤ η) (hdk : ∀ i, |k' i - k i| ≤ η) :
    |(∑ i, q' i * k' i) / Real.sqrt n - (∑ i, q i * k i) / Real.sqrt n| ≤
        Real.sqrt n * (2 * η + η ^ 2) ∧ Real.sqrt n * (2 * η + η ^ 2) ≤ 3 / 100 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs1 : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact hn'
  have hspos : 0 < Real.sqrt n := by linarith
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by linarith)
  constructor
  · rw [← sub_div, abs_div, abs_of_pos hspos, div_le_iff₀ hspos, ← Finset.sum_sub_distrib]
    calc |∑ i, (q' i * k' i - q i * k i)| ≤ ∑ i, |q' i * k' i - q i * k i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, (2 * η + η ^ 2) := by
          apply Finset.sum_le_sum; intro i _
          have e : q' i * k' i - q i * k i = (q' i - q i) * k i + q i * (k' i - k i) +
              (q' i - q i) * (k' i - k i) := by ring
          rw [e]
          calc |(q' i - q i) * k i + q i * (k' i - k i) + (q' i - q i) * (k' i - k i)|
              ≤ |(q' i - q i) * k i| + |q i * (k' i - k i)| + |(q' i - q i) * (k' i - k i)| :=
                abs_add_three _ _ _
            _ = |q' i - q i| * |k i| + |q i| * |k' i - k i| + |q' i - q i| * |k' i - k i| := by
                rw [abs_mul, abs_mul, abs_mul]
            _ ≤ η * 1 + 1 * η + η * η := by
                gcongr
                · exact hdq i
                · exact hk i
                · exact hq i
                · exact hdk i
                · exact hdq i
                · exact hdk i
            _ = 2 * η + η ^ 2 := by ring
      _ = n * (2 * η + η ^ 2) := by simp; ring
      _ = Real.sqrt n * Real.sqrt n * (2 * η + η ^ 2) := by
          rw [Real.mul_self_sqrt (by linarith)]
      _ = Real.sqrt n * (2 * η + η ^ 2) * Real.sqrt n := by ring
  · have h1 : Real.sqrt n * η ≤ 1 / 100 := by
      rw [le_div_iff₀ (by positivity)] at hη
      nlinarith
    have h2 : η ≤ 1 / 100 := by
      have : 1 / (100 * Real.sqrt n) ≤ 1 / 100 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); nlinarith
      linarith
    nlinarith

/-- Once the two cases have `u ≥ 1/2` and `u ≤ -1/2`, the token map separates them by `9/16`
and `7/16`. Paper: remark "Translating entry bounds into width"
(attention_indexed_lower.tex). -/
theorem translated_separation (u : ℝ) (hu1 : -1 ≤ u) (hu2 : u ≤ 1) :
    (1 / 2 ≤ u → 9 / 16 ≤ tokenProb u) ∧ (u ≤ -(1 / 2) → tokenProb u ≤ 7 / 16) := by
  unfold tokenProb
  constructor
  · intro h
    have := tanh_tanh_ge_quarter (x := u) (by linarith) hu2
    linarith
  · intro h
    have := tanh_tanh_ge_quarter (x := -u) (by linarith) (by linarith)
    rw [Real.tanh_neg, Real.tanh_neg] at this
    linarith

end Translation

/-! ## The finite algebra of the gadgets -/

section GadgetAlgebra

/-- Width of the repeated orthogonality gadget: `d(dL²) = (dL)²`.
Paper: `lem:indexedgadget` (attention_indexed_lower.tex). -/
theorem repeat_width_identity (d L : ℝ) : d * (d * L ^ 2) = (d * L) ^ 2 := by ring

/-- Score of the repeated orthogonality gadget: `(-(dL²)·⟨a,b⟩)/(dL) = -L⟨a,b⟩`.
Paper: `lem:indexedgadget` (attention_indexed_lower.tex). -/
theorem repeat_score_identity (d L overlap : ℝ) (hd : d ≠ 0) (hL : L ≠ 0) :
    (-(d * L ^ 2) * overlap) / (d * L) = -L * overlap := by
  field_simp

/-- Bipolar padding: `d - 2·dist + (2t - d) = 2(t - dist)`.
Paper: `thm:indexedlowerlogtwo`, display `eq:gaphammingdot` (attention_indexed_lower.tex). -/
theorem bipolar_padding_identity (d t distance : ℝ) :
    d - 2 * distance + (2 * t - d) = 2 * (t - distance) := by ring

/-- Width of the Hamming-gap gadget: `(2d)(2dH²) = (2dH)²`.
Paper: `thm:indexedlowerlogtwo` (attention_indexed_lower.tex). -/
theorem gap_repeat_width (d H : ℝ) : (2 * d) * (2 * d * H ^ 2) = (2 * d * H) ^ 2 := by ring

/-- Score of the Hamming-gap gadget: `(2dH²)·2(t - dist)/(2dH) = 2H(t - dist)`.
Paper: `thm:indexedlowerlogtwo` (attention_indexed_lower.tex). -/
theorem gap_repeat_score (d H t distance : ℝ) (hd : d ≠ 0) (hH : H ≠ 0) :
    ((2 * d * H ^ 2) * (2 * (t - distance))) / (2 * d * H) = 2 * H * (t - distance) := by
  field_simp

/-- In the no case the token probability is at most `1/2 - 15/136` once the response is at most
a quarter of the attention mean `u ≤ -15/17`. Paper: `lem:indexedgadget`
(attention_indexed_lower.tex). -/
theorem token_no_gap (u response : ℝ) (hu : u ≤ -(15 / 17 : ℝ)) (hr : response ≤ u / 4) :
    (1 + response) / 2 ≤ 1 / 2 - 15 / 136 := by linarith

/-- The no-case threshold lies below `7/16`. Paper: `lem:indexedgadget`
(attention_indexed_lower.tex). -/
theorem displayed_no_threshold : (1 / 2 - 15 / 136 : ℝ) < 7 / 16 := by norm_num

/-- In the yes case a nonnegative response gives probability at least `1/2`.
Paper: `lem:indexedgadget` (attention_indexed_lower.tex). -/
theorem token_yes_gap (response : ℝ) (hr : 0 ≤ response) : (1 / 2 : ℝ) ≤ (1 + response) / 2 := by
  linarith

/-- The restricted pre-norm readout `u/4` lies in `[-1/4, 1/4]` for `u ∈ [-1,1]`.
Paper: `cor:indexedprenorm` (attention_indexed_lower.tex). -/
theorem additive_head_range (u : ℝ) (hu0 : -1 ≤ u) (hu1 : u ≤ 1) :
    -(1 / 4 : ℝ) ≤ ((-1 + u) + 1) / 4 ∧ ((-1 + u) + 1) / 4 ≤ 1 / 4 := by
  constructor <;> linarith

/-- The pre-norm no case, given the response bound `tanh(u/4) ≤ (7/8)(u/4)`.
Paper: `cor:indexedprenorm` (attention_indexed_lower.tex). -/
theorem additive_no_gap (u response : ℝ) (hu : u ≤ -(15 / 17 : ℝ))
    (hr : response ≤ (7 / 8) * (u / 4)) : (1 + response) / 2 ≤ 1 / 2 - 105 / 1088 := by
  linarith

/-- The pre-norm no-case threshold lies below `7/16`. Paper: `cor:indexedprenorm`
(attention_indexed_lower.tex). -/
theorem additive_no_threshold : (1 / 2 - 105 / 1088 : ℝ) < 7 / 16 := by norm_num

end GadgetAlgebra

end ExactSampling.IndexedLower
