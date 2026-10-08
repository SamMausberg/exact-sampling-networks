import Mathlib

/-!
# Exact Boolean gates and the norm-eight reduction

Paper file: instance_hardness.tex.

Formalized:
* `lem:zero-positive-gates`: the tanh OR and AND gates preserve the encoding "false is `0`,
  true is a number in `[1/2, 1)`", with exact cancellation for a false input. The gates are
  written as tanh neurons with explicit weight vectors (`gates_as_neurons`), whose row norms,
  biases and dyadic parameters are computed (`gate_row_norms`, `gate_parameters_mem`,
  `parameters_on_grid`).
* The circuits in the proof of `prop:instance-hardness-eight`: literal values, padded true
  clauses, the relay `u ↦ tanh(2u)`, the parity-combination gate on encoded pairs, balanced AND
  and parity trees of any depth `r`, and the end-to-end output identity `eq:SAT-parity-output`
  for a CNF formula with at most three literals per clause (`sat_parity_end_to_end`): the
  output is exactly `0` on violating assignments and `∏ᵢ yᵢ · f ≥ 1/2` on satisfying ones.
* The amplitude factorization used in the proof of `cor:score-certificate-hardness`: on
  literal inputs, the output equals `A(x) ∏ᵢ yᵢ`, with `A(x) = 0` on violating and
  `A(x) ≥ tanh 1` on satisfying assignments.
* The layer-count arithmetic of the reduction, and the comparison that separates the two cases
  of the approximation (`g(16 m³)² < 1 + m/2` for all large `m`).

Not formalized: the layout of the circuits as one dense width-`n` network (the gates are
composed as functions; the per-layer neuron counts and the width bound `12m` are not derived),
the NP-completeness of 3-SAT, the running-time analysis of the reduction, and the
complexity-theoretic conclusions `P = NP` and `NP ⊆ BPP`. The probe lower bound
`Q^*(W_φ) ≥ m/2` is `ExactSampling.TranscriptLowerBounds.parity_cost_gap` within the finite
decision-tree model, for samplers that receive the satisfying assignment for free; the step
"giving the assignment for free can only help" is not formalized.
-/

namespace ExactSampling.BooleanGates

open Real

noncomputable section

/-! ## Elementary tanh facts -/

/-- `tanh' = 1 - tanh²`. Auxiliary for `lem:zero-positive-gates` (instance_hardness.tex). -/
lemma hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have h : Real.tanh = Real.sinh / Real.cosh := by
    funext y; rw [Pi.div_apply, Real.tanh_eq_sinh_div_cosh]
  have hc := (Real.cosh_pos x).ne'
  have hd := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  rw [← h] at hd
  refine hd.congr_deriv ?_
  rw [Real.tanh_eq_sinh_div_cosh, div_pow]
  field_simp

/-- `tanh` is strictly increasing. Auxiliary for `lem:zero-positive-gates`
(instance_hardness.tex). -/
lemma tanh_strictMono : StrictMono Real.tanh :=
  strictMono_of_hasDerivAt_pos hasDerivAt_tanh fun x => by
    have := Real.tanh_sq_lt_one x; linarith

/-- `tanh x = (e^{2x} - 1)/(e^{2x} + 1)`. Auxiliary for the numerical tanh bounds in the proof
of `lem:zero-positive-gates` (instance_hardness.tex). -/
lemma tanh_eq_exp (x : ℝ) : Real.tanh x = (Real.exp (2 * x) - 1) / (Real.exp (2 * x) + 1) := by
  rw [Real.tanh_eq]
  have h1 : Real.exp (2 * x) = Real.exp x * Real.exp x := by rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-x) = 1 / Real.exp x := by rw [Real.exp_neg, one_div]
  have h3 := Real.exp_pos x
  rw [h1, h2]
  field_simp

/-- `tanh x ≥ 1/2` as soon as `e^{2x} ≥ 3`. Auxiliary for `lem:zero-positive-gates`. -/
lemma half_le_tanh_of {x : ℝ} (h : 3 ≤ Real.exp (2 * x)) : 1 / 2 ≤ Real.tanh x := by
  rw [tanh_eq_exp, le_div_iff₀ (by positivity)]
  linarith

/-- `tanh 1 ≥ 1/2`, since `e² ≥ 3`. Paper: proof of `lem:zero-positive-gates`
(instance_hardness.tex). -/
lemma half_le_tanh_one : 1 / 2 ≤ Real.tanh 1 := by
  apply half_le_tanh_of
  have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 * 1 by norm_num)
  norm_num at this ⊢
  linarith

/-- `tanh(2/3) ≥ 1/2`, since `e^{4/3} ≥ 1 + 4/3 + 8/9 > 3`. Paper: proof of
`lem:zero-positive-gates` (instance_hardness.tex). -/
lemma half_le_tanh_two_thirds : 1 / 2 ≤ Real.tanh (2 / 3) := by
  apply half_le_tanh_of
  have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 * (2 / 3) by norm_num)
  nlinarith

/-- `tanh(1/2) ≤ 1/2`, since `e ≤ 3`. Paper: proof of `lem:zero-positive-gates`
(instance_hardness.tex). -/
lemma tanh_half_le : Real.tanh (1 / 2) ≤ 1 / 2 := by
  rw [tanh_eq_exp, div_le_iff₀ (by positivity)]
  have := Real.exp_one_lt_d9
  norm_num at this ⊢
  linarith

/-- `tanh(5/2) ≥ 11/12`, since `e⁵ ≥ 23`. Paper: proof of `lem:zero-positive-gates`
(instance_hardness.tex). -/
lemma tanh_five_halves_ge : 11 / 12 ≤ Real.tanh (5 / 2) := by
  rw [tanh_eq_exp, le_div_iff₀ (by positivity)]
  have h5 : Real.exp (2 * (5 / 2)) = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  have he := Real.exp_one_gt_d9
  have : (23 : ℝ) ≤ Real.exp 1 ^ 5 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith
    calc (23 : ℝ) ≤ 2 ^ 5 := by norm_num
      _ ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) h2 5
  rw [h5]
  linarith

/-! ## Gates and the zero/positive encoding -/

/-- Encoding of a Boolean value: false is exactly `0`, true is any number in `[1/2, 1)`. -/
def Enc (b : Bool) (u : ℝ) : Prop := if b then 1 / 2 ≤ u ∧ u < 1 else u = 0

/-- The OR gate `tanh(2 ∑ᵢ uᵢ)`. -/
def orGate {j : ℕ} (u : Fin j → ℝ) : ℝ := Real.tanh (2 * ∑ i, u i)

/-- The mixed difference `B(u,v)` of the AND gate. -/
def andBracket (u v : ℝ) : ℝ :=
  -Real.tanh (1 / 2 + 4 * u + 4 * v) + Real.tanh (1 / 2 + 4 * u) +
    Real.tanh (1 / 2 + 4 * v) - Real.tanh (1 / 2)

/-- The AND gate `tanh(2 B(u,v))`. -/
def andGate (u v : ℝ) : ℝ := Real.tanh (2 * andBracket u v)

/-- The relay `u ↦ tanh(2u)`. -/
def relay (u : ℝ) : ℝ := Real.tanh (2 * u)

/-- Encoded values are nonnegative. Auxiliary for `lem:zero-positive-gates`. -/
lemma Enc.nonneg {b : Bool} {u : ℝ} (h : Enc b u) : 0 ≤ u := by
  cases b
  · simp only [Enc] at h; rw [h]
  · simp only [Enc, ↓reduceIte] at h; linarith [h.1]

/-- A true encoding with a value at least `1/2` arises from any argument at least `1/2`.
Auxiliary for `lem:zero-positive-gates` (instance_hardness.tex). -/
lemma enc_true_of {w : ℝ} (hw : 1 / 2 ≤ w) : Enc true (Real.tanh (2 * w)) := by
  refine ⟨?_, Real.tanh_lt_one _⟩
  exact half_le_tanh_one.trans (tanh_strictMono.monotone (by linarith))

/-- **OR gate.** `tanh(2 ∑ uᵢ)` computes the disjunction in the zero/positive encoding.

Paper: `lem:zero-positive-gates` (instance_hardness.tex). -/
theorem or_enc {j : ℕ} {b : Fin j → Bool} {u : Fin j → ℝ} (h : ∀ i, Enc (b i) (u i)) :
    Enc (decide (∃ i, b i = true)) (orGate u) := by
  by_cases hex : ∃ i, b i = true
  · obtain ⟨i₀, hi₀⟩ := hex
    have hsum : 1 / 2 ≤ ∑ i, u i := by
      have h₀ := h i₀
      rw [hi₀] at h₀
      calc (1 : ℝ) / 2 ≤ u i₀ := h₀.1
        _ ≤ ∑ i, u i := Finset.single_le_sum (fun i _ => (h i).nonneg) (Finset.mem_univ i₀)
    have : decide (∃ i, b i = true) = true := decide_eq_true ⟨i₀, hi₀⟩
    rw [this]
    exact enc_true_of hsum
  · have hall : ∀ i, u i = 0 := fun i => by
      have := h i
      have hb : b i = false := by
        cases hbi : b i
        · rfl
        · exact absurd ⟨i, hbi⟩ hex
      rw [hb] at this
      exact this
    have : decide (∃ i, b i = true) = false := decide_eq_false hex
    rw [this]
    simp [Enc, orGate, hall]

/-- **Exact cancellation, first input false.** Paper: proof of `lem:zero-positive-gates`
(instance_hardness.tex). -/
lemma andBracket_zero_left (v : ℝ) : andBracket 0 v = 0 := by
  simp only [andBracket, mul_zero, add_zero]; ring

/-- **Exact cancellation, second input false.** Paper: proof of `lem:zero-positive-gates`
(instance_hardness.tex). -/
lemma andBracket_zero_right (u : ℝ) : andBracket u 0 = 0 := by
  simp only [andBracket, mul_zero, add_zero]; ring

/-- A false input makes the AND output exactly zero. Paper: `lem:zero-positive-gates`
(instance_hardness.tex). -/
lemma andGate_zero_left (v : ℝ) : andGate 0 v = 0 := by
  simp [andGate, andBracket_zero_left]

/-- A false input makes the AND output exactly zero. Paper: `lem:zero-positive-gates`
(instance_hardness.tex). -/
lemma andGate_zero_right (u : ℝ) : andGate u 0 = 0 := by
  simp [andGate, andBracket_zero_right]

/-- `B(u,v) ≥ 2 tanh(5/2) - 1 - tanh(1/2) ≥ 1/3` for true inputs. Paper: proof of
`lem:zero-positive-gates` (instance_hardness.tex). -/
lemma andBracket_true_lower {u v : ℝ} (hu : 1 / 2 ≤ u) (hv : 1 / 2 ≤ v) :
    1 / 3 ≤ andBracket u v := by
  have hpu := tanh_strictMono.monotone (show (5 / 2 : ℝ) ≤ 1 / 2 + 4 * u by linarith)
  have hpv := tanh_strictMono.monotone (show (5 / 2 : ℝ) ≤ 1 / 2 + 4 * v by linarith)
  have hpa := (Real.tanh_lt_one (1 / 2 + 4 * u + 4 * v)).le
  have h1 := tanh_five_halves_ge
  have h2 := tanh_half_le
  unfold andBracket
  linarith

/-- **AND gate.** `tanh(2 B(u,v))` computes the conjunction in the zero/positive encoding.

Paper: `lem:zero-positive-gates` (instance_hardness.tex). -/
theorem and_enc {b c : Bool} {u v : ℝ} (hu : Enc b u) (hv : Enc c v) :
    Enc (b && c) (andGate u v) := by
  cases b
  · simp only [Enc] at hu
    rw [hu, andGate_zero_left]
    simp [Enc]
  · cases c
    · simp only [Enc] at hv
      rw [hv, andGate_zero_right]
      simp [Enc]
    · simp only [Enc, ↓reduceIte] at hu hv ⊢
      have hB := andBracket_true_lower hu.1 hv.1
      refine ⟨?_, Real.tanh_lt_one _⟩
      exact half_le_tanh_two_thirds.trans (tanh_strictMono.monotone (by linarith))

/-- **Relay.** `u ↦ tanh(2u)` preserves the encoding. Paper: proof of
`prop:instance-hardness-eight` (instance_hardness.tex). -/
theorem relay_enc {b : Bool} {u : ℝ} (h : Enc b u) : Enc b (relay u) := by
  cases b
  · simp only [Enc, Bool.false_eq_true, ↓reduceIte] at h ⊢; simp [relay, h]
  · simp only [Enc, ↓reduceIte] at h
    exact enc_true_of h.1

/-- The sign `±1` of a Boolean input bit. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- **Literal values.** For an input sign `x`, `tanh((1 + x)/2)` encodes `x = 1` and
`tanh((1 - x)/2)` encodes `x = -1`; exactly one is zero and the other is `tanh 1`.

Paper: the formula circuit in the proof of `prop:instance-hardness-eight`
(instance_hardness.tex). -/
theorem literal_enc (x : Bool) :
    Enc x (Real.tanh ((1 + sgn x) / 2)) ∧ Enc (!x) (Real.tanh ((1 - sgn x) / 2)) := by
  cases x <;> simp only [sgn, Enc] <;> norm_num <;>
    exact ⟨half_le_tanh_one, Real.tanh_lt_one 1⟩

/-- A padded true clause, the constant `tanh 1` (bias one, zero weights), encodes true.
Paper: proof of `prop:instance-hardness-eight` (instance_hardness.tex). -/
theorem const_true_enc : Enc true (Real.tanh 1) := ⟨half_le_tanh_one, Real.tanh_lt_one 1⟩

/-! ## Parity combination -/

/-- A pair encoding of a sign: the first entry encodes `+1`, the second encodes `-1`. -/
def PEnc (b : Bool) (p : ℝ × ℝ) : Prop := Enc b p.1 ∧ Enc (!b) p.2

/-- The parity-combination gate on two encoded pairs (three layers: AND, then OR). -/
def parityGate (p q : ℝ × ℝ) : ℝ × ℝ :=
  (orGate ![andGate p.1 q.1, andGate p.2 q.2], orGate ![andGate p.1 q.2, andGate p.2 q.1])

/-- The product of two signs, as a Boolean value (`true` means `+1`). -/
def mulB (b c : Bool) : Bool := !(xor b c)

/-- Signs multiply along `mulB`. Auxiliary for the parity circuit in the proof of
`prop:instance-hardness-eight` (instance_hardness.tex). -/
lemma sgn_mulB (b c : Bool) : sgn (mulB b c) = sgn b * sgn c := by
  cases b <;> cases c <;> norm_num [mulB, sgn]

/-- **Parity combination.** The gate maps encoded pairs of two signs to the encoded pair of
their product. Paper: the parity circuit in the proof of `prop:instance-hardness-eight`
(instance_hardness.tex). -/
theorem parityGate_enc {b c : Bool} {p q : ℝ × ℝ} (hp : PEnc b p) (hq : PEnc c q) :
    PEnc (mulB b c) (parityGate p q) := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  have a1 := and_enc hp1 hq1
  have a2 := and_enc hp2 hq2
  have a3 := and_enc hp1 hq2
  have a4 := and_enc hp2 hq1
  constructor
  · have := or_enc (b := ![b && c, !b && !c]) (u := ![andGate p.1 q.1, andGate p.2 q.2])
      (fun i => by fin_cases i <;> assumption)
    show Enc (mulB b c) (orGate ![andGate p.1 q.1, andGate p.2 q.2])
    convert this using 2
    cases b <;> cases c <;> simp [mulB, Fin.exists_fin_two]
  · have := or_enc (b := ![b && !c, !b && c]) (u := ![andGate p.1 q.2, andGate p.2 q.1])
      (fun i => by fin_cases i <;> assumption)
    show Enc (!mulB b c) (orGate ![andGate p.1 q.2, andGate p.2 q.1])
    convert this using 2
    cases b <;> cases c <;> simp [mulB, Fin.exists_fin_two]

/-! ## Balanced trees -/

lemma two_pow_succ (r : ℕ) : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [pow_succ, mul_two]

/-- Left half of a family indexed by `Fin (2^(r+1))`. -/
def leftHalf {α : Type*} {r : ℕ} (u : Fin (2 ^ (r + 1)) → α) : Fin (2 ^ r) → α :=
  fun i => u (finCongr (two_pow_succ r).symm (Fin.castAdd (2 ^ r) i))

/-- Right half of a family indexed by `Fin (2^(r+1))`. -/
def rightHalf {α : Type*} {r : ℕ} (u : Fin (2 ^ (r + 1)) → α) : Fin (2 ^ r) → α :=
  fun i => u (finCongr (two_pow_succ r).symm (Fin.natAdd (2 ^ r) i))

/-- A statement about all indices splits into the two halves. Auxiliary for the balanced trees
in the proof of `prop:instance-hardness-eight` (instance_hardness.tex). -/
lemma forall_halves {r : ℕ} (P : Fin (2 ^ (r + 1)) → Prop) :
    (∀ i, P i) ↔ (∀ i, P (finCongr (two_pow_succ r).symm (Fin.castAdd (2 ^ r) i))) ∧
      (∀ i, P (finCongr (two_pow_succ r).symm (Fin.natAdd (2 ^ r) i))) := by
  constructor
  · intro h; exact ⟨fun i => h _, fun i => h _⟩
  · rintro ⟨h1, h2⟩ i
    have := (finCongr (two_pow_succ r)).symm_apply_apply i
    rw [← this]
    generalize finCongr (two_pow_succ r) i = k
    induction k using Fin.addCases with
    | left k => exact h1 k
    | right k => exact h2 k

/-- Products split into the two halves. Auxiliary for the balanced trees in the proof of
`prop:instance-hardness-eight` (instance_hardness.tex). -/
lemma prod_halves {r : ℕ} (f : Fin (2 ^ (r + 1)) → ℝ) :
    ∏ i, f i = (∏ i, leftHalf f i) * ∏ i, rightHalf f i := by
  rw [← (finCongr (two_pow_succ r).symm).prod_comp, Fin.prod_univ_add]
  rfl

/-- The balanced binary tree of AND gates. -/
def andTree : (r : ℕ) → (Fin (2 ^ r) → ℝ) → ℝ
  | 0, u => u 0
  | r + 1, u => andGate (andTree r (leftHalf u)) (andTree r (rightHalf u))

/-- The balanced binary tree of parity-combination gates. -/
def parityTree : (r : ℕ) → (Fin (2 ^ r) → ℝ × ℝ) → ℝ × ℝ
  | 0, p => p 0
  | r + 1, p => parityGate (parityTree r (leftHalf p)) (parityTree r (rightHalf p))

/-- The product sign of a family of signs, computed along the same tree. -/
def parityB : (r : ℕ) → (Fin (2 ^ r) → Bool) → Bool
  | 0, b => b 0
  | r + 1, b => mulB (parityB r (leftHalf b)) (parityB r (rightHalf b))

/-- The tree product sign is the product `∏ᵢ yᵢ`. Paper: the parity circuit encodes
`χ(y) = ∏ᵢ yᵢ` (proof of `prop:instance-hardness-eight`, instance_hardness.tex). -/
theorem sgn_parityB (r : ℕ) (b : Fin (2 ^ r) → Bool) : sgn (parityB r b) = ∏ i, sgn (b i) := by
  induction r with
  | zero => simp [parityB]
  | succ r ih =>
    simp only [parityB, sgn_mulB, ih]
    rw [prod_halves (fun i => sgn (b i))]
    rfl

/-- **Balanced AND tree.** On encoded inputs, the tree encodes the conjunction. Paper: the
formula circuit in the proof of `prop:instance-hardness-eight` (instance_hardness.tex). -/
theorem andTree_enc (r : ℕ) {b : Fin (2 ^ r) → Bool} {u : Fin (2 ^ r) → ℝ}
    (h : ∀ i, Enc (b i) (u i)) : Enc (decide (∀ i, b i = true)) (andTree r u) := by
  induction r with
  | zero =>
    have : decide (∀ i : Fin (2 ^ 0), b i = true) = b 0 := by
      cases hb : b 0
      · exact decide_eq_false fun hh => by simp_all
      · exact decide_eq_true fun i => by
          have : i = 0 := Fin.ext (by have h := i.isLt; simp at h ⊢)
          rw [this, hb]
    rw [this]; exact h 0
  | succ r ih =>
    have h1 := ih (b := leftHalf b) (u := leftHalf u) (fun i => h _)
    have h2 := ih (b := rightHalf b) (u := rightHalf u) (fun i => h _)
    have := and_enc h1 h2
    show Enc _ (andGate (andTree r (leftHalf u)) (andTree r (rightHalf u)))
    convert this using 2
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.and_eq_true]
    exact forall_halves (fun i => b i = true)

/-- **Balanced parity tree.** On encoded pairs, the tree encodes the product sign. Paper: the
parity circuit in the proof of `prop:instance-hardness-eight` (instance_hardness.tex). -/
theorem parityTree_enc (r : ℕ) {b : Fin (2 ^ r) → Bool} {p : Fin (2 ^ r) → ℝ × ℝ}
    (h : ∀ i, PEnc (b i) (p i)) : PEnc (parityB r b) (parityTree r p) := by
  induction r with
  | zero => exact h 0
  | succ r ih =>
    exact parityGate_enc (ih (b := leftHalf b) (p := leftHalf p) (fun i => h _))
      (ih (b := rightHalf b) (p := rightHalf p) (fun i => h _))

/-! ## The output gadget -/

/-- The final neuron `tanh(2(G₊ - G₋))` with `G± = And(V, P±)`. -/
def finalOut (V : ℝ) (P : ℝ × ℝ) : ℝ := Real.tanh (2 * (andGate V P.1 - andGate V P.2))

/-- **Output identity `eq:SAT-parity-output`.** If the formula value is false the output is
exactly zero; if it is true, the output times the parity sign is at least `tanh 1 ≥ 1/2`.

Paper: `eq:SAT-parity-output` (instance_hardness.tex). -/
theorem sat_parity_output {s c : Bool} {V : ℝ} {P : ℝ × ℝ} (hV : Enc s V) (hP : PEnc c P) :
    (s = false → finalOut V P = 0) ∧
      (s = true → Real.tanh 1 ≤ sgn c * finalOut V P ∧ 1 / 2 ≤ sgn c * finalOut V P) := by
  constructor
  · rintro rfl
    simp only [Enc, Bool.false_eq_true, ↓reduceIte] at hV
    simp [finalOut, hV, andGate_zero_left]
  · rintro rfl
    obtain ⟨hP1, hP2⟩ := hP
    have g1 := and_enc hV hP1
    have g2 := and_enc hV hP2
    cases c
    · simp only [Bool.true_and, Enc, Bool.not_false, ↓reduceIte] at g1 g2
      simp only [Bool.false_eq_true, ite_false] at g1
      simp only [finalOut, sgn, g1, Bool.false_eq_true, ite_false, zero_sub]
      have h1 : Real.tanh 1 ≤ Real.tanh (2 * andGate V P.2) :=
        tanh_strictMono.monotone (by linarith [g2.1])
      rw [mul_neg, Real.tanh_neg]
      constructor <;> linarith [half_le_tanh_one]
    · simp only [Bool.true_and, Enc, Bool.not_true, ↓reduceIte] at g1 g2
      simp only [Bool.false_eq_true, ite_false] at g2
      simp only [finalOut, sgn, g2, ite_true, sub_zero, one_mul]
      have h1 : Real.tanh 1 ≤ Real.tanh (2 * andGate V P.1) :=
        tanh_strictMono.monotone (by linarith [g1.1])
      constructor <;> linarith [half_le_tanh_one]

/-! ## Amplitude factorization -/

/-- The common amplitude of the true entry at level `r` of the parity tree on literal pairs. -/
def ampl : ℕ → ℝ
  | 0 => Real.tanh 1
  | r + 1 => Real.tanh (2 * andGate (ampl r) (ampl r))

/-- The literal pair of an input sign: `(tanh 1, 0)` for `+1` and `(0, tanh 1)` for `-1`. -/
def litPair (b : Bool) : ℝ × ℝ := if b then (Real.tanh 1, 0) else (0, Real.tanh 1)

/-- On literal pairs, the parity tree returns `(A_r, 0)` or `(0, A_r)` according to the
product sign, with an amplitude `A_r` independent of the input pattern. Paper: proof of
`cor:score-certificate-hardness` (instance_hardness.tex). -/
theorem parityTree_litPair (r : ℕ) (b : Fin (2 ^ r) → Bool) :
    parityTree r (fun i => litPair (b i)) =
      if parityB r b then (ampl r, 0) else (0, ampl r) := by
  induction r with
  | zero =>
    show litPair (b 0) = _
    simp only [litPair, parityB, ampl]
    rfl
  | succ r ih =>
    simp only [parityTree, parityB]
    have hl : leftHalf (fun i => litPair (b i)) = fun i => litPair (leftHalf b i) := rfl
    have hr : rightHalf (fun i => litPair (b i)) = fun i => litPair (rightHalf b i) := rfl
    rw [hl, hr, ih, ih]
    rcases Bool.eq_false_or_eq_true (parityB r (leftHalf b)) with hL | hL <;>
      rcases Bool.eq_false_or_eq_true (parityB r (rightHalf b)) with hR | hR <;>
      simp [hL, hR, parityGate, mulB, orGate, andGate_zero_left, andGate_zero_right, ampl,
        Fin.sum_univ_two]

/-- The amplitudes are true encodings. Auxiliary for `cor:score-certificate-hardness`. -/
lemma ampl_enc (r : ℕ) : Enc true (ampl r) := by
  induction r with
  | zero => exact const_true_enc
  | succ r ih =>
    have := and_enc ih ih
    exact enc_true_of this.1

/-- **Amplitude factorization.** On literal parity inputs, the network output factorizes as
`f(x, y) = A(x) · ∏ᵢ yᵢ` with `A(x) = tanh(2 And(V(x), A_r))`; `A(x) = 0` when the formula value
encodes false, and `A(x) ≥ tanh 1` when it encodes true.

Paper: proof of `cor:score-certificate-hardness` (instance_hardness.tex). -/
theorem output_factorizes (r : ℕ) (V : ℝ) (b : Fin (2 ^ r) → Bool) :
    finalOut V (parityTree r (fun i => litPair (b i))) =
        Real.tanh (2 * andGate V (ampl r)) * ∏ i, sgn (b i) ∧
      (Enc false V → Real.tanh (2 * andGate V (ampl r)) = 0) ∧
      (Enc true V → Real.tanh 1 ≤ Real.tanh (2 * andGate V (ampl r))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [parityTree_litPair, ← sgn_parityB]
    cases parityB r b
    · simp [finalOut, sgn, andGate_zero_right, Real.tanh_neg]
    · simp [finalOut, sgn, andGate_zero_right]
  · intro hV
    simp only [Enc, Bool.false_eq_true, ↓reduceIte] at hV
    simp [hV, andGate_zero_left]
  · intro hV
    have h := and_enc hV (ampl_enc r)
    simp only [Bool.and_self, Enc, ↓reduceIte] at h
    exact tanh_strictMono.monotone (by linarith [h.1])

/-! ## The formula circuit and the end-to-end output identity -/

/-- The literal value of `x_l` (positive literal) or `¬x_l` (negative literal) at layer one. -/
def litVal {v : ℕ} (x : Fin v → Bool) (l : Fin v × Bool) : ℝ :=
  if l.2 then Real.tanh ((1 + sgn (x l.1)) / 2) else Real.tanh ((1 - sgn (x l.1)) / 2)

/-- The truth value of a literal. -/
def litTruth {v : ℕ} (x : Fin v → Bool) (l : Fin v × Bool) : Bool :=
  if l.2 then x l.1 else !x l.1

/-- Literal values encode literal truth. Paper: the formula circuit in the proof of
`prop:instance-hardness-eight` (instance_hardness.tex). -/
lemma litVal_enc {v : ℕ} (x : Fin v → Bool) (l : Fin v × Bool) :
    Enc (litTruth x l) (litVal x l) := by
  unfold litVal litTruth
  cases l.2
  · simpa using (literal_enc (x l.1)).2
  · simpa using (literal_enc (x l.1)).1

/-- The clause value: OR of three literal values, or the constant `tanh 1` for a padded true
clause (`none`). -/
def clauseVal {v : ℕ} (x : Fin v → Bool) : Option (Fin 3 → Fin v × Bool) → ℝ
  | none => Real.tanh 1
  | some cl => orGate (fun i => litVal x (cl i))

/-- Clause satisfaction (padded clauses are true). -/
def clauseSat {v : ℕ} (x : Fin v → Bool) : Option (Fin 3 → Fin v × Bool) → Bool
  | none => true
  | some cl => decide (∃ i, litTruth x (cl i) = true)

/-- Clause values encode clause satisfaction. Paper: the formula circuit in the proof of
`prop:instance-hardness-eight` (instance_hardness.tex). -/
lemma clauseVal_enc {v : ℕ} (x : Fin v → Bool) (c : Option (Fin 3 → Fin v × Bool)) :
    Enc (clauseSat x c) (clauseVal x c) := by
  cases c with
  | none => exact const_true_enc
  | some cl => exact or_enc (fun i => litVal_enc x (cl i))

/-- Iterated relays preserve the encoding. Paper: the synchronizing relays in the proof of
`prop:instance-hardness-eight` (instance_hardness.tex). -/
lemma relayIter_enc {b : Bool} {u : ℝ} (h : Enc b u) (k : ℕ) : Enc b (relay^[k] u) := by
  induction k with
  | zero => exact h
  | succ k ih => rw [Function.iterate_succ_apply']; exact relay_enc ih

/-- The formula value `V_φ(x)`: an AND tree over the `2^r` (padded) clause values, followed by
`r - 1` relays, so that it is ready at depth `1 + 3r` together with the parity pair. -/
def formulaVal {v : ℕ} (r : ℕ) (φ : Fin (2 ^ r) → Option (Fin 3 → Fin v × Bool))
    (x : Fin v → Bool) : ℝ :=
  relay^[r - 1] (andTree r (fun j => clauseVal x (φ j)))

/-- Literal pairs encode their signs. Paper: the parity circuit in the proof of
`prop:instance-hardness-eight` (instance_hardness.tex). -/
lemma litPair_enc (b : Bool) : PEnc b (litPair b) := by
  have h := half_le_tanh_one
  cases b <;> simp only [PEnc, litPair, Enc] <;> norm_num at h ⊢ <;>
    exact ⟨h, Real.tanh_lt_one 1⟩

/-- **End-to-end output identity.** For a CNF formula with at most three literals per clause,
padded to `2^r` clauses, the network output `f_φ(x, y)` is exactly zero when the assignment `x`
violates a clause, and satisfies `∏ᵢ yᵢ · f_φ(x, y) ≥ 1/2` when `x` satisfies every clause.

Paper: `eq:SAT-parity-output` in the proof of `prop:instance-hardness-eight`
(instance_hardness.tex). -/
theorem sat_parity_end_to_end {v : ℕ} (r : ℕ) (φ : Fin (2 ^ r) → Option (Fin 3 → Fin v × Bool))
    (x : Fin v → Bool) (y : Fin (2 ^ r) → Bool) :
    ((∃ j, clauseSat x (φ j) = false) →
        finalOut (formulaVal r φ x) (parityTree r (fun i => litPair (y i))) = 0) ∧
      ((∀ j, clauseSat x (φ j) = true) →
        1 / 2 ≤ (∏ i, sgn (y i)) *
          finalOut (formulaVal r φ x) (parityTree r (fun i => litPair (y i)))) := by
  have hV := relayIter_enc (andTree_enc r (fun j => clauseVal_enc x (φ j))) (r - 1)
  have hP := parityTree_enc r (fun i => litPair_enc (y i))
  have h := sat_parity_output hV hP
  rw [sgn_parityB] at h
  refine ⟨fun ⟨j, hj⟩ => h.1 ?_, fun hall => (h.2 ?_).2⟩
  · exact decide_eq_false fun hh => by simp [hh j] at hj
  · exact decide_eq_true hall

/-! ## Parameters, depth and width -/

/-- A tanh neuron with bias `b`, weight vector `w` and inputs `u`. -/
def neuron {k : ℕ} (b : ℝ) (w u : Fin k → ℝ) : ℝ := Real.tanh (b + ∑ j, w j * u j)

/-- The row norm `∑ⱼ |wⱼ|` of a weight vector. -/
def rowNorm {k : ℕ} (w : Fin k → ℝ) : ℝ := ∑ j, |w j|

/-- **The gates as tanh neurons.** OR is one neuron with weights `2`; AND is a first layer of
four neurons with bias `1/2` and weights `(4,4)`, `(4,0)`, `(0,4)`, `(0,0)`, followed by one
neuron with weights `(-2,2,2,-2)`; the relay has weight `2`; the literal values have bias `1/2`
and weight `±1/2`; the padded true clause has bias `1`; the output neuron has weights `(2,-2)`.

Paper: `lem:zero-positive-gates` and the proof of `prop:instance-hardness-eight`
(instance_hardness.tex). -/
theorem gates_as_neurons {j : ℕ} (us : Fin j → ℝ) (u v : ℝ) (x : Bool) (V : ℝ) (P : ℝ × ℝ) :
    orGate us = neuron 0 (fun _ => 2) us ∧
      andGate u v = neuron 0 ![-2, 2, 2, -2]
        ![neuron (1 / 2) ![4, 4] ![u, v], neuron (1 / 2) ![4, 0] ![u, v],
          neuron (1 / 2) ![0, 4] ![u, v], neuron (1 / 2) ![0, 0] ![u, v]] ∧
      relay u = neuron 0 ![2] ![u] ∧
      Real.tanh ((1 + sgn x) / 2) = neuron (1 / 2) ![1 / 2] ![sgn x] ∧
      Real.tanh ((1 - sgn x) / 2) = neuron (1 / 2) ![-1 / 2] ![sgn x] ∧
      Real.tanh 1 = neuron 1 ![] ![] ∧
      finalOut V P = neuron 0 ![2, -2] ![andGate V P.1, andGate V P.2] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [orGate, neuron, Finset.mul_sum]
  · simp only [andGate, andBracket, neuron, Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp
    ring_nf
  · simp [relay, neuron]
  · simp only [neuron, Fin.sum_univ_succ, Fin.sum_univ_zero]; simp; ring_nf
  · simp only [neuron, Fin.sum_univ_succ, Fin.sum_univ_zero]; simp; ring_nf
  · simp [neuron]
  · simp only [finalOut, neuron, Fin.sum_univ_succ, Fin.sum_univ_zero]; simp; ring_nf

/-- **Row norms and biases of the gates**, for the weight vectors of `gates_as_neurons`: OR with
`j ≤ 3` inputs has row norm `2j ≤ 6`, the AND rows have norm at most eight, the relay has norm
two, the literal rows have norm `1/2`, and the output row has norm four; all biases lie in
`{0, 1/2, 1}`.

Paper: `lem:zero-positive-gates` and the proof of `prop:instance-hardness-eight`
(instance_hardness.tex). -/
theorem gate_row_norms (j : ℕ) (hj : j ≤ 3) :
    rowNorm (fun _ : Fin j => (2 : ℝ)) ≤ 6 ∧ rowNorm ![(4 : ℝ), 4] = 8 ∧
      rowNorm ![(4 : ℝ), 0] ≤ 8 ∧ rowNorm ![(0 : ℝ), 4] ≤ 8 ∧ rowNorm ![(0 : ℝ), 0] ≤ 8 ∧
      rowNorm ![(-2 : ℝ), 2, 2, -2] = 8 ∧ rowNorm ![(2 : ℝ)] = 2 ∧
      rowNorm ![(1 / 2 : ℝ)] = 1 / 2 ∧ rowNorm ![(-1 / 2 : ℝ)] = 1 / 2 ∧
      rowNorm ![(2 : ℝ), -2] = 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [rowNorm, Fin.sum_univ_succ, Fin.sum_univ_zero] <;> norm_num
  have : (j : ℝ) ≤ 3 := by exact_mod_cast hj
  linarith

/-- Every weight and bias of the gates in `gates_as_neurons` lies in
`{0, ±1/2, ±2, ±4, 1}`. Paper: proof of `prop:instance-hardness-eight`
(instance_hardness.tex). -/
theorem gate_parameters_mem :
    let S : Finset ℝ := {0, 1 / 2, -1 / 2, 2, -2, 4, -4, 1}
    (∀ i, ![(-2 : ℝ), 2, 2, -2] i ∈ S) ∧ (∀ i, ![(4 : ℝ), 4] i ∈ S) ∧
      (∀ i, ![(4 : ℝ), 0] i ∈ S) ∧ (∀ i, ![(0 : ℝ), 4] i ∈ S) ∧ (∀ i, ![(2 : ℝ), -2] i ∈ S) ∧
      (2 : ℝ) ∈ S ∧ (1 / 2 : ℝ) ∈ S ∧ (-1 / 2 : ℝ) ∈ S ∧ (0 : ℝ) ∈ S ∧ (1 : ℝ) ∈ S := by
  intro S
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try (intro i; fin_cases i)
  all_goals simp [S]

/-- All weights `{0, ±1/2, ±2, ±4}` and biases `{0, 1/2, 1}` (see `gate_parameters_mem`) lie on
the grid `2^{-b}ℤ` for every `b ≥ 1`. Paper: proof of `prop:instance-hardness-eight`
(instance_hardness.tex). -/
theorem parameters_on_grid (b : ℕ) (hb : 1 ≤ b) :
    ∀ w ∈ ({0, 1 / 2, -1 / 2, 2, -2, 4, -4, 1} : Finset ℝ), ∃ z : ℤ, w = z / 2 ^ b := by
  have h2 : (2 : ℝ) ^ b = 2 * 2 ^ (b - 1) := by
    rw [← pow_succ']; congr 1; omega
  intro w hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  have hpos : (0 : ℝ) < 2 ^ b := by positivity
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨2 ^ (b - 1), by push_cast; rw [h2]; field_simp⟩
  · exact ⟨-2 ^ (b - 1), by push_cast; rw [h2]; field_simp⟩
  · exact ⟨2 * 2 ^ b, by push_cast; field_simp⟩
  · exact ⟨-(2 * 2 ^ b), by push_cast; field_simp⟩
  · exact ⟨4 * 2 ^ b, by push_cast; field_simp⟩
  · exact ⟨-(4 * 2 ^ b), by push_cast; field_simp⟩
  · exact ⟨2 ^ b, by push_cast; field_simp⟩

/-- Layer-count arithmetic of the reduction: with `m = 2^r`, `r ≥ 1`, the formula circuit (depth
`2 + 2r`) is ready before the parity circuit (depth `1 + 3r`), the output sits at depth
`D = 4 + 3r`, the width is `n = 16 m³ = 2^D`, and the bound `12 m` on active neurons per layer
is at most `n`. The per-layer neuron counts themselves are not derived from a network.

Paper: proof of `prop:instance-hardness-eight` (instance_hardness.tex). -/
theorem depth_width (r : ℕ) (hr : 1 ≤ r) :
    2 + 2 * r ≤ 1 + 3 * r ∧ 16 * (2 ^ r) ^ 3 = 2 ^ (4 + 3 * r) ∧
      12 * 2 ^ r ≤ 16 * (2 ^ r) ^ 3 := by
  refine ⟨by omega, ?_, ?_⟩
  · rw [← pow_mul, pow_add]; norm_num; ring
  · have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    have : 2 ^ r ≤ (2 ^ r) ^ 3 := by
      calc 2 ^ r = 2 ^ r * 1 * 1 := by ring
        _ ≤ 2 ^ r * 2 ^ r * 2 ^ r := by gcongr
        _ = (2 ^ r) ^ 3 := by ring
    omega

/-- The decision rule of the reduction: if `Λ` approximates `1 + Q^*` within a factor `g`, then
`Λ ≤ g` when `Q^* = 0`, and `Λ > g` when `Q^* ≥ m/2` and `g² < 1 + m/2`.

Paper: last paragraph of the proof of `prop:instance-hardness-eight` (instance_hardness.tex). -/
theorem decision_rule {Λ Q g m : ℝ} (hg : 0 < g) (hlo : (1 + Q) / g ≤ Λ) (hhi : Λ ≤ g * (1 + Q)) :
    (Q = 0 → Λ ≤ g) ∧ (m / 2 ≤ Q → g ^ 2 < 1 + m / 2 → g < Λ) := by
  constructor
  · rintro rfl; simpa using hhi
  · intro hQ hgap
    have h1 : (1 + m / 2) / g ≤ Λ := le_trans (by gcongr) hlo
    rw [div_le_iff₀ hg] at h1
    nlinarith

/-- For fixed `K', c'`, the polylogarithmic factor `g(16 m³) = K'(log₂(16 m³) + 2)^{c'}` with
`m = 2^r` satisfies `g² < 1 + m/2` for all large `r`, so the two ranges of the decision rule
are disjoint.

Paper: last paragraph of the proof of `prop:instance-hardness-eight` (instance_hardness.tex). -/
theorem polylog_gap (K c : ℕ) :
    ∀ᶠ r : ℕ in Filter.atTop, ((K : ℝ) * ((4 + 3 * r : ℕ) + 2 : ℝ) ^ c) ^ 2 <
      1 + (2 ^ r : ℝ) / 2 := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt (2 * c) (show (1 : ℝ) < 2 by norm_num)
  have hK : (0 : ℝ) < 2 * (K : ℝ) ^ 2 * 9 ^ (2 * c) + 1 := by positivity
  have hev := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (2 * (K : ℝ) ^ 2 *
    9 ^ (2 * c) + 1) by positivity)))
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with r hr hr1
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have h2r : (0 : ℝ) < 2 ^ r := by positivity
  have hrpow := hr
  rw [div_lt_div_iff₀ h2r hK, one_mul] at hrpow
  -- `(6 + 3r) ≤ 9 r`
  have hbase : ((4 + 3 * r : ℕ) + 2 : ℝ) ≤ 9 * r := by push_cast; linarith
  have hb0 : (0 : ℝ) ≤ ((4 + 3 * r : ℕ) + 2 : ℝ) := by positivity
  have hpow : (((4 + 3 * r : ℕ) + 2 : ℝ) ^ c) ^ 2 ≤ 9 ^ (2 * c) * (r : ℝ) ^ (2 * c) := by
    rw [← pow_mul, mul_comm c 2, ← mul_pow]
    exact pow_le_pow_left₀ hb0 (by linarith) _
  have hK0 : (0 : ℝ) ≤ (K : ℝ) ^ 2 := by positivity
  calc ((K : ℝ) * ((4 + 3 * r : ℕ) + 2 : ℝ) ^ c) ^ 2 =
        (K : ℝ) ^ 2 * (((4 + 3 * r : ℕ) + 2 : ℝ) ^ c) ^ 2 := by ring
    _ ≤ (K : ℝ) ^ 2 * (9 ^ (2 * c) * (r : ℝ) ^ (2 * c)) := mul_le_mul_of_nonneg_left hpow hK0
    _ < 1 + (2 ^ r : ℝ) / 2 := by
        have hX : (0 : ℝ) ≤ (r : ℝ) ^ (2 * c) := by positivity
        calc (K : ℝ) ^ 2 * (9 ^ (2 * c) * (r : ℝ) ^ (2 * c)) =
              (r : ℝ) ^ (2 * c) * (2 * (K : ℝ) ^ 2 * 9 ^ (2 * c) + 1) / 2 -
                (r : ℝ) ^ (2 * c) / 2 := by ring
          _ ≤ (r : ℝ) ^ (2 * c) * (2 * (K : ℝ) ^ 2 * 9 ^ (2 * c) + 1) / 2 := by linarith
          _ < (2 ^ r : ℝ) / 2 := by linarith
          _ < 1 + (2 ^ r : ℝ) / 2 := by linarith

end

end ExactSampling.BooleanGates
