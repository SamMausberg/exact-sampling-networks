import Mathlib

/-!
# Weight magnitudes and one-parameter profiles do not determine sampling cost

Paper file: instance_information.tex.

Formalized:
* A layered tanh network model with weights `W ℓ i j`, biases `B ℓ i`, row norms
  `∑ⱼ |W ℓ i j|`, and its forward evaluation.
* `prop:magnitude-obstruction`: two explicit width-`n`, depth-`D` networks with zero biases,
  row norms at most `a` and entrywise equal absolute weight matrices, whose outputs are `0` and
  `F_{a,D}(m⁻¹ ∑_{i<m} xᵢ)`; all parameters lie on the grid `2^{-b}ℤ` when `a = A 2^{-r}`,
  `m = 2^k` and `b ≥ r + k + 1`.
* `prop:profile-obstruction`: the signed mean chain is realized by a network with row norms at
  most `a`, zero biases, the same absolute weights as the unsigned chain, and weights on the
  grid whenever `a` and `a/m` are (`profileNet_eq_signedChain`, `profileNet_grid`); its
  common-mean product profile `H_f(t) = E_t f(X)` vanishes identically, together with all of
  its derivatives.

The probe-cost statements of both propositions (the fair-coin sampler for the zero output, the
lower bound for the mean chain, and the equality of the optimal query costs of the signed and
unsigned chains) are proved in `ExactSampling.TranscriptLowerBounds` (`fairSampler_spec`,
`lower_exact`, `lower_super`, `relabel_sampler`, `signed_chain_lower`, `signed_target_lower`),
whose `signedTarget` is the function `signedChain` of this module.
-/

namespace ExactSampling.WeightObstructions

noncomputable section

/-! ## Odd chains and sign cancellations -/

/-- The scalar chain `F_{a,0}(z) = z`, `F_{a,d+1}(z) = φ(a F_{a,d}(z))` for an activation `φ`. -/
def gainIter (φ : ℝ → ℝ) (a : ℝ) : ℕ → ℝ → ℝ
  | 0, x => x
  | d + 1, x => φ (a * gainIter φ a d x)

/-- An odd activation gives an odd chain. Paper: proofs of `prop:magnitude-obstruction` and
`prop:profile-obstruction` ("tanh is odd"). -/
theorem gainIter_odd (φ : ℝ → ℝ) (hφ : ∀ x, φ (-x) = -φ x) (a : ℝ) (d : ℕ) (x : ℝ) :
    gainIter φ a d (-x) = -gainIter φ a d x := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [gainIter, ih, mul_neg, hφ]

/-- Equal copies cancel in the final signed row. Paper: proof of `prop:magnitude-obstruction`. -/
lemma equal_copy_cancellation (a y : ℝ) : (a / 2) * y + (-(a / 2)) * y = 0 := by ring

/-- Opposite copies reconstruct the scalar gain. Paper: proof of `prop:magnitude-obstruction`. -/
lemma opposite_copy_reinforcement (a y : ℝ) : (a / 2) * y + (-(a / 2)) * (-y) = a * y := by ring

/-- A weight-preserving permutation that negates a function makes its weighted sum vanish.
Paper: proof of `prop:profile-obstruction` (instance_information.tex). -/
theorem weighted_sum_zero_of_odd_equiv {ι : Type*} [Fintype ι] (e : ι ≃ ι) (w f : ι → ℝ)
    (hw : ∀ x, w (e x) = w x) (hf : ∀ x, f (e x) = -f x) : ∑ x, w x * f x = 0 := by
  have hs : ∑ x, w x * f x = ∑ x, w (e x) * f (e x) :=
    (Equiv.sum_comp e (fun x => w x * f x)).symm
  simp_rw [hw, hf, mul_neg, Finset.sum_neg_distrib] at hs
  linarith

/-! ## Layered tanh networks -/

/-- A layered tanh network of width `n`: layer `ℓ` (for `ℓ < D`) has weights `W ℓ i j` and
biases `B ℓ i`. -/
structure Net (n : ℕ) where
  /-- Weights of layer `ℓ + 1`. -/
  W : ℕ → Fin n → Fin n → ℝ
  /-- Biases of layer `ℓ + 1`. -/
  B : ℕ → Fin n → ℝ

namespace Net

variable {n : ℕ}

/-- Forward evaluation `h_{0} = x`, `h_{ℓ+1,i} = tanh(B ℓ i + ∑ⱼ W ℓ i j h_{ℓ,j})`. -/
def eval (N : Net n) (x : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => x
  | ℓ + 1 => fun i => Real.tanh (N.B ℓ i + ∑ j, N.W ℓ i j * N.eval x ℓ j)

/-- Row norm of row `i` of layer `ℓ + 1`. -/
def rowNorm (N : Net n) (ℓ : ℕ) (i : Fin n) : ℝ := ∑ j, |N.W ℓ i j|

/-- One step of the forward evaluation. Auxiliary for `prop:magnitude-obstruction`
(instance_information.tex). -/
lemma eval_succ (N : Net n) (x : Fin n → ℝ) (ℓ : ℕ) (i : Fin n) :
    N.eval x (ℓ + 1) i = Real.tanh (N.B ℓ i + ∑ j, N.W ℓ i j * N.eval x ℓ j) := rfl

end Net

/-! ## Equal weight magnitudes, different sampling costs -/

section Rows

variable {n : ℕ}

/-- A first-layer row with weight `c` on the first `m` inputs. -/
def firstRow (m : ℕ) (c : ℝ) (j : Fin n) : ℝ := if (j : ℕ) < m then c else 0

/-- A row with the single weight `c` at position `k`. -/
def pick (k : ℕ) (c : ℝ) (j : Fin n) : ℝ := if (j : ℕ) = k then c else 0

/-- Evaluation of a first-layer row. Auxiliary for `prop:magnitude-obstruction`. -/
lemma sum_firstRow (m : ℕ) (c : ℝ) (h : Fin n → ℝ) :
    ∑ j, firstRow m c j * h j = c * ∑ j : Fin n, (if (j : ℕ) < m then h j else 0) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold firstRow; split <;> simp

/-- Evaluation of a single-weight row. Auxiliary for `prop:magnitude-obstruction`. -/
lemma sum_pick (k : ℕ) (hk : k < n) (c : ℝ) (h : Fin n → ℝ) :
    ∑ j, pick k c j * h j = c * h ⟨k, hk⟩ := by
  rw [Finset.sum_eq_single ⟨k, hk⟩]
  · simp [pick]
  · intro j _ hj
    have : (j : ℕ) ≠ k := fun e => hj (Fin.ext e)
    simp [pick, this]
  · simp

/-- Row norm of a first-layer row. Auxiliary for `prop:magnitude-obstruction`. -/
lemma sum_abs_firstRow (m : ℕ) (c : ℝ) : ∑ j, |firstRow (n := n) m c j| ≤ m * |c| := by
  have : ∑ j, |firstRow (n := n) m c j| =
      ((Finset.univ.filter fun j : Fin n => (j : ℕ) < m).card : ℝ) * |c| := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold firstRow; split <;> simp
  rw [this]
  have hcard : (Finset.univ.filter fun j : Fin n => (j : ℕ) < m).card ≤ m := by
    calc (Finset.univ.filter fun j : Fin n => (j : ℕ) < m).card ≤ (Finset.range m).card :=
          Finset.card_le_card_of_injOn (fun j => (j : ℕ))
            (fun j hj => by simp at hj; simp [hj]) (fun j _ k _ h => Fin.ext h)
      _ = m := Finset.card_range m
  have : ((Finset.univ.filter fun j : Fin n => (j : ℕ) < m).card : ℝ) ≤ m := by
    exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_right this (abs_nonneg c)

/-- Row norm of a single-weight row. Auxiliary for `prop:magnitude-obstruction`. -/
lemma sum_abs_pick (k : ℕ) (c : ℝ) : ∑ j, |pick (n := n) k c j| ≤ |c| := by
  by_cases hk : k < n
  · rw [Finset.sum_eq_single ⟨k, hk⟩]
    · simp [pick]
    · intro j _ hj
      have : (j : ℕ) ≠ k := fun e => hj (Fin.ext e)
      simp [pick, this]
    · simp
  · have : ∀ j : Fin n, pick k c j = 0 := fun j => by
      have : (j : ℕ) ≠ k := fun e => hk (e ▸ j.isLt)
      simp [pick, this]
    simp [this]

end Rows

section Magnitude

variable {n : ℕ} (m D : ℕ) (a σ : ℝ)

/-- The networks of `prop:magnitude-obstruction`: neurons `0` and `1` carry the signal; the
second row of the first layer is multiplied by `σ ∈ {1, -1}`. With `σ = 1` the output cancels;
with `σ = -1` it is the mean chain. -/
def magNet : Net n where
  W ℓ i j :=
    if ℓ = 0 then
      (if (i : ℕ) = 0 then firstRow m (a / m) j
        else if (i : ℕ) = 1 then firstRow m (σ * (a / m)) j else 0)
    else if ℓ + 1 < D then
      (if (i : ℕ) = 0 then pick 0 a j else if (i : ℕ) = 1 then pick 1 a j else 0)
    else
      (if (i : ℕ) = 0 then pick 0 (a / 2) j + pick 1 (-(a / 2)) j else 0)
  B _ _ := 0

/-- The input mean `m⁻¹ ∑_{j<m} xⱼ`. -/
def inputMean (x : Fin n → ℝ) : ℝ := (∑ j : Fin n, if (j : ℕ) < m then x j else 0) / m

/-- First-layer weights of row `0`. Auxiliary for `prop:magnitude-obstruction`
(instance_information.tex). -/
lemma magNet_W_first0 (i j : Fin n) (hi : (i : ℕ) = 0) :
    (magNet (n := n) m D a σ).W 0 i j = firstRow m (a / m) j := by
  simp [magNet, hi]

/-- First-layer weights of row `1`. Auxiliary for `prop:magnitude-obstruction`
(instance_information.tex). -/
lemma magNet_W_first1 (i j : Fin n) (hi : (i : ℕ) = 1) :
    (magNet (n := n) m D a σ).W 0 i j = firstRow m (σ * (a / m)) j := by
  simp [magNet, hi]

/-- Middle-layer weights of row `0`. Auxiliary for `prop:magnitude-obstruction`
(instance_information.tex). -/
lemma magNet_W_mid0 {ℓ : ℕ} (h0 : ℓ ≠ 0) (hD : ℓ + 1 < D) (i j : Fin n) (hi : (i : ℕ) = 0) :
    (magNet (n := n) m D a σ).W ℓ i j = pick 0 a j := by
  simp [magNet, hi, h0, hD]

/-- Middle-layer weights of row `1`. Auxiliary for `prop:magnitude-obstruction`
(instance_information.tex). -/
lemma magNet_W_mid1 {ℓ : ℕ} (h0 : ℓ ≠ 0) (hD : ℓ + 1 < D) (i j : Fin n) (hi : (i : ℕ) = 1) :
    (magNet (n := n) m D a σ).W ℓ i j = pick 1 a j := by
  simp [magNet, hi, h0, hD]

/-- Output-layer weights. Auxiliary for `prop:magnitude-obstruction` (instance_information.tex). -/
lemma magNet_W_last {ℓ : ℕ} (h0 : ℓ ≠ 0) (hD : ¬ℓ + 1 < D) (i j : Fin n) (hi : (i : ℕ) = 0) :
    (magNet (n := n) m D a σ).W ℓ i j = pick 0 (a / 2) j + pick 1 (-(a / 2)) j := by
  simp [magNet, hi, h0, hD]

/-- Hidden activations of the magnitude networks. Paper: proof of `prop:magnitude-obstruction`
("in the first network the two active neurons at layer `D - 1` both equal `F_{a,D-1}(u)`; in
the second their values are `F_{a,D-1}(u)` and `-F_{a,D-1}(u)`"). -/
theorem magNet_hidden (hn : 2 ≤ n) (hσ : σ = 1 ∨ σ = -1) (x : Fin n → ℝ) :
    ∀ ℓ, 1 ≤ ℓ → ℓ < D →
      (magNet (n := n) m D a σ).eval x ℓ ⟨0, by omega⟩ = gainIter Real.tanh a ℓ (inputMean m x) ∧
      (magNet (n := n) m D a σ).eval x ℓ ⟨1, by omega⟩ =
        σ * gainIter Real.tanh a ℓ (inputMean m x) := by
  have htanh : ∀ y, Real.tanh (σ * y) = σ * Real.tanh y := fun y => by
    rcases hσ with rfl | rfl
    · simp
    · simp [Real.tanh_neg]
  have hB : ∀ ℓ i, (magNet (n := n) m D a σ).B ℓ i = 0 := fun _ _ => rfl
  intro ℓ hℓ hℓD
  induction ℓ with
  | zero => omega
  | succ ℓ ih =>
    rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
    · -- the first layer
      have e0 : (magNet (n := n) m D a σ).eval x 0 = x := rfl
      refine ⟨?_, ?_⟩
      · rw [Net.eval_succ, hB, zero_add, e0,
          Finset.sum_congr rfl fun j _ => by rw [magNet_W_first0 m D a σ _ j rfl], sum_firstRow]
        simp only [gainIter, inputMean]
        congr 1; ring
      · rw [Net.eval_succ, hB, zero_add, e0,
          Finset.sum_congr rfl fun j _ => by rw [magNet_W_first1 m D a σ _ j rfl], sum_firstRow]
        simp only [gainIter, inputMean]
        rw [← htanh]; congr 1; ring
    · -- a middle layer
      obtain ⟨ih0, ih1⟩ := ih hpos (by omega)
      have hne : ℓ ≠ 0 := by omega
      have hlt : ℓ + 1 < D := hℓD
      refine ⟨?_, ?_⟩
      · rw [Net.eval_succ, hB, zero_add,
          Finset.sum_congr rfl fun j _ => by rw [magNet_W_mid0 m D a σ hne hlt _ j rfl],
          sum_pick 0 (by omega), ih0]
        rfl
      · rw [Net.eval_succ, hB, zero_add,
          Finset.sum_congr rfl fun j _ => by rw [magNet_W_mid1 m D a σ hne hlt _ j rfl],
          sum_pick 1 (by omega), ih1, mul_left_comm, htanh]
        rfl

/-- **Equal weight magnitudes, different outputs.** For `D ≥ 2` and `n ≥ 2`, the network with
`σ = 1` outputs `0`, and the network with `σ = -1` outputs `F_{a,D}(m⁻¹ ∑_{i<m} xᵢ)`.

Paper: `prop:magnitude-obstruction` (instance_information.tex). -/
theorem magNet_output (hn : 2 ≤ n) (hD : 2 ≤ D) (x : Fin n → ℝ) :
    (magNet (n := n) m D a 1).eval x D ⟨0, by omega⟩ = 0 ∧
      (magNet (n := n) m D a (-1)).eval x D ⟨0, by omega⟩ =
        gainIter Real.tanh a D (inputMean m x) := by
  obtain ⟨k, rfl⟩ : ∃ k, D = k + 1 := ⟨D - 1, by omega⟩
  have hk : k ≠ 0 := by omega
  have hnot : ¬k + 1 < k + 1 := lt_irrefl _
  have hlast : ∀ σ : ℝ, (magNet (n := n) m (k + 1) a σ).eval x (k + 1) ⟨0, by omega⟩ =
      Real.tanh (a / 2 * (magNet (n := n) m (k + 1) a σ).eval x k ⟨0, by omega⟩ -
        a / 2 * (magNet (n := n) m (k + 1) a σ).eval x k ⟨1, by omega⟩) := by
    intro σ
    have hB : (magNet (n := n) m (k + 1) a σ).B k ⟨0, by omega⟩ = 0 := rfl
    rw [Net.eval_succ, hB, zero_add,
      Finset.sum_congr rfl fun j _ => by rw [magNet_W_last m (k + 1) a σ hk hnot _ j rfl],
      Finset.sum_congr rfl fun j _ => add_mul _ _ _, Finset.sum_add_distrib,
      sum_pick 0 (by omega), sum_pick 1 (by omega)]
    ring_nf
  constructor
  · obtain ⟨h0, h1⟩ := magNet_hidden m (k + 1) a 1 hn (Or.inl rfl) x k (by omega) (by omega)
    rw [hlast, h0, h1]
    simp
  · obtain ⟨h0, h1⟩ := magNet_hidden m (k + 1) a (-1) hn (Or.inr rfl) x k (by omega) (by omega)
    rw [hlast, h0, h1]
    simp only [gainIter]
    congr 1
    ring

/-- The two networks have identical entrywise absolute weights and zero biases. Paper:
`prop:magnitude-obstruction` ("the construction changes signs only"). -/
theorem magNet_abs_eq (ℓ : ℕ) (i j : Fin n) :
    |(magNet (n := n) m D a 1).W ℓ i j| = |(magNet (n := n) m D a (-1)).W ℓ i j| ∧
      (magNet (n := n) m D a 1).B ℓ i = 0 ∧ (magNet (n := n) m D a (-1)).B ℓ i = 0 := by
  refine ⟨?_, rfl, rfl⟩
  simp only [magNet, firstRow]
  split_ifs <;> simp [abs_neg]

/-- Row norms are at most `a`. Paper: `prop:magnitude-obstruction` ("its nonzero row norms
are `a`"). -/
theorem magNet_rowNorm (ha : 0 ≤ a) (hσ : σ = 1 ∨ σ = -1) (hm : 1 ≤ m) (ℓ : ℕ) (i : Fin n) :
    (magNet (n := n) m D a σ).rowNorm ℓ i ≤ a := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  have hfirst : ∀ c : ℝ, |c| = 1 → ∑ j, |firstRow (n := n) m (c * (a / m)) j| ≤ a := by
    intro c hc
    calc ∑ j, |firstRow (n := n) m (c * (a / m)) j| ≤ m * |c * (a / m)| := sum_abs_firstRow m _
      _ = a := by rw [abs_mul, hc, one_mul, abs_of_nonneg (by positivity)]; field_simp
  unfold Net.rowNorm
  simp only [magNet]
  by_cases hℓ : ℓ = 0
  · simp only [hℓ, ↓reduceIte]
    by_cases hi0 : (i : ℕ) = 0
    · simpa [hi0] using hfirst 1 (by simp)
    · by_cases hi1 : (i : ℕ) = 1
      · simpa [hi0, hi1] using hfirst σ hσabs
      · simp [hi0, hi1]; exact ha
  · simp only [hℓ, ↓reduceIte]
    split_ifs with hlt hi0 hi1 hi0'
    · simpa [abs_of_nonneg ha] using sum_abs_pick (n := n) 0 a
    · simpa [abs_of_nonneg ha] using sum_abs_pick (n := n) 1 a
    · simp; exact ha
    · calc ∑ j, |pick (n := n) 0 (a / 2) j + pick 1 (-(a / 2)) j| ≤
            ∑ j, (|pick (n := n) 0 (a / 2) j| + |pick (n := n) 1 (-(a / 2)) j|) :=
            Finset.sum_le_sum fun j _ => abs_add_le _ _
        _ ≤ |a / 2| + |-(a / 2)| := by
            rw [Finset.sum_add_distrib]
            exact add_le_add (sum_abs_pick 0 _) (sum_abs_pick 1 _)
        _ = a := by rw [abs_neg, abs_of_nonneg (by positivity)]; ring
    · simp; exact ha

/-- Every weight of the magnitude networks is `0`, `a/m`, `σ a/m`, `a`, `a/2` or `-a/2`.
Auxiliary for the grid statement of `prop:magnitude-obstruction`. -/
lemma magNet_W_cases (ℓ : ℕ) (i j : Fin n) :
    (magNet (n := n) m D a σ).W ℓ i j = 0 ∨ (magNet (n := n) m D a σ).W ℓ i j = a / m ∨
      (magNet (n := n) m D a σ).W ℓ i j = σ * (a / m) ∨ (magNet (n := n) m D a σ).W ℓ i j = a ∨
      (magNet (n := n) m D a σ).W ℓ i j = a / 2 ∨
      (magNet (n := n) m D a σ).W ℓ i j = -(a / 2) := by
  simp only [magNet, firstRow, pick]
  split_ifs <;> simp_all

/-- All parameters lie on the grid `2^{-b}ℤ` when `a = A 2^{-r}`, `m = 2^k`, `b ≥ r + k + 1`:
the only divisions of `a` are by `m` and by `2`. Paper: `prop:magnitude-obstruction`. -/
theorem magNet_grid (A r k b : ℕ) (hb : r + k + 1 ≤ b) (hσ : σ = 1 ∨ σ = -1)
    (ha : a = A / 2 ^ r) (hm : m = 2 ^ k) (ℓ : ℕ) (i j : Fin n) :
    ∃ z : ℤ, (magNet (n := n) m D a σ).W ℓ i j = z / 2 ^ b := by
  have e1 : a / m = ((A * 2 ^ (b - (r + k)) : ℕ) : ℝ) / 2 ^ b := by
    have hb' : (2 : ℝ) ^ b = 2 ^ r * 2 ^ k * 2 ^ (b - (r + k)) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [ha, hm, hb']; push_cast; field_simp
  have e2 : a / 2 = ((A * 2 ^ (b - (r + 1)) : ℕ) : ℝ) / 2 ^ b := by
    have hb' : (2 : ℝ) ^ b = 2 ^ r * 2 * 2 ^ (b - (r + 1)) := by
      rw [← pow_succ, ← pow_add]; congr 1; omega
    rw [ha, hb']; push_cast; field_simp
  have e3 : a = ((A * 2 ^ (b - r) : ℕ) : ℝ) / 2 ^ b := by
    have hb' : (2 : ℝ) ^ b = 2 ^ r * 2 ^ (b - r) := by
      rw [← pow_add]; congr 1; omega
    rw [ha, hb']; push_cast; field_simp
  rcases magNet_W_cases m D a σ ℓ i j with h | h | h | h | h | h <;> rw [h]
  · exact ⟨0, by simp⟩
  · exact ⟨(A * 2 ^ (b - (r + k)) : ℕ), by rw [e1]; push_cast; ring⟩
  · rcases hσ with rfl | rfl
    · exact ⟨(A * 2 ^ (b - (r + k)) : ℕ), by rw [one_mul, e1]; push_cast; ring⟩
    · exact ⟨-((A * 2 ^ (b - (r + k)) : ℕ) : ℤ), by rw [e1]; push_cast; ring⟩
  · exact ⟨(A * 2 ^ (b - r) : ℕ), by rw [e3]; push_cast; ring⟩
  · exact ⟨(A * 2 ^ (b - (r + 1)) : ℕ), by rw [e2]; push_cast; ring⟩
  · exact ⟨-((A * 2 ^ (b - (r + 1)) : ℕ) : ℤ), by rw [e2]; push_cast; ring⟩

end Magnitude

/-! ## A zero product profile can conceal a hard network -/

section Profile

variable {m : ℕ}

/-- The sign `±1` of a Boolean input bit. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- Signs `εⱼ = 1` on the first half and `-1` on the second half of `m` coordinates. -/
def halfSign (j : Fin m) : ℝ := if 2 * (j : ℕ) < m then 1 else -1

/-- The signed mean chain `f(x) = F_{a,D}(m⁻¹(∑_{i<m/2} xᵢ - ∑_{i≥m/2} xᵢ))`. -/
def signedChain (a : ℝ) (D : ℕ) (x : Fin m → Bool) : ℝ :=
  gainIter Real.tanh a D ((∑ j, halfSign j * sgn (x j)) / m)

/-- The common-mean product profile `H_f(t) = ∑ₓ f(x) ∏ᵢ (1 + t xᵢ)/2`. -/
def profile (f : (Fin m → Bool) → ℝ) (t : ℝ) : ℝ :=
  ∑ x : Fin m → Bool, (∏ i, (1 + t * sgn (x i)) / 2) * f x

/-- Exchanging the halves negates the signs `εⱼ`. Auxiliary for `prop:profile-obstruction`
(instance_information.tex). -/
lemma halfSign_rev (hm : Even m) (j : Fin m) : halfSign (Fin.rev j) = -halfSign j := by
  obtain ⟨h, rfl⟩ := hm
  unfold halfSign
  rw [Fin.val_rev]
  have hj := j.isLt
  by_cases hlt : 2 * (j : ℕ) < h + h
  · have : ¬ 2 * (h + h - (j + 1)) < h + h := by omega
    simp [hlt, this]
  · have : 2 * (h + h - (j + 1)) < h + h := by omega
    simp [hlt, this]

/-- **The product profile of the signed mean chain vanishes.** Exchanging the two halves of
the input leaves the common-mean product law invariant and negates the output, so
`E_t f(X) = 0` for every `t`.

Paper: `prop:profile-obstruction` (instance_information.tex). -/
theorem profile_signedChain_zero (hm : Even m) (a : ℝ) (D : ℕ) (t : ℝ) :
    profile (signedChain (m := m) a D) t = 0 := by
  unfold profile
  let e : (Fin m → Bool) ≃ (Fin m → Bool) := Equiv.arrowCongr Fin.revPerm (Equiv.refl Bool)
  have he : ∀ x, e x = fun j => x (Fin.rev j) := fun x => by
    funext j; simp [e, Equiv.arrowCongr_apply, Fin.revPerm_symm]
  refine weighted_sum_zero_of_odd_equiv e _ _ (fun x => ?_) (fun x => ?_)
  · rw [he]
    exact Equiv.prod_comp Fin.revPerm (fun i => (1 + t * sgn (x i)) / 2)
  · rw [he]
    unfold signedChain
    have hsum : ∑ j, halfSign j * sgn (x (Fin.rev j)) = -∑ j, halfSign j * sgn (x j) := by
      rw [← Equiv.sum_comp Fin.revPerm (fun j => halfSign j * sgn (x (Fin.rev j)))]
      simp only [Fin.revPerm_apply, Fin.rev_rev, halfSign_rev hm, neg_mul,
        Finset.sum_neg_distrib]
    rw [hsum, neg_div, gainIter_odd Real.tanh Real.tanh_neg]

/-- **All derivatives of the profile vanish.** Paper: `prop:profile-obstruction`
("consequently all derivatives of this one-parameter profile vanish"). -/
theorem profile_signedChain_deriv_zero (hm : Even m) (a : ℝ) (D k : ℕ) (t : ℝ) :
    iteratedDeriv k (profile (signedChain (m := m) a D)) t = 0 := by
  have : profile (signedChain (m := m) a D) = fun _ => 0 :=
    funext (profile_signedChain_zero hm a D)
  rw [this]
  exact iteratedDeriv_const_zero

/-- A first-layer row with weights `c` on the first half and `-c` on the second half of the
first `m` inputs. -/
def signedRow {n : ℕ} (c : ℝ) (j : Fin n) : ℝ :=
  if 2 * (j : ℕ) < m then c else if (j : ℕ) < m then -c else 0

/-- The network realizing the signed mean chain on the first `m` of `n` inputs: the first row
has weights `±a/m`, and each later row has the single weight `a` on neuron `0`. -/
def profileNet {n : ℕ} (a : ℝ) : Net n where
  W ℓ i j := if (i : ℕ) = 0 then (if ℓ = 0 then signedRow (m := m) (a / m) j else pick 0 a j)
    else 0
  B _ _ := 0

/-- The unsigned mean-chain network with the same pattern of weights. -/
def chainNet {n : ℕ} (a : ℝ) : Net n where
  W ℓ i j := if (i : ℕ) = 0 then (if ℓ = 0 then firstRow m (a / m) j else pick 0 a j) else 0
  B _ _ := 0

/-- **Network realization of the signed chain.** For `n ≥ 1`, the output neuron of `profileNet`
at depth `D ≥ 1` equals `F_{a,D}(m⁻¹ ∑ⱼ εⱼ xⱼ)`, where `εⱼ = 1` on the first half and `-1` on
the second half of the first `m` inputs, and `0` elsewhere.

Paper: proof of `prop:profile-obstruction` (instance_information.tex). -/
theorem profileNet_output {n : ℕ} (hn : 1 ≤ n) (a : ℝ) (x : Fin n → ℝ) :
    ∀ D, 1 ≤ D → (profileNet (m := m) (n := n) a).eval x D ⟨0, by omega⟩ =
      gainIter Real.tanh a D ((∑ j : Fin n, signedRow (m := m) 1 j * x j) / m) := by
  intro D hD
  have hB : ∀ ℓ i, (profileNet (m := m) (n := n) a).B ℓ i = 0 := fun _ _ => rfl
  induction D with
  | zero => omega
  | succ D ih =>
    rcases Nat.eq_zero_or_pos D with rfl | hpos
    · have e0 : (profileNet (m := m) (n := n) a).eval x 0 = x := rfl
      have hW : ∀ j, (profileNet (m := m) (n := n) a).W 0 ⟨0, by omega⟩ j =
          a / m * signedRow (m := m) 1 j := fun j => by
        simp only [profileNet, ↓reduceIte, signedRow]
        split_ifs <;> ring
      rw [Net.eval_succ, hB, zero_add, e0, Finset.sum_congr rfl fun j _ => by rw [hW j]]
      simp only [gainIter]
      congr 1
      rw [mul_div_assoc', Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · have hD0 : D ≠ 0 := by omega
      have hW : ∀ j, (profileNet (m := m) (n := n) a).W D ⟨0, by omega⟩ j = pick 0 a j :=
        fun j => by simp [profileNet, hD0]
      rw [Net.eval_succ, hB, zero_add, Finset.sum_congr rfl fun j _ => by rw [hW j],
        sum_pick 0 (by omega), ih hpos]
      rfl

/-- The signed and unsigned chain networks have the same entrywise absolute weights and zero
biases: the signed chain only flips the signs of half of the first row. Paper: proof of
`prop:profile-obstruction` (instance_information.tex). -/
theorem profileNet_abs {n : ℕ} (a : ℝ) (ℓ : ℕ) (i j : Fin n) :
    |(profileNet (m := m) (n := n) a).W ℓ i j| = |(chainNet (m := m) (n := n) a).W ℓ i j| ∧
      (profileNet (m := m) (n := n) a).B ℓ i = 0 ∧ (chainNet (m := m) (n := n) a).B ℓ i = 0 := by
  refine ⟨?_, rfl, rfl⟩
  simp only [profileNet, chainNet]
  split_ifs
  · simp only [signedRow, firstRow]
    split_ifs <;> first | rfl | omega | simp [abs_neg]
  · rfl
  · rfl

/-- Row norms of the signed chain network are at most `a` for `a ≥ 0`, `m ≥ 1`. Paper: proof
of `prop:profile-obstruction` ("row norms at most `a`"). -/
theorem profileNet_rowNorm {n : ℕ} {a : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m) (ℓ : ℕ) (i : Fin n) :
    (profileNet (m := m) (n := n) a).rowNorm ℓ i ≤ a := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold Net.rowNorm
  have habs : ∀ j, |(profileNet (m := m) (n := n) a).W ℓ i j| =
      |(chainNet (m := m) (n := n) a).W ℓ i j| := fun j => (profileNet_abs a ℓ i j).1
  simp only [habs, chainNet]
  split_ifs
  · calc ∑ j, |firstRow (n := n) m (a / m) j| ≤ m * |a / m| := sum_abs_firstRow m _
      _ = a := by rw [abs_of_nonneg (by positivity)]; field_simp
  · simpa [abs_of_nonneg ha] using sum_abs_pick (n := n) 0 a
  · simp; exact ha

/-- **The network computes the signed chain.** On sign inputs `xⱼ = ±1` with `n = m`, the
output of `profileNet` at depth `D ≥ 1` equals `signedChain a D`. Paper: proof of
`prop:profile-obstruction` (instance_information.tex). -/
theorem profileNet_eq_signedChain (hm : 1 ≤ m) (a : ℝ) {D : ℕ} (hD : 1 ≤ D)
    (y : Fin m → Bool) :
    (profileNet (m := m) (n := m) a).eval (fun j => sgn (y j)) D ⟨0, by omega⟩ =
      signedChain (m := m) a D y := by
  rw [profileNet_output hm a _ D hD]
  unfold signedChain
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (j : ℕ) < m := j.isLt
  simp only [signedRow, halfSign]
  split_ifs <;> ring

/-- **Grid for the signed chain network.** If `a` and `a/m` lie on the grid `2^{-b}ℤ`, so does
every weight of `profileNet`. Paper: `prop:profile-obstruction` ("whenever `a` and `a/m` belong
to the parameter grid"). -/
theorem profileNet_grid {n b : ℕ} {a : ℝ} (ha : ∃ z : ℤ, a = z / 2 ^ b)
    (ham : ∃ z : ℤ, a / m = z / 2 ^ b) (ℓ : ℕ) (i j : Fin n) :
    ∃ z : ℤ, (profileNet (m := m) (n := n) a).W ℓ i j = z / 2 ^ b := by
  obtain ⟨za, hza⟩ := ha
  obtain ⟨zm, hzm⟩ := ham
  simp only [profileNet, signedRow, pick]
  split_ifs
  all_goals first
    | exact ⟨zm, hzm⟩
    | exact ⟨-zm, by rw [hzm]; push_cast; ring⟩
    | exact ⟨za, hza⟩
    | exact ⟨0, by simp⟩

end Profile

end

end ExactSampling.WeightObstructions
