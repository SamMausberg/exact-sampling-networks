import Mathlib

/-!
# The flow program and the continuity of its value

Paper file: instance_flow.tex, `lem:instanceflow` and its proof.

Formalized:
* The flow program over partial assignments `{-1,*,1}^m` (`FlowSol`, `FlowSol.Feasible`) and its
  value `Flow(p)` (`flowValue`), with the incoming-flow, conservation, output and cost
  constraints of the paper.
* Feasibility of the complete scan with cost `m` for every table in `[0, 1]`
  (`scanSol_feasible`), feasibility of convex combinations (`FlowSol.mix_feasible`), hence
  `0 ≤ Flow(p) ≤ m` and the mixture bound `Flow(p) ≤ (1 - γ) Flow(q) + γ m`.
* The interior margin of network output probabilities: if the output preactivation has bias at
  most one, row norm at most `s` and inputs in `[-1,1]`, then `|z| ≤ 1 + s` and
  `(1 + tanh z)/2 ∈ [ε, 1 - ε]` with `ε = (1 - tanh(1 + s))/2 > 0`.
* The mixture table `r = (p - (1 - γ) q)/γ ∈ [0, 1]` and the quantitative continuity
  `|Flow(p) - Flow(q)| ≤ (m/ε) ‖p - q‖_∞` on the interior cube (`flowValue_lipschitz`).

Not formalized: the equality of `Flow(p)` with the query optimum (both directions of
`lem:instanceflow`: tree histories to flows, and normalized flows to samplers), and the
computability argument with finite-bit samplers.
-/

namespace ExactSampling.QueryFlow

noncomputable section

/-- **Preactivation bound.** With bias at most one in absolute value, row norm at most `s` and
inputs in `[-1,1]`, the preactivation `b + ∑ⱼ wⱼ hⱼ` has absolute value at most `1 + s`.
Paper: proof of `lem:instanceflow` (instance_flow.tex). -/
theorem preactivation_bound {k : ℕ} {s b : ℝ} {w h : Fin k → ℝ} (hb : |b| ≤ 1)
    (hw : ∑ j, |w j| ≤ s) (hh : ∀ j, |h j| ≤ 1) : |b + ∑ j, w j * h j| ≤ 1 + s := by
  calc |b + ∑ j, w j * h j| ≤ |b| + |∑ j, w j * h j| := abs_add_le _ _
    _ ≤ |b| + ∑ j, |w j * h j| := by gcongr; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ 1 + ∑ j, |w j| := add_le_add hb (Finset.sum_le_sum fun j _ => by
        rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hh j))
    _ ≤ 1 + s := by linarith

/-- **Interior margin.** If the output preactivation satisfies `|z| ≤ 1 + s` (for instance by
`preactivation_bound`), the output probability
`(1 + tanh z)/2` lies in `[ε, 1 - ε]` for `ε = (1 - tanh(1 + s))/2 > 0`.

Paper: proof of `lem:instanceflow` (instance_flow.tex). -/
theorem output_margin {s z : ℝ} (hz : |z| ≤ 1 + s) :
    0 < (1 - Real.tanh (1 + s)) / 2 ∧
      (1 - Real.tanh (1 + s)) / 2 ≤ (1 + Real.tanh z) / 2 ∧
      (1 + Real.tanh z) / 2 ≤ 1 - (1 - Real.tanh (1 + s)) / 2 := by
  have hmono : Monotone Real.tanh := by
    have hd : ∀ x, HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := fun x => by
      have h : Real.tanh = Real.sinh / Real.cosh := by
        funext y; rw [Pi.div_apply, Real.tanh_eq_sinh_div_cosh]
      have hc := (Real.cosh_pos x).ne'
      have hd := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
      rw [← h] at hd
      refine hd.congr_deriv ?_
      rw [Real.tanh_eq_sinh_div_cosh, div_pow]
      field_simp
    exact (strictMono_of_hasDerivAt_pos hd fun x => by
      have := Real.tanh_sq_lt_one x; linarith).monotone
  have h1 := Real.tanh_lt_one (1 + s)
  obtain ⟨hlo, hhi⟩ := abs_le.mp hz
  have h2 : Real.tanh z ≤ Real.tanh (1 + s) := hmono hhi
  have h3 : Real.tanh (-(1 + s)) ≤ Real.tanh z := hmono hlo
  rw [Real.tanh_neg] at h3
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **The mixture table.** If `p, q ∈ [ε, 1 - ε]` pointwise, `|p - q| ≤ δ` and `0 < δ ≤ ε`,
then with `γ = δ/ε` the table `r = (p - (1 - γ) q)/γ` takes values in `[0, 1]` and
`(1 - γ) q + γ r = p`.

Paper: proof of `lem:instanceflow` (instance_flow.tex). -/
theorem mixture_table {X : Type*} {p q : X → ℝ} {ε δ : ℝ}
    (hp : ∀ x, ε ≤ p x ∧ p x ≤ 1 - ε) (hq : ∀ x, ε ≤ q x ∧ q x ≤ 1 - ε)
    (hpq : ∀ x, |p x - q x| ≤ δ) (hδ : 0 < δ) (hδε : δ ≤ ε) (x : X) :
    0 ≤ (p x - (1 - δ / ε) * q x) / (δ / ε) ∧ (p x - (1 - δ / ε) * q x) / (δ / ε) ≤ 1 ∧
      (1 - δ / ε) * q x + δ / ε * ((p x - (1 - δ / ε) * q x) / (δ / ε)) = p x := by
  have hε : 0 < ε := lt_of_lt_of_le hδ hδε
  have hγ : 0 < δ / ε := div_pos hδ hε
  have hd := abs_le.mp (hpq x)
  obtain ⟨hp1, hp2⟩ := hp x
  obtain ⟨hq1, hq2⟩ := hq x
  refine ⟨?_, ?_, ?_⟩
  · apply div_nonneg _ hγ.le
    -- `γ q ≥ γ ε = δ ≥ q - p`
    have : δ ≤ δ / ε * q x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hε]; nlinarith
    nlinarith
  · rw [div_le_one hγ]
    -- `γ (1 - q) ≥ γ ε = δ ≥ p - q`
    have : δ ≤ δ / ε * (1 - q x) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hε]; nlinarith
    nlinarith
  · field_simp
    ring

/-- **Cost of the mixture.** Mixing a sampler of worst-input cost `C` with probability
`1 - γ` and a complete scan of `m` coordinates with probability `γ = δ/ε` costs at most
`C + (m/ε) δ`. Paper: proof of `lem:instanceflow` (instance_flow.tex). -/
theorem mixture_cost {C m ε δ : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hδ : 0 ≤ δ) :
    (1 - δ / ε) * C + δ / ε * m ≤ C + m / ε * δ := by
  have : 0 ≤ δ / ε * C := by positivity
  have e : δ / ε * m = m / ε * δ := by ring
  nlinarith

/-- **Abstract continuity step.** This lemma is used with `Flow = flowValue` in
`flowValue_lipschitz`, where both hypotheses are proved. Let `Flow` take values in `[0, m]` on the
interior cube `[ε, 1 - ε]^X`, and suppose that the mixture construction bounds it:
`Flow(p) ≤ (1 - γ) Flow(q) + γ m` whenever `0 < δ ≤ ε`, `‖p - q‖_∞ ≤ δ` and `γ = δ/ε`. Then
`|Flow(p) - Flow(q)| ≤ (m/ε) ‖p - q‖_∞` on the cube.

Paper: proof of `lem:instanceflow` (instance_flow.tex). -/
theorem flow_lipschitz {X : Type*} (Flow : (X → ℝ) → ℝ) {m ε : ℝ} (hε : 0 < ε)
    (Cube : (X → ℝ) → Prop)
    (hrange : ∀ p, Cube p → 0 ≤ Flow p ∧ Flow p ≤ m)
    (hmix : ∀ p q δ, Cube p → Cube q → 0 < δ → δ ≤ ε → (∀ x, |p x - q x| ≤ δ) →
      Flow p ≤ (1 - δ / ε) * Flow q + δ / ε * m)
    {p q : X → ℝ} (hp : Cube p) (hq : Cube q) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hpq : ∀ x, |p x - q x| ≤ δ) :
    |Flow p - Flow q| ≤ m / ε * δ := by
  obtain ⟨hp0, hpm⟩ := hrange p hp
  obtain ⟨hq0, hqm⟩ := hrange q hq
  have hm : 0 ≤ m := le_trans hp0 hpm
  rcases le_or_gt δ ε with hle | hlt
  · rcases hδ0.lt_or_eq with hpos | hzero
    · have h1 := hmix p q δ hp hq hpos hle hpq
      have h2 := hmix q p δ hq hp hpos hle fun x => by rw [abs_sub_comm]; exact hpq x
      have c1 := mixture_cost (m := m) hq0 hε hδ0
      have c2 := mixture_cost (m := m) hp0 hε hδ0
      rw [abs_le]; constructor <;> linarith
    · -- `δ = 0`: take any smaller positive tolerance
      subst hzero
      have hsmall : ∀ η, 0 < η → η ≤ ε → |Flow p - Flow q| ≤ m / ε * η := by
        intro η hη hηε
        have hpq' : ∀ x, |p x - q x| ≤ η := fun x => (hpq x).trans hη.le
        have h1 := hmix p q η hp hq hη hηε hpq'
        have h2 := hmix q p η hq hp hη hηε fun x => by rw [abs_sub_comm]; exact hpq' x
        have c1 := mixture_cost (m := m) hq0 hε hη.le
        have c2 := mixture_cost (m := m) hp0 hε hη.le
        rw [abs_le]; constructor <;> linarith
      rw [mul_zero]
      by_contra hne
      push Not at hne
      set g := |Flow p - Flow q|
      have hm' : 0 < m := by
        rcases hm.lt_or_eq with h | h
        · exact h
        · exfalso
          have : g ≤ 0 := by
            have := hsmall ε hε le_rfl
            rw [← h] at this; simpa using this
          linarith
      have := hsmall (min ε (g * ε / (2 * m))) (lt_min hε (by positivity)) (min_le_left _ _)
      have hmin : m / ε * min ε (g * ε / (2 * m)) ≤ m / ε * (g * ε / (2 * m)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      have heq : m / ε * (g * ε / (2 * m)) = g / 2 := by field_simp
      linarith
  · -- `δ > ε`: the trivial range bound suffices
    have : m ≤ m / ε * δ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hε]; nlinarith
    rw [abs_le]; constructor <;> linarith


/-! ## The flow program -/

section LP

open Classical

variable {m : ℕ}

/-- `x` extends the partial assignment `σ ∈ {-1,*,1}^m` (`none` is `*`). -/
def Extends (σ : Fin m → Option Bool) (x : Fin m → Bool) : Prop :=
  ∀ i, σ i = none ∨ σ i = some (x i)

/-- A candidate solution of the flow program: stopping flows `u`, `v` and query flows `a`. -/
structure FlowSol (m : ℕ) where
  /-- Flow stopping with output one at a partial assignment. -/
  u : (Fin m → Option Bool) → ℝ
  /-- Flow stopping with output zero at a partial assignment. -/
  v : (Fin m → Option Bool) → ℝ
  /-- Flow querying an unassigned coordinate at a partial assignment. -/
  a : (Fin m → Option Bool) → Fin m → ℝ

/-- Incoming flow: `1` at the empty assignment, otherwise the query flows of the assignments
with one coordinate removed. -/
noncomputable def FlowSol.inflow (F : FlowSol m) (σ : Fin m → Option Bool) : ℝ :=
  if σ = (fun _ => none) then 1
  else ∑ i ∈ Finset.univ.filter (fun i => σ i ≠ none), F.a (Function.update σ i none) i

/-- Outgoing flow: stopping plus queries of unassigned coordinates. -/
noncomputable def FlowSol.outflow (F : FlowSol m) (σ : Fin m → Option Bool) : ℝ :=
  F.u σ + F.v σ + ∑ i ∈ Finset.univ.filter (fun i => σ i = none), F.a σ i

/-- Probability of returning one on the input `x`. -/
noncomputable def FlowSol.outAt (F : FlowSol m) (x : Fin m → Bool) : ℝ :=
  ∑ σ, if Extends σ x then F.u σ else 0

/-- Expected number of queries on the input `x`. -/
noncomputable def FlowSol.costAt (F : FlowSol m) (x : Fin m → Bool) : ℝ :=
  ∑ σ, if Extends σ x then ∑ i ∈ Finset.univ.filter (fun i => σ i = none), F.a σ i else 0

/-- Feasibility for the output table `p` with worst-input cost at most `C`. -/
def FlowSol.Feasible (F : FlowSol m) (p : (Fin m → Bool) → ℝ) (C : ℝ) : Prop :=
  (∀ σ, 0 ≤ F.u σ) ∧ (∀ σ, 0 ≤ F.v σ) ∧ (∀ σ i, 0 ≤ F.a σ i) ∧
    (∀ σ, F.inflow σ = F.outflow σ) ∧ (∀ x, F.outAt x = p x) ∧ (∀ x, F.costAt x ≤ C)

/-- The value `Flow(p)` of the flow program. -/
noncomputable def flowValue (p : (Fin m → Bool) → ℝ) : ℝ :=
  sInf {C | ∃ F : FlowSol m, F.Feasible p C}

/-- The mixture `(1 - γ) F + γ G` of two candidate solutions. -/
def FlowSol.mix (γ : ℝ) (F G : FlowSol m) : FlowSol m where
  u σ := (1 - γ) * F.u σ + γ * G.u σ
  v σ := (1 - γ) * F.v σ + γ * G.v σ
  a σ i := (1 - γ) * F.a σ i + γ * G.a σ i

/-- **Mixing feasible flows.** A convex combination of a feasible flow for `q` with cost `C` and
a feasible flow for `r` with cost `C'` is feasible for `(1 - γ) q + γ r` with cost
`(1 - γ) C + γ C'`. Paper: proof of `lem:instanceflow` (instance_flow.tex). -/
theorem FlowSol.mix_feasible {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) {F G : FlowSol m}
    {q r : (Fin m → Bool) → ℝ} {C C' : ℝ} (hF : F.Feasible q C) (hG : G.Feasible r C') :
    (F.mix γ G).Feasible (fun x => (1 - γ) * q x + γ * r x) ((1 - γ) * C + γ * C') := by
  obtain ⟨hFu, hFv, hFa, hFc, hFo, hFk⟩ := hF
  obtain ⟨hGu, hGv, hGa, hGc, hGo, hGk⟩ := hG
  have h1 : 0 ≤ 1 - γ := by linarith
  refine ⟨fun σ => ?_, fun σ => ?_, fun σ i => ?_, fun σ => ?_, fun x => ?_, fun x => ?_⟩
  · simp only [mix]; have := hFu σ; have := hGu σ; positivity
  · simp only [mix]; have := hFv σ; have := hGv σ; positivity
  · simp only [mix]; have := hFa σ i; have := hGa σ i; positivity
  · have e1 : (F.mix γ G).inflow σ = (1 - γ) * F.inflow σ + γ * G.inflow σ := by
      unfold inflow
      split_ifs
      · ring
      · simp only [mix, Finset.sum_add_distrib, ← Finset.mul_sum]
    have e2 : (F.mix γ G).outflow σ = (1 - γ) * F.outflow σ + γ * G.outflow σ := by
      simp only [outflow, mix, Finset.sum_add_distrib, ← Finset.mul_sum]; ring
    rw [e1, e2, hFc σ, hGc σ]
  · have e : (F.mix γ G).outAt x = (1 - γ) * F.outAt x + γ * G.outAt x := by
      simp only [outAt, mix, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun σ _ => ?_
      split_ifs <;> ring
    rw [e, hFo x, hGo x]
  · have e : (F.mix γ G).costAt x = (1 - γ) * F.costAt x + γ * G.costAt x := by
      simp only [costAt, mix, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun σ _ => ?_
      split_ifs
      · rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      · ring
    rw [e]
    have := hFk x; have := hGk x
    nlinarith

/-- `σ` assigns exactly the first `k` coordinates. -/
def IsPrefix (k : ℕ) (σ : Fin m → Option Bool) : Prop := ∀ i : Fin m, σ i ≠ none ↔ (i : ℕ) < k

/-- The full input read from a complete assignment. -/
def toInput (σ : Fin m → Option Bool) : Fin m → Bool := fun i => (σ i).getD false

/-- The complete-scan flow for an output table `r`: query coordinates in order, then stop with
one with probability `r(x)`. -/
noncomputable def scanSol (r : (Fin m → Bool) → ℝ) : FlowSol m where
  u σ := if IsPrefix m σ then r (toInput σ) else 0
  v σ := if IsPrefix m σ then 1 - r (toInput σ) else 0
  a σ i := if IsPrefix i σ then 1 else 0

/-- A prefix length up to `m` is unique. Auxiliary for `scanSol_feasible`
(`lem:instanceflow`, instance_flow.tex). -/
lemma isPrefix_unique {σ : Fin m → Option Bool} {k k' : ℕ} (hk : k ≤ m) (hk' : k' ≤ m)
    (h : IsPrefix k σ) (h' : IsPrefix k' σ) : k = k' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := (h ⟨k, by omega⟩).symm.trans (h' ⟨k, by omega⟩)
    simp at this; omega
  · have := (h ⟨k', by omega⟩).symm.trans (h' ⟨k', by omega⟩)
    simp at this; omega

/-- Removing the last coordinate of a prefix of length `i + 1` gives the prefix of length `i`.
Auxiliary for `scanSol_feasible` (`lem:instanceflow`, instance_flow.tex). -/
lemma isPrefix_update {σ : Fin m → Option Bool} {i : Fin m} (hi : σ i ≠ none) :
    IsPrefix i (Function.update σ i none) ↔ IsPrefix (i + 1) σ := by
  constructor
  · intro h j
    by_cases hj : j = i
    · subst hj; simp [hi]
    · have := h j
      rw [Function.update_of_ne hj] at this
      rw [this]
      have : (j : ℕ) ≠ i := fun e => hj (Fin.ext e)
      omega
  · intro h j
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj, h j]
      have : (j : ℕ) ≠ i := fun e => hj (Fin.ext e)
      omega

/-- The empty assignment is the prefix of length zero. Auxiliary for `scanSol_feasible`
(`lem:instanceflow`, instance_flow.tex). -/
lemma isPrefix_empty : IsPrefix 0 (fun _ : Fin m => (none : Option Bool)) := by
  intro i; simp

/-- **The complete scan is feasible** for every table `r` with values in `[0, 1]`, with cost
`m`. Paper: proof of `lem:instanceflow` ("a complete input scan followed by an `r(x)`-coin"). -/
theorem scanSol_feasible {r : (Fin m → Bool) → ℝ} (hr : ∀ x, 0 ≤ r x ∧ r x ≤ 1) :
    (scanSol r).Feasible r m := by
  refine ⟨fun σ => ?_, fun σ => ?_, fun σ i => ?_, fun σ => ?_, fun x => ?_, fun x => ?_⟩
  · simp only [scanSol]; split_ifs <;> linarith [(hr (toInput σ)).1]
  · simp only [scanSol]; split_ifs <;> linarith [(hr (toInput σ)).2]
  · simp only [scanSol]; split_ifs <;> norm_num
  · -- conservation
    -- the outflow is the indicator that `σ` is a prefix
    have hout : (scanSol r).outflow σ = if ∃ k ≤ m, IsPrefix k σ then 1 else 0 := by
      unfold FlowSol.outflow scanSol
      simp only
      by_cases hfull : IsPrefix m σ
      · have hnone : Finset.univ.filter (fun i => σ i = none) = ∅ := by
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro h; exact absurd ((hfull i).mpr i.isLt) (by simp [h])
          · intro h; simp at h
        rw [ite_eq_left hfull, ite_eq_left hfull, hnone, ite_eq_left ⟨m, le_rfl, hfull⟩]
        simp
      · rw [ite_eq_right hfull, ite_eq_right hfull, zero_add, zero_add]
        by_cases hpre : ∃ k ≤ m, IsPrefix k σ
        · obtain ⟨k, hkm, hk⟩ := hpre
          have hk' : k < m := lt_of_le_of_ne hkm fun e => hfull (e ▸ hk)
          rw [ite_eq_left ⟨k, hkm, hk⟩]
          rw [Finset.sum_eq_single ⟨k, hk'⟩]
          · rw [ite_eq_left (by simpa using hk)]
          · intro i hi hne
            rw [ite_eq_right]
            intro hpi
            exact hne (Fin.ext (isPrefix_unique (by omega) hkm hpi hk))
          · intro h
            exfalso; apply h
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            by_contra hs
            exact absurd ((hk ⟨k, hk'⟩).mp hs) (lt_irrefl k)
        · rw [ite_eq_right hpre]
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [ite_eq_right]
          intro hpi
          exact hpre ⟨i, i.isLt.le, hpi⟩
    rw [hout]
    unfold FlowSol.inflow
    by_cases hσ : σ = fun _ => none
    · rw [ite_eq_left hσ, ite_eq_left ⟨0, Nat.zero_le _, hσ ▸ isPrefix_empty⟩]
    · rw [ite_eq_right hσ]
      simp only [scanSol]
      by_cases hpre : ∃ k ≤ m, IsPrefix k σ
      · obtain ⟨k, hkm, hk⟩ := hpre
        rw [ite_eq_left ⟨k, hkm, hk⟩]
        -- `k ≥ 1`, and the unique contributing coordinate is `k - 1`
        have hk1 : 1 ≤ k := by
          by_contra h0
          push Not at h0
          apply hσ
          funext i
          by_contra hne
          have := (hk i).mp hne
          omega
        have hlt : k - 1 < m := by omega
        rw [Finset.sum_eq_single ⟨k - 1, hlt⟩]
        · have hs : σ ⟨k - 1, hlt⟩ ≠ none := (hk ⟨k - 1, hlt⟩).mpr (by simp; omega)
          rw [ite_eq_left ((isPrefix_update hs).mpr (by
            simp only
            rw [Nat.sub_add_cancel hk1]; exact hk))]
        · intro i hi hne
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          rw [ite_eq_right]
          intro hpi
          have := isPrefix_unique (by omega) hkm ((isPrefix_update hi).mp hpi) hk
          exact hne (Fin.ext (by simp; omega))
        · intro h
          exfalso; apply h
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact (hk ⟨k - 1, hlt⟩).mpr (by simp; omega)
      · rw [ite_eq_right hpre]
        refine Finset.sum_eq_zero fun i hi => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [ite_eq_right]
        intro hpi
        exact hpre ⟨i + 1, by omega, (isPrefix_update hi).mp hpi⟩
  · -- output law
    unfold FlowSol.outAt scanSol
    simp only
    rw [Finset.sum_eq_single (fun i => some (x i))]
    · have hfull : IsPrefix m (fun i => some (x i)) := fun i => by simp
      rw [ite_eq_left (show Extends (fun i => some (x i)) x from fun i => Or.inr rfl),
        ite_eq_left hfull]
      congr 1
    · intro σ _ hne
      split_ifs with h1 h2
      · exfalso; apply hne
        funext i
        rcases h1 i with h | h
        · exact absurd ((h2 i).mpr i.isLt) (by simp [h])
        · exact h
      · rfl
      · rfl
    · simp
  · -- cost: exactly one query of each coordinate
    unfold FlowSol.costAt scanSol
    simp only
    have hswap : (∑ σ : Fin m → Option Bool, if Extends σ x then
        ∑ i ∈ Finset.univ.filter (fun i => σ i = none), (if IsPrefix i σ then (1 : ℝ) else 0)
        else 0) =
        ∑ i : Fin m, ∑ σ : Fin m → Option Bool,
          (if Extends σ x ∧ σ i = none ∧ IsPrefix i σ then (1 : ℝ) else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ _ => ?_
      split_ifs with h
      · rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h1 : σ i = none <;> by_cases h2 : IsPrefix i σ <;> simp [h, h1, h2]
      · simp [h]
    rw [hswap]
    have hone : ∀ i : Fin m, (∑ σ : Fin m → Option Bool,
        (if Extends σ x ∧ σ i = none ∧ IsPrefix i σ then (1 : ℝ) else 0)) = 1 := by
      intro i
      set τ : Fin m → Option Bool := fun j => if (j : ℕ) < i then some (x j) else none
      rw [Finset.sum_eq_single τ]
      · rw [ite_eq_left]
        refine ⟨fun j => ?_, by simp [τ], fun j => ?_⟩
        · by_cases hj : (j : ℕ) < i
          · right; simp only [τ, hj, ite_true]
          · left; simp only [τ, hj, ite_false]
        · by_cases hj : (j : ℕ) < i
          · simp only [τ, hj, ite_true]; simp
          · simp only [τ, hj, ite_false]; simp
      · intro σ _ hne
        rw [ite_eq_right]
        rintro ⟨hext, -, hpre⟩
        apply hne
        funext j
        by_cases hj : (j : ℕ) < i
        · have h1 := (hpre j).mpr hj
          rcases hext j with h | h
          · exact absurd h h1
          · simp only [τ, hj, ite_true, h]
        · have : ¬σ j ≠ none := fun h => hj ((hpre j).mp h)
          push Not at this
          simp only [τ, hj, ite_false, this]
      · simp
    simp [hone]

/-- `Flow(q) ≥ 0` and `Flow(q) ≤ m` on tables with values in `[0, 1]`: every feasible cost is
nonnegative, and the complete scan is feasible. Paper: proof of `lem:instanceflow`. -/
theorem flowValue_range {q : (Fin m → Bool) → ℝ} (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1) :
    0 ≤ flowValue q ∧ flowValue q ≤ m := by
  have hne : {C | ∃ F : FlowSol m, F.Feasible q C}.Nonempty := ⟨m, scanSol _, scanSol_feasible hq⟩
  have hbdd : ∀ C ∈ {C | ∃ F : FlowSol m, F.Feasible q C}, 0 ≤ C := by
    rintro C ⟨F, hF⟩
    obtain ⟨-, -, ha, -, -, hk⟩ := hF
    have h0 : 0 ≤ F.costAt (fun _ => false) := by
      unfold FlowSol.costAt
      refine Finset.sum_nonneg fun σ _ => ?_
      split_ifs
      · exact Finset.sum_nonneg fun i _ => ha σ i
      · exact le_rfl
    exact h0.trans (hk _)
  constructor
  · exact le_csInf hne hbdd
  · exact csInf_le ⟨0, hbdd⟩ ⟨scanSol _, scanSol_feasible hq⟩

/-- **The mixture bound for the flow program.** If `p, q ∈ [ε, 1 - ε]`, `|p - q| ≤ δ` and
`0 < δ ≤ ε`, then `Flow(p) ≤ (1 - δ/ε) Flow(q) + (δ/ε) m`: mix any feasible flow for `q` with the
complete-scan flow for the table `r` of `mixture_table`. Paper: proof of `lem:instanceflow`
(instance_flow.tex). -/
theorem flowValue_mix {p q : (Fin m → Bool) → ℝ} {ε δ : ℝ}
    (hp : ∀ x, ε ≤ p x ∧ p x ≤ 1 - ε) (hq : ∀ x, ε ≤ q x ∧ q x ≤ 1 - ε)
    (hpq : ∀ x, |p x - q x| ≤ δ) (hδ : 0 < δ) (hδε : δ ≤ ε) :
    flowValue p ≤ (1 - δ / ε) * flowValue q + δ / ε * m := by
  have hε : 0 < ε := lt_of_lt_of_le hδ hδε
  set γ := δ / ε with hγ
  have hγ0 : 0 < γ := div_pos hδ hε
  have hγ1 : γ ≤ 1 := by rw [hγ, div_le_one hε]; exact hδε
  set r : (Fin m → Bool) → ℝ := fun x => (p x - (1 - γ) * q x) / γ
  have hr : ∀ x, 0 ≤ r x ∧ r x ≤ 1 := fun x =>
    ⟨(mixture_table hp hq hpq hδ hδε x).1, (mixture_table hp hq hpq hδ hδε x).2.1⟩
  have hrp : (fun x => (1 - γ) * q x + γ * r x) = p := funext fun x =>
    (mixture_table hp hq hpq hδ hδε x).2.2
  have hq01 : ∀ x, 0 ≤ q x ∧ q x ≤ 1 := fun x => ⟨by linarith [(hq x).1], by linarith [(hq x).2]⟩
  have hp01 : ∀ x, 0 ≤ p x ∧ p x ≤ 1 := fun x => ⟨by linarith [(hp x).1], by linarith [(hp x).2]⟩
  have hbddp : BddBelow {C | ∃ F : FlowSol m, F.Feasible p C} := by
    refine ⟨0, ?_⟩
    rintro C ⟨F, hF⟩
    obtain ⟨-, -, ha, -, -, hk⟩ := hF
    have h0 : 0 ≤ F.costAt (fun _ => false) := by
      unfold FlowSol.costAt
      refine Finset.sum_nonneg fun σ _ => ?_
      split_ifs
      · exact Finset.sum_nonneg fun i _ => ha σ i
      · exact le_rfl
    exact h0.trans (hk _)
  -- every feasible cost `C` for `q` gives the feasible cost `(1 - γ) C + γ m` for `p`
  have hstep : ∀ C ∈ {C | ∃ F : FlowSol m, F.Feasible q C},
      flowValue p ≤ (1 - γ) * C + γ * m := by
    rintro C ⟨F, hF⟩
    have hmix := FlowSol.mix_feasible hγ0.le hγ1 hF (scanSol_feasible hr)
    rw [hrp] at hmix
    exact csInf_le hbddp ⟨_, hmix⟩
  have hne : {C | ∃ F : FlowSol m, F.Feasible q C}.Nonempty :=
    ⟨m, scanSol _, scanSol_feasible hq01⟩
  rcases hγ1.lt_or_eq with hlt | heq
  · have h1 : 0 < 1 - γ := by linarith
    have : (flowValue p - γ * m) / (1 - γ) ≤ flowValue q := by
      refine le_csInf hne fun C hC => ?_
      rw [div_le_iff₀ h1]
      have := hstep C hC
      linarith
    rw [div_le_iff₀ h1] at this
    linarith
  · rw [heq, sub_self, zero_mul, zero_add, one_mul]
    exact (flowValue_range hp01).2

/-- **Quantitative continuity of the flow value.** For output tables `p, q ∈ [ε, 1 - ε]`,
`|Flow(p) - Flow(q)| ≤ (m/ε) ‖p - q‖_∞`.

Paper: proof of `lem:instanceflow` (instance_flow.tex). -/
theorem flowValue_lipschitz {p q : (Fin m → Bool) → ℝ} {ε δ : ℝ} (hε : 0 < ε)
    (hp : ∀ x, ε ≤ p x ∧ p x ≤ 1 - ε) (hq : ∀ x, ε ≤ q x ∧ q x ≤ 1 - ε) (hδ0 : 0 ≤ δ)
    (hpq : ∀ x, |p x - q x| ≤ δ) :
    |flowValue p - flowValue q| ≤ m / ε * δ :=
  flow_lipschitz flowValue hε (fun p => ∀ x, ε ≤ p x ∧ p x ≤ 1 - ε)
    (fun p hp => flowValue_range fun x => ⟨by linarith [(hp x).1, (hp x).2],
      by linarith [(hp x).1, (hp x).2]⟩)
    (fun p q δ hp hq hδ hδε hpq => flowValue_mix hp hq hpq hδ hδε) hp hq hδ0 hpq

end LP

end

end ExactSampling.QueryFlow
