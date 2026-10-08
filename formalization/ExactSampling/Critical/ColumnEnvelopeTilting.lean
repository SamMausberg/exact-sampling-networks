import Mathlib

/-!
# Exact tilting, antithetic halves, and the Pólya urn

This module formalizes the exact finite identities used by the empirical
correction of `thm:column-envelope-critical` (tanh_column_envelope.tex,
`sec:column-envelope`).

Formalized:
* the exact moments `eq:column-pairing-moments` of a signed pairing sum
  `δ_i = ∑ ε_j d_j`: `E δ^2 = v`, `E δ^4 = 3v^2 - 2u`, together with the bounds
  `ν_2 ≤ 1/m`, `ν_4 ≤ 3/m^2` and the legality of the acceptance probabilities
  `m ν_2` and `m^2 ν_4/3`;
* the finite Doob transform: the sequential plus probabilities
  `P(s + d)/(2P(s))` sum to one, path probabilities are nonnegative and sum to
  one, and every sign path has tilted probability `(∑ ε_j d_j)^k / (2^m ν_k)`;
  after acceptance, for one fixed pairing, the signs have density `m δ^2` (or
  `m^2 δ^4/3`) relative to uniform signs;
* the within-population covariance decomposition
  `(m-1)(V_A + V_B) = (2m-1)V_{2m} - 2m δ δ^T` (entrywise);
* complement symmetry of a uniform half: `E δ = 0` and `E δ^{⊗3} = 0`;
* the Pólya urn word probability `(a)_s (b)_f / (a+b)_{s+f}`, its nonnegativity,
  and that the words of each length have total probability one.

Not formalized: that a uniform pairing with uniform signs selects a uniform
half, the remaining moment identities `E δδ^T = V_{2m}/(2m)` and
`E[V_A ⊗ δ]`, the paired Taylor expansion giving
`eq:column-antithetic-identity`, the Beta-integral form of the urn
probability, and the coupling of urn draws with the sampler.
-/

open Finset

namespace ExactSampling.ColumnEnvelopeTilting

/-! ## Fair-sign averages and pairing moments -/

/-- `signAvg g ds s` is the expectation of `g (s + ∑ ε_j d_j)` over independent
fair signs `ε_j`, exposed in the order of the list `ds`. Auxiliary for
`eq:column-pairing-moments` (tanh_column_envelope.tex). -/
noncomputable def signAvg (g : ℝ → ℝ) : List ℝ → ℝ → ℝ
  | [], s => g s
  | d :: ds, s => (signAvg g ds (s + d) + signAvg g ds (s - d)) / 2

/-- Sign averages of a nonnegative function are nonnegative. Auxiliary for
`eq:column-pairing-moments` (tanh_column_envelope.tex). -/
theorem signAvg_nonneg (g : ℝ → ℝ) (hg : ∀ x, 0 ≤ g x) (ds : List ℝ) (s : ℝ) :
    0 ≤ signAvg g ds s := by
  induction ds generalizing s with
  | nil => exact hg s
  | cons d ds ih =>
    simp only [signAvg]
    have := ih (s + d)
    have := ih (s - d)
    positivity

/-- Paper: `eq:column-pairing-moments` (tanh_column_envelope.tex): the remaining
second moment is `P_2(s) = s^2 + v`, `v = ∑ d_j^2`. -/
theorem signAvg_sq (ds : List ℝ) (s : ℝ) :
    signAvg (fun x => x ^ 2) ds s = s ^ 2 + (ds.map (fun d => d ^ 2)).sum := by
  induction ds generalizing s with
  | nil => simp [signAvg]
  | cons d ds ih =>
    simp only [signAvg, ih, List.map_cons, List.sum_cons]
    ring

/-- Paper: `eq:column-pairing-moments` (tanh_column_envelope.tex): the remaining
fourth moment is `P_4(s) = s^4 + 6 s^2 v + 3v^2 - 2u`, `u = ∑ d_j^4`. -/
theorem signAvg_four (ds : List ℝ) (s : ℝ) :
    signAvg (fun x => x ^ 4) ds s =
      s ^ 4 + 6 * s ^ 2 * (ds.map (fun d => d ^ 2)).sum +
        3 * (ds.map (fun d => d ^ 2)).sum ^ 2 - 2 * (ds.map (fun d => d ^ 4)).sum := by
  induction ds generalizing s with
  | nil => simp [signAvg]
  | cons d ds ih =>
    simp only [signAvg, ih, List.map_cons, List.sum_cons]
    ring

/-- Paper: `eq:column-pairing-moments` (tanh_column_envelope.tex): if
`|d_j| ≤ 1/m` for the `m` pairs, then `ν_2 = v ≤ 1/m` and
`0 ≤ ν_4 = 3v^2 - 2u ≤ 3/m^2`. -/
theorem pairing_moment_bounds (ds : List ℝ) (m : ℝ) (hm : 0 < m) (hlen : (ds.length : ℝ) = m)
    (hd : ∀ d ∈ ds, |d| ≤ 1 / m) :
    signAvg (fun x => x ^ 2) ds 0 ≤ 1 / m ∧ 0 ≤ signAvg (fun x => x ^ 4) ds 0 ∧
      signAvg (fun x => x ^ 4) ds 0 ≤ 3 / m ^ 2 := by
  have hv : (ds.map (fun d => d ^ 2)).sum ≤ ds.length * (1 / m) ^ 2 := by
    have h := List.sum_le_length_nsmul (ds.map (fun d => d ^ 2)) ((1 / m) ^ 2) (by
      intro x hx
      obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hx
      have := hd d hd'
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg d) this 2)
    simpa [nsmul_eq_mul] using h
  have hv0 : 0 ≤ (ds.map (fun d => d ^ 2)).sum :=
    List.sum_nonneg (fun x hx => by obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx; positivity)
  have hu0 : 0 ≤ (ds.map (fun d => d ^ 4)).sum :=
    List.sum_nonneg (fun x hx => by obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx; positivity)
  rw [hlen] at hv
  have hv' : (ds.map (fun d => d ^ 2)).sum ≤ 1 / m := by
    have e : m * (1 / m) ^ 2 = 1 / m := by field_simp
    linarith
  refine ⟨?_, signAvg_nonneg _ (fun x => by positivity) ds 0, ?_⟩
  · rw [signAvg_sq]; simpa using hv'
  · rw [signAvg_four]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add]
    have h1 : (ds.map (fun d => d ^ 2)).sum ^ 2 ≤ (1 / m) ^ 2 := pow_le_pow_left₀ hv0 hv' 2
    have e : 3 * (1 / m) ^ 2 = 3 / m ^ 2 := by field_simp
    nlinarith

/-- Paper: `sec:column-envelope` (tanh_column_envelope.tex): the acceptance
probabilities `m ν_2` and `m^2 ν_4/3` of the quadratic and quartic tilts lie in
`[0, 1]`. -/
theorem acceptance_legal (ds : List ℝ) (m : ℝ) (hm : 0 < m) (hlen : (ds.length : ℝ) = m)
    (hd : ∀ d ∈ ds, |d| ≤ 1 / m) :
    0 ≤ m * signAvg (fun x => x ^ 2) ds 0 ∧ m * signAvg (fun x => x ^ 2) ds 0 ≤ 1 ∧
      0 ≤ m ^ 2 * signAvg (fun x => x ^ 4) ds 0 / 3 ∧
      m ^ 2 * signAvg (fun x => x ^ 4) ds 0 / 3 ≤ 1 := by
  obtain ⟨h2, h40, h4⟩ := pairing_moment_bounds ds m hm hlen hd
  have h20 : 0 ≤ signAvg (fun x => x ^ 2) ds 0 := signAvg_nonneg _ (fun x => by positivity) ds 0
  refine ⟨by positivity, ?_, by positivity, ?_⟩
  · have := mul_le_mul_of_nonneg_left h2 hm.le
    rwa [mul_one_div_cancel hm.ne'] at this
  · have := mul_le_mul_of_nonneg_left h4 (sq_nonneg m)
    rw [show m ^ 2 * (3 / m ^ 2) = 3 by field_simp] at this
    linarith

/-! ## The finite Doob transform -/

/-- Final partial sum of a sign path (`true` is a plus sign). Auxiliary for
`eq:column-pairing-moments` (tanh_column_envelope.tex). -/
def pathSum : List ℝ → List Bool → ℝ → ℝ
  | d :: ds, e :: es, s => pathSum ds es (if e then s + d else s - d)
  | _, _, s => s

/-- Probability of a sign path under the sequential Doob transform of `g`: at
partial sum `s` the next sign is plus with probability
`signAvg g ds (s + d) / (2 signAvg g (d :: ds) s)`. Auxiliary for
`eq:column-pairing-moments` (tanh_column_envelope.tex). -/
noncomputable def doobProb (g : ℝ → ℝ) : List ℝ → List Bool → ℝ → ℝ
  | d :: ds, e :: es, s =>
      signAvg g ds (if e then s + d else s - d) / (2 * signAvg g (d :: ds) s) *
        doobProb g ds es (if e then s + d else s - d)
  | _, _, _ => 1

/-- Paper: `eq:column-pairing-moments` (tanh_column_envelope.tex): the plus and
minus probabilities of the Doob transform sum to one. -/
theorem doob_step_sum (g : ℝ → ℝ) (d : ℝ) (ds : List ℝ) (s : ℝ)
    (h : signAvg g (d :: ds) s ≠ 0) :
    signAvg g ds (s + d) / (2 * signAvg g (d :: ds) s) +
      signAvg g ds (s - d) / (2 * signAvg g (d :: ds) s) = 1 := by
  rw [← add_div, div_eq_one_iff_eq (mul_ne_zero two_ne_zero h)]
  simp only [signAvg]
  ring

/-- If a nonnegative `g` has zero average, it vanishes on every path. Auxiliary for
`eq:column-pairing-moments` (tanh_column_envelope.tex). -/
theorem pathSum_zero_of_signAvg_zero (g : ℝ → ℝ) (hg : ∀ x, 0 ≤ g x) (ds : List ℝ)
    (es : List Bool) (hes : es.length = ds.length) (s : ℝ) (h : signAvg g ds s = 0) :
    g (pathSum ds es s) = 0 := by
  induction ds generalizing es s with
  | nil => cases es <;> simp_all [signAvg, pathSum]
  | cons d ds ih =>
    cases es with
    | nil => simp at hes
    | cons e es =>
      simp only [List.length_cons, add_left_inj] at hes
      simp only [signAvg] at h
      have h1 := signAvg_nonneg g hg ds (s + d)
      have h2 := signAvg_nonneg g hg ds (s - d)
      simp only [pathSum]
      apply ih es hes
      split_ifs <;> linarith

/-- Paper: `eq:column-pairing-moments` (tanh_column_envelope.tex): for a
nonnegative `g`, every path of length `n` has tilted probability
`g(final sum) / (2^n · signAvg g ds s)`. With `g = x^k` this is the law with
density proportional to `(∑ ε_j d_j)^k`; a zero denominator is a null path. -/
theorem doobProb_eq (g : ℝ → ℝ) (hg : ∀ x, 0 ≤ g x) (ds : List ℝ) (es : List Bool)
    (hes : es.length = ds.length) (s : ℝ) (htop : signAvg g ds s ≠ 0) :
    doobProb g ds es s = g (pathSum ds es s) / (2 ^ ds.length * signAvg g ds s) := by
  induction ds generalizing es s with
  | nil =>
    cases es with
    | nil =>
      simp only [signAvg] at htop
      simp only [doobProb, pathSum, signAvg, List.length_nil, pow_zero, one_mul]
      rw [div_self htop]
    | cons e es => simp at hes
  | cons d ds ih =>
    cases es with
    | nil => simp at hes
    | cons e es =>
      simp only [List.length_cons, add_left_inj] at hes
      simp only [doobProb, pathSum, List.length_cons]
      set s' := if e then s + d else s - d
      by_cases h0 : signAvg g ds s' = 0
      · rw [pathSum_zero_of_signAvg_zero g hg ds es hes s' h0, h0]; simp
      · rw [ih es hes s' h0]
        field_simp
        ring

/-- Paper: `sec:column-envelope` (tanh_column_envelope.tex): accepting a fresh
pairing with probability `m ν_2` and then following the quadratic Doob
transform gives each sign path probability `m δ^2 / 2^m`, i.e. density `m δ^2`
relative to uniform signs, for one fixed pairing. That a uniform pairing with
uniform signs selects a uniform half is not formalized. -/
theorem accepted_quadratic_path (ds : List ℝ) (es : List Bool) (hes : es.length = ds.length)
    (m : ℝ) (hν : signAvg (fun x => x ^ 2) ds 0 ≠ 0) :
    m * signAvg (fun x => x ^ 2) ds 0 * doobProb (fun x => x ^ 2) ds es 0 =
      m * pathSum ds es 0 ^ 2 / 2 ^ ds.length := by
  rw [doobProb_eq _ (fun x => sq_nonneg x) ds es hes 0 hν]
  field_simp

/-- Paper: `sec:column-envelope` (tanh_column_envelope.tex): the quartic tilt
accepted with probability `m^2 ν_4/3` gives density `m^2 δ^4/3`. -/
theorem accepted_quartic_path (ds : List ℝ) (es : List Bool) (hes : es.length = ds.length)
    (m : ℝ) (hν : signAvg (fun x => x ^ 4) ds 0 ≠ 0) :
    m ^ 2 * signAvg (fun x => x ^ 4) ds 0 / 3 * doobProb (fun x => x ^ 4) ds es 0 =
      m ^ 2 * pathSum ds es 0 ^ 4 / 3 / 2 ^ ds.length := by
  rw [doobProb_eq _ (fun x => by positivity) ds es hes 0 hν]
  field_simp

/-- All sign paths of length `n`. Auxiliary for `eq:column-pairing-moments`
(tanh_column_envelope.tex). -/
def allPaths : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allPaths n).map (true :: ·) ++ (allPaths n).map (false :: ·)

/-- Every listed path has the right length. Auxiliary for
`eq:column-pairing-moments` (tanh_column_envelope.tex). -/
theorem length_of_mem_allPaths (n : ℕ) (es : List Bool) (h : es ∈ allPaths n) :
    es.length = n := by
  induction n generalizing es with
  | zero => simp [allPaths] at h; simp [h]
  | succ n ih =>
    simp only [allPaths, List.mem_append, List.mem_map] at h
    rcases h with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ <;> simp [ih e he]

/-- Paper: `eq:column-pairing-moments` (tanh_column_envelope.tex): for a
nonnegative `g`, every Doob path probability is nonnegative. -/
theorem doobProb_nonneg (g : ℝ → ℝ) (hg : ∀ x, 0 ≤ g x) (ds : List ℝ) (es : List Bool)
    (s : ℝ) : 0 ≤ doobProb g ds es s := by
  induction ds generalizing es s with
  | nil => cases es <;> simp [doobProb]
  | cons d ds ih =>
    cases es with
    | nil => simp [doobProb]
    | cons e es =>
      simp only [doobProb]
      have h1 := signAvg_nonneg g hg ds (if e then s + d else s - d)
      have h2 := signAvg_nonneg g hg (d :: ds) s
      have h3 := ih es (if e then s + d else s - d)
      positivity

/-- Paper: `eq:column-pairing-moments` (tanh_column_envelope.tex): if
`signAvg g ds s ≠ 0`, the Doob path probabilities sum to one over all sign paths
(for nonnegative `g` they are nonnegative by `doobProb_nonneg`). -/
theorem doobProb_sum_eq_one (g : ℝ → ℝ) (ds : List ℝ) (s : ℝ)
    (h : signAvg g ds s ≠ 0) :
    ((allPaths ds.length).map (fun es => doobProb g ds es s)).sum = 1 := by
  induction ds generalizing s with
  | nil => simp [allPaths, doobProb]
  | cons d ds ih =>
    simp only [List.length_cons, allPaths, List.map_append, List.map_map, List.sum_append]
    have ep : (allPaths ds.length).map ((fun es => doobProb g (d :: ds) es s) ∘ (true :: ·)) =
        (allPaths ds.length).map (fun es => signAvg g ds (s + d) /
          (2 * signAvg g (d :: ds) s) * doobProb g ds es (s + d)) := by
      apply List.map_congr_left; intro es _; simp [doobProb]
    have em : (allPaths ds.length).map ((fun es => doobProb g (d :: ds) es s) ∘ (false :: ·)) =
        (allPaths ds.length).map (fun es => signAvg g ds (s - d) /
          (2 * signAvg g (d :: ds) s) * doobProb g ds es (s - d)) := by
      apply List.map_congr_left; intro es _; simp [doobProb]
    rw [ep, em, List.sum_map_mul_left, List.sum_map_mul_left]
    have hstep := doob_step_sum g d ds s h
    by_cases hp : signAvg g ds (s + d) = 0 <;> by_cases hm : signAvg g ds (s - d) = 0
    · exfalso; apply h; simp only [signAvg, hp, hm]; ring
    · rw [ih (s - d) hm, mul_one, hp, zero_div, zero_mul, zero_add]
      rw [hp, zero_div, zero_add] at hstep; exact hstep
    · rw [ih (s + d) hp, mul_one, hm, zero_div, zero_mul, add_zero]
      rw [hm, zero_div, add_zero] at hstep; exact hstep
    · rw [ih (s + d) hp, ih (s - d) hm, mul_one, mul_one]; exact hstep

/-! ## Halves of a population -/

/-- Sum of `(x - c)(y - d)` over a finite set. Auxiliary for `eq:column-antithetic-identity`
(tanh_column_envelope.tex). -/
theorem sum_centered {α : Type*} (s : Finset α) (x y : α → ℝ) (c d : ℝ) :
    ∑ i ∈ s, (x i - c) * (y i - d) =
      ∑ i ∈ s, x i * y i - d * ∑ i ∈ s, x i - c * ∑ i ∈ s, y i + s.card * c * d := by
  have e : ∀ i ∈ s, (x i - c) * (y i - d) = x i * y i - d * x i - c * y i + c * d := by
    intro i _; ring
  rw [sum_congr rfl e, sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum,
    ← mul_sum, sum_const, nsmul_eq_mul]
  ring

section Halves
variable {α : Type*} [DecidableEq α]

/-- Paper: `sec:column-envelope` (tanh_column_envelope.tex), proof of
`eq:column-antithetic-identity`: for a population `A ∪ B` of `2m`
observations split into halves of size `m`, with half means `z ± δ`,
`(m-1)(V_A + V_B) = (2m-1)V_{2m} - 2m δ δ^T`, entrywise for any two coordinates
`x, y`. Here `(m-1)V_A = ∑_A (x - z_A)(y - z_A)` and
`(2m-1)V_{2m} = ∑ (x - z)(y - z)`. -/
theorem covariance_decomposition (A B : Finset α) (hAB : Disjoint A B) (m : ℕ)
    (hA : A.card = m) (hB : B.card = m) (hm : 0 < m) (x y : α → ℝ) :
    let zx := (∑ i ∈ A ∪ B, x i) / (2 * m)
    let zy := (∑ i ∈ A ∪ B, y i) / (2 * m)
    let ax := (∑ i ∈ A, x i) / m
    let ay := (∑ i ∈ A, y i) / m
    let bx := (∑ i ∈ B, x i) / m
    let b_y := (∑ i ∈ B, y i) / m
    ∑ i ∈ A, (x i - ax) * (y i - ay) + ∑ i ∈ B, (x i - bx) * (y i - b_y) =
      ∑ i ∈ A ∪ B, (x i - zx) * (y i - zy) - 2 * m * ((ax - zx) * (ay - zy)) := by
  intro zx zy ax ay bx b_y
  have hcard : (A ∪ B).card = 2 * m := by rw [card_union_of_disjoint hAB, hA, hB]; ring
  simp only [zx, zy, ax, ay, bx, b_y]
  rw [sum_centered, sum_centered, sum_centered, hA, hB, hcard,
    sum_union hAB, sum_union hAB, sum_union hAB]
  have hm' : (m : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Paper: `sec:column-envelope` (tanh_column_envelope.tex), proof of
`eq:column-antithetic-identity`: a half and its complement have means
`z + δ` and `z - δ`. -/
theorem complement_mean (s A : Finset α) (hA : A ⊆ s) (m : ℕ) (hm : 0 < m) (x : α → ℝ) :
    (∑ i ∈ s \ A, x i) / m - (∑ i ∈ s, x i) / (2 * m) =
      -((∑ i ∈ A, x i) / m - (∑ i ∈ s, x i) / (2 * m)) := by
  have h := sum_sdiff hA (f := x)
  have hm' : (m : ℝ) ≠ 0 := by positivity
  field_simp
  linarith

/-- Paper: `sec:column-envelope` (tanh_column_envelope.tex), proof of
`eq:column-antithetic-identity`: complement symmetry gives, over the uniform
halves `A` of a population `s` of `2m` observations, `∑_A f(δ_A) = 0` for every
odd function `f`; in particular `E δ = 0` and `E δ^{⊗3} = 0`. -/
theorem half_odd_moment_zero (s : Finset α) (m : ℕ) (hs : s.card = 2 * m) (hm : 0 < m)
    (x : α → ℝ) (f : ℝ → ℝ) (hf : ∀ t, f (-t) = -f t) :
    ∑ A ∈ s.powersetCard m, f ((∑ i ∈ A, x i) / m - (∑ i ∈ s, x i) / (2 * m)) = 0 := by
  set P := s.powersetCard m
  set δ : Finset α → ℝ := fun A => (∑ i ∈ A, x i) / m - (∑ i ∈ s, x i) / (2 * m)
  have hmem : ∀ A ∈ P, s \ A ∈ P := by
    intro A hA
    rw [mem_powersetCard] at hA ⊢
    refine ⟨sdiff_subset, ?_⟩
    rw [card_sdiff_of_subset hA.1, hs, hA.2]; omega
  have hinv : ∀ A ∈ P, s \ (s \ A) = A := by
    intro A hA
    exact Finset.sdiff_sdiff_eq_self (mem_powersetCard.mp hA).1
  have hneg : ∀ A ∈ P, δ (s \ A) = -δ A := by
    intro A hA
    have hA' := mem_powersetCard.mp hA
    exact complement_mean s A hA'.1 m hm x
  have hswap : ∑ A ∈ P, f (δ A) = ∑ A ∈ P, f (δ (s \ A)) := by
    refine sum_nbij' (fun A => s \ A) (fun A => s \ A) hmem hmem hinv hinv ?_
    intro A hA
    rw [hinv A hA]
  have h2 : ∑ A ∈ P, f (δ A) = -∑ A ∈ P, f (δ A) := by
    rw [← sum_neg_distrib]
    conv_lhs => rw [hswap]
    exact sum_congr rfl (fun A hA => by rw [hneg A hA, hf])
  show ∑ A ∈ P, f (δ A) = 0
  linarith

end Halves

/-! ## The Pólya urn -/

/-- Probability of a word of urn draws (`true` a success) from an urn with
initial weights `a, b`, multiplying the predictive probabilities. Auxiliary for the Pólya urn of
`sec:column-envelope`
(tanh_column_envelope.tex). -/
noncomputable def urnProb : ℝ → ℝ → List Bool → ℝ
  | _, _, [] => 1
  | a, b, true :: w => a / (a + b) * urnProb (a + 1) b w
  | a, b, false :: w => b / (a + b) * urnProb a (b + 1) w

/-- `(x)_{n+1} = x (x+1)_n`. Auxiliary for the Pólya urn of `sec:column-envelope`
(tanh_column_envelope.tex). -/
theorem poch_succ (n : ℕ) (x : ℝ) :
    (ascPochhammer ℝ (n + 1)).eval x = x * (ascPochhammer ℝ n).eval (x + 1) := by
  rw [ascPochhammer_succ_left]
  simp [Polynomial.eval_comp]

/-- Paper: `sec:column-envelope` (tanh_column_envelope.tex): a specified urn
word with `s` successes and `f` failures has probability
`(a)_s (b)_f / (a+b)_{s+f}`, with rising factorials. -/
theorem urnProb_eq (w : List Bool) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    urnProb a b w = (ascPochhammer ℝ (w.count true)).eval a *
      (ascPochhammer ℝ (w.count false)).eval b /
        (ascPochhammer ℝ (w.count true + w.count false)).eval (a + b) := by
  induction w generalizing a b with
  | nil => simp [urnProb]
  | cons c w ih =>
    have hp : ∀ n (x : ℝ), 0 < x → 0 < (ascPochhammer ℝ n).eval x :=
      fun n x hx => ascPochhammer_pos n x hx
    cases c with
    | true =>
      have h1 : (true :: w).count true = w.count true + 1 := by simp
      have h2 : (true :: w).count false = w.count false := by simp
      rw [h1, h2, show w.count true + 1 + w.count false = (w.count true + w.count false) + 1 by
        ring, poch_succ, poch_succ, urnProb, ih (a + 1) b (by linarith) hb,
        show a + 1 + b = a + b + 1 by ring]
      have := hp (w.count true + w.count false) (a + b + 1) (by linarith)
      field_simp
    | false =>
      have h1 : (false :: w).count true = w.count true := by simp
      have h2 : (false :: w).count false = w.count false + 1 := by simp
      rw [h1, h2, show w.count true + (w.count false + 1) = (w.count true + w.count false) + 1 by
        ring, poch_succ, poch_succ, urnProb, ih a (b + 1) ha (by linarith),
        show a + (b + 1) = a + b + 1 by ring]
      have := hp (w.count true + w.count false) (a + b + 1) (by linarith)
      field_simp

/-- Paper: `sec:column-envelope` (tanh_column_envelope.tex): urn word
probabilities are nonnegative for positive initial weights. -/
theorem urnProb_nonneg (w : List Bool) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ urnProb a b w := by
  induction w generalizing a b with
  | nil => simp [urnProb]
  | cons c w ih =>
    cases c with
    | true =>
      have := ih (a + 1) b (by linarith) hb
      simp only [urnProb]; positivity
    | false =>
      have := ih a (b + 1) ha (by linarith)
      simp only [urnProb]; positivity

/-- Paper: `sec:column-envelope` (tanh_column_envelope.tex): the urn word
probabilities of each length `n` sum to one. -/
theorem urnProb_sum_eq_one (n : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ((allPaths n).map (fun w => urnProb a b w)).sum = 1 := by
  induction n generalizing a b with
  | zero => simp [allPaths, urnProb]
  | succ n ih =>
    simp only [allPaths, List.map_append, List.map_map, List.sum_append]
    have ep : (allPaths n).map ((fun w => urnProb a b w) ∘ (true :: ·)) =
        (allPaths n).map (fun w => a / (a + b) * urnProb (a + 1) b w) := by
      apply List.map_congr_left; intro w _; simp [urnProb]
    have em : (allPaths n).map ((fun w => urnProb a b w) ∘ (false :: ·)) =
        (allPaths n).map (fun w => b / (a + b) * urnProb a (b + 1) w) := by
      apply List.map_congr_left; intro w _; simp [urnProb]
    rw [ep, em, List.sum_map_mul_left, List.sum_map_mul_left, ih (a + 1) b (by linarith) hb,
      ih a (b + 1) ha (by linarith)]
    field_simp

end ExactSampling.ColumnEnvelopeTilting
