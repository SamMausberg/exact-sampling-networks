import Mathlib

/-!
# A rank-one cache with an implicit query: the corrected Bernstein factory

This module formalizes quantitative steps of `attention_implicit.tex`
(`lem:correctedbernstein`, `lem:scalarsoftmaxderivatives`, `thm:implicitrankone`) and the
constants used for the rank-one query law in `attention_query_law.tex`
(`thm:rankone-worstlaw`).

Formalized here:
* `lem:scalarsoftmaxderivatives` in full: for `u(p) = ∑_j v_j e^{a_j p + c_j} / ∑_j e^{a_j p + c_j}`
  with `|v_j| ≤ 1` and `|a_j| ≤ Λ`, every iterated derivative obeys `|u^{(k)}| ≤ b_k Λ^k`,
  where `b_k = 1 + ∑_{i<k} binom(k,i) b_i`; in particular `b = 1, 2, 6, 26, 150` for
  `k ≤ 4`, so `f = u/2` has derivative bounds `Λ, 3Λ², 13Λ³, 75Λ⁴`. The bounds hold for every
  real `p`, every `T ≥ 1`, and arbitrary offsets.
* `lem:correctedbernstein`: the second derivative of `h(p) = p(1-p) f''(p)` and the bound
  `‖h''‖ ≤ 2M₂ + 2M₃ + M₄/4`; the leading-term cancellation; the moments of the uniform-half
  (hypergeometric) law: it is a probability law, `E Δ = E Δ³ = 0` by complement symmetry, and
  `E Δ² = p(1-p)/(2m-1)` by the two-indicator count; the coefficient bound `|d_{m,K}| ≤ A/(4m²)`,
  for a general finite law with these moments and for the actual uniform-half law; the masses
  `∑ c_ℓ = A/(3m₀²) ≤ 1/12`, the base margin, the fair completion, the conditional level law
  `(3/4)4^{-ℓ}`, the expected source count `(7/8)m₀ + A/m₀`, the convergence
  `B_{m_ℓ} g_{m_ℓ}(p) → f(p)` (from Mathlib's uniform Bernstein approximation), exactness of the
  mixture as a convergent telescoping series, and legality of the per-`K` coins.
* `thm:implicitrankone`: the explicit constants `A ≤ 91 max{Λ², Λ⁴}`, `m₀ < 40 max{1, Λ²}`,
  `A/m₀ ≤ m₀/4`, and source count below `45 max{1, Λ²}`; the hypergeometric weight ratio and
  its mode.
* The reparametrization of a rank-one score by the source bias `p = (1+z)/2`, and the
  constants `720β²` and `11520β²` of `thm:rankone-worstlaw`.

Stand-in hypotheses (not formalized): in `corrected_coefficient_hypergeometric`, the pointwise
Taylor bounds for `f` (fourth order) and `h` (second order), which follow from Taylor's theorem
with the derivative bounds `M₄` and `H₂`, the bound `H₂ ≤ 2M₂ + 2M₃ + M₄/4` (whose pointwise form
is `h_second_derivative_bound`), and the fourth-moment bound `E Δ⁴ ≤ m^{-2}` (proved in the paper
by a Hoeffding argument) are explicit hypotheses; in `bernstein_mixture_exact` the per-level
bound `|B_{2m}g_{2m}(p) - B_m g_m(p)| ≤ A/(4m²)` is a hypothesis. Not formalized: degree
elevation, i.e. the identity expressing `B_{2m}g_{2m} - B_m g_m` as the binomial average of the
coefficients `d_{m,K}` (conditioning a binomial sample on its total), which would turn the
coefficient bound into that per-level bound; certified coefficient tables; and all bit-cost
statements.
-/

open Finset Filter
open scoped BigOperators Topology

namespace ExactSampling.ImplicitRankOne

/-! ## Uniform derivative bounds for the scalar softmax mean (`lem:scalarsoftmaxderivatives`) -/

section Derivatives

/-- The constants `b_k = 1 + ∑_{i<k} binom(k,i) b_i` of the quotient recurrence.
Paper: `lem:scalarsoftmaxderivatives` (attention_implicit.tex). -/
def derivConst (k : ℕ) : ℕ := 1 + ∑ i : Fin k, k.choose i * derivConst i
decreasing_by exact i.isLt

/-- `b_0 = 1`. Paper: `lem:scalarsoftmaxderivatives` (attention_implicit.tex). -/
lemma derivConst_zero : derivConst 0 = 1 := by rw [derivConst]; simp

/-- `b_1 = 2`. Paper: `lem:scalarsoftmaxderivatives` (attention_implicit.tex). -/
lemma derivConst_one : derivConst 1 = 2 := by rw [derivConst]; simp [derivConst_zero]

/-- `b_2 = 6`. Paper: `lem:scalarsoftmaxderivatives` (attention_implicit.tex). -/
lemma derivConst_two : derivConst 2 = 6 := by
  rw [derivConst]; simp [Fin.sum_univ_succ, derivConst_zero, derivConst_one]

/-- `b_3 = 26`. Paper: `lem:scalarsoftmaxderivatives` (attention_implicit.tex). -/
lemma derivConst_three : derivConst 3 = 26 := by
  rw [derivConst]; simp [Fin.sum_univ_succ, derivConst_zero, derivConst_one, derivConst_two]

/-- `b_4 = 150`. Paper: `lem:scalarsoftmaxderivatives` (attention_implicit.tex). -/
lemma derivConst_four : derivConst 4 = 150 := by
  rw [derivConst]
  simp [Fin.sum_univ_succ, derivConst_zero, derivConst_one, derivConst_two, derivConst_three]
  norm_num [Nat.choose]

/-- The recurrence used for all softmax derivatives up to order four.
Paper: `lem:scalarsoftmaxderivatives` (attention_implicit.tex). -/
theorem quotient_constants :
    (1 + 1 = 2) ∧ (1 + 2 * 2 + 1 = 6) ∧ (1 + 3 * 6 + 3 * 2 + 1 = 26) ∧
      (1 + 4 * 26 + 6 * 6 + 4 * 2 + 1 = 150) := by
  norm_num

/-- Abstract quotient recurrence: if `N_k = ∑_{i ≤ k} binom(k,i) U_i Z_{k-i}` (Leibniz rule for
`N = uZ`), `Z_0 > 0`, `|N_k| ≤ Λ^k Z_0`, and `|Z_k| ≤ Λ^k Z_0`, then `|U_k| ≤ b_k Λ^k`.
Paper: `lem:scalarsoftmaxderivatives` (attention_implicit.tex), "Differentiating `uZ = N`
inductively". -/
theorem quotient_derivative_bound (U N Zd : ℕ → ℝ) (Λ : ℝ) (hΛ : 0 ≤ Λ) (hZ : 0 < Zd 0)
    (hleib : ∀ k, N k = ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * U i * Zd (k - i))
    (hN : ∀ k, |N k| ≤ Λ ^ k * Zd 0) (hZb : ∀ k, |Zd k| ≤ Λ ^ k * Zd 0) :
    ∀ k, |U k| ≤ derivConst k * Λ ^ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hsplit := hleib k
    rw [Finset.sum_range_succ, Nat.choose_self, Nat.sub_self] at hsplit
    have hUk : U k * Zd 0 = N k - ∑ i ∈ Finset.range k, (k.choose i : ℝ) * U i * Zd (k - i) := by
      rw [hsplit]; push_cast; ring
    have hsum : |∑ i ∈ Finset.range k, (k.choose i : ℝ) * U i * Zd (k - i)| ≤
        (∑ i ∈ Finset.range k, (k.choose i : ℝ) * derivConst i) * (Λ ^ k * Zd 0) := by
      rw [Finset.sum_mul]
      calc |∑ i ∈ Finset.range k, (k.choose i : ℝ) * U i * Zd (k - i)|
          ≤ ∑ i ∈ Finset.range k, |(k.choose i : ℝ) * U i * Zd (k - i)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range k, (k.choose i : ℝ) * derivConst i * (Λ ^ k * Zd 0) := by
            apply Finset.sum_le_sum
            intro i hi
            have hik : i < k := Finset.mem_range.mp hi
            rw [abs_mul, abs_mul, Nat.abs_cast]
            have h1 := ih i hik
            have h2 := hZb (k - i)
            have hpow : Λ ^ i * Λ ^ (k - i) = Λ ^ k := by
              rw [← pow_add]; congr 1; omega
            calc (k.choose i : ℝ) * |U i| * |Zd (k - i)|
                ≤ (k.choose i : ℝ) * (derivConst i * Λ ^ i) * (Λ ^ (k - i) * Zd 0) := by
                  gcongr
              _ = (k.choose i : ℝ) * derivConst i * (Λ ^ i * Λ ^ (k - i) * Zd 0) := by ring
              _ = (k.choose i : ℝ) * derivConst i * (Λ ^ k * Zd 0) := by rw [hpow]
    have hdc : (derivConst k : ℝ) = 1 + ∑ i ∈ Finset.range k, (k.choose i : ℝ) * derivConst i := by
      rw [derivConst]; push_cast
      rw [Fin.sum_univ_eq_sum_range (fun i => (k.choose i : ℝ) * (derivConst i : ℝ)) k]
    have habs : |U k| * Zd 0 ≤ derivConst k * Λ ^ k * Zd 0 := by
      have : |U k * Zd 0| ≤
          |N k| + |∑ i ∈ Finset.range k, (k.choose i : ℝ) * U i * Zd (k - i)| := by
        rw [hUk]; exact abs_sub _ _
      rw [abs_mul, abs_of_pos hZ] at this
      rw [hdc]
      nlinarith [hN k]
    exact le_of_mul_le_mul_right (by linarith) hZ

/-- Auxiliary: `d^k/dp^k e^{ap+c} = a^k e^{ap+c}`. Supports the proof of
`lem:scalarsoftmaxderivatives` (attention_implicit.tex). -/
lemma iteratedDeriv_exp_affine (a c : ℝ) (k : ℕ) (p : ℝ) :
    iteratedDeriv k (fun s => Real.exp (a * s + c)) p = a ^ k * Real.exp (a * p + c) := by
  have : (fun s => Real.exp (a * s + c)) = fun s => Real.exp c * Real.exp (a * s) := by
    funext s; rw [← Real.exp_add]; ring_nf
  rw [this, iteratedDeriv_const_mul_field, iteratedDeriv_exp_const_mul]
  simp only; rw [← mul_assoc, mul_comm (Real.exp c), mul_assoc, ← Real.exp_add]; ring_nf

/-- Auxiliary: the `k`-th derivative of `N(p) = ∑_j v_j e^{a_j p + c_j}`. Supports the proof of
`lem:scalarsoftmaxderivatives` (attention_implicit.tex). -/
lemma iteratedDeriv_weighted_exp_sum {T : ℕ} (v a c : Fin T → ℝ) (k : ℕ) (p : ℝ) :
    iteratedDeriv k (fun s => ∑ j, v j * Real.exp (a j * s + c j)) p =
      ∑ j, v j * a j ^ k * Real.exp (a j * p + c j) := by
  rw [iteratedDeriv_fun_sum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_exp_affine]; ring
  · intro j _
    exact (contDiff_const.mul ((contDiff_const.mul contDiff_id).add contDiff_const).exp).contDiffAt

/-- Auxiliary: `|N^{(k)}| ≤ Λ^k Z` and `|Z^{(k)}| ≤ Λ^k Z`. Supports the proof of
`lem:scalarsoftmaxderivatives` (attention_implicit.tex). -/
lemma weighted_exp_bound {T : ℕ} (v a c : Fin T → ℝ) (Λ : ℝ) (hv : ∀ j, |v j| ≤ 1)
    (ha : ∀ j, |a j| ≤ Λ) (k : ℕ) (p : ℝ) :
    |∑ j, v j * a j ^ k * Real.exp (a j * p + c j)| ≤
      Λ ^ k * ∑ j, Real.exp (a j * p + c j) := by
  rw [Finset.mul_sum]
  calc |∑ j, v j * a j ^ k * Real.exp (a j * p + c j)|
      ≤ ∑ j, |v j * a j ^ k * Real.exp (a j * p + c j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, Λ ^ k * Real.exp (a j * p + c j) := by
        apply Finset.sum_le_sum; intro j _
        rw [abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
        have h1 : |a j| ^ k ≤ Λ ^ k := pow_le_pow_left₀ (abs_nonneg _) (ha j) k
        calc |v j| * |a j| ^ k * Real.exp (a j * p + c j)
            ≤ 1 * Λ ^ k * Real.exp (a j * p + c j) := by gcongr; exact hv j
          _ = Λ ^ k * Real.exp (a j * p + c j) := by ring

/-- Uniform scalar softmax derivatives: for `|v_j| ≤ 1`, `|a_j| ≤ Λ`, and arbitrary offsets,
`|u^{(k)}(p)| ≤ b_k Λ^k` for every `k` and every real `p`, independently of `T`.
Paper: `lem:scalarsoftmaxderivatives` (attention_implicit.tex). -/
theorem scalar_softmax_derivatives {T : ℕ} (hT : 0 < T) (v a c : Fin T → ℝ) (Λ : ℝ)
    (hΛ : 0 ≤ Λ) (hv : ∀ j, |v j| ≤ 1) (ha : ∀ j, |a j| ≤ Λ) (k : ℕ) (p : ℝ) :
    |iteratedDeriv k (fun s => (∑ j, v j * Real.exp (a j * s + c j)) /
        ∑ j, Real.exp (a j * s + c j)) p| ≤ derivConst k * Λ ^ k := by
  have : Nonempty (Fin T) := ⟨⟨0, hT⟩⟩
  set N : ℝ → ℝ := fun s => ∑ j, v j * Real.exp (a j * s + c j) with hNdef
  set Z : ℝ → ℝ := fun s => ∑ j, Real.exp (a j * s + c j) with hZdef
  have hZpos : ∀ s, 0 < Z s := fun s =>
    Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  have hNsmooth : ContDiff ℝ ⊤ N := by
    rw [hNdef]
    exact ContDiff.sum fun j _ =>
      contDiff_const.mul ((contDiff_const.mul contDiff_id).add contDiff_const).exp
  have hZsmooth : ContDiff ℝ ⊤ Z := by
    rw [hZdef]
    exact ContDiff.sum fun j _ => ((contDiff_const.mul contDiff_id).add contDiff_const).exp
  set u : ℝ → ℝ := fun s => N s / Z s with hudef
  have husmooth : ContDiff ℝ ⊤ u := hNsmooth.div hZsmooth fun s => (hZpos s).ne'
  have hprod : u * Z = N := by
    funext s; simp only [Pi.mul_apply, hudef]; field_simp [(hZpos s).ne']
  have hZone : Z = fun s => ∑ j, (1 : ℝ) * Real.exp (a j * s + c j) := by
    funext s; simp [hZdef]
  have hNk : ∀ k, iteratedDeriv k N p = ∑ j, v j * a j ^ k * Real.exp (a j * p + c j) :=
    fun k => iteratedDeriv_weighted_exp_sum v a c k p
  have hZk : ∀ k, iteratedDeriv k Z p = ∑ j, (1 : ℝ) * a j ^ k * Real.exp (a j * p + c j) := by
    intro k; rw [hZone]; exact iteratedDeriv_weighted_exp_sum (fun _ => 1) a c k p
  have hZ0 : iteratedDeriv 0 Z p = Z p := by simp
  apply quotient_derivative_bound (fun i => iteratedDeriv i u p) (fun i => iteratedDeriv i N p)
    (fun i => iteratedDeriv i Z p) Λ hΛ (by rw [hZ0]; exact hZpos p)
  · intro k
    rw [← hprod, iteratedDeriv_mul (husmooth.contDiffAt.of_le (by exact_mod_cast le_top))
      (hZsmooth.contDiffAt.of_le (by exact_mod_cast le_top))]
  · intro k
    rw [hNk, hZ0]
    exact weighted_exp_bound v a c Λ hv ha k p
  · intro k
    rw [hZk, hZ0]
    have := weighted_exp_bound (fun _ => (1 : ℝ)) a c Λ (fun _ => by simp) ha k p
    simpa [hZdef] using this

/-- The derivative bounds of `f = u/2` used in the factory: `|f'| ≤ Λ`, `|f''| ≤ 3Λ²`,
`|f'''| ≤ 13Λ³`, `|f''''| ≤ 75Λ⁴`, and `|f| ≤ 1/2`.
Paper: `lem:scalarsoftmaxderivatives` (attention_implicit.tex). -/
theorem half_softmax_derivatives {T : ℕ} (hT : 0 < T) (v a c : Fin T → ℝ) (Λ : ℝ)
    (hΛ : 0 ≤ Λ) (hv : ∀ j, |v j| ≤ 1) (ha : ∀ j, |a j| ≤ Λ) (p : ℝ) :
    let u : ℝ → ℝ := fun s => (∑ j, v j * Real.exp (a j * s + c j)) /
        ∑ j, Real.exp (a j * s + c j)
    |u p / 2| ≤ 1 / 2 ∧ |iteratedDeriv 1 u p / 2| ≤ Λ ∧ |iteratedDeriv 2 u p / 2| ≤ 3 * Λ ^ 2 ∧
      |iteratedDeriv 3 u p / 2| ≤ 13 * Λ ^ 3 ∧ |iteratedDeriv 4 u p / 2| ≤ 75 * Λ ^ 4 := by
  intro u
  have hb := scalar_softmax_derivatives hT v a c Λ hΛ hv ha
  have h0 := hb 0 p
  have h1 := hb 1 p
  have h2 := hb 2 p
  have h3 := hb 3 p
  have h4 := hb 4 p
  rw [derivConst_zero] at h0
  rw [derivConst_one] at h1
  rw [derivConst_two] at h2
  rw [derivConst_three] at h3
  rw [derivConst_four] at h4
  simp only [iteratedDeriv_zero, pow_zero, Nat.cast_one, mul_one] at h0
  push_cast at h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [abs_div, abs_two] <;> linarith

end Derivatives

/-! ## The corrected Bernstein coefficient (`lem:correctedbernstein`) -/

section Coefficient

/-- Second derivative of `h(p) = p(1-p) f''(p)`: if `f₂' = f₃` and `f₃' = f₄`, then
`h'' = -2 f₂ + 2(1-2p) f₃ + p(1-p) f₄`.
Paper: `lem:correctedbernstein` (attention_implicit.tex), bound on `H₂ = ‖h''‖`. -/
theorem h_second_derivative (f2 f3 f4 : ℝ → ℝ) (hf2 : ∀ x, HasDerivAt f2 (f3 x) x)
    (hf3 : ∀ x, HasDerivAt f3 (f4 x) x) (p : ℝ) :
    HasDerivAt (fun x => (1 - 2 * x) * f2 x + x * (1 - x) * f3 x)
        (-2 * f2 p + 2 * (1 - 2 * p) * f3 p + p * (1 - p) * f4 p) p ∧
      ∀ x, HasDerivAt (fun x => x * (1 - x) * f2 x)
        ((1 - 2 * x) * f2 x + x * (1 - x) * f3 x) x := by
  have hq : ∀ x : ℝ, HasDerivAt (fun x : ℝ => x * (1 - x)) (1 - 2 * x) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
    have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
      simpa using (hasDerivAt_id' x).const_sub 1
    convert h1.mul h2 using 1; ring
  have hl : ∀ x : ℝ, HasDerivAt (fun x : ℝ => 1 - 2 * x) (-2) x := by
    intro x
    have h1 := ((hasDerivAt_id' x).const_mul 2).const_sub 1
    convert h1 using 1; ring
  refine ⟨?_, ?_⟩
  · have h := ((hl p).mul (hf2 p)).add ((hq p).mul (hf3 p))
    convert h using 1
    ring
  · intro x
    exact (hq x).mul (hf2 x)

/-- `‖h''‖ ≤ 2M₂ + 2M₃ + M₄/4` on `[0,1]`.
Paper: `lem:correctedbernstein` (attention_implicit.tex). -/
theorem h_second_derivative_bound (p F2 F3 F4 M2 M3 M4 : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (h2 : |F2| ≤ M2) (h3 : |F3| ≤ M3) (h4 : |F4| ≤ M4) :
    |-2 * F2 + 2 * (1 - 2 * p) * F3 + p * (1 - p) * F4| ≤ 2 * M2 + 2 * M3 + M4 / 4 := by
  have hq : |p * (1 - p)| ≤ 1 / 4 := by
    rw [abs_of_nonneg (mul_nonneg hp0 (by linarith))]; nlinarith [sq_nonneg (p - 1 / 2)]
  have hl : |1 - 2 * p| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  calc |-2 * F2 + 2 * (1 - 2 * p) * F3 + p * (1 - p) * F4|
      ≤ |-2 * F2| + |2 * (1 - 2 * p) * F3| + |p * (1 - p) * F4| := abs_add_three _ _ _
    _ = 2 * |F2| + 2 * (|1 - 2 * p| * |F3|) + |p * (1 - p)| * |F4| := by
        simp only [abs_mul, abs_neg, abs_two]; ring
    _ ≤ 2 * M2 + 2 * (1 * M3) + 1 / 4 * M4 := by
        gcongr
    _ = 2 * M2 + 2 * M3 + M4 / 4 := by ring

/-- The cancellation responsible for the summable `m^{-2}` correction:
`a d/(4m) - d (a/(2m-1))/2 = -a d/(4m(2m-1))`.
Paper: `lem:correctedbernstein` (attention_implicit.tex). -/
theorem leading_bias_cancellation {m a d : ℝ} (hm : m ≠ 0) (hden : 2 * m - 1 ≠ 0) :
    a * d / (4 * m) - d * (a / (2 * m - 1)) / 2 = -(a * d) / (4 * m * (2 * m - 1)) := by
  generalize hk : 2 * m - 1 = k at hden ⊢
  field_simp
  rw [← hk]
  ring

/-- The displayed remainder constant is at most `A/4`:
`(M₂ + H₂)/16 + M₄/24 ≤ (M₂ + M₃ + M₄)/4` when `H₂ ≤ 2M₂ + 2M₃ + M₄/4`.
Paper: `lem:correctedbernstein` (attention_implicit.tex). -/
theorem corrected_coefficient_constant {m2 m3 m4 h2 : ℝ} (hm2 : 0 ≤ m2) (hm3 : 0 ≤ m3)
    (hm4 : 0 ≤ m4) (hh2 : h2 ≤ 2 * m2 + 2 * m3 + m4 / 4) :
    (m2 + h2) / 16 + m4 / 24 ≤ (m2 + m3 + m4) / 4 := by
  linarith

/-- The corrected coefficient bound `|d_{m,K}| ≤ A/(4m²)`, eq. `eq:correctedcoefficientbound`.
Here `Y = J/m` has the finite law `(w_i, y_i)`; `Δ = Y - p` has `E Δ = E Δ³ = 0`,
`E Δ² = ν = p(1-p)/(2m-1)`, and `E Δ⁴ ≤ m^{-2}`; `f` and `h = p(1-p)f''` satisfy pointwise
Taylor bounds of orders four and two with constants `M₄` and `H₂`. These moment and Taylor
facts are stand-in hypotheses; the conclusion is the paper's algebraic assembly with
`g_m = f - h/(2m)`. Paper: `lem:correctedbernstein`, display `eq:correctedcoefficientbound`
(attention_implicit.tex). -/
theorem corrected_coefficient_bound {ι : Type*} (s : Finset ι) (w y : ι → ℝ) (m : ℕ) (hm : 1 ≤ m)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f f2 h : ℝ → ℝ) (F1 F3 H1 M2 M3 M4 H2 : ℝ)
    (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3) (hM4 : 0 ≤ M4) (hH2 : 0 ≤ H2)
    (hf2 : |f2 p| ≤ M2) (hH2b : H2 ≤ 2 * M2 + 2 * M3 + M4 / 4)
    (hh : ∀ x, h x = x * (1 - x) * f2 x)
    (hw0 : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1)
    (hmean : ∑ i ∈ s, w i * (y i - p) = 0) (hthird : ∑ i ∈ s, w i * (y i - p) ^ 3 = 0)
    (hvar : ∑ i ∈ s, w i * (y i - p) ^ 2 = p * (1 - p) / (2 * m - 1))
    (hfourth : ∑ i ∈ s, w i * (y i - p) ^ 4 ≤ 1 / (m : ℝ) ^ 2)
    (htf : ∀ i ∈ s, |f (y i) - (f p + F1 * (y i - p) + f2 p / 2 * (y i - p) ^ 2 +
        F3 / 6 * (y i - p) ^ 3)| ≤ M4 / 24 * (y i - p) ^ 4)
    (hth : ∀ i ∈ s, |h (y i) - (h p + H1 * (y i - p))| ≤ H2 / 2 * (y i - p) ^ 2) :
    |(f p - h p / (2 * (2 * m : ℕ))) - ∑ i ∈ s, w i * (f (y i) - h (y i) / (2 * m))| ≤
      (M2 + M3 + M4) / (4 * (m : ℝ) ^ 2) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  set ν := p * (1 - p) / (2 * m - 1) with hνdef
  have hpq : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
  have hpq4 : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have h2m1 : (m : ℝ) ≤ 2 * m - 1 := by linarith
  have h2m1pos : (0 : ℝ) < 2 * m - 1 := by linarith
  have hν0 : 0 ≤ ν := div_nonneg hpq h2m1pos.le
  have hν : ν ≤ 1 / (4 * m) := by
    rw [hνdef, div_le_div_iff₀ h2m1pos (by positivity)]
    nlinarith
  -- remainders as finite expectations
  set Rf := ∑ i ∈ s, w i * f (y i) - (f p + f2 p / 2 * ν) with hRf
  set Rh := ∑ i ∈ s, w i * h (y i) - h p with hRh
  have hRfb : |Rf| ≤ M4 / (24 * (m : ℝ) ^ 2) := by
    have hexp : Rf = ∑ i ∈ s, w i * (f (y i) - (f p + F1 * (y i - p) + f2 p / 2 * (y i - p) ^ 2 +
        F3 / 6 * (y i - p) ^ 3)) := by
      rw [hRf]
      have : ∑ i ∈ s, w i * (f (y i) - (f p + F1 * (y i - p) + f2 p / 2 * (y i - p) ^ 2 +
          F3 / 6 * (y i - p) ^ 3)) = ∑ i ∈ s, w i * f (y i) - (f p * ∑ i ∈ s, w i +
            F1 * ∑ i ∈ s, w i * (y i - p) + f2 p / 2 * ∑ i ∈ s, w i * (y i - p) ^ 2 +
            F3 / 6 * ∑ i ∈ s, w i * (y i - p) ^ 3) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_; ring
      rw [this, hw1, hmean, hvar, hthird]; ring
    rw [hexp]
    calc |∑ i ∈ s, w i * (f (y i) - (f p + F1 * (y i - p) + f2 p / 2 * (y i - p) ^ 2 +
          F3 / 6 * (y i - p) ^ 3))|
        ≤ ∑ i ∈ s, |w i * (f (y i) - (f p + F1 * (y i - p) + f2 p / 2 * (y i - p) ^ 2 +
          F3 / 6 * (y i - p) ^ 3))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ s, w i * (M4 / 24 * (y i - p) ^ 4) := by
          apply Finset.sum_le_sum; intro i hi
          rw [abs_mul, abs_of_nonneg (hw0 i hi)]
          exact mul_le_mul_of_nonneg_left (htf i hi) (hw0 i hi)
      _ = M4 / 24 * ∑ i ∈ s, w i * (y i - p) ^ 4 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
      _ ≤ M4 / 24 * (1 / (m : ℝ) ^ 2) := by gcongr
      _ = M4 / (24 * (m : ℝ) ^ 2) := by field_simp
  have hRhb : |Rh| ≤ H2 / 2 * ν := by
    have hexp : Rh = ∑ i ∈ s, w i * (h (y i) - (h p + H1 * (y i - p))) := by
      rw [hRh]
      have : ∑ i ∈ s, w i * (h (y i) - (h p + H1 * (y i - p))) =
          ∑ i ∈ s, w i * h (y i) - (h p * ∑ i ∈ s, w i + H1 * ∑ i ∈ s, w i * (y i - p)) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_; ring
      rw [this, hw1, hmean]; ring
    rw [hexp]
    calc |∑ i ∈ s, w i * (h (y i) - (h p + H1 * (y i - p)))|
        ≤ ∑ i ∈ s, |w i * (h (y i) - (h p + H1 * (y i - p)))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ s, w i * (H2 / 2 * (y i - p) ^ 2) := by
          apply Finset.sum_le_sum; intro i hi
          rw [abs_mul, abs_of_nonneg (hw0 i hi)]
          exact mul_le_mul_of_nonneg_left (hth i hi) (hw0 i hi)
      _ = H2 / 2 * ν := by
          rw [← hvar, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  -- the coefficient identity
  have hEg : ∑ i ∈ s, w i * (f (y i) - h (y i) / (2 * m)) =
      ∑ i ∈ s, w i * f (y i) - (∑ i ∈ s, w i * h (y i)) / (2 * m) := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_; ring
  have hid : (f p - h p / (2 * (2 * m : ℕ))) - ∑ i ∈ s, w i * (f (y i) - h (y i) / (2 * m)) =
      -(p * (1 - p) * f2 p) / (4 * m * (2 * m - 1)) - Rf + Rh / (2 * m) := by
    rw [hEg, hRf, hRh, hh p, hνdef]
    push_cast
    field_simp
    ring
  rw [hid]
  have hlead : |-(p * (1 - p) * f2 p) / (4 * m * (2 * m - 1))| ≤ M2 / (16 * (m : ℝ) ^ 2) := by
    have hpos4 : (0 : ℝ) < 4 * m * (2 * m - 1) := mul_pos (by positivity) h2m1pos
    rw [abs_div, abs_neg, abs_mul, abs_of_nonneg hpq, abs_of_pos hpos4,
      div_le_div_iff₀ hpos4 (by positivity)]
    have : p * (1 - p) * |f2 p| ≤ 1 / 4 * M2 := mul_le_mul hpq4 hf2 (abs_nonneg _) (by norm_num)
    have hden : 4 * (m : ℝ) ^ 2 ≤ 4 * m * (2 * m - 1) := by nlinarith
    nlinarith
  have hRh2 : |Rh / (2 * m)| ≤ H2 / (16 * (m : ℝ) ^ 2) := by
    have hpos2 : (0 : ℝ) < 2 * m := by linarith
    rw [abs_div, abs_of_pos hpos2, div_le_div_iff₀ hpos2 (by positivity)]
    have h1 : |Rh| ≤ H2 / 2 * (1 / (4 * m)) :=
      le_trans hRhb (mul_le_mul_of_nonneg_left hν (by positivity))
    have h2 : H2 / 2 * (1 / (4 * m)) * (16 * (m : ℝ) ^ 2) = H2 * (2 * m) := by
      field_simp; ring
    nlinarith
  calc |-(p * (1 - p) * f2 p) / (4 * m * (2 * m - 1)) - Rf + Rh / (2 * m)|
      ≤ |-(p * (1 - p) * f2 p) / (4 * m * (2 * m - 1))| + |Rf| + |Rh / (2 * m)| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ M2 / (16 * (m : ℝ) ^ 2) + M4 / (24 * (m : ℝ) ^ 2) + H2 / (16 * (m : ℝ) ^ 2) := by
        linarith
    _ = ((M2 + H2) / 16 + M4 / 24) / (m : ℝ) ^ 2 := by field_simp; ring
    _ ≤ ((M2 + M3 + M4) / 4) / (m : ℝ) ^ 2 := by
        gcongr; exact corrected_coefficient_constant hM2 hM3 hM4 hH2b
    _ = (M2 + M3 + M4) / (4 * (m : ℝ) ^ 2) := by field_simp

end Coefficient

/-! ## Degree elevation as a hypergeometric average (`lem:correctedbernstein`) -/

section Hypergeometric

variable (m : ℕ)

/-- The uniformly selected halves: the `m`-element subsets of a population of `2m` bits.
Paper: `lem:correctedbernstein` (attention_implicit.tex). -/
def halves : Finset (Finset (Fin (2 * m))) := (Finset.univ : Finset (Fin (2 * m))).powersetCard m

/-- Auxiliary: membership in `halves`. Supports `lem:correctedbernstein`
(attention_implicit.tex). -/
lemma mem_halves {S : Finset (Fin (2 * m))} : S ∈ halves m ↔ S.card = m := by
  simp [halves, Finset.mem_powersetCard]

/-- Auxiliary: there are `binom(2m, m)` halves. Supports `lem:correctedbernstein`
(attention_implicit.tex). -/
lemma halves_card : (halves m).card = (2 * m).choose m := by
  simp [halves, Finset.card_powersetCard]

/-- Auxiliary: the complement of a half is a half. Supports the symmetry argument of
`lem:correctedbernstein` (attention_implicit.tex). -/
lemma compl_mem_halves {S : Finset (Fin (2 * m))} (hS : S ∈ halves m) :
    Finset.univ \ S ∈ halves m := by
  rw [mem_halves] at *
  rw [Finset.card_univ_sdiff, Fintype.card_fin, hS]; omega

/-- Auxiliary: the complementary half contains the remaining successes. Supports
`lem:correctedbernstein` (attention_implicit.tex). -/
lemma inter_compl_card (A S : Finset (Fin (2 * m))) :
    (((Finset.univ \ S) ∩ A).card : ℝ) = A.card - (S ∩ A).card := by
  have h := Finset.card_sdiff_add_card_inter A S
  have e : (Finset.univ \ S) ∩ A = A \ S := by ext x; simp [and_comm]
  rw [e, Finset.inter_comm]
  have : ((A \ S).card : ℝ) + (A ∩ S).card = A.card := by exact_mod_cast h
  linarith

/-- Auxiliary: complementation permutes the halves. Supports `lem:correctedbernstein`
(attention_implicit.tex). -/
lemma sum_halves_compl (f : Finset (Fin (2 * m)) → ℝ) :
    ∑ S ∈ halves m, f S = ∑ S ∈ halves m, f (Finset.univ \ S) := by
  apply Finset.sum_nbij' (fun S => Finset.univ \ S) (fun S => Finset.univ \ S)
  · intro S hS; exact compl_mem_halves m hS
  · intro S hS; exact compl_mem_halves m hS
  · intro S _; simp
  · intro S _; simp
  · intro S _; simp

/-- Auxiliary: the number of halves containing a given element is `binom(2m-1, m-1)`.
Supports `lem:correctedbernstein` (attention_implicit.tex). -/
lemma count_one (hm : 1 ≤ m) (a : Fin (2 * m)) :
    ((halves m).filter (fun S => a ∈ S)).card = (2 * m - 1).choose (m - 1) := by
  have := Finset.card_filter_powersetCard_subset {a} Finset.univ m (by simp) (by simp; omega)
  simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin,
    Finset.singleton_subset_iff] at this
  simpa [halves] using this

/-- Auxiliary: the number of halves containing two given elements, times `2m(2m-1)`, is
`m(m-1) binom(2m,m)`. Supports `lem:correctedbernstein` (attention_implicit.tex). -/
lemma count_two (hm : 1 ≤ m) (a b : Fin (2 * m)) (hab : a ≠ b) :
    (((halves m).filter (fun S => a ∈ S ∧ b ∈ S)).card : ℝ) * (2 * m * (2 * m - 1)) =
      (2 * m).choose m * (m * (m - 1)) := by
  rcases Nat.lt_or_ge m 2 with h1 | h2
  · have hm1 : m = 1 := by omega
    have hempty : (halves m).filter (fun S => a ∈ S ∧ b ∈ S) = ∅ := by
      apply Finset.filter_false_of_mem
      intro S hS ⟨ha, hb⟩
      rw [mem_halves] at hS
      have : ({a, b} : Finset _) ⊆ S := by simp [Finset.insert_subset_iff, ha, hb]
      have := Finset.card_le_card this
      rw [Finset.card_pair hab] at this
      omega
    rw [hempty, hm1]; simp
  · have hf : (halves m).filter (fun S => a ∈ S ∧ b ∈ S) =
        ((Finset.univ : Finset (Fin (2 * m))).powersetCard m).filter
          (fun S => ({a, b} : Finset _) ⊆ S) := by
      unfold halves
      apply Finset.filter_congr
      intro S _
      simp [Finset.insert_subset_iff]
    have hc := Finset.card_filter_powersetCard_subset {a, b} Finset.univ m (by simp)
      (by rw [Finset.card_pair hab]; omega)
    rw [Finset.card_pair hab, Finset.card_univ, Fintype.card_fin] at hc
    rw [hf, hc]
    -- binomial identities
    have e1 := Nat.add_one_mul_choose_eq (2 * m - 1) (m - 1)
    have e2 := Nat.add_one_mul_choose_eq (2 * m - 2) (m - 2)
    have r1 : 2 * m - 1 + 1 = 2 * m := by omega
    have r2 : m - 1 + 1 = m := by omega
    have r3 : 2 * m - 2 + 1 = 2 * m - 1 := by omega
    have r4 : m - 2 + 1 = m - 1 := by omega
    rw [r1, r2] at e1
    rw [r3, r4] at e2
    have e1' : ((2 * m : ℕ) : ℝ) * ((2 * m - 1).choose (m - 1) : ℕ) =
        ((2 * m).choose m : ℕ) * (m : ℝ) := by exact_mod_cast e1
    have e2' : ((2 * m - 1 : ℕ) : ℝ) * ((2 * m - 2).choose (m - 2) : ℕ) =
        ((2 * m - 1).choose (m - 1) : ℕ) * ((m - 1 : ℕ) : ℝ) := by exact_mod_cast e2
    have c1 : ((2 * m - 1 : ℕ) : ℝ) = 2 * m - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have c2 : ((m - 1 : ℕ) : ℝ) = m - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [c1] at e2'
    rw [c2] at e2'
    push_cast at e1'
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    -- combine
    have : ((2 * m - 2).choose (m - 2) : ℝ) * (2 * m * (2 * m - 1)) =
        2 * m * (((2 * m - 1).choose (m - 1) : ℕ) * (m - 1)) := by
      rw [← e2']; ring
    rw [this]
    have : 2 * (m : ℝ) * ((2 * m - 1).choose (m - 1) : ℕ) = ((2 * m).choose m : ℕ) * m := by
      rw [← e1']
    calc 2 * (m : ℝ) * (((2 * m - 1).choose (m - 1) : ℕ) * (m - 1))
        = (2 * (m : ℝ) * ((2 * m - 1).choose (m - 1) : ℕ)) * (m - 1) := by ring
      _ = ((2 * m).choose m : ℕ) * m * (m - 1) := by rw [this]
      _ = ((2 * m).choose m : ℕ) * (m * (m - 1)) := by ring

/-- The mean of the number `J` of successes in a uniform half: `∑_S J(S) = K N/2` (from the
complement symmetry `J(Sᶜ) = K - J(S)`).
Paper: `lem:correctedbernstein` (attention_implicit.tex). -/
theorem hyper_sum (A : Finset (Fin (2 * m))) :
    ∑ S ∈ halves m, ((S ∩ A).card : ℝ) = A.card * (halves m).card / 2 := by
  have h := sum_halves_compl m (fun S => ((S ∩ A).card : ℝ))
  simp only [inter_compl_card] at h
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h
  linarith

/-- The second moment: `∑_S J(S)² = N (K/2 + K(K-1)(m-1)/(2(2m-1)))`.
Paper: `lem:correctedbernstein` (attention_implicit.tex), "the usual two-indicator
calculation". -/
theorem hyper_sum_sq (hm : 1 ≤ m) (A : Finset (Fin (2 * m))) :
    ∑ S ∈ halves m, ((S ∩ A).card : ℝ) ^ 2 =
      (halves m).card * (A.card / 2 + A.card * (A.card - 1) * (m - 1) / (2 * (2 * m - 1))) := by
  classical
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h2m : (0 : ℝ) < 2 * m - 1 := by linarith
  have hN : ((halves m).card : ℝ) = (2 * m).choose m := by rw [halves_card]
  -- indicator expansion
  have hJ : ∀ S, ((S ∩ A).card : ℝ) = ∑ a ∈ A, (if a ∈ S then (1 : ℝ) else 0) := by
    intro S
    rw [Finset.sum_boole]
    congr 1
    rw [Finset.inter_comm]
    congr 1
  have hsq : ∀ S, ((S ∩ A).card : ℝ) ^ 2 =
      ∑ a ∈ A, ∑ b ∈ A, (if a ∈ S ∧ b ∈ S then (1 : ℝ) else 0) := by
    intro S
    rw [hJ, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb]
  simp_rw [hsq]
  rw [Finset.sum_comm]
  have hinner : ∀ a ∈ A, ∑ S ∈ halves m, ∑ b ∈ A, (if a ∈ S ∧ b ∈ S then (1 : ℝ) else 0) =
      ((2 * m - 1).choose (m - 1) : ℝ) +
        (A.card - 1) * ((2 * m).choose m * (m * (m - 1)) / (2 * m * (2 * m - 1))) := by
    intro a ha
    rw [Finset.sum_comm]
    rw [← Finset.add_sum_erase _ _ ha]
    have hdiag : ∑ S ∈ halves m, (if a ∈ S ∧ a ∈ S then (1 : ℝ) else 0) =
        ((2 * m - 1).choose (m - 1) : ℝ) := by
      simp only [and_self]
      rw [Finset.sum_boole, count_one m hm a]
    have hoff : ∀ b ∈ A.erase a, ∑ S ∈ halves m, (if a ∈ S ∧ b ∈ S then (1 : ℝ) else 0) =
        (2 * m).choose m * (m * (m - 1)) / (2 * m * (2 * m - 1)) := by
      intro b hb
      have hab : a ≠ b := (Finset.ne_of_mem_erase hb).symm
      rw [Finset.sum_boole, eq_div_iff (by positivity)]
      exact count_two m hm a b hab
    rw [hdiag, Finset.sum_congr rfl hoff, Finset.sum_const, nsmul_eq_mul,
      Finset.card_erase_of_mem ha, Nat.cast_sub (Finset.card_pos.mpr ⟨a, ha⟩)]
    simp
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
  -- `binom(2m-1, m-1) = N/2`
  have e1 := Nat.add_one_mul_choose_eq (2 * m - 1) (m - 1)
  have r1 : 2 * m - 1 + 1 = 2 * m := by omega
  have r2 : m - 1 + 1 = m := by omega
  rw [r1, r2] at e1
  have e1' : (2 * (m : ℝ)) * ((2 * m - 1).choose (m - 1) : ℕ) = ((2 * m).choose m : ℕ) * m := by
    exact_mod_cast e1
  have hc1 : ((2 * m - 1).choose (m - 1) : ℝ) = ((2 * m).choose m : ℕ) / 2 := by
    have hmpos : (0 : ℝ) < m := by linarith
    field_simp
    nlinarith [e1']
  rw [hc1, hN]
  generalize (2 * (m : ℝ) - 1) = k at *
  have hk0 : k ≠ 0 := h2m.ne'
  field_simp

/-- The hypergeometric law of `Y = J/m` for a uniform half of `2m` bits with `K` successes,
`p = K/(2m)`: it is a probability law, `E Δ = 0`, `E Δ³ = 0` (symmetry under complements), and
`E Δ² = p(1-p)/(2m-1)`, where `Δ = Y - p`.
Paper: `lem:correctedbernstein` (attention_implicit.tex). -/
theorem hypergeometric_moments (hm : 1 ≤ m) (A : Finset (Fin (2 * m))) :
    let N : ℝ := (halves m).card
    let p : ℝ := A.card / (2 * m)
    let Δ : Finset (Fin (2 * m)) → ℝ := fun S => ((S ∩ A).card : ℝ) / m - p
    (∑ _S ∈ halves m, 1 / N = 1) ∧ (∑ S ∈ halves m, 1 / N * Δ S = 0) ∧
      (∑ S ∈ halves m, 1 / N * Δ S ^ 3 = 0) ∧
      (∑ S ∈ halves m, 1 / N * Δ S ^ 2 = p * (1 - p) / (2 * m - 1)) := by
  intro N p Δ
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hNpos : 0 < N := by
    show (0 : ℝ) < (halves m).card
    rw [halves_card]; exact_mod_cast Nat.choose_pos (by omega)
  have hcomp : ∀ S, Δ (Finset.univ \ S) = -Δ S := by
    intro S
    simp only [Δ, p]
    rw [inter_compl_card]
    field_simp
    ring
  have hodd : ∀ k, Odd k → ∑ S ∈ halves m, 1 / N * Δ S ^ k = 0 := by
    intro k hk
    have h := sum_halves_compl m (fun S => 1 / N * Δ S ^ k)
    simp only [hcomp, hk.neg_pow] at h
    rw [show ∑ S ∈ halves m, 1 / N * -Δ S ^ k = -∑ S ∈ halves m, 1 / N * Δ S ^ k by
      rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun S _ => ?_; ring] at h
    linarith
  refine ⟨?_, by simpa using hodd 1 odd_one, hodd 3 (by decide), ?_⟩
  · rw [Finset.sum_const, nsmul_eq_mul]; field_simp; rfl
  · have h1 := hyper_sum m A
    have h2 := hyper_sum_sq m hm A
    have hpt : ∀ S, 1 / N * Δ S ^ 2 = 1 / N / (m : ℝ) ^ 2 * ((S ∩ A).card : ℝ) ^ 2 -
        1 / N * (2 * p / m) * ((S ∩ A).card : ℝ) + 1 / N * p ^ 2 := by
      intro S; simp only [Δ]; field_simp; ring
    rw [Finset.sum_congr rfl (fun S _ => hpt S), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, h1, h2]
    have h2m : (0 : ℝ) < 2 * m - 1 := by linarith
    have hNdef : ((halves m).card : ℝ) = N := rfl
    rw [hNdef]
    simp only [p]
    generalize hk : (2 * (m : ℝ) - 1) = k at *
    have hk0 : k ≠ 0 := h2m.ne'
    field_simp
    rw [← hk]
    ring

/-- The corrected coefficient bound for the actual degree-elevation law: for a uniform half of
`2m` bits with `K` successes, `|d_{m,K}| ≤ A/(4m²)`, with the fourth-moment bound `E Δ⁴ ≤ m^{-2}`
and the pointwise Taylor bounds as the only remaining hypotheses (`hH2b` is the sup form of
`h_second_derivative_bound`).
Paper: `lem:correctedbernstein`, display `eq:correctedcoefficientbound`
(attention_implicit.tex). -/
theorem corrected_coefficient_hypergeometric (hm : 1 ≤ m) (A : Finset (Fin (2 * m)))
    (f f2 h : ℝ → ℝ) (F1 F3 H1 M2 M3 M4 H2 : ℝ)
    (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3) (hM4 : 0 ≤ M4) (hH2 : 0 ≤ H2)
    (hf2 : |f2 (A.card / (2 * m))| ≤ M2) (hH2b : H2 ≤ 2 * M2 + 2 * M3 + M4 / 4)
    (hh : ∀ x, h x = x * (1 - x) * f2 x)
    (hfourth : ∑ S ∈ halves m, 1 / ((halves m).card : ℝ) *
      (((S ∩ A).card : ℝ) / m - A.card / (2 * m)) ^ 4 ≤ 1 / (m : ℝ) ^ 2)
    (htf : ∀ S ∈ halves m, |f (((S ∩ A).card : ℝ) / m) - (f (A.card / (2 * m)) +
        F1 * (((S ∩ A).card : ℝ) / m - A.card / (2 * m)) +
        f2 (A.card / (2 * m)) / 2 * (((S ∩ A).card : ℝ) / m - A.card / (2 * m)) ^ 2 +
        F3 / 6 * (((S ∩ A).card : ℝ) / m - A.card / (2 * m)) ^ 3)| ≤
        M4 / 24 * (((S ∩ A).card : ℝ) / m - A.card / (2 * m)) ^ 4)
    (hth : ∀ S ∈ halves m, |h (((S ∩ A).card : ℝ) / m) - (h (A.card / (2 * m)) +
        H1 * (((S ∩ A).card : ℝ) / m - A.card / (2 * m)))| ≤
        H2 / 2 * (((S ∩ A).card : ℝ) / m - A.card / (2 * m)) ^ 2) :
    |(f (A.card / (2 * m)) - h (A.card / (2 * m)) / (2 * (2 * m : ℕ))) -
        ∑ S ∈ halves m, 1 / ((halves m).card : ℝ) *
          (f (((S ∩ A).card : ℝ) / m) - h (((S ∩ A).card : ℝ) / m) / (2 * m))| ≤
      (M2 + M3 + M4) / (4 * (m : ℝ) ^ 2) := by
  obtain ⟨hw1, hmean, hthird, hvar⟩ := hypergeometric_moments m hm A
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hK : (A.card : ℝ) ≤ 2 * m := by
    have := Finset.card_le_univ A
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hp0 : 0 ≤ (A.card : ℝ) / (2 * m) := by positivity
  have hp1 : (A.card : ℝ) / (2 * m) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact hK
  have hNpos : (0 : ℝ) < (halves m).card := by
    rw [halves_card]; exact_mod_cast Nat.choose_pos (by omega)
  exact corrected_coefficient_bound (halves m) (fun _ => 1 / ((halves m).card : ℝ))
    (fun S => ((S ∩ A).card : ℝ) / m) m hm _ hp0 hp1 f f2 h F1 F3 H1 M2 M3 M4 H2
    hM2 hM3 hM4 hH2 hf2 hH2b hh (fun _ _ => by positivity) hw1 hmean hthird hvar hfourth
    htf hth

end Hypergeometric

/-! ## The mixture (`lem:correctedbernstein`) -/

section Mixture

/-- The corrected base coefficients fit inside the chosen base mass:
`4/5 + M₂/(8m) < 7/8` when `2M₂ ≤ m`.
Paper: `lem:correctedbernstein` (attention_implicit.tex). -/
theorem base_margin {m m2 : ℝ} (hm : 0 < m) (hsize : 2 * m2 ≤ m) :
    (4 : ℝ) / 5 + m2 / (8 * m) < (7 : ℝ) / 8 := by
  have hdiv : m2 / (8 * m) ≤ (1 : ℝ) / 16 := by
    rw [div_le_iff₀ (by positivity : 0 < 8 * m)]
    linarith
  linarith

/-- The total geometric correction mass is at most `1/12`: `A/(3m²) ≤ 1/12` when `4A ≤ m²`.
Paper: `lem:correctedbernstein` (attention_implicit.tex). -/
theorem correction_mass {a m : ℝ} (hm : 0 < m) (hsize : 4 * a ≤ m ^ 2) :
    a / (3 * m ^ 2) ≤ (1 : ℝ) / 12 := by
  rw [div_le_iff₀ (by positivity : 0 < 3 * m ^ 2)]
  linarith

/-- The remaining probability is nonnegative, with a fixed margin.
Paper: `lem:correctedbernstein` (attention_implicit.tex). -/
theorem fair_completion {c : ℝ} (hc : c ≤ (1 : ℝ) / 12) :
    (1 : ℝ) / 24 ≤ 1 - ((7 : ℝ) / 8 + c) := by
  linarith

/-- Conditional correction-level probabilities have ratio one quarter.
Paper: `lem:correctedbernstein` (attention_implicit.tex). -/
theorem correction_scale {a m : ℝ} (hm : m ≠ 0) :
    a / (4 * (2 * m) ^ 2) = (a / (4 * m ^ 2)) / 4 := by
  field_simp
  ring

/-- A component of mass `c` and normalized mean `d/c` contributes exactly `d`.
Paper: `lem:correctedbernstein` (attention_implicit.tex). -/
theorem mixture_component_exact {c d : ℝ} (hc : c ≠ 0) : c * (d / c) = d := by
  field_simp

/-- The correction masses `c_ℓ = A/(4m_ℓ²)` with `m_ℓ = 2^ℓ m₀` sum to `A/(3m₀²)`.
Paper: `lem:correctedbernstein` (attention_implicit.tex). -/
theorem correction_masses (A m0 : ℝ) (hm0 : 0 < m0) :
    HasSum (fun ℓ : ℕ => A / (4 * (2 ^ ℓ * m0) ^ 2)) (A / (3 * m0 ^ 2)) := by
  have h := (hasSum_geometric_of_lt_one (r := (1 : ℝ) / 4) (by norm_num) (by norm_num)).mul_left
    (A / (4 * m0 ^ 2))
  convert h using 1
  · funext ℓ
    rw [mul_pow, ← pow_mul, div_pow, one_pow,
      show (2 : ℝ) ^ (ℓ * 2) = 4 ^ ℓ by rw [mul_comm, pow_mul]; norm_num]
    field_simp
  · field_simp; ring

/-- The conditional level law is `(3/4) 4^{-ℓ}`.
Paper: `lem:correctedbernstein` (attention_implicit.tex). -/
theorem level_law (A m0 : ℝ) (hA : 0 < A) (hm0 : 0 < m0) (ℓ : ℕ) :
    (A / (4 * (2 ^ ℓ * m0) ^ 2)) / (A / (3 * m0 ^ 2)) = 3 / 4 * ((1 : ℝ) / 4) ^ ℓ := by
  rw [mul_pow, ← pow_mul, div_pow, one_pow,
    show (2 : ℝ) ^ (ℓ * 2) = 4 ^ ℓ by rw [mul_comm, pow_mul]; norm_num]
  field_simp

/-- The mean source count of the corrections: `∑_ℓ 2m_ℓ c_ℓ = A/m₀`, so together with the base
branch the expected number of source bits is `b₀ m₀ + ∑_ℓ 2m_ℓ c_ℓ = (7/8)m₀ + A/m₀`.
Paper: `lem:correctedbernstein`, display `eq:correctedsourcecost` (attention_implicit.tex). -/
theorem source_count (A m0 : ℝ) (hm0 : 0 < m0) :
    HasSum (fun ℓ : ℕ => 2 * (2 ^ ℓ * m0) * (A / (4 * (2 ^ ℓ * m0) ^ 2))) (A / m0) := by
  have h := (hasSum_geometric_of_lt_one (r := (1 : ℝ) / 2) (by norm_num) (by norm_num)).mul_left
    (A / (2 * m0))
  convert h using 1
  · funext ℓ
    rw [div_pow, one_pow]
    have : (0 : ℝ) < 2 ^ ℓ := by positivity
    field_simp
    ring
  · field_simp; ring

/-- The telescoping step of the mixture: if `x_ℓ` converges to `F` and every correction
`x_{ℓ+1} - x_ℓ` obeys `|x_{ℓ+1} - x_ℓ| ≤ c_ℓ = A/(4m_ℓ²)`, then the corrections sum absolutely
to `F - x₀`, so the mixture mean `b₀ (x₀/b₀) + ∑_ℓ c_ℓ ((x_{ℓ+1} - x_ℓ)/c_ℓ)` equals `F`. The
convergence hypothesis is discharged for `x_ℓ = B_{m_ℓ} g_{m_ℓ}(p)` in
`corrected_bernstein_limit`.
Paper: `lem:correctedbernstein` (attention_implicit.tex). -/
theorem mixture_exact (A m0 F : ℝ) (hA : 0 < A) (hm0 : 0 < m0) (x : ℕ → ℝ)
    (hlim : Tendsto x atTop (𝓝 F))
    (hd : ∀ ℓ, |x (ℓ + 1) - x ℓ| ≤ A / (4 * (2 ^ ℓ * m0) ^ 2)) :
    HasSum (fun ℓ => A / (4 * (2 ^ ℓ * m0) ^ 2) * ((x (ℓ + 1) - x ℓ) /
        (A / (4 * (2 ^ ℓ * m0) ^ 2)))) (F - x 0) ∧
      7 / 8 * (x 0 / (7 / 8)) + (F - x 0) = F := by
  have hc : ∀ ℓ : ℕ, 0 < A / (4 * (2 ^ ℓ * m0) ^ 2) := fun ℓ => by positivity
  have hsummable : Summable (fun ℓ => x (ℓ + 1) - x ℓ) :=
    Summable.of_norm_bounded (correction_masses A m0 hm0).summable
      (fun ℓ => by rw [Real.norm_eq_abs]; exact hd ℓ)
  obtain ⟨S, hS⟩ := hsummable
  have hpartial : Tendsto (fun n => ∑ ℓ ∈ Finset.range n, (x (ℓ + 1) - x ℓ)) atTop
      (𝓝 (F - x 0)) := by
    have : (fun n => ∑ ℓ ∈ Finset.range n, (x (ℓ + 1) - x ℓ)) = fun n => x n - x 0 := by
      funext n; exact Finset.sum_range_sub x n
    rw [this]
    exact hlim.sub tendsto_const_nhds
  have hSeq : S = F - x 0 := tendsto_nhds_unique hS.tendsto_sum_nat hpartial
  refine ⟨?_, by field_simp; ring⟩
  have : (fun ℓ => A / (4 * (2 ^ ℓ * m0) ^ 2) * ((x (ℓ + 1) - x ℓ) /
      (A / (4 * (2 ^ ℓ * m0) ^ 2)))) = fun ℓ => x (ℓ + 1) - x ℓ := by
    funext ℓ; field_simp [(hc ℓ).ne']
  rw [this, ← hSeq]; exact hS

/-- The corrected Bernstein values converge: with `m_ℓ = 2^ℓ m₀` and
`B_m g_m(p) = B_m f(p) - B_m h(p)/(2m)` (the Bernstein polynomial of `g_m = f - h/(2m)`),
`B_{m_ℓ} g_{m_ℓ}(p) → f(p)` for continuous `f` and `h` on `[0,1]`. This uses Mathlib's uniform
convergence of Bernstein approximations and `|B_m h| ≤ ‖h‖_∞` (finite since `[0,1]` is
compact).
Paper: `lem:correctedbernstein` (attention_implicit.tex), "`B_m g_m → f` uniformly". -/
theorem corrected_bernstein_limit (f h : C(unitInterval, ℝ)) (m0 : ℕ) (hm0 : 1 ≤ m0)
    (p : unitInterval) :
    Tendsto (fun ℓ : ℕ => bernsteinApproximation (2 ^ ℓ * m0) f p -
      bernsteinApproximation (2 ^ ℓ * m0) h p / (2 * ((2 ^ ℓ * m0 : ℕ) : ℝ))) atTop
      (𝓝 (f p)) := by
  have hm : Tendsto (fun ℓ : ℕ => 2 ^ ℓ * m0) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro ℓ
    have h1 : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self
    have h2 : 2 ^ ℓ ≤ 2 ^ ℓ * m0 := Nat.le_mul_of_pos_right _ (by omega)
    simp only [id]; omega
  have h1 : Tendsto (fun ℓ : ℕ => bernsteinApproximation (2 ^ ℓ * m0) f p) atTop (𝓝 (f p)) :=
    ((continuous_eval_const p).tendsto f).comp
      ((bernsteinApproximation_uniform f).comp hm)
  set Hh := ‖h‖ with hHh
  have hh : ∀ y, |h y| ≤ Hh := fun y => by
    rw [← Real.norm_eq_abs]; exact h.norm_coe_le_norm y
  have hbound : ∀ n : ℕ, |bernsteinApproximation n h p| ≤ Hh := by
    intro n
    rw [bernsteinApproximation.apply]
    calc |∑ k : Fin (n + 1), bernstein n k p • h (bernstein.z k)|
        ≤ ∑ k : Fin (n + 1), |bernstein n k p • h (bernstein.z k)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin (n + 1), bernstein n k p * Hh := by
          apply Finset.sum_le_sum; intro k _
          rw [smul_eq_mul, abs_mul, abs_of_nonneg bernstein_nonneg]
          exact mul_le_mul_of_nonneg_left (hh _) bernstein_nonneg
      _ = Hh := by rw [← Finset.sum_mul, bernstein.probability, one_mul]
  have hden : Tendsto (fun ℓ : ℕ => 2 * ((2 ^ ℓ * m0 : ℕ) : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) (tendsto_natCast_atTop_atTop.comp hm)
  have h2 : Tendsto (fun ℓ : ℕ => bernsteinApproximation (2 ^ ℓ * m0) h p /
      (2 * ((2 ^ ℓ * m0 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have hlim0 : Tendsto (fun ℓ : ℕ => |Hh| / (2 * ((2 ^ ℓ * m0 : ℕ) : ℝ))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    apply squeeze_zero_norm _ hlim0
    intro ℓ
    have hpos : (0 : ℝ) < 2 * ((2 ^ ℓ * m0 : ℕ) : ℝ) := by
      have : 0 < 2 ^ ℓ * m0 := Nat.mul_pos (by positivity) (by omega)
      positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right ((hbound _).trans (le_abs_self Hh)) hpos.le
  simpa using h1.sub h2

/-- The mixture is exact for the corrected Bernstein values: with `x_ℓ = B_{m_ℓ} g_{m_ℓ}(p)`,
`m_ℓ = 2^ℓ m₀`, and corrections bounded by `c_ℓ = A/(4m_ℓ²)`, the corrections sum to
`f(p) - B_{m₀} g_{m₀}(p)` and the mixture mean is `f(p)`. The per-level correction bound is a
hypothesis: in the paper it is the coefficient bound `corrected_coefficient_hypergeometric`
averaged over the binomial law of the total `K`, by degree elevation (not formalized here).
Paper: `lem:correctedbernstein` (attention_implicit.tex). -/
theorem bernstein_mixture_exact (f h : C(unitInterval, ℝ)) (A : ℝ) (hA : 0 < A) (m0 : ℕ)
    (hm0 : 1 ≤ m0) (p : unitInterval)
    (hd : ∀ ℓ : ℕ, |(bernsteinApproximation (2 ^ (ℓ + 1) * m0) f p -
        bernsteinApproximation (2 ^ (ℓ + 1) * m0) h p / (2 * ((2 ^ (ℓ + 1) * m0 : ℕ) : ℝ))) -
      (bernsteinApproximation (2 ^ ℓ * m0) f p -
        bernsteinApproximation (2 ^ ℓ * m0) h p / (2 * ((2 ^ ℓ * m0 : ℕ) : ℝ)))| ≤
      A / (4 * (2 ^ ℓ * (m0 : ℝ)) ^ 2)) :
    let x : ℕ → ℝ := fun ℓ => bernsteinApproximation (2 ^ ℓ * m0) f p -
      bernsteinApproximation (2 ^ ℓ * m0) h p / (2 * ((2 ^ ℓ * m0 : ℕ) : ℝ))
    HasSum (fun ℓ => A / (4 * (2 ^ ℓ * (m0 : ℝ)) ^ 2) * ((x (ℓ + 1) - x ℓ) /
        (A / (4 * (2 ^ ℓ * (m0 : ℝ)) ^ 2)))) (f p - x 0) ∧
      7 / 8 * (x 0 / (7 / 8)) + (f p - x 0) = f p := by
  intro x
  have hm0r : (0 : ℝ) < m0 := by exact_mod_cast (show 0 < m0 by omega)
  exact mixture_exact A m0 (f p) hA hm0r x (corrected_bernstein_limit f h m0 hm0 p) hd

/-- The coins of the mixture are legal for every count `K`: the base coin has mean
`g_{m₀}(K/m₀)/b₀ ∈ [-1,1]` because `|f| ≤ 4/5`, `|h| ≤ M₂/4`, and `2M₂ ≤ m₀`; a correction coin has
mean `d_{m,K}/c_ℓ ∈ [-1,1]` whenever `|d_{m,K}| ≤ c_ℓ` (as given by
`corrected_coefficient_hypergeometric` with `c_ℓ = A/(4m²)`).
Paper: `lem:correctedbernstein` (attention_implicit.tex), "All these means are in `[-1,1]`". -/
theorem per_K_coins (fy hy M2 m0 d c : ℝ) (hf : |fy| ≤ 4 / 5) (hh : |hy| ≤ M2 / 4)
    (hm0 : 0 < m0) (hsize : 2 * M2 ≤ m0) (hc : 0 < c) (hd : |d| ≤ c) :
    |(fy - hy / (2 * m0)) / (7 / 8)| ≤ 1 ∧ |d / c| ≤ 1 := by
  constructor
  · have hM2 : 0 ≤ M2 := by have := abs_nonneg hy; linarith
    have h1 : |hy / (2 * m0)| ≤ 1 / 16 := by
      have h2m : (0 : ℝ) < 2 * m0 := by linarith
      rw [abs_div, abs_of_pos h2m, div_le_iff₀ h2m]
      linarith
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 8), div_le_one (by norm_num)]
    calc |fy - hy / (2 * m0)| ≤ |fy| + |hy / (2 * m0)| := abs_sub _ _
      _ ≤ 7 / 8 := by linarith
  · rw [abs_div, abs_of_pos hc, div_le_one hc]; exact hd

end Mixture

/-! ## Explicit constants (`thm:implicitrankone`) -/

section Constants

/-- With `M₂ = 3Λ²`, `M₃ = 13Λ³`, `M₄ = 75Λ⁴`, `A = M₂ + M₃ + M₄`, and `m₀` the least power of two
at least `X = max{1, 2M₂, 2√A}` (so `X ≤ m₀ < 2X`): `A ≤ 91 max{Λ², Λ⁴}`,
`m₀ < 40 max{1, Λ²}`, `A/m₀ ≤ m₀/4`, and the source count `(7/8)m₀ + A/m₀` is less than
`45 max{1, Λ²}`. Paper: `thm:implicitrankone` (attention_implicit.tex). -/
theorem implicit_constants (Λ m0 : ℝ) (hΛ : 0 ≤ Λ)
    (hm0 : max 1 (max (2 * (3 * Λ ^ 2))
      (2 * Real.sqrt (3 * Λ ^ 2 + 13 * Λ ^ 3 + 75 * Λ ^ 4))) ≤ m0)
    (hm0' : m0 < 2 * max 1 (max (2 * (3 * Λ ^ 2))
      (2 * Real.sqrt (3 * Λ ^ 2 + 13 * Λ ^ 3 + 75 * Λ ^ 4)))) :
    3 * Λ ^ 2 + 13 * Λ ^ 3 + 75 * Λ ^ 4 ≤ 91 * max (Λ ^ 2) (Λ ^ 4) ∧
      m0 < 40 * max 1 (Λ ^ 2) ∧
      (3 * Λ ^ 2 + 13 * Λ ^ 3 + 75 * Λ ^ 4) / m0 ≤ m0 / 4 ∧
      7 / 8 * m0 + (3 * Λ ^ 2 + 13 * Λ ^ 3 + 75 * Λ ^ 4) / m0 < 45 * max 1 (Λ ^ 2) := by
  set A := 3 * Λ ^ 2 + 13 * Λ ^ 3 + 75 * Λ ^ 4 with hA
  set μ := max 1 (Λ ^ 2) with hμ
  have hμ1 : 1 ≤ μ := le_max_left _ _
  have hμΛ : Λ ^ 2 ≤ μ := le_max_right _ _
  have hA0 : 0 ≤ A := by positivity
  have hAmax : A ≤ 91 * max (Λ ^ 2) (Λ ^ 4) := by
    rcases le_total Λ 1 with h | h
    · have h3 : Λ ^ 3 ≤ Λ ^ 2 := pow_le_pow_of_le_one hΛ h (by norm_num)
      have h4 : Λ ^ 4 ≤ Λ ^ 2 := pow_le_pow_of_le_one hΛ h (by norm_num)
      have : Λ ^ 2 ≤ max (Λ ^ 2) (Λ ^ 4) := le_max_left _ _
      nlinarith
    · have h2 : Λ ^ 2 ≤ Λ ^ 4 := pow_le_pow_right₀ h (by norm_num)
      have h3 : Λ ^ 3 ≤ Λ ^ 4 := pow_le_pow_right₀ h (by norm_num)
      have : Λ ^ 4 ≤ max (Λ ^ 2) (Λ ^ 4) := le_max_right _ _
      nlinarith
  have hAμ : A ≤ 91 * μ ^ 2 := by
    have : max (Λ ^ 2) (Λ ^ 4) ≤ μ ^ 2 := by
      apply max_le
      · nlinarith
      · have : Λ ^ 4 = (Λ ^ 2) ^ 2 := by ring
        rw [this]; exact pow_le_pow_left₀ (by positivity) hμΛ 2
    linarith
  have hsqrt : Real.sqrt A ≤ 10 * μ := by
    rw [Real.sqrt_le_iff]; constructor
    · positivity
    · nlinarith
  have hX : max 1 (max (2 * (3 * Λ ^ 2)) (2 * Real.sqrt A)) ≤ 20 * μ := by
    apply max_le
    · linarith
    · apply max_le <;> nlinarith
  have hm0pos : 0 < m0 := lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) hm0)
  have hm0A : 2 * Real.sqrt A ≤ m0 := le_trans (le_trans (le_max_right _ _)
    (le_max_right _ _)) hm0
  have hsq : 4 * A ≤ m0 ^ 2 := by
    have h1 : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA0
    nlinarith [Real.sqrt_nonneg A]
  have hAm : A / m0 ≤ m0 / 4 := by
    rw [div_le_div_iff₀ hm0pos (by norm_num)]; nlinarith
  refine ⟨hAmax, by linarith, hAm, ?_⟩
  have : m0 < 40 * μ := by linarith
  linarith

/-- Hypergeometric weights `w_j = binom(m,j) binom(m,K-j)` satisfy the forward ratio
`w_{j+1} (j+1)(m-K+j+1) = w_j (m-j)(K-j)` (natural-number form, with `m-K+j+1` written as
`m+j+1-K`, which is exact under the support condition `K - j - 1 ≤ m`).
Paper: `thm:implicitrankone` (attention_implicit.tex), the outward weight recursion. -/
theorem hypergeometric_ratio (m K j : ℕ) (hjK : j < K) (hKm : K - j - 1 ≤ m) :
    m.choose (j + 1) * m.choose (K - (j + 1)) * ((j + 1) * (m + j + 1 - K)) =
      m.choose j * m.choose (K - j) * ((m - j) * (K - j)) := by
  have h1 := Nat.choose_succ_right_eq m j
  have h2 := Nat.choose_succ_right_eq m (K - j - 1)
  have e1 : K - j - 1 + 1 = K - j := by omega
  have e2 : K - (j + 1) = K - j - 1 := by omega
  have e3 : m - (K - j - 1) = m + j + 1 - K := by omega
  rw [e1, e3] at h2
  rw [e2]
  calc m.choose (j + 1) * m.choose (K - j - 1) * ((j + 1) * (m + j + 1 - K))
      = (m.choose (j + 1) * (j + 1)) * (m.choose (K - j - 1) * (m + j + 1 - K)) := by ring
    _ = (m.choose j * (m - j)) * (m.choose (K - j) * (K - j)) := by rw [h1, h2]
    _ = m.choose j * m.choose (K - j) * ((m - j) * (K - j)) := by ring

/-- The forward ratio is at most one exactly from the mode `j ≥ (K-1)/2` on:
`(m-j)(K-j) - (j+1)(m-K+j+1) = (m+1)(K-2j-1)`.
Paper: `thm:implicitrankone` (attention_implicit.tex), the mode `⌊K/2⌋`. -/
theorem hypergeometric_mode (m K j : ℤ) :
    (m - j) * (K - j) - (j + 1) * (m - K + j + 1) = (m + 1) * (K - 2 * j - 1) := by
  ring

/-- Half the attention output leaves a fixed amplitude margin: `|u/2| ≤ 1/2` for `|u| ≤ 1`.
Paper: `thm:implicitrankone` (attention_implicit.tex), radius two. -/
theorem coordinate_radius_two {u : ℝ} (hu : |u| ≤ 1) : |u / 2| ≤ (1 : ℝ) / 2 := by
  rw [abs_div, abs_two]
  linarith

/-- Rank-one reparametrization: for `k_j = c + t_j u`, `⟨q, u⟩ = R z`, and `p = (1+z)/2`, the
score `β⟨q,k_j⟩/n` equals a common offset plus slope `2βR t_j/n` times `p` plus offset
`-βR t_j/n`. Paper: the paragraph after `thm:implicitrankone` (attention_implicit.tex), and
`thm:rankone-worstlaw` (attention_query_law.tex). -/
theorem rank_one_reparametrization (β n qc t R z : ℝ) :
    β / n * (qc + t * (R * z)) =
      β / n * qc + (2 * β * R * t / n) * ((1 + z) / 2) + (-(β * R * t / n)) := by
  ring

/-- Constants of the rank-one upper bound: with `Λ ≤ 4β`, fewer than `45Λ² ≤ 720β²` source
requests per radius-two sign, and at most `8·2` such signs per final token, give at most
`11520β²` input requests. Paper: `thm:rankone-worstlaw` (attention_query_law.tex). -/
theorem rank_one_request_constants (β Λ : ℝ) (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ 4 * β) :
    45 * Λ ^ 2 ≤ 720 * β ^ 2 ∧ 720 * β ^ 2 * 8 * 2 = 11520 * β ^ 2 := by
  constructor
  · nlinarith
  · ring

end Constants

end ExactSampling.ImplicitRankOne
