import Mathlib

/-!
# The product arity proposal: generating functions and the positive-count sampler

This module formalizes the finite and series identities behind the product law
for the majority index in `tanh_large_radius.tex` (subsection `sec:productarity`:
`lem:productaritylaw`, `lem:producttail`) that are specific to the sampler.

Formalized here:
* the geometric law and its generating function, the law of the sum of two
  independent geometric counts as a convolution, `P(G_1 + G_2 = k) = (k+1)p^2(1-p)^k`,
  and its generating function `p^2/(1 - (1-p)v)^2 = (1 + a(1-v))^{-2}` at
  `p = 1/(1+a)`;
* the budget of the tail construction: with `H = max{1,u}` and `J = ⌈H⌉`,
  `J ≤ 2H`, `Λ = 2u^2/J ≤ 2H`, and `2u^2/J^2 ≤ 2`;
* the exact conditional sampler of `lem:producttail` for a positive count, both
  as an identity of probability mass functions and of generating functions.

Not formalized: the cosine product for `sech^2(u √(1-v))` and the uniqueness of
generating functions (so the identification `P(K = k) = d_k` is not proved), the
Poisson marking theorem, and the bit-cost analysis of `lem:productaritybits`.
-/

open Real Finset

namespace ExactSampling.ProductAritySampler

/-- The probability generating function `p/(1 - (1-p)v)` of a geometric count. -/
noncomputable def geometricPGF (p v : ℝ) : ℝ := p / (1 - (1 - p) * v)

/-- The generating function of the sum of two independent geometric counts. -/
noncomputable def negativeBinomialTwoPGF (p v : ℝ) : ℝ := geometricPGF p v ^ 2

/-- Paper: `lem:productaritylaw` (tanh_large_radius.tex): `Pr(G = k) = p(1-p)^k`
has generating function `p/(1 - (1-p)v)` for `0 < p ≤ 1`, `|v| ≤ 1`. -/
theorem hasSum_geometric_pgf (p v : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hv : |v| ≤ 1) :
    HasSum (fun k : ℕ => p * (1 - p) ^ k * v ^ k) (geometricPGF p v) := by
  have hr : ‖(1 - p) * v‖ < 1 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith)]
    nlinarith [abs_nonneg v]
  have h := (hasSum_geometric_of_norm_lt_one hr).mul_left p
  unfold geometricPGF
  convert h using 1
  · funext k
    rw [mul_pow]
    ring
  · rw [div_eq_mul_inv]

/-- Paper: `lem:productaritylaw` (tanh_large_radius.tex): the law of `G_1 + G_2`
for independent geometric counts is the convolution
`∑_{i ≤ k} p(1-p)^i p(1-p)^{k-i} = (k+1) p^2 (1-p)^k`. -/
theorem convolution_geometric (p : ℝ) (k : ℕ) :
    ∑ i ∈ range (k + 1), p * (1 - p) ^ i * (p * (1 - p) ^ (k - i)) =
      (k + 1) * p ^ 2 * (1 - p) ^ k := by
  have h : ∀ i ∈ range (k + 1), p * (1 - p) ^ i * (p * (1 - p) ^ (k - i)) =
      p ^ 2 * (1 - p) ^ k := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [show p * (1 - p) ^ i * (p * (1 - p) ^ (k - i)) =
      p ^ 2 * ((1 - p) ^ i * (1 - p) ^ (k - i)) by ring, ← pow_add, Nat.add_sub_cancel' hik]
  rw [sum_congr rfl h, sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

/-- Paper: `lem:productaritylaw` (tanh_large_radius.tex): the generating function
of `G_1 + G_2` is `p^2/(1 - (1-p)v)^2`. -/
theorem hasSum_negativeBinomialTwo (p v : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hv : |v| ≤ 1) :
    HasSum (fun k : ℕ => (k + 1) * p ^ 2 * (1 - p) ^ k * v ^ k)
      (negativeBinomialTwoPGF p v) := by
  have hr : ‖(1 - p) * v‖ < 1 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith)]
    nlinarith [abs_nonneg v]
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one 1 hr).mul_left (p ^ 2)
  unfold negativeBinomialTwoPGF geometricPGF
  convert h using 1
  · funext k
    rw [Nat.choose_one_right, mul_pow]
    push_cast
    ring
  · rw [div_pow, one_div, div_eq_mul_inv]

/-- Paper: `lem:productaritylaw` (tanh_large_radius.tex): the zero-count mass is
`p^2`. -/
theorem negativeBinomialTwo_zero_mass (p : ℝ) : negativeBinomialTwoPGF p 0 = p ^ 2 := by
  simp [negativeBinomialTwoPGF, geometricPGF]

/-- Paper: `lem:productaritylaw` (tanh_large_radius.tex): the generating function
is normalized at `v = 1`. -/
theorem negativeBinomialTwo_normalizes (p : ℝ) (hp : p ≠ 0) :
    negativeBinomialTwoPGF p 1 = 1 := by
  simp [negativeBinomialTwoPGF, geometricPGF, hp]

/-- Paper: proof of `lem:productaritylaw` (tanh_large_radius.tex): with
`p = 1/(1+a)` each factor `{1 + a(1-v)}^{-2}` of the cosine product is the
generating function of `G_1 + G_2`. -/
theorem product_factor_pgf (a v : ℝ) (ha : 1 + a ≠ 0) :
    negativeBinomialTwoPGF (1 / (1 + a)) v = 1 / (1 + a * (1 - v)) ^ 2 := by
  have hinner : 1 - (1 - 1 / (1 + a)) * v = (1 + a * (1 - v)) / (1 + a) := by
    field_simp
    ring
  unfold negativeBinomialTwoPGF geometricPGF
  rw [hinner, div_div_div_cancel_right₀ ha, one_div, inv_pow]
  rw [one_div]

/-- Paper: proof of `lem:producttail` (tanh_large_radius.tex): with
`H = max{1, u}` and `J = ⌈H⌉`, `J ≤ 2H`, `Λ = 2u^2/J ≤ 2H`, and the Poisson
parameters `2u^2/J^2 ≤ 2`. -/
theorem tail_budget (u : ℝ) (hu : 0 < u) :
    (⌈max 1 u⌉₊ : ℝ) ≤ 2 * max 1 u ∧ 2 * u ^ 2 / (⌈max 1 u⌉₊ : ℝ) ≤ 2 * max 1 u ∧
      2 * u ^ 2 / (⌈max 1 u⌉₊ : ℝ) ^ 2 ≤ 2 := by
  set H := max 1 u with hH
  have hH1 : 1 ≤ H := le_max_left _ _
  have huH : u ≤ H := le_max_right _ _
  have hJ1 : H ≤ (⌈H⌉₊ : ℝ) := Nat.le_ceil H
  have hJ2 : (⌈H⌉₊ : ℝ) < H + 1 := Nat.ceil_lt_add_one (by linarith)
  have hJ0 : (0 : ℝ) < ⌈H⌉₊ := by linarith
  refine ⟨by linarith, ?_, ?_⟩
  · rw [div_le_iff₀ hJ0]
    nlinarith
  · rw [div_le_iff₀ (by positivity)]
    nlinarith

/-- Paper: `lem:producttail` (tanh_large_radius.tex), the conditional sampler at
the level of probability mass functions. For `k ≥ 1`,
`P(G_1 + G_2 = k | G_1 + G_2 > 0) = (1/(1+p)) P(1 + G_1 + G_2 = k) +
(p/(1+p)) P(1 + G_2 = k)`, with `P(G_1 + G_2 = k) = (k+1) p^2 (1-p)^k`. -/
theorem conditional_positive_sampler (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (k : ℕ) :
    ((k + 1 + 1 : ℕ) : ℝ) * p ^ 2 * (1 - p) ^ (k + 1) / (1 - p ^ 2) =
      1 / (1 + p) * (((k + 1 : ℕ) : ℝ) * p ^ 2 * (1 - p) ^ k) +
        p / (1 + p) * (p * (1 - p) ^ k) := by
  have h1 : 1 - p ≠ 0 := by linarith
  have h2 : 1 + p ≠ 0 := by linarith
  rw [show 1 - p ^ 2 = (1 - p) * (1 + p) by ring, pow_succ]
  push_cast
  field_simp
  ring

/-- Paper: proof of `lem:producttail` (tanh_large_radius.tex): the two
conditional mixture weights are valid and sum to one. -/
theorem positive_negative_binomial_weights (p : ℝ) (hp0 : 0 ≤ p) :
    0 ≤ p / (1 + p) ∧ 0 ≤ 1 / (1 + p) ∧ p / (1 + p) + 1 / (1 + p) = 1 := by
  have h : 0 < 1 + p := by linarith
  refine ⟨by positivity, by positivity, ?_⟩
  field_simp
  ring

/-- Paper: `lem:producttail` (tanh_large_radius.tex), the same mixture at the
level of generating functions: conditional on positivity, an `NB(2,p)` count is
`1 + G` with probability `p/(1+p)` and `1 + NB(2,p)` with probability `1/(1+p)`. -/
theorem positive_negative_binomial_mixture (p v : ℝ)
    (hden : 1 - (1 - p) * v ≠ 0) (hpositive : 1 - p ^ 2 ≠ 0) (hplus : 1 + p ≠ 0) :
    (negativeBinomialTwoPGF p v - p ^ 2) / (1 - p ^ 2) =
      (p / (1 + p)) * v * geometricPGF p v +
      (1 / (1 + p)) * v * negativeBinomialTwoPGF p v := by
  unfold negativeBinomialTwoPGF geometricPGF
  field_simp
  ring

/-- Paper: proof of `lem:producttail` (tanh_large_radius.tex): removing the
zero atom of mass `p^2` and adding it back restores the generating function. -/
theorem conditioning_mixture_restores_pgf (p v : ℝ) (hpositive : 1 - p ^ 2 ≠ 0) :
    p ^ 2 + (1 - p ^ 2) * ((negativeBinomialTwoPGF p v - p ^ 2) / (1 - p ^ 2)) =
      negativeBinomialTwoPGF p v := by
  field_simp
  ring

end ExactSampling.ProductAritySampler
