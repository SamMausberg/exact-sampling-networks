import Mathlib

/-!
# The sharp normalization obstruction and the geometric-majority sampler

This module formalizes `thm:rmscontextlaw`, `lem:rmsgeommajority` and `cor:rmsfixedgrid`
(normalization_obstruction.tex), including the weighted Jensen inequality
`eq:rmsweightedjensen` and the score bound `eq:rmsscorelower`.

Formalized here:
* Rademacher averages on the sign cube `{-1,1}^T`: `𝔼 M² = 1/T`, `𝔼 M⁴ = (3T-2)/T³ ≤ 3/T²`,
  and the derivative identity `H'(0) = T 𝔼₀[M g(M)]` for the output mean
  `H(t) = 𝔼_t g(M)` under independent signs of common mean `t`;
* the weighted Jensen inequality `eq:rmsweightedjensen` for finite laws;
* the width-two family: the normalized coordinate, the bound `M f_ε(M) ≥ M²/(8√(2ε+c²+M²))`,
  the score bound `H'(0) ≥ 1/(8√(2ε+c²+3/T))`, and `eq:rmsscorelower`; the assembled lower
  bound `E₀Q ≥ min{T, ε⁻¹}/384` from the transcript inequality;
* the geometric-majority identity of `lem:rmsgeommajority` in full: the majority mean `M_k`
  is defined from the binomial law of `2k+1` independent signs, its derivative is
  `C_k (1-z²)^k` with `C_k = (2k+1) C(2k,k) 4^{-k} = (3/2)_k / k!`, and
  `∑_k Pr(K=k) M_k(z) = z √(1+θ)/√(θ+z²)` for `|z| ≤ 1`; the arity `1 + 2/θ`;
* the two-category softmax with opposite logits `±ℓ`, whose sign mean is `tanh ℓ`;
* the upper-bound arithmetic of `thm:rmscontextlaw` (`4e²(1 + 2/θ) ≤ 64 ε⁻¹`, and the choice
  between scan and sampler giving `64 min{T, ε⁻¹}` for `0 ≤ ε`, with `ε⁻¹ = +∞` at zero) and the
  numerical content of `cor:rmsfixedgrid` (radicand, sentinel average, score,
  `min{T, ε⁻¹}/128`, `24/ε`, and `32 min{T, ε⁻¹}`).

Stand-in hypothesis: the finite transcript inequality `E₀Q ≥ H'(0)²` of `lem:transcript`
(tanh_lower.tex), which is the information bound imported by these lower bounds. It is used
only in `context_query_lower` and `fixed_grid_query_lower`, as an explicit hypothesis.

Not formalized: the exact-sampling query model itself; the tanh factory of `lem:unittanhfour`
(tanh_large_radius.tex), which enters only through its expected source counts (at most `2`,
used as `2e` per factory in `upper_count`, and fewer than `16` for the two factories in
`fixed_grid_upper_count`); the scan algorithm, which enters only through its count `T`; and
every bit-complexity estimate.
-/

open Real Finset Polynomial
open scoped BigOperators

namespace ExactSampling.RMSContextLaw

/-! ## Elementary bounds for `tanh` -/

/-- `tanh` is nonnegative on `[0, ∞)`. -/
theorem tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ tanh x := by
  rw [tanh_eq_sinh_div_cosh]; exact div_nonneg (sinh_nonneg_iff.2 hx) (cosh_pos x).le

/-- `tanh` is odd. -/
theorem tanh_odd (x : ℝ) : tanh (-x) = -tanh x := Real.tanh_neg x

/-- `tanh y ≥ y/√(1+y²)` for `y ≥ 0`, since `sinh y ≥ y`. -/
theorem div_sqrt_le_tanh {y : ℝ} (hy : 0 ≤ y) : y / √(1 + y ^ 2) ≤ tanh y := by
  rw [tanh_eq_sinh_div_cosh]
  have hs : y ≤ sinh y := self_le_sinh_iff.2 hy
  have hc : cosh y = √(1 + sinh y ^ 2) := by
    rw [← cosh_sq', sqrt_sq (cosh_pos y).le]
  have hS : 0 < √(1 + y ^ 2) := sqrt_pos.2 (by positivity)
  rw [div_le_div_iff₀ hS (cosh_pos y), hc]
  have h1 : y * √(1 + sinh y ^ 2) = √((y * √(1 + sinh y ^ 2)) ^ 2) :=
    (sqrt_sq (by positivity)).symm
  have h2 : sinh y * √(1 + y ^ 2) = √((sinh y * √(1 + y ^ 2)) ^ 2) :=
    (sqrt_sq (mul_nonneg (by linarith) hS.le)).symm
  rw [h1, h2]
  apply sqrt_le_sqrt
  rw [mul_pow, mul_pow, sq_sqrt (by positivity), sq_sqrt (by positivity)]
  nlinarith [mul_le_mul hs hs hy (by linarith : 0 ≤ sinh y)]

/-- `tanh u ≥ u/2` for `0 ≤ u ≤ 1`.
Paper: proof of `thm:rmscontextlaw` (normalization_obstruction.tex). -/
theorem half_le_tanh {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : u / 2 ≤ tanh u := by
  refine le_trans ?_ (div_sqrt_le_tanh h0)
  have hS : 0 < √(1 + u ^ 2) := sqrt_pos.2 (by positivity)
  have hS2 : √(1 + u ^ 2) ≤ 2 := by
    rw [sqrt_le_left (by norm_num)]; nlinarith
  exact div_le_div_of_nonneg_left h0 hS hS2

/-- `tanh ≤ 1`. -/
theorem tanh_le_one (x : ℝ) : tanh x ≤ 1 := (Real.tanh_lt_one x).le

/-- The composite bound `tanh(tanh x) ≥ x/4` on `[0, 1]`. -/
theorem quarter_le_tanh_tanh {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : x / 4 ≤ tanh (tanh x) := by
  have ha := half_le_tanh h0 h1
  have hb := half_le_tanh (tanh_nonneg h0) (tanh_le_one x)
  linarith

/-! ## Sign vectors and Rademacher averages -/

/-- The sign `±1` of a bit. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The sum of the signs of a vector in `{-1,1}^T`. -/
def sgnSum {T : ℕ} (x : Fin T → Bool) : ℝ := ∑ i, sgn (x i)

/-- The likelihood `∏ (1 + t x_i)/2` of a sign vector under independent signs of mean `t`. -/
noncomputable def lik {T : ℕ} (t : ℝ) (x : Fin T → Bool) : ℝ := ∏ i, (1 + t * sgn (x i)) / 2

/-- Splitting off the first sign of a sign vector. -/
theorem sum_cons {T : ℕ} (F : ℝ → ℝ) :
    ∑ x : Fin (T + 1) → Bool, F (sgnSum x)
      = ∑ y : Fin T → Bool, (F (1 + sgnSum y) + F (-1 + sgnSum y)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (T + 1) => Bool)).sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro y _
  simp [sgnSum, Fin.sum_univ_succ, Fin.consEquiv, sgn]

/-- There are `2^T` sign vectors. -/
theorem sum_one_signs (T : ℕ) : ∑ _x : Fin T → Bool, (1 : ℝ) = 2 ^ T := by simp

/-- `∑_x (∑_i x_i)² = T 2^T` over `{-1,1}^T`. -/
theorem sum_sq_signs (T : ℕ) : ∑ x : Fin T → Bool, sgnSum x ^ 2 = T * 2 ^ T := by
  induction T with
  | zero => simp [sgnSum]
  | succ T ih =>
    rw [sum_cons (fun s => s ^ 2)]
    have : ∀ y : Fin T → Bool, (1 + sgnSum y) ^ 2 + (-1 + sgnSum y) ^ 2
        = 2 * sgnSum y ^ 2 + 2 * 1 := by intro y; ring
    simp only [this, sum_add_distrib, ← mul_sum, ih, sum_one_signs]
    push_cast; ring

/-- `∑_x (∑_i x_i)⁴ = (3T² - 2T) 2^T` over `{-1,1}^T`. -/
theorem sum_four_signs (T : ℕ) :
    ∑ x : Fin T → Bool, sgnSum x ^ 4 = (3 * T ^ 2 - 2 * T) * 2 ^ T := by
  induction T with
  | zero => simp [sgnSum]
  | succ T ih =>
    rw [sum_cons (fun s => s ^ 4)]
    have : ∀ y : Fin T → Bool, (1 + sgnSum y) ^ 4 + (-1 + sgnSum y) ^ 4
        = 2 * sgnSum y ^ 4 + 12 * sgnSum y ^ 2 + 2 * 1 := by intro y; ring
    simp only [this, sum_add_distrib, ← mul_sum, ih, sum_sq_signs, sum_one_signs]
    push_cast; ring

/-- For independent fair signs, the average `M = T⁻¹ ∑ x_i` has `𝔼 M² = 1/T`.
Paper: proof of `thm:rmscontextlaw` (normalization_obstruction.tex). -/
theorem rademacher_second_moment {T : ℕ} (hT : 1 ≤ T) :
    (1 / 2 ^ T) * ∑ x : Fin T → Bool, (sgnSum x / T) ^ 2 = 1 / T := by
  have hT' : (T : ℝ) ≠ 0 := by positivity
  simp only [div_pow, ← sum_div, sum_sq_signs]
  field_simp

/-- For independent fair signs, `𝔼 M⁴ = (3T-2)/T³`.
Paper: proof of `thm:rmscontextlaw` (normalization_obstruction.tex). -/
theorem rademacher_fourth_moment {T : ℕ} (hT : 1 ≤ T) :
    (1 / 2 ^ T) * ∑ x : Fin T → Bool, (sgnSum x / T) ^ 4 = (3 * T - 2) / T ^ 3 := by
  have hT' : (T : ℝ) ≠ 0 := by positivity
  simp only [div_pow, ← sum_div, sum_four_signs]
  field_simp

/-- The upper bound `(3T - 2)/T³ ≤ 3/T²`.
Paper: proof of `thm:rmscontextlaw` (normalization_obstruction.tex). -/
theorem fourth_moment_upper (T : ℝ) (hT : 0 < T) : (3 * T - 2) / T ^ 3 ≤ 3 / T ^ 2 := by
  apply (div_le_div_iff₀ (pow_pos hT 3) (pow_pos hT 2)).2
  nlinarith [sq_nonneg T]

/-- The rescaled second moment: if `𝔼 S² = T` then `𝔼 (S/T)² = 1/T`. -/
theorem second_moment_of_scaled_sum (s T : ℝ) (hT : T ≠ 0) (hs : s = T) : s / T ^ 2 = 1 / T := by
  subst s
  field_simp

/-- The derivative of the likelihood at `t = 0` is `(∑ x_i)/2^T`. -/
theorem hasDerivAt_lik {T : ℕ} (x : Fin T → Bool) :
    HasDerivAt (fun t => lik t x) (sgnSum x / 2 ^ T) 0 := by
  unfold lik
  have h : ∀ i ∈ (univ : Finset (Fin T)),
      HasDerivAt (fun t => (1 + t * sgn (x i)) / 2) (sgn (x i) / 2) 0 := by
    intro i _
    have := ((hasDerivAt_id (0 : ℝ)).mul_const (sgn (x i))).const_add 1
    simpa using this.div_const 2
  have := HasDerivAt.finsetProd h
  convert this using 1
  · funext t; simp [Finset.prod_apply]
  · simp only [smul_eq_mul]
    rw [sgnSum, sum_div]
    apply sum_congr rfl
    intro i _
    have : ∏ j ∈ univ.erase i, (1 + 0 * sgn (x j)) / 2 = (1 / 2) ^ (T - 1) := by
      simp [prod_const, card_erase_of_mem (mem_univ i)]
    rw [this]
    have hT : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact Fin.elim0 i)
    rw [show (2 : ℝ) ^ T = 2 ^ (T - 1) * 2 by rw [← pow_succ, Nat.sub_add_cancel hT],
      one_div_pow]
    field_simp

/-- Differentiating the finite input distribution at `t = 0`: if the inputs are independent
signs of common mean `t` and the output sign has conditional mean `g(M)`, then
`H'(0) = T 𝔼₀[M g(M)]`.
Paper: proofs of `thm:rmscontextlaw`, `cor:rmsfixedgrid` (normalization_obstruction.tex). -/
theorem hasDerivAt_signMean {T : ℕ} (g : ℝ → ℝ) :
    HasDerivAt (fun t => ∑ x : Fin T → Bool, lik t x * g (sgnSum x / T))
      (T * ((1 / 2 ^ T) * ∑ x : Fin T → Bool, (sgnSum x / T) * g (sgnSum x / T))) 0 := by
  have h := HasDerivAt.fun_sum (u := (univ : Finset (Fin T → Bool)))
    (fun x _ => (hasDerivAt_lik x).mul_const (g (sgnSum x / T)))
  convert h using 1
  rw [mul_sum, mul_sum]
  apply sum_congr rfl
  intro x _
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT; simp [sgnSum]
  · have : (T : ℝ) ≠ 0 := by positivity
    field_simp

/-! ## Weighted Jensen (`eq:rmsweightedjensen`) -/

/-- The tangent-line inequality for `t ↦ t^{-1/2}`. -/
theorem inv_sqrt_tangent {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    1 / √B - (A - B) / (2 * B * √B) ≤ 1 / √A := by
  have hx0 : 0 < √A := sqrt_pos.2 hA
  have hy0 : 0 < √B := sqrt_pos.2 hB
  have hA' : A = √A ^ 2 := (sq_sqrt hA.le).symm
  have hB' : B = √B ^ 2 := (sq_sqrt hB.le).symm
  generalize √A = x at *
  generalize √B = y at *
  subst hA' hB'
  have key : 1 / x - (1 / y - (x ^ 2 - y ^ 2) / (2 * y ^ 2 * y))
      = (x - y) ^ 2 * (x + 2 * y) / (2 * x * y ^ 3) := by
    field_simp; ring
  have : 0 ≤ (x - y) ^ 2 * (x + 2 * y) / (2 * x * y ^ 3) := by positivity
  linarith

/-- Jensen's inequality for the convex function `t ↦ (a+t)^{-1/2}` and a finite law. -/
theorem jensen_inv_sqrt {ι : Type*} (s : Finset ι) (w Z : ι → ℝ) (a : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) (hZ : ∀ i ∈ s, 0 < a + Z i) :
    1 / √(a + ∑ i ∈ s, w i * Z i) ≤ ∑ i ∈ s, w i * (1 / √(a + Z i)) := by
  set m := ∑ i ∈ s, w i * Z i
  have hB : 0 < a + m := by
    have : a + m = ∑ i ∈ s, w i * (a + Z i) := by
      simp only [m, mul_add, sum_add_distrib, ← sum_mul, hw1]; ring
    rw [this]
    obtain ⟨i, hi, hwi⟩ : ∃ i ∈ s, 0 < w i := by
      by_contra h
      push Not at h
      have : ∑ i ∈ s, w i ≤ 0 := sum_nonpos h
      linarith
    exact lt_of_lt_of_le (mul_pos hwi (hZ i hi))
      (single_le_sum (f := fun i => w i * (a + Z i))
        (fun j hj => mul_nonneg (hw j hj) (hZ j hj).le) hi)
  have hstep : ∀ i ∈ s, w i * (1 / √(a + m) - ((a + Z i) - (a + m)) / (2 * (a + m) * √(a + m)))
      ≤ w i * (1 / √(a + Z i)) := fun i hi =>
    mul_le_mul_of_nonneg_left (inv_sqrt_tangent (hZ i hi) hB) (hw i hi)
  have hsum := sum_le_sum hstep
  have hlhs : ∑ i ∈ s, w i * (1 / √(a + m) - ((a + Z i) - (a + m)) / (2 * (a + m) * √(a + m)))
      = 1 / √(a + m) := by
    have : ∀ i ∈ s, w i * (1 / √(a + m) - ((a + Z i) - (a + m)) / (2 * (a + m) * √(a + m)))
        = w i * (1 / √(a + m) + m / (2 * (a + m) * √(a + m)))
          - (w i * Z i) * (1 / (2 * (a + m) * √(a + m))) := by
      intro i _; ring
    rw [sum_congr rfl this, sum_sub_distrib, ← sum_mul, ← sum_mul, hw1]
    ring
  rw [hlhs] at hsum
  exact hsum

/-- Weighted Jensen: for `Z ≥ 0` with positive mean and `a > 0`,
`𝔼[Z/√(a+Z)] ≥ 𝔼Z / √(a + 𝔼Z²/𝔼Z)`, for a finite family of nonnegative weights.
Paper: `eq:rmsweightedjensen` (normalization_obstruction.tex). -/
theorem weighted_jensen {ι : Type*} (s : Finset ι) (p Z : ι → ℝ) (a : ℝ) (ha : 0 < a)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hZ : ∀ i ∈ s, 0 ≤ Z i) (hEZ : 0 < ∑ i ∈ s, p i * Z i) :
    (∑ i ∈ s, p i * Z i) / √(a + (∑ i ∈ s, p i * Z i ^ 2) / ∑ i ∈ s, p i * Z i)
      ≤ ∑ i ∈ s, p i * (Z i / √(a + Z i)) := by
  set E := ∑ i ∈ s, p i * Z i
  have hJ := jensen_inv_sqrt s (fun i => p i * Z i / E) Z a
    (fun i hi => div_nonneg (mul_nonneg (hp i hi) (hZ i hi)) hEZ.le)
    (by rw [← sum_div]; exact div_self hEZ.ne')
    (fun i hi => by linarith [hZ i hi])
  have h1 : ∑ i ∈ s, p i * Z i / E * Z i = (∑ i ∈ s, p i * Z i ^ 2) / E := by
    rw [sum_div]; apply sum_congr rfl; intro i _; ring
  have h2 : ∑ i ∈ s, p i * Z i / E * (1 / √(a + Z i))
      = (∑ i ∈ s, p i * (Z i / √(a + Z i))) / E := by
    rw [sum_div]; apply sum_congr rfl; intro i _; ring
  rw [h1, h2, le_div_iff₀ hEZ] at hJ
  calc E / √(a + (∑ i ∈ s, p i * Z i ^ 2) / E)
      = 1 / √(a + (∑ i ∈ s, p i * Z i ^ 2) / E) * E := by ring
    _ ≤ _ := hJ

/-- Jensen applied to `Z = M²` for a Rademacher average: if `M x · g(M x) ≥ κ M²/√(a + M²)`
pointwise, then `T 𝔼₀[M g(M)] ≥ κ / √(a + 3/T)`. -/
theorem score_from_pointwise {T : ℕ} (hT : 1 ≤ T) (g : ℝ → ℝ) {a κ : ℝ} (ha : 0 < a)
    (hκ : 0 ≤ κ) (hpt : ∀ M : ℝ, κ * (M ^ 2 / √(a + M ^ 2)) ≤ M * g M) :
    κ / √(a + 3 / T)
      ≤ T * ((1 / 2 ^ T) * ∑ x : Fin T → Bool, (sgnSum x / T) * g (sgnSum x / T)) := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  set p : (Fin T → Bool) → ℝ := fun _ => 1 / 2 ^ T
  set Z : (Fin T → Bool) → ℝ := fun x => (sgnSum x / T) ^ 2
  have hEZ : ∑ x, p x * Z x = 1 / T := by
    simp only [p, Z, ← mul_sum]; exact rademacher_second_moment hT
  have hEZ2 : ∑ x, p x * Z x ^ 2 = (3 * T - 2) / T ^ 3 := by
    simp only [p, Z, ← mul_sum, ← pow_mul]; exact rademacher_fourth_moment hT
  have hJ := weighted_jensen univ p Z a ha (fun _ _ => by positivity) (fun _ _ => sq_nonneg _)
    (by rw [hEZ]; positivity)
  rw [hEZ, hEZ2] at hJ
  have hratio : (3 * (T : ℝ) - 2) / T ^ 3 / (1 / T) ≤ 3 / T := by
    have e : (3 * (T : ℝ) - 2) / T ^ 3 / (1 / T) = (3 * T - 2) / T ^ 2 := by
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) hTpos]
    nlinarith
  have hsq : √(a + (3 * (T : ℝ) - 2) / T ^ 3 / (1 / T)) ≤ √(a + 3 / T) :=
    sqrt_le_sqrt (by linarith)
  have hpos1 : 0 < √(a + (3 * (T : ℝ) - 2) / T ^ 3 / (1 / T)) := by
    apply sqrt_pos.2
    have : 0 ≤ (3 * (T : ℝ) - 2) / T ^ 3 / (1 / T) := by
      apply div_nonneg (div_nonneg (by linarith) (by positivity)) (by positivity)
    linarith
  have hJ' : 1 / T / √(a + 3 / T) ≤ ∑ x, p x * (Z x / √(a + Z x)) :=
    le_trans (div_le_div_of_nonneg_left (by positivity) hpos1 hsq) hJ
  have hpt' : ∀ x, κ * (p x * (Z x / √(a + Z x)))
      ≤ p x * ((sgnSum x / T) * g (sgnSum x / T)) := by
    intro x
    have := hpt (sgnSum x / T)
    have hp0 : 0 ≤ p x := by positivity
    calc κ * (p x * (Z x / √(a + Z x))) = p x * (κ * ((sgnSum x / T) ^ 2
          / √(a + (sgnSum x / T) ^ 2))) := by simp only [Z]; ring
      _ ≤ p x * ((sgnSum x / T) * g (sgnSum x / T)) := mul_le_mul_of_nonneg_left this hp0
  have hsum := sum_le_sum (fun x (_ : x ∈ univ) => hpt' x)
  rw [← mul_sum] at hsum
  have hfinal : κ * (1 / T / √(a + 3 / T)) ≤ ∑ x, p x * ((sgnSum x / T) * g (sgnSum x / T)) :=
    le_trans (mul_le_mul_of_nonneg_left hJ' hκ) hsum
  have hrw : ∑ x, p x * ((sgnSum x / T) * g (sgnSum x / T))
      = (1 / 2 ^ T) * ∑ x : Fin T → Bool, (sgnSum x / T) * g (sgnSum x / T) := by
    simp only [p, ← mul_sum]
  rw [hrw] at hfinal
  have hs : 0 < √(a + 3 / T) := sqrt_pos.2 (by positivity)
  calc κ / √(a + 3 / T) = T * (κ * (1 / T / √(a + 3 / T))) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hfinal hTpos.le

/-! ## The width-two family (`thm:rmscontextlaw`) -/

/-- The target sign mean `f_ε(M) = tanh(tanh(M / (√2 √(2ε + c² + M²))))` of the width-two block.
Paper: `eq:rmsfamilymean` (normalization_obstruction.tex). -/
noncomputable def familyMean (ε c M : ℝ) : ℝ := tanh (tanh (M / (√2 * √(2 * ε + c ^ 2 + M ^ 2))))

/-- Two output categories `Y = ±1` with opposite logits `±ℓ` have softmax probabilities
`e^{±ℓ}/(e^ℓ + e^{-ℓ})`, so `𝔼Y = (e^ℓ - e^{-ℓ})/(e^ℓ + e^{-ℓ}) = tanh ℓ`.
Paper: `eq:rmsfamilymean` in the proof of `thm:rmscontextlaw`; proof of `cor:rmsfixedgrid`
(normalization_obstruction.tex). -/
theorem opposite_logits_mean (l : ℝ) :
    exp l / (exp l + exp (-l)) * 1 + exp (-l) / (exp l + exp (-l)) * (-1) = tanh l := by
  rw [tanh_eq_sinh_div_cosh, sinh_eq, cosh_eq]
  have h : 0 < exp l + exp (-l) := by positivity
  field_simp
  ring

/-- The target mean `eq:rmsfamilymean` is the opposite-logit softmax mean at the tanh-row
output `ℓ = tanh(M / (√2 √(2ε + c² + M²)))`.
Paper: `eq:rmsfamilymean` (normalization_obstruction.tex). -/
theorem familyMean_eq_softmax (ε c M : ℝ) :
    familyMean ε c M = exp (tanh (M / (√2 * √(2 * ε + c ^ 2 + M ^ 2))))
        / (exp (tanh (M / (√2 * √(2 * ε + c ^ 2 + M ^ 2))))
          + exp (-tanh (M / (√2 * √(2 * ε + c ^ 2 + M ^ 2))))) * 1
      + exp (-tanh (M / (√2 * √(2 * ε + c ^ 2 + M ^ 2))))
        / (exp (tanh (M / (√2 * √(2 * ε + c ^ 2 + M ^ 2))))
          + exp (-tanh (M / (√2 * √(2 * ε + c ^ 2 + M ^ 2))))) * (-1) := by
  rw [opposite_logits_mean]; rfl

/-- The width-two normalization of `a = (M, c)` with stabilizer `ε`, followed by a tanh row of
coefficient `1/2`, has argument `M / (√2 √(2ε + c² + M²))`.
Paper: `eq:rmsfamilymean` (normalization_obstruction.tex), with `eq:rmsdefinition`
(normalization_floor.tex). -/
theorem width_two_argument {ε c M : ℝ} (hpos : 0 < 2 * ε + c ^ 2 + M ^ 2) :
    (1 / 2) * (M / √(ε + (M ^ 2 + c ^ 2) / 2)) = M / (√2 * √(2 * ε + c ^ 2 + M ^ 2)) := by
  have h : ε + (M ^ 2 + c ^ 2) / 2 = (2 * ε + c ^ 2 + M ^ 2) / 2 := by ring
  rw [h, sqrt_div hpos.le]
  have h2 : (0 : ℝ) < √2 := by positivity
  have hs : 0 < √(2 * ε + c ^ 2 + M ^ 2) := sqrt_pos.2 hpos
  field_simp
  rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- The normalization denominator is positive thanks to the sentinel `c > 0`.
Paper: `thm:rmscontextlaw` (normalization_obstruction.tex). -/
theorem normalization_denominator_positive (eps c m : ℝ) (heps : 0 ≤ eps) (hc : 0 < c) :
    0 < 2 * eps + c ^ 2 + m ^ 2 := by
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  nlinarith [sq_nonneg m]

/-- The squared inner argument is at most `1/2`.
Paper: proof of `thm:rmscontextlaw` (normalization_obstruction.tex). -/
theorem rms_argument_square_bound (theta z : ℝ) (ht : 0 < theta) :
    z ^ 2 / (2 * (theta + z ^ 2)) ≤ 1 / 2 := by
  have hd : 0 < 2 * (theta + z ^ 2) := by nlinarith [sq_nonneg z]
  apply (div_le_iff₀ hd).2
  nlinarith

/-- The inner argument has absolute value at most `1/√2`.
Paper: proof of `thm:rmscontextlaw` (normalization_obstruction.tex). -/
theorem inner_argument_le {θ M : ℝ} (hθ : 0 < θ) :
    |M / (√2 * √(θ + M ^ 2))| ≤ 1 / √2 := by
  have hs : 0 < √(θ + M ^ 2) := sqrt_pos.2 (by positivity)
  have h2 : (0 : ℝ) < √2 := by positivity
  rw [abs_div, abs_of_pos (mul_pos h2 hs), div_le_div_iff₀ (mul_pos h2 hs) h2]
  have : |M| ≤ √(θ + M ^ 2) := by
    rw [← sqrt_sq_eq_abs]; exact sqrt_le_sqrt (by linarith)
  nlinarith

/-- The pointwise bound `M f_ε(M) ≥ M²/(8√(2ε+c²+M²))`, from `tanh u ≥ u/2` on `[0,1]` and
oddness.
Paper: proof of `thm:rmscontextlaw` (normalization_obstruction.tex). -/
theorem mul_familyMean_ge {ε c : ℝ} (hε : 0 ≤ ε) (hc : 0 < c) (M : ℝ) :
    (1 / 8) * (M ^ 2 / √(2 * ε + c ^ 2 + M ^ 2)) ≤ M * familyMean ε c M := by
  have hθ : 0 < 2 * ε + c ^ 2 := by positivity
  have hx1 : |M| / (√2 * √(2 * ε + c ^ 2 + M ^ 2)) ≤ 1 := by
    have := inner_argument_le (M := |M|) hθ
    rw [sq_abs] at this
    have h2 : (0 : ℝ) < √2 := by positivity
    have h12 : 1 / √2 ≤ 1 := by
      rw [div_le_one h2]; nlinarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h0 : 0 ≤ |M| / (√2 * √(2 * ε + c ^ 2 + M ^ 2)) := by positivity
    rw [abs_of_nonneg h0] at this
    linarith
  unfold familyMean
  set S := 2 * ε + c ^ 2 + M ^ 2 with hSdef
  have hs : 0 < √S := sqrt_pos.2 (by rw [hSdef]; positivity)
  have h2 : (0 : ℝ) < √2 := by positivity
  have h2le : √2 ≤ 2 := by rw [sqrt_le_left (by norm_num)]; norm_num
  set x := |M| / (√2 * √S) with hx
  have hx0 : 0 ≤ x := by positivity
  have hkey : |M| * (x / 4) ≤ M * tanh (tanh (M / (√2 * √S))) := by
    rcases le_total 0 M with hM | hM
    · have hxM : x = M / (√2 * √S) := by rw [hx, abs_of_nonneg hM]
      rw [abs_of_nonneg hM, ← hxM]
      exact mul_le_mul_of_nonneg_left (quarter_le_tanh_tanh hx0 hx1) hM
    · have hneg : M / (√2 * √S) = -x := by rw [hx, abs_of_nonpos hM]; ring
      rw [abs_of_nonpos hM, hneg, tanh_odd, tanh_odd]
      have := quarter_le_tanh_tanh hx0 hx1
      nlinarith
  have hMM : |M| * |M| = M ^ 2 := by rw [← sq, sq_abs]
  have e : |M| * (x / 4) = M ^ 2 / (4 * √2 * √S) := by
    rw [hx, ← hMM]; field_simp
  have e2 : (1 / 8) * (M ^ 2 / √S) = M ^ 2 / (8 * √S) := by field_simp
  have hcalc : (1 / 8) * (M ^ 2 / √S) ≤ |M| * (x / 4) := by
    rw [e, e2]
    apply div_le_div_of_nonneg_left (sq_nonneg M) (by positivity)
    nlinarith
  linarith

/-- The score bound `H'(0) = T 𝔼₀[M f_ε(M)] ≥ 1/(8√(2ε + c² + 3/T))`.
Paper: proof of `thm:rmscontextlaw` (normalization_obstruction.tex), with
`eq:rmsweightedjensen`. -/
theorem family_score_lower {T : ℕ} (hT : 1 ≤ T) {ε c : ℝ} (hε : 0 ≤ ε) (hc : 0 < c) :
    1 / (8 * √(2 * ε + c ^ 2 + 3 / T))
      ≤ T * ((1 / 2 ^ T) * ∑ x : Fin T → Bool,
          (sgnSum x / T) * familyMean ε c (sgnSum x / T)) := by
  have h := score_from_pointwise hT (familyMean ε c) (a := 2 * ε + c ^ 2) (κ := 1 / 8)
    (by positivity) (by norm_num) (fun M => by
      have := mul_familyMean_ge hε hc M
      rwa [show 2 * ε + c ^ 2 + M ^ 2 = (2 * ε + c ^ 2) + M ^ 2 by ring] at this)
  have hs : 0 < √(2 * ε + c ^ 2 + 3 / T) := sqrt_pos.2 (by positivity)
  calc 1 / (8 * √(2 * ε + c ^ 2 + 3 / T)) = 1 / 8 / √(2 * ε + c ^ 2 + 3 / T) := by
        field_simp
    _ ≤ _ := h

/-- With `c ≤ 1/T` and `T ≥ 1`, the sentinel satisfies `c² ≤ 1/T`.
Paper: proof of `thm:rmscontextlaw` (normalization_obstruction.tex), after `eq:rmsscorelower`. -/
theorem sentinel_floor (T c : ℝ) (hT : 1 ≤ T) (hc : 0 ≤ c) (hcT : c ≤ 1 / T) :
    c ^ 2 ≤ 1 / T := by
  have hTp : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hti1 : 1 / T ≤ 1 := by rw [div_le_iff₀ hTp]; linarith
  have hc1 : c ≤ 1 := le_trans hcT hti1
  nlinarith

/-- For `ε ≤ 1/T` and `c² ≤ 1/T`: `2ε + c² + 3/T ≤ 6/T`.
Paper: after `eq:rmsscorelower` (normalization_obstruction.tex). -/
theorem small_epsilon_denominator (T eps c : ℝ) (he : eps ≤ 1 / T) (hc : c ^ 2 ≤ 1 / T) :
    2 * eps + c ^ 2 + 3 / T ≤ 6 / T := by
  have : 6 / T = 6 * (1 / T) := by ring
  have : 3 / T = 3 * (1 / T) := by ring
  linarith

/-- For `ε ≥ 1/T` and `c² ≤ 1/T`: `2ε + c² + 3/T ≤ 6ε`.
Paper: after `eq:rmsscorelower` (normalization_obstruction.tex). -/
theorem large_epsilon_denominator (T eps c : ℝ) (he : 1 / T ≤ eps) (hc : c ^ 2 ≤ 1 / T) :
    2 * eps + c ^ 2 + 3 / T ≤ 6 * eps := by
  have : 3 / T = 3 * (1 / T) := by ring
  linarith

/-- `1/(64 · 6/T) = T/384`.
Paper: `eq:rmsscorelower` (normalization_obstruction.tex). -/
theorem critical_denominator_constant (T : ℝ) (hT : 0 < T) : 1 / (64 * (6 / T)) = T / 384 := by
  field_simp; ring

/-- `1/(64 · 6ε) = ε⁻¹/384`.
Paper: `eq:rmsscorelower` (normalization_obstruction.tex). -/
theorem positive_epsilon_denominator_constant (eps : ℝ) (he : 0 < eps) :
    1 / (64 * (6 * eps)) = (1 / eps) / 384 := by
  field_simp; ring

/-- The score lower bound `eq:rmsscorelower`: `1/(64(2ε + c² + 3/T)) ≥ min{T, ε⁻¹}/384`,
split into the cases `ε ≤ 1/T` and `ε ≥ 1/T`.
Paper: `eq:rmsscorelower` (normalization_obstruction.tex). -/
theorem score_to_min {T ε c : ℝ} (hT : 1 ≤ T) (hε : 0 ≤ ε) (hc : c ^ 2 ≤ 1 / T) :
    (ε ≤ 1 / T → T / 384 ≤ 1 / (64 * (2 * ε + c ^ 2 + 3 / T))) ∧
      (1 / T ≤ ε → 1 / (384 * ε) ≤ 1 / (64 * (2 * ε + c ^ 2 + 3 / T))) := by
  have hTp : 0 < T := by linarith
  have hpos : 0 < 2 * ε + c ^ 2 + 3 / T := by positivity
  constructor
  · intro he
    have := small_epsilon_denominator T ε c he hc
    rw [← critical_denominator_constant T hTp]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  · intro he
    have hε' : 0 < ε := lt_of_lt_of_le (by positivity) he
    have := large_epsilon_denominator T ε c he hc
    rw [show 1 / (384 * ε) = 1 / (64 * (6 * ε)) by ring]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- The Cauchy-Schwarz step of the transcript bound: if `H² ≤ V Q` with `V ≤ 1`, then
`H² ≤ Q`. Here `V = 𝔼Y² = 1` for a sign output.
Paper: `lem:transcript` (tanh_lower.tex), as used in `thm:rmscontextlaw`
(normalization_obstruction.tex). -/
theorem score_bound_of_cauchy (H V Q : ℝ) (hQ : 0 ≤ Q) (hV : V ≤ 1) (hCS : H ^ 2 ≤ V * Q) :
    H ^ 2 ≤ Q := by
  nlinarith

/-- The lower half of `thm:rmscontextlaw`. Let `H(t)` be the output-sign mean of the width-two
block when the `T` context signs are independent with common mean `t`. Assume the finite
transcript inequality of `lem:transcript` (tanh_lower.tex): every derivative `H'` of `H` at `0`
satisfies
`H'² ≤ Q`, where `Q` is the expected number of distinct context probes at `t = 0`. With a
sentinel `0 < c ≤ 1/T`, `Q ≥ T/384` when `ε ≤ 1/T` and `Q ≥ 1/(384 ε)` when `ε ≥ 1/T`; this is
`Q ≥ min{T, ε⁻¹}/384`.
Paper: `thm:rmscontextlaw`, `eq:rmscontextlaw`, `eq:rmsscorelower`
(normalization_obstruction.tex). -/
theorem context_query_lower {T : ℕ} (hT : 1 ≤ T) {ε c Q : ℝ} (hε : 0 ≤ ε) (hc : 0 < c)
    (hcT : c ≤ 1 / T)
    (htranscript : ∀ H' : ℝ, HasDerivAt
        (fun t => ∑ x : Fin T → Bool, lik t x * familyMean ε c (sgnSum x / T)) H' 0 →
        H' ^ 2 ≤ Q) :
    (ε ≤ 1 / T → (T : ℝ) / 384 ≤ Q) ∧ (1 / T ≤ ε → 1 / (384 * ε) ≤ Q) := by
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hQ := htranscript _ (hasDerivAt_signMean (familyMean ε c))
  have hS := family_score_lower hT hε hc
  have hc2 := sentinel_floor T c hT1 hc.le hcT
  have hpos : 0 < 2 * ε + c ^ 2 + 3 / T := by positivity
  have hs : 0 < √(2 * ε + c ^ 2 + 3 / T) := sqrt_pos.2 hpos
  have hsq : 1 / (64 * (2 * ε + c ^ 2 + 3 / T)) ≤ Q := by
    have h0 : 0 ≤ 1 / (8 * √(2 * ε + c ^ 2 + 3 / T)) := by positivity
    have := pow_le_pow_left₀ h0 hS 2
    have heq : (1 / (8 * √(2 * ε + c ^ 2 + 3 / T))) ^ 2
        = 1 / (64 * (2 * ε + c ^ 2 + 3 / T)) := by
      rw [div_pow, mul_pow, sq_sqrt hpos.le]; norm_num
    linarith
  obtain ⟨h1, h2⟩ := score_to_min hT1 hε hc2
  exact ⟨fun he => le_trans (h1 he) hsq, fun he => le_trans (h2 he) hsq⟩

/-- The sentinel `c = 2^{-⌈log₂ T⌉}` satisfies `1/(2T) < c ≤ 1/T` for `T ≥ 2`.
Paper: `thm:rmscontextlaw` (normalization_obstruction.tex), choice of `c`, and the scan case of
the upper bound. -/
theorem sentinel_mem {T : ℕ} (hT : 2 ≤ T) :
    (1 : ℝ) / (2 * T) < 1 / 2 ^ Nat.clog 2 T ∧ (1 : ℝ) / 2 ^ Nat.clog 2 T ≤ 1 / T := by
  have hle : T ≤ 2 ^ Nat.clog 2 T := Nat.le_pow_clog (by norm_num) T
  have hlt : 2 ^ (Nat.clog 2 T - 1) < T := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hpos : 0 < Nat.clog 2 T := Nat.clog_pos (by norm_num) (by omega)
  have hT0 : (0 : ℝ) < T := by positivity
  constructor
  · have h2 : 2 ^ Nat.clog 2 T < 2 * T := by
      have : 2 ^ Nat.clog 2 T = 2 * 2 ^ (Nat.clog 2 T - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega
    have h2' : (2 : ℝ) ^ Nat.clog 2 T < 2 * T := by exact_mod_cast h2
    exact one_div_lt_one_div_of_lt (by positivity) h2'
  · have h1' : (T : ℝ) ≤ 2 ^ Nat.clog 2 T := by exact_mod_cast hle
    exact one_div_le_one_div_of_le hT0 h1'

/-! ## The geometric-majority identity (`lem:rmsgeommajority`) -/

/-- The probability that the majority of `2k+1` independent coins of bias `p` is one:
`∑_{j ≥ k+1} C(2k+1, j) p^j (1-p)^{2k+1-j}`, as a polynomial in `p`. -/
noncomputable def majPoly (k : ℕ) : ℝ[X] :=
  ∑ ν ∈ range (k + 1), bernsteinPolynomial ℝ (2 * k + 1) (k + 1 + ν)

/-- The majority polynomial in explicit binomial form. -/
theorem majPoly_eval (k : ℕ) (p : ℝ) :
    (majPoly k).eval p = ∑ ν ∈ range (k + 1),
      ((2 * k + 1).choose (k + 1 + ν) : ℝ) * p ^ (k + 1 + ν) * (1 - p) ^ (k - ν) := by
  unfold majPoly
  rw [eval_finsetSum]
  apply sum_congr rfl
  intro ν hν
  have : 2 * k + 1 - (k + 1 + ν) = k - ν := by omega
  simp [bernsteinPolynomial, this]

/-- The mean `M_k(z)` of the majority of `2k+1` independent signs of mean `z`. -/
noncomputable def majMean (k : ℕ) (z : ℝ) : ℝ := 2 * (majPoly k).eval ((1 + z) / 2) - 1

/-- `C_k = (2k+1) C(2k,k) 4^{-k}`. -/
noncomputable def Ck (k : ℕ) : ℝ := (2 * k + 1) * (Nat.centralBinom k : ℝ) / 4 ^ k

/-- The derivative of the majority polynomial: `P_k' = (2k+1) b_{2k,k}`, by telescoping the
Bernstein derivatives.
Paper: proof of `lem:rmsgeommajority` (normalization_obstruction.tex). -/
theorem majPoly_derivative (k : ℕ) :
    derivative (majPoly k) = ((2 * k + 1 : ℕ) : ℝ[X]) * bernsteinPolynomial ℝ (2 * k) k := by
  unfold majPoly
  rw [derivative_sum]
  have h : ∀ ν ∈ range (k + 1), derivative (bernsteinPolynomial ℝ (2 * k + 1) (k + 1 + ν))
      = ((2 * k + 1 : ℕ) : ℝ[X]) * (bernsteinPolynomial ℝ (2 * k) (k + ν)
          - bernsteinPolynomial ℝ (2 * k) (k + ν + 1)) := by
    intro ν _
    rw [show k + 1 + ν = (k + ν) + 1 by ring, bernsteinPolynomial.derivative_succ]
    simp
  rw [sum_congr rfl h, ← mul_sum]
  congr 1
  have := sum_range_sub' (fun ν => bernsteinPolynomial ℝ (2 * k) (k + ν)) (k + 1)
  simp only [add_zero, ← add_assoc] at this
  rw [this, bernsteinPolynomial.eq_zero_of_lt ℝ (by omega : 2 * k < k + k + 1), sub_zero]

/-- The derivative of the majority mean: `M_k'(z) = C_k (1 - z²)^k`.
Paper: proof of `lem:rmsgeommajority` (normalization_obstruction.tex). -/
theorem hasDerivAt_majMean (k : ℕ) (z : ℝ) : HasDerivAt (majMean k) (Ck k * (1 - z ^ 2) ^ k) z := by
  have h1 : HasDerivAt (fun z : ℝ => (1 + z) / 2) (1 / 2) z := by
    simpa using ((hasDerivAt_id z).const_add 1).div_const 2
  have h2 := (Polynomial.hasDerivAt (majPoly k) ((1 + z) / 2)).comp z h1
  have h3 := (h2.const_mul 2).sub_const 1
  unfold majMean
  convert h3 using 1
  · rfl
  rw [majPoly_derivative]
  simp only [eval_mul, eval_natCast, bernsteinPolynomial, eval_pow, eval_X, eval_sub, eval_one]
  rw [show 2 * k - k = k by omega]
  unfold Ck
  rw [Nat.centralBinom_eq_two_mul_choose]
  push_cast
  have : (1 - z ^ 2) ^ k = 4 ^ k * (((1 + z) / 2) ^ k * (1 - (1 + z) / 2) ^ k) := by
    rw [← mul_pow, ← mul_pow]; congr 1; ring
  rw [this]
  field_simp

/-- `P_k(1) = 1`. -/
theorem majPoly_eval_one (k : ℕ) : (majPoly k).eval 1 = 1 := by
  unfold majPoly
  rw [eval_finsetSum, sum_range_succ, sum_eq_zero]
  · rw [bernsteinPolynomial.eval_at_1]; simp; omega
  · intro ν hν
    rw [bernsteinPolynomial.eval_at_1]
    simp at hν
    simp; omega

/-- `0 ≤ P_k(p) ≤ 1` for `p ∈ [0,1]`. -/
theorem majPoly_eval_mem (k : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    0 ≤ (majPoly k).eval p ∧ (majPoly k).eval p ≤ 1 := by
  have hb : ∀ ν n, 0 ≤ (bernsteinPolynomial ℝ n ν).eval p := by
    intro ν n
    simp only [bernsteinPolynomial, eval_mul, eval_natCast, eval_pow, eval_X, eval_sub, eval_one]
    have : 0 ≤ 1 - p := by linarith
    positivity
  constructor
  · unfold majPoly; rw [eval_finsetSum]; exact sum_nonneg (fun ν _ => hb _ _)
  · have htot := congrArg (eval p) (bernsteinPolynomial.sum ℝ (2 * k + 1))
    rw [eval_finsetSum, eval_one] at htot
    unfold majPoly
    rw [eval_finsetSum, ← htot]
    have : ∑ ν ∈ range (k + 1), eval p (bernsteinPolynomial ℝ (2 * k + 1) (k + 1 + ν))
        = ∑ ν ∈ (range (k + 1)).map (addLeftEmbedding (k + 1)),
            eval p (bernsteinPolynomial ℝ (2 * k + 1) ν) := by
      rw [sum_map]; rfl
    rw [this]
    apply sum_le_sum_of_subset_of_nonneg
    · intro x hx
      simp only [mem_map, mem_range, addLeftEmbedding_apply] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      simp only [mem_range]; omega
    · intro i _ _; exact hb _ _

/-- A majority of signs has mean in `[-1, 1]`. -/
theorem abs_majMean_le (k : ℕ) {z : ℝ} (hz : |z| ≤ 1) : |majMean k z| ≤ 1 := by
  obtain ⟨h0, h1⟩ := majPoly_eval_mem k (p := (1 + z) / 2)
    (by linarith [(abs_le.1 hz).1]) (by linarith [(abs_le.1 hz).2])
  unfold majMean
  rw [abs_le]; constructor <;> linarith

/-- `M_k(1) = 1`. -/
theorem majMean_one (k : ℕ) : majMean k 1 = 1 := by
  unfold majMean; norm_num [majPoly_eval_one]

/-- Mathlib's binomial coefficients `Ring.choose (a + n - 1) n` in Pochhammer form. -/
theorem choose_eq_pochhammer (a : ℝ) (n : ℕ) :
    Ring.choose (a + n - 1) n = (ascPochhammer ℝ n).eval a / n.factorial := by
  rw [← Ring.multichoose_eq]
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n
  rw [Polynomial.ascPochhammer_smeval_eq_eval, nsmul_eq_mul] at h
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  rw [eq_div_iff hf, ← h]
  ring

/-- `C_k = (3/2)_k / k!`.
Paper: proof of `lem:rmsgeommajority` (normalization_obstruction.tex). -/
theorem pochhammer_three_halves (n : ℕ) :
    (ascPochhammer ℝ n).eval (3 / 2 : ℝ) / n.factorial = Ck n := by
  induction n with
  | zero => simp [Ck]
  | succ n ih =>
    rw [ascPochhammer_succ_eval, Nat.factorial_succ]
    have h1 := Nat.succ_mul_centralBinom_succ n
    have h2 : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ)
        = 2 * (2 * n + 1) * Nat.centralBinom n := by exact_mod_cast h1
    unfold Ck at *
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    have := ih
    rw [div_eq_div_iff hf (by positivity)] at this
    push_cast
    rw [div_eq_div_iff (by positivity) (by positivity), pow_succ]
    linear_combination (3 / 2 + (n : ℝ)) * 4 * this - (2 * (n : ℝ) + 3) * (n.factorial : ℝ) * h2

/-- The binomial series with exponent `-3/2`: `∑ C_k y^k = (1-y)^{-3/2}` for `|y| < 1`.
Paper: proof of `lem:rmsgeommajority` (normalization_obstruction.tex). -/
theorem hasSum_Ck (y : ℝ) (hy : |y| < 1) :
    HasSum (fun n => Ck n * y ^ n) (1 / ((1 - y) * √(1 - y))) := by
  have hy' : y ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]
    have : ‖y‖₊ < 1 := by rw [← NNReal.coe_lt_coe]; simpa using hy
    exact_mod_cast this
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (3 / 2 : ℝ)).hasSum hy'
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, zero_add, smul_eq_mul] at h
  convert h using 1
  · funext n
    rw [choose_eq_pochhammer, pochhammer_three_halves]
  · have hpos : 0 < 1 - y := by linarith [abs_lt.1 hy]
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add hpos, rpow_one, ← sqrt_eq_rpow]

/-- The geometric law `Pr(K = k) = θ/(1+θ) · (1+θ)^{-k}`. -/
noncomputable def geomWeight (θ : ℝ) (k : ℕ) : ℝ := θ / (1 + θ) * (1 / (1 + θ)) ^ k

/-- The target `G_θ(z) = z √(1+θ) / √(θ + z²)`.
Paper: `eq:rmsgeommajority` (normalization_obstruction.tex). -/
noncomputable def geomMajority (θ z : ℝ) : ℝ := z * √(1 + θ) / √(θ + z ^ 2)

/-- The geometric weights are nonnegative. -/
theorem geomWeight_nonneg {θ : ℝ} (hθ : 0 < θ) (k : ℕ) : 0 ≤ geomWeight θ k := by
  unfold geomWeight; positivity

/-- The geometric weights sum to one.
Paper: `lem:rmsgeommajority` (normalization_obstruction.tex). -/
theorem geomWeight_hasSum {θ : ℝ} (hθ : 0 < θ) : HasSum (geomWeight θ) 1 := by
  have h1θ : 0 < 1 + θ := by linarith
  have hr : 1 / (1 + θ) < 1 := by rw [div_lt_one h1θ]; linarith
  have h := (hasSum_geometric_of_lt_one (by positivity) hr).mul_left (θ / (1 + θ))
  unfold geomWeight
  convert h using 1
  have : 1 - 1 / (1 + θ) = θ / (1 + θ) := by field_simp; ring
  rw [this]
  field_simp

/-- `𝔼 K = 1/θ` for the geometric law.
Paper: proof of `lem:rmsgeommajority` (normalization_obstruction.tex). -/
theorem geomWeight_mean {θ : ℝ} (hθ : 0 < θ) :
    HasSum (fun k : ℕ => (k : ℝ) * geomWeight θ k) (1 / θ) := by
  have h1θ : 0 < 1 + θ := by linarith
  have hr : ‖1 / (1 + θ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_lt_one h1θ]; linarith
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hr).mul_left (θ / (1 + θ))
  unfold geomWeight
  convert h using 1
  · funext k; ring
  · have : 1 - 1 / (1 + θ) = θ / (1 + θ) := by field_simp; ring
    rw [this]
    field_simp

/-- The expected number of source signs of the geometric majority is `1 + 2/θ`.
Paper: `lem:rmsgeommajority` (normalization_obstruction.tex). -/
theorem geometric_majority_arity {θ : ℝ} (hθ : 0 < θ) :
    HasSum (fun k : ℕ => (2 * k + 1 : ℝ) * geomWeight θ k) (1 + 2 / θ) := by
  have h := ((geomWeight_mean hθ).mul_left 2).add (geomWeight_hasSum hθ)
  convert h using 1
  · funext k; ring
  · ring

/-- `1 - (1 - z²)/(1 + θ) = (θ + z²)/(1 + θ)`.
Paper: proof of `lem:rmsgeommajority` (normalization_obstruction.tex). -/
theorem geometric_majority_denominator (theta z : ℝ) (ht : 0 < theta) :
    1 - (1 - z ^ 2) / (1 + theta) = (theta + z ^ 2) / (1 + theta) := by
  have hd : 1 + theta ≠ 0 := by linarith
  field_simp
  ring

/-- The derivative of the target: `G_θ'(z) = θ √(1+θ) / (θ + z²)^{3/2}`.
Paper: proof of `lem:rmsgeommajority` (normalization_obstruction.tex). -/
theorem hasDerivAt_geomMajority {θ : ℝ} (hθ : 0 < θ) (z : ℝ) :
    HasDerivAt (geomMajority θ) (θ * √(1 + θ) / ((θ + z ^ 2) * √(θ + z ^ 2))) z := by
  have hpos : 0 < θ + z ^ 2 := by positivity
  have hs : 0 < √(θ + z ^ 2) := sqrt_pos.2 hpos
  have h1 : HasDerivAt (fun z : ℝ => θ + z ^ 2) (2 * z) z := by
    simpa using (hasDerivAt_pow 2 z).const_add θ
  have h2 := h1.sqrt hpos.ne'
  have h3 := ((hasDerivAt_id z).mul_const (√(1 + θ))).div h2 hs.ne'
  have hsq : √(θ + z ^ 2) ^ 2 = θ + z ^ 2 := sq_sqrt hpos.le
  convert h3 using 1
  · funext y; simp [geomMajority]
  · simp only [id]
    rw [hsq]
    field_simp
    rw [hsq]
    ring

/-- The geometric mixture of the derivatives `C_k (1-z²)^k` is `G_θ'(z)`: the binomial series
with exponent `-3/2` at `(1-z²)/(1+θ)`.
Paper: proof of `lem:rmsgeommajority` (normalization_obstruction.tex). -/
theorem mixture_derivative {θ z : ℝ} (hθ : 0 < θ) (hz : |1 - z ^ 2| ≤ 1) :
    HasSum (fun k => geomWeight θ k * (Ck k * (1 - z ^ 2) ^ k))
      (θ * √(1 + θ) / ((θ + z ^ 2) * √(θ + z ^ 2))) := by
  have h1θ : 0 < 1 + θ := by linarith
  have hy : |(1 - z ^ 2) / (1 + θ)| < 1 := by
    rw [abs_div, abs_of_pos h1θ, div_lt_one h1θ]; linarith
  have h := (hasSum_Ck _ hy).mul_left (θ / (1 + θ))
  convert h using 1
  · funext k; unfold geomWeight; rw [div_pow, div_pow, one_pow]; ring
  · have hpos : 0 < θ + z ^ 2 := by positivity
    rw [geometric_majority_denominator θ z hθ, sqrt_div hpos.le]
    have hs : 0 < √(θ + z ^ 2) := sqrt_pos.2 hpos
    have hs1 : 0 < √(1 + θ) := sqrt_pos.2 h1θ
    have hsq : √(1 + θ) ^ 2 = 1 + θ := sq_sqrt h1θ.le
    field_simp

/-- **The geometric-majority identity.** Draw `K` with `Pr(K = k) = θ/(1+θ) (1+θ)^{-k}`; the
majority of `2K+1` independent signs of mean `z ∈ [-1,1]` has mean
`G_θ(z) = z √(1+θ) / √(θ + z²)`.
Paper: `lem:rmsgeommajority`, `eq:rmsgeommajority` (normalization_obstruction.tex). -/
theorem geometric_majority_identity {θ z : ℝ} (hθ : 0 < θ) (hz : |z| ≤ 1) :
    HasSum (fun k => geomWeight θ k * majMean k z) (geomMajority θ z) := by
  have htopen : IsOpen (Set.Ioo (-(7 / 5 : ℝ)) (7 / 5)) := isOpen_Ioo
  have htconn : IsPreconnected (Set.Ioo (-(7 / 5 : ℝ)) (7 / 5)) := isPreconnected_Ioo
  have hbound : ∀ y ∈ Set.Ioo (-(7 / 5 : ℝ)) (7 / 5), |1 - y ^ 2| ≤ 1 := by
    intro y hy
    rw [Set.mem_Ioo] at hy
    rw [abs_le]; constructor <;> nlinarith
  have h1θ : 0 < 1 + θ := by linarith
  have hu0 := mixture_derivative hθ (z := 0) (by norm_num)
  have hu : Summable (fun k => geomWeight θ k * Ck k) := by
    refine hu0.summable.congr (fun k => ?_)
    simp
  have hwn : ∀ k, 0 ≤ geomWeight θ k := geomWeight_nonneg hθ
  have hCk : ∀ k, 0 ≤ Ck k := fun k => by unfold Ck; positivity
  have hg : ∀ k y, y ∈ Set.Ioo (-(7 / 5 : ℝ)) (7 / 5) →
      HasDerivAt (fun z => geomWeight θ k * majMean k z)
        (geomWeight θ k * (Ck k * (1 - y ^ 2) ^ k)) y :=
    fun k y _ => (hasDerivAt_majMean k y).const_mul _
  have hg' : ∀ k y, y ∈ Set.Ioo (-(7 / 5 : ℝ)) (7 / 5) →
      ‖geomWeight θ k * (Ck k * (1 - y ^ 2) ^ k)‖ ≤ geomWeight θ k * Ck k := by
    intro k y hy
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_nonneg (hwn k),
      abs_of_nonneg (hCk k)]
    have h1 : |1 - y ^ 2| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg _) (hbound y hy)
    have h0 := mul_nonneg (hwn k) (hCk k)
    calc geomWeight θ k * (Ck k * |1 - y ^ 2| ^ k)
        = (geomWeight θ k * Ck k) * |1 - y ^ 2| ^ k := by ring
      _ ≤ (geomWeight θ k * Ck k) * 1 := mul_le_mul_of_nonneg_left h1 h0
      _ = geomWeight θ k * Ck k := mul_one _
  have h1t : (1 : ℝ) ∈ Set.Ioo (-(7 / 5 : ℝ)) (7 / 5) := by rw [Set.mem_Ioo]; norm_num
  have hg0 : Summable (fun k => geomWeight θ k * majMean k 1) := by
    simp only [majMean_one, mul_one]; exact (geomWeight_hasSum hθ).summable
  have hzt : z ∈ Set.Ioo (-(7 / 5 : ℝ)) (7 / 5) := by
    rw [Set.mem_Ioo]; constructor <;> linarith [(abs_le.1 hz).1, (abs_le.1 hz).2]
  have hsum : Summable (fun k => geomWeight θ k * majMean k z) :=
    summable_of_summable_hasDerivAt_of_isPreconnected
      (g := fun k z => geomWeight θ k * majMean k z)
      (g' := fun k y => geomWeight θ k * (Ck k * (1 - y ^ 2) ^ k)) hu htopen htconn hg hg' h1t
      hg0 hzt
  refine hsum.hasSum_iff.2 ?_
  have hderiv : ∀ y ∈ Set.Ioo (-(7 / 5 : ℝ)) (7 / 5),
      HasDerivAt (fun z => ∑' k, geomWeight θ k * majMean k z)
        (θ * √(1 + θ) / ((θ + y ^ 2) * √(θ + y ^ 2))) y := by
    intro y hy
    have := hasDerivAt_tsum_of_isPreconnected
      (g := fun k z => geomWeight θ k * majMean k z)
      (g' := fun k y => geomWeight θ k * (Ck k * (1 - y ^ 2) ^ k)) hu htopen htconn hg hg' h1t
      hg0 hy
    rwa [(mixture_derivative hθ (hbound y hy)).tsum_eq] at this
  let D : ℝ → ℝ := fun z => (∑' k, geomWeight θ k * majMean k z) - geomMajority θ z
  have hDd : ∀ y ∈ Set.Ioo (-(7 / 5 : ℝ)) (7 / 5), HasDerivAt D 0 y := by
    intro y hy
    have := (hderiv y hy).sub (hasDerivAt_geomMajority hθ y)
    rw [sub_self] at this
    exact this
  have hdiff : DifferentiableOn ℝ D (Set.Ioo (-(7 / 5 : ℝ)) (7 / 5)) :=
    fun y hy => (hDd y hy).differentiableAt.differentiableWithinAt
  have hzero : Set.EqOn (deriv D) 0 (Set.Ioo (-(7 / 5 : ℝ)) (7 / 5)) :=
    fun y hy => (hDd y hy).deriv
  have hconst : D z = D 1 := htopen.is_const_of_deriv_eq_zero htconn hdiff hzero hzt h1t
  have hG1 : geomMajority θ 1 = 1 := by
    unfold geomMajority
    rw [show θ + (1 : ℝ) ^ 2 = 1 + θ by ring, one_mul, div_self (sqrt_pos.2 h1θ).ne']
  have hD1 : D 1 = 0 := by
    show (∑' k, geomWeight θ k * majMean k 1) - geomMajority θ 1 = 0
    simp only [majMean_one, mul_one, (geomWeight_hasSum hθ).tsum_eq, hG1, sub_self]
  have h' : (∑' k, geomWeight θ k * majMean k z) - geomMajority θ z = 0 := hconst.trans hD1
  show (∑' k, geomWeight θ k * majMean k z) = geomMajority θ z
  linarith

/-! ## The matching sampler for `thm:rmscontextlaw` -/

/-- A known gate of probability `(2(1+θ))^{-1/2}` turns `G_θ(z)` into `z/(√2 √(θ + z²))`.
Paper: `thm:rmscontextlaw` (normalization_obstruction.tex), the matching sampler. -/
theorem gate_geomMajority {θ z : ℝ} (hθ : 0 < θ) :
    (1 / √(2 * (1 + θ))) * geomMajority θ z + (1 - 1 / √(2 * (1 + θ))) * 0
      = z / (√2 * √(θ + z ^ 2)) := by
  unfold geomMajority
  have h1θ : 0 < 1 + θ := by linarith
  rw [sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hs : 0 < √(1 + θ) := sqrt_pos.2 h1θ
  have h2 : (0 : ℝ) < √2 := by positivity
  have hs2 : 0 < √(θ + z ^ 2) := sqrt_pos.2 (by positivity)
  rw [mul_zero, add_zero]
  field_simp

/-- The source count of the matching sampler: two tanh factories with at most `2e` source
requests each, one gate, and a geometric majority with `1 + 2/θ` context requests, `θ ≥ 2ε`.
For `0 < ε ≤ 1`, `4e²(1 + 2/θ) ≤ 32(1 + ε⁻¹) ≤ 64 ε⁻¹`.
Paper: `thm:rmscontextlaw` (normalization_obstruction.tex), the matching sampler. -/
theorem upper_count {ε θ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hθ : 2 * ε ≤ θ) :
    4 * exp 1 ^ 2 * (1 + 2 / θ) ≤ 32 * (1 + 1 / ε) ∧ 32 * (1 + 1 / ε) ≤ 64 / ε := by
  have he : exp 1 < 2.7182818286 := exp_one_lt_d9
  have he0 := exp_pos 1
  have he2 : 4 * exp 1 ^ 2 ≤ 32 := by nlinarith
  have hθ0 : 0 < θ := by linarith
  have hfrac : 2 / θ ≤ 1 / ε := by
    rw [div_le_div_iff₀ hθ0 hε]; linarith
  have hinv : 1 ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
  constructor
  · calc 4 * exp 1 ^ 2 * (1 + 2 / θ) ≤ 32 * (1 + 2 / θ) :=
          mul_le_mul_of_nonneg_right he2 (by positivity)
      _ ≤ 32 * (1 + 1 / ε) := by linarith
  · have : 64 / ε = 32 * (1 / ε) + 32 * (1 / ε) := by ring
    linarith

/-- `min{T, ε⁻¹}` with the convention `ε⁻¹ = +∞` at `ε = 0`.
Paper: `eq:rmscontextlaw` (normalization_obstruction.tex). -/
noncomputable def minInv (T ε : ℝ) : ℝ := if ε = 0 then T else min T (1 / ε)

/-- Choosing the scan (cost `T`) when `ε < 1/T` and a sampler of cost `K/ε` when `ε ≥ 1/T`
costs at most `K min{T, ε⁻¹}` for `K ≥ 1` and every `ε ≥ 0`, including `ε = 0`.
Paper: `eq:rmscontextlaw` and `eq:rmsfixedgridlaw` (normalization_obstruction.tex), upper
bounds. -/
theorem min_regimes {T ε K : ℝ} (hT : 0 < T) (hε : 0 ≤ ε) (hK : 1 ≤ K) :
    (ε < 1 / T → T ≤ K * minInv T ε) ∧ (1 / T ≤ ε → K / ε ≤ K * minInv T ε) := by
  rcases hε.eq_or_lt with h0 | hε'
  · subst h0
    refine ⟨fun _ => ?_, fun h => absurd h (not_le.2 (by positivity))⟩
    simp only [minInv, ite_true]
    nlinarith
  have hne : ε ≠ 0 := hε'.ne'
  simp only [minInv, hne, ite_false]
  constructor
  · intro h
    have : T < 1 / ε := by rw [lt_div_iff₀ hε']; rw [lt_div_iff₀ hT] at h; linarith
    rw [min_eq_left this.le]; nlinarith
  · intro h
    have : 1 / ε ≤ T := by rw [div_le_iff₀ hε']; rw [div_le_iff₀ hT] at h; linarith
    rw [min_eq_right this, mul_one_div]

/-- The two upper-bound regimes give at most `64 min{T, ε⁻¹}` for every `ε ≥ 0`: the scan
costs `T` when `ε < 1/T` (in particular at `ε = 0`), and the sampler costs at most `64/ε`
(`upper_count`) when `ε ≥ 1/T`.
Paper: `eq:rmscontextlaw` (normalization_obstruction.tex), upper bound. -/
theorem upper_min {T ε : ℝ} (hT : 0 < T) (hε : 0 ≤ ε) :
    (ε < 1 / T → T ≤ 64 * minInv T ε) ∧ (1 / T ≤ ε → 64 / ε ≤ 64 * minInv T ε) :=
  min_regimes hT hε (by norm_num)

/-! ## A fixed coefficient grid (`cor:rmsfixedgrid`) -/

/-- The public first-position feature: `(1 + η_1)/2 = 1` and `(1 + η_j)/2 = 0` for `j > 1`.
Paper: proof of `cor:rmsfixedgrid` (normalization_obstruction.tex). -/
theorem first_position_value (eta : ℝ) (h : eta = 1 ∨ eta = -1) :
    (1 + eta) / 2 = if eta = 1 then 1 else 0 := by
  rcases h with h | h
  · simp [h]
  · norm_num [h]

/-- Averaging the public feature over the first `t` positions gives the sentinel `1/t`.
Paper: proof of `cor:rmsfixedgrid` (normalization_obstruction.tex). -/
theorem sentinel_average {t : ℕ} (ht : 1 ≤ t) :
    (1 / (t : ℝ)) * ∑ j ∈ range t, (1 + (if j = 0 then (1 : ℝ) else -1)) / 2 = 1 / t := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [sum_range_succ']
  have : ∑ j ∈ range s, (1 + (if j + 1 = 0 then (1 : ℝ) else -1)) / 2 = 0 := by
    apply sum_eq_zero; intro j _; simp
  rw [this]; simp

/-- `4(ε + (M² + c²)/4) = 4ε + c² + M²`.
Paper: proof of `cor:rmsfixedgrid` (normalization_obstruction.tex). -/
theorem width_four_radicand (eps M c : ℝ) :
    4 * (eps + (M ^ 2 + c ^ 2) / 4) = 4 * eps + c ^ 2 + M ^ 2 := by
  ring

/-- The width-four normalization of `(M, 1/t, 0, 0)`, followed by the tanh row of coefficient
`1/2`, has argument `M / √(4ε + t^{-2} + M²)`.
Paper: proof of `cor:rmsfixedgrid` (normalization_obstruction.tex). -/
theorem width_four_argument {ε s M : ℝ} (hpos : 0 < 4 * ε + s ^ 2 + M ^ 2) :
    (1 / 2) * (M / √(ε + (M ^ 2 + s ^ 2 + 0 ^ 2 + 0 ^ 2) / 4)) = M / √(4 * ε + s ^ 2 + M ^ 2) := by
  have h : ε + (M ^ 2 + s ^ 2 + 0 ^ 2 + 0 ^ 2) / 4 = (4 * ε + s ^ 2 + M ^ 2) / 4 := by ring
  rw [h, sqrt_div hpos.le, show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]
  have hs : 0 < √(4 * ε + s ^ 2 + M ^ 2) := sqrt_pos.2 hpos
  field_simp

/-- The target mean of the fixed-grid block. -/
noncomputable def fixedGridMean (ε T M : ℝ) : ℝ := tanh (tanh (M / √(4 * ε + T⁻¹ ^ 2 + M ^ 2)))

/-- The pointwise bound `M f̃_ε(M) ≥ M²/(4√(4ε + T^{-2} + M²))`; the inner argument lies in
`[-1,1]`.
Paper: proof of `cor:rmsfixedgrid` (normalization_obstruction.tex). -/
theorem mul_fixedGridMean_ge {ε T : ℝ} (hε : 0 ≤ ε) (hT : 0 < T) (M : ℝ) :
    (1 / 4) * (M ^ 2 / √(4 * ε + T⁻¹ ^ 2 + M ^ 2)) ≤ M * fixedGridMean ε T M := by
  have hθ : 0 < 4 * ε + T⁻¹ ^ 2 := by positivity
  have hs : 0 < √(4 * ε + T⁻¹ ^ 2 + M ^ 2) := sqrt_pos.2 (by positivity)
  set x := |M| / √(4 * ε + T⁻¹ ^ 2 + M ^ 2) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one hs, ← sqrt_sq_eq_abs]; exact sqrt_le_sqrt (by linarith)
  have hkey : |M| * (x / 4) ≤ M * fixedGridMean ε T M := by
    unfold fixedGridMean
    rcases le_total 0 M with hM | hM
    · rw [abs_of_nonneg hM] at hx ⊢
      rw [← hx]
      exact mul_le_mul_of_nonneg_left (quarter_le_tanh_tanh hx0 hx1) hM
    · rw [abs_of_nonpos hM] at hx ⊢
      have hneg : M / √(4 * ε + T⁻¹ ^ 2 + M ^ 2) = -x := by rw [hx]; ring
      rw [hneg, tanh_odd, tanh_odd]
      have := quarter_le_tanh_tanh hx0 hx1
      nlinarith
  have hcalc : (1 / 4) * (M ^ 2 / √(4 * ε + T⁻¹ ^ 2 + M ^ 2)) = |M| * (x / 4) := by
    rw [hx, ← sq_abs]; field_simp
  linarith

/-- For `ε ≤ 1/T`, `4ε + T^{-2} + 3/T ≤ 8/T`.
Paper: proof of `cor:rmsfixedgrid` (normalization_obstruction.tex). -/
theorem width_four_small_epsilon_denominator (T eps : ℝ) (hT : 1 ≤ T) (he : eps ≤ 1 / T) :
    4 * eps + (1 / T) ^ 2 + 3 / T ≤ 8 / T := by
  have hTp : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hti : 0 < 1 / T := one_div_pos.2 hTp
  have hti1 : 1 / T ≤ 1 := by rw [div_le_iff₀ hTp]; linarith
  have : 8 / T = 8 * (1 / T) := by ring
  have : 3 / T = 3 * (1 / T) := by ring
  nlinarith

/-- For `ε ≥ 1/T`, `4ε + T^{-2} + 3/T ≤ 8ε`.
Paper: proof of `cor:rmsfixedgrid` (normalization_obstruction.tex). -/
theorem width_four_large_epsilon_denominator (T eps : ℝ) (hT : 1 ≤ T) (he : 1 / T ≤ eps) :
    4 * eps + (1 / T) ^ 2 + 3 / T ≤ 8 * eps := by
  have hTp : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hti : 0 < 1 / T := one_div_pos.2 hTp
  have hti1 : 1 / T ≤ 1 := by rw [div_le_iff₀ hTp]; linarith
  have : 3 / T = 3 * (1 / T) := by ring
  nlinarith

/-- `1/(16 · 8/T) = T/128`.
Paper: `eq:rmsfixedgridlaw` (normalization_obstruction.tex). -/
theorem width_four_lower_constant (T : ℝ) (hT : 0 < T) : 1 / (16 * (8 / T)) = T / 128 := by
  field_simp; ring

/-- The lower half of `cor:rmsfixedgrid`, under the same transcript hypothesis as
`context_query_lower`: `Q ≥ T/128` if `ε ≤ 1/T` and `Q ≥ 1/(128 ε)` if `ε ≥ 1/T`.
Paper: `cor:rmsfixedgrid`, `eq:rmsfixedgridlaw` (normalization_obstruction.tex). -/
theorem fixed_grid_query_lower {T : ℕ} (hT : 1 ≤ T) {ε Q : ℝ} (hε : 0 ≤ ε)
    (htranscript : ∀ H' : ℝ, HasDerivAt
        (fun t => ∑ x : Fin T → Bool, lik t x * fixedGridMean ε T (sgnSum x / T)) H' 0 →
        H' ^ 2 ≤ Q) :
    (ε ≤ 1 / T → (T : ℝ) / 128 ≤ Q) ∧ (1 / T ≤ ε → 1 / (128 * ε) ≤ Q) := by
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTp : (0 : ℝ) < T := by linarith
  have hQ := htranscript _ (hasDerivAt_signMean (fixedGridMean ε T))
  have hS := score_from_pointwise hT (fixedGridMean ε T) (a := 4 * ε + (T : ℝ)⁻¹ ^ 2)
    (κ := 1 / 4) (by positivity) (by norm_num) (fun M => by
      have := mul_fixedGridMean_ge hε hTp M
      rwa [show 4 * ε + (T : ℝ)⁻¹ ^ 2 + M ^ 2 = (4 * ε + (T : ℝ)⁻¹ ^ 2) + M ^ 2 by ring]
        at this)
  have hpos : 0 < 4 * ε + (T : ℝ)⁻¹ ^ 2 + 3 / T := by positivity
  have hsq : 1 / (16 * (4 * ε + (1 / (T : ℝ)) ^ 2 + 3 / T)) ≤ Q := by
    have h0 : 0 ≤ 1 / 4 / √(4 * ε + (T : ℝ)⁻¹ ^ 2 + 3 / T) := by positivity
    have := pow_le_pow_left₀ h0 hS 2
    have heq : (1 / 4 / √(4 * ε + (T : ℝ)⁻¹ ^ 2 + 3 / T)) ^ 2
        = 1 / (16 * (4 * ε + (1 / (T : ℝ)) ^ 2 + 3 / T)) := by
      rw [div_pow, sq_sqrt hpos.le, show (1 : ℝ) / T = (T : ℝ)⁻¹ from one_div _]
      field_simp
      norm_num
    linarith
  constructor
  · intro he
    have h1 := width_four_small_epsilon_denominator T ε hT1 he
    rw [← width_four_lower_constant T hTp]
    exact le_trans (one_div_le_one_div_of_le (by positivity) (by linarith)) hsq
  · intro he
    have hε' : 0 < ε := lt_of_lt_of_le (by positivity) he
    have h1 := width_four_large_epsilon_denominator T ε hT1 he
    have : 1 / (128 * ε) = 1 / (16 * (8 * ε)) := by ring
    rw [this]
    exact le_trans (one_div_le_one_div_of_le (by positivity) (by linarith)) hsq

/-- The fixed-grid sampler: the gate `(1+θ)^{-1/2}`, two unit tanh factories (fewer than `16`
requests of their source), and a geometric majority with `θ = 4ε + T^{-2} ≥ 4ε`. For
`0 < ε ≤ 1`, `16(1 + 2/θ) ≤ 16(1 + (2ε)⁻¹) ≤ 24 ε⁻¹`.
Paper: proof of `cor:rmsfixedgrid` (normalization_obstruction.tex). -/
theorem fixed_grid_upper_count {ε θ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hθ : 4 * ε ≤ θ) :
    16 * (1 + 2 / θ) ≤ 16 * (1 + 1 / (2 * ε)) ∧ 16 * (1 + 1 / (2 * ε)) ≤ 24 / ε := by
  have hθ0 : 0 < θ := by linarith
  have hfrac : 2 / θ ≤ 1 / (2 * ε) := by rw [div_le_div_iff₀ hθ0 (by positivity)]; linarith
  have hinv : 1 ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
  constructor
  · linarith
  · have h1 : 1 / (2 * ε) = (1 / 2) * (1 / ε) := by field_simp
    have h2 : 24 / ε = 24 * (1 / ε) := by ring
    rw [h1, h2]; linarith

/-- The upper half of `eq:rmsfixedgridlaw`: the scan costs `T ≤ 32 min{T, ε⁻¹}` when
`ε < 1/T` (in particular at `ε = 0`), and the sampler costs at most `24/ε ≤ 32 min{T, ε⁻¹}`
(`fixed_grid_upper_count`) when `ε ≥ 1/T`.
Paper: `eq:rmsfixedgridlaw` in `cor:rmsfixedgrid` (normalization_obstruction.tex). -/
theorem fixed_grid_upper_min {T ε : ℝ} (hT : 0 < T) (hε : 0 ≤ ε) :
    (ε < 1 / T → T ≤ 32 * minInv T ε) ∧ (1 / T ≤ ε → 24 / ε ≤ 32 * minInv T ε) := by
  obtain ⟨h1, h2⟩ := min_regimes (K := 32) hT hε (by norm_num)
  refine ⟨h1, fun h => le_trans ?_ (h2 h)⟩
  have hε' : 0 < ε := lt_of_lt_of_le (by positivity) h
  exact div_le_div_of_nonneg_right (by norm_num) hε'.le

/-- The gate of the fixed-grid sampler: `(1+θ)^{-1/2} G_θ(z) = z/√(θ + z²)`.
Paper: proof of `cor:rmsfixedgrid` (normalization_obstruction.tex). -/
theorem fixed_grid_gate {θ z : ℝ} (hθ : 0 < θ) :
    (1 / √(1 + θ)) * geomMajority θ z = z / √(θ + z ^ 2) := by
  unfold geomMajority
  have hs : 0 < √(1 + θ) := sqrt_pos.2 (by linarith)
  field_simp

end ExactSampling.RMSContextLaw
