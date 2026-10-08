import Mathlib

/-!
# The score certificate of an exact parity factor

Paper file: instance_hardness.tex, proof of `cor:score-certificate-hardness`; the certificate
is the first term of `eq:instance-certificate` (instance_information.tex).

Formalized: for `f(y) = α ∏ᵢ yᵢ` on `m ≥ 2` signs, the product extension is
`𝓗(s) = α ∏ᵢ sᵢ`; its partial derivatives are `α ∏_{j ≠ i} sⱼ`; at the common mean
`t = √(1 - 1/m)` the numerator of the first certificate term equals `α² m (1 - 1/m)^{m-1}`, the
denominator `1 - 𝓗²` lies in `(0, 1]`, the first certificate term is at least `α² m/3`
(`parity_certificate_term`), and `α² m/3 ≥ c² m/48` when `α ≥ c/4`.

The exact factorization `f(x, y) = A(x) ∏ᵢ yᵢ` that reduces the network to this parity factor is
proved for the norm-eight gates in `ExactSampling.BooleanGates.output_factorizes` (`A ≥ tanh 1`
on satisfying assignments) and for every fixed row bound above one in
`ExactSampling.RelayGates.outputC_factorizes` (`A ≥ c/4`).

Not formalized: the limit in which the means of the assignment coordinates approach a
satisfying assignment (which transfers the bound from the parity factor to the network), and
the complexity-theoretic conclusion.
-/

namespace ExactSampling.ScoreCertificate

open Finset

noncomputable section

variable {m : ℕ}

/-- The sign `±1` of a Boolean input bit. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- Product-law weight `∏ᵢ (1 + sᵢ xᵢ)/2`. -/
def prodLaw (s : Fin m → ℝ) (x : Fin m → Bool) : ℝ := ∏ i, (1 + s i * sgn (x i)) / 2

/-- The product extension `𝓗(s) = ∑ₓ f(x) ∏ᵢ (1 + sᵢ xᵢ)/2`. -/
def prodExp (s : Fin m → ℝ) (g : (Fin m → Bool) → ℝ) : ℝ := ∑ x, prodLaw s x * g x

/-- The parity `∏ᵢ yᵢ`. -/
def parity (y : Fin m → Bool) : ℝ := ∏ i, sgn (y i)

/-- The partial derivative `∂ᵢ𝓗(s)` of the product extension of `g`. -/
def partialDeriv (g : (Fin m → Bool) → ℝ) (s : Fin m → ℝ) (i : Fin m) : ℝ :=
  deriv (fun u : ℝ => prodExp (s + u • (Pi.single i (1 : ℝ) : Fin m → ℝ)) g) 0

/-- **The product extension of a parity factor.** `E_s[α ∏ᵢ yᵢ] = α ∏ᵢ sᵢ`.
Paper: proof of `cor:score-certificate-hardness` ("the output mean is `α t^m`"). -/
theorem prodExp_parity (α : ℝ) (s : Fin m → ℝ) :
    prodExp s (fun y => α * parity y) = α * ∏ i, s i := by
  classical
  unfold prodExp prodLaw parity
  have : ∀ x : Fin m → Bool, (∏ i, (1 + s i * sgn (x i)) / 2) * (α * ∏ i, sgn (x i)) =
      α * ∏ i, ((1 + s i * sgn (x i)) / 2 * sgn (x i)) := fun x => by
    rw [Finset.prod_mul_distrib]; ring
  simp_rw [this, ← Finset.mul_sum]
  congr 1
  rw [← Fintype.prod_sum (fun i (b : Bool) => (1 + s i * sgn b) / 2 * sgn b)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  simp [sgn]
  ring

/-- **Partial derivatives of the parity factor.** `∂ᵢ(α ∏ⱼ sⱼ) = α ∏_{j ≠ i} sⱼ`.
Paper: proof of `cor:score-certificate-hardness`. -/
theorem partialDeriv_parity (α : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    partialDeriv (fun y => α * parity y) s i = α * ∏ j ∈ univ.erase i, s j := by
  classical
  unfold partialDeriv
  simp_rw [prodExp_parity]
  set e : Fin m → ℝ := Pi.single i (1 : ℝ) with he
  have h := HasDerivAt.fun_finsetProd (u := univ) (x := (0 : ℝ))
    (f := fun j (u : ℝ) => s j + u * e j) (f' := fun j => e j)
    (fun j _ => by simpa using (hasDerivAt_mul_const (e j)).const_add (s j))
  have hfun : (fun u : ℝ => α * ∏ j, (s + u • e) j) = fun u => α * ∏ j, (s j + u * e j) := by
    funext u; simp
  have h2 := h.const_mul α
  rw [hfun, h2.deriv]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp [he]
  · intro j _ hj
    simp [he, Pi.single_apply, hj]
  · simp

/-- `(1 - 1/m)^{m-1} ≥ 1/3`, from `(1 + 1/(m-1))^{m-1} ≤ e < 3`. Paper: proof of
`cor:score-certificate-hardness` (instance_hardness.tex). -/
theorem one_sub_inv_pow_ge (hm : 2 ≤ m) : 1 / 3 ≤ (1 - 1 / (m : ℝ)) ^ (m - 1) := by
  have hm1 : (1 : ℝ) ≤ m - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  set k : ℕ := m - 1 with hk
  have hkr : (k : ℝ) = m - 1 := by rw [hk]; push_cast [show 1 ≤ m by omega]; ring
  have hk1 : (1 : ℝ) ≤ k := by rw [hkr]; exact hm1
  have hbase : 1 - 1 / (m : ℝ) = 1 / (1 + 1 / (k : ℝ)) := by
    rw [hkr]
    have : (m : ℝ) - 1 ≠ 0 := by linarith
    have : (m : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  rw [hbase, div_pow, one_pow]
  have hup : (1 + 1 / (k : ℝ)) ^ k ≤ Real.exp 1 := by
    have h1 : 1 + 1 / (k : ℝ) ≤ Real.exp (1 / k) := by
      have := Real.add_one_le_exp (1 / (k : ℝ)); linarith
    calc (1 + 1 / (k : ℝ)) ^ k ≤ Real.exp (1 / k) ^ k :=
          pow_le_pow_left₀ (by positivity) h1 k
      _ = Real.exp 1 := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp
  have he := Real.exp_one_lt_d9
  have hpos : 0 < (1 + 1 / (k : ℝ)) ^ k := by positivity
  rw [div_le_div_iff₀ (by norm_num) hpos]
  linarith

/-- **The certificate of the parity factor.** For `f(y) = α ∏ᵢ yᵢ` on `m ≥ 2` signs with
`0 < α ≤ 1`, at the common mean `t = √(1 - 1/m)`:
`(∑ᵢ √(1 - t²) |∂ᵢ𝓗|)² = α² m (1 - 1/m)^{m-1} ≥ α² m/3`, and `0 < 1 - 𝓗(t)² ≤ 1`, so the
first term of `eq:instance-certificate` is at least `α² m/3`.

Paper: proof of `cor:score-certificate-hardness` (instance_hardness.tex). -/
theorem parity_certificate (hm : 2 ≤ m) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    let t := Real.sqrt (1 - 1 / (m : ℝ))
    (∑ i : Fin m, Real.sqrt (1 - t ^ 2) *
        |partialDeriv (fun y : Fin m → Bool => α * parity y) (fun _ => t) i|) ^ 2 =
        α ^ 2 * m * (1 - 1 / (m : ℝ)) ^ (m - 1) ∧
      α ^ 2 * m / 3 ≤ α ^ 2 * m * (1 - 1 / (m : ℝ)) ^ (m - 1) ∧
      0 < 1 - prodExp (fun _ : Fin m => t) (fun y => α * parity y) ^ 2 ∧
      1 - prodExp (fun _ : Fin m => t) (fun y => α * parity y) ^ 2 ≤ 1 := by
  intro t
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have h1m : 0 ≤ 1 - 1 / (m : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have ht2 : t ^ 2 = 1 - 1 / (m : ℝ) := Real.sq_sqrt h1m
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht1 : t < 1 := by
    rw [Real.sqrt_lt' one_pos]
    have : 0 < 1 / (m : ℝ) := by positivity
    linarith
  have hst : Real.sqrt (1 - t ^ 2) = 1 / Real.sqrt m := by
    rw [ht2, show (1 : ℝ) - (1 - 1 / (m : ℝ)) = 1 / m by ring,
      Real.sqrt_div' 1 (by positivity : (0 : ℝ) ≤ m), Real.sqrt_one]
  have hpart : ∀ i : Fin m, partialDeriv (fun y : Fin m → Bool => α * parity y) (fun _ => t) i =
      α * t ^ (m - 1) := fun i => by
    rw [partialDeriv_parity, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  have hsum : ∑ i : Fin m, Real.sqrt (1 - t ^ 2) *
      |partialDeriv (fun y : Fin m → Bool => α * parity y) (fun _ => t) i| =
      m * (1 / Real.sqrt m) * (α * t ^ (m - 1)) := by
    simp_rw [hpart, hst]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      abs_of_nonneg (by positivity)]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsum]
    have hsq : Real.sqrt (m : ℝ) ^ 2 = m := Real.sq_sqrt (by positivity)
    have hs0 : Real.sqrt (m : ℝ) ≠ 0 := by positivity
    have htp : (t ^ (m - 1)) ^ 2 = (1 - 1 / (m : ℝ)) ^ (m - 1) := by
      rw [← pow_mul, mul_comm, pow_mul, ht2]
    calc (m * (1 / Real.sqrt m) * (α * t ^ (m - 1))) ^ 2 =
          (m : ℝ) ^ 2 / Real.sqrt m ^ 2 * α ^ 2 * (t ^ (m - 1)) ^ 2 := by
            field_simp
      _ = α ^ 2 * m * (1 - 1 / (m : ℝ)) ^ (m - 1) := by
            rw [hsq, htp]; field_simp
  · have := one_sub_inv_pow_ge hm
    have hpos : 0 ≤ α ^ 2 * m := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hpos]
  · rw [prodExp_parity, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h1 : t ^ m < 1 := pow_lt_one₀ ht0 ht1 (by omega)
    have h2 : 0 ≤ t ^ m := pow_nonneg ht0 m
    have h3 : α * t ^ m < 1 := by nlinarith
    have h4 : 0 ≤ α * t ^ m := by positivity
    nlinarith
  · nlinarith [sq_nonneg (prodExp (fun _ : Fin m => t) (fun y => α * parity y))]

/-- **The first certificate term of the parity factor.** For `f(y) = α ∏ᵢ yᵢ` on `m ≥ 2` signs
with `0 < α ≤ 1`, the first term of `eq:instance-certificate` at the common mean
`t = √(1 - 1/m)` is at least `α² m/3`.

Paper: proof of `cor:score-certificate-hardness` (instance_hardness.tex). -/
theorem parity_certificate_term (hm : 2 ≤ m) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    let t := Real.sqrt (1 - 1 / (m : ℝ))
    α ^ 2 * m / 3 ≤
      (∑ i : Fin m, Real.sqrt (1 - t ^ 2) *
          |partialDeriv (fun y : Fin m → Bool => α * parity y) (fun _ => t) i|) ^ 2 /
        (1 - prodExp (fun _ : Fin m => t) (fun y => α * parity y) ^ 2) := by
  intro t
  obtain ⟨h1, h2, h3, h4⟩ := parity_certificate hm hα0 hα1
  rw [h1, le_div_iff₀ h3]
  have hN : 0 ≤ α ^ 2 * m * (1 - 1 / (m : ℝ)) ^ (m - 1) := by
    have : 0 ≤ 1 - 1 / (m : ℝ) := by
      have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    positivity
  have hp : 0 ≤ α ^ 2 * m / 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h4 hp]

/-- The final comparison `α² m/3 ≥ c² m/48` for `α ≥ c/4 ≥ 0`.
Paper: proof of `cor:score-certificate-hardness` (instance_hardness.tex). -/
theorem certificate_gap {α c M : ℝ} (hc : 0 ≤ c) (hM : 0 ≤ M) (hα : c / 4 ≤ α) :
    c ^ 2 * M / 48 ≤ α ^ 2 * M / 3 := by
  have hα0 : 0 ≤ α := le_trans (by positivity) hα
  have : c ^ 2 / 16 ≤ α ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right this hM]

end

end ExactSampling.ScoreCertificate
