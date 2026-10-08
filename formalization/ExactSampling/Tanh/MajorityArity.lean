import Mathlib

/-!
# Odd majorities, the majority expansion, and arity bounds

This module formalizes the positive majority factory of the full version:

* `eq:majderivative` (`tanh_scalar.tex`, Section `sec:majority`): the mean `M_k` of the
  majority of `2k + 1` independent signs of mean `z` satisfies `M_k' = C_k (1 - z²)^k` with
  `C_k = (2k+1) binom(2k, k) / 4^k ≥ 1`, `M_k(0) = 0`, `M_k(1) = 1`, and `M_k` is odd. Here
  `M_k` is defined from the binomial tail, as the paper defines it;
* `lem:majority` (`tanh_scalar.tex`) and its large-radius form `lem:comptanharity`
  (`tanh_large_radius.tex`): the expansion `tanh (ρ z) / tanh ρ = Σ_k π_k M_k(z)` and the
  normalization `Σ_k π_k = 1`, derived by termwise differentiation from the power-series
  expansion of `sech² (ρ √(1 - v))` with nonnegative coefficients;
* `lem:arity` (`tanh_scalar.tex`): the sequential majority cost bound `eq:sequentialarity`;
* the exact arity draw `eq:arityenvelope` (`tanh_bits.tex`) and the acceptance loop of
  `thm:quadraticradiusbits` (`tanh_large_radius.tex`): `1/C_k = Π_{r ≤ k} 2r/(2r+1)`,
  `C_k ≥ √(k+1)`, `Σ_{r<k} 1/C_r ≤ 2√k`, and `u / tanh u ≤ 1 + u`;
* the real-variable bound `u + ∫_0^1 u tanh²(uz)/z² dz ≤ 2 max {u, u²}` of
  `lem:comptanharity` (the paper's formula for the full-majority count `Q_u`);
* the arithmetic of the one-row law (`thm:new-single-row-law`, `tanh_single_row.tex`;
  `thm:main-row`): the request bound `(r/u) Q_u ≤ 2 r (1 + r)` (`cor:comptanhrow`,
  `lem:unittanhfour`) and the elementary inequalities and constants of the lower bound;
* the algebraic facts behind `lem:coefficient-four` (`tanh_fixed_precision.tex`).

Stand-in hypotheses (named in the statements that use them):
* `d_k ≥ 0` (hypothesis `hd0` of `majority_expansion`): this is the first assertion of
  `lem:majority`, which the paper derives from the cosh product (DLMF Eq. 4.36.2); that
  derivation is not formalized. With it, `hd` asserts that the Taylor series of
  `F_ρ(v) = sech² (ρ √(1 - v))`, analytic for `|v| < 1 + π²/(4ρ²)`, represents `F_ρ` on `[0, 1]`;
* at `v = 5/4` the same series converges to `sec² (ρ/2)` (hypothesis of
  `arity_coefficient_le`);
* the coefficient `d_1 = ρ tanh ρ sech² ρ` (hypothesis of `pi_one_eq`, whose conclusion is the
  hypothesis `hw1` of `sequential_arity_bound`);
* the identity `eq:arityintegral`, `A = (ρ/q)(1 + ∫_0^1 tanh²(ρv)/v² dv)`, for the full-majority
  cost (hypothesis `hAfull` of `sequential_arity_bound`).

Not formalized: the cosh product and the nonnegativity of `d_k`; the integration-by-parts
identities behind `eq:arityintegral` and `lem:comptanharity` (the identification of the integral
formula with the expected full-majority count; `comptanh_arity_le` bounds the formula only); in
the one-row law, the identification with the expected full-majority count, the gate and
fair-sign construction, the folding of the bias into the source, the conditional charging, and
the exactness of the sampler; the finite-bit coefficient algorithm of `lem:coefficient-four`
beyond its algebraic kernels (in particular the identification of `Σ_j |a_j|` with
`cosh² (ρ √2)` and the Cauchy estimates); the product-law sampler of `lem:productaritylaw`; the
transcript information inequality and the Paley–Zygmund step of the one-row lower bound (only
their numerical consequences are checked); and the bit-work bounds.
-/

namespace ExactSampling.MajorityArity

open Real Finset

/-! ### Binomial tails and the majority polynomials -/

/-- The binomial upper tail `P(Bin(m + d, p) ≥ m) = Σ_{j ≤ d} C(m+d, m+j) p^{m+j} (1-p)^{d-j}`. -/
noncomputable def binomTail (m d : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (d + 1), ((m + d).choose (m + j) : ℝ) * p ^ (m + j) * (1 - p) ^ (d - j)

/-- The binomial tail with `d = 0`. Auxiliary for `eq:majderivative` (`tanh_scalar.tex`). -/
theorem binomTail_zero (m : ℕ) (p : ℝ) : binomTail m 0 p = p ^ m := by
  simp [binomTail]

/-- Splitting off the lowest term of the binomial tail. Auxiliary for `eq:majderivative`
(`tanh_scalar.tex`). -/
theorem binomTail_succ (m d : ℕ) (p : ℝ) :
    binomTail (m + 1) (d + 1) p =
      binomTail (m + 2) d p +
        ((m + d + 2).choose (m + 1) : ℝ) * (p ^ (m + 1) * (1 - p) ^ (d + 1)) := by
  unfold binomTail
  rw [Finset.sum_range_succ']
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    rw [show m + 1 + (d + 1) = m + 2 + d by ring, show m + 1 + (j + 1) = m + 2 + j by ring,
      Nat.add_sub_add_right]
  · rw [show m + 1 + (d + 1) = m + d + 2 by ring]
    simp [mul_assoc]

/-- The derivative of the binomial tail: `d/dp P(Bin(m+1+d, p) ≥ m+1)
= (m+1+d) C(m+d, m) p^m (1-p)^d`. Auxiliary for `eq:majderivative` (`tanh_scalar.tex`). -/
theorem hasDerivAt_binomTail (d : ℕ) : ∀ (m : ℕ) (p : ℝ),
    HasDerivAt (binomTail (m + 1) d)
      ((((m + 1 + d) * (m + d).choose m : ℕ) : ℝ) * p ^ m * (1 - p) ^ d) p := by
  induction d with
  | zero =>
      intro m p
      have e : binomTail (m + 1) 0 = fun p => p ^ (m + 1) := funext (binomTail_zero (m + 1))
      rw [e]
      have := hasDerivAt_pow (m + 1) p
      convert this using 1
      simp
  | succ d ih =>
      intro m p
      have e : binomTail (m + 1) (d + 1) = fun p => binomTail (m + 2) d p +
          ((m + d + 2).choose (m + 1) : ℝ) * (p ^ (m + 1) * (1 - p) ^ (d + 1)) :=
        funext (binomTail_succ m d)
      rw [e]
      have h1 := ih (m + 1) p
      have ha := hasDerivAt_pow (m + 1) p
      have hc := (hasDerivAt_pow (d + 1) (1 - p)).comp p ((hasDerivAt_id p).const_sub 1)
      have hb : HasDerivAt (fun p : ℝ => (1 - p) ^ (d + 1))
          (((d + 1 : ℕ) : ℝ) * (1 - p) ^ d * (-1)) p :=
        hc.congr_deriv (by simp)
      have h2 := (ha.mul hb).const_mul ((m + d + 2).choose (m + 1) : ℝ)
      have h3 := h1.add h2
      refine h3.congr_deriv ?_
      -- `(d+1) C(m+d+2, m+1) = (m+d+2) C(m+d+1, m+1)` and
      -- `(m+1) C(m+d+2, m+1) = (m+d+2) C(m+d+1, m)`
      have i1 : (m + d + 1).choose (m + 1) * (m + d + 2) =
          (m + d + 2).choose (m + 1) * (d + 1) := by
        have := Nat.choose_mul_succ_eq (m + d + 1) (m + 1)
        rw [show m + d + 1 + 1 - (m + 1) = d + 1 by omega] at this
        simpa [show m + d + 1 + 1 = m + d + 2 by ring] using this
      have i2 : (m + d + 2) * (m + d + 1).choose m = (m + d + 2).choose (m + 1) * (m + 1) := by
        have := Nat.add_one_mul_choose_eq (m + d + 1) m
        simpa [show m + d + 1 + 1 = m + d + 2 by ring] using this
      have i1r : ((m + d + 1).choose (m + 1) : ℝ) * ((m : ℝ) + d + 2) =
          ((m + d + 2).choose (m + 1) : ℝ) * ((d : ℝ) + 1) := by exact_mod_cast i1
      have i2r : ((m : ℝ) + d + 2) * ((m + d + 1).choose m : ℝ) =
          ((m + d + 2).choose (m + 1) : ℝ) * ((m : ℝ) + 1) := by exact_mod_cast i2
      simp only [Nat.add_sub_cancel]
      rw [show m + 1 + d = m + d + 1 by ring, show m + (d + 1) = m + d + 1 by ring,
        show m + 1 + 1 + d = m + d + 2 by ring]
      push_cast
      rw [pow_succ (1 - p) d, pow_succ p m]
      linear_combination (p ^ m * p * (1 - p) ^ d) * i1r - (p ^ m * (1 - p) ^ d * (1 - p)) * i2r

/-- The constant `C_k = (2k+1) binom(2k, k) / 4^k` of `eq:majderivative` (`tanh_scalar.tex`). -/
noncomputable def majC (k : ℕ) : ℝ := (2 * k + 1) * (Nat.centralBinom k : ℝ) / 4 ^ k

/-- The mean of the majority of `2k + 1` independent signs of mean `z`: twice the probability
that at least `k + 1` of them are `+1`, minus one. Section `sec:majority` (`tanh_scalar.tex`). -/
noncomputable def majMean (k : ℕ) (z : ℝ) : ℝ := 2 * binomTail (k + 1) k ((1 + z) / 2) - 1

/-- `M_k' = C_k (1 - z²)^k`. Paper: `eq:majderivative` (`tanh_scalar.tex`) and
`eq:main-majority` (`exact_sampling_networks.tex`). -/
theorem hasDerivAt_majMean (k : ℕ) (z : ℝ) :
    HasDerivAt (majMean k) (majC k * (1 - z ^ 2) ^ k) z := by
  have hlin : HasDerivAt (fun z : ℝ => (1 + z) / 2) (1 / 2) z := by
    have := ((hasDerivAt_id z).const_add 1).div_const 2
    simpa using this
  have h := ((hasDerivAt_binomTail k k ((1 + z) / 2)).comp z hlin).const_mul 2
  have h2 := h.sub_const 1
  refine h2.congr_deriv ?_
  unfold majC
  rw [Nat.centralBinom_eq_two_mul_choose, show 2 * k = k + k by ring]
  have hq : (1 - z ^ 2) ^ k = 4 ^ k * (((1 + z) / 2) ^ k * (1 - (1 + z) / 2) ^ k) := by
    rw [← mul_pow, ← mul_pow]; congr 1; ring
  rw [hq]
  push_cast
  field_simp
  ring

/-- `M_k(1) = 1`. Paper: `eq:majderivative` (`tanh_scalar.tex`). -/
theorem majMean_one (k : ℕ) : majMean k 1 = 1 := by
  unfold majMean binomTail
  rw [show (1 + (1 : ℝ)) / 2 = 1 by norm_num]
  rw [Finset.sum_eq_single k]
  · simp
    norm_num
  · intro j hj hjk
    have : 0 < k - j := by
      have := Finset.mem_range.mp hj
      omega
    simp [zero_pow this.ne']
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k)) h

/-- `M_k(0) = 0`: the majority of fair signs is fair. Paper: `eq:majderivative`
(`tanh_scalar.tex`). -/
theorem majMean_zero (k : ℕ) : majMean k 0 = 0 := by
  unfold majMean binomTail
  rw [show (1 + (0 : ℝ)) / 2 = 1 / 2 by norm_num, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  have hterm : ∀ j ∈ Finset.range (k + 1),
      ((k + 1 + k).choose (k + 1 + j) : ℝ) * (1 / 2) ^ (k + 1 + j) * (1 / 2) ^ (k - j) =
        ((2 * k + 1).choose (k - j) : ℝ) * (1 / 2) ^ (2 * k + 1) := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [mul_assoc, ← pow_add, show k + 1 + j + (k - j) = 2 * k + 1 by omega]
    congr 2
    rw [show k + 1 + k = 2 * k + 1 by ring]
    exact_mod_cast Nat.choose_symm_of_eq_add (by omega)
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  have hrefl : ∑ j ∈ Finset.range (k + 1), ((2 * k + 1).choose (k - j) : ℝ) =
      ∑ j ∈ Finset.range (k + 1), ((2 * k + 1).choose j : ℝ) := by
    have := Finset.sum_range_reflect (fun j => ((2 * k + 1).choose j : ℝ)) (k + 1)
    simpa using this
  rw [hrefl]
  have hhalf : ∑ j ∈ Finset.range (k + 1), ((2 * k + 1).choose j : ℝ) = 4 ^ k := by
    exact_mod_cast Nat.sum_range_choose_halfway k
  rw [hhalf, pow_succ, pow_mul]
  have h4 : (4 : ℝ) ^ k * ((1 / 2) ^ 2) ^ k = 1 := by
    rw [← mul_pow]; norm_num
  linear_combination h4

/-- `M_k` is odd. Paper: `lem:majority` (`tanh_scalar.tex`), "oddness gives negative `z`". -/
theorem majMean_neg (k : ℕ) (z : ℝ) : majMean k (-z) = -majMean k z := by
  have hd : ∀ x, HasDerivAt (fun x => majMean k x + majMean k (-x)) 0 x := by
    intro x
    have h1 := hasDerivAt_majMean k x
    have h2 := (hasDerivAt_majMean k (-x)).comp x (hasDerivAt_neg x)
    refine (h1.add h2).congr_deriv ?_
    rw [neg_sq]; ring
  have hconst := is_const_of_deriv_eq_zero (f := fun x => majMean k x + majMean k (-x))
    (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) z 0
  simp only [neg_zero, majMean_zero, add_zero] at hconst
  linarith

/-! ### The constants `C_k` -/

/-- `C_0 = 1`. Auxiliary for `eq:majderivative` (`tanh_scalar.tex`). -/
theorem majC_zero : majC 0 = 1 := by simp [majC]

/-- `C_1 = 3/2`. Used for `π_1` in `lem:arity` (`tanh_scalar.tex`). -/
theorem majC_one : majC 1 = 3 / 2 := by
  simp [majC, Nat.centralBinom_eq_two_mul_choose]
  norm_num

/-- `C_k > 0`. Auxiliary for `eq:majderivative` (`tanh_scalar.tex`). -/
theorem majC_pos (k : ℕ) : 0 < majC k := by
  unfold majC
  have := Nat.centralBinom_pos k
  positivity

/-- `C_{k+1} = C_k (2k+3)/(2k+2)`, i.e. `C_k / C_{k-1} = (2k+1)/(2k)`.
Paper: `thm:quadraticradiusbits` (`tanh_large_radius.tex`), proof; also `lem:comptanharity`. -/
theorem majC_succ (k : ℕ) : majC (k + 1) = majC k * ((2 * k + 3) / (2 * k + 2)) := by
  unfold majC
  have h := Nat.succ_mul_centralBinom_succ k
  have hr : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ) =
      2 * (2 * k + 1) * (Nat.centralBinom k : ℝ) := by exact_mod_cast h
  have hk : (0 : ℝ) < k + 1 := by positivity
  rw [pow_succ]
  push_cast
  field_simp
  linear_combination (2 * (k : ℝ) + 3) * 2 * hr

/-- `C_k ≥ 1`. Paper: `eq:majderivative` (`tanh_scalar.tex`). -/
theorem one_le_majC (k : ℕ) : 1 ≤ majC k := by
  induction k with
  | zero => rw [majC_zero]
  | succ k ih =>
      rw [majC_succ]
      have : (1 : ℝ) ≤ (2 * k + 3) / (2 * k + 2) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      nlinarith

/-- The acceptance probability of the arity loop is a finite product of rational coins:
`1 / C_k = Π_{r=1}^{k} 2r/(2r+1)`. Paper: `thm:quadraticradiusbits`
(`tanh_large_radius.tex`). -/
theorem inv_majC_eq_prod (k : ℕ) :
    1 / majC k = ∏ r ∈ Finset.range k, (2 * ((r : ℝ) + 1)) / (2 * ((r : ℝ) + 1) + 1) := by
  induction k with
  | zero => simp [majC_zero]
  | succ k ih =>
      rw [Finset.prod_range_succ, ← ih, majC_succ]
      have := majC_pos k
      field_simp
      ring

/-- `C_k ≥ √(k+1)`, in squared form. Paper: `thm:quadraticradiusbits`
(`tanh_large_radius.tex`). -/
theorem majC_sq_ge (k : ℕ) : (k : ℝ) + 1 ≤ majC k ^ 2 := by
  induction k with
  | zero => simp [majC_zero]
  | succ k ih =>
      rw [majC_succ, mul_pow]
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hr : ((k : ℝ) + 1 + 1) ≤ ((k : ℝ) + 1) * ((2 * k + 3) / (2 * k + 2)) ^ 2 := by
        rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
        nlinarith
      have hsq : 0 ≤ ((2 * (k : ℝ) + 3) / (2 * k + 2)) ^ 2 := sq_nonneg _
      push_cast
      nlinarith

/-- `C_k ≥ √(k+1)`. Paper: `thm:quadraticradiusbits` (`tanh_large_radius.tex`). -/
theorem sqrt_le_majC (k : ℕ) : √((k : ℝ) + 1) ≤ majC k := by
  rw [sqrt_le_left (majC_pos k).le]
  exact majC_sq_ge k

/-- The expected number of rational coins in the acceptance loop, given `K = k`, is
`Σ_{r<k} 1/C_r ≤ 2√k`. Paper: `thm:quadraticradiusbits` (`tanh_large_radius.tex`). -/
theorem sum_inv_majC_le (k : ℕ) : ∑ r ∈ Finset.range k, 1 / majC r ≤ 2 * √(k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      have hb : 0 < √((k : ℝ) + 1) := sqrt_pos.mpr (by positivity)
      have hinv : 1 / majC k ≤ 1 / √((k : ℝ) + 1) :=
        one_div_le_one_div_of_le hb (sqrt_le_majC k)
      have ha := sqrt_nonneg (k : ℝ)
      have ha2 : √(k : ℝ) ^ 2 = k := sq_sqrt (Nat.cast_nonneg k)
      have hb2 : √((k : ℝ) + 1) ^ 2 = k + 1 := sq_sqrt (by positivity)
      have key : 2 * √(k : ℝ) + 1 / √((k : ℝ) + 1) ≤ 2 * √((k : ℝ) + 1) := by
        rw [← sub_nonneg]
        have : 2 * √((k : ℝ) + 1) - (2 * √(k : ℝ) + 1 / √((k : ℝ) + 1)) =
            (√((k : ℝ) + 1) - √(k : ℝ)) ^ 2 / √((k : ℝ) + 1) := by
          field_simp
          nlinarith
        rw [this]
        positivity
      push_cast
      linarith

/-! ### The majority expansion -/

/-- The derivative of `tanh` is `1 / cosh²`. Auxiliary for `lem:majority` (`tanh_scalar.tex`). -/
theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt tanh (1 / cosh x ^ 2) x := by
  have h := (hasDerivAt_sinh x).div (hasDerivAt_cosh x) (cosh_pos x).ne'
  have e : (sinh / cosh : ℝ → ℝ) = tanh := by
    funext y; rw [Pi.div_apply, tanh_eq_sinh_div_cosh]
  rw [e] at h
  refine h.congr_deriv ?_
  have hc := cosh_pos x
  have := cosh_sq_sub_sinh_sq x
  field_simp
  linarith

/-- `-1 ≤ M_k(z) ≤ 1` on `[-1, 1]`: `M_k` is nondecreasing there. Auxiliary for
`lem:majority` (`tanh_scalar.tex`). -/
theorem abs_majMean_le_one (k : ℕ) {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    |majMean k z| ≤ 1 := by
  have hmono : MonotoneOn (majMean k) (Set.Icc (-1 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x _ => (hasDerivAt_majMean k x).continuousAt.continuousWithinAt
    · exact fun x _ => (hasDerivAt_majMean k x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hasDerivAt_majMean k x).deriv]
      have : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
      exact mul_nonneg (majC_pos k).le (pow_nonneg this k)
  have h1 := hmono hz ⟨by norm_num, by norm_num⟩ hz.2
  have h2 := hmono ⟨by norm_num, by norm_num⟩ hz hz.1
  rw [majMean_one] at h1
  rw [majMean_neg, majMean_one] at h2
  exact abs_le.mpr ⟨h2, h1⟩

/-- The majority expansion `tanh (ρ z) / tanh ρ = Σ_k π_k M_k(z)` on `[-1, 1]`, with
`π_k = (ρ / tanh ρ) d_k / C_k` a probability distribution (`π_k ≥ 0`, `Σ_k π_k = 1`).
Stand-in hypothesis `hd0`: `d_k ≥ 0`, the first assertion of `lem:majority`, which the paper
derives from the cosh product (DLMF Eq. 4.36.2); that derivation is not formalized. Hypothesis
`hd`: the Taylor series of `F_ρ(v) = sech² (ρ √(1 - v))` represents `F_ρ` on `[0, 1]`.
Paper: `lem:majority` (`tanh_scalar.tex`), `eq:generating` and `eq:majorityexpansion`; also
`lem:comptanharity` (`tanh_large_radius.tex`). -/
theorem majority_expansion (ρ : ℝ) (hρ : 0 < ρ) (d : ℕ → ℝ) (hd0 : ∀ k, 0 ≤ d k)
    (hd : ∀ v ∈ Set.Icc (0 : ℝ) 1,
      HasSum (fun k => d k * v ^ k) (1 / cosh (ρ * √(1 - v)) ^ 2)) :
    (∀ k, 0 ≤ ρ / tanh ρ * d k / majC k) ∧ HasSum (fun k => ρ / tanh ρ * d k / majC k) 1 ∧
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        HasSum (fun k => ρ / tanh ρ * d k / majC k * majMean k z) (tanh (ρ * z) / tanh ρ) := by
  have hq : 0 < tanh ρ := by
    rw [tanh_eq_sinh_div_cosh]; exact div_pos (sinh_pos_iff.mpr hρ) (cosh_pos ρ)
  set c := ρ / tanh ρ with hc
  have hc0 : 0 < c := div_pos hρ hq
  set w : ℕ → ℝ := fun k => c * d k / majC k with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => div_nonneg (mul_nonneg hc0.le (hd0 k)) (majC_pos k).le
  have hwC : ∀ k, w k * majC k = c * d k := fun k => by
    simp only [hw]; field_simp [(majC_pos k).ne']
  -- the coefficients sum to one
  have hd1 : HasSum d 1 := by
    have := hd 1 ⟨by norm_num, le_rfl⟩
    simpa using this
  have hwle : ∀ k, w k ≤ c * d k := fun k => by
    simp only [hw]
    rw [div_le_iff₀ (majC_pos k)]
    exact le_mul_of_one_le_right (mul_nonneg hc0.le (hd0 k)) (one_le_majC k)
  have hwsum : Summable w :=
    Summable.of_nonneg_of_le hw0 hwle (hd1.summable.mul_left c)
  -- summability of the mixture on `[-1, 1]`
  have hsumz : ∀ z ∈ Set.Icc (-1 : ℝ) 1, Summable (fun k => w k * majMean k z) := by
    intro z hz
    refine Summable.of_norm_bounded hwsum (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 k)]
    exact mul_le_of_le_one_right (hw0 k) (abs_majMean_le_one k hz)
  -- termwise differentiation on `(-7/5, 7/5)`
  set t : Set ℝ := Set.Ioo (-7 / 5) (7 / 5) with ht
  have hderivG : ∀ y ∈ t, HasDerivAt (fun x => ∑' k, w k * majMean k x)
      (∑' k, w k * (majC k * (1 - y ^ 2) ^ k)) y := by
    intro y hy
    apply hasDerivAt_tsum_of_isPreconnected (u := fun k => c * d k)
      (hd1.summable.mul_left c) isOpen_Ioo isPreconnected_Ioo
      (fun k x _ => (hasDerivAt_majMean k x).const_mul (w k)) _ (y₀ := 0)
      (by simp only [Set.mem_Ioo]; norm_num) _ hy
    · intro k x hx
      rw [Real.norm_eq_abs, ← mul_assoc, hwC, abs_mul, abs_of_nonneg (mul_nonneg hc0.le (hd0 k)),
        abs_pow]
      apply mul_le_of_le_one_right (mul_nonneg hc0.le (hd0 k))
      apply pow_le_one₀ (abs_nonneg _)
      rw [abs_le]
      obtain ⟨hx1, hx2⟩ := hx
      constructor <;> nlinarith
    · simp [majMean_zero]
  -- the derivative series equals `c sech² (ρ y)` on `[-1, 1]`
  have hderiv_eq : ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      ∑' k, w k * (majC k * (1 - y ^ 2) ^ k) = c * (1 / cosh (ρ * y) ^ 2) := by
    intro y hy
    have hv : 1 - y ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> nlinarith [hy.1, hy.2]
    have hs := (hd _ hv).mul_left c
    have hsq : √(1 - (1 - y ^ 2)) = |y| := by rw [sub_sub_cancel, sqrt_sq_eq_abs]
    rw [hsq] at hs
    have hcosh : cosh (ρ * |y|) = cosh (ρ * y) := by
      have : ρ * |y| = |ρ * y| := by rw [abs_mul, abs_of_pos hρ]
      rw [this, cosh_abs]
    rw [hcosh] at hs
    rw [← hs.tsum_eq]
    congr 1
    funext k
    rw [← mul_assoc, hwC, mul_assoc]
  -- the target has the same derivative
  have hderivH : ∀ y, HasDerivAt (fun x => tanh (ρ * x) / tanh ρ)
      (c * (1 / cosh (ρ * y) ^ 2)) y := by
    intro y
    have h1 : HasDerivAt (fun x => ρ * x) ρ y := by
      simpa using (hasDerivAt_id y).const_mul ρ
    have h2 := ((hasDerivAt_tanh (ρ * y)).comp y h1).div_const (tanh ρ)
    refine h2.congr_deriv ?_
    simp only [hc]
    ring
  -- the difference is constant on `[-1, 1]`
  set K : ℝ → ℝ := fun x => (∑' k, w k * majMean k x) - tanh (ρ * x) / tanh ρ with hK
  have hIcc_sub : Set.Icc (-1 : ℝ) 1 ⊆ t := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hKd : ∀ y ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt K 0 y := by
    intro y hy
    have := (hderivG y (hIcc_sub hy)).sub (hderivH y)
    refine this.congr_deriv ?_
    rw [hderiv_eq y hy, sub_self]
  have hK0 : K 0 = 0 := by simp [hK, majMean_zero]
  have hKz : ∀ z ∈ Set.Icc (-1 : ℝ) 1, K z = 0 := by
    intro z hz
    rcases lt_trichotomy z 0 with hneg | rfl | hpos
    · have hcont : ContinuousOn K (Set.Icc z 0) := fun x hx =>
        (hKd x ⟨by linarith [hz.1, hx.1], by linarith [hx.2]⟩).continuousAt.continuousWithinAt
      obtain ⟨c', hc', hslope⟩ := exists_hasDerivAt_eq_slope K (fun _ => (0 : ℝ)) hneg hcont
        (fun x hx => hKd x ⟨by linarith [hz.1, hx.1], by linarith [hx.2]⟩)
      rw [hK0] at hslope
      have hz0 : (0 : ℝ) - z ≠ 0 := by linarith
      field_simp at hslope
      linarith
    · exact hK0
    · have hcont : ContinuousOn K (Set.Icc 0 z) := fun x hx =>
        (hKd x ⟨by linarith [hx.1], by linarith [hz.2, hx.2]⟩).continuousAt.continuousWithinAt
      obtain ⟨c', hc', hslope⟩ := exists_hasDerivAt_eq_slope K (fun _ => (0 : ℝ)) hpos hcont
        (fun x hx => hKd x ⟨by linarith [hx.1], by linarith [hz.2, hx.2]⟩)
      rw [hK0] at hslope
      have hz0 : z - 0 ≠ 0 := by linarith
      field_simp at hslope
      linarith
  have hexp : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      HasSum (fun k => w k * majMean k z) (tanh (ρ * z) / tanh ρ) := by
    intro z hz
    have := (hsumz z hz).hasSum
    have hKz' := hKz z hz
    simp only [hK] at hKz'
    rwa [sub_eq_zero.mp hKz'] at this
  refine ⟨hw0, ?_, hexp⟩
  have h1 := hexp 1 ⟨by norm_num, le_rfl⟩
  simp only [majMean_one, mul_one] at h1
  rwa [div_self hq.ne'] at h1

/-! ### Hyperbolic inequalities used by the arity bounds -/

/-- `tanh` is continuous. Auxiliary for `lem:arity` and `lem:comptanharity`. -/
theorem continuous_tanh : Continuous tanh := by
  have e : tanh = fun y => sinh y / cosh y := funext tanh_eq_sinh_div_cosh
  rw [e]
  exact continuous_sinh.div continuous_cosh (fun y => (cosh_pos y).ne')

/-- `tanh x ≤ x` for `x ≥ 0`. Auxiliary for `lem:arity` (`tanh_scalar.tex`). -/
theorem tanh_le_self {x : ℝ} (hx : 0 ≤ x) : tanh x ≤ x := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]; simp
  obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope tanh (fun y => 1 / cosh y ^ 2) h
    continuous_tanh.continuousOn (fun y _ => hasDerivAt_tanh y)
  have hc1 : 1 / cosh c ^ 2 ≤ 1 := by
    rw [div_le_one (by have := cosh_pos c; positivity)]
    nlinarith [one_le_cosh c]
  rw [hc, tanh_zero, sub_zero, sub_zero, div_le_one h] at hc1
  exact hc1

/-- `tanh² x ≤ x²`, i.e. `sech² x ≥ 1 - x²`. Paper: `lem:arity` (`tanh_scalar.tex`). -/
theorem tanh_sq_le_sq (x : ℝ) : tanh x ^ 2 ≤ x ^ 2 := by
  rcases le_total 0 x with h | h
  · have h1 := tanh_le_self h
    have h0 : 0 ≤ tanh x := by
      rw [tanh_eq_sinh_div_cosh]; exact div_nonneg (sinh_nonneg_iff.mpr h) (cosh_pos x).le
    nlinarith
  · have h1 := tanh_le_self (neg_nonneg.mpr h)
    have h0 : 0 ≤ tanh (-x) := by
      rw [tanh_eq_sinh_div_cosh]
      exact div_nonneg (sinh_nonneg_iff.mpr (neg_nonneg.mpr h)) (cosh_pos _).le
    rw [tanh_neg] at h1 h0
    nlinarith

/-- Termwise comparison behind `u coth u ≤ 1 + u²/3`. Auxiliary for `lem:arity`
(`tanh_scalar.tex`). -/
theorem sinh_cosh_series_term_nonneg {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    0 ≤ u ^ 2 / 3 * (u ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) +
      u ^ (2 * (n + 1) + 1) / ((2 * (n + 1) + 1).factorial : ℝ) -
      u * (u ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ)) := by
  have hf1 : ((2 * (n + 1)).factorial : ℝ) = (2 * n + 2) * ((2 * n + 1).factorial : ℝ) := by
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Nat.factorial_succ]
    push_cast; ring
  have hf2 : ((2 * (n + 1) + 1).factorial : ℝ) =
      (2 * n + 3) * (2 * n + 2) * ((2 * n + 1).factorial : ℝ) := by
    rw [show 2 * (n + 1) + 1 = ((2 * n + 1) + 1) + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast; ring
  have hp1 : u ^ (2 * (n + 1) + 1) = u ^ (2 * n + 1) * u ^ 2 := by
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, pow_add]
  have hp2 : u ^ (2 * (n + 1)) = u ^ (2 * n + 1) * u := by
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, pow_succ]
  rw [hf1, hf2, hp1, hp2]
  have hF : 0 < ((2 * n + 1).factorial : ℝ) := by positivity
  have key : u ^ 2 / 3 * (u ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) +
      u ^ (2 * n + 1) * u ^ 2 / ((2 * n + 3) * (2 * n + 2) * ((2 * n + 1).factorial : ℝ)) -
      u * (u ^ (2 * n + 1) * u / ((2 * n + 2) * ((2 * n + 1).factorial : ℝ))) =
      u ^ (2 * n + 1) * u ^ 2 / ((2 * n + 1).factorial : ℝ) *
        ((2 * n) / (3 * (2 * n + 3))) := by
    field_simp
    ring
  rw [key]
  positivity

/-- `u cosh u ≤ (1 + u²/3) sinh u` for `u ≥ 0`, from the series of `sinh` and `cosh`.
Auxiliary for `lem:arity` (`tanh_scalar.tex`). -/
theorem mul_cosh_le {u : ℝ} (hu : 0 ≤ u) : u * cosh u ≤ (1 + u ^ 2 / 3) * sinh u := by
  set b : ℕ → ℝ := fun n => u ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) with hb
  set c : ℕ → ℝ := fun n => u ^ (2 * n) / ((2 * n).factorial : ℝ) with hc
  have hS : HasSum b (sinh u) := hasSum_sinh u
  have hC : HasSum c (cosh u) := hasSum_cosh u
  have hS1 : HasSum (fun n => b (n + 1)) (sinh u - u) := by
    have := (hasSum_nat_add_iff' 1).mpr hS
    simpa [hb] using this
  have hC1 : HasSum (fun n => c (n + 1)) (cosh u - 1) := by
    have := (hasSum_nat_add_iff' 1).mpr hC
    simpa [hc] using this
  have hsum : HasSum (fun n => u ^ 2 / 3 * b n + b (n + 1) - u * c (n + 1))
      (u ^ 2 / 3 * sinh u + (sinh u - u) - u * (cosh u - 1)) :=
    ((hS.mul_left (u ^ 2 / 3)).add hS1).sub (hC1.mul_left u)
  have hnn : 0 ≤ u ^ 2 / 3 * sinh u + (sinh u - u) - u * (cosh u - 1) :=
    hsum.nonneg (fun n => sinh_cosh_series_term_nonneg hu n)
  nlinarith [hnn]

/-- `ρ coth ρ ≤ 1 + ρ²/3` for `ρ > 0`. Paper: `lem:arity` (`tanh_scalar.tex`). -/
theorem mul_coth_le {u : ℝ} (hu : 0 < u) : u / tanh u ≤ 1 + u ^ 2 / 3 := by
  have hs : 0 < sinh u := sinh_pos_iff.mpr hu
  have hc := cosh_pos u
  rw [tanh_eq_sinh_div_cosh, div_div_eq_mul_div, div_le_iff₀ hs]
  exact mul_cosh_le hu.le

/-- `u coth u ≤ 1 + u`: the mean number `u / tanh u` of arity trials is at most `1 + u`.
Paper: `thm:quadraticradiusbits` (`tanh_large_radius.tex`). -/
theorem div_tanh_le_one_add {u : ℝ} (hu : 0 < u) : u / tanh u ≤ 1 + u := by
  have hs : 0 < sinh u := sinh_pos_iff.mpr hu
  have hc := cosh_pos u
  rw [tanh_eq_sinh_div_cosh, div_div_eq_mul_div, div_le_iff₀ hs]
  -- `u (cosh u - sinh u) ≤ sinh u`, i.e. `2u ≤ e^{2u} - 1`
  have h2 := add_one_le_exp (2 * u)
  have hcs : cosh u - sinh u = exp (-u) := by rw [cosh_eq, sinh_eq]; ring
  have hsinh : sinh u = (exp u - exp (-u)) / 2 := sinh_eq u
  have he : exp (2 * u) = exp u * exp u := by rw [← exp_add]; ring_nf
  have hpos := exp_pos u
  have hinv : exp (-u) * exp u = 1 := by rw [← exp_add]; simp
  have : u * exp (-u) ≤ sinh u := by
    rw [hsinh]
    have hneg := exp_pos (-u)
    nlinarith [mul_le_mul_of_nonneg_left h2 hneg.le]
  nlinarith

/-! ### Sequential majority cost -/

/-- The sequential majority of three signs stops after two agreeing signs: its expected
source count is `2 (p² + (1-p)²) + 3 · 2p(1-p) = 5/2 - z²/2` with `z = 2p - 1`.
Paper: `lem:arity` (`tanh_scalar.tex`), "for `K = 1`, sequential majority costs `5/2 - z²/2`". -/
theorem majority_three_expected_cost (p : ℝ) :
    2 * (p ^ 2 + (1 - p) ^ 2) + 3 * (2 * p * (1 - p)) = 5 / 2 - (2 * p - 1) ^ 2 / 2 := by
  ring

/-- The first mixture weight `π_1 = (2/3) ρ² sech² ρ`, from the coefficient
`d_1 = ρ tanh ρ sech² ρ` of `F_ρ`. Paper: `lem:arity` (`tanh_scalar.tex`). -/
theorem pi_one_eq {ρ : ℝ} (hρ : 0 < ρ) (d1 : ℝ) (hd1 : d1 = ρ * tanh ρ * (1 - tanh ρ ^ 2)) :
    ρ / tanh ρ * d1 / majC 1 = 2 / 3 * ρ ^ 2 * (1 - tanh ρ ^ 2) := by
  have hq : 0 < tanh ρ := by
    rw [tanh_eq_sinh_div_cosh]; exact div_pos (sinh_pos_iff.mpr hρ) (cosh_pos ρ)
  rw [majC_one, hd1]
  field_simp

/-- The arity integral of `eq:arityintegral` is at most `ρ²`, since `tanh² (ρ v) ≤ ρ² v²`.
Paper: `eq:arityintegral` (`tanh_scalar.tex`). -/
theorem arity_integral_le (ρ : ℝ) : ∫ v in (0 : ℝ)..1, tanh (ρ * v) ^ 2 / v ^ 2 ≤ ρ ^ 2 := by
  by_cases hint : IntervalIntegrable (fun v => tanh (ρ * v) ^ 2 / v ^ 2) MeasureTheory.volume 0 1
  · calc ∫ v in (0 : ℝ)..1, tanh (ρ * v) ^ 2 / v ^ 2 ≤ ∫ _v in (0 : ℝ)..1, ρ ^ 2 :=
          intervalIntegral.integral_mono_on (by norm_num) hint intervalIntegrable_const
            (fun v _ => by
              rcases eq_or_ne v 0 with h | h
              · rw [h]; simp; positivity
              · rw [div_le_iff₀ (by positivity)]
                have := tanh_sq_le_sq (ρ * v)
                rw [mul_pow] at this
                exact this)
      _ = ρ ^ 2 := by simp
  · rw [intervalIntegral.integral_undef hint]; positivity

/-- The sequential majority cost `A_seq ≤ 1 + (1 - z²/3) ρ² + ρ⁴`. Stand-in hypothesis `hAfull`:
the full-majority cost `A = Σ_k π_k (2k+1)` equals `(ρ/q)(1 + ∫_0^1 tanh²(ρv)/v² dv)`
(`eq:arityintegral`), whose integral is bounded by `ρ²` in `arity_integral_le`. The sequential
cost `cost k` of index `k` is at most `2k + 1`, the index-one cost is `5/2 - z²/2`
(`majority_three_expected_cost`), and `π_1 = (2/3) ρ² sech² ρ` (`pi_one_eq`).
Paper: `lem:arity` (`tanh_scalar.tex`), `eq:sequentialarity`. -/
theorem sequential_arity_bound {ρ z : ℝ} (hρ : 0 < ρ) (hz : z ^ 2 ≤ 1) (w cost : ℕ → ℝ)
    (Afull Aseq : ℝ) (hw0 : ∀ k, 0 ≤ w k)
    (hw1 : w 1 = 2 / 3 * ρ ^ 2 * (1 - tanh ρ ^ 2))
    (hfull : HasSum (fun k => w k * (2 * k + 1)) Afull)
    (hAfull : Afull = ρ / tanh ρ * (1 + ∫ v in (0 : ℝ)..1, tanh (ρ * v) ^ 2 / v ^ 2))
    (hcost : ∀ k : ℕ, cost k ≤ 2 * k + 1) (hcost1 : cost 1 = 5 / 2 - z ^ 2 / 2)
    (hseq : HasSum (fun k => w k * cost k) Aseq) :
    Aseq ≤ 1 + (1 - z ^ 2 / 3) * ρ ^ 2 + ρ ^ 4 := by
  have hAfull : Afull ≤ ρ / tanh ρ * (1 + ρ ^ 2) := by
    have hq : 0 < tanh ρ := by
      rw [tanh_eq_sinh_div_cosh]; exact div_pos (sinh_pos_iff.mpr hρ) (cosh_pos ρ)
    rw [hAfull]
    exact mul_le_mul_of_nonneg_left (by linarith [arity_integral_le ρ]) (div_pos hρ hq).le
  -- the saving at index one
  have hdiff : HasSum (fun k => w k * ((2 * k + 1) - cost k)) (Afull - Aseq) := by
    have := hfull.sub hseq
    convert this using 1
    funext k; ring
  have hsave : w 1 * ((2 * ((1 : ℕ) : ℝ) + 1) - cost 1) ≤ Afull - Aseq :=
    le_hasSum hdiff 1 (fun k _ => mul_nonneg (hw0 k) (by linarith [hcost k]))
  rw [hcost1, hw1] at hsave
  push_cast at hsave
  have hc := mul_coth_le hρ
  have hs := tanh_sq_le_sq ρ
  have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  have hA : Afull ≤ (1 + ρ ^ 2 / 3) * (1 + ρ ^ 2) :=
    hAfull.trans (mul_le_mul_of_nonneg_right hc (by positivity))
  have hz0 : 0 ≤ z ^ 2 := sq_nonneg z
  -- `π_1 (1 + z²)/2 ≥ (1 + z²)/3 · ρ² (1 - ρ²)`
  have hsech : 2 / 3 * ρ ^ 2 * (1 - ρ ^ 2) * ((1 + z ^ 2) / 2) ≤
      2 / 3 * ρ ^ 2 * (1 - tanh ρ ^ 2) * ((1 + z ^ 2) / 2) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hpoly : (1 + ρ ^ 2 / 3) * (1 + ρ ^ 2) - 2 / 3 * ρ ^ 2 * (1 - ρ ^ 2) * ((1 + z ^ 2) / 2) =
      1 + (1 - z ^ 2 / 3) * ρ ^ 2 + (2 + z ^ 2) / 3 * ρ ^ 4 := by ring
  have hlast : (2 + z ^ 2) / 3 * ρ ^ 4 ≤ ρ ^ 4 := by
    have : 0 ≤ ρ ^ 4 := by positivity
    nlinarith
  have hsave' : 2 / 3 * ρ ^ 2 * (1 - tanh ρ ^ 2) * ((1 + z ^ 2) / 2) ≤ Afull - Aseq := by
    have e : (2 * 1 + 1 : ℝ) - (5 / 2 - z ^ 2 / 2) = (1 + z ^ 2) / 2 := by ring
    rw [e] at hsave
    exact hsave
  linarith

/-! ### The large-radius arity bound -/

/-- The paper's formula for the full-majority source count of `lem:comptanharity`,
`Q_u = u + ∫_0^1 u tanh² (u z) / z² dz`, is at most `2 max {u, u²}`. This bounds the formula
only; its identification with the expected count (integration by parts and Tonelli) is not
formalized. Paper: `lem:comptanharity` (`tanh_large_radius.tex`), the final estimate. -/
theorem comptanh_arity_le {u : ℝ} (hu : 0 < u) :
    u + ∫ z in (0 : ℝ)..1, u * tanh (u * z) ^ 2 / z ^ 2 ≤ 2 * max u (u ^ 2) := by
  set f : ℝ → ℝ := fun z => u * tanh (u * z) ^ 2 / z ^ 2 with hf
  have hbound : ∀ z, f z ≤ u * u ^ 2 := by
    intro z
    simp only [hf]
    rcases eq_or_ne z 0 with h | h
    · rw [h]; simp; positivity
    · rw [div_le_iff₀ (by positivity)]
      have := tanh_sq_le_sq (u * z)
      rw [mul_pow] at this
      nlinarith
  have hnn : ∀ z, 0 ≤ f z := fun z => by simp only [hf]; positivity
  have hmeas : Measurable f := by
    simp only [hf]
    have ht : Measurable (fun z => tanh (u * z)) :=
      continuous_tanh.measurable.comp (measurable_const.mul measurable_id)
    exact (measurable_const.mul (ht.pow_const 2)).div (measurable_id.pow_const 2)
  have hint : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b := by
    intro a b
    refine IntervalIntegrable.mono_fun' (g := fun _ => u * u ^ 2) intervalIntegrable_const
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall (fun z => ?_))
    show ‖f z‖ ≤ u * u ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn z)]
    exact hbound z
  rcases le_total u 1 with h1 | h1
  · -- `u ≤ 1`: `Q_u ≤ u + u³ ≤ 2u`
    have hI : ∫ z in (0 : ℝ)..1, f z ≤ u * u ^ 2 := by
      calc ∫ z in (0 : ℝ)..1, f z ≤ ∫ _z in (0 : ℝ)..1, u * u ^ 2 :=
            intervalIntegral.integral_mono_on (by norm_num) (hint 0 1) intervalIntegrable_const
              (fun z _ => hbound z)
        _ = u * u ^ 2 := by simp
    have hmax : u ≤ max u (u ^ 2) := le_max_left _ _
    have : u * u ^ 2 ≤ u := by nlinarith
    linarith
  · -- `u ≥ 1`: split the integral at `1/u`
    have hu1 : 0 < 1 / u := by positivity
    have hu1' : 1 / u ≤ 1 := by rw [div_le_one hu]; exact h1
    have hsplit :=
      intervalIntegral.integral_add_adjacent_intervals (hint 0 (1 / u)) (hint (1 / u) 1)
    have hI1 : ∫ z in (0 : ℝ)..(1 / u), f z ≤ u ^ 2 := by
      calc ∫ z in (0 : ℝ)..(1 / u), f z ≤ ∫ _z in (0 : ℝ)..(1 / u), u * u ^ 2 :=
            intervalIntegral.integral_mono_on hu1.le (hint _ _) intervalIntegrable_const
              (fun z _ => hbound z)
        _ = u ^ 2 := by simp; field_simp
    have hcont : ContinuousOn (fun z : ℝ => u / z ^ 2) (Set.uIcc (1 / u) 1) := by
      apply ContinuousOn.div continuousOn_const (continuous_pow 2).continuousOn
      intro z hz
      rw [Set.uIcc_of_le hu1'] at hz
      have : 0 < z := lt_of_lt_of_le hu1 hz.1
      positivity
    have hI2 : ∫ z in (1 / u)..1, f z ≤ u * (u - 1) := by
      calc ∫ z in (1 / u)..1, f z ≤ ∫ z in (1 / u)..1, u / z ^ 2 := by
            apply intervalIntegral.integral_mono_on hu1' (hint _ _) (hcont.intervalIntegrable)
            intro z hz
            have hz0 : 0 < z := lt_of_lt_of_le hu1 hz.1
            simp only [hf]
            apply div_le_div_of_nonneg_right _ (by positivity)
            have : tanh (u * z) ^ 2 ≤ 1 := (tanh_sq_lt_one _).le
            nlinarith
        _ = u * (u - 1) := by
            have hderiv : ∀ x ∈ Set.uIcc (1 / u) 1,
                HasDerivAt (fun z : ℝ => -u / z) (u / x ^ 2) x := by
              intro x hx
              rw [Set.uIcc_of_le hu1'] at hx
              have hx0 : x ≠ 0 := (lt_of_lt_of_le hu1 hx.1).ne'
              have := (hasDerivAt_inv hx0).const_mul (-u)
              refine (this.congr_deriv (by field_simp)).congr_of_eventuallyEq ?_
              exact Filter.Eventually.of_forall (fun z => by simp [div_eq_mul_inv])
            rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
            field_simp
            ring
    have hmax : u ^ 2 ≤ max u (u ^ 2) := le_max_right _ _
    have hsum : ∫ z in (0 : ℝ)..1, f z ≤ u ^ 2 + u * (u - 1) := by
      rw [← hsplit]; linarith
    simp only [hf] at hsum
    nlinarith

/-! ### The exact arity draw -/

/-- `cos 1 ≥ 1/2`, from `1 ≤ π/3`. Paper: Section `sec:bits` (`tanh_bits.tex`). -/
theorem half_le_cos_one : 1 / 2 ≤ cos 1 := by
  rw [← cos_pi_div_three]
  apply cos_le_cos_of_nonneg_of_le_pi (by norm_num) (by linarith [pi_pos])
  linarith [pi_gt_three]

/-- `F_ρ(5/4) = sec² (ρ/2) ≤ 4` for `0 ≤ ρ ≤ 2`. Paper: Section `sec:bits`
(`tanh_bits.tex`). -/
theorem sec_sq_half_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h2 : ρ ≤ 2) : 1 / cos (ρ / 2) ^ 2 ≤ 4 := by
  have hc : cos 1 ≤ cos (ρ / 2) :=
    cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [pi_gt_three]) (by linarith)
  have h1 := half_le_cos_one
  have hpos : 0 < cos (ρ / 2) := by linarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- `d_k ≤ 4 (4/5)^k` from nonnegativity and `F_ρ(5/4) ≤ 4`. The hypothesis `hF` (the series
of `F_ρ` converges at `v = 5/4` to `sec² (ρ/2)`) is part of the cosh-product stand-in.
Paper: Section `sec:bits` (`tanh_bits.tex`). -/
theorem arity_coefficient_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h2 : ρ ≤ 2) (d : ℕ → ℝ) (hd0 : ∀ k, 0 ≤ d k)
    (hF : HasSum (fun k => d k * (5 / 4 : ℝ) ^ k) (1 / cos (ρ / 2) ^ 2)) (k : ℕ) :
    d k ≤ 4 * (4 / 5 : ℝ) ^ k := by
  have h := le_hasSum hF k (fun j _ => mul_nonneg (hd0 j) (by positivity))
  have h4 := (h.trans (sec_sq_half_le h0 h2))
  have hp : (4 / 5 : ℝ) ^ k * (5 / 4 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
  have hpos : 0 < (4 / 5 : ℝ) ^ k := by positivity
  calc d k = d k * (5 / 4 : ℝ) ^ k * (4 / 5 : ℝ) ^ k := by
        rw [mul_assoc, mul_comm ((5 / 4 : ℝ) ^ k), hp, mul_one]
    _ ≤ 4 * (4 / 5 : ℝ) ^ k := mul_le_mul_of_nonneg_right h4 hpos.le

/-- The arity envelope `π_k ≤ 12 (4/5)^k` for `0 < ρ ≤ 2`.
Paper: `eq:arityenvelope` (`tanh_bits.tex`). -/
theorem arity_envelope {ρ : ℝ} (h0 : 0 < ρ) (h2 : ρ ≤ 2) (d : ℕ → ℝ) (hd0 : ∀ k, 0 ≤ d k)
    (hF : HasSum (fun k => d k * (5 / 4 : ℝ) ^ k) (1 / cos (ρ / 2) ^ 2)) (k : ℕ) :
    ρ / tanh ρ * d k / majC k ≤ 12 * (4 / 5 : ℝ) ^ k := by
  have hd := arity_coefficient_le h0.le h2 d hd0 hF k
  have hc : ρ / tanh ρ ≤ 7 / 3 := by
    have := mul_coth_le h0
    nlinarith
  have hq : 0 < tanh ρ := by
    rw [tanh_eq_sinh_div_cosh]; exact div_pos (sinh_pos_iff.mpr h0) (cosh_pos ρ)
  have hc0 : 0 ≤ ρ / tanh ρ := (div_pos h0 hq).le
  rw [div_le_iff₀ (majC_pos k)]
  have h1 := one_le_majC k
  have hpos : 0 ≤ 12 * (4 / 5 : ℝ) ^ k := by positivity
  calc ρ / tanh ρ * d k ≤ 7 / 3 * (4 * (4 / 5 : ℝ) ^ k) :=
        mul_le_mul hc hd (hd0 k) (by norm_num)
    _ ≤ 12 * (4 / 5 : ℝ) ^ k := by nlinarith
    _ ≤ 12 * (4 / 5 : ℝ) ^ k * majC k := le_mul_of_one_le_right hpos h1

/-- The exact arity draw: propose `k` with probability `γ_k = (1/5)(4/5)^k` and accept with
probability `π_k / (60 γ_k) ∈ [0, 1]`. Each trial succeeds with probability `1/60`, and the
accepted index has law `π`. Paper: Section `sec:bits` (`tanh_bits.tex`), after
`eq:arityenvelope`. -/
theorem arity_rejection_draw (w : ℕ → ℝ) (hw : HasSum w 1) (hw0 : ∀ k, 0 ≤ w k)
    (henv : ∀ k, w k ≤ 12 * (4 / 5 : ℝ) ^ k) :
    (∀ k, 0 ≤ w k / (60 * (1 / 5 * (4 / 5 : ℝ) ^ k)) ∧
      w k / (60 * (1 / 5 * (4 / 5 : ℝ) ^ k)) ≤ 1) ∧
    HasSum (fun k => 1 / 5 * (4 / 5 : ℝ) ^ k) 1 ∧
    HasSum (fun k => 1 / 5 * (4 / 5 : ℝ) ^ k * (w k / (60 * (1 / 5 * (4 / 5 : ℝ) ^ k)))) (1 / 60) ∧
    ∀ k, HasSum (fun m : ℕ => (59 / 60 : ℝ) ^ m *
      (1 / 5 * (4 / 5 : ℝ) ^ k * (w k / (60 * (1 / 5 * (4 / 5 : ℝ) ^ k))))) (w k) := by
  have hγ : ∀ k, 0 < 1 / 5 * (4 / 5 : ℝ) ^ k := fun k => by positivity
  have hmass : ∀ k, 1 / 5 * (4 / 5 : ℝ) ^ k * (w k / (60 * (1 / 5 * (4 / 5 : ℝ) ^ k))) =
      w k / 60 := fun k => by
    have := hγ k
    field_simp
  refine ⟨fun k => ⟨div_nonneg (hw0 k) (by positivity), ?_⟩, ?_, ?_, ?_⟩
  · rw [div_le_one (by positivity)]
    have := henv k
    linarith
  · have h := (hasSum_geometric_of_lt_one (r := (4 / 5 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (1 / 5)
    convert h using 1
    norm_num
  · simp_rw [hmass]
    simpa using hw.div_const 60
  · intro k
    rw [hmass]
    have hg := hasSum_geometric_of_lt_one (r := (59 / 60 : ℝ)) (by norm_num) (by norm_num)
    have h := hg.mul_right (w k / 60)
    convert h using 1
    norm_num
    ring

/-- The arity normalization `Σ_k d_k / C_k = tanh u / u`, equivalent to `Σ_k π_k = 1`; the mean
number of acceptance trials is `u / tanh u`. Paper: `thm:quadraticradiusbits`
(`tanh_large_radius.tex`). -/
theorem arity_normalization {u : ℝ} (hu : 0 < u) (d : ℕ → ℝ)
    (hπ : HasSum (fun k => u / tanh u * d k / majC k) 1) :
    HasSum (fun k => d k / majC k) (tanh u / u) := by
  have hq : 0 < tanh u := by
    rw [tanh_eq_sinh_div_cosh]; exact div_pos (sinh_pos_iff.mpr hu) (cosh_pos u)
  have h := hπ.mul_left (tanh u / u)
  convert h using 1
  · funext k; field_simp
  · ring

/-! ### Algebraic kernels of the fixed-precision coefficient algorithm -/

/-- If `z = 1 - (a + bi)²`, then `|z|² = (a² + b² - 1)² + 4b²`.
Paper: `lem:coefficient-four` (`tanh_fixed_precision.tex`). -/
theorem square_root_disk_identity (a b : ℝ) :
    (1 - (a ^ 2 - b ^ 2)) ^ 2 + (2 * a * b) ^ 2 = (a ^ 2 + b ^ 2 - 1) ^ 2 + 4 * b ^ 2 := by
  ring

/-- On `|z| ≤ 1`, the imaginary part `v` of `√(1 - z)` satisfies `|v| ≤ 1/2`.
Paper: `lem:coefficient-four` (`tanh_fixed_precision.tex`). -/
theorem square_root_imaginary_bound (a b : ℝ)
    (hdisk : (1 - (a ^ 2 - b ^ 2)) ^ 2 + (2 * a * b) ^ 2 ≤ 1) : b ^ 2 ≤ 1 / 4 := by
  rw [square_root_disk_identity] at hdisk
  nlinarith [sq_nonneg (a ^ 2 + b ^ 2 - 1)]

/-- The numerical part of the coefficient norm bound: `cosh² (ρ √2) < 1024` for `0 ≤ ρ ≤ 2`, from
`ρ √2 < 3` and `cosh² 3 < e⁶ < 729`. The identification `Σ_j |a_j| = cosh² (ρ √2)` is not
formalized. Paper: `eq:coefficient-norm` in `lem:coefficient-four`
(`tanh_fixed_precision.tex`). -/
theorem coefficient_norm_bound {ρ : ℝ} (h0 : 0 ≤ ρ) (h2 : ρ ≤ 2) : cosh (ρ * √2) ^ 2 < 1024 := by
  have hs2 : √2 < 3 / 2 := by
    rw [sqrt_lt' (by norm_num)]; norm_num
  have hs0 : 0 ≤ √2 := sqrt_nonneg 2
  have hx : ρ * √2 ≤ 3 := by nlinarith
  have hx0 : 0 ≤ ρ * √2 := mul_nonneg h0 hs0
  have hc : cosh (ρ * √2) ≤ cosh 3 := by
    rw [cosh_le_cosh, abs_of_nonneg hx0, abs_of_nonneg (by norm_num)]; exact hx
  have hc3 : cosh 3 < 27 := by
    have he : exp 1 < 3 := lt_trans exp_one_lt_d9 (by norm_num)
    have h3 : exp 3 = exp 1 ^ 3 := by rw [← exp_nat_mul]; norm_num
    have he3 : exp 3 < 27 := by
      rw [h3]
      calc exp 1 ^ 3 < 3 ^ 3 := by gcongr
        _ = 27 := by norm_num
    have hm : exp (-3) ≤ exp 3 := exp_le_exp.mpr (by norm_num)
    rw [cosh_eq]
    linarith
  have hpos := cosh_pos (ρ * √2)
  nlinarith

/-- The modulus identity `|cosh (x + i y)|² = (cosh x cos y)² + (sinh x sin y)² = sinh² x + cos² y`,
and the lower bound `≥ 1/4` when `|y| ≤ 1`, which bounds the reciprocal `1/A(z)` on the unit
disk (the imaginary part of `ρ √(1 - z)` is at most `1` in modulus).
Paper: `lem:coefficient-four` (`tanh_fixed_precision.tex`). -/
theorem cosh_modulus_lower (x y : ℝ) (hy : |y| ≤ 1) :
    (cosh x * cos y) ^ 2 + (sinh x * sin y) ^ 2 = sinh x ^ 2 + cos y ^ 2 ∧
      1 / 4 ≤ sinh x ^ 2 + cos y ^ 2 := by
  have h1 := cosh_sq' x
  have h2 := sin_sq_add_cos_sq y
  constructor
  · nlinarith [h1, h2]
  · have hc : cos 1 ≤ cos |y| :=
      cos_le_cos_of_nonneg_of_le_pi (abs_nonneg y) (by linarith [pi_gt_three]) hy
    rw [cos_abs] at hc
    have h12 := half_le_cos_one
    have : 1 / 4 ≤ cos y ^ 2 := by nlinarith
    nlinarith [sq_nonneg (sinh x)]

/-- Iterating the affine error recurrence `E_0 ≤ 3Δ`, `E_k ≤ 2048 E_{k-1} + cΔ` gives
`E_k ≤ (3 + c/2047) 2048^k Δ`. Paper: `lem:coefficient-four` (`tanh_fixed_precision.tex`). -/
theorem affine_error_iterate (E : ℕ → ℝ) (c Δ : ℝ) (hΔ : 0 ≤ Δ) (hc : 0 ≤ c)
    (h0 : E 0 ≤ 3 * Δ) (hstep : ∀ k, E (k + 1) ≤ 2048 * E k + c * Δ) :
    ∀ k, E k ≤ (3 + c / 2047) * 2048 ^ k * Δ := by
  have key : ∀ k, E k ≤ (3 + c / 2047) * 2048 ^ k * Δ - c * Δ / 2047 := by
    intro k
    induction k with
    | zero =>
        simp only [pow_zero, mul_one]
        have : (3 + c / 2047) * Δ - c * Δ / 2047 = 3 * Δ := by ring
        linarith
    | succ k ih =>
        have h1 := hstep k
        calc E (k + 1) ≤ 2048 * E k + c * Δ := h1
          _ ≤ 2048 * ((3 + c / 2047) * 2048 ^ k * Δ - c * Δ / 2047) + c * Δ := by linarith
          _ = (3 + c / 2047) * 2048 ^ (k + 1) * Δ - c * Δ / 2047 := by rw [pow_succ]; ring
  intro k
  have := key k
  have : 0 ≤ c * Δ / 2047 := by positivity
  linarith

/-- The constant of the iterated recurrence: `3 + (12K + 8193)/2047 ≤ 2^14 (K + 1)`, so
`E_k ≤ 2^{11k+14} (K+1) Δ`. Paper: `lem:coefficient-four` (`tanh_fixed_precision.tex`). -/
theorem coefficient_error_constant (K k : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    (3 + (12 * (K : ℝ) + 8193) / 2047) * 2048 ^ k * Δ ≤ 2 ^ (11 * k + 14) * ((K : ℝ) + 1) * Δ := by
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h1 : 3 + (12 * (K : ℝ) + 8193) / 2047 ≤ 2 ^ 14 * ((K : ℝ) + 1) := by
    have : (12 * (K : ℝ) + 8193) / 2047 ≤ 12 * K + 8193 :=
      div_le_self (by positivity) (by norm_num)
    norm_num
    linarith
  have h2 : (2048 : ℝ) ^ k = 2 ^ (11 * k) := by rw [pow_mul]; norm_num
  rw [h2, pow_add]
  have h3 : (0 : ℝ) ≤ 2 ^ (11 * k) := by positivity
  calc (3 + (12 * (K : ℝ) + 8193) / 2047) * 2 ^ (11 * k) * Δ
      ≤ (2 ^ 14 * ((K : ℝ) + 1)) * 2 ^ (11 * k) * Δ := by gcongr
    _ = 2 ^ (11 * k) * 2 ^ 14 * ((K : ℝ) + 1) * Δ := by ring

/-- Each coin of the acceptance loop is a valid probability: `0 ≤ 2r/(2r+1) ≤ 1`.
Paper: `thm:quadraticradiusbits` (`tanh_large_radius.tex`). -/
theorem acceptance_coin_mem (r : ℕ) :
    0 ≤ (2 * ((r : ℝ) + 1)) / (2 * ((r : ℝ) + 1) + 1) ∧
      (2 * ((r : ℝ) + 1)) / (2 * ((r : ℝ) + 1) + 1) ≤ 1 := by
  constructor
  · positivity
  · rw [div_le_one (by positivity)]; linarith

/-! ### The one-row law -/

/-- The arithmetic step of the request bound of a biased row: with `u = |b| + r > 0`, `|b| ≤ 1`,
if a fraction `r / u` of `Q_u ≤ 2 max {u, u²}` mixed requests reaches the input, the product is
at most `2 r (1 + r)`. Paper: `cor:comptanhrow` (`tanh_large_radius.tex`),
`thm:new-single-row-law` (`tanh_single_row.tex`), and `thm:main-row`
(`exact_sampling_networks.tex`). -/
theorem row_request_bound {b r Q : ℝ} (hb : |b| ≤ 1) (hr : 0 ≤ r) (hu : 0 < |b| + r)
    (hQ : Q ≤ 2 * max (|b| + r) ((|b| + r) ^ 2)) :
    r / (|b| + r) * Q ≤ 2 * r * (1 + r) := by
  set u := |b| + r with hudef
  have hfrac : 0 ≤ r / u := div_nonneg hr hu.le
  have hmax : r / u * (2 * max u (u ^ 2)) = 2 * r * max 1 u := by
    rcases le_total u 1 with h | h
    · rw [max_eq_left (by nlinarith), max_eq_left h]; field_simp
    · rw [max_eq_right (by nlinarith), max_eq_right h]; field_simp
  have hmax1 : max 1 u ≤ 1 + r := max_le (by linarith) (by rw [hudef]; linarith)
  calc r / u * Q ≤ r / u * (2 * max u (u ^ 2)) := mul_le_mul_of_nonneg_left hQ hfrac
    _ = 2 * r * max 1 u := hmax
    _ ≤ 2 * r * (1 + r) := mul_le_mul_of_nonneg_left hmax1 (by linarith)

/-- The arithmetic form of the one-row request bound: with `u = |b| + r`,
`(r/u) (u + ∫_0^1 u tanh²(uz)/z² dz) ≤ 2 r (1 + r)`. Not formalized here: the identification of
the integral formula with the expected full-majority count, the gate and fair-sign construction,
the folding of the bias into the source, the conditional charging, and the exactness of the
sampler. Paper: `thm:new-single-row-law` (`tanh_single_row.tex`) and `thm:main-row`
(`exact_sampling_networks.tex`). -/
theorem row_request_bound_integral {b r : ℝ} (hb : |b| ≤ 1) (hr : 0 ≤ r) (hu : 0 < |b| + r) :
    r / (|b| + r) * ((|b| + r) + ∫ z in (0 : ℝ)..1,
        (|b| + r) * tanh ((|b| + r) * z) ^ 2 / z ^ 2) ≤ 2 * r * (1 + r) :=
  row_request_bound hb hr hu (comptanh_arity_le hu)

/-- The arithmetic of the bounded-radius factory: `2 r (1 + r) ≤ 40` for `r ≤ 4`, and the
full-majority formula `r + ∫_0^1 r tanh²(rz)/z² dz` is at most `2` when `r ≤ 1` (the case
`a = 0`). Paper: `lem:unittanhfour` (`tanh_large_radius.tex`). -/
theorem unit_tanh_four {r : ℝ} (hr0 : 0 ≤ r) :
    (r ≤ 4 → 2 * r * (1 + r) ≤ 40) ∧
      (0 < r → r ≤ 1 → r + ∫ z in (0 : ℝ)..1, r * tanh (r * z) ^ 2 / z ^ 2 ≤ 2) := by
  refine ⟨fun h => by nlinarith, fun h0 h1 => ?_⟩
  have := comptanh_arity_le h0
  have hm : max r (r ^ 2) ≤ 1 := max_le h1 (by nlinarith)
  linarith

/-- `tanh 1 > 1/2`. Paper: `thm:new-single-row-law` (`tanh_single_row.tex`). -/
theorem half_lt_tanh_one : 1 / 2 < tanh 1 := by
  have he : 2 < exp 1 := lt_trans (by norm_num) exp_one_gt_d9
  have he2 : exp 1 * exp 1 = exp 2 := by rw [← exp_add]; norm_num
  have hp := exp_pos 1
  rw [tanh_eq, exp_neg]
  rw [lt_div_iff₀ (by positivity)]
  field_simp
  nlinarith

/-- `tanh u ≥ (1/2) min {u, 1}` for `u ≥ 0`. Paper: `thm:new-single-row-law`
(`tanh_single_row.tex`), lower bound. -/
theorem tanh_ge_half_min {u : ℝ} (hu : 0 ≤ u) : 1 / 2 * min u 1 ≤ tanh u := by
  rcases le_total u 1 with h | h
  · rw [min_eq_left h]
    -- `tanh u ≥ u / (1 + u) ≥ u / 2`
    have h2 := add_one_le_exp (2 * u)
    have he : exp u * exp u = exp (2 * u) := by rw [← exp_add]; ring_nf
    have hp := exp_pos u
    have hineq : u / (1 + u) ≤ tanh u := by
      rw [tanh_eq, exp_neg, div_le_div_iff₀ (by linarith) (by positivity)]
      field_simp
      nlinarith
    have : 1 / 2 * u ≤ u / (1 + u) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    linarith
  · rw [min_eq_right h]
    have h1 := half_lt_tanh_one
    have hmono : tanh 1 ≤ tanh u := by
      by_contra hlt
      have hlt : tanh u < tanh 1 := lt_of_not_ge hlt
      have := artanh_lt_artanh (neg_one_lt_tanh u) (tanh_lt_one 1) hlt
      rw [artanh_tanh, artanh_tanh] at this
      linarith
    linarith

/-- The coupling range of the one-row lower bound: for `0 < r ≤ 1`, the total variation
`tanh r ≥ r/2 ≥ (r + r²)/4`. Paper: `thm:new-single-row-law` (`tanh_single_row.tex`). -/
theorem row_coupling_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r / 2 ≤ tanh r ∧ (r + r ^ 2) / 4 ≤ r / 2 := by
  have h := tanh_ge_half_min hr0
  rw [min_eq_left hr1] at h
  constructor
  · linarith
  · nlinarith

/-- Pointwise step of the score bound: for `|Z| ≥ 1/2` and `c ≥ 0`,
`Z tanh (c Z) ≥ (1/4) min {c/2, 1}`. Paper: `thm:new-single-row-law`
(`tanh_single_row.tex`), with `c = r/√n`. -/
theorem score_integrand_ge {Z c : ℝ} (hc : 0 ≤ c) (hZ : 1 / 2 ≤ |Z|) :
    1 / 4 * min (c / 2) 1 ≤ Z * tanh (c * Z) := by
  have key : Z * tanh (c * Z) = |Z| * tanh (c * |Z|) := by
    rcases le_total 0 Z with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, mul_neg, tanh_neg]; ring
  rw [key]
  have hmono : tanh (c * (1 / 2)) ≤ tanh (c * |Z|) := by
    by_contra hlt
    have hlt : tanh (c * |Z|) < tanh (c * (1 / 2)) := lt_of_not_ge hlt
    have := artanh_lt_artanh (neg_one_lt_tanh _) (tanh_lt_one _) hlt
    rw [artanh_tanh, artanh_tanh] at this
    nlinarith
  have hhalf := tanh_ge_half_min (u := c * (1 / 2)) (by positivity)
  have ht0 : 0 ≤ tanh (c * (1 / 2)) := by
    have : 0 ≤ 1 / 2 * min (c * (1 / 2)) 1 := by
      apply mul_nonneg (by norm_num); exact le_min (by positivity) (by norm_num)
    linarith
  have e : c * (1 / 2) = c / 2 := by ring
  rw [e] at hhalf hmono ht0
  calc 1 / 4 * min (c / 2) 1 = 1 / 2 * (1 / 2 * min (c / 2) 1) := by ring
    _ ≤ |Z| * tanh (c * |Z|) := by
        apply mul_le_mul hZ (by linarith) (by positivity) (abs_nonneg Z)

/-- The final constants of the one-row lower bound: if `H'(0) ≥ (3/128) min {r, √n}` and
`r ≥ 1`, then `H'(0)² ≥ (9/16384) min {r², n} ≥ min {r + r², n} / 65536`.
Paper: `thm:new-single-row-law` (`tanh_single_row.tex`), last display. -/
theorem row_lower_constants {r n h : ℝ} (hr : 1 ≤ r) (hn : 0 ≤ n)
    (hh : 3 / 128 * min r √n ≤ h) :
    9 / 16384 * min (r ^ 2) n ≤ h ^ 2 ∧ min (r + r ^ 2) n / 65536 ≤ h ^ 2 := by
  have hm0 : 0 ≤ min r √n := le_min (by linarith) (sqrt_nonneg n)
  have hsq : (min r √n) ^ 2 = min (r ^ 2) n := by
    rcases le_total r √n with h1 | h1
    · rw [min_eq_left h1]
      have : r ^ 2 ≤ n := by
        have := pow_le_pow_left₀ (by linarith) h1 2
        rwa [sq_sqrt hn] at this
      rw [min_eq_left this]
    · rw [min_eq_right h1, sq_sqrt hn]
      have : n ≤ r ^ 2 := by
        have := pow_le_pow_left₀ (sqrt_nonneg n) h1 2
        rwa [sq_sqrt hn] at this
      rw [min_eq_right this]
  have h1 : 9 / 16384 * min (r ^ 2) n ≤ h ^ 2 := by
    rw [← hsq]
    have := pow_le_pow_left₀ (by positivity) hh 2
    nlinarith
  refine ⟨h1, ?_⟩
  have h2 : min (r + r ^ 2) n ≤ 2 * min (r ^ 2) n := by
    rcases le_total (r ^ 2) n with h3 | h3
    · rw [min_eq_left h3]
      have := min_le_left (r + r ^ 2) n
      nlinarith
    · rw [min_eq_right h3]
      have := min_le_right (r + r ^ 2) n
      linarith
  have h0 : 0 ≤ min (r ^ 2) n := le_min (sq_nonneg r) hn
  nlinarith

/-- The Paley–Zygmund constant: with `E Z² = 1` and `E Z⁴ ≤ 3`, the threshold `1/4` gives
`(1 - 1/4)² · 1 / 3 = 3/16`. Paper: `thm:new-single-row-law` (`tanh_single_row.tex`). -/
theorem paley_zygmund_constant : (1 - 1 / 4 : ℝ) ^ 2 * 1 ^ 2 / 3 = 3 / 16 := by norm_num

end ExactSampling.MajorityArity
