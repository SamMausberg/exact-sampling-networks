import Mathlib

/-!
# Counting estimates for critical networks

This module formalizes the counting arithmetic that turns per-layer offspring
bounds into depth bounds in `tanh_zero_bias.tex` (`thm:zero-bias-linear`),
`tanh_potential_local.tex` (subsection "Bounds at a fixed cutoff"), and
`tanh_fused.tex` (`thm:fusedcritical`).

Formalized here:
* the `p`-series bound `∑_{k=1}^n k^{-p} ≤ 1 + 1/(p-1)`, giving
  `∑ k^{-3/2} ≤ 3`, `∑ k^{-5/2} ≤ 5/3`, and `∑ j^{-51/32} < 3`;
* `e^3 < 21`;
* the sums `eq:qsums` (`tanh_rates.tex`): `∑_{j=k}^{D-1} q_j ≤ (3/2) log((D+1)/(k+1))` and
  `∑_{j=k}^{D-1} q_j^2 ≤ 9/(4(k+1))` for `q_j = 3/(2j+3)`;
* the counting chain of `thm:zero-bias-linear`: per-call offspring
  `1 + ρ^2 + ρ^4 ≤ exp(r^2 + r^4)`, the rounding contribution `18 D^2 ε < 1/50`,
  the suffix estimate, the top gate `r_D ≤ 2/√(D+1)`, and the composed bound
  `1 + r_D ∑_{k<D} exp(∑_{j=k}^{D-1} (r_j^2 + r_j^4)) ≤ 128(D+1)` (`zero_bias_chain`);
* the arithmetic of the cutoff constants of `app:potential`:
  `1 + e^3 (J+1)^{5/2} S ≤ 36(J+1)^{5/2}` for `S ≤ 5/3`, `64 ε D √(D+1) < 1/100`,
  and `12 D^2 ε < 1/100`.

Not formalized: the radius lemmas `lem:radius` and `lem:rounding` (`R_j^2 ≤ q_j`
and the rounding error enter as declared stand-in hypotheses), the majority cost
`lem:arity`, and the predictable charging step
`E N_calls ≤ 1 + r_D ∑_k ∏_{ℓ>k} B_ℓ` of the recursion, which turns the composed
bound into the expected call count.
-/

open Real Finset

namespace ExactSampling.CriticalCounts

/-! ## `p`-series bounds -/

/-- Auxiliary for `thm:zero-bias-linear`, `app:potential`, and `thm:fusedcritical`:
for `p > 1`, `∑_{k=1}^{n} k^{-p} ≤ 1 + 1/(p-1)`, by comparison with `∫_1^∞ x^{-p} dx`. -/
theorem sum_rpow_neg_le (p : ℝ) (hp : 1 < p) (n : ℕ) :
    ∑ k ∈ range n, ((k : ℝ) + 1) ^ (-p) ≤ 1 + 1 / (p - 1) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp only [range_zero, sum_empty]
    have : 0 < 1 / (p - 1) := by apply div_pos one_pos; linarith
    linarith
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [sum_range_succ']
  simp only [Nat.cast_zero, zero_add, Real.one_rpow]
  -- compare the remaining terms with the integral
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-p)) (Set.Icc 1 (1 + m)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hsum := hanti.sum_le_integral
  have hint : ∫ x in (1 : ℝ)..1 + m, x ^ (-p) = ((1 + m) ^ (-p + 1) - 1 ^ (-p + 1)) / (-p + 1) :=
    integral_rpow (Or.inr ⟨by linarith, by
      rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ 1 + m)]
      intro h
      linarith [h.1]⟩)
  have hterm : ∀ i ∈ range m, ((((i + 1 : ℕ) : ℝ)) + 1) ^ (-p) =
      (fun x : ℝ => x ^ (-p)) (1 + ((i + 1 : ℕ) : ℝ)) := by
    intro i _
    simp only
    ring_nf
  rw [sum_congr rfl hterm]
  rw [hint, Real.one_rpow] at hsum
  have h1 : 0 ≤ (1 + (m : ℝ)) ^ (-p + 1) := by positivity
  have e : ((1 + (m : ℝ)) ^ (-p + 1) - 1) / (-p + 1) =
      (1 - (1 + (m : ℝ)) ^ (-p + 1)) / (p - 1) := by
    rw [show -p + 1 = -(p - 1) by ring, div_neg, ← neg_div]
    ring_nf
  rw [e] at hsum
  have : (1 - (1 + (m : ℝ)) ^ (-p + 1)) / (p - 1) ≤ 1 / (p - 1) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  linarith

/-- Paper: proof of `thm:zero-bias-linear` (tanh_zero_bias.tex): `∑_{k ≥ 1} k^{-3/2} ≤ 3`. -/
theorem sum_three_halves_le (n : ℕ) : ∑ k ∈ range n, ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) ≤ 3 := by
  have h := sum_rpow_neg_le (3 / 2) (by norm_num) n
  norm_num at h ⊢
  linarith

/-- Paper: `eq:normalizedcutoff` (tanh_potential_local.tex):
`∑_{k ≥ 1} k^{-5/2} ≤ 5/3`. -/
theorem sum_five_halves_le (n : ℕ) :
    ∑ k ∈ range n, ((k : ℝ) + 1) ^ (-(5 / 2 : ℝ)) ≤ 5 / 3 := by
  have h := sum_rpow_neg_le (5 / 2) (by norm_num) n
  norm_num at h ⊢
  linarith

/-- Paper: proof of `thm:fusedcritical` (tanh_fused.tex):
`∑_{j ≥ 1} j^{-51/32} < 3`. -/
theorem sum_fiftyone_le (n : ℕ) :
    ∑ k ∈ range n, ((k : ℝ) + 1) ^ (-(51 / 32 : ℝ)) < 3 := by
  have h := sum_rpow_neg_le (51 / 32) (by norm_num) n
  norm_num at h ⊢
  linarith

/-- Paper: `thm:zero-bias-linear` and `eq:normalizedcutoff`: `e^3 < 21`. -/
theorem exp_three_lt : Real.exp 3 < 21 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [e]
  have : Real.exp 1 ^ 3 < 2.7182818286 ^ 3 := pow_lt_pow_left₀ h (Real.exp_pos 1).le (by norm_num)
  linarith [show (2.7182818286 : ℝ) ^ 3 < 21 by norm_num]

/-! ## The sums `eq:qsums` -/

/-- Auxiliary for `eq:qsums` (tanh_rates.tex): `log((m+1)/m) ≥ 2/(2m+1)` for
`m > 0`, from the odd series of `log((1+y)/(1-y))` at `y = 1/(2m+1)`. -/
theorem two_div_le_log (m : ℝ) (hm : 0 < m) :
    2 / (2 * m + 1) ≤ Real.log ((m + 1) / m) := by
  set y := 1 / (2 * m + 1) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
  have habs : |y| < 1 := by rw [abs_of_pos hy0]; exact hy1
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hle := le_hasSum hs 0 (fun k _ => by positivity)
  simp only [CharP.cast_eq_zero, mul_zero, zero_add, div_one, pow_one] at hle
  have e1 : (m + 1) / m = (1 + y) / (1 - y) := by
    rw [hy]
    field_simp
    ring
  rw [e1, Real.log_div (by linarith) (by linarith)]
  have e2 : 2 / (2 * m + 1) = 2 * 1 * y := by rw [hy]; ring
  linarith

/-- Paper: `eq:qsums` (tanh_rates.tex), first sum:
`∑_{j=k}^{D-1} 3/(2j+3) ≤ (3/2) log((D+1)/(k+1))`. -/
theorem qsum_le (k D : ℕ) (hkD : k ≤ D) :
    ∑ j ∈ Ico k D, (3 : ℝ) / (2 * j + 3) ≤ 3 / 2 * Real.log (((D : ℝ) + 1) / (k + 1)) := by
  have hstep : ∀ j : ℕ, (3 : ℝ) / (2 * j + 3) ≤
      3 / 2 * (Real.log ((j : ℝ) + 2) - Real.log ((j : ℝ) + 1)) := by
    intro j
    have h := two_div_le_log ((j : ℝ) + 1) (by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at h
    have e : (3 : ℝ) / (2 * j + 3) = 3 / 2 * (2 / (2 * ((j : ℝ) + 1) + 1)) := by
      field_simp
      ring
    rw [e, show (j : ℝ) + 1 + 1 = (j : ℝ) + 2 by ring] at *
    linarith
  have htel : ∀ n : ℕ, ∑ j ∈ Ico k (k + n), (3 / 2 * (Real.log ((j : ℝ) + 2) -
      Real.log ((j : ℝ) + 1))) = 3 / 2 * (Real.log ((k + n : ℕ) + 1) - Real.log ((k : ℝ) + 1)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [← add_assoc, sum_Ico_succ_top (by omega), ih]
        push_cast
        ring_nf
  have h1 := sum_le_sum fun j (_ : j ∈ Ico k D) => hstep j
  have h2 := htel (D - k)
  rw [Nat.add_sub_cancel' hkD] at h2
  rw [h2] at h1
  rw [Real.log_div (by positivity) (by positivity)]
  exact h1

/-- Paper: `eq:qsums` (tanh_rates.tex), second sum:
`∑_{j=k}^{D-1} (3/(2j+3))^2 ≤ 9/(4(k+1))`. -/
theorem qsq_sum_le (k D : ℕ) :
    ∑ j ∈ Ico k D, ((3 : ℝ) / (2 * j + 3)) ^ 2 ≤ 9 / (4 * ((k : ℝ) + 1)) := by
  have hstep : ∀ j : ℕ, ((3 : ℝ) / (2 * j + 3)) ^ 2 ≤
      9 / 4 * (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2)) := by
    intro j
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    rw [div_pow, show 1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2) = 1 / (((j : ℝ) + 1) * (j + 2)) by
      field_simp; ring]
    rw [show (9 : ℝ) / 4 * (1 / (((j : ℝ) + 1) * (j + 2))) = 9 / (4 * (((j : ℝ) + 1) * (j + 2))) by
      field_simp]
    norm_num
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith
  rcases le_or_gt D k with hDk | hkD
  · rw [Ico_eq_empty_of_le hDk, sum_empty]
    positivity
  have htel : ∀ n : ℕ, ∑ j ∈ Ico k (k + n), 9 / 4 * (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2)) =
      9 / 4 * (1 / ((k : ℝ) + 1) - 1 / ((k + n : ℕ) + 1)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [← add_assoc, sum_Ico_succ_top (by omega), ih]
        push_cast
        ring
  have h1 := sum_le_sum fun j (_ : j ∈ Ico k D) => hstep j
  have h2 := htel (D - k)
  rw [Nat.add_sub_cancel' hkD.le] at h2
  rw [h2] at h1
  have : 0 ≤ 1 / ((D : ℝ) + 1) := by positivity
  have e : 9 / (4 * ((k : ℝ) + 1)) = 9 / 4 * (1 / ((k : ℝ) + 1)) := by field_simp
  rw [e]
  linarith

/-! ## `thm:zero-bias-linear` -/

/-- Paper: proof of `thm:zero-bias-linear` (tanh_zero_bias.tex): the expected
reached children `1 + ρ^2 + ρ^4` of a call with `0 ≤ ρ ≤ r` are at most
`exp(r^2 + r^4)`. -/
theorem children_le_exp (ρ r : ℝ) (hρ : 0 ≤ ρ) (hρr : ρ ≤ r) :
    1 + ρ ^ 2 + ρ ^ 4 ≤ Real.exp (r ^ 2 + r ^ 4) := by
  have h1 : ρ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hρ hρr 2
  have h2 : ρ ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ hρ hρr 4
  have := Real.add_one_le_exp (r ^ 2 + r ^ 4)
  linarith

/-- Paper: proof of `thm:zero-bias-linear` (tanh_zero_bias.tex): with
`ε ≤ [100(D+1)^4]^{-1}`, the rounding contribution satisfies `18 D^2 ε < 1/50`;
this uses `16 D^2 ≤ (D+1)^4`. -/
theorem zero_bias_rounding (D ε : ℝ) (hD : 0 ≤ D) (hε : ε ≤ 1 / (100 * (D + 1) ^ 4)) :
    16 * D ^ 2 ≤ (D + 1) ^ 4 ∧ 18 * D ^ 2 * ε < 1 / 50 := by
  have h16 : 16 * D ^ 2 ≤ (D + 1) ^ 4 := by
    have h1 : 4 * D ≤ (D + 1) ^ 2 := by nlinarith [sq_nonneg (D - 1)]
    have h2 : (4 * D) ^ 2 ≤ ((D + 1) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    nlinarith
  refine ⟨h16, ?_⟩
  have hpos : 0 < (D + 1) ^ 4 := by positivity
  have h1 : 18 * D ^ 2 * ε ≤ 18 * D ^ 2 * (1 / (100 * (D + 1) ^ 4)) :=
    mul_le_mul_of_nonneg_left hε (by positivity)
  have h2 : 18 * D ^ 2 * (1 / (100 * (D + 1) ^ 4)) ≤ 18 / 1600 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-- Paper: proof of `thm:zero-bias-linear` (tanh_zero_bias.tex): the suffix sum.
If `R_j^2 ≤ q_j = 3/(2j+3)` (`lem:radius`), `R_j ≤ r_j ≤ 1` and
`r_j^2 - R_j^2 ≤ 6Dε` (`lem:rounding`), with `ε ≤ [100(D+1)^4]^{-1}`, then for `k < D`,
`∑_{j=k}^{D-1} (r_j^2 + r_j^4) ≤ (3/2) log((D+1)/(k+1)) + 9/(4(k+1)) + 1/50
≤ (3/2) log((D+1)/(k+1)) + 3`. -/
theorem zero_bias_suffix (D k : ℕ) (hkD : k ≤ D) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / (100 * ((D : ℝ) + 1) ^ 4)) (R r : ℕ → ℝ) (hR0 : ∀ j, 0 ≤ R j)
    (hRr : ∀ j, R j ≤ r j) (hr1 : ∀ j, r j ≤ 1)
    (hRq : ∀ j : ℕ, R j ^ 2 ≤ 3 / (2 * j + 3)) (hround : ∀ j, r j ^ 2 - R j ^ 2 ≤ 6 * D * ε) :
    ∑ j ∈ Ico k D, (r j ^ 2 + r j ^ 4) ≤
      3 / 2 * Real.log (((D : ℝ) + 1) / (k + 1)) + 9 / (4 * ((k : ℝ) + 1)) + 1 / 50 ∧
    3 / 2 * Real.log (((D : ℝ) + 1) / (k + 1)) + 9 / (4 * ((k : ℝ) + 1)) + 1 / 50 ≤
      3 / 2 * Real.log (((D : ℝ) + 1) / (k + 1)) + 3 := by
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  -- per-term comparison: `v + v^2` has derivative at most three on `[0, 1]`
  have hterm : ∀ j, r j ^ 2 + r j ^ 4 ≤ 3 / (2 * (j : ℝ) + 3) + (3 / (2 * (j : ℝ) + 3)) ^ 2 +
      18 * D * ε := by
    intro j
    have h0 := hR0 j
    have hr0 : 0 ≤ r j := le_trans h0 (hRr j)
    have hr2 : r j ^ 2 ≤ 1 := by nlinarith [hr1 j]
    have hR2 : R j ^ 2 ≤ r j ^ 2 := pow_le_pow_left₀ h0 (hRr j) 2
    have hq0 : 0 ≤ R j ^ 2 := sq_nonneg _
    have e1 : r j ^ 4 - R j ^ 4 = (r j ^ 2 - R j ^ 2) * (r j ^ 2 + R j ^ 2) := by ring
    have e2 : r j ^ 4 - R j ^ 4 ≤ 2 * (r j ^ 2 - R j ^ 2) := by
      rw [e1]
      have : (r j ^ 2 - R j ^ 2) * (r j ^ 2 + R j ^ 2) ≤ (r j ^ 2 - R j ^ 2) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith
    have hRq4 : R j ^ 4 ≤ (3 / (2 * (j : ℝ) + 3)) ^ 2 := by
      rw [show R j ^ 4 = (R j ^ 2) ^ 2 by ring]
      exact pow_le_pow_left₀ hq0 (hRq j) 2
    have := hRq j
    have := hround j
    linarith
  have hsum := sum_le_sum fun j (_ : j ∈ Ico k D) => hterm j
  rw [sum_add_distrib, sum_add_distrib, sum_const, Nat.card_Ico, nsmul_eq_mul] at hsum
  have hL : ∑ j ∈ Ico k D, (r j ^ 2 + r j ^ 4) =
      ∑ j ∈ Ico k D, r j ^ 2 + ∑ j ∈ Ico k D, r j ^ 4 := sum_add_distrib
  have hR : ∑ j ∈ Ico k D, ((3 : ℝ) / (2 * j + 3) + (3 / (2 * j + 3)) ^ 2) =
      ∑ j ∈ Ico k D, (3 : ℝ) / (2 * j + 3) + ∑ j ∈ Ico k D, ((3 : ℝ) / (2 * j + 3)) ^ 2 :=
    sum_add_distrib
  have hq1 := qsum_le k D hkD
  have hq2 := qsq_sum_le k D
  have hcard : ((D - k : ℕ) : ℝ) ≤ D := by exact_mod_cast Nat.sub_le D k
  have hround2 : ((D - k : ℕ) : ℝ) * (18 * D * ε) ≤ 1 / 50 := by
    have h1 : ((D - k : ℕ) : ℝ) * (18 * D * ε) ≤ D * (18 * D * ε) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    have h2 := (zero_bias_rounding D ε hD hε).2
    nlinarith
  refine ⟨by linarith, ?_⟩
  have : 9 / (4 * ((k : ℝ) + 1)) ≤ 9 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  linarith

/-- Paper: `thm:zero-bias-linear` (tanh_zero_bias.tex), the final count. With the
top gate `r_D ≤ 2/√(D+1)` and the suffix products `∏ ≤ e^3((D+1)/(k+1))^{3/2}`,
`1 + r_D ∑_{k=0}^{D-1} e^3 ((D+1)/(k+1))^{3/2} ≤ 1 + 2e^3(D+1) ∑_{k≥1} k^{-3/2} ≤ 128(D+1)`. -/
theorem zero_bias_count (D : ℕ) (rD : ℝ) (hrD : rD ≤ 2 / Real.sqrt ((D : ℝ) + 1)) :
    1 + rD * ∑ k ∈ range D, Real.exp 3 * (((D : ℝ) + 1) / ((k : ℝ) + 1)) ^ (3 / 2 : ℝ) ≤
      128 * ((D : ℝ) + 1) := by
  set N : ℝ := (D : ℝ) + 1 with hN
  have hN1 : 1 ≤ N := by rw [hN]; have := Nat.cast_nonneg (α := ℝ) D; linarith
  have hN0 : 0 < N := by linarith
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hterm : ∀ k ∈ range D, Real.exp 3 * (N / ((k : ℝ) + 1)) ^ (3 / 2 : ℝ) =
      Real.exp 3 * N ^ (3 / 2 : ℝ) * ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
    intro k _
    rw [Real.div_rpow hN0.le (by positivity), Real.rpow_neg (by positivity), div_eq_mul_inv]
    ring
  rw [sum_congr rfl hterm, ← mul_sum]
  have hS := sum_three_halves_le D
  have hS0 : 0 ≤ ∑ k ∈ range D, ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) :=
    sum_nonneg fun k _ => by positivity
  -- `r_D N^{3/2} ≤ 2N`
  have hN32 : N ^ (3 / 2 : ℝ) = N * Real.sqrt N := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hN0, Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hgate : rD * N ^ (3 / 2 : ℝ) ≤ 2 * N := by
    rw [hN32]
    have : rD * Real.sqrt N ≤ 2 := by
      rw [le_div_iff₀ hsq] at hrD
      exact hrD
    nlinarith
  have hE := exp_three_lt
  have hE0 := Real.exp_pos 3
  have key : rD * (Real.exp 3 * N ^ (3 / 2 : ℝ) * ∑ k ∈ range D, ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ))) ≤
      Real.exp 3 * (2 * N) * 3 := by
    have e : rD * (Real.exp 3 * N ^ (3 / 2 : ℝ) * ∑ k ∈ range D, ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ))) =
        Real.exp 3 * (rD * N ^ (3 / 2 : ℝ)) * ∑ k ∈ range D, ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
      ring
    rw [e]
    have h1 : Real.exp 3 * (rD * N ^ (3 / 2 : ℝ)) ≤ Real.exp 3 * (2 * N) :=
      mul_le_mul_of_nonneg_left hgate hE0.le
    exact mul_le_mul h1 hS hS0 (by positivity)
  nlinarith

/-- Paper: proof of `thm:zero-bias-linear` (tanh_zero_bias.tex), the top gate
`r_D ≤ 2/√(D+1)`, derived from `R_D^2 ≤ 3/(2D+3)` (`lem:radius`) and the rounding
bound `r_D^2 - R_D^2 ≤ 6Dε` (`lem:rounding`). -/
theorem zero_bias_top_gate (D : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / (100 * ((D : ℝ) + 1) ^ 4)) (R r : ℕ → ℝ) (hR0 : ∀ j, 0 ≤ R j)
    (hRr : ∀ j, R j ≤ r j)
    (hRq : ∀ j : ℕ, R j ^ 2 ≤ 3 / (2 * j + 3)) (hround : ∀ j, r j ^ 2 - R j ^ 2 ≤ 6 * D * ε) :
    r D ≤ 2 / Real.sqrt ((D : ℝ) + 1) := by
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hN : (0 : ℝ) < D + 1 := by linarith
  have hr0 : 0 ≤ r D := le_trans (hR0 D) (hRr D)
  have h1 := hRq D
  have h2 := hround D
  have h3 : 3 / (2 * (D : ℝ) + 3) ≤ 3 / (D + 1) :=
    div_le_div_of_nonneg_left (by norm_num) hN (by linarith)
  have h4 : 6 * (D : ℝ) * ε ≤ 1 / (D + 1) := by
    have : ε * ((D : ℝ) + 1) ^ 4 ≤ 1 / 100 := by
      rw [le_div_iff₀ (by positivity)] at hε
      linarith
    rw [le_div_iff₀ hN]
    have hD4 : (D : ℝ) * (D + 1) ≤ ((D : ℝ) + 1) ^ 4 := by
      have hc : (D : ℝ) + 1 ≤ ((D : ℝ) + 1) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
      calc (D : ℝ) * (D + 1) ≤ ((D : ℝ) + 1) * ((D : ℝ) + 1) ^ 3 :=
            mul_le_mul (by linarith) hc (by linarith) (by positivity)
        _ = ((D : ℝ) + 1) ^ 4 := by ring
    nlinarith [mul_le_mul_of_nonneg_left hD4 hε0]
  have hsq : r D ^ 2 ≤ 4 / ((D : ℝ) + 1) := by
    have : 3 / ((D : ℝ) + 1) + 1 / (D + 1) = 4 / (D + 1) := by field_simp; ring
    linarith
  rw [le_div_iff₀ (Real.sqrt_pos.mpr hN)]
  have hs := Real.sq_sqrt hN.le
  have : (r D * Real.sqrt ((D : ℝ) + 1)) ^ 2 ≤ 2 ^ 2 := by
    rw [mul_pow, hs]
    rw [le_div_iff₀ hN] at hsq
    linarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num)).mp this

/-- Paper: `thm:zero-bias-linear` (tanh_zero_bias.tex), the composed counting
bound: from the stand-ins `R_j^2 ≤ q_j` (`lem:radius`) and the rounding bound
(`lem:rounding`), `1 + r_D ∑_{k<D} exp(∑_{j=k}^{D-1} (r_j^2 + r_j^4)) ≤ 128(D+1)`.
Since each reached call at level `j+1` has at most `exp(r_j^2 + r_j^4)` expected
children (`children_le_exp`), the predictable charging step of the paper turns this
into `E N_calls ≤ 128(D+1)`; that charging step is not formalized. -/
theorem zero_bias_chain (D : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / (100 * ((D : ℝ) + 1) ^ 4)) (R r : ℕ → ℝ) (hR0 : ∀ j, 0 ≤ R j)
    (hRr : ∀ j, R j ≤ r j) (hr1 : ∀ j, r j ≤ 1)
    (hRq : ∀ j : ℕ, R j ^ 2 ≤ 3 / (2 * j + 3)) (hround : ∀ j, r j ^ 2 - R j ^ 2 ≤ 6 * D * ε) :
    1 + r D * ∑ k ∈ range D, Real.exp (∑ j ∈ Ico k D, (r j ^ 2 + r j ^ 4)) ≤
      128 * ((D : ℝ) + 1) := by
  have hrD0 : 0 ≤ r D := le_trans (hR0 D) (hRr D)
  have hrD := zero_bias_top_gate D ε hε0 hε R r hR0 hRr hRq hround
  have hk : ∀ k ∈ range D, Real.exp (∑ j ∈ Ico k D, (r j ^ 2 + r j ^ 4)) ≤
      Real.exp 3 * (((D : ℝ) + 1) / ((k : ℝ) + 1)) ^ (3 / 2 : ℝ) := by
    intro k hk
    have hkD : k ≤ D := (mem_range.mp hk).le
    have h := zero_bias_suffix D k hkD ε hε0 hε R r hR0 hRr hr1 hRq hround
    have hx : 0 < ((D : ℝ) + 1) / ((k : ℝ) + 1) := by positivity
    have e : Real.exp 3 * (((D : ℝ) + 1) / ((k : ℝ) + 1)) ^ (3 / 2 : ℝ) =
        Real.exp (3 / 2 * Real.log (((D : ℝ) + 1) / (k + 1)) + 3) := by
      rw [Real.rpow_def_of_pos hx, ← Real.exp_add]
      ring_nf
    rw [e]
    exact Real.exp_le_exp.mpr (h.1.trans h.2)
  have := mul_le_mul_of_nonneg_left (sum_le_sum hk) hrD0
  linarith [zero_bias_count D (r D) hrD]

/-! ## Cutoff constants of `app:potential` -/

/-- Paper: `eq:normalizedcutoff` (tanh_potential_local.tex), the second inequality:
for `0 ≤ S ≤ 5/3` (`S = ∑_{k ≥ 1} k^{-5/2}`, see `sum_five_halves_le`),
`1 + e^3 (J+1)^{5/2} S ≤ 36 (J+1)^{5/2}`. The first inequality, the bound on `M_J`
from the suffix proof of `thm:upper`, is not formalized. -/
theorem normalized_cutoff (J : ℝ) (hJ : 0 ≤ J) (S : ℝ) (hS0 : 0 ≤ S) (hS : S ≤ 5 / 3) :
    1 + Real.exp 3 * (J + 1) ^ (5 / 2 : ℝ) * S ≤ 36 * (J + 1) ^ (5 / 2 : ℝ) := by
  have hE := exp_three_lt
  have hp : 1 ≤ (J + 1) ^ (5 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have h1 : Real.exp 3 * S ≤ 21 * (5 / 3) :=
    mul_le_mul hE.le hS hS0 (by norm_num)
  nlinarith

/-- Paper: `app:potential`, "Bounds at a fixed cutoff" (tanh_potential_local.tex):
the numerical bounds `12 D^2 ε < 1/100` and `64 ε D √(D+1) < 1/100` for
`ε ≤ [100(D+1)^4]^{-1}` and `D ≥ 2^{25}`. That these quantities bound the center
and rounding contributions is not formalized here. -/
theorem cutoff_rounding (D ε : ℝ) (hD : 2 ^ 25 ≤ D) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / (100 * (D + 1) ^ 4)) :
    12 * D ^ 2 * ε < 1 / 100 ∧ 64 * ε * D * Real.sqrt (D + 1) < 1 / 100 := by
  have hD0 : 0 ≤ D := le_trans (by norm_num) hD
  have hpos : 0 < (D + 1) ^ 4 := by positivity
  have hεD : ε * (D + 1) ^ 4 ≤ 1 / 100 := by
    rw [le_div_iff₀ (by positivity)] at hε
    linarith
  have h16 := (zero_bias_rounding D ε hD0 hε).1
  constructor
  · nlinarith
  · have hs : Real.sqrt (D + 1) ≤ D + 1 := by
      rw [Real.sqrt_le_left]
      · nlinarith
      · linarith
    have h1 : 64 * ε * D * Real.sqrt (D + 1) ≤ 64 * ε * (D + 1) ^ 2 := by
      have : D * Real.sqrt (D + 1) ≤ (D + 1) * (D + 1) :=
        mul_le_mul (by linarith) hs (Real.sqrt_nonneg _) (by linarith)
      nlinarith
    have h2 : 64 * (D + 1) ^ 2 < (D + 1) ^ 4 / 1 := by
      have : (8 : ℝ) ^ 2 < (D + 1) ^ 2 := pow_lt_pow_left₀ (by linarith) (by norm_num)
        (by norm_num)
      nlinarith
    have h3 : 64 * ε * (D + 1) ^ 2 < 1 / 100 := by
      by_cases hε' : ε = 0
      · rw [hε']; norm_num
      · have hεpos : 0 < ε := lt_of_le_of_ne hε0 (Ne.symm hε')
        have := mul_lt_mul_of_pos_left h2 hεpos
        nlinarith
    linarith

end ExactSampling.CriticalCounts
