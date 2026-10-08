import Mathlib

/-!
# The critical bottleneck: gate, derivative scales, and mixture exactness

This module formalizes the gate, scaling and mixture arithmetic of
`thm:rank-two-critical` (tanh_rank_two.tex), on which
`thm:signed-bottleneck` (tanh_rank_two.tex), `thm:rank-three-critical`
(tanh_rank_three.tex), `thm:fixed-rank-critical` (tanh_fixed_rank_batching.tex)
and the main statement `thm:main-bottleneck` (exact_sampling_networks.tex) rely.

Formalized:
* the output radius `|F| ≤ tanh^{∘(D-1)}(1) ≤ ρ_D = √(3/(2D+1))`;
* the dyadic gate: `q ≤ 6/√(D+1)`, `q^{-1} ≤ √D`, `‖F/q‖ ≤ 4/5`, in both cases
  `2ρ_D ≥ 1` (`q = 1`) and `2ρ_D < 1`;
* the layer sums `∑_{ℓ ≤ D} ℓ^{(k-3)/2} ≤ 2 D^{(k-1)/2}` and the conversion
  `D^{(k-1)/2} √D ≤ (D+1)^{⌈k/2⌉}` behind `M_k = 2^k C_k 4^k (D+1)^{⌈k/2⌉}`;
* from `M_k ≤ c (D+1)^{⌈k/2⌉}` (`2 ≤ k ≤ 6`), an explicit starting level
  `m = (2 + 98c)(D+1)` satisfying the conditions of `lem:rank-two-bernstein`,
  hence `O(√(D+1))` expected probes after the gate;
* exactness of the branch mixture and the geometric refinement charges;
* the guard-bit error recursion `e_{k,j} ≤ c_k ζ (D+1)^{(k+1)^2}`, with explicit
  constants `c_k` depending only on the chain-rule constants `A_k`.

Not formalized: the derivative bounds `E_{k,D} ≤ C_k 4^k D^{(k-1)/2}` (the
Bell-polynomial chain rule; they enter as the hypotheses `M_k ≤ c(D+1)^{⌈k/2⌉}`),
the error recurrences of the augmented forward pass (hypotheses of
`guard_bit_recursion`), the basis construction, the Taylor oracle, and the
online bit accounting.
-/

open Real Finset

namespace ExactSampling.NewBottleneck

/-! ## Radius estimates

These repeat the series argument of `prop:new-local-obstruction`
(tanh_new_critical.tex). -/

/-- `tanh` is positive on positive reals. Auxiliary for `thm:rank-two-critical`
(tanh_rank_two.tex). -/
theorem tanh_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hx) (Real.cosh_pos x)

/-- Paper: `prop:new-local-obstruction` (tanh_new_critical.tex), proof: each
coefficient ratio of the `sinh^2` series is at most `1/3`; in the form
`12^n ≤ 6 (2n)!`. -/
theorem twelve_pow_le (n : ℕ) : (12 : ℝ) ^ n ≤ 6 * ((2 * n).factorial : ℝ) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; norm_num [Nat.factorial]
    · have h1 : (2 * (k + 1)).factorial = (2 * k + 2) * ((2 * k + 1) * (2 * k).factorial) := by
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      rw [h1]
      push_cast
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hf : (0 : ℝ) ≤ ((2 * k).factorial : ℝ) := by positivity
      rw [pow_succ]
      have h12 : (12 : ℝ) ≤ (2 * k + 2) * (2 * k + 1) := by nlinarith
      calc (12 : ℝ) ^ k * 12 ≤ 6 * ((2 * k).factorial : ℝ) * 12 := by nlinarith
        _ ≤ 6 * ((2 * k).factorial : ℝ) * ((2 * k + 2) * (2 * k + 1)) := by
          apply mul_le_mul_of_nonneg_left h12; positivity
        _ = 6 * ((2 * k + 2) * ((2 * k + 1) * ((2 * k).factorial : ℝ))) := by ring

/-- Paper: `prop:new-local-obstruction` (tanh_new_critical.tex), proof: the
series of `sinh^2 x` is coefficientwise bounded by `x^2/(1 - x^2/3)`. -/
theorem sinh_sq_le {x : ℝ} (hx : x ^ 2 < 3) :
    Real.sinh x ^ 2 ≤ x ^ 2 / (1 - x ^ 2 / 3) := by
  set y := x ^ 2 / 3 with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y < 1 := by rw [hy]; linarith
  have hcosh := Real.hasSum_cosh (2 * x)
  have hgeo := (hasSum_geometric_of_lt_one hy0 hy1).mul_left 6
  have hδ : HasSum (fun n : ℕ => if n = 0 then (5 : ℝ) else 0) 5 := hasSum_ite_eq 0 5
  have hle := hasSum_le (fun n => ?_) (hcosh.add hδ) hgeo
  · have h2 : Real.cosh (2 * x) = 1 + 2 * Real.sinh x ^ 2 := by
      rw [Real.cosh_two_mul, Real.cosh_sq]; ring
    rw [h2] at hle
    have h1y : 0 < 1 - y := by linarith
    have : Real.sinh x ^ 2 ≤ 3 * y / (1 - y) := by
      rw [le_div_iff₀ h1y]
      rw [← div_eq_mul_inv, le_div_iff₀ h1y] at hle
      nlinarith
    calc Real.sinh x ^ 2 ≤ 3 * y / (1 - y) := this
      _ = x ^ 2 / (1 - x ^ 2 / 3) := by rw [hy]; ring
  · show (2 * x) ^ (2 * n) / ((2 * n).factorial : ℝ) + (if n = 0 then 5 else 0) ≤ 6 * y ^ n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; norm_num
    · have hne : n ≠ 0 := hn.ne'
      simp only [hne, ite_false, add_zero]
      have hf : (0 : ℝ) < ((2 * n).factorial : ℝ) := by positivity
      rw [div_le_iff₀ hf]
      have hpow : (2 * x) ^ (2 * n) = 12 ^ n * y ^ n := by
        rw [pow_mul, show (2 * x) ^ 2 = 12 * y by rw [hy]; ring, mul_pow]
      rw [hpow]
      have hyn : 0 ≤ y ^ n := pow_nonneg hy0 n
      nlinarith [twelve_pow_le n]

/-- Paper: `prop:new-local-obstruction` (tanh_new_critical.tex), proof:
`coth^2 x ≥ x^{-2} + 2/3`, in the form `tanh^2 x ≤ 3x^2/(3 + 2x^2)`. -/
theorem tanh_sq_le {x : ℝ} (hx : x ^ 2 < 3) :
    Real.tanh x ^ 2 ≤ 3 * x ^ 2 / (3 + 2 * x ^ 2) := by
  have hs := sinh_sq_le hx
  have hc : Real.cosh x ^ 2 = 1 + Real.sinh x ^ 2 := Real.cosh_sq' x
  have hcpos : 0 < Real.cosh x ^ 2 := by positivity
  rw [Real.tanh_eq_sinh_div_cosh, div_pow, div_le_div_iff₀ hcpos (by positivity), hc]
  have h3 : 0 < 1 - x ^ 2 / 3 := by linarith
  rw [le_div_iff₀ h3] at hs
  nlinarith

/-- `tanh x ≤ x` for `x ≥ 0`. Auxiliary for `thm:rank-two-critical`
(tanh_rank_two.tex). -/
theorem tanh_le_self {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  rcases lt_or_ge x 1 with h | h
  · have hx2 : x ^ 2 < 3 := by nlinarith
    have ht := tanh_sq_le hx2
    have h3 : 3 * x ^ 2 / (3 + 2 * x ^ 2) ≤ x ^ 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg x]
    have ht0 : 0 ≤ Real.tanh x := by
      rcases hx.eq_or_lt with h0 | h0
      · subst h0; simp
      · exact (tanh_pos h0).le
    nlinarith
  · exact (Real.tanh_lt_one x).le.trans h

/-- The critical radii `R_0 = 1`, `R_{j+1} = tanh R_j`
(tanh_new_critical.tex, `prop:new-local-obstruction`). -/
noncomputable def R (j : ℕ) : ℝ := Real.tanh^[j] 1

/-- `R_0 = 1`. Auxiliary for `thm:rank-two-critical`
(tanh_rank_two.tex). -/
theorem R_zero : R 0 = 1 := rfl

/-- `R_{j+1} = tanh R_j`. Auxiliary for `thm:rank-two-critical`
(tanh_rank_two.tex). -/
theorem R_succ (j : ℕ) : R (j + 1) = Real.tanh (R j) :=
  Function.iterate_succ_apply' _ _ _

/-- The radii are positive. Auxiliary for `thm:rank-two-critical`
(tanh_rank_two.tex). -/
theorem R_pos (j : ℕ) : 0 < R j := by
  induction j with
  | zero => rw [R_zero]; norm_num
  | succ j ih => rw [R_succ]; exact tanh_pos ih

/-- The radii are at most one. Auxiliary for `thm:rank-two-critical`
(tanh_rank_two.tex). -/
theorem R_le_one (j : ℕ) : R j ≤ 1 := by
  induction j with
  | zero => rw [R_zero]
  | succ j ih => rw [R_succ]; exact (tanh_le_self (R_pos j).le).trans ih

/-- The radii decrease. Auxiliary for `thm:rank-two-critical`
(tanh_rank_two.tex). -/
theorem R_succ_le (j : ℕ) : R (j + 1) ≤ R j := by
  rw [R_succ]; exact tanh_le_self (R_pos j).le

/-- Paper: `prop:new-local-obstruction` and `prop:new-critical-derivatives`
(tanh_new_critical.tex): `R_j^2 ≤ 3/(2j+3)`. -/
theorem R_sq_le (j : ℕ) : R j ^ 2 ≤ 3 / (2 * j + 3) := by
  induction j with
  | zero => rw [R_zero]; norm_num
  | succ j ih =>
    rw [R_succ]
    have h0 : 0 ≤ R j ^ 2 := sq_nonneg _
    have hlt : R j ^ 2 < 3 := by
      have : (3 : ℝ) / (2 * j + 3) ≤ 1 := by
        rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
      linarith
    have ht := tanh_sq_le hlt
    have hmono : 3 * R j ^ 2 / (3 + 2 * R j ^ 2) ≤ 3 / (2 * ((j + 1 : ℕ) : ℝ) + 3) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      rw [le_div_iff₀ (by positivity)] at ih
      push_cast
      nlinarith
    linarith

/-- `∑_{ℓ=1}^D ℓ^{-1/2} ≤ 2 √D`. Auxiliary for `thm:rank-two-critical`
(tanh_rank_two.tex). -/
theorem sum_inv_sqrt_le (D : ℕ) : ∑ ℓ ∈ range D, 1 / Real.sqrt ((ℓ : ℝ) + 1) ≤
    2 * Real.sqrt D := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [sum_range_succ]
    set a := Real.sqrt (D : ℝ)
    set b := Real.sqrt ((D : ℝ) + 1)
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have hb0 : 0 < b := Real.sqrt_pos.mpr (by positivity)
    have ha2 : a ^ 2 = D := Real.sq_sqrt (Nat.cast_nonneg D)
    have hb2 : b ^ 2 = (D : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hab : a * b ≤ (D : ℝ) + 1 / 2 := by nlinarith [sq_nonneg (a - b)]
    have hstep : 1 / b ≤ 2 * b - 2 * a := by
      rw [div_le_iff₀ hb0]; nlinarith
    push_cast
    linarith


/-- `tanh 1 < 4/5`. Auxiliary for `thm:rank-two-critical`
(tanh_rank_two.tex). -/
theorem tanh_one_lt : Real.tanh 1 < 4 / 5 := by
  rw [Real.tanh_eq]
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_one_gt_d9
  have h3 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have h4 : 0 < Real.exp (-1) := Real.exp_pos _
  rw [div_lt_iff₀ (by positivity)]
  have h5 : Real.exp (-1) * Real.exp 1 = 1 := by rw [h3]; field_simp
  nlinarith

/-- Paper: `thm:rank-two-critical` (tanh_rank_two.tex): first-layer outputs have
magnitude at most one and later rows are contractive, so
`|F| ≤ tanh^{∘(D-1)}(1) ≤ ρ_D = √(3/(2D+1))`; in squared form
`R_{D-1}^2 ≤ 3/(2D+1)`. -/
theorem output_radius (D : ℕ) (hD : 1 ≤ D) : R (D - 1) ^ 2 ≤ 3 / (2 * (D : ℝ) + 1) := by
  have h := R_sq_le (D - 1)
  have e : (2 * ((D - 1 : ℕ) : ℝ) + 3) = 2 * (D : ℝ) + 1 := by
    rw [Nat.cast_sub hD]; push_cast; ring
  rwa [e] at h

/-- Paper: `thm:rank-two-critical` (tanh_rank_two.tex): the dyadic gate when
`2ρ_D ≥ 1` and `D ≥ 2`: `q = 1` satisfies `q ≤ 6/√(D+1)`, `q^{-1} ≤ √D` and,
since `|F| ≤ tanh 1 < 4/5`, `‖F/q‖ ≤ 4/5`. -/
theorem gate_large_radius (D : ℕ) (hD : 2 ≤ D)
    (hρ : 1 ≤ 4 * (3 / (2 * (D : ℝ) + 1))) (F : ℝ) (hF : |F| ≤ R (D - 1)) :
    (1 : ℝ) ≤ 6 / Real.sqrt ((D : ℝ) + 1) ∧ 1 / (1 : ℝ) ≤ Real.sqrt D ∧ |F / 1| ≤ 4 / 5 := by
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hD5 : (D : ℝ) ≤ 11 / 2 := by
    rw [show 4 * (3 / (2 * (D : ℝ) + 1)) = 12 / (2 * (D : ℝ) + 1) by ring,
      le_div_iff₀ (by positivity)] at hρ
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ (Real.sqrt_pos.mpr (by positivity)), one_mul,
      Real.sqrt_le_left (by norm_num)]
    linarith
  · rw [div_one, show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  · rw [div_one]
    have h1 : R (D - 1) ≤ R 1 := by
      obtain ⟨j, hj⟩ : ∃ j, D - 1 = j + 1 := ⟨D - 2, by omega⟩
      rw [hj]
      clear hj
      induction j with
      | zero => exact le_rfl
      | succ j ih => exact (R_succ_le (j + 1)).trans ih
    have h2 : R 1 = Real.tanh 1 := by rw [R_succ, R_zero]
    linarith [tanh_one_lt]

/-- Paper: `thm:rank-two-critical` (tanh_rank_two.tex): when `2ρ_D < 1`, a dyadic
gate `2ρ_D ≤ q < 4ρ_D` (the least power of two at least `2ρ_D`) satisfies
`q ≤ 6/√(D+1)`, `q^{-1} ≤ √D` and `‖F/q‖ ≤ 1/2 ≤ 4/5` for `|F| ≤ ρ_D`. -/
theorem gate_small_radius (D : ℕ) (hD : 1 ≤ D) (ρ q F : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ^ 2 = 3 / (2 * (D : ℝ) + 1)) (hq1 : 2 * ρ ≤ q) (hq2 : q < 4 * ρ)
    (hF : |F| ≤ ρ) :
    q ≤ 6 / Real.sqrt ((D : ℝ) + 1) ∧ 1 / q ≤ Real.sqrt D ∧ |F / q| ≤ 4 / 5 := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hρpos : 0 < ρ := by
    rcases hρ0.eq_or_lt with h | h
    · rw [← h] at hρ; have : (0 : ℝ) < 3 / (2 * (D : ℝ) + 1) := by positivity
      simp at hρ; linarith
    · exact h
  have hq : 0 < q := by linarith
  have hρ2 : ρ ^ 2 * (2 * (D : ℝ) + 1) = 3 := by rw [hρ]; field_simp
  refine ⟨?_, ?_, ?_⟩
  · have hs : 0 < Real.sqrt ((D : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hs2 : Real.sqrt ((D : ℝ) + 1) ^ 2 = (D : ℝ) + 1 := Real.sq_sqrt (by positivity)
    rw [le_div_iff₀ hs]
    have h4 : (q * Real.sqrt ((D : ℝ) + 1)) ^ 2 ≤ 36 := by
      rw [mul_pow, hs2]
      have : q ^ 2 ≤ 16 * ρ ^ 2 := by nlinarith
      nlinarith
    nlinarith [mul_pos hq hs]
  · have hs : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hs2 : Real.sqrt (D : ℝ) ^ 2 = D := Real.sq_sqrt (by positivity)
    rw [div_le_iff₀ hq]
    have h4 : 1 ≤ (2 * ρ * Real.sqrt D) ^ 2 := by
      rw [mul_pow, mul_pow, hs2]; nlinarith
    have h5 : 1 ≤ 2 * ρ * Real.sqrt D := by nlinarith [mul_pos (mul_pos two_pos hρpos) hs]
    nlinarith
  · rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
    linarith

/-! ## Derivative scales -/

/-- Paper: `thm:rank-two-critical` (tanh_rank_two.tex), proof:
`∑_{ℓ=1}^{D} ℓ^{(k-3)/2} ≤ 2 D^{(k-1)/2}` for every `k ≥ 2`. -/
theorem layer_power_sum (k D : ℕ) (hk : 2 ≤ k) :
    ∑ ℓ ∈ range D, ((ℓ : ℝ) + 1) ^ (((k : ℝ) - 3) / 2) ≤ 2 * (D : ℝ) ^ (((k : ℝ) - 1) / 2) := by
  rcases Nat.eq_or_lt_of_le hk with h2 | h3
  · subst h2
    have e1 : ∀ ℓ : ℕ, ((ℓ : ℝ) + 1) ^ ((((2 : ℕ) : ℝ) - 3) / 2) = 1 / Real.sqrt ((ℓ : ℝ) + 1) := by
      intro ℓ
      rw [show (((2 : ℕ) : ℝ) - 3) / 2 = -(1 / 2) by norm_num, Real.rpow_neg (by positivity),
        ← Real.sqrt_eq_rpow, one_div]
    have e2 : (D : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) = Real.sqrt D := by
      rw [show (((2 : ℕ) : ℝ) - 1) / 2 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    simp_rw [e1, e2]
    exact sum_inv_sqrt_le D
  · have he : 0 ≤ ((k : ℝ) - 3) / 2 := by
      have : (3 : ℝ) ≤ k := by exact_mod_cast h3
      linarith
    have hterm : ∀ ℓ ∈ range D, ((ℓ : ℝ) + 1) ^ (((k : ℝ) - 3) / 2) ≤
        (D : ℝ) ^ (((k : ℝ) - 3) / 2) := by
      intro ℓ hℓ
      have : (ℓ : ℝ) + 1 ≤ D := by have := mem_range.mp hℓ; exact_mod_cast this
      exact Real.rpow_le_rpow (by positivity) this he
    have hs := sum_le_sum hterm
    rw [sum_const, card_range, nsmul_eq_mul] at hs
    rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD; simp only [range_zero, sum_empty, Nat.cast_zero]
      exact mul_nonneg (by norm_num) (Real.rpow_nonneg le_rfl _)
    · have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
      have e : (D : ℝ) * (D : ℝ) ^ (((k : ℝ) - 3) / 2) = (D : ℝ) ^ (((k : ℝ) - 1) / 2) := by
        rw [show ((k : ℝ) - 1) / 2 = ((k : ℝ) - 3) / 2 + 1 by ring,
          Real.rpow_add_one hDpos.ne', mul_comm]
      rw [e] at hs
      have : 0 ≤ (D : ℝ) ^ (((k : ℝ) - 1) / 2) := Real.rpow_nonneg hDpos.le _
      linarith

/-- Paper: `thm:rank-two-critical` (tanh_rank_two.tex): for `f(p) = F(2p-1)/q`
with `q^{-1} ≤ √D`, the depth factor `D^{(k-1)/2} · √D` is at most
`(D+1)^{⌈k/2⌉}`, which gives `M_k = 2^k C_k 4^k (D+1)^{⌈k/2⌉}`. -/
theorem depth_factor (k : ℕ) (hk : 1 ≤ k) (D : ℝ) (hD : 0 ≤ D) :
    D ^ (((k : ℝ) - 1) / 2) * Real.sqrt D ≤ (D + 1) ^ ((k + 1) / 2) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsq : Real.sqrt D = D ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow D
  rcases hD.eq_or_lt with h0 | hpos
  · subst h0
    rw [Real.sqrt_zero, mul_zero]; positivity
  · rw [hsq, ← Real.rpow_add hpos, show ((k : ℝ) - 1) / 2 + 1 / 2 = (k : ℝ) / 2 by ring]
    have h1 : D ^ ((k : ℝ) / 2) ≤ (D + 1) ^ ((k : ℝ) / 2) :=
      Real.rpow_le_rpow hpos.le (by linarith) (by positivity)
    have h2 : (D + 1) ^ ((k : ℝ) / 2) ≤ (D + 1) ^ (((k + 1) / 2 : ℕ) : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      have : (k : ℝ) / 2 ≤ (((k + 1) / 2 : ℕ) : ℝ) := by
        have h := Nat.div_add_mod (k + 1) 2
        have hm : (k + 1) % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
        have : k ≤ 2 * ((k + 1) / 2) := by omega
        have : (k : ℝ) ≤ 2 * (((k + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      exact this
    rw [Real.rpow_natCast] at h2
    linarith

/-- Paper: `lem:rank-two-bernstein` and `thm:rank-two-critical`
(tanh_rank_two.tex): if `M_k ≤ c n^{⌈k/2⌉}` for `2 ≤ k ≤ 6`, with `n = D + 1`,
then `m = (2 + 98c) n` satisfies `m ≥ 2`, `m ≥ 2M_2`, `m^2 ≥ 32 S` and
`m^3 ≥ 4U`, where `S = M_2 + M_3 + M_4` and `U = M_4 + M_5 + M_6`. Hence
`m_0 = O(D+1)`. -/
theorem rank_two_start (c n M₂ M₃ M₄ M₅ M₆ : ℝ) (hc : 0 ≤ c) (hn : 1 ≤ n)
    (h₂ : M₂ ≤ c * n) (h₃ : M₃ ≤ c * n ^ 2) (h₄ : M₄ ≤ c * n ^ 2) (h₅ : M₅ ≤ c * n ^ 3)
    (h₆ : M₆ ≤ c * n ^ 3) :
    2 ≤ (2 + 98 * c) * n ∧ 2 * M₂ ≤ (2 + 98 * c) * n ∧
      32 * (M₂ + M₃ + M₄) ≤ ((2 + 98 * c) * n) ^ 2 ∧
      4 * (M₄ + M₅ + M₆) ≤ ((2 + 98 * c) * n) ^ 3 := by
  set K := 2 + 98 * c
  have hK : 2 ≤ K := by simp only [K]; linarith
  have hn2 : n ≤ n ^ 2 := by nlinarith
  have hn3 : n ^ 2 ≤ n ^ 3 := by nlinarith
  refine ⟨by nlinarith, by nlinarith, ?_, ?_⟩
  · have hS : M₂ + M₃ + M₄ ≤ 3 * c * n ^ 2 := by nlinarith
    have hK2 : 96 * c ≤ K ^ 2 := by nlinarith
    calc 32 * (M₂ + M₃ + M₄) ≤ 96 * c * n ^ 2 := by linarith
      _ ≤ K ^ 2 * n ^ 2 := by nlinarith [sq_nonneg n]
      _ = (K * n) ^ 2 := by ring
  · have hU : M₄ + M₅ + M₆ ≤ 3 * c * n ^ 3 := by nlinarith
    have hK3 : 12 * c ≤ K ^ 3 := by
      have h1 : 12 * c ≤ K := by simp only [K]; linarith
      have h2 : K ≤ K ^ 3 := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ K) (by nlinarith : (0 : ℝ) ≤ K ^ 2 - 1)]
      linarith
    calc 4 * (M₄ + M₅ + M₆) ≤ 12 * c * n ^ 3 := by linarith
      _ ≤ K ^ 3 * n ^ 3 := by nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ n) 3]
      _ = (K * n) ^ 3 := by ring

/-- Paper: `thm:rank-two-critical` (tanh_rank_two.tex): with the gate
`q ≤ 6/√n` and the conditional source count `2 m_0 ≤ 4 K n`, the expected
number of input probes is at most `24 K √n = O(√(D+1))`. -/
theorem probe_bound (q m0 K n : ℝ) (hn : 0 < n) (hq : q ≤ 6 / Real.sqrt n)
    (hm0 : 0 ≤ m0) (hm : m0 ≤ 2 * (K * n)) : q * (2 * m0) ≤ 24 * K * Real.sqrt n := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hK : 0 ≤ K * n := by linarith
  calc q * (2 * m0) ≤ (6 / Real.sqrt n) * (2 * (2 * (K * n))) :=
        mul_le_mul hq (by linarith) (by positivity) (by positivity)
    _ = 24 * K * (n / Real.sqrt n) := by ring
    _ = 24 * K * Real.sqrt n := by rw [Real.div_sqrt]

/-! ## Mixture exactness and refinement charges -/

/-- Paper: `lem:fixed-rank-bernstein` (tanh_bernstein_product.tex), proof: a
mixture that selects branch `i` with probability `w_i > 0`, returns a sign of mean
`a_i/w_i` there, and a fair sign on the remaining mass, has mean `∑ a_i`. -/
theorem mixture_exactness {ι : Type*} (s : Finset ι) (w a : ι → ℝ) (hw : ∀ i ∈ s, w i ≠ 0) :
    ∑ i ∈ s, w i * (a i / w i) + (1 - ∑ i ∈ s, w i) * 0 = ∑ i ∈ s, a i := by
  rw [mul_zero, add_zero]
  exact sum_congr rfl (fun i hi => by field_simp [hw i hi])

/-- Paper: `lem:fixed-rank-bernstein` (tanh_bernstein_product.tex), proof: the
two-branch case, a partial mean plus a residual branch of mass `r`. -/
theorem residual_mixture_exactness (F part r : ℝ) (hr : r ≠ 0) :
    part + r * ((F - part) / r) = F := by
  field_simp
  ring

/-- Paper: `lem:fixed-rank-bernstein` (tanh_bernstein_product.tex), proof: a
residual bounded by its positive branch mass is a legal sign mean. -/
theorem residual_mean_bounded (remainder r : ℝ) (hr : 0 < r) (h : |remainder| ≤ r) :
    |remainder / r| ≤ 1 := by
  rw [abs_div, abs_of_pos hr]
  exact (div_le_one hr).2 h

/-- Paper: `thm:rank-two-critical` (tanh_rank_two.tex): after `t` extra accuracy
bits the unresolved measure scales by `2^{-t}`; the refinement stages sum to
`∑_{t<m} 2^{-t} = 2 - 2·2^{-m}`. -/
theorem geometric_refinement_sum (m : ℕ) :
    (∑ k ∈ range m, (1 / 2 : ℝ) ^ k) = 2 - 2 * (1 / 2 : ℝ) ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [sum_range_succ, ih, pow_succ]
    ring

/-- Paper: `thm:rank-two-critical` (tanh_rank_two.tex): the refinement stages
cost at most twice the first stage. -/
theorem geometric_refinement_charge (m : ℕ) : (∑ k ∈ range m, (1 / 2 : ℝ) ^ k) ≤ 2 := by
  rw [geometric_refinement_sum]
  have hp : 0 ≤ (1 / 2 : ℝ) ^ m := pow_nonneg (by norm_num) m
  linarith

/-! ## Guard bits -/

/-- Partial sums `∑_{a ≤ k} c_a` of the guard constants. Auxiliary for
`thm:rank-two-critical` (tanh_rank_two.tex). -/
def guardSum (A : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => guardSum A k + (A (k + 1) * guardSum A k + 1)

/-- The guard constants `c_0 = 1`, `c_{k+1} = A_{k+1} ∑_{a ≤ k} c_a + 1`; they
depend only on the chain-rule constants `A_k`. Auxiliary for
`thm:rank-two-critical` (tanh_rank_two.tex). -/
def guardConst (A : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => A (k + 1) * guardSum A k + 1

/-- `guardSum A k = ∑_{a ≤ k} guardConst A a`. Auxiliary for
`thm:rank-two-critical` (tanh_rank_two.tex). -/
theorem guardSum_eq (A : ℕ → ℝ) (k : ℕ) :
    guardSum A k = ∑ a ∈ range (k + 1), guardConst A a := by
  induction k with
  | zero => simp [guardSum, guardConst]
  | succ k ih => rw [sum_range_succ, ← ih]; simp [guardSum, guardConst]

/-- The partial sums are at least one when every `A_k ≥ 0`. Auxiliary for
`thm:rank-two-critical` (tanh_rank_two.tex). -/
theorem one_le_guardSum (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) (k : ℕ) : 1 ≤ guardSum A k := by
  induction k with
  | zero => simp [guardSum]
  | succ k ih =>
    simp only [guardSum]
    have := mul_nonneg (hA (k + 1)) (by linarith : (0 : ℝ) ≤ guardSum A k)
    linarith

/-- The guard constants are at least one when every `A_k ≥ 0`. Auxiliary for
`thm:rank-two-critical` (tanh_rank_two.tex). -/
theorem one_le_guardConst (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) (k : ℕ) : 1 ≤ guardConst A k := by
  cases k with
  | zero => simp [guardConst]
  | succ k =>
    simp only [guardConst]
    have := mul_nonneg (hA (k + 1)) (by linarith [one_le_guardSum A hA k] :
      (0 : ℝ) ≤ guardSum A k)
    linarith

/-- Paper: `thm:rank-two-critical` (tanh_rank_two.tex), the guard-bit argument.
If the order-`k` error after layer `j` satisfies `e_{k,0} = 0`,
`e_{0,j+1} ≤ e_{0,j} + ζ` and
`e_{k,j+1} ≤ e_{k,j} + A_k (D+1)^k ∑_{a<k} e_{a,j} + ζ` (`k ≥ 1`, `A_k ≥ 0`), then
`e_{k,j} ≤ c_k ζ (D+1)^{(k+1)^2}` for `j ≤ D`, where `c_k = guardConst A k`
depends only on `A_0, …, A_k` (not on `D`, `ζ` or the errors). Hence guard
lengths are logarithmic in `D`. -/
theorem guard_bit_recursion (e : ℕ → ℕ → ℝ) (A : ℕ → ℝ) (ζ : ℝ) (D : ℕ)
    (hA : ∀ k, 0 ≤ A k) (hζ : 0 ≤ ζ) (he0 : ∀ k, e k 0 = 0)
    (h0 : ∀ j, e 0 (j + 1) ≤ e 0 j + ζ)
    (hk : ∀ k j, e (k + 1) (j + 1) ≤ e (k + 1) j +
      A (k + 1) * ((D : ℝ) + 1) ^ (k + 1) * ∑ a ∈ range (k + 1), e a j + ζ) :
    ∀ k, ∀ j ≤ D, e k j ≤ guardConst A k * ζ * ((D : ℝ) + 1) ^ ((k + 1) ^ 2) := by
  have hD1 : (1 : ℝ) ≤ (D : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) D; linarith
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · intro j hj
      have hlin : ∀ j, e 0 j ≤ j * ζ := by
        intro j; induction j with
        | zero => simp [he0]
        | succ j ihj => push_cast; linarith [h0 j]
      have hj' : (j : ℝ) ≤ (D : ℝ) + 1 := by
        have : (j : ℝ) ≤ D := by exact_mod_cast hj
        linarith
      calc e 0 j ≤ j * ζ := hlin j
        _ ≤ ((D : ℝ) + 1) * ζ := mul_le_mul_of_nonneg_right hj' hζ
        _ = guardConst A 0 * ζ * ((D : ℝ) + 1) ^ ((0 + 1) ^ 2) := by simp [guardConst]; ring
    · set S := guardSum A k
      set P := ((D : ℝ) + 1) ^ ((k + 1) ^ 2)
      have hS1 : 1 ≤ S := one_le_guardSum A hA k
      have hP1 : 1 ≤ P := one_le_pow₀ hD1
      have hPa : ∀ a < k + 1, ((D : ℝ) + 1) ^ ((a + 1) ^ 2) ≤ P := by
        intro a ha
        exact pow_le_pow_right₀ hD1 (Nat.pow_le_pow_left (by omega) 2)
      have hsum : ∀ j ≤ D, ∑ a ∈ range (k + 1), e a j ≤ S * ζ * P := by
        intro j hj
        have h1 : ∀ a ∈ range (k + 1), e a j ≤ guardConst A a * ζ * P := by
          intro a ha
          have ha' := mem_range.mp ha
          calc e a j ≤ guardConst A a * ζ * ((D : ℝ) + 1) ^ ((a + 1) ^ 2) := ih a ha' j hj
            _ ≤ guardConst A a * ζ * P := by
              apply mul_le_mul_of_nonneg_left (hPa a ha')
              exact mul_nonneg (by linarith [one_le_guardConst A hA a]) hζ
        have h2 := sum_le_sum h1
        rw [← sum_mul, ← sum_mul, ← guardSum_eq] at h2
        exact h2
      set step := A (k + 1) * ((D : ℝ) + 1) ^ (k + 1) * (S * ζ * P) + ζ
      have hlin : ∀ j ≤ D, e (k + 1) j ≤ j * step := by
        intro j hj
        induction j with
        | zero => simp [he0]
        | succ j ihj =>
          have h1 := ihj (by omega)
          have h2 := hk k j
          have h3 := hsum j (by omega)
          have hA0 : 0 ≤ A (k + 1) * ((D : ℝ) + 1) ^ (k + 1) := mul_nonneg (hA _) (by positivity)
          have h4 := mul_le_mul_of_nonneg_left h3 hA0
          push_cast
          nlinarith
      intro j hj
      have hj' : (j : ℝ) ≤ (D : ℝ) + 1 := by
        have : (j : ℝ) ≤ D := by exact_mod_cast hj
        linarith
      have hstep0 : 0 ≤ step := by
        have : 0 ≤ A (k + 1) * ((D : ℝ) + 1) ^ (k + 1) * (S * ζ * P) :=
          mul_nonneg (mul_nonneg (hA _) (by positivity))
            (mul_nonneg (mul_nonneg (by linarith) hζ) (by linarith))
        linarith
      have hexp : ((D : ℝ) + 1) * (((D : ℝ) + 1) ^ (k + 1) * P) ≤
          ((D : ℝ) + 1) ^ ((k + 1 + 1) ^ 2) := by
        simp only [P]
        rw [← mul_assoc, ← pow_succ', ← pow_add]
        exact pow_le_pow_right₀ hD1 (by nlinarith)
      have hP' : ((D : ℝ) + 1) ≤ ((D : ℝ) + 1) ^ ((k + 1 + 1) ^ 2) :=
        le_self_pow₀ hD1 (by positivity)
      have hAS : 0 ≤ A (k + 1) * S * ζ :=
        mul_nonneg (mul_nonneg (hA _) (by linarith)) hζ
      calc e (k + 1) j ≤ j * step := hlin j hj
        _ ≤ ((D : ℝ) + 1) * step := mul_le_mul_of_nonneg_right hj' hstep0
        _ = A (k + 1) * S * ζ * (((D : ℝ) + 1) * (((D : ℝ) + 1) ^ (k + 1) * P)) +
              ζ * ((D : ℝ) + 1) := by simp only [step]; ring
        _ ≤ A (k + 1) * S * ζ * ((D : ℝ) + 1) ^ ((k + 1 + 1) ^ 2) +
              ζ * ((D : ℝ) + 1) ^ ((k + 1 + 1) ^ 2) := by
            gcongr
        _ = guardConst A (k + 1) * ζ * ((D : ℝ) + 1) ^ ((k + 1 + 1) ^ 2) := by
            simp only [guardConst, S]; ring

end ExactSampling.NewBottleneck
