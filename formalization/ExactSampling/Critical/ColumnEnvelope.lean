import Mathlib

/-!
# The column-envelope sampler: radii, majorants, and counting

This module formalizes quantitative parts of `thm:column-envelope-critical`
(tanh_column_envelope.tex, `sec:column-envelope`). The same bound is summarized
after `thm:main-bottleneck` (exact_sampling_networks.tex) and in `sec:conf-open`
(conference.tex). The exact tilting and antithetic identities are in the
companion module `ColumnEnvelopeTilting`.

Formalized:
* the source vector `eq:column-vector-source`: `|Y_i| ≤ 1`, `E Y = W_1 x / C`
  and `C_col ≤ C ≤ 2 C_col`;
* the rounded radii: `R_{ℓ-1} ≤ r_ℓ ≤ R_{ℓ-1} + (ℓ-1)ε_0`, `r_ℓ ≤ 1`,
  `r_ℓ^2 ≤ 2/ℓ`, `r_D^2 ≥ 1/(2D-1)`, and the gate bounds
  `eq:column-top-gate`;
* the derivative-mass recursion (`B_D ≤ 4√2 √D`, `E_D ≤ 50 D`,
  `H_D ≤ 928 D^{3/2}`) and `eq:column-derivative-masses`, given the chain-rule
  recurrences;
* the first-derivative factory `eq:column-first-derivative-factory`: the
  coefficient lies in `[0, 1]` and its exact binomial mean is
  `(1 - h^2)/(1 + ε)`;
* the normalized derivative polynomials of `lem:column-diagram-coin` (equal to
  the iterated derivatives of `tanh` divided by their majorants), their
  coefficient sums `2, 8, 5`, the loss bounds `(1 + 1/(4D))^{4D} < 3` and `16`,
  and the retained probability `≤ 1`;
* the branch cancellations, the base and cubic estimator bounds, the
  branch-mass and source-count series (`eq:column-starting-degree`,
  `eq:column-source-count`), the explicit constants, the least valid starting
  level `m_0 < 4608 κ^2 D` and the product bound `q m_0 < 27648 κ^2 √D`;
* the arity arithmetic of the paragraph before `eq:column-growing-first-moment`
  and of `eq:column-growing-second-moment` (with the first moment of
  `eq:column-growing-first-moment` as a stand-in from `thm:quadraticradiusbits`),
  the tree recurrences `eq:column-growing-tree`, and the Cauchy–Schwarz step of
  `eq:column-growing-diagram`;
* the monotone-convergence summation of per-visit work bounds and the
  geometric-tail stopping argument.

Not formalized: the multivariate chain rule, the tensor majorants of
`eq:column-scalar-majorants` and the diagram sampler with the directional
estimator `eq:column-directional-estimator`; the majority representation of the
scalar factories (its generating-function moments enter as hypotheses); the
range bound `|F| ≤ r_D` (hypothesis `hF` of `top_gate`); the count `J ≤ 24 D^2`
of roots (hypothesis of `diagram_second_moment`); predictable charging in the
observable filtration; the Taylor remainders `eq:column-quartic-integral` and
`eq:column-hessian-integral`; `E Q ≤ q m_0`; the online bound
`O(κ^7 √D B^{40})` and the finite-bit implementation; the `O(D n^2 B^4)`
preprocessing; the fallback for `D < 32`; and the probability space of the whole
sampler.
-/

open Real Finset Filter MeasureTheory
open scoped ENNReal

namespace ExactSampling.ColumnEnvelope

/-! ## Scalar facts about tanh

These are the radius facts of `lem:radius` (`eq:cothradius`, tanh_rates.tex) and
the bound `eq:xcothx` (tanh_scalar.tex), proved by the series arguments also used
for `prop:new-local-obstruction` (tanh_new_critical.tex). -/

/-- `tanh' = 1 - tanh^2`. Auxiliary for the radii and arity bounds of `sec:column-envelope`
(tanh_column_envelope.tex). -/
theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  have heq : Real.tanh = Real.sinh / Real.cosh := by
    funext y; simp [Real.tanh_eq_sinh_div_cosh]
  rw [heq]
  convert h using 1
  simp only [Pi.div_apply]
  field_simp

/-- `tanh` is positive on positive reals. Auxiliary for the radii and arity bounds of
`sec:column-envelope`
(tanh_column_envelope.tex). -/
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

/-- Paper: `eq:cothradius` in `lem:radius` (tanh_rates.tex):
`coth^2 x ≥ x^{-2} + 2/3`, in the form `tanh^2 x ≤ 3x^2/(3 + 2x^2)`, for every
real `x`. -/
theorem tanh_sq_le (x : ℝ) : Real.tanh x ^ 2 ≤ 3 * x ^ 2 / (3 + 2 * x ^ 2) := by
  rcases le_or_gt 3 (x ^ 2) with hx | hx
  · have h1 : 1 ≤ 3 * x ^ 2 / (3 + 2 * x ^ 2) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith [Real.tanh_sq_lt_one x]
  have hs := sinh_sq_le hx
  have hc : Real.cosh x ^ 2 = 1 + Real.sinh x ^ 2 := Real.cosh_sq' x
  have hcpos : 0 < Real.cosh x ^ 2 := by positivity
  rw [Real.tanh_eq_sinh_div_cosh, div_pow, div_le_div_iff₀ hcpos (by positivity), hc]
  have h3 : 0 < 1 - x ^ 2 / 3 := by linarith
  rw [le_div_iff₀ h3] at hs
  nlinarith

/-- `tanh x ≤ x` for `x ≥ 0`. Auxiliary for the radii and arity bounds of `sec:column-envelope`
(tanh_column_envelope.tex). -/
theorem tanh_le_self {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  rcases lt_or_ge x 1 with h | h
  · have hx2 : x ^ 2 < 3 := by nlinarith
    have ht := tanh_sq_le x
    have h3 : 3 * x ^ 2 / (3 + 2 * x ^ 2) ≤ x ^ 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg x]
    have ht0 : 0 ≤ Real.tanh x := by
      rcases hx.eq_or_lt with h0 | h0
      · subst h0; simp
      · exact (tanh_pos h0).le
    nlinarith
  · exact (Real.tanh_lt_one x).le.trans h

/-- Paper: `eq:xcothx` (tanh_scalar.tex): `x coth x ≤ 1 + x^2/3`; the `x^{2k+1}` coefficient of
`(1 + x^2/3) sinh x - x cosh x` is `4k(k-1)/[3(2k+1)!] ≥ 0`. -/
theorem self_le_tanh_mul {x : ℝ} (hx : 0 ≤ x) :
    x * Real.cosh x ≤ (1 + x ^ 2 / 3) * Real.sinh x := by
  have hs := Real.hasSum_sinh x
  have hc := (Real.hasSum_cosh x).mul_left x
  have hs3 := hs.mul_left (x ^ 2 / 3)
  let g : ℕ → ℝ := fun n => if n = 0 then 0 else x ^ (2 * n + 1) / (3 * ((2 * n - 1).factorial : ℝ))
  have hg : HasSum g (x ^ 2 / 3 * Real.sinh x) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, g, ite_true, sub_zero]
    convert hs3 using 1
    funext n
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega, show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring,
      pow_add]
    field_simp
  have htot := (hs.add hg).sub hc
  have hnn : 0 ≤ Real.sinh x + x ^ 2 / 3 * Real.sinh x - x * Real.cosh x := by
    refine htot.nonneg (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [g]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp only [g, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
      rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by ring,
        show 2 * (k + 1) = (2 * k + 1) + 1 by ring,
        Nat.factorial_succ, Nat.factorial_succ (2 * k + 1)]
      push_cast
      have hF : (0 : ℝ) < ((2 * k + 1).factorial : ℝ) := by positivity
      have hxp : 0 ≤ x ^ (2 * k + 1 + 1 + 1) := pow_nonneg hx _
      have hkey : x ^ (2 * k + 1 + 1 + 1) / ((2 * (k : ℝ) + 2 + 1) * ((2 * (k : ℝ) + 1 + 1) *
            ((2 * k + 1).factorial : ℝ))) +
          x ^ (2 * k + 1 + 1 + 1) / (3 * ((2 * k + 1).factorial : ℝ)) -
          x * (x ^ (2 * k + 1 + 1) / ((2 * (k : ℝ) + 1 + 1) * ((2 * k + 1).factorial : ℝ))) =
          x ^ (2 * k + 1 + 1 + 1) * (4 * k * (k + 1)) /
            (3 * (2 * k + 3) * (2 * k + 2) * ((2 * k + 1).factorial : ℝ)) := by
        rw [pow_succ x (2 * k + 1 + 1)]
        field_simp
        ring
      rw [hkey]
      positivity
  nlinarith

/-- The critical radii `R_0 = 1`, `R_{j+1} = tanh R_j`
(tanh_new_critical.tex, `prop:new-local-obstruction`). -/
noncomputable def R (j : ℕ) : ℝ := Real.tanh^[j] 1

/-- `R_0 = 1`. Auxiliary for the radii and arity bounds of `sec:column-envelope`
(tanh_column_envelope.tex). -/
theorem R_zero : R 0 = 1 := rfl

/-- `R_{j+1} = tanh R_j`. Auxiliary for the radii and arity bounds of `sec:column-envelope`
(tanh_column_envelope.tex). -/
theorem R_succ (j : ℕ) : R (j + 1) = Real.tanh (R j) :=
  Function.iterate_succ_apply' _ _ _

/-- The radii are positive. Auxiliary for the radii and arity bounds of `sec:column-envelope`
(tanh_column_envelope.tex). -/
theorem R_pos (j : ℕ) : 0 < R j := by
  induction j with
  | zero => rw [R_zero]; norm_num
  | succ j ih => rw [R_succ]; exact tanh_pos ih

/-- The radii are at most one. Auxiliary for the radii and arity bounds of `sec:column-envelope`
(tanh_column_envelope.tex). -/
theorem R_le_one (j : ℕ) : R j ≤ 1 := by
  induction j with
  | zero => rw [R_zero]
  | succ j ih => rw [R_succ]; exact (tanh_le_self (R_pos j).le).trans ih

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
    have ht := tanh_sq_le (R j)
    have hmono : 3 * R j ^ 2 / (3 + 2 * R j ^ 2) ≤ 3 / (2 * ((j + 1 : ℕ) : ℝ) + 3) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      rw [le_div_iff₀ (by positivity)] at ih
      push_cast
      nlinarith
    linarith

/-- `x / tanh x ≤ 1 + x^2/3` for `x > 0`. Auxiliary for the radii and arity bounds of
`sec:column-envelope`
(tanh_column_envelope.tex). -/
theorem self_div_tanh_le {x : ℝ} (hx : 0 < x) : x / Real.tanh x ≤ 1 + x ^ 2 / 3 := by
  have h := self_le_tanh_mul hx.le
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  rw [Real.tanh_eq_sinh_div_cosh, div_div_eq_mul_div, div_le_iff₀ hs]
  linarith

/-- A square-root comparison used below. Auxiliary for the radii and arity bounds of
`sec:column-envelope`
(tanh_column_envelope.tex). -/
theorem le_mul_sqrt {x c y : ℝ} (hc : 0 ≤ c) (h : x ^ 2 ≤ c ^ 2 * y) :
    x ≤ c * Real.sqrt y := by
  have hy : c * Real.sqrt y = Real.sqrt (c ^ 2 * y) := by
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  rw [hy]
  exact Real.le_sqrt_of_sq_le h


/-- `tanh` is monotone. Auxiliary for the radii and arity bounds of `sec:column-envelope`
(tanh_column_envelope.tex). -/
theorem tanh_monotone : Monotone Real.tanh := by
  refine monotone_of_deriv_nonneg (fun x => (hasDerivAt_tanh x).differentiableAt)
    (fun x => ?_)
  rw [(hasDerivAt_tanh x).deriv]
  have := Real.tanh_sq_lt_one x
  linarith

/-- `tanh` is one-Lipschitz: `tanh a - tanh b ≤ a - b` for `b ≤ a`. Auxiliary for the radii and
arity bounds of `sec:column-envelope`
(tanh_column_envelope.tex). -/
theorem tanh_sub_le {a b : ℝ} (h : b ≤ a) : Real.tanh a - Real.tanh b ≤ a - b := by
  have hm : Monotone (fun x => x - Real.tanh x) := by
    refine monotone_of_deriv_nonneg
      (fun x => (differentiableAt_id.sub (hasDerivAt_tanh x).differentiableAt)) (fun x => ?_)
    have hd : HasDerivAt (fun x => x - Real.tanh x) (1 - (1 - Real.tanh x ^ 2)) x :=
      (hasDerivAt_id x).sub (hasDerivAt_tanh x)
    rw [hd.deriv]
    nlinarith [sq_nonneg (Real.tanh x)]
  have := hm h
  simp only at this
  linarith

/-- `tanh 1 < 15/16`. Auxiliary for the radii and arity bounds of `sec:column-envelope`
(tanh_column_envelope.tex). -/
theorem tanh_one_lt : Real.tanh 1 < 15 / 16 := by
  rw [Real.tanh_eq]
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_one_gt_d9
  have h3 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have h4 : 0 < Real.exp (-1) := Real.exp_pos _
  rw [div_lt_iff₀ (by positivity)]
  have h5 : Real.exp (-1) * Real.exp 1 = 1 := by rw [h3]; field_simp
  nlinarith

/-- Paper: `eq:column-top-gate` (tanh_column_envelope.tex): the scalar radius
lower bound `coth^2 x ≤ x^{-2} + 1`, i.e. `x^2/(1 + x^2) ≤ tanh^2 x`. -/
theorem tanh_sq_ge {x : ℝ} (hx : 0 < x) : x ^ 2 / (1 + x ^ 2) ≤ Real.tanh x ^ 2 := by
  have hs : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx.le
  have hc : Real.cosh x ^ 2 = 1 + Real.sinh x ^ 2 := Real.cosh_sq' x
  rw [Real.tanh_eq_sinh_div_cosh, div_pow, hc, div_le_div_iff₀ (by positivity) (by positivity)]
  have : x ^ 2 ≤ Real.sinh x ^ 2 := pow_le_pow_left₀ hx.le hs 2
  nlinarith

/-- `R_j^2 ≥ 1/(j+1)`. Auxiliary for the radii and arity bounds of `sec:column-envelope`
(tanh_column_envelope.tex). -/
theorem R_sq_ge (j : ℕ) : 1 / ((j : ℝ) + 1) ≤ R j ^ 2 := by
  induction j with
  | zero => rw [R_zero]; norm_num
  | succ j ih =>
    rw [R_succ]
    have h := tanh_sq_ge (R_pos j)
    have hp : 0 < R j ^ 2 := by have := R_pos j; positivity
    have hmono : 1 / (((j + 1 : ℕ) : ℝ) + 1) ≤ R j ^ 2 / (1 + R j ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      rw [div_le_iff₀ (by positivity)] at ih
      push_cast
      nlinarith
    linarith

/-- Paper: `eq:column-growing-second-moment` (tanh_column_envelope.tex):
`x coth x ≤ 1 + x` for `x > 0`. -/
theorem self_div_tanh_le_one_add {x : ℝ} (hx : 0 < x) : x / Real.tanh x ≤ 1 + x := by
  have hs : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx.le
  have hsp : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hcs : Real.cosh x - Real.sinh x = Real.exp (-x) := by
    rw [Real.cosh_eq, Real.sinh_eq]; ring
  have he : Real.exp (-x) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  rw [Real.tanh_eq_sinh_div_cosh, div_div_eq_mul_div, div_le_iff₀ hsp]
  nlinarith

/-- Paper: the arity paragraph before `eq:column-growing-first-moment`
(tanh_column_envelope.tex): `ρ coth ρ ≤ 4/3` for `0 < ρ ≤ 1`. -/
theorem self_div_tanh_le_four_thirds {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    x / Real.tanh x ≤ 4 / 3 := by
  have := self_div_tanh_le hx
  nlinarith

/-! ## The source vector -/

/-- Paper: `eq:column-vector-source` (tanh_column_envelope.tex). Let
`c_j ≥ max_i |w_{1,ij}|` (with `c_j = 0` only on zero columns), `C = ∑_j c_j > 0`,
and `|x_j| ≤ 1`. Choosing column `J` with probability `c_J/C` and returning
`Y_i = w_{1,iJ} x_J / c_J` gives `|Y_i| ≤ 1` and `E Y_i = (W_1 x)_i / C`. -/
theorem column_vector_source {m n : ℕ} (w : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (c : Fin n → ℝ) (hx : ∀ j, |x j| ≤ 1) (hc0 : ∀ j, 0 ≤ c j)
    (hcw : ∀ i j, |w i j| ≤ c j) (hC : 0 < ∑ j, c j) :
    (∀ i j, c j ≠ 0 → |w i j * x j / c j| ≤ 1) ∧
      ∀ i, ∑ j, (c j / ∑ k, c k) * (if c j = 0 then 0 else w i j * x j / c j) =
        (∑ j, w i j * x j) / ∑ k, c k := by
  refine ⟨fun i j hj => ?_, fun i => ?_⟩
  · have hcj : 0 < c j := lt_of_le_of_ne (hc0 j) (Ne.symm hj)
    rw [abs_div, abs_of_pos hcj, div_le_one hcj, abs_mul]
    calc |w i j| * |x j| ≤ c j * 1 := mul_le_mul (hcw i j) (hx j) (abs_nonneg _) (hc0 j)
      _ = c j := mul_one _
  · rw [sum_div]
    refine sum_congr rfl (fun j _ => ?_)
    by_cases hj : c j = 0
    · have hw : w i j = 0 := abs_eq_zero.mp (le_antisymm (hj ▸ hcw i j) (abs_nonneg _))
      simp [hj, hw]
    · simp only [hj, ↓reduceIte]
      field_simp

/-- Paper: `sec:column-envelope` (tanh_column_envelope.tex): if each `c_j` is the
least power of two at least `d_j = max_i |w_{1,ij}|` (so `d_j ≤ c_j ≤ 2 d_j`),
then `C_col ≤ C ≤ 2 C_col` with `C_col = ∑ d_j` and `C = ∑ c_j`. -/
theorem column_envelope_sandwich {n : ℕ} (d c : Fin n → ℝ)
    (h : ∀ j, d j ≤ c j ∧ c j ≤ 2 * d j) :
    ∑ j, d j ≤ ∑ j, c j ∧ ∑ j, c j ≤ 2 * ∑ j, d j := by
  refine ⟨sum_le_sum (fun j _ => (h j).1), ?_⟩
  rw [mul_sum]; exact sum_le_sum (fun j _ => (h j).2)

/-! ## Normalized tanh derivatives -/

/-- `tanh'' = -2 tanh + 2 tanh^3`. Auxiliary for `lem:column-diagram-coin`
(tanh_column_envelope.tex). -/
theorem iteratedDeriv_two_tanh :
    iteratedDeriv 2 Real.tanh = fun u => -2 * Real.tanh u + 2 * Real.tanh u ^ 3 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hd : deriv Real.tanh = fun u => 1 - Real.tanh u ^ 2 :=
    funext fun u => (hasDerivAt_tanh u).deriv
  rw [hd]
  funext u
  have h : HasDerivAt (fun x => 1 - Real.tanh x ^ 2) _ u :=
    ((hasDerivAt_tanh u).pow 2).const_sub 1
  rw [h.deriv]; push_cast; ring

/-- `tanh''' = -2 + 8 tanh^2 - 6 tanh^4`. Auxiliary for `lem:column-diagram-coin`
(tanh_column_envelope.tex). -/
theorem iteratedDeriv_three_tanh :
    iteratedDeriv 3 Real.tanh =
      fun u => -2 + 8 * Real.tanh u ^ 2 - 6 * Real.tanh u ^ 4 := by
  rw [iteratedDeriv_succ, iteratedDeriv_two_tanh]
  funext u
  have h : HasDerivAt (fun x => -2 * Real.tanh x + 2 * Real.tanh x ^ 3) _ u :=
    ((hasDerivAt_tanh u).const_mul (-2)).add (((hasDerivAt_tanh u).pow 3).const_mul 2)
  rw [h.deriv]; push_cast; ring

/-- `tanh'''' = 16 tanh - 40 tanh^3 + 24 tanh^5`. Auxiliary for
`lem:column-diagram-coin` (tanh_column_envelope.tex). -/
theorem iteratedDeriv_four_tanh :
    iteratedDeriv 4 Real.tanh =
      fun u => 16 * Real.tanh u - 40 * Real.tanh u ^ 3 + 24 * Real.tanh u ^ 5 := by
  rw [iteratedDeriv_succ, iteratedDeriv_three_tanh]
  funext u
  have h : HasDerivAt (fun x => -2 + 8 * Real.tanh x ^ 2 - 6 * Real.tanh x ^ 4) _ u :=
    (((hasDerivAt_tanh u).pow 2).const_mul 8).const_add (-2) |>.sub
      (((hasDerivAt_tanh u).pow 4).const_mul 6)
  rw [h.deriv]; push_cast; ring

/-! ## Rounded radii and the top gate -/

/-- Paper: `sec:column-envelope` (tanh_column_envelope.tex), the dyadic radii.
With `s i = r_{i+1}`, `s 0 = 1` and `tanh (s i) ≤ s (i+1) ≤ tanh (s i) + ε_0`,
one has `R_i ≤ s i ≤ R_i + i ε_0`. -/
theorem radii_between (s : ℕ → ℝ) (ε₀ : ℝ) (hs0 : s 0 = 1)
    (hlo : ∀ i, Real.tanh (s i) ≤ s (i + 1)) (hhi : ∀ i, s (i + 1) ≤ Real.tanh (s i) + ε₀)
    (i : ℕ) : R i ≤ s i ∧ s i ≤ R i + i * ε₀ := by
  induction i with
  | zero => simp [hs0, R_zero]
  | succ i ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor
    · rw [R_succ]; exact (tanh_monotone h1).trans (hlo i)
    · have h3 : Real.tanh (s i) ≤ Real.tanh (R i + i * ε₀) := tanh_monotone h2
      have h4 : Real.tanh (R i + i * ε₀) - Real.tanh (R i) ≤ i * ε₀ := by
        have := tanh_sub_le (show R i ≤ R i + i * ε₀ by linarith)
        linarith
      rw [R_succ]
      push_cast
      linarith [hhi i]

/-- Paper: `sec:column-envelope` (tanh_column_envelope.tex): the rounded radii
are at most one, from `tanh 1 + 1/16 < 1`. -/
theorem radii_le_one (s : ℕ → ℝ) (ε₀ : ℝ) (hε : ε₀ ≤ 1 / 16) (hs0 : s 0 = 1)
    (hhi : ∀ i, s (i + 1) ≤ Real.tanh (s i) + ε₀)
    (i : ℕ) : s i ≤ 1 := by
  induction i with
  | zero => rw [hs0]
  | succ i ih =>
    have := tanh_monotone ih
    have := tanh_one_lt
    linarith [hhi i]

/-- Paper: `sec:column-envelope` (tanh_column_envelope.tex): for `1 ≤ ℓ ≤ D`,
`r_ℓ^2 ≤ 2/ℓ`, from `r_ℓ ≤ R_{ℓ-1} + D ε_0` and `ε_0 ≤ 1/(16 D^2)`. -/
theorem radii_sq_le (s : ℕ → ℝ) (ε₀ : ℝ) (D : ℕ) (hε0 : 0 ≤ ε₀)
    (hε : ε₀ ≤ 1 / (16 * (D : ℝ) ^ 2)) (hs0 : s 0 = 1)
    (hlo : ∀ i, Real.tanh (s i) ≤ s (i + 1)) (hhi : ∀ i, s (i + 1) ≤ Real.tanh (s i) + ε₀)
    (i : ℕ) (hi : i < D) : s i ^ 2 ≤ 2 / ((i : ℝ) + 1) := by
  obtain ⟨h1, h2⟩ := radii_between s ε₀ hs0 hlo hhi i
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hiD : (i : ℝ) + 1 ≤ D := by exact_mod_cast hi
  have hR := R_sq_le i
  have hR0 := (R_pos i).le
  have hR1 := R_le_one i
  set b := (i : ℝ) * ε₀
  have hb0 : 0 ≤ b := by positivity
  have hb : b ≤ 1 / (16 * ((i : ℝ) + 1)) := by
    have : (i : ℝ) * ε₀ ≤ D * (1 / (16 * (D : ℝ) ^ 2)) := by
      have hi' : (i : ℝ) ≤ D := by linarith
      exact mul_le_mul hi' hε hε0 (by positivity)
    have e : (D : ℝ) * (1 / (16 * (D : ℝ) ^ 2)) = 1 / (16 * D) := by field_simp
    rw [e] at this
    calc b ≤ 1 / (16 * D) := this
      _ ≤ 1 / (16 * ((i : ℝ) + 1)) := by
        apply one_div_le_one_div_of_le (by positivity); linarith
  have hs0' : 0 ≤ s i := le_trans hR0 h1
  have hsq : s i ^ 2 ≤ (R i + b) ^ 2 := pow_le_pow_left₀ hs0' h2 2
  have hl : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  rw [le_div_iff₀ hl]
  rw [le_div_iff₀ (by positivity)] at hR
  rw [le_div_iff₀ (by positivity)] at hb
  have hbl : b * ((i : ℝ) + 1) ≤ 1 / 16 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hbl hb0, mul_le_mul_of_nonneg_left hR1 hb0]

/-- Paper: `eq:column-top-gate` (tanh_column_envelope.tex), the lower bound
`r_D ≥ R_{D-1} ≥ (2D-1)^{-1/2}`, as `r_D^2 ≥ 1/(2D-1)`. -/
theorem top_radius_sq_ge (s : ℕ → ℝ) (ε₀ : ℝ) (hs0 : s 0 = 1)
    (hlo : ∀ i, Real.tanh (s i) ≤ s (i + 1)) (hhi : ∀ i, s (i + 1) ≤ Real.tanh (s i) + ε₀)
    (i : ℕ) : 1 / (2 * ((i : ℝ) + 1) - 1) ≤ s i ^ 2 := by
  have h1 := (radii_between s ε₀ hs0 hlo hhi i).1
  have h2 := R_sq_ge i
  have hR0 := (R_pos i).le
  have hsq : R i ^ 2 ≤ s i ^ 2 := pow_le_pow_left₀ hR0 h1 2
  have : 1 / (2 * ((i : ℝ) + 1) - 1) ≤ 1 / ((i : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith
  linarith

/-- Paper: `eq:column-top-gate` (tanh_column_envelope.tex). For `D ≥ 32`, if
`1/(2D-1) ≤ r_D^2 ≤ 2/D` and the gate `q` satisfies `2 r_D ≤ q < 4 r_D` (as the
least power of two at least `2 r_D` does), then `0 < q ≤ 1`,
`q ≤ 6 D^{-1/2}`, `q^{-1} ≤ √D`, and `|F| ≤ r_D` gives `|F/q| ≤ 1/2`. -/
theorem top_gate (D : ℕ) (hD : 32 ≤ D) (rD q F : ℝ) (hr0 : 0 ≤ rD)
    (hlo : 1 / (2 * (D : ℝ) - 1) ≤ rD ^ 2) (hhi : rD ^ 2 ≤ 2 / D)
    (hq1 : 2 * rD ≤ q) (hq2 : q < 4 * rD) (hF : |F| ≤ rD) :
    0 < q ∧ q ≤ 1 ∧ q ≤ 6 / Real.sqrt D ∧ 1 / q ≤ Real.sqrt D ∧ |F / q| ≤ 1 / 2 := by
  have hD' : (32 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := by linarith
  have hrpos : 0 < rD ^ 2 := lt_of_lt_of_le (div_pos one_pos (by linarith)) hlo
  have hr : 0 < rD := by
    rcases hr0.eq_or_lt with h | h
    · rw [← h] at hrpos; simp at hrpos
    · exact h
  have hq : 0 < q := by linarith
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hDpos
  have hsD2 : Real.sqrt D ^ 2 = D := Real.sq_sqrt hDpos.le
  have hr2 : rD ^ 2 * D ≤ 2 := by rw [le_div_iff₀ hDpos] at hhi; exact hhi
  refine ⟨hq, ?_, ?_, ?_, ?_⟩
  · have : rD ^ 2 ≤ 1 / 16 := by
      have : (2 : ℝ) / D ≤ 1 / 16 := by rw [div_le_div_iff₀ hDpos (by norm_num)]; linarith
      linarith
    nlinarith
  · rw [le_div_iff₀ hsD]
    have h4 : (q * Real.sqrt D) ^ 2 < 36 := by
      rw [mul_pow, hsD2]
      have : q ^ 2 < 16 * rD ^ 2 := by nlinarith
      nlinarith
    nlinarith [mul_pos hq hsD]
  · rw [div_le_iff₀ hq]
    have h4 : 1 ≤ (2 * rD * Real.sqrt D) ^ 2 := by
      rw [mul_pow, mul_pow, hsD2]
      rw [div_le_iff₀ (by linarith)] at hlo
      nlinarith
    have h5 : 1 ≤ 2 * rD * Real.sqrt D := by nlinarith [mul_pos (mul_pos two_pos hr) hsD]
    nlinarith
  · rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
    linarith

/-! ## Derivative masses -/

/-- `∑_{ℓ=1}^D ℓ^{-1/2} ≤ 2 √D`. Auxiliary for `eq:column-derivative-masses`
(tanh_column_envelope.tex). -/
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

/-- Paper: `eq:column-derivative-masses` (tanh_column_envelope.tex). Let
`B, E, H` be the normalized masses of orders two, three, four, with radii
`r ℓ` satisfying `0 ≤ r_ℓ ≤ 1` and `r_ℓ^2 ≤ 2/ℓ` (`radii_sq_le`). Under the
chain-rule recurrences (hypotheses), `B_D ≤ 4√2 √D < 6√D`, `E_D ≤ 50 D` and
`H_D ≤ 928 D^{3/2}`. -/
theorem column_mass_bounds (r B E H : ℕ → ℝ) (D : ℕ)
    (hr0 : ∀ ℓ, 0 ≤ r ℓ) (hr1 : ∀ ℓ, r ℓ ≤ 1)
    (hr2 : ∀ ℓ : ℕ, ℓ < D → r (ℓ + 1) ^ 2 ≤ 2 / ((ℓ : ℝ) + 1))
    (hB0 : B 0 = 0) (hE0 : E 0 = 0) (hH0 : H 0 = 0) (hBnn : ∀ ℓ, 0 ≤ B ℓ)
    (hB : ∀ ℓ, B (ℓ + 1) ≤ B ℓ + 2 * r (ℓ + 1))
    (hE : ∀ ℓ, E (ℓ + 1) ≤ E ℓ + 6 * r (ℓ + 1) * B ℓ + 2)
    (hH : ∀ ℓ, H (ℓ + 1) ≤ H ℓ + 8 * r (ℓ + 1) * E ℓ + 6 * r (ℓ + 1) * B ℓ ^ 2 +
      12 * B ℓ + 16 * r (ℓ + 1)) :
    B D ≤ 4 * Real.sqrt 2 * Real.sqrt D ∧ B D ≤ 6 * Real.sqrt D ∧ E D ≤ 50 * D ∧
      H D ≤ 928 * D * Real.sqrt D := by
  have hrs : ∀ ℓ : ℕ, ℓ < D → r (ℓ + 1) ≤ Real.sqrt 2 * (1 / Real.sqrt ((ℓ : ℝ) + 1)) := by
    intro ℓ hℓ
    have hl : (0 : ℝ) < (ℓ : ℝ) + 1 := by positivity
    have e : Real.sqrt 2 * (1 / Real.sqrt ((ℓ : ℝ) + 1)) = Real.sqrt (2 / ((ℓ : ℝ) + 1)) := by
      rw [Real.sqrt_div' 2 hl.le]; ring
    rw [e]
    exact Real.le_sqrt_of_sq_le (hr2 ℓ hℓ)
  have hBle : ∀ ℓ : ℕ, ℓ ≤ D → B ℓ ≤ 4 * Real.sqrt 2 * Real.sqrt ℓ := by
    intro ℓ hℓ
    have hsum : B ℓ ≤ 2 * ∑ j ∈ range ℓ, r (j + 1) := by
      clear hℓ
      induction ℓ with
      | zero => simp [hB0]
      | succ ℓ ih => rw [sum_range_succ]; linarith [hB ℓ]
    have h2 : ∑ j ∈ range ℓ, r (j + 1) ≤
        ∑ j ∈ range ℓ, Real.sqrt 2 * (1 / Real.sqrt ((j : ℝ) + 1)) :=
      sum_le_sum (fun j hj => hrs j (by have := mem_range.mp hj; omega))
    rw [← mul_sum] at h2
    have h3 := sum_inv_sqrt_le ℓ
    have h4 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith [mul_le_mul_of_nonneg_left h3 h4]
  have hBsq : ∀ ℓ : ℕ, ℓ ≤ D → B ℓ ^ 2 ≤ 32 * ℓ := by
    intro ℓ hℓ
    have h1 := hBle ℓ hℓ
    have h2 : (4 * Real.sqrt 2 * Real.sqrt ℓ) ^ 2 = 32 * ℓ := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (Nat.cast_nonneg ℓ)]; ring
    rw [← h2]
    exact pow_le_pow_left₀ (hBnn ℓ) h1 2
  have hrB : ∀ ℓ : ℕ, ℓ < D → r (ℓ + 1) * B ℓ ≤ 8 := by
    intro ℓ hℓ
    have h1 := hr2 ℓ hℓ
    have h2 := hBsq ℓ hℓ.le
    have hl : (0 : ℝ) < (ℓ : ℝ) + 1 := by positivity
    rw [le_div_iff₀ hl] at h1
    have hsq : (r (ℓ + 1) * B ℓ) ^ 2 ≤ 64 := by
      rw [mul_pow]
      have h3 : r (ℓ + 1) ^ 2 * B ℓ ^ 2 ≤ r (ℓ + 1) ^ 2 * (32 * ℓ) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
      nlinarith
    nlinarith [mul_nonneg (hr0 (ℓ + 1)) (hBnn ℓ)]
  have hEle : ∀ ℓ : ℕ, ℓ ≤ D → E ℓ ≤ 50 * ℓ := by
    intro ℓ hℓ
    induction ℓ with
    | zero => simp [hE0]
    | succ ℓ ih =>
      have := ih (by omega)
      have := hrB ℓ (by omega)
      push_cast; linarith [hE ℓ]
  have hHle : ∀ ℓ : ℕ, ℓ ≤ D → H ℓ ≤ 928 * ℓ * Real.sqrt ℓ := by
    intro ℓ hℓ
    induction ℓ with
    | zero => simp [hH0]
    | succ ℓ ih =>
      have ihℓ := ih (by omega)
      have hl : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
      set s := Real.sqrt ((ℓ : ℝ) + 1)
      have hs1 : 1 ≤ s := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
      have hs2 : s ^ 2 = (ℓ : ℝ) + 1 := Real.sq_sqrt (by positivity)
      have h1 := hr2 ℓ (by omega)
      rw [le_div_iff₀ (by positivity)] at h1
      have hrl : r (ℓ + 1) * ℓ ≤ 1.4143 * s := by
        apply le_mul_sqrt (by norm_num)
        rw [mul_pow]
        have h4 : 0 ≤ (ℓ : ℝ) ^ 2 := sq_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left h1 h4]
      have hB1 : B ℓ ≤ 4 * 1.4143 * s := by
        have h5 := hBle ℓ (by omega)
        have h6 : Real.sqrt 2 ≤ 1.4143 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        have h7 : Real.sqrt ℓ ≤ s := Real.sqrt_le_sqrt (by linarith)
        have h8 : 0 ≤ Real.sqrt (ℓ : ℝ) := Real.sqrt_nonneg _
        nlinarith [mul_le_mul h6 h7 h8 (by norm_num)]
      have hE1 := hEle ℓ (by omega)
      have hB2 := hBsq ℓ (by omega)
      have hr0' := hr0 (ℓ + 1)
      have hr1' := hr1 (ℓ + 1)
      have hincr : 8 * r (ℓ + 1) * E ℓ + 6 * r (ℓ + 1) * B ℓ ^ 2 + 12 * B ℓ + 16 * r (ℓ + 1)
          ≤ 928 * s := by
        have e1 : 8 * r (ℓ + 1) * E ℓ ≤ 8 * r (ℓ + 1) * (50 * ℓ) :=
          mul_le_mul_of_nonneg_left hE1 (by positivity)
        have e2 : 6 * r (ℓ + 1) * B ℓ ^ 2 ≤ 6 * r (ℓ + 1) * (32 * ℓ) :=
          mul_le_mul_of_nonneg_left hB2 (by positivity)
        nlinarith
      have hsqrt : Real.sqrt ℓ ≤ s := Real.sqrt_le_sqrt (by linarith)
      have hsq0 : 0 ≤ Real.sqrt (ℓ : ℝ) := Real.sqrt_nonneg _
      have hstep : 928 * (ℓ : ℝ) * Real.sqrt ℓ + 928 * s ≤ 928 * ((ℓ : ℝ) + 1) * s := by
        nlinarith [mul_le_mul_of_nonneg_left hsqrt hl]
      push_cast
      linarith [hH ℓ]
  refine ⟨hBle D le_rfl, ?_, hEle D le_rfl, hHle D le_rfl⟩
  have h6 : 4 * Real.sqrt 2 ≤ 6 := by
    have : Real.sqrt 2 ≤ 1.5 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith
  have := hBle D le_rfl
  nlinarith [Real.sqrt_nonneg (D : ℝ)]

/-- Paper: `eq:column-derivative-masses` (tanh_column_envelope.tex): with
`C ≤ κ`, `κ ≥ 1`, `q^{-1} ≤ √D` and the normalized masses above, the masses of
`f = F/q` satisfy `M_2 ≤ 6κ^2 D`, `M_3 ≤ 50 κ^4 D^2`, `M_4 ≤ 928 κ^4 D^2`. -/
theorem column_masses_f (C κ qinv B E H : ℝ) (D : ℕ) (hD : 1 ≤ D) (hC0 : 0 ≤ C)
    (hCκ : C ≤ κ) (hκ : 1 ≤ κ) (hq0 : 0 ≤ qinv) (hq : qinv ≤ Real.sqrt D)
    (hB0 : 0 ≤ B) (hE0 : 0 ≤ E) (hH0 : 0 ≤ H)
    (hB : B ≤ 6 * Real.sqrt D) (hE : E ≤ 50 * D) (hH : H ≤ 928 * D * Real.sqrt D) :
    C ^ 2 * B * qinv ≤ 6 * κ ^ 2 * D ∧ C ^ 3 * E * qinv ≤ 50 * κ ^ 4 * D ^ 2 ∧
      C ^ 4 * H * qinv ≤ 928 * κ ^ 4 * D ^ 2 := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hs : Real.sqrt D ^ 2 = D := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ Real.sqrt (D : ℝ) := Real.sqrt_nonneg _
  have hs1 : Real.sqrt (D : ℝ) ≤ D := by nlinarith
  have hC2 : C ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ hC0 hCκ 2
  have hC3 : C ^ 3 ≤ κ ^ 4 := (pow_le_pow_left₀ hC0 hCκ 3).trans
    (pow_le_pow_right₀ hκ (by norm_num))
  have hC4 : C ^ 4 ≤ κ ^ 4 := pow_le_pow_left₀ hC0 hCκ 4
  refine ⟨?_, ?_, ?_⟩
  · calc C ^ 2 * B * qinv ≤ κ ^ 2 * (6 * Real.sqrt D) * Real.sqrt D := by
          apply mul_le_mul (mul_le_mul hC2 hB hB0 (by positivity)) hq hq0 (by positivity)
      _ = 6 * κ ^ 2 * D := by
          rw [show κ ^ 2 * (6 * Real.sqrt D) * Real.sqrt D =
            6 * κ ^ 2 * (Real.sqrt D * Real.sqrt D) by ring, Real.mul_self_sqrt (by linarith)]
  · calc C ^ 3 * E * qinv ≤ κ ^ 4 * (50 * D) * Real.sqrt D := by
          apply mul_le_mul (mul_le_mul hC3 hE hE0 (by positivity)) hq hq0 (by positivity)
      _ ≤ κ ^ 4 * (50 * D) * D := by
          apply mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = 50 * κ ^ 4 * D ^ 2 := by ring
  · calc C ^ 4 * H * qinv ≤ κ ^ 4 * (928 * D * Real.sqrt D) * Real.sqrt D := by
          apply mul_le_mul (mul_le_mul hC4 hH hH0 (by positivity)) hq hq0 (by positivity)
      _ = 928 * κ ^ 4 * D ^ 2 := by
          rw [show κ ^ 4 * (928 * D * Real.sqrt D) * Real.sqrt D =
            928 * κ ^ 4 * D * (Real.sqrt D * Real.sqrt D) by ring,
            Real.mul_self_sqrt (by linarith)]
          ring

/-! ## The first-derivative factory -/

/-- Binomial weights `binom(M,K) p^K (1-p)^{M-K}`. Auxiliary for
`eq:column-first-derivative-factory` (tanh_column_envelope.tex). -/
noncomputable def binomW (M K : ℕ) (p : ℝ) : ℝ := (M.choose K : ℝ) * p ^ K * (1 - p) ^ (M - K)

/-- Binomial weights are Bernstein basis polynomials evaluated at `p`. Auxiliary for
`eq:column-first-derivative-factory` (tanh_column_envelope.tex). -/
theorem binomW_eq (M K : ℕ) (p : ℝ) : binomW M K p = (bernsteinPolynomial ℝ M K).eval p := by
  simp [binomW, bernsteinPolynomial]

/-- The binomial weights sum to one. Auxiliary for
`eq:column-first-derivative-factory` (tanh_column_envelope.tex). -/
theorem binom_sum (M : ℕ) (p : ℝ) : ∑ K ∈ range (M + 1), binomW M K p = 1 := by
  have h := congrArg (Polynomial.eval p) (bernsteinPolynomial.sum ℝ M)
  rw [Polynomial.eval_finsetSum] at h
  simpa [binomW_eq] using h

/-- The binomial mean `E K = M p`. Auxiliary for
`eq:column-first-derivative-factory` (tanh_column_envelope.tex). -/
theorem binom_mean (M : ℕ) (p : ℝ) : ∑ K ∈ range (M + 1), (K : ℝ) * binomW M K p = M * p := by
  have h := congrArg (Polynomial.eval p) (bernsteinPolynomial.sum_smul ℝ M)
  rw [Polynomial.eval_finsetSum] at h
  simpa [binomW_eq, nsmul_eq_mul] using h

/-- The factorial moment `E K(K-1) = M(M-1) p^2`. Auxiliary for
`eq:column-first-derivative-factory` (tanh_column_envelope.tex). -/
theorem binom_factorial (M : ℕ) (p : ℝ) :
    ∑ K ∈ range (M + 1), ((K : ℝ) * ((K : ℝ) - 1)) * binomW M K p =
      (M : ℝ) * ((M : ℝ) - 1) * p ^ 2 := by
  have h := congrArg (Polynomial.eval p) (bernsteinPolynomial.sum_mul_smul ℝ M)
  rw [Polynomial.eval_finsetSum] at h
  simp only [nsmul_eq_mul, Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow,
    Polynomial.eval_X, ← binomW_eq] at h
  have hR : ((M * (M - 1) : ℕ) : ℝ) = (M : ℝ) * ((M : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · subst h0; simp
    · rw [Nat.cast_mul, Nat.cast_sub h0]; simp
  rw [hR] at h
  rw [← h]
  refine sum_congr rfl (fun K _ => ?_)
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simp
  · rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring

/-- Paper: `lem:column-diagram-coin` (tanh_column_envelope.tex), proof:
`E[K(M-K)] = M(M-1) p(1-p)` for a binomial count `K`. -/
theorem binom_cross (M : ℕ) (p : ℝ) :
    ∑ K ∈ range (M + 1), (K : ℝ) * ((M : ℝ) - K) * binomW M K p =
      (M : ℝ) * ((M : ℝ) - 1) * (p * (1 - p)) := by
  have h1 := binom_mean M p
  have h2 := binom_factorial M p
  have e : ∀ K ∈ range (M + 1), (K : ℝ) * ((M : ℝ) - K) * binomW M K p =
      ((M : ℝ) - 1) * ((K : ℝ) * binomW M K p) - ((K : ℝ) * ((K : ℝ) - 1)) * binomW M K p := by
    intro K _; ring
  rw [sum_congr rfl e, sum_sub_distrib, ← mul_sum, h1, h2]
  ring


/-- Paper: `eq:column-first-derivative-factory` (tanh_column_envelope.tex): the
elementary Bernstein coefficient `4K(M-K)/M^2` lies in `[0, 1]`. -/
theorem first_derivative_coefficient_bounds (M K : ℝ) (hM : 0 < M) (hK : 0 ≤ K)
    (hKM : K ≤ M) :
    0 ≤ 4 * K * (M - K) / M ^ 2 ∧ 4 * K * (M - K) / M ^ 2 ≤ 1 := by
  constructor
  · have : 0 ≤ M - K := by linarith
    positivity
  · apply (div_le_iff₀ (sq_pos_of_pos hM)).2
    nlinarith [sq_nonneg (M - 2 * K)]

/-- Paper: `eq:column-first-derivative-factory` (tanh_column_envelope.tex): with
`ε = 1/(M-1)` (in the paper `M = 4D + 1`, `ε = 1/(4D)`), `M/(M-1) = 1 + ε` and
the denominator `M(M-1)(1+ε)` equals `M^2`. -/
theorem first_derivative_denominator (M : ℝ) (hM : M - 1 ≠ 0) :
    M * (M - 1) * (1 + 1 / (M - 1)) = M ^ 2 := by
  field_simp
  ring

/-- Paper: `eq:column-first-derivative-factory` (tanh_column_envelope.tex): with
`M` independent signs of mean `h` and `K` plus signs, the conditional
probability `4K(M-K)/(M(M-1)(1+ε))` has expectation `(1 - h^2)/(1 + ε)`. -/
theorem first_derivative_mean (M : ℕ) (hM : 2 ≤ M) (h ε : ℝ) (hε : 1 + ε ≠ 0) :
    ∑ K ∈ range (M + 1), binomW M K ((1 + h) / 2) *
        (4 * K * ((M : ℝ) - K) / ((M : ℝ) * ((M : ℝ) - 1) * (1 + ε))) =
      (1 - h ^ 2) / (1 + ε) := by
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (M : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < M).ne'
  have hM1 : (M : ℝ) - 1 ≠ 0 := (by linarith : (0 : ℝ) < (M : ℝ) - 1).ne'
  have e : ∀ K ∈ range (M + 1), binomW M K ((1 + h) / 2) *
      (4 * K * ((M : ℝ) - K) / ((M : ℝ) * ((M : ℝ) - 1) * (1 + ε))) =
      (4 / ((M : ℝ) * ((M : ℝ) - 1) * (1 + ε))) *
        ((K : ℝ) * ((M : ℝ) - K) * binomW M K ((1 + h) / 2)) := by
    intro K _; field_simp
  rw [sum_congr rfl e, ← mul_sum, binom_cross]
  field_simp
  ring

/-! ## Losses in a sampled derivative term -/

/-- Paper: `lem:column-diagram-coin` (tanh_column_envelope.tex), algebra only (the
identification with `tanh''` is `normalized_derivatives`): with
`t = r u`, the order-two polynomial divided by its majorant `2r` is
`-u + r^2 u^3`; its absolute coefficient sum is at most `2` when `r ≤ 1`. -/
theorem normalized_second (r u : ℝ) (hr : r ≠ 0) (hr1 : r ^ 2 ≤ 1) :
    (-2 * (r * u) + 2 * (r * u) ^ 3) / (2 * r) = -u + r ^ 2 * u ^ 3 ∧ 1 + r ^ 2 ≤ 2 := by
  refine ⟨?_, by linarith⟩
  rw [div_eq_iff (mul_ne_zero two_ne_zero hr)]; ring

/-- Paper: `lem:column-diagram-coin` (tanh_column_envelope.tex): the order-three
polynomial divided by `2` is `-1 + 4r^2u^2 - 3r^4u^4`, with coefficient sum at
most `8`. -/
theorem normalized_third (r u : ℝ) (hr1 : r ^ 2 ≤ 1) :
    (-2 + 8 * (r * u) ^ 2 - 6 * (r * u) ^ 4) / 2 = -1 + 4 * r ^ 2 * u ^ 2 - 3 * r ^ 4 * u ^ 4 ∧
      1 + 4 * r ^ 2 + 3 * r ^ 4 ≤ 8 := by
  refine ⟨by ring, ?_⟩
  have h0 : 0 ≤ r ^ 2 := sq_nonneg r
  have : r ^ 4 = r ^ 2 * r ^ 2 := by ring
  nlinarith

/-- Paper: `lem:column-diagram-coin` (tanh_column_envelope.tex): the order-four
polynomial divided by `16r` is `u - (5/2)r^2u^3 + (3/2)r^4u^5`, with coefficient
sum at most `5`. -/
theorem normalized_fourth (r u : ℝ) (hr : r ≠ 0) (hr1 : r ^ 2 ≤ 1) :
    (16 * (r * u) - 40 * (r * u) ^ 3 + 24 * (r * u) ^ 5) / (16 * r) =
        u - 5 / 2 * r ^ 2 * u ^ 3 + 3 / 2 * r ^ 4 * u ^ 5 ∧
      1 + 5 / 2 * r ^ 2 + 3 / 2 * r ^ 4 ≤ 5 := by
  refine ⟨?_, ?_⟩
  · rw [div_eq_iff (mul_ne_zero (by norm_num) hr)]; ring
  have h0 : 0 ≤ r ^ 2 := sq_nonneg r
  have : r ^ 4 = r ^ 2 * r ^ 2 := by ring
  nlinarith

/-- Paper: `lem:column-diagram-coin` (tanh_column_envelope.tex): at a vertex with
`h = tanh s` and normalized activation `u = h/r`, the derivatives of orders two,
three, four divided by their majorants `2r`, `2`, `16r` of
`eq:column-scalar-majorants` are `-u + r^2u^3`, `-1 + 4r^2u^2 - 3r^4u^4` and
`u - (5/2) r^2 u^3 + (3/2) r^4 u^5`. -/
theorem normalized_derivatives (s r : ℝ) (hr : r ≠ 0) :
    iteratedDeriv 2 Real.tanh s / (2 * r) =
        -(Real.tanh s / r) + r ^ 2 * (Real.tanh s / r) ^ 3 ∧
      iteratedDeriv 3 Real.tanh s / 2 =
        -1 + 4 * r ^ 2 * (Real.tanh s / r) ^ 2 - 3 * r ^ 4 * (Real.tanh s / r) ^ 4 ∧
      iteratedDeriv 4 Real.tanh s / (16 * r) =
        Real.tanh s / r - 5 / 2 * r ^ 2 * (Real.tanh s / r) ^ 3 +
          3 / 2 * r ^ 4 * (Real.tanh s / r) ^ 5 := by
  rw [iteratedDeriv_two_tanh, iteratedDeriv_three_tanh, iteratedDeriv_four_tanh]
  refine ⟨?_, ?_, ?_⟩
  · rw [div_eq_iff (mul_ne_zero two_ne_zero hr)]; field_simp
  · field_simp; ring
  · rw [div_eq_iff (mul_ne_zero (by norm_num) hr)]; field_simp; ring

/-- Paper: `lem:column-diagram-coin` (tanh_column_envelope.tex): at most `4D`
first-derivative vertices lose a factor below `(1 + 1/(4D))^{4D} < 3`. -/
theorem first_derivative_loss (D N : ℕ) (hD : 1 ≤ D) (hN : N ≤ 4 * D) :
    (1 + 1 / (4 * (D : ℝ))) ^ N < 3 := by
  have hD' : (0 : ℝ) < 4 * D := by have : (1 : ℝ) ≤ D := by exact_mod_cast hD
                                   linarith
  have h1 : (1 + 1 / (4 * (D : ℝ))) ^ N ≤ (1 + 1 / (4 * (D : ℝ))) ^ (4 * D) :=
    pow_le_pow_right₀ (by have : 0 < 1 / (4 * (D : ℝ)) := by positivity
                          linarith) hN
  have h2 : (1 + 1 / (4 * (D : ℝ))) ^ (4 * D) ≤ Real.exp 1 := by
    have h3 : 1 + 1 / (4 * (D : ℝ)) ≤ Real.exp (1 / (4 * D)) := by
      have := Real.add_one_le_exp (1 / (4 * (D : ℝ))); linarith
    calc (1 + 1 / (4 * (D : ℝ))) ^ (4 * D) ≤ Real.exp (1 / (4 * D)) ^ (4 * D) :=
          pow_le_pow_left₀ (by positivity) h3 _
      _ = Real.exp 1 := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
  have h4 := Real.exp_one_lt_d9
  linarith

/-- Paper: `lem:column-diagram-coin` (tanh_column_envelope.tex): with
`K_2 = 2`, `K_3 = 8`, `K_4 = 5`, a diagram with `n_2, n_3, n_4` vertices of
orders two, three, four and `∑ (ν - 1) = n_2 + 2n_3 + 3n_4 ≤ 3` has
higher-derivative loss `2^{n_2} 8^{n_3} 5^{n_4} ≤ 16`. -/
theorem higher_derivative_loss (n₂ n₃ n₄ : ℕ) (h : n₂ + 2 * n₃ + 3 * n₄ ≤ 3) :
    (2 : ℝ) ^ n₂ * 8 ^ n₃ * 5 ^ n₄ ≤ 16 := by
  have h4 : n₄ ≤ 1 := by omega
  have h3 : n₃ ≤ 1 := by omega
  have h2 : n₂ ≤ 3 := by omega
  interval_cases n₄ <;> interval_cases n₃ <;> interval_cases n₂ <;>
    first | omega | norm_num

/-- Paper: `lem:column-diagram-coin` (tanh_column_envelope.tex): the final
retention probability `(1+ε)^{N_1} ∏ K_ν / 48` is at most one. -/
theorem retention_le_one (D N : ℕ) (hD : 1 ≤ D) (hN : N ≤ 4 * D) (n₂ n₃ n₄ : ℕ)
    (h : n₂ + 2 * n₃ + 3 * n₄ ≤ 3) :
    (1 + 1 / (4 * (D : ℝ))) ^ N * ((2 : ℝ) ^ n₂ * 8 ^ n₃ * 5 ^ n₄) / 48 ≤ 1 := by
  have h1 := first_derivative_loss D N hD hN
  have h2 := higher_derivative_loss n₂ n₃ n₄ h
  have h0 : 0 ≤ (1 + 1 / (4 * (D : ℝ))) ^ N := by positivity
  have h0' : 0 ≤ (2 : ℝ) ^ n₂ * 8 ^ n₃ * 5 ^ n₄ := by positivity
  rw [div_le_one (by norm_num)]
  nlinarith

/-- Paper: `lem:column-diagram-coin` (tanh_column_envelope.tex): the algebraic
rearrangement `(σa)(τb) = (στ)(ab)` used when the known edge signs are
multiplied with the factor means; the independence of the factors is not
formalized. -/
theorem product_of_signed_means (a b σ τ : ℝ) : (σ * a) * (τ * b) = (σ * τ) * (a * b) := by
  ring

/-! ## Empirical correction branches -/

/-- Paper: `sec:column-envelope` (tanh_column_envelope.tex): accepting a pairing
with probability `m ν_2` and returning `δ^2/ν_2` gives density `m δ^2`. -/
theorem accepted_quadratic_density (m v delta : ℝ) (hv : v ≠ 0) :
    (m * v) * (delta ^ 2 / v) = m * delta ^ 2 := by
  field_simp

/-- Paper: `sec:column-envelope` (tanh_column_envelope.tex): accepting with
probability `m^2 ν_4/3` gives density `m^2 δ^4/3`. -/
theorem accepted_quartic_density (m v delta : ℝ) (hv : v ≠ 0) :
    (m ^ 2 * v / 3) * (delta ^ 4 / v) = m ^ 2 * delta ^ 4 / 3 := by
  field_simp

/-- Paper: `eq:column-hessian-integral` (tanh_column_envelope.tex): the branch
mass `48 M_4/(2m^2)`, accepted density `m v_δ`, diagram mean `α/48` and bounded
factors give the integrand coefficient `M_4/(8m)`. -/
theorem hessian_branch_cancellation (M m v alpha u₁ u₂ d₁ d₂ : ℝ)
    (hm : m ≠ 0) (hv : v ≠ 0) :
    (48 * M / (2 * m ^ 2)) * (m * v) * (alpha / 48) * (u₁ * u₂ / 4) * (d₁ * d₂ / v) =
      M / (8 * m) * alpha * u₁ * u₂ * d₁ * d₂ := by
  field_simp
  ring

/-- Paper: `eq:column-quartic-integral` (tanh_column_envelope.tex): the quartic
branch gives exactly the negative fourth-order term `-(M_4/24) α ∏ δ`. -/
theorem quartic_branch_cancellation (M m w alpha d₁ d₂ d₃ d₄ : ℝ)
    (hm : m ≠ 0) (hw : w ≠ 0) :
    (48 * M / (8 * m ^ 2)) * (m ^ 2 * w / 3) * (alpha / 48) * (-(d₁ * d₂ * d₃ * d₄) / w) =
      -(M / 24 * alpha * d₁ * d₂ * d₃ * d₄) := by
  field_simp
  ring

/-- Paper: `sec:column-envelope` (tanh_column_envelope.tex): the quartic ratio
`∏ δ_a / (¼ ∑ δ_a^4)` has magnitude at most one (AM-GM). -/
theorem quartic_ratio_le (d₁ d₂ d₃ d₄ : ℝ) :
    |d₁ * d₂ * d₃ * d₄| ≤ (d₁ ^ 4 + d₂ ^ 4 + d₃ ^ 4 + d₄ ^ 4) / 4 := by
  have h1 : |d₁ * d₂| ≤ (d₁ ^ 2 + d₂ ^ 2) / 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (d₁ + d₂), sq_nonneg (d₁ - d₂)]
  have h2 : |d₃ * d₄| ≤ (d₃ ^ 2 + d₄ ^ 2) / 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (d₃ + d₄), sq_nonneg (d₃ - d₄)]
  rw [show d₁ * d₂ * d₃ * d₄ = (d₁ * d₂) * (d₃ * d₄) by ring, abs_mul]
  have := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  nlinarith [sq_nonneg (d₁ ^ 2 - d₂ ^ 2), sq_nonneg (d₃ ^ 2 - d₄ ^ 2),
    sq_nonneg (d₁ ^ 2 + d₂ ^ 2 - d₃ ^ 2 - d₄ ^ 2)]

/-- Paper: `sec:column-envelope` (tanh_column_envelope.tex): the Hessian ratio
`δ_{J_3} δ_{J_4} / v_δ`, `v_δ = (δ_{J_3}^2 + δ_{J_4}^2)/2`, has magnitude at most
one. -/
theorem hessian_ratio_le (d₃ d₄ : ℝ) : |d₃ * d₄| ≤ (d₃ ^ 2 + d₄ ^ 2) / 2 := by
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (d₃ + d₄), sq_nonneg (d₃ - d₄)]

/-- Paper: `sec:column-envelope` (tanh_column_envelope.tex): if
`m ≥ 384 M_2`, the base estimator `Ĝ_m = S/2 - (48 M_2/(4m)) Z u_{J_1} u_{J_2}`
satisfies `|Ĝ_m| ≤ 5/8`, so `Ĝ_m/(3/4)` is a legal sign mean. -/
theorem base_estimator_bound (S Z u₁ u₂ m M₂ : ℝ) (hS : |S| ≤ 1) (hZ : |Z| ≤ 1)
    (hu₁ : |u₁| ≤ 2) (hu₂ : |u₂| ≤ 2) (hm : 0 < m) (hM : 0 ≤ M₂) (h : 384 * M₂ ≤ m) :
    |S / 2 - 48 * M₂ / (4 * m) * Z * u₁ * u₂| ≤ 5 / 8 ∧
      |(S / 2 - 48 * M₂ / (4 * m) * Z * u₁ * u₂) / (3 / 4)| ≤ 1 := by
  have h1 : |S / 2| ≤ 1 / 2 := by rw [abs_div]; norm_num; linarith
  have hc : 48 * M₂ / (4 * m) ≤ 1 / 32 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hc0 : 0 ≤ 48 * M₂ / (4 * m) := by positivity
  have hZu : |Z * u₁ * u₂| ≤ 4 := by
    rw [abs_mul, abs_mul]
    have := abs_nonneg Z
    have := abs_nonneg u₁
    have := abs_nonneg u₂
    calc |Z| * |u₁| * |u₂| ≤ 1 * 2 * 2 := by
          apply mul_le_mul (mul_le_mul hZ hu₁ (by positivity) (by norm_num)) hu₂
            (by positivity) (by norm_num)
      _ = 4 := by norm_num
  have h2 : |48 * M₂ / (4 * m) * Z * u₁ * u₂| ≤ 1 / 8 := by
    rw [show 48 * M₂ / (4 * m) * Z * u₁ * u₂ = 48 * M₂ / (4 * m) * (Z * u₁ * u₂) by ring,
      abs_mul, abs_of_nonneg hc0]
    nlinarith [abs_nonneg (Z * u₁ * u₂)]
  have h3 := (abs_sub _ _).trans (add_le_add h1 h2)
  refine ⟨by linarith, ?_⟩
  rw [abs_div, div_le_one (by norm_num)]; norm_num; linarith

/-- Paper: `sec:column-envelope` (tanh_column_envelope.tex): the cubic estimator
`48 M_3 Z u_{J_1}u_{J_2}u_{J_3}/(2(m-1)(2m-1))` with `|u| ≤ 2` has magnitude at
most `48 · 6 M_3/m^2` for `m ≥ 2`. -/
theorem cubic_estimator_bound (Z u₁ u₂ u₃ m M₃ : ℝ) (hZ : |Z| ≤ 1) (hu₁ : |u₁| ≤ 2)
    (hu₂ : |u₂| ≤ 2) (hu₃ : |u₃| ≤ 2) (hm : 2 ≤ m) (hM : 0 ≤ M₃) :
    |48 * M₃ * Z * u₁ * u₂ * u₃ / (2 * (m - 1) * (2 * m - 1))| ≤ 48 * 6 * M₃ / m ^ 2 := by
  have hden : 0 < 2 * (m - 1) * (2 * m - 1) := by
    have : 0 < m - 1 := by linarith
    have : 0 < 2 * m - 1 := by linarith
    positivity
  have hprod : |Z * u₁ * u₂ * u₃| ≤ 8 := by
    rw [abs_mul, abs_mul, abs_mul]
    have := abs_nonneg Z
    have := abs_nonneg u₁
    have := abs_nonneg u₂
    have := abs_nonneg u₃
    calc |Z| * |u₁| * |u₂| * |u₃| ≤ 1 * 2 * 2 * 2 := by gcongr
      _ = 8 := by norm_num
  rw [show 48 * M₃ * Z * u₁ * u₂ * u₃ = 48 * M₃ * (Z * u₁ * u₂ * u₃) by ring, abs_div,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 48 * M₃), abs_of_pos hden,
    div_le_div_iff₀ hden (by positivity)]
  have hpoly : 4 * m ^ 2 ≤ 6 * ((m - 1) * (2 * m - 1)) := by nlinarith
  have h0 : 0 ≤ 48 * M₃ := by positivity
  calc 48 * M₃ * |Z * u₁ * u₂ * u₃| * m ^ 2 ≤ 48 * M₃ * 8 * m ^ 2 := by gcongr
    _ ≤ 48 * 6 * M₃ * (2 * (m - 1) * (2 * m - 1)) := by
      nlinarith [mul_le_mul_of_nonneg_left hpoly hM]

/-! ## Branch masses, source count and constants -/

/-- Paper: `sec:column-envelope` (tanh_column_envelope.tex): the cubic, Hessian
and quartic branch masses `48·6M_3/m^2`, `48M_4/(2m^2)`, `48M_4/(8m^2)` sum to
`(288M_3 + 30M_4)/m^2 ≤ K_* A/m^2`, with `K_* = 48`, `A = 6M_3 + M_4`. -/
theorem branch_masses (M₃ M₄ m : ℝ) (hM₄ : 0 ≤ M₄) (hm : 0 < m) :
    48 * 6 * M₃ / m ^ 2 + 48 * M₄ / (2 * m ^ 2) + 48 * M₄ / (8 * m ^ 2) =
        (288 * M₃ + 30 * M₄) / m ^ 2 ∧
      (288 * M₃ + 30 * M₄) / m ^ 2 ≤ 48 * (6 * M₃ + M₄) / m ^ 2 := by
  refine ⟨by field_simp; ring, ?_⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

/-- Paper: `eq:column-starting-degree` (tanh_column_envelope.tex): summing the
non-base masses over the levels `m = 2^a m_0` gives `4(288M_3 + 30M_4)/(3m_0^2)`. -/
theorem nonbase_mass_hasSum (c m0 : ℝ) (hm0 : 0 < m0) :
    HasSum (fun a : ℕ => c / (2 ^ a * m0) ^ 2) (4 * c / (3 * m0 ^ 2)) := by
  have hg := (hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num)
    (by norm_num)).mul_left (c / m0 ^ 2)
  convert hg using 1
  · funext a
    have h4 : ((2 : ℝ) ^ a) ^ 2 = 4 ^ a := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [mul_pow, h4, one_div_pow]
    field_simp
  · field_simp; ring

/-- Paper: `eq:column-starting-degree` (tanh_column_envelope.tex): the level law
`(3/4) 4^{-a}` is a probability distribution. -/
theorem level_law_hasSum : HasSum (fun a : ℕ => (3 / 4 : ℝ) * (1 / 4) ^ a) 1 := by
  have hg := (hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num)
    (by norm_num)).mul_left (3 / 4)
  convert hg using 1
  norm_num

/-- Paper: `eq:column-starting-degree` (tanh_column_envelope.tex): if
`m_0^2 ≥ 16 K_* A`, the total non-base mass `4K_*A/(3m_0^2)` is at most `1/12`. -/
theorem correction_mass (m K A : ℝ) (hm : 0 < m) (hstart : 16 * K * A ≤ m ^ 2) :
    4 * K * A / (3 * m ^ 2) ≤ (1 : ℝ) / 12 := by
  apply (div_le_iff₀ (by positivity : 0 < 3 * m ^ 2)).2
  nlinarith

/-- Paper: `eq:column-starting-degree` (tanh_column_envelope.tex): the base has
room inside its mixture weight, `1/2 + K M_2/m ≤ 5/8` when `8 K M_2 ≤ m`. -/
theorem base_margin (m K M₂ : ℝ) (hm : 0 < m) (hstart : 8 * K * M₂ ≤ m) :
    (1 : ℝ) / 2 + K * M₂ / m ≤ (5 : ℝ) / 8 := by
  have ht : K * M₂ / m ≤ (1 : ℝ) / 8 := by
    apply (div_le_iff₀ hm).2
    nlinarith
  linarith

/-- Paper: `eq:column-source-count` (tanh_column_envelope.tex): a correction at
level `m` probes `2m` observations, so the corrections cost
`∑_a (K_*A/m^2)(2m) = 4K_*A/m_0`. -/
theorem source_count_hasSum (K A m0 : ℝ) (hm0 : 0 < m0) :
    HasSum (fun a : ℕ => K * A / (2 ^ a * m0) ^ 2 * (2 * (2 ^ a * m0))) (4 * K * A / m0) := by
  have hg := (hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
    (by norm_num)).mul_left (2 * K * A / m0)
  convert hg using 1
  · funext a
    have h2 : (0 : ℝ) < 2 ^ a := by positivity
    rw [one_div_pow]
    field_simp
  · field_simp; ring

/-- Paper: `eq:column-source-count` (tanh_column_envelope.tex):
`(3/4) m_0 + 4K_*A/m_0 ≤ m_0` when `m_0^2 ≥ 16 K_* A`. -/
theorem conditional_source_count (m K A : ℝ) (hm : 0 < m) (hstart : 16 * K * A ≤ m ^ 2) :
    (3 : ℝ) / 4 * m + 4 * K * A / m ≤ m := by
  have ht : 4 * K * A / m ≤ m / 4 := by
    apply (div_le_iff₀ hm).2
    nlinarith
  linarith

/-- Paper: `eq:column-source-count` (tanh_column_envelope.tex):
`16 · 48 · (6 · 50 + 928) = 943104`. -/
theorem uniform_starting_constant : (16 : ℕ) * 48 * (6 * 50 + 928) = 943104 := by
  norm_num

/-- Paper: `eq:column-source-count` (tanh_column_envelope.tex):
`943104 ≤ 2304^2`. -/
theorem uniform_starting_square : (943104 : ℕ) ≤ 2304 ^ 2 := by
  norm_num

/-- Paper: `eq:column-source-count` (tanh_column_envelope.tex): `6 · 4608 = 27648`. -/
theorem uniform_source_constant : (6 : ℕ) * 4608 = 27648 := by
  norm_num

/-- Paper: `eq:column-source-count` (tanh_column_envelope.tex): with the mass
bounds `eq:column-derivative-masses`, every `m ≥ 2304 κ^2 D` satisfies the three
starting conditions `eq:column-starting-degree`. -/
theorem starting_level_sufficient (κ D M₂ M₃ M₄ m : ℝ) (hκ : 1 ≤ κ) (hD : 1 ≤ D)
    (hM₃0 : 0 ≤ M₃)
    (hM₂ : M₂ ≤ 6 * κ ^ 2 * D) (hM₃ : M₃ ≤ 50 * κ ^ 4 * D ^ 2)
    (hM₄ : M₄ ≤ 928 * κ ^ 4 * D ^ 2) (hm : 2304 * κ ^ 2 * D ≤ m) :
    2 ≤ m ∧ 8 * 48 * M₂ ≤ m ∧ 16 * 48 * (6 * M₃ + M₄) ≤ m ^ 2 := by
  have hκ2 : 1 ≤ κ ^ 2 := by nlinarith
  have hx : 1 ≤ κ ^ 2 * D := by nlinarith
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have h1 : 16 * 48 * (6 * M₃ + M₄) ≤ 943104 * (κ ^ 2 * D) ^ 2 := by nlinarith
  have h2 : 943104 * (κ ^ 2 * D) ^ 2 ≤ (2304 * κ ^ 2 * D) ^ 2 := by nlinarith
  have h3 : (2304 * κ ^ 2 * D) ^ 2 ≤ m ^ 2 :=
    pow_le_pow_left₀ (by positivity) hm 2
  linarith

/-- Paper: `eq:column-source-count` (tanh_column_envelope.tex), the arithmetic
`q m_0 < 27648 κ^2 √D` for `q ≤ 6 D^{-1/2}` and `m_0 < 4608 κ^2 D`. See
`column_query_bound` for the chained version. -/
theorem query_bound (κ D q m0 : ℝ) (hD : 0 < D) (hq0 : 0 < q) (hq : q ≤ 6 / Real.sqrt D)
    (hm0 : 0 ≤ m0) (hm : m0 < 4608 * κ ^ 2 * D) :
    q * m0 < 27648 * κ ^ 2 * Real.sqrt D := by
  have hs : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hsD : Real.sqrt D * Real.sqrt D = D := Real.mul_self_sqrt hD.le
  calc q * m0 < q * (4608 * κ ^ 2 * D) := mul_lt_mul_of_pos_left hm hq0
    _ ≤ 6 / Real.sqrt D * (4608 * κ ^ 2 * D) :=
        mul_le_mul_of_nonneg_right hq (by nlinarith [sq_nonneg κ])
    _ = 27648 * κ ^ 2 * Real.sqrt D := by
        have e : (6 : ℝ) / Real.sqrt D * (4608 * κ ^ 2 * D) =
            27648 * κ ^ 2 * (D / Real.sqrt D) := by ring
        rw [e, Real.div_sqrt]

/-- The least power of two at least `x ≥ 1` is below `2x`. Auxiliary for
`eq:column-source-count` (tanh_column_envelope.tex). -/
theorem least_pow_two_lt (x : ℝ) (hx : 1 ≤ x) : ∃ k : ℕ, x ≤ 2 ^ k ∧ (2 : ℝ) ^ k < 2 * x := by
  classical
  have hex : ∃ k : ℕ, x ≤ 2 ^ k := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)
    exact ⟨k, hk.le⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]; norm_num; linarith
  · have hlt := not_le.mp (Nat.find_min hex (Nat.sub_lt hpos one_pos))
    have e : (2 : ℝ) ^ Nat.find hex = 2 * 2 ^ (Nat.find hex - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e]; linarith

/-- The three starting conditions `eq:column-starting-degree` for a level `m`. -/
def StartOK (M₂ M₃ M₄ m : ℝ) : Prop :=
  2 ≤ m ∧ 8 * 48 * M₂ ≤ m ∧ 16 * 48 * (6 * M₃ + M₄) ≤ m ^ 2

/-- Paper: `eq:column-source-count` (tanh_column_envelope.tex): under the mass
bounds `eq:column-derivative-masses`, the least power of two `m_0 = 2^{k_0}`
satisfying the starting conditions exists and obeys `m_0 < 4608 κ^2 D`. -/
theorem least_starting_level (κ D M₂ M₃ M₄ : ℝ) (hκ : 1 ≤ κ) (hD : 1 ≤ D) (hM₃0 : 0 ≤ M₃)
    (hM₂ : M₂ ≤ 6 * κ ^ 2 * D) (hM₃ : M₃ ≤ 50 * κ ^ 4 * D ^ 2)
    (hM₄ : M₄ ≤ 928 * κ ^ 4 * D ^ 2) :
    ∃ k₀ : ℕ, StartOK M₂ M₃ M₄ (2 ^ k₀) ∧ (∀ k < k₀, ¬ StartOK M₂ M₃ M₄ (2 ^ k)) ∧
      (2 : ℝ) ^ k₀ < 4608 * κ ^ 2 * D := by
  classical
  have hx : 1 ≤ 2304 * κ ^ 2 * D := by
    have : 1 ≤ κ ^ 2 := one_le_pow₀ hκ
    nlinarith
  obtain ⟨k, hk1, hk2⟩ := least_pow_two_lt (2304 * κ ^ 2 * D) hx
  have hok : StartOK M₂ M₃ M₄ (2 ^ k) :=
    starting_level_sufficient κ D M₂ M₃ M₄ (2 ^ k) hκ hD hM₃0 hM₂ hM₃ hM₄ hk1
  have hex : ∃ k, StartOK M₂ M₃ M₄ (2 ^ k) := ⟨k, hok⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun k' hk' => Nat.find_min hex hk', ?_⟩
  have hle : Nat.find hex ≤ k := Nat.find_min' hex hok
  have : (2 : ℝ) ^ Nat.find hex ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hle
  linarith

/-- Paper: `eq:column-source-count` and `eq:column-top-gate`
(tanh_column_envelope.tex): for `D ≥ 32`, the gate `q` of `top_gate` and the least
valid starting level `m_0 = 2^{k_0}` satisfy `q m_0 < 27648 κ^2 √D`. The
probabilistic step `E Q ≤ q m_0` (the gate opens with probability `q`, and the
conditional source count is at most `m_0` by `conditional_source_count`) is not
formalized. -/
theorem column_query_bound (D : ℕ) (hD : 32 ≤ D) (κ M₂ M₃ M₄ rD q F : ℝ) (hκ : 1 ≤ κ)
    (hM₃0 : 0 ≤ M₃) (hM₂ : M₂ ≤ 6 * κ ^ 2 * D) (hM₃ : M₃ ≤ 50 * κ ^ 4 * D ^ 2)
    (hM₄ : M₄ ≤ 928 * κ ^ 4 * D ^ 2) (hr0 : 0 ≤ rD)
    (hlo : 1 / (2 * (D : ℝ) - 1) ≤ rD ^ 2) (hhi : rD ^ 2 ≤ 2 / D)
    (hq1 : 2 * rD ≤ q) (hq2 : q < 4 * rD) (hF : |F| ≤ rD) :
    ∃ k₀ : ℕ, StartOK M₂ M₃ M₄ (2 ^ k₀) ∧ (∀ k < k₀, ¬ StartOK M₂ M₃ M₄ (2 ^ k)) ∧
      q * 2 ^ k₀ < 27648 * κ ^ 2 * Real.sqrt D := by
  have hD1 : (1 : ℝ) ≤ D := by have : (32 : ℝ) ≤ D := by exact_mod_cast hD
                               linarith
  obtain ⟨hq0, -, hq, -, -⟩ := top_gate D hD rD q F hr0 hlo hhi hq1 hq2 hF
  obtain ⟨k₀, hok, hmin, hlt⟩ := least_starting_level κ D M₂ M₃ M₄ hκ hD1 hM₃0 hM₂ hM₃ hM₄
  exact ⟨k₀, hok, hmin, query_bound κ D q (2 ^ k₀) (by linarith) hq0 hq (by positivity) hlt⟩

/-- Paper: `thm:column-envelope-critical` (tanh_column_envelope.tex): an
amplitude gate `q ≤ 6/r` turns `N ≤ C r^2` retained observations into
`q N ≤ 6 C r`, with `r = √D`. -/
theorem gated_source_count (q N C r : ℝ) (hq0 : 0 ≤ q) (hC : 0 ≤ C) (hr : 0 < r)
    (hq : q ≤ 6 / r) (hN : N ≤ C * r ^ 2) :
    q * N ≤ 6 * C * r := by
  calc q * N ≤ q * (C * r ^ 2) := mul_le_mul_of_nonneg_left hN hq0
    _ ≤ (6 / r) * (C * r ^ 2) := mul_le_mul_of_nonneg_right hq (by positivity)
    _ = 6 * C * r := by field_simp

/-- Paper: `eq:column-starting-degree` (tanh_column_envelope.tex): a branch
sampled with its envelope mass contributes its exact mean. -/
theorem bounded_branch_mean (mass coefficient : ℝ) (hm : mass ≠ 0) :
    mass * (coefficient / mass) = coefficient := by
  field_simp

/-! ## Exactness and stopping -/

/-- Paper: `eq:column-starting-degree` (tanh_column_envelope.tex): finite
telescope for the corrected empirical coefficients. -/
theorem finite_telescope (P : ℕ → ℝ) (N : ℕ) :
    P 0 + ∑ k ∈ range N, (P (k + 1) - P k) = P N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ]
      linarith

/-- Paper: `eq:column-starting-degree` (tanh_column_envelope.tex): if the
coefficients converge, `P_m → f(E Y)`, the correction series converges to
`f(E Y) - P_{m_0}`, which is the exactness identity. The convergence `P_m → f`
itself (strong law and bounded convergence) is not formalized. -/
theorem telescope_exactness (P : ℕ → ℝ) (target : ℝ) (hP : Tendsto P atTop (nhds target)) :
    Tendsto (fun N => ∑ k ∈ range N, (P (k + 1) - P k)) atTop (nhds (target - P 0)) := by
  have heq : (fun N => ∑ k ∈ range N, (P (k + 1) - P k)) = fun N => P N - P 0 := by
    funext N
    have := finite_telescope P N
    linarith
  rw [heq]
  exact hP.sub_const (P 0)

/-- Paper: `eq:column-growing-coefficient` (tanh_column_envelope.tex), the
summation step only: the expected total of nonnegative per-visit costs is at
most the sum of per-visit expectation bounds (monotone convergence). The
hypothesis `hcost` is an unconditional bound for each visit index; deriving it
from the conditional work bound in the observable filtration (predictable
charging) is not formalized. -/
theorem predictable_stopped_work {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (cost : ℕ → Ω → ℝ≥0∞) (budget : ℕ → ℝ≥0∞)
    (hmeas : ∀ j, AEMeasurable (cost j) μ) (hcost : ∀ j, (∫⁻ ω, cost j ω ∂μ) ≤ budget j) :
    (∫⁻ ω, ∑' j : ℕ, cost j ω ∂μ) ≤ ∑' j : ℕ, budget j := by
  rw [lintegral_tsum hmeas]
  exact ENNReal.tsum_le_tsum hcost

/-- Paper: `thm:column-envelope-critical` (tanh_column_envelope.tex): a geometric
tail leaves no probability of infinite execution. -/
theorem zero_of_geometric_tail (p C : ℝ) (hp : 0 ≤ p)
    (htail : ∀ j : ℕ, p ≤ C * ((1 : ℝ) / 2) ^ j) : p = 0 := by
  have hpow : Tendsto (fun j : ℕ => ((1 : ℝ) / 2) ^ j) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Tendsto (fun j : ℕ => C * ((1 : ℝ) / 2) ^ j) atTop (nhds 0) := by
    simpa using hpow.const_mul C
  have hp0 : p ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall htail)
  linarith

/-! ## Arity moments -/

/-- Paper: the arity paragraph before `eq:column-growing-first-moment` and
`eq:column-growing-second-moment` (tanh_column_envelope.tex): the
majority index law `π_k = c d_k / C_k` with `C_k ≥ 1` has moments at most `c`
times those of the proposal `d`. -/
theorem tilted_moment_le (pw d Cw g : ℕ → ℝ) (c a b : ℝ) (hc : 0 ≤ c)
    (hπ : ∀ k, pw k = c * d k / Cw k) (hC : ∀ k, 1 ≤ Cw k) (hd : ∀ k, 0 ≤ d k)
    (hg : ∀ k, 0 ≤ g k) (ha : HasSum (fun k => pw k * g k) a)
    (hb : HasSum (fun k => d k * g k) b) : a ≤ c * b := by
  refine hasSum_le (fun k => ?_) ha (hb.mul_left c)
  rw [hπ k]
  have hC0 : 0 < Cw k := lt_of_lt_of_le one_pos (hC k)
  rw [div_mul_eq_mul_div, div_le_iff₀ hC0]
  have h1 : 0 ≤ c * d k * g k := by have := hd k; have := hg k; positivity
  nlinarith [hC k]

/-- Paper: the arity paragraph before `eq:column-growing-first-moment`
(tanh_column_envelope.tex): at a later layer, with `E_π K ≤ (ρ coth ρ) ρ^2` and
`E_π K^2 ≤ (ρ coth ρ)(ρ^2 + 4ρ^4/3)` (from the proposal moments, a stand-in for
the majority generating function), the full arity `2K + 1` has
`E A ≤ 1 + 3ρ^2` and `E A^2 ≤ 1 + 18ρ^2` for `0 < ρ ≤ 1`. -/
theorem upper_arity_moments (ρ EK EK2 : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hEK : EK ≤ ρ / Real.tanh ρ * ρ ^ 2)
    (hEK2 : EK2 ≤ ρ / Real.tanh ρ * (ρ ^ 2 + 4 / 3 * ρ ^ 4)) :
    1 + 2 * EK ≤ 1 + 3 * ρ ^ 2 ∧ 1 + (4 * EK2 + 4 * EK) ≤ 1 + 18 * ρ ^ 2 := by
  have hc := self_div_tanh_le_four_thirds hρ hρ1
  have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  have hρ21 : ρ ^ 2 ≤ 1 := by nlinarith
  have hρ4 : ρ ^ 4 ≤ ρ ^ 2 := by
    calc ρ ^ 4 = ρ ^ 2 * ρ ^ 2 := by ring
      _ ≤ ρ ^ 2 * 1 := mul_le_mul_of_nonneg_left hρ21 hρ2
      _ = ρ ^ 2 := by ring
  have hρ40 : 0 ≤ ρ ^ 4 := by positivity
  have h1 : EK ≤ 4 / 3 * ρ ^ 2 := le_trans hEK (mul_le_mul_of_nonneg_right hc hρ2)
  have h2 : EK2 ≤ 4 / 3 * (ρ ^ 2 + 4 / 3 * ρ ^ 4) :=
    le_trans hEK2 (mul_le_mul_of_nonneg_right hc (by positivity))
  constructor <;> nlinarith

/-- Paper: the arity paragraph before `eq:column-growing-first-moment`
(tanh_column_envelope.tex): with `ρ^2 ≤ r_{ℓ-1}^2 ≤ 2/(ℓ-1)`, the arity moments are
at most `1 + 6/(ℓ-1)` and
`1 + 36/(ℓ-1)`. -/
theorem layer_arity_constants (ρ i : ℝ) (hρ : ρ ^ 2 ≤ 2 / i) :
    1 + 3 * ρ ^ 2 ≤ 1 + 6 / i ∧ 1 + 18 * ρ ^ 2 ≤ 1 + 36 / i := by
  have e1 : 6 / i = 3 * (2 / i) := by ring
  have e2 : 36 / i = 18 * (2 / i) := by ring
  constructor <;> nlinarith

/-- Paper: `eq:column-growing-second-moment` (tanh_column_envelope.tex): the
expansion used after `C coth C ≤ 2κ`. -/
theorem uniform_arity_expansion (kappa : ℝ) :
    1 + 2 * kappa * (8 * kappa ^ 2 + (16 : ℝ) / 3 * kappa ^ 4) =
      1 + 16 * kappa ^ 3 + (32 : ℝ) / 3 * kappa ^ 5 := by
  ring

/-- Paper: `eq:column-growing-second-moment` (tanh_column_envelope.tex): for
`0 < C ≤ κ` and `κ ≥ 1`, `1 + C coth C (8C^2 + 16C^4/3) ≤ 28 κ^5`. -/
theorem first_layer_second_moment (C κ : ℝ) (hC : 0 < C) (hCκ : C ≤ κ) (hκ : 1 ≤ κ) :
    1 + C / Real.tanh C * (8 * C ^ 2 + 16 / 3 * C ^ 4) ≤ 28 * κ ^ 5 := by
  have h1 := self_div_tanh_le_one_add hC
  have h2 : C / Real.tanh C ≤ 2 * κ := by linarith
  have h0 : 0 ≤ C / Real.tanh C := by have := tanh_pos hC; positivity
  have hC2 : C ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ hC.le hCκ 2
  have hC4 : C ^ 4 ≤ κ ^ 4 := pow_le_pow_left₀ hC.le hCκ 4
  have h3 : 8 * C ^ 2 + 16 / 3 * C ^ 4 ≤ 8 * κ ^ 2 + 16 / 3 * κ ^ 4 := by linarith
  have h4 : C / Real.tanh C * (8 * C ^ 2 + 16 / 3 * C ^ 4) ≤
      2 * κ * (8 * κ ^ 2 + 16 / 3 * κ ^ 4) :=
    mul_le_mul h2 h3 (by positivity) (by positivity)
  have h5 := uniform_arity_expansion κ
  have hk3 : κ ^ 3 ≤ κ ^ 5 := pow_le_pow_right₀ hκ (by norm_num)
  have hk0 : 1 ≤ κ ^ 5 := one_le_pow₀ hκ
  linarith

/-- Paper: `eq:column-growing-second-moment` (tanh_column_envelope.tex): the
semantic first-layer count `S_1 = 1 + A_1` has `E S_1 ≤ 3κ^2` and
`E S_1^2 ≤ 58 κ^5`. The hypothesis `hEA`, `E A_1 ≤ 2κ^2`, is the content of
`eq:column-growing-first-moment`, imported from the general-radius theorem
`thm:quadraticradiusbits` (tanh_large_radius.tex) and taken here as a stand-in;
`hEA2` is supplied by `first_layer_second_moment`. -/
theorem semantic_first_layer (EA EA2 κ : ℝ) (hκ : 1 ≤ κ)
    (hEA : EA ≤ 2 * κ ^ 2) (hEA2 : EA2 ≤ 28 * κ ^ 5) :
    1 + EA ≤ 3 * κ ^ 2 ∧ 1 + 2 * EA + EA2 ≤ 58 * κ ^ 5 := by
  have hk2 : 1 ≤ κ ^ 2 := one_le_pow₀ hκ
  have hk5 : 1 ≤ κ ^ 5 := one_le_pow₀ hκ
  have hk25 : κ ^ 2 ≤ κ ^ 5 := pow_le_pow_right₀ hκ (by norm_num)
  constructor <;> nlinarith

/-! ## Recursive call trees -/

/-- Paper: `eq:column-growing-tree` (tanh_column_envelope.tex):
`p_ℓ = ∏_{j=1}^{ℓ-1} (1 + 6/j) = binom(ℓ+5, 6)`, here with `ℓ = i + 1`. -/
theorem tree_product_eq (i : ℕ) :
    ∏ j ∈ range i, (1 + 6 / ((j : ℝ) + 1)) = ((i + 6).choose 6 : ℝ) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [prod_range_succ, ih]
    have h := Nat.choose_mul_succ_eq (i + 6) 6
    rw [show i + 6 + 1 - 6 = i + 1 by omega, show i + 6 + 1 = i + 7 by ring] at h
    have h' : ((i + 6).choose 6 : ℝ) * ((i : ℝ) + 7) =
        ((i + 7).choose 6 : ℝ) * ((i : ℝ) + 1) := by
      have := congrArg (Nat.cast (R := ℝ)) h
      push_cast at this
      linarith
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    rw [show i + 1 + 6 = i + 7 by ring]
    field_simp
    linarith [h']

/-- Paper: `eq:column-growing-tree` (tanh_column_envelope.tex):
`1 ≤ p_ℓ ≤ (ℓ+5)^6`. -/
theorem tree_product_bounds (i : ℕ) :
    1 ≤ ∏ j ∈ range i, (1 + 6 / ((j : ℝ) + 1)) ∧
      ∏ j ∈ range i, (1 + 6 / ((j : ℝ) + 1)) ≤ ((i : ℝ) + 6) ^ 6 := by
  rw [tree_product_eq]
  constructor
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  · have := Nat.choose_le_pow (i + 6) 6
    exact_mod_cast this

/-- Paper: `eq:column-growing-tree` (tanh_column_envelope.tex), first moments:
if `a_1 ≤ 3κ^2` and `a_ℓ ≤ 1 + (1 + 6/(ℓ-1)) a_{ℓ-1}`, then
`a_ℓ ≤ κ^2 (ℓ+5)^7` (here `a i` stands for `a_{i+1}`). -/
theorem tree_first_moment (a : ℕ → ℝ) (κ : ℝ) (hκ : 1 ≤ κ) (h0 : a 0 ≤ 3 * κ ^ 2)
    (hstep : ∀ i : ℕ, a (i + 1) ≤ 1 + (1 + 6 / ((i : ℝ) + 1)) * a i) (i : ℕ) :
    a i ≤ κ ^ 2 * ((i : ℝ) + 6) ^ 7 := by
  set p : ℕ → ℝ := fun i => ∏ j ∈ range i, (1 + 6 / ((j : ℝ) + 1))
  have hp : ∀ i, a i ≤ p i * (3 * κ ^ 2 + i) := by
    intro i
    induction i with
    | zero => simp [p, h0]
    | succ i ih =>
      have hμ : 0 ≤ 1 + 6 / ((i : ℝ) + 1) := by positivity
      have hp1 : 1 ≤ p (i + 1) := (tree_product_bounds (i + 1)).1
      have hps : p (i + 1) = p i * (1 + 6 / ((i : ℝ) + 1)) := by simp [p, prod_range_succ]
      calc a (i + 1) ≤ 1 + (1 + 6 / ((i : ℝ) + 1)) * a i := hstep i
        _ ≤ 1 + (1 + 6 / ((i : ℝ) + 1)) * (p i * (3 * κ ^ 2 + i)) := by gcongr
        _ = 1 + p (i + 1) * (3 * κ ^ 2 + i) := by rw [hps]; ring
        _ ≤ p (i + 1) * (3 * κ ^ 2 + ((i + 1 : ℕ) : ℝ)) := by push_cast; nlinarith
  have h1 := hp i
  have h2 := (tree_product_bounds i).2
  have hk : 1 ≤ κ ^ 2 := one_le_pow₀ hκ
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hpi : 0 ≤ p i := le_trans zero_le_one (tree_product_bounds i).1
  calc a i ≤ p i * (3 * κ ^ 2 + i) := h1
    _ ≤ ((i : ℝ) + 6) ^ 6 * (κ ^ 2 * ((i : ℝ) + 6)) := by
        apply mul_le_mul h2 (by nlinarith) (by positivity) (by positivity)
    _ = κ ^ 2 * ((i : ℝ) + 6) ^ 7 := by ring

/-- Paper: `eq:column-growing-tree` (tanh_column_envelope.tex), second moments:
with `0 ≤ a_ℓ ≤ κ^2(ℓ+5)^7`, `b_1 ≤ 58κ^5` and
`b_ℓ ≤ μ_ℓ b_{ℓ-1} + 1 + 2μ_ℓ a_{ℓ-1} + ν_ℓ a_{ℓ-1}^2`,
`μ_ℓ = 1 + 6/(ℓ-1)`, `ν_ℓ = 1 + 36/(ℓ-1)`, one gets
`b_ℓ ≤ 110 κ^5 (ℓ+5)^{21}` (here `b i` stands for `b_{i+1}`). -/
theorem tree_second_moment (a b : ℕ → ℝ) (κ : ℝ) (hκ : 1 ≤ κ)
    (ha0 : ∀ i, 0 ≤ a i) (ha : ∀ i, a i ≤ κ ^ 2 * ((i : ℝ) + 6) ^ 7) (hb0 : b 0 ≤ 58 * κ ^ 5)
    (hstep : ∀ i : ℕ, b (i + 1) ≤ (1 + 6 / ((i : ℝ) + 1)) * b i + 1 +
      2 * (1 + 6 / ((i : ℝ) + 1)) * a i + (1 + 36 / ((i : ℝ) + 1)) * a i ^ 2) (i : ℕ) :
    b i ≤ 110 * κ ^ 5 * ((i : ℝ) + 6) ^ 21 := by
  set p : ℕ → ℝ := fun i => ∏ j ∈ range i, (1 + 6 / ((j : ℝ) + 1))
  have hk2 : 1 ≤ κ ^ 2 := one_le_pow₀ hκ
  have hk4 : 1 ≤ κ ^ 4 := one_le_pow₀ hκ
  have hk45 : κ ^ 4 ≤ κ ^ 5 := pow_le_pow_right₀ hκ (by norm_num)
  have hnonrec : ∀ i : ℕ, 1 + 2 * (1 + 6 / ((i : ℝ) + 1)) * a i +
      (1 + 36 / ((i : ℝ) + 1)) * a i ^ 2 ≤ 52 * κ ^ 4 * ((i : ℝ) + 6) ^ 14 := by
    intro i
    have hi : (1 : ℝ) ≤ (i : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) i; linarith
    have hμ : 1 + 6 / ((i : ℝ) + 1) ≤ 7 := by
      have : 6 / ((i : ℝ) + 1) ≤ 6 := by rw [div_le_iff₀ (by linarith)]; nlinarith
      linarith
    have hν : 1 + 36 / ((i : ℝ) + 1) ≤ 37 := by
      have : 36 / ((i : ℝ) + 1) ≤ 36 := by rw [div_le_iff₀ (by linarith)]; nlinarith
      linarith
    have hμ0 : 0 ≤ 1 + 6 / ((i : ℝ) + 1) := by positivity
    have hν0 : 0 ≤ 1 + 36 / ((i : ℝ) + 1) := by positivity
    set X := ((i : ℝ) + 6) ^ 7
    have hX : 1 ≤ X := one_le_pow₀ (by linarith)
    have hX2 : ((i : ℝ) + 6) ^ 14 = X ^ 2 := by rw [← pow_mul]
    have hai := ha i
    have hai0 := ha0 i
    have ha2 : a i ^ 2 ≤ κ ^ 4 * X ^ 2 := by
      have := pow_le_pow_left₀ hai0 hai 2
      rw [mul_pow, ← pow_mul] at this; simpa using this
    rw [hX2]
    have t1 : 2 * (1 + 6 / ((i : ℝ) + 1)) * a i ≤ 14 * (κ ^ 2 * X) := by
      have := mul_le_mul hμ hai hai0 (by norm_num); nlinarith
    have t2 : (1 + 36 / ((i : ℝ) + 1)) * a i ^ 2 ≤ 37 * (κ ^ 4 * X ^ 2) :=
      mul_le_mul hν ha2 (sq_nonneg _) (by norm_num)
    have t3 : κ ^ 2 * X ≤ κ ^ 4 * X ^ 2 := by
      have h1 : κ ^ 2 ≤ κ ^ 4 := pow_le_pow_right₀ hκ (by norm_num)
      have h2 : X ≤ X ^ 2 := by nlinarith
      exact mul_le_mul h1 h2 (by linarith) (by positivity)
    have t4 : 1 ≤ κ ^ 4 * X ^ 2 := by nlinarith
    linarith
  have hp : ∀ i : ℕ, b i ≤ p i * (58 * κ ^ 5 + 52 * κ ^ 4 * i * ((i : ℝ) + 6) ^ 14) := by
    intro i
    induction i with
    | zero => simp [p, hb0]
    | succ i ih =>
      have hμ : 0 ≤ 1 + 6 / ((i : ℝ) + 1) := by positivity
      have hp1 : 1 ≤ p (i + 1) := (tree_product_bounds (i + 1)).1
      have hps : p (i + 1) = p i * (1 + 6 / ((i : ℝ) + 1)) := by simp [p, prod_range_succ]
      have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      have hmono : ((i : ℝ) + 6) ^ 14 ≤ (((i + 1 : ℕ) : ℝ) + 6) ^ 14 := by
        push_cast; exact pow_le_pow_left₀ (by linarith) (by linarith) 14
      have hY0 : 0 ≤ 52 * κ ^ 4 * ((i : ℝ) + 6) ^ 14 := by positivity
      calc b (i + 1) ≤ (1 + 6 / ((i : ℝ) + 1)) * b i + 1 +
            2 * (1 + 6 / ((i : ℝ) + 1)) * a i + (1 + 36 / ((i : ℝ) + 1)) * a i ^ 2 := hstep i
        _ ≤ (1 + 6 / ((i : ℝ) + 1)) *
              (p i * (58 * κ ^ 5 + 52 * κ ^ 4 * i * ((i : ℝ) + 6) ^ 14)) +
              52 * κ ^ 4 * ((i : ℝ) + 6) ^ 14 := by
            have := hnonrec i
            have := mul_le_mul_of_nonneg_left ih hμ
            linarith
        _ = p (i + 1) * (58 * κ ^ 5 + 52 * κ ^ 4 * i * ((i : ℝ) + 6) ^ 14) +
              52 * κ ^ 4 * ((i : ℝ) + 6) ^ 14 := by rw [hps]; ring
        _ ≤ p (i + 1) * (58 * κ ^ 5 + 52 * κ ^ 4 * i * ((i : ℝ) + 6) ^ 14) +
              p (i + 1) * (52 * κ ^ 4 * ((i : ℝ) + 6) ^ 14) := by nlinarith
        _ ≤ p (i + 1) * (58 * κ ^ 5 + 52 * κ ^ 4 * ((i + 1 : ℕ) : ℝ) *
              (((i + 1 : ℕ) : ℝ) + 6) ^ 14) := by
            rw [← mul_add]
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            have h4 : 0 ≤ 52 * κ ^ 4 := by positivity
            have := mul_le_mul_of_nonneg_left hmono h4
            have h5 : 0 ≤ 52 * κ ^ 4 * (i : ℝ) := by positivity
            have := mul_le_mul_of_nonneg_left hmono h5
            push_cast at *
            nlinarith
  have h1 := hp i
  have h2 := (tree_product_bounds i).2
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hY : 1 ≤ ((i : ℝ) + 6) := by linarith
  have h15 : 1 ≤ ((i : ℝ) + 6) ^ 15 := one_le_pow₀ hY
  have hbr : 58 * κ ^ 5 + 52 * κ ^ 4 * i * ((i : ℝ) + 6) ^ 14 ≤
      110 * κ ^ 5 * ((i : ℝ) + 6) ^ 15 := by
    have e1 : 58 * κ ^ 5 ≤ 58 * κ ^ 5 * ((i : ℝ) + 6) ^ 15 := by
      have : 0 ≤ 58 * κ ^ 5 := by positivity
      nlinarith
    have e2 : 52 * κ ^ 4 * i * ((i : ℝ) + 6) ^ 14 ≤ 52 * κ ^ 5 * ((i : ℝ) + 6) ^ 15 := by
      rw [pow_succ ((i : ℝ) + 6) 14]
      have h14 : 0 ≤ ((i : ℝ) + 6) ^ 14 := by positivity
      have hi6 : (i : ℝ) ≤ (i : ℝ) + 6 := by linarith
      have := mul_le_mul hk45 hi6 hi (by positivity)
      have := mul_le_mul_of_nonneg_right this h14
      nlinarith
    linarith
  have hpi : 0 ≤ p i := le_trans zero_le_one (tree_product_bounds i).1
  have hbr0 : 0 ≤ 58 * κ ^ 5 + 52 * κ ^ 4 * i * ((i : ℝ) + 6) ^ 14 := by positivity
  calc b i ≤ p i * (58 * κ ^ 5 + 52 * κ ^ 4 * i * ((i : ℝ) + 6) ^ 14) := h1
    _ ≤ ((i : ℝ) + 6) ^ 6 * (110 * κ ^ 5 * ((i : ℝ) + 6) ^ 15) :=
        mul_le_mul h2 hbr hbr0 (by positivity)
    _ = 110 * κ ^ 5 * ((i : ℝ) + 6) ^ 21 := by ring

/-- Paper: `eq:column-growing-diagram` (tanh_column_envelope.tex): for
`J ≤ 24 D^2` neuron roots with second moments at most `110 κ^5 (D+5)^{21}`, the
pointwise bound `(∑ T_j)^2 ≤ J ∑ T_j^2` gives at most
`63360 κ^5 (D+5)^{25} < 2·10^5 κ^5 (D+5)^{25}`. -/
theorem diagram_second_moment (J D : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) (hJ : J ≤ 24 * D ^ 2)
    (T : ℕ → ℝ) (ET2 : ℕ → ℝ) (hT : ∀ j, ET2 j ≤ 110 * κ ^ 5 * ((D : ℝ) + 5) ^ 21) :
    (∑ j ∈ range J, T j) ^ 2 ≤ J * ∑ j ∈ range J, T j ^ 2 ∧
      (J : ℝ) * ∑ j ∈ range J, ET2 j ≤ 63360 * κ ^ 5 * ((D : ℝ) + 5) ^ 25 ∧
      (63360 : ℝ) < 2 * 10 ^ 5 := by
  refine ⟨?_, ?_, by norm_num⟩
  · have := sq_sum_le_card_mul_sum_sq (s := range J) (f := T)
    simpa using this
  · have hJ' : (J : ℝ) ≤ 24 * (D : ℝ) ^ 2 := by exact_mod_cast hJ
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have hsum : ∑ j ∈ range J, ET2 j ≤ J * (110 * κ ^ 5 * ((D : ℝ) + 5) ^ 21) := by
      have := sum_le_sum (fun j (_ : j ∈ range J) => hT j)
      simpa using this
    have hk : 0 ≤ 110 * κ ^ 5 * ((D : ℝ) + 5) ^ 21 := by positivity
    have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    have hD4 : (D : ℝ) ^ 4 ≤ ((D : ℝ) + 5) ^ 4 := pow_le_pow_left₀ hD0 (by linarith) 4
    have hJJ : (J : ℝ) * J ≤ 576 * ((D : ℝ) + 5) ^ 4 := by nlinarith
    calc (J : ℝ) * ∑ j ∈ range J, ET2 j ≤ J * (J * (110 * κ ^ 5 * ((D : ℝ) + 5) ^ 21)) :=
          mul_le_mul_of_nonneg_left hsum hJ0
      _ = (J * J) * (110 * κ ^ 5 * ((D : ℝ) + 5) ^ 21) := by ring
      _ ≤ (576 * ((D : ℝ) + 5) ^ 4) * (110 * κ ^ 5 * ((D : ℝ) + 5) ^ 21) :=
          mul_le_mul_of_nonneg_right hJJ hk
      _ = 63360 * κ ^ 5 * ((D : ℝ) + 5) ^ 25 := by ring

end ExactSampling.ColumnEnvelope
