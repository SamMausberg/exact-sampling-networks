import Mathlib

/-!
# Second-order score witnesses: common Hessian majorants

This module formalizes parts of `critical_score_ceiling.tex`
(`sec:critical-score-ceiling`, `prop:critical-hessian-majorant`,
`prop:critical-matrix-score`) and the claim of `sec:conf-open`
(conference.tex) that grouped matrix-valued second-order score witnesses are
at most `√(6D)`.

All layers are `n × n` (narrower layers are padded with zero rows and columns,
which keeps absolute row sums at most one), and the norm statements hold for
every seminorm `N` on matrices with `N(E_ab) ≤ 1` on the coordinate matrices
`E_ab`; the nuclear norm is one such seminorm, but it is not defined here.

Formalized:
* the radius estimate `r_ℓ^2 ≤ 3/(2ℓ+3)` for `r_ℓ = tanh^[ℓ] 1` and
  `∑_{ℓ=1}^D r_ℓ ≤ √(6D)` (the series argument is repeated from
  `prop:new-local-obstruction`, tanh_new_critical.tex);
* the explicit majorant recursion `P_ℓ = |W_ℓ| P_{ℓ-1}`,
  `C_{ℓ,a} = ∑_j |w_{ℓ,aj}| C_{ℓ-1,j} + 2 r_ℓ v v^T`, the row-sum bound for
  `P_ℓ`, and the entry-sum bound `∑ C ≤ 2 ∑ r_ℓ ≤ 2√(6D)`;
* the chain-rule step and its induction: on the cube `|h_{ℓ,a}| ≤ r_ℓ`, and the
  gradient and Hessian arrays produced by the scalar chain rule are bounded by
  `P_ℓ` and `C_{ℓ,a}` (`gradArr_le`, `hessArr_le`);
* grouping and whitening do not increase the mass, and every seminorm with
  `N(E_ab) ≤ 1` is bounded by the entry sum;
* the triangle-inequality step of `prop:critical-matrix-score` for a finite
  family of transcripts, and the resulting witness ceiling `√(6D)`;
* the one-coordinate chain rule `hasDerivAt_fwd_update` and the coupling bound
  `½ ∑_i |f(x) - f(x^{(i)})| ≤ 1` for the actual network
  (`coupling_witness_fwd`), and the first-score witness bound `cosh^2 1 < 3`.

Not formalized:
* the identification of `hessArr` with the second partial derivatives of the
  network (for `gradArr` the one-coordinate case is `hasDerivAt_fwd_update`),
  and the multilinear-extension and
  finite-difference step for the mixed derivatives of `H`; together they are
  the content of the hypothesis `hH` of `nuclear_bound` and `witness_ceiling`;
* the likelihood calculus for the grouped product experiment in
  `prop:critical-matrix-score` (the formula
  `D^2 H = E[Y(ZZ^T - A)]` and the two stopped isometries); these enter as
  hypotheses of `matrix_score_bound`, together with the values of the
  nuclear norm on the two matrices.
-/

open Real Finset

namespace ExactSampling.CriticalScoreCeiling

/-! ## Radius estimates

The following lemmas repeat the series argument of
`prop:new-local-obstruction` (tanh_new_critical.tex); they supply the radius
estimate `r_ℓ ≤ √(3/(2ℓ+3))` used in `prop:critical-hessian-majorant`. -/

/-- `tanh` is positive on positive reals. Auxiliary for
`prop:critical-hessian-majorant` (critical_score_ceiling.tex). -/
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

/-- `tanh x ≤ x` for `x ≥ 0`. Auxiliary for
`prop:critical-hessian-majorant` (critical_score_ceiling.tex). -/
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

/-- `R_0 = 1`. Auxiliary for
`prop:critical-hessian-majorant` (critical_score_ceiling.tex). -/
theorem R_zero : R 0 = 1 := rfl

/-- `R_{j+1} = tanh R_j`. Auxiliary for
`prop:critical-hessian-majorant` (critical_score_ceiling.tex). -/
theorem R_succ (j : ℕ) : R (j + 1) = Real.tanh (R j) :=
  Function.iterate_succ_apply' _ _ _

/-- The radii are positive. Auxiliary for
`prop:critical-hessian-majorant` (critical_score_ceiling.tex). -/
theorem R_pos (j : ℕ) : 0 < R j := by
  induction j with
  | zero => rw [R_zero]; norm_num
  | succ j ih => rw [R_succ]; exact tanh_pos ih

/-- The radii are at most one. Auxiliary for
`prop:critical-hessian-majorant` (critical_score_ceiling.tex). -/
theorem R_le_one (j : ℕ) : R j ≤ 1 := by
  induction j with
  | zero => rw [R_zero]
  | succ j ih => rw [R_succ]; exact (tanh_le_self (R_pos j).le).trans ih

/-- The radii decrease. Auxiliary for
`prop:critical-hessian-majorant` (critical_score_ceiling.tex). -/
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

/-- Paper: `prop:new-critical-derivatives` (tanh_new_critical.tex), proof: one
step of `∑_{j ≤ ℓ} R_j ≤ √6 √ℓ`. -/
theorem sqrt_step (ℓ : ℕ) {r : ℝ} (hr : r ^ 2 ≤ 3 / (2 * ((ℓ : ℝ) + 1) + 3)) :
    Real.sqrt (6 * ℓ) + r ≤ Real.sqrt (6 * ((ℓ : ℝ) + 1)) := by
  set a := Real.sqrt (6 * ℓ)
  set b := Real.sqrt (6 * ((ℓ : ℝ) + 1))
  have hl : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  have ha2 : a ^ 2 = 6 * ℓ := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = 6 * ((ℓ : ℝ) + 1) := Real.sq_sqrt (by positivity)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have hrb : (r * b) ^ 2 ≤ 9 := by
    rw [mul_pow, hb2]
    rw [le_div_iff₀ (by positivity)] at hr
    nlinarith
  have hrb' : r * b ≤ 3 := by nlinarith
  have hab : a * b ≤ 6 * ℓ + 3 := by nlinarith [sq_nonneg (a - b)]
  have : (a + r) * b ≤ b * b := by nlinarith
  exact le_of_mul_le_mul_right this hb0

/-- Paper: `prop:new-critical-derivatives` (tanh_new_critical.tex), proof:
`∑_{j=1}^{ℓ} R_j ≤ √(6ℓ)`. -/
theorem sum_R_le (ℓ : ℕ) : ∑ j ∈ range ℓ, R (j + 1) ≤ Real.sqrt (6 * ℓ) := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    rw [sum_range_succ]
    have hr := R_sq_le (ℓ + 1)
    push_cast at hr ⊢
    have := sqrt_step ℓ hr
    linarith


/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex):
`∑_{ℓ=1}^D r_ℓ ≤ √(6D)`. -/
theorem sum_radii_le (D : ℕ) : ∑ ℓ ∈ range D, R (ℓ + 1) ≤ Real.sqrt (6 * D) := sum_R_le D

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex): for
`D ≥ 1`, `|H(t)| ≤ r_D ≤ tanh 1`. -/
theorem R_le_tanh_one (D : ℕ) (hD : 1 ≤ D) : R D ≤ Real.tanh 1 := by
  induction D with
  | zero => omega
  | succ D ih =>
    rcases Nat.eq_zero_or_pos D with h | h
    · subst h; rw [R_succ, R_zero]
    · exact (R_succ_le D).trans (ih h)

/-! ## Finite mass identities -/

section FiniteMass
variable {ι : Type*} [Fintype ι]

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex), proof:
`∑_{i,j} v_i v_j = (∑_i v_i)^2`. -/
theorem outer_mass (v : ι → ℝ) : (∑ i, ∑ j, v i * v j) = (∑ i, v i) ^ 2 := by
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex), proof:
a nonnegative row of sum at most one has outer-product mass at most one. -/
theorem outer_mass_le_one (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) (hvs : ∑ i, v i ≤ 1) :
    (∑ i, ∑ j, v i * v j) ≤ 1 := by
  rw [outer_mass]
  have h0 : 0 ≤ ∑ i, v i := Finset.sum_nonneg fun i _ => hv i
  nlinarith

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex), proof:
the entry sum of the new majorant is at most the largest preceding entry sum
plus `2 r_ℓ`. -/
theorem weighted_majorant_step (w b : ι → ℝ) (M r q : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hws : ∑ i, w i ≤ 1) (hb : ∀ i, b i ≤ M)
    (hM : 0 ≤ M) (hr : 0 ≤ r) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∑ i, w i * b i) + 2 * r * q ^ 2 ≤ M + 2 * r := by
  have hsum : (∑ i, w i * b i) ≤ M := by
    calc (∑ i, w i * b i) ≤ ∑ i, w i * M :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hb i) (hw i)
      _ = (∑ i, w i) * M := by rw [Finset.sum_mul]
      _ ≤ M := by nlinarith
  have hq2 : q ^ 2 ≤ 1 := by nlinarith
  have hm : 2 * r * q ^ 2 ≤ 2 * r := by nlinarith
  linarith

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex), proof:
multiplication by diagonal entries in `[0, 1]` cannot increase the mass. -/
theorem whitened_entry_mass_le (C : ι → ι → ℝ) (σ : ι → ℝ)
    (hC : ∀ i j, 0 ≤ C i j) (hσ0 : ∀ i, 0 ≤ σ i) (hσ1 : ∀ i, σ i ≤ 1) :
    (∑ i, ∑ j, σ i * C i j * σ j) ≤ ∑ i, ∑ j, C i j := by
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hi : σ i * C i j ≤ C i j := by
    simpa using mul_le_mul_of_nonneg_right (hσ1 i) (hC i j)
  simpa using mul_le_mul hi (hσ1 j) (hσ0 j) (hC i j)

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex), proof:
summing over pairs of groups does not add mass. -/
theorem grouped_mass {κ : Type*} [Fintype κ] [DecidableEq κ] (g : ι → κ)
    (C : ι → ι → ℝ) :
    ∑ a, ∑ b, ∑ i ∈ univ.filter (fun i => g i = a), ∑ j ∈ univ.filter (fun j => g j = b),
      C i j = ∑ i, ∑ j, C i j := by
  have h1 : ∀ a, ∑ b, ∑ i ∈ univ.filter (fun i => g i = a),
      ∑ j ∈ univ.filter (fun j => g j = b), C i j =
      ∑ i ∈ univ.filter (fun i => g i = a), ∑ j, C i j := by
    intro a
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_fiberwise univ g (C i))
  simp_rw [h1]
  exact Finset.sum_fiberwise univ g (fun i => ∑ j, C i j)

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex), proof:
if `|∂_{ab} H| ≤ ∑_{g(i)=a, g(j)=b} C_{ij}` and the whitening entries lie in
`[0, 1]`, the whitened grouped Hessian has absolute entry sum at most `∑ C`. -/
theorem grouped_whitened_le {κ : Type*} [Fintype κ] [DecidableEq κ] (g : ι → κ)
    (C : ι → ι → ℝ) (Hg : κ → κ → ℝ) (σ : κ → ℝ)
    (hσ0 : ∀ a, 0 ≤ σ a) (hσ1 : ∀ a, σ a ≤ 1)
    (hH : ∀ a b, |Hg a b| ≤ ∑ i ∈ univ.filter (fun i => g i = a),
      ∑ j ∈ univ.filter (fun j => g j = b), C i j) :
    ∑ a, ∑ b, |σ a * Hg a b * σ b| ≤ ∑ i, ∑ j, C i j := by
  rw [← grouped_mass g C]
  apply Finset.sum_le_sum; intro a _
  apply Finset.sum_le_sum; intro b _
  rw [abs_mul, abs_mul, abs_of_nonneg (hσ0 a), abs_of_nonneg (hσ0 b)]
  have h0 : 0 ≤ |Hg a b| := abs_nonneg _
  calc σ a * |Hg a b| * σ b ≤ 1 * |Hg a b| * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right (hσ1 a) h0) (hσ1 b) (hσ0 b)
        positivity
    _ = |Hg a b| := by ring
    _ ≤ _ := hH a b

end FiniteMass

/-! ## Majorant propagation through the network

Width `n`, layer `ℓ ≥ 1` has weight matrix `W ℓ`, with absolute row sums at
most one. `absProd W ℓ = |W_ℓ| ⋯ |W_1|` and `hessMaj W r ℓ a` is the matrix
`C_{ℓ,a}` of the proof of `prop:critical-hessian-majorant`. -/

section Network
variable {n : ℕ}

/-- The products `P_ℓ = |W_ℓ| ⋯ |W_1|`, with `P_0 = I`. Auxiliary for
`prop:critical-hessian-majorant` (critical_score_ceiling.tex). -/
def absProd (W : ℕ → Fin n → Fin n → ℝ) : ℕ → Fin n → Fin n → ℝ
  | 0 => fun a i => if a = i then 1 else 0
  | ℓ + 1 => fun a i => ∑ j, |W (ℓ + 1) a j| * absProd W ℓ j i

/-- The majorants `C_{0,a} = 0` and
`C_{ℓ,a} = ∑_j |w_{ℓ,aj}| C_{ℓ-1,j} + 2 r_ℓ v_{ℓ,a} v_{ℓ,a}^T`, `v_{ℓ,a} = P_ℓ[a,:]`. Auxiliary for
`prop:critical-hessian-majorant` (critical_score_ceiling.tex). -/
def hessMaj (W : ℕ → Fin n → Fin n → ℝ) (r : ℕ → ℝ) : ℕ → Fin n → Fin n → Fin n → ℝ
  | 0 => fun _ _ _ => 0
  | ℓ + 1 => fun a i k => ∑ j, |W (ℓ + 1) a j| * hessMaj W r ℓ j i k +
      2 * r (ℓ + 1) * absProd W (ℓ + 1) a i * absProd W (ℓ + 1) a k

variable (W : ℕ → Fin n → Fin n → ℝ)

/-- Every entry of `P_ℓ` is nonnegative. Auxiliary for
`prop:critical-hessian-majorant` (critical_score_ceiling.tex). -/
theorem absProd_nonneg (ℓ : ℕ) (a i : Fin n) : 0 ≤ absProd W ℓ a i := by
  induction ℓ generalizing a i with
  | zero => simp only [absProd]; split_ifs <;> norm_num
  | succ ℓ ih =>
    simp only [absProd]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (ih j i))

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex), proof:
every row of `P_ℓ` is nonnegative and sums to at most one. -/
theorem absProd_row_sum_le (hW : ∀ ℓ a, ∑ j, |W ℓ a j| ≤ 1) (ℓ : ℕ) (a : Fin n) :
    ∑ i, absProd W ℓ a i ≤ 1 := by
  induction ℓ generalizing a with
  | zero => simp [absProd]
  | succ ℓ ih =>
    simp only [absProd]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc ∑ j, |W (ℓ + 1) a j| * ∑ i, absProd W ℓ j i ≤ ∑ j, |W (ℓ + 1) a j| * 1 :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (ih j) (abs_nonneg _))
      _ ≤ 1 := by simpa using hW (ℓ + 1) a

/-- Every entry of `C_{ℓ,a}` is nonnegative when the radii are nonnegative. Auxiliary for
`prop:critical-hessian-majorant` (critical_score_ceiling.tex). -/
theorem hessMaj_nonneg (r : ℕ → ℝ) (hr : ∀ ℓ, 0 ≤ r ℓ) (ℓ : ℕ) (a i k : Fin n) :
    0 ≤ hessMaj W r ℓ a i k := by
  induction ℓ generalizing a i k with
  | zero => simp [hessMaj]
  | succ ℓ ih =>
    simp only [hessMaj]
    have h1 := absProd_nonneg W (ℓ + 1) a i
    have h2 := absProd_nonneg W (ℓ + 1) a k
    have h3 := hr (ℓ + 1)
    have h4 : 0 ≤ ∑ j, |W (ℓ + 1) a j| * hessMaj W r ℓ j i k :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (ih j i k))
    positivity

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex): the
entry sum of `C_{ℓ,a}` is at most `2 ∑_{m ≤ ℓ} r_m`. -/
theorem hessMaj_mass (hW : ∀ ℓ a, ∑ j, |W ℓ a j| ≤ 1) (r : ℕ → ℝ) (hr : ∀ ℓ, 0 ≤ r ℓ)
    (ℓ : ℕ) (a : Fin n) :
    ∑ i, ∑ k, hessMaj W r ℓ a i k ≤ 2 * ∑ m ∈ range ℓ, r (m + 1) := by
  induction ℓ generalizing a with
  | zero => simp [hessMaj]
  | succ ℓ ih =>
    simp only [hessMaj]
    simp_rw [Finset.sum_add_distrib]
    have hfirst : ∑ i, ∑ k, ∑ j, |W (ℓ + 1) a j| * hessMaj W r ℓ j i k ≤
        2 * ∑ m ∈ range ℓ, r (m + 1) := by
      have e : ∑ i, ∑ k, ∑ j, |W (ℓ + 1) a j| * hessMaj W r ℓ j i k =
          ∑ j, |W (ℓ + 1) a j| * ∑ i, ∑ k, hessMaj W r ℓ j i k := by
        calc ∑ i, ∑ k, ∑ j, |W (ℓ + 1) a j| * hessMaj W r ℓ j i k
            = ∑ i, ∑ j, ∑ k, |W (ℓ + 1) a j| * hessMaj W r ℓ j i k :=
              Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
          _ = ∑ j, ∑ i, ∑ k, |W (ℓ + 1) a j| * hessMaj W r ℓ j i k := Finset.sum_comm
          _ = _ := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [Finset.mul_sum]
      rw [e]
      have hM : 0 ≤ 2 * ∑ m ∈ range ℓ, r (m + 1) := by
        have := Finset.sum_nonneg (fun m (_ : m ∈ range ℓ) => hr (m + 1)); linarith
      calc ∑ j, |W (ℓ + 1) a j| * ∑ i, ∑ k, hessMaj W r ℓ j i k
          ≤ ∑ j, |W (ℓ + 1) a j| * (2 * ∑ m ∈ range ℓ, r (m + 1)) :=
            Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (ih j) (abs_nonneg _))
        _ = (∑ j, |W (ℓ + 1) a j|) * (2 * ∑ m ∈ range ℓ, r (m + 1)) := by
            rw [Finset.sum_mul]
        _ ≤ 1 * (2 * ∑ m ∈ range ℓ, r (m + 1)) :=
            mul_le_mul_of_nonneg_right (hW (ℓ + 1) a) hM
        _ = _ := one_mul _
    have hsecond : ∑ i, ∑ k, 2 * r (ℓ + 1) * absProd W (ℓ + 1) a i * absProd W (ℓ + 1) a k
        ≤ 2 * r (ℓ + 1) := by
      have e : ∑ i, ∑ k, 2 * r (ℓ + 1) * absProd W (ℓ + 1) a i * absProd W (ℓ + 1) a k =
          2 * r (ℓ + 1) * ∑ i, ∑ k, absProd W (ℓ + 1) a i * absProd W (ℓ + 1) a k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring
      rw [e]
      have h1 := outer_mass_le_one (absProd W (ℓ + 1) a) (absProd_nonneg W (ℓ + 1) a)
        (absProd_row_sum_le W hW (ℓ + 1) a)
      have h2 := hr (ℓ + 1)
      nlinarith
    rw [Finset.sum_range_succ]
    linarith

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex): with
`r_ℓ = tanh^[ℓ] 1`, `∑_{i,j} C_{ij} ≤ 2 ∑_{ℓ=1}^D r_ℓ ≤ 2√(6D)`. -/
theorem hessian_majorant_mass (hW : ∀ ℓ a, ∑ j, |W ℓ a j| ≤ 1) (D : ℕ) (a : Fin n) :
    ∑ i, ∑ k, hessMaj W R D a i k ≤ 2 * ∑ ℓ ∈ range D, R (ℓ + 1) ∧
      ∑ i, ∑ k, hessMaj W R D a i k ≤ 2 * Real.sqrt (6 * D) := by
  have h := hessMaj_mass W hW R (fun ℓ => (R_pos ℓ).le) D a
  exact ⟨h, by linarith [sum_radii_le D]⟩

end Network

/-! ## The chain-rule step

For a neuron `h = tanh s` with preactivation `s = ∑_j w_j h_j`, the scalar chain
rule gives `∂_i h = tanh'(s) ∑_j w_j ∂_i h_j` and
`∂_{ik} h = tanh'(s) ∑_j w_j ∂_{ik} h_j + tanh''(s) ∂_i s ∂_k s`. The next two
lemmas show that the majorants propagate through these formulas. -/

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex), proof:
the gradient bound `|∂_i h| ≤ P_ℓ[a,i]` propagates, since `|tanh'| ≤ 1`. -/
theorem gradient_step {m : ℕ} (w : Fin m → ℝ) (G P : Fin m → ℝ) (t₁ : ℝ)
    (ht₁ : |t₁| ≤ 1) (hG : ∀ j, |G j| ≤ P j) :
    |t₁ * ∑ j, w j * G j| ≤ ∑ j, |w j| * P j := by
  rw [abs_mul]
  have h1 : |∑ j, w j * G j| ≤ ∑ j, |w j| * P j := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hG j) (abs_nonneg _)
  have h0 : 0 ≤ ∑ j, |w j| * P j := (abs_nonneg _).trans h1
  nlinarith [abs_nonneg t₁, abs_nonneg (∑ j, w j * G j)]

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex), proof:
since `|tanh'| ≤ 1` and `|tanh'' u| ≤ 2|tanh u| ≤ 2 r_ℓ`, the Hessian bound
`C_{ℓ,a}` propagates through one neuron. -/
theorem hessian_step {m : ℕ} (w : Fin m → ℝ) (H C : Fin m → ℝ) (gi gk vi vk t₁ t₂ r : ℝ)
    (ht₁ : |t₁| ≤ 1) (ht₂ : |t₂| ≤ 2 * r) (hH : ∀ j, |H j| ≤ C j)
    (hgi : |gi| ≤ vi) (hgk : |gk| ≤ vk) :
    |t₁ * ∑ j, w j * H j + t₂ * gi * gk| ≤ ∑ j, |w j| * C j + 2 * r * vi * vk := by
  have h1 := gradient_step w H C t₁ ht₁ hH
  have h2 : |t₂ * gi * gk| ≤ 2 * r * vi * vk := by
    rw [abs_mul, abs_mul]
    have := abs_nonneg t₂
    have := abs_nonneg gi
    have := abs_nonneg gk
    have hvi : 0 ≤ vi := (abs_nonneg _).trans hgi
    calc |t₂| * |gi| * |gk| ≤ (2 * r) * vi * vk := by
          apply mul_le_mul (mul_le_mul ht₂ hgi (by positivity) (by linarith)) hgk
            (by positivity) (by nlinarith)
      _ = 2 * r * vi * vk := by ring
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-! ## The chain-rule arrays of the network

For an input `x ∈ [-1,1]^n`, `fwd W x ℓ a` is the output of neuron `a` at layer
`ℓ`, and `gradArr`, `hessArr` are the arrays produced by the scalar chain rule,
`∂_i h = tanh'(s) ∑_j w_j ∂_i h_j` and
`∂_{ik} h = tanh'(s) ∑_j w_j ∂_{ik} h_j + tanh''(s) ∂_i s ∂_k s`. That `gradArr`
gives the derivative along one coordinate is proved below
(`hasDerivAt_fwd_update`); that `hessArr` gives the second partial derivatives is
not formalized. The bounds below are the inductive step of
`prop:critical-hessian-majorant` applied to these arrays. -/

/-- `tanh' = 1 - tanh^2`. Auxiliary for `prop:critical-hessian-majorant`
(critical_score_ceiling.tex). -/
theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  have heq : Real.tanh = Real.sinh / Real.cosh := by
    funext y; simp [Real.tanh_eq_sinh_div_cosh]
  rw [heq]
  convert h using 1
  simp only [Pi.div_apply]
  field_simp

/-- `tanh'' = -2 tanh + 2 tanh^3`. Auxiliary for `prop:critical-hessian-majorant`
(critical_score_ceiling.tex). -/
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

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex), proof:
`|tanh'| ≤ 1` and `|tanh'' u| ≤ 2 |tanh u|`. -/
theorem tanh_first_second_bounds (u : ℝ) :
    |deriv Real.tanh u| ≤ 1 ∧ |iteratedDeriv 2 Real.tanh u| ≤ 2 * |Real.tanh u| := by
  rw [(hasDerivAt_tanh u).deriv, iteratedDeriv_two_tanh]
  simp only []
  set t := Real.tanh u
  have ht : t ^ 2 < 1 := Real.tanh_sq_lt_one u
  have hs0 : 0 ≤ t ^ 2 := sq_nonneg t
  constructor
  · rw [abs_le]; constructor <;> nlinarith
  · have e : -2 * t + 2 * t ^ 3 = t * (-2 * (1 - t ^ 2)) := by ring
    rw [e, abs_mul, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg t)
    rw [abs_le]; constructor <;> nlinarith

/-- `tanh` is monotone. Auxiliary for `prop:critical-hessian-majorant`
(critical_score_ceiling.tex). -/
theorem tanh_monotone : Monotone Real.tanh := by
  refine monotone_of_deriv_nonneg (fun x => (hasDerivAt_tanh x).differentiableAt)
    (fun x => ?_)
  rw [(hasDerivAt_tanh x).deriv]
  have := Real.tanh_sq_lt_one x
  linarith

/-- `|tanh u| ≤ tanh r` when `|u| ≤ r`. Auxiliary for
`prop:critical-hessian-majorant` (critical_score_ceiling.tex). -/
theorem abs_tanh_le {u r : ℝ} (h : |u| ≤ r) : |Real.tanh u| ≤ Real.tanh r := by
  rcases le_total 0 u with hu | hu
  · have h0 : 0 ≤ Real.tanh u := by
      rcases hu.eq_or_lt with h1 | h1
      · rw [← h1]; simp
      · exact (tanh_pos h1).le
    rw [abs_of_nonneg h0]
    exact tanh_monotone (by rw [abs_of_nonneg hu] at h; exact h)
  · have h0 : Real.tanh u ≤ 0 := by
      have := tanh_monotone hu; rwa [Real.tanh_zero] at this
    rw [abs_of_nonpos h0, ← Real.tanh_neg]
    exact tanh_monotone (by rw [abs_of_nonpos hu] at h; exact h)

section ChainRule
variable {n : ℕ} (W : ℕ → Fin n → Fin n → ℝ) (x : Fin n → ℝ)

/-- Neuron outputs `h_0 = x`, `h_{ℓ+1,a} = tanh(∑_j w_{ℓ+1,aj} h_{ℓ,j})`. -/
noncomputable def fwd : ℕ → Fin n → ℝ
  | 0 => x
  | ℓ + 1 => fun a => Real.tanh (∑ j, W (ℓ + 1) a j * fwd ℓ j)

/-- Gradient array from the scalar chain rule (row `a`, input coordinate `i`). -/
noncomputable def gradArr : ℕ → Fin n → Fin n → ℝ
  | 0 => fun a i => if a = i then 1 else 0
  | ℓ + 1 => fun a i => deriv Real.tanh (∑ j, W (ℓ + 1) a j * fwd W x ℓ j) *
      ∑ j, W (ℓ + 1) a j * gradArr ℓ j i

/-- Hessian array from the scalar chain rule. -/
noncomputable def hessArr : ℕ → Fin n → Fin n → Fin n → ℝ
  | 0 => fun _ _ _ => 0
  | ℓ + 1 => fun a i k =>
      deriv Real.tanh (∑ j, W (ℓ + 1) a j * fwd W x ℓ j) *
          ∑ j, W (ℓ + 1) a j * hessArr ℓ j i k +
        iteratedDeriv 2 Real.tanh (∑ j, W (ℓ + 1) a j * fwd W x ℓ j) *
          (∑ j, W (ℓ + 1) a j * gradArr W x ℓ j i) * (∑ j, W (ℓ + 1) a j * gradArr W x ℓ j k)

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex), proof:
on the cube, `|h_{ℓ,a}| ≤ r_ℓ`. -/
theorem fwd_abs_le (hW : ∀ ℓ a, ∑ j, |W ℓ a j| ≤ 1) (hx : ∀ i, |x i| ≤ 1) (ℓ : ℕ)
    (a : Fin n) : |fwd W x ℓ a| ≤ R ℓ := by
  induction ℓ generalizing a with
  | zero => simpa [fwd, R_zero] using hx a
  | succ ℓ ih =>
    simp only [fwd]
    rw [R_succ]
    apply abs_tanh_le
    calc |∑ j, W (ℓ + 1) a j * fwd W x ℓ j| ≤ ∑ j, |W (ℓ + 1) a j * fwd W x ℓ j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |W (ℓ + 1) a j| * R ℓ := Finset.sum_le_sum (fun j _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (ih j) (abs_nonneg _))
      _ = (∑ j, |W (ℓ + 1) a j|) * R ℓ := by rw [Finset.sum_mul]
      _ ≤ 1 * R ℓ := mul_le_mul_of_nonneg_right (hW (ℓ + 1) a) (R_pos ℓ).le
      _ = R ℓ := one_mul _

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex): the
chain-rule gradient satisfies `|∂_i h_{ℓ,a}| ≤ P_ℓ[a, i]`. -/
theorem gradArr_le (ℓ : ℕ) (a i : Fin n) : |gradArr W x ℓ a i| ≤ absProd W ℓ a i := by
  induction ℓ generalizing a with
  | zero => simp only [gradArr, absProd]; split_ifs <;> simp
  | succ ℓ ih =>
    simp only [gradArr, absProd]
    exact gradient_step (W (ℓ + 1) a) (fun j => gradArr W x ℓ j i) (fun j => absProd W ℓ j i)
      _ (tanh_first_second_bounds _).1 (fun j => ih j)

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex): on the
cube, the chain-rule Hessian satisfies `|∂_{ik} h_{ℓ,a}| ≤ (C_{ℓ,a})_{ik}`, with
the common majorant `C = hessMaj W R`. -/
theorem hessArr_le (hW : ∀ ℓ a, ∑ j, |W ℓ a j| ≤ 1) (hx : ∀ i, |x i| ≤ 1) (ℓ : ℕ)
    (a i k : Fin n) : |hessArr W x ℓ a i k| ≤ hessMaj W R ℓ a i k := by
  induction ℓ generalizing a with
  | zero => simp [hessArr, hessMaj]
  | succ ℓ ih =>
    simp only [hessArr, hessMaj]
    have hgrad : ∀ i, |∑ j, W (ℓ + 1) a j * gradArr W x ℓ j i| ≤ absProd W (ℓ + 1) a i := by
      intro i
      have := gradient_step (W (ℓ + 1) a) (fun j => gradArr W x ℓ j i)
        (fun j => absProd W ℓ j i) 1 (by simp) (fun j => gradArr_le W x ℓ j i)
      simpa [absProd] using this
    have ht2 : |iteratedDeriv 2 Real.tanh (∑ j, W (ℓ + 1) a j * fwd W x ℓ j)| ≤
        2 * R (ℓ + 1) := by
      have h1 := (tanh_first_second_bounds (∑ j, W (ℓ + 1) a j * fwd W x ℓ j)).2
      have h2 := fwd_abs_le W x hW hx (ℓ + 1) a
      simp only [fwd] at h2
      linarith
    exact hessian_step (W (ℓ + 1) a) (fun j => hessArr W x ℓ j i k)
      (fun j => hessMaj W R ℓ j i k) _ _ _ _ _ _ (R (ℓ + 1))
      (tanh_first_second_bounds _).1 ht2 (fun j => ih j) (hgrad i) (hgrad k)

end ChainRule

/-! ## Norms of matrices -/

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex), proof:
a seminorm that is at most one on every coordinate matrix (the nuclear norm,
for instance) is at most the sum of absolute entries. -/
theorem seminorm_le_entry_sum {κ : Type*} [Fintype κ] [DecidableEq κ]
    (N : Seminorm ℝ (Matrix κ κ ℝ)) (hN : ∀ a b, N (Matrix.single a b 1) ≤ 1)
    (M : Matrix κ κ ℝ) : N M ≤ ∑ a, ∑ b, |M a b| := by
  have hsub : ∀ x y : Matrix κ κ ℝ, N (x + y) ≤ N x + N y := fun x y => map_add_le_add N x y
  have hz : N 0 = 0 := map_zero N
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  refine (Finset.le_sum_of_subadditive N hz.le hsub _ _).trans
    (Finset.sum_le_sum (fun a _ => ?_))
  refine (Finset.le_sum_of_subadditive N hz.le hsub _ _).trans
    (Finset.sum_le_sum (fun b _ => ?_))
  have e : Matrix.single a b (M a b) = M a b • Matrix.single a b (1 : ℝ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e, map_smul_eq_mul, Real.norm_eq_abs]
  have := abs_nonneg (M a b)
  nlinarith [hN a b]

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex): for a
seminorm `N` that is at most one on coordinate matrices, the whitened grouped
Hessian obeys `N(Σ D^2 H Σ) ≤ 2 ∑_{ℓ=1}^D r_ℓ ≤ 2√(6D)`. The hypothesis `hH`,
`|∂_{ab} H| ≤ ∑_{g(i)=a, g(j)=b} C_{ij}`, is a stand-in combining two steps of
the proof: the pointwise bound `|∂_{ij} f| ≤ C_{ij}` on the cube (proved here
for the chain-rule arrays in `hessArr_le`, but not identified with the actual
derivatives) and the multilinear-extension and finite-difference argument. -/
theorem nuclear_bound {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (W : ℕ → Fin n → Fin n → ℝ) (hW : ∀ ℓ a, ∑ j, |W ℓ a j| ≤ 1) (D : ℕ) (out : Fin n)
    (g : Fin n → κ) (Hg : κ → κ → ℝ) (σ : κ → ℝ) (hσ0 : ∀ a, 0 ≤ σ a) (hσ1 : ∀ a, σ a ≤ 1)
    (hH : ∀ a b, |Hg a b| ≤ ∑ i ∈ univ.filter (fun i => g i = a),
      ∑ j ∈ univ.filter (fun j => g j = b), hessMaj W R D out i j)
    (N : Seminorm ℝ (Matrix κ κ ℝ)) (hN : ∀ a b, N (Matrix.single a b 1) ≤ 1) :
    N (Matrix.of fun a b => σ a * Hg a b * σ b) ≤ 2 * ∑ ℓ ∈ range D, R (ℓ + 1) ∧
      N (Matrix.of fun a b => σ a * Hg a b * σ b) ≤ 2 * Real.sqrt (6 * D) := by
  have h1 := seminorm_le_entry_sum N hN (Matrix.of fun a b => σ a * Hg a b * σ b)
  simp only [Matrix.of_apply] at h1
  have h2 := grouped_whitened_le g (hessMaj W R D out) Hg σ hσ0 hσ1 hH
  have h3 := hessian_majorant_mass W hW D out
  exact ⟨by linarith [h3.1], by linarith [h3.2]⟩

/-! ## The matrix-valued transcript bound -/

/-- Paper: `prop:critical-matrix-score` (critical_score_ceiling.tex), proof: for
a finite family of transcripts `ω` with probabilities `p ω`, outputs
`|Y ω| ≤ 1`, whitened score matrices `Pm ω = (ΣZ)(ΣZ)^T` and diagonal terms
`Am ω = ΣAΣ`, `N(∑ p Y (Pm - Am)) ≤ ∑ p (N(Pm) + N(Am))`. The hypotheses `hP`,
`hA` (the nuclear norm of `(ΣZ)(ΣZ)^T` is `‖ΣZ‖^2` and that of a nonnegative
diagonal matrix is its trace) and `hQ₁`, `hQ₂` (the two stopped isometries,
both equal to `E_t Q`) are stand-ins for the facts proved in the paper. The
conclusion is `N(∑ p Y (Pm - Am)) ≤ 2 E_t Q`. -/
theorem matrix_score_bound {Ω κ : Type*} [Fintype κ] (s : Finset Ω) (p Y q₁ q₂ : Ω → ℝ)
    (EQ : ℝ) (Pm Am : Ω → Matrix κ κ ℝ) (N : Seminorm ℝ (Matrix κ κ ℝ))
    (hp : ∀ ω ∈ s, 0 ≤ p ω) (hY : ∀ ω ∈ s, |Y ω| ≤ 1)
    (hP : ∀ ω ∈ s, N (Pm ω) = q₁ ω) (hA : ∀ ω ∈ s, N (Am ω) = q₂ ω)
    (hQ₁ : ∑ ω ∈ s, p ω * q₁ ω = EQ) (hQ₂ : ∑ ω ∈ s, p ω * q₂ ω = EQ) :
    N (∑ ω ∈ s, (p ω * Y ω) • (Pm ω - Am ω)) ≤ 2 * EQ := by
  have hsub : ∀ x y : Matrix κ κ ℝ, N (x + y) ≤ N x + N y := fun x y => map_add_le_add N x y
  refine (Finset.le_sum_of_subadditive N (map_zero N).le hsub _ _).trans ?_
  have hterm : ∀ ω ∈ s, N ((p ω * Y ω) • (Pm ω - Am ω)) ≤ p ω * q₁ ω + p ω * q₂ ω := by
    intro ω hω
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp ω hω)]
    have h1 : N (Pm ω - Am ω) ≤ q₁ ω + q₂ ω := by
      rw [← hP ω hω, ← hA ω hω]; exact map_sub_le_add N _ _
    have h2 : 0 ≤ N (Pm ω - Am ω) := apply_nonneg N _
    have h3 := hY ω hω
    have h4 := hp ω hω
    have h5 : |Y ω| * N (Pm ω - Am ω) ≤ q₁ ω + q₂ ω := by nlinarith [abs_nonneg (Y ω)]
    nlinarith [mul_le_mul_of_nonneg_left h5 h4]
  calc ∑ ω ∈ s, N ((p ω * Y ω) • (Pm ω - Am ω)) ≤ ∑ ω ∈ s, (p ω * q₁ ω + p ω * q₂ ω) :=
        Finset.sum_le_sum hterm
    _ = 2 * EQ := by rw [Finset.sum_add_distrib, hQ₁, hQ₂]; ring

/-- Paper: `prop:critical-matrix-score` (critical_score_ceiling.tex) and
`sec:conf-open` (conference.tex): the grouped matrix witness
`½ ‖Σ D^2 H Σ‖_*` is at most `∑_{ℓ=1}^D r_ℓ ≤ √(6D)`, by
`prop:critical-hessian-majorant`. As in `nuclear_bound`, `hH` is a stand-in
for the pointwise bound `|∂_{ij} f| ≤ C_{ij}` (see `hessArr_le`) together with
the multilinear-extension argument. -/
theorem witness_ceiling {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (W : ℕ → Fin n → Fin n → ℝ) (hW : ∀ ℓ a, ∑ j, |W ℓ a j| ≤ 1) (D : ℕ) (out : Fin n)
    (g : Fin n → κ) (Hg : κ → κ → ℝ) (σ : κ → ℝ) (hσ0 : ∀ a, 0 ≤ σ a) (hσ1 : ∀ a, σ a ≤ 1)
    (hH : ∀ a b, |Hg a b| ≤ ∑ i ∈ univ.filter (fun i => g i = a),
      ∑ j ∈ univ.filter (fun j => g j = b), hessMaj W R D out i j)
    (N : Seminorm ℝ (Matrix κ κ ℝ)) (hN : ∀ a b, N (Matrix.single a b 1) ≤ 1) :
    N (Matrix.of fun a b => σ a * Hg a b * σ b) / 2 ≤ ∑ ℓ ∈ range D, R (ℓ + 1) ∧
      N (Matrix.of fun a b => σ a * Hg a b * σ b) / 2 ≤ Real.sqrt (6 * D) := by
  have h := nuclear_bound W hW D out g Hg σ hσ0 hσ1 hH N hN
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-! ## One-coordinate and first-score witnesses -/

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex): if the
restriction `φ_i` of `f` to coordinate `i` (other coordinates fixed) has
derivative bounded by `c_i` on `[-1, 1]`, and `∑ c_i ≤ 1`, then
`½ ∑_i |f(x) - f(x^{(i)})| ≤ 1`. -/
theorem coupling_witness_le {ι : Type*} (s : Finset ι) (φ φ' : ι → ℝ → ℝ) (c : ι → ℝ)
    (hd : ∀ i ∈ s, ∀ y ∈ Set.Icc (-1 : ℝ) 1, HasDerivWithinAt (φ i) (φ' i y) (Set.Icc (-1) 1) y)
    (hb : ∀ i ∈ s, ∀ y ∈ Set.Icc (-1 : ℝ) 1, |φ' i y| ≤ c i) (hc : ∑ i ∈ s, c i ≤ 1) :
    (∑ i ∈ s, |φ i 1 - φ i (-1)|) / 2 ≤ 1 := by
  have hone : ∀ i ∈ s, |φ i 1 - φ i (-1)| ≤ 2 * c i := by
    intro i hi
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := φ i) (a := -1) (b := 1)
      (C := c i) (fun y hy => hd i hi y hy)
      (fun y hy => by rw [Real.norm_eq_abs]; exact hb i hi y (Set.Ico_subset_Icc_self hy))
      1 (by simp)
    rw [Real.norm_eq_abs] at h
    linarith
  have := Finset.sum_le_sum hone
  rw [← Finset.mul_sum] at this
  linarith

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex): the
coupling bound for any family `φ_i` whose derivatives on `[-1,1]` are bounded by
the common gradient majorant `P_D[a, i]` (see `gradArr_le`), whose entries sum to
at most one by `absProd_row_sum_le`. For the actual network see
`coupling_witness_fwd`. -/
theorem coupling_witness_network {n : ℕ} (W : ℕ → Fin n → Fin n → ℝ)
    (hW : ∀ ℓ a, ∑ j, |W ℓ a j| ≤ 1) (D : ℕ) (a : Fin n) (φ φ' : Fin n → ℝ → ℝ)
    (hd : ∀ i, ∀ y ∈ Set.Icc (-1 : ℝ) 1, HasDerivWithinAt (φ i) (φ' i y) (Set.Icc (-1) 1) y)
    (hb : ∀ i, ∀ y ∈ Set.Icc (-1 : ℝ) 1, |φ' i y| ≤ absProd W D a i) :
    (∑ i, |φ i 1 - φ i (-1)|) / 2 ≤ 1 :=
  coupling_witness_le univ φ φ' (absProd W D a) (fun i _ => hd i) (fun i _ => hb i)
    (absProd_row_sum_le W hW D a)

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex): the
one-coordinate chain rule. Along coordinate `i`, the network output
`y ↦ h_{ℓ,a}(x with x_i := y)` has derivative `gradArr` at that point. -/
theorem hasDerivAt_fwd_update {n : ℕ} (W : ℕ → Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (i : Fin n) (ℓ : ℕ) (a : Fin n) (y : ℝ) :
    HasDerivAt (fun t => fwd W (Function.update x i t) ℓ a)
      (gradArr W (Function.update x i y) ℓ a i) y := by
  induction ℓ generalizing a with
  | zero =>
    simp only [fwd, gradArr]
    by_cases h : a = i
    · subst h
      simp only [Function.update_self, ↓reduceIte]
      exact hasDerivAt_id y
    · simp only [Function.update_of_ne h, h, ↓reduceIte]
      exact hasDerivAt_const y (x a)
  | succ ℓ ih =>
    simp only [fwd, gradArr]
    have hsum : HasDerivAt (fun t => ∑ j, W (ℓ + 1) a j * fwd W (Function.update x i t) ℓ j)
        (∑ j, W (ℓ + 1) a j * gradArr W (Function.update x i y) ℓ j i) y :=
      HasDerivAt.fun_sum (fun j _ => (ih j).const_mul (W (ℓ + 1) a j))
    have ht := (hasDerivAt_tanh (∑ j, W (ℓ + 1) a j * fwd W (Function.update x i y) ℓ j)).comp
      y hsum
    rw [(hasDerivAt_tanh _).deriv]
    exact ht

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex): for every
sign input `x ∈ {-1,1}^n`, with `x^{(i)}` the flip of coordinate `i`, the network
output `f = h_{D,a}` satisfies `½ ∑_i |f(x) - f(x^{(i)})| ≤ 1`. The derivative
along each coordinate is the chain-rule array (`hasDerivAt_fwd_update`), bounded
by `P_D[a, i]` (`gradArr_le`), whose entries sum to at most one. -/
theorem coupling_witness_fwd {n : ℕ} (W : ℕ → Fin n → Fin n → ℝ)
    (hW : ∀ ℓ a, ∑ j, |W ℓ a j| ≤ 1) (D : ℕ) (a : Fin n) (x : Fin n → ℝ)
    (hx : ∀ i, x i = 1 ∨ x i = -1) :
    (∑ i, |fwd W x D a - fwd W (Function.update x i (-x i)) D a|) / 2 ≤ 1 := by
  have h := coupling_witness_network W hW D a
    (fun i t => fwd W (Function.update x i t) D a)
    (fun i t => gradArr W (Function.update x i t) D a i)
    (fun i y _ => (hasDerivAt_fwd_update W x i D a y).hasDerivWithinAt)
    (fun i y _ => gradArr_le W _ D a i)
  have e : ∀ i, |fwd W x D a - fwd W (Function.update x i (-x i)) D a| =
      |fwd W (Function.update x i 1) D a - fwd W (Function.update x i (-1)) D a| := by
    intro i
    rcases hx i with h1 | h1
    · have hu : Function.update x i 1 = x := by rw [← h1]; exact Function.update_eq_self i x
      rw [hu, h1]
    · have hu : Function.update x i (-1) = x := by
        rw [← h1]; exact Function.update_eq_self i x
      rw [hu, h1, neg_neg]
      exact abs_sub_comm _ _
  simp_rw [e]
  exact h

/-- `cosh^2 1 < 3`. Auxiliary for
`prop:critical-hessian-majorant` (critical_score_ceiling.tex). -/
theorem cosh_one_sq_lt_three : Real.cosh 1 ^ 2 < 3 := by
  rw [Real.cosh_eq]
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_one_gt_d9
  have h3 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  have h4 : Real.exp (-1) < 3 / 5 := by
    rw [h3, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]; linarith
  have h5 : 0 < Real.exp (-1) := Real.exp_pos _
  nlinarith

/-- `1/(1 - tanh^2 1) = cosh^2 1`. Auxiliary for
`prop:critical-hessian-majorant` (critical_score_ceiling.tex). -/
theorem inv_one_sub_tanh_sq (x : ℝ) : 1 / (1 - Real.tanh x ^ 2) = Real.cosh x ^ 2 := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  rw [Real.tanh_eq_sinh_div_cosh, div_pow]
  have : 1 - Real.sinh x ^ 2 / Real.cosh x ^ 2 = 1 / Real.cosh x ^ 2 := by
    field_simp; nlinarith [Real.cosh_sq x]
  rw [this]; field_simp

/-- Paper: `prop:critical-hessian-majorant` (critical_score_ceiling.tex): the
first-score product witness obeys `‖Σ ∇H‖_2^2 / (1 - H^2) < 3`, from
`‖∇H‖_1 ≤ 1`, whitening entries in `[0, 1]`, and `|H| ≤ tanh 1`. -/
theorem first_score_witness_lt {κ : Type*} (s : Finset κ) (grad σ : κ → ℝ) (H : ℝ)
    (hg : ∑ a ∈ s, |grad a| ≤ 1) (hσ0 : ∀ a, 0 ≤ σ a) (hσ1 : ∀ a, σ a ≤ 1)
    (hH : |H| ≤ Real.tanh 1) :
    (∑ a ∈ s, (σ a * grad a) ^ 2) / (1 - H ^ 2) < 3 := by
  have hsq : ∑ a ∈ s, (σ a * grad a) ^ 2 ≤ 1 := by
    have h1 : ∑ a ∈ s, (σ a * grad a) ^ 2 ≤ ∑ a ∈ s, |grad a| ^ 2 := by
      apply Finset.sum_le_sum; intro a _
      rw [mul_pow, sq_abs]
      have : σ a ^ 2 ≤ 1 := by nlinarith [hσ0 a, hσ1 a]
      nlinarith [sq_nonneg (grad a)]
    have h2 : ∑ a ∈ s, |grad a| ^ 2 ≤ (∑ a ∈ s, |grad a|) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun a _ => abs_nonneg _)
    have h3 : 0 ≤ ∑ a ∈ s, |grad a| := Finset.sum_nonneg (fun a _ => abs_nonneg _)
    nlinarith
  have ht1 : Real.tanh 1 ^ 2 < 1 := Real.tanh_sq_lt_one 1
  have hH2 : H ^ 2 ≤ Real.tanh 1 ^ 2 := by
    rw [← sq_abs H]; exact pow_le_pow_left₀ (abs_nonneg H) hH 2
  have hpos : 0 < 1 - H ^ 2 := by linarith
  have hcosh : 1 / (1 - Real.tanh 1 ^ 2) < 3 := by
    rw [inv_one_sub_tanh_sq]; exact cosh_one_sq_lt_three
  have hmono : 1 / (1 - H ^ 2) ≤ 1 / (1 - Real.tanh 1 ^ 2) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hnn : 0 ≤ ∑ a ∈ s, (σ a * grad a) ^ 2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  calc (∑ a ∈ s, (σ a * grad a) ^ 2) / (1 - H ^ 2) ≤ 1 / (1 - H ^ 2) :=
        div_le_div_of_nonneg_right hsq hpos.le
    _ < 3 := lt_of_le_of_lt hmono hcosh

/-- Paper: `cor:new-integer-score` (tanh_new_critical.tex), proof, in natural
number form: `(2k+1) v ≤ v^2 + k(k+1)` for natural `v, k`. -/
theorem integer_magnitude_parabola (v k : ℕ) :
    (2 * (k : ℝ) + 1) * (v : ℝ) ≤ (v : ℝ) ^ 2 + (k : ℝ) * ((k : ℝ) + 1) := by
  by_cases h : v ≤ k
  · have hreal : (v : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
    have hprod : 0 ≤ ((k : ℝ) - v) * ((k : ℝ) + 1 - v) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · have hnat : k + 1 ≤ v := by omega
    have hreal : (k : ℝ) + 1 ≤ (v : ℝ) := by exact_mod_cast hnat
    have hprod : 0 ≤ ((v : ℝ) - k) * ((v : ℝ) - k - 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

end ExactSampling.CriticalScoreCeiling
