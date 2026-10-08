import Mathlib

/-!
# Checkpoint certificates

This module formalizes the certificate inequalities of `checkpoint_certificates.tex`
(`app:checkpoint`) and the quantities listed in `checkpoint_applicability.tex`
(`sec:checkpoint`), which feed the decoder theorem `thm:momentdecoder`
(`attention_moment_decoder.tex`; `thm:main-decoder` in `main_decoder.tex`).

Formalized here:
* `lem:checkpoint-rms-lipschitz` in full, for `N_ε(h) = h / r_ε(h)` with
  `r_ε(h) = √(ε + ‖h‖²/n)`: `|r_ε(h) - r_ε(h̃)| ≤ ‖h - h̃‖_∞`, `|h̃_i|/r_ε(h̃) ≤ √n`, and
  `‖N_ε(h) - N_ε(h̃)‖_∞ ≤ (1+√n)‖h - h̃‖_∞ / r_ε(h)`, with no floor on `h̃`; the floor
  corollary; `‖N_ε(h)‖₂² ≤ n` and `‖N_ε(h)‖_∞ ≤ R/√λ`;
* `lem:checkpoint-precision`: the stage recursion, the bound
  `e_J ≤ 2^{-P} ∑_i ∏_{j>i} Λ_j ≤ J 2^{-P} ∏_j max{1,Λ_j}`, and the explicit precision
  `P = p + ⌈log₂(J+1)⌉ + ∑_j ⌈log₂ max{1,Λ_j}⌉ + 10`; the attention stage bound `Λ_A`;
* `cor:checkpoint-score-rank`: the score decomposition, cancellation of key-independent terms
  in softmax, the recoded key `S v` with `(u,1)ᵀ S v`, the rank bound
  `rank S ≤ min{rank W_K, rank W_Q + 1}`, and the row-norm bound `d s²`;
* `cor:checkpoint-rectangular` and the chart integer `H`: `‖t‖₁ ≤ 2rβQK`;
* `prop:checkpoint-key-residual`: the residual identity `k - c₀ - Pk = (I-P)W N`, `(c₀)_I = 0`,
  both certificates `η₁` and `η₂`, `‖I - P‖_{∞→∞} ≤ 1 + 2r`, and the stored-key allowance
  `(1+2r)δ`;
* `prop:checkpoint-rotary-span`: a pair rotation and its `t`-fold iterate are multiplication by
  `e^{iω}` and `(e^{iω})^t` in the complex coordinate `x + iy` (nonzero iff the pair is nonzero);
  the Vandermonde determinant
  `det(diag(c) [λ_k^t]) ≠ 0`; and the rank transfer: a real relation `∑_t a_t R^t v = 0`
  (`0 ≤ t < d`), written in the pair coordinates and their conjugates, forces `a = 0`, and the
  same holds for the `d+1` augmented records `(1, R^t v)`, `0 ≤ t ≤ d`;
* `cor:checkpoint-initial-radius`: the telescoping leaf bound `R₀P_J/R_J`, the exact solution
  of the work recurrence, and the uniform bound `(2+L)(1 + log(R_J/R₀))(R_J/R₀)^{m-1}`;
* worksheet arithmetic: the moment degree `m = ⌈8(p + 3H + 7)⌉` and the binomial counts
  `binom(259,3) = 2862209` and `binom(264,8) = 525783425977953 > 5·10^14`.

Not formalized: in `prop:checkpoint-rotary-span`, the passage from linear independence of the
rotated vectors to the dimension statement about the containing space (standard linear algebra);
in `prop:checkpoint-key-residual`, its final cell bound `M_T ≤ min{T, (5 + 64rβ̄Q_max K)^r}` and
the index claim it inherits from `cor:dynamicapproximatespace` (whose allowance split, choice of
`m`, and count are `ExactSampling.DynamicIndex.approximate_space_allowance`,
`exists_pow_two_between`, `approximate_space_cell_count`, and `approximate_space_cell_bound`);
certified evaluation and bit costs; the sign-factory constants `K_N = 1 + 228κ²` (from the
normalization appendix); and the claims about measured checkpoints, which the paper itself treats
as data rather than theorems.
-/

open Finset Matrix
open scoped BigOperators

namespace ExactSampling.CheckpointCertificates

/-! ## Normalization floors (`lem:checkpoint-rms-lipschitz`) -/

section RMS

/-- `r_ε(h) = √(ε + ‖h‖₂²/n)`. -/
noncomputable def rmsDen {n : ℕ} (ε : ℝ) (h : Fin n → ℝ) : ℝ :=
  Real.sqrt (ε + (∑ i, h i ^ 2) / n)

/-- `N_ε(h) = h / r_ε(h)`. -/
noncomputable def rmsNorm {n : ℕ} (ε : ℝ) (h : Fin n → ℝ) (i : Fin n) : ℝ := h i / rmsDen ε h

/-- Auxiliary: a positive stabilizer makes the denominator positive. Supports
`lem:checkpoint-rms-lipschitz` (checkpoint_certificates.tex). -/
lemma rmsDen_pos {n : ℕ} {ε : ℝ} (hε : 0 < ε) (h : Fin n → ℝ) : 0 < rmsDen ε h :=
  Real.sqrt_pos.mpr (by positivity)

/-- Auxiliary: `r_ε(h)² = ε + ‖h‖²/n`. Supports `lem:checkpoint-rms-lipschitz`
(checkpoint_certificates.tex). -/
lemma rmsDen_sq {n : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (h : Fin n → ℝ) :
    rmsDen ε h ^ 2 = ε + (∑ i, h i ^ 2) / n :=
  Real.sq_sqrt (by positivity)

/-- Reverse triangle inequality for the Euclidean norm.
Paper: `lem:checkpoint-rms-lipschitz` (checkpoint_certificates.tex). -/
lemma euclid_reverse {n : ℕ} (h h' : Fin n → ℝ) :
    |Real.sqrt (∑ i, h i ^ 2) - Real.sqrt (∑ i, h' i ^ 2)| ≤
      Real.sqrt (∑ i, (h i - h' i) ^ 2) := by
  have key : ∀ g : Fin n → ℝ,
      ‖(WithLp.toLp 2 g : EuclideanSpace ℝ (Fin n))‖ = Real.sqrt (∑ i, g i ^ 2) := by
    intro g; rw [EuclideanSpace.norm_eq]; simp [Real.norm_eq_abs, sq_abs]
  have := abs_norm_sub_norm_le (WithLp.toLp 2 h : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 h')
  rw [key, key, ← WithLp.toLp_sub, key] at this
  simpa using this

/-- `|√(c + x²) - √(c + y²)| ≤ |x - y|` for `c ≥ 0`: the denominator is the Euclidean norm of
the augmented vector `(√c, x)`. Paper: `lem:checkpoint-rms-lipschitz`
(checkpoint_certificates.tex). -/
lemma sqrt_shift_lipschitz (c x y : ℝ) (hc : 0 ≤ c) :
    |Real.sqrt (c + x ^ 2) - Real.sqrt (c + y ^ 2)| ≤ |x - y| := by
  have h := euclid_reverse ![Real.sqrt c, x] ![Real.sqrt c, y]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.sq_sqrt hc, sub_self] at h
  simpa [Real.sqrt_sq_eq_abs] using h

/-- The denominator is 1-Lipschitz in the maximum coordinate norm:
`|r_ε(h) - r_ε(h̃)| ≤ ‖h - h̃‖₂/√n ≤ ‖h - h̃‖_∞`.
Paper: `lem:checkpoint-rms-lipschitz` (checkpoint_certificates.tex). -/
theorem rmsDen_lipschitz {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 ≤ ε) (h h' : Fin n → ℝ) (δ : ℝ)
    (hδ : ∀ i, |h i - h' i| ≤ δ) : |rmsDen ε h - rmsDen ε h'| ≤ δ := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) (hδ ⟨0, hn⟩)
  set S := ∑ i, h i ^ 2
  set S' := ∑ i, h' i ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hS' : 0 ≤ S' := Finset.sum_nonneg fun i _ => sq_nonneg _
  have e1 : rmsDen ε h = Real.sqrt (ε + Real.sqrt (S / n) ^ 2) := by
    unfold rmsDen; rw [Real.sq_sqrt (by positivity)]
  have e2 : rmsDen ε h' = Real.sqrt (ε + Real.sqrt (S' / n) ^ 2) := by
    unfold rmsDen; rw [Real.sq_sqrt (by positivity)]
  rw [e1, e2]
  refine le_trans (sqrt_shift_lipschitz ε _ _ hε) ?_
  rw [Real.sqrt_div hS, Real.sqrt_div hS', ← sub_div, abs_div,
    abs_of_pos (Real.sqrt_pos.mpr hnr), div_le_iff₀ (Real.sqrt_pos.mpr hnr)]
  have hsum : ∑ i, (h i - h' i) ^ 2 ≤ n * δ ^ 2 := by
    calc ∑ i, (h i - h' i) ^ 2 ≤ ∑ _i : Fin n, δ ^ 2 := by
          apply Finset.sum_le_sum; intro i _
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hδ i) 2
      _ = n * δ ^ 2 := by simp
  calc |Real.sqrt S - Real.sqrt S'| ≤ Real.sqrt (∑ i, (h i - h' i) ^ 2) := euclid_reverse h h'
    _ ≤ Real.sqrt (n * δ ^ 2) := Real.sqrt_le_sqrt hsum
    _ = δ * Real.sqrt n := by
        rw [Real.sqrt_mul hnr.le, Real.sqrt_sq hδ0, mul_comm]

/-- Coordinates of a normalized vector are at most `√n`: `|h_i| ≤ √n r_ε(h)`.
Paper: `lem:checkpoint-rms-lipschitz` (checkpoint_certificates.tex). -/
theorem rms_coord_le {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 ≤ ε) (h : Fin n → ℝ) (i : Fin n) :
    |h i| ≤ Real.sqrt n * rmsDen ε h := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : h i ^ 2 ≤ ∑ j, h j ^ 2 :=
    Finset.single_le_sum (f := fun j => h j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hsq : (Real.sqrt n * rmsDen ε h) ^ 2 = n * ε + ∑ j, h j ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hnr.le, rmsDen_sq hε]; field_simp
  have : h i ^ 2 ≤ (Real.sqrt n * rmsDen ε h) ^ 2 := by rw [hsq]; nlinarith
  rw [← Real.sqrt_sq (abs_nonneg (h i)), ← Real.sqrt_sq (by
    have := Real.sqrt_nonneg (n : ℝ); have := Real.sqrt_nonneg (ε + (∑ j, h j ^ 2) / n)
    unfold rmsDen; positivity : 0 ≤ Real.sqrt n * rmsDen ε h)]
  apply Real.sqrt_le_sqrt
  rw [sq_abs]; exact this

/-- Error control from the exact state's denominator:
`|N_ε(h)_i - N_ε(h̃)_i| ≤ (1+√n) ‖h - h̃‖_∞ / r_ε(h)`, with no floor hypothesis on `h̃`.
Paper: `lem:checkpoint-rms-lipschitz` (checkpoint_certificates.tex). -/
theorem rms_lipschitz {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) (h h' : Fin n → ℝ) (δ : ℝ)
    (hδ : ∀ i, |h i - h' i| ≤ δ) (i : Fin n) :
    |rmsNorm ε h i - rmsNorm ε h' i| ≤ (1 + Real.sqrt n) * δ / rmsDen ε h := by
  have hr := rmsDen_pos hε h
  have hr' := rmsDen_pos hε h'
  have hden := rmsDen_lipschitz hn hε.le h h' δ hδ
  have hcoord := rms_coord_le hn hε.le h' i
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) (hδ i)
  have hid : rmsNorm ε h i - rmsNorm ε h' i =
      (h i - h' i) / rmsDen ε h + (h' i / rmsDen ε h') *
        ((rmsDen ε h' - rmsDen ε h) / rmsDen ε h) := by
    unfold rmsNorm; field_simp; ring
  rw [hid]
  have hq : |h' i / rmsDen ε h'| ≤ Real.sqrt n := by
    rw [abs_div, abs_of_pos hr', div_le_iff₀ hr']; exact hcoord
  calc |(h i - h' i) / rmsDen ε h + h' i / rmsDen ε h' *
        ((rmsDen ε h' - rmsDen ε h) / rmsDen ε h)|
      ≤ |(h i - h' i) / rmsDen ε h| + |h' i / rmsDen ε h'| *
          |(rmsDen ε h' - rmsDen ε h) / rmsDen ε h| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ = |h i - h' i| / rmsDen ε h + |h' i / rmsDen ε h'| *
          (|rmsDen ε h - rmsDen ε h'| / rmsDen ε h) := by
        rw [abs_div (h i - h' i), abs_div (rmsDen ε h' - rmsDen ε h), abs_of_pos hr,
          abs_sub_comm (rmsDen ε h')]
    _ ≤ δ / rmsDen ε h + Real.sqrt n * (δ / rmsDen ε h) := by
        gcongr
        · exact hδ i
    _ = (1 + Real.sqrt n) * δ / rmsDen ε h := by ring

/-- With a floor `λ ≤ r_ε(h)²` certified for the exact state only, the error factor is
`(1+√n)/√λ`. Paper: `lem:checkpoint-rms-lipschitz` (checkpoint_certificates.tex). -/
theorem rms_lipschitz_floor {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) (h h' : Fin n → ℝ)
    (δ lam : ℝ) (hlam : 0 < lam) (hfloor : lam ≤ rmsDen ε h ^ 2)
    (hδ : ∀ i, |h i - h' i| ≤ δ) (i : Fin n) :
    |rmsNorm ε h i - rmsNorm ε h' i| ≤ (1 + Real.sqrt n) * δ / Real.sqrt lam := by
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) (hδ i)
  have hr := rmsDen_pos hε h
  have hroot : Real.sqrt lam ≤ rmsDen ε h := by
    rw [← Real.sqrt_sq hr.le]; exact Real.sqrt_le_sqrt hfloor
  refine le_trans (rms_lipschitz hn hε h h' δ hδ i) ?_
  exact div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hlam) hroot

/-- `‖N_ε(h)‖₂² ≤ n` and, if `|h_i| ≤ R` and `λ ≤ r_ε(h)²`, `|N_ε(h)_i| ≤ R/√λ`.
Paper: the display before `lem:checkpoint-rms-lipschitz` (checkpoint_certificates.tex). -/
theorem rms_bounds {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) (h : Fin n → ℝ) (R lam : ℝ)
    (hlam : 0 < lam) (hfloor : lam ≤ rmsDen ε h ^ 2) (hR : ∀ i, |h i| ≤ R) :
    ∑ i, rmsNorm ε h i ^ 2 ≤ n ∧ ∀ i, |rmsNorm ε h i| ≤ R / Real.sqrt lam := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hr := rmsDen_pos hε h
  constructor
  · unfold rmsNorm
    simp_rw [div_pow]
    rw [← Finset.sum_div, div_le_iff₀ (by positivity), rmsDen_sq hε.le]
    have hS : 0 ≤ ∑ i, h i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have : (n : ℝ) * ((∑ i, h i ^ 2) / n) = ∑ i, h i ^ 2 := by field_simp
    nlinarith
  · intro i
    have hroot : Real.sqrt lam ≤ rmsDen ε h := by
      rw [← Real.sqrt_sq hr.le]; exact Real.sqrt_le_sqrt hfloor
    unfold rmsNorm
    rw [abs_div, abs_of_pos hr]
    have hR0 : 0 ≤ R := le_trans (abs_nonneg _) (hR i)
    calc |h i| / rmsDen ε h ≤ R / rmsDen ε h := by gcongr; exact hR i
      _ ≤ R / Real.sqrt lam := div_le_div_of_nonneg_left hR0 (Real.sqrt_pos.mpr hlam) hroot

/-- Splitting a ratio difference into numerator and denominator errors.
Paper: `lem:checkpoint-rms-lipschitz` (checkpoint_certificates.tex), the exact identity. -/
theorem ratio_difference_split (a b r s : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) :
    a / r - b / s = (a - b) / r + (b / s) * ((s - r) / r) := by
  field_simp
  ring

/-- Scalar form of the normalization error bound.
Paper: `lem:checkpoint-rms-lipschitz` (checkpoint_certificates.tex). -/
theorem normalized_coordinate_error (a b r s δ C : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hab : |a - b| ≤ δ) (hrs : |s - r| ≤ δ) (hb : |b / s| ≤ C) :
    |a / r - b / s| ≤ (1 + C) * δ / r := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) hb
  rw [ratio_difference_split a b r s (ne_of_gt hr) (ne_of_gt hs)]
  calc |(a - b) / r + (b / s) * ((s - r) / r)| ≤ |(a - b) / r| + |(b / s) * ((s - r) / r)| :=
        abs_add_le _ _
    _ = |a - b| / r + |b / s| * (|s - r| / r) := by
        simp only [abs_div, abs_mul, abs_of_pos hr]
    _ ≤ δ / r + C * (δ / r) := by gcongr
    _ = (1 + C) * δ / r := by ring

/-- Scalar form with a squared-denominator floor `λ ≤ r²`.
Paper: `lem:checkpoint-rms-lipschitz` (checkpoint_certificates.tex). -/
theorem normalized_coordinate_squared_floor (a b r s δ C lam : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hlam : 0 < lam) (hfloor : lam ≤ r ^ 2) (hab : |a - b| ≤ δ)
    (hrs : |s - r| ≤ δ) (hb : |b / s| ≤ C) :
    |a / r - b / s| ≤ (1 + C) * δ / Real.sqrt lam := by
  have hrootpos : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam
  have hroot : Real.sqrt lam ≤ r := by
    rw [← Real.sqrt_sq hr.le]; exact Real.sqrt_le_sqrt hfloor
  calc |a / r - b / s| ≤ (1 + C) * δ / r := normalized_coordinate_error a b r s δ C hr hs hab hrs hb
    _ ≤ (1 + C) * δ / Real.sqrt lam := div_le_div_of_nonneg_left (by positivity) hrootpos hroot

end RMS

/-! ## Variable-stage precision (`lem:checkpoint-precision`) -/

section Precision

/-- `∏_{j<k} max{1, L_j}`. -/
def stageAmplification (L : ℕ → ℝ) (k : ℕ) : ℝ := ∏ j ∈ Finset.range k, max 1 (L j)

/-- Auxiliary: the empty amplification product. Supports `lem:checkpoint-precision`
(checkpoint_certificates.tex). -/
theorem stageAmplification_zero (L : ℕ → ℝ) : stageAmplification L 0 = 1 := by
  simp [stageAmplification]

/-- Auxiliary: one more stage multiplies the amplification by `max{1, L_k}`. Supports
`lem:checkpoint-precision` (checkpoint_certificates.tex). -/
theorem stageAmplification_succ (L : ℕ → ℝ) (k : ℕ) :
    stageAmplification L (k + 1) = stageAmplification L k * max 1 (L k) := by
  simp [stageAmplification, Finset.prod_range_succ]

/-- Auxiliary: the amplification product is at least one. Supports `lem:checkpoint-precision`
(checkpoint_certificates.tex). -/
theorem stageAmplification_ge_one (L : ℕ → ℝ) (k : ℕ) : 1 ≤ stageAmplification L k := by
  induction k with
  | zero => simp [stageAmplification]
  | succ k ih =>
    rw [stageAmplification_succ]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ stageAmplification L k * max 1 (L k) :=
        mul_le_mul ih (le_max_left _ _) (by norm_num) (le_trans (by norm_num) ih)

/-- The exact solution `S_J = ∑_i ∏_{i<j<J} Λ_j` of `S_{j+1} = Λ_j S_j + 1`, `S_0 = 0`. -/
def stageSum (L : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => L k * stageSum L k + 1

/-- Each local error is multiplied only by the later stage bounds: `e_J ≤ δ S_J`.
Paper: `lem:checkpoint-precision` (checkpoint_certificates.tex). -/
theorem stage_error_sum (L e : ℕ → ℝ) (δ : ℝ) (hL : ∀ j, 0 ≤ L j) (hzero : e 0 = 0)
    (hstep : ∀ j, e (j + 1) ≤ L j * e j + δ) (k : ℕ) : e k ≤ δ * stageSum L k := by
  induction k with
  | zero => simp [hzero, stageSum]
  | succ k ih =>
    calc e (k + 1) ≤ L k * e k + δ := hstep k
      _ ≤ L k * (δ * stageSum L k) + δ := by gcongr; exact hL k
      _ = δ * stageSum L (k + 1) := by simp only [stageSum]; ring

/-- Auxiliary: `S_J ≥ 0`. Supports `lem:checkpoint-precision` (checkpoint_certificates.tex). -/
lemma stageSum_nonneg (L : ℕ → ℝ) (hL : ∀ j, 0 ≤ L j) (k : ℕ) : 0 ≤ stageSum L k := by
  induction k with
  | zero => simp [stageSum]
  | succ k ih => simp only [stageSum]; nlinarith [hL k]

/-- `S_J ≤ J ∏_j max{1, Λ_j}`. Paper: `lem:checkpoint-precision` (checkpoint_certificates.tex). -/
theorem stageSum_le (L : ℕ → ℝ) (hL : ∀ j, 0 ≤ L j) (k : ℕ) :
    stageSum L k ≤ k * stageAmplification L k := by
  induction k with
  | zero => simp [stageSum]
  | succ k ih =>
    have hA := stageAmplification_ge_one L k
    have hM : 1 ≤ max 1 (L k) := le_max_left _ _
    have hS0 : 0 ≤ stageSum L k := stageSum_nonneg L hL k
    rw [stageAmplification_succ]
    simp only [stageSum]
    push_cast
    have h1 : L k * stageSum L k ≤ max 1 (L k) * (k * stageAmplification L k) :=
      mul_le_mul (le_max_right _ _) ih hS0 (by linarith)
    nlinarith

/-- The product form `e_k ≤ k δ ∏_{j<k} max{1, L_j}`.
Paper: `lem:checkpoint-precision` (checkpoint_certificates.tex). -/
theorem stage_error_recurrence (L e : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hL : ∀ j, 0 ≤ L j)
    (hzero : e 0 = 0) (hstep : ∀ j, e (j + 1) ≤ L j * e j + δ) (k : ℕ) :
    e k ≤ (k : ℝ) * δ * stageAmplification L k := by
  calc e k ≤ δ * stageSum L k := stage_error_sum L e δ hL hzero hstep k
    _ ≤ δ * (k * stageAmplification L k) := by gcongr; exact stageSum_le L hL k
    _ = (k : ℝ) * δ * stageAmplification L k := by ring

/-- A sufficient precision budget. Paper: `lem:checkpoint-precision`
(checkpoint_certificates.tex). -/
theorem precision_budget_suffices (L e : ℕ → ℝ) (δ tolerance : ℝ) (hδ : 0 ≤ δ)
    (hL : ∀ j, 0 ≤ L j) (hzero : e 0 = 0) (hstep : ∀ j, e (j + 1) ≤ L j * e j + δ) (k : ℕ)
    (hbudget : (k : ℝ) * δ * stageAmplification L k ≤ tolerance) : e k ≤ tolerance :=
  le_trans (stage_error_recurrence L e δ hδ hL hzero hstep k) hbudget

/-- The ceiling of the binary logarithm bounds a real factor: `x ≤ 2^{⌈log₂ x⌉}` for `x ≥ 1`
(this is how `⌈log₂ max{1, Λ_j}⌉` enters the precision).
Paper: `lem:checkpoint-precision` (checkpoint_certificates.tex). -/
theorem le_two_pow_ceil_logb (x : ℝ) (hx : 1 ≤ x) : x ≤ 2 ^ ⌈Real.logb 2 x⌉₊ := by
  have hxpos : 0 < x := by linarith
  calc x = (2 : ℝ) ^ (Real.logb 2 x) := (Real.rpow_logb (by norm_num) (by norm_num) hxpos).symm
    _ ≤ (2 : ℝ) ^ ((⌈Real.logb 2 x⌉₊ : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    _ = 2 ^ ⌈Real.logb 2 x⌉₊ := Real.rpow_natCast 2 _

/-- The variable-stage precision certificate: with local errors `2^{-P}` and
`P ≥ p + ⌈log₂(J+1)⌉ + ∑_j ⌈log₂ max{1,Λ_j}⌉ + 10`, the final error is at most
`2^{-p-10} < 2^{-p}`. Paper: `lem:checkpoint-precision` (checkpoint_certificates.tex). -/
theorem precision_guard (L e : ℕ → ℝ) (J p P : ℕ) (hL : ∀ j, 0 ≤ L j) (hzero : e 0 = 0)
    (hstep : ∀ j, e (j + 1) ≤ L j * e j + (2 : ℝ)⁻¹ ^ P)
    (hP : p + Nat.clog 2 (J + 1) + ∑ j ∈ Finset.range J, ⌈Real.logb 2 (max 1 (L j))⌉₊ + 10 ≤ P) :
    e J ≤ (2 : ℝ)⁻¹ ^ (p + 10) ∧ (2 : ℝ)⁻¹ ^ (p + 10) < (2 : ℝ)⁻¹ ^ p := by
  set a : ℕ → ℕ := fun j => ⌈Real.logb 2 (max 1 (L j))⌉₊
  set b := Nat.clog 2 (J + 1)
  have hb : (J : ℝ) + 1 ≤ 2 ^ b := by
    have := Nat.le_pow_clog (by norm_num : 1 < 2) (J + 1); exact_mod_cast this
  have hamp : stageAmplification L J ≤ 2 ^ (∑ j ∈ Finset.range J, a j) := by
    unfold stageAmplification
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod₀ (fun j _ => le_trans zero_le_one (le_max_left _ _))
      (fun j _ => le_two_pow_ceil_logb _ (le_max_left _ _))
  have he := stage_error_recurrence L e ((2 : ℝ)⁻¹ ^ P) (by positivity) hL hzero hstep J
  refine ⟨?_, pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)⟩
  have hP' : (2 : ℝ)⁻¹ ^ P ≤ (2 : ℝ)⁻¹ ^ (p + b + ∑ j ∈ Finset.range J, a j + 10) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hP
  have hA1 := stageAmplification_ge_one L J
  calc e J ≤ (J : ℝ) * (2 : ℝ)⁻¹ ^ P * stageAmplification L J := he
    _ ≤ 2 ^ b * (2 : ℝ)⁻¹ ^ (p + b + ∑ j ∈ Finset.range J, a j + 10) *
          2 ^ (∑ j ∈ Finset.range J, a j) := by
        gcongr; linarith
    _ = (2 : ℝ)⁻¹ ^ (p + 10) := by
        rw [show p + b + ∑ j ∈ Finset.range J, a j + 10 =
          (p + 10) + b + ∑ j ∈ Finset.range J, a j by ring, pow_add, pow_add, inv_pow (2 : ℝ) b,
          inv_pow (2 : ℝ) (∑ j ∈ Finset.range J, a j)]
        field_simp

/-- The attention stage bound
`Λ_A ≤ 1 + α s_O Λ_N [s_V + 2U|β|(K s_Q + Q s_K)]`: it follows from the attention-mean bound
`|F(a,v) - F(a',v')| ≤ ‖v - v'‖ + 2U‖a - a'‖` and the score bound `|β|(K δ_q + Q δ_k)`.
Paper: the paragraph after `lem:checkpoint-precision` (checkpoint_certificates.tex). -/
theorem attention_stage_bound (δ ΛN sQ sK sV sO U K Q β α errRes errN errQ errK errV errA errF
    errOut : ℝ) (hα : 0 ≤ α) (hsO : 0 ≤ sO) (hU : 0 ≤ U) (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hRes : errRes ≤ δ) (hN : errN ≤ ΛN * δ) (hq : errQ ≤ sQ * errN) (hk : errK ≤ sK * errN)
    (hv : errV ≤ sV * errN) (hsQ : 0 ≤ sQ) (hsK : 0 ≤ sK) (hsV : 0 ≤ sV)
    (hA : errA ≤ |β| * (K * errQ + Q * errK)) (hF : errF ≤ errV + 2 * U * errA)
    (hOut : errOut ≤ errRes + α * sO * errF) :
    errOut ≤ (1 + α * sO * ΛN * (sV + 2 * U * |β| * (K * sQ + Q * sK))) * δ := by
  have hβ := abs_nonneg β
  have hαs : 0 ≤ α * sO := mul_nonneg hα hsO
  have h1 : errQ ≤ sQ * (ΛN * δ) := le_trans hq (mul_le_mul_of_nonneg_left hN hsQ)
  have h2 : errK ≤ sK * (ΛN * δ) := le_trans hk (mul_le_mul_of_nonneg_left hN hsK)
  have h3 : errV ≤ sV * (ΛN * δ) := le_trans hv (mul_le_mul_of_nonneg_left hN hsV)
  have h4 : errA ≤ |β| * (K * (sQ * (ΛN * δ)) + Q * (sK * (ΛN * δ))) := by
    refine le_trans hA (mul_le_mul_of_nonneg_left ?_ hβ)
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hK) (mul_le_mul_of_nonneg_left h2 hQ)
  have h5 : errF ≤ sV * (ΛN * δ) + 2 * U * (|β| * (K * (sQ * (ΛN * δ)) + Q * (sK * (ΛN * δ)))) :=
    le_trans hF (add_le_add h3 (mul_le_mul_of_nonneg_left h4 (by positivity)))
  have h6 := le_trans hOut (add_le_add hRes (mul_le_mul_of_nonneg_left h5 hαs))
  calc errOut ≤ δ + α * sO * (sV * (ΛN * δ) + 2 * U * (|β| * (K * (sQ * (ΛN * δ)) +
        Q * (sK * (ΛN * δ))))) := h6
    _ = (1 + α * sO * ΛN * (sV + 2 * U * |β| * (K * sQ + Q * sK))) * δ := by ring

end Precision

/-! ## Effective score rank (`cor:checkpoint-score-rank`) -/

section ScoreRank

variable {n d : ℕ}

/-- The score decomposition: `⟨W_Q u + b_Q, W_K v + b_K⟩` equals the key-dependent part
`uᵀ W_Qᵀ W_K v + b_Qᵀ W_K v` plus `uᵀ W_Qᵀ b_K + b_Qᵀ b_K`, which does not depend on the key
stream `v`. Paper: `cor:checkpoint-score-rank` (checkpoint_certificates.tex). -/
theorem score_decomposition (WQ WK : Matrix (Fin d) (Fin n) ℝ) (bQ bK : Fin d → ℝ)
    (u v : Fin n → ℝ) :
    (WQ *ᵥ u + bQ) ⬝ᵥ (WK *ᵥ v + bK) =
      (u ⬝ᵥ ((WQᵀ * WK) *ᵥ v) + bQ ⬝ᵥ (WK *ᵥ v)) + ((WQ *ᵥ u) ⬝ᵥ bK + bQ ⬝ᵥ bK) := by
  have h : (WQ *ᵥ u) ⬝ᵥ (WK *ᵥ v) = u ⬝ᵥ ((WQᵀ * WK) *ᵥ v) := by
    rw [dotProduct_mulVec, dotProduct_mulVec, ← vecMul_vecMul, vecMul_transpose]
  rw [add_dotProduct, dotProduct_add, dotProduct_add, h]
  ring

/-- Terms common to all keys cancel from softmax.
Paper: `cor:checkpoint-score-rank` (checkpoint_certificates.tex). -/
theorem softmax_shift {ι : Type*} [Fintype ι] (a : ι → ℝ) (c : ℝ) (j : ι) :
    Real.exp (a j + c) / ∑ i, Real.exp (a i + c) = Real.exp (a j) / ∑ i, Real.exp (a i) := by
  simp_rw [Real.exp_add]
  rw [← Finset.sum_mul]
  have : 0 < Real.exp c := Real.exp_pos c
  field_simp

/-- The recoded key map `S = [W_Qᵀ W_K; b_Qᵀ W_K] = [W_Qᵀ; b_Qᵀ] W_K`.
Paper: `cor:checkpoint-score-rank` (checkpoint_certificates.tex). -/
def scoreMatrix (WQ WK : Matrix (Fin d) (Fin n) ℝ) (bQ : Fin d → ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n) ℝ :=
  Matrix.fromRows WQᵀ (Matrix.of fun (_ : Unit) i => bQ i) * WK

/-- The virtual query `(u,1)` and recoded key `S v` reproduce the key-dependent score.
Paper: `cor:checkpoint-score-rank` (checkpoint_certificates.tex). -/
theorem score_recoding (WQ WK : Matrix (Fin d) (Fin n) ℝ) (bQ : Fin d → ℝ) (u v : Fin n → ℝ) :
    Sum.elim u (fun _ => 1) ⬝ᵥ (scoreMatrix WQ WK bQ *ᵥ v) =
      u ⬝ᵥ ((WQᵀ * WK) *ᵥ v) + bQ ⬝ᵥ (WK *ᵥ v) := by
  unfold scoreMatrix
  rw [← Matrix.mulVec_mulVec, Matrix.fromRows_mulVec, Matrix.mulVec_mulVec]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, one_mul,
    Fintype.univ_unit, Finset.sum_singleton]
  congr 1

/-- Auxiliary: stacking rows adds at most the rank of the new rows. Supports the rank bound of
`cor:checkpoint-score-rank` (checkpoint_certificates.tex). -/
lemma rank_fromRows_le {m₁ m₂ k : Type*} [Fintype k] [Fintype m₁] [Fintype m₂]
    (A : Matrix m₁ k ℝ) (B : Matrix m₂ k ℝ) : (Matrix.fromRows A B).rank ≤ A.rank + B.rank := by
  rw [← Matrix.rank_transpose, ← Matrix.rank_transpose A, ← Matrix.rank_transpose B,
    Matrix.transpose_fromRows]
  unfold Matrix.rank
  have hle : LinearMap.range (Matrix.fromCols Aᵀ Bᵀ).mulVecLin ≤
      LinearMap.range Aᵀ.mulVecLin ⊔ LinearMap.range Bᵀ.mulVecLin := by
    rintro x ⟨v, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.fromCols_mulVec]
    exact Submodule.add_mem_sup ⟨v ∘ Sum.inl, rfl⟩ ⟨v ∘ Sum.inr, rfl⟩
  calc Module.finrank ℝ (LinearMap.range (Matrix.fromCols Aᵀ Bᵀ).mulVecLin)
      ≤ Module.finrank ℝ ↥(LinearMap.range Aᵀ.mulVecLin ⊔ LinearMap.range Bᵀ.mulVecLin) :=
        Submodule.finrank_mono hle
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

/-- `r_score = rank S ≤ min{rank W_K, rank W_Q + 1}`.
Paper: `cor:checkpoint-score-rank` (checkpoint_certificates.tex). -/
theorem score_rank_le (WQ WK : Matrix (Fin d) (Fin n) ℝ) (bQ : Fin d → ℝ) :
    (scoreMatrix WQ WK bQ).rank ≤ min WK.rank (WQ.rank + 1) := by
  unfold scoreMatrix
  apply le_min (Matrix.rank_mul_le_right _ _)
  refine le_trans (Matrix.rank_mul_le_left _ _) ?_
  refine le_trans (rank_fromRows_le _ _) ?_
  rw [Matrix.rank_transpose]
  have : (Matrix.of fun (_ : Unit) i => bQ i).rank ≤ 1 :=
    le_trans (Matrix.rank_le_card_height _) (by simp)
  omega

/-- Row norms of the recoded map are at most `d s²` when the rows of `W_Q`, `W_K` have absolute
sums at most `s` and `|b_{Q,i}| ≤ s`.
Paper: `cor:checkpoint-score-rank` (checkpoint_certificates.tex). -/
theorem score_row_norm (WQ WK : Matrix (Fin d) (Fin n) ℝ) (bQ : Fin d → ℝ) (s : ℝ)
    (hQ : ∀ i, ∑ c, |WQ i c| ≤ s) (hK : ∀ i, ∑ b, |WK i b| ≤ s) (hb : ∀ i, |bQ i| ≤ s) :
    (∀ a, ∑ b, |(WQᵀ * WK) a b| ≤ d * s ^ 2) ∧ ∑ b, |∑ i, bQ i * WK i b| ≤ d * s ^ 2 := by
  have hrow : ∀ (x : Fin d → ℝ), (∀ i, |x i| ≤ s) →
      ∑ b, |∑ i, x i * WK i b| ≤ d * s ^ 2 := by
    intro x hx
    calc ∑ b, |∑ i, x i * WK i b| ≤ ∑ b, ∑ i, |x i| * |WK i b| := by
          apply Finset.sum_le_sum; intro b _
          exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp [abs_mul])
      _ = ∑ i, |x i| * ∑ b, |WK i b| := by
          rw [Finset.sum_comm]; simp [Finset.mul_sum]
      _ ≤ ∑ _i : Fin d, s * s := by
          apply Finset.sum_le_sum; intro i _
          have hs : 0 ≤ s := le_trans (abs_nonneg _) (hx i)
          exact mul_le_mul (hx i) (hK i) (Finset.sum_nonneg fun _ _ => abs_nonneg _) hs
      _ = d * s ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  constructor
  · intro a
    have h := hrow (fun i => WQ i a) (fun i => le_trans
      (Finset.single_le_sum (f := fun c => |WQ i c|) (fun c _ => abs_nonneg _)
        (Finset.mem_univ a)) (hQ i))
    simpa [Matrix.mul_apply] using h
  · exact hrow bQ hb

end ScoreRank

/-! ## Chart coefficients (`cor:checkpoint-rectangular`) -/

section Chart

/-- With `|C_{ia}| ≤ 2`, `r_h ≤ r` columns, and `|q_i| ≤ Q_i ≤ Q`, the moment coefficients
`t = (βK/d) qᵀC` satisfy `‖t‖₁ ≤ (|β|K/d) ∑_a ∑_i Q_i |C_{ia}| ≤ 2r|β|QK`; the latter is the
computable integer certificate `H`.
Paper: `cor:checkpoint-rectangular` (checkpoint_certificates.tex), and the choice of `H` in the
same appendix. -/
theorem chart_coefficients {d r : ℕ} (hd : 0 < d) (q Qv : Fin d → ℝ) (C : Fin d → Fin r → ℝ)
    (β K Q : ℝ) (hK : 0 ≤ K) (hq : ∀ i, |q i| ≤ Qv i) (hQ : ∀ i, Qv i ≤ Q)
    (hC : ∀ i a, |C i a| ≤ 2) :
    ∑ a, |β * K / d * ∑ i, q i * C i a| ≤ |β| * K / d * ∑ a, ∑ i, Qv i * |C i a| ∧
      |β| * K / d * ∑ a, ∑ i, Qv i * |C i a| ≤ 2 * r * |β| * Q * K := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hc : 0 ≤ |β| * K / d := by positivity
  have hQv0 : ∀ i, 0 ≤ Qv i := fun i => le_trans (abs_nonneg _) (hq i)
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro a _
    rw [abs_mul, abs_div, abs_mul, abs_of_nonneg hK, Nat.abs_cast]
    gcongr
    calc |∑ i, q i * C i a| ≤ ∑ i, |q i * C i a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, Qv i * |C i a| := by
          apply Finset.sum_le_sum; intro i _
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hq i) (abs_nonneg _)
  · have hsum : ∑ a, ∑ i, Qv i * |C i a| ≤ r * (d * (Q * 2)) := by
      calc ∑ a, ∑ i, Qv i * |C i a| ≤ ∑ _a : Fin r, ∑ _i : Fin d, Q * 2 := by
            apply Finset.sum_le_sum; intro a _
            apply Finset.sum_le_sum; intro i _
            have hQ0 : 0 ≤ Q := le_trans (hQv0 i) (hQ i)
            exact mul_le_mul (hQ i) (hC i a) (abs_nonneg _) hQ0
        _ = r * (d * (Q * 2)) := by simp
    calc |β| * K / d * ∑ a, ∑ i, Qv i * |C i a| ≤ |β| * K / d * (r * (d * (Q * 2))) := by
          gcongr
      _ = 2 * r * |β| * Q * K := by field_simp

end Chart

/-! ## Certified approximate key spaces (`prop:checkpoint-key-residual`) -/

section KeyResidual

variable {d r : ℕ}

/-- The coordinate selector `R_I`. -/
def selector (I : Fin r → Fin d) : Matrix (Fin r) (Fin d) ℝ := fun a i => if I a = i then 1 else 0

/-- The residual map `I - P` with `P = C R_I`. -/
def residualMap (C : Matrix (Fin d) (Fin r) ℝ) (I : Fin r → Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  1 - C * selector I

/-- Auxiliary: `R_I x = x_I`. Supports `prop:checkpoint-key-residual`
(checkpoint_certificates.tex). -/
lemma selector_mulVec (I : Fin r → Fin d) (x : Fin d → ℝ) : selector I *ᵥ x = x ∘ I := by
  ext a
  simp [selector, Matrix.mulVec, dotProduct]

/-- The residual identity: for `k = b_K + W N`, `c₀ = (I - P) b_K`, and `P = C R_I`,
`k - c₀ - P k = (I - P) W N`. Paper: `prop:checkpoint-key-residual`
(checkpoint_certificates.tex). -/
theorem key_residual_identity (C : Matrix (Fin d) (Fin r) ℝ) (I : Fin r → Fin d)
    (bK y : Fin d → ℝ) :
    let P := C * selector I
    (bK + y) - (bK - P *ᵥ bK) - P *ᵥ (bK + y) = y - P *ᵥ y := by
  intro P
  rw [Matrix.mulVec_add]
  abel

/-- With `C_I = I_r`, the offset `c₀ = (I - P) b_K` vanishes on the selected coordinates.
Paper: `prop:checkpoint-key-residual` (checkpoint_certificates.tex). -/
theorem offset_selected_zero (C : Matrix (Fin d) (Fin r) ℝ) (I : Fin r → Fin d)
    (hCI : ∀ a c, C (I a) c = if a = c then 1 else 0) (bK : Fin d → ℝ) (a : Fin r) :
    (bK - (C * selector I) *ᵥ bK) (I a) = 0 := by
  rw [← Matrix.mulVec_mulVec, selector_mulVec]
  simp [Matrix.mulVec, dotProduct, hCI]

/-- Row sums: `‖I - P‖_{∞→∞} ≤ 1 + 2r` for `P = C R_I` with `|C_{ia}| ≤ 2`.
Paper: `prop:checkpoint-key-residual` (checkpoint_certificates.tex), and the remark on stored
key errors. -/
theorem projection_row_sum (C : Matrix (Fin d) (Fin r) ℝ) (I : Fin r → Fin d)
    (hC : ∀ i a, |C i a| ≤ 2) (i : Fin d) :
    ∑ j, |residualMap C I i j| ≤ 1 + 2 * r := by
  have hP : ∀ j, (C * selector I) i j = ∑ a, C i a * (if I a = j then 1 else 0) := by
    intro j; simp [Matrix.mul_apply, selector]
  have hrow : ∑ j, |(C * selector I) i j| ≤ 2 * r := by
    calc ∑ j, |(C * selector I) i j| ≤ ∑ j, ∑ a, |C i a| * (if I a = j then 1 else 0) := by
          apply Finset.sum_le_sum; intro j _
          rw [hP j]
          refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
          refine Finset.sum_congr rfl fun a _ => ?_
          split_ifs <;> simp
      _ = ∑ a, |C i a| := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          simp
      _ ≤ ∑ _a : Fin r, (2 : ℝ) := Finset.sum_le_sum fun a _ => hC i a
      _ = 2 * r := by simp; ring
  calc ∑ j, |residualMap C I i j| ≤
        ∑ j, (|(1 : Matrix (Fin d) (Fin d) ℝ) i j| + |(C * selector I) i j|) := by
        apply Finset.sum_le_sum; intro j _
        rw [residualMap, Matrix.sub_apply]; exact abs_sub _ _
    _ = ∑ j, |(1 : Matrix (Fin d) (Fin d) ℝ) i j| + ∑ j, |(C * selector I) i j| :=
        Finset.sum_add_distrib
    _ ≤ 1 + 2 * r := by
        have : ∑ j, |(1 : Matrix (Fin d) (Fin d) ℝ) i j| = 1 := by
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji; simp [Ne.symm hji]
          · simp
        linarith

/-- The two certificates bound the same residual coordinate `((I-P)W N)_i`:
`η₁ = G ∑_j |M_{ij}|` when `‖N‖_∞ ≤ G`, and `η₂ = √n (∑_j M_{ij}²)^{1/2}` when `‖N‖₂² ≤ n`
(here `M = (I - P)W`). Paper: `prop:checkpoint-key-residual` (checkpoint_certificates.tex). -/
theorem residual_certificates {n : ℕ} (M : Matrix (Fin d) (Fin n) ℝ) (N : Fin n → ℝ) (G : ℝ)
    (hG : ∀ j, |N j| ≤ G) (hN2 : ∑ j, N j ^ 2 ≤ n) (i : Fin d) :
    |(M *ᵥ N) i| ≤ G * ∑ j, |M i j| ∧
      |(M *ᵥ N) i| ≤ Real.sqrt n * Real.sqrt (∑ j, M i j ^ 2) := by
  constructor
  · calc |(M *ᵥ N) i| = |∑ j, M i j * N j| := by simp [Matrix.mulVec, dotProduct]
      _ ≤ ∑ j, |M i j| * |N j| := (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp [abs_mul])
      _ ≤ ∑ j, |M i j| * G := by
          apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_left (hG j) (abs_nonneg _)
      _ = G * ∑ j, |M i j| := by rw [← Finset.sum_mul, mul_comm]
  · have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => M i j) N
    have hv : (M *ᵥ N) i = ∑ j, M i j * N j := by simp [Matrix.mulVec, dotProduct]
    rw [hv, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    have hM : 0 ≤ ∑ j, M i j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    calc (∑ j, M i j * N j) ^ 2 ≤ (∑ j, M i j ^ 2) * ∑ j, N j ^ 2 := hcs
      _ ≤ (∑ j, M i j ^ 2) * n := mul_le_mul_of_nonneg_left hN2 hM
      _ = n * ∑ j, M i j ^ 2 := by ring

/-- A stored key with coordinate error at most `δ` enlarges the residual allowance by at most
`(1 + 2r)δ`: every coordinate of `(I - P)e` is at most `(1+2r)δ` when `‖e‖_∞ ≤ δ`.
Paper: the remark after `prop:checkpoint-key-residual`
(checkpoint_certificates.tex); the bound `‖I - P‖ ≤ 1+2r` in the last paragraph of
`cor:dynamicapproximatespace` (attention_dynamic_index.tex). -/
theorem stored_key_allowance (C : Matrix (Fin d) (Fin r) ℝ) (I : Fin r → Fin d)
    (hC : ∀ i a, |C i a| ≤ 2) (e : Fin d → ℝ) (δ : ℝ) (he : ∀ j, |e j| ≤ δ) (i : Fin d) :
    |(residualMap C I *ᵥ e) i| ≤ (1 + 2 * r) * δ := by
  calc |(residualMap C I *ᵥ e) i| = |∑ j, residualMap C I i j * e j| := by
        simp [Matrix.mulVec, dotProduct]
    _ ≤ ∑ j, |residualMap C I i j| * |e j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp [abs_mul])
    _ ≤ ∑ j, |residualMap C I i j| * δ := by
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_left (he j) (abs_nonneg _)
    _ = (∑ j, |residualMap C I i j|) * δ := by rw [Finset.sum_mul]
    _ ≤ (1 + 2 * r) * δ := by
        have hδ : 0 ≤ δ := le_trans (abs_nonneg _) (he i)
        exact mul_le_mul_of_nonneg_right (projection_row_sum C I hC i) hδ

end KeyResidual

/-! ## A rotational example (`prop:checkpoint-rotary-span`) -/

section Rotary

/-- The Vandermonde step: `det(diag(c) [λ_i^t]) ≠ 0` when the `λ_i` are distinct and every
`c_i` is nonzero. In eigen-coordinates this is the matrix with columns `R^t v`
(`rotary_independent` performs the change of coordinates).
Paper: `prop:checkpoint-rotary-span` (checkpoint_certificates.tex). -/
theorem rotary_vandermonde {d : ℕ} (c lam : Fin d → ℂ) (hc : ∀ i, c i ≠ 0)
    (hlam : Function.Injective lam) :
    (Matrix.diagonal c * Matrix.vandermonde lam).det ≠ 0 := by
  rw [Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hc i)
    (Matrix.det_vandermonde_ne_zero_iff.mpr hlam)

/-- Distinct paired eigenvalues exclude `1`: if `z ≠ z⁻¹` then `z ≠ 1`.
Paper: `prop:checkpoint-rotary-span` (checkpoint_certificates.tex). -/
theorem paired_eigenvalue_ne_one (z : ℂ) (hz : z ≠ z⁻¹) : z ≠ 1 := by
  rintro rfl; simp at hz

/-- Affine version of the Vandermonde step: the Vandermonde matrix of `1, λ_1, …, λ_d` with
nonzero row factors is nonsingular when the `λ_i` are distinct and different from `1`.
Paper: `prop:checkpoint-rotary-span` (checkpoint_certificates.tex). -/
theorem rotary_affine_vandermonde {d : ℕ} (c lam : Fin d → ℂ) (hc : ∀ i, c i ≠ 0)
    (hlam : Function.Injective lam) (hne : ∀ i, lam i ≠ 1) :
    (Matrix.diagonal (Fin.cons 1 c) * Matrix.vandermonde (Fin.cons 1 lam)).det ≠ 0 := by
  apply rotary_vandermonde
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simpa using hc j
  · intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j => simp at hij; exact absurd hij.symm (hne j)
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at hij; exact absurd hij (hne i)
      | succ j => simp at hij; rw [hlam hij]

/-- A pair rotation is complex multiplication: in the coordinate `x + iy`, the rotation through
`ω` multiplies by `e^{iω}` (its `t`-fold iterate is `rotPair_iterate`), and the coordinate is
nonzero iff the pair `(x, y)` is nonzero.
Paper: `prop:checkpoint-rotary-span` (checkpoint_certificates.tex), "diagonalize each
two-dimensional rotation". -/
theorem rotation_as_mul (x y ω : ℝ) :
    (((x * Real.cos ω - y * Real.sin ω : ℝ) : ℂ) +
        ((x * Real.sin ω + y * Real.cos ω : ℝ) : ℂ) * Complex.I =
      Complex.exp (ω * Complex.I) * (x + y * Complex.I)) ∧
      ((x : ℂ) + y * Complex.I ≠ 0 ↔ (x, y) ≠ (0, 0)) := by
  constructor
  · rw [Complex.exp_mul_I]
    push_cast
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring_nf
    rw [Complex.I_sq]
    ring
  · constructor
    · intro h hxy
      apply h
      simp only [Prod.mk.injEq] at hxy
      rw [hxy.1, hxy.2]; simp
    · intro h hz
      apply h
      have h1 := congrArg Complex.re hz
      have h2 := congrArg Complex.im hz
      simp at h1 h2
      rw [h1, h2]

/-- The real rotation of a coordinate pair through `ω`. -/
noncomputable def rotPair (ω : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (v.1 * Real.cos ω - v.2 * Real.sin ω, v.1 * Real.sin ω + v.2 * Real.cos ω)

/-- The `t`-th power of a pair rotation multiplies the complex coordinate `x + iy` by
`(e^{iω})^t`; this is the `t`-fold iterate of `rotation_as_mul`.
Paper: `prop:checkpoint-rotary-span` (checkpoint_certificates.tex). -/
theorem rotPair_iterate (ω : ℝ) (t : ℕ) (v : ℝ × ℝ) :
    (((rotPair ω)^[t] v).1 : ℂ) + (((rotPair ω)^[t] v).2 : ℂ) * Complex.I =
      Complex.exp (ω * Complex.I) ^ t * (v.1 + v.2 * Complex.I) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', pow_succ, mul_comm (Complex.exp (ω * Complex.I) ^ t),
      mul_assoc, ← ih]
    exact (rotation_as_mul _ _ ω).1

/-- Rank transfer for the rotated key images. Let `R` act on `m` coordinate pairs by rotations
through `ω_j`, let the pair coordinates of `v` be `z_j ≠ 0`, and suppose the `2m` numbers
`e^{iω_j}, e^{-iω_j}` are distinct. If real coefficients `a_t`, `0 ≤ t < 2m`, satisfy
`∑_t a_t R^t v = 0`, written in pair coordinates (by `rotPair_iterate`) as
`∑_t a_t (e^{iω_j})^t z_j = 0` for every `j`,
then `a = 0`: the `d = 2m` images `R^t v` are linearly independent.
Paper: `prop:checkpoint-rotary-span` (checkpoint_certificates.tex). -/
theorem rotary_independent {m : ℕ} (ω : Fin m → ℝ) (z : Fin m → ℂ) (hz : ∀ j, z j ≠ 0)
    (hlam : Function.Injective (Fin.append (fun j => Complex.exp (ω j * Complex.I))
      (fun j => Complex.exp (-(ω j) * Complex.I))))
    (a : Fin (m + m) → ℝ)
    (h : ∀ j, ∑ t : Fin (m + m),
      (a t : ℂ) * (Complex.exp (ω j * Complex.I) ^ (t : ℕ) * z j) = 0) :
    a = 0 := by
  set lam : Fin (m + m) → ℂ := Fin.append (fun j => Complex.exp (ω j * Complex.I))
      (fun j => Complex.exp (-(ω j) * Complex.I)) with hlamdef
  set c : Fin (m + m) → ℂ := Fin.append z (fun j => (starRingEnd ℂ) (z j)) with hcdef
  have hdet : (Matrix.diagonal c * Matrix.vandermonde lam).det ≠ 0 := by
    refine rotary_vandermonde c lam (fun k => ?_) hlam
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · show c (Fin.castAdd m j) ≠ 0
      rw [hcdef, Fin.append_left]; exact hz j
    · show c (Fin.natAdd m j) ≠ 0
      rw [hcdef, Fin.append_right]; simpa using hz j
  have hmul : (Matrix.diagonal c * Matrix.vandermonde lam).mulVec (fun t => (a t : ℂ)) = 0 := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_mul, Matrix.vandermonde_apply,
      Pi.zero_apply]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp only [hcdef, hlamdef, Fin.append_left]
      rw [← h j]
      refine Finset.sum_congr rfl fun t _ => ?_
      ring
    · simp only [hcdef, hlamdef, Fin.append_right]
      have hc := congrArg (starRingEnd ℂ) (h j)
      rw [map_zero, map_sum] at hc
      rw [← hc]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [map_mul, map_pow, Complex.conj_ofReal]
      rw [← Complex.exp_conj]
      simp [Complex.conj_ofReal]
      ring
  have := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  funext t
  have ht := congrFun this t
  simpa using ht

/-- Rank transfer for the `d + 1` actual records `R^t v`, `0 ≤ t ≤ d = 2m`, augmented by a
coordinate one: if `∑_t a_t = 0` and `∑_t a_t (e^{iω_j})^t z_j = 0` for every `j`, then `a = 0`;
so the records have affine dimension `d`. Distinct paired eigenvalues exclude `1`.
Paper: `prop:checkpoint-rotary-span` (checkpoint_certificates.tex). -/
theorem rotary_affine_independent {m : ℕ} (ω : Fin m → ℝ) (z : Fin m → ℂ) (hz : ∀ j, z j ≠ 0)
    (hlam : Function.Injective (Fin.append (fun j => Complex.exp (ω j * Complex.I))
      (fun j => Complex.exp (-(ω j) * Complex.I))))
    (a : Fin (m + m + 1) → ℝ) (h0 : ∑ t, a t = 0)
    (h : ∀ j, ∑ t : Fin (m + m + 1),
      (a t : ℂ) * (Complex.exp (ω j * Complex.I) ^ (t : ℕ) * z j) = 0) :
    a = 0 := by
  set lam : Fin (m + m) → ℂ := Fin.append (fun j => Complex.exp (ω j * Complex.I))
      (fun j => Complex.exp (-(ω j) * Complex.I)) with hlamdef
  set c : Fin (m + m) → ℂ := Fin.append z (fun j => (starRingEnd ℂ) (z j)) with hcdef
  have hne : ∀ k, lam k ≠ 1 := by
    intro k hk
    refine Fin.addCases (fun j hj => ?_) (fun j hj => ?_) k hk
    · have e1 : lam (Fin.castAdd m j) = lam (Fin.natAdd m j) := by
        rw [hj]; rw [hlamdef, Fin.append_right]
        rw [hlamdef, Fin.append_left] at hj
        have : Complex.exp (-(ω j) * Complex.I) = (Complex.exp (ω j * Complex.I))⁻¹ := by
          rw [← Complex.exp_neg]; ring_nf
        rw [this, hj, inv_one]
      have := hlam e1
      exact absurd this (by simp [Fin.ext_iff]; omega)
    · have e1 : lam (Fin.castAdd m j) = lam (Fin.natAdd m j) := by
        rw [hj]; rw [hlamdef, Fin.append_left]
        rw [hlamdef, Fin.append_right] at hj
        have : Complex.exp (ω j * Complex.I) = (Complex.exp (-(ω j) * Complex.I))⁻¹ := by
          rw [← Complex.exp_neg]; ring_nf
        rw [this, hj, inv_one]
      have := hlam e1
      exact absurd this (by simp [Fin.ext_iff]; omega)
  have hdet := rotary_affine_vandermonde c lam (fun k => ?_) hlam hne
  · have hmul : (Matrix.diagonal (Fin.cons 1 c) * Matrix.vandermonde (Fin.cons 1 lam)).mulVec
        (fun t => (a t : ℂ)) = 0 := by
      funext k
      simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_mul, Matrix.vandermonde_apply,
        Pi.zero_apply]
      refine Fin.cases ?_ (fun k' => ?_) k
      · simp only [Fin.cons_zero, one_pow, one_mul, mul_one]
        exact_mod_cast h0
      · simp only [Fin.cons_succ]
        refine Fin.addCases (fun j => ?_) (fun j => ?_) k'
        · simp only [hcdef, hlamdef, Fin.append_left]
          rw [← h j]
          refine Finset.sum_congr rfl fun t _ => ?_
          ring
        · simp only [hcdef, hlamdef, Fin.append_right]
          have hc := congrArg (starRingEnd ℂ) (h j)
          rw [map_zero, map_sum] at hc
          rw [← hc]
          refine Finset.sum_congr rfl fun t _ => ?_
          simp only [map_mul, map_pow, Complex.conj_ofReal]
          rw [← Complex.exp_conj]
          simp [Complex.conj_ofReal]
          ring
    have := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
    funext t
    have ht := congrFun this t
    simpa using ht
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · show c (Fin.castAdd m j) ≠ 0
      rw [hcdef, Fin.append_left]; exact hz j
    · show c (Fin.natAdd m j) ≠ 0
      rw [hcdef, Fin.append_right]; simpa using hz j

end Rotary

/-! ## An arbitrary initial residual radius (`cor:checkpoint-initial-radius`) -/

section InitialRadius

/-- `P_j = ∏_{k ≤ j} (1 + u_k m_k / R_{k-1})` (indices shifted to start at zero). -/
noncomputable def radiusProduct (R u m : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∏ k ∈ Finset.range j, (1 + u (k + 1) * m (k + 1) / R k)

/-- Auxiliary: one more factor of `P_j`. Supports `cor:checkpoint-initial-radius`
(checkpoint_certificates.tex). -/
lemma radiusProduct_succ (R u m : ℕ → ℝ) (j : ℕ) :
    radiusProduct R u m (j + 1) = radiusProduct R u m j * (1 + u (j + 1) * m (j + 1) / R j) := by
  simp [radiusProduct, Finset.prod_range_succ]

/-- Auxiliary: `P_j > 0`. Supports `cor:checkpoint-initial-radius`
(checkpoint_certificates.tex). -/
lemma radiusProduct_pos (R u m : ℕ → ℝ) (hR : ∀ j, 0 < R j) (hu : ∀ j, 0 ≤ u j)
    (hm : ∀ j, 0 ≤ m j) (j : ℕ) : 0 < radiusProduct R u m j := by
  unfold radiusProduct
  exact Finset.prod_pos fun k _ => by have := hR k; have := hu (k + 1); have := hm (k + 1)
                                      positivity

/-- The leaf count telescopes: if `C_0 ≤ 1` and `C_j ≤ ((R_{j-1} + u_j m_j)/R_j) C_{j-1}`,
then `C_J ≤ R₀ P_J / R_J`. Paper: `cor:checkpoint-initial-radius`
(checkpoint_certificates.tex), `Q_leaves ≤ R₀P_J/R_J`. -/
theorem leaf_bound (R u m Cl : ℕ → ℝ) (hR : ∀ j, 0 < R j) (hu : ∀ j, 0 ≤ u j)
    (hm : ∀ j, 0 ≤ m j) (hC0 : Cl 0 ≤ 1)
    (hC : ∀ j, Cl (j + 1) ≤ (R j + u (j + 1) * m (j + 1)) / R (j + 1) * Cl j) (J : ℕ) :
    Cl J ≤ R 0 * radiusProduct R u m J / R J := by
  induction J with
  | zero => simp [radiusProduct]; rw [div_self (hR 0).ne']; exact hC0
  | succ J ih =>
    have hfac : 0 ≤ (R J + u (J + 1) * m (J + 1)) / R (J + 1) := by
      have := hR J; have := hR (J + 1); have := hu (J + 1); have := hm (J + 1); positivity
    calc Cl (J + 1) ≤ (R J + u (J + 1) * m (J + 1)) / R (J + 1) * Cl J := hC J
      _ ≤ (R J + u (J + 1) * m (J + 1)) / R (J + 1) * (R 0 * radiusProduct R u m J / R J) := by
          gcongr
      _ = R 0 * radiusProduct R u m (J + 1) / R (J + 1) := by
          rw [radiusProduct_succ]
          have := (hR J).ne'
          field_simp

/-- The work majorant: if `W_0 = 2R₀c` and `W_j = (1 + u_j m_j/R_{j-1}) W_{j-1} + c u_j(1+L_j)`,
then `W_J = P_J (2R₀c + ∑_{j ≤ J} c u_j(1+L_j)/P_j)`; consequently a work bound `T_J` with
`R_J T_J ≤ W_J` obeys `T_J ≤ c (P_J/R_J)(2R₀ + ∑_j u_j(1+L_j)/P_j)`.
Paper: `cor:checkpoint-initial-radius` (checkpoint_certificates.tex). -/
theorem work_majorant (R u m Lw W : ℕ → ℝ) (c : ℝ) (hR : ∀ j, 0 < R j) (hu : ∀ j, 0 ≤ u j)
    (hm : ∀ j, 0 ≤ m j) (hW0 : W 0 = 2 * R 0 * c)
    (hW : ∀ j, W (j + 1) =
      (1 + u (j + 1) * m (j + 1) / R j) * W j + c * u (j + 1) * (1 + Lw (j + 1)))
    (J : ℕ) :
    W J = radiusProduct R u m J * (2 * R 0 * c + ∑ j ∈ Finset.range J,
      c * u (j + 1) * (1 + Lw (j + 1)) / radiusProduct R u m (j + 1)) := by
  induction J with
  | zero => simp [radiusProduct, hW0]
  | succ J ih =>
    rw [hW J, ih, Finset.sum_range_succ, radiusProduct_succ]
    have hP := radiusProduct_pos R u m hR hu hm J
    have hf : 0 < 1 + u (J + 1) * m (J + 1) / R J := by
      have := hR J; have := hu (J + 1); have := hm (J + 1); positivity
    field_simp
    ring

/-- Uniform consequences, with every source budget replaced by `m ≥ 1` and every local factor
by `L ≥ 0` (the uniform majorant `P̂_j = ∏_{k ≤ j}(1 + m u_k/R_{k-1})`): `P̂_J ≤ (R_J/R₀)^m`,
`P̂_j ≥ R_j/R₀`, `∑_j u_j/P̂_j ≤ R₀ log(R_J/R₀)`, and hence
`(P̂_J/R_J)(2R₀ + ∑_j u_j(1+L)/P̂_j) ≤ (2+L)(1 + log(R_J/R₀))(R_J/R₀)^{m-1}`.
Paper: `cor:checkpoint-initial-radius` (checkpoint_certificates.tex), the uniform bound after the
corollary. -/
theorem uniform_radius_bound (R u : ℕ → ℝ) (m L : ℝ) (hR : ∀ j, 0 < R j) (hu : ∀ j, 0 ≤ u j)
    (hm : 1 ≤ m) (hL : 0 ≤ L) (hRstep : ∀ j, R (j + 1) = R j + u (j + 1)) (J : ℕ) :
    radiusProduct R u (fun _ => m) J ≤ (R J / R 0) ^ m ∧
      (∀ j, R j / R 0 ≤ radiusProduct R u (fun _ => m) j) ∧
      ∑ j ∈ Finset.range J, u (j + 1) / radiusProduct R u (fun _ => m) (j + 1) ≤
        R 0 * Real.log (R J / R 0) ∧
      radiusProduct R u (fun _ => m) J / R J * (2 * R 0 + ∑ j ∈ Finset.range J,
        u (j + 1) * (1 + L) / radiusProduct R u (fun _ => m) (j + 1)) ≤
        (2 + L) * (1 + Real.log (R J / R 0)) * (R J / R 0) ^ (m - 1) := by
  set P := radiusProduct R u (fun _ => m) with hPdef
  have hR0 := hR 0
  have hm0 : ∀ j : ℕ, 0 ≤ (fun _ => m) j := fun _ => by simp only; linarith
  have hPpos : ∀ j, 0 < P j := radiusProduct_pos R u (fun _ => m) hR hu hm0
  have hratio : ∀ j, R (j + 1) / R j = 1 + u (j + 1) / R j := by
    intro j; rw [hRstep j]; have := (hR j).ne'; field_simp
  have hmono : ∀ j, R 0 ≤ R j := by
    intro j
    induction j with
    | zero => exact le_rfl
    | succ j ih => rw [hRstep j]; linarith [hu (j + 1)]
  -- upper bound on the product
  have hPup : ∀ J, P J ≤ (R J / R 0) ^ m := by
    intro J
    induction J with
    | zero => simp [hPdef, radiusProduct, div_self hR0.ne']
    | succ J ih =>
      rw [hPdef, radiusProduct_succ, ← hPdef]
      have hx : 0 ≤ u (J + 1) / R J := div_nonneg (hu _) (hR J).le
      have hbern : 1 + m * (u (J + 1) / R J) ≤ (1 + u (J + 1) / R J) ^ m :=
        one_add_mul_self_le_rpow_one_add (by linarith) hm
      have h1 : 1 + u (J + 1) * m / R J = 1 + m * (u (J + 1) / R J) := by ring
      calc P J * (1 + u (J + 1) * m / R J) ≤ (R J / R 0) ^ m * (1 + u (J + 1) / R J) ^ m := by
            rw [h1]
            exact mul_le_mul ih hbern (add_nonneg zero_le_one (mul_nonneg (by linarith) hx))
              (Real.rpow_nonneg (div_nonneg (hR J).le hR0.le) _)
        _ = (R (J + 1) / R 0) ^ m := by
            rw [← Real.mul_rpow (by have := hR J; positivity) (by positivity), ← hratio J]
            congr 1; have := (hR J).ne'; field_simp
  -- lower bound on the product
  have hPlo : ∀ j, R j / R 0 ≤ P j := by
    intro j
    induction j with
    | zero => simp [hPdef, radiusProduct, div_self hR0.ne']
    | succ j ih =>
      rw [hPdef, radiusProduct_succ, ← hPdef]
      have hx : 0 ≤ u (j + 1) / R j := div_nonneg (hu _) (hR j).le
      have h1 : 1 + u (j + 1) / R j ≤ 1 + u (j + 1) * m / R j := by
        have : u (j + 1) * m / R j = m * (u (j + 1) / R j) := by ring
        rw [this]; nlinarith
      calc R (j + 1) / R 0 = R j / R 0 * (1 + u (j + 1) / R j) := by
            rw [← hratio j]; have := (hR j).ne'; field_simp
        _ ≤ P j * (1 + u (j + 1) * m / R j) :=
            mul_le_mul ih h1 (by positivity) (le_of_lt (hPpos j))
  -- the logarithmic sum
  have hlogstep : ∀ j, u (j + 1) / R (j + 1) ≤ Real.log (R (j + 1)) - Real.log (R j) := by
    intro j
    have hx : 0 < R (j + 1) / R j := div_pos (hR _) (hR _)
    have h := Real.one_sub_inv_le_log_of_pos hx
    rw [Real.log_div (hR _).ne' (hR _).ne', inv_div] at h
    have : u (j + 1) / R (j + 1) = 1 - R j / R (j + 1) := by
      rw [hRstep j]; have := (hR (j + 1)).ne'; rw [← hRstep j]; field_simp; rw [hRstep j]; ring
    linarith
  have hsumlog : ∑ j ∈ Finset.range J, u (j + 1) / P (j + 1) ≤ R 0 * Real.log (R J / R 0) := by
    calc ∑ j ∈ Finset.range J, u (j + 1) / P (j + 1)
        ≤ ∑ j ∈ Finset.range J, R 0 * (u (j + 1) / R (j + 1)) := by
          apply Finset.sum_le_sum; intro j _
          have hlo := hPlo (j + 1)
          have hP := hPpos (j + 1)
          rw [div_le_iff₀ hP]
          have : R 0 * (u (j + 1) / R (j + 1)) * P (j + 1) ≥
              R 0 * (u (j + 1) / R (j + 1)) * (R (j + 1) / R 0) := by
            apply mul_le_mul_of_nonneg_left hlo
            exact mul_nonneg hR0.le (div_nonneg (hu _) (hR _).le)
          have heq : R 0 * (u (j + 1) / R (j + 1)) * (R (j + 1) / R 0) = u (j + 1) := by
            have := (hR (j + 1)).ne'; field_simp
          linarith
      _ ≤ ∑ j ∈ Finset.range J, R 0 * (Real.log (R (j + 1)) - Real.log (R j)) := by
          apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_left (hlogstep j) hR0.le
      _ = R 0 * Real.log (R J / R 0) := by
          rw [← Finset.mul_sum, Finset.sum_range_sub (fun j => Real.log (R j)),
            Real.log_div (hR J).ne' hR0.ne']
  refine ⟨hPup J, hPlo, hsumlog, ?_⟩
  -- the final bound
  set ℓ := Real.log (R J / R 0) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by rw [le_div_iff₀ hR0, one_mul]; exact hmono J)
  have hsum' : ∑ j ∈ Finset.range J, u (j + 1) * (1 + L) / P (j + 1) =
      (1 + L) * ∑ j ∈ Finset.range J, u (j + 1) / P (j + 1) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  rw [hsum']
  have hRJ := hR J
  have hx : 0 < R J / R 0 := div_pos hRJ hR0
  have hpow : (R J / R 0) ^ m / R J * R 0 = (R J / R 0) ^ (m - 1) := by
    rw [Real.rpow_sub_one hx.ne']; field_simp
  have hinner : 2 * R 0 + (1 + L) * ∑ j ∈ Finset.range J, u (j + 1) / P (j + 1) ≤
      R 0 * (2 + (1 + L) * ℓ) := by
    have := mul_le_mul_of_nonneg_left hsumlog (show 0 ≤ 1 + L by linarith); nlinarith
  have hinner0 : 0 ≤ 2 * R 0 + (1 + L) * ∑ j ∈ Finset.range J, u (j + 1) / P (j + 1) := by
    have : 0 ≤ ∑ j ∈ Finset.range J, u (j + 1) / P (j + 1) :=
      Finset.sum_nonneg fun j _ => div_nonneg (hu _) (hPpos _).le
    nlinarith
  calc P J / R J * (2 * R 0 + (1 + L) * ∑ j ∈ Finset.range J, u (j + 1) / P (j + 1))
      ≤ (R J / R 0) ^ m / R J * (R 0 * (2 + (1 + L) * ℓ)) := by
        apply mul_le_mul (div_le_div_of_nonneg_right (hPup J) hRJ.le) hinner hinner0
        positivity
    _ = (R J / R 0) ^ (m - 1) * (2 + (1 + L) * ℓ) := by rw [← hpow]; ring
    _ ≤ (R J / R 0) ^ (m - 1) * ((2 + L) * (1 + ℓ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
    _ = (2 + L) * (1 + ℓ) * (R J / R 0) ^ (m - 1) := by ring

end InitialRadius

/-! ## Worksheet arithmetic -/

section Worksheet

/-- The worksheet degree `m = ⌈8(p + 3H + 7)⌉` is the degree `⌈8(H + q + 1)⌉` of
`lem:finitemomentindex` with `q = p + 2H + 6`.
Paper: `checkpoint_certificates.tex` (`app:checkpoint`), "Construction sizes and a numerical
worksheet"; `lem:finitemomentindex` (attention_moment_decoder.tex). -/
theorem worksheet_degree (p H : ℝ) : 8 * (H + (p + 2 * H + 6) + 1) = 8 * (p + 3 * H + 7) := by
  ring

/-- Illustrative feature counts at degree `m = 256`: `binom(259,3) = 2862209` (rank three) and
`binom(264,8) > 5·10^14` (rank eight).
Paper: `sec:checkpoint` (checkpoint_applicability.tex). -/
theorem worksheet_counts : Nat.choose 259 3 = 2862209 ∧ 5 * 10 ^ 14 < Nat.choose 264 8 := by
  constructor
  · rw [Nat.choose_eq_descFactorial_div_factorial]; norm_num [Nat.descFactorial, Nat.factorial]
  · rw [Nat.choose_eq_descFactorial_div_factorial]; norm_num [Nat.descFactorial, Nat.factorial]

/-- The exact count at rank eight: `binom(264, 8) = 525783425977953`.
Paper: `sec:checkpoint` (checkpoint_applicability.tex). -/
theorem worksheet_count_rank_eight : Nat.choose 264 8 = 525783425977953 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; norm_num [Nat.descFactorial, Nat.factorial]

end Worksheet

end ExactSampling.CheckpointCertificates
