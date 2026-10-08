import Mathlib

/-!
# Bounded rational coordinate charts

Paper: `conference.tex`, Section `sec:conf-grid`, Lemma `lem:conf-chart` (bounded rational
coordinates) and its proof; full version `exact_sampling_networks.tex`, Lemma
`lem:dynamicchart` (`attention_dynamic_index.tex`). The chart-membership test and the chart
representation `k = c₀ + A k_I` are used in the proof of `thm:conf-grid` and of
`thm:dynamicfixedrank`.

For an `n × d` matrix `U` and selected rows `I : Fin d → Fin n` with `U_I` nonsingular, the chart
coefficients are `A = U (U_I)⁻¹`.

## What is formalized

* `A_I = I_d` (selected rows have identity coefficients) and `U = A U_I`.
* Determinant multilinearity under row replacement: replacing selected row `j` by row `i`
  multiplies the minor by `A_{ij}`.
* A row with `|A_{ij}| > 1` (in particular `> 2`) is not already selected, so a replacement keeps
  the selected rows distinct.
* Clearing a common denominator does not change the coefficients.
* The termination count: along any run of replacements on an integer matrix with entries of
  magnitude at most `M`, each replacing a row with `|A_{ij}| > 2`, after `m` replacements
  `2^m ≤ d! M^d`, so `m ≤ log₂(d! M^d)`.
* Existence: a full-column-rank matrix has a nonsingular `d × d` row minor, and a selection of
  maximal minor magnitude gives a chart with `A_I = I_d` and `|A_{ij}| ≤ 1 ≤ 2`.
* The membership test: `v` is in the column span of `U` iff `v = A v_I`, and then
  `k = c₀ + A k_I` with `c₀ = c - A c_I` whenever `k - c` lies in that span.

## What is not formalized

The bit-length bounds (`O_r(B)`-bit coefficients via Cramer's rule, the `O_r(n B^3)` work, and
the `O_r(n B^2)` cost per stage) are out of scope; the count `m ≤ log₂(d! M^d)` is the
mathematical content behind "only `O_r(B)` replacements occur".
-/

open Matrix
open scoped Nat

namespace ExactSampling.Chart

variable {n d : ℕ}

/-- The selected `d × d` row block `U_I`. Paper: `lem:conf-chart` (conference.tex). -/
def rows {R : Type*} (U : Matrix (Fin n) (Fin d) R) (I : Fin d → Fin n) :
    Matrix (Fin d) (Fin d) R :=
  U.submatrix I id

/-- The chart coefficients `A = U (U_I)⁻¹`. Paper: `lem:conf-chart` (conference.tex). -/
noncomputable def coeff (U : Matrix (Fin n) (Fin d) ℝ) (I : Fin d → Fin n) :
    Matrix (Fin n) (Fin d) ℝ :=
  U * (rows U I)⁻¹

/-- Row selection commutes with right multiplication: `(U B)_I = U_I B`. Auxiliary for the
proof of `lem:conf-chart` (conference.tex). -/
theorem rows_mul {R : Type*} [CommRing R] (U : Matrix (Fin n) (Fin d) R)
    (B : Matrix (Fin d) (Fin d) R) (I : Fin d → Fin n) :
    rows (U * B) I = rows U I * B := by
  ext a b
  simp [rows, mul_apply]

/-- Selected rows have identity coefficients: `A_I = I_d`. Paper: `lem:conf-chart`
(conference.tex), "`A_I = I_d`"; full version: `lem:dynamicchart`
(attention_dynamic_index.tex). -/
theorem rows_coeff (U : Matrix (Fin n) (Fin d) ℝ) (I : Fin d → Fin n)
    (h : (rows U I).det ≠ 0) : rows (coeff U I) I = 1 := by
  unfold coeff
  rw [rows_mul]
  exact mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h)

/-- Reconstruction: `U = A U_I`, i.e. each row of `U` is the combination of the selected rows
with the chart coefficients. Paper: proof of `lem:conf-chart` (conference.tex). -/
theorem coeff_mul_rows (U : Matrix (Fin n) (Fin d) ℝ) (I : Fin d → Fin n)
    (h : (rows U I).det ≠ 0) : coeff U I * rows U I = U := by
  unfold coeff
  rw [Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h), Matrix.mul_one]

/-- Entrywise form of `A_I = I_d`. Paper: proof of `lem:conf-chart` (conference.tex), "selected
rows have identity coefficients". -/
theorem coeff_selected (U : Matrix (Fin n) (Fin d) ℝ) (I : Fin d → Fin n)
    (h : (rows U I).det ≠ 0) (l j : Fin d) :
    coeff U I (I l) j = if l = j then 1 else 0 := by
  have := congrFun (congrFun (rows_coeff U I h) l) j
  simpa [rows, one_apply] using this

/-- A row whose coefficient exceeds one in magnitude is not a selected row; hence the replacement
in the proof of `lem:conf-chart` (conference.tex) produces distinct rows ("the new row is
distinct because selected rows have identity coefficients"). -/
theorem not_mem_range_of_one_lt (U : Matrix (Fin n) (Fin d) ℝ) (I : Fin d → Fin n)
    (h : (rows U I).det ≠ 0) {i : Fin n} {j : Fin d} (hij : 1 < |coeff U I i j|) :
    i ∉ Set.range I := by
  rintro ⟨l, rfl⟩
  rw [coeff_selected U I h] at hij
  split_ifs at hij <;> norm_num at hij

/-- Selected rows of a nonsingular minor are distinct. Auxiliary for the proof of
`lem:conf-chart` (conference.tex). -/
theorem injective_of_det_ne_zero {R : Type*} [CommRing R] (U : Matrix (Fin n) (Fin d) R)
    (I : Fin d → Fin n) (h : (rows U I).det ≠ 0) : Function.Injective I := by
  intro a b hab
  by_contra hne
  apply h
  exact det_zero_of_row_eq hne (by funext c; simp [rows, hab])

/-- Replacing selected row `j` by row `i` as an update of the selected block. Auxiliary for the
proof of `lem:conf-chart` (conference.tex). -/
theorem rows_update {R : Type*} (U : Matrix (Fin n) (Fin d) R) (I : Fin d → Fin n)
    (j : Fin d) (i : Fin n) :
    rows U (Function.update I j i) = (rows U I).updateRow j (U i) := by
  ext a b
  by_cases ha : a = j
  · subst ha; simp [rows]
  · simp [rows, ha]

/-- Determinant multilinearity under row replacement: replacing selected row `j` of `U_I` by row
`i` multiplies the determinant by the coefficient `[U (U_I)⁻¹]_{ij}`. Paper: proof of
`lem:conf-chart` (conference.tex), "determinant multilinearity multiplies the determinant's
absolute value by that coefficient"; full version: proof of `lem:dynamicchart`
(attention_dynamic_index.tex). -/
theorem det_replace (U : Matrix (Fin n) (Fin d) ℝ) (I : Fin d → Fin n)
    (h : (rows U I).det ≠ 0) (i : Fin n) (j : Fin d) :
    (rows U (Function.update I j i)).det = coeff U I i j * (rows U I).det := by
  have hrow : U i = ∑ k, coeff U I i k • rows U I k := by
    have := congrFun (coeff_mul_rows U I h) i
    rw [← this]
    funext b
    simp [mul_apply, Finset.sum_apply]
  rw [rows_update, hrow, det_updateRow_sum, smul_eq_mul]

/-- Clearing a common nonzero scalar (for instance the dyadic denominator `2^b`) does not change
the chart coefficients: `(sU) ((sU)_I)⁻¹ = U (U_I)⁻¹`. Paper: proof of `lem:conf-chart`
(conference.tex), "clear the common dyadic denominator". -/
theorem coeff_smul (U : Matrix (Fin n) (Fin d) ℝ) (I : Fin d → Fin n)
    (h : (rows U I).det ≠ 0) {s : ℝ} (hs : s ≠ 0) :
    coeff (s • U) I = coeff U I := by
  unfold coeff
  have hr : rows (s • U) I = s • rows U I := by ext a b; simp [rows]
  have hinv : (s • rows U I)⁻¹ = s⁻¹ • (rows U I)⁻¹ := by
    apply inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hs, one_smul,
      nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h)]
  rw [hr, hinv, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hs, one_smul]

/-- Minor bound `|det E_I| ≤ d! M^d` for an integer matrix with entries of magnitude at most
`M`. Paper: proof of `lem:conf-chart` (conference.tex), "every minor has magnitude at most
`d!‖E‖_max^d`". -/
theorem abs_det_rows_le (E : Matrix (Fin n) (Fin d) ℤ) (M : ℤ) (hM : ∀ i j, |E i j| ≤ M)
    (I : Fin d → Fin n) : |(rows E I).det| ≤ (d ! : ℤ) * M ^ d := by
  have := Matrix.det_le (A := rows E I) (abv := AbsoluteValue.abs) (x := M)
    (fun a b => hM (I a) b)
  simpa [nsmul_eq_mul] using this

/-- Casting an integer minor to the reals. Auxiliary for the termination count in the proof of
`lem:conf-chart` (conference.tex). -/
theorem det_rows_map (E : Matrix (Fin n) (Fin d) ℤ) (I : Fin d → Fin n) :
    (rows (E.map (Int.cast : ℤ → ℝ)) I).det = ((rows E I).det : ℝ) := by
  rw [Int.cast_det]
  rfl

/-- One replacement more than doubles the minor. Paper: proof of `lem:conf-chart`
(conference.tex), "if `|[E(E_I)⁻¹]_{ij}| > 2`, replace selected row `j` by row `i`"; full
version: `lem:dynamicchart` (attention_dynamic_index.tex). -/
theorem abs_det_replace_gt (U : Matrix (Fin n) (Fin d) ℝ) (I : Fin d → Fin n)
    (h : (rows U I).det ≠ 0) {i : Fin n} {j : Fin d} (hij : 2 < |coeff U I i j|) :
    2 * |(rows U I).det| < |(rows U (Function.update I j i)).det| := by
  rw [det_replace U I h, abs_mul]
  exact mul_lt_mul_of_pos_right hij (abs_pos.mpr h)

/-- Termination count of the maximum-volume iteration. Let `E` be an integer matrix with entries
of magnitude at most `M`, let `I 0` select a nonsingular minor, and suppose that for `t < m`
the selection `I (t+1)` replaces some selected row `j` of `I t` by a row `i` with
`|[E (E_{I t})⁻¹]_{ij}| > 2`. Then every minor along the run is nonzero with
`|det E_{I t}| ≥ 2^t`, and `2^m ≤ d! M^d`. Paper: proof of `lem:conf-chart` (conference.tex),
"a nonzero integer minor has magnitude at least one; every minor has magnitude at most
`d!‖E‖_max^d`. Only `O_r(B)` replacements occur"; full version: `lem:dynamicchart`
(attention_dynamic_index.tex). -/
theorem replacement_count (E : Matrix (Fin n) (Fin d) ℤ) (M : ℤ) (hM : ∀ i j, |E i j| ≤ M)
    (I : ℕ → Fin d → Fin n) (m : ℕ) (h0 : (rows E (I 0)).det ≠ 0)
    (hstep : ∀ t < m, ∃ i j, I (t + 1) = Function.update (I t) j i ∧
      2 < |coeff (E.map (Int.cast : ℤ → ℝ)) (I t) i j|) :
    (∀ t ≤ m, (rows E (I t)).det ≠ 0 ∧ (2 : ℝ) ^ t ≤ |((rows E (I t)).det : ℝ)|) ∧
      (2 : ℤ) ^ m ≤ (d ! : ℤ) * M ^ d := by
  set F := E.map (Int.cast : ℤ → ℝ)
  have key : ∀ t ≤ m, (rows E (I t)).det ≠ 0 ∧ (2 : ℝ) ^ t ≤ |((rows E (I t)).det : ℝ)| := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨h0, ?_⟩
      have : (1 : ℤ) ≤ |(rows E (I 0)).det| := Int.one_le_abs h0
      simpa [← Int.cast_abs] using (show (1 : ℝ) ≤ ((|(rows E (I 0)).det| : ℤ) : ℝ) by
        exact_mod_cast this)
    | succ t ih =>
      intro ht
      obtain ⟨hne, hpow⟩ := ih (by omega)
      obtain ⟨i, j, hI, hij⟩ := hstep t (by omega)
      have hneR : (rows F (I t)).det ≠ 0 := by
        rw [det_rows_map]; exact_mod_cast hne
      have hgt := abs_det_replace_gt F (I t) hneR hij
      rw [← hI, det_rows_map, det_rows_map] at hgt
      refine ⟨?_, ?_⟩
      · intro h
        rw [h] at hgt
        simp only [Int.cast_zero, abs_zero] at hgt
        linarith [abs_nonneg ((rows E (I t)).det : ℝ)]
      · rw [pow_succ]
        linarith
  refine ⟨key, ?_⟩
  obtain ⟨-, hpow⟩ := key m le_rfl
  have hle := abs_det_rows_le E M hM (I m)
  have hle' : |((rows E (I m)).det : ℝ)| ≤ ((d ! : ℤ) * M ^ d : ℤ) := by
    rw [← Int.cast_abs]; exact_mod_cast hle
  have : ((2 : ℤ) ^ m : ℤ) ≤ ((d ! : ℤ) * M ^ d : ℤ) := by
    have h2 : ((2 : ℤ) ^ m : ℝ) = (2 : ℝ) ^ m := by push_cast; ring
    exact_mod_cast (h2 ▸ hpow).trans hle'
  exact this

/-- The number of replacements is at most `log₂(d! M^d)`. Paper: proof of `lem:conf-chart`
(conference.tex), "only `O_r(B)` replacements occur". -/
theorem replacement_count_le_log (E : Matrix (Fin n) (Fin d) ℤ) (M : ℕ)
    (hM : ∀ i j, |E i j| ≤ M) (I : ℕ → Fin d → Fin n) (m : ℕ) (h0 : (rows E (I 0)).det ≠ 0)
    (hstep : ∀ t < m, ∃ i j, I (t + 1) = Function.update (I t) j i ∧
      2 < |coeff (E.map (Int.cast : ℤ → ℝ)) (I t) i j|) :
    m ≤ Nat.log 2 (d ! * M ^ d) := by
  have h := (replacement_count E M hM I m h0 hstep).2
  have h' : 2 ^ m ≤ d ! * M ^ d := by exact_mod_cast h
  exact Nat.le_log_of_pow_le (by norm_num) h'

/-- A full-column-rank matrix has a nonsingular `d × d` row minor. Paper: proof of
`lem:conf-chart` (conference.tex), "start with any nonsingular row minor"; full version: proof
of `lem:dynamicchart` (attention_dynamic_index.tex), "find any nonsingular row minor". -/
theorem exists_det_rows_ne_zero (U : Matrix (Fin n) (Fin d) ℝ) (hU : U.rank = d) :
    ∃ I : Fin d → Fin n, (rows U I).det ≠ 0 := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ U.row
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = d := by
    rw [← finrank_span_eq_card hli, hspan, ← rank_eq_finrank_span_row, hU]
  let e : κ ≃ Fin d := Fintype.equivFinOfCardEq hcard
  refine ⟨a ∘ e.symm, ?_⟩
  have hli' : LinearIndependent ℝ (rows U (a ∘ e.symm)).row :=
    hli.comp e.symm e.symm.injective
  have hu := linearIndependent_rows_iff_isUnit.mp hli'
  exact ((isUnit_iff_isUnit_det _).mp hu).ne_zero

/-- Existence of a bounded chart (maximum volume). For a full-column-rank `U`, a selection `I`
whose minor has maximal magnitude is injective, nonsingular, has `A_I = I_d`, and all chart
coefficients satisfy `|A_{ij}| ≤ 1`, in particular `|A_{ij}| ≤ 2`. Paper: `lem:conf-chart`
(conference.tex), "`A_I = I_d` and `|A_{ij}| ≤ 2`"; full version: `lem:dynamicchart`
(attention_dynamic_index.tex). -/
theorem exists_bounded_chart (U : Matrix (Fin n) (Fin d) ℝ) (hU : U.rank = d) :
    ∃ I : Fin d → Fin n, Function.Injective I ∧ (rows U I).det ≠ 0 ∧
      rows (coeff U I) I = 1 ∧ (∀ i j, |coeff U I i j| ≤ 1) ∧ ∀ i j, |coeff U I i j| ≤ 2 := by
  obtain ⟨I0, hI0⟩ := exists_det_rows_ne_zero U hU
  obtain ⟨I, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun J : Fin d → Fin n => |(rows U J).det|) ⟨I0, Finset.mem_univ _⟩
  have hI : (rows U I).det ≠ 0 := by
    intro h
    have := hmax I0 (Finset.mem_univ _)
    rw [h, abs_zero] at this
    exact hI0 (abs_nonpos_iff.mp this)
  have hle : ∀ i j, |coeff U I i j| ≤ 1 := by
    intro i j
    have h1 := hmax (Function.update I j i) (Finset.mem_univ _)
    rw [det_replace U I hI, abs_mul] at h1
    have hpos : 0 < |(rows U I).det| := abs_pos.mpr hI
    nlinarith
  exact ⟨I, injective_of_det_ne_zero U I hI, hI, rows_coeff U I hI, hle,
    fun i j => (hle i j).trans (by norm_num)⟩

/-- The chart membership test: a vector `v` lies in the column span of `U` iff `v = A v_I`.
Paper: proof of `thm:conf-grid` (conference.tex), "membership in the current span is tested by
the exact equality `k - c = A(k_I - c_I)`"; full version: proof of `thm:dynamicfixedrank`
(attention_dynamic_index.tex). -/
theorem mem_span_iff (U : Matrix (Fin n) (Fin d) ℝ) (I : Fin d → Fin n)
    (h : (rows U I).det ≠ 0) (v : Fin n → ℝ) :
    (∃ z : Fin d → ℝ, v = U *ᵥ z) ↔ v = coeff U I *ᵥ (fun l => v (I l)) := by
  constructor
  · rintro ⟨z, rfl⟩
    have hvI : (fun l => (U *ᵥ z) (I l)) = rows U I *ᵥ z := by
      funext l; simp [rows, mulVec, dotProduct]
    rw [hvI, mulVec_mulVec, coeff_mul_rows U I h]
  · intro hv
    exact ⟨(rows U I)⁻¹ *ᵥ (fun l => v (I l)), by rw [mulVec_mulVec]; exact hv⟩

/-- The chart representation `k = c₀ + A k_I` with `c₀ = c - A c_I`, for a key `k` whose
difference `k - c` from the first key lies in the column span of `U`. Paper: proof of
`thm:conf-grid` (conference.tex), "within one chart, `k = c₀ + A k_I`, where
`c₀ = c - A c_I`"; full version: proof of `thm:dynamicfixedrank`
(attention_dynamic_index.tex). -/
theorem chart_repr (U : Matrix (Fin n) (Fin d) ℝ) (I : Fin d → Fin n)
    (h : (rows U I).det ≠ 0) (c k : Fin n → ℝ) (hk : ∃ z : Fin d → ℝ, k - c = U *ᵥ z) :
    k = (c - coeff U I *ᵥ (fun l => c (I l))) + coeff U I *ᵥ (fun l => k (I l)) := by
  have h1 := (mem_span_iff U I h (k - c)).mp hk
  have h2 : (fun l => (k - c) (I l)) = (fun l => k (I l)) - (fun l => c (I l)) := by
    funext l; simp
  rw [h2, mulVec_sub] at h1
  funext a
  have := congrFun h1 a
  simp only [Pi.sub_apply, Pi.add_apply] at this ⊢
  linarith

end ExactSampling.Chart
