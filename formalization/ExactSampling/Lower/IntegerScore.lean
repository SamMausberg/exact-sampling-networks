import Mathlib

/-!
# The integer score obstruction

Paper file: tanh_new_critical.tex, `cor:new-integer-score` and the discussion after it.

Formalized:
* the supporting lines `(2k + 1)|v| ≤ v² + k(k + 1)` for integers `v` ("no integer lies strictly
  between `k` and `k + 1`");
* the integrated bound `E T ≥ (2k + 1)|f'(0)| - k(k + 1)` for an integer-valued stopped score
  `S_T` on an arbitrary probability space: the lattice inequality is derived pointwise from
  integrality, and only the score identity `f'(0) = E[Y S_T]` and the stopped isometry
  `E S_T² = E T` enter as hypotheses (`hscore`, `hiso`), together with `|Y| ≤ 1` and
  integrability;
* the optimal line at `k = ⌊a⌋`: `(2k + 1)a - k(k + 1) = a² + (a - k)(k + 1 - a) ∈ [a², a² + 1/4]`;
* `G_r'(0) = r coth r` for the normalized target `G_r(z) = tanh(rz)/tanh r`.

The score identity and the stopped isometry for factories with finite expected work
(`lem:new-finite-score`) are not formalized; they are the hypotheses `hscore` and `hiso`. For
factories given by finitely many decision trees, the full statement
`E₀Q ≥ (2k + 1)|H'(0)| - k(k + 1)` and the expansion `3 r coth r - 2 ≥ 1 + r² - r⁴/6` are
proved in `ExactSampling.TranscriptLowerBounds` (`integer_score_bound`, `three_r_coth_lower`).
-/

namespace ExactSampling.IntegerScore

noncomputable section

/-- Integer spacing: `(2k + 1)|v| ≤ v² + k(k + 1)` for every integer `v` and natural `k`.

Paper: proof of `cor:new-integer-score` (tanh_new_critical.tex). -/
theorem integer_score_line (v : ℤ) (k : ℕ) :
    (2 * k + 1) * |(v : ℝ)| ≤ (v : ℝ) ^ 2 + k * (k + 1) := by
  have h : |v| ≤ k ∨ k + 1 ≤ |v| := by omega
  have hsq : (v : ℝ) ^ 2 = |(v : ℝ)| ^ 2 := (sq_abs _).symm
  rcases h with h | h
  · have hc : |(v : ℝ)| ≤ k := by exact_mod_cast h
    have h0 : 0 ≤ |(v : ℝ)| := abs_nonneg _
    nlinarith
  · have hc : (k : ℝ) + 1 ≤ |(v : ℝ)| := by exact_mod_cast h
    nlinarith

/-- **Integrated integer score bound.** Let `S` be an integer-valued stopped score and `Y` an
output with `|Y| ≤ 1` on a probability space. If `f'(0) = E[Y S]` (score identity) and
`E S² = E T` (stopped isometry), then `E T ≥ (2k + 1)|f'(0)| - k(k + 1)` for every `k`. The
lattice inequality `(2k + 1)|S| ≤ S² + k(k + 1)` is derived from integrality.

Paper: `cor:new-integer-score` (tanh_new_critical.tex). -/
theorem integrated_integer_score_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (S : Ω → ℤ) (Y : Ω → ℝ) (hY : ∀ ω, |Y ω| ≤ 1)
    (hS2 : MeasureTheory.Integrable (fun ω => ((S ω : ℝ)) ^ 2) μ)
    (hYS : MeasureTheory.Integrable (fun ω => Y ω * (S ω : ℝ)) μ)
    {work deriv0 : ℝ} (hscore : deriv0 = ∫ ω, Y ω * (S ω : ℝ) ∂μ)
    (hiso : ∫ ω, ((S ω : ℝ)) ^ 2 ∂μ = work) (k : ℕ) :
    (2 * (k : ℝ) + 1) * |deriv0| - k * (k + 1) ≤ work := by
  have hk : 0 ≤ 2 * (k : ℝ) + 1 := by positivity
  have hpt : ∀ ω, (2 * (k : ℝ) + 1) * |Y ω * (S ω : ℝ)| ≤ ((S ω : ℝ)) ^ 2 + k * (k + 1) := by
    intro ω
    have h1 : |Y ω * (S ω : ℝ)| ≤ |(S ω : ℝ)| := by
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (hY ω)
    exact (mul_le_mul_of_nonneg_left h1 hk).trans (integer_score_line (S ω) k)
  have hint : ∫ ω, (2 * (k : ℝ) + 1) * |Y ω * (S ω : ℝ)| ∂μ ≤
      ∫ ω, (((S ω : ℝ)) ^ 2 + k * (k + 1)) ∂μ :=
    MeasureTheory.integral_mono (hYS.abs.const_mul _) (hS2.add (MeasureTheory.integrable_const _))
      hpt
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hS2
    (MeasureTheory.integrable_const _), MeasureTheory.integral_const, hiso] at hint
  simp only [MeasureTheory.probReal_univ, smul_eq_mul, one_mul] at hint
  have habs : |deriv0| ≤ ∫ ω, |Y ω * (S ω : ℝ)| ∂μ := by
    rw [hscore]; exact MeasureTheory.abs_integral_le_integral_abs
  have := mul_le_mul_of_nonneg_left habs hk
  linarith

/-- **The optimal supporting line.** For `a ≥ 0` and `k = ⌊a⌋`,
`(2k + 1)a - k(k + 1) = a² + (a - k)(k + 1 - a)`, which lies in `[a², a² + 1/4]`.

Paper: discussion after `cor:new-integer-score` (tanh_new_critical.tex). -/
theorem optimal_integer_line {a : ℝ} (ha : 0 ≤ a) :
    (2 * (⌊a⌋₊ : ℝ) + 1) * a - ⌊a⌋₊ * (⌊a⌋₊ + 1) = a ^ 2 + (a - ⌊a⌋₊) * (⌊a⌋₊ + 1 - a) ∧
      a ^ 2 ≤ (2 * (⌊a⌋₊ : ℝ) + 1) * a - ⌊a⌋₊ * (⌊a⌋₊ + 1) ∧
      (2 * (⌊a⌋₊ : ℝ) + 1) * a - ⌊a⌋₊ * (⌊a⌋₊ + 1) ≤ a ^ 2 + 1 / 4 := by
  have h1 : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha
  have h2 : a < ⌊a⌋₊ + 1 := Nat.lt_floor_add_one a
  have e : (2 * (⌊a⌋₊ : ℝ) + 1) * a - ⌊a⌋₊ * (⌊a⌋₊ + 1) =
      a ^ 2 + (a - ⌊a⌋₊) * (⌊a⌋₊ + 1 - a) := by ring
  refine ⟨e, ?_, ?_⟩
  · rw [e]; nlinarith
  · rw [e]; nlinarith [sq_nonneg (a - ⌊a⌋₊ - 1 / 2)]

/-- The normalized factory target `G_r(z) = tanh(rz)/tanh r` has `G_r'(0) = r coth r`, so the
first integer line gives `E₀T ≥ 3 r coth r - 2`.

Paper: `cor:new-integer-score` (tanh_new_critical.tex). -/
theorem normalized_target_deriv (r : ℝ) :
    HasDerivAt (fun z => Real.tanh (r * z) / Real.tanh r) (r / Real.tanh r) 0 := by
  have hd : ∀ x, HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := fun x => by
    have h : Real.tanh = Real.sinh / Real.cosh := by
      funext y; rw [Pi.div_apply, Real.tanh_eq_sinh_div_cosh]
    have hc := (Real.cosh_pos x).ne'
    have hd := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
    rw [← h] at hd
    refine hd.congr_deriv ?_
    rw [Real.tanh_eq_sinh_div_cosh, div_pow]
    field_simp
  have h := ((hd (r * 0)).comp 0 ((hasDerivAt_id' (0 : ℝ)).const_mul r)).div_const
    (Real.tanh r)
  refine h.congr_deriv ?_
  simp

/-- The `k = 1` instance: `E₀T ≥ 3|f'(0)| - 2`; for `G_r` this is `3 r coth r - 2`.
Paper: `cor:new-integer-score` (tanh_new_critical.tex). -/
theorem first_integer_score_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (S : Ω → ℤ) (Y : Ω → ℝ) (hY : ∀ ω, |Y ω| ≤ 1)
    (hS2 : MeasureTheory.Integrable (fun ω => ((S ω : ℝ)) ^ 2) μ)
    (hYS : MeasureTheory.Integrable (fun ω => Y ω * (S ω : ℝ)) μ)
    {work deriv0 : ℝ} (hscore : deriv0 = ∫ ω, Y ω * (S ω : ℝ) ∂μ)
    (hiso : ∫ ω, ((S ω : ℝ)) ^ 2 ∂μ = work) :
    3 * |deriv0| - 2 ≤ work := by
  have := integrated_integer_score_bound μ S Y hY hS2 hYS hscore hiso 1
  norm_num at this
  linarith

end

end ExactSampling.IntegerScore
