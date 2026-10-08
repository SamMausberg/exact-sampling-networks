import ExactSampling.Tanh.SharpRates
import ExactSampling.Residual.CriticalCounts

/-!
# The zero-bias counting chain with the radius lemmas

Paper: `tanh_zero_bias.tex`, proof of Theorem `thm:zero-bias-linear`, with Lemma
`lem:radius` and Lemma `lem:rounding` (`tanh_rates.tex`) and the stored radii of
`eq:rounded` (`tanh_scalar.tex`).

`ExactSampling.CriticalCounts.zero_bias_chain` proves the counting bound
`1 + r_D ∑_{k<D} exp(∑_{j=k}^{D-1} (r_j² + r_j⁴)) ≤ 128(D+1)` from two declared stand-ins: the
radius decay `R_j² ≤ 3/(2j+3)` (`lem:radius`) and the rounding bounds `R_j ≤ r_j ≤ 1`,
`r_j² - R_j² ≤ 6Dε` (`lem:rounding`). Both lemmas are proved in `ExactSampling.SharpRates`
(`idealRadius_sq_le`, `rounding_error`). `zero_bias_chain_rounded` composes them: for the
stored radii of `eq:rounded` at reference gain one, the counting bound holds with no stand-in.

Statement mismatch handled here: `zero_bias_chain` asks for `r_j² - R_j² ≤ 6Dε` for every `j`,
while `lem:rounding` gives `r_j - R_j ≤ 3jε`, hence `r_j² - R_j² ≤ 6jε`, which is at most
`6Dε` only for `j ≤ D` (the only indices the proof uses). The composition applies
`zero_bias_chain` to the radii truncated after layer `D` (replaced by the ideal radii there),
which agree with `r_j` at every index that occurs in the conclusion.

Not formalized: the predictable charging step that turns the counting bound into
`E N_calls ≤ 128(D+1)` (as in `CriticalCounts`).
-/

namespace ExactSampling.Links.ZeroBiasChain

open Finset

/-- `tanh 1 ≤ 4/5`, from `tanh² 1 ≤ 3/5` (`SharpRates.tanh_sq_le`). Auxiliary for
`lem:rounding` (tanh_rates.tex). -/
theorem tanh_one_le : Real.tanh 1 ≤ 4 / 5 := by
  have h := SharpRates.tanh_sq_le 1
  have h0 := SharpRates.tanh_nonneg_of_nonneg (zero_le_one : (0 : ℝ) ≤ 1)
  norm_num at h
  nlinarith

/-- Paper: `lem:rounding` (tanh_rates.tex), "and `r_j ≤ 1`": stored radii of `eq:rounded`
(tanh_scalar.tex) at reference gain one with `ε ≤ 1/15` stay in `[0, 1]`. -/
theorem stored_radius_mem {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 15) (r : ℕ → ℝ) (hr0 : r 0 = 1)
    (hlow : ∀ j, Real.tanh (r j) + 2 * ε ≤ r (j + 1))
    (hup : ∀ j, r (j + 1) ≤ Real.tanh (r j) + 3 * ε) :
    ∀ j, 0 ≤ r j ∧ r j ≤ 1 := by
  intro j
  induction j with
  | zero => simp [hr0]
  | succ j ih =>
    obtain ⟨h0, h1⟩ := ih
    have ht0 := SharpRates.tanh_nonneg_of_nonneg h0
    have ht1 := SharpRates.tanh_le_tanh h1
    have h45 := tanh_one_le
    exact ⟨by linarith [hlow j], by linarith [hup j]⟩

/-- `ε ≤ [100(D+1)^4]^{-1}` implies `ε ≤ 1/15`. Auxiliary for `thm:zero-bias-linear`
(tanh_zero_bias.tex). -/
theorem eps_le_of_precision {ε : ℝ} {D : ℕ} (hε : ε ≤ 1 / (100 * ((D : ℝ) + 1) ^ 4)) :
    ε ≤ 1 / 15 := by
  have h1 : (1 : ℝ) ≤ ((D : ℝ) + 1) ^ 4 :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
  refine hε.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- Paper: `lem:rounding` (tanh_rates.tex), "Lemma `lem:rounding` gives
`0 ≤ r_j² - R_j² ≤ 6Dε` and `r_j ≤ 1`", in the form used by `thm:zero-bias-linear`: for the
stored radii of `eq:rounded` at reference gain one and `j ≤ D`, `R_j ≤ r_j ≤ 1` and
`r_j² - R_j² ≤ 6Dε`. From `SharpRates.rounding_error`. -/
theorem rounding_sq {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 15) (r : ℕ → ℝ) (hr0 : r 0 = 1)
    (hlow : ∀ j, Real.tanh (r j) + 2 * ε ≤ r (j + 1))
    (hup : ∀ j, r (j + 1) ≤ Real.tanh (r j) + 3 * ε) {D j : ℕ} (hj : j ≤ D) :
    SharpRates.idealRadius 1 j ≤ r j ∧ r j ≤ 1 ∧
      r j ^ 2 - SharpRates.idealRadius 1 j ^ 2 ≤ 6 * D * ε := by
  have hround := SharpRates.rounding_error (g := 1) zero_le_one hε0 r hr0
    (fun j => by rw [one_mul]; exact hlow j) (fun j => by rw [one_mul]; exact hup j) j
  have hmem := stored_radius_mem hε0 hε r hr0 hlow hup j
  have hR0 := SharpRates.idealRadius_nonneg zero_le_one j
  have hj' : (j : ℝ) ≤ D := by exact_mod_cast hj
  refine ⟨by linarith [hround.1], hmem.2, ?_⟩
  set R := SharpRates.idealRadius 1 j
  have hsum : r j + R ≤ 2 := by linarith [hmem.2]
  have hdiff : r j - R ≤ 3 * D * ε := hround.2.trans (by nlinarith)
  calc r j ^ 2 - R ^ 2 = (r j - R) * (r j + R) := by ring
    _ ≤ (3 * D * ε) * 2 :=
        mul_le_mul hdiff hsum (by linarith [hround.1]) (by positivity)
    _ = 6 * D * ε := by ring

/-- Paper: proof of `thm:zero-bias-linear` (tanh_zero_bias.tex), the composed counting bound
`1 + r_D ∑_{k<D} exp(∑_{j=k}^{D-1} (r_j² + r_j⁴)) ≤ 128(D+1)` for the stored radii of
`eq:rounded` (tanh_scalar.tex) at reference gain one, with `ε ≤ [100(D+1)^4]^{-1}`. This is
`CriticalCounts.zero_bias_chain` with its stand-ins `lem:radius` and `lem:rounding` discharged
by `SharpRates.idealRadius_sq_le` and `rounding_sq`. -/
theorem zero_bias_chain_rounded (D : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / (100 * ((D : ℝ) + 1) ^ 4)) (r : ℕ → ℝ) (hr0 : r 0 = 1)
    (hlow : ∀ j, Real.tanh (r j) + 2 * ε ≤ r (j + 1))
    (hup : ∀ j, r (j + 1) ≤ Real.tanh (r j) + 3 * ε) :
    1 + r D * ∑ k ∈ range D, Real.exp (∑ j ∈ Ico k D, (r j ^ 2 + r j ^ 4)) ≤
      128 * ((D : ℝ) + 1) := by
  have hε' := eps_le_of_precision hε
  set R := SharpRates.idealRadius 1 with hRdef
  set r' : ℕ → ℝ := fun j => if j ≤ D then r j else R j with hr'def
  have hR0 : ∀ j, 0 ≤ R j := SharpRates.idealRadius_nonneg zero_le_one
  have hRr : ∀ j, R j ≤ r' j := fun j => by
    simp only [hr'def]
    split_ifs with hj
    · exact (rounding_sq hε0 hε' r hr0 hlow hup hj).1
    · exact le_rfl
  have hr1 : ∀ j, r' j ≤ 1 := fun j => by
    simp only [hr'def]
    split_ifs with hj
    · exact (rounding_sq hε0 hε' r hr0 hlow hup hj).2.1
    · exact SharpRates.idealRadius_le_one 1 j
  have hRq : ∀ j : ℕ, R j ^ 2 ≤ 3 / (2 * j + 3) := fun j =>
    SharpRates.idealRadius_sq_le zero_le_one le_rfl j
  have hround : ∀ j, r' j ^ 2 - R j ^ 2 ≤ 6 * D * ε := fun j => by
    simp only [hr'def]
    split_ifs with hj
    · exact (rounding_sq hε0 hε' r hr0 hlow hup hj).2.2
    · rw [sub_self]; positivity
  have h := CriticalCounts.zero_bias_chain D ε hε0 hε R r' hR0 hRr hr1 hRq hround
  have hD : r' D = r D := by simp [hr'def]
  have hsum : ∑ k ∈ range D, Real.exp (∑ j ∈ Ico k D, (r' j ^ 2 + r' j ^ 4)) =
      ∑ k ∈ range D, Real.exp (∑ j ∈ Ico k D, (r j ^ 2 + r j ^ 4)) := by
    refine sum_congr rfl fun k _ => ?_
    congr 1
    refine sum_congr rfl fun j hj => ?_
    have hjD : j ≤ D := (mem_Ico.mp hj).2.le
    simp [hr'def, hjD]
  rw [hD, hsum] at h
  exact h

end ExactSampling.Links.ZeroBiasChain
