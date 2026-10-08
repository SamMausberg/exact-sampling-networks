import Mathlib

/-!
# RMS normalization with a certified denominator floor

This module formalizes the quantitative content of `thm:rmsfloor` (normalization_floor.tex). That
theorem is the first construction of `thm:main-rms` (main_normalization.tex) and the RMS row of
the certificate table in `sec:checkpoint` (checkpoint_conference.tex). The module also covers the
counting estimates in the proofs of `lem:rmshalfnb` and `lem:general-linear-bits`.

Formalized here:
* the disagreement coin `q = (1 - n⁻¹ ∑ (a_j/R)²)/2` and the parameters `U, d, C, ζ` of
  `eq:rmsparameters`, with the amplifier properties of `eq:rmsamplifier` and the replacement
  of `λ` by `max{λ, ε}`;
* the half-order negative-binomial law `Pr(K = k) = √d c_k (1-d)^k`, `c_k = C(2k,k) 4^{-k}`:
  it is a probability law, its generating function is `√d / √(1 - (1-d)x)`, and its mean is
  `(1-d)/(2d)`. These use Mathlib's binomial series for `(1-x)^{-1/2}`;
* the exactness identity `eq:rmsattenuation` as a series identity, the output mean
  `𝒩_ε(a)_i / R_out`, the arity identity `eq:rmsarity`, and the arithmetic of the source count
  `eq:rmschildbound`, `1 + 228 κ²`, with Huber's count entering as the expression `9.5 C / e`;
* in `lem:rmshalfnb`: the acceptance identity of the geometric proposal, the bound
  `c_j ≤ 1/√(j+1)`, the stopped-product count `∑_{j<k} c_j ≤ 2√k`, the per-trial bound `2/√d`,
  and the geometric interval-mass identity together with its bound `6e`;
* in `lem:general-linear-bits`: the continuation bound `exp(-46/25) < 1/6`, the stage
  multipliers `C_j < 2C`, the arithmetic inequality `((C_j - 1)⌈k_j⌉ + C_j)/e_j ≤ 14 C e_j^{-2}`
  behind the stopped-drift bound (the stopped drift itself is not formalized), and the reach
  bound `6^{-j}`;
* the rounding of `R_out` to a power of two and the corresponding thinning identity.

Not formalized: the probability space of the adaptive sampler and the conditional charging
argument; Huber's linear Bernoulli factory and its input-count theorem (the bound `9.5 C / e`
of `huber2016linear` enters only as the numerical expression it provides); and every
bit-complexity estimate (interval arithmetic, logarithm evaluation, the `B⁴` factors).
-/

open Real Finset
open scoped BigOperators

namespace ExactSampling.RMSFloor

/-! ## The disagreement coin -/

/-- Two independent signs of mean `u` disagree with probability `(1 - u²)/2`.
Paper: proof of `thm:rmsfloor` (normalization_floor.tex), the disagreement coin. -/
theorem disagreement_probability (u : ℝ) :
    ((1 + u) / 2) * ((1 - u) / 2) + ((1 - u) / 2) * ((1 + u) / 2) = (1 - u ^ 2) / 2 := by
  ring

/-- The product of two independent signs of mean `u` has mean `u²`; it is a signed quantity and
not a coin of probability `u²`.
Paper: proof of `thm:rmsfloor` (normalization_floor.tex), first paragraph. -/
theorem agreement_signed_mean (u : ℝ) :
    (((1 + u) / 2) ^ 2 + ((1 - u) / 2) ^ 2) - (2 * ((1 + u) / 2) * ((1 - u) / 2)) = u ^ 2 := by
  ring

/-- On the fair branch the output sign has mean zero: `a·u + (1 - a)·0 = a·u`.
Paper: proof of `thm:rmsfloor` (normalization_floor.tex), the fair-sign completion. -/
theorem fair_branch_mean (a u : ℝ) : a * u + (1 - a) * 0 = a * u := by
  ring

/-- The disagreement coin `q`, written with the mean square `m = n⁻¹ ∑ a_j²`. -/
noncomputable def qCoin (R m : ℝ) : ℝ := (1 - m / R ^ 2) / 2

/-- A uniform coordinate followed by two independent signs of mean `a_j / R` yields a
disagreement with probability `q = (1 - n⁻¹ ∑_j (a_j/R)²)/2`.
Paper: proof of `thm:rmsfloor` (normalization_floor.tex), definition of `q`. -/
theorem disagreement_coin {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) {R : ℝ} (hR : 0 < R) :
    (1 / (n : ℝ)) * ∑ j, (2 * (((1 + a j / R) / 2) * ((1 - a j / R) / 2)))
      = qCoin R ((1 / (n : ℝ)) * ∑ j, a j ^ 2) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hR' : R ≠ 0 := hR.ne'
  unfold qCoin
  have h : ∀ j, 2 * (((1 + a j / R) / 2) * ((1 - a j / R) / 2))
      = 1 / 2 - a j ^ 2 / (2 * R ^ 2) := by
    intro j; field_simp; ring
  simp only [h, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← sum_div]
  field_simp

/-- The disagreement coin is a probability in `[0, 1/2]` when the mean square is at most `R²`.
Paper: proof of `thm:rmsfloor` (normalization_floor.tex). -/
theorem qCoin_mem {R m : ℝ} (hR : 0 < R) (hm : 0 ≤ m) (hmR : m ≤ R ^ 2) :
    0 ≤ qCoin R m ∧ qCoin R m ≤ 1 / 2 := by
  unfold qCoin
  have hR2 : 0 < R ^ 2 := by positivity
  have h1 : m / R ^ 2 ≤ 1 := (div_le_one hR2).2 hmR
  have h2 : 0 ≤ m / R ^ 2 := div_nonneg hm hR2.le
  constructor <;> linarith

/-! ## The floor parameters (`eq:rmsparameters`, `eq:rmsamplifier`) -/

/-- `U = ε + R²`. -/
noncomputable def capU (ε R : ℝ) : ℝ := ε + R ^ 2

/-- `d = λ / (2U)`. -/
noncomputable def dPar (ε R lam : ℝ) : ℝ := lam / (2 * capU ε R)

/-- The amplifier multiplier `C = 2R² / (U - λ/2)`. -/
noncomputable def cPar (ε R lam : ℝ) : ℝ := 2 * R ^ 2 / (capU ε R - lam / 2)

/-- The slack `ζ = λ / (2U - λ)`. -/
noncomputable def zetaPar (ε R lam : ℝ) : ℝ := lam / (2 * capU ε R - lam)

/-- The condition number `κ = max{1, R²/λ}`. -/
noncomputable def kappa (R lam : ℝ) : ℝ := max 1 (R ^ 2 / lam)

section Parameters

variable {ε R lam m : ℝ}

/-- The floor promise implies `0 < λ ≤ U`.
Paper: `thm:rmsfloor` (normalization_floor.tex), after `eq:rmsparameters`. -/
theorem lam_le_capU (hmR : m ≤ R ^ 2) (hv : lam ≤ ε + m) : lam ≤ capU ε R := by
  unfold capU; linarith

/-- `0 < d ≤ 1/2`.
Paper: `thm:rmsfloor` (normalization_floor.tex), after `eq:rmsparameters`. -/
theorem dPar_mem (hlam : 0 < lam) (hmR : m ≤ R ^ 2)
    (hv : lam ≤ ε + m) : 0 < dPar ε R lam ∧ dPar ε R lam ≤ 1 / 2 := by
  have hU := lam_le_capU hmR hv
  have hU0 : 0 < capU ε R := lt_of_lt_of_le hlam hU
  unfold dPar
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- The amplifier multiplier satisfies `0 < C ≤ 4`.
Paper: `thm:rmsfloor` (normalization_floor.tex), after `eq:rmsparameters`. -/
theorem cPar_mem (hε : 0 ≤ ε) (hR : 0 < R) (hlam : 0 < lam) (hmR : m ≤ R ^ 2)
    (hv : lam ≤ ε + m) : 0 < cPar ε R lam ∧ cPar ε R lam ≤ 4 := by
  have hU := lam_le_capU hmR hv
  have hden : 0 < capU ε R - lam / 2 := by linarith
  unfold cPar
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hden]
  unfold capU at hU ⊢
  nlinarith

/-- The slack is positive: `0 < ζ`.
Paper: `eq:rmsamplifier` (normalization_floor.tex). -/
theorem zetaPar_pos (hlam : 0 < lam) (hmR : m ≤ R ^ 2) (hv : lam ≤ ε + m) :
    0 < zetaPar ε R lam := by
  have hU := lam_le_capU hmR hv
  unfold zetaPar
  have : 0 < 2 * capU ε R - lam := by linarith
  positivity

/-- The amplified coin `r = C q` satisfies `r ≤ 1 - ζ`.
Paper: `eq:rmsamplifier` (normalization_floor.tex). -/
theorem amplifier_slack (hR : 0 < R) (hlam : 0 < lam) (hmR : m ≤ R ^ 2)
    (hv : lam ≤ ε + m) : cPar ε R lam * qCoin R m ≤ 1 - zetaPar ε R lam := by
  have hU := lam_le_capU hmR hv
  have hden : 0 < capU ε R - lam / 2 := by linarith
  have hden' : 0 < 2 * capU ε R - lam := by linarith
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have key : cPar ε R lam * qCoin R m = (R ^ 2 - m) / (capU ε R - lam / 2) := by
    unfold cPar qCoin; field_simp
  have key2 : 1 - zetaPar ε R lam = (capU ε R - lam) / (capU ε R - lam / 2) := by
    unfold zetaPar; field_simp; ring
  rw [key, key2]
  apply div_le_div_of_nonneg_right _ hden.le
  unfold capU; linarith

/-- The ratio of multiplier to slack: `C / ζ = 4R²/λ`.
Paper: `eq:rmsamplifier` (normalization_floor.tex). -/
theorem cPar_div_zetaPar (hlam : 0 < lam) (hmR : m ≤ R ^ 2)
    (hv : lam ≤ ε + m) : cPar ε R lam / zetaPar ε R lam = 4 * R ^ 2 / lam := by
  have hU := lam_le_capU hmR hv
  have hden : capU ε R - lam / 2 ≠ 0 := by linarith
  have hz : zetaPar ε R lam = lam / (2 * (capU ε R - lam / 2)) := by
    unfold zetaPar; congr 1; ring
  rw [hz]
  unfold cPar
  generalize capU ε R - lam / 2 = A at *
  field_simp
  ring

/-- `(1 - d) C = 2R²/U`.
Paper: `thm:rmsfloor` (normalization_floor.tex), the algebra after `eq:rmsarity`. -/
theorem one_sub_d_mul_C (hlam : 0 < lam) (hmR : m ≤ R ^ 2) (hv : lam ≤ ε + m) :
    (1 - dPar ε R lam) * cPar ε R lam = 2 * R ^ 2 / capU ε R := by
  have hU := lam_le_capU hmR hv
  have hU0 : capU ε R ≠ 0 := by linarith
  have hden : capU ε R - lam / 2 ≠ 0 := by linarith
  have h1 : 1 - dPar ε R lam = (capU ε R - lam / 2) / capU ε R := by
    unfold dPar; field_simp
  rw [h1]
  unfold cPar
  generalize capU ε R - lam / 2 = A at *
  field_simp

/-- `1 - (1-d) C q = v / U` with `v = ε + m`.
Paper: `thm:rmsfloor` (normalization_floor.tex), the algebra after `eq:rmsarity`. -/
theorem pgf_argument (hR : 0 < R) (hlam : 0 < lam) (hmR : m ≤ R ^ 2) (hv : lam ≤ ε + m) :
    1 - (1 - dPar ε R lam) * (cPar ε R lam * qCoin R m) = (ε + m) / capU ε R := by
  have hU := lam_le_capU hmR hv
  have hU0 : capU ε R ≠ 0 := by linarith
  rw [← mul_assoc, one_sub_d_mul_C hlam hmR hv]
  unfold qCoin capU at *
  field_simp
  ring

/-- The attenuation probability: `(1/√2) √(d / (1 - (1-d) r)) = √λ / (2√v)` with `r = C q`.
Paper: `eq:rmsattenuation` (normalization_floor.tex), second equality. -/
theorem attenuation_value (hR : 0 < R) (hlam : 0 < lam) (hmR : m ≤ R ^ 2) (hv : lam ≤ ε + m) :
    (1 / √2) * √(dPar ε R lam / (1 - (1 - dPar ε R lam) * (cPar ε R lam * qCoin R m)))
      = √lam / (2 * √(ε + m)) := by
  have hU := lam_le_capU hmR hv
  have hU0 : 0 < capU ε R := by linarith
  have hv0 : 0 < ε + m := by linarith
  rw [pgf_argument hR hlam hmR hv]
  have : dPar ε R lam / ((ε + m) / capU ε R) = lam / (2 * (ε + m)) := by
    unfold dPar; field_simp
  rw [this, sqrt_div hlam.le, sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : (0 : ℝ) < √2 := by positivity
  have hs : 0 < √(ε + m) := sqrt_pos.2 hv0
  field_simp
  rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The mean arity: `(1-d)/(2d) = U/λ - 1/2`.
Paper: `eq:rmsarity` (normalization_floor.tex). -/
theorem arity_identity (hlam : 0 < lam) (hmR : m ≤ R ^ 2) (hv : lam ≤ ε + m) :
    (1 - dPar ε R lam) / (2 * dPar ε R lam) = capU ε R / lam - 1 / 2 := by
  have hU := lam_le_capU hmR hv
  have hU0 : capU ε R ≠ 0 := by linarith
  unfold dPar
  field_simp

/-- After the replacement `λ ← max{λ, ε}`, the mean arity is at most `3κ/2`.
Paper: `eq:rmsarity` (normalization_floor.tex). -/
theorem arity_bound (hlam : 0 < lam) (hεl : ε ≤ lam) :
    capU ε R / lam - 1 / 2 ≤ 3 / 2 * kappa R lam := by
  unfold capU kappa
  have h1 : ε / lam ≤ 1 := (div_le_one hlam).2 hεl
  have h2 : R ^ 2 / lam ≤ max 1 (R ^ 2 / lam) := le_max_right _ _
  have h3 : 1 ≤ max 1 (R ^ 2 / lam) := le_max_left _ _
  have : (ε + R ^ 2) / lam = ε / lam + R ^ 2 / lam := add_div _ _ _
  rw [this]
  linarith

/-- The replacement `λ ← max{λ, ε}` keeps the floor promise, can only lower `κ`, and gives
`ε ≤ λ`.
Paper: `thm:rmsfloor` (normalization_floor.tex), the replacement of `λ` by `max{λ, ε}`. -/
theorem floor_replacement (hlam : 0 < lam) (hm : 0 ≤ m) (hv : lam ≤ ε + m) :
    max lam ε ≤ ε + m ∧ kappa R (max lam ε) ≤ kappa R lam ∧ ε ≤ max lam ε := by
  refine ⟨max_le hv (by linarith), ?_, le_max_right _ _⟩
  unfold kappa
  apply max_le_max le_rfl
  exact div_le_div_of_nonneg_left (sq_nonneg R) hlam (le_max_left _ _)

/-- Huber's input-count expression `9.5 C / e`, with the supplied slack `e = min{ζ, 1/2}`, is at
most `76 κ`. The thinning case `C ≤ 1` is `thinning_count_bound`.
Paper: `thm:rmsfloor` (normalization_floor.tex), "an `r`-coin costs at most `76κ` `q`-coins". -/
theorem huber_count_bound (hε : 0 ≤ ε) (hR : 0 < R) (hlam : 0 < lam) (hmR : m ≤ R ^ 2)
    (hv : lam ≤ ε + m) :
    9.5 * cPar ε R lam / min (zetaPar ε R lam) (1 / 2) ≤ 76 * kappa R lam := by
  obtain ⟨hC0, hC4⟩ := cPar_mem hε hR hlam hmR hv
  have hz := zetaPar_pos hlam hmR hv
  have hk1 : 1 ≤ kappa R lam := le_max_left _ _
  have hk2 : R ^ 2 / lam ≤ kappa R lam := le_max_right _ _
  have hmin : 0 < min (zetaPar ε R lam) (1 / 2) := lt_min hz (by norm_num)
  rw [div_le_iff₀ hmin]
  rcases min_cases (zetaPar ε R lam) (1 / 2) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
    have hcz := cPar_div_zetaPar hlam hmR hv
    have : cPar ε R lam = 4 * R ^ 2 / lam * zetaPar ε R lam := by
      rw [← hcz]; field_simp
    rw [this]
    have h4 : 4 * R ^ 2 / lam = 4 * (R ^ 2 / lam) := by ring
    rw [h4]
    nlinarith
  · rw [h]; nlinarith

/-- The thinning case `C ≤ 1` uses one `q`-coin per `r`-coin, and `1 ≤ 76 κ`.
Paper: `thm:rmsfloor` (normalization_floor.tex), "This bound also covers thinning". -/
theorem thinning_count_bound : (1 : ℝ) ≤ 76 * kappa R lam := by
  have hk1 : 1 ≤ kappa R lam := le_max_left _ _
  linarith

/-- The numerical identity behind `eq:rmschildbound`: `1 + 2 (76κ)(3κ/2) = 1 + 228κ²`.
Paper: `eq:rmschildbound` (normalization_floor.tex). -/
theorem normalization_child_count (kap : ℝ) :
    1 + 2 * (76 * kap) * ((3 / 2) * kap) = 1 + 228 * kap ^ 2 := by
  ring

/-- Arithmetic of `eq:rmschildbound`. Huber's input count enters as the expression `9.5 C / e`
(the theorem of `huber2016linear` is not formalized). Each `q`-coin costs two source signs;
each amplified coin costs at most `9.5 C / e` `q`-coins; the expected number of amplified coins
is the mean arity `(1-d)/(2d)`; one more request supplies the output sign. The total is at most
`1 + 228 κ²`, for the floor after the replacement `λ ← max{λ, ε}`.
Paper: `eq:rmschildbound` in `thm:rmsfloor` (normalization_floor.tex); `thm:main-rms`
(main_normalization.tex); the RMS row of `sec:checkpoint` (checkpoint_conference.tex). -/
theorem source_count_bound (hε : 0 ≤ ε) (hR : 0 < R) (hlam : 0 < lam) (hmR : m ≤ R ^ 2)
    (hv : lam ≤ ε + m) (hεl : ε ≤ lam) :
    1 + 2 * (9.5 * cPar ε R lam / min (zetaPar ε R lam) (1 / 2))
        * ((1 - dPar ε R lam) / (2 * dPar ε R lam))
      ≤ 1 + 228 * kappa R lam ^ 2 := by
  have hH := huber_count_bound hε hR hlam hmR hv
  have hA := arity_identity hlam hmR hv
  have hB := arity_bound (R := R) hlam hεl
  obtain ⟨hd0, hd1⟩ := dPar_mem hlam hmR hv
  have hA0 : 0 ≤ (1 - dPar ε R lam) / (2 * dPar ε R lam) :=
    div_nonneg (by linarith) (by linarith)
  obtain ⟨hC0, _⟩ := cPar_mem hε hR hlam hmR hv
  have hz := zetaPar_pos hlam hmR hv
  have hH0 : 0 ≤ 9.5 * cPar ε R lam / min (zetaPar ε R lam) (1 / 2) :=
    div_nonneg (by positivity) (le_min hz.le (by norm_num))
  have hk1 : 1 ≤ kappa R lam := le_max_left _ _
  rw [hA] at hA0 ⊢
  have := mul_le_mul hH hB hA0 (by positivity)
  nlinarith

/-- The output mean: `(a_i/R) · √λ/(2√v) = 𝒩_ε(a)_i / R_out` with `R_out = 2R/√λ`.
Paper: `thm:rmsfloor` (normalization_floor.tex), the output sign. -/
theorem output_mean (a v : ℝ) (hR : 0 < R) (hv : 0 < v) (hlam : 0 < lam) :
    (a / R) * (√lam / (2 * √v)) = (a / √v) / (2 * R / √lam) := by
  have h1 : √v ≠ 0 := (sqrt_pos.2 hv).ne'
  have h2 : √lam ≠ 0 := (sqrt_pos.2 hlam).ne'
  field_simp

end Parameters

/-! ## The half-order negative-binomial law -/

/-- The central coefficients `c_k = C(2k,k) 4^{-k}`. -/
noncomputable def halfCoeff (k : ℕ) : ℝ := (Nat.centralBinom k : ℝ) / 4 ^ k

/-- `c_0 = 1`. -/
@[simp] theorem halfCoeff_zero : halfCoeff 0 = 1 := by simp [halfCoeff]

/-- The ratio `c_{k+1}/c_k = (2k+1)/(2k+2)`.
Paper: proof of `lem:rmshalfnb` (normalization_floor.tex). -/
theorem halfCoeff_succ (k : ℕ) : halfCoeff (k + 1) = halfCoeff k * ((2 * k + 1) / (2 * k + 2)) := by
  have h1 := Nat.succ_mul_centralBinom_succ k
  have h2 : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ)
      = 2 * (2 * k + 1) * Nat.centralBinom k := by
    exact_mod_cast h1
  unfold halfCoeff
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  rw [div_eq_iff (by positivity), pow_succ]
  field_simp
  linear_combination 2 * h2

/-- `0 < c_k`. -/
theorem halfCoeff_pos (k : ℕ) : 0 < halfCoeff k := by
  unfold halfCoeff
  have := Nat.centralBinom_pos k
  positivity

/-- `c_k² ≤ 1/(k+1)`, by induction from the ratio `(2k+1)/(2k+2)`.
Paper: proof of `lem:rmshalfnb` (normalization_floor.tex), "the elementary bound". -/
theorem halfCoeff_sq_le (k : ℕ) : halfCoeff k ^ 2 ≤ 1 / (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [halfCoeff_succ, mul_pow]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hr : 0 ≤ ((2 * (k : ℝ) + 1) / (2 * k + 2)) ^ 2 := sq_nonneg _
    calc halfCoeff k ^ 2 * ((2 * k + 1) / (2 * k + 2)) ^ 2
        ≤ 1 / (k + 1) * ((2 * k + 1) / (2 * k + 2)) ^ 2 := mul_le_mul_of_nonneg_right ih hr
      _ ≤ 1 / ((k + 1 : ℕ) + 1) := by
        push_cast
        rw [div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith

/-- `c_k ≤ 1/√(k+1)`.
Paper: proof of `lem:rmshalfnb` (normalization_floor.tex). -/
theorem halfCoeff_le_inv_sqrt (k : ℕ) : halfCoeff k ≤ 1 / √(k + 1) := by
  have h := halfCoeff_sq_le k
  have hpos := halfCoeff_pos k
  have hs : 0 < √((k : ℝ) + 1) := sqrt_pos.2 (by positivity)
  rw [le_div_iff₀ hs]
  have : (halfCoeff k * √((k : ℝ) + 1)) ^ 2 ≤ 1 := by
    rw [mul_pow, sq_sqrt (by positivity)]
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  nlinarith [sq_nonneg (halfCoeff k * √((k : ℝ) + 1) - 1), mul_pos hpos hs]

/-- `c_k ≤ 1`. -/
theorem halfCoeff_le_one (k : ℕ) : halfCoeff k ≤ 1 := by
  have h := halfCoeff_le_inv_sqrt k
  have hs : 1 ≤ √((k : ℝ) + 1) := by
    have : √1 ≤ √((k : ℝ) + 1) := sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) k])
    rwa [sqrt_one] at this
  exact le_trans h (by rw [div_le_one (by linarith)]; exact hs)

/-- The stopped product tests: `∑_{j<k} c_j ≤ 2√k`.
Paper: proof of `lem:rmshalfnb` (normalization_floor.tex). -/
theorem sum_halfCoeff_le (k : ℕ) : ∑ j ∈ range k, halfCoeff j ≤ 2 * √k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    have h := halfCoeff_le_inv_sqrt k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hs0 : 0 ≤ √(k : ℝ) := sqrt_nonneg _
    have hs1 : 0 < √((k : ℝ) + 1) := sqrt_pos.2 (by positivity)
    have hsq0 : √(k : ℝ) ^ 2 = k := sq_sqrt hk
    have hsq1 : √((k : ℝ) + 1) ^ 2 = k + 1 := sq_sqrt (by positivity)
    have hstep : 1 / √((k : ℝ) + 1) ≤ 2 * (√((k : ℝ) + 1) - √k) := by
      rw [div_le_iff₀ hs1]
      nlinarith [sq_nonneg (√((k : ℝ) + 1) - √k)]
    push_cast
    linarith

/-- Coefficients of Mathlib's series for `(1-x)^{-a}` in Pochhammer form. -/
theorem choose_eq_pochhammer (a : ℝ) (n : ℕ) :
    Ring.choose (a + n - 1) n = (ascPochhammer ℝ n).eval a / n.factorial := by
  rw [← Ring.multichoose_eq]
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n
  rw [Polynomial.ascPochhammer_smeval_eq_eval, nsmul_eq_mul] at h
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  rw [eq_div_iff hf, ← h]
  ring

/-- `(1/2)_n / n! = c_n`. -/
theorem pochhammer_half (n : ℕ) :
    (ascPochhammer ℝ n).eval (1 / 2 : ℝ) / n.factorial = halfCoeff n := by
  induction n with
  | zero => simp [halfCoeff]
  | succ n ih =>
    rw [ascPochhammer_succ_eval, Nat.factorial_succ]
    have h1 := Nat.succ_mul_centralBinom_succ n
    have h2 : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ)
        = 2 * (2 * n + 1) * Nat.centralBinom n := by exact_mod_cast h1
    unfold halfCoeff at *
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    have := ih
    rw [div_eq_div_iff hf (by positivity)] at this
    push_cast
    rw [div_eq_div_iff (by positivity) (by positivity), pow_succ]
    linear_combination (1 / 2 + (n : ℝ)) * 4 * this - (n.factorial : ℝ) * h2

/-- The binomial series `∑ c_k y^k = (1-y)^{-1/2}` for `|y| < 1`.
Paper: proof of `thm:rmsfloor` (normalization_floor.tex), "the binomial generating function". -/
theorem hasSum_halfCoeff (y : ℝ) (hy : |y| < 1) :
    HasSum (fun n => halfCoeff n * y ^ n) (1 / √(1 - y)) := by
  have hy' : y ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]
    have : ‖y‖₊ < 1 := by rw [← NNReal.coe_lt_coe]; simpa using hy
    exact_mod_cast this
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2 : ℝ)).hasSum hy'
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, zero_add, smul_eq_mul] at h
  convert h using 1
  · funext n
    rw [choose_eq_pochhammer, pochhammer_half]
  · rw [sqrt_eq_rpow]

/-- The half-order negative-binomial law `Pr(K = k) = √d c_k (1-d)^k`. -/
noncomputable def halfNB (d : ℝ) (k : ℕ) : ℝ := √d * halfCoeff k * (1 - d) ^ k

/-- The half-order negative-binomial weights are nonnegative. -/
theorem halfNB_nonneg {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (k : ℕ) : 0 ≤ halfNB d k := by
  unfold halfNB
  have := halfCoeff_pos k
  have : 0 ≤ 1 - d := by linarith
  positivity

/-- The generating function of the half-order negative binomial law:
`∑_k √d c_k (1-d)^k x^k = √d / √(1 - (1-d) x)` for `0 < d ≤ 1` and `|x| ≤ 1`.
Paper: `eq:rmsattenuation` (normalization_floor.tex), first equality. -/
theorem halfNB_pgf {d x : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hx : |x| ≤ 1) :
    HasSum (fun k => halfNB d k * x ^ k) (√d / √(1 - (1 - d) * x)) := by
  have hy : |(1 - d) * x| < 1 := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - d)]
    calc (1 - d) * |x| ≤ (1 - d) * 1 := mul_le_mul_of_nonneg_left hx (by linarith)
      _ < 1 := by linarith
  have h := (hasSum_halfCoeff _ hy).mul_left (√d)
  convert h using 1
  · funext k; unfold halfNB; rw [mul_pow]; ring
  · ring

/-- The half-order negative-binomial weights sum to one.
Paper: `thm:rmsfloor` (normalization_floor.tex), the law of `K`. -/
theorem halfNB_hasSum_one {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) : HasSum (halfNB d) 1 := by
  have h := halfNB_pgf hd hd1 (x := 1) (by simp)
  simp only [one_pow, mul_one, sub_sub_cancel] at h
  rwa [div_self (sqrt_pos.2 hd).ne'] at h

/-- The mean of the half-order negative binomial law is `(1-d)/(2d)`.
Paper: `eq:rmsarity` (normalization_floor.tex). -/
theorem halfNB_mean {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    HasSum (fun k : ℕ => (k : ℝ) * halfNB d k) ((1 - d) / (2 * d)) := by
  have hy0 : 0 ≤ 1 - d := by linarith
  have hyabs : |1 - d| < 1 := by rw [abs_of_nonneg hy0]; linarith
  have hsum : Summable (fun k : ℕ => (k : ℝ) * (halfCoeff k * (1 - d) ^ k)) := by
    have hg : Summable (fun k : ℕ => (k : ℝ) * (1 - d) ^ k) :=
      (hasSum_coe_mul_geometric_of_norm_lt_one (r := 1 - d) (by rwa [Real.norm_eq_abs])).summable
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hg
    · have := halfCoeff_pos k; positivity
    · have h1 := halfCoeff_le_one k
      have h2 := halfCoeff_pos k
      have : (0 : ℝ) ≤ k * (1 - d) ^ k := by positivity
      nlinarith
  obtain ⟨T, hTs⟩ := hsum
  have hS := hasSum_halfCoeff (1 - d) hyabs
  rw [sub_sub_cancel] at hS
  have hshift : HasSum (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * (halfCoeff (k + 1) * (1 - d) ^ (k + 1)))
      T := by
    have := (hasSum_nat_add_iff' 1).2 hTs
    simpa using this
  have hrec : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) * (halfCoeff (k + 1) * (1 - d) ^ (k + 1))
      = (1 - d) * ((k : ℝ) * (halfCoeff k * (1 - d) ^ k))
        + ((1 - d) / 2) * (halfCoeff k * (1 - d) ^ k) := by
    intro k
    rw [halfCoeff_succ]
    push_cast
    field_simp
    ring
  have hcomb : HasSum (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * (halfCoeff (k + 1) * (1 - d) ^ (k + 1)))
      ((1 - d) * T + ((1 - d) / 2) * (1 / √d)) := by
    simp only [hrec]
    exact (hTs.mul_left (1 - d)).add (hS.mul_left ((1 - d) / 2))
  have hT_eq : T = (1 - d) * T + ((1 - d) / 2) * (1 / √d) := hshift.unique hcomb
  have hsd : 0 < √d := sqrt_pos.2 hd
  have hdT : d * T = (1 - d) / 2 * (1 / √d) := by linarith
  have hTval : T * (2 * d * √d) = 1 - d := by
    calc T * (2 * d * √d) = 2 * √d * (d * T) := by ring
      _ = 2 * √d * ((1 - d) / 2 * (1 / √d)) := by rw [hdT]
      _ = 1 - d := by field_simp
  have hfin := hTs.mul_left (√d)
  convert hfin using 1
  · funext k; unfold halfNB; ring
  · rw [eq_comm, eq_div_iff (by positivity)]
    calc √d * T * (2 * d) = T * (2 * d * √d) := by ring
      _ = 1 - d := hTval

/-! ## Exactness of the attenuation step (`eq:rmsattenuation`) -/

/-- Exactness of the attenuated coin. Open a known gate of probability `1/√2`; draw `K` from the
half-order negative binomial law; return one exactly when `K` independent `r`-coins are all one.
For the floor parameters and `r = C q`, the success probability is `√λ/(2√v)`, written as a
series over `k`.
Paper: `eq:rmsattenuation` in the proof of `thm:rmsfloor` (normalization_floor.tex). -/
theorem attenuation_exact {ε R lam m : ℝ} (hε : 0 ≤ ε) (hR : 0 < R) (hlam : 0 < lam)
    (hm : 0 ≤ m) (hmR : m ≤ R ^ 2) (hv : lam ≤ ε + m) :
    HasSum (fun k => (1 / √2) * (halfNB (dPar ε R lam) k * (cPar ε R lam * qCoin R m) ^ k))
      (√lam / (2 * √(ε + m))) := by
  obtain ⟨hd0, hd1⟩ := dPar_mem hlam hmR hv
  obtain ⟨hC0, _⟩ := cPar_mem hε hR hlam hmR hv
  obtain ⟨hq0, _⟩ := qCoin_mem hR hm hmR
  have hz := zetaPar_pos hlam hmR hv
  have hr1 := amplifier_slack hR hlam hmR hv
  have hr : |cPar ε R lam * qCoin R m| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg hC0.le hq0)]; linarith
  have h := (halfNB_pgf hd0 (by linarith) hr).mul_left (1 / √2)
  convert h using 1
  rw [← attenuation_value hR hlam hmR hv]
  congr 1
  have hp : 0 < 1 - (1 - dPar ε R lam) * (cPar ε R lam * qCoin R m) := by
    rw [pgf_argument hR hlam hmR hv]
    have := lam_le_capU hmR hv
    apply div_pos <;> linarith
  rw [sqrt_div hd0.le]

/-- The output sign of the floor factory has mean `𝒩_ε(a)_i / R_out`: on `A = 1` it returns a
fresh sign of mean `a_i/R`, and on `A = 0` a fair sign.
Paper: `thm:rmsfloor` (normalization_floor.tex), exactness of the output law. -/
theorem output_sign_mean {ε R lam m a : ℝ} (hε : 0 ≤ ε) (hR : 0 < R) (hlam : 0 < lam)
    (hm : 0 ≤ m) (hmR : m ≤ R ^ 2) (hv : lam ≤ ε + m) :
    let pA := ∑' k, (1 / √2) * (halfNB (dPar ε R lam) k * (cPar ε R lam * qCoin R m) ^ k)
    pA * (a / R) + (1 - pA) * 0 = (a / √(ε + m)) / (2 * R / √lam) := by
  intro pA
  have h := (attenuation_exact hε hR hlam hm hmR hv).tsum_eq
  simp only [pA, h, mul_zero, add_zero]
  rw [mul_comm]
  exact output_mean a (ε + m) hR (by linarith) hlam

/-! ## Finite-bit sampling of the half-order law (`lem:rmshalfnb`) -/

/-- The geometric proposal `d(1-d)^k` has mean `(1-d)/d`.
Paper: proof of `lem:rmshalfnb` (normalization_floor.tex). -/
theorem geometric_mean {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    HasSum (fun k : ℕ => (k : ℝ) * (d * (1 - d) ^ k)) ((1 - d) / d) := by
  have hy : ‖1 - d‖ < 1 := by rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hy).mul_left d
  convert h using 1
  · funext k; ring
  · rw [sub_sub_cancel]; field_simp

/-- Acceptance with probability `c_G` turns the geometric proposal into the half-order law: the
mean acceptance probability is `√d`, and the accepted law is `√d c_k (1-d)^k`.
Paper: proof of `lem:rmshalfnb` (normalization_floor.tex). -/
theorem geometric_acceptance {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    HasSum (fun k => d * (1 - d) ^ k * halfCoeff k) (√d) ∧
      ∀ k, d * (1 - d) ^ k * halfCoeff k / √d = halfNB d k := by
  have hsd : 0 < √d := sqrt_pos.2 hd
  constructor
  · have h := (halfNB_hasSum_one hd hd1).mul_left (√d)
    convert h using 1
    · funext k; unfold halfNB
      have : √d * √d = d := mul_self_sqrt hd.le
      calc d * (1 - d) ^ k * halfCoeff k = (√d * √d) * (1 - d) ^ k * halfCoeff k := by rw [this]
        _ = √d * (√d * halfCoeff k * (1 - d) ^ k) := by ring
    · ring
  · intro k
    unfold halfNB
    have hdd : √d * √d = d := mul_self_sqrt hd.le
    rw [div_eq_iff hsd.ne']
    calc d * (1 - d) ^ k * halfCoeff k = (√d * √d) * (1 - d) ^ k * halfCoeff k := by rw [hdd]
      _ = √d * halfCoeff k * (1 - d) ^ k * √d := by ring

/-- An unconditional trial makes at most `2/√d` product tests in expectation: conditional on
`G = k` the count is at most `2√k`, and `𝔼 √G ≤ √(𝔼 G) ≤ 1/√d`.
Paper: proof of `lem:rmshalfnb` (normalization_floor.tex). -/
theorem expected_tests_per_trial {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    Summable (fun k : ℕ => d * (1 - d) ^ k * (2 * √k)) ∧
      ∑' k : ℕ, d * (1 - d) ^ k * (2 * √k) ≤ 2 / √d := by
  have hsd : 0 < √d := sqrt_pos.2 hd
  have hG := geometric_mean hd hd1
  have hgeo : HasSum (fun k : ℕ => d * (1 - d) ^ k) 1 := by
    have h := (hasSum_geometric_of_lt_one (r := 1 - d) (by linarith) (by linarith)).mul_left d
    convert h using 1
    rw [sub_sub_cancel]; field_simp
  -- `2√k ≤ √d k + 1/√d`
  have hpt : ∀ k : ℕ, d * (1 - d) ^ k * (2 * √k)
      ≤ √d * ((k : ℝ) * (d * (1 - d) ^ k)) + (1 / √d) * (d * (1 - d) ^ k) := by
    intro k
    have h1d : 0 ≤ 1 - d := by linarith
    have hw : 0 ≤ d * (1 - d) ^ k := by positivity
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hsk : √(k : ℝ) ^ 2 = k := sq_sqrt hk
    have hamgm : 2 * √(k : ℝ) ≤ √d * k + 1 / √d := by
      rw [← sub_nonneg]
      have : √d * k + 1 / √d - 2 * √(k : ℝ) = (√d * √(k : ℝ) - 1) ^ 2 / √d := by
        field_simp
        linear_combination (-(√d ^ 2)) * hsk
      rw [this]; positivity
    nlinarith
  have hR : HasSum (fun k : ℕ => √d * ((k : ℝ) * (d * (1 - d) ^ k))
      + (1 / √d) * (d * (1 - d) ^ k)) (√d * ((1 - d) / d) + (1 / √d) * 1) :=
    (hG.mul_left _).add (hgeo.mul_left _)
  have hnn : ∀ k : ℕ, 0 ≤ d * (1 - d) ^ k * (2 * √k) := by
    intro k; have : 0 ≤ 1 - d := by linarith
    positivity
  have hS : Summable (fun k : ℕ => d * (1 - d) ^ k * (2 * √k)) :=
    Summable.of_nonneg_of_le hnn hpt hR.summable
  refine ⟨hS, ?_⟩
  calc ∑' k : ℕ, d * (1 - d) ^ k * (2 * √k) ≤ √d * ((1 - d) / d) + (1 / √d) * 1 :=
        hasSum_le hpt hS.hasSum hR
    _ = (2 - d) / √d := by
        field_simp; rw [sq_sqrt hd.le]; ring
    _ ≤ 2 / √d := by
        apply div_le_div_of_nonneg_right _ hsd.le; linarith

/-- Dividing the per-trial count `2/√d` by the success probability `√d` gives `2/d`.
Paper: proof of `lem:rmshalfnb` (normalization_floor.tex). -/
theorem expected_tests_total {d : ℝ} (hd : 0 < d) : (2 / √d) / √d = 2 / d := by
  have hsd : 0 < √d := sqrt_pos.2 hd
  field_simp
  rw [sq_sqrt hd.le]

/-- `sinh x ≤ x cosh x` for `x ≥ 0`, by comparing the two power series termwise. -/
theorem sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) : sinh x ≤ x * cosh x := by
  have h1 := Real.hasSum_sinh x
  have h2 := (Real.hasSum_cosh x).mul_left x
  refine hasSum_le (fun n => ?_) h1 h2
  have hf : ((2 * n).factorial : ℝ) ≤ ((2 * n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hf0 : (0 : ℝ) < ((2 * n).factorial : ℝ) := by positivity
  calc x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)
      = x * (x ^ (2 * n) / ((2 * n + 1).factorial : ℝ)) := by rw [pow_succ]; ring
    _ ≤ x * (x ^ (2 * n) / ((2 * n).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) hf0 hf) hx

/-- The geometric interval masses: with `L = -log(1-d) > 0`, the probability that `X/L` lies
within `e` of the positive integer `k`, for `X` exponential, is at most
`e^{-L(k-e)} - e^{-L(k+e)}`, and these masses sum to `2 sinh(eL)/(e^L - 1)`.
Paper: proof of `lem:rmshalfnb` (normalization_floor.tex), geometric inversion. -/
theorem interval_masses {L e : ℝ} (hL : 0 < L) :
    HasSum (fun k : ℕ => exp (-L * ((k + 1 : ℕ) - e)) - exp (-L * ((k + 1 : ℕ) + e)))
      (2 * sinh (e * L) / (exp L - 1)) := by
  have hq : exp (-L) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hgeo := hasSum_geometric_of_lt_one (exp_pos (-L)).le hq
  have hfun : ∀ k : ℕ, exp (-L * ((k + 1 : ℕ) - e)) - exp (-L * ((k + 1 : ℕ) + e))
      = (exp (-L) * 2 * sinh (e * L)) * exp (-L) ^ k := by
    intro k
    rw [sinh_eq, ← exp_nat_mul]
    have h1 : exp (-L * ((k + 1 : ℕ) - e)) = exp (-L) * exp (↑k * -L) * exp (e * L) := by
      rw [← exp_add, ← exp_add]; push_cast; ring_nf
    have h2 : exp (-L * ((k + 1 : ℕ) + e)) = exp (-L) * exp (↑k * -L) * exp (-(e * L)) := by
      rw [← exp_add, ← exp_add]; push_cast; ring_nf
    rw [h1, h2]; ring
  simp only [hfun]
  have h := hgeo.mul_left (exp (-L) * 2 * sinh (e * L))
  convert h using 1
  have hE : exp L - 1 ≠ 0 := by
    have : 1 < exp L := by rw [Real.one_lt_exp_iff]; exact hL
    linarith
  have hEm : exp (-L) * exp L = 1 := by rw [← exp_add]; simp
  have h1q : 1 - exp (-L) ≠ 0 := by linarith
  field_simp
  rw [show exp L - 1 = exp L * (1 - exp (-L)) by
    rw [mul_sub, mul_one, mul_comm, hEm]]
  field_simp
  linear_combination (-sinh (e * L)) * hEm

/-- The interval masses are at most `6e` when `0 ≤ e` and `e L ≤ 1`.
Paper: proof of `lem:rmshalfnb` (normalization_floor.tex). -/
theorem interval_masses_le {L e : ℝ} (hL : 0 < L) (he : 0 ≤ e) (heL : e * L ≤ 1) :
    2 * sinh (e * L) / (exp L - 1) ≤ 6 * e := by
  have hx : 0 ≤ e * L := mul_nonneg he hL.le
  have hE : L ≤ exp L - 1 := by linarith [add_one_le_exp L]
  have hEpos : 0 < exp L - 1 := by linarith
  have hs := sinh_le_mul_cosh hx
  have hc : cosh (e * L) ≤ cosh 1 := cosh_le_cosh.2 (by
    rw [abs_of_nonneg hx, abs_one]; exact heL)
  have hc1 : cosh (1 : ℝ) < 2 := by
    rw [cosh_eq]
    have h1 := exp_one_lt_d9
    have h2 : exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    norm_num at h1 ⊢; linarith
  rw [div_le_iff₀ hEpos]
  have : sinh (e * L) ≤ 2 * (e * L) := by nlinarith [cosh_pos (e * L)]
  nlinarith

/-! ## Stage estimates for Huber's factory (`lem:general-linear-bits`) -/

/-- `exp(-46/25) < 1/6`.
Paper: proof of `lem:general-linear-bits` (normalization_floor.tex). -/
theorem exp_neg_46_25_lt : exp (-(46 / 25 : ℝ)) < 1 / 6 := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 46 / 25 by norm_num) 6
  have hsum : ∑ i ∈ range 6, (46 / 25 : ℝ) ^ i / (i.factorial : ℝ) > 6 := by
    simp [sum_range_succ, Nat.factorial]
    norm_num
  have hpos := exp_pos (46 / 25 : ℝ)
  rw [exp_neg, inv_lt_comm₀ hpos (by norm_num)]
  norm_num
  linarith

/-- `log(1+x) ≥ x - x²/2` for `x ≥ 0`. -/
theorem log_one_add_ge {x : ℝ} (hx : 0 ≤ x) : x - x ^ 2 / 2 ≤ log (1 + x) := by
  let f : ℝ → ℝ := fun t => log (1 + t) - t + t ^ 2 / 2
  have hd : ∀ t, 0 ≤ t → HasDerivAt f (1 / (1 + t) - 1 + t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 t := by
      simpa using (hasDerivAt_id t).const_add 1
    have h3 := ((h1.log (by linarith)).sub (hasDerivAt_id t)).add
      ((hasDerivAt_pow 2 t).div_const 2)
    convert h3 using 1
    · funext y; simp [f]
    · norm_num
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hd t (le_of_lt ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hd t (le_of_lt ht)).deriv]
      have ht' : (0 : ℝ) < t := ht
      have : 1 / (1 + t) - 1 + t = t ^ 2 / (1 + t) := by field_simp; ring
      rw [this]; positivity
  have := hmono Set.self_mem_Ici hx hx
  simp [f] at this
  linarith

/-- The continuation probability at an upper exit: if `0 < e ≤ 1/2` and the counter is at
least `k = (23/5)/e`, then `(1 + e/2)^{-i} ≤ exp(-46/25) < 1/6`.
Paper: proof of `lem:general-linear-bits` (normalization_floor.tex). -/
theorem continuation_le {e : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 2) {i : ℕ}
    (hi : 23 / 5 / e ≤ i) : ((1 + e / 2)⁻¹) ^ i ≤ exp (-(46 / 25 : ℝ)) ∧
      ((1 + e / 2)⁻¹) ^ i < 1 / 6 := by
  have hpos : 0 < 1 + e / 2 := by linarith
  have hlog : 2 * e / 5 ≤ log (1 + e / 2) := by
    have := log_one_add_ge (x := e / 2) (by linarith)
    nlinarith
  have hrw : ((1 + e / 2)⁻¹) ^ i = exp (-(i * log (1 + e / 2))) := by
    rw [inv_pow, ← exp_log (pow_pos hpos i), ← exp_neg, log_pow]
  have hkey : (46 / 25 : ℝ) ≤ i * log (1 + e / 2) := by
    have h1 : (23 / 5 / e) * (2 * e / 5) = 46 / 25 := by field_simp; ring
    have h2 : (0 : ℝ) ≤ 2 * e / 5 := by positivity
    calc (46 / 25 : ℝ) = (23 / 5 / e) * (2 * e / 5) := h1.symm
      _ ≤ i * (2 * e / 5) := mul_le_mul_of_nonneg_right hi h2
      _ ≤ i * log (1 + e / 2) := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg i)
  have hle : ((1 + e / 2)⁻¹) ^ i ≤ exp (-(46 / 25 : ℝ)) := by
    rw [hrw]; exact exp_le_exp.2 (by linarith)
  exact ⟨hle, lt_of_le_of_lt hle exp_neg_46_25_lt⟩

/-- Reaching stage `j` requires `j` successful continuations, each of probability below `1/6`.
Paper: proof of `lem:general-linear-bits` (normalization_floor.tex), the reach bound `6^{-j}`. -/
theorem stage_reach (j : ℕ) (p : ℕ → ℝ) (hp0 : ∀ r, 0 ≤ p r) (hp : ∀ r, p r ≤ 1 / 6) :
    ∏ r ∈ range j, p r ≤ (1 / 6) ^ j := by
  calc ∏ r ∈ range j, p r ≤ ∏ _r ∈ range j, (1 / 6 : ℝ) :=
        prod_le_prod₀ (fun r _ => hp0 r) (fun r _ => hp r)
    _ = (1 / 6) ^ j := by rw [prod_const, card_range]

/-- The stage multipliers stay below `2C`: `C ∏_{r<j} (1 + e_r/2) < 2C` with `e_r = 2^{-r} e`
and `0 < e ≤ 1/2`.
Paper: proof of `lem:general-linear-bits` (normalization_floor.tex). -/
theorem stage_multiplier_lt {C e : ℝ} (hC : 0 < C) (he : 0 < e) (he1 : e ≤ 1 / 2) (j : ℕ) :
    C * ∏ r ∈ range j, (1 + (e / 2 ^ r) / 2) < 2 * C := by
  have hprod : ∏ r ∈ range j, (1 + (e / 2 ^ r) / 2) ≤ exp (∑ r ∈ range j, (e / 2 ^ r) / 2) := by
    rw [exp_sum]
    apply prod_le_prod₀ (fun r _ => by positivity) (fun r _ => by
      have := add_one_le_exp ((e / 2 ^ r) / 2); linarith)
  have hsum : ∑ r ∈ range j, (e / 2 ^ r) / 2 ≤ e := by
    have : ∑ r ∈ range j, (e / 2 ^ r) / 2 = e / 2 * ∑ r ∈ range j, (1 / 2 : ℝ) ^ r := by
      rw [mul_sum]; apply sum_congr rfl; intro r _; rw [one_div_pow]; ring
    rw [this]
    have hg : ∑ r ∈ range j, (1 / 2 : ℝ) ^ r ≤ 2 := by
      have := sum_geometric_two_le j
      simpa using this
    nlinarith
  have hexp : exp e < 2 := by
    have h1 : exp e ≤ exp (1 / 2) := exp_le_exp.2 he1
    have h2 : exp (1 / 2 : ℝ) < 2 := by
      have h := Real.add_one_lt_exp (show (-(1 / 2 : ℝ)) ≠ 0 by norm_num)
      have hpos := exp_pos (1 / 2 : ℝ)
      have hmul : exp (-(1 / 2)) * exp (1 / 2) = 1 := by rw [← exp_add]; simp
      nlinarith
    linarith
  have := lt_of_le_of_lt (le_trans hprod (exp_le_exp.2 hsum)) hexp
  nlinarith

/-- The arithmetic inequality behind the stopped-drift count of one stage: with
`1 ≤ C_j < 2C`, `0 < e_j ≤ 1/2` and the threshold `k_j = (23/5)/e_j`,
`((C_j - 1)⌈k_j⌉ + C_j)/e_j ≤ 14 C e_j^{-2}`. The stopped-drift bound itself is not
formalized.
Paper: proof of `lem:general-linear-bits` (normalization_floor.tex). -/
theorem stage_update_bound {C Cj ej : ℝ} (hCj1 : 1 ≤ Cj) (hCj : Cj < 2 * C) (he : 0 < ej)
    (he1 : ej ≤ 1 / 2) :
    ((Cj - 1) * ⌈23 / 5 / ej⌉ + Cj) / ej ≤ 14 * C / ej ^ 2 := by
  have hk : (⌈23 / 5 / ej⌉ : ℝ) ≤ 23 / 5 / ej + 1 := by
    have := Int.ceil_lt_add_one (23 / 5 / ej); linarith
  have h1e : 2 ≤ 1 / ej := by rw [le_div_iff₀ he]; linarith
  have hnum : (Cj - 1) * ⌈23 / 5 / ej⌉ + Cj ≤ Cj * (23 / 5 / ej + 2) := by
    have h0 : 0 ≤ Cj - 1 := by linarith
    have h1 := mul_le_mul_of_nonneg_left hk h0
    have h2 : 0 ≤ 23 / 5 / ej := by positivity
    nlinarith
  have hC : 0 < C := by linarith
  have hbound : Cj * (23 / 5 / ej + 2) ≤ 2 * C * (28 / 5 / ej) := by
    have h2 : 23 / 5 / ej + 2 ≤ 28 / 5 / ej := by
      have : 28 / 5 / ej = 23 / 5 / ej + 1 / ej := by ring
      linarith
    have hpos : 0 ≤ 23 / 5 / ej + 2 := by positivity
    calc Cj * (23 / 5 / ej + 2) ≤ 2 * C * (23 / 5 / ej + 2) :=
          mul_le_mul_of_nonneg_right hCj.le hpos
      _ ≤ 2 * C * (28 / 5 / ej) := mul_le_mul_of_nonneg_left h2 (by linarith)
  rw [div_le_div_iff₀ he (by positivity)]
  have : 2 * C * (28 / 5 / ej) * ej ^ 2 = 56 / 5 * C * ej := by field_simp; ring
  nlinarith

/-! ## Rational output radius -/

/-- For every `x > 0` there is a power of two `2^k` with `x ≤ 2^k < 2x`.
Paper: `thm:rmsfloor` (normalization_floor.tex), the rational radius `R̄`. -/
theorem exists_pow_two_mem {x : ℝ} (hx : 0 < x) :
    ∃ k : ℤ, x ≤ (2 : ℝ) ^ k ∧ (2 : ℝ) ^ k < 2 * x := by
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hx (by norm_num : (1 : ℝ) < 2)
  refine ⟨n + 1, hn2, ?_⟩
  rw [zpow_add_one₀ (by norm_num)]
  linarith

/-- Thinning to a rational radius `R̄` with `R_out ≤ R̄ < 2 R_out`: open a gate of probability
`R_out/R̄ ∈ (1/2, 1]` and return a fair sign otherwise. The mean becomes `𝒩/R̄`.
Paper: `thm:rmsfloor` (normalization_floor.tex), the paragraph on recursive composition. -/
theorem radius_thinning {Rout Rbar N : ℝ} (hR : 0 < Rout) (h1 : Rout ≤ Rbar)
    (h2 : Rbar < 2 * Rout) :
    (Rout / Rbar) * (N / Rout) + (1 - Rout / Rbar) * 0 = N / Rbar ∧
      1 / 2 < Rout / Rbar ∧ Rout / Rbar ≤ 1 := by
  have hb : 0 < Rbar := lt_of_lt_of_le hR h1
  refine ⟨by rw [mul_zero, add_zero]; field_simp, ?_, (div_le_one hb).2 h1⟩
  rw [lt_div_iff₀ hb]; linarith

end ExactSampling.RMSFloor
