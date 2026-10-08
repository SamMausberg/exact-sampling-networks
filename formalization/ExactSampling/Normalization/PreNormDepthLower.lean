import Mathlib

/-!
# Additive pre-norm blocks can reveal a majority

This module formalizes the quantitative content of `thm:pn-absolute-lower` and
`cor:pn-fresh-query` (normalization_depth_lower.tex, `sec:pn-depth-lower`).

Formalized here:
* the network bookkeeping: the first denominator `√(3 + 1) = 2`, the attention residual that
  writes the prefix mean `M_t` into coordinate two, the fresh-query value map `2(J_n - I_n)`
  with row norm `4(1 - 1/n) < 4` and residual `M·1`, and the squared denominators `11/3 + F²/3`
  and `3 + F²`;
* the scalar recurrences `F_{r+1} = F_r + tanh(F_r/√(A + BF_r²))` with `(A, B) = (11/3, 1/3)` and
  `(3, 1)`: the increment is at least `y/4` for `0 ≤ y ≤ 1` and at least `1/4` for `y ≥ 1`;
  oddness; `|F_d| ≤ 1 + d`; the growth `F_d(z) ≥ d/8` for `z ≥ 1/(2√T)` with
  `k = ⌈log_{5/4}(2√T)⌉` and `d = 2^{⌈log₂(2k)⌉} ∈ [2k, 4k)`;
* the readout `g = tanh(F_d/(2d)) ≥ 1/32` above the threshold, with logits in `[-1, 1]`;
* the second-moment inequality (Paley–Zygmund) for finite laws, giving
  `Pr{|M| ≥ 1/(2√T)} ≥ 3/16` from `𝔼M² = 1/T` and `𝔼M⁴ ≤ 3/T²`;
* the score `H'(0) ≥ 3√T/1024` and the bound `𝔼Q ≥ 9T/2^20 ≥ T/2^17`;
* the moments `𝔼M² = 1/T`, `𝔼M⁴ = (3T-2)/T³ ≤ 3/T²` of the average `M` of `T` fair signs, and
  the resulting bound for that context law (`absolute_lower_rademacher`).

Stand-in hypothesis: the transcript inequality of `lem:transcript` (tanh_lower.tex), as the
hypothesis `Q ≥ (T 𝔼₀[M g(M)])²`; the derivative identity `H'(0) = T 𝔼₀[M g(M)]` is proved in
`ExactSampling.RMSContextLaw.hasDerivAt_signMean`.

Not formalized: the transformer block at the vector level beyond the displayed coordinate
identities, the query model and preprocessing, and the dyadic encoding of the readout.
-/

open Real Finset
open scoped BigOperators

namespace ExactSampling.PreNormDepthLower

/-! ## Elementary bounds for `tanh` -/

/-- `tanh` is nonnegative on `[0, ∞)`. -/
theorem tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ tanh x := by
  rw [tanh_eq_sinh_div_cosh]; exact div_nonneg (sinh_nonneg_iff.2 hx) (cosh_pos x).le

/-- `tanh y ≥ y/√(1+y²)` for `y ≥ 0`. -/
theorem div_sqrt_le_tanh {y : ℝ} (hy : 0 ≤ y) : y / √(1 + y ^ 2) ≤ tanh y := by
  rw [tanh_eq_sinh_div_cosh]
  have hs : y ≤ sinh y := self_le_sinh_iff.2 hy
  have hc : cosh y = √(1 + sinh y ^ 2) := by
    rw [← cosh_sq', sqrt_sq (cosh_pos y).le]
  have hS : 0 < √(1 + y ^ 2) := sqrt_pos.2 (by positivity)
  rw [div_le_div_iff₀ hS (cosh_pos y), hc]
  have h1 : y * √(1 + sinh y ^ 2) = √((y * √(1 + sinh y ^ 2)) ^ 2) :=
    (sqrt_sq (by positivity)).symm
  have h2 : sinh y * √(1 + y ^ 2) = √((sinh y * √(1 + y ^ 2)) ^ 2) :=
    (sqrt_sq (mul_nonneg (by linarith) hS.le)).symm
  rw [h1, h2]
  apply sqrt_le_sqrt
  rw [mul_pow, mul_pow, sq_sqrt (by positivity), sq_sqrt (by positivity)]
  nlinarith [mul_le_mul hs hs hy (by linarith : 0 ≤ sinh y)]

/-- `tanh v ≥ v/2` for `0 ≤ v ≤ 1`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem half_le_tanh {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : u / 2 ≤ tanh u := by
  refine le_trans ?_ (div_sqrt_le_tanh h0)
  have hS : 0 < √(1 + u ^ 2) := sqrt_pos.2 (by positivity)
  have hS2 : √(1 + u ^ 2) ≤ 2 := by
    rw [sqrt_le_left (by norm_num)]; nlinarith
  exact div_le_div_of_nonneg_left h0 hS hS2

/-- `tanh` is monotone. -/
theorem tanh_mono {a b : ℝ} (h : a ≤ b) : tanh a ≤ tanh b := by
  have e : tanh b - tanh a = sinh (b - a) / (cosh a * cosh b) := by
    rw [tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh, sinh_sub]
    have ha := (cosh_pos a).ne'
    have hb := (cosh_pos b).ne'
    field_simp
  have h1 : 0 ≤ sinh (b - a) := sinh_nonneg_iff.2 (by linarith)
  have h2 : 0 < cosh a * cosh b := mul_pos (cosh_pos a) (cosh_pos b)
  have : 0 ≤ tanh b - tanh a := by rw [e]; exact div_nonneg h1 h2.le
  linarith

/-! ## Network bookkeeping -/

/-- With width three, stabilizer three and all coordinates of magnitude one, the first
normalization denominator is `√(3 + 1) = 2`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem initial_denominator : √((3 : ℝ) + 1) = 2 := by
  rw [show (3 : ℝ) + 1 = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]

/-- The public-coordinate construction cancels exactly: `1 + (2M - 2)/2 = M`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem context_mean_collapse (mean : ℝ) : 1 + (2 * mean - 2) / 2 = mean := by
  ring

/-- The attention residual of the first block: uniform attention over the normalized tokens
`(x_j/2, 1/2, -1/2)` with value row `(2, -2, 0)` adds `M_t - 1` to the second coordinate, which
becomes the prefix mean `M_t`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem attention_residual {t : ℕ} (ht : 0 < t) (x : Fin t → ℝ) :
    1 + (1 / (t : ℝ)) * ∑ j, (2 * (x j / 2) - 2 * (1 / 2)) = (1 / (t : ℝ)) * ∑ j, x j := by
  have ht' : (t : ℝ) ≠ 0 := by positivity
  simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The first additive residual in the fresh-query family: `x + 2((M - x)/2) = M`.
Paper: proof of `cor:pn-fresh-query` (normalization_depth_lower.tex). -/
theorem mean_collapse_coordinate (x mean : ℝ) : x + 2 * ((mean - x) / 2) = mean := by
  ring

/-- The value map `V = 2(J_n - I_n)` applied to the normalized query `x/2` gives
`M - x_i`, so the residual is `M` in every coordinate.
Paper: proof of `cor:pn-fresh-query` (normalization_depth_lower.tex). -/
theorem fresh_value_map {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (i : Fin n) :
    x i + ∑ k, 2 * ((1 / (n : ℝ)) - if k = i then 1 else 0) * (x k / 2)
      = (1 / (n : ℝ)) * ∑ k, x k := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have e : ∀ k, 2 * ((1 / (n : ℝ)) - if k = i then 1 else 0) * (x k / 2)
      = (1 / (n : ℝ)) * x k - (if k = i then x k else 0) := by
    intro k; split_ifs <;> ring
  rw [sum_congr rfl (fun k _ => e k), sum_sub_distrib, ← mul_sum, sum_ite_eq']
  simp only [mem_univ, ite_true]
  ring

/-- The rows of `V = 2(J_n - I_n)` have `ℓ₁` norm `4(1 - 1/n) < 4`.
Paper: proof of `cor:pn-fresh-query` (normalization_depth_lower.tex). -/
theorem fresh_row_norm {n : ℕ} (hn : 0 < n) (i : Fin n) :
    ∑ k, |2 * ((1 / (n : ℝ)) - if k = i then 1 else 0)| = 4 * (1 - 1 / n) ∧
      4 * (1 - 1 / (n : ℝ)) < 4 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hle : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hn']; exact hn1
  have e : ∀ k, |2 * ((1 / (n : ℝ)) - if k = i then 1 else 0)|
      = 2 / (n : ℝ) + (if k = i then (2 : ℝ) - 4 / n else 0) := by
    intro k
    split_ifs with h
    · rw [abs_of_nonpos (by linarith)]; ring
    · rw [sub_zero, abs_of_nonneg (by positivity)]; ring
  constructor
  · rw [sum_congr rfl (fun k _ => e k), sum_add_distrib, sum_ite_eq']
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mem_univ, ite_true]
    field_simp
    ring
  · have : 0 < 1 / (n : ℝ) := by positivity
    linarith

/-- The squared denominators: `3 + (x² + F² + 1)/3 = 11/3 + F²/3` for a sign `x`, and
`3 + F²` when every coordinate equals `F`.
Paper: proofs of `thm:pn-absolute-lower` and `cor:pn-fresh-query`
(normalization_depth_lower.tex). -/
theorem recurrence_denominators (x F : ℝ) (hx : x ^ 2 = 1) {n : ℕ} (hn : 0 < n) :
    3 + (x ^ 2 + F ^ 2 + (-1) ^ 2) / 3 = 11 / 3 + F ^ 2 / 3 ∧
      3 + (1 / (n : ℝ)) * ∑ _i : Fin n, F ^ 2 = 3 + F ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  refine ⟨by rw [hx]; ring, ?_⟩
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-! ## The scalar recurrences -/

/-- The recurrence `F_{r+1} = F_r + tanh(F_r/√(A + B F_r²))`; `(A, B) = (11/3, 1/3)` in
`thm:pn-absolute-lower` and `(3, 1)` in `cor:pn-fresh-query`.
Paper: proofs of `thm:pn-absolute-lower` and `cor:pn-fresh-query`
(normalization_depth_lower.tex). -/
noncomputable def recF (A B : ℝ) : ℕ → ℝ → ℝ
  | 0, z => z
  | r + 1, z => recF A B r z + tanh (recF A B r z / √(A + B * recF A B r z ^ 2))

/-- The recurrence is odd in `z`. -/
theorem recF_neg (A B : ℝ) (r : ℕ) (z : ℝ) : recF A B r (-z) = -recF A B r z := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [recF, ih, neg_sq]
    rw [neg_div, Real.tanh_neg]; ring

/-- The increment bound: if `1 ≤ A`, `0 ≤ B` and `A + B ≤ 4`, then for `y ≥ 0` the increment
`tanh(y/√(A + By²))` is at least `y/4` when `y ≤ 1` and at least `1/4` when `y ≥ 1`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem increment_ge {A B y : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) (hAB : A + B ≤ 4) (hy : 0 ≤ y) :
    min y 1 / 4 ≤ tanh (y / √(A + B * y ^ 2)) := by
  have hD : 0 < A + B * y ^ 2 := by positivity
  have hs : 0 < √(A + B * y ^ 2) := sqrt_pos.2 hD
  rcases le_total y 1 with h | h
  · rw [min_eq_left h]
    have harg1 : y / √(A + B * y ^ 2) ≤ 1 := by
      rw [div_le_one hs]
      have : 1 ≤ √(A + B * y ^ 2) := by
        have := sqrt_le_sqrt (show (1 : ℝ) ≤ A + B * y ^ 2 by nlinarith)
        rwa [sqrt_one] at this
      linarith
    have harg2 : y / 2 ≤ y / √(A + B * y ^ 2) := by
      apply div_le_div_of_nonneg_left hy hs
      rw [sqrt_le_left (by norm_num)]
      have := mul_le_mul_of_nonneg_left (show y ^ 2 ≤ 1 by nlinarith) hB
      nlinarith
    have := half_le_tanh (div_nonneg hy hs.le) harg1
    linarith
  · rw [min_eq_right h]
    have harg : 1 / 2 ≤ y / √(A + B * y ^ 2) := by
      rw [le_div_iff₀ hs]
      have : √(A + B * y ^ 2) ≤ 2 * y := by
        rw [sqrt_le_left (by linarith)]
        have := mul_le_mul_of_nonneg_left (show 1 ≤ y ^ 2 by nlinarith)
          (show (0 : ℝ) ≤ 4 - B by linarith)
        nlinarith
      linarith
    have h1 := half_le_tanh (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    have h2 := tanh_mono harg
    linarith

/-- `F_r` is nondecreasing in `r` for `z ≥ 0` and satisfies
`F_{r+1} ≥ F_r + min{F_r, 1}/4`. -/
theorem recF_step {A B : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) (hAB : A + B ≤ 4) {z : ℝ} (hz : 0 ≤ z)
    (r : ℕ) : 0 ≤ recF A B r z ∧
      recF A B r z + min (recF A B r z) 1 / 4 ≤ recF A B (r + 1) z := by
  have h0 : 0 ≤ recF A B r z := by
    induction r with
    | zero => exact hz
    | succ r ih =>
      simp only [recF]
      have := increment_ge hA hB hAB ih
      have : 0 ≤ min (recF A B r z) 1 := le_min ih zero_le_one
      linarith
  refine ⟨h0, ?_⟩
  simp only [recF]
  have := increment_ge hA hB hAB h0
  linarith

/-- The geometric phase: `F_r ≥ min{1, (5/4)^r z}`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem recF_geometric {A B : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) (hAB : A + B ≤ 4) {z : ℝ}
    (hz : 0 ≤ z) (r : ℕ) : min 1 ((5 / 4 : ℝ) ^ r * z) ≤ recF A B r z := by
  induction r with
  | zero => simp [recF]
  | succ r ih =>
    obtain ⟨h0, h1⟩ := recF_step hA hB hAB hz r
    rcases le_total 1 (recF A B r z) with h | h
    · rw [min_eq_right h] at h1
      have := min_le_left 1 ((5 / 4 : ℝ) ^ (r + 1) * z)
      linarith
    · rw [min_eq_left h] at h1
      have hm : min 1 ((5 / 4 : ℝ) ^ (r + 1) * z) ≤ 5 / 4 * min 1 ((5 / 4 : ℝ) ^ r * z) := by
        rcases le_total 1 ((5 / 4 : ℝ) ^ r * z) with h' | h'
        · rw [min_eq_left h']; have := min_le_left 1 ((5 / 4 : ℝ) ^ (r + 1) * z); linarith
        · rw [min_eq_right h', pow_succ]
          have := min_le_right 1 ((5 / 4 : ℝ) ^ r * (5 / 4) * z); linarith
      linarith

/-- The linear phase: once `F_k ≥ 1`, `F_{k+j} ≥ 1 + j/4`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem recF_linear {A B : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) (hAB : A + B ≤ 4) {z : ℝ}
    (hz : 0 ≤ z) {k : ℕ} (hk : 1 ≤ recF A B k z) (j : ℕ) : 1 + j / 4 ≤ recF A B (k + j) z := by
  induction j with
  | zero => simpa using hk
  | succ j ih =>
    obtain ⟨_, h1⟩ := recF_step hA hB hAB hz (k + j)
    have hge : 1 ≤ recF A B (k + j) z := by
      have : (0 : ℝ) ≤ j / 4 := by positivity
      linarith
    rw [min_eq_right hge] at h1
    rw [← add_assoc]
    push_cast
    linarith

/-- Crossing by half the horizon leaves a linear amplification interval:
`(d - k)/4 ≥ d/8` when `2k ≤ d`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem remaining_steps (d k : ℝ) (hd : 2 * k ≤ d) : (d - k) / 4 ≥ d / 8 := by
  linarith

/-- **The growth of the recurrence.** If `(5/4)^k z ≥ 1`, `z ≥ 0`, and `d ≥ 2k`, then
`F_d(z) ≥ d/8`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem recF_ge_d8 {A B : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) (hAB : A + B ≤ 4) {z : ℝ} (hz : 0 ≤ z)
    {k d : ℕ} (hk : 1 ≤ (5 / 4 : ℝ) ^ k * z) (hd : 2 * k ≤ d) : (d : ℝ) / 8 ≤ recF A B d z := by
  have h1 : 1 ≤ recF A B k z := by
    have := recF_geometric hA hB hAB hz k
    rw [min_eq_left hk] at this; exact this
  obtain ⟨j, rfl⟩ : ∃ j, d = k + j := ⟨d - k, by omega⟩
  have h2 := recF_linear hA hB hAB hz h1 j
  have hkj : (2 * k : ℝ) ≤ k + j := by exact_mod_cast hd
  push_cast
  have := remaining_steps ((k : ℝ) + j) k hkj
  linarith

/-- The trivial upper bound `|F_d(z)| ≤ 1 + d ≤ 2d` for `|z| ≤ 1`, `d ≥ 1`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem recF_abs_le (A B : ℝ) {z : ℝ} (hz : |z| ≤ 1) (d : ℕ) : |recF A B d z| ≤ 1 + d := by
  induction d with
  | zero => simpa [recF] using hz
  | succ d ih =>
    simp only [recF]
    have h := abs_le.2 ⟨(Real.neg_one_lt_tanh (recF A B d z / √(A + B * recF A B d z ^ 2))).le,
      (Real.tanh_lt_one _).le⟩
    calc |recF A B d z + tanh (recF A B d z / √(A + B * recF A B d z ^ 2))|
        ≤ |recF A B d z| + |tanh (recF A B d z / √(A + B * recF A B d z ^ 2))| :=
          abs_add_le _ _
      _ ≤ 1 + d + 1 := add_le_add ih h
      _ = 1 + ((d + 1 : ℕ) : ℝ) := by push_cast; ring

/-- The number of geometric steps: `k = ⌈log_{5/4} x⌉` satisfies `(5/4)^k ≥ x` for `x > 0`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem geometric_steps {x : ℝ} (hx : 0 < x) : x ≤ (5 / 4 : ℝ) ^ ⌈logb (5 / 4) x⌉₊ := by
  have h1 : logb (5 / 4) x ≤ (⌈logb (5 / 4) x⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (5 / 4 : ℝ) ^ logb (5 / 4) x = x := rpow_logb (by norm_num) (by norm_num) hx
  have h3 : (5 / 4 : ℝ) ^ logb (5 / 4) x ≤ (5 / 4 : ℝ) ^ ((⌈logb (5 / 4) x⌉₊ : ℕ) : ℝ) :=
    rpow_le_rpow_of_exponent_le (by norm_num) h1
  rw [h2, rpow_natCast] at h3
  exact h3

/-- The depth `d = 2^{⌈log₂(2k)⌉}` satisfies `2k ≤ d < 4k` for `k ≥ 1`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem depth_choice {k : ℕ} (hk : 1 ≤ k) :
    2 * k ≤ 2 ^ Nat.clog 2 (2 * k) ∧ 2 ^ Nat.clog 2 (2 * k) < 4 * k := by
  have hle : 2 * k ≤ 2 ^ Nat.clog 2 (2 * k) := Nat.le_pow_clog (by norm_num) _
  have hlt : 2 ^ (Nat.clog 2 (2 * k) - 1) < 2 * k := Nat.pow_pred_clog_lt_self (by norm_num)
    (by omega)
  have hpos : 0 < Nat.clog 2 (2 * k) := Nat.clog_pos (by norm_num) (by omega)
  refine ⟨hle, ?_⟩
  have : 2 ^ Nat.clog 2 (2 * k) = 2 * 2 ^ (Nat.clog 2 (2 * k) - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

/-! ## The readout -/

/-- The output logit stays bounded after the dyadic readout: `|F/(2d)| ≤ 1` when `|F| ≤ 2d`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem bounded_readout (F d : ℝ) (hd : 0 < d) (hF : |F| ≤ 2 * d) : |F / (2 * d)| ≤ 1 := by
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * d)]
  exact (div_le_iff₀ (by positivity : 0 < 2 * d)).2 (by simpa using hF)

/-- Threshold amplitude becomes a constant-sized final logit: `F ≥ d/8` gives `F/(2d) ≥ 1/16`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem threshold_readout (F d : ℝ) (hd : 0 < d) (hF : d / 8 ≤ F) : (1 : ℝ) / 16 ≤ F / (2 * d) := by
  apply (le_div_iff₀ (by positivity : 0 < 2 * d)).2
  linarith

/-- Above the threshold the output-sign mean `tanh(F_d/(2d))` is at least `1/32`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem readout_threshold {F d : ℝ} (hd : 0 < d) (hF : d / 8 ≤ F) (hF2 : F ≤ 2 * d) :
    (1 : ℝ) / 32 ≤ tanh (F / (2 * d)) := by
  have h1 := threshold_readout F d hd hF
  have h2 : F / (2 * d) ≤ 1 := by rw [div_le_one (by positivity)]; exact hF2
  have := half_le_tanh (by linarith) h2
  linarith

/-! ## The score -/

/-- The second-moment (Paley–Zygmund) inequality for a finite law: for `Z ≥ 0`, `0 ≤ θ ≤ 1`,
`Pr{Z ≥ θ𝔼Z} 𝔼Z² ≥ (1-θ)²(𝔼Z)²`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem paley_zygmund {ι : Type*} (S : Finset ι) (p Z : ι → ℝ) (hp : ∀ i ∈ S, 0 ≤ p i)
    (hZ : ∀ i ∈ S, 0 ≤ Z i) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hp1 : ∑ i ∈ S, p i = 1) :
    (1 - θ) ^ 2 * (∑ i ∈ S, p i * Z i) ^ 2
      ≤ (∑ i ∈ S with θ * (∑ j ∈ S, p j * Z j) ≤ Z i, p i) * ∑ i ∈ S, p i * Z i ^ 2 := by
  set E := ∑ i ∈ S, p i * Z i with hE
  have hE0 : 0 ≤ E := sum_nonneg (fun i hi => mul_nonneg (hp i hi) (hZ i hi))
  -- split the mean at the threshold
  have hsplit : E ≤ θ * E + ∑ i ∈ S with θ * E ≤ Z i, p i * Z i := by
    have h := sum_filter_add_sum_filter_not S (fun i => θ * E ≤ Z i) (fun i => p i * Z i)
    have hlow : ∑ i ∈ S with ¬ (θ * E ≤ Z i), p i * Z i
        ≤ ∑ i ∈ S with ¬ (θ * E ≤ Z i), p i * (θ * E) := by
      apply sum_le_sum; intro i hi
      rw [mem_filter] at hi
      exact mul_le_mul_of_nonneg_left (le_of_lt (not_le.1 hi.2)) (hp i hi.1)
    have hlow2 : ∑ i ∈ S with ¬ (θ * E ≤ Z i), p i * (θ * E) ≤ θ * E := by
      rw [← sum_mul]
      have : ∑ i ∈ S with ¬ (θ * E ≤ Z i), p i ≤ 1 := by
        rw [← hp1]
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i hi _ => hp i hi)
      have hθE : 0 ≤ θ * E := mul_nonneg hθ0 hE0
      nlinarith [sum_nonneg (fun i (hi : i ∈ S.filter (fun i => ¬ (θ * E ≤ Z i))) =>
        hp i (mem_filter.1 hi).1)]
    linarith
  -- Cauchy-Schwarz on the upper part
  have hcs : (∑ i ∈ S with θ * E ≤ Z i, p i * Z i) ^ 2
      ≤ (∑ i ∈ S with θ * E ≤ Z i, p i) * ∑ i ∈ S with θ * E ≤ Z i, p i * Z i ^ 2 := by
    have h := sum_mul_sq_le_sq_mul_sq (S.filter (fun i => θ * E ≤ Z i))
      (fun i => √(p i)) (fun i => √(p i) * Z i)
    have e1 : ∀ i ∈ S.filter (fun i => θ * E ≤ Z i), √(p i) * (√(p i) * Z i) = p i * Z i := by
      intro i hi
      rw [← mul_assoc, mul_self_sqrt (hp i (mem_filter.1 hi).1)]
    have e2 : ∀ i ∈ S.filter (fun i => θ * E ≤ Z i), √(p i) ^ 2 = p i := by
      intro i hi; exact sq_sqrt (hp i (mem_filter.1 hi).1)
    have e3 : ∀ i ∈ S.filter (fun i => θ * E ≤ Z i), (√(p i) * Z i) ^ 2 = p i * Z i ^ 2 := by
      intro i hi; rw [mul_pow, sq_sqrt (hp i (mem_filter.1 hi).1)]
    rw [sum_congr rfl e1, sum_congr rfl e2, sum_congr rfl e3] at h
    exact h
  have hsub : ∑ i ∈ S with θ * E ≤ Z i, p i * Z i ^ 2 ≤ ∑ i ∈ S, p i * Z i ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun i hi _ => mul_nonneg (hp i hi) (sq_nonneg _))
  have hP0 : 0 ≤ ∑ i ∈ S with θ * E ≤ Z i, p i :=
    sum_nonneg (fun i hi => hp i (mem_filter.1 hi).1)
  have hupper : (1 - θ) * E ≤ ∑ i ∈ S with θ * E ≤ Z i, p i * Z i := by linarith
  have h0 : 0 ≤ (1 - θ) * E := mul_nonneg (by linarith) hE0
  have hsq := pow_le_pow_left₀ h0 hupper 2
  calc (1 - θ) ^ 2 * E ^ 2 = ((1 - θ) * E) ^ 2 := by ring
    _ ≤ (∑ i ∈ S with θ * E ≤ Z i, p i * Z i) ^ 2 := hsq
    _ ≤ _ := hcs
    _ ≤ _ := mul_le_mul_of_nonneg_left hsub hP0

/-- With `𝔼M² = 1/T` and `𝔼M⁴ ≤ 3/T²`: `Pr{M² ≥ 1/(4T)} ≥ 3/16`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem threshold_probability {ι : Type*} (S : Finset ι) (p M : ι → ℝ) {T : ℝ} (hT : 0 < T)
    (hp : ∀ i ∈ S, 0 ≤ p i) (hp1 : ∑ i ∈ S, p i = 1) (h2 : ∑ i ∈ S, p i * M i ^ 2 = 1 / T)
    (h4 : ∑ i ∈ S, p i * M i ^ 4 ≤ 3 / T ^ 2) :
    3 / 16 ≤ ∑ i ∈ S with 1 / (4 * T) ≤ M i ^ 2, p i := by
  have h := paley_zygmund S p (fun i => M i ^ 2) hp (fun i _ => sq_nonneg _)
    (θ := 1 / 4) (by norm_num) (by norm_num) hp1
  simp only [← pow_mul] at h
  rw [h2] at h
  have e : ∀ i, (1 / 4 * (1 / T) ≤ M i ^ 2) ↔ (1 / (4 * T) ≤ M i ^ 2) := by
    intro i; rw [show 1 / 4 * (1 / T) = 1 / (4 * T) by ring]
  simp only [e] at h
  have h4' : ∑ i ∈ S, p i * M i ^ (2 * 2) ≤ 3 / T ^ 2 := by norm_num; exact h4
  set P := ∑ i ∈ S with 1 / (4 * T) ≤ M i ^ 2, p i
  have hP0 : 0 ≤ P := sum_nonneg (fun i hi => hp i (mem_filter.1 hi).1)
  have := le_trans h (mul_le_mul_of_nonneg_left h4' hP0)
  have hT2 : 0 < T ^ 2 := by positivity
  rw [div_pow, one_pow] at this
  rw [show (1 - 1 / 4 : ℝ) ^ 2 * (1 / T ^ 2) = (9 / 16) / T ^ 2 by ring] at this
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hT2] at this
  linarith

/-- The lower-bound numerical constants: `(3√T/1024)² = 9T/2^20`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem score_constant (N : ℝ) (hN : 0 ≤ N) : (3 * √N / 1024) ^ 2 = 9 * N / (2 : ℝ) ^ 20 := by
  have hs := sq_sqrt hN
  nlinarith

/-- `T/2^17 ≤ 9T/2^20`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem score_constant_relaxation (N : ℝ) (hN : 0 ≤ N) :
    N / (2 : ℝ) ^ 17 ≤ 9 * N / (2 : ℝ) ^ 20 := by
  norm_num
  linarith

/-- **The majority lower bound.** For either recurrence (`(A,B) = (11/3, 1/3)` or `(3, 1)`), let
`k ≥ 1` with `(5/4)^k ≥ 2√T`, let `d ≥ 2k`, and let the output sign have mean
`g(z) = tanh(F_d(z)/(2d))`. For a finite law of `M` with `∑p = 1`, `𝔼M² = 1/T`,
`𝔼M⁴ ≤ 3/T²` and `|M| ≤ 1`, the transcript inequality `Q ≥ (T 𝔼[M g(M)])²` gives
`Q ≥ 9T/2^20 ≥ T/2^17`.
Paper: `thm:pn-absolute-lower` (with `T` context positions) and `cor:pn-fresh-query` (with `n`
query coordinates) (normalization_depth_lower.tex). -/
theorem majority_lower {A B : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) (hAB : A + B ≤ 4) {T : ℝ}
    (hT : 0 < T) {k d : ℕ} (hk : 2 * √T ≤ (5 / 4 : ℝ) ^ k) (hk1 : 1 ≤ k) (hd : 2 * k ≤ d)
    {ι : Type*} (S : Finset ι) (p M : ι → ℝ) {Q : ℝ}
    (hp : ∀ i ∈ S, 0 ≤ p i) (hp1 : ∑ i ∈ S, p i = 1) (h2 : ∑ i ∈ S, p i * M i ^ 2 = 1 / T)
    (h4 : ∑ i ∈ S, p i * M i ^ 4 ≤ 3 / T ^ 2) (hM : ∀ i ∈ S, |M i| ≤ 1)
    (hQ : (T * ∑ i ∈ S, p i * (M i * tanh (recF A B d (M i) / (2 * d)))) ^ 2 ≤ Q) :
    T / (2 : ℝ) ^ 17 ≤ Q := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hsT : 0 < √T := sqrt_pos.2 hT
  set g := fun z => tanh (recF A B d z / (2 * d))
  -- `M g(M) ≥ 0`, and `≥ |M|/32` above the threshold
  have hodd : ∀ z, z * g z = |z| * g |z| := by
    intro z
    rcases le_total 0 z with h | h
    · rw [abs_of_nonneg h]
    · simp only [g]
      rw [abs_of_nonpos h, recF_neg, neg_div, Real.tanh_neg]; ring
  have hnn : ∀ z, 0 ≤ z * g z := by
    intro z
    rw [hodd]
    have h0 := (recF_step hA hB hAB (abs_nonneg z) d).1
    exact mul_nonneg (abs_nonneg z) (tanh_nonneg (div_nonneg h0 (by positivity)))
  have hthr : ∀ z, |z| ≤ 1 → 1 / (4 * T) ≤ z ^ 2 → 1 / (2 * √T) * (1 / 32) ≤ z * g z := by
    intro z hz hz2
    rw [hodd]
    have hz0 : 1 / (2 * √T) ≤ |z| := by
      have : (1 / (2 * √T)) ^ 2 ≤ |z| ^ 2 := by
        rw [div_pow, mul_pow, sq_sqrt hT.le, sq_abs]; linarith
      exact (pow_le_pow_iff_left₀ (by positivity) (abs_nonneg z) (by norm_num)).1 this
    have hk' : 1 ≤ (5 / 4 : ℝ) ^ k * |z| := by
      have := mul_le_mul hk hz0 (by positivity) (by positivity)
      rw [show 2 * √T * (1 / (2 * √T)) = 1 by field_simp] at this
      linarith
    have hF := recF_ge_d8 hA hB hAB (abs_nonneg z) hk' hd
    have hF2 : recF A B d |z| ≤ 2 * d := by
      have := recF_abs_le A B (z := |z|) (by rwa [abs_abs]) d
      have := le_abs_self (recF A B d |z|)
      linarith
    have hg := readout_threshold hd0 hF hF2
    have : 1 / (2 * √T) * (1 / 32) ≤ |z| * (1 / 32) :=
      mul_le_mul_of_nonneg_right hz0 (by norm_num)
    calc 1 / (2 * √T) * (1 / 32) ≤ |z| * (1 / 32) := this
      _ ≤ |z| * g |z| := mul_le_mul_of_nonneg_left hg (abs_nonneg z)
  -- the expectation
  have hprob := threshold_probability S p M hT hp hp1 h2 h4
  have hE : 1 / (2 * √T) * (1 / 32) * (3 / 16) ≤ ∑ i ∈ S, p i * (M i * g (M i)) := by
    have hsplit := sum_filter_add_sum_filter_not S (fun i => 1 / (4 * T) ≤ M i ^ 2)
      (fun i => p i * (M i * g (M i)))
    have hrest : 0 ≤ ∑ i ∈ S with ¬ (1 / (4 * T) ≤ M i ^ 2), p i * (M i * g (M i)) :=
      sum_nonneg (fun i hi => mul_nonneg (hp i (mem_filter.1 hi).1) (hnn _))
    have hmain : 1 / (2 * √T) * (1 / 32) * ∑ i ∈ S with 1 / (4 * T) ≤ M i ^ 2, p i
        ≤ ∑ i ∈ S with 1 / (4 * T) ≤ M i ^ 2, p i * (M i * g (M i)) := by
      rw [mul_sum]
      apply sum_le_sum; intro i hi
      rw [mem_filter] at hi
      have := hthr (M i) (hM i hi.1) hi.2
      calc 1 / (2 * √T) * (1 / 32) * p i = p i * (1 / (2 * √T) * (1 / 32)) := by ring
        _ ≤ p i * (M i * g (M i)) := mul_le_mul_of_nonneg_left this (hp i hi.1)
    have hc : 0 ≤ 1 / (2 * √T) * (1 / 32) := by positivity
    have := mul_le_mul_of_nonneg_left hprob hc
    linarith
  have hH : 3 * √T / 1024 ≤ T * ∑ i ∈ S, p i * (M i * g (M i)) := by
    have e : T * (1 / (2 * √T) * (1 / 32) * (3 / 16)) = 3 * √T / 1024 := by
      have hsq : √T ^ 2 = T := sq_sqrt hT.le
      field_simp
      linear_combination (-1024 : ℝ) * hsq
    rw [← e]
    exact mul_le_mul_of_nonneg_left hE hT.le
  have hsq := pow_le_pow_left₀ (by positivity) hH 2
  rw [score_constant T hT.le] at hsq
  have := score_constant_relaxation T hT.le
  linarith

/-- The concrete choices `k = ⌈log_{5/4}(2√T)⌉ ≥ 1` and `d = 2^{⌈log₂(2k)⌉}` satisfy the
hypotheses of `majority_lower` for `T ≥ 1`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem concrete_depth {T : ℝ} (hT : 1 ≤ T) :
    2 * √T ≤ (5 / 4 : ℝ) ^ ⌈logb (5 / 4) (2 * √T)⌉₊ ∧ 1 ≤ ⌈logb (5 / 4) (2 * √T)⌉₊ ∧
      2 * ⌈logb (5 / 4) (2 * √T)⌉₊ ≤ 2 ^ Nat.clog 2 (2 * ⌈logb (5 / 4) (2 * √T)⌉₊) := by
  have hs : 1 ≤ √T := by have := sqrt_le_sqrt hT; rwa [sqrt_one] at this
  have hx : 0 < 2 * √T := by positivity
  have hlog : 0 < logb (5 / 4) (2 * √T) :=
    logb_pos (by norm_num) (by linarith)
  have hk : 1 ≤ ⌈logb (5 / 4) (2 * √T)⌉₊ := Nat.one_le_iff_ne_zero.2
    (by rw [ne_eq, Nat.ceil_eq_zero, not_le]; exact hlog)
  exact ⟨geometric_steps hx, hk, (depth_choice hk).1⟩

/-- **`thm:pn-absolute-lower`.** For the width-three block with `T ≥ 1` positions and the
recurrence `F_{r+1} = F_r + tanh(F_r/√(11/3 + F_r²/3))`, at depth `d = 2^{⌈log₂(2k)⌉}`,
`k = ⌈log_{5/4}(2√T)⌉`, the transcript inequality gives `𝔼Q ≥ T/2^17`. The same statement with
`(A, B) = (3, 1)` and `n` query coordinates is `cor:pn-fresh-query`. The law of `M` is any finite
law with the Rademacher moments; `absolute_lower_rademacher` instantiates it with the average of
`T` fair signs.
Paper: `thm:pn-absolute-lower`, `cor:pn-fresh-query` (normalization_depth_lower.tex). -/
theorem absolute_lower {A B : ℝ} (hAB' : (A = 11 / 3 ∧ B = 1 / 3) ∨ (A = 3 ∧ B = 1)) {T : ℝ}
    (hT : 1 ≤ T) {ι : Type*} (S : Finset ι) (p M : ι → ℝ) {Q : ℝ}
    (hp : ∀ i ∈ S, 0 ≤ p i) (hp1 : ∑ i ∈ S, p i = 1) (h2 : ∑ i ∈ S, p i * M i ^ 2 = 1 / T)
    (h4 : ∑ i ∈ S, p i * M i ^ 4 ≤ 3 / T ^ 2) (hM : ∀ i ∈ S, |M i| ≤ 1)
    (hQ : (T * ∑ i ∈ S, p i * (M i * tanh (recF A B (2 ^ Nat.clog 2 (2 * ⌈logb (5 / 4)
      (2 * √T)⌉₊)) (M i) / (2 * ((2 ^ Nat.clog 2 (2 * ⌈logb (5 / 4) (2 * √T)⌉₊) : ℕ) : ℝ))))) ^ 2
      ≤ Q) :
    T / (2 : ℝ) ^ 17 ≤ Q := by
  obtain ⟨h1, h2', h3⟩ := concrete_depth hT
  have hA : 1 ≤ A ∧ 0 ≤ B ∧ A + B ≤ 4 := by
    rcases hAB' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  exact majority_lower hA.1 hA.2.1 hA.2.2 (by linarith) h1 h2' h3 S p M hp hp1 h2 h4 hM hQ

/-! ## The Rademacher average -/

/-- The sign `±1` of a bit. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The sum of the signs of a vector in `{-1,1}^T`. -/
def sgnSum {T : ℕ} (x : Fin T → Bool) : ℝ := ∑ i, sgn (x i)

/-- Splitting off the first sign of a sign vector.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem sum_cons {T : ℕ} (F : ℝ → ℝ) :
    ∑ x : Fin (T + 1) → Bool, F (sgnSum x)
      = ∑ y : Fin T → Bool, (F (1 + sgnSum y) + F (-1 + sgnSum y)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (T + 1) => Bool)).sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro y _
  simp [sgnSum, Fin.sum_univ_succ, Fin.consEquiv, sgn]

/-- There are `2^T` sign vectors. -/
theorem sum_one_signs (T : ℕ) : ∑ _x : Fin T → Bool, (1 : ℝ) = 2 ^ T := by simp

/-- `∑_x (∑_i x_i)² = T 2^T` over `{-1,1}^T`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem sum_sq_signs (T : ℕ) : ∑ x : Fin T → Bool, sgnSum x ^ 2 = T * 2 ^ T := by
  induction T with
  | zero => simp [sgnSum]
  | succ T ih =>
    rw [sum_cons (fun s => s ^ 2)]
    have : ∀ y : Fin T → Bool, (1 + sgnSum y) ^ 2 + (-1 + sgnSum y) ^ 2
        = 2 * sgnSum y ^ 2 + 2 * 1 := by intro y; ring
    simp only [this, sum_add_distrib, ← mul_sum, ih, sum_one_signs]
    push_cast; ring

/-- `∑_x (∑_i x_i)⁴ = (3T² - 2T) 2^T` over `{-1,1}^T`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem sum_four_signs (T : ℕ) :
    ∑ x : Fin T → Bool, sgnSum x ^ 4 = (3 * T ^ 2 - 2 * T) * 2 ^ T := by
  induction T with
  | zero => simp [sgnSum]
  | succ T ih =>
    rw [sum_cons (fun s => s ^ 4)]
    have : ∀ y : Fin T → Bool, (1 + sgnSum y) ^ 4 + (-1 + sgnSum y) ^ 4
        = 2 * sgnSum y ^ 4 + 12 * sgnSum y ^ 2 + 2 * 1 := by intro y; ring
    simp only [this, sum_add_distrib, ← mul_sum, ih, sum_sq_signs, sum_one_signs]
    push_cast; ring

/-- `|∑_i x_i| ≤ T`.
Paper: proof of `thm:pn-absolute-lower` (normalization_depth_lower.tex). -/
theorem abs_sgnSum_le {T : ℕ} (x : Fin T → Bool) : |sgnSum x| ≤ T := by
  unfold sgnSum
  calc |∑ i, sgn (x i)| ≤ ∑ i, |sgn (x i)| := abs_sum_le_sum_abs _ _
    _ = ∑ _i : Fin T, (1 : ℝ) := by
        apply sum_congr rfl; intro i _; unfold sgn; split_ifs <;> simp
    _ = T := by simp

/-- **`thm:pn-absolute-lower` for fair context signs.** With `T ≥ 1` independent fair context
signs, `M = T⁻¹ ∑ x_i` has `𝔼M² = 1/T`, `𝔼M⁴ = (3T-2)/T³ ≤ 3/T²` and `|M| ≤ 1`, so the
transcript inequality `Q ≥ (T 𝔼₀[M g(M)])²` gives `Q ≥ T/2^17`.
Paper: `thm:pn-absolute-lower`, `cor:pn-fresh-query` (normalization_depth_lower.tex). -/
theorem absolute_lower_rademacher {A B : ℝ} (hAB' : (A = 11 / 3 ∧ B = 1 / 3) ∨ (A = 3 ∧ B = 1))
    {T : ℕ} (hT : 1 ≤ T) {Q : ℝ}
    (hQ : ((T : ℝ) * ∑ x : Fin T → Bool, (1 / 2 ^ T : ℝ) * ((sgnSum x / T)
      * tanh (recF A B (2 ^ Nat.clog 2 (2 * ⌈logb (5 / 4) (2 * √(T : ℝ))⌉₊)) (sgnSum x / T)
        / (2 * ((2 ^ Nat.clog 2 (2 * ⌈logb (5 / 4) (2 * √(T : ℝ))⌉₊) : ℕ) : ℝ))))) ^ 2 ≤ Q) :
    (T : ℝ) / (2 : ℝ) ^ 17 ≤ Q := by
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (T : ℝ) ≠ 0 := by positivity
  refine absolute_lower hAB' hT1 univ (fun _ => (1 / 2 ^ T : ℝ)) (fun x => sgnSum x / T)
    (fun _ _ => by positivity) ?_ ?_ ?_ ?_ hQ
  · rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast; field_simp
  · rw [← mul_sum]; simp only [div_pow, ← sum_div, sum_sq_signs]; field_simp
  · rw [← mul_sum]; simp only [div_pow, ← sum_div, sum_four_signs]
    have hTp : (0 : ℝ) < T := by positivity
    rw [show (1 / 2 ^ T : ℝ) * ((3 * T ^ 2 - 2 * T) * 2 ^ T / T ^ 4) = (3 * T - 2) / T ^ 3 by
      field_simp]
    apply (div_le_div_iff₀ (pow_pos hTp 3) (pow_pos hTp 2)).2
    nlinarith
  · intro x _
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < T), div_le_one (by positivity)]
    exact abs_sgnSum_le x

end ExactSampling.PreNormDepthLower
