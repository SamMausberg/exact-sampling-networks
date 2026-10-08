import Mathlib

/-!
# Complex continuation through a scalar bottleneck

This module formalizes `lem:signedstrip` and the gate and cache arithmetic of
`thm:signed-bottleneck` (tanh_rank_two.tex), together with the
finite-bit charges of `thm:rank-two-critical` (tanh_rank_two.tex) on which that
corollary relies.

Formalized:
* the real and imaginary parts of `tanh(u + iv)`, the bounds
  `|Im tanh(u + iv)| ≤ tan |v|` (`|v| < π/2`) and `|Re tanh(u + iv)| ≤ 1`
  (`|v| ≤ π/4`), and complex differentiability of `tanh` on `|Im| < π/2`;
* `tan^2 t ≤ t^2/(1 - t^2)` and the scalar recursion `y_ℓ ≤ y/√(1 - ℓ y^2)`;
* `lem:signedstrip` itself for an explicit complex tanh network with absolute
  row sums at most one (`network_imag_bound`, `network_strip`): for
  `|Im z| ≤ 1/(4√D)` every neuron is complex differentiable at `z`, and every
  neuron output has `|Im| < 1/2`, `|Re| ≤ 1` and modulus at most two;
* the rank-two strip geometry: `1/(16√D)` for the first affine row of sum four,
  the polydisk inside the tube, and the scale conversion
  `1/(q a^4) ≤ 2^{32} D^{5/2}`;
* outer-gate exactness, the cache-miss cancellation
  `c min(1, ε/c) = min(c, ε)`, the dyadic sum
  `∑_m min(Ā/m^2, ε) m ≤ 4 √(Ā ε)`, and `H √(Ā ε) ≤ √Ā` for `ε ≤ H^{-2}`;
* the real-number step behind almost sure termination.

Not formalized: the Cauchy coefficient estimates, the Taylor oracle and its
rounding analysis, the tail bounds of the comparisons, and the Bernstein
factory itself.
-/

open Real Finset Filter

namespace ExactSampling.NewSignedBottleneck

/-! ## Complex tanh on a horizontal strip -/

/-- `sinh(u + iv) = sinh u cos v + i cosh u sin v`. Auxiliary for `lem:signedstrip`
(tanh_rank_two.tex). -/
theorem sinh_decomp (u v : ℝ) :
    Complex.sinh ((u : ℂ) + (v : ℂ) * Complex.I) =
      ((Real.sinh u * Real.cos v : ℝ) : ℂ) + ((Real.cosh u * Real.sin v : ℝ) : ℂ) * Complex.I := by
  rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  push_cast
  ring

/-- `cosh(u + iv) = cosh u cos v + i sinh u sin v`. Auxiliary for `lem:signedstrip`
(tanh_rank_two.tex). -/
theorem cosh_decomp (u v : ℝ) :
    Complex.cosh ((u : ℂ) + (v : ℂ) * Complex.I) =
      ((Real.cosh u * Real.cos v : ℝ) : ℂ) + ((Real.sinh u * Real.sin v : ℝ) : ℂ) * Complex.I := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  push_cast
  ring

/-- Real and imaginary parts of `a + b i`. Auxiliary for `lem:signedstrip`
(tanh_rank_two.tex). -/
theorem re_im_of (a b : ℝ) :
    ((a : ℂ) + (b : ℂ) * Complex.I).re = a ∧ ((a : ℂ) + (b : ℂ) * Complex.I).im = b := by
  simp

/-- `|cosh(u + iv)|^2 = sinh^2 u + cos^2 v`. Auxiliary for `lem:signedstrip`
(tanh_rank_two.tex). -/
theorem normSq_cosh (u v : ℝ) :
    Complex.normSq (Complex.cosh ((u : ℂ) + (v : ℂ) * Complex.I)) =
      Real.sinh u ^ 2 + Real.cos v ^ 2 := by
  rw [cosh_decomp, Complex.normSq_apply]
  simp only [re_im_of]
  have h1 := Real.cosh_sq u
  have h2 := Real.sin_sq_add_cos_sq v
  nlinarith [h1, h2]

/-- Paper: `lem:signedstrip` (tanh_rank_two.tex), proof:
`Im tanh(u + iv) = sin v cos v / (sinh^2 u + cos^2 v)`. -/
theorem tanh_im (u v : ℝ) :
    (Complex.tanh ((u : ℂ) + (v : ℂ) * Complex.I)).im =
      Real.sin v * Real.cos v / (Real.sinh u ^ 2 + Real.cos v ^ 2) := by
  rw [Complex.tanh_eq_sinh_div_cosh, Complex.div_im, normSq_cosh, sinh_decomp, cosh_decomp]
  simp only [re_im_of]
  have h1 := Real.cosh_sq u
  rw [← sub_div]
  congr 1
  linear_combination (Real.sin v * Real.cos v) * h1

/-- Paper: `lem:signedstrip` (tanh_rank_two.tex), proof:
`Re tanh(u + iv) = sinh u cosh u / (sinh^2 u + cos^2 v)`. -/
theorem tanh_re (u v : ℝ) :
    (Complex.tanh ((u : ℂ) + (v : ℂ) * Complex.I)).re =
      Real.sinh u * Real.cosh u / (Real.sinh u ^ 2 + Real.cos v ^ 2) := by
  rw [Complex.tanh_eq_sinh_div_cosh, Complex.div_re, normSq_cosh, sinh_decomp, cosh_decomp]
  simp only [re_im_of]
  rw [← add_div]
  congr 1
  have h2 := Real.sin_sq_add_cos_sq v
  linear_combination (Real.sinh u * Real.cosh u) * h2


/-- Paper: `lem:signedstrip` (tanh_rank_two.tex), proof: for `|v| < π/2`,
`|cosh(u + iv)|^2 ≥ cos^2 v > 0`, so `tanh` has no pole at `u + iv`. -/
theorem cosh_ne_zero_of_strip (u v : ℝ) (hv : |v| < π / 2) :
    Complex.cosh ((u : ℂ) + (v : ℂ) * Complex.I) ≠ 0 := by
  have hc : 0 < Real.cos v := Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le v],
    by linarith [le_abs_self v]⟩
  intro h
  have := normSq_cosh u v
  rw [h, map_zero] at this
  nlinarith [sq_nonneg (Real.sinh u), sq_pos_of_pos hc]

/-- Paper: `lem:signedstrip` (tanh_rank_two.tex): `tanh` is complex
differentiable at every point of the strip `|Im z| < π/2`. -/
theorem tanh_differentiableAt_strip (u v : ℝ) (hv : |v| < π / 2) :
    DifferentiableAt ℂ Complex.tanh ((u : ℂ) + (v : ℂ) * Complex.I) := by
  have h : Complex.tanh = fun z => Complex.sinh z / Complex.cosh z := by
    funext z; exact Complex.tanh_eq_sinh_div_cosh z
  rw [h]
  exact (Complex.differentiable_sinh _).div (Complex.differentiable_cosh _)
    (cosh_ne_zero_of_strip u v hv)

/-- Paper: `lem:signedstrip` (tanh_rank_two.tex): for `|v| < π/2`,
`|Im tanh(u + iv)| ≤ tan |v|`. -/
theorem tanh_im_le (u v : ℝ) (hv : |v| < π / 2) :
    |(Complex.tanh ((u : ℂ) + (v : ℂ) * Complex.I)).im| ≤ Real.tan |v| := by
  have hc : 0 < Real.cos v := Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le v],
    by linarith [le_abs_self v]⟩
  rw [tanh_im, Real.tan_eq_sin_div_cos, Real.cos_abs]
  have hN : Real.cos v ^ 2 ≤ Real.sinh u ^ 2 + Real.cos v ^ 2 := by nlinarith [sq_nonneg (sinh u)]
  have hNpos : 0 < Real.sinh u ^ 2 + Real.cos v ^ 2 := by positivity
  have hsin : |Real.sin (|v|)| = |Real.sin v| := by
    rcases le_total 0 v with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, Real.sin_neg, abs_neg]
  rw [abs_div, abs_of_pos hNpos, abs_mul, abs_of_pos hc]
  have h0 : 0 ≤ Real.sin |v| := Real.sin_nonneg_of_nonneg_of_le_pi (abs_nonneg v)
    (by linarith [Real.pi_pos])
  rw [abs_of_nonneg h0] at hsin
  rw [hsin, div_le_div_iff₀ hNpos hc]
  have := abs_nonneg (Real.sin v)
  nlinarith [mul_le_mul_of_nonneg_left hN (mul_nonneg this hc.le)]

/-- Paper: `lem:signedstrip` (tanh_rank_two.tex): for `|v| ≤ π/4`,
`|Re tanh(u + iv)| ≤ 1`. -/
theorem tanh_re_le (u v : ℝ) (hv : |v| ≤ π / 4) :
    |(Complex.tanh ((u : ℂ) + (v : ℂ) * Complex.I)).re| ≤ 1 := by
  have h2v : 0 ≤ Real.cos (2 * v) := Real.cos_nonneg_of_mem_Icc ⟨by
    linarith [neg_abs_le v], by linarith [le_abs_self v]⟩
  have hc2 : 1 / 2 ≤ Real.cos v ^ 2 := by rw [Real.cos_two_mul] at h2v; linarith
  rw [tanh_re]
  have hNpos : 0 < Real.sinh u ^ 2 + Real.cos v ^ 2 := by positivity
  rw [abs_div, abs_of_pos hNpos, div_le_one hNpos]
  have hch := Real.cosh_sq u
  have hsq : (Real.sinh u * Real.cosh u) ^ 2 ≤ (Real.sinh u ^ 2 + Real.cos v ^ 2) ^ 2 := by
    rw [mul_pow, hch]; nlinarith [sq_nonneg (Real.sinh u)]
  rw [← sq_abs (Real.sinh u * Real.cosh u)] at hsq
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) hNpos.le (by norm_num)).mp hsq

/-! ## The tangent recursion -/

/-- Paper: `lem:signedstrip` (tanh_rank_two.tex), proof:
`tan t ≤ t/√(1 - t^2)` for `0 ≤ t < 1`, from `sin^2 t ≤ t^2`; in squared form
`tan^2 t ≤ t^2/(1 - t^2)`. -/
theorem tan_sq_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Real.tan t ^ 2 ≤ t ^ 2 / (1 - t ^ 2) := by
  have hc : 0 < Real.cos t := Real.cos_pos_of_le_one (by rw [abs_of_nonneg ht0]; linarith)
  have hs0 : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0
    (by linarith [Real.pi_gt_three])
  have hs : Real.sin t ≤ t := Real.sin_le ht0
  have hs2 : Real.sin t ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hs0 hs 2
  have hsc := Real.sin_sq_add_cos_sq t
  have ht2 : 0 < 1 - t ^ 2 := by nlinarith
  rw [Real.tan_eq_sin_div_cos, div_pow, div_le_div_iff₀ (by positivity) ht2]
  nlinarith

/-- `tan t ≥ 0` for `0 ≤ t < 1`. Auxiliary for `lem:signedstrip`
(tanh_rank_two.tex). -/
theorem tan_nonneg_of_lt_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : 0 ≤ Real.tan t := by
  have hc : 0 < Real.cos t := Real.cos_pos_of_le_one (by rw [abs_of_nonneg ht0]; linarith)
  have hs0 : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0
    (by linarith [Real.pi_gt_three])
  rw [Real.tan_eq_sin_div_cos]; positivity

/-- Paper: `lem:signedstrip` (tanh_rank_two.tex), the scalar tangent recursion:
if `Y_0 ≤ y`, `Y_{ℓ+1} ≤ tan Y_ℓ` whenever `Y_ℓ < 1`, and `D y^2 < 1`, then
`Y_ℓ^2 ≤ y^2/(1 - ℓ y^2)`, i.e. `Y_ℓ ≤ y/√(1 - ℓ y^2)`, for `ℓ ≤ D`. For an actual
complex network the step hypothesis is supplied by `imag_step`; see
`network_imag_bound`. -/
theorem imag_recursion (y : ℝ) (Y : ℕ → ℝ) (D : ℕ) (hY0 : Y 0 ≤ y)
    (hYnn : ∀ ℓ, 0 ≤ Y ℓ) (hstep : ∀ ℓ < D, Y ℓ < 1 → Y (ℓ + 1) ≤ Real.tan (Y ℓ))
    (hD : (D : ℝ) * y ^ 2 < 1) (ℓ : ℕ) (hℓ : ℓ ≤ D) :
    Y ℓ ^ 2 ≤ y ^ 2 / (1 - ℓ * y ^ 2) := by
  induction ℓ with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, sub_zero, div_one]
    exact pow_le_pow_left₀ (hYnn 0) hY0 2
  | succ ℓ ih =>
    have ih' := ih (by omega)
    have hℓD : ((ℓ + 1 : ℕ) : ℝ) ≤ D := by exact_mod_cast hℓ
    have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
    have hpos : 0 < 1 - ((ℓ + 1 : ℕ) : ℝ) * y ^ 2 := by nlinarith
    push_cast at hpos hℓD ⊢
    have hpos' : 0 < 1 - (ℓ : ℝ) * y ^ 2 := by nlinarith
    have hY1 : Y ℓ ^ 2 < 1 := by
      rw [le_div_iff₀ hpos'] at ih'
      nlinarith
    have hYl1 : Y ℓ < 1 := by nlinarith [hYnn ℓ]
    have htan := tan_sq_le (hYnn ℓ) hYl1
    have hYs : Y (ℓ + 1) ^ 2 ≤ Real.tan (Y ℓ) ^ 2 :=
      pow_le_pow_left₀ (hYnn (ℓ + 1)) (hstep ℓ (by omega) hYl1) 2
    have hmono : Y ℓ ^ 2 / (1 - Y ℓ ^ 2) ≤ y ^ 2 / (1 - ((ℓ : ℝ) + 1) * y ^ 2) := by
      rw [div_le_div_iff₀ (by linarith) hpos]
      rw [le_div_iff₀ hpos'] at ih'
      nlinarith
    linarith

/-- Paper: `lem:signedstrip` (tanh_rank_two.tex): for `|y| ≤ 1/(4√D)`
and `ℓ ≤ D`, `y^2/(1 - ℓ y^2) ≤ 1/(15D) < 1/4`, so every layer has imaginary
magnitude below `1/2`. -/
theorem strip_constant (D ℓ : ℕ) (hD : 1 ≤ D) (hℓ : ℓ ≤ D) (y : ℝ)
    (hy : y ^ 2 ≤ 1 / (16 * D)) :
    (D : ℝ) * y ^ 2 < 1 ∧ y ^ 2 / (1 - ℓ * y ^ 2) ≤ 1 / (15 * D) ∧
      1 / (15 * (D : ℝ)) < 1 / 4 := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hℓ' : (ℓ : ℝ) ≤ D := by exact_mod_cast hℓ
  have hDy : (D : ℝ) * y ^ 2 ≤ 1 / 16 := by
    rw [le_div_iff₀ (by positivity)] at hy
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  have hy0 : 0 ≤ y ^ 2 := sq_nonneg y
  have hℓy : (ℓ : ℝ) * y ^ 2 ≤ 1 / 16 := by nlinarith
  refine ⟨by linarith, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by linarith) (by positivity)]
    rw [le_div_iff₀ (by positivity)] at hy
    nlinarith
  · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith

/-- Paper: `lem:signedstrip` (tanh_rank_two.tex): real part at most one
and imaginary part below one half give modulus at most two. -/
theorem modulus_le_two (w : ℂ) (hre : |w.re| ≤ 1) (him : |w.im| < 1 / 2) : ‖w‖ ≤ 2 := by
  have h1 : w.re ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg w.re]
  have h2 : w.im ^ 2 ≤ 1 / 4 := by rw [← sq_abs]; nlinarith [abs_nonneg w.im]
  have h3 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  nlinarith [norm_nonneg w]

/-- Paper: `lem:signedstrip` (tanh_rank_two.tex), proof: a row of
absolute sum at most one does not increase the largest imaginary magnitude. -/
theorem row_imag_le {m : ℕ} (w : Fin m → ℝ) (h : Fin m → ℂ) (Y : ℝ)
    (hw : ∑ j, |w j| ≤ 1) (hh : ∀ j, |(h j).im| ≤ Y) (hY : 0 ≤ Y) :
    |(∑ j, (w j : ℂ) * h j).im| ≤ Y := by
  rw [Complex.im_sum]
  simp only [Complex.im_ofReal_mul]
  calc |∑ j, w j * (h j).im| ≤ ∑ j, |w j * (h j).im| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |w j| * Y := Finset.sum_le_sum (fun j _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hh j) (abs_nonneg _))
    _ = (∑ j, |w j|) * Y := by rw [Finset.sum_mul]
    _ ≤ 1 * Y := mul_le_mul_of_nonneg_right hw hY
    _ = Y := one_mul Y

/-- Paper: `lem:signedstrip` (tanh_rank_two.tex), proof: one neuron step. A row
of absolute sum at most one followed by complex `tanh` maps imaginary
magnitudes at most `Y < π/2` to imaginary magnitudes at most `tan Y`. -/
theorem imag_step {m : ℕ} (w : Fin m → ℝ) (h : Fin m → ℂ) (Y : ℝ)
    (hw : ∑ j, |w j| ≤ 1) (hh : ∀ j, |(h j).im| ≤ Y) (hY0 : 0 ≤ Y) (hY : Y < π / 2) :
    |(Complex.tanh (∑ j, (w j : ℂ) * h j)).im| ≤ Real.tan Y := by
  set s := ∑ j, (w j : ℂ) * h j
  have hs : |s.im| ≤ Y := row_imag_le w h Y hw hh hY0
  have hs' : s = (s.re : ℂ) + (s.im : ℂ) * Complex.I := (Complex.re_add_im s).symm
  rw [hs']
  refine (tanh_im_le s.re s.im (lt_of_le_of_lt hs hY)).trans ?_
  rcases eq_or_lt_of_le hs with h | h
  · rw [h]
  · exact (Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two (abs_nonneg _) hY h).le

/-- Paper: `lem:signedstrip` (tanh_rank_two.tex): for a complex tanh network
`h_{ℓ+1,a} = tanh(∑_j w_{ℓ+1,aj} h_{ℓ,j})` with absolute row sums at most one,
input imaginary parts at most `y` and `D y^2 < 1/4`, every layer `ℓ ≤ D` has
`|Im h_{ℓ,a}|^2 ≤ y^2/(1 - ℓ y^2)`. -/
theorem network_imag_bound {n : ℕ} (D : ℕ) (W : ℕ → Fin n → Fin n → ℝ)
    (hW : ∀ ℓ a, ∑ j, |W ℓ a j| ≤ 1) (h : ℕ → Fin n → ℂ)
    (hrec : ∀ ℓ a, h (ℓ + 1) a = Complex.tanh (∑ j, (W (ℓ + 1) a j : ℂ) * h ℓ j))
    (y : ℝ) (h0 : ∀ a, |(h 0 a).im| ≤ y) (hD : (D : ℝ) * y ^ 2 < 1 / 4) :
    ∀ ℓ ≤ D, ∀ a, |(h ℓ a).im| ^ 2 ≤ y ^ 2 / (1 - ℓ * y ^ 2) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro _ a
    simp only [Nat.cast_zero, zero_mul, sub_zero, div_one]
    exact pow_le_pow_left₀ (abs_nonneg _) (h0 a) 2
  | succ ℓ ih =>
    intro hℓ a
    have hℓD : ((ℓ + 1 : ℕ) : ℝ) ≤ D := by exact_mod_cast hℓ
    have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
    push_cast at hℓD ⊢
    have hpos' : 0 < 1 - (ℓ : ℝ) * y ^ 2 := by nlinarith
    have hpos : 0 < 1 - ((ℓ : ℝ) + 1) * y ^ 2 := by nlinarith
    set b := Real.sqrt (y ^ 2 / (1 - ℓ * y ^ 2))
    have hb0 : 0 ≤ b := Real.sqrt_nonneg _
    have hb2 : b ^ 2 = y ^ 2 / (1 - ℓ * y ^ 2) := Real.sq_sqrt (by positivity)
    have hbq : b ^ 2 < 1 / 4 := by
      rw [hb2, div_lt_iff₀ hpos']; nlinarith
    have hb1 : b < 1 := by nlinarith
    have hbpi : b < π / 2 := by linarith [Real.pi_gt_three]
    have hih : ∀ j, |(h ℓ j).im| ≤ b := fun j => by
      have := Real.abs_le_sqrt (ih (by omega) j)
      rwa [abs_abs] at this
    have hstep := imag_step (W (ℓ + 1) a) (h ℓ) b (hW (ℓ + 1) a) hih hb0 hbpi
    rw [← hrec] at hstep
    have htan := tan_sq_le hb0 hb1
    have hsq : |(h (ℓ + 1) a).im| ^ 2 ≤ Real.tan b ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hstep 2
    have hfin : b ^ 2 / (1 - b ^ 2) ≤ y ^ 2 / (1 - ((ℓ : ℝ) + 1) * y ^ 2) := by
      rw [hb2]; apply le_of_eq
      rw [one_sub_div hpos'.ne', div_div_div_cancel_right₀ hpos'.ne']
      congr 1; ring
    linarith

/-- Paper: `lem:signedstrip` (tanh_rank_two.tex). Let `h_{0,a}(z) = z` and
`h_{ℓ+1,a}(z) = tanh(∑_j w_{ℓ+1,aj} h_{ℓ,j}(z))` with absolute row sums at most
one (so the first preactivations are `a_i z` with `|a_i| ≤ 1`). If `D ≥ 1` and
`|Im z| ≤ 1/(4√D)` (written `(Im z)^2 ≤ 1/(16D)`), then for every `ℓ ≤ D` and
neuron `a`, `h_{ℓ,a}` is complex differentiable at `z`, and for `ℓ ≥ 1` its
value has `|Im| < 1/2`, `|Re| ≤ 1` and modulus at most two. -/
theorem network_strip {n : ℕ} (D : ℕ) (hD : 1 ≤ D) (W : ℕ → Fin n → Fin n → ℝ)
    (hW : ∀ ℓ a, ∑ j, |W ℓ a j| ≤ 1) (h : ℕ → Fin n → ℂ → ℂ) (h0 : ∀ a z, h 0 a z = z)
    (hrec : ∀ ℓ a z, h (ℓ + 1) a z = Complex.tanh (∑ j, (W (ℓ + 1) a j : ℂ) * h ℓ j z))
    (z : ℂ) (hz : z.im ^ 2 ≤ 1 / (16 * D)) :
    ∀ ℓ ≤ D, ∀ a, DifferentiableAt ℂ (h ℓ a) z ∧
      (1 ≤ ℓ → |(h ℓ a z).im| < 1 / 2 ∧ |(h ℓ a z).re| ≤ 1 ∧ ‖h ℓ a z‖ ≤ 2) := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  set y := |z.im|
  have hy0 : 0 ≤ y := abs_nonneg _
  have hy2 : y ^ 2 ≤ 1 / (16 * D) := by rw [sq_abs]; exact hz
  have hDy : (D : ℝ) * y ^ 2 < 1 / 4 := by
    have := (strip_constant D 0 hD (Nat.zero_le _) y hy2).1
    have h16 : (D : ℝ) * y ^ 2 ≤ 1 / 16 := by
      rw [le_div_iff₀ (by positivity)] at hy2
      rw [le_div_iff₀ (by norm_num)]; nlinarith
    linarith
  have himb := network_imag_bound D W hW (fun ℓ a => h ℓ a z) (fun ℓ a => hrec ℓ a z) y
    (fun a => by simp [h0, y]) hDy
  have hhalf : ∀ ℓ ≤ D, ∀ a, |(h ℓ a z).im| < 1 / 2 := by
    intro ℓ hℓ a
    have h1 := himb ℓ hℓ a
    have h2 := (strip_constant D ℓ hD hℓ y hy2).2
    have h3 : 1 / (15 * (D : ℝ)) < 1 / 4 := (strip_constant D ℓ hD hℓ y hy2).2.2
    have h4 : |(h ℓ a z).im| ^ 2 < (1 / 2) ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) h4
  have hpre : ∀ m < D, ∀ a,
      |(∑ j, (W (m + 1) a j : ℂ) * h m j z).im| ≤ 1 / 2 := by
    intro m hm a
    exact row_imag_le (W (m + 1) a) (fun j => h m j z) (1 / 2) (hW (m + 1) a)
      (fun j => (hhalf m hm.le j).le) (by norm_num)
  have hpi : (1 : ℝ) / 2 < π / 2 := by linarith [Real.pi_gt_three]
  have hpi4 : (1 : ℝ) / 2 ≤ π / 4 := by linarith [Real.pi_gt_three]
  intro ℓ
  induction ℓ with
  | zero =>
    intro _ a
    refine ⟨?_, fun h1 => absurd h1 (by norm_num)⟩
    have : h 0 a = fun z => z := funext (h0 a)
    rw [this]; exact differentiableAt_id
  | succ m ih =>
    intro hm a
    set s := ∑ j, (W (m + 1) a j : ℂ) * h m j z
    have hs : |s.im| ≤ 1 / 2 := hpre m (by omega) a
    have hsdec : s = (s.re : ℂ) + (s.im : ℂ) * Complex.I := (Complex.re_add_im s).symm
    refine ⟨?_, fun _ => ⟨hhalf (m + 1) hm a, ?_, ?_⟩⟩
    · have hfun : h (m + 1) a =
          fun z => Complex.tanh (∑ j, (W (m + 1) a j : ℂ) * h m j z) := funext (hrec m a)
      rw [hfun]
      have hin : DifferentiableAt ℂ (fun z => ∑ j, (W (m + 1) a j : ℂ) * h m j z) z := by
        have hj : ∀ j, DifferentiableAt ℂ (fun z => (W (m + 1) a j : ℂ) * h m j z) z :=
          fun j => ((ih (by omega) j).1).const_mul _
        simpa using DifferentiableAt.fun_sum (u := Finset.univ) (fun j _ => hj j)
      have htanh : DifferentiableAt ℂ Complex.tanh s := by
        rw [hsdec]; exact tanh_differentiableAt_strip s.re s.im (lt_of_le_of_lt hs hpi)
      exact htanh.comp z hin
    · rw [hrec]
      show |(Complex.tanh s).re| ≤ 1
      rw [hsdec]; exact tanh_re_le s.re s.im (le_trans hs hpi4)
    · refine modulus_le_two _ ?_ (hhalf (m + 1) hm a)
      rw [hrec]
      show |(Complex.tanh s).re| ≤ 1
      rw [hsdec]; exact tanh_re_le s.re s.im (le_trans hs hpi4)

/-! ## Strip geometry in the rank-two oracle -/

/-- Paper: `thm:rank-two-critical` (tanh_rank_two.tex): the strip of
`lem:signedstrip` applies to the rank-two source means, since a first affine
row `∑_a c_a z_a` with `∑ |c_a| ≤ 4` and `|Im z_a| ≤ 1/(16√D)` has
imaginary part at most `1/(4√D)` (here `s = √D`). -/
theorem rank_two_first_row {m : ℕ} (c t : Fin m → ℝ) (s : ℝ) (hs : 0 < s)
    (hc : ∑ a, |c a| ≤ 4) (ht : ∀ a, |t a| ≤ 1 / (16 * s)) :
    |∑ a, c a * t a| ≤ 1 / (4 * s) := by
  calc |∑ a, c a * t a| ≤ ∑ a, |c a * t a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |c a| * (1 / (16 * s)) := Finset.sum_le_sum (fun a _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (ht a) (abs_nonneg _))
    _ = (∑ a, |c a|) * (1 / (16 * s)) := by rw [Finset.sum_mul]
    _ ≤ 4 * (1 / (16 * s)) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 1 / (4 * s) := by field_simp; ring

/-- Paper: `thm:rank-two-critical` (tanh_rank_two.tex): with grid spacing
`a ≤ 1/(128√D)` and scaled variables `z = c + 2a u`, the polydisk `|u| ≤ 2` has
`|Im z| ≤ 4a ≤ 1/(32√D) < 1/(16√D)`. -/
theorem polydisk_in_tube (a s : ℝ) (hs : 0 < s) (ha0 : 0 ≤ a) (ha : a ≤ 1 / (128 * s))
    (uim : ℝ) (hu : |uim| ≤ 2) : |2 * a * uim| < 1 / (16 * s) := by
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * a)]
  calc 2 * a * |uim| ≤ 2 * a * 2 := mul_le_mul_of_nonneg_left hu (by positivity)
    _ ≤ 4 * (1 / (128 * s)) := by linarith
    _ < 1 / (16 * s) := by
      rw [show 4 * (1 / (128 * s)) = 1 / (32 * s) by field_simp; ring]
      exact one_div_lt_one_div_of_lt (by positivity) (by linarith)

/-- Paper: `thm:rank-two-critical` (tanh_rank_two.tex): for
`a > 1/(256√D)` and `q^{-1} ≤ √D`, the scale conversion of the mixed fourth
derivative is `1/(q a^4) ≤ 2^{32} D^{5/2}` (written `2^{32} D^2 √D`). -/
theorem scale_conversion (D : ℝ) (hD : 0 < D) (a qinv : ℝ) (ha : 1 / (256 * Real.sqrt D) < a)
    (hq : qinv ≤ Real.sqrt D) :
    qinv * (1 / a ^ 4) ≤ 2 ^ 32 * D ^ 2 * Real.sqrt D := by
  have hs : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hs2 : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD.le
  have ha0 : 0 < a := lt_trans (by positivity) ha
  have h1 : 1 < 256 * Real.sqrt D * a := by
    rw [div_lt_iff₀ (by positivity)] at ha; linarith
  have h4 : 1 < (256 * Real.sqrt D * a) ^ 4 := one_lt_pow₀ h1 (by norm_num)
  have h5 : 1 / a ^ 4 < 2 ^ 32 * D ^ 2 := by
    rw [div_lt_iff₀ (by positivity)]
    have e : (256 * Real.sqrt D * a) ^ 4 = 2 ^ 32 * D ^ 2 * a ^ 4 := by
      rw [mul_pow, mul_pow, show Real.sqrt D ^ 4 = (Real.sqrt D ^ 2) ^ 2 by ring, hs2]; norm_num
    linarith
  calc qinv * (1 / a ^ 4) ≤ Real.sqrt D * (2 ^ 32 * D ^ 2) :=
        mul_le_mul hq h5.le (by positivity) hs.le
    _ = 2 ^ 32 * D ^ 2 * Real.sqrt D := by ring

/-- Paper: `thm:rank-two-critical` (tanh_rank_two.tex): in variables `p` with
`z = 2p - 1 = c + 2a u`, the `k`-th derivative conversion of `f = F/q` is
`2^k / (q (2a)^k) = 1/(q a^k)`: only powers of `a^{-1}` and `q^{-1}` appear. -/
theorem grid_scale (q a : ℝ) (k : ℕ) : 2 ^ k / (q * (2 * a) ^ k) = 1 / (q * a ^ k) := by
  by_cases hq : q = 0
  · simp [hq]
  by_cases ha : a = 0
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · simp [ha, zero_pow hk.ne']
  rw [mul_pow]
  field_simp

/-! ## Gates, cache misses and refinement charges -/

/-- Paper: `thm:signed-bottleneck` (tanh_rank_two.tex) via
`thm:rank-two-critical`: opening the gate `q` and sampling `F/q` on the open
branch reproduces the mean `F`. -/
theorem outer_gate_exactness (q F : ℝ) (hq : q ≠ 0) : q * (F / q) = F := by
  field_simp

/-- Paper: `thm:rank-two-critical` (tanh_rank_two.tex): on a branch of mass
`c`, the unresolved interval has measure `min(1, ε/c)`; multiplying by the
branch mass gives `min(c, ε)`. -/
theorem cache_miss_mass_cancellation (c ε : ℝ) (hc : 0 < c) :
    c * min 1 (ε / c) = min c ε := by
  by_cases h : ε ≤ c
  · have hratio : ε / c ≤ 1 := (div_le_one hc).2 h
    rw [min_eq_right hratio, min_eq_right h]
    field_simp
  · have hcε : c ≤ ε := le_of_lt (lt_of_not_ge h)
    have hratio : 1 ≤ ε / c := (one_le_div hc).2 hcε
    rw [min_eq_left hratio, min_eq_left hcε]
    ring

/-- `∑_{ℓ<N} min(x_ℓ, 1/x_ℓ) ≤ 4` for a doubling sequence `x_ℓ = 2^ℓ x_0`. Auxiliary for
`thm:rank-two-critical` (tanh_rank_two.tex). -/
theorem dyadic_min_sum (x0 : ℝ) (hx0 : 0 < x0) (N : ℕ) :
    ∑ ℓ ∈ range N, min (2 ^ ℓ * x0) (1 / (2 ^ ℓ * x0)) ≤ 4 := by
  have key : ∀ N : ℕ, (2 ^ N * x0 ≤ 1 →
      ∑ ℓ ∈ range N, min (2 ^ ℓ * x0) (1 / (2 ^ ℓ * x0)) ≤ 2 ^ N * x0) ∧
      (1 < 2 ^ N * x0 →
      ∑ ℓ ∈ range N, min (2 ^ ℓ * x0) (1 / (2 ^ ℓ * x0)) ≤ 4 - 2 / (2 ^ N * x0)) := by
    intro N
    induction N with
    | zero =>
      simp only [range_zero, sum_empty, pow_zero, one_mul]
      constructor
      · intro _; exact hx0.le
      · intro h
        have : 2 / x0 < 2 := by rw [div_lt_iff₀ hx0]; linarith
        linarith
    | succ N ih =>
      obtain ⟨ih1, ih2⟩ := ih
      set x := 2 ^ N * x0 with hx
      have hxpos : 0 < x := by positivity
      have hx' : 2 ^ (N + 1) * x0 = 2 * x := by rw [pow_succ]; ring
      rw [sum_range_succ, hx']
      rcases le_or_gt x 1 with h | h
      · have hmin : min x (1 / x) = x := min_eq_left (by
          rw [le_div_iff₀ hxpos]; nlinarith)
        rw [hmin]
        have hs := ih1 h
        constructor
        · intro _; linarith
        · intro h2
          have hx1 : 1 / 2 < x := by linarith
          have h3 : 2 / (2 * x) = 1 / x := by field_simp
          have h4 : 2 * x + 1 / x ≤ 4 := by
            rw [← sub_nonneg]
            have e : 4 - (2 * x + 1 / x) = (4 * x - 2 * x ^ 2 - 1) / x := by field_simp; ring
            rw [e]; apply div_nonneg _ hxpos.le; nlinarith
          rw [h3]; linarith
      · have hmin : min x (1 / x) = 1 / x := min_eq_right (by
          rw [div_le_iff₀ hxpos]; nlinarith)
        rw [hmin]
        have hs := ih2 h
        constructor
        · intro h2; nlinarith
        · intro _
          rw [show 2 / (2 * x) = 1 / x by field_simp]
          have : 2 / x = 2 * (1 / x) := by ring
          linarith
  rcases le_or_gt (2 ^ N * x0) 1 with h | h
  · linarith [(key N).1 h]
  · have := (key N).2 h
    have : 0 < 2 / (2 ^ N * x0) := by positivity
    linarith

/-- Paper: `thm:rank-two-critical` (tanh_rank_two.tex): over the correction
levels `m = 2^ℓ m_0`, the expensive refinement charges satisfy
`∑_m min(Ā/m^2, ε) m ≤ 4 √(Ā ε)`. -/
theorem refinement_sum (A ε m0 : ℝ) (hA : 0 < A) (hε : 0 < ε) (hm0 : 0 < m0) (N : ℕ) :
    ∑ ℓ ∈ range N, min (A / (2 ^ ℓ * m0) ^ 2) ε * (2 ^ ℓ * m0) ≤ 4 * Real.sqrt (A * ε) := by
  set a := Real.sqrt A
  set e := Real.sqrt ε
  have ha : 0 < a := Real.sqrt_pos.mpr hA
  have he : 0 < e := Real.sqrt_pos.mpr hε
  have hA2 : A = a ^ 2 := (Real.sq_sqrt hA.le).symm
  have hε2 : ε = e ^ 2 := (Real.sq_sqrt hε.le).symm
  have hAe : Real.sqrt (A * ε) = a * e := Real.sqrt_mul hA.le ε
  have key : ∀ ℓ : ℕ, min (A / (2 ^ ℓ * m0) ^ 2) ε * (2 ^ ℓ * m0) =
      a * e * min (2 ^ ℓ * (m0 * e / a)) (1 / (2 ^ ℓ * (m0 * e / a))) := by
    intro ℓ
    have hm : 0 < 2 ^ ℓ * m0 := by positivity
    rw [min_mul_of_nonneg _ _ hm.le, mul_min_of_nonneg _ _ (by positivity), min_comm]
    congr 1
    · rw [hε2]; field_simp
    · rw [hA2]; field_simp
  rw [hAe]
  simp_rw [key]
  rw [← mul_sum]
  have h := dyadic_min_sum (m0 * e / a) (by positivity) N
  nlinarith [mul_pos ha he]

/-- Paper: `thm:rank-two-critical` (tanh_rank_two.tex): with stored accuracy
`ε ≤ H^{-2}`, `H = n^2 D`, the refinement total `H √(Ā ε)` is at most `√Ā`,
which is `O(D+1)` when `Ā = O((D+1)^2)`. -/
theorem refinement_total (H A ε : ℝ) (hH : 0 < H) (hA : 0 ≤ A)
    (hε : ε ≤ 1 / H ^ 2) : H * Real.sqrt (A * ε) ≤ Real.sqrt A := by
  rw [Real.sqrt_mul hA]
  have h1 : Real.sqrt ε ≤ 1 / H := by
    rw [show (1 : ℝ) / H = Real.sqrt (1 / H ^ 2) by
      rw [Real.sqrt_div' 1 (sq_nonneg H), Real.sqrt_sq hH.le, Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hε
  have h2 : 0 ≤ Real.sqrt A := Real.sqrt_nonneg A
  calc H * (Real.sqrt A * Real.sqrt ε) ≤ H * (Real.sqrt A * (1 / H)) := by gcongr
    _ = Real.sqrt A := by field_simp

/-- Paper: `thm:signed-bottleneck` (tanh_rank_two.tex) via
`thm:rank-two-critical`: a gate `q ≤ c/√d` and conditional cost `K d` give
unconditional cost `c K √d`. -/
theorem gated_source_constant (q cost d c K : ℝ) (hd : 0 < d) (hq0 : 0 ≤ q) (hK : 0 ≤ K)
    (hq : q ≤ c / Real.sqrt d) (hc : cost ≤ K * d) :
    q * cost ≤ c * K * Real.sqrt d := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have hc0 : 0 ≤ c := by
    have h := le_trans hq0 hq
    rwa [le_div_iff₀ hs, zero_mul] at h
  calc q * cost ≤ q * (K * d) := mul_le_mul_of_nonneg_left hc hq0
    _ ≤ (c / Real.sqrt d) * (K * d) := mul_le_mul_of_nonneg_right hq (by positivity)
    _ = c * K * Real.sqrt d := by
        rw [show c / Real.sqrt d * (K * d) = c * K * (d / Real.sqrt d) by ring, Real.div_sqrt]

/-- Paper: `thm:rank-two-critical` (tanh_rank_two.tex), the real-number step
behind almost sure termination: a nonnegative number `p` bounded by every term
of a sequence tending to zero is zero. The tail bounds themselves are not
formalized. -/
theorem stopping_from_vanishing_tail (p : ℝ) (tail : ℕ → ℝ) (hp : 0 ≤ p)
    (hbound : ∀ m, p ≤ tail m) (htail : Tendsto tail atTop (nhds 0)) : p = 0 := by
  have hupper : p ≤ 0 := ge_of_tendsto htail (Eventually.of_forall hbound)
  exact le_antisymm hupper hp

end ExactSampling.NewSignedBottleneck
