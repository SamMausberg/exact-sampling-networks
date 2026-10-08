import Mathlib

/-!
# The recursive exact tanh sampler: intervals, biases, and offspring factors

This module formalizes the exactness identities and the local cost factor of the recursive
sampler for dense tanh networks in the full version:

* `tanh_scalar.tex`, Section `sec:algorithm`: the interval invariant `lem:interval`
  (endpoint formulas `eq:midrad` and the complete layer induction), the normalized source
  identity, the internal three-way mixture `eq:internalmixture`, and the top mixture
  `eq:topmixture`;
* `tanh_scalar.tex`, Section `sec:bias`: the bias identity `eq:biasidentity`, the exact odds
  race (acceptance probability, accepted signed mean, termination and the geometric number of
  trials, written as `HasSum` identities), and the joint cost identity `eq:jointcost`;
* `tanh_scalar.tex`, `lem:offspring`: the hyperbolic form of the race factor, its bound
  `exp (ρ² (1 - z)² / 4)`, the offspring bound `eq:offspring`, and the root bound `r_D B_D`;
* the end-to-end exactness of the bias step: the race on the source `(1 ± G_ρ(z))/2` returns
  the centered target of `eq:centered` (`race_realizes_centered` and its complement);
* the countable sign-mixture identity used with `lem:majority` and `eq:chainmixture`.

Here `tanh` is `Real.tanh`; `tanh_eq_exp_form` records the exponential formula of the paper.

The rounding rule `eq:rounded` follows from the certified approximation `|q* - tanh(g r)| ≤ ε/16`
and the choice `r_ℓ = q* + 5ε/2` (`rounded_radius_bounds`); the computation of `q*` and of the
rounded centers is not formalized, and the centers enter `interval_invariant` through the
hypothesis `|c - m| ≤ ε` as the paper states it.

Not formalized here: the probability space of the recursive sampler itself (the identities are
stated for the means and probabilities that the sampler's elementary steps produce), the
dyadic computation of `q*` and of the centers, and the finite-bit implementation. The bound
`lem:arity` on the sequential majority cost enters `offspring_bound` as a hypothesis; in
`ExactSampling.MajorityArity` it is proved (`sequential_arity_bound`) only from the stand-in
identity `eq:arityintegral` for the full-majority cost and the stand-in coefficient `d_1`.
The measure-theoretic stopped-work lemma `lem:stopping` is in `ExactSampling.StoppedWork`.
-/

namespace ExactSampling.TanhFactory

open Real Finset

/-! ### Elementary tanh facts -/

/-- The exponential formula `tanh s = (e^{2s} - 1)/(e^{2s} + 1)` for the activation of the
network `eq:network` (`tanh_model.tex`). -/
theorem tanh_eq_exp_form (s : ℝ) :
    tanh s = (exp (2 * s) - 1) / (exp (2 * s) + 1) := by
  have he : 0 < exp s := exp_pos s
  have h2 : exp (2 * s) = exp s * exp s := by rw [← exp_add]; ring_nf
  rw [tanh_eq, h2, exp_neg]
  field_simp

/-- `tanh` is monotone. Auxiliary for `lem:interval` (`tanh_scalar.tex`). -/
theorem tanh_le_tanh {x y : ℝ} (h : x ≤ y) : tanh x ≤ tanh y := by
  by_contra hlt
  have hlt : tanh y < tanh x := lt_of_not_ge hlt
  have := artanh_lt_artanh (neg_one_lt_tanh y) (tanh_lt_one x) hlt
  rw [artanh_tanh, artanh_tanh] at this
  linarith

/-- `tanh` is nonnegative on `[0, ∞)`. Auxiliary for `lem:interval` (`tanh_scalar.tex`). -/
theorem tanh_nonneg_of_nonneg {x : ℝ} (h : 0 ≤ x) : 0 ≤ tanh x := by
  simpa using tanh_le_tanh h

/-- `tanh` is positive on `(0, ∞)`. Auxiliary for `eq:biasidentity` (`tanh_scalar.tex`). -/
theorem tanh_pos_of_pos {x : ℝ} (h : 0 < x) : 0 < tanh x := by
  rw [tanh_eq_sinh_div_cosh]
  exact div_pos (sinh_pos_iff.mpr h) (cosh_pos x)

/-- `|tanh a tanh b| < 1`. Auxiliary for `eq:midrad` (`tanh_scalar.tex`). -/
theorem abs_tanh_mul_lt_one (a b : ℝ) : |tanh a * tanh b| < 1 := by
  rw [abs_mul]
  have ha := abs_tanh_lt_one a
  have hb := abs_tanh_lt_one b
  calc |tanh a| * |tanh b| ≤ |tanh a| * 1 :=
        mul_le_mul_of_nonneg_left hb.le (abs_nonneg _)
    _ < 1 := by simpa using ha

/-- `1 + tanh a tanh b > 0`. Auxiliary for `eq:midrad` and `eq:biasidentity`
(`tanh_scalar.tex`). -/
theorem one_add_tanh_mul_pos (a b : ℝ) : 0 < 1 + tanh a * tanh b := by
  have h := (abs_lt.mp (abs_tanh_mul_lt_one a b)).1
  linarith

/-- `1 - tanh a tanh b > 0`. Auxiliary for `eq:midrad` (`tanh_scalar.tex`). -/
theorem one_sub_tanh_mul_pos (a b : ℝ) : 0 < 1 - tanh a * tanh b := by
  have h := (abs_lt.mp (abs_tanh_mul_lt_one a b)).2
  linarith

/-- The tanh addition formula, used for `eq:midrad` and `eq:biasidentity`
(`tanh_scalar.tex`). -/
theorem tanh_add_formula (a b : ℝ) :
    tanh (a + b) = (tanh a + tanh b) / (1 + tanh a * tanh b) := by
  have ca := cosh_pos a
  have cb := cosh_pos b
  have hd : cosh a * cosh b + sinh a * sinh b = cosh (a + b) := (cosh_add a b).symm
  have hab := cosh_pos (a + b)
  rw [tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh, sinh_add,
    cosh_add]
  rw [cosh_add] at hab
  field_simp

/-- The tanh subtraction formula. Auxiliary for `eq:midrad` (`tanh_scalar.tex`). -/
theorem tanh_sub_formula (a b : ℝ) :
    tanh (a - b) = (tanh a - tanh b) / (1 - tanh a * tanh b) := by
  rw [sub_eq_add_neg, tanh_add_formula, tanh_neg, mul_neg, ← sub_eq_add_neg, ← sub_eq_add_neg]

/-- `1 - tanh² = 1 / cosh²`. Auxiliary for `lem:offspring` (`tanh_scalar.tex`). -/
theorem one_sub_tanh_sq (a : ℝ) : 1 - tanh a ^ 2 = 1 / cosh a ^ 2 := by
  have ca := cosh_pos a
  rw [tanh_eq_sinh_div_cosh]
  have := cosh_sq_sub_sinh_sq a
  field_simp
  exact this

/-! ### Endpoint formulas and the interval invariant -/

/-- The Möbius map `T_θ(u) = (u + θ) / (1 + θ u)` of Section `sec:bias` (`tanh_scalar.tex`). -/
noncomputable def mobius (θ u : ℝ) : ℝ := (u + θ) / (1 + θ * u)

/-- The midpoint `m = t (1 - q²) / (1 - t² q²)` of `eq:midrad` (`tanh_scalar.tex`). -/
noncomputable def midpt (t q : ℝ) : ℝ := t * (1 - q ^ 2) / (1 - t ^ 2 * q ^ 2)

/-- The image radius `R = q (1 - t²) / (1 - t² q²)` of `eq:midrad` (`tanh_scalar.tex`). -/
noncomputable def imgRadius (t q : ℝ) : ℝ := q * (1 - t ^ 2) / (1 - t ^ 2 * q ^ 2)

/-- Factorization of the denominator of `eq:midrad` (`tanh_scalar.tex`). -/
theorem one_sub_sq_mul_sq_eq (a b : ℝ) :
    1 - tanh a ^ 2 * tanh b ^ 2 = (1 - tanh a * tanh b) * (1 + tanh a * tanh b) := by ring

/-- The denominator of `eq:midrad` is positive (`tanh_scalar.tex`), as the proof of
`lem:interval` notes. -/
theorem one_sub_sq_mul_sq_pos (a b : ℝ) : 0 < 1 - tanh a ^ 2 * tanh b ^ 2 := by
  rw [one_sub_sq_mul_sq_eq]
  exact mul_pos (one_sub_tanh_mul_pos a b) (one_add_tanh_mul_pos a b)

/-- `1 - tanh² a > 0`. Auxiliary for `lem:interval` (`tanh_scalar.tex`). -/
theorem one_sub_tanh_sq_pos (a : ℝ) : 0 < 1 - tanh a ^ 2 := by
  have := tanh_sq_lt_one a
  linarith

/-- The midpoint of the image interval `[tanh (a - ρ), tanh (a + ρ)]`.
Paper: `lem:interval` (`tanh_scalar.tex`), first formula of `eq:midrad`. -/
theorem endpoint_midpoint (a ρ : ℝ) :
    (tanh (a + ρ) + tanh (a - ρ)) / 2 = midpt (tanh a) (tanh ρ) := by
  have h1 : 1 + tanh a * tanh ρ ≠ 0 := (one_add_tanh_mul_pos a ρ).ne'
  have h2 : 1 - tanh a * tanh ρ ≠ 0 := (one_sub_tanh_mul_pos a ρ).ne'
  have h3 : 1 - tanh a ^ 2 * tanh ρ ^ 2 ≠ 0 := (one_sub_sq_mul_sq_pos a ρ).ne'
  rw [tanh_add_formula, tanh_sub_formula]
  unfold midpt
  field_simp
  ring

/-- The half-width of the image interval `[tanh (a - ρ), tanh (a + ρ)]`.
Paper: `lem:interval` (`tanh_scalar.tex`), second formula of `eq:midrad`. -/
theorem endpoint_radius (a ρ : ℝ) :
    (tanh (a + ρ) - tanh (a - ρ)) / 2 = imgRadius (tanh a) (tanh ρ) := by
  have h1 : 1 + tanh a * tanh ρ ≠ 0 := (one_add_tanh_mul_pos a ρ).ne'
  have h2 : 1 - tanh a * tanh ρ ≠ 0 := (one_sub_tanh_mul_pos a ρ).ne'
  have h3 : 1 - tanh a ^ 2 * tanh ρ ^ 2 ≠ 0 := (one_sub_sq_mul_sq_pos a ρ).ne'
  rw [tanh_add_formula, tanh_sub_formula]
  unfold imgRadius
  field_simp
  ring

/-- The image radius is nonnegative. Paper: `lem:interval` (`tanh_scalar.tex`). -/
theorem imgRadius_nonneg (a : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ imgRadius (tanh a) (tanh ρ) := by
  unfold imgRadius
  have := one_sub_sq_mul_sq_pos a ρ
  have := one_sub_tanh_sq_pos a
  have := tanh_nonneg_of_nonneg hρ
  positivity

/-- The image radius is positive for a positive row radius. Auxiliary for `eq:centered`
(`tanh_scalar.tex`). -/
theorem imgRadius_pos (a : ℝ) {ρ : ℝ} (hρ : 0 < ρ) : 0 < imgRadius (tanh a) (tanh ρ) := by
  unfold imgRadius
  have := one_sub_sq_mul_sq_pos a ρ
  have := one_sub_tanh_sq_pos a
  have := tanh_pos_of_pos hρ
  positivity

/-- `R ≤ q` in `eq:midrad`. Paper: `lem:interval` (`tanh_scalar.tex`). -/
theorem imgRadius_le (a : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) : imgRadius (tanh a) (tanh ρ) ≤ tanh ρ := by
  unfold imgRadius
  have hd := one_sub_sq_mul_sq_pos a ρ
  have hq := tanh_nonneg_of_nonneg hρ
  have hq1 := tanh_sq_lt_one ρ
  have ht := sq_nonneg (tanh a)
  rw [div_le_iff₀ hd]
  have : tanh a ^ 2 * tanh ρ ^ 2 ≤ tanh a ^ 2 := by nlinarith
  nlinarith

/-- Monotone propagation: a preactivation within `ρ` of `a` has activation within the image
radius of the midpoint. Paper: `lem:interval` (`tanh_scalar.tex`), first step of the proof. -/
theorem abs_tanh_sub_midpt_le (a ρ x : ℝ) (hx : |x - a| ≤ ρ) :
    |tanh x - midpt (tanh a) (tanh ρ)| ≤ imgRadius (tanh a) (tanh ρ) := by
  rw [← endpoint_midpoint, ← endpoint_radius]
  have h1 := tanh_le_tanh (show a - ρ ≤ x by linarith [(abs_le.mp hx).1])
  have h2 := tanh_le_tanh (show x ≤ a + ρ by linarith [(abs_le.mp hx).2])
  rw [abs_le]
  constructor <;> linarith

/-- The error budget of one row: `R + |m - c| ≤ r_ℓ`.
Paper: `lem:interval` (`tanh_scalar.tex`), the displayed inequality of the proof, with the
rounding rule `eq:rounded` and `σ ≤ g`. -/
theorem radius_add_center_error_le (a σ rPrev rNext cNext g ε : ℝ) (hσ0 : 0 ≤ σ)
    (hr : 0 ≤ rPrev) (hσ : σ ≤ g)
    (hc : |cNext - midpt (tanh a) (tanh (σ * rPrev))| ≤ ε)
    (hround : tanh (g * rPrev) + 2 * ε ≤ rNext) :
    imgRadius (tanh a) (tanh (σ * rPrev)) + |midpt (tanh a) (tanh (σ * rPrev)) - cNext|
      ≤ rNext := by
  have hρ : 0 ≤ σ * rPrev := mul_nonneg hσ0 hr
  have hRle := imgRadius_le a hρ
  have hmono : tanh (σ * rPrev) ≤ tanh (g * rPrev) :=
    tanh_le_tanh (mul_le_mul_of_nonneg_right hσ hr)
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) hc
  rw [abs_sub_comm] at hc
  linarith

/-- The rounding rule `eq:rounded`: a certified approximation `|q* - tanh (g r)| ≤ ε/16` and the
choice `r' = q* + 5ε/2` give `tanh (g r) + 2ε ≤ r' ≤ tanh (g r) + 3ε`.
Paper: `eq:rounded` (`tanh_scalar.tex`). -/
theorem rounded_radius_bounds {y qstar ε : ℝ} (hε : 0 ≤ ε) (hq : |qstar - y| ≤ ε / 16) :
    y + 2 * ε ≤ qstar + 5 * ε / 2 ∧ qstar + 5 * ε / 2 ≤ y + 3 * ε := by
  obtain ⟨h1, h2⟩ := abs_le.mp hq
  constructor <;> linarith

/-- One inductive step of the interval invariant: if every predecessor lies in its stored
interval, so does the new activation.
Paper: `lem:interval` (`tanh_scalar.tex`), inductive step, with row data `eq:rowdata`. -/
theorem interval_step {ι : Type*} (s : Finset ι) (w h c : ι → ℝ)
    (bias rPrev rNext cNext g ε : ℝ) (hr : 0 ≤ rPrev)
    (hh : ∀ j ∈ s, |h j - c j| ≤ rPrev) (hσ : ∑ j ∈ s, |w j| ≤ g)
    (hc : |cNext - midpt (tanh (bias + ∑ j ∈ s, w j * c j))
        (tanh ((∑ j ∈ s, |w j|) * rPrev))| ≤ ε)
    (hround : tanh (g * rPrev) + 2 * ε ≤ rNext) :
    |tanh (bias + ∑ j ∈ s, w j * h j) - cNext| ≤ rNext := by
  set a := bias + ∑ j ∈ s, w j * c j with ha
  set σ := ∑ j ∈ s, |w j| with hσdef
  have hσ0 : 0 ≤ σ := Finset.sum_nonneg (fun j _ => abs_nonneg (w j))
  have hdiff : (bias + ∑ j ∈ s, w j * h j) - a = ∑ j ∈ s, w j * (h j - c j) := by
    rw [ha]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have hpre : |(bias + ∑ j ∈ s, w j * h j) - a| ≤ σ * rPrev := by
    rw [hdiff]
    calc |∑ j ∈ s, w j * (h j - c j)| ≤ ∑ j ∈ s, |w j * (h j - c j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ s, |w j| * rPrev := by
          apply Finset.sum_le_sum
          intro j hj
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hh j hj) (abs_nonneg _)
      _ = σ * rPrev := by rw [hσdef, Finset.sum_mul]
  have hR := abs_tanh_sub_midpt_le a (σ * rPrev) _ hpre
  have hbudget := radius_add_center_error_le a σ rPrev rNext cNext g ε hσ0 hr hσ hc hround
  calc |tanh (bias + ∑ j ∈ s, w j * h j) - cNext|
      ≤ |tanh (bias + ∑ j ∈ s, w j * h j) - midpt (tanh a) (tanh (σ * rPrev))|
        + |midpt (tanh a) (tanh (σ * rPrev)) - cNext| := abs_sub_le _ _ _
    _ ≤ rNext := by linarith

/-- Activations of the network `eq:network` (`tanh_model.tex`): layer `0` is the input and
layer `ℓ + 1` applies `tanh` to the affine row with weights `W (ℓ + 1)` and biases
`b (ℓ + 1)`. -/
noncomputable def activation {n : ℕ} (W : ℕ → Fin n → Fin n → ℝ) (b : ℕ → Fin n → ℝ)
    (x : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => x
  | ℓ + 1 => fun i => tanh (b (ℓ + 1) i + ∑ j, W (ℓ + 1) i j * activation W b x ℓ j)

/-- The interval invariant `|h_{ℓ,i} - c_{ℓ,i}| ≤ r_ℓ` for every layer and every context.
The centers are any values within `ε` of the exact midpoints, and the radii obey the lower
half of the rounding rule `eq:rounded` with reference gain `g` bounding every row norm.
Paper: `lem:interval` (`tanh_scalar.tex`), with `eq:rounded` and `eq:rowdata`. The input
hypothesis `|x_j| ≤ 1` is weaker than `x_j ∈ {-1, 1}`. -/
theorem interval_invariant {n : ℕ} (W : ℕ → Fin n → Fin n → ℝ) (b : ℕ → Fin n → ℝ)
    (x : Fin n → ℝ) (c : ℕ → Fin n → ℝ) (r : ℕ → ℝ) (g ε : ℝ)
    (hx : ∀ j, |x j| ≤ 1) (hc0 : ∀ j, c 0 j = 0) (hr0 : r 0 = 1) (hg : 0 ≤ g) (hε : 0 ≤ ε)
    (hS : ∀ ℓ i, ∑ j, |W (ℓ + 1) i j| ≤ g)
    (hc : ∀ ℓ i, |c (ℓ + 1) i - midpt (tanh (b (ℓ + 1) i + ∑ j, W (ℓ + 1) i j * c ℓ j))
        (tanh ((∑ j, |W (ℓ + 1) i j|) * r ℓ))| ≤ ε)
    (hround : ∀ ℓ, tanh (g * r ℓ) + 2 * ε ≤ r (ℓ + 1)) :
    ∀ ℓ i, |activation W b x ℓ i - c ℓ i| ≤ r ℓ := by
  have hrnn : ∀ ℓ, 0 ≤ r ℓ := by
    intro ℓ
    induction ℓ with
    | zero => rw [hr0]; norm_num
    | succ ℓ ih =>
        have := tanh_nonneg_of_nonneg (mul_nonneg hg ih)
        linarith [hround ℓ]
  intro ℓ
  induction ℓ with
  | zero =>
      intro i
      simp only [activation, hc0, sub_zero, hr0]
      exact hx i
  | succ ℓ ih =>
      intro i
      exact interval_step Finset.univ (W (ℓ + 1) i) (activation W b x ℓ) (c ℓ) (b (ℓ + 1) i)
        (r ℓ) (r (ℓ + 1)) (c (ℓ + 1) i) g ε (hrnn ℓ) (fun j _ => ih j) (hS ℓ i) (hc ℓ i)
        (hround ℓ)

/-! ### Normalized source signs and the centered factory -/

/-- The weighted coordinate request: the preactivation equals `a + ρ z`, where
`z = Σ_j (w_j / σ) v_j` is the mean of the normalized source sign and `ρ = σ r_{ℓ-1}`.
Paper: Section `sec:algorithm` (`tanh_scalar.tex`), display before `eq:centered`. -/
theorem preactivation_eq {ι : Type*} (s : Finset ι) (w h c : ι → ℝ) (bias r : ℝ)
    (hσ : ∑ j ∈ s, |w j| ≠ 0) (hr : r ≠ 0) :
    bias + ∑ j ∈ s, w j * h j =
      (bias + ∑ j ∈ s, w j * c j) +
        ((∑ j ∈ s, |w j|) * r) * ∑ j ∈ s, (w j / ∑ k ∈ s, |w k|) * ((h j - c j) / r) := by
  have hterm : ∀ j ∈ s, ((∑ k ∈ s, |w k|) * r) * ((w j / ∑ k ∈ s, |w k|) * ((h j - c j) / r))
      = w j * h j - w j * c j := by
    intro j _
    field_simp
  rw [Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  ring

/-- The normalized source mean lies in `[-1, 1]` when every predecessor mean does.
Paper: Section `sec:algorithm` (`tanh_scalar.tex`), the source of mean `z`. -/
theorem abs_source_mean_le_one {ι : Type*} (s : Finset ι) (w v : ι → ℝ)
    (hσ : 0 < ∑ j ∈ s, |w j|) (hv : ∀ j ∈ s, |v j| ≤ 1) :
    |∑ j ∈ s, (w j / ∑ k ∈ s, |w k|) * v j| ≤ 1 := by
  calc |∑ j ∈ s, (w j / ∑ k ∈ s, |w k|) * v j|
      ≤ ∑ j ∈ s, |(w j / ∑ k ∈ s, |w k|) * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ s, |w j| / ∑ k ∈ s, |w k| := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_div, abs_of_pos hσ]
        calc |w j| / (∑ k ∈ s, |w k|) * |v j| ≤ |w j| / (∑ k ∈ s, |w k|) * 1 :=
              mul_le_mul_of_nonneg_left (hv j hj) (by positivity)
          _ = |w j| / ∑ k ∈ s, |w k| := mul_one _
    _ = 1 := by rw [← Finset.sum_div, div_self hσ.ne']

/-- The bias identity `tanh (a + ρ z) = m + R T_{tq}(G_ρ(z))` with
`G_ρ(z) = tanh (ρ z) / tanh ρ`. Paper: `eq:biasidentity` (`tanh_scalar.tex`). -/
theorem bias_identity (a ρ z : ℝ) (hρ : 0 < ρ) :
    tanh (a + ρ * z) =
      midpt (tanh a) (tanh ρ) +
        imgRadius (tanh a) (tanh ρ) * mobius (tanh a * tanh ρ) (tanh (ρ * z) / tanh ρ) := by
  have hq : tanh ρ ≠ 0 := (tanh_pos_of_pos hρ).ne'
  have hmul : tanh ρ * (tanh (ρ * z) / tanh ρ) = tanh (ρ * z) := by field_simp
  have h0 : 1 - tanh a ^ 2 * tanh ρ ^ 2 ≠ 0 := (one_sub_sq_mul_sq_pos a ρ).ne'
  have h1 : 1 + tanh a * tanh (ρ * z) ≠ 0 := (one_add_tanh_mul_pos a (ρ * z)).ne'
  rw [tanh_add_formula]
  unfold midpt imgRadius mobius
  rw [mul_assoc, hmul]
  field_simp
  ring

/-- The centered factory target `G = (tanh (a + ρ z) - m) / R` of `eq:centered` equals the
Möbius image `T_{tq}(G_ρ(z))`. Paper: `eq:centered` and `eq:biasidentity`
(`tanh_scalar.tex`). -/
theorem centered_eq_mobius (a ρ z : ℝ) (hρ : 0 < ρ) :
    (tanh (a + ρ * z) - midpt (tanh a) (tanh ρ)) / imgRadius (tanh a) (tanh ρ) =
      mobius (tanh a * tanh ρ) (tanh (ρ * z) / tanh ρ) := by
  have hR := (imgRadius_pos a hρ).ne'
  rw [bias_identity a ρ z hρ]
  field_simp
  ring

/-! ### The internal and top mixtures -/

/-- The internal three-way mixture: with `α = R / r` and `κ = (m - c) / r`, the gate and the two
constant signs have nonnegative probabilities summing to one, and the resulting mean is the
normalized value `(h - c) / r`. Paper: `eq:internalmixture` (`tanh_scalar.tex`). -/
theorem internal_mixture (h c m R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hinv : R + |m - c| ≤ r) :
    0 ≤ R / r ∧ 0 ≤ (1 - R / r + (m - c) / r) / 2 ∧ 0 ≤ (1 - R / r - (m - c) / r) / 2 ∧
      R / r + (1 - R / r + (m - c) / r) / 2 + (1 - R / r - (m - c) / r) / 2 = 1 ∧
      R / r * ((h - m) / R) + (m - c) / r = (h - c) / r := by
  have hsum : R / r + |m - c| / r ≤ 1 := by
    rw [← add_div, div_le_one hr]; exact hinv
  have hk1 : (m - c) / r ≤ |m - c| / r := div_le_div_of_nonneg_right (le_abs_self _) hr.le
  have hk2 : -((m - c) / r) ≤ |m - c| / r := by
    rw [← neg_div]; exact div_le_div_of_nonneg_right (neg_le_abs _) hr.le
  refine ⟨by positivity, by linarith, by linarith, by ring, ?_⟩
  field_simp
  ring

/-- The plus probability of the internal mixture is `(1 + v) / 2` for its signed mean `v`.
Paper: `eq:internalmixture` (`tanh_scalar.tex`). -/
theorem mixture_plus_probability (α κ G : ℝ) :
    α * ((1 + G) / 2) + (1 - α + κ) / 2 = (1 + (α * G + κ)) / 2 := by ring

/-- The top mixture is valid: `|m| + R < 1`. Paper: `eq:topmixture` (`tanh_scalar.tex`). -/
theorem top_mixture_valid (a ρ : ℝ) :
    |midpt (tanh a) (tanh ρ)| + imgRadius (tanh a) (tanh ρ) < 1 := by
  rw [← endpoint_midpoint, ← endpoint_radius]
  have h1 := tanh_lt_one (a + ρ)
  have h2 := neg_one_lt_tanh (a - ρ)
  rcases abs_cases ((tanh (a + ρ) + tanh (a - ρ)) / 2) with ⟨h, _⟩ | ⟨h, _⟩ <;>
    rw [h] <;> linarith

/-- The top mixture produces an output bit of probability `(1 + h) / 2`, where the centered
factory has mean `(h - m) / R`. Paper: `eq:topmixture` (`tanh_scalar.tex`). -/
theorem top_mixture_probability (h m R : ℝ) (hR : R ≠ 0) :
    R * ((1 + (h - m) / R) / 2) + (1 - R + m) / 2 = (1 + h) / 2 := by
  field_simp
  ring

/-! ### The exact odds race for a nonnegative bias parameter -/

/-- The return probability `λ = (1 - θ) / (1 + θ)` after a minus sign in the race of
Section `sec:bias` (`tanh_scalar.tex`). -/
noncomputable def raceLambda (θ : ℝ) : ℝ := (1 - θ) / (1 + θ)

/-- The success probability `σ = p + (1 - p) λ` of one race trial when the source has plus
probability `p`. Section `sec:bias` (`tanh_scalar.tex`). -/
noncomputable def raceSuccess (θ p : ℝ) : ℝ := p + (1 - p) * raceLambda θ

/-- `σ (1 + θ) = 1 + θ (2p - 1)`. Paper: Section `sec:bias` (`tanh_scalar.tex`). -/
theorem raceSuccess_eq (θ p : ℝ) (h : 1 + θ ≠ 0) :
    raceSuccess θ p = (1 + θ * (2 * p - 1)) / (1 + θ) := by
  unfold raceSuccess raceLambda
  field_simp
  ring

/-- `λ > 0` for `0 ≤ θ < 1`. Auxiliary for Section `sec:bias` (`tanh_scalar.tex`). -/
theorem raceLambda_pos {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) : 0 < raceLambda θ := by
  unfold raceLambda
  apply div_pos <;> linarith

/-- `λ ≤ 1` for `θ ≥ 0`, so `λ` is a probability. Auxiliary for Section `sec:bias`
(`tanh_scalar.tex`). -/
theorem raceLambda_le_one {θ : ℝ} (h0 : 0 ≤ θ) : raceLambda θ ≤ 1 := by
  unfold raceLambda
  rw [div_le_one (by linarith)]
  linarith

/-- A race trial succeeds with positive probability. Paper: Section `sec:bias`
(`tanh_scalar.tex`). -/
theorem raceSuccess_pos {θ p : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hp0 : 0 ≤ p) :
    0 < raceSuccess θ p := by
  rw [raceSuccess_eq θ p (by linarith)]
  apply div_pos _ (by linarith)
  nlinarith

/-- The failure probability of one trial is `(1 - p)(1 - λ)`. Auxiliary for Section `sec:bias`
(`tanh_scalar.tex`). -/
theorem one_sub_raceSuccess (θ p : ℝ) :
    1 - raceSuccess θ p = (1 - p) * (1 - raceLambda θ) := by
  unfold raceSuccess
  ring

/-- The failure probability of a trial is nonnegative. Auxiliary for Section `sec:bias`
(`tanh_scalar.tex`). -/
theorem one_sub_raceSuccess_nonneg {θ p : ℝ} (h0 : 0 ≤ θ) (hp1 : p ≤ 1) :
    0 ≤ 1 - raceSuccess θ p := by
  rw [one_sub_raceSuccess]
  exact mul_nonneg (by linarith) (by linarith [raceLambda_le_one h0])

/-- The accepted plus probability `p / σ` has signed mean `T_θ(2p - 1)`.
Paper: Section `sec:bias` (`tanh_scalar.tex`), exactness of the race. -/
theorem race_accepted_mean {θ p : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hp0 : 0 ≤ p) :
    2 * (p / raceSuccess θ p) - 1 = mobius θ (2 * p - 1) := by
  have hplus : 0 < 1 + θ := by linarith
  have hden : 0 < 1 + θ * (2 * p - 1) := by nlinarith
  rw [raceSuccess_eq θ p hplus.ne']
  unfold mobius
  field_simp
  ring

/-- The race returns `+1` with total probability `p / σ`: summing over the number `k` of
failed trials, `Σ_k (1 - σ)^k p = p / σ`. Paper: Section `sec:bias` (`tanh_scalar.tex`). -/
theorem race_plus_hasSum {θ p : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    HasSum (fun k : ℕ => (1 - raceSuccess θ p) ^ k * p) (p / raceSuccess θ p) := by
  have hσ := raceSuccess_pos h0 h1 hp0
  have hg := hasSum_geometric_of_lt_one (one_sub_raceSuccess_nonneg h0 hp1) (by linarith)
  have := hg.mul_right p
  simpa [sub_sub_cancel, div_eq_inv_mul] using this

/-- The race returns `-1` with total probability `(1 - p) λ / σ`.
Paper: Section `sec:bias` (`tanh_scalar.tex`). -/
theorem race_minus_hasSum {θ p : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    HasSum (fun k : ℕ => (1 - raceSuccess θ p) ^ k * ((1 - p) * raceLambda θ))
      ((1 - p) * raceLambda θ / raceSuccess θ p) := by
  have hσ := raceSuccess_pos h0 h1 hp0
  have hg := hasSum_geometric_of_lt_one (one_sub_raceSuccess_nonneg h0 hp1) (by linarith)
  have := hg.mul_right ((1 - p) * raceLambda θ)
  simpa [sub_sub_cancel, div_eq_inv_mul] using this

/-- The two outputs exhaust the probability: the race terminates almost surely.
Paper: Section `sec:bias` (`tanh_scalar.tex`). -/
theorem race_output_total {θ p : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hp0 : 0 ≤ p) :
    p / raceSuccess θ p + (1 - p) * raceLambda θ / raceSuccess θ p = 1 := by
  have hσ := raceSuccess_pos h0 h1 hp0
  rw [← add_div, div_eq_one_iff_eq hσ.ne']
  rfl

/-- The tail probabilities `(1 - σ)^k` of the number of race trials (the probability that the
first `k` independent trials all fail) sum to `1 / σ`. Paper: `lem:stopping`
(`tanh_scalar.tex`), the independent case `E T = 1 / σ`. -/
theorem race_expected_trials {θ p : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    HasSum (fun k : ℕ => (1 - raceSuccess θ p) ^ k) (1 / raceSuccess θ p) := by
  have hσ := raceSuccess_pos h0 h1 hp0
  have hg := hasSum_geometric_of_lt_one (one_sub_raceSuccess_nonneg h0 hp1) (by linarith)
  simpa [sub_sub_cancel, one_div] using hg

/-- The first-step identity of the race: if `q = p + (1 - p)(1 - λ) q`, then
`q = p / (p + λ (1 - p))`. Paper: Section `sec:bias` (`tanh_scalar.tex`), the accepted plus
probability `p / σ`. -/
theorem race_output_fixed_point (p lam q : ℝ) (hden : p + lam * (1 - p) ≠ 0)
    (hrec : q = p + (1 - p) * (1 - lam) * q) : q = p / (p + lam * (1 - p)) := by
  rw [eq_div_iff hden]
  linarith [hrec]

/-- For a negative bias the race runs on complemented signs: complementing the source and the
output turns `T_{-θ}` into `T_θ`. Paper: Section `sec:bias` (`tanh_scalar.tex`), last sentence
of the race paragraph. -/
theorem mobius_complement (θ u : ℝ) : -mobius (-θ) (-u) = mobius θ u := by
  unfold mobius
  rw [show 1 + -θ * -u = 1 + θ * u by ring, show -u + -θ = -(u + θ) by ring, neg_div, neg_neg]

/-! ### The race inside the factory and the joint cost identity -/

/-- With source plus probability `(1 + G_ρ(z)) / 2` and `θ = t q`, the race succeeds with
probability `(1 + t u) / (1 + t q)`, where `u = tanh (ρ z)`.
Paper: `lem:offspring` (`tanh_scalar.tex`), the race factor in `eq:jointcost`. -/
theorem raceSuccess_factory (a ρ z : ℝ) (hρ : 0 < ρ) :
    raceSuccess (tanh a * tanh ρ) ((1 + tanh (ρ * z) / tanh ρ) / 2) =
      (1 + tanh a * tanh (ρ * z)) / (1 + tanh a * tanh ρ) := by
  have hq : tanh ρ ≠ 0 := (tanh_pos_of_pos hρ).ne'
  rw [raceSuccess_eq _ _ (one_add_tanh_mul_pos a ρ).ne']
  congr 1
  field_simp
  ring

/-- The complemented race used when `t < 0`: its success probability is
`(1 + t u) / (1 - t q)`. Paper: `lem:offspring` (`tanh_scalar.tex`), negative `t`. -/
theorem raceSuccess_factory_complement (a ρ z : ℝ) (hρ : 0 < ρ) :
    raceSuccess (-(tanh a * tanh ρ)) ((1 - tanh (ρ * z) / tanh ρ) / 2) =
      (1 + tanh a * tanh (ρ * z)) / (1 - tanh a * tanh ρ) := by
  have hq : tanh ρ ≠ 0 := (tanh_pos_of_pos hρ).ne'
  have h := (one_sub_tanh_mul_pos a ρ).ne'
  rw [raceSuccess_eq _ _ (by rw [← sub_eq_add_neg]; exact h)]
  rw [← sub_eq_add_neg]
  congr 1
  field_simp
  ring

/-- `|tanh x| = tanh |x|`. Auxiliary for `abs_G_le_one`. -/
theorem abs_tanh_eq (x : ℝ) : |tanh x| = tanh |x| := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (tanh_nonneg_of_nonneg h)]
  · rw [abs_of_nonpos h, tanh_neg, abs_of_nonpos]
    have := tanh_nonneg_of_nonneg (neg_nonneg.mpr h)
    rw [tanh_neg] at this
    linarith

/-- `|G_ρ(z)| ≤ 1` for `|z| ≤ 1`, so the source plus probabilities `(1 ± G_ρ(z))/2` of the race
lie in `[0, 1]`. Paper: Section `sec:majority` (`tanh_scalar.tex`), `G_ρ(z) = tanh(ρz)/tanh ρ`. -/
theorem abs_G_le_one {ρ z : ℝ} (hρ : 0 < ρ) (hz : |z| ≤ 1) : |tanh (ρ * z) / tanh ρ| ≤ 1 := by
  have hq := tanh_pos_of_pos hρ
  rw [abs_div, abs_of_pos hq, div_le_one hq, abs_tanh_eq]
  apply tanh_le_tanh
  rw [abs_mul, abs_of_pos hρ]
  nlinarith [abs_nonneg z]

/-- End-to-end exactness of the bias step for a nonnegative stored bias: the race with
`θ = t q` run on a source of plus probability `p = (1 + G_ρ(z))/2` returns a sign of mean
`(tanh (a + ρ z) - m)/R`, the centered factory target. Paper: `eq:centered`,
`eq:biasidentity`, and the race of Section `sec:bias` (`tanh_scalar.tex`). -/
theorem race_realizes_centered {a ρ z : ℝ} (ha : 0 ≤ a) (hρ : 0 < ρ) (hz : |z| ≤ 1) :
    2 * ((1 + tanh (ρ * z) / tanh ρ) / 2 /
        raceSuccess (tanh a * tanh ρ) ((1 + tanh (ρ * z) / tanh ρ) / 2)) - 1 =
      (tanh (a + ρ * z) - midpt (tanh a) (tanh ρ)) / imgRadius (tanh a) (tanh ρ) := by
  have hG := abs_le.mp (abs_G_le_one hρ hz)
  have ht := tanh_nonneg_of_nonneg ha
  have hq := tanh_pos_of_pos hρ
  have h1 : tanh a * tanh ρ < 1 := (abs_lt.mp (abs_tanh_mul_lt_one a ρ)).2
  rw [race_accepted_mean (mul_nonneg ht hq.le) h1 (by linarith [hG.1]),
    centered_eq_mobius a ρ z hρ,
    show 2 * ((1 + tanh (ρ * z) / tanh ρ) / 2) - 1 = tanh (ρ * z) / tanh ρ by ring]

/-- End-to-end exactness of the bias step for a nonpositive stored bias: the race with
parameter `-t q ≥ 0` run on the complemented source of plus probability `(1 - G_ρ(z))/2`, with
its output complemented, returns a sign of mean `(tanh (a + ρ z) - m)/R`.
Paper: Section `sec:bias` (`tanh_scalar.tex`), "for negative `θ`, complement the source and the
output", with `eq:centered`. -/
theorem race_realizes_centered_complement {a ρ z : ℝ} (ha : a ≤ 0) (hρ : 0 < ρ)
    (hz : |z| ≤ 1) :
    -(2 * ((1 - tanh (ρ * z) / tanh ρ) / 2 /
        raceSuccess (-(tanh a * tanh ρ)) ((1 - tanh (ρ * z) / tanh ρ) / 2)) - 1) =
      (tanh (a + ρ * z) - midpt (tanh a) (tanh ρ)) / imgRadius (tanh a) (tanh ρ) := by
  have hG := abs_le.mp (abs_G_le_one hρ hz)
  have ht : tanh a ≤ 0 := by
    have := tanh_nonneg_of_nonneg (neg_nonneg.mpr ha)
    rw [tanh_neg] at this
    linarith
  have hq := tanh_pos_of_pos hρ
  have h0 : 0 ≤ -(tanh a * tanh ρ) := by nlinarith
  have h1 : -(tanh a * tanh ρ) < 1 := by
    have := (abs_lt.mp (abs_tanh_mul_lt_one a ρ)).1
    linarith
  rw [race_accepted_mean h0 h1 (by linarith [hG.2]),
    show 2 * ((1 - tanh (ρ * z) / tanh ρ) / 2) - 1 = -(tanh (ρ * z) / tanh ρ) by ring,
    mobius_complement, centered_eq_mobius a ρ z hρ]

/-- The joint cost identity: the gate `R` divided by the race success probability equals
`q (1 - t²) / ((1 - t q)(1 + t u))`. Paper: `eq:jointcost` (`tanh_scalar.tex`). -/
theorem joint_cost_identity (a ρ z : ℝ) (hρ : 0 < ρ) :
    imgRadius (tanh a) (tanh ρ) /
        raceSuccess (tanh a * tanh ρ) ((1 + tanh (ρ * z) / tanh ρ) / 2) =
      tanh ρ * ((1 - tanh a ^ 2) /
        ((1 - tanh a * tanh ρ) * (1 + tanh a * tanh (ρ * z)))) := by
  rw [raceSuccess_factory a ρ z hρ]
  unfold imgRadius
  have h1 := (one_add_tanh_mul_pos a ρ).ne'
  have h2 := (one_sub_tanh_mul_pos a ρ).ne'
  have h3 := (one_add_tanh_mul_pos a (ρ * z)).ne'
  have h1' := (one_add_tanh_mul_pos ρ a).ne'
  have h2' := (one_sub_tanh_mul_pos ρ a).ne'
  rw [one_sub_sq_mul_sq_eq]
  field_simp

/-- The joint cost identity for the complemented race (negative `t`).
Paper: `lem:offspring` (`tanh_scalar.tex`), negative `t`. -/
theorem joint_cost_identity_complement (a ρ z : ℝ) (hρ : 0 < ρ) :
    imgRadius (tanh a) (tanh ρ) /
        raceSuccess (-(tanh a * tanh ρ)) ((1 - tanh (ρ * z) / tanh ρ) / 2) =
      tanh ρ * ((1 - tanh a ^ 2) /
        ((1 + tanh a * tanh ρ) * (1 + tanh a * tanh (ρ * z)))) := by
  rw [raceSuccess_factory_complement a ρ z hρ]
  unfold imgRadius
  have h1 := (one_add_tanh_mul_pos a ρ).ne'
  have h2 := (one_sub_tanh_mul_pos a ρ).ne'
  have h3 := (one_add_tanh_mul_pos a (ρ * z)).ne'
  have h1' := (one_add_tanh_mul_pos ρ a).ne'
  have h2' := (one_sub_tanh_mul_pos ρ a).ne'
  rw [one_sub_sq_mul_sq_eq]
  field_simp

/-! ### The hyperbolic race factor and the offspring bound -/

/-- The race factor in hyperbolic form:
`(1 - t²) / ((1 - t q)(1 + t u)) = cosh ρ cosh (ρ z) / (cosh (a - ρ) cosh (a + ρ z))`.
Paper: `lem:offspring` (`tanh_scalar.tex`), the factor `K`. -/
theorem race_factor_eq (a ρ z : ℝ) :
    (1 - tanh a ^ 2) / ((1 - tanh a * tanh ρ) * (1 + tanh a * tanh (ρ * z))) =
      cosh ρ * cosh (ρ * z) / (cosh (a - ρ) * cosh (a + ρ * z)) := by
  have ca := cosh_pos a
  have cr := cosh_pos ρ
  have cz := cosh_pos (ρ * z)
  have c1 := cosh_pos (a - ρ)
  have c2 := cosh_pos (a + ρ * z)
  have e1 : 1 - tanh a * tanh ρ = cosh (a - ρ) / (cosh a * cosh ρ) := by
    rw [tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh, cosh_sub]
    field_simp
  have e2 : 1 + tanh a * tanh (ρ * z) = cosh (a + ρ * z) / (cosh a * cosh (ρ * z)) := by
    rw [tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh, cosh_add]
    field_simp
  rw [one_sub_tanh_sq, e1, e2]
  field_simp

/-- The product-to-sum lower bound `cosh (a - ρ) cosh (a + ρ z) ≥ cosh² (ρ (1 + z) / 2)`,
uniformly in the bias `a`. Paper: `lem:offspring` (`tanh_scalar.tex`). -/
theorem cosh_sq_half_le (a ρ z : ℝ) :
    cosh (ρ * (1 + z) / 2) ^ 2 ≤ cosh (a - ρ) * cosh (a + ρ * z) := by
  have key : ∀ x y : ℝ, cosh x * cosh y = (cosh (x + y) + cosh (x - y)) / 2 := by
    intro x y; rw [cosh_add, cosh_sub]; ring
  have e1 := key (a - ρ) (a + ρ * z)
  have e2 : cosh (ρ * (1 + z) / 2) ^ 2 = (1 + cosh (2 * (ρ * (1 + z) / 2))) / 2 := by
    rw [cosh_two_mul, cosh_sq']; ring
  have e3 : cosh ((a - ρ) - (a + ρ * z)) = cosh (2 * (ρ * (1 + z) / 2)) := by
    rw [show (a - ρ) - (a + ρ * z) = -(2 * (ρ * (1 + z) / 2)) by ring, cosh_neg]
  have h1 := one_le_cosh ((a - ρ) + (a + ρ * z))
  rw [e1, e2, e3]
  linarith

/-- `cosh x cosh y ≤ cosh² ((x + y)/2) · exp (((x - y)/2)²)`: the midpoint second-difference
bound for `log cosh`. Auxiliary for `lem:offspring` (`tanh_scalar.tex`). -/
theorem cosh_mul_cosh_le (x y : ℝ) :
    cosh x * cosh y ≤ cosh ((x + y) / 2) ^ 2 * exp (((x - y) / 2) ^ 2) := by
  set m := (x + y) / 2
  set d := (x - y) / 2
  have hx : x = m + d := by simp only [m, d]; ring
  have hy : y = m - d := by simp only [m, d]; ring
  have hid : cosh x * cosh y = cosh m ^ 2 + sinh d ^ 2 := by
    rw [hx, hy, cosh_add, cosh_sub]
    have h1 := cosh_sq' m
    have h2 := cosh_sq' d
    nlinarith [h1, h2]
  have hcd : cosh d ^ 2 ≤ exp (d ^ 2) := by
    have h := cosh_le_exp_half_sq d
    have h0 : 0 ≤ cosh d := (cosh_pos d).le
    calc cosh d ^ 2 ≤ exp (d ^ 2 / 2) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = exp (d ^ 2) := by rw [← exp_nat_mul]; ring_nf
  have hm1 : 1 ≤ cosh m ^ 2 := by nlinarith [one_le_cosh m]
  have hs : 0 ≤ sinh d ^ 2 := sq_nonneg _
  have hcd' : cosh d ^ 2 = 1 + sinh d ^ 2 := cosh_sq' d
  rw [hid]
  calc cosh m ^ 2 + sinh d ^ 2 ≤ cosh m ^ 2 * (1 + sinh d ^ 2) := by nlinarith
    _ = cosh m ^ 2 * cosh d ^ 2 := by rw [hcd']
    _ ≤ cosh m ^ 2 * exp (d ^ 2) := mul_le_mul_of_nonneg_left hcd (by positivity)

/-- The race factor is at most `exp (ρ² (1 - z)² / 4)`, uniformly in the bias.
Paper: `lem:offspring` (`tanh_scalar.tex`), the bound `log K ≤ ρ² (1 - z)² / 4`. -/
theorem race_factor_le (a ρ z : ℝ) :
    (1 - tanh a ^ 2) / ((1 - tanh a * tanh ρ) * (1 + tanh a * tanh (ρ * z))) ≤
      exp (ρ ^ 2 * (1 - z) ^ 2 / 4) := by
  rw [race_factor_eq]
  have hlow := cosh_sq_half_le a ρ z
  have hpos : 0 < cosh (ρ * (1 + z) / 2) ^ 2 := by have := cosh_pos (ρ * (1 + z) / 2); positivity
  have hnum := cosh_mul_cosh_le ρ (ρ * z)
  have hm : (ρ + ρ * z) / 2 = ρ * (1 + z) / 2 := by ring
  have hd : ((ρ - ρ * z) / 2) ^ 2 = ρ ^ 2 * (1 - z) ^ 2 / 4 := by ring
  rw [hm, hd] at hnum
  have hden : 0 < cosh (a - ρ) * cosh (a + ρ * z) := lt_of_lt_of_le hpos hlow
  rw [div_le_iff₀ hden]
  calc cosh ρ * cosh (ρ * z) ≤ cosh (ρ * (1 + z) / 2) ^ 2 * exp (ρ ^ 2 * (1 - z) ^ 2 / 4) :=
        hnum
    _ ≤ exp (ρ ^ 2 * (1 - z) ^ 2 / 4) * (cosh (a - ρ) * cosh (a + ρ * z)) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hlow (exp_pos _).le

/-- Completion of a square for the race factor. Auxiliary for `race_factor_upper_bound`. -/
theorem race_square_identity (t q u d : ℝ) :
    (1 - q * u + d) * (2 * ((1 - t * q) * (1 + t * u)) - (1 - t ^ 2) * (1 + q * u + d)) =
      ((1 - q * u + d) * t - (q - u)) ^ 2 + ((1 - q ^ 2) * (1 - u ^ 2) - d ^ 2) := by
  ring

/-- The race factor is at most `2 / (1 + q u + d)` with `d² = (1 - q²)(1 - u²)`, uniformly in
`t`. Algebraic form of the bound `K ≤ cosh ρ cosh (ρ z) / cosh² (ρ (1+z)/2)` of
`lem:offspring` (`tanh_scalar.tex`); see `race_factor_bound_eq`. -/
theorem race_factor_upper_bound (t q u d : ℝ) (hsq : d ^ 2 = (1 - q ^ 2) * (1 - u ^ 2))
    (hcoef : 0 < 1 - q * u + d) (hbase : 0 < 1 + q * u + d)
    (hden : 0 < (1 - t * q) * (1 + t * u)) :
    (1 - t ^ 2) / ((1 - t * q) * (1 + t * u)) ≤ 2 / (1 + q * u + d) := by
  have hs := race_square_identity t q u d
  have hnonneg : 0 ≤ 2 * ((1 - t * q) * (1 + t * u)) - (1 - t ^ 2) * (1 + q * u + d) := by
    have hp : 0 ≤ (1 - q * u + d) *
        (2 * ((1 - t * q) * (1 + t * u)) - (1 - t ^ 2) * (1 + q * u + d)) := by
      rw [hs, ← hsq]
      nlinarith [sq_nonneg ((1 - q * u + d) * t - (q - u))]
    rcases mul_nonneg_iff.mp hp with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · linarith
  rw [div_le_div_iff₀ hden hbase]
  nlinarith

/-- With `q = tanh ρ`, `u = tanh (ρ z)`, and `d = sech ρ sech (ρ z)`, the algebraic bound equals
the hyperbolic one: `2 / (1 + q u + d) = cosh ρ cosh (ρ z) / cosh² (ρ (1 + z)/2)`.
Paper: `lem:offspring` (`tanh_scalar.tex`). -/
theorem race_factor_bound_eq (ρ z : ℝ) :
    2 / (1 + tanh ρ * tanh (ρ * z) + 1 / (cosh ρ * cosh (ρ * z))) =
      cosh ρ * cosh (ρ * z) / cosh (ρ * (1 + z) / 2) ^ 2 := by
  have c1 := cosh_pos ρ
  have c2 := cosh_pos (ρ * z)
  have c3 := cosh_pos (ρ * (1 + z) / 2)
  have hhalf : cosh (ρ * (1 + z) / 2) ^ 2 = (1 + cosh (ρ + ρ * z)) / 2 := by
    have := cosh_two_mul (ρ * (1 + z) / 2)
    rw [show 2 * (ρ * (1 + z) / 2) = ρ + ρ * z by ring, cosh_sq'] at this
    rw [cosh_sq']
    linarith
  have hsum : cosh (ρ + ρ * z) = cosh ρ * cosh (ρ * z) + sinh ρ * sinh (ρ * z) := cosh_add _ _
  rw [hhalf, hsum, tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh]
  have hpos : 0 < 1 + cosh ρ * cosh (ρ * z) + sinh ρ * sinh (ρ * z) := by
    have := cosh_add ρ (ρ * z)
    have := cosh_pos (ρ + ρ * z)
    linarith
  field_simp
  ring

/-- The quadratic coefficient after combining the majority and race factors is at most `5/3`.
Paper: `lem:offspring` (`tanh_scalar.tex`), last display of the proof. -/
theorem joint_quadratic_coefficient (u : ℝ) (hu1 : u ≤ 1) :
    1 - u ^ 2 / 3 + (1 + u) ^ 2 / 4 ≤ 5 / 3 := by
  have hprod : 0 ≤ (1 - u) * (5 - u) := by apply mul_nonneg <;> linarith
  nlinarith

/-- Combination of the sequential majority bound `A ≤ 1 + (1 - z²/3) ρ² + ρ⁴` (the conclusion
of `lem:arity`, proved in `ExactSampling.MajorityArity` from the stand-in `eq:arityintegral`)
with a race factor
`K ≤ exp (ρ² (1 + |z|)² / 4)`: `A K ≤ exp (5ρ²/3 + ρ⁴)`.
Paper: `lem:offspring` (`tanh_scalar.tex`). -/
theorem arity_mul_race_le (A K z ρ : ℝ) (hz : |z| ≤ 1)
    (hA : A ≤ 1 + (1 - z ^ 2 / 3) * ρ ^ 2 + ρ ^ 4) (hK0 : 0 ≤ K)
    (hK : K ≤ exp (ρ ^ 2 * (1 + |z|) ^ 2 / 4)) :
    A * K ≤ exp (5 / 3 * ρ ^ 2 + ρ ^ 4) := by
  have hAexp : A ≤ exp ((1 - z ^ 2 / 3) * ρ ^ 2 + ρ ^ 4) :=
    hA.trans (by linarith [add_one_le_exp ((1 - z ^ 2 / 3) * ρ ^ 2 + ρ ^ 4)])
  have hcoef := joint_quadratic_coefficient |z| hz
  rw [sq_abs] at hcoef
  have hexp : (1 - z ^ 2 / 3) * ρ ^ 2 + ρ ^ 4 + ρ ^ 2 * (1 + |z|) ^ 2 / 4 ≤
      5 / 3 * ρ ^ 2 + ρ ^ 4 := by nlinarith [sq_nonneg ρ]
  calc A * K ≤ exp ((1 - z ^ 2 / 3) * ρ ^ 2 + ρ ^ 4) * exp (ρ ^ 2 * (1 + |z|) ^ 2 / 4) :=
        mul_le_mul hAexp hK hK0 (exp_pos _).le
    _ = exp ((1 - z ^ 2 / 3) * ρ ^ 2 + ρ ^ 4 + ρ ^ 2 * (1 + |z|) ^ 2 / 4) := by
        rw [← exp_add]
    _ ≤ exp (5 / 3 * ρ ^ 2 + ρ ^ 4) := exp_le_exp.mpr hexp

/-- The race factor `K` is nonnegative. Auxiliary for `lem:offspring` (`tanh_scalar.tex`). -/
theorem race_factor_nonneg (a ρ z : ℝ) :
    0 ≤ (1 - tanh a ^ 2) / ((1 - tanh a * tanh ρ) * (1 + tanh a * tanh (ρ * z))) := by
  have := one_sub_tanh_sq_pos a
  have := one_sub_tanh_mul_pos a ρ
  have := one_add_tanh_mul_pos a (ρ * z)
  positivity

/-- The offspring bound `eq:offspring` for the race with `θ = t q`, which the sampler uses when
the stored bias is nonnegative (the inequality itself holds for every `a`): a normalized call
opens the gate `R / r_ℓ`, runs the race with mean `1 / σ` trials, and each trial uses a
sequential majority with mean source count `A`. The expected number of children is at most
`(tanh ρ / r_ℓ) exp (5ρ²/3 + ρ⁴)`. The hypothesis on `A` is the conclusion of `lem:arity`
(`sequential_arity_bound` in `ExactSampling.MajorityArity`).
Paper: `lem:offspring` (`tanh_scalar.tex`), `eq:offspring` and `eq:jointcost`. -/
theorem offspring_bound (a ρ z r A : ℝ) (hρ : 0 < ρ) (hz : |z| ≤ 1) (hr : 0 < r)
    (hA : A ≤ 1 + (1 - z ^ 2 / 3) * ρ ^ 2 + ρ ^ 4) :
    imgRadius (tanh a) (tanh ρ) / r * A *
        (1 / raceSuccess (tanh a * tanh ρ) ((1 + tanh (ρ * z) / tanh ρ) / 2)) ≤
      tanh ρ / r * exp (5 / 3 * ρ ^ 2 + ρ ^ 4) := by
  have hid := joint_cost_identity a ρ z hρ
  set K := (1 - tanh a ^ 2) / ((1 - tanh a * tanh ρ) * (1 + tanh a * tanh (ρ * z))) with hKdef
  have hK0 : 0 ≤ K := race_factor_nonneg a ρ z
  have hK1 : K ≤ exp (ρ ^ 2 * (1 + |z|) ^ 2 / 4) := by
    refine (race_factor_le a ρ z).trans (exp_le_exp.mpr ?_)
    have : (1 - z) ^ 2 ≤ (1 + |z|) ^ 2 := by
      have h1 : -z ≤ |z| := neg_le_abs z
      have h2 : 0 ≤ 1 - z := by linarith [le_abs_self z, (abs_le.mp hz).2]
      nlinarith
    have := mul_le_mul_of_nonneg_left this (sq_nonneg ρ)
    linarith
  have hAK := arity_mul_race_le A K z ρ hz hA hK0 hK1
  have hq : 0 ≤ tanh ρ := (tanh_pos_of_pos hρ).le
  have hσ : 0 < raceSuccess (tanh a * tanh ρ) ((1 + tanh (ρ * z) / tanh ρ) / 2) := by
    rw [raceSuccess_factory a ρ z hρ]
    exact div_pos (one_add_tanh_mul_pos _ _) (one_add_tanh_mul_pos _ _)
  have hR : imgRadius (tanh a) (tanh ρ) /
      raceSuccess (tanh a * tanh ρ) ((1 + tanh (ρ * z) / tanh ρ) / 2) = tanh ρ * K := hid
  have : imgRadius (tanh a) (tanh ρ) / r * A *
        (1 / raceSuccess (tanh a * tanh ρ) ((1 + tanh (ρ * z) / tanh ρ) / 2)) =
      tanh ρ / r * (A * K) := by
    rw [show imgRadius (tanh a) (tanh ρ) / r * A *
        (1 / raceSuccess (tanh a * tanh ρ) ((1 + tanh (ρ * z) / tanh ρ) / 2)) =
        imgRadius (tanh a) (tanh ρ) /
          raceSuccess (tanh a * tanh ρ) ((1 + tanh (ρ * z) / tanh ρ) / 2) * A / r by ring, hR]
    ring
  rw [this]
  exact mul_le_mul_of_nonneg_left hAK (div_nonneg hq hr.le)

/-- The offspring bound `eq:offspring` for the complemented race with parameter `-t q`, which
the sampler uses when the stored bias is negative (the inequality holds for every `a`).
Paper: `lem:offspring` (`tanh_scalar.tex`), "for negative `t`, replace `z` by `-z`". -/
theorem offspring_bound_complement (a ρ z r A : ℝ) (hρ : 0 < ρ) (hz : |z| ≤ 1) (hr : 0 < r)
    (hA : A ≤ 1 + (1 - z ^ 2 / 3) * ρ ^ 2 + ρ ^ 4) :
    imgRadius (tanh a) (tanh ρ) / r * A *
        (1 / raceSuccess (-(tanh a * tanh ρ)) ((1 - tanh (ρ * z) / tanh ρ) / 2)) ≤
      tanh ρ / r * exp (5 / 3 * ρ ^ 2 + ρ ^ 4) := by
  have hid := joint_cost_identity_complement a ρ z hρ
  -- the complemented factor is the ordinary factor at `(-a, -z)`
  have hsym : (1 - tanh a ^ 2) / ((1 + tanh a * tanh ρ) * (1 + tanh a * tanh (ρ * z))) =
      (1 - tanh (-a) ^ 2) / ((1 - tanh (-a) * tanh ρ) * (1 + tanh (-a) * tanh (ρ * -z))) := by
    rw [tanh_neg, show ρ * -z = -(ρ * z) by ring, tanh_neg]
    congr 1
    · ring
    · ring
  set K := (1 - tanh a ^ 2) / ((1 + tanh a * tanh ρ) * (1 + tanh a * tanh (ρ * z))) with hKdef
  have hK0 : 0 ≤ K := by rw [hsym]; exact race_factor_nonneg (-a) ρ (-z)
  have hK1 : K ≤ exp (ρ ^ 2 * (1 + |z|) ^ 2 / 4) := by
    rw [hsym]
    refine (race_factor_le (-a) ρ (-z)).trans (exp_le_exp.mpr ?_)
    have : (1 - -z) ^ 2 ≤ (1 + |z|) ^ 2 := by
      have h1 : z ≤ |z| := le_abs_self z
      have h2 : 0 ≤ 1 + z := by linarith [neg_abs_le z, (abs_le.mp hz).1]
      nlinarith
    have := mul_le_mul_of_nonneg_left this (sq_nonneg ρ)
    linarith
  have hAK := arity_mul_race_le A K z ρ hz hA hK0 hK1
  have hq : 0 ≤ tanh ρ := (tanh_pos_of_pos hρ).le
  have hσ : 0 < raceSuccess (-(tanh a * tanh ρ)) ((1 - tanh (ρ * z) / tanh ρ) / 2) := by
    rw [raceSuccess_factory_complement a ρ z hρ]
    exact div_pos (one_add_tanh_mul_pos _ _) (one_sub_tanh_mul_pos _ _)
  have : imgRadius (tanh a) (tanh ρ) / r * A *
        (1 / raceSuccess (-(tanh a * tanh ρ)) ((1 - tanh (ρ * z) / tanh ρ) / 2)) =
      tanh ρ / r * (A * K) := by
    rw [show imgRadius (tanh a) (tanh ρ) / r * A *
        (1 / raceSuccess (-(tanh a * tanh ρ)) ((1 - tanh (ρ * z) / tanh ρ) / 2)) =
        imgRadius (tanh a) (tanh ρ) /
          raceSuccess (-(tanh a * tanh ρ)) ((1 - tanh (ρ * z) / tanh ρ) / 2) * A / r by ring,
      hid]
    ring
  rw [this]
  exact mul_le_mul_of_nonneg_left hAK (div_nonneg hq hr.le)

/-- The uniform layer bound: if `ρ ≤ g r_{ℓ-1}` and `tanh ρ ≤ r_ℓ` (the latter from
`eq:rounded`), the offspring factor is at most
`B_ℓ = exp (5 (g r_{ℓ-1})²/3 + (g r_{ℓ-1})⁴)`. Paper: `lem:offspring` (`tanh_scalar.tex`),
uniform layer bound. -/
theorem offspring_layer_bound (ρ r x : ℝ) (hρ : 0 ≤ ρ) (hρx : ρ ≤ x) (hr : 0 < r)
    (hq : tanh ρ ≤ r) :
    tanh ρ / r * exp (5 / 3 * ρ ^ 2 + ρ ^ 4) ≤ exp (5 / 3 * x ^ 2 + x ^ 4) := by
  have h1 : tanh ρ / r ≤ 1 := by rw [div_le_one hr]; exact hq
  have h0 : 0 ≤ tanh ρ / r := div_nonneg (tanh_nonneg_of_nonneg hρ) hr.le
  have hsq : ρ ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hρ hρx 2
  have h4 : ρ ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ hρ hρx 4
  calc tanh ρ / r * exp (5 / 3 * ρ ^ 2 + ρ ^ 4) ≤ 1 * exp (5 / 3 * ρ ^ 2 + ρ ^ 4) :=
        mul_le_mul_of_nonneg_right h1 (exp_pos _).le
    _ ≤ exp (5 / 3 * x ^ 2 + x ^ 4) := by
        rw [one_mul]; exact exp_le_exp.mpr (by linarith)

/-- The root bound of `lem:offspring`: at the root the gate is `R` itself, so the expected number
of children is `R A / σ ≤ tanh ρ · exp (5ρ²/3 + ρ⁴) ≤ r_D B_D`, given `ρ ≤ x = g r_{D-1}` and
`tanh ρ ≤ r_D` (from `eq:rounded`). Race with `θ = t q`.
Paper: `lem:offspring` (`tanh_scalar.tex`), "the root's expected children are at most
`r_D B_D`". -/
theorem root_offspring_bound (a ρ z A x rD : ℝ) (hρ : 0 < ρ) (hz : |z| ≤ 1)
    (hA : A ≤ 1 + (1 - z ^ 2 / 3) * ρ ^ 2 + ρ ^ 4) (hρx : ρ ≤ x) (hq : tanh ρ ≤ rD) :
    imgRadius (tanh a) (tanh ρ) * A *
        (1 / raceSuccess (tanh a * tanh ρ) ((1 + tanh (ρ * z) / tanh ρ) / 2)) ≤
      rD * exp (5 / 3 * x ^ 2 + x ^ 4) := by
  have h := offspring_bound a ρ z 1 A hρ hz one_pos hA
  simp only [div_one] at h
  have hsq : ρ ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hρ.le hρx 2
  have h4 : ρ ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ hρ.le hρx 4
  have he : exp (5 / 3 * ρ ^ 2 + ρ ^ 4) ≤ exp (5 / 3 * x ^ 2 + x ^ 4) :=
    exp_le_exp.mpr (by linarith)
  have hq0 := (tanh_pos_of_pos hρ).le
  exact h.trans (mul_le_mul hq he (exp_pos _).le (le_trans hq0 hq))

/-- The root bound of `lem:offspring` for the complemented race (nonpositive stored bias).
Paper: `lem:offspring` (`tanh_scalar.tex`). -/
theorem root_offspring_bound_complement (a ρ z A x rD : ℝ) (hρ : 0 < ρ) (hz : |z| ≤ 1)
    (hA : A ≤ 1 + (1 - z ^ 2 / 3) * ρ ^ 2 + ρ ^ 4) (hρx : ρ ≤ x) (hq : tanh ρ ≤ rD) :
    imgRadius (tanh a) (tanh ρ) * A *
        (1 / raceSuccess (-(tanh a * tanh ρ)) ((1 - tanh (ρ * z) / tanh ρ) / 2)) ≤
      rD * exp (5 / 3 * x ^ 2 + x ^ 4) := by
  have h := offspring_bound_complement a ρ z 1 A hρ hz one_pos hA
  simp only [div_one] at h
  have hsq : ρ ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hρ.le hρx 2
  have h4 : ρ ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ hρ.le hρx 4
  have he : exp (5 / 3 * ρ ^ 2 + ρ ^ 4) ≤ exp (5 / 3 * x ^ 2 + x ^ 4) :=
    exp_le_exp.mpr (by linarith)
  have hq0 := (tanh_pos_of_pos hρ).le
  exact h.trans (mul_le_mul hq he (exp_pos _).le (le_trans hq0 hq))

/-! ### Countable sign mixtures -/

/-- Countable sign-mixture exactness: if a known distribution `w` selects interfaces of signed
means `m k`, and the mixture of means converges to `g`, then the output bit has probability
`(1 + g) / 2`. Used with `lem:majority` (`tanh_scalar.tex`) and `eq:chainmixture`
(`tanh_mean.tex`). -/
theorem countable_sign_mixture_exact (w m : ℕ → ℝ) (g : ℝ)
    (hw : HasSum w 1) (hmean : HasSum (fun k => w k * m k) g) :
    HasSum (fun k => w k * ((1 + m k) / 2)) ((1 + g) / 2) := by
  have hsum := (hw.add hmean).div_const (2 : ℝ)
  have heq : (fun k => (w k + w k * m k) / 2) = (fun k => w k * ((1 + m k) / 2)) := by
    funext k
    ring
  rw [heq] at hsum
  exact hsum

/-- The generic gate identity: a gate of probability `q`, an interface of mean `G = y / q` on the
open branch, and a fair sign on the closed branch give mean `y`. This is the elementary mixing
step used in `lem:comptanharity` (`tanh_large_radius.tex`) and in the top gate of
`eq:chainmixture` (`tanh_mean.tex`); it does not formalize those statements. -/
theorem gated_factory_mean (q G : ℝ) (hq : q ≠ 0) (y : ℝ) (hG : G = y / q) :
    q * G + (1 - q) * 0 = y := by
  rw [hG]; field_simp; ring

end ExactSampling.TanhFactory
