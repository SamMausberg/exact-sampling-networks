import Mathlib

/-!
# Normalized gain: lower bounds for additive pre-norm networks

This module formalizes the deterministic analysis behind the depth lower bounds for additive
pre-norm networks: `thm:pn-normalized-gain` (normalization_gain.tex) and, with the comparison
constants retained at the carrier fraction `η`, the lower half of `thm:main-carrier`
(main_normalization.tex) with exponent `2ν_η`, `thm:pn-scaled-lower`,
`cor:pn-scaled-finalnorm-lower`, `cor:pn-scaled-padding`, `cor:pn-scheduled-lower`
(normalization_depth_lower.tex), `thm:real-ffn-lower` and `cor:real-ffn-scheduled`
(normalization_ffn.tex), and the scalar estimates of `thm:pn-family-query-law`
(normalization_family_query.tex) and `thm:pn-family-bit-law` (normalization_family_oracle.tex).

Formalized here:
* elementary bounds: `tanh y ≥ y/√(1+y²)`, `tanh u ≥ u/2` on `[0,1]`, slope of `tanh` above
  `1/4` on `[-1,1]`, `tanh 1 > 3/4`, `log(1+x) ≥ x - x²/2`, the tangent line of `t ↦ t^{-1/2}`;
* the gain-chain machinery: the convexity step, the reciprocal-square comparison and its
  inversion, the schedule sums `∑q_j² ≤ 1/r_{j₀}`, `∑q_j/r_j = 1/r_{j₀} - 1/r_D`,
  `∑q_j ≥ log(r_D/r_{j₀}) - 1/r_{j₀}`, weighted Jensen, the score bound, and the passage from
  the score to `min{G², N}`;
* the carrier family: the floor `eq:pn-carrier-floor`, `γ₀ > 1/12`, the full-cube floor, the
  scalar recurrence `F_j`, its normalized update, and, at a comparison level `θ ≥ η` with
  `A₀ = θc²`, `A₁ = 4 + 2θc(1-c)`, `B_j = (s² + θ)/(A₀ + A₁/r_j)`: the gains `t_j`, the
  comparison `eq:pn-normalized-gain-comparison`, the product bound `G ≥ e^{-E_*}(r_D/M_*)^{ν_θ}`,
  the readout identity, the head bound `ḡ ≥ u_D/32`, and the assembled lower bound
  `Q ≥ min{c₁, c₂} min{r_D^{2ν_θ}, n}`, `ν_θ = s/(c√θ) - 1`. The level `θ = 1/2` gives
  `thm:pn-normalized-gain` (`ν = √2 s/c - 1`, constants depending only on `s`), and `θ = η`
  gives the exponent `2ν_η` of `thm:main-carrier`;
* the padded families (tanh or, after the antisymmetric identity, linear updates): the
  comparison `eq:pn-scaled-comparison`, the gain products for constant and prescribed steps, the
  full-cube floor `(1+τ)²/12`, the coordinate and final-normalization heads, and the assembled
  bounds with the explicit constants `c_s`, `c_s/16`, `c_s^pad`, `c_s^sched`, `c_s^ff` and the
  prefactor of `cor:real-ffn-scheduled` (including its small-`τ_D` case);
* for the full-cube carrier family: `b_j > 1/12`, `|b_j - ηc²| ≤ 8/r_j`, the slope bound of the
  tanh step, the multiplier product `eq:pn-family-derivative-product`, the power-sum steps, the
  bootstrap for `v_{j+1} ≤ v_j + a_j v_j²`, and the rounding product `≤ r^C`.

Stand-in hypothesis: in every assembled lower bound, the finite transcript inequality of
`lem:transcript` (tanh_lower.tex) enters as the explicit hypothesis `Q ≥ (N 𝔼[M ḡ(M)])²`,
where `N 𝔼[M ḡ(M)]` is the derivative at zero of the output mean (proved for sign vectors as
`ExactSampling.RMSContextLaw.hasDerivAt_signMean`). The law of the feature mean `M` enters through
its moments `𝔼M² = 1/N`, `𝔼M⁴ ≤ 3/N²` and `|M| ≤ 1` (proved for Rademacher averages as
`ExactSampling.RMSContextLaw.rademacher_fourth_moment`).

Modeling assumption: the heads read the feature coordinate of `x₁`, and the conditional
output means `carrierHead` and `headMean` build in `Pr(x₁ = 1 | M = z) = (1 + z)/2` for the
feature mean `M`, which holds by exchangeability of the fair signs but is not derived here
(`ExactSampling.RMSContextLaw.hasDerivAt_signMean` covers outputs that depend on `M` alone).

Not formalized: the vector-level network (only the scalar recurrences, the feature-row and
mean-square identities, and the denominator averages are formalized), the query model and
preprocessing, the Bernstein factories, Cauchy estimates and derivative tensors of orders two
to six in `thm:pn-family-query-law`, the Taylor-patch oracle of `thm:pn-family-bit-law`, the
upper half of `thm:main-carrier`, the choice of constants uniform in `η ∈ [1/4, 1/2]` for the
exponent `2ν_η` (the constants here depend on `η` and `s`), the `(θ, b)` parameterized form in
the paragraph "Dependence on the normalization floor" of normalization_gain.tex (only the bias
`b = 1` is treated, through the comparison level `θ`), and all bit-complexity statements.
The activation identities for GELU and SwiGLU are formalized in `ExactSampling.FeedForward`.
-/

open Real Finset
open scoped BigOperators

namespace ExactSampling.AdditiveNormalizedGain
/-! ## Elementary inequalities -/

/-- `tanh` is nonnegative on `[0, ∞)`. -/
theorem tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ tanh x := by
  rw [tanh_eq_sinh_div_cosh]; exact div_nonneg (sinh_nonneg_iff.2 hx) (cosh_pos x).le

/-- `tanh ≤ 1`. -/
theorem tanh_le_one (x : ℝ) : tanh x ≤ 1 := (Real.tanh_lt_one x).le

/-- `tanh ≥ -1`. -/
theorem neg_one_le_tanh (x : ℝ) : -1 ≤ tanh x := (Real.neg_one_lt_tanh x).le

/-- `tanh b - tanh a = sinh(b - a)/(cosh a cosh b)`. -/
theorem tanh_sub_tanh (a b : ℝ) : tanh b - tanh a = sinh (b - a) / (cosh a * cosh b) := by
  rw [tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh, sinh_sub]
  have ha := (cosh_pos a).ne'
  have hb := (cosh_pos b).ne'
  field_simp

/-- `tanh` is monotone. -/
theorem tanh_mono {a b : ℝ} (h : a ≤ b) : tanh a ≤ tanh b := by
  have := tanh_sub_tanh a b
  have h1 : 0 ≤ sinh (b - a) := sinh_nonneg_iff.2 (by linarith)
  have h2 : 0 < cosh a * cosh b := mul_pos (cosh_pos a) (cosh_pos b)
  have : 0 ≤ tanh b - tanh a := by rw [this]; exact div_nonneg h1 h2.le
  linarith

/-- `cosh 1 < 2`, hence `sech²(1) > 1/4`. -/
theorem cosh_one_lt_two : cosh 1 < 2 := by
  rw [cosh_eq]
  have h1 := exp_one_lt_d9
  have h2 : exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
  norm_num at h1 ⊢
  linarith

/-- On `[-1, 1]` the slope of `tanh` exceeds `sech²(1) > 1/4`: `tanh b - tanh a ≥ (b - a)/4`.
Paper: proof of `thm:pn-scaled-lower` (normalization_depth_lower.tex), before
`eq:pn-scaled-coordinatehead`. -/
theorem tanh_sub_tanh_ge {a b : ℝ} (ha : -1 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (b - a) / 4 ≤ tanh b - tanh a := by
  rw [tanh_sub_tanh]
  have h1 : b - a ≤ sinh (b - a) := self_le_sinh_iff.2 (by linarith)
  have hca : cosh a ≤ cosh 1 := cosh_le_cosh.2 (by rw [abs_one, abs_le]; constructor <;> linarith)
  have hcb : cosh b ≤ cosh 1 := cosh_le_cosh.2 (by rw [abs_one, abs_le]; constructor <;> linarith)
  have h2 : 0 < cosh a * cosh b := mul_pos (cosh_pos a) (cosh_pos b)
  have h3 : cosh a * cosh b ≤ 4 := by
    have := cosh_one_lt_two
    nlinarith [cosh_pos a, cosh_pos b]
  rw [le_div_iff₀ h2]
  nlinarith

/-- `tanh y ≥ y/√(1+y²)` for `y ≥ 0`, since `sinh y ≥ y`.
Paper: proof of `thm:pn-scaled-lower` (normalization_depth_lower.tex). -/
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

/-- `tanh u ≥ u/2` for `0 ≤ u ≤ 1` (used for the value `z tanh k` at `A = 0`).
Paper: proof of `thm:pn-scaled-lower` (normalization_depth_lower.tex), before
`eq:pn-scaled-coordinatehead`. -/
theorem half_le_tanh {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : u / 2 ≤ tanh u := by
  refine le_trans ?_ (div_sqrt_le_tanh h0)
  have hS : 0 < √(1 + u ^ 2) := sqrt_pos.2 (by positivity)
  have hS2 : √(1 + u ^ 2) ≤ 2 := by
    rw [sqrt_le_left (by norm_num)]; nlinarith
  exact div_le_div_of_nonneg_left h0 hS hS2

/-- `tanh 1 > 3/4`, from `e² > 7`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem tanh_one_gt : (3 : ℝ) / 4 < tanh 1 := by
  rw [tanh_eq]
  have h1 := exp_one_gt_d9
  have hpos := exp_pos 1
  have hinv : exp (-1) = (exp 1)⁻¹ := by rw [exp_neg]
  rw [hinv, lt_div_iff₀ (by positivity)]
  have : exp 1 * (exp 1)⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  norm_num at h1
  nlinarith

/-- `tanh 1 < 1`. -/
theorem tanh_one_lt_one : tanh 1 < 1 := Real.tanh_lt_one 1

/-- `log(1+x) ≥ x - x²/2` for `x ≥ 0`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
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

/-- A product of factors `1 + x_i`, `x_i ≥ 0`, is at least `exp(∑ x_i - ∑ x_i²/2)`. -/
theorem prod_one_add_ge {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    exp (∑ i ∈ s, x i - ∑ i ∈ s, x i ^ 2 / 2) ≤ ∏ i ∈ s, (1 + x i) := by
  have hpos : ∀ i ∈ s, 0 < 1 + x i := fun i hi => by linarith [hx i hi]
  have hprod : ∏ i ∈ s, (1 + x i) = exp (∑ i ∈ s, log (1 + x i)) := by
    rw [exp_sum]; exact prod_congr rfl (fun i hi => (exp_log (hpos i hi)).symm)
  rw [hprod, ← sum_sub_distrib]
  exact exp_le_exp.2 (sum_le_sum (fun i hi => log_one_add_ge (hx i hi)))

/-- The tangent-line inequality for `t ↦ t^{-1/2}`. -/
theorem inv_sqrt_tangent {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    1 / √B - (A - B) / (2 * B * √B) ≤ 1 / √A := by
  have hx0 : 0 < √A := sqrt_pos.2 hA
  have hy0 : 0 < √B := sqrt_pos.2 hB
  have hA' : A = √A ^ 2 := (sq_sqrt hA.le).symm
  have hB' : B = √B ^ 2 := (sq_sqrt hB.le).symm
  generalize √A = x at *
  generalize √B = y at *
  subst hA' hB'
  have key : 1 / x - (1 / y - (x ^ 2 - y ^ 2) / (2 * y ^ 2 * y))
      = (x - y) ^ 2 * (x + 2 * y) / (2 * x * y ^ 3) := by
    field_simp; ring
  have : 0 ≤ (x - y) ^ 2 * (x + 2 * y) / (2 * x * y ^ 3) := by positivity
  linarith

/-- `1 - (1+x)^{-1/2} ≤ x/2` for `x ≥ 0`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem one_sub_inv_sqrt_le {x : ℝ} (hx : 0 ≤ x) : 1 - 1 / √(1 + x) ≤ x / 2 := by
  have := inv_sqrt_tangent (A := 1 + x) (B := 1) (by linarith) one_pos
  rw [sqrt_one] at this
  norm_num at this ⊢
  linarith

/-! ## Gain chains: the convexity step and the reciprocal-square comparison -/

/-- The convexity step. With weights `(1-q)/g` and `qt/g`, `g = 1 - q + qt`, convexity of
`x ↦ (1+x)^{-1/2}` gives `(1-q)u + q t u/√(1 + Bu²) ≥ g u/√(1 + (qtB/g) u²)`.
Paper: proofs of `thm:pn-scaled-lower` (normalization_depth_lower.tex) and
`thm:pn-normalized-gain` (normalization_gain.tex), the convexity step. -/
theorem step_convex {q t B u : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hu : 0 ≤ u) (hg : 0 < 1 - q + q * t) :
    (1 - q + q * t) * u / √(1 + (q * t * B / (1 - q + q * t)) * u ^ 2)
      ≤ (1 - q) * u + q * (t * u / √(1 + B * u ^ 2)) := by
  set g := 1 - q + q * t with hgdef
  set w2 := q * t / g
  have hw2 : 0 ≤ w2 := div_nonneg (mul_nonneg hq0 ht) hg.le
  have hw1 : (1 - q) / g + w2 = 1 := by
    simp only [w2]; rw [← add_div]
    show (1 - q + q * t) / g = 1
    rw [← hgdef]; exact div_self hg.ne'
  set M := 1 + w2 * (B * u ^ 2) with hM
  have hM0 : 0 < M := by have := mul_nonneg hw2 (mul_nonneg hB (sq_nonneg u)); linarith
  have hd : q * t * B / g * u ^ 2 = w2 * (B * u ^ 2) := by simp only [w2]; ring
  rw [hd]
  have h1 := inv_sqrt_tangent (A := 1) (B := M) one_pos hM0
  have h2 := inv_sqrt_tangent (A := 1 + B * u ^ 2) (B := M) (by positivity) hM0
  rw [sqrt_one] at h1
  have hw1' : 0 ≤ (1 - q) / g := div_nonneg (by linarith) hg.le
  have key : 1 / √M ≤ (1 - q) / g * (1 / 1) + w2 * (1 / √(1 + B * u ^ 2)) := by
    have e : 1 / √M = (1 - q) / g * (1 / √M - (1 - M) / (2 * M * √M))
        + w2 * (1 / √M - (1 + B * u ^ 2 - M) / (2 * M * √M)) := by
      have e2 : (1 - q) / g = 1 - w2 := by linarith
      rw [e2, hM]
      ring
    rw [e]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hw1') (mul_le_mul_of_nonneg_left h2 hw2)
  have hgu : 0 ≤ g * u := mul_nonneg hg.le hu
  have := mul_le_mul_of_nonneg_left key hgu
  have e3 : g * u * ((1 - q) / g * (1 / 1) + w2 * (1 / √(1 + B * u ^ 2)))
      = (1 - q) * u + q * (t * u / √(1 + B * u ^ 2)) := by
    simp only [w2]; field_simp
  rw [e3] at this
  calc g * u / √M = g * u * (1 / √M) := by ring
    _ ≤ _ := this

/-- The reciprocal-square step: `u' ≥ g u/√(1 + d u²)` with `u, g > 0`, `d ≥ 0` gives `u' > 0`
and `1/u'² ≤ 1/(g²u²) + d/g²`. -/
theorem reciprocal_step {u u' g d : ℝ} (hu : 0 < u) (hg : 0 < g) (hd : 0 ≤ d)
    (h : g * u / √(1 + d * u ^ 2) ≤ u') :
    0 < u' ∧ 1 / u' ^ 2 ≤ 1 / (g ^ 2 * u ^ 2) + d / g ^ 2 := by
  have hs : 0 < √(1 + d * u ^ 2) := sqrt_pos.2 (by positivity)
  have hx : 0 < g * u / √(1 + d * u ^ 2) := by positivity
  have hu' : 0 < u' := lt_of_lt_of_le hx h
  refine ⟨hu', ?_⟩
  have h2 : (g * u / √(1 + d * u ^ 2)) ^ 2 ≤ u' ^ 2 := pow_le_pow_left₀ hx.le h 2
  have h3 : 1 / u' ^ 2 ≤ 1 / (g * u / √(1 + d * u ^ 2)) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) h2
  have e : 1 / (g * u / √(1 + d * u ^ 2)) ^ 2 = 1 / (g ^ 2 * u ^ 2) + d / g ^ 2 := by
    rw [div_pow, sq_sqrt (by positivity)]
    field_simp
  linarith

/-- **The reciprocal-square comparison.** Let `u_{i+1} ≥ g_i u_i/√(1 + d_i u_i²)` with
`u_0 > 0`, `g_i > 0`, `0 ≤ d_i ≤ C(g_i² - 1)`. Then for `G_k = ∏_{i<k} g_i`,
`G_k²/u_k² ≤ 1/u_0² + C(G_k² - 1)` and `u_k > 0`.
Paper: proof of `thm:pn-scaled-lower`, the reciprocal-square inequality before
`eq:pn-scaled-comparison` (normalization_depth_lower.tex); reused for
`eq:pn-normalized-gain-comparison` (normalization_gain.tex). -/
theorem reciprocal_chain {u g d : ℕ → ℝ} {C : ℝ} {n : ℕ} (hu0 : 0 < u 0)
    (hg : ∀ i < n, 0 < g i) (hd : ∀ i < n, 0 ≤ d i) (hdC : ∀ i < n, d i ≤ C * (g i ^ 2 - 1))
    (hstep : ∀ i < n, g i * u i / √(1 + d i * u i ^ 2) ≤ u (i + 1)) :
    ∀ k ≤ n, 0 < u k ∧
      (∏ i ∈ range k, g i) ^ 2 / u k ^ 2 ≤ 1 / u 0 ^ 2 + C * ((∏ i ∈ range k, g i) ^ 2 - 1) := by
  intro k
  induction k with
  | zero => intro _; simp [hu0]
  | succ k ih =>
    intro hk
    obtain ⟨hpos, hih⟩ := ih (by omega)
    obtain ⟨hpos', hrec⟩ := reciprocal_step hpos (hg k (by omega)) (hd k (by omega))
      (hstep k (by omega))
    refine ⟨hpos', ?_⟩
    rw [prod_range_succ]
    set Gk := ∏ i ∈ range k, g i
    have hgk := hg k (by omega)
    have hmul := mul_le_mul_of_nonneg_left hrec (by positivity : (0 : ℝ) ≤ (Gk * g k) ^ 2)
    have e1 : (Gk * g k) ^ 2 * (1 / (g k ^ 2 * u k ^ 2) + d k / g k ^ 2)
        = Gk ^ 2 / u k ^ 2 + d k * Gk ^ 2 := by field_simp
    have e2 : (Gk * g k) ^ 2 * (1 / u (k + 1) ^ 2) = (Gk * g k) ^ 2 / u (k + 1) ^ 2 := by ring
    rw [e1, e2] at hmul
    have hdk : d k * Gk ^ 2 ≤ C * (g k ^ 2 - 1) * Gk ^ 2 :=
      mul_le_mul_of_nonneg_right (hdC k (by omega)) (sq_nonneg _)
    have e3 : C * ((Gk * g k) ^ 2 - 1) = C * (Gk ^ 2 - 1) + C * (g k ^ 2 - 1) * Gk ^ 2 := by ring
    rw [e3]
    linarith

/-- Inverting the reciprocal-square comparison: if `G²/u² ≤ 1/u₀² + C(G² - 1)`, `u₀ ≥ v > 0`,
`G > 0`, `C(G² - 1) ≥ 0`, then `u ≥ G v / √(1 + C(G² - 1)v²)`.
Paper: the inversion step of `eq:pn-scaled-comparison` (normalization_depth_lower.tex) and of
`eq:pn-normalized-gain-comparison` (normalization_gain.tex). -/
theorem invert_comparison {u u0 v G C : ℝ} (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u0)
    (hG : 0 < G) (hCG : 0 ≤ C * (G ^ 2 - 1))
    (h : G ^ 2 / u ^ 2 ≤ 1 / u0 ^ 2 + C * (G ^ 2 - 1)) :
    G * v / √(1 + C * (G ^ 2 - 1) * v ^ 2) ≤ u := by
  have hu0 : 0 < u0 := lt_of_lt_of_le hv hvu
  have h1 : 1 / u0 ^ 2 ≤ 1 / v ^ 2 := one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_left₀ hv.le hvu 2)
  have h2 : G ^ 2 / u ^ 2 ≤ (1 + C * (G ^ 2 - 1) * v ^ 2) / v ^ 2 := by
    have : (1 + C * (G ^ 2 - 1) * v ^ 2) / v ^ 2 = 1 / v ^ 2 + C * (G ^ 2 - 1) := by
      field_simp
    rw [this]; linarith
  have hS : 0 < 1 + C * (G ^ 2 - 1) * v ^ 2 := by positivity
  have hsq : (G * v) ^ 2 / (1 + C * (G ^ 2 - 1) * v ^ 2) ≤ u ^ 2 := by
    rw [div_le_iff₀ hS]
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h2
    nlinarith
  have hlhs : (G * v / √(1 + C * (G ^ 2 - 1) * v ^ 2)) ^ 2
      = (G * v) ^ 2 / (1 + C * (G ^ 2 - 1) * v ^ 2) := by
    rw [div_pow, sq_sqrt hS.le]
  have hx : 0 ≤ G * v / √(1 + C * (G ^ 2 - 1) * v ^ 2) := by positivity
  nlinarith [sq_nonneg (G * v / √(1 + C * (G ^ 2 - 1) * v ^ 2) - u)]

/-- Multiplying the reciprocal-square inequality by the squared growth product: if
`g²/v² ≤ 1/u² + d` then `(Gg)²/v² ≤ G²/u² + dG²`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex), the reciprocal-square
comparison. -/
theorem reciprocal_comparison_charge (G g u v d : ℝ) (h : g ^ 2 / v ^ 2 ≤ 1 / u ^ 2 + d) :
    (G * g) ^ 2 / v ^ 2 ≤ G ^ 2 / u ^ 2 + d * G ^ 2 := by
  calc (G * g) ^ 2 / v ^ 2 = G ^ 2 * (g ^ 2 / v ^ 2) := by ring
    _ ≤ G ^ 2 * (1 / u ^ 2 + d) := mul_le_mul_of_nonneg_left h (sq_nonneg G)
    _ = G ^ 2 / u ^ 2 + d * G ^ 2 := by ring

/-- The telescoping increment `(g² - 1)G² = (Gg)² - G²`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem gain_square_increment (G g : ℝ) : (g ^ 2 - 1) * G ^ 2 = (G * g) ^ 2 - G ^ 2 := by
  ring

/-- The reciprocal-square comparison telescopes after multiplication by the squared growth
product: if `next ≤ (old + d)/g²` then `(Gg)² next ≤ G² old + dG²`.
Paper: proofs of `thm:pn-normalized-gain` (normalization_gain.tex) and `thm:pn-scaled-lower`
(normalization_depth_lower.tex). -/
theorem reciprocal_budget_step (G g old next d : ℝ) (hg : g ≠ 0)
    (hstep : next ≤ (old + d) / g ^ 2) : (G * g) ^ 2 * next ≤ G ^ 2 * old + d * G ^ 2 := by
  have hmul := mul_le_mul_of_nonneg_left hstep (sq_nonneg (G * g))
  calc (G * g) ^ 2 * next ≤ (G * g) ^ 2 * ((old + d) / g ^ 2) := hmul
    _ = G ^ 2 * old + d * G ^ 2 := by field_simp

/-! ## Step schedules -/

/-- The schedule radius `r_j = 1 + ∑_{k<j} a_k`. -/
noncomputable def schedR (a : ℕ → ℝ) (j : ℕ) : ℝ := 1 + ∑ k ∈ range j, a k

/-- `r_0 = 1`. -/
theorem schedR_zero (a : ℕ → ℝ) : schedR a 0 = 1 := by simp [schedR]

/-- `r_{j+1} = r_j + a_j`. -/
theorem schedR_succ (a : ℕ → ℝ) (j : ℕ) : schedR a (j + 1) = schedR a j + a j := by
  simp [schedR, sum_range_succ]; ring

/-- `r_j ≥ 1` for nonnegative steps. -/
theorem schedR_ge_one {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (j : ℕ) : 1 ≤ schedR a j := by
  unfold schedR
  have := sum_nonneg (fun k (_ : k ∈ range j) => ha k)
  linarith

/-- `r_j > 0` for nonnegative steps. -/
theorem schedR_pos {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (j : ℕ) : 0 < schedR a j :=
  lt_of_lt_of_le one_pos (schedR_ge_one ha j)

/-- The radii are monotone in `j` for nonnegative steps. -/
theorem schedR_mono {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) {i j : ℕ} (h : i ≤ j) :
    schedR a i ≤ schedR a j := by
  unfold schedR
  have := sum_le_sum_of_subset_of_nonneg (range_subset_range.2 h) (fun k _ _ => ha k)
  linarith

/-- The reciprocal increment: `a/(r(r+a)) = 1/r - 1/(r+a)`.
Paper: proof of `cor:pn-scheduled-lower` (normalization_depth_lower.tex). -/
theorem reciprocal_schedule_identity (r a : ℝ) (hr : r ≠ 0) (hra : r + a ≠ 0) :
    a / (r * (r + a)) = 1 / r - 1 / (r + a) := by
  field_simp
  ring

/-- The residual reciprocal increment `(a/(r+a))/r = 1/r - 1/(r+a)`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex),
`∑ q_j/r_j = 1/r_{j₀} - 1/r_D`. -/
theorem residual_reciprocal_increment (r a : ℝ) (hr : 0 < r) (ha : 0 ≤ a) :
    (a / (r + a)) / r = 1 / r - 1 / (r + a) := by
  have hra0 : r + a ≠ 0 := ne_of_gt (by linarith : 0 < r + a)
  field_simp
  ring

/-- The exact normalized coefficient of an additive step:
`(r u + a f)/(r + a) = (1 - a/(r+a)) u + (a/(r+a)) f`.
Paper: proofs of `thm:pn-scaled-lower` and `cor:pn-scheduled-lower`
(normalization_depth_lower.tex), the normalized update. -/
theorem normalized_schedule_update (r a u f : ℝ) (hra : r + a ≠ 0) :
    (r * u + a * f) / (r + a) = (1 - a / (r + a)) * u + (a / (r + a)) * f := by
  field_simp
  ring

/-- `(a/(r+a))² ≤ 1/r - 1/(r+a)` for `r > 0`, `0 ≤ a ≤ 1`.
Paper: proofs of `thm:pn-normalized-gain` (normalization_gain.tex) and `cor:pn-scheduled-lower`
(normalization_depth_lower.tex). -/
theorem residual_square_bound (r a : ℝ) (hr : 0 < r) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (a / (r + a)) ^ 2 ≤ 1 / r - 1 / (r + a) := by
  have hra : 0 < r + a := by linarith
  have hid : (a / (r + a)) / r = 1 / r - 1 / (r + a) := by field_simp; ring
  rw [← hid]
  have hq0 : 0 ≤ a / (r + a) := div_nonneg ha (le_of_lt hra)
  have hq : a / (r + a) ≤ 1 / r := by
    apply (div_le_div_iff₀ hra hr).2
    nlinarith [mul_nonneg (le_of_lt hr) (sub_nonneg.mpr ha1)]
  calc (a / (r + a)) ^ 2 = (a / (r + a)) * (a / (r + a)) := by ring
    _ ≤ (a / (r + a)) * (1 / r) := mul_le_mul_of_nonneg_left hq hq0
    _ = (a / (r + a)) / r := by ring

/-- `log((r+a)/r) ≤ a/(r+a) + (1/r - 1/(r+a))` for `r > 0`, `0 ≤ a ≤ 1`.
Paper: proofs of `thm:pn-normalized-gain` (normalization_gain.tex) and `cor:pn-scheduled-lower`
(normalization_depth_lower.tex). -/
theorem log_step_le (r a : ℝ) (hr : 0 < r) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    log ((r + a) / r) ≤ a / (r + a) + (1 / r - 1 / (r + a)) := by
  have hra : 0 < r + a := by linarith
  have h1 : log ((r + a) / r) ≤ (r + a) / r - 1 := log_le_sub_one_of_pos (by positivity)
  have h2 : (r + a) / r - 1 = a / r := by field_simp; ring
  have h3 : a / r - a / (r + a) = a * a / (r * (r + a)) := by field_simp; ring
  have h4 : a * a / (r * (r + a)) ≤ a / (r * (r + a)) := by
    apply div_le_div_of_nonneg_right _ (by positivity); nlinarith
  have h5 : a / (r * (r + a)) = 1 / r - 1 / (r + a) := reciprocal_schedule_identity r a hr.ne'
    hra.ne'
  linarith

/-- Sums along a schedule over `[j₀, j₀ + n)`: with `q_j = a_j/r_{j+1}`,
`∑ q_j² ≤ 1/r_{j₀} - 1/r_{j₀+n}`, `∑ q_j/r_j = 1/r_{j₀} - 1/r_{j₀+n}` and
`∑ q_j ≥ log(r_{j₀+n}/r_{j₀}) - (1/r_{j₀} - 1/r_{j₀+n})`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex); proof of
`cor:pn-scheduled-lower` (normalization_depth_lower.tex). -/
theorem schedule_sums {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1) (j0 n : ℕ) :
    ∑ i ∈ range n, (a (j0 + i) / schedR a (j0 + i + 1)) ^ 2
        ≤ 1 / schedR a j0 - 1 / schedR a (j0 + n) ∧
      ∑ i ∈ range n, a (j0 + i) / schedR a (j0 + i + 1) / schedR a (j0 + i)
        = 1 / schedR a j0 - 1 / schedR a (j0 + n) ∧
      log (schedR a (j0 + n) / schedR a j0) - (1 / schedR a j0 - 1 / schedR a (j0 + n))
        ≤ ∑ i ∈ range n, a (j0 + i) / schedR a (j0 + i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hr := schedR_pos ha (j0 + n)
    have hr1 := schedR_pos ha (j0 + n + 1)
    have hs : schedR a (j0 + n + 1) = schedR a (j0 + n) + a (j0 + n) := schedR_succ a _
    rw [sum_range_succ, sum_range_succ, sum_range_succ, ← add_assoc]
    refine ⟨?_, ?_, ?_⟩
    · have := residual_square_bound _ _ hr (ha (j0 + n)) (ha1 (j0 + n))
      rw [← hs] at this
      linarith
    · rw [h2, hs]
      have hne : schedR a (j0 + n) + a (j0 + n) ≠ 0 := by rw [← hs]; exact hr1.ne'
      field_simp
      ring
    · have hl := log_step_le _ _ hr (ha (j0 + n)) (ha1 (j0 + n))
      rw [← hs] at hl
      have hsplit : log (schedR a (j0 + n + 1) / schedR a j0)
          = log (schedR a (j0 + n) / schedR a j0)
            + log (schedR a (j0 + n + 1) / schedR a (j0 + n)) := by
        rw [← log_mul (by have := schedR_pos ha j0; positivity) (by positivity)]
        congr 1; field_simp [(schedR_pos ha j0).ne']
      rw [hsplit]
      linarith

/-! ## Scores and query bounds -/

/-- Weighted Jensen for `t ↦ (a+t)^{-1/2}`.
Paper: `eq:rmsweightedjensen` (normalization_obstruction.tex); proof of `thm:pn-scaled-lower`
(normalization_depth_lower.tex). -/
theorem weighted_jensen {ι : Type*} (s : Finset ι) (p Z : ι → ℝ) (a : ℝ) (ha : 0 < a)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hZ : ∀ i ∈ s, 0 ≤ Z i) (hEZ : 0 < ∑ i ∈ s, p i * Z i) :
    (∑ i ∈ s, p i * Z i) / √(a + (∑ i ∈ s, p i * Z i ^ 2) / ∑ i ∈ s, p i * Z i)
      ≤ ∑ i ∈ s, p i * (Z i / √(a + Z i)) := by
  set E := ∑ i ∈ s, p i * Z i
  set m := (∑ i ∈ s, p i * Z i ^ 2) / E
  have hm0 : 0 ≤ m := div_nonneg (sum_nonneg (fun i hi => mul_nonneg (hp i hi)
    (sq_nonneg _))) hEZ.le
  have hB : 0 < a + m := by linarith
  have hstep : ∀ i ∈ s, p i * Z i / E * (1 / √(a + m) - ((a + Z i) - (a + m))
      / (2 * (a + m) * √(a + m))) ≤ p i * Z i / E * (1 / √(a + Z i)) := fun i hi =>
    mul_le_mul_of_nonneg_left (inv_sqrt_tangent (by linarith [hZ i hi]) hB)
      (div_nonneg (mul_nonneg (hp i hi) (hZ i hi)) hEZ.le)
  have hsum := sum_le_sum hstep
  have hlhs : ∑ i ∈ s, p i * Z i / E * (1 / √(a + m) - ((a + Z i) - (a + m))
      / (2 * (a + m) * √(a + m))) = 1 / √(a + m) := by
    have e : ∀ i ∈ s, p i * Z i / E * (1 / √(a + m) - ((a + Z i) - (a + m))
        / (2 * (a + m) * √(a + m))) = (p i * Z i) * (1 / E * (1 / √(a + m)
          + m / (2 * (a + m) * √(a + m)))) - (p i * Z i ^ 2) * (1 / E
            * (1 / (2 * (a + m) * √(a + m)))) := by intro i _; ring
    rw [sum_congr rfl e, sum_sub_distrib, ← sum_mul, ← sum_mul]
    have hE : E ≠ 0 := hEZ.ne'
    have hm : ∑ i ∈ s, p i * Z i ^ 2 = m * E := by simp only [m]; field_simp
    rw [hm]
    field_simp
    ring
  have hrhs : ∑ i ∈ s, p i * Z i / E * (1 / √(a + Z i))
      = (∑ i ∈ s, p i * (Z i / √(a + Z i))) / E := by
    rw [sum_div]; apply sum_congr rfl; intro i _; ring
  rw [hlhs, hrhs, le_div_iff₀ hEZ] at hsum
  calc E / √(a + m) = 1 / √(a + m) * E := by ring
    _ ≤ _ := hsum

/-- **Score from a pointwise comparison.** Let `(p_i, M_i)` be a finite law with
`𝔼M² = 1/N` and `𝔼M⁴ ≤ 3/N²` (the Rademacher average of `N` fair signs; see
`ExactSampling.RMSContextLaw.rademacher_fourth_moment`). If `M g(M) ≥ λ M²/√(1 + βM²)` with
`λ ≥ 0`, `β > 0`, then `N 𝔼[M g(M)] ≥ λ / √(1 + 3β/N)`.
Paper: proof of `thm:pn-scaled-lower` (normalization_depth_lower.tex), Jensen's inequality
weighted by `M²`. -/
theorem score_lower {ι : Type*} (s : Finset ι) (p M : ι → ℝ) (g : ℝ → ℝ) {N lam β : ℝ}
    (hN : 0 < N) (hlam : 0 ≤ lam) (hβ : 0 < β) (hp : ∀ i ∈ s, 0 ≤ p i)
    (h2 : ∑ i ∈ s, p i * M i ^ 2 = 1 / N) (h4 : ∑ i ∈ s, p i * M i ^ 4 ≤ 3 / N ^ 2)
    (hpt : ∀ i ∈ s, lam * (M i ^ 2 / √(1 + β * M i ^ 2)) ≤ M i * g (M i)) :
    lam / √(1 + 3 * β / N) ≤ N * ∑ i ∈ s, p i * (M i * g (M i)) := by
  have hJ := weighted_jensen s p (fun i => M i ^ 2) (1 / β) (by positivity) hp
    (fun i _ => sq_nonneg _) (by rw [h2]; positivity)
  simp only [← pow_mul] at hJ
  rw [h2] at hJ
  have hratio : (∑ i ∈ s, p i * M i ^ (2 * 2)) / (1 / N) ≤ 3 / N := by
    rw [div_le_iff₀ (by positivity)]
    calc (∑ i ∈ s, p i * M i ^ (2 * 2)) = ∑ i ∈ s, p i * M i ^ 4 := by norm_num
      _ ≤ 3 / N ^ 2 := h4
      _ = 3 / N * (1 / N) := by field_simp
  have hpos1 : 0 < 1 / β + (∑ i ∈ s, p i * M i ^ (2 * 2)) / (1 / N) := by
    have : 0 ≤ (∑ i ∈ s, p i * M i ^ (2 * 2)) / (1 / N) := by
      apply div_nonneg _ (by positivity)
      apply sum_nonneg; intro i hi
      exact mul_nonneg (hp i hi) (by rw [pow_mul]; positivity)
    have : 0 < 1 / β := by positivity
    linarith
  have hJ' : 1 / N / √(1 / β + 3 / N) ≤ ∑ i ∈ s, p i * (M i ^ 2 / √(1 / β + M i ^ 2)) :=
    le_trans (div_le_div_of_nonneg_left (by positivity) (sqrt_pos.2 hpos1)
      (sqrt_le_sqrt (by linarith))) hJ
  -- rescale the pointwise bound
  have hsb : 0 < √β := sqrt_pos.2 hβ
  have hpt' : ∀ i ∈ s, lam / √β * (M i ^ 2 / √(1 / β + M i ^ 2)) ≤ M i * g (M i) := by
    intro i hi
    set x := M i
    have hb : 1 / √β * (x ^ 2 / √(1 / β + x ^ 2)) = x ^ 2 / √(1 + β * x ^ 2) := by
      have e : 1 + β * x ^ 2 = β * (1 / β + x ^ 2) := by field_simp
      rw [e, sqrt_mul hβ.le]
      have : 0 < √(1 / β + x ^ 2) := sqrt_pos.2 (by positivity)
      field_simp
    calc lam / √β * (x ^ 2 / √(1 / β + x ^ 2))
        = lam * (1 / √β * (x ^ 2 / √(1 / β + x ^ 2))) := by ring
      _ = lam * (x ^ 2 / √(1 + β * x ^ 2)) := by rw [hb]
      _ ≤ x * g x := hpt i hi
  have hsum : lam / √β * ∑ i ∈ s, p i * (M i ^ 2 / √(1 / β + M i ^ 2))
      ≤ ∑ i ∈ s, p i * (M i * g (M i)) := by
    rw [mul_sum]
    apply sum_le_sum; intro i hi
    calc lam / √β * (p i * (M i ^ 2 / √(1 / β + M i ^ 2)))
        = p i * (lam / √β * (M i ^ 2 / √(1 / β + M i ^ 2))) := by ring
      _ ≤ p i * (M i * g (M i)) := mul_le_mul_of_nonneg_left (hpt' i hi) (hp i hi)
  have hfin := le_trans (mul_le_mul_of_nonneg_left hJ' (by positivity : 0 ≤ lam / √β)) hsum
  have e : N * (lam / √β * (1 / N / √(1 / β + 3 / N))) = lam / √(1 + 3 * β / N) := by
    have e1 : 1 + 3 * β / N = β * (1 / β + 3 / N) := by field_simp
    rw [e1, sqrt_mul hβ.le]
    have : 0 < √(1 / β + 3 / N) := sqrt_pos.2 (by positivity)
    field_simp
  rw [← e]
  exact mul_le_mul_of_nonneg_left hfin hN.le

/-- From the score to the query count: if `Q ≥ H'²` and `H' ≥ λ/√(1 + 3β'G²/N)` with
`λ = G/K₀`, then `Q ≥ min{G², N}/(K₀²(1 + 3β'))`.
Paper: proof of `thm:pn-scaled-lower` (normalization_depth_lower.tex), the bound on `𝔼Q`. -/
theorem query_min_bound {Q H G N K0 β' : ℝ} (hG : 0 < G) (hN : 0 < N) (hK0 : 0 < K0)
    (hβ' : 0 ≤ β') (hQ : H ^ 2 ≤ Q) (hH : G / K0 / √(1 + 3 * β' * G ^ 2 / N) ≤ H) :
    min (G ^ 2) N / (K0 ^ 2 * (1 + 3 * β')) ≤ Q := by
  have hS : 0 < 1 + 3 * β' * G ^ 2 / N := by positivity
  have h0 : 0 ≤ G / K0 / √(1 + 3 * β' * G ^ 2 / N) := by positivity
  have hsq := pow_le_pow_left₀ h0 hH 2
  have e : (G / K0 / √(1 + 3 * β' * G ^ 2 / N)) ^ 2
      = G ^ 2 / (K0 ^ 2 * (1 + 3 * β' * G ^ 2 / N)) := by
    rw [div_pow, div_pow, sq_sqrt hS.le]; field_simp
  rw [e] at hsq
  have hmin : min (G ^ 2) N / (K0 ^ 2 * (1 + 3 * β'))
      ≤ G ^ 2 / (K0 ^ 2 * (1 + 3 * β' * G ^ 2 / N)) := by
    rcases le_total (G ^ 2) N with h | h
    · rw [min_eq_left h]
      apply div_le_div_of_nonneg_left (sq_nonneg G) (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : G ^ 2 / N ≤ 1 := by rw [div_le_one hN]; exact h
      have : 3 * β' * G ^ 2 / N = 3 * β' * (G ^ 2 / N) := by ring
      nlinarith
    · rw [min_eq_right h]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have e2 : N * (K0 ^ 2 * (1 + 3 * β' * G ^ 2 / N)) = K0 ^ 2 * (N + 3 * β' * G ^ 2) := by
        field_simp
      rw [e2]
      have hK2 : 0 ≤ K0 ^ 2 := sq_nonneg K0
      have h3 : K0 ^ 2 * N ≤ K0 ^ 2 * G ^ 2 := mul_le_mul_of_nonneg_left h hK2
      nlinarith [mul_nonneg hβ' (sq_nonneg G)]
  linarith

/-- `min{x, N} ≥ min{x, n}/4` whenever `N > n/4`; used to pass from the feature-group size
`N` to the width `n`.
Paper: proofs of `thm:pn-normalized-gain` (normalization_gain.tex) and `cor:pn-scaled-padding`
(normalization_depth_lower.tex), `N > n/4`. -/
theorem min_quarter {x N n : ℝ} (hx : 0 ≤ x) (hN : n / 4 < N) :
    min x n / 4 ≤ min x N := by
  rcases le_total x N with h | h
  · rw [min_eq_left h]
    have := min_le_left x n
    linarith
  · rw [min_eq_right h]
    have := min_le_right x n
    linarith

/-! ## The fixed readout -/

/-- The polynomial identity behind the whole-domain readout bound:
`(16/3)(3 + F²/4) - (|F| + 2)² = (|F| - 6)²/3`.
Paper: proofs of `thm:pn-normalized-gain` (normalization_gain.tex) and `thm:real-ffn-lower`
(normalization_ffn.tex). -/
theorem head_bound_identity (F : ℝ) :
    (16 / 3 : ℝ) * (3 + F ^ 2 / 4) - (|F| + 2) ^ 2 = (|F| - 6) ^ 2 / 3 := by
  have habs : |F| ^ 2 = F ^ 2 := sq_abs F
  nlinarith

/-- The fixed logit `h/(4√v)` is at most `1/√3 < 1` in absolute value whenever
`|h| ≤ |F| + 2` and `v ≥ 3 + F²/4`.
Paper: proofs of `thm:pn-normalized-gain` (normalization_gain.tex) and `thm:real-ffn-lower`
(normalization_ffn.tex). -/
theorem readout_le {h F v : ℝ} (hh : |h| ≤ |F| + 2) (hv : 3 + F ^ 2 / 4 ≤ v) :
    |h| / (4 * √v) ≤ 1 / √3 ∧ |F| + 2 ≤ 4 * √v / √3 := by
  have hv0 : 0 < v := by nlinarith [sq_nonneg F]
  have hs : 0 < √v := sqrt_pos.2 hv0
  have h3 : (0 : ℝ) < √3 := by positivity
  have hid := head_bound_identity F
  have key : (|F| + 2) ^ 2 ≤ (4 * √v / √3) ^ 2 := by
    rw [div_pow, mul_pow, sq_sqrt hv0.le, sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    nlinarith [sq_nonneg (|F| - 6)]
  have key2 : |F| + 2 ≤ 4 * √v / √3 := (abs_le_of_sq_le_sq' key (by positivity)).2
  refine ⟨?_, key2⟩
  rw [div_le_div_iff₀ (by positivity) h3]
  have : |h| ≤ 4 * √v / √3 := le_trans hh key2
  rw [le_div_iff₀ h3] at this
  linarith

/-- The conditional output mean of the fixed head, increased along the shift. For `z ∈ [0,1]`,
`k ∈ [0,1]`, `A ≥ 0` and `A + k ≤ 1`,
`((1+z)/2) tanh(A + k) + ((1-z)/2) tanh(A - k) ≥ (zk + A)/4`; the slope of `tanh` on `[-1,1]`
is at least `sech²(1) > 1/4`.
Paper: proofs of `thm:pn-normalized-gain` (normalization_gain.tex), `eq:pn-scaled-coordinatehead`
(normalization_depth_lower.tex) and `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem head_shift {z A k : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (hA : 0 ≤ A) (hAk : A + k ≤ 1) :
    (z * k + A) / 4 ≤ (1 + z) / 2 * tanh (A + k) + (1 - z) / 2 * tanh (A - k) := by
  have h1 := tanh_sub_tanh_ge (a := k) (b := A + k) (by linarith) (by linarith) hAk
  have h2 := tanh_sub_tanh_ge (a := -k) (b := A - k) (by linarith) (by linarith) (by linarith)
  have h3 := half_le_tanh hk0 hk1
  have hneg : tanh (-k) = -tanh k := Real.tanh_neg k
  rw [hneg] at h2
  have e : (1 + z) / 2 * tanh (A + k) + (1 - z) / 2 * tanh (A - k)
      = (1 + z) / 2 * (tanh (A + k) - tanh k) + (1 - z) / 2 * (tanh (A - k) - -tanh k)
        + z * tanh k := by ring
  rw [e]
  have hz' : 0 ≤ (1 - z) / 2 := by linarith
  have hz'' : 0 ≤ (1 + z) / 2 := by linarith
  have := mul_le_mul_of_nonneg_left h1 hz''
  have := mul_le_mul_of_nonneg_left h2 hz'
  have := mul_le_mul_of_nonneg_left h3 hz0
  nlinarith

/-! ## The carrier family: floors (`thm:pn-normalized-gain`, `eq:pn-carrier-floor`) -/

/-- The carrier speed `c = tanh 1`. -/
noncomputable def cT : ℝ := tanh 1

/-- `c = tanh 1 > 3/4`. -/
theorem cT_gt : (3 : ℝ) / 4 < cT := tanh_one_gt

/-- `c > 0`. -/
theorem cT_pos : 0 < cT := by have := cT_gt; linarith

/-- `c < 1`. -/
theorem cT_lt_one : cT < 1 := tanh_one_lt_one

/-- Completing the square in `eq:pn-carrier-floor`: after multiplication by
`A = 3 + θ(1+c)²` the difference is `[A - θc(1+c)(1+τ)]²`.
Paper: `eq:pn-carrier-floor` (normalization_gain.tex). -/
theorem carrier_floor_identity (theta c tau : ℝ) :
    (3 + theta * (1 + c) ^ 2) * (3 + theta * (c * tau - 1) ^ 2)
      - 3 * theta * c ^ 2 * (1 + tau) ^ 2 =
    (3 + theta * (1 + c) ^ 2 - theta * c * (1 + c) * (1 + tau)) ^ 2 := by
  ring

/-- The carrier floor `3 + θ(cτ - 1)² ≥ (3θc²/(3 + θ(1+c)²))(1+τ)²` for `θ > 0`.
Paper: `eq:pn-carrier-floor` (normalization_gain.tex). -/
theorem carrier_floor (theta c tau : ℝ) (htheta : 0 < theta) :
    (3 * theta * c ^ 2 / (3 + theta * (1 + c) ^ 2)) * (1 + tau) ^ 2
      ≤ 3 + theta * (c * tau - 1) ^ 2 := by
  have hd : 0 < 3 + theta * (1 + c) ^ 2 := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).2
  have hid := carrier_floor_identity theta c tau
  have hs := sq_nonneg (3 + theta * (1 + c) ^ 2 - theta * c * (1 + c) * (1 + tau))
  nlinarith

/-- At `θ = 1/4`, the floor constant is `γ₀ = 3c²/(12 + (1+c)²)`, and `γ₀ > 1/12`: the
inequality `c > 3/4` gives `35c² - 2c - 13 > 0`.
Paper: `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem gamma0_spec :
    3 * (1 / 4) * cT ^ 2 / (3 + (1 / 4) * (1 + cT) ^ 2) = 3 * cT ^ 2 / (12 + (1 + cT) ^ 2) ∧
      (1 : ℝ) / 12 < 3 * cT ^ 2 / (12 + (1 + cT) ^ 2) := by
  have hc := cT_gt
  constructor
  · field_simp; ring
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith

/-- A carrier coordinate `e - cτ` with an arbitrary initial sign `e` has square at least
`(cτ - 1)²`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem carrier_sq_ge {e τ c : ℝ} (he : e = 1 ∨ e = -1) (hτ : 0 ≤ τ) (hc : 0 ≤ c) :
    (c * τ - 1) ^ 2 ≤ (e - c * τ) ^ 2 := by
  rcases he with rfl | rfl
  · nlinarith
  · nlinarith [mul_nonneg hc hτ]

/-- **The full-cube floor.** If the squared denominator satisfies `v ≥ 3 + η(cτ - 1)²` with
`η ≥ 1/4` (a carrier fraction), then `v ≥ γ₀ (1+τ)²` with `γ₀ = 3c²/(12 + (1+c)²) > 1/12`.
Paper: `thm:pn-normalized-gain` (normalization_gain.tex); `thm:main-carrier`
(main_normalization.tex). -/
theorem full_cube_floor {v η τ : ℝ} (hη : 1 / 4 ≤ η) (hv : 3 + η * (cT * τ - 1) ^ 2 ≤ v) :
    3 * cT ^ 2 / (12 + (1 + cT) ^ 2) * (1 + τ) ^ 2 ≤ v := by
  have h1 := carrier_floor (1 / 4) cT τ (by norm_num)
  rw [gamma0_spec.1] at h1
  have h2 : (1 / 4 : ℝ) * (cT * τ - 1) ^ 2 ≤ η * (cT * τ - 1) ^ 2 :=
    mul_le_mul_of_nonneg_right hη (sq_nonneg _)
  linarith

/-! ## The carrier family: the scalar recurrence -/

/-- The squared normalization denominator on the lower-bound subdomain, with `η = N/n`:
`4 - η - ηz² + ηF² + η(1 + cτ_j)²` (stabilizer `3`, inert coordinates of square one,
features `x_i - z + F`, carriers `-(1 + cτ_j)`).
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
noncomputable def carrierDen (η : ℝ) (a : ℕ → ℝ) (j : ℕ) (z F : ℝ) : ℝ :=
  4 - η - η * z ^ 2 + η * F ^ 2 + η * (1 + cT * (schedR a j - 1)) ^ 2

/-- The feature mean `F_j(z)` of the carrier family: `F_0(z) = z` and
`F_{j+1} = F_j + a_j tanh(s F_j / √(carrierDen))`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
noncomputable def carrierF (s η : ℝ) (a : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0, z => z
  | j + 1, z => carrierF s η a j z
      + a j * tanh (s * carrierF s η a j z / √(carrierDen η a j z (carrierF s η a j z)))

/-- The carrier denominator is at least `3 + ηF²` (stabilizer three).
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem carrierDen_ge {η : ℝ} (a : ℕ → ℝ) (j : ℕ) {z F : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2)
    (hz : z ^ 2 ≤ 1) : 3 + η * F ^ 2 ≤ carrierDen η a j z F := by
  unfold carrierDen
  have : η * z ^ 2 ≤ η := by nlinarith
  have : 0 ≤ η * (1 + cT * (schedR a j - 1)) ^ 2 := by positivity
  linarith

/-- The recurrence is odd in `z`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem carrierF_neg (s η : ℝ) (a : ℕ → ℝ) (j : ℕ) (z : ℝ) :
    carrierF s η a j (-z) = -carrierF s η a j z := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [carrierF, ih, carrierDen, neg_sq]
    rw [show s * -carrierF s η a j z = -(s * carrierF s η a j z) by ring, neg_div, Real.tanh_neg]
    ring

/-- For `z ∈ [0,1]`, `z ≤ F_j(z) ≤ z + τ_j`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem carrierF_bounds {s η : ℝ} {a : ℕ → ℝ} (hs : 0 ≤ s) (ha : ∀ k, 0 ≤ a k) {z : ℝ}
    (hz0 : 0 ≤ z) (j : ℕ) :
    z ≤ carrierF s η a j z ∧ carrierF s η a j z ≤ z + (schedR a j - 1) := by
  induction j with
  | zero => simp [carrierF, schedR_zero]
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [carrierF]
    rw [schedR_succ]
    have hF : 0 ≤ carrierF s η a j z := le_trans hz0 h1
    have ht0 : 0 ≤ tanh (s * carrierF s η a j z / √(carrierDen η a j z (carrierF s η a j z))) :=
      tanh_nonneg (div_nonneg (mul_nonneg hs hF) (sqrt_nonneg _))
    have ht1 := tanh_le_one (s * carrierF s η a j z / √(carrierDen η a j z (carrierF s η a j z)))
    constructor
    · have := mul_nonneg (ha j) ht0; linarith
    · have := mul_le_mul_of_nonneg_left ht1 (ha j); linarith

/-- The normalized update. With `u_j = F_j/r_j`, `q_j = a_j/r_{j+1}` and
`b_j = (4 - η - ηz² + η(1 + cτ_j)²)/r_j²`, the recurrence reads
`u_{j+1} = (1 - q_j) u_j + q_j tanh(s u_j/√(b_j + η u_j²))`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem carrier_normalized_update {s η : ℝ} {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (j : ℕ) (z : ℝ)
    (hden : 0 < carrierDen η a j z (carrierF s η a j z)) :
    carrierF s η a (j + 1) z / schedR a (j + 1)
      = (1 - a j / schedR a (j + 1)) * (carrierF s η a j z / schedR a j)
        + a j / schedR a (j + 1) * tanh (s * (carrierF s η a j z / schedR a j)
          / √((4 - η - η * z ^ 2 + η * (1 + cT * (schedR a j - 1)) ^ 2) / schedR a j ^ 2
              + η * (carrierF s η a j z / schedR a j) ^ 2)) := by
  have hr := schedR_pos ha j
  have hr1 := schedR_pos ha (j + 1)
  have hs1 : schedR a (j + 1) = schedR a j + a j := schedR_succ a j
  set F := carrierF s η a j z
  have harg : s * (F / schedR a j) / √((4 - η - η * z ^ 2 + η * (1 + cT * (schedR a j - 1)) ^ 2)
      / schedR a j ^ 2 + η * (F / schedR a j) ^ 2) = s * F / √(carrierDen η a j z F) := by
    have e : (4 - η - η * z ^ 2 + η * (1 + cT * (schedR a j - 1)) ^ 2) / schedR a j ^ 2
        + η * (F / schedR a j) ^ 2 = carrierDen η a j z F / schedR a j ^ 2 := by
      unfold carrierDen; field_simp; ring
    rw [e, sqrt_div hden.le, sqrt_sq hr.le]
    field_simp
  rw [harg]
  rw [show carrierF s η a (j + 1) z = F + a j * tanh (s * F / √(carrierDen η a j z F)) from rfl]
  rw [hs1]
  have hne : schedR a j + a j ≠ 0 := by rw [← hs1]; exact hr1.ne'
  field_simp
  ring

/-! ## The carrier family: gains -/

/-- `A₀ = θc²` at the comparison level `θ` (`θ = 1/2` in `thm:pn-normalized-gain`, `θ = η` in
the lower half of `thm:main-carrier`).
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex); proof of
`thm:pn-family-query-law` (normalization_family_query.tex). -/
noncomputable def A0 (θ : ℝ) : ℝ := θ * cT ^ 2

/-- `A₁ = 4 + 2θc(1 - c)`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
noncomputable def A1 (θ : ℝ) : ℝ := 4 + 2 * θ * cT * (1 - cT)

/-- `A₀ > 0`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem A0_pos {θ : ℝ} (hθ : 0 < θ) : 0 < A0 θ := by unfold A0; have := cT_pos; positivity

/-- `A₁ > 0`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem A1_pos {θ : ℝ} (hθ : 0 ≤ θ) : 0 < A1 θ := by
  unfold A1; have := cT_pos; have := cT_lt_one
  have : 0 ≤ θ * cT * (1 - cT) := mul_nonneg (mul_nonneg hθ cT_pos.le) (by linarith)
  nlinarith

/-- The normalized nonsignal part of the denominator: `b_j ≤ A₀ + A₁/r_j` when `η ≤ θ`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem carrier_b_le {θ η z r : ℝ} (hη0 : 0 ≤ η) (hηθ : η ≤ θ) (hr : 1 ≤ r) :
    (4 - η - η * z ^ 2 + η * (1 + cT * (r - 1)) ^ 2) / r ^ 2 ≤ A0 θ + A1 θ / r := by
  have hc0 := cT_pos
  have hc1 := cT_lt_one
  have hr0 : 0 < r := by linarith
  rw [div_le_iff₀ (by positivity)]
  unfold A0 A1
  have e : (θ * cT ^ 2 + (4 + 2 * θ * cT * (1 - cT)) / r) * r ^ 2
      = θ * cT ^ 2 * r ^ 2 + (4 + 2 * θ * cT * (1 - cT)) * r := by field_simp
  rw [e]
  have h1 : (1 + cT * (r - 1)) ^ 2 = cT ^ 2 * r ^ 2 + 2 * cT * (1 - cT) * r + (1 - cT) ^ 2 := by
    ring
  have hcc : 0 ≤ cT * (1 - cT) := mul_nonneg hc0.le (by linarith)
  have h2 : η * (1 - cT) ^ 2 ≤ η := by
    have : (1 - cT) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have h3 : η * (cT ^ 2 * r ^ 2) ≤ θ * cT ^ 2 * r ^ 2 := by
    have := mul_le_mul_of_nonneg_right hηθ (sq_nonneg (cT * r))
    nlinarith
  have h4 : η * (2 * cT * (1 - cT) * r) ≤ 2 * θ * cT * (1 - cT) * r := by
    have := mul_le_mul_of_nonneg_right hηθ (mul_nonneg hcc hr0.le)
    nlinarith
  have h5 : 4 ≤ 4 * r := by linarith
  have h6 : 0 ≤ η * z ^ 2 := by positivity
  rw [h1]
  nlinarith

/-- The normalized nonsignal part is positive: `b_j ≥ 3/r_j² > 0` for `z² ≤ 1`, `η ≤ 1/2`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem carrier_b_pos {η z r : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2) (hz : z ^ 2 ≤ 1) (hr : 0 < r) :
    3 / r ^ 2 ≤ (4 - η - η * z ^ 2 + η * (1 + cT * (r - 1)) ^ 2) / r ^ 2 ∧
      0 < (4 - η - η * z ^ 2 + η * (1 + cT * (r - 1)) ^ 2) / r ^ 2 := by
  have h3 : 3 ≤ 4 - η - η * z ^ 2 + η * (1 + cT * (r - 1)) ^ 2 := by
    have : η * z ^ 2 ≤ η := by nlinarith
    have : 0 ≤ η * (1 + cT * (r - 1)) ^ 2 := by positivity
    linarith
  have hle := div_le_div_of_nonneg_right h3 (sq_nonneg r)
  exact ⟨hle, lt_of_lt_of_le (by positivity) hle⟩

/-- The gain constant `κ_θ = s/√A₀ = s/(c√θ)`. At `θ = η` it is the limiting gain
`s/(c√η)`; at `θ = 1/2` it is `√2 s/c`, a lower bound for it when `η ≤ 1/2`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
noncomputable def kap (θ s : ℝ) : ℝ := s / √(A0 θ)

/-- The gain at radius `r`: `t(r) = s/√(A₀ + A₁/r)`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
noncomputable def tGain (θ s r : ℝ) : ℝ := s / √(A0 θ + A1 θ / r)

/-- The saturation coefficient `B(r) = (s² + θ)/(A₀ + A₁/r)`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
noncomputable def BGain (θ s r : ℝ) : ℝ := (s ^ 2 + θ) / (A0 θ + A1 θ / r)

/-- `κ_θ = s/(c√θ)`.
Paper: `thm:main-carrier` (main_normalization.tex), definition of `ν_η = κ_η - 1`. -/
theorem kap_eq {θ : ℝ} (hθ : 0 < θ) (s : ℝ) : kap θ s = s / (cT * √θ) := by
  unfold kap A0
  rw [sqrt_mul hθ.le, sqrt_sq cT_pos.le, mul_comm]

/-- `κ_{1/2} = √2 s/c`, so `κ_{1/2} > 1` exactly when `s > c/√2`, and `ν = κ_{1/2} - 1`.
Paper: `thm:pn-normalized-gain` (normalization_gain.tex), definition of `ν`. -/
theorem kap_half (s : ℝ) : kap (1 / 2) s = √2 * s / cT := by
  rw [kap_eq (by norm_num)]
  have hc := cT_pos
  have h2 : (0 : ℝ) < √2 := by positivity
  have hs2 : √2 * √2 = 2 := mul_self_sqrt (by norm_num)
  rw [show √(1 / 2 : ℝ) = 1 / √2 by rw [sqrt_div' _ (by norm_num), sqrt_one]]
  field_simp

/-- `κ_θ ≥ κ_{1/2}` for `0 < θ ≤ 1/2` and `s ≥ 0`: the exponent `2ν_η` of `thm:main-carrier`
is at least the exponent `2ν` of `thm:pn-normalized-gain`.
Paper: proof of `thm:pn-family-query-law` (normalization_family_query.tex),
`ν_η ≥ √2 s/c - 1`. -/
theorem kap_half_le {θ s : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 2) (hs : 0 ≤ s) :
    kap (1 / 2) s ≤ kap θ s := by
  unfold kap
  apply div_le_div_of_nonneg_left hs (sqrt_pos.2 (A0_pos hθ))
  apply sqrt_le_sqrt
  unfold A0
  exact mul_le_mul_of_nonneg_right hθ1 (sq_nonneg _)

/-- `0 ≤ κ - t(r) ≤ K/r` with `K = κA₁/(2A₀)`, from `1 - (1+x)^{-1/2} ≤ x/2`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem gain_gap {θ s r : ℝ} (hθ : 0 < θ) (hs : 0 ≤ s) (hr : 0 < r) :
    tGain θ s r ≤ kap θ s ∧ kap θ s - tGain θ s r ≤ kap θ s * A1 θ / (2 * A0 θ) / r := by
  have hA0 := (A0_pos hθ)
  have hA1 := (A1_pos hθ.le)
  have hx : 0 ≤ A1 θ / (A0 θ * r) := by positivity
  have he : tGain θ s r = kap θ s * (1 / √(1 + A1 θ / (A0 θ * r))) := by
    unfold tGain kap
    have e : A0 θ + A1 θ / r = A0 θ * (1 + A1 θ / (A0 θ * r)) := by field_simp
    rw [e, sqrt_mul hA0.le]
    have : 0 < √(1 + A1 θ / (A0 θ * r)) := sqrt_pos.2 (by positivity)
    have : 0 < √(A0 θ) := sqrt_pos.2 hA0
    field_simp
  have hk : 0 ≤ kap θ s := by unfold kap; positivity
  have hs1 : 1 ≤ √(1 + A1 θ / (A0 θ * r)) := by
    have := sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + A1 θ / (A0 θ * r) by linarith)
    rwa [sqrt_one] at this
  constructor
  · rw [he]
    have : 1 / √(1 + A1 θ / (A0 θ * r)) ≤ 1 := by rw [div_le_one (by linarith)]; exact hs1
    nlinarith
  · rw [he]
    have h := one_sub_inv_sqrt_le hx
    have e2 : kap θ s * A1 θ / (2 * A0 θ) / r = kap θ s * (A1 θ / (A0 θ * r) / 2) := by field_simp
    rw [e2]
    nlinarith

/-- The tanh step of the carrier family: for `u ≥ 0`, `0 < b ≤ A₀ + A₁/r` and `0 ≤ η ≤ θ`,
`tanh(s u/√(b + ηu²)) ≥ t(r) u/√(1 + B(r) u²)`, from `tanh y ≥ y/√(1+y²)`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem carrier_tanh_step {θ s η b r u : ℝ} (hθ : 0 < θ) (hs : 0 ≤ s) (hη0 : 0 ≤ η)
    (hηθ : η ≤ θ)
    (hb0 : 0 < b) (hb : b ≤ A0 θ + A1 θ / r) (hr : 0 < r) (hu : 0 ≤ u) :
    tGain θ s r * u / √(1 + BGain θ s r * u ^ 2) ≤ tanh (s * u / √(b + η * u ^ 2)) := by
  have hA : 0 < A0 θ + A1 θ / r := by have := (A0_pos hθ); have := (A1_pos hθ.le); positivity
  have hD : 0 < b + η * u ^ 2 := by positivity
  set y := s * u / √(b + η * u ^ 2)
  have hy : 0 ≤ y := by positivity
  have h1 := div_sqrt_le_tanh hy
  have hform : y / √(1 + y ^ 2) = s * u / √(b + η * u ^ 2 + s ^ 2 * u ^ 2) := by
    have hsD : 0 < √(b + η * u ^ 2) := sqrt_pos.2 hD
    have e : 1 + y ^ 2 = (b + η * u ^ 2 + s ^ 2 * u ^ 2) / (b + η * u ^ 2) := by
      simp only [y]; rw [div_pow, mul_pow, sq_sqrt hD.le]; field_simp
    rw [e, sqrt_div (by positivity)]
    have : 0 < √(b + η * u ^ 2 + s ^ 2 * u ^ 2) := sqrt_pos.2 (by positivity)
    simp only [y]
    field_simp
  rw [hform] at h1
  refine le_trans ?_ h1
  have hlhs : tGain θ s r * u / √(1 + BGain θ s r * u ^ 2)
      = s * u / √(A0 θ + A1 θ / r + (s ^ 2 + θ) * u ^ 2) := by
    unfold tGain BGain
    have e : A0 θ + A1 θ / r + (s ^ 2 + θ) * u ^ 2
        = (A0 θ + A1 θ / r) * (1 + (s ^ 2 + θ) / (A0 θ + A1 θ / r) * u ^ 2) := by
      have hne : A0 θ * r + A1 θ ≠ 0 := by have := (A0_pos hθ); have := (A1_pos hθ.le); positivity
      field_simp
    rw [e, sqrt_mul hA.le]
    have : 0 < √(1 + (s ^ 2 + θ) / (A0 θ + A1 θ / r) * u ^ 2) := sqrt_pos.2 (by positivity)
    have : 0 < √(A0 θ + A1 θ / r) := sqrt_pos.2 hA
    field_simp
  rw [hlhs]
  apply div_le_div_of_nonneg_left (by positivity) (sqrt_pos.2 (by positivity))
  apply sqrt_le_sqrt
  nlinarith [sq_nonneg u]

/-! ## The carrier family: the normalized-gain comparison -/

/-- `ν_θ = κ_θ - 1`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
noncomputable def nuG (θ s : ℝ) : ℝ := kap θ s - 1

/-- `K = κA₁/(2A₀)`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
noncomputable def KG (θ s : ℝ) : ℝ := kap θ s * A1 θ / (2 * A0 θ)

/-- `R_* = ⌈max{4, 2K/ν}⌉`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
noncomputable def RstarG (θ s : ℝ) : ℝ := (⌈max 4 (2 * KG θ s / nuG θ s)⌉₊ : ℝ)

/-- `M_* = R_* + 1`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
noncomputable def MstarG (θ s : ℝ) : ℝ := RstarG θ s + 1

/-- `C = κ(s² + θ)/(A₀ν)`; at `θ = 1/2` this is the constant `κ(s² + 1/2)/(A₀ν)` of the paper.
-/
noncomputable def CG (θ s : ℝ) : ℝ := kap θ s * (s ^ 2 + θ) / (A0 θ * nuG θ s)

/-- `E_* = (ν + K + ν²/2)/R_*`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
noncomputable def EstarG (θ s : ℝ) : ℝ := (nuG θ s + KG θ s + nuG θ s ^ 2 / 2) / RstarG θ s

/-- `R_* ≥ 4` and `R_* ≥ 2K/ν`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem RstarG_ge (θ s : ℝ) : 4 ≤ RstarG θ s ∧ 2 * KG θ s / nuG θ s ≤ RstarG θ s := by
  unfold RstarG
  have h := Nat.le_ceil (max 4 (2 * KG θ s / nuG θ s))
  exact ⟨le_trans (le_max_left _ _) h, le_trans (le_max_right _ _) h⟩

/-- Beyond `R_*` the gains stay in `[1 + ν/2, 1 + ν]`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex), `ν/2 ≤ ν_j ≤ ν`. -/
theorem gain_window {θ s r : ℝ} (hθ : 0 < θ) (hs : 0 ≤ s) (hν : 0 < nuG θ s) (hr : RstarG θ s ≤ r) :
    1 + nuG θ s / 2 ≤ tGain θ s r ∧ tGain θ s r ≤ 1 + nuG θ s ∧
      nuG θ s - KG θ s / r ≤ tGain θ s r - 1 := by
  have hR := RstarG_ge θ s
  have hr0 : 0 < r := by linarith
  obtain ⟨h1, h2⟩ := gain_gap hθ hs hr0
  have hK : 0 ≤ KG θ s := by
    unfold KG kap; have := (A0_pos hθ); have := (A1_pos hθ.le); positivity
  have hKr : KG θ s / r ≤ nuG θ s / 2 := by
    have : KG θ s / r ≤ KG θ s / RstarG θ s := div_le_div_of_nonneg_left hK (by linarith) hr
    have h2K : KG θ s / RstarG θ s ≤ nuG θ s / 2 := by
      rw [div_le_iff₀ (by linarith)]
      have := hR.2
      rw [div_le_iff₀ hν] at this
      linarith
    linarith
  unfold nuG at *
  have e : kap θ s * A1 θ / (2 * A0 θ) / r = KG θ s / r := rfl
  rw [e] at h2
  refine ⟨by linarith, by linarith, by linarith⟩

/-- One step of the carrier family past the burn-in: with `q = a_j/r_{j+1}`, `t = t(r_j)`,
`g = 1 - q + qt` and `d = qtB(r_j)/g`, `u_{j+1} ≥ g u_j/√(1 + d u_j²)`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex), the convexity step. -/
theorem carrier_step {θ s η : ℝ} {a : ℕ → ℝ} (hθ : 0 < θ) (hηθ : η ≤ θ) (hs : 0 ≤ s)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2)
    (ha : ∀ k, 0 ≤ a k) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (j : ℕ)
    (ht : 1 ≤ tGain θ s (schedR a j)) :
    (1 - a j / schedR a (j + 1) + a j / schedR a (j + 1) * tGain θ s (schedR a j))
        * (carrierF s η a j z / schedR a j)
        / √(1 + (a j / schedR a (j + 1) * tGain θ s (schedR a j) * BGain θ s (schedR a j)
            / (1 - a j / schedR a (j + 1) + a j / schedR a (j + 1) * tGain θ s (schedR a j)))
          * (carrierF s η a j z / schedR a j) ^ 2)
      ≤ carrierF s η a (j + 1) z / schedR a (j + 1) := by
  have hr := schedR_pos ha j
  have hr1' := schedR_ge_one ha j
  have hr1 := schedR_pos ha (j + 1)
  have hz2 : z ^ 2 ≤ 1 := by nlinarith
  set q := a j / schedR a (j + 1) with hq
  have hq0 : 0 ≤ q := div_nonneg (ha j) hr1.le
  have hq1 : q ≤ 1 := by
    rw [hq, div_le_one hr1, schedR_succ]; linarith
  have hF := (carrierF_bounds (η := η) hs ha hz0 j).1
  set u := carrierF s η a j z / schedR a j with hu
  have hu0 : 0 ≤ u := div_nonneg (le_trans hz0 hF) hr.le
  set b := (4 - η - η * z ^ 2 + η * (1 + cT * (schedR a j - 1)) ^ 2) / schedR a j ^ 2 with hb
  have hb0 : 0 < b := (carrier_b_pos hη0 hη1 hz2 hr).2
  have hb1 : b ≤ A0 θ + A1 θ / schedR a j := carrier_b_le hη0 hηθ hr1'
  have hden : 0 < carrierDen η a j z (carrierF s η a j z) := by
    have := carrierDen_ge a j (F := carrierF s η a j z) hη0 hη1 hz2
    nlinarith [sq_nonneg (carrierF s η a j z)]
  have hupd := carrier_normalized_update (s := s) (η := η) ha j z hden
  rw [← hu, ← hq, ← hb] at hupd
  rw [hupd]
  have htanh := carrier_tanh_step hθ hs hη0 hηθ hb0 hb1 hr hu0
  have hB : 0 ≤ BGain θ s (schedR a j) := by
    unfold BGain; have := (A0_pos hθ); have := (A1_pos hθ.le); positivity
  have hg : 0 < 1 - q + q * tGain θ s (schedR a j) := by nlinarith
  have hconv := step_convex hq0 hq1 (by linarith) hB hu0 hg
  calc _ ≤ (1 - q) * u + q * (tGain θ s (schedR a j) * u / √(1 + BGain θ s (schedR a j) * u ^ 2)) :=
        hconv
    _ ≤ (1 - q) * u + q * tanh (s * u / √(b + η * u ^ 2)) := by
        have := mul_le_mul_of_nonneg_left htanh hq0
        linarith

/-- The saturation coefficient past the burn-in: `d ≤ C(g² - 1)`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem carrier_d_le {θ s q r : ℝ} (hθ : 0 < θ) (hs : 0 ≤ s) (hν : 0 < nuG θ s)
    (hr : RstarG θ s ≤ r)
    (hq0 : 0 ≤ q) :
    0 < 1 - q + q * tGain θ s r ∧ 1 ≤ 1 - q + q * tGain θ s r ∧
      0 ≤ q * tGain θ s r * BGain θ s r / (1 - q + q * tGain θ s r) ∧
      q * tGain θ s r * BGain θ s r / (1 - q + q * tGain θ s r)
        ≤ CG θ s * ((1 - q + q * tGain θ s r) ^ 2 - 1) := by
  obtain ⟨w1, w2, _⟩ := gain_window hθ hs hν hr
  have hr0 : 0 < r := by have := (RstarG_ge θ s).1; linarith
  have hA0 := (A0_pos hθ)
  have hA1 := (A1_pos hθ.le)
  have hg1 : 1 ≤ 1 - q + q * tGain θ s r := by nlinarith
  have ht0 : 0 ≤ tGain θ s r := by linarith
  have hB0 : 0 ≤ BGain θ s r := by unfold BGain; positivity
  have hBle : BGain θ s r ≤ (s ^ 2 + θ) / A0 θ := by
    unfold BGain; apply div_le_div_of_nonneg_left (by positivity) hA0; have := div_pos hA1 hr0
    linarith
  refine ⟨by linarith, hg1, by positivity, ?_⟩
  have hκ : tGain θ s r ≤ kap θ s := by unfold nuG at w2; linarith
  have hd1 : q * tGain θ s r * BGain θ s r / (1 - q + q * tGain θ s r)
      ≤ q * kap θ s * ((s ^ 2 + θ) / A0 θ) := by
    rw [div_le_iff₀ (by linarith)]
    have h1 : q * tGain θ s r * BGain θ s r ≤ q * kap θ s * ((s ^ 2 + θ) / A0 θ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hκ hq0) hBle hB0 (by
        have : 0 ≤ kap θ s := by unfold kap; positivity
        positivity)
    have h2 : 0 ≤ q * kap θ s * ((s ^ 2 + θ) / A0 θ) := by
      have : 0 ≤ kap θ s := by unfold kap; positivity
      positivity
    nlinarith
  have hg2 : nuG θ s * q ≤ (1 - q + q * tGain θ s r) ^ 2 - 1 := by nlinarith
  have hC : CG θ s * (nuG θ s * q) = q * kap θ s * ((s ^ 2 + θ) / A0 θ) := by
    unfold CG; field_simp
  have hC0 : 0 ≤ CG θ s := by
    unfold CG; have : 0 ≤ kap θ s := by unfold kap; positivity
    positivity
  have := mul_le_mul_of_nonneg_left hg2 hC0
  linarith

/-- **The normalized-gain comparison** `eq:pn-normalized-gain-comparison`. Let `j₀ ≤ D` with
`R_* ≤ r_{j₀} ≤ M_*` and put `G = ∏_{j=j₀}^{D-1} g_j`. For `0 < z ≤ 1`,
`u_D(z) ≥ G (z/M_*) / √(1 + C(G² - 1)(z/M_*)²)`, and `G ≥ 1`.
Paper: `eq:pn-normalized-gain-comparison` in the proof of `thm:pn-normalized-gain`
(normalization_gain.tex). -/
theorem carrier_comparison {θ s η : ℝ} {a : ℕ → ℝ} (hθ : 0 < θ) (hηθ : η ≤ θ) (hs : 0 ≤ s)
    (hν : 0 < nuG θ s) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / 2) (ha : ∀ k, 0 ≤ a k) {j0 n : ℕ} (hj0 : RstarG θ s ≤ schedR a j0)
    (hj0' : schedR a j0 ≤ MstarG θ s) {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) :
    let g := fun i => 1 - a (j0 + i) / schedR a (j0 + i + 1)
      + a (j0 + i) / schedR a (j0 + i + 1) * tGain θ s (schedR a (j0 + i))
    1 ≤ ∏ i ∈ range n, g i ∧
    (∏ i ∈ range n, g i) * (z / MstarG θ s)
        / √(1 + CG θ s * ((∏ i ∈ range n, g i) ^ 2 - 1) * (z / MstarG θ s) ^ 2)
      ≤ carrierF s η a (j0 + n) z / schedR a (j0 + n) := by
  intro g
  set d := fun i => a (j0 + i) / schedR a (j0 + i + 1) * tGain θ s (schedR a (j0 + i))
      * BGain θ s (schedR a (j0 + i)) / g i with hd
  set u := fun i => carrierF s η a (j0 + i) z / schedR a (j0 + i) with hu
  have hrj : ∀ i, RstarG θ s ≤ schedR a (j0 + i) := fun i =>
    le_trans hj0 (schedR_mono ha (by omega))
  have hprop : ∀ i, 0 < g i ∧ 1 ≤ g i ∧ 0 ≤ d i ∧ d i ≤ CG θ s * (g i ^ 2 - 1) := by
    intro i
    obtain ⟨p1, p2, p3, p4⟩ := carrier_d_le hθ hs hν (hrj i)
      (div_nonneg (ha (j0 + i)) (schedR_pos ha (j0 + i + 1)).le)
    exact ⟨p1, p2, p3, p4⟩
  have hF0 := (carrierF_bounds (η := η) hs ha hz0.le j0).1
  have hu0 : 0 < u 0 := by
    simp only [hu, add_zero]; exact div_pos (lt_of_lt_of_le hz0 hF0) (schedR_pos ha j0)
  have hstep : ∀ i < n, g i * u i / √(1 + d i * u i ^ 2) ≤ u (i + 1) := by
    intro i _
    have ht := (gain_window hθ hs hν (hrj i)).1
    have := carrier_step hθ hηθ hs hη0 hη1 ha hz0.le hz1 (j0 + i) (by linarith)
    exact this
  have hchain := reciprocal_chain (u := u) (g := g) (d := d) (C := CG θ s) (n := n) hu0
    (fun i _ => (hprop i).1) (fun i _ => (hprop i).2.2.1) (fun i _ => (hprop i).2.2.2) hstep n
    le_rfl
  have hG1 : 1 ≤ ∏ i ∈ range n, g i := by
    apply one_le_prod₀ (fun i _ => (hprop i).2.1)
  refine ⟨hG1, ?_⟩
  have hMs : 0 < MstarG θ s := by unfold MstarG; have := (RstarG_ge θ s).1; linarith
  have hv : z / MstarG θ s ≤ u 0 := by
    simp only [hu, add_zero]
    have hr := schedR_pos ha j0
    calc z / MstarG θ s ≤ carrierF s η a j0 z / MstarG θ s := div_le_div_of_nonneg_right hF0 hMs.le
      _ ≤ carrierF s η a j0 z / schedR a j0 :=
          div_le_div_of_nonneg_left (le_trans hz0.le hF0) hr hj0'
  have hC0 : 0 ≤ CG θ s := by
    unfold CG; have : 0 ≤ kap θ s := by unfold kap; have := (A0_pos hθ); positivity
    have := (A0_pos hθ); positivity
  have hCG : 0 ≤ CG θ s * ((∏ i ∈ range n, g i) ^ 2 - 1) := by
    apply mul_nonneg hC0; nlinarith
  exact invert_comparison hchain.1 (div_pos hz0 hMs) hv (by linarith) hCG hchain.2

/-- **The gain product.** With `j₀` as in `carrier_comparison`,
`G ≥ e^{-E_*} (r_D/M_*)^ν`, `E_* = (ν + K + ν²/2)/R_*`; the step schedule only needs
`0 ≤ a_j ≤ 1`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem carrier_gain_product {θ s : ℝ} {a : ℕ → ℝ} (hθ : 0 < θ) (hs : 0 ≤ s) (hν : 0 < nuG θ s)
    (ha : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1) {j0 n : ℕ} (hj0 : RstarG θ s ≤ schedR a j0)
    (hj0' : schedR a j0 ≤ MstarG θ s) :
    exp (-EstarG θ s) * (schedR a (j0 + n) / MstarG θ s) ^ nuG θ s
      ≤ ∏ i ∈ range n, (1 - a (j0 + i) / schedR a (j0 + i + 1)
        + a (j0 + i) / schedR a (j0 + i + 1) * tGain θ s (schedR a (j0 + i))) := by
  set q := fun i => a (j0 + i) / schedR a (j0 + i + 1)
  set x := fun i => (tGain θ s (schedR a (j0 + i)) - 1) * q i
  have hrj : ∀ i, RstarG θ s ≤ schedR a (j0 + i) := fun i =>
    le_trans hj0 (schedR_mono ha (by omega))
  have hq0 : ∀ i, 0 ≤ q i := fun i => div_nonneg (ha _) (schedR_pos ha _).le
  have hx0 : ∀ i, 0 ≤ x i := fun i => by
    have := (gain_window hθ hs hν (hrj i)).1
    exact mul_nonneg (by linarith) (hq0 i)
  have hprod : ∏ i ∈ range n, (1 - a (j0 + i) / schedR a (j0 + i + 1)
      + a (j0 + i) / schedR a (j0 + i + 1) * tGain θ s (schedR a (j0 + i)))
      = ∏ i ∈ range n, (1 + x i) := by
    apply prod_congr rfl; intro i _; simp only [x, q]; ring
  rw [hprod]
  refine le_trans ?_ (prod_one_add_ge (range n) x (fun i _ => hx0 i))
  obtain ⟨S1, S2, S3⟩ := schedule_sums ha ha1 j0 n
  have hK : 0 ≤ KG θ s := by unfold KG kap; have := (A0_pos hθ); have := (A1_pos hθ.le); positivity
  have hr0 := schedR_pos ha j0
  have hrD := schedR_pos ha (j0 + n)
  have hRs := (RstarG_ge θ s).1
  -- lower bound on the linear sum
  have hlin : nuG θ s * ∑ i ∈ range n, q i - KG θ s * (1 / schedR a j0 - 1 / schedR a (j0 + n))
      ≤ ∑ i ∈ range n, x i := by
    rw [← S2, mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_le_sum; intro i _
    have hw := (gain_window hθ hs hν (hrj i)).2.2
    have hr := schedR_pos ha (j0 + i)
    have : (nuG θ s - KG θ s / schedR a (j0 + i)) * q i ≤ x i :=
      mul_le_mul_of_nonneg_right hw (hq0 i)
    simp only [q] at this ⊢
    have e : nuG θ s * (a (j0 + i) / schedR a (j0 + i + 1))
        - KG θ s * (a (j0 + i) / schedR a (j0 + i + 1) / schedR a (j0 + i))
        = (nuG θ s - KG θ s / schedR a (j0 + i)) * (a (j0 + i) / schedR a (j0 + i + 1)) := by ring
    rw [e]; exact this
  -- upper bound on the quadratic sum
  have hquad : ∑ i ∈ range n, x i ^ 2 / 2
      ≤ nuG θ s ^ 2 / 2 * (1 / schedR a j0 - 1 / schedR a (j0 + n)) := by
    have : ∑ i ∈ range n, x i ^ 2 ≤ nuG θ s ^ 2 * ∑ i ∈ range n, q i ^ 2 := by
      rw [mul_sum]; apply sum_le_sum; intro i _
      have hw := (gain_window hθ hs hν (hrj i)).2.1
      have h0 : 0 ≤ tGain θ s (schedR a (j0 + i)) - 1 := by
        have := (gain_window hθ hs hν (hrj i)).1; linarith
      simp only [x]
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 (by linarith) 2) (sq_nonneg _)
    have hS1 : ∑ i ∈ range n, q i ^ 2 ≤ 1 / schedR a j0 - 1 / schedR a (j0 + n) := S1
    rw [← sum_div]
    have := mul_le_mul_of_nonneg_left hS1 (sq_nonneg (nuG θ s))
    calc (∑ i ∈ range n, x i ^ 2) / 2
        ≤ nuG θ s ^ 2 * (1 / schedR a j0 - 1 / schedR a (j0 + n)) / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num); linarith
      _ = _ := by ring
  have hgap : 0 ≤ 1 / schedR a j0 - 1 / schedR a (j0 + n) := by
    have := schedR_mono ha (show j0 ≤ j0 + n by omega)
    rw [sub_nonneg]; exact one_div_le_one_div_of_le hr0 this
  have hgap2 : 1 / schedR a j0 - 1 / schedR a (j0 + n) ≤ 1 / RstarG θ s := by
    have : 1 / schedR a j0 ≤ 1 / RstarG θ s := one_div_le_one_div_of_le (by linarith) hj0
    have : 0 < 1 / schedR a (j0 + n) := by positivity
    linarith
  have hlog : log (schedR a (j0 + n) / MstarG θ s) ≤ log (schedR a (j0 + n) / schedR a j0) := by
    apply log_le_log (div_pos hrD (by linarith))
    exact div_le_div_of_nonneg_left hrD.le hr0 hj0'
  have hexpo : nuG θ s * log (schedR a (j0 + n) / MstarG θ s) - EstarG θ s
      ≤ ∑ i ∈ range n, x i - ∑ i ∈ range n, x i ^ 2 / 2 := by
    have e1 : EstarG θ s = (nuG θ s + KG θ s + nuG θ s ^ 2 / 2) * (1 / RstarG θ s) := by
      unfold EstarG; ring
    have hcoef : 0 ≤ nuG θ s + KG θ s + nuG θ s ^ 2 / 2 := by positivity
    have := mul_le_mul_of_nonneg_left hgap2 hcoef
    have h3 := mul_le_mul_of_nonneg_left S3 hν.le
    have h4 := mul_le_mul_of_nonneg_left hlog hν.le
    nlinarith
  calc exp (-EstarG θ s) * (schedR a (j0 + n) / MstarG θ s) ^ nuG θ s
      = exp (nuG θ s * log (schedR a (j0 + n) / MstarG θ s) - EstarG θ s) := by
        rw [rpow_def_of_pos (div_pos hrD (by unfold MstarG; linarith)), ← exp_add]; ring_nf
    _ ≤ exp (∑ i ∈ range n, x i - ∑ i ∈ range n, x i ^ 2 / 2) := exp_le_exp.2 hexpo

/-- The first index past `R`: if `1 < R ≤ r_D` and `0 ≤ a_j ≤ 1`, some `j₀ ≤ D` has
`R ≤ r_{j₀} ≤ R + 1`.
Paper: proofs of `thm:pn-normalized-gain` (normalization_gain.tex) and `cor:pn-scheduled-lower`
(normalization_depth_lower.tex), the first index with `r_{j₀} ≥ R`. -/
theorem exists_first_index {a : ℕ → ℝ} (ha1 : ∀ k, a k ≤ 1) {R : ℝ}
    (hR : 1 < R) {D : ℕ} (hD : R ≤ schedR a D) :
    ∃ j0 ≤ D, R ≤ schedR a j0 ∧ schedR a j0 ≤ R + 1 := by
  classical
  have hex : ∃ j, R ≤ schedR a j := ⟨D, hD⟩
  set j0 := Nat.find hex with hj0
  have hP : R ≤ schedR a j0 := Nat.find_spec hex
  have hle : j0 ≤ D := Nat.find_min' hex hD
  refine ⟨j0, hle, hP, ?_⟩
  have hpos : j0 ≠ 0 := by
    intro h; rw [h, schedR_zero] at hP; linarith
  obtain ⟨k, hk⟩ : ∃ k, j0 = k + 1 := ⟨j0 - 1, by omega⟩
  have hnot : ¬ R ≤ schedR a k := Nat.find_min hex (by omega)
  rw [hk, schedR_succ]
  have := ha1 k
  push Not at hnot
  linarith

/-! ## The carrier family: the fixed head and the query bound -/

/-- The conditional output-sign mean of the fixed head `±𝒩₃(h_D)₁/4` on the lower-bound
subdomain, given `M = z`: the observed feature is `x₁ - z + F_D(z)` with `x₁ = ±1` of
probabilities `(1 ± z)/2` (the conditional law of `x₁` given `M = z`, taken as a modeling step;
see the module header), and `L(z) = 4√(v_D(z))`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
noncomputable def carrierHead (s η : ℝ) (a : ℕ → ℝ) (D : ℕ) (z : ℝ) : ℝ :=
  (1 + z) / 2 * tanh ((carrierF s η a D z - z + 1)
      / (4 * √(carrierDen η a D z (carrierF s η a D z))))
    + (1 - z) / 2 * tanh ((carrierF s η a D z - z - 1)
      / (4 * √(carrierDen η a D z (carrierF s η a D z))))

/-- The head is odd: the denominator is even in `z`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem carrierHead_neg (s η : ℝ) (a : ℕ → ℝ) (D : ℕ) (z : ℝ) :
    carrierHead s η a D (-z) = -carrierHead s η a D z := by
  unfold carrierHead
  rw [carrierF_neg]
  have hden : carrierDen η a D (-z) (-carrierF s η a D z)
      = carrierDen η a D z (carrierF s η a D z) := by
    unfold carrierDen; ring
  rw [hden]
  set L := 4 * √(carrierDen η a D z (carrierF s η a D z))
  set F := carrierF s η a D z
  have e1 : (-F - -z + 1) / L = -((F - z - 1) / L) := by ring
  have e2 : (-F - -z - 1) / L = -((F - z + 1) / L) := by ring
  rw [e1, e2, Real.tanh_neg, Real.tanh_neg]
  ring

/-- The squared final denominator is at most `3 + r_D² ≤ 4 r_D²`: every coordinate is bounded
by `r_D`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem carrierDen_le {s η : ℝ} {a : ℕ → ℝ} (hs : 0 ≤ s) (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2)
    (ha : ∀ k, 0 ≤ a k) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (D : ℕ) :
    carrierDen η a D z (carrierF s η a D z) ≤ 4 * schedR a D ^ 2 := by
  obtain ⟨h1, h2⟩ := carrierF_bounds (η := η) hs ha hz0 D
  have hr := schedR_ge_one ha D
  have hc0 := cT_pos
  have hc1 := cT_lt_one
  unfold carrierDen
  set F := carrierF s η a D z
  set r := schedR a D
  have hF : 1 - z ^ 2 + F ^ 2 ≤ r ^ 2 := by
    have hF0 : 0 ≤ F := le_trans hz0 h1
    have : F ^ 2 ≤ (z + (r - 1)) ^ 2 := pow_le_pow_left₀ hF0 h2 2
    nlinarith
  have hC : (1 + cT * (r - 1)) ^ 2 ≤ r ^ 2 := by
    have h0 : 0 ≤ 1 + cT * (r - 1) := by nlinarith
    have : 1 + cT * (r - 1) ≤ r := by nlinarith
    exact pow_le_pow_left₀ h0 this 2
  have hr2 : 1 ≤ r ^ 2 := by nlinarith
  have e : 4 - η - η * z ^ 2 + η * F ^ 2 + η * (1 + cT * (r - 1)) ^ 2
      = 3 + (1 - 2 * η) + η * (1 - z ^ 2 + F ^ 2) + η * (1 + cT * (r - 1)) ^ 2 := by ring
  rw [e]
  have := mul_le_mul_of_nonneg_left hF hη0
  have := mul_le_mul_of_nonneg_left hC hη0
  have := mul_le_mul_of_nonneg_left hr2 (by linarith : (0 : ℝ) ≤ 1 - 2 * η)
  nlinarith

/-- **The head bound.** For `z ∈ [0,1]` and `1/4 ≤ η ≤ 1/2`,
`ḡ(z) ≥ F_D(z)/(4L(z)) ≥ u_D(z)/32`, with `L(z) ≤ 8 r_D`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem carrierHead_lower {s η : ℝ} {a : ℕ → ℝ} (hs : 0 ≤ s) (hη0 : 1 / 4 ≤ η) (hη1 : η ≤ 1 / 2)
    (ha : ∀ k, 0 ≤ a k) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (D : ℕ) :
    carrierF s η a D z / schedR a D / 32 ≤ carrierHead s η a D z := by
  obtain ⟨h1, _⟩ := carrierF_bounds (η := η) hs ha hz0 D
  set F := carrierF s η a D z with hFdef
  have hF0 : 0 ≤ F := le_trans hz0 h1
  have hz2 : z ^ 2 ≤ 1 := by nlinarith
  have hvlow := carrierDen_ge a D (F := F) (by linarith) hη1 hz2
  have hvlow' : 3 + F ^ 2 / 4 ≤ carrierDen η a D z F := by nlinarith [sq_nonneg F]
  have hv0 : 0 < carrierDen η a D z F := by nlinarith [sq_nonneg F]
  set L := 4 * √(carrierDen η a D z F) with hL
  have hL0 : 0 < L := by positivity
  have hro := (readout_le (h := F) (F := F) (by rw [abs_of_nonneg hF0]; linarith) hvlow').2
  rw [abs_of_nonneg hF0] at hro
  have h3 : (0 : ℝ) < √3 := by positivity
  have hs3 : 1 ≤ √3 := by
    have := sqrt_le_sqrt (show (1 : ℝ) ≤ 3 by norm_num); rwa [sqrt_one] at this
  have hFL : F + 2 ≤ L := by
    have : 4 * √(carrierDen η a D z F) / √3 ≤ L := by
      rw [div_le_iff₀ h3, hL]; nlinarith [sqrt_nonneg (carrierDen η a D z F)]
    linarith
  have hL1 : 1 ≤ L := by linarith
  have hshift := head_shift (z := z) (A := (F - z) / L) (k := 1 / L) hz0 hz1 (by positivity)
    (by rw [div_le_one hL0]; linarith) (div_nonneg (by linarith) hL0.le)
    (by rw [← add_div, div_le_one hL0]; linarith)
  have e1 : (F - z) / L + 1 / L = (F - z + 1) / L := by ring
  have e2 : (F - z) / L - 1 / L = (F - z - 1) / L := by ring
  rw [e1, e2] at hshift
  have hhead : F / (4 * L) ≤ carrierHead s η a D z := by
    unfold carrierHead
    rw [← hFdef, ← hL]
    have : (z * (1 / L) + (F - z) / L) / 4 = F / (4 * L) := by field_simp; ring
    linarith
  have hLle : L ≤ 8 * schedR a D := by
    have hv := carrierDen_le hs (by linarith) hη1 ha hz0 hz1 D
    rw [← hFdef] at hv
    have hr := schedR_pos ha D
    have : √(carrierDen η a D z F) ≤ 2 * schedR a D := by
      rw [sqrt_le_left (by positivity)]; nlinarith
    rw [hL]; linarith
  have hr := schedR_pos ha D
  calc F / schedR a D / 32 = F / (4 * (8 * schedR a D)) := by field_simp; ring
    _ ≤ F / (4 * L) := div_le_div_of_nonneg_left hF0 (by positivity) (by linarith)
    _ ≤ _ := hhead

/-- The explicit constant `c₁ = e^{-2E_*} M_*^{-2ν} / (4096 M_*² + 12288 C)`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
noncomputable def c1G (θ s : ℝ) : ℝ :=
  exp (-(2 * EstarG θ s)) * MstarG θ s ^ (-(2 * nuG θ s)) / (4096 * MstarG θ s ^ 2 + 12288 * CG θ s)

/-- The explicit constant `c₂ = 1/(1024 R_*^{2ν+2})`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
noncomputable def c2G (θ s : ℝ) : ℝ := 1 / (1024 * RstarG θ s ^ (2 * nuG θ s + 2))

/-- **The normalized-gain lower bound at comparison level `θ`.** Let `1/4 ≤ η ≤ 1/2` with
`η ≤ θ`, let `ν_θ = s/(c√θ) - 1 > 0`, and let the step schedule satisfy `0 ≤ a_j ≤ 1`. Let
`(p_i, M_i)` be the law of the feature mean `M` of `N` fair signs (`𝔼M² = 1/N`, `𝔼M⁴ ≤ 3/N²`,
`|M| ≤ 1`), with `n/4 < N`. Let `Q` be the expected number of fresh-query probes of an exact
sampler, and assume the transcript inequality of `lem:transcript` (tanh_lower.tex) in the form
`Q ≥ H'(0)²` with `H'(0) = N 𝔼[M ḡ(M)]`. Then `Q ≥ min{c₁, c₂} · min{r_D^{2ν_θ}, n}`, where
`r_D = 1 + τ_D` and `c₁, c₂` depend only on `θ` and `s`. At `θ = 1/2` this is
`thm:pn-normalized-gain` (`normalized_gain_lower_half`); at `θ = η` it gives the exponent
`2ν_η` of `thm:main-carrier` (`carrier_lower_eta`).
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex); proof of
`thm:pn-family-query-law` (normalization_family_query.tex), which retains `A₀ = ηc²` and
`A₁ = 4 + 2ηc(1-c)`. -/
theorem normalized_gain_lower {θ s η : ℝ} {a : ℕ → ℝ} {D : ℕ} (hθ : 0 < θ) (hηθ : η ≤ θ)
    (hs : 0 ≤ s) (hν : 0 < nuG θ s)
    (hη0 : 1 / 4 ≤ η) (hη1 : η ≤ 1 / 2) (ha : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1)
    {ι : Type*} (S : Finset ι) (p M : ι → ℝ) {N n Q : ℝ} (hN : 0 < N) (hn : 0 ≤ n)
    (hNn : n / 4 < N) (hp : ∀ i ∈ S, 0 ≤ p i) (h2 : ∑ i ∈ S, p i * M i ^ 2 = 1 / N)
    (h4 : ∑ i ∈ S, p i * M i ^ 4 ≤ 3 / N ^ 2) (hM : ∀ i ∈ S, |M i| ≤ 1)
    (hQ : (N * ∑ i ∈ S, p i * (M i * carrierHead s η a D (M i))) ^ 2 ≤ Q) :
    min (c1G θ s) (c2G θ s) * min (schedR a D ^ (2 * nuG θ s)) n ≤ Q := by
  have hR4 := (RstarG_ge θ s).1
  have hMs : 0 < MstarG θ s := by unfold MstarG; linarith
  have hC : 0 < CG θ s := by
    unfold CG; have := (A0_pos hθ)
    have : 0 < kap θ s := by unfold nuG at hν; linarith
    positivity
  -- oddness reduces the pointwise bound to `z ≥ 0`
  have hodd : ∀ x : ℝ, x * carrierHead s η a D x = |x| * carrierHead s η a D |x| := by
    intro x
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, carrierHead_neg]; ring
  have hrD := schedR_pos ha D
  have hmin0 : 0 ≤ min (schedR a D ^ (2 * nuG θ s)) n := le_min (by positivity) hn
  rcases le_or_gt (RstarG θ s) (schedR a D) with hbig | hsmall
  · -- the growth regime
    obtain ⟨j0, hj0D, hj0, hj0'⟩ := exists_first_index ha1 (by linarith) hbig
    obtain ⟨n0, hn0⟩ : ∃ n0, D = j0 + n0 := ⟨D - j0, by omega⟩
    set G := ∏ i ∈ range n0, (1 - a (j0 + i) / schedR a (j0 + i + 1)
        + a (j0 + i) / schedR a (j0 + i + 1) * tGain θ s (schedR a (j0 + i))) with hG
    have hG1 : 1 ≤ G := (carrier_comparison (η := η) (n := n0) hθ hηθ hs hν (by linarith) hη1 ha hj0
      hj0' (z := 1) one_pos le_rfl).1
    have hG0 : 0 < G := by linarith
    -- the pointwise score bound
    have hpt : ∀ i ∈ S, G / (32 * MstarG θ s) * (M i ^ 2 / √(1 + CG θ s * G ^ 2 / MstarG θ s ^ 2
        * M i ^ 2)) ≤ M i * carrierHead s η a D (M i) := by
      intro i hi
      rw [hodd]
      set x := |M i|
      have hx0 : 0 ≤ x := abs_nonneg _
      have hx1 : x ≤ 1 := hM i hi
      have hxsq : M i ^ 2 = x ^ 2 := (sq_abs _).symm
      rw [hxsq]
      rcases eq_or_lt_of_le hx0 with hx | hx
      · rw [← hx]; simp
      have hcomp := (carrier_comparison (η := η) (n := n0) hθ hηθ hs hν (by linarith) hη1 ha hj0
        hj0'
        hx hx1).2
      rw [← hG, ← hn0] at hcomp
      have hhead := carrierHead_lower (s := s) hs hη0 hη1 ha hx0 hx1 D
      have hS' : 0 < 1 + CG θ s * (G ^ 2 - 1) * (x / MstarG θ s) ^ 2 := by
        have : 0 ≤ CG θ s * (G ^ 2 - 1) := mul_nonneg hC.le (by nlinarith)
        positivity
      have hmono : G * (x / MstarG θ s) / √(1 + CG θ s * G ^ 2 / MstarG θ s ^ 2 * x ^ 2)
          ≤ G * (x / MstarG θ s) / √(1 + CG θ s * (G ^ 2 - 1) * (x / MstarG θ s) ^ 2) := by
        apply div_le_div_of_nonneg_left (by positivity) (sqrt_pos.2 hS')
        apply sqrt_le_sqrt
        have : CG θ s * (G ^ 2 - 1) * (x / MstarG θ s) ^ 2
            ≤ CG θ s * G ^ 2 / MstarG θ s ^ 2 * x ^ 2 := by
          rw [div_pow]
          have : CG θ s * (G ^ 2 - 1) ≤ CG θ s * G ^ 2 := by nlinarith
          have hx2 : 0 ≤ x ^ 2 / MstarG θ s ^ 2 := by positivity
          calc CG θ s * (G ^ 2 - 1) * (x ^ 2 / MstarG θ s ^ 2)
              ≤ CG θ s * G ^ 2 * (x ^ 2 / MstarG θ s ^ 2) := mul_le_mul_of_nonneg_right this hx2
            _ = CG θ s * G ^ 2 / MstarG θ s ^ 2 * x ^ 2 := by ring
        linarith
      have hfin : G / (32 * MstarG θ s) * (x ^ 2 / √(1 + CG θ s * G ^ 2 / MstarG θ s ^ 2 * x ^ 2))
          = x * (G * (x / MstarG θ s) / √(1 + CG θ s * G ^ 2 / MstarG θ s ^ 2 * x ^ 2) / 32) := by
        field_simp
      rw [hfin]
      apply mul_le_mul_of_nonneg_left _ hx0
      calc G * (x / MstarG θ s) / √(1 + CG θ s * G ^ 2 / MstarG θ s ^ 2 * x ^ 2) / 32
          ≤ carrierF s η a D x / schedR a D / 32 := by
            apply div_le_div_of_nonneg_right _ (by norm_num); linarith
        _ ≤ _ := hhead
    have hscore := score_lower S p M (carrierHead s η a D) hN (by positivity)
      (by positivity : 0 < CG θ s * G ^ 2 / MstarG θ s ^ 2) hp h2 h4 hpt
    have hq := query_min_bound (Q := Q) (K0 := 32 * MstarG θ s) (β' := CG θ s / MstarG θ s ^ 2)
      hG0 hN
      (by positivity) (by positivity) hQ (by
        have e : 3 * (CG θ s / MstarG θ s ^ 2) * G ^ 2 / N
            = 3 * (CG θ s * G ^ 2 / MstarG θ s ^ 2) / N :=
          by ring
        rw [e]
        exact hscore)
    -- the gain product
    have hGp := carrier_gain_product (n := n0) hθ hs hν ha ha1 hj0 hj0'
    rw [← hG, ← hn0] at hGp
    set X := schedR a D with hX
    set f := exp (-(2 * EstarG θ s)) * MstarG θ s ^ (-(2 * nuG θ s)) with hf
    have hE0 : 0 ≤ EstarG θ s := by
      unfold EstarG
      have : 0 ≤ KG θ s := by unfold KG kap; have := (A0_pos hθ); have := (A1_pos hθ.le); positivity
      apply div_nonneg _ (by linarith)
      nlinarith [sq_nonneg (nuG θ s)]
    have hf0 : 0 ≤ f := by positivity
    have hf1 : f ≤ 1 := by
      have h1 : exp (-(2 * EstarG θ s)) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
      have hM1 : 1 ≤ MstarG θ s := by unfold MstarG; linarith
      have h2' : MstarG θ s ^ (-(2 * nuG θ s)) ≤ 1 :=
        rpow_le_one_of_one_le_of_nonpos hM1 (by linarith)
      have h0 : 0 ≤ MstarG θ s ^ (-(2 * nuG θ s)) := rpow_nonneg hMs.le _
      calc f ≤ 1 * 1 := mul_le_mul h1 h2' h0 zero_le_one
        _ = 1 := by ring
    have hG2 : f * X ^ (2 * nuG θ s) ≤ G ^ 2 := by
      have hsq := pow_le_pow_left₀ (by positivity) hGp 2
      have hXM : 0 ≤ X / MstarG θ s := by positivity
      have e1 : ((X / MstarG θ s) ^ nuG θ s) ^ 2 = (X / MstarG θ s) ^ (2 * nuG θ s) := by
        rw [← rpow_natCast, ← rpow_mul hXM]; ring_nf
      have e2 : (X / MstarG θ s) ^ (2 * nuG θ s)
          = MstarG θ s ^ (-(2 * nuG θ s)) * X ^ (2 * nuG θ s) := by
        rw [div_rpow hrD.le hMs.le, rpow_neg hMs.le]; ring
      have e3 : exp (-EstarG θ s) ^ 2 = exp (-(2 * EstarG θ s)) := by
        rw [← exp_nat_mul]; ring_nf
      have e : (exp (-EstarG θ s) * (X / MstarG θ s) ^ nuG θ s) ^ 2 = f * X ^ (2 * nuG θ s) := by
        rw [mul_pow, e1, e2, e3, hf]; ring
      linarith
    have hmin1 : f * min (X ^ (2 * nuG θ s)) n ≤ min (G ^ 2) n := by
      apply le_min
      · exact le_trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hf0) hG2
      · calc f * min (X ^ (2 * nuG θ s)) n ≤ 1 * min (X ^ (2 * nuG θ s)) n :=
            mul_le_mul_of_nonneg_right hf1 hmin0
          _ ≤ n := by rw [one_mul]; exact min_le_right _ _
    have hmin2 := min_quarter (x := G ^ 2) (sq_nonneg G) hNn
    have hden : (32 * MstarG θ s) ^ 2 * (1 + 3 * (CG θ s / MstarG θ s ^ 2))
        = 4096 * MstarG θ s ^ 2 / 4 + 12288 * CG θ s / 4 := by field_simp; ring
    rw [hden] at hq
    have hc1 : c1G θ s * min (X ^ (2 * nuG θ s)) n ≤ Q := by
      unfold c1G
      rw [← hf]
      have hD0 : 0 < 4096 * MstarG θ s ^ 2 + 12288 * CG θ s := by positivity
      calc f / (4096 * MstarG θ s ^ 2 + 12288 * CG θ s) * min (X ^ (2 * nuG θ s)) n
          = (f * min (X ^ (2 * nuG θ s)) n / 4)
            / (4096 * MstarG θ s ^ 2 / 4 + 12288 * CG θ s / 4) := by field_simp
        _ ≤ min (G ^ 2) N / (4096 * MstarG θ s ^ 2 / 4 + 12288 * CG θ s / 4) := by
            apply div_le_div_of_nonneg_right _ (by positivity); linarith
        _ ≤ Q := hq
    calc min (c1G θ s) (c2G θ s) * min (X ^ (2 * nuG θ s)) n
        ≤ c1G θ s * min (X ^ (2 * nuG θ s)) n :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hmin0
      _ ≤ Q := hc1
  · -- the short regime `r_D < R_*`
    have hpt : ∀ i ∈ S, M i ^ 2 / (32 * RstarG θ s) ≤ M i * carrierHead s η a D (M i) := by
      intro i hi
      rw [hodd]
      set x := |M i|
      have hx0 : 0 ≤ x := abs_nonneg _
      have hx1 : x ≤ 1 := hM i hi
      have hxsq : M i ^ 2 = x ^ 2 := (sq_abs _).symm
      rw [hxsq]
      have hhead := carrierHead_lower (s := s) hs hη0 hη1 ha hx0 hx1 D
      have hF := (carrierF_bounds (η := η) hs ha hx0 D).1
      have : x / (32 * RstarG θ s) ≤ carrierHead s η a D x := by
        calc x / (32 * RstarG θ s) ≤ x / (32 * schedR a D) :=
              div_le_div_of_nonneg_left hx0 (by positivity) (by linarith)
          _ ≤ carrierF s η a D x / schedR a D / 32 := by
              rw [div_div, mul_comm (schedR a D) 32]
              exact div_le_div_of_nonneg_right hF (by positivity)
          _ ≤ _ := hhead
      calc x ^ 2 / (32 * RstarG θ s) = x * (x / (32 * RstarG θ s)) := by ring
        _ ≤ x * carrierHead s η a D x := mul_le_mul_of_nonneg_left this hx0
    have hsum : 1 / (32 * RstarG θ s) ≤ N * ∑ i ∈ S, p i * (M i * carrierHead s η a D (M i)) := by
      have h := sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hpt i hi) (hp i hi))
      have e : ∑ i ∈ S, p i * (M i ^ 2 / (32 * RstarG θ s)) = 1 / N / (32 * RstarG θ s) := by
        rw [← h2, sum_div]; apply sum_congr rfl; intro i _; ring
      rw [e] at h
      calc 1 / (32 * RstarG θ s) = N * (1 / N / (32 * RstarG θ s)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left h hN.le
    have hQ' : (1 / (32 * RstarG θ s)) ^ 2 ≤ Q :=
      le_trans (pow_le_pow_left₀ (by positivity) hsum 2) hQ
    have hpow : schedR a D ^ (2 * nuG θ s) ≤ RstarG θ s ^ (2 * nuG θ s) :=
      rpow_le_rpow hrD.le hsmall.le (by linarith)
    have hc2 : c2G θ s * min (schedR a D ^ (2 * nuG θ s)) n ≤ Q := by
      unfold c2G
      have hR0 : 0 < RstarG θ s := by linarith
      have e : RstarG θ s ^ (2 * nuG θ s + 2) = RstarG θ s ^ (2 * nuG θ s) * RstarG θ s ^ 2 := by
        rw [rpow_add hR0, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]
      rw [e]
      have hRp : 0 < RstarG θ s ^ (2 * nuG θ s) := rpow_pos_of_pos hR0 _
      calc 1 / (1024 * (RstarG θ s ^ (2 * nuG θ s) * RstarG θ s ^ 2))
            * min (schedR a D ^ (2 * nuG θ s)) n
          ≤ 1 / (1024 * (RstarG θ s ^ (2 * nuG θ s) * RstarG θ s ^ 2))
            * RstarG θ s ^ (2 * nuG θ s) :=
            mul_le_mul_of_nonneg_left (le_trans (min_le_left _ _) hpow) (by positivity)
        _ = (1 / (32 * RstarG θ s)) ^ 2 := by field_simp; ring
        _ ≤ Q := hQ'
    calc min (c1G θ s) (c2G θ s) * min (schedR a D ^ (2 * nuG θ s)) n
        ≤ c2G θ s * min (schedR a D ^ (2 * nuG θ s)) n :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hmin0
      _ ≤ Q := hc2

/-- **`thm:pn-normalized-gain`.** For `s > c/√2`, i.e. `ν = √2 s/c - 1 > 0` (`kap_half`), and
every carrier fraction `1/4 ≤ η ≤ 1/2`, `Q ≥ min{c₁, c₂} · min{r_D^{2ν}, n}` with constants
depending only on `s`, under the transcript hypothesis of `normalized_gain_lower`.
Paper: `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem normalized_gain_lower_half {s η : ℝ} {a : ℕ → ℝ} {D : ℕ} (hs : 0 ≤ s)
    (hν : 0 < nuG (1 / 2) s) (hη0 : 1 / 4 ≤ η) (hη1 : η ≤ 1 / 2) (ha : ∀ k, 0 ≤ a k)
    (ha1 : ∀ k, a k ≤ 1) {ι : Type*} (S : Finset ι) (p M : ι → ℝ) {N n Q : ℝ} (hN : 0 < N)
    (hn : 0 ≤ n) (hNn : n / 4 < N) (hp : ∀ i ∈ S, 0 ≤ p i)
    (h2 : ∑ i ∈ S, p i * M i ^ 2 = 1 / N) (h4 : ∑ i ∈ S, p i * M i ^ 4 ≤ 3 / N ^ 2)
    (hM : ∀ i ∈ S, |M i| ≤ 1)
    (hQ : (N * ∑ i ∈ S, p i * (M i * carrierHead s η a D (M i))) ^ 2 ≤ Q) :
    min (c1G (1 / 2) s) (c2G (1 / 2) s) * min (schedR a D ^ (2 * nuG (1 / 2) s)) n ≤ Q :=
  normalized_gain_lower (by norm_num) hη1 hs hν hη0 hη1 ha ha1 S p M hN hn hNn hp h2 h4 hM hQ

/-- **The lower half of `thm:main-carrier`.** For `s > c/√2` and `1/4 ≤ η ≤ 1/2`, the
exponent is `2ν_η` with `ν_η = s/(c√η) - 1` (`kap_eq`), and `ν_η ≥ √2 s/c - 1 > 0`
(`kap_half_le`): `Q ≥ min{c₁, c₂} · min{r_D^{2ν_η}, n}` under the transcript hypothesis of
`normalized_gain_lower`. Here the constants depend on `η` and `s`; the uniform choice over
`η ∈ [1/4, 1/2]` made in the paper is not formalized.
Paper: lower half of `thm:main-carrier` (main_normalization.tex); proof of
`thm:pn-family-query-law` (normalization_family_query.tex). -/
theorem carrier_lower_eta {s η : ℝ} {a : ℕ → ℝ} {D : ℕ} (hs : 0 ≤ s)
    (hν : 0 < nuG (1 / 2) s) (hη0 : 1 / 4 ≤ η) (hη1 : η ≤ 1 / 2) (ha : ∀ k, 0 ≤ a k)
    (ha1 : ∀ k, a k ≤ 1) {ι : Type*} (S : Finset ι) (p M : ι → ℝ) {N n Q : ℝ} (hN : 0 < N)
    (hn : 0 ≤ n) (hNn : n / 4 < N) (hp : ∀ i ∈ S, 0 ≤ p i)
    (h2 : ∑ i ∈ S, p i * M i ^ 2 = 1 / N) (h4 : ∑ i ∈ S, p i * M i ^ 4 ≤ 3 / N ^ 2)
    (hM : ∀ i ∈ S, |M i| ≤ 1)
    (hQ : (N * ∑ i ∈ S, p i * (M i * carrierHead s η a D (M i))) ^ 2 ≤ Q) :
    min (c1G η s) (c2G η s) * min (schedR a D ^ (2 * nuG η s)) n ≤ Q := by
  have hηpos : 0 < η := by linarith
  have hk := kap_half_le hηpos hη1 hs
  have hνη : 0 < nuG η s := by unfold nuG at hν ⊢; linarith
  exact normalized_gain_lower hηpos le_rfl hs hνη hη0 hη1 ha ha1 S p M hN hn hNn hp h2 h4 hM hQ

/-! ## Network bookkeeping for the carrier family -/

/-- The feature row with weight `s/N` on each normalized feature `x_i - M + F` returns
`sF/√v`, since the centered signs sum to zero.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex); proof of
`thm:pn-scaled-lower` (normalization_depth_lower.tex). -/
theorem feature_row {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (s F v : ℝ) :
    ∑ i, s / N * ((x i - (1 / (N : ℝ)) * ∑ k, x k + F) / √v) = s * F / √v := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  simp only [← mul_sum, ← sum_div, sum_add_distrib, sum_sub_distrib, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- For signs `x_i ∈ {±1}`, the mean square of the features `x_i - M + F` is `1 - M² + F²`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex); proof of
`thm:pn-scaled-lower` (normalization_depth_lower.tex). -/
theorem feature_mean_square {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (hx : ∀ i, x i ^ 2 = 1)
    (F : ℝ) : (1 / (N : ℝ)) * ∑ i, (x i - (1 / (N : ℝ)) * ∑ k, x k + F) ^ 2
      = 1 - ((1 / (N : ℝ)) * ∑ k, x k) ^ 2 + F ^ 2 := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  set M := (1 / (N : ℝ)) * ∑ k, x k with hM
  have hsum : ∑ k, x k = N * M := by rw [hM]; field_simp
  have e : ∀ i, (x i - M + F) ^ 2 = x i ^ 2 + 2 * (F - M) * x i + (F - M) ^ 2 := by
    intro i; ring
  simp only [e, hx, sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, hsum]
  field_simp
  ring

/-- The squared denominator of the carrier family as an average: `N` features of mean square
`1 - z² + F²`, `N` carriers of square `(1 + cτ)²`, and `n - 2N` inert signs, with stabilizer `3`
and `η = N/n`, give `4 - η - ηz² + ηF² + η(1 + cτ)²`.
Paper: proof of `thm:pn-normalized-gain` (normalization_gain.tex). -/
theorem carrier_denominator_average {N n z F C : ℝ} (hn : n ≠ 0) :
    3 + (N * (1 - z ^ 2 + F ^ 2) + N * C ^ 2 + (n - 2 * N) * 1) / n
      = 4 - N / n - N / n * z ^ 2 + N / n * F ^ 2 + N / n * C ^ 2 := by
  field_simp
  ring

/-! ## The padded families (`thm:pn-scaled-lower` and its corollaries, `thm:real-ffn-lower`) -/

/-- The squared denominator of the padded families: a fraction `η` of features of mean square
`1 - z² + F²` and a fraction `1 - η` of carriers `-(1 + t₀ τ_j)`, with stabilizer `3`.
Paper: `eq:pn-scaled-meanrec` (normalization_depth_lower.tex), `η = 1/2`;
`cor:pn-scaled-padding` (normalization_depth_lower.tex); `thm:real-ffn-lower`
(normalization_ffn.tex). -/
noncomputable def padDen (η t0 : ℝ) (a : ℕ → ℝ) (j : ℕ) (z F : ℝ) : ℝ :=
  3 + η * (1 - z ^ 2 + F ^ 2) + (1 - η) * (1 + t0 * (schedR a j - 1)) ^ 2

/-- The feature mean of the padded families with update activation `ψ`:
`F_{j+1} = F_j + a_j ψ(s F_j/√v_j)`; `ψ = tanh` for the tanh blocks and `ψ = id` for the
GELU/SwiGLU blocks after the antisymmetric identity.
Paper: `eq:pn-scaled-meanrec` (normalization_depth_lower.tex); proof of `thm:real-ffn-lower`
(normalization_ffn.tex). -/
noncomputable def padF (ψ : ℝ → ℝ) (s η t0 : ℝ) (a : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0, z => z
  | j + 1, z => padF ψ s η t0 a j z
      + a j * ψ (s * padF ψ s η t0 a j z / √(padDen η t0 a j z (padF ψ s η t0 a j z)))

/-- The padded denominator is at least `3 + ηF²` for `z² ≤ 1`.
Paper: proof of `thm:pn-scaled-lower` (normalization_depth_lower.tex). -/
theorem padDen_ge {η t0 : ℝ} (a : ℕ → ℝ) (j : ℕ) {z F : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hz : z ^ 2 ≤ 1) : 3 + η * F ^ 2 ≤ padDen η t0 a j z F := by
  unfold padDen
  have : 0 ≤ η * (1 - z ^ 2) := mul_nonneg hη0 (by linarith)
  have : 0 ≤ (1 - η) * (1 + t0 * (schedR a j - 1)) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  nlinarith

/-- The padded recurrence is odd in `z` when `ψ` is odd.
Paper: proof of `thm:pn-scaled-lower` (normalization_depth_lower.tex). -/
theorem padF_neg {ψ : ℝ → ℝ} (hψ : ∀ y, ψ (-y) = -ψ y) (s η t0 : ℝ) (a : ℕ → ℝ) (j : ℕ)
    (z : ℝ) : padF ψ s η t0 a j (-z) = -padF ψ s η t0 a j z := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [padF, ih, padDen, neg_sq]
    rw [show s * -padF ψ s η t0 a j z = -(s * padF ψ s η t0 a j z) by ring, neg_div, hψ]
    ring

/-- For `z ≥ 0`, `F_j(z) ≥ z` when `ψ ≥ 0` on `[0, ∞)`.
Paper: proof of `thm:pn-scaled-lower` (normalization_depth_lower.tex). -/
theorem padF_ge {ψ : ℝ → ℝ} (hψ0 : ∀ y, 0 ≤ y → 0 ≤ ψ y) {s η t0 : ℝ} {a : ℕ → ℝ}
    (hs : 0 ≤ s) (ha : ∀ k, 0 ≤ a k) {z : ℝ} (hz0 : 0 ≤ z) (j : ℕ) :
    z ≤ padF ψ s η t0 a j z := by
  induction j with
  | zero => simp [padF]
  | succ j ih =>
    simp only [padF]
    have hF : 0 ≤ padF ψ s η t0 a j z := le_trans hz0 ih
    have := mul_nonneg (ha j) (hψ0 (s * padF ψ s η t0 a j z
      / √(padDen η t0 a j z (padF ψ s η t0 a j z))) (div_nonneg (mul_nonneg hs hF) (sqrt_nonneg _)))
    linarith

/-- The normalized update of the padded families:
`u_{j+1} = (1 - q_j) u_j + q_j ψ(s u_j/√(b_j + η u_j²))`, with
`b_j = (3 + η(1 - z²) + (1-η)(1 + t₀τ_j)²)/r_j²`.
Paper: proof of `thm:pn-scaled-lower` (normalization_depth_lower.tex). -/
theorem pad_normalized_update {ψ : ℝ → ℝ} {s η t0 : ℝ} {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k)
    (j : ℕ) (z : ℝ) (hden : 0 < padDen η t0 a j z (padF ψ s η t0 a j z)) :
    padF ψ s η t0 a (j + 1) z / schedR a (j + 1)
      = (1 - a j / schedR a (j + 1)) * (padF ψ s η t0 a j z / schedR a j)
        + a j / schedR a (j + 1) * ψ (s * (padF ψ s η t0 a j z / schedR a j)
          / √((3 + η * (1 - z ^ 2) + (1 - η) * (1 + t0 * (schedR a j - 1)) ^ 2) / schedR a j ^ 2
              + η * (padF ψ s η t0 a j z / schedR a j) ^ 2)) := by
  have hr := schedR_pos ha j
  have hr1 := schedR_pos ha (j + 1)
  have hs1 : schedR a (j + 1) = schedR a j + a j := schedR_succ a j
  set F := padF ψ s η t0 a j z
  have harg : s * (F / schedR a j) / √((3 + η * (1 - z ^ 2) + (1 - η) * (1 + t0 * (schedR a j - 1))
      ^ 2) / schedR a j ^ 2 + η * (F / schedR a j) ^ 2) = s * F / √(padDen η t0 a j z F) := by
    have e : (3 + η * (1 - z ^ 2) + (1 - η) * (1 + t0 * (schedR a j - 1)) ^ 2) / schedR a j ^ 2
        + η * (F / schedR a j) ^ 2 = padDen η t0 a j z F / schedR a j ^ 2 := by
      unfold padDen; field_simp; ring
    rw [e, sqrt_div hden.le, sqrt_sq hr.le]
    field_simp
  rw [harg]
  rw [show padF ψ s η t0 a (j + 1) z = F + a j * ψ (s * F / √(padDen η t0 a j z F)) from rfl]
  rw [hs1]
  have hne : schedR a j + a j ≠ 0 := by rw [← hs1]; exact hr1.ne'
  field_simp
  ring

/-- The nonsignal part of the padded denominator: `0 < b_j ≤ (3 + η)/r_j² + (1 - η)`, hence
`b_j ≤ 1` once `3 + η ≤ η r_j²`; for `η = 1/2` this needs `r_j ≥ 3` and gives `b_j ≤ 8/9`,
and for `η ≥ 1/4` it needs `r_j ≥ 4` and gives `b_j ≤ 31/32`.
Paper: proofs of `thm:pn-scaled-lower` and `cor:pn-scaled-padding`
(normalization_depth_lower.tex); proof of `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem pad_b_bounds {η t0 z r : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ht0 : 0 ≤ t0) (ht1 : t0 ≤ 1)
    (hz : z ^ 2 ≤ 1) (hr : 1 ≤ r) :
    0 < (3 + η * (1 - z ^ 2) + (1 - η) * (1 + t0 * (r - 1)) ^ 2) / r ^ 2 ∧
      (3 + η * (1 - z ^ 2) + (1 - η) * (1 + t0 * (r - 1)) ^ 2) / r ^ 2
        ≤ (3 + η) / r ^ 2 + (1 - η) := by
  have hr0 : 0 < r := by linarith
  have hC0 : 0 ≤ 1 + t0 * (r - 1) := by nlinarith
  have hC : 1 + t0 * (r - 1) ≤ r := by nlinarith
  have hC2 : (1 + t0 * (r - 1)) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hC0 hC 2
  constructor
  · apply div_pos _ (by positivity)
    have : 0 ≤ η * (1 - z ^ 2) := mul_nonneg hη0 (by linarith)
    have : 0 ≤ (1 - η) * (1 + t0 * (r - 1)) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  · rw [div_add' _ _ _ (by positivity), div_le_div_iff_of_pos_right (by positivity)]
    have : η * (1 - z ^ 2) ≤ η := by nlinarith
    have := mul_le_mul_of_nonneg_left hC2 (by linarith : (0 : ℝ) ≤ 1 - η)
    nlinarith

/-- The activation step of the padded families. If `ψ(y) ≥ y/√(1 + κ_ψ y²)` for `y ≥ 0`
(`κ_ψ = 1` for `tanh`, `κ_ψ = 0` for the identity), then for `u ≥ 0`, `0 < b ≤ 1` and
`0 ≤ η ≤ 1/2`, `ψ(s u/√(b + ηu²)) ≥ s u/√(1 + (κ_ψ s² + 1/2) u²)`.
Paper: proofs of `thm:pn-scaled-lower` (normalization_depth_lower.tex) and `thm:real-ffn-lower`
(normalization_ffn.tex). -/
theorem pad_activation_step {ψ : ℝ → ℝ} {kψ s η b u : ℝ} (hkψ : 0 ≤ kψ)
    (hψ : ∀ y, 0 ≤ y → y / √(1 + kψ * y ^ 2) ≤ ψ y) (hs : 0 ≤ s) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / 2) (hb0 : 0 < b) (hb1 : b ≤ 1) (hu : 0 ≤ u) :
    s * u / √(1 + (kψ * s ^ 2 + 1 / 2) * u ^ 2) ≤ ψ (s * u / √(b + η * u ^ 2)) := by
  have hD : 0 < b + η * u ^ 2 := by positivity
  set y := s * u / √(b + η * u ^ 2)
  have hy : 0 ≤ y := by positivity
  have h1 := hψ y hy
  have hform : y / √(1 + kψ * y ^ 2) = s * u / √(b + η * u ^ 2 + kψ * s ^ 2 * u ^ 2) := by
    have hsD : 0 < √(b + η * u ^ 2) := sqrt_pos.2 hD
    have e : 1 + kψ * y ^ 2 = (b + η * u ^ 2 + kψ * s ^ 2 * u ^ 2) / (b + η * u ^ 2) := by
      simp only [y]; rw [div_pow, mul_pow, sq_sqrt hD.le]; field_simp
    rw [e, sqrt_div (by positivity)]
    have : 0 < √(b + η * u ^ 2 + kψ * s ^ 2 * u ^ 2) := sqrt_pos.2 (by positivity)
    simp only [y]
    field_simp
  rw [hform] at h1
  refine le_trans ?_ h1
  apply div_le_div_of_nonneg_left (by positivity) (sqrt_pos.2 (by positivity))
  apply sqrt_le_sqrt
  nlinarith [sq_nonneg u, mul_nonneg hkψ (mul_nonneg (sq_nonneg s) (sq_nonneg u))]

/-- One chain step of the padded families past the burn-in: with `q = a_j/r_{j+1}`,
`g = 1 + δq` (`δ = s - 1`) and `d = qsB/g`, `B = κ_ψ s² + 1/2`, `u_{j+1} ≥ g u_j/√(1 + d u_j²)`.
Paper: proofs of `thm:pn-scaled-lower` (normalization_depth_lower.tex) and `thm:real-ffn-lower`
(normalization_ffn.tex). -/
theorem pad_step {ψ : ℝ → ℝ} {kψ s η t0 : ℝ} (hkψ : 0 ≤ kψ)
    (hψ : ∀ y, 0 ≤ y → y / √(1 + kψ * y ^ 2) ≤ ψ y) (hψ0 : ∀ y, 0 ≤ y → 0 ≤ ψ y) (hs : 1 ≤ s)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2) (ht0 : 0 ≤ t0) (ht1 : t0 ≤ 1) {a : ℕ → ℝ}
    (ha : ∀ k, 0 ≤ a k) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (j : ℕ)
    (hrj : 3 + η ≤ η * schedR a j ^ 2) :
    (1 + (s - 1) * (a j / schedR a (j + 1))) * (padF ψ s η t0 a j z / schedR a j)
        / √(1 + (a j / schedR a (j + 1) * s * (kψ * s ^ 2 + 1 / 2)
            / (1 + (s - 1) * (a j / schedR a (j + 1)))) * (padF ψ s η t0 a j z / schedR a j) ^ 2)
      ≤ padF ψ s η t0 a (j + 1) z / schedR a (j + 1) := by
  have hr := schedR_pos ha j
  have hr1' := schedR_ge_one ha j
  have hr1 := schedR_pos ha (j + 1)
  have hz2 : z ^ 2 ≤ 1 := by nlinarith
  set q := a j / schedR a (j + 1) with hq
  have hq0 : 0 ≤ q := div_nonneg (ha j) hr1.le
  have hq1 : q ≤ 1 := by rw [hq, div_le_one hr1, schedR_succ]; linarith
  have hF := padF_ge (s := s) (η := η) (t0 := t0) hψ0 (by linarith) ha hz0 j
  set u := padF ψ s η t0 a j z / schedR a j with hu
  have hu0 : 0 ≤ u := div_nonneg (le_trans hz0 hF) hr.le
  obtain ⟨hb0, hb1⟩ := pad_b_bounds (z := z) hη0 (by linarith) ht0 ht1 hz2 hr1'
  set b := (3 + η * (1 - z ^ 2) + (1 - η) * (1 + t0 * (schedR a j - 1)) ^ 2) / schedR a j ^ 2
    with hb
  have hb1' : b ≤ 1 := by
    have : (3 + η) / schedR a j ^ 2 ≤ η := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hden : 0 < padDen η t0 a j z (padF ψ s η t0 a j z) := by
    have := padDen_ge (t0 := t0) a j (F := padF ψ s η t0 a j z) hη0 (by linarith) hz2
    nlinarith [sq_nonneg (padF ψ s η t0 a j z)]
  have hupd := pad_normalized_update (ψ := ψ) (s := s) ha j z hden
  rw [← hu, ← hq, ← hb] at hupd
  rw [hupd]
  have hact := pad_activation_step (s := s) hkψ hψ (by linarith) hη0 hη1 hb0 hb1' hu0
  have hB : 0 ≤ kψ * s ^ 2 + 1 / 2 := by positivity
  have hg : 0 < 1 - q + q * s := by nlinarith
  have hconv := step_convex (t := s) hq0 hq1 (by linarith) hB hu0 hg
  have e1 : 1 - q + q * s = 1 + (s - 1) * q := by ring
  rw [e1] at hconv
  have e2 : q * s * (kψ * s ^ 2 + 1 / 2) / (1 + (s - 1) * q) * u ^ 2
      = q * s * (kψ * s ^ 2 + 1 / 2) / (1 + (s - 1) * q) * u ^ 2 := rfl
  calc _ ≤ (1 - q) * u + q * (s * u / √(1 + (kψ * s ^ 2 + 1 / 2) * u ^ 2)) := hconv
    _ ≤ (1 - q) * u + q * ψ (s * u / √(b + η * u ^ 2)) := by
        have := mul_le_mul_of_nonneg_left hact hq0
        linarith

/-- **The padded comparison** (`eq:pn-scaled-comparison`, and its analogues in
`cor:pn-scaled-padding`, `cor:pn-scheduled-lower` and `thm:real-ffn-lower`). Suppose
`3 + η ≤ η r_{j₀}²` (so `b_j ≤ 1` for `j ≥ j₀`) and `r_{j₀} ≤ ρ`.
Put `G = ∏_{i<n} (1 + δ q_{j₀+i})`,
`δ = s - 1 > 0`, and `C = s(κ_ψ s² + 1/2)/(2δ)`. For `0 < z ≤ 1`,
`u_{j₀+n}(z) ≥ G(z/ρ)/√(1 + C(G² - 1)(z/ρ)²)`, and `G ≥ 1`.
Paper: `eq:pn-scaled-comparison` (normalization_depth_lower.tex); proof of
`thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem pad_comparison {ψ : ℝ → ℝ} {kψ s η t0 : ℝ} (hkψ : 0 ≤ kψ)
    (hψ : ∀ y, 0 ≤ y → y / √(1 + kψ * y ^ 2) ≤ ψ y) (hψ0 : ∀ y, 0 ≤ y → 0 ≤ ψ y) (hs : 1 < s)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2) (ht0 : 0 ≤ t0) (ht1 : t0 ≤ 1) {a : ℕ → ℝ}
    (ha : ∀ k, 0 ≤ a k) {j0 n : ℕ} (hr : 3 + η ≤ η * schedR a j0 ^ 2) {ρ : ℝ}
    (hρ : schedR a j0 ≤ ρ) {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) :
    1 ≤ ∏ i ∈ range n, (1 + (s - 1) * (a (j0 + i) / schedR a (j0 + i + 1))) ∧
    (∏ i ∈ range n, (1 + (s - 1) * (a (j0 + i) / schedR a (j0 + i + 1)))) * (z / ρ)
        / √(1 + s * (kψ * s ^ 2 + 1 / 2) / (2 * (s - 1))
          * ((∏ i ∈ range n, (1 + (s - 1) * (a (j0 + i) / schedR a (j0 + i + 1)))) ^ 2 - 1)
          * (z / ρ) ^ 2)
      ≤ padF ψ s η t0 a (j0 + n) z / schedR a (j0 + n) := by
  set q := fun i => a (j0 + i) / schedR a (j0 + i + 1)
  set g := fun i => 1 + (s - 1) * q i
  set C := s * (kψ * s ^ 2 + 1 / 2) / (2 * (s - 1))
  set d := fun i => q i * s * (kψ * s ^ 2 + 1 / 2) / g i
  set u := fun i => padF ψ s η t0 a (j0 + i) z / schedR a (j0 + i)
  have hq0 : ∀ i, 0 ≤ q i := fun i => div_nonneg (ha _) (schedR_pos ha _).le
  have hg1 : ∀ i, 1 ≤ g i := fun i => by
    have := hq0 i; simp only [g]; nlinarith
  have hB : 0 ≤ kψ * s ^ 2 + 1 / 2 := by positivity
  have hd0 : ∀ i, 0 ≤ d i := fun i => by
    have := hg1 i; have := hq0 i; simp only [d]; positivity
  have hdC : ∀ i, d i ≤ C * (g i ^ 2 - 1) := by
    intro i
    have hg := hg1 i
    have hqi := hq0 i
    have h1 : d i ≤ q i * s * (kψ * s ^ 2 + 1 / 2) := by
      simp only [d]
      rw [div_le_iff₀ (by linarith)]
      have : 0 ≤ q i * s * (kψ * s ^ 2 + 1 / 2) := by positivity
      nlinarith
    have h2 : 2 * (s - 1) * q i ≤ g i ^ 2 - 1 := by
      simp only [g]; nlinarith [mul_nonneg (mul_nonneg hqi hqi) (sq_nonneg (s - 1))]
    have hC : C * (2 * (s - 1) * q i) = q i * s * (kψ * s ^ 2 + 1 / 2) := by
      have hs1 : s - 1 ≠ 0 := by linarith
      simp only [C]; field_simp
    have hC0 : 0 ≤ C := by simp only [C]; apply div_nonneg (by positivity); linarith
    have := mul_le_mul_of_nonneg_left h2 hC0
    linarith
  have hrj : ∀ i, 3 + η ≤ η * schedR a (j0 + i) ^ 2 := by
    intro i
    have h1 := schedR_mono ha (show j0 ≤ j0 + i by omega)
    have h0 := schedR_pos ha j0
    have : schedR a j0 ^ 2 ≤ schedR a (j0 + i) ^ 2 := pow_le_pow_left₀ h0.le h1 2
    nlinarith
  have hF0 := padF_ge (s := s) (η := η) (t0 := t0) hψ0 (by linarith) ha hz0.le j0
  have hu0 : 0 < u 0 := by
    simp only [u, add_zero]; exact div_pos (lt_of_lt_of_le hz0 hF0) (schedR_pos ha j0)
  have hstep : ∀ i < n, g i * u i / √(1 + d i * u i ^ 2) ≤ u (i + 1) := by
    intro i _
    exact pad_step hkψ hψ hψ0 hs.le hη0 hη1 ht0 ht1 ha hz0.le hz1 (j0 + i) (hrj i)
  have hchain := reciprocal_chain (u := u) (g := g) (d := d) (C := C) (n := n) hu0
    (fun i _ => by linarith [hg1 i]) (fun i _ => hd0 i) (fun i _ => hdC i) hstep n le_rfl
  have hG1 : 1 ≤ ∏ i ∈ range n, g i := one_le_prod₀ (fun i _ => hg1 i)
  refine ⟨hG1, ?_⟩
  have hρ0 : 0 < ρ := lt_of_lt_of_le (schedR_pos ha j0) hρ
  have hv : z / ρ ≤ u 0 := by
    simp only [u, add_zero]
    calc z / ρ ≤ padF ψ s η t0 a j0 z / ρ := div_le_div_of_nonneg_right hF0 hρ0.le
      _ ≤ padF ψ s η t0 a j0 z / schedR a j0 :=
          div_le_div_of_nonneg_left (le_trans hz0.le hF0) (schedR_pos ha j0) hρ
  have hC0 : 0 ≤ C := by simp only [C]; apply div_nonneg (by positivity); linarith
  have hCG : 0 ≤ C * ((∏ i ∈ range n, g i) ^ 2 - 1) := mul_nonneg hC0 (by nlinarith)
  exact invert_comparison hchain.1 (div_pos hz0 hρ0) hv (by linarith) hCG hchain.2

/-! ## The padded families: gain products -/

/-- A generic product bound: `∏ (1 + δq_i) ≥ exp(δ∑q_i - δ²∑q_i²/2)`.
Paper: proofs of `thm:pn-scaled-lower`, `cor:pn-scaled-padding`, `cor:pn-scheduled-lower`
(normalization_depth_lower.tex), `log(1+x) ≥ x - x²/2`. -/
theorem pad_gain_exp {δ : ℝ} (hδ : 0 ≤ δ) (q : ℕ → ℝ) (hq : ∀ i, 0 ≤ q i) (n : ℕ) :
    exp (δ * ∑ i ∈ range n, q i - δ ^ 2 * ∑ i ∈ range n, q i ^ 2 / 2)
      ≤ ∏ i ∈ range n, (1 + δ * q i) := by
  have h := prod_one_add_ge (range n) (fun i => δ * q i) (fun i _ => mul_nonneg hδ (hq i))
  refine le_trans (le_of_eq ?_) h
  congr 1
  rw [mul_sum, mul_sum]
  congr 1
  apply sum_congr rfl; intro i _; ring

/-- For a constant step `α`, `∑_{i<n} α/(1 + α(j₀+i+1)) ≥ log((1 + α(j₀+n+1))/(1 + α(j₀+1)))`,
by monotonicity of `x ↦ 1/(1+x)`.
Paper: proof of `thm:pn-scaled-lower` (normalization_depth_lower.tex). -/
theorem uniform_step_log {α : ℝ} (hα : 0 ≤ α) (j0 n : ℕ) :
    log ((1 + α * (j0 + n + 1)) / (1 + α * (j0 + 1)))
      ≤ ∑ i ∈ range n, α / (1 + α * (j0 + i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have h1 : 0 < 1 + α * (j0 + 1 : ℝ) := by positivity
    have h2 : 0 < 1 + α * (j0 + n + 1 : ℝ) := by positivity
    have h3 : 0 < 1 + α * ((j0 : ℝ) + (n + 1 : ℕ) + 1) := by positivity
    have hsplit : log ((1 + α * ((j0 : ℝ) + (n + 1 : ℕ) + 1)) / (1 + α * (j0 + 1)))
        = log ((1 + α * (j0 + n + 1)) / (1 + α * (j0 + 1)))
          + log ((1 + α * ((j0 : ℝ) + (n + 1 : ℕ) + 1)) / (1 + α * (j0 + n + 1))) := by
      rw [← log_mul (by positivity) (by positivity)]; congr 1; field_simp
    rw [hsplit]
    have hstep : log ((1 + α * ((j0 : ℝ) + (n + 1 : ℕ) + 1)) / (1 + α * (j0 + n + 1)))
        ≤ α / (1 + α * (j0 + n + 1)) := by
      have := log_le_sub_one_of_pos (div_pos h3 h2)
      have e : (1 + α * ((j0 : ℝ) + (n + 1 : ℕ) + 1)) / (1 + α * (j0 + n + 1)) - 1
          = α / (1 + α * (j0 + n + 1)) := by push_cast; field_simp; ring
      linarith
    push_cast at ih hstep ⊢
    linarith

/-- The constant-step radii `r_j = 1 + αj`. -/
theorem schedR_const (α : ℝ) (j : ℕ) : schedR (fun _ => α) j = 1 + α * j := by
  simp [schedR, sum_const, card_range]; ring

/-- The gain product for a constant step: if `R₀ ≤ r_{j₀}` and `r_{j₀+1} ≤ ρ₁`, then
`G ≥ e^{-δ²/(2R₀)} ((1 + αD)/ρ₁)^δ` with `D = j₀ + n`. With `R₀ = 3`, `ρ₁ = 5` this is
`e^{-δ²/6}((1+αD)/5)^δ`; with `R₀ = 4`, `ρ₁ = 6` it is `e^{-δ²/8}((1+αD)/6)^δ`.
Paper: proofs of `thm:pn-scaled-lower` and `cor:pn-scaled-padding`
(normalization_depth_lower.tex); proof of `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem uniform_gain_bound {α δ R0 ρ1 : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hδ : 0 ≤ δ)
    (hR0 : 0 < R0) {j0 n : ℕ} (hj0 : R0 ≤ 1 + α * j0) (hj1 : 1 + α * (j0 + 1) ≤ ρ1) :
    exp (-(δ ^ 2 / (2 * R0))) * ((1 + α * (j0 + n)) / ρ1) ^ δ
      ≤ ∏ i ∈ range n, (1 + δ * (α / schedR (fun _ => α) (j0 + i + 1))) := by
  set q := fun i : ℕ => α / schedR (fun _ => α) (j0 + i + 1)
  have hq0 : ∀ i, 0 ≤ q i := fun i => div_nonneg hα0.le (schedR_pos (fun _ => hα0.le) _).le
  refine le_trans ?_ (pad_gain_exp hδ q hq0 n)
  have hq : ∀ i, q i = α / (1 + α * (j0 + i + 1)) := by
    intro i; simp only [q]; rw [schedR_const]; push_cast; ring
  have hlin : log ((1 + α * (j0 + n)) / ρ1) ≤ ∑ i ∈ range n, q i := by
    simp only [hq]
    refine le_trans ?_ (uniform_step_log hα0.le j0 n)
    have hj0n : (0 : ℝ) ≤ j0 := Nat.cast_nonneg j0
    have h1 : 0 < 1 + α * (j0 + n : ℝ) := by positivity
    have hd : 0 < 1 + α * ((j0 : ℝ) + 1) := by positivity
    have hρ1 : 0 < ρ1 := lt_of_lt_of_le hd hj1
    apply log_le_log (div_pos h1 hρ1)
    exact div_le_div₀ (by positivity) (by nlinarith) hd hj1
  have hquad : ∑ i ∈ range n, q i ^ 2 ≤ 1 / R0 := by
    obtain ⟨S1, _, _⟩ := schedule_sums (a := fun _ => α) (fun _ => hα0.le) (fun _ => hα1) j0 n
    have hr := schedR_pos (fun _ => hα0.le) (j0 + n)
    have hr0 : R0 ≤ schedR (fun _ => α) j0 := by rw [schedR_const]; exact hj0
    have : 1 / schedR (fun _ => α) j0 ≤ 1 / R0 := one_div_le_one_div_of_le hR0 hr0
    have : 0 < 1 / schedR (fun _ => α) (j0 + n) := by positivity
    simp only [q] at S1 ⊢
    linarith
  have hd : 0 < 1 + α * ((j0 : ℝ) + 1) := by positivity
  have hX : 0 < (1 + α * (j0 + n)) / ρ1 := div_pos (by positivity) (lt_of_lt_of_le hd hj1)
  rw [rpow_def_of_pos hX, ← exp_add]
  apply exp_le_exp.2
  rw [← sum_div]
  have h1 := mul_le_mul_of_nonneg_left hlin hδ
  have h2 : δ ^ 2 * (∑ i ∈ range n, q i ^ 2) / 2 ≤ δ ^ 2 / (2 * R0) := by
    have := mul_le_mul_of_nonneg_left hquad (sq_nonneg δ)
    have e : δ ^ 2 / (2 * R0) = δ ^ 2 * (1 / R0) / 2 := by field_simp
    rw [e]; linarith
  nlinarith

/-- The gain product for a prescribed schedule: if `4 ≤ r_{j₀} ≤ 5` then
`G ≥ e^{-δ/4 - δ²/8} (r_D/5)^δ`, `D = j₀ + n`.
Paper: proof of `cor:pn-scheduled-lower` (normalization_depth_lower.tex); proof of
`cor:real-ffn-scheduled` (normalization_ffn.tex). -/
theorem scheduled_gain_bound {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1) {δ : ℝ}
    (hδ : 0 ≤ δ) {j0 n : ℕ} (hj0 : 4 ≤ schedR a j0) (hj0' : schedR a j0 ≤ 5) :
    exp (-(δ / 4) - δ ^ 2 / 8) * (schedR a (j0 + n) / 5) ^ δ
      ≤ ∏ i ∈ range n, (1 + δ * (a (j0 + i) / schedR a (j0 + i + 1))) := by
  set q := fun i => a (j0 + i) / schedR a (j0 + i + 1)
  have hq0 : ∀ i, 0 ≤ q i := fun i => div_nonneg (ha _) (schedR_pos ha _).le
  refine le_trans ?_ (pad_gain_exp hδ q hq0 n)
  obtain ⟨S1, _, S3⟩ := schedule_sums ha ha1 j0 n
  have hr0 := schedR_pos ha j0
  have hrD := schedR_pos ha (j0 + n)
  have hgap : 1 / schedR a j0 - 1 / schedR a (j0 + n) ≤ 1 / 4 := by
    have : 1 / schedR a j0 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hj0
    have : 0 < 1 / schedR a (j0 + n) := by positivity
    linarith
  have hlog : log (schedR a (j0 + n) / 5) ≤ log (schedR a (j0 + n) / schedR a j0) := by
    apply log_le_log (by positivity)
    exact div_le_div_of_nonneg_left hrD.le hr0 hj0'
  have hlin : log (schedR a (j0 + n) / 5) - 1 / 4 ≤ ∑ i ∈ range n, q i := by
    simp only [q]; linarith
  have hquad : ∑ i ∈ range n, q i ^ 2 ≤ 1 / 4 := by simp only [q]; linarith
  have hX : 0 < schedR a (j0 + n) / 5 := by positivity
  rw [rpow_def_of_pos hX, ← exp_add]
  apply exp_le_exp.2
  rw [← sum_div]
  have h1 := mul_le_mul_of_nonneg_left hlin hδ
  have h2 := mul_le_mul_of_nonneg_left hquad (sq_nonneg δ)
  nlinarith

/-! ## The padded families: floors and heads -/

/-- The full-cube floor of the padded families, `12(3 + (τ/2 - 1)²/2) - (1+τ)² =
(τ - 8)²/2 + 9`.
Paper: proof of `thm:pn-scaled-lower` (normalization_depth_lower.tex). -/
theorem carrier_floor_identity_half (tau : ℝ) :
    12 * (3 + (tau / 2 - 1) ^ 2 / 2) - (1 + tau) ^ 2 = (tau - 8) ^ 2 / 2 + 9 := by
  ring

/-- **The full-cube floor `v_j ≥ (1+τ)²/12`.** Let `t₀ > 1/2`, `τ ≥ 0`, and let a carrier
fraction at least `1/2` take values `e - τt₀` with `e = ±1`, so that
`v ≥ 3 + w²/2` for a carrier value `w = e - τ t₀`. Then `v ≥ (1+τ)²/12`.
Paper: proof of `thm:pn-scaled-lower`, `cor:pn-scaled-padding`, `cor:pn-scheduled-lower`
(normalization_depth_lower.tex); proof of `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem padded_full_floor {v e τ t0 : ℝ} (he : e = 1 ∨ e = -1) (hτ : 0 ≤ τ) (ht0 : 1 / 2 < t0)
    (hv : 3 + (e - τ * t0) ^ 2 / 2 ≤ v) : (1 + τ) ^ 2 / 12 ≤ v := by
  rcases le_total τ 2 with h | h
  · have : (1 + τ) ^ 2 ≤ 9 := by nlinarith
    nlinarith [sq_nonneg (e - τ * t0)]
  · have hw : τ / 2 - 1 ≤ |e - τ * t0| := by
      rcases he with rfl | rfl
      · rw [abs_sub_comm, abs_of_nonneg (by nlinarith)]; nlinarith
      · rw [abs_of_nonpos (by nlinarith)]; nlinarith
    have hw2 : (τ / 2 - 1) ^ 2 ≤ (e - τ * t0) ^ 2 := by
      rw [← sq_abs (e - τ * t0)]; exact pow_le_pow_left₀ (by linarith) hw 2
    have := carrier_floor_identity_half τ
    nlinarith [sq_nonneg (τ - 8)]

/-- On the lower-bound subdomain of `thm:pn-scaled-lower` the carriers `C_j = -(1 + αjt₀)`
satisfy `|C_j| ≥ R_j/2` (`t₀ > 1/2`), so the squared denominator is at least `R_j²/8`.
Paper: proof of `thm:pn-scaled-lower` (normalization_depth_lower.tex). -/
theorem carrier_amplitude (j t : ℝ) (hj : 0 ≤ j) (ht0 : (1 : ℝ) / 2 ≤ t) (ht1 : t ≤ 1) :
    (j + 1) / 2 ≤ 1 + j * t ∧ 1 + j * t ≤ j + 1 := by
  constructor <;> nlinarith

/-- `|C_j| ≥ R_j/2` gives `C_j²/2 ≥ R_j²/8`: the squared denominator is at least `R_j²/8` on the
lower-bound subdomain.
Paper: proof of `thm:pn-scaled-lower` (normalization_depth_lower.tex). -/
theorem carrier_energy (R C : ℝ) (hR : 0 ≤ R) (hC : R / 2 ≤ C) : R ^ 2 / 8 ≤ C ^ 2 / 2 := by
  have hCp : 0 ≤ C := by linarith
  have hmul := mul_self_le_mul_self (by linarith : 0 ≤ R / 2) hC
  nlinarith

/-- The tanh padded family moves by at most the step: `F_j(z) ≤ z + τ_j`.
Paper: proof of `thm:pn-scaled-lower` (normalization_depth_lower.tex). -/
theorem padF_tanh_le {s η t0 : ℝ} {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (z : ℝ) (j : ℕ) :
    padF tanh s η t0 a j z ≤ z + (schedR a j - 1) := by
  induction j with
  | zero => simp [padF, schedR_zero]
  | succ j ih =>
    simp only [padF]; rw [schedR_succ]
    have := mul_le_mul_of_nonneg_left (tanh_le_one (s * padF tanh s η t0 a j z
      / √(padDen η t0 a j z (padF tanh s η t0 a j z)))) (ha j)
    linarith

/-- The linear (GELU/SwiGLU) padded family moves by at most `2s` per unit step when
`η ≥ 1/4`: `F_j(z) ≤ z + 2sτ_j`, because the feature mean is at most `√(v/η)`.
Paper: proof of `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem padF_id_le {s η t0 : ℝ} {a : ℕ → ℝ} (hs : 0 ≤ s) (hη0 : 1 / 4 ≤ η) (hη1 : η ≤ 1)
    (ha : ∀ k, 0 ≤ a k) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (j : ℕ) :
    padF id s η t0 a j z ≤ z + 2 * s * (schedR a j - 1) := by
  induction j with
  | zero => simp [padF, schedR_zero]
  | succ j ih =>
    simp only [padF, id]; rw [schedR_succ]
    have hF : 0 ≤ padF id s η t0 a j z := le_trans hz0 (padF_ge (fun y hy => hy) hs ha hz0 j)
    have hz2 : z ^ 2 ≤ 1 := by nlinarith
    have hv := padDen_ge (t0 := t0) a j (F := padF id s η t0 a j z) (by linarith) hη1 hz2
    have hv0 : 0 < padDen η t0 a j z (padF id s η t0 a j z) := by
      nlinarith [sq_nonneg (padF id s η t0 a j z)]
    have hupd : s * padF id s η t0 a j z / √(padDen η t0 a j z (padF id s η t0 a j z))
        ≤ 2 * s := by
      rw [div_le_iff₀ (sqrt_pos.2 hv0)]
      have h4 : padF id s η t0 a j z ≤ √(4 * padDen η t0 a j z (padF id s η t0 a j z)) :=
        le_trans (le_abs_self _) (Real.abs_le_sqrt (by nlinarith))
      have e : √(4 * padDen η t0 a j z (padF id s η t0 a j z))
          = 2 * √(padDen η t0 a j z (padF id s η t0 a j z)) := by
        rw [sqrt_mul (by norm_num), show √(4 : ℝ) = 2 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
      rw [e] at h4
      nlinarith
    have := mul_le_mul_of_nonneg_left hupd (ha j)
    linarith

/-- The squared final denominator is at most `3 + Λ²` when every coordinate is at most `Λ`:
features `x_i - z + F` with `0 ≤ z ≤ F ≤ z + Λ - 1` and carriers `1 + t₀τ ≤ Λ`.
Paper: proofs of `cor:pn-scaled-finalnorm-lower` (normalization_depth_lower.tex) and
`thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem padDen_le {η t0 : ℝ} (a : ℕ → ℝ) (j : ℕ) {z F Λ : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hF0 : z ≤ F) (hF1 : F ≤ z + (Λ - 1))
    (hC0 : 0 ≤ 1 + t0 * (schedR a j - 1)) (hC1 : 1 + t0 * (schedR a j - 1) ≤ Λ) :
    padDen η t0 a j z F ≤ 3 + Λ ^ 2 := by
  unfold padDen
  have hF : 1 - z ^ 2 + F ^ 2 ≤ Λ ^ 2 := by
    have : F ^ 2 ≤ (z + (Λ - 1)) ^ 2 := pow_le_pow_left₀ (by linarith) hF1 2
    nlinarith
  have hC : (1 + t0 * (schedR a j - 1)) ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hC0 hC1 2
  have := mul_le_mul_of_nonneg_left hF hη0
  have := mul_le_mul_of_nonneg_left hC (by linarith : (0 : ℝ) ≤ 1 - η)
  nlinarith

/-- The conditional output mean of a head with scale `L`:
`((1+z)/2) tanh((F - z + 1)/L) + ((1-z)/2) tanh((F - z - 1)/L)`.
Paper: `eq:pn-scaled-coordinatehead` (normalization_depth_lower.tex). -/
noncomputable def headMean (F z L : ℝ) : ℝ :=
  (1 + z) / 2 * tanh ((F - z + 1) / L) + (1 - z) / 2 * tanh ((F - z - 1) / L)

/-- The head mean is odd under `(F, z) ↦ (-F, -z)`.
Paper: proof of `thm:pn-scaled-lower` (normalization_depth_lower.tex). -/
theorem headMean_neg (F z L : ℝ) : headMean (-F) (-z) L = -headMean F z L := by
  unfold headMean
  have e1 : (-F - -z + 1) / L = -((F - z - 1) / L) := by ring
  have e2 : (-F - -z - 1) / L = -((F - z + 1) / L) := by ring
  rw [e1, e2, Real.tanh_neg, Real.tanh_neg]
  ring

/-- The shift bound for a head of scale `L ≥ F + 1 - z`, `F ≥ z ≥ 0`, `z ≤ 1`, `L ≥ 1`:
`headMean F z L ≥ F/(4L)`.
Paper: `eq:pn-scaled-coordinatehead` (normalization_depth_lower.tex); proof of
`cor:pn-scaled-finalnorm-lower`. -/
theorem headMean_ge {F z L : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hF : z ≤ F) (hL1 : 1 ≤ L)
    (hFL : F - z + 1 ≤ L) : F / (4 * L) ≤ headMean F z L := by
  have hL0 : 0 < L := by linarith
  have h := head_shift (z := z) (A := (F - z) / L) (k := 1 / L) hz0 hz1 (by positivity)
    (by rw [div_le_one hL0]; linarith) (div_nonneg (by linarith) hL0.le)
    (by rw [← add_div, div_le_one hL0]; linarith)
  have e1 : (F - z) / L + 1 / L = (F - z + 1) / L := by ring
  have e2 : (F - z) / L - 1 / L = (F - z - 1) / L := by ring
  rw [e1, e2] at h
  unfold headMean
  have : (z * (1 / L) + (F - z) / L) / 4 = F / (4 * L) := by field_simp; ring
  linarith

/-! ## Assembly of the query bounds -/

/-- **Assembly.** Combine a normalized comparison `U(x) ≥ G(x/ρ)/√(1 + C(G²-1)(x/ρ)²)`, an odd
head with `ḡ(x) ≥ U(x)/h₀`, a gain bound `G ≥ c₀X^δ` (`0 < c₀ ≤ 1`), the Rademacher moments, and
the transcript inequality `Q ≥ (N𝔼[Mḡ(M)])²`. Then
`Q ≥ c₀² min{X^{2δ}, N} / (h₀²ρ²(1 + 3C/ρ²))`.
Paper: the score and query steps in the proofs of `thm:pn-scaled-lower`,
`cor:pn-scaled-finalnorm-lower`, `cor:pn-scaled-padding`, `cor:pn-scheduled-lower`
(normalization_depth_lower.tex), `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem assemble_lower {ι : Type*} (S : Finset ι) (p M : ι → ℝ) {N Q G X c0 δ h0 ρ C : ℝ}
    (hN : 0 < N) (hp : ∀ i ∈ S, 0 ≤ p i) (h2 : ∑ i ∈ S, p i * M i ^ 2 = 1 / N)
    (h4 : ∑ i ∈ S, p i * M i ^ 4 ≤ 3 / N ^ 2) (hM : ∀ i ∈ S, |M i| ≤ 1)
    (hG1 : 1 ≤ G) (hρ : 0 < ρ) (hC : 0 < C) (hh0 : 0 < h0) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hX : 0 ≤ X) (hGX : c0 * X ^ δ ≤ G) (U gbar : ℝ → ℝ)
    (hcomp : ∀ x, 0 < x → x ≤ 1 → G * (x / ρ) / √(1 + C * (G ^ 2 - 1) * (x / ρ) ^ 2) ≤ U x)
    (hhead : ∀ x, 0 < x → x ≤ 1 → U x / h0 ≤ gbar x) (hodd : ∀ x, gbar (-x) = -gbar x)
    (hQ : (N * ∑ i ∈ S, p i * (M i * gbar (M i))) ^ 2 ≤ Q) :
    c0 ^ 2 * min (X ^ (2 * δ)) N / (h0 ^ 2 * ρ ^ 2 * (1 + 3 * C / ρ ^ 2)) ≤ Q := by
  have hG0 : 0 < G := by linarith
  have hpt : ∀ i ∈ S, G / (h0 * ρ) * (M i ^ 2 / √(1 + C * G ^ 2 / ρ ^ 2 * M i ^ 2))
      ≤ M i * gbar (M i) := by
    intro i hi
    have hodd' : M i * gbar (M i) = |M i| * gbar |M i| := by
      rcases le_total 0 (M i) with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, hodd]; ring
    rw [hodd', ← sq_abs (M i)]
    set x := |M i|
    have hx0 : 0 ≤ x := abs_nonneg _
    have hx1 : x ≤ 1 := hM i hi
    rcases eq_or_lt_of_le hx0 with hx | hx
    · rw [← hx]; simp
    have hc := hcomp x hx hx1
    have hh := hhead x hx hx1
    have hS' : 0 < 1 + C * (G ^ 2 - 1) * (x / ρ) ^ 2 := by
      have : 0 ≤ C * (G ^ 2 - 1) := mul_nonneg hC.le (by nlinarith)
      positivity
    have hmono : G * (x / ρ) / √(1 + C * G ^ 2 / ρ ^ 2 * x ^ 2)
        ≤ G * (x / ρ) / √(1 + C * (G ^ 2 - 1) * (x / ρ) ^ 2) := by
      apply div_le_div_of_nonneg_left (by positivity) (sqrt_pos.2 hS')
      apply sqrt_le_sqrt
      rw [div_pow]
      have h1 : C * (G ^ 2 - 1) ≤ C * G ^ 2 := by nlinarith
      have hx2 : 0 ≤ x ^ 2 / ρ ^ 2 := by positivity
      have : C * (G ^ 2 - 1) * (x ^ 2 / ρ ^ 2) ≤ C * G ^ 2 / ρ ^ 2 * x ^ 2 := by
        calc C * (G ^ 2 - 1) * (x ^ 2 / ρ ^ 2) ≤ C * G ^ 2 * (x ^ 2 / ρ ^ 2) :=
              mul_le_mul_of_nonneg_right h1 hx2
          _ = C * G ^ 2 / ρ ^ 2 * x ^ 2 := by ring
      linarith
    have hfin : G / (h0 * ρ) * (x ^ 2 / √(1 + C * G ^ 2 / ρ ^ 2 * x ^ 2))
        = x * (G * (x / ρ) / √(1 + C * G ^ 2 / ρ ^ 2 * x ^ 2) / h0) := by
      field_simp
    rw [hfin]
    apply mul_le_mul_of_nonneg_left _ hx0
    calc G * (x / ρ) / √(1 + C * G ^ 2 / ρ ^ 2 * x ^ 2) / h0 ≤ U x / h0 := by
          apply div_le_div_of_nonneg_right _ hh0.le; linarith
      _ ≤ gbar x := hh
  have hscore := score_lower S p M gbar hN (by positivity) (by positivity : 0 < C * G ^ 2 / ρ ^ 2)
    hp h2 h4 hpt
  have hq := query_min_bound (Q := Q) (K0 := h0 * ρ) (β' := C / ρ ^ 2) hG0 hN (by positivity)
    (by positivity) hQ (by
      have e : 3 * (C / ρ ^ 2) * G ^ 2 / N = 3 * (C * G ^ 2 / ρ ^ 2) / N := by ring
      rw [e]; exact hscore)
  have hG2 : c0 ^ 2 * X ^ (2 * δ) ≤ G ^ 2 := by
    have hsq := pow_le_pow_left₀ (by positivity) hGX 2
    have e : (c0 * X ^ δ) ^ 2 = c0 ^ 2 * X ^ (2 * δ) := by
      rw [mul_pow, ← rpow_natCast (X ^ δ), ← rpow_mul hX]; ring_nf
    linarith
  have hc2 : c0 ^ 2 ≤ 1 := by nlinarith
  have hmin : c0 ^ 2 * min (X ^ (2 * δ)) N ≤ min (G ^ 2) N := by
    apply le_min
    · exact le_trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (sq_nonneg _)) hG2
    · have h0' : 0 ≤ min (X ^ (2 * δ)) N := le_min (by positivity) hN.le
      calc c0 ^ 2 * min (X ^ (2 * δ)) N ≤ 1 * min (X ^ (2 * δ)) N :=
            mul_le_mul_of_nonneg_right hc2 h0'
        _ ≤ N := by rw [one_mul]; exact min_le_right _ _
  have e : (h0 * ρ) ^ 2 * (1 + 3 * (C / ρ ^ 2)) = h0 ^ 2 * ρ ^ 2 * (1 + 3 * C / ρ ^ 2) := by ring
  rw [e] at hq
  calc c0 ^ 2 * min (X ^ (2 * δ)) N / (h0 ^ 2 * ρ ^ 2 * (1 + 3 * C / ρ ^ 2))
      ≤ min (G ^ 2) N / (h0 ^ 2 * ρ ^ 2 * (1 + 3 * C / ρ ^ 2)) :=
        div_le_div_of_nonneg_right hmin (by positivity)
    _ ≤ Q := hq

/-! ## The padded families: heads -/

/-- `tanh` satisfies the activation hypothesis with `κ_ψ = 1`. -/
theorem tanh_hyp : ∀ y : ℝ, 0 ≤ y → y / √(1 + 1 * y ^ 2) ≤ tanh y := by
  intro y hy; rw [one_mul]; exact div_sqrt_le_tanh hy

/-- The identity satisfies the activation hypothesis with `κ_ψ = 0`. -/
theorem id_hyp : ∀ y : ℝ, 0 ≤ y → y / √(1 + 0 * y ^ 2) ≤ id y := by
  intro y _; simp

/-- The coordinate head of `thm:pn-scaled-lower`: with a power of two `L`, `R_D ≤ L ≤ 2R_D`,
the conditional mean satisfies `ḡ(z) ≥ F_D(z)/(4L) ≥ u_D(z)/8`.
Paper: `eq:pn-scaled-coordinatehead` (normalization_depth_lower.tex). -/
theorem head_scaled {s η t0 : ℝ} {a : ℕ → ℝ} (hs : 0 ≤ s) (ha : ∀ k, 0 ≤ a k) {D : ℕ} {L : ℝ}
    (hL1 : schedR a D ≤ L) (hL2 : L ≤ 2 * schedR a D) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    padF tanh s η t0 a D z / schedR a D / 8 ≤ headMean (padF tanh s η t0 a D z) z L := by
  have hF0 := padF_ge (ψ := tanh) (s := s) (η := η) (t0 := t0) (fun y hy => tanh_nonneg hy) hs
    ha hz0 D
  have hF1 := padF_tanh_le (s := s) (η := η) (t0 := t0) ha z D
  have hr := schedR_ge_one ha D
  have h := headMean_ge (L := L) hz0 hz1 hF0 (by linarith) (by linarith)
  have hF : 0 ≤ padF tanh s η t0 a D z := le_trans hz0 hF0
  calc padF tanh s η t0 a D z / schedR a D / 8 = padF tanh s η t0 a D z / (4 * (2 * schedR a D)) :=
        by field_simp; ring
    _ ≤ padF tanh s η t0 a D z / (4 * L) :=
        div_le_div_of_nonneg_left hF (by linarith) (by linarith)
    _ ≤ _ := h

/-- The final-normalization head: with `L = 4√v` and `v ≥ 3 + F²/4` (which holds for `η ≥ 1/4`),
`ḡ(z) ≥ F/(4L)` for `0 ≤ z ≤ F`. The scale bound `L ≤ 4√(3 + Λ²)` for coordinates bounded by
`Λ` is `padDen_le`.
Paper: proofs of `cor:pn-scaled-finalnorm-lower` (normalization_depth_lower.tex) and
`thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem head_final {F z v : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hF : z ≤ F)
    (hv : 3 + F ^ 2 / 4 ≤ v) : F / (4 * (4 * √v)) ≤ headMean F z (4 * √v) := by
  have hF0 : 0 ≤ F := le_trans hz0 hF
  have hro := (readout_le (h := F) (F := F) (by rw [abs_of_nonneg hF0]; linarith) hv).2
  rw [abs_of_nonneg hF0] at hro
  have hv0 : 0 < v := by nlinarith [sq_nonneg F]
  have h3 : (0 : ℝ) < √3 := by positivity
  have hs3 : 1 ≤ √3 := by
    have := sqrt_le_sqrt (show (1 : ℝ) ≤ 3 by norm_num); rwa [sqrt_one] at this
  have hFL : F + 2 ≤ 4 * √v := by
    have : 4 * √v / √3 ≤ 4 * √v := by
      rw [div_le_iff₀ h3]; nlinarith [sqrt_nonneg v]
    linarith
  exact headMean_ge hz0 hz1 hF (by linarith) (by linarith)

/-- The final-normalization head of the tanh padded families: `ḡ(z) ≥ u_D(z)/32`.
Paper: proof of `cor:pn-scaled-finalnorm-lower` (normalization_depth_lower.tex). -/
theorem head_final_tanh {s η t0 : ℝ} {a : ℕ → ℝ} (hs : 0 ≤ s) (hη0 : 1 / 4 ≤ η) (hη1 : η ≤ 1)
    (ht0 : 0 ≤ t0) (ht1 : t0 ≤ 1) (ha : ∀ k, 0 ≤ a k) (D : ℕ) {z : ℝ} (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) :
    padF tanh s η t0 a D z / schedR a D / 32 ≤ headMean (padF tanh s η t0 a D z) z
      (4 * √(padDen η t0 a D z (padF tanh s η t0 a D z))) := by
  have hF0 := padF_ge (ψ := tanh) (s := s) (η := η) (t0 := t0) (fun y hy => tanh_nonneg hy) hs
    ha hz0 D
  have hF1 := padF_tanh_le (s := s) (η := η) (t0 := t0) ha z D
  set F := padF tanh s η t0 a D z
  have hr := schedR_ge_one ha D
  have hz2 : z ^ 2 ≤ 1 := by nlinarith
  have hv := padDen_ge (t0 := t0) a D (F := F) (by linarith) hη1 hz2
  have hv' : 3 + F ^ 2 / 4 ≤ padDen η t0 a D z F := by nlinarith [sq_nonneg F]
  have h := head_final hz0 hz1 hF0 hv'
  have hv0 : 0 < padDen η t0 a D z F := by nlinarith [sq_nonneg F]
  have hC0 : 0 ≤ 1 + t0 * (schedR a D - 1) := by nlinarith
  have hC1 : 1 + t0 * (schedR a D - 1) ≤ schedR a D := by nlinarith
  have hup := padDen_le a D (by linarith) hη1 hz0 hz1 hF0 (by linarith) hC0 hC1
  have hsq : √(padDen η t0 a D z F) ≤ 2 * schedR a D := by
    rw [sqrt_le_left (by positivity)]; nlinarith
  have hF : 0 ≤ F := le_trans hz0 hF0
  calc F / schedR a D / 32 = F / (4 * (4 * (2 * schedR a D))) := by field_simp; ring
    _ ≤ F / (4 * (4 * √(padDen η t0 a D z F))) :=
        div_le_div_of_nonneg_left hF (by have := sqrt_pos.2 hv0; positivity) (by nlinarith)
    _ ≤ _ := h

/-- The final-normalization head of the GELU/SwiGLU padded families:
`L ≤ 4√(3 + (2s r_D)²) ≤ 8(s+1) r_D` and `ḡ(z) ≥ u_D(z)/(32(s+1))`.
Paper: proof of `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem head_final_ffn {s η t0 : ℝ} {a : ℕ → ℝ} (hs : 1 ≤ s) (hη0 : 1 / 4 ≤ η) (hη1 : η ≤ 1)
    (ht0 : 0 ≤ t0) (ht1 : t0 ≤ 1) (ha : ∀ k, 0 ≤ a k) (D : ℕ) {z : ℝ} (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) :
    padF id s η t0 a D z / schedR a D / (32 * (s + 1)) ≤ headMean (padF id s η t0 a D z) z
      (4 * √(padDen η t0 a D z (padF id s η t0 a D z))) := by
  have hF0 := padF_ge (ψ := id) (s := s) (η := η) (t0 := t0) (fun y hy => hy) (by linarith) ha
    hz0 D
  have hF1 := padF_id_le (t0 := t0) (by linarith) hη0 hη1 ha hz0 hz1 D (s := s)
  set F := padF id s η t0 a D z
  have hr := schedR_ge_one ha D
  have hz2 : z ^ 2 ≤ 1 := by nlinarith
  have hv := padDen_ge (t0 := t0) a D (F := F) (by linarith) hη1 hz2
  have hv' : 3 + F ^ 2 / 4 ≤ padDen η t0 a D z F := by nlinarith [sq_nonneg F]
  have h := head_final hz0 hz1 hF0 hv'
  have hv0 : 0 < padDen η t0 a D z F := by nlinarith [sq_nonneg F]
  have hC0 : 0 ≤ 1 + t0 * (schedR a D - 1) := by nlinarith
  have hC1 : 1 + t0 * (schedR a D - 1) ≤ 1 + 2 * s * (schedR a D - 1) := by
    have := mul_le_mul_of_nonneg_right (show t0 ≤ 2 * s by linarith)
      (show (0 : ℝ) ≤ schedR a D - 1 by linarith)
    linarith
  have hup := padDen_le a D (Λ := 1 + 2 * s * (schedR a D - 1)) (by linarith) hη1 hz0 hz1 hF0
    (by linarith) hC0 hC1
  have hΛ : 1 + 2 * s * (schedR a D - 1) ≤ 2 * s * schedR a D := by linarith
  have hΛ0 : 0 ≤ 1 + 2 * s * (schedR a D - 1) := by
    have := mul_nonneg (show (0 : ℝ) ≤ 2 * s by linarith)
      (show (0 : ℝ) ≤ schedR a D - 1 by linarith)
    linarith
  have hsq : √(padDen η t0 a D z F) ≤ 2 * (s + 1) * schedR a D := by
    rw [sqrt_le_left (by positivity)]
    have h1 : (1 + 2 * s * (schedR a D - 1)) ^ 2 ≤ (2 * s * schedR a D) ^ 2 :=
      pow_le_pow_left₀ hΛ0 hΛ 2
    have h2 : 3 ≤ 4 * (2 * s + 1) * schedR a D ^ 2 := by nlinarith
    nlinarith
  have hF : 0 ≤ F := le_trans hz0 hF0
  calc F / schedR a D / (32 * (s + 1)) = F / (4 * (4 * (2 * (s + 1) * schedR a D))) := by
        field_simp; ring
    _ ≤ F / (4 * (4 * √(padDen η t0 a D z F))) :=
        div_le_div_of_nonneg_left hF (by have := sqrt_pos.2 hv0; positivity) (by nlinarith)
    _ ≤ _ := h

/-! ## The padded families: query bounds -/

/-- The comparison constant `C = s(κ_ψ s² + 1/2)/(2δ)`: `C = s(s² + 1/2)/(2(s-1))` for tanh
blocks and `C_* = s/(4(s-1))` for GELU/SwiGLU blocks. -/
noncomputable def Cpad (kψ s : ℝ) : ℝ := s * (kψ * s ^ 2 + 1 / 2) / (2 * (s - 1))

/-- `C > 0` for `s > 1`. -/
theorem Cpad_pos {kψ s : ℝ} (hk : 0 ≤ kψ) (hs : 1 < s) : 0 < Cpad kψ s := by
  unfold Cpad; have : 0 < s - 1 := by linarith
  have : 0 < s := by linarith
  positivity

/-- The core of the padded lower bounds: the comparison, a head bound `ḡ ≥ u_D/h₀`, a gain bound
`G ≥ c₀X^δ`, and the transcript inequality give
`Q ≥ c₀² min{X^{2δ}, N} / (h₀²ρ²(1 + 3C/ρ²))`.
Paper: proofs of `thm:pn-scaled-lower`, `cor:pn-scaled-finalnorm-lower`,
`cor:pn-scaled-padding`, `cor:pn-scheduled-lower` (normalization_depth_lower.tex) and
`thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem pad_lower_core {ψ : ℝ → ℝ} {kψ s η t0 : ℝ} (hkψ : 0 ≤ kψ)
    (hψ : ∀ y, 0 ≤ y → y / √(1 + kψ * y ^ 2) ≤ ψ y) (hψ0 : ∀ y, 0 ≤ y → 0 ≤ ψ y)
    (hs : 1 < s) (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2) (ht0 : 0 ≤ t0) (ht1 : t0 ≤ 1) {a : ℕ → ℝ}
    (ha : ∀ k, 0 ≤ a k) {j0 n : ℕ} (hr : 3 + η ≤ η * schedR a j0 ^ 2) {ρ : ℝ}
    (hρ : schedR a j0 ≤ ρ) {c0 X h0 : ℝ} (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hX : 0 ≤ X)
    (hGX : c0 * X ^ (s - 1)
      ≤ ∏ i ∈ range n, (1 + (s - 1) * (a (j0 + i) / schedR a (j0 + i + 1))))
    (hh0 : 0 < h0) (gbar : ℝ → ℝ)
    (hhead : ∀ x, 0 < x → x ≤ 1 → padF ψ s η t0 a (j0 + n) x / schedR a (j0 + n) / h0 ≤ gbar x)
    (hodd : ∀ x, gbar (-x) = -gbar x)
    {ι : Type*} (S : Finset ι) (p M : ι → ℝ) {N Q : ℝ} (hN : 0 < N)
    (hp : ∀ i ∈ S, 0 ≤ p i) (h2 : ∑ i ∈ S, p i * M i ^ 2 = 1 / N)
    (h4 : ∑ i ∈ S, p i * M i ^ 4 ≤ 3 / N ^ 2) (hM : ∀ i ∈ S, |M i| ≤ 1)
    (hQ : (N * ∑ i ∈ S, p i * (M i * gbar (M i))) ^ 2 ≤ Q) :
    c0 ^ 2 * min (X ^ (2 * (s - 1))) N / (h0 ^ 2 * ρ ^ 2 * (1 + 3 * Cpad kψ s / ρ ^ 2)) ≤ Q := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le (schedR_pos ha j0) hρ
  have hG1 := (pad_comparison (n := n) (t0 := t0) hkψ hψ hψ0 hs hη0 hη1 ht0 ht1 ha hr hρ
    (z := 1) one_pos le_rfl).1
  exact assemble_lower S p M hN hp h2 h4 hM hG1 hρ0 (Cpad_pos hkψ hs) hh0 hc0 hc01 hX hGX
    (fun x => padF ψ s η t0 a (j0 + n) x / schedR a (j0 + n)) gbar
    (fun x hx0 hx1 => (pad_comparison (n := n) (t0 := t0) hkψ hψ hψ0 hs hη0 hη1 ht0 ht1 ha hr
      hρ hx0 hx1).2) hhead hodd hQ

/-- The burn-in index for a constant step: `j₀ = ⌈K/α⌉` gives
`1 + K ≤ r_{j₀} ≤ 2 + K` and `r_{j₀+1} ≤ 3 + K`, and `j₀ ≤ D` when `αD ≥ K + 1`.
Paper: proofs of `thm:pn-scaled-lower` (`K = 2`) and `cor:pn-scaled-padding` (`K = 3`)
(normalization_depth_lower.tex). -/
theorem uniform_burn_in {α K : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K) {D : ℕ}
    (hD : K + 1 ≤ α * D) :
    1 + K ≤ 1 + α * (⌈K / α⌉₊ : ℝ) ∧ 1 + α * (⌈K / α⌉₊ : ℝ) ≤ 2 + K ∧
      1 + α * ((⌈K / α⌉₊ : ℝ) + 1) ≤ 3 + K ∧ ⌈K / α⌉₊ ≤ D := by
  have h1 : K / α ≤ (⌈K / α⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈K / α⌉₊ : ℝ) < K / α + 1 := Nat.ceil_lt_add_one (by positivity)
  have e : α * (K / α) = K := by field_simp
  have hA : K ≤ α * (⌈K / α⌉₊ : ℝ) := by
    have := mul_le_mul_of_nonneg_left h1 hα0.le; linarith
  have hB : α * (⌈K / α⌉₊ : ℝ) ≤ K + 1 := by
    have := mul_le_mul_of_nonneg_left h2.le hα0.le
    nlinarith
  refine ⟨by linarith, by linarith, by nlinarith, ?_⟩
  have hlt : α * (⌈K / α⌉₊ : ℝ) < K + α := by
    have := mul_lt_mul_of_pos_left h2 hα0; nlinarith
  have : (⌈K / α⌉₊ : ℝ) ≤ D := by
    by_contra hc
    push Not at hc
    have : α * (D : ℝ) < α * (⌈K / α⌉₊ : ℝ) := mul_lt_mul_of_pos_left hc hα0
    nlinarith
  exact_mod_cast this

/-- The explicit constant of `thm:pn-scaled-lower`:
`c_s = e^{-δ²/3} 5^{-2δ}/(1024(1 + 3C/16))`, `δ = s - 1`, `C = s(s² + 1/2)/(2δ)`. -/
noncomputable def cScaled (s : ℝ) : ℝ :=
  exp (-((s - 1) ^ 2 / 3)) * 5 ^ (-(2 * (s - 1))) / (1024 * (1 + 3 * Cpad 1 s / 16))

/-- Rewriting `c₀²` for `c₀ = e^{-x} b^{-δ}`. -/
theorem c0_sq {x b δ : ℝ} (hb : 0 < b) :
    (exp (-x) * b ^ (-δ)) ^ 2 = exp (-(2 * x)) * b ^ (-(2 * δ)) := by
  rw [mul_pow, ← exp_nat_mul, ← rpow_natCast (b ^ (-δ)), ← rpow_mul hb.le]
  push_cast; ring_nf

/-- `0 < e^{-x} b^{-δ} ≤ 1` for `x, δ ≥ 0`, `b ≥ 1`. -/
theorem c0_mem {x b δ : ℝ} (hx : 0 ≤ x) (hb : 1 ≤ b) (hδ : 0 ≤ δ) :
    0 < exp (-x) * b ^ (-δ) ∧ exp (-x) * b ^ (-δ) ≤ 1 := by
  have h1 : exp (-x) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have h2 : b ^ (-δ) ≤ 1 := rpow_le_one_of_one_le_of_nonpos hb (by linarith)
  have h0 : 0 < b ^ (-δ) := rpow_pos_of_pos (by linarith) _
  refine ⟨by positivity, ?_⟩
  calc exp (-x) * b ^ (-δ) ≤ 1 * 1 := mul_le_mul h1 h2 h0.le zero_le_one
    _ = 1 := by ring

/-- `e^{-x} b^{-δ} X^δ = e^{-x}(X/b)^δ`. -/
theorem c0_mul_rpow {x b δ X : ℝ} (hb : 0 < b) (hX : 0 ≤ X) :
    exp (-x) * b ^ (-δ) * X ^ δ = exp (-x) * (X / b) ^ δ := by
  rw [div_rpow hX hb.le, rpow_neg hb.le]; ring

/-- **The relative-floor depth lower bound** `thm:pn-scaled-lower`, `eq:pn-scaled-lower`. For
the width-`2N` tanh network with constant step `α ∈ (0,1]`, `αD ≥ 4`, carriers moving at
`t₀ = tanh 1`, and the coordinate head of scale `L ∈ [R_D, 2R_D]`, the transcript inequality
`Q ≥ (N𝔼[Mḡ(M)])²` gives `Q ≥ c_s min{(1 + αD)^{2δ}, N}`.
Paper: `thm:pn-scaled-lower`, `eq:pn-scaled-lower` (normalization_depth_lower.tex);
`eq:main-prenorm-lower` (main_normalization.tex). -/
theorem scaled_lower {s α L : ℝ} {D : ℕ} (hs : 1 < s) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hαD : 4 ≤ α * D) (hL1 : 1 + α * D ≤ L) (hL2 : L ≤ 2 * (1 + α * D))
    {ι : Type*} (S : Finset ι) (p M : ι → ℝ) {N Q : ℝ} (hN : 0 < N)
    (hp : ∀ i ∈ S, 0 ≤ p i) (h2 : ∑ i ∈ S, p i * M i ^ 2 = 1 / N)
    (h4 : ∑ i ∈ S, p i * M i ^ 4 ≤ 3 / N ^ 2) (hM : ∀ i ∈ S, |M i| ≤ 1)
    (hQ : (N * ∑ i ∈ S, p i * (M i
        * headMean (padF tanh s (1 / 2) cT (fun _ => α) D (M i)) (M i) L)) ^ 2 ≤ Q) :
    cScaled s * min ((1 + α * D) ^ (2 * (s - 1))) N ≤ Q := by
  have ha : ∀ k : ℕ, (0 : ℝ) ≤ (fun _ => α) k := fun _ => hα0.le
  obtain ⟨b1, b2, b3, b4⟩ := uniform_burn_in (K := 2) hα0 hα1 (by norm_num) (D := D) (by linarith)
  set j0 := ⌈(2 : ℝ) / α⌉₊
  obtain ⟨n, hn⟩ : ∃ n, D = j0 + n := ⟨D - j0, by omega⟩
  have hrj0 : schedR (fun _ => α) j0 = 1 + α * j0 := schedR_const α j0
  have hδ : 0 ≤ s - 1 := by linarith
  obtain ⟨hc0, hc01⟩ := c0_mem (x := (s - 1) ^ 2 / 6) (b := 5) (δ := s - 1) (by positivity)
    (by norm_num) hδ
  have hX : 0 ≤ 1 + α * D := by positivity
  have hgain := uniform_gain_bound (δ := s - 1) (R0 := 3) (ρ1 := 5) (n := n) hα0 hα1 hδ
    (by norm_num) (j0 := j0) (by linarith) (by linarith)
  have hcast : ((j0 : ℝ) + n) = (D : ℝ) := by rw [hn]; push_cast; ring
  rw [hcast, show (-((s - 1) ^ 2 / (2 * 3))) = -((s - 1) ^ 2 / 6) by ring] at hgain
  have hGX : exp (-((s - 1) ^ 2 / 6)) * 5 ^ (-(s - 1)) * (1 + α * D) ^ (s - 1)
      ≤ ∏ i ∈ range n,
          (1 + (s - 1) * ((fun _ => α) (j0 + i) / schedR (fun _ => α) (j0 + i + 1))) := by
    rw [c0_mul_rpow (by norm_num) hX]; exact hgain
  have hcore := pad_lower_core (ψ := tanh) (kψ := 1) (s := s) (η := 1 / 2) (t0 := cT)
    (by norm_num) tanh_hyp (fun y hy => tanh_nonneg hy) hs (by norm_num) (by norm_num)
    cT_pos.le cT_lt_one.le ha (j0 := j0) (n := n) (by rw [hrj0]; nlinarith) (ρ := 4)
    (by rw [hrj0]; linarith) hc0 hc01 hX hGX (h0 := 8) (by norm_num)
    (fun x => headMean (padF tanh s (1 / 2) cT (fun _ => α) D x) x L)
    (fun x hx0 hx1 => by
      rw [← hn]
      have hRD : schedR (fun _ => α) D = 1 + α * D := schedR_const α D
      exact head_scaled (by linarith) ha (by rw [hRD]; exact hL1) (by rw [hRD]; exact hL2)
        hx0.le hx1)
    (fun x => by rw [padF_neg (fun y => Real.tanh_neg y), headMean_neg])
    S p M hN hp h2 h4 hM hQ
  have e : cScaled s * min ((1 + α * D) ^ (2 * (s - 1))) N
      = (exp (-((s - 1) ^ 2 / 6)) * 5 ^ (-(s - 1))) ^ 2 * min ((1 + α * D) ^ (2 * (s - 1))) N
        / ((8 : ℝ) ^ 2 * 4 ^ 2 * (1 + 3 * Cpad 1 s / 4 ^ 2)) := by
    unfold cScaled
    rw [c0_sq (by norm_num)]
    rw [show 2 * ((s - 1) ^ 2 / 6) = (s - 1) ^ 2 / 3 by ring]
    norm_num
    ring
  rw [e]; exact hcore

/-- The padded denominator is even in `(z, F)`. -/
theorem padDen_neg (η t0 : ℝ) (a : ℕ → ℝ) (j : ℕ) (z F : ℝ) :
    padDen η t0 a j (-z) (-F) = padDen η t0 a j z F := by
  unfold padDen; ring

/-- The final-normalization head is odd. -/
theorem finalHead_odd {ψ : ℝ → ℝ} (hψ : ∀ y, ψ (-y) = -ψ y) (s η t0 : ℝ) (a : ℕ → ℝ) (D : ℕ)
    (x : ℝ) :
    headMean (padF ψ s η t0 a D (-x)) (-x) (4 * √(padDen η t0 a D (-x) (padF ψ s η t0 a D (-x))))
      = -headMean (padF ψ s η t0 a D x) x (4 * √(padDen η t0 a D x (padF ψ s η t0 a D x))) := by
  rw [padF_neg hψ, padDen_neg, headMean_neg]

/-- **The fixed final RMSNorm readout** `cor:pn-scaled-finalnorm-lower`: with the head
`±𝒩₃(h_D)₁/4` the bound of `thm:pn-scaled-lower` holds with `c_s/16`.
Stand-in: the transcript inequality of `lem:transcript` (tanh_lower.tex), as the hypothesis
`Q ≥ (N𝔼[Mḡ(M)])²`.
Paper: `cor:pn-scaled-finalnorm-lower` (normalization_depth_lower.tex). -/
theorem scaled_finalnorm_lower {s α : ℝ} {D : ℕ} (hs : 1 < s) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hαD : 4 ≤ α * D) {ι : Type*} (S : Finset ι) (p M : ι → ℝ) {N Q : ℝ} (hN : 0 < N)
    (hp : ∀ i ∈ S, 0 ≤ p i) (h2 : ∑ i ∈ S, p i * M i ^ 2 = 1 / N)
    (h4 : ∑ i ∈ S, p i * M i ^ 4 ≤ 3 / N ^ 2) (hM : ∀ i ∈ S, |M i| ≤ 1)
    (hQ : (N * ∑ i ∈ S, p i * (M i * headMean (padF tanh s (1 / 2) cT (fun _ => α) D (M i)) (M i)
        (4 * √(padDen (1 / 2) cT (fun _ => α) D (M i)
          (padF tanh s (1 / 2) cT (fun _ => α) D (M i)))))) ^ 2 ≤ Q) :
    cScaled s / 16 * min ((1 + α * D) ^ (2 * (s - 1))) N ≤ Q := by
  have ha : ∀ k : ℕ, (0 : ℝ) ≤ (fun _ => α) k := fun _ => hα0.le
  obtain ⟨b1, b2, b3, b4⟩ := uniform_burn_in (K := 2) hα0 hα1 (by norm_num) (D := D) (by linarith)
  set j0 := ⌈(2 : ℝ) / α⌉₊
  obtain ⟨n, hn⟩ : ∃ n, D = j0 + n := ⟨D - j0, by omega⟩
  have hrj0 : schedR (fun _ => α) j0 = 1 + α * j0 := schedR_const α j0
  have hδ : 0 ≤ s - 1 := by linarith
  obtain ⟨hc0, hc01⟩ := c0_mem (x := (s - 1) ^ 2 / 6) (b := 5) (δ := s - 1) (by positivity)
    (by norm_num) hδ
  have hX : 0 ≤ 1 + α * D := by positivity
  have hgain := uniform_gain_bound (δ := s - 1) (R0 := 3) (ρ1 := 5) (n := n) hα0 hα1 hδ
    (by norm_num) (j0 := j0) (by linarith) (by linarith)
  have hcast : ((j0 : ℝ) + n) = (D : ℝ) := by rw [hn]; push_cast; ring
  rw [hcast, show (-((s - 1) ^ 2 / (2 * 3))) = -((s - 1) ^ 2 / 6) by ring] at hgain
  have hGX : exp (-((s - 1) ^ 2 / 6)) * 5 ^ (-(s - 1)) * (1 + α * D) ^ (s - 1)
      ≤ ∏ i ∈ range n,
          (1 + (s - 1) * ((fun _ => α) (j0 + i) / schedR (fun _ => α) (j0 + i + 1))) := by
    rw [c0_mul_rpow (by norm_num) hX]; exact hgain
  have hcore := pad_lower_core (ψ := tanh) (kψ := 1) (s := s) (η := 1 / 2) (t0 := cT)
    (by norm_num) tanh_hyp (fun y hy => tanh_nonneg hy) hs (by norm_num) (by norm_num)
    cT_pos.le cT_lt_one.le ha (j0 := j0) (n := n) (by rw [hrj0]; nlinarith) (ρ := 4)
    (by rw [hrj0]; linarith) hc0 hc01 hX hGX (h0 := 32) (by norm_num)
    (fun x => headMean (padF tanh s (1 / 2) cT (fun _ => α) D x) x
      (4 * √(padDen (1 / 2) cT (fun _ => α) D x (padF tanh s (1 / 2) cT (fun _ => α) D x))))
    (fun x hx0 hx1 => by
      rw [← hn]
      exact head_final_tanh (by linarith) (by norm_num) (by norm_num) cT_pos.le cT_lt_one.le ha D
        hx0.le hx1)
    (fun x => finalHead_odd (fun y => Real.tanh_neg y) s (1 / 2) cT _ D x)
    S p M hN hp h2 h4 hM hQ
  have e : cScaled s / 16 * min ((1 + α * D) ^ (2 * (s - 1))) N
      = (exp (-((s - 1) ^ 2 / 6)) * 5 ^ (-(s - 1))) ^ 2 * min ((1 + α * D) ^ (2 * (s - 1))) N
        / ((32 : ℝ) ^ 2 * 4 ^ 2 * (1 + 3 * Cpad 1 s / 4 ^ 2)) := by
    unfold cScaled
    rw [c0_sq (by norm_num)]
    rw [show 2 * ((s - 1) ^ 2 / 6) = (s - 1) ^ 2 / 3 by ring]
    have hCp' := Cpad_pos (kψ := 1) (by norm_num) hs
    field_simp
    ring
  rw [e]; exact hcore

/-- The explicit constant of `cor:pn-scaled-padding`:
`c_s^pad = e^{-δ²/4} 6^{-2δ}/(102400(1 + 3C/25))`. -/
noncomputable def cPadded (s : ℝ) : ℝ :=
  exp (-((s - 1) ^ 2 / 4)) * 6 ^ (-(2 * (s - 1))) / (102400 * (1 + 3 * Cpad 1 s / 25))

/-- From the feature-group size to the width: `c₀² min{x, N}/K ≥ c₀² min{x, n}/(4K)` when
`N > n/4`.
Paper: proofs of `cor:pn-scaled-padding` (normalization_depth_lower.tex) and
`thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem to_width {c x N n K Q : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hK : 0 < K) (hNn : n / 4 < N)
    (h : c * min x N / K ≤ Q) : c * min x n / (4 * K) ≤ Q := by
  have hm := min_quarter (x := x) hx hNn
  calc c * min x n / (4 * K) = c * (min x n / 4) / K := by field_simp
    _ ≤ c * min x N / K := by
        apply div_le_div_of_nonneg_right _ hK.le; exact mul_le_mul_of_nonneg_left hm hc
    _ ≤ Q := h

/-- **Padding to every width** `cor:pn-scaled-padding`: width `n`, feature fraction
`η = N/n ∈ [1/4, 1/2]`, constant step `α`, `αD ≥ 4`, final RMSNorm head:
`Q ≥ c_s^pad min{(1 + αD)^{2δ}, n}`.
Stand-in: the transcript inequality of `lem:transcript` (tanh_lower.tex), as the hypothesis
`Q ≥ (N𝔼[Mḡ(M)])²`.
Paper: `cor:pn-scaled-padding` (normalization_depth_lower.tex). -/
theorem padding_lower {s α η : ℝ} {D : ℕ} (hs : 1 < s) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hαD : 4 ≤ α * D) (hη0 : 1 / 4 ≤ η) (hη1 : η ≤ 1 / 2)
    {ι : Type*} (S : Finset ι) (p M : ι → ℝ) {N n Q : ℝ} (hN : 0 < N) (hNn : n / 4 < N)
    (hp : ∀ i ∈ S, 0 ≤ p i) (h2 : ∑ i ∈ S, p i * M i ^ 2 = 1 / N)
    (h4 : ∑ i ∈ S, p i * M i ^ 4 ≤ 3 / N ^ 2) (hM : ∀ i ∈ S, |M i| ≤ 1)
    (hQ : (N * ∑ i ∈ S, p i * (M i * headMean (padF tanh s η cT (fun _ => α) D (M i)) (M i)
        (4 * √(padDen η cT (fun _ => α) D (M i) (padF tanh s η cT (fun _ => α) D (M i)))))) ^ 2
        ≤ Q) :
    cPadded s * min ((1 + α * D) ^ (2 * (s - 1))) n ≤ Q := by
  have ha : ∀ k : ℕ, (0 : ℝ) ≤ (fun _ => α) k := fun _ => hα0.le
  obtain ⟨b1, b2, b3, b4⟩ := uniform_burn_in (K := 3) hα0 hα1 (by norm_num) (D := D) (by linarith)
  set j0 := ⌈(3 : ℝ) / α⌉₊
  obtain ⟨m, hm⟩ : ∃ m, D = j0 + m := ⟨D - j0, by omega⟩
  have hrj0 : schedR (fun _ => α) j0 = 1 + α * j0 := schedR_const α j0
  have hδ : 0 ≤ s - 1 := by linarith
  obtain ⟨hc0, hc01⟩ := c0_mem (x := (s - 1) ^ 2 / 8) (b := 6) (δ := s - 1) (by positivity)
    (by norm_num) hδ
  have hX : 0 ≤ 1 + α * D := by positivity
  have hgain := uniform_gain_bound (δ := s - 1) (R0 := 4) (ρ1 := 6) (n := m) hα0 hα1 hδ
    (by norm_num) (j0 := j0) (by linarith) (by linarith)
  have hcast : ((j0 : ℝ) + m) = (D : ℝ) := by rw [hm]; push_cast; ring
  rw [hcast, show (-((s - 1) ^ 2 / (2 * 4))) = -((s - 1) ^ 2 / 8) by ring] at hgain
  have hGX : exp (-((s - 1) ^ 2 / 8)) * 6 ^ (-(s - 1)) * (1 + α * D) ^ (s - 1)
      ≤ ∏ i ∈ range m,
          (1 + (s - 1) * ((fun _ => α) (j0 + i) / schedR (fun _ => α) (j0 + i + 1))) := by
    rw [c0_mul_rpow (by norm_num) hX]; exact hgain
  have hcore := pad_lower_core (ψ := tanh) (kψ := 1) (s := s) (η := η) (t0 := cT)
    (by norm_num) tanh_hyp (fun y hy => tanh_nonneg hy) hs (by linarith) hη1
    cT_pos.le cT_lt_one.le ha (j0 := j0) (n := m) (by rw [hrj0]; nlinarith) (ρ := 5)
    (by rw [hrj0]; linarith) hc0 hc01 hX hGX (h0 := 32) (by norm_num)
    (fun x => headMean (padF tanh s η cT (fun _ => α) D x) x
      (4 * √(padDen η cT (fun _ => α) D x (padF tanh s η cT (fun _ => α) D x))))
    (fun x hx0 hx1 => by
      rw [← hm]
      exact head_final_tanh (by linarith) hη0 (by linarith) cT_pos.le cT_lt_one.le ha D
        hx0.le hx1)
    (fun x => finalHead_odd (fun y => Real.tanh_neg y) s η cT _ D x)
    S p M hN hp h2 h4 hM hQ
  have hCp := Cpad_pos (kψ := 1) (by norm_num) hs
  have hw := to_width (by positivity) (by positivity) (by positivity) hNn hcore
  have e : cPadded s * min ((1 + α * D) ^ (2 * (s - 1))) n
      = (exp (-((s - 1) ^ 2 / 8)) * 6 ^ (-(s - 1))) ^ 2 * min ((1 + α * D) ^ (2 * (s - 1))) n
        / (4 * ((32 : ℝ) ^ 2 * 5 ^ 2 * (1 + 3 * Cpad 1 s / 5 ^ 2))) := by
    unfold cPadded
    rw [c0_sq (by norm_num)]
    rw [show 2 * ((s - 1) ^ 2 / 8) = (s - 1) ^ 2 / 4 by ring]
    have hCp' := Cpad_pos (kψ := 1) (by norm_num) hs
    field_simp
    ring
  rw [e]; exact hw

/-- The explicit constant of `cor:pn-scheduled-lower`:
`c_s^sched = e^{-δ/2 - δ²/4} 5^{-2δ}/(102400(1 + 3C/25))`. -/
noncomputable def cSched (s : ℝ) : ℝ :=
  exp (-((s - 1) / 2 + (s - 1) ^ 2 / 4)) * 5 ^ (-(2 * (s - 1)))
    / (102400 * (1 + 3 * Cpad 1 s / 25))

/-- **Prescribed step schedules** `cor:pn-scheduled-lower`: for dyadic steps `a_j ∈ [0,1]` with
`τ_D ≥ 4`, `Q ≥ c_s^sched min{(1 + τ_D)^{2δ}, n}`.
Stand-in: the transcript inequality of `lem:transcript` (tanh_lower.tex), as the hypothesis
`Q ≥ (N𝔼[Mḡ(M)])²`.
Paper: `cor:pn-scheduled-lower` (normalization_depth_lower.tex); `eq:main-prenorm-lower`
(main_normalization.tex). -/
theorem scheduled_lower {s η : ℝ} {a : ℕ → ℝ} {D : ℕ} (hs : 1 < s) (ha : ∀ k, 0 ≤ a k)
    (ha1 : ∀ k, a k ≤ 1) (hτ : 5 ≤ schedR a D) (hη0 : 1 / 4 ≤ η) (hη1 : η ≤ 1 / 2)
    {ι : Type*} (S : Finset ι) (p M : ι → ℝ) {N n Q : ℝ} (hN : 0 < N) (hNn : n / 4 < N)
    (hp : ∀ i ∈ S, 0 ≤ p i) (h2 : ∑ i ∈ S, p i * M i ^ 2 = 1 / N)
    (h4 : ∑ i ∈ S, p i * M i ^ 4 ≤ 3 / N ^ 2) (hM : ∀ i ∈ S, |M i| ≤ 1)
    (hQ : (N * ∑ i ∈ S, p i * (M i * headMean (padF tanh s η cT a D (M i)) (M i)
        (4 * √(padDen η cT a D (M i) (padF tanh s η cT a D (M i)))))) ^ 2 ≤ Q) :
    cSched s * min (schedR a D ^ (2 * (s - 1))) n ≤ Q := by
  obtain ⟨j0, hj0D, hj0, hj0'⟩ := exists_first_index ha1 (R := 4) (by norm_num) (by linarith)
  obtain ⟨m, hm⟩ : ∃ m, D = j0 + m := ⟨D - j0, by omega⟩
  have hδ : 0 ≤ s - 1 := by linarith
  obtain ⟨hc0, hc01⟩ := c0_mem (x := (s - 1) / 4 + (s - 1) ^ 2 / 8) (b := 5) (δ := s - 1)
    (by positivity) (by norm_num) hδ
  have hX : 0 ≤ schedR a D := (schedR_pos ha D).le
  have hgain := scheduled_gain_bound ha ha1 hδ (n := m) hj0 (by linarith)
  rw [← hm] at hgain
  have hGX : exp (-((s - 1) / 4 + (s - 1) ^ 2 / 8)) * 5 ^ (-(s - 1)) * schedR a D ^ (s - 1)
      ≤ ∏ i ∈ range m, (1 + (s - 1) * (a (j0 + i) / schedR a (j0 + i + 1))) := by
    rw [c0_mul_rpow (by norm_num) hX, show -((s - 1) / 4 + (s - 1) ^ 2 / 8)
      = -((s - 1) / 4) - (s - 1) ^ 2 / 8 by ring]; exact hgain
  have hcore := pad_lower_core (ψ := tanh) (kψ := 1) (s := s) (η := η) (t0 := cT)
    (by norm_num) tanh_hyp (fun y hy => tanh_nonneg hy) hs (by linarith) hη1
    cT_pos.le cT_lt_one.le ha (j0 := j0) (n := m) (by nlinarith) (ρ := 5)
    (by linarith) hc0 hc01 hX hGX (h0 := 32) (by norm_num)
    (fun x => headMean (padF tanh s η cT a D x) x
      (4 * √(padDen η cT a D x (padF tanh s η cT a D x))))
    (fun x hx0 hx1 => by
      rw [← hm]
      exact head_final_tanh (by linarith) hη0 (by linarith) cT_pos.le cT_lt_one.le ha D
        hx0.le hx1)
    (fun x => finalHead_odd (fun y => Real.tanh_neg y) s η cT a D x)
    S p M hN hp h2 h4 hM hQ
  have hCp := Cpad_pos (kψ := 1) (by norm_num) hs
  have hw := to_width (by positivity) (by positivity) (by positivity) hNn hcore
  have e : cSched s * min (schedR a D ^ (2 * (s - 1))) n
      = (exp (-((s - 1) / 4 + (s - 1) ^ 2 / 8)) * 5 ^ (-(s - 1))) ^ 2
          * min (schedR a D ^ (2 * (s - 1))) n
        / (4 * ((32 : ℝ) ^ 2 * 5 ^ 2 * (1 + 3 * Cpad 1 s / 5 ^ 2))) := by
    unfold cSched
    rw [c0_sq (by norm_num)]
    rw [show 2 * ((s - 1) / 4 + (s - 1) ^ 2 / 8) = (s - 1) / 2 + (s - 1) ^ 2 / 4 by ring]
    have hCp' := Cpad_pos (kψ := 1) (by norm_num) hs
    field_simp
    ring
  rw [e]; exact hw

/-! ## GELU and SwiGLU blocks (`thm:real-ffn-lower`, `cor:real-ffn-scheduled`) -/

/-- The explicit constant of `thm:real-ffn-lower`:
`c_s^ff = e^{-δ²/4} 6^{-2δ}/(102400(s+1)²(1 + 3C_*/25))`, `C_* = s/(4δ)`. -/
noncomputable def cFF (s : ℝ) : ℝ :=
  exp (-((s - 1) ^ 2 / 4)) * 6 ^ (-(2 * (s - 1)))
    / (102400 * (s + 1) ^ 2 * (1 + 3 * Cpad 0 s / 25))

/-- `C_* = s/(4(s-1))`.
Paper: `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem Cpad_zero (s : ℝ) : Cpad 0 s = s / (4 * (s - 1)) := by
  unfold Cpad
  rcases eq_or_ne (s - 1) 0 with h | h
  · simp [h]
  · field_simp; ring

/-- **The GELU/SwiGLU depth obstruction** `thm:real-ffn-lower`. After the antisymmetric identity
`φ(v) - φ(-v) = v`, the feature mean follows the linear update `F_{j+1} = F_j + αsF_j/√v_j`
(`ψ = id`); the carriers move at speed `t₀ = φ(1) ∈ [0,1]`. With `αD ≥ 4` and the fixed final
RMSNorm head, `Q ≥ c_s^ff min{(1 + αD)^{2δ}, n}`.
Stand-in: the transcript inequality of `lem:transcript` (tanh_lower.tex), as the hypothesis
`Q ≥ (N𝔼[Mḡ(M)])²`.
Paper: `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem ffn_lower {s α η t0 : ℝ} {D : ℕ} (hs : 1 < s) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hαD : 4 ≤ α * D) (hη0 : 1 / 4 ≤ η) (hη1 : η ≤ 1 / 2) (ht0 : 0 ≤ t0) (ht1 : t0 ≤ 1)
    {ι : Type*} (S : Finset ι) (p M : ι → ℝ) {N n Q : ℝ} (hN : 0 < N) (hNn : n / 4 < N)
    (hp : ∀ i ∈ S, 0 ≤ p i) (h2 : ∑ i ∈ S, p i * M i ^ 2 = 1 / N)
    (h4 : ∑ i ∈ S, p i * M i ^ 4 ≤ 3 / N ^ 2) (hM : ∀ i ∈ S, |M i| ≤ 1)
    (hQ : (N * ∑ i ∈ S, p i * (M i * headMean (padF id s η t0 (fun _ => α) D (M i)) (M i)
        (4 * √(padDen η t0 (fun _ => α) D (M i) (padF id s η t0 (fun _ => α) D (M i)))))) ^ 2
        ≤ Q) :
    cFF s * min ((1 + α * D) ^ (2 * (s - 1))) n ≤ Q := by
  have ha : ∀ k : ℕ, (0 : ℝ) ≤ (fun _ => α) k := fun _ => hα0.le
  obtain ⟨b1, b2, b3, b4⟩ := uniform_burn_in (K := 3) hα0 hα1 (by norm_num) (D := D) (by linarith)
  set j0 := ⌈(3 : ℝ) / α⌉₊
  obtain ⟨m, hm⟩ : ∃ m, D = j0 + m := ⟨D - j0, by omega⟩
  have hrj0 : schedR (fun _ => α) j0 = 1 + α * j0 := schedR_const α j0
  have hδ : 0 ≤ s - 1 := by linarith
  obtain ⟨hc0, hc01⟩ := c0_mem (x := (s - 1) ^ 2 / 8) (b := 6) (δ := s - 1) (by positivity)
    (by norm_num) hδ
  have hX : 0 ≤ 1 + α * D := by positivity
  have hgain := uniform_gain_bound (δ := s - 1) (R0 := 4) (ρ1 := 6) (n := m) hα0 hα1 hδ
    (by norm_num) (j0 := j0) (by linarith) (by linarith)
  have hcast : ((j0 : ℝ) + m) = (D : ℝ) := by rw [hm]; push_cast; ring
  rw [hcast, show (-((s - 1) ^ 2 / (2 * 4))) = -((s - 1) ^ 2 / 8) by ring] at hgain
  have hGX : exp (-((s - 1) ^ 2 / 8)) * 6 ^ (-(s - 1)) * (1 + α * D) ^ (s - 1)
      ≤ ∏ i ∈ range m,
          (1 + (s - 1) * ((fun _ => α) (j0 + i) / schedR (fun _ => α) (j0 + i + 1))) := by
    rw [c0_mul_rpow (by norm_num) hX]; exact hgain
  have hcore := pad_lower_core (ψ := id) (kψ := 0) (s := s) (η := η) (t0 := t0)
    le_rfl id_hyp (fun y hy => hy) hs (by linarith) hη1 ht0 ht1 ha (j0 := j0) (n := m)
    (by rw [hrj0]; nlinarith) (ρ := 5) (by rw [hrj0]; linarith) hc0 hc01 hX hGX
    (h0 := 32 * (s + 1)) (by linarith)
    (fun x => headMean (padF id s η t0 (fun _ => α) D x) x
      (4 * √(padDen η t0 (fun _ => α) D x (padF id s η t0 (fun _ => α) D x))))
    (fun x hx0 hx1 => by
      rw [← hm]
      exact head_final_ffn hs.le hη0 (by linarith) ht0 ht1 ha D hx0.le hx1)
    (fun x => finalHead_odd (fun y => by simp) s η t0 _ D x)
    S p M hN hp h2 h4 hM hQ
  have hCp := Cpad_pos (kψ := 0) le_rfl hs
  have hs1 : 0 < s + 1 := by linarith
  have hw := to_width (by positivity) (by positivity) (by positivity) hNn hcore
  have e : cFF s * min ((1 + α * D) ^ (2 * (s - 1))) n
      = (exp (-((s - 1) ^ 2 / 8)) * 6 ^ (-(s - 1))) ^ 2 * min ((1 + α * D) ^ (2 * (s - 1))) n
        / (4 * ((32 * (s + 1)) ^ 2 * 5 ^ 2 * (1 + 3 * Cpad 0 s / 5 ^ 2))) := by
    unfold cFF
    rw [c0_sq (by norm_num)]
    rw [show 2 * ((s - 1) ^ 2 / 8) = (s - 1) ^ 2 / 4 by ring]
    have hCp' := Cpad_pos (kψ := 1) (by norm_num) hs
    field_simp
    ring
  rw [e]; exact hw

/-- The explicit prefactor of `cor:real-ffn-scheduled`:
`e^{-δ/2 - δ²/4} 5^{-2δ}/(102400(s+1)²(1 + 3C_*/25))`. -/
noncomputable def cFFSched (s : ℝ) : ℝ :=
  exp (-((s - 1) / 2 + (s - 1) ^ 2 / 4)) * 5 ^ (-(2 * (s - 1)))
    / (102400 * (s + 1) ^ 2 * (1 + 3 * Cpad 0 s / 25))

/-- **GELU and SwiGLU with a prescribed schedule** `cor:real-ffn-scheduled`, for every depth:
`Q ≥ c min{(1 + τ_D)^{2δ}, n}` with the displayed prefactor. When `τ_D ≥ 4` the growth comparison
applies; when `τ_D < 4` the head bound alone gives `Q > 1/(25600(s+1)²)`.
Stand-in: the transcript inequality of `lem:transcript` (tanh_lower.tex), as the hypothesis
`Q ≥ (N𝔼[Mḡ(M)])²`.
Paper: `cor:real-ffn-scheduled` (normalization_ffn.tex). -/
theorem ffn_scheduled_lower {s η t0 : ℝ} {a : ℕ → ℝ} {D : ℕ} (hs : 1 < s) (ha : ∀ k, 0 ≤ a k)
    (ha1 : ∀ k, a k ≤ 1) (hη0 : 1 / 4 ≤ η) (hη1 : η ≤ 1 / 2) (ht0 : 0 ≤ t0) (ht1 : t0 ≤ 1)
    {ι : Type*} (S : Finset ι) (p M : ι → ℝ) {N n Q : ℝ} (hN : 0 < N) (hn : 0 ≤ n)
    (hNn : n / 4 < N) (hp : ∀ i ∈ S, 0 ≤ p i) (h2 : ∑ i ∈ S, p i * M i ^ 2 = 1 / N)
    (h4 : ∑ i ∈ S, p i * M i ^ 4 ≤ 3 / N ^ 2) (hM : ∀ i ∈ S, |M i| ≤ 1)
    (hQ : (N * ∑ i ∈ S, p i * (M i * headMean (padF id s η t0 a D (M i)) (M i)
        (4 * √(padDen η t0 a D (M i) (padF id s η t0 a D (M i)))))) ^ 2 ≤ Q) :
    cFFSched s * min (schedR a D ^ (2 * (s - 1))) n ≤ Q := by
  have hδ : 0 ≤ s - 1 := by linarith
  have hC0 : 0 < Cpad 0 s := Cpad_pos le_rfl hs
  set gbar := fun x => headMean (padF id s η t0 a D x) x
      (4 * √(padDen η t0 a D x (padF id s η t0 a D x))) with hgbar
  have hodd : ∀ x, gbar (-x) = -gbar x := fun x => finalHead_odd (fun y => by simp) s η t0 a D x
  rcases le_or_gt 5 (schedR a D) with hbig | hsmall
  · obtain ⟨j0, hj0D, hj0, hj0'⟩ := exists_first_index ha1 (R := 4) (by norm_num) (by linarith)
    obtain ⟨m, hm⟩ : ∃ m, D = j0 + m := ⟨D - j0, by omega⟩
    obtain ⟨hc0, hc01⟩ := c0_mem (x := (s - 1) / 4 + (s - 1) ^ 2 / 8) (b := 5) (δ := s - 1)
      (by positivity) (by norm_num) hδ
    have hX : 0 ≤ schedR a D := (schedR_pos ha D).le
    have hgain := scheduled_gain_bound ha ha1 hδ (n := m) hj0 (by linarith)
    rw [← hm] at hgain
    have hGX : exp (-((s - 1) / 4 + (s - 1) ^ 2 / 8)) * 5 ^ (-(s - 1)) * schedR a D ^ (s - 1)
        ≤ ∏ i ∈ range m, (1 + (s - 1) * (a (j0 + i) / schedR a (j0 + i + 1))) := by
      rw [c0_mul_rpow (by norm_num) hX, show -((s - 1) / 4 + (s - 1) ^ 2 / 8)
        = -((s - 1) / 4) - (s - 1) ^ 2 / 8 by ring]; exact hgain
    have hcore := pad_lower_core (ψ := id) (kψ := 0) (s := s) (η := η) (t0 := t0)
      le_rfl id_hyp (fun y hy => hy) hs (by linarith) hη1 ht0 ht1 ha (j0 := j0) (n := m)
      (by nlinarith) (ρ := 5) (by linarith) hc0 hc01 hX hGX
      (h0 := 32 * (s + 1)) (by linarith) gbar
      (fun x hx0 hx1 => by
        rw [← hm]
        exact head_final_ffn hs.le hη0 (by linarith) ht0 ht1 ha D hx0.le hx1)
      hodd S p M hN hp h2 h4 hM hQ
    have hs1 : 0 < s + 1 := by linarith
    have hw := to_width (by positivity) (by positivity) (by positivity) hNn hcore
    have e : cFFSched s * min (schedR a D ^ (2 * (s - 1))) n
        = (exp (-((s - 1) / 4 + (s - 1) ^ 2 / 8)) * 5 ^ (-(s - 1))) ^ 2
            * min (schedR a D ^ (2 * (s - 1))) n
          / (4 * ((32 * (s + 1)) ^ 2 * 5 ^ 2 * (1 + 3 * Cpad 0 s / 5 ^ 2))) := by
      unfold cFFSched
      rw [c0_sq (by norm_num)]
      rw [show 2 * ((s - 1) / 4 + (s - 1) ^ 2 / 8) = (s - 1) / 2 + (s - 1) ^ 2 / 4 by ring]
      field_simp
      ring
    rw [e]; exact hw
  · -- small total step: the head bound alone
    have hrD := schedR_pos ha D
    have hr1 := schedR_ge_one ha D
    have hpt : ∀ i ∈ S, M i ^ 2 / (32 * (s + 1) * 5) ≤ M i * gbar (M i) := by
      intro i hi
      have hodd' : M i * gbar (M i) = |M i| * gbar |M i| := by
        rcases le_total 0 (M i) with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_nonpos h, hodd]; ring
      rw [hodd', ← sq_abs (M i)]
      set x := |M i|
      have hx0 : 0 ≤ x := abs_nonneg _
      have hx1 : x ≤ 1 := hM i hi
      have hhead := head_final_ffn hs.le hη0 (by linarith) ht0 ht1 ha D (t0 := t0) hx0 hx1
        (η := η) (s := s)
      have hF := padF_ge (ψ := id) (s := s) (η := η) (t0 := t0) (fun y hy => hy) (by linarith)
        ha hx0 D
      have : x / (32 * (s + 1) * 5) ≤ gbar x := by
        calc x / (32 * (s + 1) * 5) ≤ padF id s η t0 a D x / schedR a D / (32 * (s + 1)) := by
              rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
              have := mul_le_mul hF (show schedR a D ≤ 5 by linarith) hrD.le (by linarith)
              nlinarith
          _ ≤ gbar x := hhead
      calc x ^ 2 / (32 * (s + 1) * 5) = x * (x / (32 * (s + 1) * 5)) := by ring
        _ ≤ x * gbar x := mul_le_mul_of_nonneg_left this hx0
    have hsum : 1 / (160 * (s + 1)) ≤ N * ∑ i ∈ S, p i * (M i * gbar (M i)) := by
      have h := sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hpt i hi) (hp i hi))
      have e : ∑ i ∈ S, p i * (M i ^ 2 / (32 * (s + 1) * 5)) = 1 / N / (32 * (s + 1) * 5) := by
        rw [← h2, sum_div]; apply sum_congr rfl; intro i _; ring
      rw [e] at h
      have : 0 < s + 1 := by linarith
      calc 1 / (160 * (s + 1)) = N * (1 / N / (32 * (s + 1) * 5)) := by field_simp; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h hN.le
    have hs1 : 0 < s + 1 := by linarith
    have hQ' : (1 / (160 * (s + 1))) ^ 2 ≤ Q :=
      le_trans (pow_le_pow_left₀ (by positivity) hsum 2) hQ
    have hpow : schedR a D ^ (2 * (s - 1)) ≤ 5 ^ (2 * (s - 1)) :=
      rpow_le_rpow hrD.le hsmall.le (by linarith)
    have hmin : min (schedR a D ^ (2 * (s - 1))) n ≤ 5 ^ (2 * (s - 1)) :=
      le_trans (min_le_left _ _) hpow
    have hmin0 : 0 ≤ min (schedR a D ^ (2 * (s - 1))) n := le_min (by positivity) hn
    have hc : cFFSched s * 5 ^ (2 * (s - 1)) ≤ 1 / (102400 * (s + 1) ^ 2) := by
      unfold cFFSched
      have h5 : (5 : ℝ) ^ (-(2 * (s - 1))) * 5 ^ (2 * (s - 1)) = 1 := by
        rw [← rpow_add (by norm_num)]; simp
      have hE : exp (-((s - 1) / 2 + (s - 1) ^ 2 / 4)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith
      have hD1 : 1 ≤ 1 + 3 * Cpad 0 s / 25 := by have := hC0.le; linarith
      have hs1 : 0 < s + 1 := by linarith
      rw [div_mul_eq_mul_div, mul_assoc, h5, mul_one, div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith [exp_pos (-((s - 1) / 2 + (s - 1) ^ 2 / 4)), sq_nonneg (s + 1)]
    have hs1 : 0 < s + 1 := by linarith
    have hc0 : 0 ≤ cFFSched s := by unfold cFFSched; positivity
    calc cFFSched s * min (schedR a D ^ (2 * (s - 1))) n ≤ cFFSched s * 5 ^ (2 * (s - 1)) :=
          mul_le_mul_of_nonneg_left hmin hc0
      _ ≤ 1 / (102400 * (s + 1) ^ 2) := hc
      _ ≤ (1 / (160 * (s + 1))) ^ 2 := by
          have : 0 < s + 1 := by linarith
          rw [div_pow, one_pow, mul_pow]
          apply one_div_le_one_div_of_le (by positivity); nlinarith
      _ ≤ Q := hQ'

/-- The supplied radii of the GELU/SwiGLU construction: `R_j = 1 + 4sαj ≤ 4s r_j`, so the floor
`v_j ≥ r_j²/12` gives `v_j ≥ R_j²/(192 s²) = γ_* R_j²`.
Paper: proof of `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem ffn_relative_floor {s α j v : ℝ} (hs : 1 ≤ s) (hα : 0 ≤ α) (hj : 0 ≤ j)
    (hv : (1 + α * j) ^ 2 / 12 ≤ v) : (1 + 4 * s * α * j) ^ 2 / (192 * s ^ 2) ≤ v := by
  have hR : 1 + 4 * s * α * j ≤ 4 * s * (1 + α * j) := by nlinarith [mul_nonneg hα hj]
  have hR0 : 0 ≤ 1 + 4 * s * α * j := by
    have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * s) hα) hj
    linarith
  have hsq := pow_le_pow_left₀ hR0 hR 2
  rw [div_le_iff₀ (by positivity)]
  have e : (4 * s * (1 + α * j)) ^ 2 = 16 * s ^ 2 * (1 + α * j) ^ 2 := by ring
  have : (1 + α * j) ^ 2 ≤ 12 * v := by linarith
  nlinarith [sq_nonneg s]

/-- A larger supplied additive radius weakens the certified floor by the square of the radius
ratio: if `R ≤ c r` and `v ≥ r²/12`, then `v ≥ R²/(12c²)`.
Paper: proof of `thm:real-ffn-lower` (normalization_ffn.tex). -/
theorem floor_under_radius_scaling (v r R c : ℝ) (hr : 0 ≤ r) (hR : 0 ≤ R) (hc : 0 < c)
    (hscale : R ≤ c * r) (hfloor : r ^ 2 / 12 ≤ v) : R ^ 2 / (12 * c ^ 2) ≤ v := by
  have hcr : 0 ≤ c * r := mul_nonneg (le_of_lt hc) hr
  have hsq : R ^ 2 ≤ (c * r) ^ 2 := by nlinarith
  have hden : 0 < 12 * c ^ 2 := by positivity
  apply (div_le_iff₀ hden).2
  have hmul := mul_le_mul_of_nonneg_left hfloor (sq_nonneg c)
  nlinarith

/-! ## The carrier family on the full cube (`thm:pn-family-query-law`, `thm:pn-family-bit-law`) -/

/-- The normalized nonsignal denominator on the full cube, with feature mean `z` and carrier mean
`w`: `b_j = (4 - ηz² - 2ηcτ_j w + ηc²τ_j²)/r_j²`.
Paper: proof of `thm:pn-family-query-law` (normalization_family_query.tex). -/
noncomputable def bFull (η : ℝ) (r z w : ℝ) : ℝ :=
  (4 - η * z ^ 2 - 2 * η * cT * (r - 1) * w + η * cT ^ 2 * (r - 1) ^ 2) / r ^ 2

/-- The stable form of `b_j` used by the oracle:
`b_j = ηc² - 2ηc(c + w)/r_j + (4 - ηz² + 2ηcw + ηc²)/r_j²`.
Paper: proof of `thm:pn-family-bit-law` (normalization_family_oracle.tex). -/
theorem bFull_stable (η r z w : ℝ) (hr : r ≠ 0) :
    bFull η r z w = η * cT ^ 2 - 2 * η * cT * (cT + w) / r
      + (4 - η * z ^ 2 + 2 * η * cT * w + η * cT ^ 2) / r ^ 2 := by
  unfold bFull; field_simp; ring

/-- On the full cube, `r_j² b_j ≥ 4 - 2η + η(cτ_j - 1)² ≥ 3 + η(cτ_j - 1)²`, hence
`b_j ≥ γ₀ > 1/12` by `eq:pn-carrier-floor` (normalization_gain.tex).
Paper: proof of `thm:pn-family-query-law` (normalization_family_query.tex). -/
theorem bFull_ge {η r z w : ℝ} (hη0 : 1 / 4 ≤ η) (hη1 : η ≤ 1 / 2) (hr : 1 ≤ r)
    (hz : |z| ≤ 1) (hw : |w| ≤ 1) : 1 / 12 < bFull η r z w := by
  have hc0 := cT_pos
  have hc1 := cT_lt_one
  have hr0 : 0 < r := by linarith
  have hz2 : z ^ 2 ≤ 1 := by
    have := sq_abs z; nlinarith [abs_nonneg z]
  have hw1 : w ≤ 1 := (abs_le.1 hw).2
  have hτ : 0 ≤ r - 1 := by linarith
  have hnum : 3 + η * (cT * (r - 1) - 1) ^ 2
      ≤ 4 - η * z ^ 2 - 2 * η * cT * (r - 1) * w + η * cT ^ 2 * (r - 1) ^ 2 := by
    have h1 : η * z ^ 2 ≤ η := by nlinarith
    have h2 : 2 * η * cT * (r - 1) * w ≤ 2 * η * cT * (r - 1) := by
      have : 0 ≤ 2 * η * cT * (r - 1) := by positivity
      nlinarith
    nlinarith
  have hfloor := full_cube_floor (v := 4 - η * z ^ 2 - 2 * η * cT * (r - 1) * w
    + η * cT ^ 2 * (r - 1) ^ 2) (τ := r - 1) hη0 hnum
  have hγ := gamma0_spec.2
  unfold bFull
  rw [lt_div_iff₀ (by positivity)]
  rw [show 1 + (r - 1) = r by ring] at hfloor
  nlinarith [sq_nonneg r]

/-- `|b_j - ηc²| ≤ 8/r_j` on the full cube: the first-order coefficient `-2ηc(c+w)` has magnitude
at most two and the second-order coefficient at most six.
Paper: proof of `thm:pn-family-query-law` (normalization_family_query.tex). -/
theorem bFull_close {η r z w : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2) (hr : 1 ≤ r)
    (hz : |z| ≤ 1) (hw : |w| ≤ 1) : |bFull η r z w - η * cT ^ 2| ≤ 8 / r := by
  have hc0 := cT_pos
  have hc1 := cT_lt_one
  have hr0 : 0 < r := by linarith
  rw [bFull_stable η r z w hr0.ne']
  have e : η * cT ^ 2 - 2 * η * cT * (cT + w) / r + (4 - η * z ^ 2 + 2 * η * cT * w
      + η * cT ^ 2) / r ^ 2 - η * cT ^ 2
      = -(2 * η * cT * (cT + w)) / r + (4 - η * z ^ 2 + 2 * η * cT * w + η * cT ^ 2) / r ^ 2 := by
    ring
  rw [e]
  have hz2 : z ^ 2 ≤ 1 := by have := sq_abs z; nlinarith [abs_nonneg z]
  have hwl := abs_le.1 hw
  have h1 : |2 * η * cT * (cT + w)| ≤ 2 := by
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg hη0 hc0.le]
  have h2 : |4 - η * z ^ 2 + 2 * η * cT * w + η * cT ^ 2| ≤ 6 := by
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg hη0 hc0.le, sq_nonneg z, sq_nonneg cT]
  have hA : |-(2 * η * cT * (cT + w)) / r| ≤ 2 / r := by
    rw [abs_div, abs_neg, abs_of_pos hr0]; exact div_le_div_of_nonneg_right h1 hr0.le
  have hB : |(4 - η * z ^ 2 + 2 * η * cT * w + η * cT ^ 2) / r ^ 2| ≤ 6 / r := by
    rw [abs_div, abs_of_pos (pow_pos hr0 2)]
    calc |4 - η * z ^ 2 + 2 * η * cT * w + η * cT ^ 2| / r ^ 2 ≤ 6 / r ^ 2 :=
          div_le_div_of_nonneg_right h2 (by positivity)
      _ ≤ 6 / r := div_le_div_of_nonneg_left (by norm_num) hr0 (by nlinarith)
  have := abs_add_le (-(2 * η * cT * (cT + w)) / r)
    ((4 - η * z ^ 2 + 2 * η * cT * w + η * cT ^ 2) / r ^ 2)
  have e8 : 2 / r + 6 / r = 8 / r := by ring
  linarith

/-- The inverse square root is `21`-Lipschitz on `[1/12, ∞)`: its derivative there is at most
`12^{3/2}/2 < 21`.
Paper: proof of `thm:pn-family-query-law` (normalization_family_query.tex). -/
theorem inv_sqrt_lipschitz {x y : ℝ} (hx : 1 / 12 ≤ x) (hy : 1 / 12 ≤ y) :
    |1 / √x - 1 / √y| ≤ 21 * |x - y| := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hsx : 0 < √x := sqrt_pos.2 hx0
  have hsy : 0 < √y := sqrt_pos.2 hy0
  have hsx1 : 2886 / 10000 ≤ √x := by
    have := sqrt_le_sqrt (show (2886 / 10000 : ℝ) ^ 2 ≤ x by norm_num; linarith)
    rwa [sqrt_sq (by norm_num)] at this
  have hsy1 : 2886 / 10000 ≤ √y := by
    have := sqrt_le_sqrt (show (2886 / 10000 : ℝ) ^ 2 ≤ y by norm_num; linarith)
    rwa [sqrt_sq (by norm_num)] at this
  have hxx : √x ^ 2 = x := sq_sqrt hx0.le
  have hyy : √y ^ 2 = y := sq_sqrt hy0.le
  have e : 1 / √x - 1 / √y = (y - x) / (√x * √y * (√x + √y)) := by
    field_simp
    linear_combination hyy - hxx
  have hden : 0 < √x * √y * (√x + √y) := mul_pos (mul_pos hsx hsy) (by linarith)
  rw [e, abs_div, abs_of_pos hden, abs_sub_comm y x]
  rw [div_le_iff₀ hden]
  have : 1 / 21 ≤ √x * √y * (√x + √y) := by
    have h1 : (2886 / 10000) ^ 2 ≤ √x * √y := by nlinarith
    have h2 : 2 * (2886 / 10000) ≤ √x + √y := by linarith
    have := mul_le_mul h1 h2 (by norm_num) (by positivity)
    norm_num at this ⊢
    linarith
  nlinarith [abs_nonneg (x - y)]

/-- The derivative estimate `∂_u T_j ≤ 1 + ν_η + C_u/r_j`, `C_u = 192 s`, in its scalar form:
for `b ≥ 1/12`, `B₀ = ηc² ≥ 1/12` and `|b - B₀| ≤ 8/r`, `s/√b ≤ s/√B₀ + 192 s/r`; here
`s/√B₀ = s/(c√η) = 1 + ν_η`.
Paper: proof of `thm:pn-family-query-law` (normalization_family_query.tex). -/
theorem slope_le {s b B0 r : ℝ} (hs : 0 ≤ s) (hb : 1 / 12 ≤ b) (hB0 : 1 / 12 ≤ B0) (hr : 0 < r)
    (hbB : |b - B0| ≤ 8 / r) : s / √b ≤ s / √B0 + 192 * s / r := by
  have h := inv_sqrt_lipschitz hb hB0
  have h1 : 1 / √b - 1 / √B0 ≤ 21 * (8 / r) := by
    have := le_trans (le_abs_self _) h
    nlinarith [abs_nonneg (b - B0)]
  have e1 : s / √b = s * (1 / √b) := by ring
  have e2 : s / √B0 = s * (1 / √B0) := by ring
  rw [e1, e2]
  have := mul_le_mul_of_nonneg_left h1 hs
  have e3 : s * (21 * (8 / r)) = 168 * s / r := by ring
  have h168 : 168 * s / r ≤ 192 * s / r := div_le_div_of_nonneg_right (by nlinarith) hr.le
  nlinarith

/-- `tanh' = 1 - tanh²`. -/
theorem hasDerivAt_tanh' (x : ℝ) : HasDerivAt tanh (1 - tanh x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (cosh_pos x).ne'
  have hc := (cosh_pos x).ne'
  have e : (cosh x * cosh x - sinh x * sinh x) / cosh x ^ 2 = 1 - tanh x ^ 2 := by
    rw [tanh_eq_sinh_div_cosh]; field_simp
  rw [e] at h
  have hf : (sinh / cosh) = tanh := by
    funext y; simp only [Pi.div_apply]; exact (tanh_eq_sinh_div_cosh y).symm
  rw [hf] at h; exact h

/-- The local slope of the tanh step: `0 ≤ ∂_u tanh(su/√(b + ηu²))
= sech²(·) · s b/(b + ηu²)^{3/2} ≤ s/√b`.
Paper: proof of `thm:pn-family-query-law` (normalization_family_query.tex). -/
theorem tanh_step_slope {s b η u : ℝ} (hs : 0 ≤ s) (hb : 0 < b) (hη : 0 ≤ η) :
    HasDerivAt (fun u => tanh (s * u / √(b + η * u ^ 2)))
      ((1 - tanh (s * u / √(b + η * u ^ 2)) ^ 2) * (s * b / ((b + η * u ^ 2)
        * √(b + η * u ^ 2)))) u ∧
      0 ≤ (1 - tanh (s * u / √(b + η * u ^ 2)) ^ 2) * (s * b / ((b + η * u ^ 2)
        * √(b + η * u ^ 2))) ∧
      (1 - tanh (s * u / √(b + η * u ^ 2)) ^ 2) * (s * b / ((b + η * u ^ 2)
        * √(b + η * u ^ 2))) ≤ s / √b := by
  have hD : 0 < b + η * u ^ 2 := by positivity
  have hsD : 0 < √(b + η * u ^ 2) := sqrt_pos.2 hD
  have hsq : √(b + η * u ^ 2) ^ 2 = b + η * u ^ 2 := sq_sqrt hD.le
  have h1 : HasDerivAt (fun u : ℝ => b + η * u ^ 2) (η * (2 * u)) u := by
    have := ((hasDerivAt_pow 2 u).const_mul η).const_add b
    simpa using this
  have h2 := ((hasDerivAt_id u).const_mul s).div (h1.sqrt hD.ne') hsD.ne'
  have harg : HasDerivAt (fun u => s * u / √(b + η * u ^ 2))
      (s * b / ((b + η * u ^ 2) * √(b + η * u ^ 2))) u := by
    convert h2 using 1
    · funext v; simp
    · simp only [id, mul_one]
      generalize √(b + η * u ^ 2) = q at *
      rw [← hsq]
      field_simp
      linear_combination (-s) * hsq
  have htanh := (hasDerivAt_tanh' (s * u / √(b + η * u ^ 2))).comp u harg
  have ht2 : tanh (s * u / √(b + η * u ^ 2)) ^ 2 ≤ 1 := by
    have h := abs_le.2 ⟨neg_one_le_tanh (s * u / √(b + η * u ^ 2)),
      tanh_le_one (s * u / √(b + η * u ^ 2))⟩
    nlinarith [abs_nonneg (tanh (s * u / √(b + η * u ^ 2))),
      sq_abs (tanh (s * u / √(b + η * u ^ 2)))]
  have hfrac0 : 0 ≤ s * b / ((b + η * u ^ 2) * √(b + η * u ^ 2)) := by positivity
  have hfrac : s * b / ((b + η * u ^ 2) * √(b + η * u ^ 2)) ≤ s / √b := by
    have hsb : 0 < √b := sqrt_pos.2 hb
    have hbb : √b ≤ √(b + η * u ^ 2) := sqrt_le_sqrt (by nlinarith [mul_nonneg hη (sq_nonneg u)])
    rw [div_le_div_iff₀ (by positivity) hsb]
    have hb2 : √b ^ 2 = b := sq_sqrt hb.le
    have : b * √b ≤ (b + η * u ^ 2) * √(b + η * u ^ 2) := by
      apply mul_le_mul (by linarith [mul_nonneg hη (sq_nonneg u)]) hbb hsb.le hD.le
    nlinarith
  refine ⟨htanh, mul_nonneg (by linarith) hfrac0, ?_⟩
  · calc (1 - tanh (s * u / √(b + η * u ^ 2)) ^ 2) * (s * b / ((b + η * u ^ 2)
          * √(b + η * u ^ 2))) ≤ 1 * (s * b / ((b + η * u ^ 2) * √(b + η * u ^ 2))) :=
          mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (tanh (s * u / √(b + η * u ^ 2)))])
            hfrac0
      _ ≤ s / √b := by rw [one_mul]; exact hfrac

/-- `(1 - x)^{-ν} ≥ 1 + νx` for `x < 1`, `ν ≥ 0`. -/
theorem one_sub_rpow_neg_ge {x ν : ℝ} (hx1 : x < 1) (hν : 0 ≤ ν) :
    1 + ν * x ≤ (1 - x) ^ (-ν) := by
  have h1x : 0 < 1 - x := by linarith
  rw [rpow_def_of_pos h1x]
  have hlog : log (1 - x) ≤ -x := by have := log_le_sub_one_of_pos h1x; linarith
  have : ν * x ≤ log (1 - x) * -ν := by nlinarith
  have := add_one_le_exp (log (1 - x) * -ν)
  linarith

/-- The integral comparison `∑ q_i r_{i+1}^{-ν} ≤ (r_k^{-ν} - r_j^{-ν})/ν ≤ 1/ν`, in its
step form: `ν (a/r') r'^{-ν} ≤ r^{-ν} - r'^{-ν}` for `r' = r + a`, `r > 0`, `a ≥ 0`.
Paper: proof of `thm:pn-family-query-law` (normalization_family_query.tex). -/
theorem neg_power_step {r a ν : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (hν : 0 ≤ ν) :
    ν * (a / (r + a)) * (r + a) ^ (-ν) ≤ r ^ (-ν) - (r + a) ^ (-ν) := by
  have hra : 0 < r + a := by linarith
  have hx0 : 0 ≤ a / (r + a) := div_nonneg ha hra.le
  have hx1 : a / (r + a) < 1 := by rw [div_lt_one hra]; linarith
  have h := one_sub_rpow_neg_ge hx1 hν
  have e : 1 - a / (r + a) = r / (r + a) := by field_simp; ring
  rw [e, div_rpow hr.le hra.le] at h
  have hp : 0 < (r + a) ^ (-ν) := rpow_pos_of_pos hra _
  rw [le_div_iff₀ hp] at h
  nlinarith

/-- The integral comparison with a positive power: `(a/r') r^p ≤ (r'^p - r^p)/p` for
`r' = r + a`, `p > 0`; summed, `∑ q_i r_i^p ≤ (r_j^p - 1)/p`.
Paper: proof of `thm:pn-family-query-law` (normalization_family_query.tex). -/
theorem pos_power_step {r a p : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (hp : 0 < p) :
    a / (r + a) * r ^ p ≤ ((r + a) ^ p - r ^ p) / p := by
  have hra : 0 < r + a := by linarith
  set y := (r + a) / r with hy
  have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ hr]; linarith
  have hy0 : 0 < y := by linarith
  have hlog : 1 - 1 / y ≤ log y := by
    have := one_sub_inv_le_log_of_pos hy0; rwa [one_div]
  have hexp : 1 + p * log y ≤ y ^ p := by
    rw [rpow_def_of_pos hy0]; have := add_one_le_exp (log y * p); nlinarith
  have hstep : 1 + p * (a / (r + a)) ≤ y ^ p := by
    have e : a / (r + a) = 1 - 1 / y := by rw [hy]; field_simp; ring
    rw [e]; nlinarith
  have hyp : y ^ p = (r + a) ^ p / r ^ p := by rw [hy, div_rpow hra.le hr.le]
  rw [hyp, le_div_iff₀ (rpow_pos_of_pos hr p)] at hstep
  rw [le_div_iff₀ hp]
  nlinarith

/-- The derivative multipliers `∏_{i=k}^{j-1} (1 + νq_i + C_u q_i/r_i) ≤ e^{C_u} (r_j/r_k)^ν`,
using `∑ q_i ≤ log(r_j/r_k)` and `∑ q_i/r_i = 1/r_k - 1/r_j ≤ 1`.
Paper: `eq:pn-family-derivative-product` (normalization_family_query.tex). -/
theorem derivative_product {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1) {ν Cu : ℝ}
    (hν : 0 ≤ ν) (hCu : 0 ≤ Cu) (k n : ℕ) :
    ∏ i ∈ range n, (1 + ν * (a (k + i) / schedR a (k + i + 1))
        + Cu * (a (k + i) / schedR a (k + i + 1)) / schedR a (k + i))
      ≤ exp Cu * (schedR a (k + n) / schedR a k) ^ ν := by
  have hlogq : ∀ i, a (k + i) / schedR a (k + i + 1)
      ≤ log (schedR a (k + i + 1)) - log (schedR a (k + i)) := by
    intro i
    have hr := schedR_pos ha (k + i)
    have hr1 := schedR_pos ha (k + i + 1)
    rw [← log_div hr1.ne' hr.ne']
    have := one_sub_inv_le_log_of_pos (div_pos hr1 hr)
    have e : 1 - (schedR a (k + i + 1) / schedR a (k + i))⁻¹
        = a (k + i) / schedR a (k + i + 1) := by
      rw [inv_div, schedR_succ]
      have : schedR a (k + i) + a (k + i) ≠ 0 := by rw [← schedR_succ]; exact hr1.ne'
      field_simp; ring
    linarith
  have hsumq : ∑ i ∈ range n, a (k + i) / schedR a (k + i + 1)
      ≤ log (schedR a (k + n)) - log (schedR a k) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ]
      have := hlogq n
      rw [show k + (n + 1) = k + n + 1 by ring]
      linarith
  obtain ⟨_, S2, _⟩ := schedule_sums ha ha1 k n
  have hS2 : ∑ i ∈ range n, a (k + i) / schedR a (k + i + 1) / schedR a (k + i) ≤ 1 := by
    rw [S2]
    have h1 : 1 / schedR a k ≤ 1 := by rw [div_le_one (schedR_pos ha k)]; exact schedR_ge_one ha k
    have h2 : 0 < 1 / schedR a (k + n) := one_div_pos.2 (schedR_pos ha _)
    linarith
  have hfac : ∀ i ∈ range n, 1 + ν * (a (k + i) / schedR a (k + i + 1))
      + Cu * (a (k + i) / schedR a (k + i + 1)) / schedR a (k + i)
      ≤ exp (ν * (a (k + i) / schedR a (k + i + 1))
        + Cu * (a (k + i) / schedR a (k + i + 1)) / schedR a (k + i)) := by
    intro i _
    have := add_one_le_exp (ν * (a (k + i) / schedR a (k + i + 1))
      + Cu * (a (k + i) / schedR a (k + i + 1)) / schedR a (k + i))
    linarith
  have hnn : ∀ i ∈ range n, 0 ≤ 1 + ν * (a (k + i) / schedR a (k + i + 1))
      + Cu * (a (k + i) / schedR a (k + i + 1)) / schedR a (k + i) := by
    intro i _
    have h0 := div_nonneg (ha (k + i)) (schedR_pos ha (k + i + 1)).le
    have := div_nonneg (mul_nonneg hCu h0) (schedR_pos ha (k + i)).le
    have := mul_nonneg hν h0
    linarith
  refine le_trans (prod_le_prod₀ hnn hfac) ?_
  rw [← exp_sum, sum_add_distrib, ← mul_sum]
  have hk := schedR_pos ha k
  have hkn := schedR_pos ha (k + n)
  rw [rpow_def_of_pos (div_pos hkn hk), log_div hkn.ne' hk.ne', ← exp_add]
  apply exp_le_exp.2
  have h1 := mul_le_mul_of_nonneg_left hsumq hν
  have h2 : ∑ i ∈ range n, Cu * (a (k + i) / schedR a (k + i + 1)) / schedR a (k + i) ≤ Cu := by
    have e : ∑ i ∈ range n, Cu * (a (k + i) / schedR a (k + i + 1)) / schedR a (k + i)
        = Cu * ∑ i ∈ range n, a (k + i) / schedR a (k + i + 1) / schedR a (k + i) := by
      rw [mul_sum]; apply sum_congr rfl; intro i _; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hS2 hCu
    linarith
  nlinarith

/-- The bootstrap for `v_{j+1} ≤ v_j + a_j v_j²`: if `v_j, a_j ≥ 0` and `4 v₀ ∑ a_j ≤ 1`, then
`v_j ≤ v₀ + 4v₀² ∑_{i<j} a_i ≤ 2 v₀`.
Paper: proof of `thm:pn-family-bit-law` (normalization_family_oracle.tex). -/
theorem bootstrap {v a : ℕ → ℝ} (hv : ∀ j, 0 ≤ v j) (ha : ∀ j, 0 ≤ a j) {n : ℕ}
    (hrec : ∀ j < n, v (j + 1) ≤ v j + a j * v j ^ 2)
    (hsmall : 4 * v 0 * ∑ i ∈ range n, a i ≤ 1) :
    ∀ j ≤ n, v j ≤ v 0 + 4 * v 0 ^ 2 * ∑ i ∈ range j, a i ∧ v j ≤ 2 * v 0 := by
  have hv0 := hv 0
  have hpart : ∀ j ≤ n, ∑ i ∈ range j, a i ≤ ∑ i ∈ range n, a i := fun j hj =>
    sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hj) (fun i _ _ => ha i)
  intro j
  induction j with
  | zero => intro _; simp; linarith
  | succ j ih =>
    intro hj
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hr := hrec j (by omega)
    have hsq : v j ^ 2 ≤ 4 * v 0 ^ 2 := by
      have := pow_le_pow_left₀ (hv j) h2 2; nlinarith
    have hstep : v (j + 1) ≤ v 0 + 4 * v 0 ^ 2 * ∑ i ∈ range (j + 1), a i := by
      rw [sum_range_succ]
      have := mul_le_mul_of_nonneg_left hsq (ha j)
      nlinarith
    refine ⟨hstep, ?_⟩
    have hP := hpart (j + 1) hj
    have : 4 * v 0 ^ 2 * ∑ i ∈ range (j + 1), a i ≤ v 0 := by
      have := mul_le_mul_of_nonneg_left hP (by positivity : (0 : ℝ) ≤ 4 * v 0 ^ 2)
      nlinarith
    linarith

/-- The rounding amplification `∏ (1 + C q_i) ≤ r^C`, from `∑ q_i ≤ log r`.
Paper: proof of `thm:pn-family-bit-law` (normalization_family_oracle.tex). -/
theorem rounding_product {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) {C : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    ∏ i ∈ range n, (1 + C * (a i / schedR a (i + 1))) ≤ schedR a n ^ C := by
  have hlogq : ∀ i, a i / schedR a (i + 1) ≤ log (schedR a (i + 1)) - log (schedR a i) := by
    intro i
    have hr := schedR_pos ha i
    have hr1 := schedR_pos ha (i + 1)
    rw [← log_div hr1.ne' hr.ne']
    have := one_sub_inv_le_log_of_pos (div_pos hr1 hr)
    have e : 1 - (schedR a (i + 1) / schedR a i)⁻¹ = a i / schedR a (i + 1) := by
      rw [inv_div, schedR_succ]
      have : schedR a i + a i ≠ 0 := by rw [← schedR_succ]; exact hr1.ne'
      field_simp; ring
    rw [← e]; exact this
  have hsum : ∑ i ∈ range n, a i / schedR a (i + 1) ≤ log (schedR a n) := by
    induction n with
    | zero => simp [schedR_zero]
    | succ n ih =>
      rw [sum_range_succ]
      calc ∑ i ∈ range n, a i / schedR a (i + 1) + a n / schedR a (n + 1)
          ≤ log (schedR a n) + (log (schedR a (n + 1)) - log (schedR a n)) :=
            add_le_add ih (hlogq n)
        _ = log (schedR a (n + 1)) := by ring
  have hnn : ∀ i ∈ range n, 0 ≤ 1 + C * (a i / schedR a (i + 1)) := fun i _ =>
    add_nonneg zero_le_one (mul_nonneg hC (div_nonneg (ha i) (schedR_pos ha (i + 1)).le))
  refine le_trans (prod_le_prod₀ hnn (fun i _ =>
    (add_comm 1 (C * (a i / schedR a (i + 1)))).trans_le (add_one_le_exp _))) ?_
  rw [← exp_sum, ← mul_sum, rpow_def_of_pos (schedR_pos ha n)]
  apply exp_le_exp.2
  calc C * ∑ i ∈ range n, a i / schedR a (i + 1) ≤ C * log (schedR a n) :=
        mul_le_mul_of_nonneg_left hsum hC
    _ = log (schedR a n) * C := mul_comm _ _

end ExactSampling.AdditiveNormalizedGain
