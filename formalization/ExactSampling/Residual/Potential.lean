import Mathlib

/-!
# The concave potential and the residual mixing estimate

This module formalizes the potential `φ(v) = √(1 + η - v^2)` of
`tanh_potential_local.tex` (subsection `app:potential`) and its use in
`tanh_residual_fused.tex` (section `sec:residualfused`).

Formalized here:
* the elementary properties of `φ` and of `ℓ = log φ` stated before
  `lem:potential-majority-bias`: evenness, `√η ≤ φ ≤ √α`, concavity with an
  explicit Jensen gap, finite Jensen inequality for signed mixtures, the
  derivative formulas and bounds `eq:potentialderivatives`, monotonicity of
  `θ / φ(θu)`, and the unit bound for `d/du ℓ(tanh u)`;
* the bias-term bound of `lem:potential-majority-bias`, including `B ≤ 0` for
  `t ≥ (7/2) q`;
* the residual mixing estimate `lem:respotentialmix` in full;
* the local steps of `thm:residualfused`: the weighted local estimate in terms of
  `d_j` (from the declared stand-in `d ≥ r^2/3 - r^4/5`, proved in
  `ExactSampling.ResidualDepth.tanh_le_quintic`), the bounds `1/8 ≤ φ ≤ √65/8`, and the
  radius powers `r^{1-κ} ≤ (1+αD)^{35/32}` (from the declared stand-in
  `r ≥ (1+x)^{-1/2}`, `eq:resradiuslower`); the numerical constants of `thm:residualfused` and
  `prop:residualfusedrate`, the rate bounds `(51/16)δ ≤ Γ_s ≤ (51/16)δ + 2^{36}δ^2`
  (given the fixed-point bounds on `u_*`), and the geometric generation bound.

Not formalized: the majority part of `lem:potential-majority-bias` (it rests on
`lem:arity` and a fifth-order Taylor bound for `tanh`), the probabilistic weighted
charging, and the fixed-point estimates `3δ ≤ u_*^2 ≤ 3δ + (3/2)δ^2`, which enter as
hypotheses.
-/

open Real Finset

namespace ExactSampling.Potential

/-- The potential `φ(v) = √(1 + η - v^2)` of `app:potential`. -/
noncomputable def phi (η v : ℝ) : ℝ := Real.sqrt (1 + η - v ^ 2)

/-! ## Elementary properties of `φ` -/

/-- Paper: `app:potential` (tanh_potential_local.tex): `φ` is even. -/
theorem phi_neg (η v : ℝ) : phi η (-v) = phi η v := by
  simp [phi]

/-- Auxiliary for `app:potential`: `φ(v)^2 = α - v^2` on `[-1, 1]`. -/
theorem phi_sq {η v : ℝ} (hη : 0 ≤ η) (hv : |v| ≤ 1) : phi η v ^ 2 = 1 + η - v ^ 2 := by
  have : v ^ 2 ≤ 1 := by nlinarith [abs_le.mp hv, sq_abs v]
  exact Real.sq_sqrt (by linarith)

/-- Paper: `app:potential` (tanh_potential_local.tex): `√η ≤ φ ≤ √α` on `[-1, 1]`. -/
theorem sqrt_le_phi {η v : ℝ} (hv : |v| ≤ 1) : Real.sqrt η ≤ phi η v := by
  apply Real.sqrt_le_sqrt
  nlinarith [abs_le.mp hv, sq_abs v]

/-- Paper: `app:potential` (tanh_potential_local.tex): `φ ≤ √α`. -/
theorem phi_le_sqrt (η v : ℝ) : phi η v ≤ Real.sqrt (1 + η) :=
  Real.sqrt_le_sqrt (by nlinarith [sq_nonneg v])

/-- Auxiliary for `app:potential`: `φ > 0` on `[-1, 1]` when `η > 0`. -/
theorem phi_pos {η v : ℝ} (hη : 0 < η) (hv : |v| ≤ 1) : 0 < phi η v :=
  lt_of_lt_of_le (Real.sqrt_pos.mpr hη) (sqrt_le_phi hv)

/-- Paper: proof of `lem:respotentialmix` (tanh_residual_fused.tex), the Jensen
gap `φ(v) - (1-ω)φ(u) - ωφ(w) ≥ ω(1-ω)Δ^2/(2√A)` with `A = 1 + η`. This also
proves the concavity of `φ` stated in `app:potential`. -/
theorem phi_jensen_gap {η u w ω : ℝ} (hη : 0 < η) (hu : |u| ≤ 1) (hw : |w| ≤ 1)
    (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) :
    (1 - ω) * phi η u + ω * phi η w + ω * (1 - ω) * (u - w) ^ 2 / (2 * Real.sqrt (1 + η)) ≤
      phi η ((1 - ω) * u + ω * w) := by
  set v := (1 - ω) * u + ω * w with hv
  have hu' := abs_le.mp hu
  have hw' := abs_le.mp hw
  have hvabs : |v| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith
  set a := phi η u with ha
  set b := phi η w with hb
  set P := phi η v with hP
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hP0 : 0 < P := phi_pos hη hvabs
  have ha2 := phi_sq hη.le hu
  have hb2 := phi_sq hη.le hw
  have hP2 := phi_sq hη.le hvabs
  have hPA : P ≤ Real.sqrt (1 + η) := phi_le_sqrt η v
  set g := ω * (1 - ω) * (u - w) ^ 2 with hg
  have hg0 : 0 ≤ g := by positivity
  set m := (1 - ω) * a + ω * b with hm
  have hm0 : 0 ≤ m := by positivity
  -- `m^2 ≤ P^2 - g`
  have hm2 : m ^ 2 ≤ P ^ 2 - g := by
    have e1 : (1 - ω) * a ^ 2 + ω * b ^ 2 - m ^ 2 = ω * (1 - ω) * (a - b) ^ 2 := by
      rw [hm]; ring
    have e2 : (1 - ω) * a ^ 2 + ω * b ^ 2 = P ^ 2 - g := by
      rw [ha2, hb2, hP2, hg, hv]; ring
    have : 0 ≤ ω * (1 - ω) * (a - b) ^ 2 := by
      have : 0 ≤ 1 - ω := by linarith
      positivity
    linarith
  -- `m ≤ P - g/(2P)`
  have hPg : g ≤ P ^ 2 := by nlinarith
  have hm_le : m ≤ P - g / (2 * P) := by
    have hrhs : 0 ≤ P - g / (2 * P) := by
      rw [sub_nonneg, div_le_iff₀ (by positivity)]
      nlinarith
    apply le_of_sq_le_sq _ hrhs
    have e : (P - g / (2 * P)) ^ 2 = P ^ 2 - g + (g / (2 * P)) ^ 2 := by
      field_simp
      ring
    rw [e]
    nlinarith [sq_nonneg (g / (2 * P))]
  have hfrac : g / (2 * Real.sqrt (1 + η)) ≤ g / (2 * P) :=
    div_le_div_of_nonneg_left hg0 (by positivity) (by linarith)
  have e3 : ω * (1 - ω) * (u - w) ^ 2 / (2 * Real.sqrt (1 + η)) =
      g / (2 * Real.sqrt (1 + η)) := by rw [hg]
  rw [e3]
  linarith

/-- Paper: proof of `lem:respotentialmix` (tanh_residual_fused.tex),
`|φ(w) - φ(v)| ≤ |w - v| / √η` on `[-1, 1]` (from `|φ'| ≤ η^{-1/2}`). -/
theorem phi_lipschitz {η v w : ℝ} (hη : 0 < η) (hv : |v| ≤ 1) (hw : |w| ≤ 1) :
    |phi η w - phi η v| ≤ |w - v| / Real.sqrt η := by
  have hv0 := sqrt_le_phi (η := η) hv
  have hw0 := sqrt_le_phi (η := η) hw
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hsum : 2 * Real.sqrt η ≤ phi η w + phi η v := by linarith
  have hsum0 : 0 < phi η w + phi η v := by linarith
  have e : phi η w - phi η v = (v - w) * (v + w) / (phi η w + phi η v) := by
    rw [eq_div_iff hsum0.ne']
    have := phi_sq hη.le hv
    have := phi_sq hη.le hw
    nlinarith
  rw [e, abs_div, abs_mul, abs_of_pos hsum0, div_le_div_iff₀ hsum0 hs]
  have hvw : |v + w| ≤ 2 := by
    have := abs_add_le v w
    linarith
  rw [abs_sub_comm v w]
  have h0 : 0 ≤ |w - v| := abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hvw h0]

/-- Paper: `app:potential` (tanh_potential_local.tex): `φ` is concave on
`[-1, 1]`. -/
theorem phi_concaveOn {η : ℝ} (hη : 0 < η) : ConcaveOn ℝ (Set.Icc (-1) 1) (phi η) := by
  refine ⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => ?_⟩
  have hxa : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2⟩
  have hya : |y| ≤ 1 := abs_le.mpr ⟨hy.1, hy.2⟩
  have h := phi_jensen_gap hη hxa hya hb (by linarith)
  have ha' : a = 1 - b := by linarith
  subst ha'
  simp only [smul_eq_mul]
  have : 0 ≤ b * (1 - b) * (x - y) ^ 2 / (2 * Real.sqrt (1 + η)) := by
    have : 0 ≤ 1 - b := by linarith
    positivity
  linarith

/-- Paper: `app:potential` (tanh_potential_local.tex), the finite Jensen
inequality for a signed row mixture: `∑ p_j φ(v_j) = ∑ p_j φ(σ_j v_j) ≤
φ(∑ p_j σ_j v_j)` when `σ_j = ±1`. -/
theorem phi_signed_jensen {ι : Type*} {η : ℝ} (hη : 0 < η) (s : Finset ι)
    (p v σ : ι → ℝ) (hp : ∀ j ∈ s, 0 ≤ p j) (hp1 : ∑ j ∈ s, p j = 1)
    (hv : ∀ j ∈ s, |v j| ≤ 1) (hσ : ∀ j ∈ s, σ j = 1 ∨ σ j = -1) :
    ∑ j ∈ s, p j * phi η (v j) ≤ phi η (∑ j ∈ s, p j * (σ j * v j)) := by
  have heq : ∀ j ∈ s, phi η (v j) = phi η (σ j * v j) := by
    intro j hj
    rcases hσ j hj with h | h <;> simp [h, phi_neg]
  rw [sum_congr rfl fun j hj => by rw [heq j hj]]
  have hmem : ∀ j ∈ s, σ j * v j ∈ Set.Icc (-1 : ℝ) 1 := by
    intro j hj
    have h1 := abs_le.mp (hv j hj)
    rcases hσ j hj with h | h <;> rw [h] <;> constructor <;> linarith
  have := (phi_concaveOn hη).le_map_sum hp hp1 hmem
  simpa only [smul_eq_mul] using this

/-- Paper: `app:potential` (tanh_potential_local.tex): for `|u| ≤ 1`,
`θ ↦ θ / φ(θ u)` is increasing on `[0, 1]`. -/
theorem div_phi_mono {η u θ₁ θ₂ : ℝ} (hη : 0 < η) (hu : |u| ≤ 1) (h0 : 0 ≤ θ₁)
    (h12 : θ₁ ≤ θ₂) (h2 : θ₂ ≤ 1) :
    θ₁ / phi η (θ₁ * u) ≤ θ₂ / phi η (θ₂ * u) := by
  have hu' := abs_le.mp hu
  have habs : ∀ θ, 0 ≤ θ → θ ≤ 1 → |θ * u| ≤ 1 := fun θ h0 h1 => by
    rw [abs_mul, abs_of_nonneg h0]
    nlinarith [abs_nonneg u]
  have hp1 := phi_pos hη (habs θ₁ h0 (by linarith))
  have hp2 := phi_pos hη (habs θ₂ (by linarith) h2)
  rw [div_le_div_iff₀ hp1 hp2]
  have hs1 := phi_sq hη.le (habs θ₁ h0 (by linarith))
  have hs2 := phi_sq hη.le (habs θ₂ (by linarith) h2)
  have hθ : 0 ≤ θ₂ := by linarith
  apply le_of_sq_le_sq _ (by positivity)
  rw [mul_pow, mul_pow, hs1, hs2]
  have : θ₁ ^ 2 ≤ θ₂ ^ 2 := pow_le_pow_left₀ h0 h12 2
  nlinarith

/-- Paper: `tanh_residual_fused.tex`, proof of `thm:residualfused`: the
actual-row factor can be absorbed, `θ φ(v) ≤ φ(θ v)` for `0 ≤ θ ≤ 1`. This is the
squared form `θ^2 (α - u^2) ≤ α - θ^2 u^2` of the monotonicity of `θ/φ(θu)`. -/
theorem mul_phi_le {η v θ : ℝ} (hη : 0 < η) (hv : |v| ≤ 1) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ * phi η v ≤ phi η (θ * v) := by
  have h := div_phi_mono hη hv h0 h1 le_rfl
  rw [one_mul] at h
  have hp1 := phi_pos hη hv
  have hθv : |θ * v| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg h0]
    nlinarith [abs_nonneg v]
  have hp2 := phi_pos hη hθv
  rw [div_le_div_iff₀ hp2 hp1, mul_comm] at h
  linarith

/-! ## The logarithmic potential `ℓ = log φ` -/

/-- `ℓ(v) = log φ(v)`, written as `(1/2) log(α - v^2)`. -/
noncomputable def ell (η v : ℝ) : ℝ := Real.log (1 + η - v ^ 2) / 2

/-- Auxiliary for `eq:potentialderivatives`: `ℓ = log φ`. -/
theorem ell_eq_log_phi {η v : ℝ} (h : v ^ 2 < 1 + η) : ell η v = Real.log (phi η v) := by
  rw [ell, phi, Real.log_sqrt (by linarith)]

/-- Paper: `eq:potentialderivatives` (tanh_potential_local.tex): `ℓ'(v) = -v/(α - v^2)`. -/
theorem hasDerivAt_ell {η v : ℝ} (h : v ^ 2 < 1 + η) :
    HasDerivAt (ell η) (-v / (1 + η - v ^ 2)) v := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + η - x ^ 2) (-(2 * v)) v := by
    simpa using ((hasDerivAt_pow 2 v).const_sub (1 + η))
  have h2 := (h1.log (by linarith)).div_const 2
  show HasDerivAt (fun x => Real.log (1 + η - x ^ 2) / 2) _ v
  convert h2 using 1
  ring

/-- Paper: `eq:potentialderivatives` (tanh_potential_local.tex):
`ℓ''(v) = -(α + v^2)/(α - v^2)^2`. -/
theorem hasDerivAt_ell_deriv {η v : ℝ} (h : v ^ 2 < 1 + η) :
    HasDerivAt (fun x => -x / (1 + η - x ^ 2)) (-(1 + η + v ^ 2) / (1 + η - v ^ 2) ^ 2) v := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + η - x ^ 2) (-(2 * v)) v := by
    simpa using ((hasDerivAt_pow 2 v).const_sub (1 + η))
  have h0 : HasDerivAt (fun x : ℝ => -x) (-1) v := (hasDerivAt_id' v).neg
  have h2 := h0.div h1 (by linarith)
  convert h2 using 1
  ring

/-- Paper: `eq:potentialderivatives` (tanh_potential_local.tex): for
`0 < η ≤ 1/4` and `|v| ≤ 1`, `|ℓ'(v)| = |v|/(α - v^2) ≤ η^{-1}` and
`|ℓ''(v)| = (α + v^2)/(α - v^2)^2 ≤ 9/(4η^2)`. -/
theorem ell_deriv_bounds {η v : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (hv : |v| ≤ 1) :
    |-v / (1 + η - v ^ 2)| ≤ 1 / η ∧
      |-(1 + η + v ^ 2) / (1 + η - v ^ 2) ^ 2| ≤ 9 / (4 * η ^ 2) := by
  have hv2 : v ^ 2 ≤ 1 := by nlinarith [abs_le.mp hv, sq_abs v]
  have hd : η ≤ 1 + η - v ^ 2 := by linarith
  have hd0 : 0 < 1 + η - v ^ 2 := by linarith
  constructor
  · rw [abs_div, abs_neg, abs_of_pos hd0, div_le_div_iff₀ hd0 hη0]
    nlinarith [abs_nonneg v]
  · rw [abs_div, abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have : η ^ 2 ≤ (1 + η - v ^ 2) ^ 2 := pow_le_pow_left₀ hη0.le hd 2
    nlinarith

/-- Paper: proof of `lem:potential-majority-bias` (tanh_potential_local.tex): for
`v = tanh u`, `|d/du ℓ(tanh u)| = |v|(1 - v^2)/(α - v^2) ≤ 1`. -/
theorem ell_tanh_deriv_le {η v : ℝ} (hη : 0 ≤ η) (hv : |v| ≤ 1) :
    |-v / (1 + η - v ^ 2) * (1 - v ^ 2)| ≤ 1 := by
  have hv2 : v ^ 2 ≤ 1 := by nlinarith [abs_le.mp hv, sq_abs v]
  rcases lt_or_eq_of_le hv2 with hlt | heq
  · have hd0 : 0 < 1 + η - v ^ 2 := by linarith
    rw [abs_mul, abs_div, abs_neg, abs_of_pos hd0,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - v ^ 2), div_mul_eq_mul_div, div_le_one hd0]
    nlinarith [abs_nonneg v]
  · rw [heq]
    simp

/-! ## The bias term of `lem:potential-majority-bias` -/

/-- Auxiliary for `lem:potential-majority-bias`: `tanh' = 1 - tanh^2`. -/
theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have hfun : Real.sinh / Real.cosh = Real.tanh := by
    funext y
    rw [Pi.div_apply, Real.tanh_eq_sinh_div_cosh]
  rw [hfun] at h
  convert h using 1
  rw [Real.tanh_eq_sinh_div_cosh]
  have := Real.cosh_pos x
  field_simp

/-- Auxiliary: the addition formula `tanh(x+y) = (tanh x + tanh y)/(1 + tanh x tanh y)`. -/
theorem tanh_add (x y : ℝ) :
    Real.tanh (x + y) = (Real.tanh x + Real.tanh y) / (1 + Real.tanh x * Real.tanh y) := by
  have hx := Real.cosh_pos x
  have hy := Real.cosh_pos y
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    Real.sinh_add, Real.cosh_add]
  have hden : 0 < Real.cosh x * Real.cosh y + Real.sinh x * Real.sinh y := by
    rw [← Real.cosh_add]; exact Real.cosh_pos _
  field_simp

/-- Auxiliary for `lem:potential-majority-bias`: `x ↦ x + ℓ(tanh x)` is monotone. -/
theorem add_ell_tanh_monotone {η : ℝ} (hη : 0 < η) :
    Monotone (fun x => x + ell η (Real.tanh x)) := by
  have hd : ∀ x, HasDerivAt (fun x => x + ell η (Real.tanh x))
      (1 + -Real.tanh x / (1 + η - Real.tanh x ^ 2) * (1 - Real.tanh x ^ 2)) x := by
    intro x
    have ht2 : Real.tanh x ^ 2 < 1 + η := by
      have := Real.abs_tanh_lt_one x
      nlinarith [sq_abs (Real.tanh x), abs_nonneg (Real.tanh x)]
    exact (hasDerivAt_id x).add ((hasDerivAt_ell ht2).comp x (hasDerivAt_tanh x))
  refine monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt) fun x => ?_
  rw [(hd x).deriv]
  have := ell_tanh_deriv_le hη.le (Real.abs_tanh_lt_one x).le
  have := (abs_le.mp this).1
  linarith

/-- Paper: proof of `lem:potential-majority-bias` (tanh_potential_local.tex):
`ℓ(g) - ℓ(T_c(g)) ≤ artanh c` for `0 ≤ c < 1` and `|g| ≤ 1`, including `g = ±1`. -/
theorem ell_sub_ell_bias_le {η c g : ℝ} (hη : 0 < η) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hg : |g| ≤ 1) : ell η g - ell η ((g + c) / (1 + c * g)) ≤ Real.artanh c := by
  have hart : 0 ≤ Real.artanh c := Real.artanh_nonneg hc0
  rcases lt_or_eq_of_le hg with hlt | heq
  · have hgI : g ∈ Set.Ioo (-1 : ℝ) 1 := ⟨(abs_lt.mp hlt).1, (abs_lt.mp hlt).2⟩
    have hcI : c ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hc1⟩
    set x := Real.artanh g with hx
    set y := Real.artanh c with hy
    have htx : Real.tanh x = g := Real.tanh_artanh hgI
    have hty : Real.tanh y = c := Real.tanh_artanh hcI
    have hadd : Real.tanh (x + y) = (g + c) / (1 + c * g) := by
      rw [tanh_add, htx, hty, mul_comm]
    have hmono := add_ell_tanh_monotone hη (by linarith : x ≤ x + y)
    simp only at hmono
    rw [htx, hadd] at hmono
    linarith
  · rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp heq with h | h
    · subst h
      have : (1 + c) / (1 + c * 1) = 1 := by field_simp
      rw [this]
      simpa using hart
    · subst h
      have hc : (1 : ℝ) - c ≠ 0 := by linarith
      have : (-1 + c) / (1 + c * -1) = -1 := by
        rw [show (1 : ℝ) + c * -1 = 1 - c by ring, div_eq_iff hc]
        ring
      rw [this]
      simpa using hart

/-- Auxiliary for `lem:potential-majority-bias`: `artanh c ≤ c/(1 - c^2)` for
`0 ≤ c < 1`, from the odd series of `log((1+c)/(1-c))`. -/
theorem artanh_le (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) : Real.artanh c ≤ c / (1 - c ^ 2) := by
  have habs : |c| < 1 := by rw [abs_of_nonneg hc0]; exact hc1
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hgeo : HasSum (fun k : ℕ => 2 * c ^ (2 * k + 1)) (2 * c / (1 - c ^ 2)) := by
    have h := hasSum_geometric_of_lt_one (sq_nonneg c) (by nlinarith : c ^ 2 < 1)
    have h2 := h.mul_left (2 * c)
    convert h2 using 1
    · funext k
      rw [pow_succ, pow_mul]
      ring
    · field_simp
  have hle := hasSum_le (fun k => by
      have hk : (0 : ℝ) ≤ c ^ (2 * k + 1) := pow_nonneg hc0 _
      have hk1 : 1 / (2 * (k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      have : 2 * (1 / (2 * (k : ℝ) + 1)) * c ^ (2 * k + 1) ≤ 2 * 1 * c ^ (2 * k + 1) := by
        apply mul_le_mul_of_nonneg_right _ hk
        linarith
      linarith) hs hgeo
  rw [Real.artanh_eq_half_log ⟨by linarith, hc1.le⟩,
    Real.log_div (by linarith) (by linarith)]
  have e : 2 * c / (1 - c ^ 2) = 2 * (c / (1 - c ^ 2)) := by ring
  linarith

/-- Paper: `lem:potential-majority-bias` (tanh_potential_local.tex), the bias
term. Let `0 ≤ t < 1`, `0 < q < 1` with `2q^2 ≤ 1`, `|g| ≤ 1`, `c = tq`,
`k = (1 - t^2)/(1 - c^2)` and `T_c(g) = (g + c)/(1 + cg)`. Then
`B = log k + log((1+c)/(1+cg)) + ℓ(g) - ℓ(k T_c(g)) ≤ (-(1 - 2q^2)t^2 + 3tq)/(1 - q^2)`. -/
theorem bias_term_le {η t q g : ℝ} (hη : 0 < η) (ht0 : 0 ≤ t) (ht1 : t < 1) (hq0 : 0 < q)
    (hq1 : q < 1) (hq2 : 2 * q ^ 2 ≤ 1) (hg : |g| ≤ 1) :
    Real.log ((1 - t ^ 2) / (1 - (t * q) ^ 2)) + Real.log ((1 + t * q) / (1 + t * q * g)) +
        ell η g - ell η ((1 - t ^ 2) / (1 - (t * q) ^ 2) * ((g + t * q) / (1 + t * q * g))) ≤
      (-(1 - 2 * q ^ 2) * t ^ 2 + 3 * t * q) / (1 - q ^ 2) := by
  set c := t * q with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c < 1 := by nlinarith
  have hcq : c ≤ q := by nlinarith
  have hg' := abs_le.mp hg
  have hq2' : q ^ 2 < 1 := by nlinarith
  have hc2 : c ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hc0 hcq 2
  have hden : 0 < 1 - c ^ 2 := by nlinarith
  set k := (1 - t ^ 2) / (1 - c ^ 2) with hk
  have hk0 : 0 < k := div_pos (by nlinarith) hden
  have hk1 : k ≤ 1 := by
    rw [hk, div_le_one hden]
    nlinarith
  -- `log k ≤ -(1 - 2q^2) t^2/(1 - q^2)`
  have hlogk : Real.log k ≤ -(1 - 2 * q ^ 2) * t ^ 2 / (1 - q ^ 2) := by
    refine (Real.log_le_sub_one_of_pos hk0).trans ?_
    rw [hk, div_sub_one hden.ne', le_div_iff₀ (by linarith)]
    have e1 : (1 - t ^ 2 - (1 - c ^ 2)) / (1 - c ^ 2) * (1 - q ^ 2) =
        -(t ^ 2 * (1 - q ^ 2) ^ 2) / (1 - c ^ 2) := by rw [hcdef]; field_simp; ring
    rw [e1, div_le_iff₀ hden]
    have : 0 ≤ q ^ 2 * (q ^ 2 + t ^ 2 * (1 - 2 * q ^ 2)) := by
      apply mul_nonneg (sq_nonneg q)
      nlinarith [sq_nonneg t]
    rw [hcdef]
    nlinarith
  -- the race term: `log((1+c)/(1+cg)) ≤ 2 artanh c`
  have hrace : Real.log ((1 + c) / (1 + c * g)) ≤ 2 * Real.artanh c := by
    have hcg : 1 - c ≤ 1 + c * g := by nlinarith
    have hpos : 0 < 1 + c * g := by linarith
    rw [Real.artanh_eq_half_log ⟨by linarith, hc1.le⟩]
    have : (1 + c) / (1 + c * g) ≤ (1 + c) / (1 - c) :=
      div_le_div_of_nonneg_left (by linarith) (by linarith) hcg
    have := Real.log_le_log (div_pos (by linarith) hpos) this
    linarith
  -- `ℓ(g) - ℓ(k T) ≤ ℓ(g) - ℓ(T) ≤ artanh c`
  set T := (g + c) / (1 + c * g) with hT
  have hTabs : |T| ≤ 1 := by
    have hpos : 0 < 1 + c * g := by nlinarith
    rw [hT, abs_div, abs_of_pos hpos, div_le_one hpos, abs_le]
    constructor <;> nlinarith
  have hkT : ell η T ≤ ell η (k * T) := by
    unfold ell
    have hT2 : T ^ 2 ≤ 1 := by nlinarith [abs_le.mp hTabs, sq_abs T]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply Real.log_le_log (by linarith)
    have : (k * T) ^ 2 ≤ T ^ 2 := by
      rw [mul_pow]
      have : k ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg T]
    linarith
  have hell := ell_sub_ell_bias_le hη hc0 hc1 hg
  have hart := artanh_le c hc0 hc1
  have hart2 : c / (1 - c ^ 2) ≤ c / (1 - q ^ 2) :=
    div_le_div_of_nonneg_left hc0 (by linarith) (by linarith)
  have e : (-(1 - 2 * q ^ 2) * t ^ 2 + 3 * t * q) / (1 - q ^ 2) =
      -(1 - 2 * q ^ 2) * t ^ 2 / (1 - q ^ 2) + 3 * (c / (1 - q ^ 2)) := by
    rw [hcdef]; field_simp
  rw [e]
  have hmulc : c * g = t * q * g := by rw [hcdef]
  rw [← hmulc] at *
  linarith

/-- Paper: `lem:potential-majority-bias` (tanh_potential_local.tex), "in
particular `B ≤ 0` when `t ≥ (7/2) q`", using `q ≤ ρ ≤ 1/16`. -/
theorem bias_bound_nonpos {t q : ℝ} (hq0 : 0 < q) (hq : q ≤ 1 / 16) (ht : 7 / 2 * q ≤ t) :
    (-(1 - 2 * q ^ 2) * t ^ 2 + 3 * t * q) / (1 - q ^ 2) ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg _ (by nlinarith)
  have ht0 : 0 ≤ t := by linarith
  have h1 : -(1 - 2 * q ^ 2) * t ^ 2 + 3 * t * q ≤ t * q * (-1 / 2 + 7 * q ^ 2) := by
    have : 0 ≤ 1 - 2 * q ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left ht (mul_nonneg ht0 this)]
  have h2 : -1 / 2 + 7 * q ^ 2 ≤ 0 := by nlinarith
  nlinarith [mul_nonneg ht0 hq0.le]

/-- Paper: proof of `lem:potential-majority-bias` (tanh_potential_local.tex):
`η^2 + 11η + 9/32 ≤ 99/32 < 4` for `0 < η ≤ 1/4`, so
`1 + 11/η + 9/(32 η^2) ≤ 4/η^2`. -/
theorem majority_remainder_constant {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) :
    1 + 11 / η + 9 / (32 * η ^ 2) ≤ 4 / η ^ 2 := by
  have e : 1 + 11 / η + 9 / (32 * η ^ 2) = (η ^ 2 + 11 * η + 9 / 32) / η ^ 2 := by
    field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

/-! ## The residual mixing estimate `lem:respotentialmix` -/

/-- Paper: `lem:respotentialmix` (tanh_residual_fused.tex). Let `0 < η ≤ 1/4`,
`u, w ∈ [-1, 1]`, `0 ≤ ω ≤ 1`, `0 ≤ ξ ≤ 1`. Then
`log(((1-ω)φ(u) + ω e^ξ φ(w)) / φ((1-ω)u + ωw)) ≤ ωξ + 4 η^{-3/2} ω ξ^2`, with
`η^{-3/2} = 1/(η √η)`. -/
theorem respotentialmix {η u w ω ξ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (hu : |u| ≤ 1)
    (hw : |w| ≤ 1) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) :
    Real.log (((1 - ω) * phi η u + ω * Real.exp ξ * phi η w) /
        phi η ((1 - ω) * u + ω * w)) ≤ ω * ξ + 4 / (η * Real.sqrt η) * ω * ξ ^ 2 := by
  set v := (1 - ω) * u + ω * w with hv
  have hu' := abs_le.mp hu
  have hw' := abs_le.mp hw
  have hvabs : |v| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith
  set A := 1 + η with hA
  set sη := Real.sqrt η with hsη
  set sA := Real.sqrt A with hsA
  have hsη0 : 0 < sη := Real.sqrt_pos.mpr hη0
  have hsη2 : sη ^ 2 = η := Real.sq_sqrt hη0.le
  have hsA0 : 0 < sA := Real.sqrt_pos.mpr (by linarith)
  have hsA2 : sA ^ 2 = A := Real.sq_sqrt (by linarith)
  have hsη_le : sη ≤ 1 / 2 := by
    apply le_of_sq_le_sq _ (by norm_num)
    rw [hsη2]
    linarith
  have hsA_le : sA ≤ 9 / 8 := by
    apply le_of_sq_le_sq _ (by norm_num)
    rw [hsA2]
    linarith
  set P := phi η v with hP
  have hP0 : 0 < P := phi_pos hη0 hvabs
  have hPη : sη ≤ P := sqrt_le_phi hvabs
  set a := phi η u
  set b := phi η w
  have ha0 : 0 < a := phi_pos hη0 hu
  have hb0 : 0 < b := phi_pos hη0 hw
  set t := Real.exp ξ - 1 with ht
  have ht0 : 0 ≤ t := by
    have := Real.add_one_le_exp ξ
    linarith
  have ht1 : t ≤ ξ + ξ ^ 2 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := ξ) (by rw [abs_of_nonneg hξ0]; exact hξ1)
    have := (abs_le.mp h).2
    linarith
  have ht2 : t ≤ 2 * ξ := by nlinarith
  set Δ := |u - w| with hΔ
  have hΔ0 : 0 ≤ Δ := abs_nonneg _
  have hgap := phi_jensen_gap hη0 hu hw hω0 hω1
  rw [← hv] at hgap
  have hgap' : (1 - ω) * a + ω * b ≤ P - ω * (1 - ω) * Δ ^ 2 / (2 * sA) := by
    have e : (u - w) ^ 2 = Δ ^ 2 := by rw [hΔ, sq_abs]
    rw [e] at hgap
    linarith
  have hlip : b - P ≤ (1 - ω) * Δ / sη := by
    have h := phi_lipschitz hη0 hvabs hw
    have e : |w - v| = (1 - ω) * Δ := by
      rw [hv, hΔ, show w - ((1 - ω) * u + ω * w) = (1 - ω) * (w - u) by ring, abs_mul,
        abs_of_nonneg (by linarith), abs_sub_comm]
    rw [e] at h
    exact le_trans (le_abs_self _) h
  -- the numerator minus `(1 + ωt) P`
  have hnum : (1 - ω) * a + ω * Real.exp ξ * b - (1 + ω * t) * P ≤
      ω * (1 - ω) * (t * Δ / sη - Δ ^ 2 / (2 * sA)) := by
    have e : (1 - ω) * a + ω * Real.exp ξ * b - (1 + ω * t) * P =
        ((1 - ω) * a + ω * b - P) + ω * t * (b - P) := by rw [ht]; ring
    rw [e]
    have h1 : ω * t * (b - P) ≤ ω * t * ((1 - ω) * Δ / sη) :=
      mul_le_mul_of_nonneg_left hlip (by positivity)
    have e2 : ω * (1 - ω) * (t * Δ / sη - Δ ^ 2 / (2 * sA)) =
        ω * t * ((1 - ω) * Δ / sη) - ω * (1 - ω) * Δ ^ 2 / (2 * sA) := by ring
    rw [e2]
    linarith
  -- completing the square
  have hsq : t * Δ / sη - Δ ^ 2 / (2 * sA) ≤ t ^ 2 * sA / (2 * η) := by
    set p := t / sη with hp
    have e1 : t * Δ / sη = p * Δ := by rw [hp]; ring
    have e2 : t ^ 2 * sA / (2 * η) = p ^ 2 * sA / 2 := by
      rw [hp, div_pow, hsη2]
      field_simp
    rw [e1, e2]
    have hkey : 0 ≤ (Δ - p * sA) ^ 2 / (2 * sA) := by positivity
    have e3 : p ^ 2 * sA / 2 - (p * Δ - Δ ^ 2 / (2 * sA)) = (Δ - p * sA) ^ 2 / (2 * sA) := by
      field_simp
      ring
    linarith
  have hω1' : 0 ≤ 1 - ω := by linarith
  have hnum2 : (1 - ω) * a + ω * Real.exp ξ * b - (1 + ω * t) * P ≤ ω * (t ^ 2 * sA / (2 * η)) := by
    have h1 := mul_le_mul_of_nonneg_left hsq (mul_nonneg hω0 hω1')
    have h2 : ω * (1 - ω) * (t ^ 2 * sA / (2 * η)) ≤ ω * (t ^ 2 * sA / (2 * η)) := by
      have : 0 ≤ ω * (t ^ 2 * sA / (2 * η)) := by positivity
      nlinarith
    linarith
  -- the ratio
  have hN0 : 0 < (1 - ω) * a + ω * Real.exp ξ * b := by
    rcases eq_or_lt_of_le hω0 with h | h
    · rw [← h]; simp [ha0]
    · have := Real.exp_pos ξ
      have : 0 < ω * Real.exp ξ * b := by positivity
      have : 0 ≤ (1 - ω) * a := mul_nonneg hω1' ha0.le
      linarith
  set N := (1 - ω) * a + ω * Real.exp ξ * b with hN
  have hratio : N / P - 1 ≤ ω * t + ω * (t ^ 2 * sA / (2 * η * sη)) := by
    rw [div_sub_one hP0.ne']
    have k2 : (N - P) / P ≤ (ω * t * P + ω * (t ^ 2 * sA / (2 * η))) / P :=
      div_le_div_of_nonneg_right (by linarith [hnum2]) hP0.le
    have k3 : (ω * t * P + ω * (t ^ 2 * sA / (2 * η))) / P =
        ω * t + ω * (t ^ 2 * sA / (2 * η)) / P := by
      rw [add_div, mul_div_assoc, div_self hP0.ne', mul_one]
    have hX : 0 ≤ ω * (t ^ 2 * sA / (2 * η)) := by positivity
    have k4 : ω * (t ^ 2 * sA / (2 * η)) / P ≤ ω * (t ^ 2 * sA / (2 * η)) / sη :=
      div_le_div_of_nonneg_left hX hsη0 hPη
    have k5 : ω * (t ^ 2 * sA / (2 * η)) / sη = ω * (t ^ 2 * sA / (2 * η * sη)) := by ring
    linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hN0 hP0)
  -- final numerical comparison
  have hηs0 : 0 < η * sη := by positivity
  have hfin : ω * t + ω * (t ^ 2 * sA / (2 * η * sη)) ≤
      ω * ξ + 4 / (η * sη) * ω * ξ ^ 2 := by
    have e1 : ω * t ≤ ω * (ξ + ξ ^ 2) := mul_le_mul_of_nonneg_left ht1 hω0
    have ht4 : t ^ 2 ≤ (2 * ξ) ^ 2 := pow_le_pow_left₀ ht0 ht2 2
    have hη3 : η * sη ≤ 1 / 4 * (1 / 2) := mul_le_mul hη1 hsη_le hsη0.le (by norm_num)
    set K := 1 / (η * sη) with hK
    have hK8 : 8 ≤ K := by
      rw [hK, le_div_iff₀ hηs0]
      linarith
    have e2 : t ^ 2 * sA ≤ (2 * ξ) ^ 2 * (9 / 8) :=
      mul_le_mul ht4 hsA_le hsA0.le (by positivity)
    have e3 : t ^ 2 * sA / (2 * η * sη) ≤ (2 * ξ) ^ 2 * (9 / 8) / (2 * η * sη) :=
      div_le_div_of_nonneg_right e2 (by positivity)
    have e4 : (2 * ξ) ^ 2 * (9 / 8) / (2 * η * sη) = 9 / 4 * ξ ^ 2 * K := by
      rw [hK]
      ring
    have e5 : 4 / (η * sη) * ω * ξ ^ 2 = 4 * K * (ω * ξ ^ 2) := by
      rw [hK]
      ring
    have e6 : ω * (t ^ 2 * sA / (2 * η * sη)) ≤ ω * (9 / 4 * ξ ^ 2 * K) := by
      rw [← e4]
      exact mul_le_mul_of_nonneg_left e3 hω0
    have h0 : 0 ≤ ω * ξ ^ 2 := by positivity
    have e7 : ω * ξ ^ 2 * 8 ≤ ω * ξ ^ 2 * K := mul_le_mul_of_nonneg_left hK8 h0
    have f1 : ω * (ξ + ξ ^ 2) = ω * ξ + ω * ξ ^ 2 := by ring
    have f2 : ω * (9 / 4 * ξ ^ 2 * K) = 9 / 4 * (ω * ξ ^ 2 * K) := by ring
    have f3 : 4 * K * (ω * ξ ^ 2) = 4 * (ω * ξ ^ 2 * K) := by ring
    rw [e5, f3]
    linarith
  linarith

/-! ## Constants in `thm:residualfused` and `prop:residualfusedrate` -/

/-- Paper: `thm:residualfused` (tanh_residual_fused.tex): with `κ = 3 c_0 = 51/16`,
`(κ - 1)/2 = 35/32` and `(5 - κ)/2 = 29/32`. -/
theorem residualfused_exponents :
    ((3 : ℝ) * (17 / 16) - 1) / 2 = 35 / 32 ∧ (5 - (3 : ℝ) * (17 / 16)) / 2 = 29 / 32 := by
  constructor <;> norm_num

/-- Paper: proof of `thm:residualfused` (tanh_residual_fused.tex): with
`κ = 3 c_0`, the bound `d ≥ r^2/3 - r^4/5` (a declared stand-in here; it is
`ExactSampling.ResidualDepth.tanh_le_quintic`) gives
`α c_0 r^2 ≤ κ α d + (κ/5) α r^4`. -/
theorem weighted_local_step (α c₀ r d : ℝ) (hα : 0 ≤ α) (hc : 0 ≤ c₀)
    (hd : r ^ 2 / 3 - r ^ 4 / 5 ≤ d) :
    α * c₀ * r ^ 2 ≤ 3 * c₀ * α * d + 3 * c₀ / 5 * α * r ^ 4 := by
  have := mul_le_mul_of_nonneg_left hd (mul_nonneg (by positivity : (0 : ℝ) ≤ 3 * c₀) hα)
  nlinarith

/-- Paper: proof of `thm:residualfused` (tanh_residual_fused.tex): at `η = 1/64`,
`1/8 ≤ φ ≤ √65/8` on `[-1, 1]`. -/
theorem phi_bounds_fixed {v : ℝ} (hv : |v| ≤ 1) :
    1 / 8 ≤ phi (1 / 64) v ∧ phi (1 / 64) v ≤ Real.sqrt 65 / 8 := by
  constructor
  · have h := sqrt_le_phi (η := 1 / 64) hv
    have e : Real.sqrt (1 / 64) = 1 / 8 := by
      rw [show (1 / 64 : ℝ) = (1 / 8) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  · have h := phi_le_sqrt (1 / 64) v
    have e : Real.sqrt (1 + 1 / 64) = Real.sqrt 65 / 8 := by
      rw [show (1 + 1 / 64 : ℝ) = 65 / 8 ^ 2 by norm_num, Real.sqrt_div' _ (by norm_num),
        Real.sqrt_sq (by norm_num)]
    linarith

/-- Paper: proof of `thm:residualfused` (tanh_residual_fused.tex): from the declared
stand-in `r ≥ (1 + x)^{-1/2}` (`eq:resradiuslower` with `r_j ≥ R_j`),
`r^{-p} ≤ (1 + x)^{p/2}` for `p ≥ 0`; with `p = κ - 1 = 35/16` this gives
`r^{1-κ} ≤ (1 + αD)^{35/32}`, and with `p = 5 - κ = 29/16` it gives
`r_K^{κ-5} ≤ (1 + αK)^{29/32}`. -/
theorem rpow_neg_le_of_radius {r x p : ℝ} (hx : 0 ≤ x) (hp : 0 ≤ p)
    (hr : 1 / Real.sqrt (1 + x) ≤ r) : r ^ (-p) ≤ (1 + x) ^ (p / 2) := by
  have hs : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.mpr (by linarith)
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  have h1 : r ^ (-p) ≤ (1 / Real.sqrt (1 + x)) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hr (by linarith)
  have h2 : (1 / Real.sqrt (1 + x)) ^ (-p) = (1 + x) ^ (p / 2) := by
    rw [one_div, Real.inv_rpow hs.le, Real.rpow_neg hs.le, inv_inv, Real.sqrt_eq_rpow,
      ← Real.rpow_mul (by linarith)]
    ring_nf
  linarith

/-- Paper: `prop:residualfusedrate` (tanh_residual_fused.tex). For
`0 ≤ x ≤ 2^{-12}` and `ξ = (17/16)x + 2^{22}x^2`: `ξ ≤ 1026 x < 1`, and the mixing
estimate with `η = 1/64` (so `4 η^{-3/2} = 2048`) gives
`ξ + 2048 ξ^2 ≤ (17/16)x + 2^{32}x^2`, using `2^{22} + 2048·1026^2 < 2^{32}`. -/
theorem residualfused_local_rate {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ (1 / 2) ^ 12) :
    (17 / 16) * x + 2 ^ 22 * x ^ 2 ≤ 1026 * x ∧ 1026 * x < 1 ∧
      (17 / 16) * x + 2 ^ 22 * x ^ 2 + 2048 * ((17 / 16) * x + 2 ^ 22 * x ^ 2) ^ 2 ≤
        (17 / 16) * x + 2 ^ 32 * x ^ 2 := by
  have hxs : x ≤ 1 / 4096 := by norm_num at hx; linarith
  have h1 : (17 / 16) * x + 2 ^ 22 * x ^ 2 ≤ 1026 * x := by nlinarith
  refine ⟨h1, by linarith, ?_⟩
  have hξ0 : 0 ≤ (17 / 16) * x + 2 ^ 22 * x ^ 2 := by positivity
  have h2 : ((17 / 16) * x + 2 ^ 22 * x ^ 2) ^ 2 ≤ (1026 * x) ^ 2 :=
    pow_le_pow_left₀ hξ0 h1 2
  have h3 : (2 : ℝ) ^ 22 + 2048 * 1026 ^ 2 < 2 ^ 32 := by norm_num
  nlinarith [sq_nonneg x]

/-- Paper: `prop:residualfusedrate` (tanh_residual_fused.tex): the derivative of
`P(x) = (17/16)x + 2^{32}x^2` is below `H_0 = 2^{22}` on `[0, 2^{-12}]`. -/
theorem residualfused_derivative_bound {x : ℝ} (hx : x ≤ (1 / 2) ^ 12) :
    17 / 16 + 2 * 2 ^ 32 * x < 2 ^ 22 := by
  norm_num at hx
  nlinarith

/-- Paper: `prop:residualfusedrate` (tanh_residual_fused.tex): the numerical step
`11 δ + 7/J < 2^{-12}` for `δ ≤ 2^{-16}` and `J = 2^{28}`. The bound
`x_j ≤ 11 δ + 7/J` itself (from `lem:residualsuperradius` and the rounding estimate)
is not formalized here. -/
theorem residualfused_cutoff_square {δ : ℝ} (hδ : δ ≤ (1 / 2) ^ 16) :
    11 * δ + 7 / 2 ^ 28 < (1 / 2) ^ 12 := by
  norm_num at hδ ⊢
  linarith

/-- Paper: `prop:residualfusedrate` (tanh_residual_fused.tex): with
`Γ_s = (17/16)u_*^2 + 2^{32}u_*^4` and `3δ ≤ u_*^2 ≤ 3δ + (3/2)δ^2`, `0 < δ ≤ 2^{-16}`,
one has `(51/16)δ ≤ Γ_s ≤ (51/16)δ + 2^{36}δ^2`. The bounds on `u_*` are the
fixed-point inequalities proved elsewhere in the paper. -/
theorem residualfused_rate_bounds {δ U : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (1 / 2) ^ 16)
    (hU1 : 3 * δ ≤ U) (hU2 : U ≤ 3 * δ + 3 / 2 * δ ^ 2) :
    51 / 16 * δ ≤ 17 / 16 * U + 2 ^ 32 * U ^ 2 ∧
      17 / 16 * U + 2 ^ 32 * U ^ 2 ≤ 51 / 16 * δ + 2 ^ 36 * δ ^ 2 := by
  have hU0 : 0 ≤ U := by linarith
  constructor
  · nlinarith [sq_nonneg U]
  · have hδ1 : δ ≤ 1 / 4 := by norm_num at hδ; linarith
    have hU3 : U ≤ 25 / 8 * δ := by nlinarith
    have hU4 : U ^ 2 ≤ (25 / 8 * δ) ^ 2 := pow_le_pow_left₀ hU0 hU3 2
    have h2 : (51 / 32 + 2 ^ 32 * (25 / 8) ^ 2 : ℝ) ≤ 2 ^ 36 := by norm_num
    nlinarith [sq_nonneg δ]

/-- Paper: `prop:residualfusedrate` (tanh_residual_fused.tex), the geometric
generation sum: `α / (1 - e^{-αΓ}) ≤ α + 1/Γ` for `α, Γ > 0`. -/
theorem geometric_generation_le {α Γ : ℝ} (hα : 0 < α) (hΓ : 0 < Γ) :
    α / (1 - Real.exp (-(α * Γ))) ≤ α + 1 / Γ := by
  have hx : 0 < α * Γ := mul_pos hα hΓ
  have hexp : Real.exp (-(α * Γ)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hden : 0 < 1 - Real.exp (-(α * Γ)) := by linarith
  rw [div_le_iff₀ hden]
  have key : (α * Γ + 1) * Real.exp (-(α * Γ)) ≤ 1 := by
    have h := Real.add_one_le_exp (α * Γ)
    have hpos := Real.exp_pos (α * Γ)
    have e : Real.exp (-(α * Γ)) = 1 / Real.exp (α * Γ) := by rw [Real.exp_neg, one_div]
    rw [e, mul_one_div, div_le_one hpos]
    exact h
  have e2 : (α + 1 / Γ) * (1 - Real.exp (-(α * Γ))) =
      (α * Γ + 1 - (α * Γ + 1) * Real.exp (-(α * Γ))) / Γ := by field_simp
  rw [e2, le_div_iff₀ hΓ]
  nlinarith

/-- Paper: `prop:residualfusedrate` (tanh_residual_fused.tex): the cancellation
`α / (1 - λ_α) = 1/(1 - λ_s)` with `λ_α = 1 - α + α λ_s`, which makes the transient
bound uniform in `α`. -/
theorem residual_contraction_cancellation (α lam : ℝ) (ha : α ≠ 0) (hl : 1 - lam ≠ 0) :
    α / (1 - ((1 - α) + α * lam)) = 1 / (1 - lam) := by
  have hden : 1 - ((1 - α) + α * lam) = α * (1 - lam) := by ring
  rw [hden]
  field_simp

/-- Paper: proof of `thm:residualfused` (tanh_residual_fused.tex): with
`J = 2^{28}`, `2^{23} · 14 / J = 7/16 < 1`; `J + 2 ≤ 2^{29}`;
`(J+2)^{29/32} < 2^{27}`; `e^{24} < 2^{36}`; hence
`16 · 64 e^{24} (J+2)^{29/32} < 2^{76}`. -/
theorem residualfused_constants :
    (2 : ℝ) ^ 23 * 14 / 2 ^ 28 = 7 / 16 ∧ (2 : ℝ) ^ 28 + 2 ≤ 2 ^ 29 ∧
      ((2 : ℝ) ^ 28 + 2) ^ ((29 : ℝ) / 32) < 2 ^ 27 ∧ Real.exp 24 < 2 ^ 36 ∧
      16 * (64 * Real.exp 24 * ((2 : ℝ) ^ 28 + 2) ^ ((29 : ℝ) / 32)) < 2 ^ 76 := by
  have hJ : ((2 : ℝ) ^ 28 + 2) ^ ((29 : ℝ) / 32) < 2 ^ 27 := by
    have h1 : ((2 : ℝ) ^ 28 + 2) ^ ((29 : ℝ) / 32) ≤ ((2 : ℝ) ^ 29) ^ ((29 : ℝ) / 32) :=
      Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)
    have h2 : ((2 : ℝ) ^ 29) ^ ((29 : ℝ) / 32) = (2 : ℝ) ^ ((29 : ℝ) * (29 / 32)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    have h3 : (2 : ℝ) ^ ((29 : ℝ) * (29 / 32)) < (2 : ℝ) ^ ((27 : ℕ) : ℝ) :=
      (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr (by norm_num)
    rw [Real.rpow_natCast] at h3
    linarith
  have hE : Real.exp 24 < 2 ^ 36 := by
    have h := Real.exp_one_lt_d9
    have e : Real.exp 24 = Real.exp 1 ^ 24 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [e]
    have : Real.exp 1 ^ 24 < 2.7182818286 ^ 24 :=
      pow_lt_pow_left₀ h (Real.exp_pos 1).le (by norm_num)
    linarith [show (2.7182818286 : ℝ) ^ 24 < 2 ^ 36 by norm_num]
  refine ⟨by norm_num, by norm_num, hJ, hE, ?_⟩
  have h0 : 0 ≤ ((2 : ℝ) ^ 28 + 2) ^ ((29 : ℝ) / 32) := by positivity
  have hE0 : 0 < Real.exp 24 := Real.exp_pos 24
  have : Real.exp 24 * ((2 : ℝ) ^ 28 + 2) ^ ((29 : ℝ) / 32) < 2 ^ 36 * 2 ^ 27 :=
    mul_lt_mul'' hE hJ hE0.le h0
  nlinarith

/-- Paper: `prop:residualfusedrate` (tanh_residual_fused.tex), the numerical
inequality `7000 · 2^{-16} (J+1) + 30 + log 10 + (5/2) log(J+2) < 2^{26}` with
`J = 2^{28}`. -/
theorem residualfused_cutoff_exponent :
    7000 * (1 / 2) ^ 16 * ((2 : ℝ) ^ 28 + 1) + 30 + Real.log 10 +
      5 / 2 * Real.log ((2 : ℝ) ^ 28 + 2) < 2 ^ 26 := by
  have h10 : Real.log 10 ≤ 9 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
    linarith
  have hJ : Real.log ((2 : ℝ) ^ 28 + 2) ≤ 29 := by
    have h1 : Real.log ((2 : ℝ) ^ 28 + 2) ≤ Real.log ((2 : ℝ) ^ 29) :=
      Real.log_le_log (by positivity) (by norm_num)
    rw [Real.log_pow] at h1
    have := Real.log_two_lt_d9
    push_cast at h1
    nlinarith
  norm_num at hJ ⊢
  linarith

end ExactSampling.Potential
