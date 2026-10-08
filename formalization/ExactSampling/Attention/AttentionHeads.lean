import Mathlib

/-!
# Bounded heads, the two-key query law, and the cached scan

This module formalizes quantitative steps of four results in the attention appendix:
`thm:quadraticscaledhead` (`attention_head.tex`), `lem:lazyattentionblocks`
(`attention_primitives.tex`, part of `thm:attentionprimitive` behind `thm:main-attention`),
`thm:rankonequerylaw` and the odd-length case of `thm:rankone-worstlaw`
(`attention_query_law.tex`), and `lem:newcachescan` (`attention_finite_bits.tex`).

Formalized here:
* `tanh` calculus: `tanh' = 1 - tanh²`, `tanh` is `1`-Lipschitz and strictly increasing, and
  `tanh` and `tanh ∘ tanh` are star-shaped on `[0,∞)`: `λ f(y) ≤ f(λy)` for `λ ∈ [0,1]`;
* `thm:quadraticscaledhead`: the logistic coin `(1 + tanh(z/2 - 1))/2 = e^{z-2}/(1+e^{z-2})`,
  the bound `q ≤ 1/(1+e) < 1/3`, the geometric product `∑_k 2^{-k}(2q)^k = q/(1-q) = e^{z-2}`,
  `E K = 2`, the trial success `≥ e^{-3}`, the exact softmax law of the race, and the source
  constants `R(1+R/2) ≤ 3R²/2` and `171e³R² < 4096R²`;
* `lem:lazyattentionblocks`: `(e^{2A}-1)/(1-e^{-1}) + e^{2A} < 3e^{2A}`;
* `thm:rankonequerylaw`: the two-key attention value `tanh(βM)`, `F₃(β) ≥ β/8` on `[0,1]`, the
  integrand bound `Z F₃(κZ) ≥ d/32` on `|Z| ≥ 1/2`, its nonnegativity, the arithmetic of the
  Paley–Zygmund and Cauchy–Schwarz constants, and the combination of the two ranges into the
  universal constant `1/65536` (taking the probe-cost lower bounds as hypotheses);
* `thm:rankone-worstlaw`: the odd-length attenuation `|u| ≥ (2/3)|tanh(βM)|` and the transfer
  through the concave map `tanh ∘ tanh`;
* `lem:newcachescan`: shifted weights `w_j ≤ 1` with `Z ≥ 1`, the division enclosure of width
  `≤ 2^{-t-3}` at `P = t + ⌈log₂(T+1)⌉ + 8` (any sign of the numerator), and the boundary
  union bound
  `10T²2^{-P} ≤ 2^{2-t}` at `P = t + 2⌈log₂(T+1)⌉ + 8`.

Not formalized: the Bernoulli factories themselves (Huber's linear factory, the tanh factories)
and hence the factory upper bounds of `thm:rankonequerylaw` and `thm:rankone-worstlaw`; Poisson
generation; for the lower bounds, the total-variation coupling argument for `β ≤ 1`, the
transcript inequality `E₀ Q ≥ H'(0)²` (`lem:transcript`), the score identity
`H'(0) = E₀[F₃(βS/n) S]`, the Rademacher fourth moment `E Z⁴ = 3 - 2/n`, and the Paley–Zygmund
inequality itself (only its numerical constants are checked; the resulting probe-cost lower
bounds enter `query_law_combination` as hypotheses); and bit costs.
-/

open Filter Finset
open scoped BigOperators Topology

namespace ExactSampling.AttentionHeads

/-! ## `tanh` calculus -/

section Tanh

/-- `tanh' = 1 - tanh²`. Auxiliary for the `tanh` estimates of `thm:rankonequerylaw`
(attention_query_law.tex) and `lem:newcachescan` (attention_finite_bits.tex). -/
theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hfun : Real.tanh = fun y => Real.sinh y / Real.cosh y := by
    funext y; exact Real.tanh_eq_sinh_div_cosh y
  rw [hfun]
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  convert h using 1
  have hc := (Real.cosh_pos x).ne'
  show 1 - (Real.sinh x / Real.cosh x) ^ 2 = _
  field_simp

/-- `tanh` is `1`-Lipschitz. Paper: `lem:newcachescan` (attention_finite_bits.tex), "The two
tanh maps are 1-Lipschitz". -/
theorem tanh_lipschitz (x y : ℝ) : |Real.tanh x - Real.tanh y| ≤ |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Real.tanh)
    (f' := fun z => 1 - Real.tanh z ^ 2) (s := Set.univ) (x := y) (y := x) (C := 1)
    (fun z _ => (hasDerivAt_tanh z).hasDerivWithinAt)
    (fun z _ => by
      rw [Real.norm_eq_abs, abs_le]
      have := Real.tanh_sq_lt_one z
      constructor <;> nlinarith [sq_nonneg (Real.tanh z)])
    convex_univ trivial trivial
  simpa [Real.norm_eq_abs] using h

/-- `tanh` is strictly increasing. Auxiliary for `thm:rankonequerylaw`
(attention_query_law.tex). -/
theorem tanh_strictMono : StrictMono Real.tanh :=
  strictMono_of_deriv_pos fun x => by
    rw [(hasDerivAt_tanh x).deriv]; have := Real.tanh_sq_lt_one x; linarith

/-- Auxiliary: `tanh x ≥ 0` for `x ≥ 0`. Supports `thm:rankonequerylaw`
(attention_query_law.tex). -/
lemma tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  have := tanh_strictMono.monotone hx; simpa using this

/-- `tanh x ≥ x/2` on `[0,1]`. Paper: `thm:rankonequerylaw` (attention_query_law.tex). -/
theorem tanh_ge_half {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x / 2 ≤ Real.tanh x := by
  have he := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * x by linarith)
  have hpos : 0 < Real.exp (2 * x) + 1 := by positivity
  have htanh : Real.tanh x = (Real.exp (2 * x) - 1) / (Real.exp (2 * x) + 1) := by
    rw [Real.tanh_eq]
    have h2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by rw [← Real.exp_add]; ring_nf
    rw [h2, Real.exp_neg]
    have := Real.exp_pos x
    field_simp
  rw [htanh, le_div_iff₀ hpos]
  nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1), mul_nonneg hx0 hx0]

/-- Star shape of `tanh`: `λ tanh y ≤ tanh(λy)` for `λ ∈ [0,1]` and `y ≥ 0` (implied by concavity
of `tanh` on `[0,∞)` and `tanh 0 = 0`; proved here from the derivative).
Paper: `thm:rankone-worstlaw`
(attention_query_law.tex), "The map `φ(u) = tanh(tanh u)` is increasing and concave". -/
theorem tanh_star (lam y : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hy : 0 ≤ y) :
    lam * Real.tanh y ≤ Real.tanh (lam * y) := by
  set g : ℝ → ℝ := fun y => Real.tanh (lam * y) - lam * Real.tanh y with hg
  have hderiv : ∀ y, HasDerivAt g (lam * (Real.tanh y ^ 2 - Real.tanh (lam * y) ^ 2)) y := by
    intro y
    have h1 := (hasDerivAt_tanh (lam * y)).comp y ((hasDerivAt_id y).const_mul lam)
    have h2 := (hasDerivAt_tanh y).const_mul lam
    convert h1.sub h2 using 1
    · funext z; simp [hg]
    · ring
  have hmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun y _ => (hderiv y).continuousAt.continuousWithinAt
    · exact fun y _ => (hderiv y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hderiv y).deriv]
      have hy0 : 0 ≤ y := le_of_lt hy
      have h1 : Real.tanh (lam * y) ≤ Real.tanh y :=
        tanh_strictMono.monotone (by nlinarith)
      have h2 : 0 ≤ Real.tanh (lam * y) := tanh_nonneg (mul_nonneg hl0 hy0)
      have : Real.tanh (lam * y) ^ 2 ≤ Real.tanh y ^ 2 := by nlinarith
      nlinarith
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
  simp [hg] at this
  linarith

/-- Star shape of `tanh ∘ tanh` on `[0,∞)`. Paper: `thm:rankone-worstlaw`
(attention_query_law.tex). -/
theorem tanh_tanh_star (lam y : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hy : 0 ≤ y) :
    lam * Real.tanh (Real.tanh y) ≤ Real.tanh (Real.tanh (lam * y)) := by
  have h1 := tanh_star lam y hl0 hl1 hy
  have h2 := tanh_star lam (Real.tanh y) hl0 hl1 (tanh_nonneg hy)
  exact h2.trans (tanh_strictMono.monotone h1)

end Tanh

/-! ## Bounded logits from attenuated signs (`thm:quadraticscaledhead`) -/

section QuadraticHead

/-- The logistic coin: `(1 + tanh(z/2 - 1))/2 = e^{z-2}/(1 + e^{z-2})`.
Paper: `thm:quadraticscaledhead` (attention_head.tex). -/
theorem logistic_coin (z : ℝ) :
    (1 + Real.tanh (z / 2 - 1)) / 2 = Real.exp (z - 2) / (1 + Real.exp (z - 2)) := by
  rw [Real.tanh_eq]
  have hx : 0 < Real.exp (z / 2 - 1) := Real.exp_pos _
  have h2 : Real.exp (z - 2) = Real.exp (z / 2 - 1) * Real.exp (z / 2 - 1) := by
    rw [← Real.exp_add]; ring_nf
  rw [h2, Real.exp_neg]
  field_simp
  ring

/-- For `z ≤ 1`, the logistic coin satisfies `q ≤ 1/(1+e) < 1/3`.
Paper: `thm:quadraticscaledhead` (attention_head.tex). -/
theorem logistic_small (z : ℝ) (hz : z ≤ 1) :
    Real.exp (z - 2) / (1 + Real.exp (z - 2)) ≤ 1 / (1 + Real.exp 1) ∧
      1 / (1 + Real.exp 1) < 1 / 3 := by
  have he : 2 < Real.exp 1 := by
    have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num); linarith
  have hx : Real.exp (z - 2) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have hinv : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
  have hxpos : 0 < Real.exp (z - 2) := Real.exp_pos _
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.exp_pos 1]
  · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith

/-- The geometric product: drawing `K ≥ 1` with `Pr(K = k) = 2^{-k}` and testing `K` amplified
coins of bias `2q` succeeds with probability `∑_k 2^{-k}(2q)^k = q/(1-q)`, and with the logistic
coin this equals `e^{z-2}`. Paper: `thm:quadraticscaledhead` (attention_head.tex). -/
theorem geometric_success (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun k : ℕ => (2 : ℝ)⁻¹ ^ (k + 1) * (2 * q) ^ (k + 1)) (q / (1 - q)) := by
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left q
  convert h using 1
  · funext k; rw [← mul_pow, ← mul_assoc, inv_mul_cancel₀ (two_ne_zero), one_mul, pow_succ]; ring
  · field_simp

/-- With `q = e^{z-2}/(1+e^{z-2})`, `q/(1-q) = e^{z-2}`.
Paper: `thm:quadraticscaledhead` (attention_head.tex). -/
theorem logistic_odds (z : ℝ) :
    (Real.exp (z - 2) / (1 + Real.exp (z - 2))) / (1 - Real.exp (z - 2) / (1 + Real.exp (z - 2)))
      = Real.exp (z - 2) := by
  have hx : 0 < Real.exp (z - 2) := Real.exp_pos _
  field_simp
  ring

/-- `E K = ∑_{k≥1} k 2^{-k} = 2`, which bounds the expected number of tested amplified coins.
Paper: `thm:quadraticscaledhead` (attention_head.tex). -/
theorem expected_K : HasSum (fun k : ℕ => ((k : ℝ) + 1) * (2 : ℝ)⁻¹ ^ (k + 1)) 2 := by
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := 2⁻¹) (by norm_num)
  have h2 := hasSum_geometric_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
  have h3 := (h1.add h2).mul_left 2⁻¹
  convert h3 using 1
  · funext k; rw [pow_succ]; ring
  · norm_num

/-- A race trial with logits `z ≥ -1` succeeds with probability at least `e^{-3}`.
Paper: `thm:quadraticscaledhead` (attention_head.tex). -/
theorem trial_success (z : ℝ) (hz : -1 ≤ z) : Real.exp (-3) ≤ Real.exp (z - 2) :=
  Real.exp_le_exp.mpr (by linarith)

/-- The race over categories returns the softmax law: proposing a category uniformly from `K`
and accepting with probability `e^{z_i - 2}`, the first accepted category is `i` with
probability `e^{z_i}/∑_j e^{z_j}`; the common factor `e^{-2}` cancels.
Paper: `thm:quadraticscaledhead` (attention_head.tex). -/
theorem race_softmax_law {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℝ) (hz : ∀ j, z j ≤ 1)
    (i : ι) :
    HasSum (fun m : ℕ => (1 - (∑ j, Real.exp (z j - 2)) / Fintype.card ι) ^ m *
        (Real.exp (z i - 2) / Fintype.card ι)) (Real.exp (z i) / ∑ j, Real.exp (z j)) := by
  set K := (Fintype.card ι : ℝ)
  have hK : 0 < K := Nat.cast_pos.mpr Fintype.card_pos
  set s := (∑ j, Real.exp (z j - 2)) / K
  have hs0 : 0 < s := div_pos (Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty) hK
  have hs1 : s ≤ 1 := by
    rw [div_le_one hK]
    calc ∑ j, Real.exp (z j - 2) ≤ ∑ _j : ι, (1 : ℝ) := by
          apply Finset.sum_le_sum; intro j _
          exact Real.exp_le_one_iff.mpr (by linarith [hz j])
      _ = K := by simp [K]
  have hgeom := hasSum_geometric_of_lt_one (r := 1 - s) (by linarith) (by linarith)
  have h := hgeom.mul_right (Real.exp (z i - 2) / K)
  have hval : (1 - (1 - s))⁻¹ * (Real.exp (z i - 2) / K) =
      Real.exp (z i) / ∑ j, Real.exp (z j) := by
    rw [sub_sub_cancel]
    have hsum : ∑ j, Real.exp (z j - 2) = (∑ j, Real.exp (z j)) * Real.exp (-2) := by
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Real.exp_add]; ring_nf
    have hzi : Real.exp (z i - 2) = Real.exp (z i) * Real.exp (-2) := by
      rw [← Real.exp_add]; ring_nf
    simp only [s]
    rw [hsum, hzi]
    have h1 : 0 < ∑ j, Real.exp (z j) := Finset.sum_pos (fun j _ => Real.exp_pos _)
      Finset.univ_nonempty
    have h2 : 0 < Real.exp (-2) := Real.exp_pos _
    field_simp
  rwa [hval] at h

/-- Source constants: `R(1 + R/2) ≤ 3R²/2` for `R ≥ 1`, and the total
`114 e³ (3R²/2) = 171 e³ R² < 4096 R²` (using `e < 11/4`, so `e³ < 21`).
Paper: `thm:quadraticscaledhead` (attention_head.tex). -/
theorem head_constants (R : ℝ) (hR : 1 ≤ R) :
    R * (1 + R / 2) ≤ 3 * R ^ 2 / 2 ∧ 57 * 2 = 114 ∧
      114 * Real.exp 1 ^ 3 * (3 * R ^ 2 / 2) = 171 * Real.exp 1 ^ 3 * R ^ 2 ∧
      171 * Real.exp 1 ^ 3 * R ^ 2 < 4096 * R ^ 2 := by
  have he : Real.exp 1 < 11 / 4 := by
    have := Real.exp_one_lt_d9; norm_num at this; linarith
  have he3 : Real.exp 1 ^ 3 < 21 := by
    calc Real.exp 1 ^ 3 < (11 / 4 : ℝ) ^ 3 := by
          gcongr
      _ < 21 := by norm_num
  refine ⟨by nlinarith, by norm_num, by ring, ?_⟩
  have hR2 : 0 < R ^ 2 := by positivity
  nlinarith

end QuadraticHead

/-! ## Reached Poisson intervals (`lem:lazyattentionblocks`) -/

/-- `(1 - e^{-1})^{-1} < 2`, so the reached unit intervals and final intervals number fewer than
`(e^{2A} - 1)/(1 - e^{-1}) + e^{2A} < 3e^{2A}` in expectation.
Paper: `lem:lazyattentionblocks` (attention_primitives.tex). -/
theorem lazy_blocks (A : ℝ) (hA : 0 ≤ A) :
    (1 - Real.exp (-1))⁻¹ < 2 ∧
      (Real.exp (2 * A) - 1) / (1 - Real.exp (-1)) + Real.exp (2 * A) < 3 * Real.exp (2 * A) := by
  have he : Real.exp (-1) < 1 / 2 := by
    have h := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    have hinv : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-1)]
  have hpos : 0 < 1 - Real.exp (-1) := by linarith
  have hE : 1 ≤ Real.exp (2 * A) := Real.one_le_exp (by linarith)
  constructor
  · rw [inv_lt_comm₀ hpos (by norm_num)]; linarith
  · rw [div_add' _ _ _ hpos.ne', div_lt_iff₀ hpos]
    nlinarith [Real.exp_pos (-1)]

/-! ## The two-key query law (`thm:rankonequerylaw`, `thm:rankone-worstlaw`) -/

section TwoKey

/-- Two-key attention: with `c ≥ 1` copies of each key `±1` with values `±1`, scores `±s`
(here `s = βM`), the attention value is `tanh s`.
Paper: `thm:rankonequerylaw` (attention_query_law.tex). -/
theorem two_key_attention (c s : ℝ) (hc : 0 < c) :
    (c * Real.exp s * 1 + c * Real.exp (-s) * (-1)) / (c * Real.exp s + c * Real.exp (-s)) =
      Real.tanh s := by
  rw [Real.tanh_eq]
  have h1 := Real.exp_pos s
  have h2 := Real.exp_pos (-s)
  field_simp
  ring

/-- Odd cache length: one extra zero key with value zero attenuates the attention value by a
factor in `[2/3, 1]`: `u = λ tanh s` with `2/3 ≤ λ ≤ 1` for `c ≥ 1` pairs.
Paper: `thm:rankone-worstlaw` (attention_query_law.tex). -/
theorem odd_attenuation (c s : ℝ) (hc : 1 ≤ c) :
    ∃ lam : ℝ, 2 / 3 ≤ lam ∧ lam ≤ 1 ∧
      (c * Real.exp s - c * Real.exp (-s)) / (c * Real.exp s + c * Real.exp (-s) + 1) =
        lam * Real.tanh s := by
  set E := Real.exp s + Real.exp (-s) with hE
  have h1 := Real.exp_pos s
  have h2 := Real.exp_pos (-s)
  have hE2 : 2 ≤ E := by
    have hprod : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [sq_nonneg (Real.exp s - Real.exp (-s))]
  refine ⟨c * E / (c * E + 1), ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_one (by positivity)]; linarith
  · rw [Real.tanh_eq]
    field_simp
    ring

/-- Transfer of the attenuation through `tanh ∘ tanh`: if `u = λ y` with `λ ∈ [2/3, 1]`, then
`|tanh(tanh u)| ≥ (2/3)|tanh(tanh y)|`.
Paper: `thm:rankone-worstlaw` (attention_query_law.tex). -/
theorem attenuated_output (lam y : ℝ) (hl0 : 2 / 3 ≤ lam) :
    2 / 3 * |Real.tanh (Real.tanh y)| ≤ |Real.tanh (Real.tanh (lam * y))| := by
  have hodd : ∀ x, Real.tanh (Real.tanh (-x)) = -Real.tanh (Real.tanh x) := by
    intro x; rw [Real.tanh_neg, Real.tanh_neg]
  have hpos : ∀ x, 0 ≤ x → 0 ≤ Real.tanh (Real.tanh x) := fun x hx =>
    tanh_nonneg (tanh_nonneg hx)
  have key : ∀ x, 0 ≤ x → 2 / 3 * Real.tanh (Real.tanh x) ≤ Real.tanh (Real.tanh (lam * x)) := by
    intro x hx
    have h1 := tanh_tanh_star (2 / 3) x (by norm_num) (by norm_num) hx
    have h2 : Real.tanh (Real.tanh (2 / 3 * x)) ≤ Real.tanh (Real.tanh (lam * x)) :=
      tanh_strictMono.monotone (tanh_strictMono.monotone (by nlinarith))
    linarith
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg (hpos y hy), abs_of_nonneg (hpos _ (by nlinarith))]
    exact key y hy
  · have h := key (-y) (by linarith)
    rw [hodd, show lam * -y = -(lam * y) by ring, hodd] at h
    rw [abs_of_nonpos (by have := hpos (-y) (by linarith); rw [hodd] at this; linarith),
      abs_of_nonpos (by have := hpos (-(lam * y)) (by nlinarith); rw [hodd] at this; linarith)]
    linarith

/-- `F₃(β) = tanh(tanh(tanh β)) ≥ β/8` on `[0,1]`.
Paper: `thm:rankonequerylaw` (attention_query_law.tex). -/
theorem F3_ge (β : ℝ) (h0 : 0 ≤ β) (h1 : β ≤ 1) :
    β / 8 ≤ Real.tanh (Real.tanh (Real.tanh β)) := by
  have a1 := tanh_ge_half h0 h1
  have t1 : Real.tanh β ≤ 1 := (Real.tanh_lt_one β).le
  have a2 := tanh_ge_half (tanh_nonneg h0) t1
  have t2 : Real.tanh (Real.tanh β) ≤ 1 := (Real.tanh_lt_one _).le
  have a3 := tanh_ge_half (tanh_nonneg (tanh_nonneg h0)) t2
  linarith

/-- The score integrand is nonnegative, and on `|Z| ≥ 1/2` with `κ ≥ d`, `d ∈ [0,1]`, it is at
least `F₃(d/2)/2 ≥ d/32`. Paper: `thm:rankonequerylaw` (attention_query_law.tex). -/
theorem score_integrand (κ d z : ℝ) (hκ : 0 ≤ κ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hdκ : d ≤ κ) :
    0 ≤ z * Real.tanh (Real.tanh (Real.tanh (κ * z))) ∧
      (1 / 2 ≤ |z| → d / 32 ≤ z * Real.tanh (Real.tanh (Real.tanh (κ * z)))) := by
  have F3mono : Monotone fun x => Real.tanh (Real.tanh (Real.tanh x)) :=
    tanh_strictMono.monotone.comp (tanh_strictMono.monotone.comp tanh_strictMono.monotone)
  have hodd : ∀ x, Real.tanh (Real.tanh (Real.tanh (-x))) = -Real.tanh (Real.tanh (Real.tanh x)) :=
    by intro x; rw [Real.tanh_neg, Real.tanh_neg, Real.tanh_neg]
  have hpos : ∀ x, 0 ≤ x → 0 ≤ Real.tanh (Real.tanh (Real.tanh x)) := fun x hx =>
    tanh_nonneg (tanh_nonneg (tanh_nonneg hx))
  -- reduce to `z ≥ 0` by oddness
  have hsym : ∀ z, z * Real.tanh (Real.tanh (Real.tanh (κ * z))) =
      |z| * Real.tanh (Real.tanh (Real.tanh (κ * |z|))) := by
    intro z
    rcases le_total 0 z with hz | hz
    · rw [abs_of_nonneg hz]
    · rw [abs_of_nonpos hz, show κ * -z = -(κ * z) by ring, hodd]; ring
  rw [hsym]
  have habs := abs_nonneg z
  refine ⟨mul_nonneg habs (hpos _ (mul_nonneg hκ habs)), fun hz => ?_⟩
  have h1 : d / 2 ≤ κ * |z| := by nlinarith
  have h2 := F3mono h1
  have h3 := F3_ge (d / 2) (by linarith) (by linarith)
  simp only at h2
  have h4 : 0 ≤ Real.tanh (Real.tanh (Real.tanh (κ * |z|))) := hpos _ (mul_nonneg hκ habs)
  nlinarith

/-- Constant bookkeeping of the lower bound: Paley–Zygmund gives `(1 - 1/4)²/3 = 3/16`, so
`H'(0) ≥ √n (3/16)(d/32) = 3 min{β, √n}/512`, and `(3/512)² ≥ 1/32768`; in the odd case
`(2/3)(3/512) = 1/256` and `(1/256)² = 1/65536`.
Paper: `thm:rankonequerylaw` and `thm:rankone-worstlaw` (attention_query_law.tex). -/
theorem query_law_constants :
    (1 - 1 / 4 : ℝ) ^ 2 / 3 = 3 / 16 ∧ (3 / 16 : ℝ) * (1 / 32) = 3 / 512 ∧
      (1 / 32768 : ℝ) ≤ (3 / 512) ^ 2 ∧ (2 / 3 : ℝ) * (3 / 512) = 1 / 256 ∧
      ((1 : ℝ) / 256) ^ 2 = 1 / 65536 := by
  norm_num

/-- `√n · min{β/√n, 1} = min{β, √n}`. Paper: `thm:rankonequerylaw`
(attention_query_law.tex). -/
theorem sqrt_min (β s : ℝ) (hs : 0 < s) : s * min (β / s) 1 = min β s := by
  rw [mul_min_of_nonneg _ _ hs.le, mul_div_cancel₀ _ hs.ne', mul_one]

/-- Combining the two ranges: for `0 ≤ β ≤ 1` a probe probability at least `F₃(β) ≥ β/8`
gives `Q ≥ min{n, β+β²}/65536`; for `β ≥ 1`, `Q ≥ min{β², n}/32768` gives the same bound
since `β + β² ≤ 2β²`. Paper: `thm:rankonequerylaw` (attention_query_law.tex). -/
theorem query_law_combination (β n Q : ℝ) (hβ : 0 ≤ β) (hn : 0 ≤ n) :
    (β ≤ 1 → β / 8 ≤ Q → min n (β + β ^ 2) / 65536 ≤ Q) ∧
      (1 ≤ β → min (β ^ 2) n / 32768 ≤ Q → min n (β + β ^ 2) / 65536 ≤ Q) := by
  constructor
  · intro h1 hQ
    have : min n (β + β ^ 2) ≤ 2 * β := le_trans (min_le_right _ _) (by nlinarith)
    have : min n (β + β ^ 2) / 65536 ≤ β / 8 := by
      have hm : 0 ≤ min n (β + β ^ 2) := le_min hn (by positivity)
      linarith
    linarith
  · intro h1 hQ
    have hb : β + β ^ 2 ≤ 2 * β ^ 2 := by nlinarith
    have : min n (β + β ^ 2) ≤ 2 * min (β ^ 2) n := by
      rcases le_total (β ^ 2) n with h | h
      · rw [min_eq_left h]; exact le_trans (min_le_right _ _) hb
      · rw [min_eq_right h]
        have hn2 : n ≤ 2 * n := by linarith
        exact le_trans (min_le_left _ _) hn2
    linarith

end TwoKey

/-! ## A finite-bit scan for cached attention (`lem:newcachescan`) -/

section CacheScan

/-- Shifting by the largest score: all weights `w_j = e^{a_j - a_max}` are at most one and their
sum is at least one. Paper: `lem:newcachescan` (attention_finite_bits.tex). -/
theorem shifted_weights {ι : Type*} [Fintype ι] (a : ι → ℝ) (amax : ℝ) (hmax : ∀ j, a j ≤ amax)
    (j0 : ι) (hj0 : a j0 = amax) :
    (∀ j, Real.exp (a j - amax) ≤ 1) ∧ 1 ≤ ∑ j, Real.exp (a j - amax) := by
  refine ⟨fun j => Real.exp_le_one_iff.mpr (by linarith [hmax j]), ?_⟩
  calc (1 : ℝ) = Real.exp (a j0 - amax) := by rw [hj0, sub_self, Real.exp_zero]
    _ ≤ ∑ j, Real.exp (a j - amax) :=
      Finset.single_le_sum (f := fun j => Real.exp (a j - amax)) (fun j _ => (Real.exp_pos _).le)
        (Finset.mem_univ j0)

/-- Interval division for the attention mean: with `|N| ≤ Z`, `Z ≥ 1`, and numerator and
denominator errors at most `δ = T2^{-P}` with `P = t + ⌈log₂(T+1)⌉ + 8` (so `δ ≤ 2^{-t-8}`), every
quotient `n/z` with `|n - N| ≤ δ` and `|z - Z| ≤ δ` lies within `2^{-t-4}` of `N/Z`, for either
sign of `N`; so the quotient enclosure has width at most `2^{-t-3}`.
Paper: `lem:newcachescan` (attention_finite_bits.tex). -/
theorem scan_division_width (N Z δ n z : ℝ) (t : ℕ) (hZ : 1 ≤ Z) (hN : |N| ≤ Z) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ (2 : ℝ)⁻¹ ^ (t + 8)) (hn : |n - N| ≤ δ) (hz : |z - Z| ≤ δ) :
    |n / z - N / Z| ≤ (2 : ℝ)⁻¹ ^ (t + 4) := by
  have hδ1 : δ ≤ 1 / 256 := by
    refine le_trans hδ ?_
    rw [pow_add]
    have : (2 : ℝ)⁻¹ ^ t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h8 : (2 : ℝ)⁻¹ ^ 8 = 1 / 256 := by norm_num
    rw [h8]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) t]
  have hz' := abs_le.mp hz
  have hzpos : 0 < z := by linarith
  have hZpos : 0 < Z := by linarith
  have hid : n / z - N / Z = ((n - N) * Z + N * (Z - z)) / (z * Z) := by
    field_simp; ring
  rw [hid, abs_div, abs_of_pos (mul_pos hzpos hZpos), div_le_iff₀ (mul_pos hzpos hZpos)]
  have hnum : |(n - N) * Z + N * (Z - z)| ≤ 2 * δ * Z := by
    calc |(n - N) * Z + N * (Z - z)| ≤ |(n - N) * Z| + |N * (Z - z)| := abs_add_le _ _
      _ = |n - N| * Z + |N| * |z - Z| := by
          rw [abs_mul, abs_mul, abs_of_pos hZpos, abs_sub_comm Z z]
      _ ≤ δ * Z + Z * δ := by gcongr
      _ = 2 * δ * Z := by ring
  have hpow : (2 : ℝ)⁻¹ ^ (t + 8) = (2 : ℝ)⁻¹ ^ (t + 4) / 16 := by
    rw [show t + 8 = (t + 4) + 4 by ring, pow_add]; ring
  have hδ' : 16 * δ ≤ (2 : ℝ)⁻¹ ^ (t + 4) := by rw [hpow] at hδ; linarith
  have hz1 : 1 / 2 ≤ z := by linarith
  have e1 : 16 * δ * (z * Z) ≤ (2 : ℝ)⁻¹ ^ (t + 4) * (z * Z) :=
    mul_le_mul_of_nonneg_right hδ' (by positivity)
  have e2 : 16 * δ * Z * (1 / 2) ≤ 16 * δ * Z * z :=
    mul_le_mul_of_nonneg_left hz1 (by positivity)
  nlinarith

/-- The index variant: at `P = t + 2⌈log₂(T+1)⌉ + 8` the `T - 1` interior boundaries, each with
enclosure width at most `8T2^{-P}` plus `2^{-P}` on either side, cover measure at most
`10T²2^{-P} ≤ 2^{2-t}`. Paper: `lem:newcachescan` (attention_finite_bits.tex). -/
theorem scan_index_union (T t P : ℕ) (hT : 1 ≤ T)
    (hP : (2 : ℝ) ^ (t + 8) * ((T : ℝ) + 1) ^ 2 ≤ 2 ^ P) :
    ((T : ℝ) - 1) * (8 * T * (2 : ℝ)⁻¹ ^ P + 2 * (2 : ℝ)⁻¹ ^ P) ≤ 10 * T ^ 2 * (2 : ℝ)⁻¹ ^ P ∧
      10 * (T : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ P ≤ 4 * (2 : ℝ)⁻¹ ^ t := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ P := by positivity
  constructor
  · have : ((T : ℝ) - 1) * (8 * T + 2) ≤ 10 * T ^ 2 := by nlinarith
    nlinarith
  · have h2P : (0 : ℝ) < 2 ^ P := by positivity
    rw [inv_pow, inv_pow, ← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ h2P (by positivity)]
    have h8 : (2 : ℝ) ^ (t + 8) = 256 * 2 ^ t := by rw [pow_add]; norm_num; ring
    rw [h8] at hP
    have h2t : (0 : ℝ) < 2 ^ t := by positivity
    nlinarith

end CacheScan

end ExactSampling.AttentionHeads
