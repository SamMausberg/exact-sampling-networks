import Mathlib

/-!
# Relay gates for every fixed row bound above one

Paper file: instance_hardness.tex, proof of `thm:instance-hardness`.

Formalized:
* The relay `T(u) = tanh(a u)` with `a = 1 + δ`, `δ = 2^{-R}`, `c = δ/16`: the local growth
  `T(u) ≥ (1 + δ/2) u` on `[0, c]`, preservation of `[c, 1)`, and the fact that
  `K = 3 · 2^R (R + 18)` relay layers take `[d, 1)` into `[c, 1)` for `d = c²/2^{14}`, while
  preserving zero exactly (including the count `K log(1 + δ/2) ≥ log(c/d)`).
* The reduced-gain AND gate `A_a(u,v) = tanh(κ B_a(u,v))` with `γ = a/2`, `κ = a/4`: exact
  cancellation for a false input, `B_a(u,v) ≥ γ² u v / 384 ≥ c²/1536` (from `tanh ≥ 1/3` and
  `sech² > 1/256` on `[1/2, 5/2]`), hence `A_a ≥ c²/12288 ≥ d` on true inputs; the reduced OR
  gate `tanh(κ ∑ uᵢ) ≥ c/8 ≥ d`; and the output correlation `tanh(ac/2) ≥ c/4`.
* Correctness of the relayed gates in the encoding "false is `0`, true is in `[c, 1)`", and their
  composition: relayed literal values and padded clauses, the relayed parity-combination gate,
  balanced relayed AND and parity trees, the synchronizing relays, and the end-to-end statement
  (`sat_parity_end_to_endC`): for a CNF formula with at most three literals per clause, the
  output is exactly zero on violating assignments and `∏ᵢ yᵢ · f ≥ c/4` for every `y` on
  satisfying ones.
* The amplitude factorization `f(x, y) = A(x) ∏ᵢ yᵢ` of the relayed network, with `A(x) = 0`
  on violating and `A(x) ≥ c/4` on satisfying assignments (`outputC_factorizes`), used in
  `cor:score-certificate-hardness` for every fixed row bound above one.
* The gates written as tanh neurons with explicit weight vectors (`gates_as_neurons`), their row
  norms (`reduced_row_norms`, including the relay), the parameter grid, and the layer-count
  arithmetic `D = K + 4 + C r`, `n = 2^{K+4} m^C = 2^D`.
* The polylogarithmic gap `g(2^{K+4+Cr})² < 1 + cm/4` for all large `r` (`polylog_gapC`).

Not formalized: the assembly of the gates into one dense width-`n` network (the gates are
composed as functions; per-layer neuron counts and the width bound are not derived), the
complexity-theoretic conclusions, and the upper bound of `thm:upper` used for the case `s ≤ 1`
(taken as a hypothesis in `constant_approximation`). With correlation `c/4`, the probe bound
`Q^* ≥ cm/4` is `ExactSampling.TranscriptLowerBounds.parity_cost_gap` within the finite
decision-tree model, for samplers that receive the satisfying assignment for free; the step
"giving the assignment for free can only help" is not formalized.
-/

namespace ExactSampling.RelayGates

open Real

noncomputable section

/-! ## Elementary tanh facts -/

/-- `tanh' = 1 - tanh²`. Auxiliary for the gate bounds in the proof of `thm:instance-hardness`
(instance_hardness.tex). -/
lemma hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have h : Real.tanh = Real.sinh / Real.cosh := by
    funext y; rw [Pi.div_apply, Real.tanh_eq_sinh_div_cosh]
  have hc := (Real.cosh_pos x).ne'
  have hd := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  rw [← h] at hd
  refine hd.congr_deriv ?_
  rw [Real.tanh_eq_sinh_div_cosh, div_pow]
  field_simp

/-- `tanh` is strictly increasing. Auxiliary for `thm:instance-hardness`. -/
lemma tanh_strictMono : StrictMono Real.tanh :=
  strictMono_of_hasDerivAt_pos hasDerivAt_tanh fun x => by
    have := Real.tanh_sq_lt_one x; linarith

/-- `tanh` is monotone. Auxiliary for `thm:instance-hardness`. -/
lemma tanh_mono {x y : ℝ} (h : x ≤ y) : Real.tanh x ≤ Real.tanh y := tanh_strictMono.monotone h

/-- `tanh ≥ 0` on `[0, ∞)`. Auxiliary for `thm:instance-hardness`. -/
lemma tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  have := tanh_mono hx; rwa [Real.tanh_zero] at this

/-- `tanh v ≤ v` on `[0, ∞)`. Auxiliary for `thm:instance-hardness`. -/
lemma tanh_le_self {v : ℝ} (hv : 0 ≤ v) : Real.tanh v ≤ v := by
  have hd : ∀ x, HasDerivAt (fun x => x - Real.tanh x) (Real.tanh x ^ 2) x := fun x => by
    have := (hasDerivAt_id' x).sub (hasDerivAt_tanh x)
    refine this.congr_deriv ?_; ring
  have hmono : Monotone (fun x => x - Real.tanh x) :=
    monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt) fun x => by
      rw [(hd x).deriv]; positivity
  have := hmono hv
  simp only [Real.tanh_zero, sub_zero] at this
  linarith

/-- `tanh v ≥ v - v³/3` for `v ≥ 0`, by integrating `tanh' = 1 - tanh² ≥ 1 - v²`.

Paper: proof of `thm:instance-hardness` (instance_hardness.tex). -/
lemma tanh_ge_cubic {v : ℝ} (hv : 0 ≤ v) : v - v ^ 3 / 3 ≤ Real.tanh v := by
  have hd : ∀ x, HasDerivAt (fun x => Real.tanh x - x + x ^ 3 / 3)
      (x ^ 2 - Real.tanh x ^ 2) x := fun x => by
    have := (((hasDerivAt_tanh x).sub (hasDerivAt_id' x)).add
      ((hasDerivAt_pow 3 x).div_const 3))
    refine this.congr_deriv ?_; push_cast; ring
  have hmono : MonotoneOn (fun x => Real.tanh x - x + x ^ 3 / 3) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Ici] at hx
    rw [(hd x).deriv]
    have h1 := tanh_nonneg hx.out.le
    have h2 := tanh_le_self hx.out.le
    nlinarith
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hv) hv
  simp only [Real.tanh_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div, add_zero] at this
  linarith

/-- `tanh z ≥ z/2` on `[0, 1]`. Paper: proof of `thm:instance-hardness`
(instance_hardness.tex). -/
lemma tanh_ge_half {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) : z / 2 ≤ Real.tanh z := by
  have := tanh_ge_cubic h0
  nlinarith [mul_nonneg h0 h0]

/-- `tanh x = (e^{2x} - 1)/(e^{2x} + 1)`. Auxiliary for `thm:instance-hardness`. -/
lemma tanh_eq_exp (x : ℝ) : Real.tanh x = (Real.exp (2 * x) - 1) / (Real.exp (2 * x) + 1) := by
  rw [Real.tanh_eq]
  have h1 : Real.exp (2 * x) = Real.exp x * Real.exp x := by rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-x) = 1 / Real.exp x := by rw [Real.exp_neg, one_div]
  have h3 := Real.exp_pos x
  rw [h1, h2]
  field_simp

/-- `tanh(1/2) ≥ 1/3`, since `e ≥ 2`. Paper: proof of `thm:instance-hardness`. -/
lemma third_le_tanh_half : 1 / 3 ≤ Real.tanh (1 / 2) := by
  rw [tanh_eq_exp, le_div_iff₀ (by positivity)]
  have := Real.exp_one_gt_d9
  norm_num
  linarith

/-- `sech² w ≥ 1/256` on `[0, 5/2]`, from `sech² w ≥ e^{-2w}` and `e⁵ < 256`.
Paper: proof of `thm:instance-hardness` (instance_hardness.tex). -/
lemma sech_sq_ge {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 5 / 2) : 1 / 256 ≤ 1 - Real.tanh w ^ 2 := by
  have hc := Real.cosh_pos w
  have hsech : 1 - Real.tanh w ^ 2 = 1 / Real.cosh w ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh, div_pow]
    field_simp
    rw [Real.cosh_sq]; ring
  rw [hsech]
  have hcosh : Real.cosh w ≤ Real.exp w := by
    rw [Real.cosh_eq]
    have : Real.exp (-w) ≤ Real.exp w := Real.exp_le_exp.mpr (by linarith)
    linarith
  have he : Real.exp w ^ 2 ≤ 256 := by
    have h5 : Real.exp w ^ 2 ≤ Real.exp 1 ^ 5 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      exact Real.exp_le_exp.mpr (by push_cast; linarith)
    have := Real.exp_one_lt_d9
    have h3 : Real.exp 1 ^ 5 ≤ 3 ^ 5 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 5
    have h4 : (3 : ℝ) ^ 5 = 243 := by norm_num
    linarith
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith [pow_le_pow_left₀ hc.le hcosh 2]

/-! ## The relay -/

section Params

variable (R : ℕ)

/-- `δ = 2^{-R}`. -/
def δ : ℝ := (1 / 2) ^ R
/-- The row bound `a = 1 + δ`. -/
def a : ℝ := 1 + δ R
/-- The true threshold `c = δ/16`. -/
def c : ℝ := δ R / 16
/-- The relay start `d = c²/2^{14}`. -/
def d : ℝ := c R ^ 2 / 2 ^ 14
/-- The number of relay layers `K = 3 · 2^R (R + 18)`. -/
def K : ℕ := 3 * 2 ^ R * (R + 18)

/-- `δ > 0`. Auxiliary for the proof of `thm:instance-hardness` (instance_hardness.tex). -/
lemma δ_pos : 0 < δ R := by unfold δ; positivity
/-- `δ ≤ 1`. Auxiliary for the proof of `thm:instance-hardness` (instance_hardness.tex). -/
lemma δ_le_one : δ R ≤ 1 := by unfold δ; exact pow_le_one₀ (by norm_num) (by norm_num)
/-- `c > 0`. Auxiliary for the proof of `thm:instance-hardness` (instance_hardness.tex). -/
lemma c_pos : 0 < c R := by unfold c; have := δ_pos R; positivity
/-- `c ≤ 1/16`. Auxiliary for the proof of `thm:instance-hardness` (instance_hardness.tex). -/
lemma c_le : c R ≤ 1 / 16 := by unfold c; have := δ_le_one R; linarith
/-- `d > 0`. Auxiliary for the proof of `thm:instance-hardness` (instance_hardness.tex). -/
lemma d_pos : 0 < d R := by unfold d; have := c_pos R; positivity
/-- `a ≤ 2`. Auxiliary for the proof of `thm:instance-hardness` (instance_hardness.tex). -/
lemma a_le_two : a R ≤ 2 := by unfold a; have := δ_le_one R; linarith
/-- `a > 1`. Auxiliary for the proof of `thm:instance-hardness` (instance_hardness.tex). -/
lemma one_lt_a : 1 < a R := by unfold a; have := δ_pos R; linarith

/-- The relay `T(u) = tanh(a u)`. -/
def relay (u : ℝ) : ℝ := Real.tanh (a R * u)

/-- **Local growth of the relay.** `T(u) ≥ (1 + δ/2) u` for `0 ≤ u ≤ c`, because
`a³ c²/3 ≤ δ²/96 ≤ δ/2`. Paper: proof of `thm:instance-hardness` (instance_hardness.tex). -/
theorem relay_growth {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ c R) :
    (1 + δ R / 2) * u ≤ relay R u := by
  have hδ0 := δ_pos R
  have hδ1 := δ_le_one R
  have ha2 := a_le_two R
  have ha1 := one_lt_a R
  have hc : c R = δ R / 16 := rfl
  have hapos : 0 < a R := by linarith
  have hcub := tanh_ge_cubic (mul_nonneg hapos.le h0)
  unfold relay
  have hu2 : u ^ 2 ≤ (δ R / 16) ^ 2 := by rw [← hc]; nlinarith
  have ha3 : a R ^ 3 ≤ 8 := by
    have := pow_le_pow_left₀ hapos.le ha2 3
    norm_num at this
    linarith
  have hprod : a R ^ 3 * u ^ 2 ≤ 3 * (δ R / 2) := by
    have h1 : a R ^ 3 * u ^ 2 ≤ 8 * (δ R / 16) ^ 2 :=
      mul_le_mul ha3 hu2 (sq_nonneg u) (by norm_num)
    have h2 : 8 * (δ R / 16) ^ 2 ≤ 3 * (δ R / 2) := by nlinarith
    linarith
  have hkey : (a R * u) ^ 3 / 3 ≤ δ R / 2 * u := by
    have e : (a R * u) ^ 3 = u * (a R ^ 3 * u ^ 2) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hprod h0
    linarith
  have hau : a R * u = u + δ R * u := by unfold a; ring
  linarith

/-- The relay keeps `[c, ∞)` above `c`. Paper: proof of `thm:instance-hardness`. -/
theorem relay_above {u : ℝ} (h : c R ≤ u) : c R ≤ relay R u := by
  have hc := c_pos R
  have h1 := relay_growth R hc.le le_rfl
  have h2 : relay R (c R) ≤ relay R u :=
    tanh_mono (mul_le_mul_of_nonneg_left h (by linarith [one_lt_a R]))
  have : c R ≤ (1 + δ R / 2) * c R := by nlinarith [δ_pos R]
  linarith

/-- Relays keep nonnegative values nonnegative. Auxiliary for the proof of
`thm:instance-hardness` (instance_hardness.tex). -/
lemma relay_nonneg {u : ℝ} (h : 0 ≤ u) : 0 ≤ relay R u :=
  tanh_nonneg (mul_nonneg (by linarith [one_lt_a R]) h)

/-- Relays preserve zero exactly. Paper: proof of `thm:instance-hardness`
(instance_hardness.tex). -/
lemma relay_zero : relay R 0 = 0 := by simp [relay]

/-- Iterated relays. -/
def relayIter (k : ℕ) (u : ℝ) : ℝ := (relay R)^[k] u

/-- **Truncated geometric growth.** After `k` relays, the value is at least
`min{c, (1 + δ/2)^k u}`. This avoids assuming that an iterate stays below `c` once it has
crossed it. Paper: proof of `thm:instance-hardness` (instance_hardness.tex). -/
theorem relayIter_min_lower (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ relayIter R k u ∧ min (c R) ((1 + δ R / 2) ^ k * u) ≤ relayIter R k u := by
  have hl : (1 : ℝ) ≤ 1 + δ R / 2 := by linarith [δ_pos R]
  induction k with
  | zero => simp [relayIter, hu]
  | succ k ih =>
    obtain ⟨ih0, ih1⟩ := ih
    have hrw : relayIter R (k + 1) u = relay R (relayIter R k u) := by
      simp only [relayIter, Function.iterate_succ_apply']
    rw [hrw]
    refine ⟨relay_nonneg R ih0, ?_⟩
    by_cases hcross : c R ≤ relayIter R k u
    · exact (min_le_left _ _).trans (relay_above R hcross)
    · push Not at hcross
      have hstep := relay_growth R ih0 hcross.le
      have hmin : min (c R) ((1 + δ R / 2) ^ (k + 1) * u) ≤
          (1 + δ R / 2) * min (c R) ((1 + δ R / 2) ^ k * u) := by
        rcases le_total (c R) ((1 + δ R / 2) ^ k * u) with h | h
        · rw [min_eq_left h]
          exact (min_le_left _ _).trans (le_mul_of_one_le_left (c_pos R).le hl)
        · rw [min_eq_right h, pow_succ]
          exact (min_le_right _ _).trans (le_of_eq (by ring))
      calc min (c R) ((1 + δ R / 2) ^ (k + 1) * u) ≤
            (1 + δ R / 2) * min (c R) ((1 + δ R / 2) ^ k * u) := hmin
        _ ≤ (1 + δ R / 2) * relayIter R k u :=
            mul_le_mul_of_nonneg_left ih1 (by linarith)
        _ ≤ _ := hstep

/-- **Enough relays.** `(1 + δ/2)^K d ≥ c`: indeed `K log(1 + δ/2) ≥ K δ/3 = R + 18 ≥
(R + 18) log 2 = log(c/d)`. Paper: proof of `thm:instance-hardness` (instance_hardness.tex). -/
theorem relay_count : c R ≤ (1 + δ R / 2) ^ K R * d R := by
  have hδ0 := δ_pos R
  have hδ1 := δ_le_one R
  have hcd : c R / d R = 2 ^ (R + 18) := by
    unfold d c δ
    have : (1 / 2 : ℝ) ^ R * 2 ^ R = 1 := by rw [← mul_pow]; norm_num
    field_simp
    rw [pow_add]
    nlinarith [this]
  have hlog : (R : ℝ) + 18 ≤ (K R : ℝ) * Real.log (1 + δ R / 2) := by
    have h1 : δ R / 3 ≤ Real.log (1 + δ R / 2) := by
      have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 + δ R / 2 by linarith)
      have h2 : δ R / 3 ≤ 1 - (1 + δ R / 2)⁻¹ := by
        rw [inv_eq_one_div, le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ (by linarith)]
        nlinarith
      linarith
    have hK : (K R : ℝ) * (δ R / 3) = R + 18 := by
      unfold K δ
      push_cast
      have : (2 : ℝ) ^ R * (1 / 2) ^ R = 1 := by rw [← mul_pow]; norm_num
      linear_combination (R + 18 : ℝ) * this
    calc (R : ℝ) + 18 = (K R : ℝ) * (δ R / 3) := hK.symm
      _ ≤ (K R : ℝ) * Real.log (1 + δ R / 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
  have hpow : (2 : ℝ) ^ (R + 18) ≤ (1 + δ R / 2) ^ K R := by
    have e1 : (1 + δ R / 2) ^ K R = Real.exp ((K R : ℝ) * Real.log (1 + δ R / 2)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
    have e2 : (2 : ℝ) ^ (R + 18) ≤ Real.exp ((R : ℝ) + 18) := by
      have : Real.exp ((R : ℝ) + 18) = Real.exp 1 ^ (R + 18) := by
        rw [← Real.exp_nat_mul]; push_cast; ring_nf
      rw [this]
      exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
    rw [e1]
    exact e2.trans (Real.exp_le_exp.mpr hlog)
  have hd := d_pos R
  rw [div_eq_iff hd.ne'] at hcd
  rw [hcd]
  exact mul_le_mul_of_nonneg_right hpow hd.le

/-- **Relays restore the encoding.** `K` relays map `[d, 1)` into `[c, 1)` and keep zero exactly.
Paper: proof of `thm:instance-hardness` (instance_hardness.tex). -/
theorem relayIter_restore {u : ℝ} (hd : d R ≤ u) :
    c R ≤ relayIter R (K R) u ∧ relayIter R (K R) u < 1 := by
  have hu : 0 ≤ u := (d_pos R).le.trans hd
  obtain ⟨-, h⟩ := relayIter_min_lower R (K R) hu
  refine ⟨le_trans ?_ h, ?_⟩
  · refine le_min le_rfl ?_
    exact (relay_count R).trans
      (mul_le_mul_of_nonneg_left hd (pow_nonneg (by linarith [δ_pos R]) _))
  · cases hK : K R with
    | zero => simp [K] at hK
    | succ k =>
      simp only [relayIter, Function.iterate_succ_apply']
      exact Real.tanh_lt_one _

/-- Iterated relays preserve zero exactly. Paper: proof of `thm:instance-hardness`
(instance_hardness.tex). -/
lemma relayIter_zero (k : ℕ) : relayIter R k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [relayIter, Function.iterate_succ_apply'] at *; rw [ih, relay_zero]

/-! ## The reduced-gain AND and OR gates -/

/-- The mixed difference with bias `b`, coefficient `γ` and activation `φ`. -/
def mixedDifference (φ : ℝ → ℝ) (b γ u v : ℝ) : ℝ :=
  -φ (b + γ * u + γ * v) + φ (b + γ * u) + φ (b + γ * v) - φ b

/-- A false first input cancels exactly, for every activation. Paper: proof of
`thm:instance-hardness` ("a zero input still causes exact cancellation"). -/
lemma mixedDifference_zero_left (φ : ℝ → ℝ) (b γ v : ℝ) : mixedDifference φ b γ 0 v = 0 := by
  simp only [mixedDifference, mul_zero, add_zero]; ring

/-- A false second input cancels exactly, for every activation. Paper: proof of
`thm:instance-hardness`. -/
lemma mixedDifference_zero_right (φ : ℝ → ℝ) (b γ u : ℝ) : mixedDifference φ b γ u 0 = 0 := by
  simp only [mixedDifference, mul_zero, add_zero]; ring

/-- `sech²` drops at rate at least `1/384` on `[1/2, 5/2]`. Auxiliary for `B_a ≥ γ²uv/384`
in the proof of `thm:instance-hardness`. -/
lemma sech_sq_drop {w w' : ℝ} (hw : 1 / 2 ≤ w) (hww : w ≤ w') (hw' : w' ≤ 5 / 2) :
    (1 - Real.tanh w' ^ 2) - (1 - Real.tanh w ^ 2) ≤ -(w' - w) / 384 := by
  have hd : ∀ x, HasDerivAt (fun x => (1 - Real.tanh x ^ 2) + x / 384)
      (-(2 * Real.tanh x * (1 - Real.tanh x ^ 2)) + 1 / 384) x := fun x => by
    have h1 := ((hasDerivAt_tanh x).pow 2).const_sub 1
    have h2 := (hasDerivAt_id' x).div_const 384
    refine (h1.add h2).congr_deriv ?_
    push_cast; ring
  have hanti : AntitoneOn (fun x => (1 - Real.tanh x ^ 2) + x / 384) (Set.Icc (1 / 2) (5 / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hd x).deriv]
    have ht : 1 / 3 ≤ Real.tanh x := third_le_tanh_half.trans (tanh_mono hx.1.le)
    have hs := sech_sq_ge (by linarith [hx.1]) hx.2.le
    nlinarith [mul_le_mul ht hs (by norm_num) (by linarith)]
  have := hanti ⟨hw, hww.trans hw'⟩ ⟨hw.trans hww, hw'⟩ hww
  simp only at this
  linarith

/-- **The AND lower bound.** For `γ ∈ [1/2, 1]` and `u, v ∈ [0, 1]`,
`B_a(u,v) ≥ γ² u v / 384`, the discrete form of
`B_a = ∫₀^{γu} ∫₀^{γv} 2 tanh(1/2 + y + z) sech²(1/2 + y + z) dz dy`.

Paper: proof of `thm:instance-hardness` (instance_hardness.tex). -/
theorem mixedDifference_lower {γ u v : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    γ ^ 2 * u * v / 384 ≤ mixedDifference Real.tanh (1 / 2) γ u v := by
  set h := γ * u with hh
  set g := γ * v with hg
  have hh0 : 0 ≤ h := mul_nonneg hγ0 hu0
  have hh1 : h ≤ 1 := by nlinarith
  have hg0 : 0 ≤ g := mul_nonneg hγ0 hv0
  have hg1 : g ≤ 1 := by nlinarith
  -- `ψ(w) = tanh(w + h) - tanh w` has `ψ' ≤ -h/384` on `[1/2, 3/2]`
  have hd : ∀ x, HasDerivAt (fun x => Real.tanh (x + h) - Real.tanh x + h / 384 * x)
      ((1 - Real.tanh (x + h) ^ 2) - (1 - Real.tanh x ^ 2) + h / 384) x := fun x => by
    have h1 := (hasDerivAt_tanh (x + h)).comp x ((hasDerivAt_id' x).add_const h)
    have h2 := hasDerivAt_tanh x
    have h3 := (hasDerivAt_id' x).const_mul (h / 384)
    refine ((h1.sub h2).add h3).congr_deriv ?_
    simp
  have hanti : AntitoneOn (fun x => Real.tanh (x + h) - Real.tanh x + h / 384 * x)
      (Set.Icc (1 / 2) (3 / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hd x).deriv]
    have := sech_sq_drop (w := x) (w' := x + h) hx.1.le (by linarith) (by linarith [hx.2])
    linarith
  have := hanti ⟨le_rfl, by norm_num⟩ ⟨by linarith, by linarith⟩ (by linarith : 1 / 2 ≤ 1 / 2 + g)
  simp only at this
  unfold mixedDifference
  have e : γ ^ 2 * u * v / 384 = h / 384 * g := by rw [hh, hg]; ring
  rw [e]
  have e2 : 1 / 2 + h + g = 1 / 2 + g + h := by ring
  rw [show 1 / 2 + γ * u + γ * v = 1 / 2 + g + h by rw [← hh, ← hg]; ring,
    show 1 / 2 + γ * u = 1 / 2 + h by rw [hh],
    show 1 / 2 + γ * v = 1 / 2 + g by rw [hg]]
  nlinarith

/-- The mixed difference with tanh lies below `2`. Auxiliary for `A_a ≥ κB_a/2`. -/
lemma mixedDifference_le_two {γ u v : ℝ} (hγ : 0 ≤ γ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    mixedDifference Real.tanh (1 / 2) γ u v ≤ 2 := by
  unfold mixedDifference
  have h1 := tanh_nonneg (show (0 : ℝ) ≤ 1 / 2 + γ * u + γ * v by positivity)
  have h2 := Real.tanh_lt_one (1 / 2 + γ * u)
  have h3 := Real.tanh_lt_one (1 / 2 + γ * v)
  have h4 := tanh_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  linarith

/-- The reduced-gain AND gate `A_a(u,v) = tanh(κ B_a(u,v))` with `γ = a/2`, `κ = a/4`. -/
def andA (u v : ℝ) : ℝ := Real.tanh (a R / 4 * mixedDifference Real.tanh (1 / 2) (a R / 2) u v)

/-- **Reduced-gain AND on true inputs.** For `u, v ∈ [c, 1)`, `B_a(u,v) ≥ c²/1536`, and
`A_a(u,v) ≥ κ B_a/2 ≥ c²/12288 ≥ d`. Paper: proof of `thm:instance-hardness`. -/
theorem andA_true {u v : ℝ} (hu : c R ≤ u) (hu1 : u < 1) (hv : c R ≤ v) (hv1 : v < 1) :
    c R ^ 2 / 1536 ≤ mixedDifference Real.tanh (1 / 2) (a R / 2) u v ∧
      c R ^ 2 / 12288 ≤ andA R u v ∧ d R ≤ andA R u v ∧ andA R u v < 1 := by
  have hc := c_pos R
  have ha1 := one_lt_a R
  have ha2 := a_le_two R
  have hB := mixedDifference_lower (γ := a R / 2) (u := u) (v := v) (by linarith)
    (by linarith) (by linarith) hu1.le (by linarith) hv1.le
  have hB2 := mixedDifference_le_two (γ := a R / 2) (by linarith) (by linarith) (by linarith)
    (u := u) (v := v)
  set B := mixedDifference Real.tanh (1 / 2) (a R / 2) u v
  have hu0 : 0 ≤ u := by linarith
  have hv0 : 0 ≤ v := by linarith
  have hB0 : 0 ≤ B := le_trans (by positivity) hB
  have harg0 : 0 ≤ a R / 4 * B := mul_nonneg (by linarith) hB0
  have harg1 : a R / 4 * B ≤ 1 := by nlinarith
  have hA := tanh_ge_half harg0 harg1
  have huv : c R * c R ≤ u * v := mul_le_mul hu hv hc.le (by linarith)
  have hγ2 : 1 / 4 ≤ (a R / 2) ^ 2 := by nlinarith
  -- `B ≥ γ² c²/384 ≥ c²/1536`
  have h2 : c R ^ 2 / 1536 ≤ B := by
    have h1 : (a R / 2) ^ 2 * (c R * c R) / 384 ≤ B := by
      calc (a R / 2) ^ 2 * (c R * c R) / 384 ≤ (a R / 2) ^ 2 * u * v / 384 := by
            rw [mul_assoc]; gcongr
        _ ≤ B := hB
    exact le_trans (by nlinarith) h1
  -- `A ≥ κ B/2 ≥ (1/4)(c²/1536)/2 = c²/12288`
  have hlow : c R ^ 2 / 12288 ≤ andA R u v := by
    have h3 : 1 / 4 * (c R ^ 2 / 1536) ≤ a R / 4 * B :=
      mul_le_mul (by linarith) h2 (by positivity) (by linarith)
    unfold andA
    linarith
  have hd : d R ≤ c R ^ 2 / 12288 := by unfold d; nlinarith [sq_nonneg (c R)]
  exact ⟨h2, hlow, hd.trans hlow, Real.tanh_lt_one _⟩

/-- A false input makes the reduced AND output exactly zero. Paper: proof of
`thm:instance-hardness` (instance_hardness.tex). -/
lemma andA_zero_left (v : ℝ) : andA R 0 v = 0 := by
  simp [andA, mixedDifference_zero_left]

/-- A false input makes the reduced AND output exactly zero. Paper: proof of
`thm:instance-hardness` (instance_hardness.tex). -/
lemma andA_zero_right (u : ℝ) : andA R u 0 = 0 := by
  simp [andA, mixedDifference_zero_right]

/-- The reduced OR gate before relays, `tanh(κ ∑ᵢ uᵢ)`. -/
def orA {j : ℕ} (u : Fin j → ℝ) : ℝ := Real.tanh (a R / 4 * ∑ i, u i)

/-- **Reduced OR on a true input.** If some input is at least `c` and all are nonnegative,
`tanh(κ ∑ uᵢ) ≥ κ c/2 ≥ c/8 ≥ d`. Paper: proof of `thm:instance-hardness`. -/
theorem orA_true {j : ℕ} {u : Fin j → ℝ} (h0 : ∀ i, 0 ≤ u i) {i₀ : Fin j} (hi : c R ≤ u i₀) :
    c R / 8 ≤ orA R u ∧ d R ≤ orA R u ∧ orA R u < 1 := by
  have hc := c_pos R
  have hc16 := c_le R
  have ha1 := one_lt_a R
  have ha2 := a_le_two R
  have hsum : c R ≤ ∑ i, u i :=
    hi.trans (Finset.single_le_sum (fun i _ => h0 i) (Finset.mem_univ i₀))
  have h1 : Real.tanh (a R / 4 * c R) ≤ orA R u :=
    tanh_mono (mul_le_mul_of_nonneg_left hsum (by linarith))
  have h2 := tanh_ge_half (z := a R / 4 * c R) (by positivity) (by nlinarith)
  have h3 : c R / 8 ≤ a R / 4 * c R / 2 := by nlinarith
  have h4 : d R ≤ c R / 8 := by
    unfold d
    nlinarith
  exact ⟨by linarith, by linarith, Real.tanh_lt_one _⟩

/-- The OR gate output vanishes on false inputs. Paper: proof of `thm:instance-hardness`
(instance_hardness.tex). -/
lemma orA_zero {j : ℕ} : orA R (fun _ : Fin j => (0 : ℝ)) = 0 := by simp [orA]

/-! ## The relayed gates in the `c`-encoding -/

/-- Encoding with threshold `c`: false is `0`, true is any number in `[c, 1)`. -/
def EncC (b : Bool) (u : ℝ) : Prop := if b then c R ≤ u ∧ u < 1 else u = 0

/-- Encoded values are nonnegative. Auxiliary for the proof of `thm:instance-hardness`
(instance_hardness.tex). -/
lemma EncC.nonneg {b : Bool} {u : ℝ} (h : EncC R b u) : 0 ≤ u := by
  cases b
  · simp only [EncC, Bool.false_eq_true, ↓reduceIte] at h; rw [h]
  · simp only [EncC, ↓reduceIte] at h; linarith [h.1, c_pos R]

/-- **Relayed AND.** `K` relays after `A_a` give a gate of depth `K + 2` computing conjunction in
the `c`-encoding. Paper: proof of `thm:instance-hardness` (instance_hardness.tex). -/
theorem andGate_enc {b b' : Bool} {u v : ℝ} (hu : EncC R b u) (hv : EncC R b' v) :
    EncC R (b && b') (relayIter R (K R) (andA R u v)) := by
  cases b
  · simp only [EncC, Bool.false_eq_true, ↓reduceIte] at hu
    simp [EncC, hu, andA_zero_left, relayIter_zero]
  · cases b'
    · simp only [EncC, Bool.false_eq_true, ↓reduceIte] at hv
      simp [EncC, hv, andA_zero_right, relayIter_zero]
    · simp only [EncC, ↓reduceIte, Bool.and_self] at hu hv ⊢
      exact relayIter_restore R (andA_true R hu.1 hu.2 hv.1 hv.2).2.2.1

/-- **Relayed OR.** `K` relays after `tanh(κ ∑ uᵢ)` give a gate of depth `K + 1` computing
disjunction in the `c`-encoding. Paper: proof of `thm:instance-hardness`. -/
theorem orGate_enc {j : ℕ} {b : Fin j → Bool} {u : Fin j → ℝ} (h : ∀ i, EncC R (b i) (u i)) :
    EncC R (decide (∃ i, b i = true)) (relayIter R (K R) (orA R u)) := by
  by_cases hex : ∃ i, b i = true
  · obtain ⟨i₀, hi₀⟩ := hex
    have h₀ := h i₀
    rw [hi₀] at h₀
    simp only [EncC, ↓reduceIte] at h₀
    rw [show decide (∃ i, b i = true) = true from decide_eq_true ⟨i₀, hi₀⟩]
    simp only [EncC, ↓reduceIte]
    exact relayIter_restore R (orA_true R (fun i => (h i).nonneg) h₀.1).2.1
  · have hall : u = fun _ => 0 := by
      funext i
      have := h i
      have hb : b i = false := by
        cases hbi : b i
        · rfl
        · exact absurd ⟨i, hbi⟩ hex
      rw [hb] at this
      simpa [EncC] using this
    rw [show decide (∃ i, b i = true) = false from decide_eq_false hex, hall, orA_zero]
    simp [EncC, relayIter_zero]

/-- Literal values `tanh 1 ≥ 1/2 ≥ c` are true in the `c`-encoding. Paper: proof of
`thm:instance-hardness` ("the original literal outputs are at least `1/2`, hence at least
`c`"). -/
theorem literal_true : EncC R true (Real.tanh 1) := by
  simp only [EncC, ↓reduceIte]
  refine ⟨?_, Real.tanh_lt_one 1⟩
  have h1 : 1 / 2 ≤ Real.tanh 1 := by
    rw [tanh_eq_exp, le_div_iff₀ (by positivity)]
    have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 * 1 by norm_num)
    norm_num at this ⊢
    linarith
  linarith [c_le R]

/-- **Output correlation.** If one gated value is in `[c, 1)` and the other is zero, the final
neuron `tanh((a/2)(G₊ - G₋))` has absolute value at least `tanh(ac/2) ≥ c/4`, with the sign of
the nonzero branch. Paper: proof of `thm:instance-hardness` (instance_hardness.tex). -/
theorem output_correlation {G : ℝ} (hG : c R ≤ G) :
    c R / 4 ≤ Real.tanh (a R / 2 * (G - 0)) ∧ Real.tanh (a R / 2 * (0 - G)) ≤ -(c R / 4) := by
  have hc := c_pos R
  have ha1 := one_lt_a R
  have ha2 := a_le_two R
  have hc16 := c_le R
  have h1 : Real.tanh (a R * c R / 2) ≤ Real.tanh (a R / 2 * (G - 0)) :=
    tanh_mono (by nlinarith)
  have h2 := tanh_ge_half (z := a R * c R / 2) (by positivity) (by nlinarith)
  have h3 : c R / 4 ≤ a R * c R / 2 / 2 := by nlinarith
  refine ⟨by linarith, ?_⟩
  rw [show a R / 2 * (0 - G) = -(a R / 2 * (G - 0)) by ring, Real.tanh_neg]
  linarith

/-! ## The relayed circuits -/

/-- The relayed AND gate (depth `K + 2`). -/
def andR (u v : ℝ) : ℝ := relayIter R (K R) (andA R u v)

/-- The relayed OR gate (depth `K + 1`). -/
def orR {j : ℕ} (u : Fin j → ℝ) : ℝ := relayIter R (K R) (orA R u)

/-- One relay preserves the `c`-encoding. Paper: the synchronizing relays in the proof of
`thm:instance-hardness` (instance_hardness.tex). -/
lemma relay_encC {b : Bool} {u : ℝ} (h : EncC R b u) : EncC R b (relay R u) := by
  cases b
  · simp only [EncC, Bool.false_eq_true, ↓reduceIte] at h ⊢; rw [h, relay_zero]
  · simp only [EncC, ↓reduceIte] at h ⊢
    exact ⟨relay_above R h.1, Real.tanh_lt_one _⟩

/-- Iterated relays preserve the `c`-encoding. Paper: proof of `thm:instance-hardness`. -/
lemma relayIter_encC {b : Bool} {u : ℝ} (h : EncC R b u) (k : ℕ) :
    EncC R b (relayIter R k u) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    simp only [relayIter, Function.iterate_succ_apply'] at ih ⊢
    exact relay_encC R ih

/-- The sign `±1` of a Boolean input bit. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- **Literal values in the `c`-encoding.** `tanh((1 + x)/2)` encodes `x = 1` and
`tanh((1 - x)/2)` encodes `x = -1`; the true value is `tanh 1 ≥ c`. Paper: proof of
`thm:instance-hardness` (instance_hardness.tex). -/
theorem literal_encC (x : Bool) :
    EncC R x (Real.tanh ((1 + sgn x) / 2)) ∧ EncC R (!x) (Real.tanh ((1 - sgn x) / 2)) := by
  have h := literal_true R
  cases x
  · refine ⟨?_, ?_⟩
    · simp [EncC, sgn]
    · have e : (1 - sgn false) / 2 = 1 := by norm_num [sgn]
      rw [e]; exact h
  · refine ⟨?_, ?_⟩
    · have e : (1 + sgn true) / 2 = 1 := by norm_num [sgn]
      rw [e]; exact h
    · simp [EncC, sgn]

/-- A pair encoding of a sign in the `c`-encoding. -/
def PEncC (b : Bool) (p : ℝ × ℝ) : Prop := EncC R b p.1 ∧ EncC R (!b) p.2

/-- The product of two signs, as a Boolean value (`true` means `+1`). -/
def mulB (b c : Bool) : Bool := !(xor b c)

/-- Signs multiply along `mulB`. Auxiliary for the parity circuit of `thm:instance-hardness`. -/
lemma sgn_mulB (b c : Bool) : sgn (mulB b c) = sgn b * sgn c := by
  cases b <;> cases c <;> norm_num [mulB, sgn]

/-- The relayed parity-combination gate (depth `C = 2K + 3`). -/
def parityGateC (p q : ℝ × ℝ) : ℝ × ℝ :=
  (orR R ![andR R p.1 q.1, andR R p.2 q.2], orR R ![andR R p.1 q.2, andR R p.2 q.1])

/-- **Relayed parity combination.** Paper: proof of `thm:instance-hardness`
("repeat the formula and parity construction with these gates"). -/
theorem parityGateC_enc {b c' : Bool} {p q : ℝ × ℝ} (hp : PEncC R b p) (hq : PEncC R c' q) :
    PEncC R (mulB b c') (parityGateC R p q) := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  have a1 := andGate_enc R hp1 hq1
  have a2 := andGate_enc R hp2 hq2
  have a3 := andGate_enc R hp1 hq2
  have a4 := andGate_enc R hp2 hq1
  constructor
  · have := orGate_enc R (b := ![b && c', !b && !c'])
      (u := ![andR R p.1 q.1, andR R p.2 q.2]) (fun i => by fin_cases i <;> assumption)
    show EncC R (mulB b c') (relayIter R (K R) (orA R ![andR R p.1 q.1, andR R p.2 q.2]))
    convert this using 2
    cases b <;> cases c' <;> simp [mulB, Fin.exists_fin_two]
  · have := orGate_enc R (b := ![b && !c', !b && c'])
      (u := ![andR R p.1 q.2, andR R p.2 q.1]) (fun i => by fin_cases i <;> assumption)
    show EncC R (!mulB b c') (relayIter R (K R) (orA R ![andR R p.1 q.2, andR R p.2 q.1]))
    convert this using 2
    cases b <;> cases c' <;> simp [mulB, Fin.exists_fin_two]

/-- `2^(r+1) = 2^r + 2^r`. Auxiliary for the balanced trees in the proof of
`thm:instance-hardness`. -/
lemma two_pow_succ (r : ℕ) : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [pow_succ, mul_two]

/-- Left half of a family indexed by `Fin (2^(r+1))`. -/
def leftHalf {α : Type*} {r : ℕ} (u : Fin (2 ^ (r + 1)) → α) : Fin (2 ^ r) → α :=
  fun i => u (finCongr (two_pow_succ r).symm (Fin.castAdd (2 ^ r) i))

/-- Right half of a family indexed by `Fin (2^(r+1))`. -/
def rightHalf {α : Type*} {r : ℕ} (u : Fin (2 ^ (r + 1)) → α) : Fin (2 ^ r) → α :=
  fun i => u (finCongr (two_pow_succ r).symm (Fin.natAdd (2 ^ r) i))

/-- A statement about all indices splits into the two halves. Auxiliary for the balanced trees
in the proof of `thm:instance-hardness`. -/
lemma forall_halves {r : ℕ} (P : Fin (2 ^ (r + 1)) → Prop) :
    (∀ i, P i) ↔ (∀ i, P (finCongr (two_pow_succ r).symm (Fin.castAdd (2 ^ r) i))) ∧
      (∀ i, P (finCongr (two_pow_succ r).symm (Fin.natAdd (2 ^ r) i))) := by
  constructor
  · intro h; exact ⟨fun i => h _, fun i => h _⟩
  · rintro ⟨h1, h2⟩ i
    have := (finCongr (two_pow_succ r)).symm_apply_apply i
    rw [← this]
    generalize finCongr (two_pow_succ r) i = k
    induction k using Fin.addCases with
    | left k => exact h1 k
    | right k => exact h2 k

/-- Products split into the two halves. Auxiliary for the balanced trees in the proof of
`thm:instance-hardness`. -/
lemma prod_halves {r : ℕ} (f : Fin (2 ^ (r + 1)) → ℝ) :
    ∏ i, f i = (∏ i, leftHalf f i) * ∏ i, rightHalf f i := by
  rw [← (finCongr (two_pow_succ r).symm).prod_comp, Fin.prod_univ_add]
  rfl

/-- The balanced tree of relayed AND gates. -/
def andTreeC : (r : ℕ) → (Fin (2 ^ r) → ℝ) → ℝ
  | 0, u => u 0
  | r + 1, u => andR R (andTreeC r (leftHalf u)) (andTreeC r (rightHalf u))

/-- The balanced tree of relayed parity-combination gates. -/
def parityTreeC : (r : ℕ) → (Fin (2 ^ r) → ℝ × ℝ) → ℝ × ℝ
  | 0, p => p 0
  | r + 1, p => parityGateC R (parityTreeC r (leftHalf p)) (parityTreeC r (rightHalf p))

/-- The product sign of a family of signs, computed along the same tree. -/
def parityB : (r : ℕ) → (Fin (2 ^ r) → Bool) → Bool
  | 0, b => b 0
  | r + 1, b => mulB (parityB r (leftHalf b)) (parityB r (rightHalf b))

/-- The tree product sign is `∏ᵢ yᵢ`. Paper: proof of `thm:instance-hardness`. -/
theorem sgn_parityB (r : ℕ) (b : Fin (2 ^ r) → Bool) : sgn (parityB r b) = ∏ i, sgn (b i) := by
  induction r with
  | zero => simp [parityB]
  | succ r ih =>
    simp only [parityB, sgn_mulB, ih]
    rw [prod_halves (fun i => sgn (b i))]
    rfl

/-- **Balanced relayed AND tree.** Paper: the formula circuit in the proof of
`thm:instance-hardness` (instance_hardness.tex). -/
theorem andTreeC_enc (r : ℕ) {b : Fin (2 ^ r) → Bool} {u : Fin (2 ^ r) → ℝ}
    (h : ∀ i, EncC R (b i) (u i)) : EncC R (decide (∀ i, b i = true)) (andTreeC R r u) := by
  induction r with
  | zero =>
    have : decide (∀ i : Fin (2 ^ 0), b i = true) = b 0 := by
      cases hb : b 0
      · exact decide_eq_false fun hh => by simp_all
      · exact decide_eq_true fun i => by
          have : i = 0 := Fin.ext (by have h := i.isLt; simp at h ⊢)
          rw [this, hb]
    rw [this]; exact h 0
  | succ r ih =>
    have h1 := ih (b := leftHalf b) (u := leftHalf u) (fun i => h _)
    have h2 := ih (b := rightHalf b) (u := rightHalf u) (fun i => h _)
    have := andGate_enc R h1 h2
    show EncC R _ (relayIter R (K R) (andA R (andTreeC R r (leftHalf u))
      (andTreeC R r (rightHalf u))))
    convert this using 2
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.and_eq_true]
    exact forall_halves (fun i => b i = true)

/-- **Balanced relayed parity tree.** Paper: the parity circuit in the proof of
`thm:instance-hardness` (instance_hardness.tex). -/
theorem parityTreeC_enc (r : ℕ) {b : Fin (2 ^ r) → Bool} {p : Fin (2 ^ r) → ℝ × ℝ}
    (h : ∀ i, PEncC R (b i) (p i)) : PEncC R (parityB r b) (parityTreeC R r p) := by
  induction r with
  | zero => exact h 0
  | succ r ih =>
    exact parityGateC_enc R (ih (b := leftHalf b) (p := leftHalf p) (fun i => h _))
      (ih (b := rightHalf b) (p := rightHalf p) (fun i => h _))

/-- The final neuron `tanh((a/2)(G₊ - G₋))` with `G± = And(V, P±)` (relayed). -/
def finalC (V : ℝ) (P : ℝ × ℝ) : ℝ := Real.tanh (a R / 2 * (andR R V P.1 - andR R V P.2))

/-- **Output gadget.** If the formula value encodes false, the output is exactly zero; if it
encodes true, the output times the parity sign is at least `c/4`. Paper: proof of
`thm:instance-hardness` (instance_hardness.tex). -/
theorem sat_parity_outputC {s c' : Bool} {V : ℝ} {P : ℝ × ℝ} (hV : EncC R s V)
    (hP : PEncC R c' P) :
    (s = false → finalC R V P = 0) ∧ (s = true → c R / 4 ≤ sgn c' * finalC R V P) := by
  obtain ⟨hP1, hP2⟩ := hP
  have g1 := andGate_enc R hV hP1
  have g2 := andGate_enc R hV hP2
  constructor
  · rintro rfl
    simp only [Bool.false_and, EncC, Bool.false_eq_true, ↓reduceIte] at g1 g2
    simp only [finalC, andR, g1, g2, sub_self, mul_zero, Real.tanh_zero]
  · rintro rfl
    cases c'
    · simp only [Bool.true_and, Bool.not_false, EncC, Bool.false_eq_true, ↓reduceIte] at g1 g2
      have := (output_correlation R g2.1).2
      simp only [finalC, andR, sgn, Bool.false_eq_true, ↓reduceIte, g1] at this ⊢
      linarith
    · simp only [Bool.true_and, Bool.not_true, EncC, Bool.false_eq_true, ↓reduceIte] at g1 g2
      have := (output_correlation R g1.1).1
      simp only [finalC, andR, sgn, ↓reduceIte, g2, one_mul] at this ⊢
      exact this

/-- The literal value of `x_l` (positive literal) or `¬x_l` (negative literal). -/
def litVal {v : ℕ} (x : Fin v → Bool) (l : Fin v × Bool) : ℝ :=
  if l.2 then Real.tanh ((1 + sgn (x l.1)) / 2) else Real.tanh ((1 - sgn (x l.1)) / 2)

/-- The truth value of a literal. -/
def litTruth {v : ℕ} (x : Fin v → Bool) (l : Fin v × Bool) : Bool :=
  if l.2 then x l.1 else !x l.1

/-- Literal values encode literal truth. Paper: proof of `thm:instance-hardness`. -/
lemma litVal_encC {v : ℕ} (x : Fin v → Bool) (l : Fin v × Bool) :
    EncC R (litTruth x l) (litVal x l) := by
  unfold litVal litTruth
  cases l.2
  · simpa using (literal_encC R (x l.1)).2
  · simpa using (literal_encC R (x l.1)).1

/-- The clause value: relayed OR of three literal values, or the constant `tanh 1` for a padded
true clause (`none`). -/
def clauseValC {v : ℕ} (x : Fin v → Bool) : Option (Fin 3 → Fin v × Bool) → ℝ
  | none => Real.tanh 1
  | some cl => orR R (fun i => litVal x (cl i))

/-- Clause satisfaction (padded clauses are true). -/
def clauseSat {v : ℕ} (x : Fin v → Bool) : Option (Fin 3 → Fin v × Bool) → Bool
  | none => true
  | some cl => decide (∃ i, litTruth x (cl i) = true)

/-- Clause values encode clause satisfaction. Paper: proof of `thm:instance-hardness`. -/
lemma clauseValC_enc {v : ℕ} (x : Fin v → Bool) (cl : Option (Fin 3 → Fin v × Bool)) :
    EncC R (clauseSat x cl) (clauseValC R x cl) := by
  cases cl with
  | none => exact literal_true R
  | some cl => exact orGate_enc R (fun i => litVal_encC R x (cl i))

/-- The formula value: the relayed AND tree over the `2^r` clause values, followed by
`(K + 1)(r - 1)` relays so that it is ready together with the parity pair. -/
def formulaValC {v : ℕ} (r : ℕ) (φ : Fin (2 ^ r) → Option (Fin 3 → Fin v × Bool))
    (x : Fin v → Bool) : ℝ :=
  relayIter R ((K R + 1) * (r - 1)) (andTreeC R r (fun j => clauseValC R x (φ j)))

/-- The literal pair of an input sign: `(tanh 1, 0)` for `+1` and `(0, tanh 1)` for `-1`. -/
def litPair (b : Bool) : ℝ × ℝ := if b then (Real.tanh 1, 0) else (0, Real.tanh 1)

/-- Literal pairs encode their signs. Paper: proof of `thm:instance-hardness`. -/
lemma litPair_encC (b : Bool) : PEncC R b (litPair b) := by
  have h := literal_true R
  cases b
  · exact ⟨by simp [EncC, litPair], by simpa [litPair] using h⟩
  · exact ⟨by simpa [litPair] using h, by simp [EncC, litPair]⟩

/-- **End-to-end output correlation for row bound `a = 1 + 2^{-R}`.** For a CNF formula with at
most three literals per clause, padded to `2^r` clauses, the output of the relayed network is
exactly zero when `x` violates a clause, and `∏ᵢ yᵢ · f_φ(x, y) ≥ c/4` for every `y` when `x`
satisfies every clause.

Paper: proof of `thm:instance-hardness` (instance_hardness.tex). -/
theorem sat_parity_end_to_endC {v : ℕ} (r : ℕ)
    (φ : Fin (2 ^ r) → Option (Fin 3 → Fin v × Bool)) (x : Fin v → Bool)
    (y : Fin (2 ^ r) → Bool) :
    ((∃ j, clauseSat x (φ j) = false) →
        finalC R (formulaValC R r φ x) (parityTreeC R r (fun i => litPair (y i))) = 0) ∧
      ((∀ j, clauseSat x (φ j) = true) →
        c R / 4 ≤ (∏ i, sgn (y i)) *
          finalC R (formulaValC R r φ x) (parityTreeC R r (fun i => litPair (y i)))) := by
  have hV := relayIter_encC R (andTreeC_enc R r (fun j => clauseValC_enc R x (φ j)))
    ((K R + 1) * (r - 1))
  have hP := parityTreeC_enc R r (fun i => litPair_encC R (y i))
  have h := sat_parity_outputC R hV hP
  rw [sgn_parityB] at h
  refine ⟨fun ⟨j, hj⟩ => h.1 ?_, fun hall => h.2 ?_⟩
  · exact decide_eq_false fun hh => by simp [hh j] at hj
  · exact decide_eq_true hall

/-! ## Amplitude factorization for the relayed network -/

/-- The common amplitude of the true entry at level `r` of the relayed parity tree. -/
def amplC : ℕ → ℝ
  | 0 => Real.tanh 1
  | r + 1 => orR R ![andR R (amplC r) (amplC r), 0]

/-- A false input makes the relayed AND output exactly zero. Paper: proof of
`thm:instance-hardness` (instance_hardness.tex). -/
lemma andR_zero_left (v : ℝ) : andR R 0 v = 0 := by
  simp [andR, andA_zero_left, relayIter_zero]

/-- A false input makes the relayed AND output exactly zero. Paper: proof of
`thm:instance-hardness` (instance_hardness.tex). -/
lemma andR_zero_right (u : ℝ) : andR R u 0 = 0 := by
  simp [andR, andA_zero_right, relayIter_zero]

/-- The OR gate is symmetric in its inputs. Auxiliary for `cor:score-certificate-hardness`
(instance_hardness.tex). -/
lemma orR_swap (X : ℝ) : orR R ![0, X] = orR R ![X, 0] := by
  simp [orR, orA, Fin.sum_univ_two]


/-- On literal pairs, the relayed parity tree returns `(A_r, 0)` or `(0, A_r)` according to the
product sign, with an amplitude independent of the pattern. Paper: proof of
`cor:score-certificate-hardness` (instance_hardness.tex). -/
theorem parityTreeC_litPair (r : ℕ) (b : Fin (2 ^ r) → Bool) :
    parityTreeC R r (fun i => litPair (b i)) =
      if parityB r b then (amplC R r, 0) else (0, amplC R r) := by
  induction r with
  | zero =>
    show litPair (b 0) = _
    simp only [litPair, parityB, amplC]
    rfl
  | succ r ih =>
    simp only [parityTreeC, parityB]
    have hl : leftHalf (fun i => litPair (b i)) = fun i => litPair (leftHalf b i) := rfl
    have hr : rightHalf (fun i => litPair (b i)) = fun i => litPair (rightHalf b i) := rfl
    rw [hl, hr, ih, ih]
    rcases Bool.eq_false_or_eq_true (parityB r (leftHalf b)) with hL | hL <;>
      rcases Bool.eq_false_or_eq_true (parityB r (rightHalf b)) with hR | hR <;>
      simp [hL, hR, parityGateC, mulB, andR_zero_left, andR_zero_right, amplC, orR_swap] <;>
      simp [orR, orA, relayIter_zero]

/-- The amplitudes are true encodings. Auxiliary for `cor:score-certificate-hardness`. -/
lemma amplC_enc (r : ℕ) : EncC R true (amplC R r) := by
  induction r with
  | zero => exact literal_true R
  | succ r ih =>
    have h1 := andGate_enc R ih ih
    have h0 : EncC R false (0 : ℝ) := by simp [EncC]
    have := orGate_enc R (b := ![true && true, false]) (u := ![andR R (amplC R r) (amplC R r), 0])
      (fun i => by fin_cases i <;> assumption)
    have e : decide (∃ i, ![true && true, false] i = true) = true :=
      decide_eq_true ⟨0, rfl⟩
    rw [e] at this
    exact this

/-- **Amplitude factorization, every row bound above one.** On literal parity inputs, the
relayed network output factorizes as `f(x, y) = A(x) ∏ᵢ yᵢ` with
`A(x) = tanh((a/2) And(V(x), A_r))`; `A(x) = 0` when the formula value encodes false, and
`A(x) ≥ c/4` when it encodes true.

Paper: proof of `cor:score-certificate-hardness` (instance_hardness.tex). -/
theorem outputC_factorizes (r : ℕ) (V : ℝ) (b : Fin (2 ^ r) → Bool) :
    finalC R V (parityTreeC R r (fun i => litPair (b i))) =
        Real.tanh (a R / 2 * andR R V (amplC R r)) * ∏ i, sgn (b i) ∧
      (EncC R false V → Real.tanh (a R / 2 * andR R V (amplC R r)) = 0) ∧
      (EncC R true V → c R / 4 ≤ Real.tanh (a R / 2 * andR R V (amplC R r))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [parityTreeC_litPair, ← sgn_parityB]
    cases parityB r b
    · simp [finalC, sgn, andR_zero_right, Real.tanh_neg]
    · simp [finalC, sgn, andR_zero_right]
  · intro hV
    simp only [EncC, Bool.false_eq_true, ↓reduceIte] at hV
    simp [hV, andR_zero_left]
  · intro hV
    have h := andGate_enc R hV (amplC_enc R r)
    simp only [Bool.and_self, EncC, ↓reduceIte] at h
    have := (output_correlation R h.1).1
    simpa [andR] using this

/-- **The polylogarithmic gap for row bound `a`.** For fixed `R`, `K'` and `c'`, the factor
`g(n) = K'(log₂ n + 2)^{c'}` at `n = 2^{K+4+Cr}` satisfies `g² < 1 + c m/4` with `m = 2^r` for
all large `r`, so the ranges `Λ ≤ g` (unsatisfiable, `Q^* = 0`) and `Λ ≥ (1 + cm/4)/g`
(satisfiable, `Q^* ≥ cm/4`) are disjoint.

Paper: proof of `thm:instance-hardness` ("this polynomial gap again exceeds the square of any
fixed polylogarithmic factor"). -/
theorem polylog_gapC (K' c' : ℕ) :
    ∀ᶠ r : ℕ in Filter.atTop,
      ((K' : ℝ) * ((K R + 4 + (2 * K R + 3) * r : ℕ) + 2 : ℝ) ^ c') ^ 2 <
        1 + c R * (2 ^ r : ℝ) / 4 := by
  set B : ℝ := (K R : ℝ) + 6 + (2 * K R + 3) with hB
  have hc := c_pos R
  have hB0 : 0 ≤ B := by positivity
  have hK : 0 < 4 * (K' : ℝ) ^ 2 * B ^ (2 * c') / c R + 1 := by positivity
  have ht := tendsto_pow_const_div_const_pow_of_one_lt (2 * c') (show (1 : ℝ) < 2 by norm_num)
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (4 * (K' : ℝ) ^ 2 *
    B ^ (2 * c') / c R + 1) by positivity))
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with r hr hr1
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have h2r : (0 : ℝ) < 2 ^ r := by positivity
  have hrpow := hr
  rw [div_lt_div_iff₀ h2r hK, one_mul] at hrpow
  have hbase : ((K R + 4 + (2 * K R + 3) * r : ℕ) + 2 : ℝ) ≤ B * r := by
    push_cast
    rw [hB]
    nlinarith
  have hb0 : (0 : ℝ) ≤ ((K R + 4 + (2 * K R + 3) * r : ℕ) + 2 : ℝ) := by positivity
  have hpow : (((K R + 4 + (2 * K R + 3) * r : ℕ) + 2 : ℝ) ^ c') ^ 2 ≤
      B ^ (2 * c') * (r : ℝ) ^ (2 * c') := by
    rw [← pow_mul, mul_comm c' 2, ← mul_pow]
    exact pow_le_pow_left₀ hb0 hbase _
  have hK0 : (0 : ℝ) ≤ (K' : ℝ) ^ 2 := by positivity
  have hX : (0 : ℝ) ≤ (r : ℝ) ^ (2 * c') := by positivity
  have hmain : (K' : ℝ) ^ 2 * (B ^ (2 * c') * (r : ℝ) ^ (2 * c')) < c R * 2 ^ r / 4 := by
    have e : (K' : ℝ) ^ 2 * (B ^ (2 * c') * (r : ℝ) ^ (2 * c')) =
        c R / 4 * ((r : ℝ) ^ (2 * c') * (4 * (K' : ℝ) ^ 2 * B ^ (2 * c') / c R)) := by
      field_simp
    rw [e]
    have h1 : (r : ℝ) ^ (2 * c') * (4 * (K' : ℝ) ^ 2 * B ^ (2 * c') / c R) <
        (2 : ℝ) ^ r := by nlinarith
    have := mul_lt_mul_of_pos_left h1 (show 0 < c R / 4 by positivity)
    linarith
  calc ((K' : ℝ) * ((K R + 4 + (2 * K R + 3) * r : ℕ) + 2 : ℝ) ^ c') ^ 2 =
        (K' : ℝ) ^ 2 * (((K R + 4 + (2 * K R + 3) * r : ℕ) + 2 : ℝ) ^ c') ^ 2 := by ring
    _ ≤ (K' : ℝ) ^ 2 * (B ^ (2 * c') * (r : ℝ) ^ (2 * c')) := mul_le_mul_of_nonneg_left hpow hK0
    _ < c R * 2 ^ r / 4 := hmain
    _ < 1 + c R * (2 ^ r : ℝ) / 4 := by linarith

/-! ## Row norms, depth and precision -/

/-- A tanh neuron with bias `b`, weight vector `w` and inputs `u`. -/
def neuron {k : ℕ} (b : ℝ) (w u : Fin k → ℝ) : ℝ := Real.tanh (b + ∑ j, w j * u j)

/-- The row norm `∑ⱼ |wⱼ|` of a weight vector. -/
def rowNorm {k : ℕ} (w : Fin k → ℝ) : ℝ := ∑ j, |w j|

/-- **The reduced gates as tanh neurons.** The AND gate is a first layer of four neurons with
bias `1/2` and weights `(γ,γ)`, `(γ,0)`, `(0,γ)`, `(0,0)`, `γ = a/2`, followed by one neuron
with weights `(-κ,κ,κ,-κ)`, `κ = a/4`; OR is one neuron with weights `κ`; the relay has weight
`a`; the literal values have bias `1/2` and weight `±1/2`; the output neuron has weights
`(a/2, -a/2)`. Paper: proof of `thm:instance-hardness` (instance_hardness.tex). -/
theorem gates_as_neurons {j : ℕ} (us : Fin j → ℝ) (u v : ℝ) (x : Bool) (V : ℝ) (P : ℝ × ℝ) :
    andA R u v = neuron 0 ![-(a R / 4), a R / 4, a R / 4, -(a R / 4)]
        ![neuron (1 / 2) ![a R / 2, a R / 2] ![u, v], neuron (1 / 2) ![a R / 2, 0] ![u, v],
          neuron (1 / 2) ![0, a R / 2] ![u, v], neuron (1 / 2) ![0, 0] ![u, v]] ∧
      orA R us = neuron 0 (fun _ => a R / 4) us ∧
      relay R u = neuron 0 ![a R] ![u] ∧
      Real.tanh ((1 + sgn x) / 2) = neuron (1 / 2) ![1 / 2] ![sgn x] ∧
      Real.tanh ((1 - sgn x) / 2) = neuron (1 / 2) ![-1 / 2] ![sgn x] ∧
      finalC R V P = neuron 0 ![a R / 2, -(a R / 2)] ![andR R V P.1, andR R V P.2] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [andA, mixedDifference, neuron, Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp
    ring_nf
  · simp [orA, neuron, Finset.mul_sum]
  · simp [relay, neuron]
  · simp only [neuron, Fin.sum_univ_succ, Fin.sum_univ_zero]; simp; ring_nf
  · simp only [neuron, Fin.sum_univ_succ, Fin.sum_univ_zero]; simp; ring_nf
  · simp only [finalC, neuron, Fin.sum_univ_succ, Fin.sum_univ_zero]; simp; ring_nf

/-- **Row norms of the reduced gates**, for the weight vectors of `gates_as_neurons`: the first
AND layer has row norm at most `2γ = a`, the second `4κ = a`, the OR row with `j ≤ 3` inputs at
most `3a/4`, the relay `a`, the output neuron `a`, and the literal rows `1/2 ≤ a`; all biases
lie in `{0, 1/2}` (the padded true clause has bias one). Paper: proof of
`thm:instance-hardness` (instance_hardness.tex). -/
theorem reduced_row_norms (j : ℕ) (hj : j ≤ 3) :
    rowNorm ![a R / 2, a R / 2] = a R ∧ rowNorm ![a R / 2, 0] ≤ a R ∧
      rowNorm ![0, a R / 2] ≤ a R ∧ rowNorm ![(0 : ℝ), 0] ≤ a R ∧
      rowNorm ![-(a R / 4), a R / 4, a R / 4, -(a R / 4)] = a R ∧
      rowNorm (fun _ : Fin j => a R / 4) ≤ 3 * a R / 4 ∧ rowNorm ![a R] = a R ∧
      rowNorm ![a R / 2, -(a R / 2)] = a R ∧ rowNorm ![(1 / 2 : ℝ)] ≤ a R ∧
      rowNorm ![(-1 / 2 : ℝ)] ≤ a R := by
  have ha : 0 ≤ a R := by linarith [one_lt_a R]
  have ha1 := one_lt_a R
  have h2 : 0 ≤ a R / 2 := by positivity
  have h4 : 0 ≤ a R / 4 := by positivity
  have hj' : (j : ℝ) ≤ 3 := by exact_mod_cast hj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [rowNorm, Fin.sum_univ_succ, Fin.sum_univ_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] <;>
    simp [abs_of_nonneg h2, abs_of_nonneg h4, abs_of_nonneg ha] <;>
    nlinarith

/-- Depth bookkeeping: with `C = 2K + 3` and `r ≥ 1`, the formula value is ready at depth
`(r + 1)(K + 2) ≤ 1 + C r`; the network has depth `D = K + 4 + C r`, and the width
`n = 2^{K+4} m^C` with `m = 2^r` equals `2^D`. Paper: proof of `thm:instance-hardness`. -/
theorem depth_bookkeeping (Kn r : ℕ) (hr : 1 ≤ r) :
    (r + 1) * (Kn + 2) ≤ 1 + (2 * Kn + 3) * r ∧
      2 ^ (Kn + 4) * (2 ^ r) ^ (2 * Kn + 3) = 2 ^ (Kn + 4 + (2 * Kn + 3) * r) := by
  refine ⟨?_, ?_⟩
  · have : (r + 1) * (Kn + 2) + (Kn + 1) * (r - 1) = 1 + (2 * Kn + 3) * r := by
      obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    omega
  · rw [← pow_mul, ← pow_add, mul_comm r]

/-- Precision: every gate parameter (the entries `±a`, `±a/2`, `±a/4`, `±1/2` and the biases
`0, 1/2, 1` of `gates_as_neurons`) is an integer multiple of `2^{-(R+2)}`, and
`R + 2 ≤ 20(K + 4)`, so all parameters lie on the prescribed grid `2^{-20D}ℤ`.
Paper: proof of `thm:instance-hardness` (instance_hardness.tex). -/
theorem parameters_on_grid :
    (∀ w ∈ ({a R, a R / 2, a R / 4, 1 / 2, 1} : Finset ℝ), ∃ z : ℤ, w = z / 2 ^ (R + 2)) ∧
      R + 2 ≤ 20 * (K R + 4) := by
  refine ⟨?_, ?_⟩
  · have hδ : δ R * 2 ^ R = 1 := by unfold δ; rw [← mul_pow]; norm_num
    have hp : (0 : ℝ) < 2 ^ R := by positivity
    have hR2 : (2 : ℝ) ^ (R + 2) = 4 * 2 ^ R := by rw [pow_add]; ring
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · refine ⟨4 * (2 ^ R + 1), ?_⟩
      push_cast; rw [hR2]; unfold a; field_simp; linear_combination hδ
    · refine ⟨2 * (2 ^ R + 1), ?_⟩
      push_cast; rw [hR2]; unfold a; field_simp; linear_combination 4 * hδ
    · refine ⟨2 ^ R + 1, ?_⟩
      push_cast; rw [hR2]; unfold a; field_simp; linear_combination hδ
    · exact ⟨2 * 2 ^ R, by push_cast; rw [hR2]; field_simp; ring⟩
    · exact ⟨4 * 2 ^ R, by push_cast; rw [hR2]; field_simp⟩
  · unfold K
    have : R ≤ 2 ^ R := Nat.lt_two_pow_self.le
    nlinarith

end Params

/-- For every fixed `s > 1` there is `R` with `δ = 2^{-R} ≤ min{s - 1, 1}`, so `a = 1 + δ ≤ s`.
Paper: first line of the proof of `thm:instance-hardness` (instance_hardness.tex). -/
theorem exists_R {s : ℝ} (hs : 1 < s) : ∃ R : ℕ, δ R ≤ min (s - 1) 1 ∧ a R ≤ s := by
  obtain ⟨R, hR⟩ := exists_pow_lt_of_lt_one (show 0 < min (s - 1) 1 by
    simp only [lt_min_iff]; constructor <;> linarith) (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨R, hR.le, ?_⟩
  unfold a
  have : δ R ≤ s - 1 := hR.le.trans (min_le_left _ _)
  linarith

/-- For `s ≤ 1` the constant value one approximates `1 + Q^*` within a factor `g ≥ 1` whenever
`Q^* ≤ g - 1`; the bound `Q^* ≤ log^{O(1)} n` is `thm:upper` and is taken as the hypothesis
`hQ`. Paper: last paragraph of the proof of `thm:instance-hardness`
(instance_hardness.tex). -/
theorem constant_approximation {Q g : ℝ} (hQ0 : 0 ≤ Q) (hg : 1 ≤ g) (hQ : 1 + Q ≤ g) :
    (1 + Q) / g ≤ 1 ∧ 1 ≤ g * (1 + Q) := by
  constructor
  · rw [div_le_one (by linarith)]; exact hQ
  · nlinarith

end

end ExactSampling.RelayGates
