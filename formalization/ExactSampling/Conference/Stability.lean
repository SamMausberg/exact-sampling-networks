import Mathlib

/-!
# Uniform prefix stability through depth

This module formalizes the quantitative steps of the proof of `lem:conf-stability`
(conference.tex, section `sec:conf-stability`, equations `eq:conf-P` and
`eq:conf-attention-Lip`), for the model of `thm:conf-decoder` (`sec:conf-model`).  The same
lemma appears in the full version as `lem:prefixstability` (attention_moment_decoder.tex), with
the attention estimate `eq:attentionstabilitymoment`; its precision formula is restated after
`thm:main-decoder` (main_normalization.tex).

Formalized:
* the softmax directional derivative `ṗ_j = p_j (ȧ_j - ∑_i p_i ȧ_i)` and the bound
  `‖p(a) - p(a')‖₁ ≤ 2‖a - a'‖_∞` for every finite, nonempty index type (so uniformly in the
  number of positions);
* the attention estimate `eq:conf-attention-Lip`, in pointwise form and with Mathlib's sup norms;
* the score perturbation bound `β K (δ_q + δ_k)` for scores `(β/n)⟨q,k⟩` with `n` coordinates;
* `|N_ε(h)_i| ≤ √n`, the Jacobian entry formula of the normalization as a partial derivative,
  the row-sum bound `(1+√n)/√ε`, the resulting `ℓ∞` Lipschitz bound, and
  `(1+√n)/√ε ≤ (1+√n) √(2^b)` for `ε ≥ 2^(-b)`;
* the depth induction: `J` stages, each `L0`-Lipschitz with local error at most `δ`, give final
  error at most `J L0^J δ`;
* the Lipschitz constants of the other primitives: `s` for affine maps with row sums at most
  `s`, one for tanh, and two for every cumulative output probability;
* the precision choice `P ≥ p + ⌈log₂(J+1)⌉ + J⌈log₂ L0⌉ + 10`, which gives
  `J L0^J 2^(-P) ≤ 2^(-p-10)`, and an explicit bound on this guard in terms of `D + 1`;
* the shifted softmax denominator bound `∑ e^(z_i - A) > 1/2`, including the choice of `A` as the
  largest upper endpoint of logit enclosures of width `1/4`;
* the coordinate bound `K ≥ s(⌈√n⌉+1)` for affine images of normalized states, the existence of
  a power of two `K` in `[x, 2x)`, and the residual range `s + D(sK + s + 1)`, including convex
  residual mixtures;
* the chart decomposition of scores: the common offset cancels in softmax, the coefficient vector
  `t = (βK/n) qᵀA` satisfies `‖t‖₁ ≤ 2rβK²`, the chart coordinates lie in `[-1,1]`, and the
  attention mean equals the ratio `A(t)` enclosed by the moment evaluator of `lem:conf-moments`;
* the causal attention error at every position of a prefix, uniform in the prefix length.

Assembled (section `Layers`): the attention sublayer (normalization, affine queries, keys and
values, causal attention over `j ≤ t`, affine output map, additive update with coefficient in
`[0,1]`) and the feedforward sublayer (normalization, affine map, tanh, additive update) are
defined as maps on prefix arrays `Fin T → Fin n → ℝ` with the sup metric over positions and
coordinates.  Each is proved Lipschitz with the common constant
`L = 1 + s² (1+√n)/√ε (1 + 4βK²)`, independent of `T`, on all inputs (normalization bounds the
attention inputs).  `error_induction` is instantiated for the `2D` sublayers of `D` blocks; the
affine head and the cumulative softmax are added; `L ≤ 18 M^8 2^b` with `M = n + s + β + 2`
gives `⌈log₂ L0⌉ ≤ b + 5 + 8⌈log₂ M⌉`; and `stability_certificate` concludes that local errors
`2^(-P)` with `P = p + O((D+1)[b + log(n+s+β+2)])` enclose every cumulative probability to
`2^(-p)` at every position, for every `T`.

Not formalized: the existence of the bounded chart itself (`lem:conf-chart`, taken as the
hypothesis `k = c₀ + A k_I` with `|A_ij| ≤ 2`); how each stage attains its local error `2^(-P)`
(the certified evaluation of tanh, normalization and exponentials, midpoint rounding, the exact
key product, and the use of the moment evaluator inside the attention stage, which is connected
to this module only through `attn_chart_eq`); the `log(D+V+2)` term of `eq:conf-P` that comes
from evaluating the softmax by refined exponentials (here the head and cumulative softmax are
stages with local error `2^(-P)`); convex residual mixtures `(1-λ)h + λu` inside the assembled
layers (the sublayers here use additive updates `h + α·u`; mixtures appear only in
`mix_step_le` and `residual_range`); and the per-token cost polynomial.
-/

namespace ExactSampling.Stability

open Finset

/-! ## Softmax -/

section Softmax

variable {ι : Type*} [Fintype ι]

/-- Softmax `p(a)_j = e^(a_j) / ∑_i e^(a_i)`. -/
noncomputable def softmax (a : ι → ℝ) (j : ι) : ℝ := Real.exp (a j) / ∑ i, Real.exp (a i)

/-- The softmax denominator is positive.  Auxiliary for `lem:conf-stability`
(conference.tex). -/
theorem sum_exp_pos [Nonempty ι] (a : ι → ℝ) : 0 < ∑ i, Real.exp (a i) :=
  sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty

/-- Softmax probabilities are positive.  Auxiliary for `lem:conf-stability`
(conference.tex). -/
theorem softmax_pos [Nonempty ι] (a : ι → ℝ) (j : ι) : 0 < softmax a j :=
  div_pos (Real.exp_pos _) (sum_exp_pos a)

/-- Softmax probabilities sum to one.  Auxiliary for `lem:conf-stability`
(conference.tex). -/
theorem sum_softmax [Nonempty ι] (a : ι → ℝ) : ∑ j, softmax a j = 1 := by
  simp only [softmax, ← sum_div]
  exact div_self (sum_exp_pos a).ne'

/-- Paper: `lem:conf-stability` (conference.tex): the softmax directional derivative
`ṗ_j = p_j (ȧ_j - ∑_i p_i ȧ_i)` along the score path `s ↦ a + s d`; full version
`lem:prefixstability` (attention_moment_decoder.tex). -/
theorem hasDerivAt_softmax_line [Nonempty ι] (a d : ι → ℝ) (j : ι) (s : ℝ) :
    HasDerivAt (fun s => softmax (fun i => a i + s * d i) j)
      (softmax (fun i => a i + s * d i) j *
        (d j - ∑ i, softmax (fun i => a i + s * d i) i * d i)) s := by
  have hlin : ∀ i, HasDerivAt (fun s => a i + s * d i) (d i) s := fun i => by
    simpa using ((hasDerivAt_id s).mul_const (d i)).const_add (a i)
  have hexp : ∀ i, HasDerivAt (fun s => Real.exp (a i + s * d i))
      (Real.exp (a i + s * d i) * d i) s := fun i => (hlin i).exp
  have hZ : HasDerivAt (fun s => ∑ i, Real.exp (a i + s * d i))
      (∑ i, Real.exp (a i + s * d i) * d i) s :=
    HasDerivAt.fun_sum (fun i _ => hexp i)
  have hZpos := sum_exp_pos (fun i => a i + s * d i)
  have hq := (hexp j).div hZ hZpos.ne'
  convert hq using 1
  · funext s'
    simp only [softmax, Pi.div_apply]
  · have hs : ∑ i, softmax (fun i => a i + s * d i) i * d i =
        (∑ i, Real.exp (a i + s * d i) * d i) / ∑ i, Real.exp (a i + s * d i) := by
      simp only [softmax]
      rw [sum_div]
      refine sum_congr rfl fun i _ => ?_
      ring
    rw [hs]
    simp only [softmax]
    field_simp

/-- Paper: `lem:conf-stability` (conference.tex): softmax is Lipschitz from `ℓ∞` scores to `ℓ₁`
probabilities with constant two, `‖p(a) - p(a')‖₁ ≤ 2‖a - a'‖_∞`, independently of the number
of positions (any finite nonempty index type); full version `lem:prefixstability`
(attention_moment_decoder.tex).  The proof integrates the directional derivative. -/
theorem softmax_l1_le [Nonempty ι] (a a' : ι → ℝ) {δ : ℝ} (h : ∀ i, |a i - a' i| ≤ δ) :
    ∑ j, |softmax a j - softmax a' j| ≤ 2 * δ := by
  set d : ι → ℝ := fun i => a i - a' i with hd
  set σ : ι → ℝ := fun j => if 0 ≤ softmax a j - softmax a' j then 1 else -1 with hσ
  have hσabs : ∀ j, σ j * (softmax a j - softmax a' j) = |softmax a j - softmax a' j| := by
    intro j
    simp only [hσ]
    split_ifs with hx
    · rw [one_mul, abs_of_nonneg hx]
    · rw [abs_of_neg (not_le.1 hx)]; ring
  have hσ1 : ∀ j, |σ j| ≤ 1 := by
    intro j; simp only [hσ]; split_ifs <;> simp
  set P : ℝ → ι → ℝ := fun s => softmax (fun i => a' i + s * d i) with hP
  set g' : ℝ → ℝ := fun s => ∑ j, σ j * (P s j * (d j - ∑ i, P s i * d i)) with hg'
  have hderiv : ∀ s, HasDerivAt (fun s => ∑ j, σ j * P s j) (g' s) s := fun s =>
    HasDerivAt.fun_sum (fun j _ => (hasDerivAt_softmax_line a' d j s).const_mul (σ j))
  have hbound : ∀ s, ‖g' s‖ ≤ 2 * δ := by
    intro s
    have hp : ∀ j, 0 ≤ P s j := fun j => (softmax_pos _ j).le
    have hsum : ∑ j, P s j = 1 := sum_softmax _
    have hmean : |∑ i, P s i * d i| ≤ δ := by
      calc |∑ i, P s i * d i| ≤ ∑ i, |P s i * d i| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, P s i * δ := sum_le_sum fun i _ => by
            rw [abs_mul, abs_of_nonneg (hp i)]
            exact mul_le_mul_of_nonneg_left (h i) (hp i)
        _ = δ := by rw [← sum_mul, hsum, one_mul]
    rw [Real.norm_eq_abs]
    calc |g' s| ≤ ∑ j, |σ j * (P s j * (d j - ∑ i, P s i * d i))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, P s j * (2 * δ) := sum_le_sum fun j _ => by
          rw [abs_mul, abs_mul, abs_of_nonneg (hp j)]
          have hdj : |d j - ∑ i, P s i * d i| ≤ 2 * δ :=
            (abs_sub _ _).trans (by linarith [h j, hmean])
          calc |σ j| * (P s j * |d j - ∑ i, P s i * d i|) ≤ 1 * (P s j * (2 * δ)) :=
                mul_le_mul (hσ1 j) (mul_le_mul_of_nonneg_left hdj (hp j))
                  (mul_nonneg (hp j) (abs_nonneg _)) zero_le_one
            _ = P s j * (2 * δ) := one_mul _
      _ = 2 * δ := by rw [← sum_mul, hsum, one_mul]
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s => ∑ j, σ j * P s j) (f' := g') (C := 2 * δ)
    (fun s _ => (hderiv s).hasDerivWithinAt) (fun s _ => hbound s)
  have ha1 : (fun i => a' i + (1 : ℝ) * d i) = a := by
    funext i; simp only [hd]; ring
  have ha0 : (fun i => a' i + (0 : ℝ) * d i) = a' := by
    funext i; ring
  simp only [hP, ha1, ha0, Real.norm_eq_abs, ← sum_sub_distrib] at hmv
  calc ∑ j, |softmax a j - softmax a' j|
      = ∑ j, (σ j * softmax a j - σ j * softmax a' j) := by
        refine sum_congr rfl fun j _ => ?_
        rw [← mul_sub, hσabs]
    _ ≤ |∑ j, (σ j * softmax a j - σ j * softmax a' j)| := le_abs_self _
    _ ≤ 2 * δ := hmv

/-- Softmax is invariant under a common score offset.  Used in the proof of `lem:conf-stability`
(conference.tex): "The common score offset cancels." -/
theorem softmax_add_const (a : ι → ℝ) (c : ℝ) :
    softmax (fun j => c + a j) = softmax a := by
  funext j
  simp only [softmax, Real.exp_add, ← mul_sum]
  have : 0 < Real.exp c := Real.exp_pos c
  rw [mul_div_mul_left _ _ this.ne']

/-- The attention mean `A(a, v)_c = ∑_j p_j(a) v_{j,c}`. -/
noncomputable def attn {κ : Type*} (a : ι → ℝ) (v : ι → κ → ℝ) (c : κ) : ℝ :=
  ∑ j, softmax a j * v j c

/-- Paper: `eq:conf-attention-Lip` (conference.tex), coordinatewise form: if the values `v` are
bounded by `K`, then `|A(a,v)_c - A(a',v')_c| ≤ ‖v - v'‖_∞ + 2K‖a - a'‖_∞`; full version
`eq:attentionstabilitymoment` (attention_moment_decoder.tex). -/
theorem attn_sub_le [Nonempty ι] {κ : Type*} (a a' : ι → ℝ) (v v' : ι → κ → ℝ)
    {K δa δv : ℝ} (hv : ∀ j c, |v j c| ≤ K) (ha : ∀ j, |a j - a' j| ≤ δa)
    (hvv : ∀ j c, |v j c - v' j c| ≤ δv) (c : κ) :
    |attn a v c - attn a' v' c| ≤ δv + 2 * K * δa := by
  have hsplit : attn a v c - attn a' v' c =
      ∑ j, (softmax a j - softmax a' j) * v j c + ∑ j, softmax a' j * (v j c - v' j c) := by
    simp only [attn, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    ring
  have hK : 0 ≤ K := (abs_nonneg _).trans (hv (Classical.arbitrary ι) c)
  rw [hsplit]
  have h1 : |∑ j, (softmax a j - softmax a' j) * v j c| ≤ K * (2 * δa) := by
    calc |∑ j, (softmax a j - softmax a' j) * v j c|
        ≤ ∑ j, |(softmax a j - softmax a' j) * v j c| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, K * |softmax a j - softmax a' j| := sum_le_sum fun j _ => by
          rw [abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hv j c) (abs_nonneg _)
      _ = K * ∑ j, |softmax a j - softmax a' j| := (mul_sum _ _ _).symm
      _ ≤ K * (2 * δa) := mul_le_mul_of_nonneg_left (softmax_l1_le a a' ha) hK
  have h2 : |∑ j, softmax a' j * (v j c - v' j c)| ≤ δv := by
    calc |∑ j, softmax a' j * (v j c - v' j c)|
        ≤ ∑ j, |softmax a' j * (v j c - v' j c)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, softmax a' j * δv := sum_le_sum fun j _ => by
          rw [abs_mul, abs_of_pos (softmax_pos a' j)]
          exact mul_le_mul_of_nonneg_left (hvv j c) (softmax_pos a' j).le
      _ = δv := by rw [← sum_mul, sum_softmax, one_mul]
  calc |∑ j, (softmax a j - softmax a' j) * v j c + ∑ j, softmax a' j * (v j c - v' j c)|
      ≤ |∑ j, (softmax a j - softmax a' j) * v j c| +
          |∑ j, softmax a' j * (v j c - v' j c)| := abs_add_le _ _
    _ ≤ K * (2 * δa) + δv := add_le_add h1 h2
    _ = δv + 2 * K * δa := by ring

/-- Paper: `eq:conf-attention-Lip` (conference.tex), with Mathlib's sup norms on arrays:
`‖A(a,v) - A(a',v')‖_∞ ≤ ‖v - v'‖_∞ + 2K‖a - a'‖_∞` whenever `‖v‖_∞ ≤ K`; full version
`eq:attentionstabilitymoment` (attention_moment_decoder.tex). -/
theorem attn_norm_sub_le [Nonempty ι] {κ : Type*} [Fintype κ] (a a' : ι → ℝ)
    (v v' : ι → κ → ℝ) {K : ℝ} (hv : ‖v‖ ≤ K) :
    ‖(fun c => attn a v c) - (fun c => attn a' v' c)‖ ≤ ‖v - v'‖ + 2 * K * ‖a - a'‖ := by
  have hK : 0 ≤ K := (norm_nonneg _).trans hv
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun c => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  apply attn_sub_le
  · intro j c
    rw [← Real.norm_eq_abs]
    exact ((norm_le_pi_norm (v j) c).trans (norm_le_pi_norm v j)).trans hv
  · intro j
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm (a - a') j
  · intro j c
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm ((v - v') j) c).trans (norm_le_pi_norm (v - v') j)

end Softmax

/-! ## Score perturbation -/

/-- Paper: `lem:conf-stability` (conference.tex): for scores `(β/n)⟨q,k⟩` over `n` coordinates,
with the keys `k` and the perturbed queries `q'` bounded by `K`, perturbations of size `δ_q` and
`δ_k` change the score by at most `β K (δ_q + δ_k)`; the bound holds exactly as stated, with no
product-error term.  Full version: proof of `lem:prefixstability`
(attention_moment_decoder.tex). -/
theorem score_perturbation {n : ℕ} (hn : 0 < n) {β K δq δk : ℝ} (hβ : 0 ≤ β)
    (q q' k k' : Fin n → ℝ) (hk : ∀ i, |k i| ≤ K) (hq' : ∀ i, |q' i| ≤ K)
    (hdq : ∀ i, |q i - q' i| ≤ δq) (hdk : ∀ i, |k i - k' i| ≤ δk) :
    |β / n * ∑ i, q i * k i - β / n * ∑ i, q' i * k' i| ≤ β * K * (δq + δk) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : 0 ≤ K := (abs_nonneg _).trans (hk ⟨0, hn⟩)
  have hsplit : β / n * ∑ i, q i * k i - β / n * ∑ i, q' i * k' i =
      β / n * (∑ i, (q i - q' i) * k i + ∑ i, q' i * (k i - k' i)) := by
    rw [← mul_sub, ← sum_add_distrib, ← sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit, abs_mul, abs_of_nonneg (by positivity)]
  have hb : |∑ i, (q i - q' i) * k i + ∑ i, q' i * (k i - k' i)| ≤ n * (δq * K + K * δk) := by
    calc |∑ i, (q i - q' i) * k i + ∑ i, q' i * (k i - k' i)|
        ≤ ∑ i, |(q i - q' i) * k i| + ∑ i, |q' i * (k i - k' i)| :=
          (abs_add_le _ _).trans (add_le_add (abs_sum_le_sum_abs _ _) (abs_sum_le_sum_abs _ _))
      _ ≤ ∑ _i : Fin n, δq * K + ∑ _i : Fin n, K * δk := by
          gcongr with i _ i _
          · rw [abs_mul]; exact mul_le_mul (hdq i) (hk i) (abs_nonneg _)
              ((abs_nonneg _).trans (hdq i))
          · rw [abs_mul]; exact mul_le_mul (hq' i) (hdk i) (abs_nonneg _) hK
      _ = n * (δq * K + K * δk) := by
          rw [sum_const, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
          ring
  calc β / n * |∑ i, (q i - q' i) * k i + ∑ i, q' i * (k i - k' i)|
      ≤ β / n * (n * (δq * K + K * δk)) := by gcongr
    _ = β * K * (δq + δk) := by field_simp

/-! ## Normalization -/

section Normalization

variable {n : ℕ}

/-- `v = ε + ‖h‖₂²/n`. -/
noncomputable def rmsVar (ε : ℝ) (h : Fin n → ℝ) : ℝ := ε + (∑ k, h k ^ 2) / n

/-- The unscaled normalization `N_ε(h) = h / √(ε + ‖h‖₂²/n)` of `sec:conf-model`
(conference.tex). -/
noncomputable def normalize (ε : ℝ) (h : Fin n → ℝ) (i : Fin n) : ℝ :=
  h i / Real.sqrt (rmsVar ε h)

/-- The Jacobian entries `δ_ij/√v - h_i h_j/(n v^(3/2))` of the proof of `lem:conf-stability`
(conference.tex). -/
noncomputable def jac (ε : ℝ) (h : Fin n → ℝ) (i j : Fin n) : ℝ :=
  (if i = j then 1 else 0) / Real.sqrt (rmsVar ε h) -
    h i * h j / (n * (rmsVar ε h * Real.sqrt (rmsVar ε h)))

/-- `‖h‖₂² ≥ 0`.  Auxiliary for `lem:conf-stability` (conference.tex). -/
theorem sum_sq_nonneg (h : Fin n → ℝ) : 0 ≤ ∑ k, h k ^ 2 :=
  sum_nonneg fun k _ => sq_nonneg (h k)

/-- `ε ≤ v = ε + ‖h‖₂²/n`.  Auxiliary for `lem:conf-stability` (conference.tex). -/
theorem le_rmsVar (ε : ℝ) (h : Fin n → ℝ) : ε ≤ rmsVar ε h := by
  rw [rmsVar]
  have := div_nonneg (sum_sq_nonneg h) (Nat.cast_nonneg n)
  linarith

/-- `v > 0` for `ε > 0`.  Auxiliary for `lem:conf-stability` (conference.tex). -/
theorem rmsVar_pos {ε : ℝ} (hε : 0 < ε) (h : Fin n → ℝ) : 0 < rmsVar ε h :=
  lt_of_lt_of_le hε (le_rmsVar ε h)

/-- Paper: `lem:conf-stability` (conference.tex): `‖N_ε(h)‖_∞ ≤ √n`; full version
`lem:prefixstability` (attention_moment_decoder.tex). -/
theorem abs_normalize_le {ε : ℝ} (hε : 0 < ε) (h : Fin n → ℝ) (i : Fin n) :
    |normalize ε h i| ≤ Real.sqrt n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Fin.pos i
  have hv := rmsVar_pos hε h
  rw [normalize, abs_div, abs_of_pos (Real.sqrt_pos.2 hv), div_le_iff₀ (Real.sqrt_pos.2 hv),
    ← Real.sqrt_mul hn.le, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  have hS : h i ^ 2 ≤ ∑ k, h k ^ 2 := single_le_sum (fun k _ => sq_nonneg (h k)) (mem_univ i)
  rw [rmsVar, mul_add, mul_div_cancel₀ _ hn.ne']
  nlinarith

/-- `∑_j J_ij d_j = d_i/√v - x_i ⟨x,d⟩/(n v^(3/2))`.  Auxiliary for the Jacobian formula in
`lem:conf-stability` (conference.tex). -/
theorem sum_jac_mul (ε : ℝ) (x d : Fin n → ℝ) (i : Fin n) :
    ∑ j, jac ε x i j * d j =
      d i / Real.sqrt (rmsVar ε x) -
        x i * (∑ j, x j * d j) / (n * (rmsVar ε x * Real.sqrt (rmsVar ε x))) := by
  simp only [jac, sub_mul, sum_sub_distrib]
  congr 1
  · simp only [div_mul_eq_mul_div, ite_mul, one_mul, zero_mul]
    rw [← sum_div]
    simp
  · rw [mul_sum, sum_div]
    refine sum_congr rfl fun j _ => ?_
    ring

/-- Paper: `lem:conf-stability` (conference.tex): the derivative of `N_ε` along the line
`s ↦ h + s d` is `∑_j J_ij d_j`, with the Jacobian entries `jac`; full version
`lem:prefixstability` (attention_moment_decoder.tex). -/
theorem hasDerivAt_normalize_line {ε : ℝ} (hε : 0 < ε) (h d : Fin n → ℝ) (i : Fin n) (s : ℝ) :
    HasDerivAt (fun s => normalize ε (fun k => h k + s * d k) i)
      (∑ j, jac ε (fun k => h k + s * d k) i j * d j) s := by
  have hlin : ∀ k, HasDerivAt (fun s => h k + s * d k) (d k) s := fun k => by
    simpa using ((hasDerivAt_id s).mul_const (d k)).const_add (h k)
  have hsqk : ∀ k, HasDerivAt (fun s => (h k + s * d k) ^ 2)
      (2 * (h k + s * d k) * d k) s := fun k => by
    have := (hlin k).pow 2
    convert this using 1
    simp
  have hsum : HasDerivAt (fun s => ∑ k, (h k + s * d k) ^ 2)
      (∑ k, 2 * (h k + s * d k) * d k) s :=
    HasDerivAt.fun_sum (fun k _ => hsqk k)
  have hvar : HasDerivAt (fun s => rmsVar ε (fun k => h k + s * d k))
      ((∑ k, 2 * (h k + s * d k) * d k) / n) s :=
    (hsum.div_const (n : ℝ)).const_add ε
  have hv : 0 < rmsVar ε (fun k => h k + s * d k) := rmsVar_pos hε _
  have hsqrt := hvar.sqrt hv.ne'
  have hq := (hlin i).div hsqrt (Real.sqrt_pos.2 hv).ne'
  convert hq using 1
  · funext s'
    simp only [normalize, Pi.div_apply]
  rw [sum_jac_mul]
  have hsum2 : ∑ k, 2 * (h k + s * d k) * d k = 2 * ∑ k, (h k + s * d k) * d k := by
    rw [mul_sum]; refine sum_congr rfl fun k _ => ?_; ring
  rw [hsum2]
  generalize hV : rmsVar ε (fun k => h k + s * d k) = V at hv ⊢
  have hsv : 0 < Real.sqrt V := Real.sqrt_pos.2 hv
  have hsq : Real.sqrt V ^ 2 = V := Real.sq_sqrt hv.le
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact absurd i.pos (lt_irrefl 0)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [hsq]
  field_simp
  rw [hsq]
  ring

/-- Paper: `lem:conf-stability` (conference.tex): the Jacobian of `N_ε` has entries
`∂N_i/∂h_j = δ_ij/√v - h_i h_j/(n v^(3/2))`, `v = ε + ‖h‖₂²/n`; full version
`lem:prefixstability` (attention_moment_decoder.tex). -/
theorem hasDerivAt_normalize_coord {ε : ℝ} (hε : 0 < ε) (h : Fin n → ℝ) (i j : Fin n) :
    HasDerivAt (fun s => normalize ε (fun k => h k + s * (if k = j then 1 else 0)) i)
      (jac ε h i j) 0 := by
  have := hasDerivAt_normalize_line hε h (fun k => if k = j then 1 else 0) i 0
  convert this using 1
  simp

/-- Paper: `lem:conf-stability` (conference.tex): every absolute row sum of the normalization
Jacobian is at most `(1+√n)/√ε`; full version `lem:prefixstability`
(attention_moment_decoder.tex). -/
theorem jac_row_sum_le {ε : ℝ} (hε : 0 < ε) (h : Fin n → ℝ) (i : Fin n) :
    ∑ j, |jac ε h i j| ≤ (1 + Real.sqrt n) / Real.sqrt ε := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Fin.pos i
  set v := rmsVar ε h with hvdef
  set S := ∑ k, h k ^ 2 with hSdef
  have hv : 0 < v := rmsVar_pos hε h
  have hεv : ε ≤ v := le_rmsVar ε h
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have hS0 : 0 ≤ S := sum_sq_nonneg h
  have hterm : ∀ j, |jac ε h i j| ≤
      (if i = j then 1 else 0) / Real.sqrt v + |h i| * |h j| / (n * (v * Real.sqrt v)) := by
    intro j
    rw [jac]
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_div, abs_div, abs_of_pos hsv, abs_mul, abs_of_pos (by positivity : (0 : ℝ) <
      n * (v * Real.sqrt v))]
    split_ifs <;> simp
  have hsum : ∑ j, |jac ε h i j| ≤
      1 / Real.sqrt v + |h i| * (∑ j, |h j|) / (n * (v * Real.sqrt v)) := by
    calc ∑ j, |jac ε h i j|
        ≤ ∑ j, ((if i = j then 1 else 0) / Real.sqrt v +
            |h i| * |h j| / (n * (v * Real.sqrt v))) := sum_le_sum fun j _ => hterm j
      _ = 1 / Real.sqrt v + |h i| * (∑ j, |h j|) / (n * (v * Real.sqrt v)) := by
          rw [sum_add_distrib, mul_sum, sum_div]
          congr 1
          simp [ite_div]
  have h1 : |h i| ≤ Real.sqrt S :=
    Real.abs_le_sqrt (single_le_sum (fun k _ => sq_nonneg (h k)) (mem_univ i))
  have h2 : ∑ j, |h j| ≤ Real.sqrt n * Real.sqrt S := by
    rw [← Real.sqrt_mul hn.le]
    apply Real.le_sqrt_of_sq_le
    have cs := sum_mul_sq_le_sq_mul_sq univ (fun _ => (1 : ℝ)) (fun j => |h j|)
    simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, sq_abs] at cs
    exact cs
  have h3 : |h i| * ∑ j, |h j| ≤ Real.sqrt n * S := by
    calc |h i| * ∑ j, |h j| ≤ Real.sqrt S * (Real.sqrt n * Real.sqrt S) :=
          mul_le_mul h1 h2 (sum_nonneg fun j _ => abs_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt n * S := by
          rw [mul_left_comm, ← mul_assoc, mul_assoc, Real.mul_self_sqrt hS0]
  have h4 : S ≤ n * v := by
    rw [hvdef, rmsVar, mul_add, mul_div_cancel₀ _ hn.ne']
    nlinarith
  have h5 : |h i| * (∑ j, |h j|) / (n * (v * Real.sqrt v)) ≤ Real.sqrt n / Real.sqrt v := by
    rw [div_le_div_iff₀ (by positivity) hsv]
    calc |h i| * (∑ j, |h j|) * Real.sqrt v ≤ Real.sqrt n * S * Real.sqrt v := by gcongr
      _ ≤ Real.sqrt n * (n * v) * Real.sqrt v := by gcongr
      _ = Real.sqrt n * (n * (v * Real.sqrt v)) := by ring
  calc ∑ j, |jac ε h i j| ≤ 1 / Real.sqrt v + Real.sqrt n / Real.sqrt v := by linarith
    _ = (1 + Real.sqrt n) / Real.sqrt v := by ring
    _ ≤ (1 + Real.sqrt n) / Real.sqrt ε := by
        gcongr

/-- Paper: `lem:conf-stability` (conference.tex): the normalization is Lipschitz in the maximum
norm with constant `(1+√n)/√ε`, a consequence of the Jacobian row-sum bound; full version
`lem:prefixstability` (attention_moment_decoder.tex). -/
theorem normalize_lipschitz {ε : ℝ} (hε : 0 < ε) (h h' : Fin n → ℝ) {δ : ℝ}
    (hδ : ∀ k, |h k - h' k| ≤ δ) (i : Fin n) :
    |normalize ε h i - normalize ε h' i| ≤ (1 + Real.sqrt n) / Real.sqrt ε * δ := by
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ i)
  set d : Fin n → ℝ := fun k => h k - h' k with hd
  have hbound : ∀ s, ‖∑ j, jac ε (fun k => h' k + s * d k) i j * d j‖ ≤
      (1 + Real.sqrt n) / Real.sqrt ε * δ := by
    intro s
    rw [Real.norm_eq_abs]
    calc |∑ j, jac ε (fun k => h' k + s * d k) i j * d j|
        ≤ ∑ j, |jac ε (fun k => h' k + s * d k) i j * d j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |jac ε (fun k => h' k + s * d k) i j| * δ := sum_le_sum fun j _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hδ j) (abs_nonneg _)
      _ = (∑ j, |jac ε (fun k => h' k + s * d k) i j|) * δ := (sum_mul _ _ _).symm
      _ ≤ (1 + Real.sqrt n) / Real.sqrt ε * δ := by
          gcongr
          exact jac_row_sum_le hε _ i
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s => normalize ε (fun k => h' k + s * d k) i)
    (fun s _ => (hasDerivAt_normalize_line hε h' d i s).hasDerivWithinAt)
    (fun s _ => hbound s)
  have h1 : (fun k => h' k + (1 : ℝ) * d k) = h := by funext k; simp only [hd]; ring
  have h0 : (fun k => h' k + (0 : ℝ) * d k) = h' := by funext k; ring
  simpa only [h1, h0, Real.norm_eq_abs] using hmv

/-- Paper: `lem:conf-stability` (conference.tex): with `ε ≥ 2^(-b)`, the normalization Lipschitz
constant satisfies `(1+√n)/√ε ≤ (1+√n) √(2^b) = (1+√n) 2^(b/2)`; full version
`lem:prefixstability` (attention_moment_decoder.tex). -/
theorem normalize_lipschitz_const_le (b : ℕ) {ε : ℝ} (hε : ((2 : ℝ) ^ b)⁻¹ ≤ ε) :
    (1 + Real.sqrt n) / Real.sqrt ε ≤ (1 + Real.sqrt n) * Real.sqrt (2 ^ b) := by
  have h2b : (0 : ℝ) < 2 ^ b := by positivity
  have hε0 : 0 < ε := lt_of_lt_of_le (inv_pos.2 h2b) hε
  rw [div_le_iff₀ (Real.sqrt_pos.2 hε0), mul_assoc]
  have hprod : 1 ≤ Real.sqrt (2 ^ b) * Real.sqrt ε := by
    rw [← Real.sqrt_mul h2b.le]
    rw [Real.one_le_sqrt]
    calc (1 : ℝ) = 2 ^ b * (2 ^ b)⁻¹ := (mul_inv_cancel₀ h2b.ne').symm
      _ ≤ 2 ^ b * ε := by gcongr
  have h1n : 0 ≤ 1 + Real.sqrt n := by positivity
  nlinarith

end Normalization

/-! ## Lipschitz constants of the remaining primitives -/

/-- Paper: `lem:conf-stability` (conference.tex): an affine map whose absolute row sums are at
most `s` has Lipschitz constant at most `s` in the maximum norm. -/
theorem affine_lipschitz {m n : ℕ} (W : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x x' : Fin n → ℝ)
    {s δ : ℝ} (hW : ∀ i, ∑ j, |W i j| ≤ s) (hδ0 : 0 ≤ δ) (hx : ∀ j, |x j - x' j| ≤ δ)
    (i : Fin m) : |(∑ j, W i j * x j + b i) - (∑ j, W i j * x' j + b i)| ≤ s * δ := by
  rw [add_sub_add_right_eq_sub, ← sum_sub_distrib]
  calc |∑ j, (W i j * x j - W i j * x' j)| ≤ ∑ j, |W i j * x j - W i j * x' j| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |W i j| * δ := sum_le_sum fun j _ => by
        rw [← mul_sub, abs_mul]; exact mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _)
    _ = (∑ j, |W i j|) * δ := (sum_mul _ _ _).symm
    _ ≤ s * δ := mul_le_mul_of_nonneg_right (hW i) hδ0

/-- Paper: `lem:conf-stability` (conference.tex): tanh has Lipschitz constant at most one; its
derivative is `1/cosh² ∈ (0,1]`. -/
theorem tanh_lipschitz (x y : ℝ) : |Real.tanh x - Real.tanh y| ≤ |x - y| := by
  have hd : ∀ z, HasDerivAt Real.tanh (1 / Real.cosh z ^ 2) z := by
    intro z
    have h := (Real.hasDerivAt_sinh z).div (Real.hasDerivAt_cosh z) (Real.cosh_pos z).ne'
    have heq : (fun w => Real.sinh w / Real.cosh w) = Real.tanh :=
      funext fun w => (Real.tanh_eq_sinh_div_cosh w).symm
    have h' : HasDerivAt (fun w => Real.sinh w / Real.cosh w)
        ((Real.cosh z * Real.cosh z - Real.sinh z * Real.sinh z) / Real.cosh z ^ 2) z := h
    rw [heq] at h'
    convert h' using 1
    rw [← sq, ← sq, Real.cosh_sq_sub_sinh_sq]
  have hb : ∀ z ∈ (Set.univ : Set ℝ), ‖1 / Real.cosh z ^ 2‖ ≤ 1 := by
    intro z _
    have hc : 1 ≤ Real.cosh z := Real.one_le_cosh z
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_one (by positivity)]
    nlinarith
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (hd z).hasDerivWithinAt) hb convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using this

/-- Paper: `lem:conf-stability` (conference.tex): every cumulative probability
`F_i = ∑_{j ≤ i} p_j` of the output softmax changes by at most `2‖z - z'‖_∞`, a consequence of
`softmax_l1_le`. -/
theorem cumulative_softmax_lipschitz {V : ℕ} [NeZero V] (z z' : Fin V → ℝ) {δ : ℝ}
    (h : ∀ i, |z i - z' i| ≤ δ) (i : Fin V) :
    |∑ j ∈ univ.filter (· ≤ i), softmax z j - ∑ j ∈ univ.filter (· ≤ i), softmax z' j| ≤
      2 * δ := by
  rw [← sum_sub_distrib]
  calc |∑ j ∈ univ.filter (· ≤ i), (softmax z j - softmax z' j)|
      ≤ ∑ j ∈ univ.filter (· ≤ i), |softmax z j - softmax z' j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |softmax z j - softmax z' j| :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j _ _ => abs_nonneg _
    _ ≤ 2 * δ := softmax_l1_le z z' h

/-! ## Error induction through depth and the precision choice -/

/-- Paper: `lem:conf-stability` (conference.tex): if each of `J` stages is `L0`-Lipschitz and
each computed stage output has local error at most `δ`, then the final error is at most
`J L0^J δ`.  The stages map between arbitrary (pseudo)metric spaces, so the prefix arrays with
the maximum norm over positions are included; the exact and computed computations start from the
same exact input (the token embeddings).  Only `L0 ≥ 1` is needed; the paper takes `L0 ≥ 2`.
Full version: proof of `lem:prefixstability` (attention_moment_decoder.tex). -/
theorem error_induction {X : ℕ → Type*} [∀ k, PseudoMetricSpace (X k)]
    (f : ∀ k, X k → X (k + 1)) {L0 δ : ℝ} (hL : 1 ≤ L0) (hδ : 0 ≤ δ)
    (hf : ∀ k x y, dist (f k x) (f k y) ≤ L0 * dist x y)
    (x y : ∀ k, X k) (hx : ∀ k, x (k + 1) = f k (x k))
    (hy : ∀ k, dist (y (k + 1)) (f k (y k)) ≤ δ) (h0 : y 0 = x 0) (J : ℕ) :
    dist (y J) (x J) ≤ J * L0 ^ J * δ := by
  induction J with
  | zero => simp [h0]
  | succ k ih =>
    have hL0 : 0 ≤ L0 := by linarith
    have hpow : 1 ≤ L0 ^ (k + 1) := one_le_pow₀ hL
    calc dist (y (k + 1)) (x (k + 1))
        ≤ dist (y (k + 1)) (f k (y k)) + dist (f k (y k)) (f k (x k)) := by
          rw [hx k]; exact dist_triangle _ _ _
      _ ≤ δ + L0 * (k * L0 ^ k * δ) := add_le_add (hy k) ((hf k _ _).trans
          (mul_le_mul_of_nonneg_left ih hL0))
      _ = δ + k * L0 ^ (k + 1) * δ := by ring
      _ ≤ L0 ^ (k + 1) * δ + k * L0 ^ (k + 1) * δ := by
          gcongr
          calc δ = 1 * δ := (one_mul δ).symm
            _ ≤ L0 ^ (k + 1) * δ := by gcongr
      _ = ((k + 1 : ℕ) : ℝ) * L0 ^ (k + 1) * δ := by push_cast; ring

/-- `x ≤ 2^⌈log₂ x⌉` for `x > 0`.  Auxiliary for the precision choice in `lem:conf-stability`
(conference.tex). -/
theorem le_two_pow_ceil_logb {x : ℝ} (hx : 0 < x) : x ≤ (2 : ℝ) ^ ⌈Real.logb 2 x⌉₊ := by
  calc x = 2 ^ Real.logb 2 x := (Real.rpow_logb (by norm_num) (by norm_num) hx).symm
    _ ≤ 2 ^ (⌈Real.logb 2 x⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    _ = 2 ^ ⌈Real.logb 2 x⌉₊ := Real.rpow_natCast _ _

/-- Paper: `lem:conf-stability` (conference.tex): the precision choice
`P ≥ p + ⌈log₂(J+1)⌉ + J⌈log₂ L0⌉ + 10` gives `J L0^J 2^(-P) ≤ 2^(-p-10)`. -/
theorem precision_choice_sharp (p J P : ℕ) {L0 : ℝ} (hL : 2 ≤ L0)
    (hP : p + ⌈Real.logb 2 (J + 1)⌉₊ + J * ⌈Real.logb 2 L0⌉₊ + 10 ≤ P) :
    (J : ℝ) * L0 ^ J * (2 : ℝ) ^ (-(P : ℤ)) ≤ (2 : ℝ) ^ (-(p : ℤ) - 10) := by
  set a := ⌈Real.logb 2 ((J : ℝ) + 1)⌉₊
  set c := ⌈Real.logb 2 L0⌉₊
  have hJ : (J : ℝ) ≤ 2 ^ a :=
    (le_two_pow_ceil_logb (by positivity : (0 : ℝ) < J + 1)).trans' (by linarith)
  have hL0 : L0 ^ J ≤ ((2 : ℝ) ^ c) ^ J :=
    pow_le_pow_left₀ (by linarith) (le_two_pow_ceil_logb (by linarith)) J
  have hprod : (J : ℝ) * L0 ^ J ≤ (2 : ℝ) ^ ((a + c * J : ℕ) : ℤ) := by
    rw [zpow_natCast, pow_add, pow_mul]
    exact mul_le_mul hJ hL0 (by positivity) (by positivity)
  calc (J : ℝ) * L0 ^ J * (2 : ℝ) ^ (-(P : ℤ))
      ≤ (2 : ℝ) ^ ((a + c * J : ℕ) : ℤ) * (2 : ℝ) ^ (-(P : ℤ)) := by gcongr
    _ = (2 : ℝ) ^ (((a + c * J : ℕ) : ℤ) - P) := by
        rw [← zpow_add₀ (by norm_num)]; ring_nf
    _ ≤ (2 : ℝ) ^ (-(p : ℤ) - 10) := by
        apply zpow_le_zpow_right₀ (by norm_num)
        have : a + c * J + p + 10 ≤ P := by rw [mul_comm]; omega
        omega

/-- Paper: `lem:conf-stability` (conference.tex): with
`P ≥ p + ⌈log₂(J+1)⌉ + J⌈log₂ L0⌉ + 10` and `δ = 2^(-P)`, the propagated error bound
`J L0^J δ` is at most `2^(-p)`. -/
theorem precision_choice (p J P : ℕ) {L0 : ℝ} (hL : 2 ≤ L0)
    (hP : p + ⌈Real.logb 2 (J + 1)⌉₊ + J * ⌈Real.logb 2 L0⌉₊ + 10 ≤ P) :
    (J : ℝ) * L0 ^ J * (2 : ℝ) ^ (-(P : ℤ)) ≤ (2 : ℝ) ^ (-(p : ℤ)) :=
  (precision_choice_sharp p J P hL hP).trans
    (zpow_le_zpow_right₀ (by norm_num) (by omega))

/-- `⌈log₂(J+1)⌉ ≤ J + 1`.  Auxiliary for `eq:conf-P` (conference.tex). -/
theorem ceil_logb_succ_le (J : ℕ) : ⌈Real.logb 2 ((J : ℝ) + 1)⌉₊ ≤ J + 1 := by
  rw [Nat.ceil_le]
  have hpos : (0 : ℝ) < J + 1 := by positivity
  have h2 : ((J : ℝ) + 1) ≤ (2 : ℝ) ^ (J + 1) := by
    have : J + 1 < 2 ^ (J + 1) := Nat.lt_two_pow_self
    exact_mod_cast this.le
  calc Real.logb 2 ((J : ℝ) + 1) ≤ Real.logb 2 ((2 : ℝ) ^ (J + 1)) :=
        Real.logb_le_logb_of_le (by norm_num) hpos h2
    _ = ((J + 1 : ℕ) : ℝ) := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; push_cast; ring

/-- Paper: `eq:conf-P` (conference.tex), explicit arithmetic behind the working precision: with
`J ≤ c(D+1)` stages and `⌈log₂ L0⌉ ≤ ℓ`, the guard `⌈log₂(J+1)⌉ + J⌈log₂ L0⌉ + 10` is at most
`c(D+1)(ℓ+1) + 11`.  With `ℓ = O(b + log(n+s+β+2))` (see `ceil_logb_stageLip_le`) this is the
depth term `O((D+1)[b + log(n+s+β+2)])` of `eq:conf-P`. -/
theorem guard_le (J D c ℓ : ℕ) {L0 : ℝ} (hJ : J ≤ c * (D + 1))
    (hℓ : ⌈Real.logb 2 L0⌉₊ ≤ ℓ) :
    ⌈Real.logb 2 ((J : ℝ) + 1)⌉₊ + J * ⌈Real.logb 2 L0⌉₊ + 10 ≤ c * (D + 1) * (ℓ + 1) + 11 := by
  have hlog := ceil_logb_succ_le J
  have hJl : J * ⌈Real.logb 2 L0⌉₊ ≤ c * (D + 1) * ℓ := Nat.mul_le_mul hJ hℓ
  nlinarith

/-! ## The shifted softmax denominator -/

section Shift

variable {ι : Type*} [Fintype ι]

/-- Paper: `lem:conf-stability` (conference.tex): if some `z_i - A ≥ -1/4`, then
`∑_i e^(z_i - A) > 1/2`.  (The paper also has `z_i - A ≤ 0` for all `i`; that hypothesis is not
needed for this lower bound.) -/
theorem shifted_sum_exp_gt (z : ι → ℝ) (A : ℝ) (i₀ : ι)
    (hi₀ : -(1 / 4) ≤ z i₀ - A) : 1 / 2 < ∑ i, Real.exp (z i - A) := by
  have h1 : Real.exp (z i₀ - A) ≤ ∑ i, Real.exp (z i - A) :=
    single_le_sum (f := fun i => Real.exp (z i - A)) (fun i _ => (Real.exp_pos _).le)
      (mem_univ i₀)
  have h2 : (z i₀ - A) + 1 ≤ Real.exp (z i₀ - A) := Real.add_one_le_exp _
  linarith

/-- Paper: `lem:conf-stability` (conference.tex): enclose each logit to width `1/4` and take `A`
as the largest upper endpoint.  Then `z_i - A ≤ 0` for all `i`, some `z_i - A ≥ -1/4`, and
consequently `∑_i e^(z_i - A) > 1/2`. -/
theorem shift_from_enclosures [Nonempty ι] (z lo hi : ι → ℝ) (hlo : ∀ i, lo i ≤ z i)
    (hhi : ∀ i, z i ≤ hi i) (hw : ∀ i, hi i - lo i ≤ 1 / 4) :
    (∀ i, z i - univ.sup' univ_nonempty hi ≤ 0) ∧
      (∃ i₀, -(1 / 4) ≤ z i₀ - univ.sup' univ_nonempty hi) ∧
      1 / 2 < ∑ i, Real.exp (z i - univ.sup' univ_nonempty hi) := by
  set A := univ.sup' univ_nonempty hi
  have hle : ∀ i, z i - A ≤ 0 := fun i => by
    have : hi i ≤ A := le_sup' hi (mem_univ i)
    linarith [hhi i]
  obtain ⟨i₀, -, hi₀⟩ := exists_mem_eq_sup' (univ_nonempty (α := ι)) hi
  have hA : A = hi i₀ := hi₀
  have hge : -(1 / 4) ≤ z i₀ - A := by
    rw [hA]; linarith [hlo i₀, hw i₀]
  exact ⟨hle, ⟨i₀, hge⟩, shifted_sum_exp_gt z A i₀ hge⟩

end Shift

/-! ## Coordinate bounds and the residual range -/

/-- An affine map with absolute row sums and bias bounded by `s` maps `‖x‖_∞ ≤ R` into
`‖Wx + b‖_∞ ≤ sR + s`.  Auxiliary step for `lem:conf-stability` (conference.tex). -/
theorem affine_bound {m n : ℕ} (W : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ)
    {s R : ℝ} (hW : ∀ i, ∑ j, |W i j| ≤ s) (hb : ∀ i, |b i| ≤ s) (hx : ∀ j, |x j| ≤ R)
    (hR : 0 ≤ R) (i : Fin m) : |∑ j, W i j * x j + b i| ≤ s * R + s := by
  calc |∑ j, W i j * x j + b i| ≤ ∑ j, |W i j * x j| + |b i| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_sum_le_sum_abs _ _) _)
    _ ≤ ∑ j, |W i j| * R + s := by
        gcongr with j
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _)
        · exact hb i
    _ = (∑ j, |W i j|) * R + s := by rw [sum_mul]
    _ ≤ s * R + s := by gcongr; exact hW i

/-- Paper: `lem:conf-stability` (conference.tex): queries, keys and values are affine images of
`N_ε(h)`, so they are bounded by `s(⌈√n⌉ + 1) ≤ K`. -/
theorem affine_normalize_bound {m n : ℕ} (W : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    {ε s K : ℝ} (hε : 0 < ε) (hW : ∀ i, ∑ j, |W i j| ≤ s) (hb : ∀ i, |b i| ≤ s)
    (hK : s * (⌈Real.sqrt n⌉₊ + 1) ≤ K) (h : Fin n → ℝ) (i : Fin m) :
    |∑ j, W i j * normalize ε h j + b i| ≤ K := by
  have hx : ∀ j, |normalize ε h j| ≤ (⌈Real.sqrt n⌉₊ : ℝ) :=
    fun j => (abs_normalize_le hε h j).trans (Nat.le_ceil _)
  calc |∑ j, W i j * normalize ε h j + b i| ≤ s * ⌈Real.sqrt n⌉₊ + s :=
        affine_bound W b _ hW hb hx (Nat.cast_nonneg _) i
    _ = s * (⌈Real.sqrt n⌉₊ + 1) := by ring
    _ ≤ K := hK

/-- A convex combination of values bounded by `K` is bounded by `K`: the attention output is
bounded by `K`.  Auxiliary step for `lem:conf-stability` (conference.tex). -/
theorem abs_attn_le {ι κ : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ) (v : ι → κ → ℝ) {K : ℝ}
    (hv : ∀ j c, |v j c| ≤ K) (c : κ) : |attn a v c| ≤ K := by
  calc |attn a v c| ≤ ∑ j, |softmax a j * v j c| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, softmax a j * K := sum_le_sum fun j _ => by
        rw [abs_mul, abs_of_pos (softmax_pos a j)]
        exact mul_le_mul_of_nonneg_left (hv j c) (softmax_pos a j).le
    _ = K := by rw [← sum_mul, sum_softmax, one_mul]

/-- Paper: `lem:conf-stability` (conference.tex): one residual block changes each coordinate by at
most `sK + s + 1`: the attention update is an affine image (row sums and bias at most `s`) of an
attention output bounded by `K`, the feedforward update is a coordinatewise tanh, and each update
may be multiplied by a coefficient in `[0,1]`. -/
theorem block_increment {n : ℕ} (W : Fin n → Fin n → ℝ) (b : Fin n → ℝ) (u g : Fin n → ℝ)
    {s K α₁ α₂ : ℝ} (hW : ∀ i, ∑ j, |W i j| ≤ s) (hb : ∀ i, |b i| ≤ s) (hu : ∀ j, |u j| ≤ K)
    (hK : 0 ≤ K) (hα₁ : α₁ ∈ Set.Icc (0 : ℝ) 1) (hα₂ : α₂ ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    |α₁ * (∑ j, W i j * u j + b i) + α₂ * Real.tanh (g i)| ≤ s * K + s + 1 := by
  have h1 := affine_bound W b u hW hb hu hK i
  have h2 := (Real.abs_tanh_lt_one (g i)).le
  calc |α₁ * (∑ j, W i j * u j + b i) + α₂ * Real.tanh (g i)|
      ≤ |α₁| * |∑ j, W i j * u j + b i| + |α₂| * |Real.tanh (g i)| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ 1 * (s * K + s) + 1 * 1 := by
        rw [abs_of_nonneg hα₁.1, abs_of_nonneg hα₂.1]
        gcongr
        · exact hα₁.2
        · exact hα₂.2
    _ = s * K + s + 1 := by ring

/-- A convex mixture `(1-λ)a + λb`, `λ ∈ [0,1]`, is bounded by `max |a| |b|`.  Auxiliary for the
residual range in `lem:conf-stability` (conference.tex), which allows convex residual
mixtures. -/
theorem abs_convex_mix_le {a b l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    |(1 - l) * a + l * b| ≤ max |a| |b| := by
  calc |(1 - l) * a + l * b| ≤ (1 - l) * |a| + l * |b| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hl0]
    _ ≤ (1 - l) * max |a| |b| + l * max |a| |b| :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hl0)
    _ = max |a| |b| := by ring

/-- Paper: `lem:conf-stability` (conference.tex): a residual step `h ↦ (1-λ)h + λu` with
`λ ∈ [0,1]` increases the coordinate range by at most `c` whenever `|u| ≤ |h| + c`.  This covers
the additive update `u = h + update` and the convex mixture with the update itself `u = update`,
when `|update| ≤ c` (for instance `c = sK + s + 1`, see `block_increment`). -/
theorem mix_step_le {h u l c : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hc : 0 ≤ c)
    (hu : |u| ≤ |h| + c) : |(1 - l) * h + l * u| ≤ |h| + c :=
  (abs_convex_mix_le hl0 hl1).trans (max_le (by linarith) hu)

/-- Paper: `lem:conf-stability` (conference.tex): the residual range is at most
`s + D(sK + s + 1)`: embeddings are bounded by `s` and each of the `D` blocks raises the
coordinate range by at most `sK + s + 1` (additive updates by `block_increment`, convex residual
mixtures by `mix_step_le`). -/
theorem residual_range {n : ℕ} (h : ℕ → Fin n → ℝ) {s K : ℝ}
    (h0 : ∀ i, |h 0 i| ≤ s) (hstep : ∀ d i, |h (d + 1) i| ≤ |h d i| + (s * K + s + 1))
    (D : ℕ) (i : Fin n) : |h D i| ≤ s + D * (s * K + s + 1) := by
  induction D with
  | zero => simpa using h0 i
  | succ d ih =>
    calc |h (d + 1) i| ≤ |h d i| + (s * K + s + 1) := hstep d i
      _ ≤ (s + d * (s * K + s + 1)) + (s * K + s + 1) := by linarith
      _ = s + ((d + 1 : ℕ) : ℝ) * (s * K + s + 1) := by push_cast; ring

/-- Paper: `lem:conf-stability` (conference.tex): for `x ≥ 1` there is a power of two `K` with
`x ≤ K < 2x`; applied to `x = s(⌈√n⌉+1)`. -/
theorem exists_two_pow_between {x : ℝ} (hx : 1 ≤ x) :
    ∃ k : ℕ, x ≤ (2 : ℝ) ^ k ∧ (2 : ℝ) ^ k < 2 * x := by
  have hex : ∃ k : ℕ, x ≤ (2 : ℝ) ^ k :=
    (pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)).imp fun _ hk => hk.le
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, pow_zero]; linarith
  · have hlt := Nat.find_min hex (Nat.sub_lt hpos one_pos)
    rw [not_le] at hlt
    calc (2 : ℝ) ^ Nat.find hex = 2 * 2 ^ (Nat.find hex - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hpos]
      _ < 2 * x := by linarith

/-! ## Scores in a bounded chart -/

/-- Paper: `lem:conf-stability` (conference.tex): in a chart `k = c₀ + A k_I` of the key space,
with `z = k_I / K`, the score is the common offset `(β/n)⟨q, c₀⟩` plus `⟨t, z⟩` with
`t = (βK/n) qᵀA`. -/
theorem chart_score {n r : ℕ} (β K : ℝ) (hK : K ≠ 0) (q c₀ : Fin n → ℝ)
    (A : Fin n → Fin r → ℝ) (kI : Fin r → ℝ) :
    β / n * ∑ i, q i * (c₀ i + ∑ l, A i l * kI l) =
      β / n * ∑ i, q i * c₀ i +
        ∑ l, (β * K / n * ∑ i, q i * A i l) * (kI l / K) := by
  simp only [mul_add, sum_add_distrib, mul_sum, sum_mul]
  rw [sum_comm (s := univ) (t := univ)]
  congr 1
  refine sum_congr rfl fun l _ => sum_congr rfl fun i _ => ?_
  field_simp

/-- Paper: `lem:conf-stability` (conference.tex): for `|q_i| ≤ K` and chart entries
`|A_il| ≤ 2`, the coefficient vector `t = (βK/n) qᵀA` satisfies `‖t‖₁ ≤ 2rβK²`. -/
theorem chart_coeff_l1 {n r : ℕ} {β K : ℝ} (hβ : 0 ≤ β) (q : Fin n → ℝ)
    (A : Fin n → Fin r → ℝ) (hq : ∀ i, |q i| ≤ K) (hA : ∀ i l, |A i l| ≤ 2) :
    ∑ l, |β * K / n * ∑ i, q i * A i l| ≤ 2 * r * β * K ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [univ_eq_empty, sum_empty, mul_zero, abs_zero, sum_const_zero]
    have hK : 0 ≤ K ^ 2 := sq_nonneg K
    positivity
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : 0 ≤ K := (abs_nonneg _).trans (hq ⟨0, hn⟩)
  have hterm : ∀ l, |β * K / n * ∑ i, q i * A i l| ≤ 2 * β * K ^ 2 := by
    intro l
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have hs : |∑ i, q i * A i l| ≤ n * (K * 2) := by
      calc |∑ i, q i * A i l| ≤ ∑ i, |q i * A i l| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, K * 2 := sum_le_sum fun i _ => by
            rw [abs_mul]; exact mul_le_mul (hq i) (hA i l) (abs_nonneg _) hK
        _ = n * (K * 2) := by simp
    calc β * K / n * |∑ i, q i * A i l| ≤ β * K / n * (n * (K * 2)) := by gcongr
      _ = 2 * β * K ^ 2 := by field_simp
  calc ∑ l, |β * K / n * ∑ i, q i * A i l| ≤ ∑ _l : Fin r, 2 * β * K ^ 2 :=
        sum_le_sum fun l _ => hterm l
    _ = 2 * r * β * K ^ 2 := by simp; ring

/-- Paper: `lem:conf-stability` (conference.tex): chart coordinates `z = k_I / K` of keys bounded
by `K` lie in `[-1,1]^r`. -/
theorem chart_coord_le_one {r : ℕ} {K : ℝ} (hK : 0 < K) (kI : Fin r → ℝ)
    (hk : ∀ l, |kI l| ≤ K) (l : Fin r) : |kI l / K| ≤ 1 := by
  rw [abs_div, abs_of_pos hK, div_le_one hK]
  exact hk l

/-- Paper: `lem:conf-stability` (conference.tex): in the chart, the attention mean over the
keys `k_j = c₀ + A k_{I,j}` equals the ratio `∑_j e^⟨t,z_j⟩ v_j / ∑_j e^⟨t,z_j⟩` with
`t = (βK/n) qᵀA` and `z_j = k_{I,j}/K`, which is the quantity `A(t)` enclosed by the moment
evaluator of `lem:conf-moments` (conference.tex). -/
theorem attn_chart_eq {ι κ : Type*} [Fintype ι] {n r : ℕ} (β K : ℝ) (hK : K ≠ 0)
    (q c₀ : Fin n → ℝ) (A : Fin n → Fin r → ℝ) (kI : ι → Fin r → ℝ) (v : ι → κ → ℝ) (c : κ) :
    attn (fun j => β / n * ∑ i, q i * (c₀ i + ∑ l, A i l * kI j l)) v c =
      (∑ j, Real.exp (∑ l, (β * K / n * ∑ i, q i * A i l) * (kI j l / K)) * v j c) /
        ∑ j, Real.exp (∑ l, (β * K / n * ∑ i, q i * A i l) * (kI j l / K)) := by
  have hscore : (fun j => β / n * ∑ i, q i * (c₀ i + ∑ l, A i l * kI j l)) =
      fun j => β / n * ∑ i, q i * c₀ i +
        ∑ l, (β * K / n * ∑ i, q i * A i l) * (kI j l / K) :=
    funext fun j => chart_score β K hK q c₀ A (kI j)
  rw [hscore, attn, softmax_add_const]
  simp only [softmax]
  simp only [div_eq_mul_inv, sum_mul]
  refine sum_congr rfl fun j _ => ?_
  ring

/-! ## Causal attention over a prefix, uniformly in its length -/

/-- Causal attention at position `t` over the positions `j ≤ t`, with scores `(β/n)⟨q_t, k_j⟩`
(`eq:conf-attention`, conference.tex). -/
noncomputable def causalAttn {T n m : ℕ} (β : ℝ) (q k : Fin T → Fin n → ℝ)
    (v : Fin T → Fin m → ℝ) (t : Fin T) (c : Fin m) : ℝ :=
  attn (fun j : {j : Fin T // j ≤ t} => β / n * ∑ i, q t i * k j.1 i) (fun j => v j.1) c

/-- Every causal prefix `{j ≤ t}` is nonempty. -/
scoped instance nonempty_causalPrefix {T : ℕ} (t : Fin T) : Nonempty {j : Fin T // j ≤ t} :=
  ⟨⟨t, le_rfl⟩⟩

/-- Paper: `lem:conf-stability` (conference.tex): at every position `t` of a prefix of any
length `T`, causal attention computed from perturbed queries, keys and values (errors at most
`δ_q, δ_k, δ_v`, with keys, perturbed queries and values bounded by `K`) differs from the exact
output by at most `δ_v + 2K · βK(δ_q + δ_k)`.  The bound does not depend on `T`; this is the
statement that `eq:conf-attention-Lip` is uniform in prefix length. -/
theorem causalAttn_error {T n m : ℕ} (hn : 0 < n) {β K δq δk δv : ℝ} (hβ : 0 ≤ β)
    (q q' k k' : Fin T → Fin n → ℝ) (v v' : Fin T → Fin m → ℝ)
    (hk : ∀ j i, |k j i| ≤ K) (hq' : ∀ j i, |q' j i| ≤ K) (hv : ∀ j c, |v j c| ≤ K)
    (hdq : ∀ j i, |q j i - q' j i| ≤ δq) (hdk : ∀ j i, |k j i - k' j i| ≤ δk)
    (hdv : ∀ j c, |v j c - v' j c| ≤ δv) (t : Fin T) (c : Fin m) :
    |causalAttn β q k v t c - causalAttn β q' k' v' t c| ≤
      δv + 2 * K * (β * K * (δq + δk)) := by
  unfold causalAttn
  apply attn_sub_le
  · intro j c; exact hv j.1 c
  · intro j
    exact score_perturbation hn hβ (q t) (q' t) (k j.1) (k' j.1) (hk j.1) (hq' t) (hdq t)
      (hdk j.1)
  · intro j c; exact hdv j.1 c

/-! ## Layer maps on prefix arrays and the assembled depth induction -/

section Layers

variable {T n : ℕ}

/-- The affine map `x ↦ Wx + b`. -/
def affineMap {m k : ℕ} (W : Fin m → Fin k → ℝ) (b : Fin m → ℝ) (x : Fin k → ℝ) (i : Fin m) :
    ℝ :=
  ∑ j, W i j * x j + b i

/-- Absolute row sums and bias coordinates at most `s`, as in `sec:conf-model` (conference.tex). -/
def RowBounded {m k : ℕ} (W : Fin m → Fin k → ℝ) (b : Fin m → ℝ) (s : ℝ) : Prop :=
  (∀ i, ∑ j, |W i j| ≤ s) ∧ ∀ i, |b i| ≤ s

/-- Parameters of an attention sublayer (`eq:conf-attention`, conference.tex): affine query,
key, value and output maps and the coefficient `α` of the additive update. -/
structure AttnParams (n : ℕ) where
  /-- query weights -/
  WQ : Fin n → Fin n → ℝ
  /-- query bias -/
  bQ : Fin n → ℝ
  /-- key weights -/
  WK : Fin n → Fin n → ℝ
  /-- key bias -/
  bK : Fin n → ℝ
  /-- value weights -/
  WV : Fin n → Fin n → ℝ
  /-- value bias -/
  bV : Fin n → ℝ
  /-- output weights -/
  WO : Fin n → Fin n → ℝ
  /-- output bias -/
  bO : Fin n → ℝ
  /-- update coefficient -/
  α : ℝ

/-- Parameters of a feedforward sublayer: affine map before the tanh and update coefficient. -/
structure FFNParams (n : ℕ) where
  /-- weights -/
  WF : Fin n → Fin n → ℝ
  /-- bias -/
  bF : Fin n → ℝ
  /-- update coefficient -/
  α : ℝ

/-- The parameter bounds of `sec:conf-model` for an attention sublayer. -/
def AttnParams.Bounded (A : AttnParams n) (s : ℝ) : Prop :=
  RowBounded A.WQ A.bQ s ∧ RowBounded A.WK A.bK s ∧ RowBounded A.WV A.bV s ∧
    RowBounded A.WO A.bO s ∧ 0 ≤ A.α ∧ A.α ≤ 1

/-- The parameter bounds of `sec:conf-model` for a feedforward sublayer. -/
def FFNParams.Bounded (F : FFNParams n) (s : ℝ) : Prop :=
  RowBounded F.WF F.bF s ∧ 0 ≤ F.α ∧ F.α ≤ 1

/-- The attention sublayer on a prefix array `h : Fin T → ℝ^n` (`sec:conf-model`,
conference.tex): normalize each state, form affine queries, keys and values, take causal
attention over `j ≤ t`, apply the output map and add it with coefficient `α`. -/
noncomputable def attnLayer (ε β : ℝ) (A : AttnParams n) (h : Fin T → Fin n → ℝ) :
    Fin T → Fin n → ℝ :=
  fun t i => h t i + A.α * affineMap A.WO A.bO
    (causalAttn β (fun t' => affineMap A.WQ A.bQ (normalize ε (h t')))
      (fun t' => affineMap A.WK A.bK (normalize ε (h t')))
      (fun t' => affineMap A.WV A.bV (normalize ε (h t'))) t) i

/-- The feedforward sublayer on a prefix array: a second normalization, an affine map and a
coordinatewise tanh, added with coefficient `α` (`sec:conf-model`, conference.tex). -/
noncomputable def ffnLayer (ε : ℝ) (F : FFNParams n) (h : Fin T → Fin n → ℝ) :
    Fin T → Fin n → ℝ :=
  fun t i => h t i + F.α * Real.tanh (affineMap F.WF F.bF (normalize ε (h t)) i)

/-- The normalization Lipschitz constant `Λ = (1+√n)/√ε`. -/
noncomputable def normLip (n : ℕ) (ε : ℝ) : ℝ := (1 + Real.sqrt n) / Real.sqrt ε

/-- The common stage constant `L = 1 + s² Λ (1 + 4βK²)`. -/
noncomputable def stageLip (n : ℕ) (ε β s K : ℝ) : ℝ :=
  1 + s ^ 2 * normLip n ε * (1 + 4 * β * K ^ 2)

/-- `Λ ≥ 0`.  Auxiliary for `lem:conf-stability` (conference.tex). -/
theorem normLip_nonneg (n : ℕ) (ε : ℝ) : 0 ≤ normLip n ε :=
  div_nonneg (by positivity) (Real.sqrt_nonneg _)

/-- `L ≥ 1`.  Auxiliary for `lem:conf-stability` (conference.tex). -/
theorem one_le_stageLip (n : ℕ) {ε β s K : ℝ} (hβ : 0 ≤ β) : 1 ≤ stageLip n ε β s K := by
  have h1 : 0 ≤ 1 + 4 * β * K ^ 2 := by nlinarith [sq_nonneg K]
  have := mul_nonneg (mul_nonneg (sq_nonneg s) (normLip_nonneg n ε)) h1
  unfold stageLip; linarith

/-- Paper: `lem:conf-stability` (conference.tex): the attention sublayer is Lipschitz on prefix
arrays in the maximum norm over positions and coordinates, with constant
`L = 1 + s² (1+√n)/√ε (1 + 4βK²)` independent of the prefix length `T`.  No boundedness of the
input is needed, because queries, keys and values are formed from normalized states and are
therefore bounded by `K ≥ s(⌈√n⌉+1)`. -/
theorem attnLayer_sub_le {ε β s K δ : ℝ} (hε : 0 < ε) (hβ : 0 ≤ β) (hn : 0 < n)
    (A : AttnParams n) (hA : A.Bounded s) (hK : s * (⌈Real.sqrt n⌉₊ + 1) ≤ K)
    (h h' : Fin T → Fin n → ℝ) (hδ : ∀ t i, |h t i - h' t i| ≤ δ) (t : Fin T) (i : Fin n) :
    |attnLayer ε β A h t i - attnLayer ε β A h' t i| ≤ stageLip n ε β s K * δ := by
  obtain ⟨hQ, hKm, hV, hO, hα0, hα1⟩ := hA
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ t i)
  have hs : 0 ≤ s := (abs_nonneg _).trans (hQ.2 ⟨0, hn⟩)
  have hΛ := normLip_nonneg n ε
  have hN : ∀ t' j, |normalize ε (h t') j - normalize ε (h' t') j| ≤ normLip n ε * δ :=
    fun t' j => normalize_lipschitz hε (h t') (h' t') (hδ t') j
  have hNδ : 0 ≤ normLip n ε * δ := mul_nonneg hΛ hδ0
  set q := fun t' => affineMap A.WQ A.bQ (normalize ε (h t')) with hq_def
  set q' := fun t' => affineMap A.WQ A.bQ (normalize ε (h' t')) with hq'_def
  set k := fun t' => affineMap A.WK A.bK (normalize ε (h t')) with hk_def
  set k' := fun t' => affineMap A.WK A.bK (normalize ε (h' t')) with hk'_def
  set v := fun t' => affineMap A.WV A.bV (normalize ε (h t')) with hv_def
  set v' := fun t' => affineMap A.WV A.bV (normalize ε (h' t')) with hv'_def
  have hdq : ∀ t' j, |q t' j - q' t' j| ≤ s * (normLip n ε * δ) :=
    fun t' j => affine_lipschitz A.WQ A.bQ _ _ hQ.1 hNδ (hN t') j
  have hdk : ∀ t' j, |k t' j - k' t' j| ≤ s * (normLip n ε * δ) :=
    fun t' j => affine_lipschitz A.WK A.bK _ _ hKm.1 hNδ (hN t') j
  have hdv : ∀ t' j, |v t' j - v' t' j| ≤ s * (normLip n ε * δ) :=
    fun t' j => affine_lipschitz A.WV A.bV _ _ hV.1 hNδ (hN t') j
  have hkb : ∀ t' j, |k t' j| ≤ K :=
    fun t' j => affine_normalize_bound A.WK A.bK hε hKm.1 hKm.2 hK (h t') j
  have hqb : ∀ t' j, |q' t' j| ≤ K :=
    fun t' j => affine_normalize_bound A.WQ A.bQ hε hQ.1 hQ.2 hK (h' t') j
  have hvb : ∀ t' j, |v t' j| ≤ K :=
    fun t' j => affine_normalize_bound A.WV A.bV hε hV.1 hV.2 hK (h t') j
  set e := s * (normLip n ε * δ) * (1 + 4 * β * K ^ 2) with he_def
  have he0 : 0 ≤ e := mul_nonneg (mul_nonneg hs hNδ) (by nlinarith [sq_nonneg K])
  have hu : ∀ c, |causalAttn β q k v t c - causalAttn β q' k' v' t c| ≤ e := fun c =>
    (causalAttn_error hn hβ q q' k k' v v' hkb hqb hvb hdq hdk hdv t c).trans
      (le_of_eq (by rw [he_def]; ring))
  have hO' := affine_lipschitz A.WO A.bO (causalAttn β q k v t) (causalAttn β q' k' v' t)
    hO.1 he0 hu i
  have hsplit : attnLayer ε β A h t i - attnLayer ε β A h' t i =
      (h t i - h' t i) + A.α * (affineMap A.WO A.bO (causalAttn β q k v t) i -
        affineMap A.WO A.bO (causalAttn β q' k' v' t) i) := by
    simp only [attnLayer, hq_def, hq'_def, hk_def, hk'_def, hv_def, hv'_def]
    ring
  rw [hsplit]
  calc |(h t i - h' t i) + A.α * (affineMap A.WO A.bO (causalAttn β q k v t) i -
        affineMap A.WO A.bO (causalAttn β q' k' v' t) i)|
      ≤ |h t i - h' t i| + A.α * |affineMap A.WO A.bO (causalAttn β q k v t) i -
        affineMap A.WO A.bO (causalAttn β q' k' v' t) i| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_of_nonneg hα0]
    _ ≤ δ + 1 * (s * e) := add_le_add (hδ t i) (mul_le_mul hα1 hO' (abs_nonneg _) zero_le_one)
    _ = stageLip n ε β s K * δ := by rw [he_def, stageLip]; ring

/-- Paper: `lem:conf-stability` (conference.tex): the feedforward sublayer is Lipschitz on prefix
arrays with constant `1 + sΛ`, uniformly in `T` (normalization, an affine map with Lipschitz
constant `s`, and tanh with constant one). -/
theorem ffnLayer_sub_le {ε s δ : ℝ} (hε : 0 < ε) (F : FFNParams n) (hF : F.Bounded s)
    (h h' : Fin T → Fin n → ℝ) (hδ : ∀ t i, |h t i - h' t i| ≤ δ) (t : Fin T) (i : Fin n) :
    |ffnLayer ε F h t i - ffnLayer ε F h' t i| ≤ (1 + s * normLip n ε) * δ := by
  obtain ⟨hW, hα0, hα1⟩ := hF
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ t i)
  have hNδ : 0 ≤ normLip n ε * δ := mul_nonneg (normLip_nonneg n ε) hδ0
  have hN : ∀ j, |normalize ε (h t) j - normalize ε (h' t) j| ≤ normLip n ε * δ :=
    fun j => normalize_lipschitz hε (h t) (h' t) (hδ t) j
  have ha := affine_lipschitz F.WF F.bF _ _ hW.1 hNδ hN i
  have htanh := (tanh_lipschitz (affineMap F.WF F.bF (normalize ε (h t)) i)
    (affineMap F.WF F.bF (normalize ε (h' t)) i)).trans ha
  have hsplit : ffnLayer ε F h t i - ffnLayer ε F h' t i =
      (h t i - h' t i) + F.α * (Real.tanh (affineMap F.WF F.bF (normalize ε (h t)) i) -
        Real.tanh (affineMap F.WF F.bF (normalize ε (h' t)) i)) := by
    simp only [ffnLayer]; ring
  rw [hsplit]
  calc |(h t i - h' t i) + F.α * (Real.tanh (affineMap F.WF F.bF (normalize ε (h t)) i) -
        Real.tanh (affineMap F.WF F.bF (normalize ε (h' t)) i))|
      ≤ |h t i - h' t i| + F.α * |Real.tanh (affineMap F.WF F.bF (normalize ε (h t)) i) -
        Real.tanh (affineMap F.WF F.bF (normalize ε (h' t)) i)| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_of_nonneg hα0]
    _ ≤ δ + 1 * (s * (normLip n ε * δ)) :=
        add_le_add (hδ t i) (mul_le_mul hα1 htanh (abs_nonneg _) zero_le_one)
    _ = (1 + s * normLip n ε) * δ := by ring

/-- The sup distance on prefix arrays is controlled coordinatewise.  Auxiliary for
`lem:conf-stability` (conference.tex). -/
theorem dist_le_of_coord {f g : Fin T → Fin n → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ t i, |f t i - g t i| ≤ r) : dist f g ≤ r :=
  (dist_pi_le_iff hr).2 fun t => (dist_pi_le_iff hr).2 fun i => by
    rw [Real.dist_eq]; exact h t i

/-- Each coordinate difference is at most the sup distance of prefix arrays.  Auxiliary for
`lem:conf-stability` (conference.tex). -/
theorem coord_le_dist (f g : Fin T → Fin n → ℝ) (t : Fin T) (i : Fin n) :
    |f t i - g t i| ≤ dist f g := by
  rw [← Real.dist_eq]
  exact (dist_le_pi_dist (f t) (g t) i).trans (dist_le_pi_dist f g t)

/-- The `k`-th stage of the residual stream: the attention sublayer of block `k/2` for even `k`
and its feedforward sublayer for odd `k`. -/
noncomputable def sublayer (ε β : ℝ) (A : ℕ → AttnParams n) (F : ℕ → FFNParams n) (k : ℕ)
    (h : Fin T → Fin n → ℝ) : Fin T → Fin n → ℝ :=
  if k % 2 = 0 then attnLayer ε β (A (k / 2)) h else ffnLayer ε (F (k / 2)) h

/-- Paper: `lem:conf-stability` (conference.tex): every stage of the residual stream is
`L`-Lipschitz on prefix arrays with the sup metric over positions, with the common constant
`L = stageLip n ε β s K`, independent of `T`. -/
theorem sublayer_dist_le {ε β s K : ℝ} (hε : 0 < ε) (hβ : 0 ≤ β) (hn : 0 < n) (hs : 1 ≤ s)
    (A : ℕ → AttnParams n) (F : ℕ → FFNParams n) (hA : ∀ d, (A d).Bounded s)
    (hF : ∀ d, (F d).Bounded s) (hK : s * (⌈Real.sqrt n⌉₊ + 1) ≤ K) (k : ℕ)
    (h h' : Fin T → Fin n → ℝ) :
    dist (sublayer ε β A F k h) (sublayer ε β A F k h') ≤ stageLip n ε β s K * dist h h' := by
  have hcoord := coord_le_dist h h'
  have hL0 : 0 ≤ stageLip n ε β s K * dist h h' :=
    mul_nonneg ((zero_le_one).trans (one_le_stageLip n hβ)) dist_nonneg
  have hffn : 1 + s * normLip n ε ≤ stageLip n ε β s K := by
    have hΛ := normLip_nonneg n ε
    have h1 : s * normLip n ε ≤ s ^ 2 * normLip n ε :=
      mul_le_mul_of_nonneg_right (by nlinarith) hΛ
    have h2 : s ^ 2 * normLip n ε ≤ s ^ 2 * normLip n ε * (1 + 4 * β * K ^ 2) :=
      le_mul_of_one_le_right (mul_nonneg (sq_nonneg s) hΛ) (by nlinarith [sq_nonneg K])
    unfold stageLip; linarith
  unfold sublayer
  split_ifs
  · exact dist_le_of_coord hL0 fun t i => attnLayer_sub_le hε hβ hn _ (hA _) hK h h' hcoord t i
  · exact dist_le_of_coord hL0 fun t i =>
      (ffnLayer_sub_le hε _ (hF _) h h' hcoord t i).trans
        (mul_le_mul_of_nonneg_right hffn dist_nonneg)

/-- Paper: `lem:conf-stability` (conference.tex): the depth induction instantiated for the
residual stream.  If the exact prefix arrays satisfy `x_{k+1} = stage_k(x_k)`, the computed
arrays have local error at most `δ` at every stage (maximum over all positions and
coordinates), and both start from the same embeddings, then after `J` stages the error is at
most `J L^J δ`, independently of the prefix length `T`. -/
theorem residual_stream_error {ε β s K δ : ℝ} (hε : 0 < ε) (hβ : 0 ≤ β) (hn : 0 < n)
    (hs : 1 ≤ s) (hδ : 0 ≤ δ) (A : ℕ → AttnParams n) (F : ℕ → FFNParams n)
    (hA : ∀ d, (A d).Bounded s) (hF : ∀ d, (F d).Bounded s)
    (hK : s * (⌈Real.sqrt n⌉₊ + 1) ≤ K) (x y : ℕ → Fin T → Fin n → ℝ)
    (hx : ∀ k, x (k + 1) = sublayer ε β A F k (x k))
    (hy : ∀ k, dist (y (k + 1)) (sublayer ε β A F k (y k)) ≤ δ) (h0 : y 0 = x 0) (J : ℕ) :
    dist (y J) (x J) ≤ J * stageLip n ε β s K ^ J * δ :=
  error_induction (X := fun _ => Fin T → Fin n → ℝ) (fun k => sublayer ε β A F k)
    (one_le_stageLip n hβ) hδ (fun k => sublayer_dist_le hε hβ hn hs A F hA hF hK k) x y hx hy
    h0 J

/-- The cumulative probabilities `F_i = ∑_{j ≤ i} p_j(z)` of the output softmax. -/
noncomputable def cumProb {V : ℕ} (z : Fin V → ℝ) (i : Fin V) : ℝ :=
  ∑ j ∈ univ.filter (· ≤ i), softmax z j

/-- Paper: `lem:conf-stability` (conference.tex): the assembled error bound.  After the `2D`
sublayers of `D` blocks, the affine head and the cumulative softmax, each computed with local
error at most `δ`, every cumulative probability at every position is within
`(2D+2) L0^(2D+2) δ` of its exact value, for any `L0 ≥ max(L, s, 2)`; the bound does not depend
on the prefix length `T`. -/
theorem prefix_network_error {V : ℕ} [NeZero V] {ε β s K δ L0 : ℝ} (hε : 0 < ε) (hβ : 0 ≤ β)
    (hn : 0 < n) (hs : 1 ≤ s) (hδ : 0 ≤ δ) (A : ℕ → AttnParams n) (F : ℕ → FFNParams n)
    (hA : ∀ d, (A d).Bounded s) (hF : ∀ d, (F d).Bounded s)
    (hK : s * (⌈Real.sqrt n⌉₊ + 1) ≤ K) (D : ℕ) (WH : Fin V → Fin n → ℝ) (bH : Fin V → ℝ)
    (hH : RowBounded WH bH s) (x y : ℕ → Fin T → Fin n → ℝ)
    (hx : ∀ k, x (k + 1) = sublayer ε β A F k (x k))
    (hy : ∀ k, dist (y (k + 1)) (sublayer ε β A F k (y k)) ≤ δ) (h0 : y 0 = x 0)
    (zt : Fin T → Fin V → ℝ) (hz : ∀ t j, |zt t j - affineMap WH bH (y (2 * D) t) j| ≤ δ)
    (Ft : Fin T → Fin V → ℝ) (hFt : ∀ t i, |Ft t i - cumProb (zt t) i| ≤ δ)
    (hL : stageLip n ε β s K ≤ L0) (hLs : s ≤ L0) (hL2 : 2 ≤ L0) (t : Fin T) (i : Fin V) :
    |Ft t i - cumProb (affineMap WH bH (x (2 * D) t)) i| ≤
      ((2 * D + 2 : ℕ) : ℝ) * L0 ^ (2 * D + 2) * δ := by
  have hres := residual_stream_error hε hβ hn hs hδ A F hA hF hK x y hx hy h0 (2 * D)
  set e := dist (y (2 * D)) (x (2 * D)) with he_def
  have hQ1 : 1 ≤ L0 ^ (2 * D) := one_le_pow₀ (by linarith)
  have he : e ≤ (2 * D : ℕ) * L0 ^ (2 * D) * δ := by
    refine hres.trans ?_
    gcongr
    · exact (zero_le_one).trans (one_le_stageLip n hβ)
  have he0 : 0 ≤ e := dist_nonneg
  have hs0 : 0 ≤ s := by linarith
  -- logits
  have hlog : ∀ j, |zt t j - affineMap WH bH (x (2 * D) t) j| ≤ δ + s * e := by
    intro j
    have h1 := affine_lipschitz WH bH (y (2 * D) t) (x (2 * D) t) hH.1 he0
      (fun l => coord_le_dist _ _ t l) j
    calc |zt t j - affineMap WH bH (x (2 * D) t) j|
        ≤ |zt t j - affineMap WH bH (y (2 * D) t) j| +
            |affineMap WH bH (y (2 * D) t) j - affineMap WH bH (x (2 * D) t) j| :=
          abs_sub_le _ _ _
      _ ≤ δ + s * e := add_le_add (hz t j) h1
  have hcum := cumulative_softmax_lipschitz (zt t) (affineMap WH bH (x (2 * D) t)) hlog i
  have htot : |Ft t i - cumProb (affineMap WH bH (x (2 * D) t)) i| ≤ δ + 2 * (δ + s * e) :=
    (abs_sub_le _ (cumProb (zt t) i) _).trans (add_le_add (hFt t i) hcum)
  refine htot.trans ?_
  set Q := L0 ^ (2 * D) with hQ_def
  have hpow : L0 ^ (2 * D + 2) = Q * L0 ^ 2 := by rw [hQ_def, pow_add]
  rw [hpow]
  have hse : s * e ≤ L0 * ((2 * D : ℕ) * Q * δ) := mul_le_mul hLs he he0 (by linarith)
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hQ0 : 0 ≤ Q := by linarith
  push_cast at hse ⊢
  have h1 : 0 ≤ D * Q * δ * L0 * (L0 - 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hD0 hQ0) hδ) (by linarith)) (by linarith)
  have h4 : 4 ≤ Q * L0 ^ 2 := by nlinarith
  have h2 : 0 ≤ (Q * L0 ^ 2 - 4) * δ := mul_nonneg (by linarith) hδ
  calc δ + 2 * (δ + s * e) ≤ δ + 2 * (δ + L0 * (2 * D * Q * δ)) := by linarith
    _ = 3 * δ + 4 * (D * Q * δ * L0) := by ring
    _ ≤ (2 * D + 2) * (Q * L0 ^ 2) * δ := by nlinarith

/-- Paper: `lem:conf-stability` (conference.tex): under the paper's choices `ε ≥ 2^(-b)`,
`s ≥ 1` and `K < 2s(⌈√n⌉+1)`, the stage constant satisfies `L ≤ 18 M^8 2^b` with
`M = n + s + β + 2`; also `s ≤ 18 M^8 2^b` and `2 ≤ 18 M^8 2^b`.  Hence
`log₂ L0 = O(b + log(n+s+β+2))` for `L0 = 18 M^8 2^b`. -/
theorem stageLip_le (b : ℕ) {ε β s K : ℝ} (hε : ((2 : ℝ) ^ b)⁻¹ ≤ ε) (hβ : 0 ≤ β)
    (hs : 1 ≤ s) (hK0 : 0 ≤ K) (hK : K ≤ 2 * s * (⌈Real.sqrt n⌉₊ + 1)) :
    stageLip n ε β s K ≤ 18 * ((n : ℝ) + s + β + 2) ^ 8 * 2 ^ b ∧
      s ≤ 18 * ((n : ℝ) + s + β + 2) ^ 8 * 2 ^ b ∧
      2 ≤ 18 * ((n : ℝ) + s + β + 2) ^ 8 * 2 ^ b := by
  set M := (n : ℝ) + s + β + 2 with hM_def
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hM1 : 1 ≤ M := by linarith
  have hM0 : 0 ≤ M := by linarith
  have h2b : (1 : ℝ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  have hsqrt : Real.sqrt n ≤ n + 1 := by
    rw [Real.sqrt_le_iff]; constructor <;> nlinarith
  have hceil : (⌈Real.sqrt n⌉₊ : ℝ) ≤ Real.sqrt n + 1 :=
    (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le
  have hsM : s ≤ M := by linarith
  have hβM : β ≤ M := by linarith
  have hKM : K ≤ 2 * M ^ 2 := by
    have : (⌈Real.sqrt n⌉₊ : ℝ) + 1 ≤ M := by linarith
    calc K ≤ 2 * s * (⌈Real.sqrt n⌉₊ + 1) := hK
      _ ≤ 2 * M * M := by gcongr
      _ = 2 * M ^ 2 := by ring
  have hΛ : normLip n ε ≤ M * 2 ^ b := by
    have h1 := normalize_lipschitz_const_le (n := n) b hε
    have h2 : Real.sqrt (2 ^ b) ≤ 2 ^ b := by
      rw [Real.sqrt_le_iff]; constructor <;> nlinarith
    have h3 : 1 + Real.sqrt n ≤ M := by linarith
    calc normLip n ε = (1 + Real.sqrt n) / Real.sqrt ε := rfl
      _ ≤ (1 + Real.sqrt n) * Real.sqrt (2 ^ b) := h1
      _ ≤ M * 2 ^ b := mul_le_mul h3 h2 (Real.sqrt_nonneg _) hM0
  have hM5 : 1 ≤ M ^ 5 := one_le_pow₀ hM1
  have hβK : 1 + 4 * β * K ^ 2 ≤ 17 * M ^ 5 := by
    have hK2 : K ^ 2 ≤ (2 * M ^ 2) ^ 2 := pow_le_pow_left₀ hK0 hKM 2
    have : 4 * β * K ^ 2 ≤ 4 * M * (2 * M ^ 2) ^ 2 :=
      mul_le_mul (by linarith) hK2 (sq_nonneg K) (by linarith)
    nlinarith
  have hs2 : s ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (by linarith) hsM 2
  have hprod : s ^ 2 * normLip n ε * (1 + 4 * β * K ^ 2) ≤ M ^ 2 * (M * 2 ^ b) * (17 * M ^ 5) :=
    mul_le_mul (mul_le_mul hs2 hΛ (normLip_nonneg n ε) (sq_nonneg M)) hβK
      (by nlinarith [sq_nonneg K]) (by positivity)
  have hM8 : 1 ≤ M ^ 8 * 2 ^ b := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM1) h2b
  have hM8' : M ≤ M ^ 8 * 2 ^ b := by
    calc M = M ^ 1 * 1 := by ring
      _ ≤ M ^ 8 * 2 ^ b := mul_le_mul (pow_le_pow_right₀ hM1 (by norm_num)) h2b zero_le_one
          (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · have : M ^ 2 * (M * 2 ^ b) * (17 * M ^ 5) = 17 * (M ^ 8 * 2 ^ b) := by ring
    unfold stageLip; linarith
  · linarith
  · linarith

/-- Paper: `lem:conf-stability` (conference.tex): `⌈log₂(18 M^8 2^b)⌉ ≤ b + 5 + 8⌈log₂ M⌉`, so
`log₂ L0 = O(b + log(n+s+β+2))`. -/
theorem ceil_logb_stageLip_le (b : ℕ) {M : ℝ} (hM : 1 ≤ M) :
    ⌈Real.logb 2 (18 * M ^ 8 * 2 ^ b)⌉₊ ≤ b + 5 + 8 * ⌈Real.logb 2 M⌉₊ := by
  set c := ⌈Real.logb 2 M⌉₊
  have hMc : M ≤ (2 : ℝ) ^ c := le_two_pow_ceil_logb (by linarith)
  have hle : 18 * M ^ 8 * 2 ^ b ≤ (2 : ℝ) ^ (b + 5 + 8 * c) := by
    have h8 : M ^ 8 ≤ ((2 : ℝ) ^ c) ^ 8 := pow_le_pow_left₀ (by linarith) hMc 8
    calc 18 * M ^ 8 * 2 ^ b ≤ 2 ^ 5 * ((2 : ℝ) ^ c) ^ 8 * 2 ^ b := by gcongr; norm_num
      _ = (2 : ℝ) ^ (b + 5 + 8 * c) := by
          rw [← pow_mul, ← pow_add, ← pow_add]; ring_nf
  rw [Nat.ceil_le]
  have hpos : (0 : ℝ) < 18 * M ^ 8 * 2 ^ b := by positivity
  calc Real.logb 2 (18 * M ^ 8 * 2 ^ b) ≤ Real.logb 2 ((2 : ℝ) ^ (b + 5 + 8 * c)) :=
        Real.logb_le_logb_of_le (by norm_num) hpos hle
    _ = ((b + 5 + 8 * c : ℕ) : ℝ) := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

/-- Paper: `lem:conf-stability` and `eq:conf-P` (conference.tex), assembled certificate.  For
the model with `D` blocks (attention and feedforward sublayers with additive updates; convex
residual mixtures are not included), affine head and cumulative softmax, under
`ε ≥ 2^(-b)`, `s ≥ 1`, `s(⌈√n⌉+1) ≤ K ≤ 2s(⌈√n⌉+1)`, if every stage is computed with local
error at most `2^(-P)` and
`P ≥ p + ⌈log₂(2D+3)⌉ + (2D+2)(b + 5 + 8⌈log₂(n+s+β+2)⌉) + 10`, then every cumulative
probability at every position is within `2^(-p)`, for every prefix length `T`. -/
theorem stability_certificate {V : ℕ} [NeZero V] (b p P D : ℕ) {ε β s K : ℝ}
    (hε : ((2 : ℝ) ^ b)⁻¹ ≤ ε) (hβ : 0 ≤ β) (hn : 0 < n) (hs : 1 ≤ s)
    (A : ℕ → AttnParams n) (F : ℕ → FFNParams n)
    (hA : ∀ d, (A d).Bounded s) (hF : ∀ d, (F d).Bounded s)
    (hK : s * (⌈Real.sqrt n⌉₊ + 1) ≤ K) (hK2 : K ≤ 2 * s * (⌈Real.sqrt n⌉₊ + 1))
    (WH : Fin V → Fin n → ℝ) (bH : Fin V → ℝ) (hH : RowBounded WH bH s)
    (x y : ℕ → Fin T → Fin n → ℝ) (hx : ∀ k, x (k + 1) = sublayer ε β A F k (x k))
    (hy : ∀ k, dist (y (k + 1)) (sublayer ε β A F k (y k)) ≤ (2 : ℝ) ^ (-(P : ℤ)))
    (h0 : y 0 = x 0) (zt : Fin T → Fin V → ℝ)
    (hz : ∀ t j, |zt t j - affineMap WH bH (y (2 * D) t) j| ≤ (2 : ℝ) ^ (-(P : ℤ)))
    (Ft : Fin T → Fin V → ℝ) (hFt : ∀ t i, |Ft t i - cumProb (zt t) i| ≤ (2 : ℝ) ^ (-(P : ℤ)))
    (hP : p + ⌈Real.logb 2 (((2 * D + 2 : ℕ) : ℝ) + 1)⌉₊ +
      (2 * D + 2) * (b + 5 + 8 * ⌈Real.logb 2 ((n : ℝ) + s + β + 2)⌉₊) + 10 ≤ P)
    (t : Fin T) (i : Fin V) :
    |Ft t i - cumProb (affineMap WH bH (x (2 * D) t)) i| ≤ (2 : ℝ) ^ (-(p : ℤ)) := by
  have hε0 : 0 < ε := lt_of_lt_of_le (by positivity) hε
  have hK0 : 0 ≤ K := le_trans (by positivity) hK
  obtain ⟨hL, hLs, hL2⟩ := stageLip_le (n := n) b hε hβ hs hK0 hK2
  have herr := prefix_network_error hε0 hβ hn hs (by positivity) A F hA hF hK D WH bH hH x y hx
    hy h0 zt hz Ft hFt hL hLs hL2 t i
  refine herr.trans (precision_choice p (2 * D + 2) P hL2 ?_)
  have hM : (1 : ℝ) ≤ (n : ℝ) + s + β + 2 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hc := ceil_logb_stageLip_le b hM
  have hmul := Nat.mul_le_mul_left (2 * D + 2) hc
  omega

/-- Paper: `eq:conf-P` (conference.tex): the working precision of `stability_certificate`
exceeds `p` by at most `2(D+1)(b + 8⌈log₂(n+s+β+2)⌉ + 6) + 11`, which is
`O((D+1)[b + log(n+s+β+2)])`. -/
theorem stability_precision_le (b p D c : ℕ) :
    p + ⌈Real.logb 2 (((2 * D + 2 : ℕ) : ℝ) + 1)⌉₊ + (2 * D + 2) * (b + 5 + 8 * c) + 10 ≤
      p + 2 * (D + 1) * (b + 8 * c + 6) + 11 := by
  have h := ceil_logb_succ_le (2 * D + 2)
  nlinarith

end Layers

end ExactSampling.Stability
