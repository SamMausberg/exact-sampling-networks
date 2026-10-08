import Mathlib
import ExactSampling.Conference.RejectionLoop

/-!
# One bounded tanh row and the Poisson acceptance race

Paper: `conference.tex`, Section `sec:conf-scalar`: Proposition `prop:conf-row` (one bounded tanh
row), its proof (weighted choice, Poisson acceptance race, renewal count, finite-bit Poisson
draws), and the paragraph after it (the Poisson test for an attention index and the expected
predecessor count). The same constructions appear in the full version
`exact_sampling_networks.tex`: the related result `thm:new-single-row-law` (`tanh_single_row.tex`,
which uses a different tanh factory) for the row, and
`thm:attentionprimitive`, `lem:attentionraceexact`, `lem:stoppedpoissonattention` and
`lem:smallpoissonattention` (`attention_primitives.tex`) for the race.

## What is formalized

* The weighted choice among `sgn c` and `sgn(w_j) x_j` is a probability vector whose returned
  sign has mean `u / A`, and the derived bit has bias `(1 + Y u / A) / 2 ∈ [0, 1]`.
* The Poisson generating function `E pᴺ = exp(-λ(1-p))` for `N ∼ Pois(λ)`, stated with
  Mathlib's `poissonMeasure`, both as a series and as an integral; the Poisson mean.
* Acceptance `exp(Y u - A)` for `N ∼ Pois(2A)`; the one-trial masses `m(±1)` built from these
  Poisson series, the trial success probability `m(1) + m(-1) = e^{-A} cosh u ∈ [e^{-A}, 1]`,
  and the law `e^{yu}/(e^u + e^{-u})` and mean `tanh u` of the accepted sign.
* The renewal identity: if a trial succeeds with probability `s` and has expected cost `c`, the
  probability that trial `m` is reached is `(1-s)^m` and the expected total cost is
  `∑ₘ (1-s)^m c = c / s`; the law of the first accepted outcome is `α / s`.
  With `c = 2 ∑ |w_j| ≤ 2A` and `s ≥ e^{-A}` this gives at most `2A e^A ≤ 4e^2` requests.
  The output sign of the row sampler is `+1` with probability `e^u / (e^u + e^{-u})`.
* The finite-bit Poisson sampler: geometric proposal `2^{-(K+1)}`, acceptance
  `e^{-λ}(2λ)^K/(128 K!) ≤ e^4/128 < 1` for `λ ≤ 4`, accepted mass `e^{-λ}λ^K/(256 K!)`, trial
  success probability `1/256`, Poisson law of the accepted count, and the rational-factor bound
  `(2λ)^K/(128 K!) ≤ e^8/128 < 52`.
* The attention race: a proposal `j` is accepted with probability `exp(a_j - A)`, the
  first-acceptance series gives the softmax law, the stopped Poisson test count of
  `lem:stoppedpoissonattention` and its ratio bound, and the predecessor bound `2e^{2A} - 1`.
* Independent trials on a probability space (`row_sampler_iid`, `attention_race_iid`, using the
  module `ExactSampling.RejectionLoop`): with the one-trial laws above, the output sign of the
  row sampler is `y` with probability `e^{yu}/(e^u + e^{-u})` and its expected request count is
  `2 ∑ⱼ |wⱼ| / (e^{-A} cosh u) ≤ 2A e^A ≤ 4e^2`; the attention race returns the softmax index
  with expected score tests at most `e^{2A} - 1`, predecessor count at most `2e^{2A} - 1`, and
  proposals at most `e^{2A}`.

## What is not formalized

The bit-complexity accounting (the `O(nB^2)` preprocessing, integer cumulative weights,
certified exponential enclosures, the `O(B^4)` expected bit work, and the uniform-comparison
tails) is out of scope. In this module repeated trials are summarized by the renewal series, in
which trial `m` is reached with probability `(1-s)^m` and contributes its own success mass or
expected cost; the module `ExactSampling.RejectionLoop` derives this series from mutually
independent, identically distributed trials, and `row_sampler_iid`, `attention_race_iid` apply it.
In those corollaries the one-trial law is a hypothesis matching the construction (the
acceptance masses as Poisson series and the expected cost of one trial); the internal
randomness of one trial (Poisson count, coin flips, weighted choices) is not modeled as random
variables. The expected number of input requests of one trial is the Poisson average
`∑ₖ P(N = k) k ρ`, where `ρ` is the request probability of one weighted choice.
-/

open Real MeasureTheory ProbabilityTheory Finset
open scoped NNReal Nat

namespace ExactSampling.RowFactory

/-! ### Exponential series and the Poisson generating function -/

/-- The exponential series `∑ₖ xᵏ / k! = eˣ`. Auxiliary for the Poisson generating function in
the proof of `prop:conf-row` (conference.tex). -/
theorem hasSum_pow_div_factorial (x : ℝ) : HasSum (fun k : ℕ => x ^ k / k !) (exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

/-- Poisson probability generating function: for `N ∼ Pois(r)` and every real `p`,
`E pᴺ = exp(-r (1 - p))`. Paper: proof of `prop:conf-row` (conference.tex), "the Poisson
generating function gives acceptance", and proof of `lem:attentionraceexact`
(attention_primitives.tex). -/
theorem hasSum_poisson_pgf (r : ℝ≥0) (p : ℝ) :
    HasSum (fun k : ℕ => (poissonMeasure r).real {k} * p ^ k) (exp (-(r : ℝ) * (1 - p))) := by
  have h := (hasSum_pow_div_factorial ((r : ℝ) * p)).mul_left (exp (-(r : ℝ)))
  convert h using 1
  · funext k
    rw [poissonMeasure_real_singleton, mul_pow]
    ring
  · rw [← exp_add]
    ring_nf

/-- The Poisson generating function as an integral against `poissonMeasure`. Paper: proof of
`prop:conf-row` (conference.tex) and of `lem:attentionraceexact` (attention_primitives.tex). -/
theorem integral_poisson_pgf (r : ℝ≥0) (p : ℝ) :
    ∫ k, p ^ k ∂(poissonMeasure r) = exp (-(r : ℝ) * (1 - p)) := by
  rw [integral_poissonMeasure, ← (hasSum_poisson_pgf r p).tsum_eq]
  congr 1
  funext k
  rw [poissonMeasure_real_singleton, smul_eq_mul]

/-- The Poisson mean: `E N = r` for `N ∼ Pois(r)`. Paper: proof of `prop:conf-row`
(conference.tex), "its expected source count is at most `2A`". -/
theorem hasSum_poisson_mean (r : ℝ≥0) :
    HasSum (fun k : ℕ => (poissonMeasure r).real {k} * k) (r : ℝ) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, sub_zero]
  have h := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  rw [mul_one] at h
  convert h using 1
  funext k
  rw [poissonMeasure_real_singleton, Nat.factorial_succ]
  push_cast
  have hk : (k ! : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-! ### The renewal identity for repeated independent trials -/

/-- Renewal identity. If every trial succeeds with probability `s ∈ (0, 1]`, then trial `m` is
reached with probability `(1-s)^m`; a quantity `c` charged once per reached trial (an expected
per-trial cost, or the success mass of one outcome) has total `∑ₘ (1-s)^m c = c / s`.
Paper: proof of `prop:conf-row` (conference.tex), "renewal gives at most `2Ae^A` requests", and
the geometric sum in the proof of `lem:attentionraceexact` (attention_primitives.tex). -/
theorem hasSum_renewal {s : ℝ} (c : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    HasSum (fun m : ℕ => (1 - s) ^ m * c) (c / s) := by
  have h := (hasSum_geometric_of_lt_one (r := 1 - s) (by linarith) (by linarith)).mul_right c
  convert h using 1
  rw [sub_sub_cancel, div_eq_inv_mul]

/-- Expected number of trials: `∑ₘ P(trial m is reached) = 1 / s`. Paper: proof of
`prop:conf-row` (conference.tex), renewal count. -/
theorem hasSum_expected_trials {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    HasSum (fun m : ℕ => (1 - s) ^ m) (1 / s) := by
  simpa using hasSum_renewal 1 hs0 hs1

/-- The law of the first success: if outcome `y` has success mass `α y` in one trial and the
masses sum to `s > 0`, the first accepted outcome equals `y` with probability `α y / s`, and
these probabilities sum to one. Paper: proof of `prop:conf-row` (conference.tex) and of
`lem:attentionraceexact` (attention_primitives.tex). -/
theorem first_success_law {ι : Type*} [Fintype ι] (α : ι → ℝ) (hα : ∀ y, 0 ≤ α y)
    (hs0 : 0 < ∑ y, α y) (hs1 : ∑ y, α y ≤ 1) :
    (∀ y, HasSum (fun m : ℕ => (1 - ∑ y, α y) ^ m * α y) (α y / ∑ y, α y)) ∧
      (∀ y, 0 ≤ α y / ∑ y, α y) ∧ ∑ y, α y / ∑ y, α y = 1 := by
  refine ⟨fun y => hasSum_renewal (α y) hs0 hs1, fun y => div_nonneg (hα y) hs0.le, ?_⟩
  rw [← Finset.sum_div, div_self hs0.ne']

/-! ### The weighted choice and the biased bit -/

/-- The amplitude `A = |c| + ∑ⱼ |wⱼ|` of a row. Paper: proof of `prop:conf-row`
(conference.tex). -/
noncomputable def amplitude {n : ℕ} (c : ℝ) (w : Fin n → ℝ) : ℝ := |c| + ∑ j, |w j|

/-- The preactivation `u = c + ∑ⱼ wⱼ xⱼ`. Paper: `prop:conf-row` (conference.tex). -/
noncomputable def preact {n : ℕ} (c : ℝ) (w x : Fin n → ℝ) : ℝ := c + ∑ j, w j * x j

/-- Probabilities of the weighted choice: `none` selects the bias with probability `|c| / A`,
`some j` selects coordinate `j` with probability `|wⱼ| / A`. -/
noncomputable def choiceProb {n : ℕ} (c : ℝ) (w : Fin n → ℝ) : Option (Fin n) → ℝ
  | none => |c| / amplitude c w
  | some j => |w j| / amplitude c w

/-- The sign returned by the weighted choice: `sgn c` for the bias, `sgn(wⱼ) xⱼ` for
coordinate `j`. -/
noncomputable def choiceSign {n : ℕ} (c : ℝ) (w x : Fin n → ℝ) : Option (Fin n) → ℝ
  | none => (SignType.sign c : ℝ)
  | some j => (SignType.sign (w j) : ℝ) * x j

/-- The amplitude is nonnegative. Auxiliary for the proof of `prop:conf-row`
(conference.tex). -/
theorem amplitude_nonneg {n : ℕ} (c : ℝ) (w : Fin n → ℝ) : 0 ≤ amplitude c w := by
  unfold amplitude
  have := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => abs_nonneg (w j))
  positivity

/-- The weighted choice is a probability vector. Paper: proof of `prop:conf-row`
(conference.tex), "a weighted choice among `sgn(c)` and `sgn(w_j)x_j`". -/
theorem choiceProb_nonneg {n : ℕ} (c : ℝ) (w : Fin n → ℝ) (o : Option (Fin n)) :
    0 ≤ choiceProb c w o := by
  cases o <;> simp only [choiceProb] <;> exact div_nonneg (abs_nonneg _) (amplitude_nonneg c w)

/-- The weighted-choice probabilities sum to one. Paper: proof of `prop:conf-row`
(conference.tex). -/
theorem sum_choiceProb {n : ℕ} (c : ℝ) (w : Fin n → ℝ) (hA : 0 < amplitude c w) :
    ∑ o, choiceProb c w o = 1 := by
  rw [Fintype.sum_option]
  simp only [choiceProb]
  rw [← Finset.sum_div, ← add_div]
  exact div_self hA.ne'

/-- The weighted choice returns a sign of mean `u / A`. Paper: proof of `prop:conf-row`
(conference.tex), "returns a sign of mean `u/A`"; full version: proof of
`thm:new-single-row-law` (tanh_single_row.tex). -/
theorem choice_mean {n : ℕ} (c : ℝ) (w x : Fin n → ℝ) :
    ∑ o, choiceProb c w o * choiceSign c w x o = preact c w x / amplitude c w := by
  rw [Fintype.sum_option]
  simp only [choiceProb, choiceSign, preact]
  have h1 : |c| / amplitude c w * (SignType.sign c : ℝ) = c / amplitude c w := by
    rw [div_mul_eq_mul_div, abs_mul_sign]
  have h2 : ∀ j, |w j| / amplitude c w * ((SignType.sign (w j) : ℝ) * x j)
      = w j * x j / amplitude c w := by
    intro j
    rw [← mul_assoc, div_mul_eq_mul_div, abs_mul_sign, div_mul_eq_mul_div]
  rw [h1, Finset.sum_congr rfl (fun j _ => h2 j), ← Finset.sum_div, ← add_div]

/-- The preactivation is bounded by the amplitude when `|xⱼ| ≤ 1`. Paper: proof of
`prop:conf-row` (conference.tex); it makes `(1 + Y u / A) / 2` a probability. -/
theorem abs_preact_le {n : ℕ} (c : ℝ) (w x : Fin n → ℝ) (hx : ∀ j, |x j| ≤ 1) :
    |preact c w x| ≤ amplitude c w := by
  unfold preact amplitude
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hx j)

/-- Every sign returned with positive probability is `±1` when `xⱼ ∈ {-1, 1}`. Paper: proof of
`prop:conf-row` (conference.tex). -/
theorem choiceSign_eq_one_or {n : ℕ} (c : ℝ) (w x : Fin n → ℝ) (hx : ∀ j, x j = 1 ∨ x j = -1)
    (o : Option (Fin n)) (ho : choiceProb c w o ≠ 0) :
    choiceSign c w x o = 1 ∨ choiceSign c w x o = -1 := by
  cases o with
  | none =>
    simp only [choiceProb, choiceSign] at ho ⊢
    have hc : c ≠ 0 := by
      rintro rfl
      simp at ho
    rcases hc.lt_or_gt with h | h
    · right; simp [sign_neg h]
    · left; simp [sign_pos h]
  | some j =>
    simp only [choiceProb, choiceSign] at ho ⊢
    have hw : w j ≠ 0 := by
      intro h
      simp [h] at ho
    rcases hw.lt_or_gt with h | h
    · rcases hx j with hxj | hxj <;> simp [sign_neg h, hxj]
    · rcases hx j with hxj | hxj <;> simp [sign_pos h, hxj]

/-- The derived bit `[Y · S = 1]`, for a proposal `Y ∈ {-1, 1}` and the weighted-choice sign
`S`, is one with probability `(1 + Y u / A) / 2`. Paper: proof of `prop:conf-row`
(conference.tex), "bits of bias `(1+Yu/A)/2`". -/
theorem bit_bias {n : ℕ} (c : ℝ) (w x : Fin n → ℝ) (hx : ∀ j, x j = 1 ∨ x j = -1)
    (hA : 0 < amplitude c w) (Y : ℝ) (hY : Y = 1 ∨ Y = -1) :
    ∑ o, choiceProb c w o * (if Y * choiceSign c w x o = 1 then 1 else 0)
      = (1 + Y * preact c w x / amplitude c w) / 2 := by
  have key : ∀ o, choiceProb c w o * (if Y * choiceSign c w x o = 1 then 1 else 0)
      = choiceProb c w o * ((1 + Y * choiceSign c w x o) / 2) := by
    intro o
    by_cases ho : choiceProb c w o = 0
    · simp [ho]
    · rcases choiceSign_eq_one_or c w x hx o ho with h | h <;> rcases hY with rfl | rfl <;>
        norm_num [h]
  rw [Finset.sum_congr rfl (fun o _ => key o)]
  have hsum := sum_choiceProb c w hA
  have hmean := choice_mean c w x
  calc ∑ o, choiceProb c w o * ((1 + Y * choiceSign c w x o) / 2)
      = ((∑ o, choiceProb c w o) + Y * ∑ o, choiceProb c w o * choiceSign c w x o) / 2 := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun o _ => ?_
        ring
    _ = (1 + Y * preact c w x / amplitude c w) / 2 := by
        rw [hsum, hmean, mul_div_assoc]

/-- The bit bias `(1 + Y u / A) / 2` lies in `[0, 1]` for `Y = ±1` and `|u| ≤ A`. Paper: proof
of `prop:conf-row` (conference.tex). -/
theorem bit_bias_mem_Icc {A u Y : ℝ} (hA : 0 < A) (hu : |u| ≤ A) (hY : Y = 1 ∨ Y = -1) :
    0 ≤ (1 + Y * u / A) / 2 ∧ (1 + Y * u / A) / 2 ≤ 1 := by
  have h1 : |Y * u / A| ≤ 1 := by
    rw [abs_div, abs_of_pos hA, div_le_one hA, abs_mul]
    rcases hY with rfl | rfl <;> simpa using hu
  have h2 := abs_le.mp h1
  constructor <;> linarith [h2.1, h2.2]

/-! ### The Poisson acceptance race for one row -/

/-- Acceptance of a proposal. With `N ∼ Pois(2A)` and `N` independent bits of bias
`(1 + b / A) / 2`, all bits are one with probability `exp(b - A)`; with `b = Y u` this is the
acceptance `exp(Y u - A)`. Paper: proof of `prop:conf-row` (conference.tex), "the Poisson
generating function gives acceptance `e^{Yu-A}`"; full version: `lem:attentionraceexact`
(attention_primitives.tex). -/
theorem hasSum_acceptance {A : ℝ} (hA : 0 < A) {r : ℝ≥0} (hr : (r : ℝ) = 2 * A) (b : ℝ) :
    HasSum (fun k : ℕ => (poissonMeasure r).real {k} * ((1 + b / A) / 2) ^ k)
      (exp (b - A)) := by
  convert hasSum_poisson_pgf r ((1 + b / A) / 2) using 2
  rw [hr]
  field_simp
  ring

/-- The acceptance probability as a `tsum` over the Poisson law, for the row of
`prop:conf-row` (conference.tex): `∑ₖ P(N = k) ((1 + Y u / A) / 2)ᵏ = exp(Y u - A)` with
`N ∼ Pois(2A)`. -/
theorem row_acceptance {n : ℕ} (c : ℝ) (w x : Fin n → ℝ) (hA : 0 < amplitude c w) (Y : ℝ) :
    ∑' k : ℕ, (poissonMeasure (2 * amplitude c w).toNNReal).real {k}
        * ((1 + Y * preact c w x / amplitude c w) / 2) ^ k
      = exp (Y * preact c w x - amplitude c w) :=
  (hasSum_acceptance hA (Real.coe_toNNReal _ (by positivity)) _).tsum_eq

/-- Algebra behind the mean of the accepted sign: `(e^{u-A} - e^{-u-A}) / (e^{u-A} + e^{-u-A})`
equals `tanh u`. Auxiliary for `row_trial_law`; paper: proof of `prop:conf-row`
(conference.tex), displayed identity `(e^u - e^{-u}) / (e^u + e^{-u}) = tanh u`. -/
theorem accepted_sign_mean (u A : ℝ) :
    ((1 / 2) * exp (u - A) - (1 / 2) * exp (-u - A))
        / ((1 / 2) * exp (u - A) + (1 / 2) * exp (-u - A)) = tanh u := by
  rw [Real.tanh_eq, sub_eq_add_neg u A, sub_eq_add_neg (-u) A, exp_add, exp_add]
  have h1 : 0 < exp (-A) := exp_pos _
  have h2 : 0 < exp u + exp (-u) := by positivity
  rw [show (1 / 2) * (exp u * exp (-A)) - (1 / 2) * (exp (-u) * exp (-A))
      = ((1 / 2) * exp (-A)) * (exp u - exp (-u)) by ring,
    show (1 / 2) * (exp u * exp (-A)) + (1 / 2) * (exp (-u) * exp (-A))
      = ((1 / 2) * exp (-A)) * (exp u + exp (-u)) by ring,
    mul_div_mul_left _ _ (by positivity)]

/-- `±1` as a real number: `true ↦ 1`, `false ↦ -1`. -/
def signVal (b : Bool) : ℝ := if b then 1 else -1

/-- The one-trial mass of the row sampler for proposal `y = ±1` followed by acceptance: the
proposal has probability `1/2`, and the `N ∼ Pois(2A)` independent bits of bias
`(1 + y u / A) / 2` are all one with probability `∑ₖ P(N = k) ((1 + y u / A) / 2)^k`. Paper:
proof of `prop:conf-row` (conference.tex), "propose `Y = ±1` uniformly and draw
`N ∼ Pois(2A)`. Accept if all `N` independent bits of bias `(1+Yu/A)/2` are one". -/
noncomputable def rowTrialMass {n : ℕ} (c : ℝ) (w x : Fin n → ℝ) (y : ℝ) : ℝ :=
  (1 / 2) * ∑' k : ℕ, (poissonMeasure (2 * amplitude c w).toNNReal).real {k}
    * ((1 + y * preact c w x / amplitude c w) / 2) ^ k

/-- The one-trial mass via the Poisson generating function: `m(y) = e^{y u - A} / 2`. Paper:
proof of `prop:conf-row` (conference.tex), "the Poisson generating function gives acceptance
`e^{Yu-A}`". -/
theorem rowTrialMass_eq {n : ℕ} (c : ℝ) (w x : Fin n → ℝ) (hA : 0 < amplitude c w) (y : ℝ) :
    rowTrialMass c w x y = (1 / 2) * exp (y * preact c w x - amplitude c w) := by
  rw [rowTrialMass, row_acceptance c w x hA y]

/-- The trial success probability is `e^{-A} cosh u`. Paper: proof of `prop:conf-row`
(conference.tex), "a trial succeeds with probability `e^{-A} cosh u`". -/
theorem trial_success_eq (u A : ℝ) :
    (1 / 2) * exp (u - A) + (1 / 2) * exp (-u - A) = exp (-A) * cosh u := by
  rw [Real.cosh_eq, sub_eq_add_neg u A, sub_eq_add_neg (-u) A, exp_add, exp_add]
  ring

/-- The trial success probability satisfies `e^{-A} ≤ e^{-A} cosh u ≤ 1` when `|u| ≤ A`. Paper:
proof of `prop:conf-row` (conference.tex), "`e^{-A} cosh u ≥ e^{-A}`". -/
theorem trial_success_bounds {u A : ℝ} (hu : |u| ≤ A) :
    exp (-A) ≤ exp (-A) * cosh u ∧ exp (-A) * cosh u ≤ 1 := by
  constructor
  · exact le_mul_of_one_le_right (exp_pos _).le (Real.one_le_cosh u)
  · have hc : cosh u ≤ cosh A := Real.cosh_le_cosh.mpr (by
      rw [abs_of_nonneg ((abs_nonneg u).trans hu)]; exact hu)
    have hA : cosh A ≤ exp A := by
      rw [Real.cosh_eq]
      have : exp (-A) ≤ exp A := exp_le_exp.mpr (by linarith [(abs_nonneg u).trans hu])
      linarith
    calc exp (-A) * cosh u ≤ exp (-A) * exp A :=
          mul_le_mul_of_nonneg_left (hc.trans hA) (exp_pos _).le
      _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]

/-- Expected input requests of one trial. Each of the `N ∼ Pois(2A)` bits uses one weighted
choice, which requests an input coordinate with probability `ρ = ∑ⱼ |wⱼ| / A`; the expected
request count of a trial is `∑ₖ P(N = k) k ρ = 2 ∑ⱼ |wⱼ| ≤ 2A`. Paper: proof of
`prop:conf-row` (conference.tex), "its expected source count is at most `2A`". -/
theorem trial_requests {n : ℕ} (c : ℝ) (w : Fin n → ℝ) (hA : 0 < amplitude c w) :
    HasSum (fun k : ℕ => (poissonMeasure (2 * amplitude c w).toNNReal).real {k}
        * (k * ((∑ j, |w j|) / amplitude c w))) (2 * ∑ j, |w j|) ∧
      2 * ∑ j, |w j| ≤ 2 * amplitude c w := by
  constructor
  · have h := (hasSum_poisson_mean (2 * amplitude c w).toNNReal).mul_right
      ((∑ j, |w j|) / amplitude c w)
    rw [Real.coe_toNNReal _ (by positivity)] at h
    convert h using 1
    · funext k; ring
    · field_simp
  · unfold amplitude
    linarith [abs_nonneg c]

/-- Arithmetic of the request bound: `2A e^A ≤ 4 e^2` for `0 ≤ A ≤ 2`. Paper: proof of
`prop:conf-row` (conference.tex), "`2Ae^A ≤ 4e^2` requests". -/
theorem two_mul_exp_le {A : ℝ} (hA2 : A ≤ 2) : 2 * A * exp A ≤ 4 * exp 2 := by
  have h1 : exp A ≤ exp 2 := exp_le_exp.mpr hA2
  have h2 : 0 ≤ exp A := (exp_pos _).le
  nlinarith

/-- Renewal bound on the expected number of input requests of the row sampler: the per-trial
expectation `2 ∑ⱼ |wⱼ|` is charged once per reached trial, trial `m` is reached with
probability `(1 - s)^m` where `s = e^{-A} cosh u`, and the total `2 ∑ⱼ |wⱼ| / s` is at most
`2A e^A ≤ 4e^2`. Paper: proof of `prop:conf-row` (conference.tex), "renewal gives at most
`2Ae^A ≤ 4e^2` requests". -/
theorem row_expected_requests {n : ℕ} (c : ℝ) (w x : Fin n → ℝ) (hc : |c| ≤ 1)
    (hw : ∑ j, |w j| ≤ 1) (hx : ∀ j, |x j| ≤ 1) (hA : 0 < amplitude c w) :
    HasSum (fun m : ℕ => (1 - exp (-amplitude c w) * cosh (preact c w x)) ^ m
        * (2 * ∑ j, |w j|)) ((2 * ∑ j, |w j|) / (exp (-amplitude c w) * cosh (preact c w x))) ∧
      (2 * ∑ j, |w j|) / (exp (-amplitude c w) * cosh (preact c w x))
        ≤ 2 * amplitude c w * exp (amplitude c w) ∧
      2 * amplitude c w * exp (amplitude c w) ≤ 4 * exp 2 := by
  set A := amplitude c w with hAdef
  set u := preact c w x
  have hu : |u| ≤ A := abs_preact_le c w x hx
  obtain ⟨hs0, hs1⟩ := trial_success_bounds hu
  have hspos : 0 < exp (-A) * cosh u := lt_of_lt_of_le (exp_pos _) hs0
  have hcost := (trial_requests c w hA).2
  refine ⟨hasSum_renewal _ hspos hs1, ?_, ?_⟩
  · rw [div_le_iff₀ hspos]
    calc 2 * ∑ j, |w j| ≤ 2 * A := hcost
      _ = 2 * A * exp A * exp (-A) := by
          rw [mul_assoc (2 * A), ← exp_add, add_neg_cancel, exp_zero, mul_one]
      _ ≤ 2 * A * exp A * (exp (-A) * cosh u) :=
          mul_le_mul_of_nonneg_left hs0 (by positivity)
  · apply two_mul_exp_le
    rw [hAdef]
    unfold amplitude
    linarith

/-- The degenerate row `A = 0`: then `u = 0` and the target mean `tanh u` is zero, so a fair sign
is exact. Paper: proof of `prop:conf-row` (conference.tex), "if `A = 0`, return a fair sign". -/
theorem row_zero_amplitude {n : ℕ} (c : ℝ) (w x : Fin n → ℝ) (hx : ∀ j, |x j| ≤ 1)
    (hA : amplitude c w = 0) : tanh (preact c w x) = 0 := by
  have hu := abs_preact_le c w x hx
  rw [hA] at hu
  have : preact c w x = 0 := abs_nonpos_iff.mp hu
  rw [this, Real.tanh_zero]

/-- The one-trial law of the row sampler and the law of the accepted sign, derived from the
Poisson acceptance. With `m(y)` the one-trial mass of proposal `y` and acceptance
(`rowTrialMass`): `m(±1) = e^{±u - A}/2`; a trial succeeds with probability
`m(1) + m(-1) = e^{-A} cosh u`; the accepted sign equals `y` with probability
`m(y) / (m(1) + m(-1)) = e^{yu} / (e^u + e^{-u})`; and its mean is `tanh u`. Paper: proof of
`prop:conf-row` (conference.tex), "hence the accepted sign has mean `tanh u`. A trial succeeds
with probability `e^{-A} cosh u`". -/
theorem row_trial_law {n : ℕ} (c : ℝ) (w x : Fin n → ℝ) (hA : 0 < amplitude c w) :
    rowTrialMass c w x 1 = (1 / 2) * exp (preact c w x - amplitude c w) ∧
    rowTrialMass c w x (-1) = (1 / 2) * exp (-preact c w x - amplitude c w) ∧
    rowTrialMass c w x 1 + rowTrialMass c w x (-1)
      = exp (-amplitude c w) * cosh (preact c w x) ∧
    (∀ b : Bool, rowTrialMass c w x (signVal b)
        / (rowTrialMass c w x 1 + rowTrialMass c w x (-1))
      = exp (signVal b * preact c w x) / (exp (preact c w x) + exp (-preact c w x))) ∧
    (rowTrialMass c w x 1 - rowTrialMass c w x (-1))
        / (rowTrialMass c w x 1 + rowTrialMass c w x (-1)) = tanh (preact c w x) := by
  set u := preact c w x
  set A := amplitude c w
  have h1 : rowTrialMass c w x 1 = (1 / 2) * exp (u - A) := by
    rw [rowTrialMass_eq c w x hA, one_mul]
  have h2 : rowTrialMass c w x (-1) = (1 / 2) * exp (-u - A) := by
    rw [rowTrialMass_eq c w x hA, neg_one_mul]
  have hD : 0 < exp u + exp (-u) := by positivity
  have hEA : 0 < exp (-A) := exp_pos _
  refine ⟨h1, h2, by rw [h1, h2]; exact trial_success_eq u A, fun b => ?_, ?_⟩
  · have hden : rowTrialMass c w x 1 + rowTrialMass c w x (-1)
        = (1 / 2) * exp (-A) * (exp u + exp (-u)) := by
      rw [h1, h2, sub_eq_add_neg u A, sub_eq_add_neg (-u) A, exp_add, exp_add]; ring
    rw [hden, rowTrialMass_eq c w x hA, sub_eq_add_neg _ A, exp_add,
      div_eq_div_iff (by positivity) hD.ne']
    ring
  · rw [h1, h2]; exact accepted_sign_mean u A

/-- Summary of `prop:conf-row` (conference.tex) for a row with `|c| ≤ 1`, `∑ⱼ |wⱼ| ≤ 1`,
`xⱼ ∈ {-1, 1}` and `A > 0`: the weighted choice has mean `u / A`; the bit bias
`(1 + Y u / A) / 2` lies in `[0, 1]` and is the probability of a one; a proposal `Y` is accepted
with probability `exp(Y u - A)` (Poisson series with `N ∼ Pois(2A)`); with the one-trial masses
`m(y)` built from these Poisson series, a trial succeeds with probability
`m(1) + m(-1) = s = e^{-A} cosh u ≥ e^{-A}`, the accepted sign is `y` with probability
`e^{yu} / (e^u + e^{-u})` and has mean `tanh u`; and the renewal bound on input requests is
`2 ∑ⱼ |wⱼ| / s ≤ 2A e^A ≤ 4e^2`. The same law and request count for independent trials on a
probability space are `row_sampler_iid`. The single-row theorem of the full version
(tanh_single_row.tex) uses a different tanh factory and is not formalized here. -/
theorem prop_conf_row {n : ℕ} (c : ℝ) (w x : Fin n → ℝ) (hc : |c| ≤ 1) (hw : ∑ j, |w j| ≤ 1)
    (hx : ∀ j, x j = 1 ∨ x j = -1) (hA : 0 < amplitude c w) :
    ∑ o, choiceProb c w o * choiceSign c w x o = preact c w x / amplitude c w ∧
    (∀ Y : ℝ, (Y = 1 ∨ Y = -1) →
      ∑ o, choiceProb c w o * (if Y * choiceSign c w x o = 1 then 1 else 0)
        = (1 + Y * preact c w x / amplitude c w) / 2 ∧
      0 ≤ (1 + Y * preact c w x / amplitude c w) / 2 ∧
      (1 + Y * preact c w x / amplitude c w) / 2 ≤ 1 ∧
      ∑' k : ℕ, (poissonMeasure (2 * amplitude c w).toNNReal).real {k}
          * ((1 + Y * preact c w x / amplitude c w) / 2) ^ k
        = exp (Y * preact c w x - amplitude c w)) ∧
    rowTrialMass c w x 1 + rowTrialMass c w x (-1)
        = exp (-amplitude c w) * cosh (preact c w x) ∧
    exp (-amplitude c w) ≤ exp (-amplitude c w) * cosh (preact c w x) ∧
    (∀ b : Bool, rowTrialMass c w x (signVal b)
        / (rowTrialMass c w x 1 + rowTrialMass c w x (-1))
      = exp (signVal b * preact c w x) / (exp (preact c w x) + exp (-preact c w x))) ∧
    (rowTrialMass c w x 1 - rowTrialMass c w x (-1))
        / (rowTrialMass c w x 1 + rowTrialMass c w x (-1)) = tanh (preact c w x) ∧
    (2 * ∑ j, |w j|) / (exp (-amplitude c w) * cosh (preact c w x))
        ≤ 2 * amplitude c w * exp (amplitude c w) ∧
    2 * amplitude c w * exp (amplitude c w) ≤ 4 * exp 2 := by
  have hx' : ∀ j, |x j| ≤ 1 := fun j => by rcases hx j with h | h <;> simp [h]
  have hu := abs_preact_le c w x hx'
  obtain ⟨-, hreq1, hreq2⟩ := row_expected_requests c w x hc hw hx' hA
  obtain ⟨-, -, hsum, hlaw, hmean⟩ := row_trial_law c w x hA
  refine ⟨choice_mean c w x, fun Y hY => ?_, hsum, (trial_success_bounds hu).1, hlaw, hmean,
    hreq1, hreq2⟩
  have hb := bit_bias_mem_Icc hA hu hY
  exact ⟨bit_bias c w x hx hA Y hY, hb.1, hb.2, row_acceptance c w x hA Y⟩

/-- The output law of the row sampler as a renewal series: summing over the first accepted trial,
`∑ₘ (1 - s)^m m(y) = e^{yu} / (e^u + e^{-u})`, where `m(y)` is the one-trial mass built from the
Poisson acceptance and `s = m(1) + m(-1)`. Paper: proof of `prop:conf-row` (conference.tex),
"hence the accepted sign has mean `tanh u`". -/
theorem row_output_law {n : ℕ} (c : ℝ) (w x : Fin n → ℝ) (hx : ∀ j, |x j| ≤ 1)
    (hA : 0 < amplitude c w) (b : Bool) :
    HasSum (fun m : ℕ => (1 - (rowTrialMass c w x 1 + rowTrialMass c w x (-1))) ^ m
        * rowTrialMass c w x (signVal b))
      (exp (signVal b * preact c w x) / (exp (preact c w x) + exp (-preact c w x))) := by
  obtain ⟨-, -, hsum, hlaw, -⟩ := row_trial_law c w x hA
  obtain ⟨hs0, hs1⟩ := trial_success_bounds (abs_preact_le c w x hx)
  rw [← hlaw b]
  rw [← hsum] at hs0 hs1
  exact hasSum_renewal _ (lt_of_lt_of_le (exp_pos _) hs0) hs1

/-! ### A finite-bit Poisson sampler -/

/-- The geometric proposal `P(K) = 2^{-(K+1)}` drawn with fair bits. Paper: proof of
`prop:conf-row` (conference.tex). -/
noncomputable def geomProposal (K : ℕ) : ℝ := (1 / 2) ^ (K + 1)

/-- The acceptance probability `e^{-λ} (2λ)^K / (128 K!)` of the proposal `K`. Paper: proof
of `prop:conf-row` (conference.tex). -/
noncomputable def poissonAccept (lam : ℝ) (K : ℕ) : ℝ := exp (-lam) * (2 * lam) ^ K / (128 * K !)

/-- The geometric proposal is a probability law on `ℕ`. Paper: proof of `prop:conf-row`
(conference.tex), "propose `K ≥ 0` with probability `2^{-(K+1)}`". -/
theorem hasSum_geomProposal : HasSum geomProposal 1 := by
  have h := (hasSum_geometric_two).mul_left (1 / 2 : ℝ)
  convert h using 1
  · funext K
    simp only [geomProposal, pow_succ]
    ring
  · norm_num

/-- Numerical bound `e^4 / 128 < 1`. Paper: proof of `prop:conf-row` (conference.tex). -/
theorem exp_four_div_lt_one : exp 4 / 128 < 1 := by
  have h := Real.exp_one_lt_d9
  have h4 : exp 4 = exp 1 ^ 4 := by rw [Real.exp_one_pow]; norm_num
  rw [div_lt_one (by norm_num), h4]
  have h0 : 0 ≤ exp 1 := (exp_pos 1).le
  calc exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 := by gcongr
    _ < 128 := by norm_num

/-- The acceptance probability is at most `e^λ / 128 ≤ e^4 / 128 < 1` for `0 ≤ λ ≤ 4`, so it is
a probability. Paper: proof of `prop:conf-row` (conference.tex), "this is at most
`e^4/128 < 1`"; full version: `lem:smallpoissonattention` (attention_primitives.tex), the same
construction with different constants. -/
theorem poissonAccept_bounds {lam : ℝ} (h0 : 0 ≤ lam) (h4 : lam ≤ 4) (K : ℕ) :
    0 ≤ poissonAccept lam K ∧ poissonAccept lam K ≤ exp 4 / 128 ∧ exp 4 / 128 < 1 := by
  refine ⟨by unfold poissonAccept; positivity, ?_, exp_four_div_lt_one⟩
  have hf := Real.pow_div_factorial_le_exp (x := 2 * lam) (by linarith) K
  unfold poissonAccept
  have hK : (0 : ℝ) < K ! := by positivity
  calc exp (-lam) * (2 * lam) ^ K / (128 * K !)
      = exp (-lam) * ((2 * lam) ^ K / K !) / 128 := by field_simp
    _ ≤ exp (-lam) * exp (2 * lam) / 128 := by gcongr
    _ = exp lam / 128 := by rw [← exp_add]; ring_nf
    _ ≤ exp 4 / 128 := by gcongr

/-- The accepted mass of the proposal `K`: `2^{-(K+1)} e^{-λ}(2λ)^K / (128 K!) =
e^{-λ} λ^K / (256 K!)`. Paper: proof of `prop:conf-row` (conference.tex), "its accepted mass
is `e^{-λ}λ^K/(256K!)`". -/
theorem accepted_mass (lam : ℝ) (K : ℕ) :
    geomProposal K * poissonAccept lam K = exp (-lam) * lam ^ K / (256 * K !) := by
  unfold geomProposal poissonAccept
  have hK : (K ! : ℝ) ≠ 0 := by positivity
  have h2 : ((1 : ℝ) / 2) ^ K * 2 ^ K = 1 := by rw [← mul_pow]; norm_num
  rw [mul_pow, pow_succ]
  field_simp
  linear_combination (lam ^ K * 256) * h2

/-- Each trial of the finite-bit Poisson sampler succeeds with probability `1/256`, and its
accepted mass is `1/256` times the Poisson probability. Paper: proof of `prop:conf-row`
(conference.tex), "each trial succeeds with probability `1/256` and the accepted `K` is
Poisson"; full version: `lem:smallpoissonattention` (attention_primitives.tex), the same
construction with different constants. -/
theorem poisson_trial (r : ℝ≥0) :
    HasSum (fun K : ℕ => geomProposal K * poissonAccept r K) (1 / 256) ∧
      ∀ K : ℕ, geomProposal K * poissonAccept r K / (1 / 256) = (poissonMeasure r).real {K} := by
  have hmass : ∀ K : ℕ, geomProposal K * poissonAccept r K
      = (1 / 256) * (poissonMeasure r).real {K} := by
    intro K
    rw [accepted_mass, poissonMeasure_real_singleton]
    ring
  constructor
  · have h := (hasSum_one_poissonMeasure r).mul_left (1 / 256 : ℝ)
    rw [mul_one] at h
    convert h using 1
    funext K
    rw [hmass, poissonMeasure_real_singleton]
  · intro K
    rw [hmass]
    field_simp

/-- The accepted count of the repeated finite-bit sampler is exactly Poisson: summing over the
first successful trial, `∑ₘ (1 - 1/256)^m · mass(K) = P(Pois(λ) = K)`. Paper: proof of
`prop:conf-row` (conference.tex), "the accepted `K` is Poisson"; full version:
`lem:smallpoissonattention` (attention_primitives.tex), the same construction with different
constants. -/
theorem poisson_sampler_law (r : ℝ≥0) (K : ℕ) :
    HasSum (fun m : ℕ => (1 - 1 / 256 : ℝ) ^ m * (geomProposal K * poissonAccept r K))
      ((poissonMeasure r).real {K}) := by
  rw [← (poisson_trial r).2 K]
  exact hasSum_renewal _ (by norm_num) (by norm_num)

/-- The rational factor `(2λ)^K / (128 K!)` of the acceptance probability is below
`e^8 / 128 < 52` for `0 ≤ λ ≤ 4`. Paper: proof of `prop:conf-row` (conference.tex), "the
rational factor is below `e^8/128 < 52`". (In fact `e^8 / 128 < 24`.) -/
theorem rational_factor_bound {lam : ℝ} (h0 : 0 ≤ lam) (h4 : lam ≤ 4) (K : ℕ) :
    (2 * lam) ^ K / (128 * K !) ≤ exp 8 / 128 ∧ exp 8 / 128 < 52 ∧ exp 8 / 128 < 24 := by
  have he := Real.exp_one_lt_d9
  have h8 : exp 8 = exp 1 ^ 8 := by rw [Real.exp_one_pow]; norm_num
  have h0' : 0 ≤ exp 1 := (exp_pos 1).le
  have hlt : exp 8 < 24 * 128 := by
    rw [h8]
    calc exp 1 ^ 8 ≤ (2.7182818286 : ℝ) ^ 8 := by gcongr
      _ < 24 * 128 := by norm_num
  refine ⟨?_, by linarith, by linarith⟩
  have hf := Real.pow_div_factorial_le_exp (x := 2 * lam) (by linarith) K
  have hK : (0 : ℝ) < K ! := by positivity
  calc (2 * lam) ^ K / (128 * K !) = ((2 * lam) ^ K / K !) / 128 := by field_simp
    _ ≤ exp (2 * lam) / 128 := by gcongr
    _ ≤ exp 8 / 128 := by gcongr; linarith

/-- Summary of the finite-bit Poisson sampler in the proof of `prop:conf-row` (conference.tex), for
`0 ≤ λ ≤ 4`: the geometric proposal `2^{-(K+1)}` is a probability law; the acceptance
probability `e^{-λ}(2λ)^K/(128K!)` lies in `[0, e^4/128]` with `e^4/128 < 1`; the accepted mass
is `e^{-λ}λ^K/(256K!)`; a trial succeeds with probability `1/256`; the accepted count is
Poisson; the expected number of trials is `256`; and the rational factor is below
`e^8/128 < 52`. The small-Poisson lemma of the full version (attention_primitives.tex) uses the
same construction with `θ ≤ 1`, factor `4` and success probability `1/8`; it is not formalized
here, and neither is the bit work. -/
theorem finite_bit_poisson (r : ℝ≥0) (hr : (r : ℝ) ≤ 4) :
    HasSum geomProposal 1 ∧
    (∀ K, 0 ≤ poissonAccept r K ∧ poissonAccept r K ≤ exp 4 / 128) ∧ exp 4 / 128 < 1 ∧
    (∀ K, geomProposal K * poissonAccept r K = exp (-(r : ℝ)) * (r : ℝ) ^ K / (256 * K !)) ∧
    HasSum (fun K : ℕ => geomProposal K * poissonAccept r K) (1 / 256) ∧
    (∀ K, HasSum (fun m : ℕ => (1 - 1 / 256 : ℝ) ^ m * (geomProposal K * poissonAccept r K))
      ((poissonMeasure r).real {K})) ∧
    HasSum (fun m : ℕ => (1 - 1 / 256 : ℝ) ^ m) 256 ∧
    (∀ K, (2 * (r : ℝ)) ^ K / (128 * K !) ≤ exp 8 / 128) ∧ exp 8 / 128 < 52 := by
  have h0 : (0 : ℝ) ≤ r := r.2
  refine ⟨hasSum_geomProposal, fun K => ⟨(poissonAccept_bounds h0 hr K).1,
    (poissonAccept_bounds h0 hr K).2.1⟩, exp_four_div_lt_one, fun K => accepted_mass _ K,
    (poisson_trial r).1, poisson_sampler_law r, ?_, fun K => (rational_factor_bound h0 hr K).1,
    (rational_factor_bound h0 hr 0).2.1⟩
  have := hasSum_expected_trials (s := 1 / 256) (by norm_num) (by norm_num)
  norm_num at this ⊢
  exact this

/-! ### The attention race -/

/-- Acceptance of an attention proposal: if `|a_j| ≤ A` and the score coin has bias
`(1 + a_j / A) / 2`, a Poisson test with `N ∼ Pois(2A)` accepts `j` with probability
`exp(a_j - A)`. Paper: the paragraph after `prop:conf-row` (conference.tex), "the Poisson test
accepts a uniform proposal `j` with probability `e^{a_j - A_coin}`"; full version:
`lem:attentionraceexact` (attention_primitives.tex). -/
theorem attention_acceptance {A : ℝ} (hA : 0 < A) {r : ℝ≥0} (hr : (r : ℝ) = 2 * A) (a : ℝ) :
    ∑' k : ℕ, (poissonMeasure r).real {k} * ((1 + a / A) / 2) ^ k = exp (a - A) :=
  (hasSum_acceptance hA hr a).tsum_eq

/-- Normalized acceptance mass is softmax: with a uniform proposal over `T` positions and
acceptance `exp(a_j - A)`, the accepted mass of `j` normalized by the total success
probability is `e^{a_j} / ∑ₖ e^{a_k}`. Paper: the paragraph after `prop:conf-row`
(conference.tex), "giving the exact attention law" (`eq:conf-attention`); full version:
`lem:attentionraceexact` (attention_primitives.tex). -/
theorem attention_normalized_mass {T : ℕ} (hT : 0 < T) (a : Fin T → ℝ) (A : ℝ) (j : Fin T) :
    (exp (a j - A) / T) / (∑ k, exp (a k - A) / T) = exp (a j) / ∑ k, exp (a k) := by
  have hT' : (T : ℝ) ≠ 0 := by positivity
  have hsum : ∑ k, exp (a k - A) / T = exp (-A) / T * ∑ k, exp (a k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sub_eq_add_neg, exp_add]
    ring
  rw [hsum, sub_eq_add_neg, exp_add]
  have hpos : 0 < ∑ k, exp (a k) := by
    have : Nonempty (Fin T) := ⟨⟨0, hT⟩⟩
    exact Finset.sum_pos (fun k _ => exp_pos _) Finset.univ_nonempty
  field_simp

/-- Renewal series of the attention race. With uniform proposals over `T` positions, scores
`|a_j| ≤ A` and acceptance `exp(a_j - A)`, the success probability of one proposal is
`r̄ = T⁻¹ ∑ₖ e^{a_k - A} ∈ [e^{-2A}, 1]`, the first-acceptance series satisfies
`∑ₘ (1 - r̄)^m e^{a_j - A} / T = e^{a_j} / ∑ₖ e^{a_k}`, and `∑ₘ (1 - r̄)^m = 1 / r̄ ≤ e^{2A}`.
For independent proposals on a probability space these are the law of the accepted index and
the expected number of proposals (`attention_race_iid`). Paper: the paragraph after
`prop:conf-row` (conference.tex); full version: `lem:attentionraceexact` and
`thm:attentionprimitive` (attention_primitives.tex). -/
theorem attention_first_accept {T : ℕ} (hT : 0 < T) (a : Fin T → ℝ) {A : ℝ}
    (ha : ∀ j, |a j| ≤ A) :
    exp (-2 * A) ≤ ∑ k, exp (a k - A) / T ∧ ∑ k, exp (a k - A) / T ≤ 1 ∧
    (∀ j, HasSum (fun m : ℕ => (1 - ∑ k, exp (a k - A) / T) ^ m * (exp (a j - A) / T))
      (exp (a j) / ∑ k, exp (a k))) ∧
    HasSum (fun m : ℕ => (1 - ∑ k, exp (a k - A) / T) ^ m) (1 / ∑ k, exp (a k - A) / T) ∧
    1 / ∑ k, exp (a k - A) / T ≤ exp (2 * A) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hlow : ∀ k, exp (-2 * A) ≤ exp (a k - A) := fun k =>
    exp_le_exp.mpr (by linarith [(abs_le.mp (ha k)).1])
  have hup : ∀ k, exp (a k - A) ≤ 1 := fun k =>
    exp_le_one_iff.mpr (by linarith [(abs_le.mp (ha k)).2])
  have hcard : ∑ _k : Fin T, (1 : ℝ) / T = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have h1 : exp (-2 * A) ≤ ∑ k, exp (a k - A) / T := by
    calc exp (-2 * A) = ∑ _k : Fin T, exp (-2 * A) / T := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
      _ ≤ ∑ k, exp (a k - A) / T :=
          Finset.sum_le_sum fun k _ => div_le_div_of_nonneg_right (hlow k) hT'.le
  have h2 : ∑ k, exp (a k - A) / T ≤ 1 := by
    calc ∑ k, exp (a k - A) / T ≤ ∑ _k : Fin T, (1 : ℝ) / T :=
          Finset.sum_le_sum fun k _ => div_le_div_of_nonneg_right (hup k) hT'.le
      _ = 1 := hcard
  have hpos : 0 < ∑ k, exp (a k - A) / T := lt_of_lt_of_le (exp_pos _) h1
  refine ⟨h1, h2, fun j => ?_, hasSum_expected_trials hpos h2, ?_⟩
  · rw [← attention_normalized_mass hT a A j]
    exact hasSum_renewal _ hpos h2
  · rw [div_le_iff₀ hpos]
    calc (1 : ℝ) = exp (2 * A) * exp (-2 * A) := by rw [← exp_add]; ring_nf; exact exp_zero.symm
      _ ≤ exp (2 * A) * ∑ k, exp (a k - A) / T :=
          mul_le_mul_of_nonneg_left h1 (exp_pos _).le

/-! ### Stopped Poisson tests and the expected predecessor count -/

/-- Stopped Poisson tests: for a coin of bias `p ≠ 1` and `N ∼ Pois(λ)`, the number `G` of coins
inspected before the first failure or the completion of all `N` tests has mean
`(1 - e^{-λ(1-p)}) / (1 - p)`; conditional on `N = k` it is `∑_{i<k} pⁱ`. Paper: full version
`lem:stoppedpoissonattention` (attention_primitives.tex), used in the paragraph after
`prop:conf-row` (conference.tex) for the expected predecessor count. -/
theorem hasSum_stopped_count (r : ℝ≥0) {p : ℝ} (hp : p ≠ 1) :
    HasSum (fun k : ℕ => (poissonMeasure r).real {k} * ∑ i ∈ range k, p ^ i)
      ((1 - exp (-(r : ℝ) * (1 - p))) / (1 - p)) := by
  have hp' : p - 1 ≠ 0 := sub_ne_zero.mpr hp
  have h := ((hasSum_poisson_pgf r p).sub (hasSum_one_poissonMeasure r)).div_const (p - 1)
  convert h using 1
  · funext k
    rw [geom_sum_eq hp, poissonMeasure_real_singleton]
    field_simp
  · have : (1 : ℝ) - p ≠ 0 := by intro h; apply hp; linarith
    field_simp
    ring

/-- Stopped Poisson tests at bias one: every coin succeeds, so `E G = E N = λ`. Paper: full
version `lem:stoppedpoissonattention` (attention_primitives.tex). -/
theorem hasSum_stopped_count_one (r : ℝ≥0) :
    HasSum (fun k : ℕ => (poissonMeasure r).real {k} * ∑ i ∈ range k, (1 : ℝ) ^ i) (r : ℝ) := by
  simpa using hasSum_poisson_mean r

/-- The ratio bound `E G ≤ (e^λ - 1) e^{-λ(1-p)}` of the stopped Poisson test count, for
`p ∈ [0, 1]` and `λ ≥ 0`. Paper: full version `lem:stoppedpoissonattention`,
`eq:stoppedpoissonratio` (attention_primitives.tex), by convexity of the exponential. -/
theorem stopped_count_le (r : ℝ≥0) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑' k : ℕ, (poissonMeasure r).real {k} * ∑ i ∈ range k, p ^ i
      ≤ (exp (r : ℝ) - 1) * exp (-(r : ℝ) * (1 - p)) := by
  set lam : ℝ := (r : ℝ)
  have hlam : 0 ≤ lam := r.2
  rcases eq_or_lt_of_le hp1 with h1 | h1
  · subst h1
    rw [(hasSum_stopped_count_one r).tsum_eq]
    simp only [sub_self, mul_zero, exp_zero, mul_one]
    linarith [Real.add_one_le_exp lam]
  · rw [(hasSum_stopped_count r h1.ne).tsum_eq]
    set q := 1 - p with hq
    have hq0 : 0 < q := by linarith
    have hq1 : q ≤ 1 := by linarith
    -- convexity: e^{λq} ≤ (1 - q) + q e^λ
    have hconv : exp (q * lam) ≤ (1 - q) + q * exp lam := by
      have := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ lam) (by linarith : 0 ≤ 1 - q)
        hq0.le (by ring)
      simpa [smul_eq_mul] using this
    rw [div_le_iff₀ hq0]
    have he : exp (-lam * q) * exp (q * lam) = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
    have hpos : 0 < exp (-lam * q) := exp_pos _
    nlinarith [hconv, he, hpos]

/-- Renewal bound for the predecessor count of the attention race. With scores `|a_j| ≤ A`,
`A > 0`, score coins of bias `p_j = (1 + a_j / A) / 2`, Poisson time `2A`, stopped tests with
mean `g_j`, and acceptance `r_j = e^{a_j - A}`, the renewal quantity `(T⁻¹ ∑ⱼ gⱼ) / r̄` is at most
`e^{2A} - 1`, and `2 (T⁻¹ ∑ⱼ gⱼ) / r̄ + 1 ≤ 2e^{2A} - 1`. For independent proposals these are
the expected number of score tests and the expected predecessor count with two signs per test
and one fresh value sign (`attention_race_iid`). Paper: the paragraph after
`prop:conf-row` (conference.tex), "at most `2e^{2A_coin} - 1`"; full version:
`thm:attentionprimitive`, `eq:attentionoffspring`, and `lem:stoppedpoissonattention`
(attention_primitives.tex). -/
theorem attention_predecessor_count {T : ℕ} (hT : 0 < T) (a : Fin T → ℝ) {A : ℝ}
    (hA : 0 < A) (ha : ∀ j, |a j| ≤ A) :
    (∑ j, (∑' k : ℕ, (poissonMeasure (2 * A).toNNReal).real {k}
          * ∑ i ∈ range k, ((1 + a j / A) / 2) ^ i) / T) / (∑ k, exp (a k - A) / T)
        ≤ exp (2 * A) - 1 ∧
    2 * ((∑ j, (∑' k : ℕ, (poissonMeasure (2 * A).toNNReal).real {k}
          * ∑ i ∈ range k, ((1 + a j / A) / 2) ^ i) / T) / (∑ k, exp (a k - A) / T)) + 1
        ≤ 2 * exp (2 * A) - 1 := by
  have hr : ((2 * A).toNNReal : ℝ) = 2 * A := Real.coe_toNNReal _ (by linarith)
  have hpos : 0 < ∑ k, exp (a k - A) / T :=
    lt_of_lt_of_le (exp_pos _) (attention_first_accept hT a ha).1
  have hg : ∀ j, ∑' k : ℕ, (poissonMeasure (2 * A).toNNReal).real {k}
      * ∑ i ∈ range k, ((1 + a j / A) / 2) ^ i ≤ (exp (2 * A) - 1) * exp (a j - A) := by
    intro j
    have hb := bit_bias_mem_Icc (u := a j) (Y := 1) hA (ha j) (Or.inl rfl)
    simp only [one_mul] at hb
    have := stopped_count_le (2 * A).toNNReal hb.1 hb.2
    rw [hr] at this
    convert this using 2
    congr 1
    field_simp
    ring
  have hmain : (∑ j, (∑' k : ℕ, (poissonMeasure (2 * A).toNNReal).real {k}
          * ∑ i ∈ range k, ((1 + a j / A) / 2) ^ i) / T) / (∑ k, exp (a k - A) / T)
        ≤ exp (2 * A) - 1 := by
    rw [div_le_iff₀ hpos, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hT' : (0 : ℝ) < T := by exact_mod_cast hT
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hg j) hT'.le
  exact ⟨hmain, by linarith⟩

/-! ### The samplers as independent trials on a probability space -/

section IID

open ExactSampling.RejectionLoop
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Trial records `(proposal, accepted, cost)`: the accepted records. -/
def acceptedSet (ι : Type*) : Set (ι × Bool × ℕ) := {r | r.2.1 = true}

/-- The accepted records with proposal `j`. -/
def acceptedAt {ι : Type*} (j : ι) : Set (ι × Bool × ℕ) := {r | r.1 = j ∧ r.2.1 = true}

/-- Independent trials with a finite set of proposals. If one trial accepts proposal `j` with
probability `α_j`, then a trial succeeds with probability `s = ∑ⱼ α_j`, the first accepted
proposal is `j` with probability `α_j / s`, the expected total cost of all reached trials is
`E[cost of one trial] / s`, and the expected number of trials is `1 / s`. This applies
`first_success_law`, `renewal_cost` and `expected_trials` of `ExactSampling.RejectionLoop`.
Auxiliary for the repeated-trial arguments in the proof of `prop:conf-row` (conference.tex) and
of `lem:attentionraceexact` (attention_primitives.tex). -/
theorem iid_trials {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (Y : ℕ → Ω → ι × Bool × ℕ) (hY : iIndepFun Y P) (hid : ∀ m, P.map (Y m) = P.map (Y 0))
    (hmeas : ∀ m, Measurable (Y m)) (α : ι → ℝ) (hα : ∀ j, 0 ≤ α j) (hs : 0 < ∑ j, α j)
    (hmass : ∀ j, P (Y 0 ⁻¹' acceptedAt j) = ENNReal.ofReal (α j)) :
    P (Y 0 ⁻¹' acceptedSet ι) = ENNReal.ofReal (∑ j, α j) ∧
    (∀ j, P {ω | ∃ m, ω ∈ Reached Y (acceptedSet ι) m ∧ Y m ω ∈ acceptedAt j}
      = ENNReal.ofReal (α j / ∑ j, α j)) ∧
    ∫⁻ ω, ∑' m, (Reached Y (acceptedSet ι) m).indicator (fun ω => ((Y m ω).2.2 : ℝ≥0∞)) ω ∂P
      = (∫⁻ ω, ((Y 0 ω).2.2 : ℝ≥0∞) ∂P) / ENNReal.ofReal (∑ j, α j) ∧
    ∫⁻ ω, ∑' m, (Reached Y (acceptedSet ι) m).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P
      = ENNReal.ofReal (1 / ∑ j, α j) := by
  classical
  have hms : ∀ t : Set (ι × Bool × ℕ), MeasurableSet t := fun t =>
    (Set.to_countable t).measurableSet
  have hS : P (Y 0 ⁻¹' acceptedSet ι) = ENNReal.ofReal (∑ j, α j) := by
    have hU : Y 0 ⁻¹' acceptedSet ι = ⋃ j ∈ (Finset.univ : Finset ι), Y 0 ⁻¹' acceptedAt j := by
      ext ω; simp [acceptedSet, acceptedAt]
    rw [hU, measure_biUnion_finset]
    · rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => hα j)]
      exact Finset.sum_congr rfl fun j _ => hmass j
    · intro i _ j _ hij
      exact Disjoint.preimage _ (Set.disjoint_left.mpr fun r hr hr' => hij (hr.1.symm.trans hr'.1))
    · intro j _
      exact hmeas 0 (hms _)
  refine ⟨hS, fun j => ?_, ?_, ?_⟩
  · rw [ExactSampling.RejectionLoop.first_success_law Y hY hid hmeas (hms _) (hms _)
      (fun r hr => hr.2), hmass j, hS, ENNReal.ofReal_div_of_pos hs]
  · have hc := ExactSampling.RejectionLoop.renewal_cost Y hY hid hmeas (hms (acceptedSet ι))
      (fun r : ι × Bool × ℕ => (r.2.2 : ℝ≥0∞)) (measurable_of_countable _)
    rw [hS] at hc
    exact hc
  · rw [ExactSampling.RejectionLoop.expected_trials Y hY hid hmeas (hms _), hS,
      ENNReal.ofReal_div_of_pos hs, ENNReal.ofReal_one]

/-- The row sampler as independent trials. Let the trial records `Y m = (sign, accepted,
requests)` be independent and identically distributed, with one-trial law given by the
construction of `prop:conf-row` (conference.tex): proposal `y = ±1` is accepted with probability
`m(y)` (the Poisson series `rowTrialMass`), and the expected number of input requests of one trial
is the Poisson average `∑ₖ P(N = k) k ρ`. Then the first accepted sign equals `y` with probability
`e^{yu} / (e^u + e^{-u})` (mean `tanh u`), the expected total number of input requests is
`2 ∑ⱼ |wⱼ| / (e^{-A} cosh u) ≤ 2A e^A ≤ 4e^2`, and the expected number of trials is
`1 / (e^{-A} cosh u)`. Paper: proof of `prop:conf-row` (conference.tex). -/
theorem row_sampler_iid {n : ℕ} (c : ℝ) (w x : Fin n → ℝ) (hc : |c| ≤ 1)
    (hw : ∑ j, |w j| ≤ 1) (hx : ∀ j, x j = 1 ∨ x j = -1) (hA : 0 < amplitude c w)
    (Y : ℕ → Ω → Bool × Bool × ℕ) (hY : iIndepFun Y P) (hid : ∀ m, P.map (Y m) = P.map (Y 0))
    (hmeas : ∀ m, Measurable (Y m))
    (hmass : ∀ b, P (Y 0 ⁻¹' acceptedAt b) = ENNReal.ofReal (rowTrialMass c w x (signVal b)))
    (hreq : ∫⁻ ω, ((Y 0 ω).2.2 : ℝ≥0∞) ∂P
      = ENNReal.ofReal (∑' k : ℕ, (poissonMeasure (2 * amplitude c w).toNNReal).real {k}
        * (k * ((∑ j, |w j|) / amplitude c w)))) :
    (∀ b, P {ω | ∃ m, ω ∈ Reached Y (acceptedSet Bool) m ∧ Y m ω ∈ acceptedAt b}
      = ENNReal.ofReal (exp (signVal b * preact c w x)
          / (exp (preact c w x) + exp (-preact c w x)))) ∧
    ∫⁻ ω, ∑' m, (Reached Y (acceptedSet Bool) m).indicator (fun ω => ((Y m ω).2.2 : ℝ≥0∞)) ω ∂P
      = ENNReal.ofReal ((2 * ∑ j, |w j|) / (exp (-amplitude c w) * cosh (preact c w x))) ∧
    (2 * ∑ j, |w j|) / (exp (-amplitude c w) * cosh (preact c w x))
        ≤ 2 * amplitude c w * exp (amplitude c w) ∧
    2 * amplitude c w * exp (amplitude c w) ≤ 4 * exp 2 ∧
    ∫⁻ ω, ∑' m, (Reached Y (acceptedSet Bool) m).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P
      = ENNReal.ofReal (1 / (exp (-amplitude c w) * cosh (preact c w x))) := by
  have hx' : ∀ j, |x j| ≤ 1 := fun j => by rcases hx j with h | h <;> simp [h]
  obtain ⟨-, -, hsum, hlaw, -⟩ := row_trial_law c w x hA
  obtain ⟨hs0, -⟩ := trial_success_bounds (abs_preact_le c w x hx')
  have hspos : 0 < exp (-amplitude c w) * cosh (preact c w x) :=
    lt_of_lt_of_le (exp_pos _) hs0
  have hα : ∀ b, 0 ≤ rowTrialMass c w x (signVal b) := fun b => by
    rw [rowTrialMass_eq c w x hA]; positivity
  have hsumα : ∑ b, rowTrialMass c w x (signVal b)
      = exp (-amplitude c w) * cosh (preact c w x) := by
    rw [Fintype.sum_bool, ← hsum]; simp [signVal]
  obtain ⟨-, hfirst, hcost, htrials⟩ := iid_trials Y hY hid hmeas
    (fun b => rowTrialMass c w x (signVal b)) hα (by rw [hsumα]; exact hspos) hmass
  rw [hsumα] at hfirst hcost htrials
  obtain ⟨-, hreq1, hreq2⟩ := row_expected_requests c w x hc hw hx' hA
  refine ⟨fun b => ?_, ?_, hreq1, hreq2, htrials⟩
  · rw [hfirst b, ← hlaw b, hsum]
  · rw [hcost, hreq, (trial_requests c w hA).1.tsum_eq, ← ENNReal.ofReal_div_of_pos hspos]

/-- The attention race as independent trials. Let the trial records `Y m = (proposal, accepted,
score tests)` be independent and identically distributed, with one-trial law given by the
construction after `prop:conf-row` (conference.tex): proposal `j` is uniform and is accepted with
probability `∑ₖ P(N = k) ((1 + a_j / A) / 2)^k` for `N ∼ Pois(2A)`, and the expected number of
inspected score coins of one trial is `T⁻¹ ∑ⱼ g_j` with `g_j` the stopped Poisson test count.
Then the first accepted index has the attention law `e^{a_j} / ∑ₖ e^{a_k}`, the expected number
of score tests is at most `e^{2A} - 1`, the expected predecessor count (two signs per test and
one fresh value sign) is at most `2e^{2A} - 1`, and the expected number of proposals is at most
`e^{2A}`. Paper: the paragraph after `prop:conf-row` (conference.tex); full version:
`lem:attentionraceexact`, `lem:stoppedpoissonattention` and `thm:attentionprimitive`
(attention_primitives.tex). -/
theorem attention_race_iid {T : ℕ} (hT : 0 < T) (a : Fin T → ℝ) {A : ℝ} (hA : 0 < A)
    (ha : ∀ j, |a j| ≤ A) (Y : ℕ → Ω → Fin T × Bool × ℕ) (hY : iIndepFun Y P)
    (hid : ∀ m, P.map (Y m) = P.map (Y 0)) (hmeas : ∀ m, Measurable (Y m))
    (hmass : ∀ j, P (Y 0 ⁻¹' acceptedAt j) = ENNReal.ofReal
      ((∑' k : ℕ, (poissonMeasure (2 * A).toNNReal).real {k} * ((1 + a j / A) / 2) ^ k) / T))
    (htests : ∫⁻ ω, ((Y 0 ω).2.2 : ℝ≥0∞) ∂P = ENNReal.ofReal
      (∑ j, (∑' k : ℕ, (poissonMeasure (2 * A).toNNReal).real {k}
          * ∑ i ∈ range k, ((1 + a j / A) / 2) ^ i) / T)) :
    (∀ j, P {ω | ∃ m, ω ∈ Reached Y (acceptedSet (Fin T)) m ∧ Y m ω ∈ acceptedAt j}
      = ENNReal.ofReal (exp (a j) / ∑ k, exp (a k))) ∧
    ∫⁻ ω, ∑' m, (Reached Y (acceptedSet (Fin T)) m).indicator
        (fun ω => ((Y m ω).2.2 : ℝ≥0∞)) ω ∂P ≤ ENNReal.ofReal (exp (2 * A) - 1) ∧
    2 * ∫⁻ ω, ∑' m, (Reached Y (acceptedSet (Fin T)) m).indicator
        (fun ω => ((Y m ω).2.2 : ℝ≥0∞)) ω ∂P + 1 ≤ ENNReal.ofReal (2 * exp (2 * A) - 1) ∧
    ∫⁻ ω, ∑' m, (Reached Y (acceptedSet (Fin T)) m).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P
      ≤ ENNReal.ofReal (exp (2 * A)) := by
  have hr : ((2 * A).toNNReal : ℝ) = 2 * A := Real.coe_toNNReal _ (by linarith)
  have hacc : ∀ j, (∑' k : ℕ, (poissonMeasure (2 * A).toNNReal).real {k}
      * ((1 + a j / A) / 2) ^ k) / T = exp (a j - A) / T := fun j => by
    rw [attention_acceptance hA hr]
  obtain ⟨h1, -, -, -, hprop⟩ := attention_first_accept hT a ha
  have hpos : 0 < ∑ k, exp (a k - A) / T := lt_of_lt_of_le (exp_pos _) h1
  have hα : ∀ j, 0 ≤ (∑' k : ℕ, (poissonMeasure (2 * A).toNNReal).real {k}
      * ((1 + a j / A) / 2) ^ k) / T := fun j => by rw [hacc]; positivity
  have hsumα : ∑ j, (∑' k : ℕ, (poissonMeasure (2 * A).toNNReal).real {k}
      * ((1 + a j / A) / 2) ^ k) / T = ∑ k, exp (a k - A) / T :=
    Finset.sum_congr rfl fun j _ => hacc j
  obtain ⟨-, hfirst, hcost, htrials⟩ := iid_trials Y hY hid hmeas _ hα
    (by rw [hsumα]; exact hpos) hmass
  rw [hsumα] at hfirst hcost htrials
  obtain ⟨hpred1, -⟩ := attention_predecessor_count hT a hA ha
  have hG : 0 ≤ ∑ j, (∑' k : ℕ, (poissonMeasure (2 * A).toNNReal).real {k}
      * ∑ i ∈ range k, ((1 + a j / A) / 2) ^ i) / T := by
    apply Finset.sum_nonneg
    intro j _
    apply div_nonneg _ (Nat.cast_nonneg T)
    apply tsum_nonneg
    intro k
    apply mul_nonneg measureReal_nonneg
    apply Finset.sum_nonneg
    intro i _
    have hb := bit_bias_mem_Icc (u := a j) (Y := 1) hA (ha j) (Or.inl rfl)
    simp only [one_mul] at hb
    exact pow_nonneg hb.1 i
  have htot : ∫⁻ ω, ∑' m, (Reached Y (acceptedSet (Fin T)) m).indicator
      (fun ω => ((Y m ω).2.2 : ℝ≥0∞)) ω ∂P ≤ ENNReal.ofReal (exp (2 * A) - 1) := by
    rw [hcost, htests, ← ENNReal.ofReal_div_of_pos hpos]
    exact ENNReal.ofReal_le_ofReal hpred1
  have hE : 0 ≤ exp (2 * A) - 1 := by
    have := Real.add_one_le_exp (2 * A); linarith
  refine ⟨fun j => ?_, htot, ?_, ?_⟩
  · rw [hfirst j, hacc j, attention_normalized_mass hT a A j]
  · calc 2 * ∫⁻ ω, ∑' m, (Reached Y (acceptedSet (Fin T)) m).indicator
          (fun ω => ((Y m ω).2.2 : ℝ≥0∞)) ω ∂P + 1
        ≤ 2 * ENNReal.ofReal (exp (2 * A) - 1) + 1 := by gcongr
      _ = ENNReal.ofReal (2 * exp (2 * A) - 1) := by
        rw [show 2 * exp (2 * A) - 1 = 2 * (exp (2 * A) - 1) + 1 by ring,
          ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_mul zero_le_two,
          ENNReal.ofReal_ofNat, ENNReal.ofReal_one]
  · rw [htrials]
    exact ENNReal.ofReal_le_ofReal hprop

end IID

end ExactSampling.RowFactory
