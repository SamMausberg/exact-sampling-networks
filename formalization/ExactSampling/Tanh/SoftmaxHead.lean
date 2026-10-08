import Mathlib

/-!
# The bounded softmax output head

This module formalizes the exact categorical output used after the tanh network
(`thm:boundedsoftmaxinterface`, `attention_primitives.tex`, Section
`sec:boundedoutputprimitive`), whose proof applies the Poisson race with score range `A = 1`:

* the Poisson probability generating function `E ρ^N = exp (λ (ρ - 1))` for
  `N ~ Poisson(λ)`, as a `HasSum` identity (proof of `lem:attentionraceexact`);
* the acceptance probability `exp (z - 1)` of a logit test with `N ~ Poisson(2)` coins of bias
  `(1 + z)/2`, and the general exponent identity `-2A(1 - p) = a - A`;
* the law of the first accepted category, `exp (z_k) / Σ_j exp (z_j)`, as a geometric
  `HasSum` over the number of rejected proposals, together with almost sure termination and
  the bound `e²` on the expected number of proposals;
* the stopped Poisson tests `lem:stoppedpoissonattention` (exact mean and the convexity
  bound `E G ≤ (e^λ - 1) e^{-λ(1-p)}`), giving at most `e² - 1` expected sign requests;
* the small Poisson generator of `lem:smallpoissonattention` (acceptance below one, success
  probability `1/8`, exact Poisson law of the accepted count);
* the binary head: logits `±v` give the sign mean `tanh v`.

Not formalized: the finite-bit refinement of the acceptance probabilities, the bit-work bound
`O(B⁴)`, and the construction of the logit sign interfaces themselves. The conference-version
row sampler `prop:conf-row` is formalized separately in `ExactSampling/Conference/`.
-/

namespace ExactSampling.SoftmaxHead

open Real Finset

/-! ### Poisson laws and generating functions -/

/-- The Poisson probability mass function `e^{-λ} λ^k / k!`, as in `lem:attentionraceexact`
(`attention_primitives.tex`). -/
noncomputable def poissonPmf (lam : ℝ) (k : ℕ) : ℝ := exp (-lam) * lam ^ k / (k.factorial : ℝ)

/-- The exponential series `Σ_k x^k / k! = exp x`. Auxiliary for `lem:attentionraceexact`
(`attention_primitives.tex`). -/
theorem hasSum_exp_series (x : ℝ) : HasSum (fun k : ℕ => x ^ k / (k.factorial : ℝ)) (exp x) := by
  rw [exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

/-- The Poisson probability generating function `E ρ^N = exp (λ (ρ - 1))`.
Paper: `lem:attentionraceexact` (`attention_primitives.tex`), used by
`thm:boundedsoftmaxinterface`. -/
theorem poisson_pgf (lam ρ : ℝ) :
    HasSum (fun k : ℕ => poissonPmf lam k * ρ ^ k) (exp (lam * (ρ - 1))) := by
  have h := (hasSum_exp_series (lam * ρ)).mul_left (exp (-lam))
  convert h using 1
  · funext k
    unfold poissonPmf
    rw [mul_pow]
    ring
  · rw [← exp_add]
    congr 1
    ring

/-- The Poisson probabilities sum to one. Auxiliary for `lem:stoppedpoissonattention`
(`attention_primitives.tex`). -/
theorem hasSum_poissonPmf (lam : ℝ) : HasSum (poissonPmf lam) 1 := by
  have h := poisson_pgf lam 1
  simpa using h

/-- The Poisson probabilities are nonnegative. Auxiliary for `lem:attentionraceexact`
(`attention_primitives.tex`). -/
theorem poissonPmf_nonneg {lam : ℝ} (h : 0 ≤ lam) (k : ℕ) : 0 ≤ poissonPmf lam k := by
  unfold poissonPmf; positivity

/-- The exponent of the score test: with `λ = 2A` and coin bias `p = (1 + a/A)/2`,
`λ (p - 1) = a - A`. Paper: `lem:attentionraceexact` (`attention_primitives.tex`). -/
theorem normalized_logit_exponent (A a : ℝ) (hA : A ≠ 0) :
    2 * A * ((1 + a / A) / 2 - 1) = a - A := by
  field_simp
  ring

/-- A logit test accepts with probability `exp (z - 1)`: `N ~ Poisson(2)` coins of bias
`(1 + z)/2` all succeed with this probability.
Paper: proof of `thm:boundedsoftmaxinterface` (`attention_primitives.tex`). -/
theorem logit_test_acceptance (z : ℝ) :
    HasSum (fun k : ℕ => poissonPmf 2 k * ((1 + z) / 2) ^ k) (exp (z - 1)) := by
  have h := poisson_pgf 2 ((1 + z) / 2)
  convert h using 2
  ring

/-! ### The first accepted category -/

/-- Rescaling every weight by a common nonzero factor leaves the normalized weights unchanged.
Auxiliary for `lem:attentionraceexact` (`attention_primitives.tex`). -/
theorem common_scale_normalization {I : Type*} [Fintype I] (w : I → ℝ) (c : ℝ) (hc : c ≠ 0)
    (i : I) : (c * w i) / (∑ j, c * w j) = w i / (∑ j, w j) := by
  rw [← Finset.mul_sum]
  by_cases hsum : (∑ j, w j) = 0
  · simp [hsum]
  · field_simp

/-- A common shift of the logits leaves the softmax law unchanged.
Paper: `lem:attentionraceexact` (`attention_primitives.tex`), cancellation of the common scale. -/
theorem shifted_exp_softmax {I : Type*} [Fintype I] (z : I → ℝ) (M : ℝ) (i : I) :
    exp (z i - M) / (∑ j, exp (z j - M)) = exp (z i) / (∑ j, exp (z j)) := by
  have hform (j : I) : exp (z j - M) = exp (-M) * exp (z j) := by
    rw [show z j - M = -M + z j by ring, exp_add]
  simp_rw [hform]
  exact common_scale_normalization (fun j => exp (z j)) (exp (-M)) (exp_ne_zero _) i

/-- The overall success probability `s = K⁻¹ Σ_k exp (z_k - 1)` of one uniform proposal
(`lem:attentionraceexact` with `A = 1`, `attention_primitives.tex`). -/
noncomputable def proposalSuccess {K : ℕ} (z : Fin K → ℝ) : ℝ :=
  (∑ k, exp (z k - 1)) / K

/-- A proposal succeeds with positive probability. Paper: `lem:attentionraceexact`
(`attention_primitives.tex`). -/
theorem proposalSuccess_pos {K : ℕ} (hK : 0 < K) (z : Fin K → ℝ) : 0 < proposalSuccess z := by
  unfold proposalSuccess
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  apply div_pos _ (by exact_mod_cast hK)
  exact Finset.sum_pos (fun k _ => exp_pos _) Finset.univ_nonempty

/-- Bounded logits give success probability in `[e^{-2}, 1]`.
Paper: `lem:attentionraceexact` (`attention_primitives.tex`) with `A = 1`. -/
theorem proposalSuccess_mem {K : ℕ} (hK : 0 < K) (z : Fin K → ℝ) (hz : ∀ k, |z k| ≤ 1) :
    exp (-2) ≤ proposalSuccess z ∧ proposalSuccess z ≤ 1 := by
  unfold proposalSuccess
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hlow : ∀ k, exp (-2) ≤ exp (z k - 1) := fun k =>
    exp_le_exp.mpr (by linarith [(abs_le.mp (hz k)).1])
  have hup : ∀ k, exp (z k - 1) ≤ 1 := fun k =>
    exp_le_one_iff.mpr (by linarith [(abs_le.mp (hz k)).2])
  have h1 : ∑ _k : Fin K, exp (-2) ≤ ∑ k, exp (z k - 1) := Finset.sum_le_sum (fun k _ => hlow k)
  have h2 : ∑ k, exp (z k - 1) ≤ ∑ _k : Fin K, (1 : ℝ) := Finset.sum_le_sum (fun k _ => hup k)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h1 h2
  constructor
  · rw [le_div_iff₀ hKr]; linarith
  · rw [div_le_one hKr]; exact h2

/-- The first accepted category has the softmax law: summing over the number `m` of rejected
proposals, `Σ_m (1 - s)^m · K⁻¹ exp (z_k - 1) = exp (z_k) / Σ_j exp (z_j)`.
Paper: `thm:boundedsoftmaxinterface` and `lem:attentionraceexact`
(`attention_primitives.tex`). -/
theorem softmax_race_law {K : ℕ} (hK : 0 < K) (z : Fin K → ℝ) (hz : ∀ k, |z k| ≤ 1)
    (k : Fin K) :
    HasSum (fun m : ℕ => (1 - proposalSuccess z) ^ m * (exp (z k - 1) / K))
      (exp (z k) / ∑ j, exp (z j)) := by
  obtain ⟨_, h1⟩ := proposalSuccess_mem hK z hz
  have hs := proposalSuccess_pos hK z
  have hg := hasSum_geometric_of_lt_one (r := 1 - proposalSuccess z) (by linarith) (by linarith)
  have h := hg.mul_right (exp (z k - 1) / K)
  rw [sub_sub_cancel] at h
  convert h using 1
  rw [← shifted_exp_softmax z 1 k]
  unfold proposalSuccess
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hsum : ∑ j, exp (z j - 1) ≠ 0 := by
    have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
    exact (Finset.sum_pos (fun j _ => exp_pos _) Finset.univ_nonempty).ne'
  field_simp

/-- The softmax category probabilities sum to one; together with `softmax_race_law` this says the
accepted category is defined with probability one. Paper: `thm:boundedsoftmaxinterface`
(`attention_primitives.tex`). -/
theorem softmax_law_total {K : ℕ} (hK : 0 < K) (z : Fin K → ℝ) :
    ∑ k, exp (z k) / ∑ j, exp (z j) = 1 := by
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  rw [← Finset.sum_div, div_self (Finset.sum_pos (fun j _ => exp_pos _) Finset.univ_nonempty).ne']

/-- The expected number of proposals is `1/s ≤ e²`.
Paper: `thm:boundedsoftmaxinterface` (`attention_primitives.tex`), "`e²` expected
proposals". -/
theorem expected_proposals_le {K : ℕ} (hK : 0 < K) (z : Fin K → ℝ) (hz : ∀ k, |z k| ≤ 1) :
    HasSum (fun m : ℕ => (1 - proposalSuccess z) ^ m) (1 / proposalSuccess z) ∧
      1 / proposalSuccess z ≤ exp 2 := by
  obtain ⟨h0, h1⟩ := proposalSuccess_mem hK z hz
  have hs := proposalSuccess_pos hK z
  constructor
  · have hg := hasSum_geometric_of_lt_one (r := 1 - proposalSuccess z) (by linarith) (by linarith)
    simpa [sub_sub_cancel, one_div] using hg
  · rw [div_le_iff₀ hs]
    calc (1 : ℝ) = exp 2 * exp (-2) := by rw [← exp_add]; norm_num
      _ ≤ exp 2 * proposalSuccess z := mul_le_mul_of_nonneg_left h0 (exp_pos _).le

/-! ### Stopped Poisson tests -/

/-- Conditional on `N = k`, the number of coins inspected before the first failure has mean
`Σ_{r<k} p^r`. Summed against the Poisson law, the mean is `(1 - e^{-λ(1-p)})/(1-p)` for
`p ≠ 1`. Paper: `lem:stoppedpoissonattention` (`attention_primitives.tex`). -/
theorem stopped_poisson_mean {lam p : ℝ} (hp : p ≠ 1) :
    HasSum (fun k : ℕ => poissonPmf lam k * ∑ r ∈ Finset.range k, p ^ r)
      ((1 - exp (-lam * (1 - p))) / (1 - p)) := by
  have hq : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  have h := ((hasSum_poissonPmf lam).sub (poisson_pgf lam p)).div_const (1 - p)
  convert h using 1
  · funext k
    rw [geom_sum_eq hp]
    field_simp
    ring
  · congr 1
    ring_nf

/-- At `p = 1` every one of the `N` coins is read, and the mean is `λ`.
Paper: `lem:stoppedpoissonattention` (`attention_primitives.tex`). -/
theorem stopped_poisson_mean_one (lam : ℝ) :
    HasSum (fun k : ℕ => poissonPmf lam k * ∑ r ∈ Finset.range k, (1 : ℝ) ^ r) lam := by
  have h := (hasSum_exp_series lam).mul_left (lam * exp (-lam))
  have hshift : HasSum (fun k : ℕ => poissonPmf lam (k + 1) * ((k + 1 : ℕ) : ℝ)) lam := by
    convert h using 1
    · funext k
      unfold poissonPmf
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · rw [mul_assoc, ← exp_add]; simp
  have h0 : HasSum (fun k : ℕ => poissonPmf lam k * (k : ℝ)) lam := by
    rw [← hasSum_nat_add_iff' 1]
    simpa using hshift
  convert h0 using 1
  funext k
  simp

/-- The convexity bound `(e^{λq} - 1)/q ≤ e^λ - 1` for `0 < q ≤ 1`, `λ ≥ 0`.
Paper: `lem:stoppedpoissonattention` (`attention_primitives.tex`), proof of
`eq:stoppedpoissonratio`. -/
theorem exp_mul_sub_one_le {lam q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (exp (lam * q) - 1) / q ≤ exp lam - 1 := by
  have hc := convexOn_exp.2 (Set.mem_univ lam) (Set.mem_univ 0) hq0.le (sub_nonneg.mpr hq1)
    (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, exp_zero, mul_one] at hc
  rw [div_le_iff₀ hq0]
  have : exp (q * lam) = exp (lam * q) := by rw [mul_comm]
  linarith

/-- The stopped-test bound `E G ≤ (e^λ - 1) e^{-λ(1-p)}` for a coin of bias `p ∈ [0, 1)`.
Paper: `eq:stoppedpoissonratio` in `lem:stoppedpoissonattention`
(`attention_primitives.tex`). -/
theorem stopped_poisson_ratio {lam p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    (1 - exp (-lam * (1 - p))) / (1 - p) ≤ (exp lam - 1) * exp (-lam * (1 - p)) := by
  have hq0 : 0 < 1 - p := by linarith
  have hq1 : 1 - p ≤ 1 := by linarith
  have h := exp_mul_sub_one_le (lam := lam) hq0 hq1
  have he := exp_pos (-lam * (1 - p))
  have hinv : exp (-lam * (1 - p)) * exp (lam * (1 - p)) = 1 := by
    rw [← exp_add]; ring_nf; exact exp_zero
  rw [div_le_iff₀ hq0] at h ⊢
  have key : 1 - exp (-lam * (1 - p)) = exp (-lam * (1 - p)) * (exp (lam * (1 - p)) - 1) := by
    rw [mul_sub (exp (-lam * (1 - p))) (exp (lam * (1 - p))) 1, hinv, mul_one]
  rw [key]
  calc exp (-lam * (1 - p)) * (exp (lam * (1 - p)) - 1)
      ≤ exp (-lam * (1 - p)) * ((exp lam - 1) * (1 - p)) := mul_le_mul_of_nonneg_left h he.le
    _ = (exp lam - 1) * exp (-lam * (1 - p)) * (1 - p) := by ring

/-- The stopped-test bound at `p = 1`: `λ ≤ e^λ - 1`. Paper: `lem:stoppedpoissonattention`
(`attention_primitives.tex`), the case `q = 0`. -/
theorem stopped_poisson_ratio_one (lam : ℝ) : lam ≤ (exp lam - 1) * exp (-lam * (1 - 1)) := by
  simp only [sub_self, mul_zero, exp_zero, mul_one]
  linarith [add_one_le_exp lam]

/-- The expected number of logit-sign requests of the whole softmax race is at most `e² - 1`:
if a proposal of `k` inspects `g_k ≤ (e² - 1) e^{z_k - 1}` coins on average, the total
`(K⁻¹ Σ_k g_k) / s` over all proposals is at most `e² - 1`.
Paper: `thm:boundedsoftmaxinterface` (`attention_primitives.tex`), "at most `e² - 1` expected
sign requests", from `lem:stoppedpoissonattention` and predictable charging. -/
theorem expected_requests_le {K : ℕ} (hK : 0 < K) (z : Fin K → ℝ) (g : Fin K → ℝ)
    (hg : ∀ k, g k ≤ (exp 2 - 1) * exp (z k - 1)) :
    ((∑ k, g k) / K) / proposalSuccess z ≤ exp 2 - 1 := by
  have hs := proposalSuccess_pos hK z
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  rw [div_le_iff₀ hs]
  unfold proposalSuccess
  rw [div_le_iff₀ hKr, mul_div_assoc', div_mul_cancel₀ _ hKr.ne', Finset.mul_sum]
  exact Finset.sum_le_sum (fun k _ => hg k)

/-- For a logit `z ∈ [-1, 1)`, the stopped-test mean of a proposal satisfies
`g ≤ (e² - 1) e^{z - 1}` with `λ = 2` and `p = (1 + z)/2`; the case `z = 1` is
`logit_stopped_tests_le_one`.
Paper: proof of `thm:boundedsoftmaxinterface` (`attention_primitives.tex`). -/
theorem logit_stopped_tests_le {z : ℝ} (hz : |z| ≤ 1) (hz1 : z < 1) :
    (1 - exp (-2 * (1 - (1 + z) / 2))) / (1 - (1 + z) / 2) ≤ (exp 2 - 1) * exp (z - 1) := by
  have h := stopped_poisson_ratio (lam := 2) (p := (1 + z) / 2)
    (by linarith [(abs_le.mp hz).1]) (by linarith)
  have e : -2 * (1 - (1 + z) / 2) = z - 1 := by ring
  rw [e] at h ⊢
  exact h

/-- The case `z = 1` of `logit_stopped_tests_le`: the coin has bias one, every one of the `N`
coins is read, the mean is `λ = 2` (`stopped_poisson_mean_one`), and `2 ≤ (e² - 1) e^{z-1}`.
Paper: proof of `thm:boundedsoftmaxinterface` (`attention_primitives.tex`). -/
theorem logit_stopped_tests_le_one : (2 : ℝ) ≤ (exp 2 - 1) * exp (1 - 1) := by
  simp only [sub_self, exp_zero, mul_one]
  linarith [add_one_le_exp (2 : ℝ)]

/-! ### Small Poisson draws -/

/-- The acceptance probability `a_k = e^{-θ} (2θ)^k / (4 k!)` of the small Poisson generator
is at most one for `θ ∈ [0, 1]`. Paper: `lem:smallpoissonattention`
(`attention_primitives.tex`). -/
theorem small_poisson_acceptance_le_one {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (k : ℕ) :
    exp (-θ) * (2 * θ) ^ k / (4 * (k.factorial : ℝ)) ≤ 1 := by
  have hterm : (2 * θ) ^ k / (k.factorial : ℝ) ≤ exp (2 * θ) := by
    have hs := hasSum_exp_series (2 * θ)
    exact le_hasSum hs k (fun j _ => by positivity)
  have hF : (0 : ℝ) < k.factorial := by positivity
  have he : exp (-θ) * exp (2 * θ) = exp θ := by rw [← exp_add]; ring_nf
  have heθ : exp θ ≤ exp 1 := exp_le_exp.mpr h1
  have he1 : exp 1 < 4 := lt_trans exp_one_lt_d9 (by norm_num)
  rw [div_le_one (by positivity)]
  calc exp (-θ) * (2 * θ) ^ k = exp (-θ) * ((2 * θ) ^ k / (k.factorial : ℝ)) * k.factorial := by
        field_simp
    _ ≤ exp (-θ) * exp (2 * θ) * k.factorial := by
        gcongr
    _ = exp θ * k.factorial := by rw [he]
    _ ≤ 4 * k.factorial := by
        apply mul_le_mul_of_nonneg_right (by linarith) hF.le

/-- The proposal `2^{-k-1}` times the acceptance `a_k` is `(1/8) e^{-θ} θ^k / k!`, so each trial
succeeds with probability `1/8`. Paper: `lem:smallpoissonattention`
(`attention_primitives.tex`). -/
theorem small_poisson_trial_mass (θ : ℝ) (k : ℕ) :
    (1 / 2) ^ (k + 1) * (exp (-θ) * (2 * θ) ^ k / (4 * (k.factorial : ℝ))) =
      poissonPmf θ k / 8 := by
  unfold poissonPmf
  rw [one_div, inv_pow, mul_pow, pow_succ]
  field_simp
  ring

/-- One trial of the small Poisson generator succeeds with probability `1/8`. Paper:
`lem:smallpoissonattention` (`attention_primitives.tex`). -/
theorem small_poisson_success (θ : ℝ) :
    HasSum (fun k : ℕ => (1 / 2) ^ (k + 1) * (exp (-θ) * (2 * θ) ^ k / (4 * (k.factorial : ℝ))))
      (1 / 8) := by
  simp_rw [small_poisson_trial_mass]
  have := (hasSum_poissonPmf θ).div_const 8
  simpa using this

/-- The accepted count of the small Poisson generator has exactly the Poisson law:
`Σ_m (7/8)^m · poissonPmf θ k / 8 = poissonPmf θ k`. Paper: `lem:smallpoissonattention`
(`attention_primitives.tex`). -/
theorem small_poisson_law (θ : ℝ) (k : ℕ) :
    HasSum (fun m : ℕ => (7 / 8 : ℝ) ^ m * (poissonPmf θ k / 8)) (poissonPmf θ k) := by
  have hg := hasSum_geometric_of_lt_one (r := (7 / 8 : ℝ)) (by norm_num) (by norm_num)
  have h := hg.mul_right (poissonPmf θ k / 8)
  convert h using 1
  norm_num
  ring

/-! ### The binary head -/

/-- Logits `±v` give the sign mean `tanh v`: the plus category has probability
`e^v / (e^v + e^{-v})`. Paper: `thm:boundedsoftmaxinterface` (`attention_primitives.tex`)
with two categories; used for the binary softmax head after a tanh layer
(`main_attention.tex`, worked example). -/
theorem binary_softmax_mean (v : ℝ) :
    exp v / (exp v + exp (-v)) - exp (-v) / (exp v + exp (-v)) = tanh v := by
  rw [tanh_eq, sub_div]

/-- The binary head through the race: with logits `z = (v, -v)` and `|v| ≤ 1`, the first
accepted category has the probabilities `e^{±v}/(e^v + e^{-v})`, so the returned sign has mean
`tanh v`. Paper: `thm:boundedsoftmaxinterface` (`attention_primitives.tex`). -/
theorem binary_race_mean (v : ℝ) :
    let z : Fin 2 → ℝ := ![v, -v]
    exp (z 0) / ∑ j, exp (z j) - exp (z 1) / ∑ j, exp (z j) = tanh v := by
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact binary_softmax_mean v

end ExactSampling.SoftmaxHead
