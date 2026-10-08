import Mathlib

/-!
# The product law of the arity proposal

This module formalizes the quantitative identities behind the cosh-product sampler for the
majority index (`tanh_large_radius.tex`, Section `sec:productarity`):

* `lem:productaritylaw`: with `a_j = 4u²/(π²(2j-1)²)` and `p_j = 1/(1 + a_j)`, a geometric
  variable of parameter `p_j` has mean `a_j`, so each pair `G_{j,1} + G_{j,2}` has mean `2a_j`,
  and `E K = Σ_j 2 a_j = u²` by the sum of reciprocal odd squares
  `Σ_{j ≥ 1} (2j-1)⁻² = π²/8`;
* `lem:producttail`: the activation probability `1 - e^{-μ_j} = 1 - p_j²` with
  `μ_j = 2 log(1 + a_j)`, the conditional case probability `(1 - p_j)/(1 - p_j²) = 1/(1 + p_j)`,
  the domination `μ_j ≤ 2 a_j ≤ ν_j = 2u²/(j(j-1))` above the cutoff, the mark law
  `J/(j(j-1))` of `eq:producttailindex` (its total mass is one, the event `1 + ⌊J/U⌋ = j` is the
  interval `(J/j, J/(j-1)]`, and its length is `J/(j(j-1))`), and the Poisson mean
  `Λ = Σ_{j > J} ν_j = 2u²/J`;
* `lem:productaritybits`: the Poisson proposal for parameters `λ ≤ 2` (acceptance at most one,
  trial success `1/16`), and the refinement tail of a geometric inversion,
  `Σ_{k ≥ 1} (e^{-d(k-ε)} - e^{-d(k+ε)}) = 2 sinh(dε)/(e^d - 1) ≤ 6ε`.

Not formalized: the cosh product and the identification of the law of `K` (uniqueness of
probability generating functions), the Poisson marking and thinning theorems themselves, and
the bit-work accounting of `lem:productaritybits`.
-/

namespace ExactSampling.ProductArity

open Real

/-! ### Reciprocal odd squares and the mean arity -/

/-- `Σ_{j ≥ 0} 1/(2j+1)² = π²/8`. Paper: `lem:productaritylaw` (`tanh_large_radius.tex`),
"the sum of the reciprocal odd squares". -/
theorem hasSum_inv_odd_sq : HasSum (fun j : ℕ => 1 / ((2 * (j : ℝ) + 1) ^ 2)) (π ^ 2 / 8) := by
  have hz := hasSum_zeta_two
  have he : HasSum (fun k : ℕ => 1 / (((2 * k : ℕ) : ℝ) ^ 2)) (π ^ 2 / 24) := by
    have h4 := hz.mul_left (1 / 4)
    have e : (fun k : ℕ => 1 / (((2 * k : ℕ) : ℝ) ^ 2)) =
        fun k : ℕ => 1 / 4 * (1 / (k : ℝ) ^ 2) := by
      funext k
      push_cast
      rw [one_div_mul_one_div, mul_pow]
      norm_num
    rw [e, show π ^ 2 / 24 = 1 / 4 * (π ^ 2 / 6) by ring]
    exact h4
  have hs1 : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr hz.summable
    simpa using this
  have hsum : Summable (fun k : ℕ => 1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hs1
    push_cast
    apply one_div_le_one_div_of_le (by positivity)
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have hall := HasSum.even_add_odd (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) he hsum.hasSum
  have huniq : π ^ 2 / 6 = π ^ 2 / 24 + ∑' k : ℕ, 1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) :=
    hz.unique hall
  have hodd : ∑' k : ℕ, 1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) = π ^ 2 / 8 := by
    linarith
  have h := hsum.hasSum
  rw [hodd] at h
  have e : (fun k : ℕ => 1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2)) =
      fun j : ℕ => 1 / ((2 * (j : ℝ) + 1) ^ 2) := by
    funext j; push_cast; ring
  rw [e] at h
  exact h

/-- The weights `a_j = 4u² / (π² (2j - 1)²)` of `lem:productaritylaw` (`tanh_large_radius.tex`),
indexed from zero: `arityWeight u j = a_{j+1} = 4u²/(π²(2j+1)²)`. -/
noncomputable def arityWeight (u : ℝ) (j : ℕ) : ℝ := 4 * u ^ 2 / (π ^ 2 * (2 * (j : ℝ) + 1) ^ 2)

/-- `2 Σ_j a_j = u²`, so the arity `K = Σ_j (G_{j,1} + G_{j,2})` has mean `E K = u²`.
Paper: `lem:productaritylaw` (`tanh_large_radius.tex`). -/
theorem two_sum_arityWeight (u : ℝ) : HasSum (fun j => 2 * arityWeight u j) (u ^ 2) := by
  have h := hasSum_inv_odd_sq.mul_left (8 * u ^ 2 / π ^ 2)
  have hpi : π ^ 2 ≠ 0 := by positivity
  convert h using 1
  · funext j; unfold arityWeight; field_simp; ring
  · field_simp

/-- A geometric variable with `P(G = k) = p (1 - p)^k` has mean `(1 - p)/p`.
Paper: `lem:productaritylaw` (`tanh_large_radius.tex`). -/
theorem geometric_mean {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    HasSum (fun k : ℕ => (k : ℝ) * (p * (1 - p) ^ k)) ((1 - p) / p) := by
  have hr : ‖(1 - p : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hr).mul_left p
  convert h using 1
  · funext k; ring
  · rw [sub_sub_cancel]; field_simp

/-- With `p_j = 1/(1 + a_j)`, the geometric mean `(1 - p_j)/p_j` equals `a_j`, so each pair
`G_{j,1} + G_{j,2}` has mean `2 a_j`. Paper: `lem:productaritylaw` (`tanh_large_radius.tex`). -/
theorem geometric_mean_eq {a : ℝ} (ha : 0 ≤ a) : (1 - 1 / (1 + a)) / (1 / (1 + a)) = a := by
  have : 0 < 1 + a := by linarith
  field_simp
  ring

/-! ### The Poisson tail sampler -/

/-- The activation probability of a tail index: with `μ = 2 log(1 + a)` and `p = 1/(1 + a)`,
`1 - e^{-μ} = 1 - p²`, the probability that two independent `Geom(p)` variables are not both
zero. Paper: `lem:producttail` (`tanh_large_radius.tex`). -/
theorem activation_probability {a : ℝ} (ha : 0 ≤ a) :
    1 - exp (-(2 * log (1 + a))) = 1 - (1 / (1 + a)) ^ 2 := by
  have h : 0 < 1 + a := by linarith
  rw [show -(2 * log (1 + a)) = 2 * log ((1 + a)⁻¹) by rw [log_inv]; ring,
    show (2 : ℝ) * log ((1 + a)⁻¹) = ((2 : ℕ) : ℝ) * log ((1 + a)⁻¹) by norm_num, exp_nat_mul,
    exp_log (inv_pos.mpr h), one_div]

/-- Conditional on a positive sum, the first geometric variable is positive with probability
`(1 - p)/(1 - p²) = 1/(1 + p)`. Paper: `lem:producttail` (`tanh_large_radius.tex`). -/
theorem conditional_case_probability {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    (1 - p) / (1 - p ^ 2) = 1 / (1 + p) := by
  have h1 : 1 - p ≠ 0 := by linarith
  have h2 : 1 + p ≠ 0 := by linarith
  have h3 : 1 - p ^ 2 = (1 - p) * (1 + p) := by ring
  rw [h3]
  field_simp

/-- Above the cutoff the Poisson intensities dominate the activation intensities:
`μ_j = 2 log(1 + a_j) ≤ 2 a_j ≤ ν_j = 2u²/(j(j-1))`, using `4j(j-1) ≤ π²(2j-1)²`.
Here the index is `j ≥ 2`, written as `j = i + 2`. Paper: `lem:producttail`
(`tanh_large_radius.tex`). -/
theorem tail_domination (u : ℝ) (i : ℕ) :
    2 * log (1 + arityWeight u (i + 1)) ≤ 2 * arityWeight u (i + 1) ∧
      2 * arityWeight u (i + 1) ≤ 2 * u ^ 2 / (((i : ℝ) + 2) * ((i : ℝ) + 1)) := by
  have ha : 0 ≤ arityWeight u (i + 1) := by unfold arityWeight; positivity
  constructor
  · have := log_le_sub_one_of_pos (show 0 < 1 + arityWeight u (i + 1) by linarith)
    linarith
  · unfold arityWeight
    push_cast
    have hpi : (1 : ℝ) ≤ π ^ 2 := by nlinarith [pi_gt_three]
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have hu : 0 ≤ u ^ 2 := sq_nonneg u
    have key : 4 * (((i : ℝ) + 2) * ((i : ℝ) + 1)) ≤ π ^ 2 * (2 * ((i : ℝ) + 1) + 1) ^ 2 := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left key hu]

/-- Above the cutoff `J ≥ u` the weights are small: `a_j < 1/π² < 1/8` for every tail index
`j > J` of the paper, which is `arityWeight u j` with `j ≥ J` in the zero-based indexing here.
Paper: `lem:producttail` (`tanh_large_radius.tex`). -/
theorem tail_weight_small {u : ℝ} {J j : ℕ} (hu : 0 ≤ u) (hJ : u ≤ J) (hj : J ≤ j) :
    arityWeight u j < 1 / 8 := by
  unfold arityWeight
  have hpi : (9 : ℝ) < π ^ 2 := by nlinarith [pi_gt_three]
  have hjr : (J : ℝ) ≤ j := by exact_mod_cast hj
  have h2 : 2 * u < 2 * (j : ℝ) + 1 := by linarith
  have h3 : 4 * u ^ 2 < (2 * (j : ℝ) + 1) ^ 2 := by nlinarith
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- The mark law of `eq:producttailindex` is a probability distribution on `j ≥ J + 1`:
`Σ_{j ≥ J+1} J/(j(j-1)) = 1`, written with `j = J + 1 + i`. Paper: `lem:producttail`
(`tanh_large_radius.tex`). -/
theorem mark_law_total {J : ℕ} (hJ : 1 ≤ J) :
    HasSum (fun i : ℕ => (J : ℝ) / (((J : ℝ) + i + 1) * ((J : ℝ) + i))) 1 := by
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  set g : ℕ → ℝ := fun i => (J : ℝ) / ((J : ℝ) + i) with hg
  have htel : ∀ i : ℕ, (J : ℝ) / (((J : ℝ) + i + 1) * ((J : ℝ) + i)) = g i - g (i + 1) := by
    intro i
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    simp only [hg]
    push_cast
    field_simp
    ring
  have hnn : ∀ i : ℕ, 0 ≤ (J : ℝ) / (((J : ℝ) + i + 1) * ((J : ℝ) + i)) := fun i => by
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  simp_rw [htel, Finset.sum_range_sub']
  have hg0 : g 0 = 1 := by simp only [hg]; push_cast; rw [add_zero, div_self (by linarith)]
  rw [hg0]
  have hlim : Filter.Tendsto g Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun i : ℕ => (J : ℝ) + (i : ℝ)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
    exact Filter.Tendsto.div_atTop tendsto_const_nhds h2
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hlim

/-- The Poisson mean of the tail proposals: `Λ = Σ_{j > J} 2u²/(j(j-1)) = 2u²/J`.
Paper: `lem:producttail` (`tanh_large_radius.tex`). -/
theorem tail_poisson_mean {J : ℕ} (hJ : 1 ≤ J) (u : ℝ) :
    HasSum (fun i : ℕ => 2 * u ^ 2 / (((J : ℝ) + i + 1) * ((J : ℝ) + i))) (2 * u ^ 2 / J) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have h := (mark_law_total hJ).mul_left (2 * u ^ 2 / J)
  convert h using 1
  · funext i
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    field_simp
  · ring

/-- For `U > 0`, the mark `j = 1 + ⌊J/U⌋` equals `J + 1 + i` exactly when `U` lies in the
interval `(J/(J+i+1), J/(J+i)]`, a subinterval of `(0, 1]`.
Paper: `eq:producttailindex` in `lem:producttail` (`tanh_large_radius.tex`). -/
theorem mark_event_iff {J : ℕ} (hJ : 1 ≤ J) (i : ℕ) {U : ℝ} (hU : 0 < U) :
    1 + ⌊(J : ℝ) / U⌋₊ = J + 1 + i ↔
      U ∈ Set.Ioc ((J : ℝ) / ((J : ℝ) + i + 1)) ((J : ℝ) / ((J : ℝ) + i)) := by
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hx : 0 ≤ (J : ℝ) / U := by positivity
  have e : 1 + ⌊(J : ℝ) / U⌋₊ = J + 1 + i ↔ ⌊(J : ℝ) / U⌋₊ = J + i := by omega
  rw [e, Nat.floor_eq_iff hx, Set.mem_Ioc]
  push_cast
  rw [le_div_iff₀ hU, div_lt_iff₀ hU, div_lt_iff₀ (by positivity), le_div_iff₀ (by positivity)]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

/-- The mark interval `(J/(J+i+1), J/(J+i)]` has length equal to the mark probability
`J/((J+i+1)(J+i))`. Paper: `eq:producttailindex` in `lem:producttail`
(`tanh_large_radius.tex`). -/
theorem mark_interval_length {J : ℕ} (hJ : 1 ≤ J) (i : ℕ) :
    MeasureTheory.volume (Set.Ioc ((J : ℝ) / ((J : ℝ) + i + 1)) ((J : ℝ) / ((J : ℝ) + i))) =
      ENNReal.ofReal ((J : ℝ) / (((J : ℝ) + i + 1) * ((J : ℝ) + i))) := by
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  rw [Real.volume_Ioc]
  congr 1
  field_simp
  ring

/-! ### Finite-bit primitives -/

/-- The Poisson proposal of `lem:productaritybits`: for `0 ≤ λ ≤ 2`, the acceptance
probability `(e^{-λ} λ^k / k!) / (16 · 2^{-k-1})` is at most one. Paper:
`lem:productaritybits` (`tanh_large_radius.tex`). -/
theorem poisson_proposal_acceptance_le_one {lam : ℝ} (h0 : 0 ≤ lam) (h2 : lam ≤ 2) (k : ℕ) :
    exp (-lam) * lam ^ k / (k.factorial : ℝ) / (16 * (1 / 2) ^ (k + 1)) ≤ 1 := by
  have hterm : (2 * lam) ^ k / (k.factorial : ℝ) ≤ exp (2 * lam) := by
    have hs : HasSum (fun k : ℕ => (2 * lam) ^ k / (k.factorial : ℝ)) (exp (2 * lam)) := by
      rw [exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp (2 * lam)
    exact le_hasSum hs k (fun j _ => by positivity)
  have hF : (0 : ℝ) < k.factorial := by positivity
  have he : exp (-lam) * exp (2 * lam) = exp lam := by rw [← exp_add]; ring_nf
  have hel : exp lam ≤ exp 2 := exp_le_exp.mpr h2
  have he2 : exp 2 < 8 := by
    have h1 : exp 1 < 2.72 := lt_trans exp_one_lt_d9 (by norm_num)
    have : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
    rw [this]
    nlinarith [exp_pos 1]
  have hrw : exp (-lam) * lam ^ k / (k.factorial : ℝ) / (16 * (1 / 2) ^ (k + 1)) =
      exp (-lam) * ((2 * lam) ^ k / (k.factorial : ℝ)) / 8 := by
    rw [one_div, inv_pow, mul_pow, pow_succ]
    field_simp
    ring
  rw [hrw, div_le_one (by norm_num)]
  calc exp (-lam) * ((2 * lam) ^ k / (k.factorial : ℝ)) ≤ exp (-lam) * exp (2 * lam) :=
        mul_le_mul_of_nonneg_left hterm (exp_pos _).le
    _ = exp lam := he
    _ ≤ 8 := by linarith

/-- Each trial of the Poisson proposal succeeds with probability `1/16`, and the accepted count
is Poisson: the product of proposal and acceptance is `e^{-λ} λ^k / (16 k!)`.
Paper: `lem:productaritybits` (`tanh_large_radius.tex`). -/
theorem poisson_proposal_success (lam : ℝ) :
    HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1) *
      (exp (-lam) * lam ^ k / (k.factorial : ℝ) / (16 * (1 / 2) ^ (k + 1)))) (1 / 16) := by
  have hs : HasSum (fun k : ℕ => lam ^ k / (k.factorial : ℝ)) (exp lam) := by
    rw [exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp lam
  have h := hs.mul_left (exp (-lam) / 16)
  convert h using 1
  · funext k
    have : (0 : ℝ) < (1 / 2) ^ (k + 1) := by positivity
    field_simp
  · rw [show exp (-lam) / 16 * exp lam = exp (-lam) * exp lam / 16 by ring, ← exp_add]
    simp

/-- The refinement tail of a geometric inversion:
`Σ_{k ≥ 1} (e^{-d(k-ε)} - e^{-d(k+ε)}) = 2 sinh(dε)/(e^d - 1)`. For `0 < ε ≤ 1/2` (the paper's
range) the windows `[k - ε, k + ε]` are disjoint and this sum is the probability that an
exponential variable of rate `d` lies within `ε` of a positive integer; that probabilistic
identification is not formalized, and the identity holds for every `ε`.
Paper: `lem:productaritybits` (`tanh_large_radius.tex`). -/
theorem geometric_refinement_tail {d : ℝ} (hd : 0 < d) (ε : ℝ) :
    HasSum (fun k : ℕ => exp (-(d * ((k : ℝ) + 1 - ε))) - exp (-(d * ((k : ℝ) + 1 + ε))))
      (2 * sinh (d * ε) / (exp d - 1)) := by
  have hr0 : 0 ≤ exp (-d) := (exp_pos _).le
  have hr1 : exp (-d) < 1 := exp_lt_one_iff.mpr (by linarith)
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left
    ((exp (d * ε) - exp (-(d * ε))) * exp (-d))
  have hed : 1 < exp d := one_lt_exp_iff.mpr hd
  convert hg using 1
  · funext k
    rw [← exp_nat_mul]
    have e1 : exp (-(d * ((k : ℝ) + 1 - ε))) = exp (d * ε) * exp (-d) * exp ((k : ℝ) * -d) := by
      rw [← exp_add, ← exp_add]; ring_nf
    have e2 : exp (-(d * ((k : ℝ) + 1 + ε))) =
        exp (-(d * ε)) * exp (-d) * exp ((k : ℝ) * -d) := by
      rw [← exp_add, ← exp_add]; ring_nf
    rw [e1, e2]
    ring
  · rw [sinh_eq, exp_neg d]
    have hpos : 0 < exp d := exp_pos d
    field_simp

/-- The refinement tail is at most `6ε` when `d ε ≤ 1`, uniformly in the rate. The paper states
it for `0 < ε ≤ 1/2`; the bound holds for every `ε ≥ 0` with `d ε ≤ 1`.
Paper: `lem:productaritybits` (`tanh_large_radius.tex`). -/
theorem geometric_refinement_tail_le {d ε : ℝ} (hd : 0 < d) (hε : 0 ≤ ε) (hdε : d * ε ≤ 1) :
    2 * sinh (d * ε) / (exp d - 1) ≤ 6 * ε := by
  set x := d * ε with hx
  have hx0 : 0 ≤ x := mul_nonneg hd.le hε
  -- `sinh x = tanh x cosh x ≤ x cosh 1 ≤ 3x`
  have hsinh : sinh x ≤ 3 * x := by
    have ht : tanh x ≤ x := by
      have h := tanh_lt_one x
      rcases eq_or_lt_of_le hx0 with h0 | h0
      · rw [← h0]; simp
      obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope tanh (fun y => 1 / cosh y ^ 2) h0
        (by
          have e : tanh = fun y => sinh y / cosh y := funext tanh_eq_sinh_div_cosh
          rw [e]
          exact (continuous_sinh.div continuous_cosh (fun y => (cosh_pos y).ne')).continuousOn)
        (fun y _ => by
          have hh := (hasDerivAt_sinh y).div (hasDerivAt_cosh y) (cosh_pos y).ne'
          have e : (sinh / cosh : ℝ → ℝ) = tanh := by
            funext z; rw [Pi.div_apply, tanh_eq_sinh_div_cosh]
          rw [e] at hh
          refine hh.congr_deriv ?_
          have := cosh_sq_sub_sinh_sq y
          have hc := cosh_pos y
          field_simp
          linarith)
      have hc1 : 1 / cosh c ^ 2 ≤ 1 := by
        rw [div_le_one (by have := cosh_pos c; positivity)]
        nlinarith [one_le_cosh c]
      rw [hc, tanh_zero, sub_zero, sub_zero, div_le_one h0] at hc1
      exact hc1
    have hc : cosh x ≤ 3 := by
      have h1 : cosh x ≤ cosh 1 := by
        rw [cosh_le_cosh, abs_of_nonneg hx0, abs_one]; exact hdε
      have h2 : cosh 1 < 3 := by
        rw [cosh_eq]
        have he : exp 1 < 3 := lt_trans exp_one_lt_d9 (by norm_num)
        have hi : exp (-1) ≤ 1 := exp_le_one_iff.mpr (by norm_num)
        linarith
      linarith
    have htc : sinh x = tanh x * cosh x := by
      rw [tanh_eq_sinh_div_cosh]; field_simp [(cosh_pos x).ne']
    rw [htc]
    have h0 : 0 ≤ tanh x := by
      rw [tanh_eq_sinh_div_cosh]; exact div_nonneg (sinh_nonneg_iff.mpr hx0) (cosh_pos x).le
    calc tanh x * cosh x ≤ x * 3 := mul_le_mul ht hc (cosh_pos x).le hx0
      _ = 3 * x := by ring
  have hed : d ≤ exp d - 1 := by linarith [add_one_le_exp d]
  have hs0 : 0 ≤ sinh x := sinh_nonneg_iff.mpr hx0
  rw [div_le_iff₀ (by linarith)]
  calc 2 * sinh x ≤ 2 * (3 * x) := by linarith
    _ = 6 * ε * d := by rw [hx]; ring
    _ ≤ 6 * ε * (exp d - 1) := mul_le_mul_of_nonneg_left hed (by positivity)

end ExactSampling.ProductArity
