import Mathlib

/-!
# Finite-mean score obstruction and critical tanh derivatives

This module formalizes parts of `tanh_new_critical.tex`
(`sec:new-finite-score`, `lem:new-finite-score`, `cor:new-integer-score`,
`prop:new-local-obstruction`, `sec:new-critical-smoothness`,
`prop:new-critical-derivatives`) and the stopped-score inequality
`1 + ρ^2 + O(ρ^4)` quoted in `sec:conf-open` of `conference.tex`.

Formalized:
* the integer inequality `(2k+1)|v| ≤ v^2 + k(k+1)`, the strongest line of
  that family, and finite weighted versions;
* a finite-horizon model of an adaptive experiment on fair or biased signs,
  with the likelihood-ratio identity, the score identity `f'(0) = E_0[Y S]`,
  the stopped isometry `E_0 S^2 = E_0 T`, and the resulting integer
  obstruction, with no hypothesis beyond boundedness of the output;
* the integer obstruction for a general probability space, where the score
  identity and the isometry of `lem:new-finite-score` are hypotheses;
* calculus facts: the derivative of `tanh`, its iterated derivatives through
  order four and their bounds, `G_r'(0) = r coth r`, the series bounds
  `x coth x ≤ 1 + x^2/3` and `coth^2 x ≥ x^{-2} + 2/3`, and the two-sided
  estimate `1 + ρ^2 - ρ^4/6 ≤ 3ρ coth ρ - 2 ≤ 1 + ρ^2` for `0 < ρ ≤ 1`;
* the radius bound `R_j^2 ≤ 3/(2j+3)` for `R_j = tanh^[j] 1` and the complete
  arithmetic of `prop:new-local-obstruction`, with the local bounds
  `E T_j ≥ 3 a_j - 2` derived from the score identity and isometry of each local
  factory (`local_obstruction_from_scores`);
* the derivative-mass recursion of `prop:new-critical-derivatives`, giving
  `2√6 √D`, `38 D` and `624 D^{3/2}`;
* `eq:main-radius` (exact_sampling_networks.tex), `1/(ℓ+1) ≤ r_ℓ^2 ≤ 3/(2ℓ+3)`,
  and the argument after it giving `r_ℓ^2 ∼ 3/(2ℓ)`, with the explicit
  remainder `|r_ℓ^2 (2ℓ/3) - 1| ≤ 2/√ℓ`.

Not formalized:
* the passage from a finite horizon to an almost surely terminating rule with
  finite mean (the relative-entropy, Pinsker and `L^2` limit argument of
  `lem:new-finite-score`); in the measure-theoretic statement the score
  identity and the isometry are explicit hypotheses;
* the predictable charging of fresh recursive calls in
  `prop:new-local-obstruction`; the bottom request bound `N ≥ R_D ∏ E T_j` is a
  hypothesis, as are the per-layer score identities and isometries;
* the multivariate chain rule for derivative tensors of the network; the
  per-layer recurrences of `prop:new-critical-derivatives` are hypotheses
  of `derivative_mass_bounds`.
-/

open Real Finset Filter

namespace ExactSampling.NewCriticalLemmas

/-! ## Integer algebra -/

/-- Paper: `cor:new-integer-score` (tanh_new_critical.tex), proof: consecutive
integers give `(|v| - k)(|v| - k - 1) ≥ 0`. -/
theorem consecutive_integer_product (v k : ℤ) : 0 ≤ (v - k) * (v - k - 1) := by
  have h : v ≤ k ∨ k + 1 ≤ v := by omega
  rcases h with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  · exact mul_nonneg (by omega) (by omega)

/-- Paper: `cor:new-integer-score` (tanh_new_critical.tex), proof:
`(2k+1)|v| ≤ v^2 + k(k+1)` for every integer `v`. -/
theorem integer_abs_quadratic (v k : ℤ) : (2 * k + 1) * |v| ≤ v ^ 2 + k * (k + 1) := by
  have h := consecutive_integer_product (|v|) k
  have hs : |v| ^ 2 = v ^ 2 := sq_abs v
  nlinarith

/-- Paper: `cor:new-integer-score` (tanh_new_critical.tex), the case `k = 1`. -/
theorem integer_abs_three (v : ℤ) : 3 * |v| ≤ v ^ 2 + 2 := by
  simpa using integer_abs_quadratic v 1

/-- Real form of `integer_abs_quadratic` for a natural number `k`. Auxiliary for
`cor:new-integer-score`
(tanh_new_critical.tex). -/
theorem integer_abs_quadratic_real (v : ℤ) (k : ℕ) :
    (2 * (k : ℝ) + 1) * |(v : ℝ)| ≤ (v : ℝ) ^ 2 + k * ((k : ℝ) + 1) := by
  have h := integer_abs_quadratic v k
  have h' : ((2 * (k : ℤ) + 1) * |v| : ℤ) ≤ ((v ^ 2 + (k : ℤ) * ((k : ℤ) + 1)) : ℤ) := h
  exact_mod_cast h'

/-- An integer is bounded in absolute value by its square. Auxiliary for `cor:new-integer-score`
(tanh_new_critical.tex). -/
theorem abs_le_sq_int (v : ℤ) : |(v : ℝ)| ≤ (v : ℝ) ^ 2 := by
  have h : |v| ≤ v ^ 2 := by
    rcases eq_or_ne v 0 with h0 | h0
    · simp [h0]
    · have h1 : 1 ≤ |v| := Int.one_le_abs h0
      calc |v| = |v| * 1 := by ring
        _ ≤ |v| * |v| := mul_le_mul_of_nonneg_left h1 (abs_nonneg v)
        _ = v ^ 2 := by rw [← sq, sq_abs]
  exact_mod_cast h

/-- Paper: discussion after `cor:new-integer-score` (tanh_new_critical.tex): for
`a = |f'(0)|` and `k = ⌊a⌋`, the strongest line is
`(2k+1)a - k(k+1) = a^2 + (a-k)(k+1-a) ∈ [a^2, a^2 + 1/4]`. -/
theorem strongest_line {a : ℝ} (ha : 0 ≤ a) :
    (2 * (⌊a⌋₊ : ℝ) + 1) * a - ⌊a⌋₊ * ((⌊a⌋₊ : ℝ) + 1) =
        a ^ 2 + (a - ⌊a⌋₊) * ((⌊a⌋₊ : ℝ) + 1 - a) ∧
      a ^ 2 ≤ (2 * (⌊a⌋₊ : ℝ) + 1) * a - ⌊a⌋₊ * ((⌊a⌋₊ : ℝ) + 1) ∧
      (2 * (⌊a⌋₊ : ℝ) + 1) * a - ⌊a⌋₊ * ((⌊a⌋₊ : ℝ) + 1) ≤ a ^ 2 + 1 / 4 := by
  have h1 : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha
  have h2 : a < (⌊a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one a
  refine ⟨by ring, ?_, ?_⟩
  · nlinarith
  · nlinarith [sq_nonneg (a - ⌊a⌋₊ - 1 / 2)]

/-- Paper: discussion after `cor:new-integer-score` (tanh_new_critical.tex): the
small amplification `a = 1 + u` costs at least `1 + 3u` on the line `k = 1`. -/
theorem small_amplification (u : ℝ) : (2 * 1 + 1) * (1 + u) - 1 * (1 + 1) = 1 + 3 * u := by
  ring

/-- Paper: `cor:new-integer-score` (tanh_new_critical.tex), finite weighted form
of the score obstruction for bounded real outputs `y` and integer scores `v`. -/
theorem finite_weighted_integer_score {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (v : ι → ℤ) (y : ι → ℝ) (k : ℕ)
    (hw : ∀ i, 0 ≤ w i) (hy : ∀ i, |y i| ≤ 1) (hsum : ∑ i, w i = 1) :
    (2 * (k : ℝ) + 1) * |∑ i, w i * y i * (v i : ℝ)| ≤
      (∑ i, w i * (v i : ℝ) ^ 2) + k * ((k : ℝ) + 1) := by
  have hk : (0 : ℝ) ≤ 2 * k + 1 := by positivity
  calc (2 * (k : ℝ) + 1) * |∑ i, w i * y i * (v i : ℝ)|
      ≤ (2 * (k : ℝ) + 1) * ∑ i, |w i * y i * (v i : ℝ)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hk
    _ ≤ ∑ i, w i * ((2 * (k : ℝ) + 1) * |(v i : ℝ)|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_mul, abs_of_nonneg (hw i)]
      have hm := mul_le_mul_of_nonneg_left (hy i) (hw i)
      have hm' := mul_le_mul_of_nonneg_right hm (abs_nonneg (v i : ℝ))
      nlinarith
    _ ≤ ∑ i, w i * ((v i : ℝ) ^ 2 + k * ((k : ℝ) + 1)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (integer_abs_quadratic_real (v i) k) (hw i)
    _ = (∑ i, w i * (v i : ℝ) ^ 2) + k * ((k : ℝ) + 1) := by
      set c : ℝ := k * ((k : ℝ) + 1)
      have e : ∑ i, w i * ((v i : ℝ) ^ 2 + c) = ∑ i, w i * (v i : ℝ) ^ 2 + (∑ i, w i) * c := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [e, hsum, one_mul]

/-- Paper: `cor:new-integer-score` (tanh_new_critical.tex), the slope-three
case `k = 1` of `finite_weighted_integer_score`. -/
theorem finite_weighted_integer_score_three {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (v : ι → ℤ) (y : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hy : ∀ i, |y i| ≤ 1) (hsum : ∑ i, w i = 1) :
    3 * |∑ i, w i * y i * (v i : ℝ)| ≤ (∑ i, w i * (v i : ℝ) ^ 2) + 2 := by
  have h := finite_weighted_integer_score w v y 1 hw hy hsum
  norm_num at h
  linarith

/-! ## A finite-horizon stopped sign experiment

A history is the list of signs received so far, the most recent first. At a
history `h` the experiment halts if `stop h` holds; otherwise it requests a new
sign, equal to `1` with probability `(1+z)/2` and to `-1` with probability
`(1-z)/2`. After `n` further requests it halts in any case. The number of
requests is the length of the terminal history and the stopped score is its
sum. `stoppedExpect stop z w n h` is the expectation of `w` at the terminal
history. Auxiliary randomness is a finite mixture of such rules; see
`mixture_integer_obstruction`. -/

/-- Expected terminal payoff of a finite-horizon stopped experiment on signs
of mean `z`. Auxiliary for
`lem:new-finite-score` (tanh_new_critical.tex). -/
noncomputable def stoppedExpect (stop : List ℤ → Prop) [DecidablePred stop] (z : ℝ)
    (w : List ℤ → ℝ) : ℕ → List ℤ → ℝ
  | 0, h => w h
  | n + 1, h => if stop h then w h else
      (1 + z) / 2 * stoppedExpect stop z w n (1 :: h) +
        (1 - z) / 2 * stoppedExpect stop z w n ((-1) :: h)

/-- Likelihood of a history under signs of mean `z` relative to fair signs. Auxiliary for
`lem:new-finite-score` (tanh_new_critical.tex). -/
noncomputable def likelihood (z : ℝ) (h : List ℤ) : ℝ :=
  (h.map (fun x : ℤ => 1 + z * (x : ℝ))).prod

variable (stop : List ℤ → Prop) [DecidablePred stop]

/-- Linearity of the stopped expectation (sums). Auxiliary for
`lem:new-finite-score` (tanh_new_critical.tex). -/
theorem stoppedExpect_add (z : ℝ) (w₁ w₂ : List ℤ → ℝ) (n : ℕ) (h : List ℤ) :
    stoppedExpect stop z (fun g => w₁ g + w₂ g) n h =
      stoppedExpect stop z w₁ n h + stoppedExpect stop z w₂ n h := by
  induction n generalizing h with
  | zero => simp [stoppedExpect]
  | succ n ih =>
    simp only [stoppedExpect]
    split_ifs
    · rfl
    · rw [ih, ih]; ring

/-- Linearity of the stopped expectation (scalars). Auxiliary for
`lem:new-finite-score` (tanh_new_critical.tex). -/
theorem stoppedExpect_const_mul (z c : ℝ) (w : List ℤ → ℝ) (n : ℕ) (h : List ℤ) :
    stoppedExpect stop z (fun g => c * w g) n h = c * stoppedExpect stop z w n h := by
  induction n generalizing h with
  | zero => simp [stoppedExpect]
  | succ n ih =>
    simp only [stoppedExpect]
    split_ifs
    · rfl
    · rw [ih, ih]; ring

/-- The stopped expectation of a constant. Auxiliary for
`lem:new-finite-score` (tanh_new_critical.tex). -/
theorem stoppedExpect_const (z c : ℝ) (n : ℕ) (h : List ℤ) :
    stoppedExpect stop z (fun _ => c) n h = c := by
  induction n generalizing h with
  | zero => simp [stoppedExpect]
  | succ n ih =>
    simp only [stoppedExpect]
    split_ifs
    · rfl
    · rw [ih, ih]; ring

/-- Monotonicity of the stopped expectation for a legal mean `|z| ≤ 1`. Auxiliary for
`lem:new-finite-score` (tanh_new_critical.tex). -/
theorem stoppedExpect_mono {z : ℝ} (hz : |z| ≤ 1) {w₁ w₂ : List ℤ → ℝ}
    (hw : ∀ g, w₁ g ≤ w₂ g) (n : ℕ) (h : List ℤ) :
    stoppedExpect stop z w₁ n h ≤ stoppedExpect stop z w₂ n h := by
  have hp : 0 ≤ (1 + z) / 2 := by linarith [neg_abs_le z]
  have hm : 0 ≤ (1 - z) / 2 := by linarith [le_abs_self z]
  induction n generalizing h with
  | zero => simpa [stoppedExpect] using hw h
  | succ n ih =>
    simp only [stoppedExpect]
    split_ifs
    · exact hw h
    · exact add_le_add (mul_le_mul_of_nonneg_left (ih _) hp)
        (mul_le_mul_of_nonneg_left (ih _) hm)

/-- Paper: `lem:new-finite-score` (tanh_new_critical.tex), proof: at a finite
horizon the mean is differentiable and `f_N'(0) = E_0[g_N S_{T ∧ N}]`. Here the
score is measured from the starting history `h`. -/
theorem score_identity (w : List ℤ → ℝ) (n : ℕ) (h : List ℤ) :
    HasDerivAt (fun z => stoppedExpect stop z w n h)
      (stoppedExpect stop 0 (fun g => w g * ((g.sum : ℝ) - h.sum)) n h) 0 := by
  induction n generalizing h with
  | zero =>
    simp only [stoppedExpect, sub_self, mul_zero]
    exact hasDerivAt_const _ _
  | succ n ih =>
    simp only [stoppedExpect]
    split_ifs with hs
    · simp only [sub_self, mul_zero]
      exact hasDerivAt_const _ _
    · have h1 := ih (1 :: h)
      have h2 := ih ((-1) :: h)
      have hp : HasDerivAt (fun z : ℝ => (1 + z) / 2) (1 / 2) 0 := by
        have := ((hasDerivAt_id (0:ℝ)).const_add 1).div_const 2
        simpa using this
      have hm : HasDerivAt (fun z : ℝ => (1 - z) / 2) (-(1 / 2)) 0 := by
        have := ((hasDerivAt_id (0:ℝ)).const_sub 1).div_const 2
        simpa [neg_div] using this
      have hd := (hp.mul h1).add (hm.mul h2)
      convert hd using 1
      -- rewrite the target derivative
      have e1 : stoppedExpect stop 0 (fun g => w g * ((g.sum : ℝ) - h.sum)) n (1 :: h) =
          stoppedExpect stop 0 (fun g => w g * ((g.sum : ℝ) - (List.sum (1 :: h) : ℤ))) n (1 :: h)
            + stoppedExpect stop 0 w n (1 :: h) := by
        rw [← stoppedExpect_add]
        congr 1; funext g; push_cast [List.sum_cons]; ring
      have e2' : stoppedExpect stop 0 (fun g => w g * ((g.sum : ℝ) - h.sum)) n ((-1) :: h) +
          stoppedExpect stop 0 w n ((-1) :: h) =
          stoppedExpect stop 0 (fun g => w g * ((g.sum : ℝ) - (List.sum ((-1) :: h) : ℤ))) n
            ((-1) :: h) := by
        rw [← stoppedExpect_add]
        congr 1; funext g; push_cast [List.sum_cons]; ring
      have e2 := eq_sub_of_add_eq e2'
      rw [e1, e2]
      simp only [add_zero, sub_zero]
      ring

/-- Paper: `lem:new-finite-score` (tanh_new_critical.tex), proof: the fair-sign
martingale isometry `E_0 S_{T∧N}^2 = E_0 (T ∧ N)`, relative to a starting
history `h`. -/
theorem isometry (n : ℕ) (h : List ℤ) :
    stoppedExpect stop 0 (fun g => ((g.sum : ℝ)) ^ 2 - g.length) n h =
      (h.sum : ℝ) ^ 2 - h.length := by
  induction n generalizing h with
  | zero => simp [stoppedExpect]
  | succ n ih =>
    simp only [stoppedExpect]
    split_ifs
    · rfl
    · rw [ih, ih]
      simp only [List.sum_cons, List.length_cons]
      push_cast
      ring


/-- Paper: `lem:new-finite-score` (tanh_new_critical.tex), proof: the
finite-prefix likelihood ratio `L_{z,N} = ∏ (1 + z X_j)` converts the mean-`z`
law into the fair-sign law. -/
theorem likelihood_identity (z : ℝ) (w : List ℤ → ℝ) (n : ℕ) (h : List ℤ) :
    stoppedExpect stop z w n h * likelihood z h =
      stoppedExpect stop 0 (fun g => w g * likelihood z g) n h := by
  induction n generalizing h with
  | zero => simp [stoppedExpect]
  | succ n ih =>
    simp only [stoppedExpect]
    split_ifs
    · rfl
    · rw [← ih, ← ih]
      simp only [likelihood, List.map_cons, List.prod_cons]
      push_cast
      ring

/-- Paper: `lem:new-finite-score` (tanh_new_critical.tex), proof: for signs
`X_j ∈ {-1, 1}` and `|z| ≤ 1`, `L_{z,N} ≤ (1 + |z|)^N`. -/
theorem likelihood_le {z : ℝ} (hz : |z| ≤ 1) (h : List ℤ) (hh : ∀ x ∈ h, |x| ≤ 1) :
    0 ≤ likelihood z h ∧ likelihood z h ≤ (1 + |z|) ^ h.length := by
  induction h with
  | nil => simp [likelihood]
  | cons x t ih =>
    have hx : |(x : ℝ)| ≤ 1 := by exact_mod_cast hh x (by simp)
    obtain ⟨ih0, ih1⟩ := ih (fun y hy => hh y (by simp [hy]))
    have hzx : |z * x| ≤ |z| := by
      rw [abs_mul]; nlinarith [abs_nonneg z, abs_nonneg (x : ℝ)]
    have hlo : 0 ≤ 1 + z * x := by linarith [neg_abs_le (z * x)]
    have hhi : 1 + z * x ≤ 1 + |z| := by linarith [le_abs_self (z * x)]
    simp only [likelihood, List.map_cons, List.prod_cons, List.length_cons] at *
    refine ⟨mul_nonneg hlo ih0, ?_⟩
    rw [pow_succ, mul_comm ((1 + |z|) ^ t.length)]
    exact mul_le_mul hhi ih1 ih0 (by linarith [abs_nonneg z])

/-- Paper: `cor:new-integer-score` (tanh_new_critical.tex), for every stopping
rule with a finite horizon `N` and every output `Y ∈ [-1, 1]`:
`E_0 T ≥ (2k+1)|f'(0)| - k(k+1)`, where `f(z) = E_z Y`. No further hypothesis
is needed at a finite horizon. -/
theorem finite_integer_obstruction (out : List ℤ → ℝ) (hout : ∀ g, |out g| ≤ 1)
    (N k : ℕ) {f' : ℝ} (hf : HasDerivAt (fun z => stoppedExpect stop z out N []) f' 0) :
    (2 * (k : ℝ) + 1) * |f'| - k * ((k : ℝ) + 1) ≤
      stoppedExpect stop 0 (fun g => (g.length : ℝ)) N [] := by
  have hs := score_identity stop out N []
  have hf' : f' = stoppedExpect stop 0 (fun g => out g * (g.sum : ℝ)) N [] := by
    have := hf.unique hs
    rw [this]; simp
  have h0 : |(0 : ℝ)| ≤ 1 := by simp
  have hup : stoppedExpect stop 0 (fun g => out g * (g.sum : ℝ)) N [] ≤
      stoppedExpect stop 0 (fun g => |((g.sum : ℤ) : ℝ)|) N [] := by
    apply stoppedExpect_mono stop h0
    intro g
    have := hout g
    calc out g * (g.sum : ℝ) ≤ |out g * (g.sum : ℝ)| := le_abs_self _
      _ = |out g| * |(g.sum : ℝ)| := abs_mul _ _
      _ ≤ 1 * |(g.sum : ℝ)| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
      _ = _ := one_mul _
  have hlo : -stoppedExpect stop 0 (fun g => |((g.sum : ℤ) : ℝ)|) N [] ≤
      stoppedExpect stop 0 (fun g => out g * (g.sum : ℝ)) N [] := by
    rw [neg_eq_neg_one_mul, ← stoppedExpect_const_mul]
    apply stoppedExpect_mono stop h0
    intro g
    have := hout g
    have h2 : |out g * (g.sum : ℝ)| ≤ |(g.sum : ℝ)| := by
      rw [abs_mul]; nlinarith [abs_nonneg (g.sum : ℝ)]
    linarith [neg_abs_le (out g * (g.sum : ℝ))]
  have habs : |f'| ≤ stoppedExpect stop 0 (fun g => |((g.sum : ℤ) : ℝ)|) N [] := by
    rw [hf', abs_le]; exact ⟨hlo, hup⟩
  have hquad : stoppedExpect stop 0 (fun g => (2 * (k : ℝ) + 1) * |((g.sum : ℤ) : ℝ)|) N [] ≤
      stoppedExpect stop 0 (fun g => (((g.sum : ℤ) : ℝ) ^ 2 - g.length) +
        ((g.length : ℝ) + k * ((k : ℝ) + 1))) N [] := by
    apply stoppedExpect_mono stop h0
    intro g
    have := integer_abs_quadratic_real g.sum k
    linarith
  rw [stoppedExpect_const_mul, stoppedExpect_add, isometry, stoppedExpect_add,
    stoppedExpect_const] at hquad
  simp only [List.sum_nil, Int.cast_zero, List.length_nil, Nat.cast_zero] at hquad
  have hk : (0 : ℝ) ≤ 2 * k + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left habs hk]

/-- Paper: `lem:new-finite-score` (tanh_new_critical.tex): an auxiliary tape
whose law does not depend on `z` mixes the local bounds. If each deterministic
rule satisfies the integer bound, so does every finite mixture. -/
theorem mixture_integer_obstruction {ι : Type*} (s : Finset ι) (p T f : ι → ℝ) (k : ℕ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∑ i ∈ s, p i = 1)
    (hT : ∀ i ∈ s, (2 * (k : ℝ) + 1) * |f i| - k * ((k : ℝ) + 1) ≤ T i) :
    (2 * (k : ℝ) + 1) * |∑ i ∈ s, p i * f i| - k * ((k : ℝ) + 1) ≤ ∑ i ∈ s, p i * T i := by
  have hk : (0 : ℝ) ≤ 2 * k + 1 := by positivity
  have h1 : |∑ i ∈ s, p i * f i| ≤ ∑ i ∈ s, p i * |f i| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [abs_mul, abs_of_nonneg (hp i hi)]
  have h2 : ∑ i ∈ s, p i * ((2 * (k : ℝ) + 1) * |f i| - k * ((k : ℝ) + 1)) ≤
      ∑ i ∈ s, p i * T i :=
    Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hT i hi) (hp i hi))
  have h3 : ∑ i ∈ s, p i * ((2 * (k : ℝ) + 1) * |f i| - k * ((k : ℝ) + 1)) =
      (2 * (k : ℝ) + 1) * ∑ i ∈ s, p i * |f i| - k * ((k : ℝ) + 1) := by
    set a : ℝ := 2 * (k : ℝ) + 1
    set c : ℝ := k * ((k : ℝ) + 1)
    have e : ∀ i, p i * (a * |f i| - c) = a * (p i * |f i|) - c * p i := fun i => by ring
    simp_rw [e, Finset.sum_sub_distrib, ← Finset.mul_sum, hp1, mul_one]
  nlinarith [mul_le_mul_of_nonneg_left h1 hk]

/-! ## The obstruction on a general probability space -/

/-- Paper: `cor:new-integer-score` (tanh_new_critical.tex). On a probability
space, let `Y ∈ [-1,1]` be the output, `S` the integer stopped score and `T`
the number of source requests. The two hypotheses `hscore` (the score identity
`f'(0) = E_0[Y S_T]`) and `hiso` (the isometry `E_0 S_T^2 = E_0 T`) are the
conclusions of `lem:new-finite-score`, taken here as stand-ins; the finite
horizon case is proved in `finite_integer_obstruction`. -/
theorem integer_score_bound {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (Y : Ω → ℝ) (S : Ω → ℤ) (T : Ω → ℝ) (fd : ℝ)
    (k : ℕ) (hY : ∀ ω, |Y ω| ≤ 1) (hYm : MeasureTheory.AEStronglyMeasurable Y μ)
    (hSm : MeasureTheory.AEStronglyMeasurable (fun ω => (S ω : ℝ)) μ)
    (hS2 : MeasureTheory.Integrable (fun ω => (S ω : ℝ) ^ 2) μ)
    (hscore : fd = ∫ ω, Y ω * S ω ∂μ)
    (hiso : ∫ ω, T ω ∂μ = ∫ ω, (S ω : ℝ) ^ 2 ∂μ) :
    (2 * (k : ℝ) + 1) * |fd| - k * ((k : ℝ) + 1) ≤ ∫ ω, T ω ∂μ := by
  have hSint : MeasureTheory.Integrable (fun ω => (S ω : ℝ)) μ := by
    refine hS2.mono' hSm (MeasureTheory.ae_of_all _ (fun ω => ?_))
    rw [Real.norm_eq_abs]; exact abs_le_sq_int (S ω)
  have hYS : MeasureTheory.Integrable (fun ω => Y ω * S ω) μ := by
    refine hSint.abs.mono' (hYm.mul hSm) (MeasureTheory.ae_of_all _ (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [hY ω, abs_nonneg (S ω : ℝ)]
  have h1 : |fd| ≤ ∫ ω, |(S ω : ℝ)| ∂μ := by
    rw [hscore]
    refine (MeasureTheory.abs_integral_le_integral_abs).trans ?_
    refine MeasureTheory.integral_mono hYS.abs hSint.abs (fun ω => ?_)
    simp only [abs_mul]
    nlinarith [hY ω, abs_nonneg (S ω : ℝ), abs_nonneg (Y ω)]
  have h2 : ∫ ω, (2 * (k : ℝ) + 1) * |(S ω : ℝ)| ∂μ ≤
      ∫ ω, ((S ω : ℝ) ^ 2 + k * ((k : ℝ) + 1)) ∂μ :=
    MeasureTheory.integral_mono (hSint.abs.const_mul _)
      (hS2.add (MeasureTheory.integrable_const _))
      (fun ω => integer_abs_quadratic_real (S ω) k)
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add hS2 (MeasureTheory.integrable_const _),
    MeasureTheory.integral_const] at h2
  simp only [MeasureTheory.probReal_univ, smul_eq_mul, one_mul] at h2
  have hk : (0 : ℝ) ≤ 2 * k + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 hk]

/-! ## Calculus of tanh -/

/-- `tanh' = 1 - tanh^2`. Auxiliary for
`prop:new-critical-derivatives` (tanh_new_critical.tex). -/
theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  have heq : Real.tanh = Real.sinh / Real.cosh := by
    funext y; simp [Real.tanh_eq_sinh_div_cosh]
  rw [heq]
  convert h using 1
  simp only [Pi.div_apply]
  field_simp

/-- The derivative of `tanh` as a function. Auxiliary for
`prop:new-critical-derivatives` (tanh_new_critical.tex). -/
theorem deriv_tanh_eq : deriv Real.tanh = fun u => 1 - Real.tanh u ^ 2 :=
  funext fun u => (hasDerivAt_tanh u).deriv

/-- Paper: `prop:new-critical-derivatives` (tanh_new_critical.tex), proof:
`tanh'' = -2t + 2t^3` with `t = tanh u`. -/
theorem iteratedDeriv_two_tanh :
    iteratedDeriv 2 Real.tanh = fun u => -2 * Real.tanh u + 2 * Real.tanh u ^ 3 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_tanh_eq]
  funext u
  have h : HasDerivAt (fun x => 1 - Real.tanh x ^ 2) _ u :=
    ((hasDerivAt_tanh u).pow 2).const_sub 1
  rw [h.deriv]; push_cast; ring

/-- Paper: `prop:new-critical-derivatives` (tanh_new_critical.tex), proof:
`tanh''' = -2 + 8t^2 - 6t^4`. -/
theorem iteratedDeriv_three_tanh :
    iteratedDeriv 3 Real.tanh =
      fun u => -2 + 8 * Real.tanh u ^ 2 - 6 * Real.tanh u ^ 4 := by
  rw [iteratedDeriv_succ, iteratedDeriv_two_tanh]
  funext u
  have h : HasDerivAt (fun x => -2 * Real.tanh x + 2 * Real.tanh x ^ 3) _ u :=
    ((hasDerivAt_tanh u).const_mul (-2)).add (((hasDerivAt_tanh u).pow 3).const_mul 2)
  rw [h.deriv]; push_cast; ring

/-- Paper: `prop:new-critical-derivatives` (tanh_new_critical.tex), proof:
`tanh'''' = t(16 - 40t^2 + 24t^4)`. -/
theorem iteratedDeriv_four_tanh :
    iteratedDeriv 4 Real.tanh =
      fun u => 16 * Real.tanh u - 40 * Real.tanh u ^ 3 + 24 * Real.tanh u ^ 5 := by
  rw [iteratedDeriv_succ, iteratedDeriv_three_tanh]
  funext u
  have h : HasDerivAt (fun x => -2 + 8 * Real.tanh x ^ 2 - 6 * Real.tanh x ^ 4) _ u :=
    (((hasDerivAt_tanh u).pow 2).const_mul 8).const_add (-2) |>.sub
      (((hasDerivAt_tanh u).pow 4).const_mul 6)
  rw [h.deriv]; push_cast; ring

/-- Paper: `prop:new-critical-derivatives` (tanh_new_critical.tex), proof:
`|tanh'| ≤ 1`, `|tanh''| ≤ 2|t|`, `|tanh'''| ≤ 2`, `|tanh''''| ≤ 16|t|`. -/
theorem tanh_derivative_bounds (u : ℝ) :
    |deriv Real.tanh u| ≤ 1 ∧
    |iteratedDeriv 2 Real.tanh u| ≤ 2 * |Real.tanh u| ∧
    |iteratedDeriv 3 Real.tanh u| ≤ 2 ∧
    |iteratedDeriv 4 Real.tanh u| ≤ 16 * |Real.tanh u| := by
  rw [deriv_tanh_eq, iteratedDeriv_two_tanh, iteratedDeriv_three_tanh, iteratedDeriv_four_tanh]
  simp only []
  set t := Real.tanh u
  have ht : t ^ 2 < 1 := Real.tanh_sq_lt_one u
  have hs0 : 0 ≤ t ^ 2 := sq_nonneg t
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [abs_le]; constructor <;> nlinarith
  · have e : -2 * t + 2 * t ^ 3 = t * (-2 * (1 - t ^ 2)) := by ring
    rw [e, abs_mul, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg t)
    rw [abs_le]; constructor <;> nlinarith
  · rw [abs_le]; constructor <;> nlinarith [sq_nonneg (t ^ 2 - 2 / 3)]
  · have e : 16 * t - 40 * t ^ 3 + 24 * t ^ 5 = t * (16 - 40 * t ^ 2 + 24 * (t ^ 2) ^ 2) := by
      ring
    rw [e, abs_mul, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg t)
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (t ^ 2 - 5 / 6)]

/-- Paper: `cor:new-integer-score` (tanh_new_critical.tex): the normalized
factory target `G_r(z) = tanh(rz)/tanh r` has `G_r'(0) = r coth r`. -/
theorem hasDerivAt_normalized_tanh (r : ℝ) :
    HasDerivAt (fun z => Real.tanh (r * z) / Real.tanh r) (r / Real.tanh r) 0 := by
  have h1 : HasDerivAt (fun z : ℝ => r * z) r 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_mul r
  have h2 := ((hasDerivAt_tanh (r * 0)).comp (0:ℝ) h1).div_const (Real.tanh r)
  have h3 : HasDerivAt (fun z => Real.tanh (r * z) / Real.tanh r)
      ((1 - Real.tanh (r * 0) ^ 2) * r / Real.tanh r) 0 := h2
  rw [mul_zero, Real.tanh_zero] at h3
  simpa using h3

/-- `tanh` is positive on positive reals. Auxiliary for
`prop:new-local-obstruction` (tanh_new_critical.tex). -/
theorem tanh_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hx) (Real.cosh_pos x)

/-- Paper: `prop:new-local-obstruction` (tanh_new_critical.tex), proof: each
coefficient ratio of the `sinh^2` series is at most `1/3`; in the form
`12^n ≤ 6 (2n)!`. -/
theorem twelve_pow_le (n : ℕ) : (12 : ℝ) ^ n ≤ 6 * ((2 * n).factorial : ℝ) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; norm_num [Nat.factorial]
    · have h1 : (2 * (k + 1)).factorial = (2 * k + 2) * ((2 * k + 1) * (2 * k).factorial) := by
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      rw [h1]
      push_cast
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hf : (0 : ℝ) ≤ ((2 * k).factorial : ℝ) := by positivity
      rw [pow_succ]
      have h12 : (12 : ℝ) ≤ (2 * k + 2) * (2 * k + 1) := by nlinarith
      calc (12 : ℝ) ^ k * 12 ≤ 6 * ((2 * k).factorial : ℝ) * 12 := by nlinarith
        _ ≤ 6 * ((2 * k).factorial : ℝ) * ((2 * k + 2) * (2 * k + 1)) := by
          apply mul_le_mul_of_nonneg_left h12; positivity
        _ = 6 * ((2 * k + 2) * ((2 * k + 1) * ((2 * k).factorial : ℝ))) := by ring

/-- Paper: `prop:new-local-obstruction` (tanh_new_critical.tex), proof: the
series of `sinh^2 x` is coefficientwise bounded by `x^2/(1 - x^2/3)`. -/
theorem sinh_sq_le {x : ℝ} (hx : x ^ 2 < 3) :
    Real.sinh x ^ 2 ≤ x ^ 2 / (1 - x ^ 2 / 3) := by
  set y := x ^ 2 / 3 with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y < 1 := by rw [hy]; linarith
  have hcosh := Real.hasSum_cosh (2 * x)
  have hgeo := (hasSum_geometric_of_lt_one hy0 hy1).mul_left 6
  have hδ : HasSum (fun n : ℕ => if n = 0 then (5 : ℝ) else 0) 5 := hasSum_ite_eq 0 5
  have hle := hasSum_le (fun n => ?_) (hcosh.add hδ) hgeo
  · have h2 : Real.cosh (2 * x) = 1 + 2 * Real.sinh x ^ 2 := by
      rw [Real.cosh_two_mul, Real.cosh_sq]; ring
    rw [h2] at hle
    have h1y : 0 < 1 - y := by linarith
    have : Real.sinh x ^ 2 ≤ 3 * y / (1 - y) := by
      rw [le_div_iff₀ h1y]
      rw [← div_eq_mul_inv, le_div_iff₀ h1y] at hle
      nlinarith
    calc Real.sinh x ^ 2 ≤ 3 * y / (1 - y) := this
      _ = x ^ 2 / (1 - x ^ 2 / 3) := by rw [hy]; ring
  · show (2 * x) ^ (2 * n) / ((2 * n).factorial : ℝ) + (if n = 0 then 5 else 0) ≤ 6 * y ^ n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; norm_num
    · have hne : n ≠ 0 := hn.ne'
      simp only [hne, ite_false, add_zero]
      have hf : (0 : ℝ) < ((2 * n).factorial : ℝ) := by positivity
      rw [div_le_iff₀ hf]
      have hpow : (2 * x) ^ (2 * n) = 12 ^ n * y ^ n := by
        rw [pow_mul, show (2 * x) ^ 2 = 12 * y by rw [hy]; ring, mul_pow]
      rw [hpow]
      have hyn : 0 ≤ y ^ n := pow_nonneg hy0 n
      nlinarith [twelve_pow_le n]


/-- Paper: `prop:new-local-obstruction` (tanh_new_critical.tex), proof, and
`eq:cothradius` in `lem:radius` (tanh_rates.tex): `coth^2 x ≥ x^{-2} + 2/3`, in
the form `tanh^2 x ≤ 3x^2/(3 + 2x^2)`. -/
theorem tanh_sq_le {x : ℝ} (hx : x ^ 2 < 3) :
    Real.tanh x ^ 2 ≤ 3 * x ^ 2 / (3 + 2 * x ^ 2) := by
  have hs := sinh_sq_le hx
  have hc : Real.cosh x ^ 2 = 1 + Real.sinh x ^ 2 := Real.cosh_sq' x
  have hcpos : 0 < Real.cosh x ^ 2 := by positivity
  rw [Real.tanh_eq_sinh_div_cosh, div_pow, div_le_div_iff₀ hcpos (by positivity), hc]
  have h3 : 0 < 1 - x ^ 2 / 3 := by linarith
  rw [le_div_iff₀ h3] at hs
  nlinarith

/-- `tanh x ≤ x` for `x ≥ 0`. Auxiliary for
`prop:new-local-obstruction` (tanh_new_critical.tex). -/
theorem tanh_le_self {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  rcases lt_or_ge x 1 with h | h
  · have hx2 : x ^ 2 < 3 := by nlinarith
    have ht := tanh_sq_le hx2
    have h3 : 3 * x ^ 2 / (3 + 2 * x ^ 2) ≤ x ^ 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg x]
    have ht0 : 0 ≤ Real.tanh x := by
      rcases hx.eq_or_lt with h0 | h0
      · subst h0; simp
      · exact (tanh_pos h0).le
    nlinarith
  · exact (Real.tanh_lt_one x).le.trans h

/-- Paper: `prop:new-local-obstruction` (tanh_new_critical.tex), proof, and
`eq:xcothx` (tanh_scalar.tex): `x coth x ≤ 1 + x^2/3`; the `x^{2k+1}` coefficient of
`(1 + x^2/3) sinh x - x cosh x` is `4k(k-1)/[3(2k+1)!] ≥ 0`. -/
theorem self_le_tanh_mul {x : ℝ} (hx : 0 ≤ x) :
    x * Real.cosh x ≤ (1 + x ^ 2 / 3) * Real.sinh x := by
  have hs := Real.hasSum_sinh x
  have hc := (Real.hasSum_cosh x).mul_left x
  have hs3 := hs.mul_left (x ^ 2 / 3)
  let g : ℕ → ℝ := fun n => if n = 0 then 0 else x ^ (2 * n + 1) / (3 * ((2 * n - 1).factorial : ℝ))
  have hg : HasSum g (x ^ 2 / 3 * Real.sinh x) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, g, ite_true, sub_zero]
    convert hs3 using 1
    funext n
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega, show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring,
      pow_add]
    field_simp
  have htot := (hs.add hg).sub hc
  have hnn : 0 ≤ Real.sinh x + x ^ 2 / 3 * Real.sinh x - x * Real.cosh x := by
    refine htot.nonneg (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [g]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp only [g, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
      rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by ring,
        show 2 * (k + 1) = (2 * k + 1) + 1 by ring,
        Nat.factorial_succ, Nat.factorial_succ (2 * k + 1)]
      push_cast
      have hF : (0 : ℝ) < ((2 * k + 1).factorial : ℝ) := by positivity
      have hxp : 0 ≤ x ^ (2 * k + 1 + 1 + 1) := pow_nonneg hx _
      have hkey : x ^ (2 * k + 1 + 1 + 1) / ((2 * (k : ℝ) + 2 + 1) * ((2 * (k : ℝ) + 1 + 1) *
            ((2 * k + 1).factorial : ℝ))) +
          x ^ (2 * k + 1 + 1 + 1) / (3 * ((2 * k + 1).factorial : ℝ)) -
          x * (x ^ (2 * k + 1 + 1) / ((2 * (k : ℝ) + 1 + 1) * ((2 * k + 1).factorial : ℝ))) =
          x ^ (2 * k + 1 + 1 + 1) * (4 * k * (k + 1)) /
            (3 * (2 * k + 3) * (2 * k + 2) * ((2 * k + 1).factorial : ℝ)) := by
        rw [pow_succ x (2 * k + 1 + 1)]
        field_simp
        ring
      rw [hkey]
      positivity
  nlinarith


/-- The critical radii `R_0 = 1`, `R_{j+1} = tanh R_j`
(tanh_new_critical.tex, `prop:new-local-obstruction`). -/
noncomputable def R (j : ℕ) : ℝ := Real.tanh^[j] 1

/-- `R_0 = 1`. Auxiliary for
`prop:new-local-obstruction` (tanh_new_critical.tex). -/
theorem R_zero : R 0 = 1 := rfl

/-- `R_{j+1} = tanh R_j`. Auxiliary for
`prop:new-local-obstruction` (tanh_new_critical.tex). -/
theorem R_succ (j : ℕ) : R (j + 1) = Real.tanh (R j) :=
  Function.iterate_succ_apply' _ _ _

/-- The radii are positive. Auxiliary for
`prop:new-local-obstruction` (tanh_new_critical.tex). -/
theorem R_pos (j : ℕ) : 0 < R j := by
  induction j with
  | zero => rw [R_zero]; norm_num
  | succ j ih => rw [R_succ]; exact tanh_pos ih

/-- The radii are at most one. Auxiliary for
`prop:new-local-obstruction` (tanh_new_critical.tex). -/
theorem R_le_one (j : ℕ) : R j ≤ 1 := by
  induction j with
  | zero => rw [R_zero]
  | succ j ih => rw [R_succ]; exact (tanh_le_self (R_pos j).le).trans ih

/-- The radii decrease. Auxiliary for
`prop:new-local-obstruction` (tanh_new_critical.tex). -/
theorem R_succ_le (j : ℕ) : R (j + 1) ≤ R j := by
  rw [R_succ]; exact tanh_le_self (R_pos j).le

/-- Paper: `prop:new-local-obstruction` and `prop:new-critical-derivatives`
(tanh_new_critical.tex), `lem:radius` (tanh_rates.tex), and the right half of
`eq:main-radius` (exact_sampling_networks.tex): `R_j^2 ≤ 3/(2j+3)`. -/
theorem R_sq_le (j : ℕ) : R j ^ 2 ≤ 3 / (2 * j + 3) := by
  induction j with
  | zero => rw [R_zero]; norm_num
  | succ j ih =>
    rw [R_succ]
    have h0 : 0 ≤ R j ^ 2 := sq_nonneg _
    have hlt : R j ^ 2 < 3 := by
      have : (3 : ℝ) / (2 * j + 3) ≤ 1 := by
        rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
      linarith
    have ht := tanh_sq_le hlt
    have hmono : 3 * R j ^ 2 / (3 + 2 * R j ^ 2) ≤ 3 / (2 * ((j + 1 : ℕ) : ℝ) + 3) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      rw [le_div_iff₀ (by positivity)] at ih
      push_cast
      nlinarith
    linarith

/-- Paper: `prop:new-local-obstruction` (tanh_new_critical.tex):
`R_D^{-2} ≥ 1 + 2D/3`. -/
theorem one_add_le_inv_R_sq (j : ℕ) : 1 + 2 * (j : ℝ) / 3 ≤ 1 / R j ^ 2 := by
  have h := R_sq_le j
  have hp : 0 < R j ^ 2 := by have := R_pos j; positivity
  rw [le_div_iff₀ hp]
  rw [le_div_iff₀ (by positivity)] at h
  nlinarith

/-- `x / tanh x ≤ 1 + x^2/3` for `x > 0`. Auxiliary for
`prop:new-local-obstruction` (tanh_new_critical.tex). -/
theorem self_div_tanh_le {x : ℝ} (hx : 0 < x) : x / Real.tanh x ≤ 1 + x ^ 2 / 3 := by
  have h := self_le_tanh_mul hx.le
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  rw [Real.tanh_eq_sinh_div_cosh, div_div_eq_mul_div, div_le_iff₀ hs]
  linarith

/-- `x / tanh x ≥ 1` for `x > 0`. Auxiliary for
`prop:new-local-obstruction` (tanh_new_critical.tex). -/
theorem one_le_self_div_tanh {x : ℝ} (hx : 0 < x) : 1 ≤ x / Real.tanh x := by
  rw [le_div_iff₀ (tanh_pos hx)]; simpa using tanh_le_self hx.le

/-- The local amplification `a_{j+1} = R_j / R_{j+1} = R_j coth R_j` of
`prop:new-local-obstruction` (indexed from zero here). Auxiliary for
`prop:new-local-obstruction` (tanh_new_critical.tex). -/
noncomputable def amp (j : ℕ) : ℝ := R j / R (j + 1)

/-- `a_{j+1} = R_j / tanh R_j`. Auxiliary for
`prop:new-local-obstruction` (tanh_new_critical.tex). -/
theorem amp_eq (j : ℕ) : amp j = R j / Real.tanh (R j) := by rw [amp, R_succ]

/-- `a_{j+1} ≥ 1`. Auxiliary for
`prop:new-local-obstruction` (tanh_new_critical.tex). -/
theorem one_le_amp (j : ℕ) : 1 ≤ amp j := by rw [amp_eq]; exact one_le_self_div_tanh (R_pos j)

/-- Paper: `prop:new-local-obstruction` (tanh_new_critical.tex), proof:
`a_{j+1} - 1 ≤ R_j^2/3 ≤ 1/(2j+3)`. -/
theorem amp_sub_one_le (j : ℕ) : amp j - 1 ≤ 1 / (2 * j + 3) := by
  have h1 := self_div_tanh_le (R_pos j)
  have h2 := R_sq_le j
  rw [amp_eq]
  have : R j ^ 2 / 3 ≤ 1 / (2 * j + 3) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    rw [le_div_iff₀ (by positivity)] at h2
    linarith
  linarith

/-- Paper: `prop:new-local-obstruction` (tanh_new_critical.tex), proof:
`∏ a_j = R_D^{-1}`. -/
theorem prod_amp (D : ℕ) : ∏ j ∈ range D, amp j = 1 / R D := by
  induction D with
  | zero => simp [R_zero]
  | succ D ih =>
    rw [prod_range_succ, ih, amp]
    have h1 := (R_pos D).ne'
    have h2 := (R_pos (D + 1)).ne'
    field_simp

/-- Paper: `prop:new-local-obstruction` (tanh_new_critical.tex), proof: the
midpoint bound `∑_{j≥0} 9/(2j+3)^2 ≤ 9/4`, in the finite form
`∑_{j<D} 1/(2j+3)^2 ≤ 1/4 - 1/(4(D+1))`. -/
theorem sum_inv_sq_le (D : ℕ) :
    ∑ j ∈ range D, (1 / (2 * (j : ℝ) + 3)) ^ 2 ≤ 1 / 4 - 1 / (4 * ((D : ℝ) + 1)) := by
  induction D with
  | zero => norm_num
  | succ D ih =>
    rw [sum_range_succ]
    have hstep : (1 / (2 * (D : ℝ) + 3)) ^ 2 ≤
        1 / (4 * ((D : ℝ) + 1)) - 1 / (4 * ((D : ℝ) + 2)) := by
      rw [div_pow, one_pow, div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have he : (1 : ℝ) / (4 * (((D + 1 : ℕ) : ℝ) + 1)) = 1 / (4 * ((D : ℝ) + 2)) := by
      push_cast; ring_nf
    rw [he]
    linarith

/-- Paper: `prop:new-local-obstruction` (tanh_new_critical.tex), proof:
`∑ (a_j - 1)^2 ≤ 1/4`. -/
theorem sum_amp_sq_le (D : ℕ) : ∑ j ∈ range D, (amp j - 1) ^ 2 ≤ 1 / 4 := by
  have h := sum_inv_sq_le D
  have h' : ∑ j ∈ range D, (amp j - 1) ^ 2 ≤ ∑ j ∈ range D, (1 / (2 * (j : ℝ) + 3)) ^ 2 := by
    apply sum_le_sum
    intro j _
    have h0 : 0 ≤ amp j - 1 := by linarith [one_le_amp j]
    exact pow_le_pow_left₀ h0 (amp_sub_one_le j) 2
  have h4 : 0 ≤ 1 / (4 * ((D : ℝ) + 1)) := by positivity
  linarith

/-- Paper: `prop:new-local-obstruction` (tanh_new_critical.tex), proof: for
`a = 1 + b ≥ 1`, `3 log(1+b) - log(1+3b) ≤ 3b^2`, in the form
`a^3 exp(-3(a-1)^2) ≤ 3a - 2`. -/
theorem cube_exp_le {a : ℝ} (ha : 1 ≤ a) : a ^ 3 * Real.exp (-(3 * (a - 1) ^ 2)) ≤ 3 * a - 2 := by
  have he := Real.add_one_le_exp (3 * (a - 1) ^ 2)
  have hpos : 0 < Real.exp (3 * (a - 1) ^ 2) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
  have hb : 0 ≤ a - 1 := by linarith
  have hpoly : a ^ 3 ≤ (3 * a - 2) * (3 * (a - 1) ^ 2 + 1) := by
    nlinarith [pow_nonneg hb 3]
  have h3 : 0 ≤ 3 * a - 2 := by linarith
  calc a ^ 3 ≤ (3 * a - 2) * (3 * (a - 1) ^ 2 + 1) := hpoly
    _ ≤ (3 * a - 2) * Real.exp (3 * (a - 1) ^ 2) := mul_le_mul_of_nonneg_left he h3

/-- Paper: `prop:new-local-obstruction` (tanh_new_critical.tex): `e^{3/4} < 8/3`. -/
theorem exp_three_quarters_lt : Real.exp (3 / 4) < 8 / 3 := by
  have h4 : Real.exp (3 / 4) ^ 4 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have he := Real.exp_one_lt_d9
  have h3 : Real.exp 1 ^ 3 < (8 / 3) ^ 4 := by
    have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    calc Real.exp 1 ^ 3 < 2.7182818286 ^ 3 := by gcongr
      _ < (8 / 3) ^ 4 := by norm_num
  rw [← h4] at h3
  exact lt_of_pow_lt_pow_left₀ 4 (by norm_num) h3

/-- Paper: `prop:new-local-obstruction` (tanh_new_critical.tex), proof:
`∏ (3a_j - 2) ≥ R_D^{-3} e^{-3/4}`. -/
theorem prod_lower (D : ℕ) :
    Real.exp (-(3 / 4)) * (1 / R D) ^ 3 ≤ ∏ j ∈ range D, (3 * amp j - 2) := by
  have hpt : ∀ j ∈ range D, amp j ^ 3 * Real.exp (-(3 * (amp j - 1) ^ 2)) ≤ 3 * amp j - 2 :=
    fun j _ => cube_exp_le (one_le_amp j)
  have hprod := prod_le_prod₀
    (fun j _ => mul_nonneg (pow_nonneg (by linarith [one_le_amp j]) 3) (Real.exp_pos _).le) hpt
  rw [prod_mul_distrib, prod_pow, prod_amp, ← Real.exp_sum] at hprod
  have hsum : -(3 / 4 : ℝ) ≤ ∑ j ∈ range D, -(3 * (amp j - 1) ^ 2) := by
    rw [sum_neg_distrib, ← mul_sum]
    have := sum_amp_sq_le D
    linarith
  have hexp := Real.exp_le_exp.mpr hsum
  have hR : 0 ≤ (1 / R D) ^ 3 := by have := R_pos D; positivity
  calc Real.exp (-(3 / 4)) * (1 / R D) ^ 3
      ≤ Real.exp (∑ j ∈ range D, -(3 * (amp j - 1) ^ 2)) * (1 / R D) ^ 3 :=
        mul_le_mul_of_nonneg_right hexp hR
    _ = (1 / R D) ^ 3 * Real.exp (∑ j ∈ range D, -(3 * (amp j - 1) ^ 2)) := by ring
    _ ≤ _ := hprod

/-- Paper: `prop:new-local-obstruction` (tanh_new_critical.tex): multiplication
by the root gate gives `R_D ∏ (3a_j - 2) ≥ e^{-3/4} R_D^{-2}`. -/
theorem bottom_lower (D : ℕ) :
    Real.exp (-(3 / 4)) * (1 / R D ^ 2) ≤ R D * ∏ j ∈ range D, (3 * amp j - 2) := by
  have h := prod_lower D
  have hR := R_pos D
  calc Real.exp (-(3 / 4)) * (1 / R D ^ 2)
      = R D * (Real.exp (-(3 / 4)) * (1 / R D) ^ 3) := by field_simp
    _ ≤ R D * ∏ j ∈ range D, (3 * amp j - 2) := mul_le_mul_of_nonneg_left h hR.le

/-- Paper: `prop:new-local-obstruction` (tanh_new_critical.tex):
`e^{-3/4}(1 + 2D/3) > D/4`. -/
theorem quarter_lt (D : ℕ) : (D : ℝ) / 4 < Real.exp (-(3 / 4)) * (1 + 2 * D / 3) := by
  have he := exp_three_quarters_lt
  have hpos := Real.exp_pos (3 / 4)
  rw [Real.exp_neg, ← div_eq_inv_mul, lt_div_iff₀ hpos]
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  nlinarith

/-- Paper: `prop:new-local-obstruction` (tanh_new_critical.tex). Let `L j` be the
expected number of source requests of the local factory at layer `j+1`, and
`N` the expected number of bottom source requests. The hypotheses are the two
probabilistic inputs of the proof, taken as stand-ins: `hL` is
`cor:new-integer-score` applied to `G_{R_j}`, whose derivative at zero is
`amp j` (`amp_eq_normalized_derivative`), and `hN` is the predictable
charging of fresh recursive calls. Then
`N ≥ e^{-3/4} R_D^{-2} ≥ e^{-3/4}(1 + 2D/3) > D/4`. The variant
`local_obstruction_from_scores` derives `hL` from per-layer score identities. -/
theorem local_obstruction (D : ℕ) (L : ℕ → ℝ) (N : ℝ)
    (hL : ∀ j ∈ range D, 3 * amp j - 2 ≤ L j)
    (hN : R D * ∏ j ∈ range D, L j ≤ N) :
    Real.exp (-(3 / 4)) * (1 / R D ^ 2) ≤ N ∧
      Real.exp (-(3 / 4)) * (1 + 2 * D / 3) ≤ N ∧ (D : ℝ) / 4 < N := by
  have h1 := bottom_lower D
  have hprod : ∏ j ∈ range D, (3 * amp j - 2) ≤ ∏ j ∈ range D, L j :=
    prod_le_prod₀ (fun j _ => by linarith [one_le_amp j]) hL
  have h2 : R D * ∏ j ∈ range D, (3 * amp j - 2) ≤ R D * ∏ j ∈ range D, L j :=
    mul_le_mul_of_nonneg_left hprod (R_pos D).le
  have hA : Real.exp (-(3 / 4)) * (1 / R D ^ 2) ≤ N := by linarith
  have hB : Real.exp (-(3 / 4)) * (1 + 2 * D / 3) ≤ Real.exp (-(3 / 4)) * (1 / R D ^ 2) :=
    mul_le_mul_of_nonneg_left (one_add_le_inv_R_sq D) (Real.exp_pos _).le
  exact ⟨hA, by linarith, by linarith [quarter_lt D]⟩

/-- A square-root comparison used below. Auxiliary for
`prop:new-critical-derivatives` (tanh_new_critical.tex). -/
theorem le_mul_sqrt {x c y : ℝ} (hc : 0 ≤ c) (h : x ^ 2 ≤ c ^ 2 * y) :
    x ≤ c * Real.sqrt y := by
  have hy : c * Real.sqrt y = Real.sqrt (c ^ 2 * y) := by
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  rw [hy]
  exact Real.le_sqrt_of_sq_le h

/-- Paper: `prop:new-critical-derivatives` (tanh_new_critical.tex), proof: one
step of `∑_{j ≤ ℓ} R_j ≤ √6 √ℓ`. -/
theorem sqrt_step (ℓ : ℕ) {r : ℝ} (hr : r ^ 2 ≤ 3 / (2 * ((ℓ : ℝ) + 1) + 3)) :
    Real.sqrt (6 * ℓ) + r ≤ Real.sqrt (6 * ((ℓ : ℝ) + 1)) := by
  set a := Real.sqrt (6 * ℓ)
  set b := Real.sqrt (6 * ((ℓ : ℝ) + 1))
  have hl : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  have ha2 : a ^ 2 = 6 * ℓ := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = 6 * ((ℓ : ℝ) + 1) := Real.sq_sqrt (by positivity)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have hrb : (r * b) ^ 2 ≤ 9 := by
    rw [mul_pow, hb2]
    rw [le_div_iff₀ (by positivity)] at hr
    nlinarith
  have hrb' : r * b ≤ 3 := by nlinarith
  have hab : a * b ≤ 6 * ℓ + 3 := by nlinarith [sq_nonneg (a - b)]
  have : (a + r) * b ≤ b * b := by nlinarith
  exact le_of_mul_le_mul_right this hb0

/-- Paper: `prop:new-critical-derivatives` (tanh_new_critical.tex), proof:
`∑_{j=1}^{ℓ} R_j ≤ √(6ℓ)`. -/
theorem sum_R_le (ℓ : ℕ) : ∑ j ∈ range ℓ, R (j + 1) ≤ Real.sqrt (6 * ℓ) := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    rw [sum_range_succ]
    have hr := R_sq_le (ℓ + 1)
    push_cast at hr ⊢
    have := sqrt_step ℓ hr
    linarith

/-- Paper: `prop:new-critical-derivatives` (tanh_new_critical.tex). `A, B, C, E`
bound the entrywise `ℓ_1` norms of the first through fourth derivative tensors
at depth `ℓ`. The per-layer recurrences `hA, hB, hC, hE` are the chain-rule
recurrences displayed in the proof and are hypotheses here; `hBnn` records
that `B` bounds a norm. Conclusion: `A_D ≤ 1`, `B_D ≤ 2√6 √D`, `C_D ≤ 38 D`,
`E_D ≤ 624 D^{3/2}`. -/
theorem derivative_mass_bounds (A B C E : ℕ → ℝ)
    (hA0 : A 0 ≤ 1) (hB0 : B 0 = 0) (hC0 : C 0 = 0) (hE0 : E 0 = 0)
    (hBnn : ∀ ℓ, 0 ≤ B ℓ)
    (hA : ∀ ℓ, A (ℓ + 1) ≤ A ℓ)
    (hB : ∀ ℓ, B (ℓ + 1) ≤ B ℓ + 2 * R (ℓ + 1))
    (hC : ∀ ℓ, C (ℓ + 1) ≤ C ℓ + 6 * R (ℓ + 1) * B ℓ + 2)
    (hE : ∀ ℓ, E (ℓ + 1) ≤ E ℓ + 8 * R (ℓ + 1) * C ℓ + 6 * R (ℓ + 1) * B ℓ ^ 2 +
      12 * B ℓ + 16 * R (ℓ + 1)) (D : ℕ) :
    A D ≤ 1 ∧ B D ≤ 2 * Real.sqrt 6 * Real.sqrt D ∧ C D ≤ 38 * D ∧
      E D ≤ 624 * D * Real.sqrt D := by
  have hAll : ∀ ℓ, A ℓ ≤ 1 := by
    intro ℓ; induction ℓ with
    | zero => exact hA0
    | succ ℓ ih => exact (hA ℓ).trans ih
  have hBsum : ∀ ℓ, B ℓ ≤ 2 * ∑ j ∈ range ℓ, R (j + 1) := by
    intro ℓ; induction ℓ with
    | zero => simp [hB0]
    | succ ℓ ih => rw [sum_range_succ]; linarith [hB ℓ]
  have hBle : ∀ ℓ : ℕ, B ℓ ≤ 2 * Real.sqrt (6 * ℓ) := fun ℓ => by
    linarith [hBsum ℓ, sum_R_le ℓ]
  have hBsq : ∀ ℓ : ℕ, B ℓ ^ 2 ≤ 24 * ℓ := fun ℓ => by
    have h1 := hBle ℓ
    have h2 : Real.sqrt (6 * ℓ) ^ 2 = 6 * ℓ := Real.sq_sqrt (by positivity)
    have h3 := hBnn ℓ
    nlinarith
  have hRB : ∀ ℓ : ℕ, R (ℓ + 1) * B ℓ ≤ 6 := fun ℓ => by
    have hr := R_sq_le (ℓ + 1)
    have hr0 := (R_pos (ℓ + 1)).le
    have hl : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    have hsq : (R (ℓ + 1) * B ℓ) ^ 2 ≤ 36 := by
      rw [mul_pow]
      push_cast at hr
      rw [le_div_iff₀ (by positivity)] at hr
      have := hBsq ℓ
      have h4 : 0 ≤ R (ℓ + 1) ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left this h4]
    nlinarith [mul_nonneg hr0 (hBnn ℓ)]
  have hCle : ∀ ℓ : ℕ, C ℓ ≤ 38 * ℓ := by
    intro ℓ; induction ℓ with
    | zero => simp [hC0]
    | succ ℓ ih => push_cast; linarith [hC ℓ, hRB ℓ]
  have hEle : ∀ ℓ : ℕ, E ℓ ≤ 624 * ℓ * Real.sqrt ℓ := by
    intro ℓ; induction ℓ with
    | zero => simp [hE0]
    | succ ℓ ih =>
      have hl : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
      set s := Real.sqrt ((ℓ : ℝ) + 1)
      have hs1 : 1 ≤ s := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
      have hr := R_sq_le (ℓ + 1)
      have hr0 := (R_pos (ℓ + 1)).le
      have hr1 := R_le_one (ℓ + 1)
      push_cast at hr
      rw [le_div_iff₀ (by positivity)] at hr
      have hRl : R (ℓ + 1) * ℓ ≤ 49 / 40 * s := by
        apply le_mul_sqrt (by norm_num)
        rw [mul_pow]
        have h4 : 0 ≤ (ℓ : ℝ) ^ 2 := sq_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left hr h4]
      have hsB : Real.sqrt (6 * ℓ) ≤ 49 / 20 * s := by
        apply le_mul_sqrt (by norm_num)
        rw [Real.sq_sqrt (by positivity)]
        nlinarith
      have hC1 := hCle ℓ
      have hB1 := hBle ℓ
      have hB2 := hBsq ℓ
      have hincr : 8 * R (ℓ + 1) * C ℓ + 6 * R (ℓ + 1) * B ℓ ^ 2 + 12 * B ℓ + 16 * R (ℓ + 1)
          ≤ 624 * s := by
        have e1 : 8 * R (ℓ + 1) * C ℓ ≤ 8 * R (ℓ + 1) * (38 * ℓ) :=
          mul_le_mul_of_nonneg_left hC1 (by positivity)
        have e2 : 6 * R (ℓ + 1) * B ℓ ^ 2 ≤ 6 * R (ℓ + 1) * (24 * ℓ) :=
          mul_le_mul_of_nonneg_left hB2 (by positivity)
        nlinarith
      have hsqrt : Real.sqrt ℓ ≤ s := Real.sqrt_le_sqrt (by linarith)
      have hsq0 : 0 ≤ Real.sqrt (ℓ : ℝ) := Real.sqrt_nonneg _
      have hstep : 624 * (ℓ : ℝ) * Real.sqrt ℓ + 624 * s ≤ 624 * ((ℓ : ℝ) + 1) * s := by
        nlinarith [mul_le_mul_of_nonneg_left hsqrt hl]
      push_cast
      linarith [hE ℓ]
  refine ⟨hAll D, ?_, hCle D, hEle D⟩
  rw [mul_assoc, ← Real.sqrt_mul (by norm_num)]
  exact hBle D

/-- Paper: `prop:new-critical-derivatives` (tanh_new_critical.tex):
`448√(3/2) + 24√6 + 16 < 624`. -/
theorem fourth_derivative_constant :
    448 * Real.sqrt (3 / 2) + 24 * Real.sqrt 6 + 16 < 624 := by
  have h1 : Real.sqrt (3 / 2) < 49 / 40 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h2 : Real.sqrt 6 < 49 / 20 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith


/-- Paper: `prop:new-critical-derivatives` (tanh_new_critical.tex): the rational
bounds `√(3/2) < 49/40` and `√6 < 49/20` give the constant `624`. -/
theorem fourth_derivative_coefficient :
    448 * (49 / 40 : ℝ) + 24 * (49 / 20 : ℝ) + 16 < 624 := by
  norm_num

/-- Paper: `prop:new-local-obstruction` (tanh_new_critical.tex): the local
amplification `a_{j+1}` is the derivative at zero of `G_{R_j}`. -/
theorem amp_eq_normalized_derivative (j : ℕ) :
    HasDerivAt (fun z => Real.tanh (R j * z) / Real.tanh (R j)) (amp j) 0 := by
  rw [amp_eq]; exact hasDerivAt_normalized_tanh (R j)

/-- Paper: `prop:new-local-obstruction` (tanh_new_critical.tex): multiplying by
the root gate `R_D`, `R_D · R_D^{-3} c = R_D^{-2} c`. -/
theorem root_radius_product (r : ℝ) (hr : 0 < r) (c : ℝ) :
    r * (r⁻¹ ^ 3 * c) = r⁻¹ ^ 2 * c := by
  have hn : r ≠ 0 := ne_of_gt hr
  field_simp

/-- Paper: `cor:new-integer-score` (tanh_new_critical.tex) and `sec:conf-open`
(conference.tex), the calculus part only: `3ρ coth ρ - 2 = 1 + ρ^2 + O(ρ^4)`,
explicitly `1 + ρ^2 - ρ^4/6 ≤ 3ρ coth ρ - 2 ≤ 1 + ρ^2` for `0 < ρ ≤ 1`. The
request lower bound itself is `normalized_factory_cost`. -/
theorem score_cost_expansion {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    1 + ρ ^ 2 - ρ ^ 4 / 6 ≤ 3 * (ρ / Real.tanh ρ) - 2 ∧
      3 * (ρ / Real.tanh ρ) - 2 ≤ 1 + ρ ^ 2 := by
  have hup := self_div_tanh_le hρ
  have hc1 := one_le_self_div_tanh hρ
  refine ⟨?_, by linarith⟩
  set c := ρ / Real.tanh ρ with hc
  have ht := tanh_pos hρ
  have hsq : 1 + 2 * ρ ^ 2 / 3 ≤ c ^ 2 := by
    have h1 := tanh_sq_le (x := ρ) (by nlinarith)
    have htp : 0 < Real.tanh ρ ^ 2 := by positivity
    rw [hc, div_pow, le_div_iff₀ htp]
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hL0 : 0 ≤ 1 + ρ ^ 2 / 3 - ρ ^ 4 / 18 := by nlinarith [pow_le_one₀ hρ.le hρ1 (n := 4)]
  have hL2 : (1 + ρ ^ 2 / 3 - ρ ^ 4 / 18) ^ 2 ≤ 1 + 2 * ρ ^ 2 / 3 := by
    have hy : ρ ^ 2 ≤ 1 := by nlinarith
    have hy0 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
    nlinarith [mul_nonneg (mul_nonneg hy0 hy0) (mul_nonneg hy0 (sub_nonneg.mpr hy)),
      mul_nonneg (mul_nonneg hy0 hy0) hy0]
  have hL : 1 + ρ ^ 2 / 3 - ρ ^ 4 / 18 ≤ c := by nlinarith
  linarith

/-- Paper: `lem:new-finite-score` (tanh_new_critical.tex), proof: with
`d(z) = -½ log(1 - z^2)`, `z^2 ≤ 2 d(z) ≤ z^2/(1 - z^2)`; hence
`√(2d(z))/|z| → 1` as `z → 0`. -/
theorem relative_entropy_bounds {z : ℝ} (hz : z ^ 2 < 1) :
    z ^ 2 ≤ -Real.log (1 - z ^ 2) ∧ -Real.log (1 - z ^ 2) ≤ z ^ 2 / (1 - z ^ 2) := by
  have hpos : 0 < 1 - z ^ 2 := by linarith
  constructor
  · have := Real.log_le_sub_one_of_pos hpos; linarith
  · have h := Real.one_sub_inv_le_log_of_pos hpos
    have e : 1 - (1 - z ^ 2)⁻¹ = -(z ^ 2 / (1 - z ^ 2)) := by field_simp; ring
    rw [e] at h; linarith

/-- Paper: `lem:new-finite-score` (tanh_new_critical.tex), proof:
`√(2d(z))/|z| → 1` as `z → 0`. -/
theorem relative_entropy_ratio_tendsto :
    Filter.Tendsto (fun z : ℝ => Real.sqrt (-Real.log (1 - z ^ 2)) / |z|)
      (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
  have hcont : ContinuousAt (fun z : ℝ => 1 / Real.sqrt (1 - z ^ 2)) 0 :=
    ContinuousAt.div continuousAt_const (by fun_prop) (by simp)
  have hup : Filter.Tendsto (fun z : ℝ => 1 / Real.sqrt (1 - z ^ 2)) (nhdsWithin 0 {0}ᶜ)
      (nhds 1) := by
    have h := hcont.tendsto
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
      Real.sqrt_one, div_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h1 : ∀ᶠ z in nhds (0 : ℝ), z ^ 2 < 1 := by
    have ht : Filter.Tendsto (fun z : ℝ => z ^ 2) (nhds 0) (nhds 0) := by
      simpa using (continuous_pow 2).tendsto (0 : ℝ)
    exact ht.eventually (gt_mem_nhds (by norm_num))
  have h2 : ∀ᶠ z in nhdsWithin (0 : ℝ) {0}ᶜ, z ≠ 0 := self_mem_nhdsWithin
  have hev := (h1.filter_mono nhdsWithin_le_nhds).and h2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · filter_upwards [hev] with z hz
    obtain ⟨hz1, hz0⟩ := hz
    have hb := (relative_entropy_bounds hz1).1
    rw [le_div_iff₀ (abs_pos.mpr hz0), one_mul]
    exact Real.le_sqrt_of_sq_le (by rw [sq_abs]; exact hb)
  · filter_upwards [hev] with z hz
    obtain ⟨hz1, hz0⟩ := hz
    have hb := (relative_entropy_bounds hz1).2
    have hpos : 0 < 1 - z ^ 2 := by linarith
    rw [div_le_div_iff₀ (abs_pos.mpr hz0) (Real.sqrt_pos.mpr hpos), one_mul,
      ← Real.sqrt_mul' _ hpos.le, ← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ hpos] at hb
    exact hb

/-! ## The critical radius asymptotics -/

/-- Paper: the sentences after `eq:main-radius` (exact_sampling_networks.tex):
`sinh^2 x ≥ x^2 + x^4/3`, from the first terms of the series of `cosh 2x`. -/
theorem sinh_sq_ge (x : ℝ) : x ^ 2 + x ^ 4 / 3 ≤ Real.sinh x ^ 2 := by
  have hc := Real.hasSum_cosh (2 * x)
  have h := sum_le_hasSum (range 3)
    (fun n _ => div_nonneg (by rw [pow_mul]; positivity) (by positivity)) hc
  simp only [sum_range_succ, sum_range_zero] at h
  norm_num [Nat.factorial] at h
  have h2 : Real.cosh (2 * x) = 1 + 2 * Real.sinh x ^ 2 := by
    rw [Real.cosh_two_mul, Real.cosh_sq]; ring
  rw [h2] at h
  nlinarith

/-- Paper: the sentences after `eq:main-radius` (exact_sampling_networks.tex):
`coth^2 x ≤ x^{-2} + 2/3 + x^2/9` for `x > 0`. -/
theorem inv_tanh_sq_le {x : ℝ} (hx : 0 < x) :
    1 / Real.tanh x ^ 2 ≤ 1 / x ^ 2 + 2 / 3 + x ^ 2 / 9 := by
  have hs := sinh_sq_ge x
  have hsp : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hc : Real.cosh x ^ 2 = 1 + Real.sinh x ^ 2 := Real.cosh_sq' x
  have hx2 : 0 < x ^ 2 := by positivity
  have e : 1 / Real.tanh x ^ 2 = 1 + 1 / Real.sinh x ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh, div_pow, one_div_div, hc]; field_simp; ring
  rw [e]
  have h1 : 1 / Real.sinh x ^ 2 ≤ 1 / (x ^ 2 + x ^ 4 / 3) :=
    one_div_le_one_div_of_le (by positivity) hs
  have h2 : 1 / (x ^ 2 + x ^ 4 / 3) ≤ 1 / x ^ 2 - 1 / 3 + x ^ 2 / 9 := by
    rw [div_le_iff₀ (by positivity)]
    have e2 : (1 / x ^ 2 - 1 / 3 + x ^ 2 / 9) * (x ^ 2 + x ^ 4 / 3) = 1 + x ^ 6 / 27 := by
      field_simp; ring
    rw [e2]; nlinarith [pow_pos hx 6]
  linarith

/-- `∑_{ℓ=1}^D ℓ^{-1/2} ≤ 2 √D`. Auxiliary for `eq:main-radius`
(exact_sampling_networks.tex). -/
theorem sum_inv_sqrt_le (D : ℕ) : ∑ ℓ ∈ range D, 1 / Real.sqrt ((ℓ : ℝ) + 1) ≤
    2 * Real.sqrt D := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [sum_range_succ]
    set a := Real.sqrt (D : ℝ)
    set b := Real.sqrt ((D : ℝ) + 1)
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have hb0 : 0 < b := Real.sqrt_pos.mpr (by positivity)
    have ha2 : a ^ 2 = D := Real.sq_sqrt (Nat.cast_nonneg D)
    have hb2 : b ^ 2 = (D : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hab : a * b ≤ (D : ℝ) + 1 / 2 := by nlinarith [sq_nonneg (a - b)]
    have hstep : 1 / b ≤ 2 * b - 2 * a := by
      rw [div_le_iff₀ hb0]; nlinarith
    push_cast
    linarith

/-- Paper: the sentences after `eq:main-radius` (exact_sampling_networks.tex):
summing the bound of `inv_tanh_sq_le` over the recursion, with
`R_i^2 ≤ 3/(2i+3)` and `∑_{i<j} 1/(2i+3) ≤ √j`, gives
`R_j^{-2} ≤ 1 + 2j/3 + √j/3`. -/
theorem inv_R_sq_le (j : ℕ) : 1 / R j ^ 2 ≤ 1 + 2 * (j : ℝ) / 3 + Real.sqrt j / 3 := by
  have hT : ∀ j : ℕ, 1 / R j ^ 2 ≤ 1 + 2 * (j : ℝ) / 3 +
      (∑ i ∈ range j, 1 / (2 * (i : ℝ) + 3)) / 3 := by
    intro j
    induction j with
    | zero => simp [R_zero]
    | succ j ih =>
      rw [R_succ, sum_range_succ]
      have h1 := inv_tanh_sq_le (R_pos j)
      have h2 := R_sq_le j
      have h3 : R j ^ 2 / 9 ≤ 1 / (3 * (2 * (j : ℝ) + 3)) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        rw [le_div_iff₀ (by positivity)] at h2
        linarith
      push_cast
      have e : 1 / (3 * (2 * (j : ℝ) + 3)) = (1 / (2 * (j : ℝ) + 3)) / 3 := by
        rw [div_div, mul_comm]
      linarith
  have hS : ∑ i ∈ range j, 1 / (2 * (i : ℝ) + 3) ≤ Real.sqrt j := by
    have h1 : ∀ i ∈ range j, 1 / (2 * (i : ℝ) + 3) ≤ 1 / 2 * (1 / Real.sqrt ((i : ℝ) + 1)) := by
      intro i _
      have hs : 0 < Real.sqrt ((i : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
      have hs1 : Real.sqrt ((i : ℝ) + 1) ≤ (i : ℝ) + 1 := by
        rw [Real.sqrt_le_left (by positivity)]
        have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        nlinarith
      rw [div_le_iff₀ (by positivity)]
      field_simp
      linarith
    have h2 := sum_le_sum h1
    rw [← mul_sum] at h2
    have h3 := sum_inv_sqrt_le j
    linarith
  linarith [hT j]

/-- Paper: the sentences after `eq:main-radius` (exact_sampling_networks.tex),
with an explicit remainder: `|R_j^2 · (2j/3) - 1| ≤ 2/√j` for `j ≥ 1`. -/
theorem radius_asymptotic_bound (j : ℕ) (hj : 1 ≤ j) :
    |R j ^ 2 * (2 * (j : ℝ) / 3) - 1| ≤ 2 / Real.sqrt j := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  set s := Real.sqrt (j : ℝ)
  have hs1 : 1 ≤ s := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hj'
  have hs2 : s ^ 2 = j := Real.sq_sqrt (by linarith)
  have hR := R_pos j
  have hRp : 0 < R j ^ 2 := by positivity
  have hup := R_sq_le j
  have hinv := inv_R_sq_le j
  set Q := 1 + 2 * (j : ℝ) / 3 + s / 3
  have hQ : 0 < Q := by positivity
  have hRQ : 1 ≤ R j ^ 2 * Q := by
    rw [div_le_iff₀ hRp] at hinv; linarith
  rw [abs_le]
  constructor
  · -- lower bound: R^2 (2j/3) ≥ 1 - 2/s
    rw [neg_le_sub_iff_le_add]
    have hpoly : (1 - 2 / s) * Q ≤ 2 * (j : ℝ) / 3 := by
      have hQ' : Q = 1 + 2 * s ^ 2 / 3 + s / 3 := by rw [hs2]
      rw [hQ', ← hs2]
      have e : (1 - 2 / s) * (1 + 2 * s ^ 2 / 3 + s / 3) =
          2 * s ^ 2 / 3 + (-3 * s ^ 2 + s - 6) / (3 * s) := by
        field_simp; ring
      rw [e]
      have : (-3 * s ^ 2 + s - 6) / (3 * s) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
      linarith
    have h2 : 0 ≤ 2 / s := by positivity
    by_cases hneg : 1 - 2 / s ≤ 0
    · have : 0 ≤ R j ^ 2 * (2 * (j : ℝ) / 3) := by positivity
      linarith
    · have hneg' := not_le.mp hneg
      have : (1 - 2 / s) ≤ (1 - 2 / s) * (R j ^ 2 * Q) := by nlinarith
      have h3 : (1 - 2 / s) * (R j ^ 2 * Q) ≤ R j ^ 2 * (2 * (j : ℝ) / 3) := by
        have := mul_le_mul_of_nonneg_left hpoly hRp.le
        nlinarith
      linarith
  · -- upper bound: R^2 (2j/3) ≤ 2j/(2j+3) ≤ 1
    have h1 : R j ^ 2 * (2 * (j : ℝ) / 3) ≤ 3 / (2 * (j : ℝ) + 3) * (2 * (j : ℝ) / 3) :=
      mul_le_mul_of_nonneg_right hup (by positivity)
    have h2 : 3 / (2 * (j : ℝ) + 3) * (2 * (j : ℝ) / 3) ≤ 1 := by
      rw [div_mul_div_comm, div_le_one (by positivity)]; nlinarith
    have h3 : 0 ≤ 2 / s := by positivity
    linarith

/-- Paper: the conclusion `r_ℓ^2 ∼ 3/(2ℓ)` stated after `eq:main-radius`
(exact_sampling_networks.tex, before `thm:main-depth`) for the zero-bias
unit-norm radii. -/
theorem radius_asymptotic :
    Tendsto (fun j : ℕ => R j ^ 2 * (2 * (j : ℝ) / 3)) atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / ε ^ 2)
  refine ⟨N + 1, fun j hj => ?_⟩
  have hj1 : 1 ≤ j := by omega
  have hb := radius_asymptotic_bound j hj1
  rw [Real.dist_eq]
  have hjN : (N : ℝ) + 1 ≤ j := by exact_mod_cast hj
  have hs : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hlt : 2 / Real.sqrt j < ε := by
    rw [div_lt_iff₀ hs]
    have h4 : 4 / ε ^ 2 < j := by linarith
    have h5 : (2 / ε) ^ 2 < Real.sqrt j ^ 2 := by
      rw [Real.sq_sqrt (by positivity), div_pow]; linarith
    have h6 : 2 / ε < Real.sqrt j := by
      exact lt_of_pow_lt_pow_left₀ 2 hs.le h5
    rw [div_lt_iff₀ hε] at h6
    linarith
  linarith

/-- Paper: `cor:new-integer-score` (tanh_new_critical.tex) and `sec:conf-open`
(conference.tex): a factory whose output `Y ∈ [-1,1]` has mean
`G_ρ(z) = tanh(ρz)/tanh ρ` and whose stopped transcript satisfies the score
identity `G_ρ'(0) = E_0[Y S_T]` and the isometry `E_0 S_T^2 = E_0 T` (the
conclusions of `lem:new-finite-score`, taken as hypotheses) uses
`E_0 T ≥ 3ρ coth ρ - 2 ≥ 1 + ρ^2 - ρ^4/6` source requests, for `0 < ρ ≤ 1`. -/
theorem normalized_factory_cost {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (Y : Ω → ℝ) (S : Ω → ℤ) (T : Ω → ℝ) (ρ : ℝ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hY : ∀ ω, |Y ω| ≤ 1)
    (hYm : MeasureTheory.AEStronglyMeasurable Y μ)
    (hSm : MeasureTheory.AEStronglyMeasurable (fun ω => (S ω : ℝ)) μ)
    (hS2 : MeasureTheory.Integrable (fun ω => (S ω : ℝ) ^ 2) μ) (fd : ℝ)
    (hfd : HasDerivAt (fun z => Real.tanh (ρ * z) / Real.tanh ρ) fd 0)
    (hscore : fd = ∫ ω, Y ω * S ω ∂μ)
    (hiso : ∫ ω, T ω ∂μ = ∫ ω, (S ω : ℝ) ^ 2 ∂μ) :
    3 * (ρ / Real.tanh ρ) - 2 ≤ ∫ ω, T ω ∂μ ∧ 1 + ρ ^ 2 - ρ ^ 4 / 6 ≤ ∫ ω, T ω ∂μ := by
  have hfd' : fd = ρ / Real.tanh ρ := hfd.unique (hasDerivAt_normalized_tanh ρ)
  have h := integer_score_bound μ Y S T fd 1 hY hYm hSm hS2 hscore hiso
  have hpos : 0 < ρ / Real.tanh ρ := div_pos hρ (tanh_pos hρ)
  rw [hfd', abs_of_pos hpos] at h
  norm_num at h
  have h2 := (score_cost_expansion hρ hρ1).1
  constructor <;> linarith

/-- Paper: `eq:main-radius` (exact_sampling_networks.tex), proof: the bound
`coth^2 u ≤ 1 + u^{-2}`, in the form `u^2/(1 + u^2) ≤ tanh^2 u`. -/
theorem tanh_sq_ge {x : ℝ} (hx : 0 < x) : x ^ 2 / (1 + x ^ 2) ≤ Real.tanh x ^ 2 := by
  have hs : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx.le
  have hc : Real.cosh x ^ 2 = 1 + Real.sinh x ^ 2 := Real.cosh_sq' x
  rw [Real.tanh_eq_sinh_div_cosh, div_pow, hc, div_le_div_iff₀ (by positivity) (by positivity)]
  have : x ^ 2 ≤ Real.sinh x ^ 2 := pow_le_pow_left₀ hx.le hs 2
  nlinarith

/-- Paper: the left half of `eq:main-radius` (exact_sampling_networks.tex):
`1/(ℓ+1) ≤ r_ℓ^2`. -/
theorem R_sq_ge (j : ℕ) : 1 / ((j : ℝ) + 1) ≤ R j ^ 2 := by
  induction j with
  | zero => rw [R_zero]; norm_num
  | succ j ih =>
    rw [R_succ]
    have h := tanh_sq_ge (R_pos j)
    have hp : 0 < R j ^ 2 := by have := R_pos j; positivity
    have hmono : 1 / (((j + 1 : ℕ) : ℝ) + 1) ≤ R j ^ 2 / (1 + R j ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      rw [div_le_iff₀ (by positivity)] at ih
      push_cast
      nlinarith
    linarith

/-- Paper: `eq:main-radius` (exact_sampling_networks.tex):
`1/(ℓ+1) ≤ r_ℓ^2 ≤ 3/(2ℓ+3)`. -/
theorem main_radius_bounds (j : ℕ) : 1 / ((j : ℝ) + 1) ≤ R j ^ 2 ∧ R j ^ 2 ≤ 3 / (2 * j + 3) :=
  ⟨R_sq_ge j, R_sq_le j⟩

/-- Paper: `prop:new-local-obstruction` (tanh_new_critical.tex), with the local
bounds derived rather than assumed. For each layer `j < D` the local factory for
`G_{R_j}` is modelled on a probability space by an output `Y_j ∈ [-1,1]`, an
integer stopped score `S_j` and a request count `T_j`, satisfying the score
identity and the isometry of `lem:new-finite-score` (hypotheses `hscore`,
`hiso`). The remaining stand-in `hN` is the predictable charging of fresh
recursive calls: the expected number `N` of bottom requests is at least
`R_D ∏_j E T_j`. Then `N > D/4`. -/
theorem local_obstruction_from_scores (D : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → MeasureTheory.Measure Ω) [∀ j, MeasureTheory.IsProbabilityMeasure (μ j)]
    (Y : ℕ → Ω → ℝ) (S : ℕ → Ω → ℤ) (T : ℕ → Ω → ℝ)
    (hY : ∀ j ω, |Y j ω| ≤ 1) (hYm : ∀ j, MeasureTheory.AEStronglyMeasurable (Y j) (μ j))
    (hSm : ∀ j, MeasureTheory.AEStronglyMeasurable (fun ω => (S j ω : ℝ)) (μ j))
    (hS2 : ∀ j, MeasureTheory.Integrable (fun ω => (S j ω : ℝ) ^ 2) (μ j))
    (hscore : ∀ j < D, amp j = ∫ ω, Y j ω * S j ω ∂(μ j))
    (hiso : ∀ j < D, ∫ ω, T j ω ∂(μ j) = ∫ ω, (S j ω : ℝ) ^ 2 ∂(μ j))
    (N : ℝ) (hN : R D * ∏ j ∈ range D, ∫ ω, T j ω ∂(μ j) ≤ N) :
    Real.exp (-(3 / 4)) * (1 / R D ^ 2) ≤ N ∧
      Real.exp (-(3 / 4)) * (1 + 2 * D / 3) ≤ N ∧ (D : ℝ) / 4 < N := by
  refine local_obstruction D (fun j => ∫ ω, T j ω ∂(μ j)) N (fun j hj => ?_) hN
  have hj' := mem_range.mp hj
  have h := (normalized_factory_cost (μ j) (Y j) (S j) (T j) (R j) (R_pos j) (R_le_one j)
    (hY j) (hYm j) (hSm j) (hS2 j) (amp j) (amp_eq_normalized_derivative j)
    (hscore j hj') (hiso j hj')).1
  rw [← amp_eq] at h
  exact h

end ExactSampling.NewCriticalLemmas
