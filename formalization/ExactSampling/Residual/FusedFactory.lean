import Mathlib

/-!
# The fused first-vote factory

This module formalizes the exactness and cost identities of the fused factory of
`tanh_fused.tex` (section `app:fused`) and the polynomial estimates behind the
fixed potential bound and the constants of the depth theorems.

Formalized here:
* `lem:fusedfactory`: conditioning on the first source sign, the majority, OR,
  and signed-tail continuations change the mean by exactly `(1-z^2)(A+Bz)` and
  `(1-z^2) h_k z^k`; the complete factory (`factoryMean`), with the reserved tail
  mass `e_0`, the proposal `2^{1-k}` and the acceptance probabilities, has mean
  `z + (1-z^2) ∑_k h_k z^k` (`factoryMean_eq`), which is `F(z)` once the expansion
  `H = (F - z)/(1 - z^2) = ∑_k h_k z^k` is supplied (`factoryMean_eq_F`); the exact
  source-count formula `1 + E(A,B,z) + ∑_{k≥2} |h_k| (2 + k(1-z^2))`; the Lipschitz
  constants `2` and `3` of `E`; the identity `E(uρ^2, ρ^2/3, z) = ρ^2 e(u,z)`; the
  arity bound `eq:fusedarity` from the coefficient bounds; validity and
  nonnegativity of all category probabilities;
* `lem:fusedlocal`: the coefficient bound `C_η(u,z) ≤ 17/16` for `0 < η ≤ 1/64`,
  `|z| ≤ 1` and every real `u`, via the certificate polynomial `P_η`, and the
  numerical value `2295289 < 2^{22}` of the fourth-order coefficient;
* `lem:fusedcoeff`, elementary part: `x coth x ≤ 1 + x^2/3` from the series of
  `(1 + x^2/3) sinh x - x cosh x`, `0 ≤ h_0 ≤ 4ρ^2`, `h_1 ≤ ρ^2/3`, and `h_1 ≥ 0`
  (from `tanh ρ ≤ ρ - 16ρ^5` for `ρ ≤ 1/32`);
* the numerical constants of `thm:fusedcritical` and `prop:fusedrate`.

Not formalized: the complex-analytic part of `lem:fusedcoeff`. The expansion
`H(z) = ∑_k h_k z^k`, the tail bound `|h_k| ≤ 200 ρ^4 2^{-k}`, and the estimates
`|h_0 - uρ^2| ≤ 2ρ^4`, `|h_1 - ρ^2/3| ≤ 100ρ^4` enter as declared stand-in
hypotheses (`factoryMean_eq_F`, `fused_arity_bound`). Also not formalized: the
Taylor expansion giving `log W_f ≤ C_η ρ^2 + (...) ρ^4`, almost-sure termination, and
the probabilistic weighted charging.
-/

open Real Finset

namespace ExactSampling.FusedFactory

/-! ## Exactness of the factory (`lem:fusedfactory`) -/

/-- Paper: `lem:fusedfactory` (tanh_fused.tex), "conditioning on `X_1`, the
majority and OR continuations change its mean by precisely `(1-z^2)(A+Bz)`".
With `p = (1+z)/2`, after `X_1 = +1` a majority-of-three continuation is chosen with
probability `2(B-A)_+` (mean `p + (1-p)z`); after `X_1 = -1` a majority
continuation is chosen with probability `2B + 2 min(A,B)` (mean `pz - (1-p)`) and an
OR continuation with probability `2(A-B)_+` (mean `z`); otherwise `X_1` is
returned. The resulting mean is `z + (1 - z^2)(A + Bz)` for all real `A, B`. -/
theorem first_vote_mean (A B z : ℝ) :
    (1 + z) / 2 * ((1 - 2 * max (B - A) 0) * 1 +
        2 * max (B - A) 0 * ((1 + z) / 2 + (1 - (1 + z) / 2) * z)) +
      (1 - (1 + z) / 2) * ((1 - (2 * B + 2 * min A B) - 2 * max (A - B) 0) * (-1) +
        (2 * B + 2 * min A B) * ((1 + z) / 2 * z - (1 - (1 + z) / 2)) +
        2 * max (A - B) 0 * z) =
      z + (1 - z ^ 2) * (A + B * z) := by
  rcases le_total A B with h | h
  · rw [max_eq_left (by linarith), min_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (by linarith), min_eq_right h, max_eq_left (by linarith)]
    ring

/-- Paper: `lem:fusedfactory` (tanh_fused.tex): a signed tail component reads
`X_2`; if `X_1 = X_2` it returns the common sign, otherwise the chosen sign `σ`
times the product of `k` fresh signs. Its mean is `z + σ (1-z^2) z^k / 2`. -/
theorem tail_component_mean (z σ : ℝ) (k : ℕ) :
    (1 + z) / 2 * ((1 + z) / 2 * 1 + (1 - (1 + z) / 2) * (σ * z ^ k)) +
      (1 - (1 + z) / 2) * ((1 - (1 + z) / 2) * (-1) + (1 + z) / 2 * (σ * z ^ k)) =
      z + σ * (1 - z ^ 2) * z ^ k / 2 := by
  ring

/-- Paper: `lem:fusedfactory` (tanh_fused.tex): the positive and negative tail
components have unconditional probabilities `2(h_k)_+` and `2(-h_k)_+`; their total
change of mean, relative to returning `X_1`, is `(1 - z^2) h_k z^k`. -/
theorem tail_pair_change (z hk : ℝ) (k : ℕ) :
    2 * max hk 0 * ((1 - z ^ 2) * z ^ k / 2) +
      2 * max (-hk) 0 * (-(1 - z ^ 2) * z ^ k / 2) = (1 - z ^ 2) * hk * z ^ k := by
  rcases le_total 0 hk with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring

/-- Paper: the tail proposal before `lem:fusedfactory` (tanh_fused.tex): with the
reserved mass `e_0`, the proposal `Pr(K = k) = 2^{1-k}` and the acceptance
probability `(h_k)_+/(e_0 2^{-k})`, the unconditional mass of a positive component is
`e_0 2^{1-k} (h_k)_+/(e_0 2^{-k}) = 2 (h_k)_+`; here `k = j + 2`. -/
theorem tail_category_mass (e0 x : ℝ) (he0 : 0 < e0) (j : ℕ) :
    e0 * (1 / 2) ^ (j + 1) * (max x 0 / (e0 * (1 / 2) ^ (j + 2))) = 2 * max x 0 := by
  have hw : (1 / 2 : ℝ) ^ (j + 2) = (1 / 2) ^ (j + 1) * (1 / 2) := by rw [← pow_succ]
  have hw0 : (0 : ℝ) < (1 / 2) ^ (j + 1) := by positivity
  rw [hw]
  field_simp

/-- The acceptance probability `x_+/(e_0 2^{-k})` of a tail proposal at `k = j + 2`. -/
noncomputable def tailAccept (e0 x : ℝ) (j : ℕ) : ℝ := max x 0 / (e0 * (1 / 2) ^ (j + 2))

/-- Conditional mean of the tail proposal of the fused factory given `X_1 = x₁`,
`x₁ = ±1`. With probability `2^{1-k}` the index is `k = j + 2`; the positive or
negative component is accepted with probability `tailAccept e0 (±h_k)`; on acceptance
`X_2` is read (it equals `x₁` with probability `(1 + x₁ z)/2`), the common sign is
returned if `X_2 = x₁`, and otherwise `±` the product of `k` fresh signs, of mean
`±z^k`; on rejection `X_1` is returned. -/
noncomputable def tailMean (e0 z : ℝ) (h : ℕ → ℝ) (x₁ : ℝ) : ℝ :=
  ∑' j : ℕ, (1 / 2) ^ (j + 1) *
    (tailAccept e0 (h (j + 2)) j * ((1 + x₁ * z) / 2 * x₁ + (1 - x₁ * z) / 2 * z ^ (j + 2)) +
      tailAccept e0 (-h (j + 2)) j *
        ((1 + x₁ * z) / 2 * x₁ + (1 - x₁ * z) / 2 * -z ^ (j + 2)) +
      (1 - tailAccept e0 (h (j + 2)) j - tailAccept e0 (-h (j + 2)) j) * x₁)

/-- The mean of the complete fused factory of `tanh_fused.tex`, with `A = h_0`,
`B = h_1` and reserved tail mass `e_0`: after `X_1 = +1` a majority continuation with
probability `2(B-A)_+`, the tail proposal with probability `e_0`, and otherwise `X_1`;
after `X_1 = -1` a majority continuation with probability `2B + 2 min(A,B)`, an OR
continuation with probability `2(A-B)_+`, the tail proposal with probability `e_0`,
and otherwise `X_1`. -/
noncomputable def factoryMean (e0 z : ℝ) (h : ℕ → ℝ) : ℝ :=
  (1 + z) / 2 * ((1 - 2 * max (h 1 - h 0) 0 - e0) * 1 +
      2 * max (h 1 - h 0) 0 * ((1 + z) / 2 + (1 - (1 + z) / 2) * z) + e0 * tailMean e0 z h 1) +
    (1 - (1 + z) / 2) * ((1 - (2 * h 1 + 2 * min (h 0) (h 1)) - 2 * max (h 0 - h 1) 0 - e0) *
        (-1) + (2 * h 1 + 2 * min (h 0) (h 1)) * ((1 + z) / 2 * z - (1 - (1 + z) / 2)) +
      2 * max (h 0 - h 1) 0 * z + e0 * tailMean e0 z h (-1))

/-- Auxiliary for `lem:fusedfactory`: the tail proposal changes the conditional mean
given `X_1 = x₁` by `(1 - x₁ z)(∑ h_k z^k - x₁ ∑ |h_k|)/e_0`. -/
theorem tailMean_eq (e0 z S : ℝ) (h : ℕ → ℝ) (he0 : 0 < e0)
    (htail : ∀ j : ℕ, |h (j + 2)| ≤ e0 * (1 / 2) ^ (j + 2))
    (hS : HasSum (fun j : ℕ => h (j + 2) * z ^ (j + 2)) S) (x₁ : ℝ) :
    e0 * tailMean e0 z h x₁ = e0 * x₁ + (1 - x₁ * z) * (S - x₁ * ∑' j : ℕ, |h (j + 2)|) := by
  have hgeo2 : Summable (fun j : ℕ => e0 * (1 / 2 : ℝ) ^ (j + 2)) := by
    have := (summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).mul_left (e0 * (1 / 2) ^ 2)
    refine this.congr fun j => ?_
    rw [pow_add]
    ring
  have hsa : Summable (fun j : ℕ => |h (j + 2)|) :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) htail hgeo2
  have hgeo : HasSum (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1)) 1 := by
    have := (hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (1 / 2)
    convert this using 1
    · funext j
      rw [pow_succ]
      ring
    · norm_num
  have hterm : ∀ j : ℕ, e0 * ((1 / 2) ^ (j + 1) *
      (tailAccept e0 (h (j + 2)) j * ((1 + x₁ * z) / 2 * x₁ + (1 - x₁ * z) / 2 * z ^ (j + 2)) +
        tailAccept e0 (-h (j + 2)) j *
          ((1 + x₁ * z) / 2 * x₁ + (1 - x₁ * z) / 2 * -z ^ (j + 2)) +
        (1 - tailAccept e0 (h (j + 2)) j - tailAccept e0 (-h (j + 2)) j) * x₁)) =
      e0 * x₁ * (1 / 2) ^ (j + 1) +
        (1 - x₁ * z) * (h (j + 2) * z ^ (j + 2) - x₁ * |h (j + 2)|) := by
    intro j
    have hw : (1 / 2 : ℝ) ^ (j + 2) = (1 / 2) ^ (j + 1) * (1 / 2) := by rw [← pow_succ]
    have hw0 : (0 : ℝ) < (1 / 2) ^ (j + 1) := by positivity
    unfold tailAccept
    rw [hw]
    rcases le_total 0 (h (j + 2)) with hh | hh
    · rw [max_eq_left hh, max_eq_right (by linarith), abs_of_nonneg hh]
      field_simp
      ring
    · rw [max_eq_right hh, max_eq_left (by linarith), abs_of_nonpos hh]
      field_simp
      ring
  have hall : HasSum (fun j : ℕ => e0 * x₁ * (1 / 2) ^ (j + 1) +
      (1 - x₁ * z) * (h (j + 2) * z ^ (j + 2) - x₁ * |h (j + 2)|))
      (e0 * x₁ * 1 + (1 - x₁ * z) * (S - x₁ * ∑' j : ℕ, |h (j + 2)|)) :=
    (hgeo.mul_left (e0 * x₁)).add ((hS.sub (hsa.hasSum.mul_left x₁)).mul_left (1 - x₁ * z))
  unfold tailMean
  rw [← tsum_mul_left, tsum_congr hterm, hall.tsum_eq, mul_one]

/-- Paper: `lem:fusedfactory` (tanh_fused.tex), the mean of the whole factory.
If `|h_k| ≤ e_0 2^{-k}` for `k ≥ 2` and `∑_{k≥2} h_k z^k = S`, the factory, with all
its categories and the tail proposal, has mean `z + (1-z^2)(h_0 + h_1 z + S)`. -/
theorem factoryMean_eq (e0 z S : ℝ) (h : ℕ → ℝ) (he0 : 0 < e0)
    (htail : ∀ j : ℕ, |h (j + 2)| ≤ e0 * (1 / 2) ^ (j + 2))
    (hS : HasSum (fun j : ℕ => h (j + 2) * z ^ (j + 2)) S) :
    factoryMean e0 z h = z + (1 - z ^ 2) * (h 0 + h 1 * z + S) := by
  have t1 := tailMean_eq e0 z S h he0 htail hS 1
  have t2 := tailMean_eq e0 z S h he0 htail hS (-1)
  have hfv := first_vote_mean (h 0) (h 1) z
  unfold factoryMean
  linear_combination hfv + (1 + z) / 2 * t1 + (1 - (1 + z) / 2) * t2

/-- `G(z) = tanh(ρz)/tanh ρ` of `app:fused`. -/
noncomputable def Gfun (ρ z : ℝ) : ℝ := Real.tanh (ρ * z) / Real.tanh ρ

/-- `F(z) = (G(z) + c)/(1 + c G(z))` with `c = tanh a · tanh ρ`, the target of the fused
factory in `app:fused`. -/
noncomputable def Ffun (ρ a z : ℝ) : ℝ :=
  (Gfun ρ z + Real.tanh a * Real.tanh ρ) / (1 + Real.tanh a * Real.tanh ρ * Gfun ρ z)

/-- `H(z) = (F(z) - z)/(1 - z^2)` of `app:fused`. -/
noncomputable def Hfun (ρ a z : ℝ) : ℝ := (Ffun ρ a z - z) / (1 - z ^ 2)

/-- Paper: `lem:fusedfactory` (tanh_fused.tex): "the factory terminates almost
surely and has mean `F(z)`". The analytic part of `lem:fusedcoeff` enters as two
declared stand-ins: the expansion `H(z) = ∑_k h_k z^k` for `|z| < 1` and the tail
bound `|h_k| ≤ e_0 2^{-k}` with `e_0 = 200ρ^4`. At `z = ±1` the identity holds because
`F(±1) = ±1`. -/
theorem factoryMean_eq_F (ρ a z e0 : ℝ) (h : ℕ → ℝ) (hρ : 0 < ρ) (hz : |z| ≤ 1)
    (he0 : 0 < e0) (htail : ∀ j : ℕ, |h (j + 2)| ≤ e0 * (1 / 2) ^ (j + 2))
    (hH : |z| < 1 → HasSum (fun k : ℕ => h k * z ^ k) (Hfun ρ a z)) :
    factoryMean e0 z h = Ffun ρ a z := by
  have hq : 0 < Real.tanh ρ := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hρ) (Real.cosh_pos ρ)
  have hc1 : |Real.tanh a * Real.tanh ρ| < 1 := by
    rw [abs_mul]
    have h1 := Real.abs_tanh_lt_one a
    have h2 := Real.abs_tanh_lt_one ρ
    have : |Real.tanh a| * |Real.tanh ρ| < 1 * 1 :=
      mul_lt_mul'' h1 h2 (abs_nonneg _) (abs_nonneg _)
    linarith
  have hc := abs_lt.mp hc1
  rcases lt_or_eq_of_le hz with hlt | heq
  · have hH' := hH hlt
    have h2 := (hasSum_nat_add_iff' 2).mpr hH'
    simp only [sum_range_succ, sum_range_zero, pow_zero, pow_one, mul_one, zero_add] at h2
    rw [factoryMean_eq e0 z _ h he0 htail h2]
    have hz2 : 1 - z ^ 2 ≠ 0 := by
      have := abs_lt.mp hlt
      nlinarith
    unfold Hfun
    field_simp
    ring
  · -- `z = ±1`: the tail series converges absolutely and `F(±1) = ±1`
    have hsum : Summable (fun j : ℕ => h (j + 2) * z ^ (j + 2)) := by
      have hz1 : ∀ j : ℕ, |z ^ (j + 2)| = 1 := fun j => by rw [abs_pow, heq, one_pow]
      refine Summable.of_norm_bounded (g := fun j : ℕ => e0 * (1 / 2) ^ (j + 2)) ?_ ?_
      · exact ((summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
          (by norm_num)).mul_left (e0 * (1 / 2) ^ 2)).congr fun j => by rw [pow_add]; ring
      · intro j
        rw [Real.norm_eq_abs, abs_mul, hz1, mul_one]
        exact htail j
    rw [factoryMean_eq e0 z _ h he0 htail hsum.hasSum]
    have hz2 : z ^ 2 = 1 := by rw [← sq_abs, heq, one_pow]
    rw [hz2, sub_self, zero_mul, add_zero]
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp heq with h1 | h1
    · rw [h1]
      unfold Ffun Gfun
      rw [mul_one, div_self hq.ne']
      have : 1 + Real.tanh a * Real.tanh ρ * 1 ≠ 0 := by linarith
      rw [eq_div_iff this]
      ring
    · rw [h1]
      unfold Ffun Gfun
      rw [mul_neg_one, Real.tanh_neg, neg_div, div_self hq.ne']
      have : 1 + Real.tanh a * Real.tanh ρ * -1 ≠ 0 := by linarith
      rw [eq_div_iff this]
      ring

/-! ## Source counts (`lem:fusedfactory`) -/

/-- The first-two-coefficient cost `E(A,B,z) = B(3-z^2) - 2Az + (A-B)_+(1+z)`. -/
noncomputable def costE (A B z : ℝ) : ℝ := B * (3 - z ^ 2) - 2 * A * z + max (A - B) 0 * (1 + z)

/-- Paper: `lem:fusedfactory` (tanh_fused.tex): conditional on a positive first
sign a majority continuation uses `(3-z)/2` further signs, after a negative one
`(3+z)/2`, and the OR continuation one. The expected additional count is
`E(A, B, z)` for all real `A, B`. -/
theorem first_vote_cost (A B z : ℝ) :
    (1 + z) / 2 * (2 * max (B - A) 0 * ((3 - z) / 2)) +
      (1 - (1 + z) / 2) * ((2 * B + 2 * min A B) * ((3 + z) / 2) + 2 * max (A - B) 0 * 1) =
      costE A B z := by
  unfold costE
  rcases le_total A B with h | h
  · rw [max_eq_left (by linarith), min_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (by linarith), min_eq_right h, max_eq_left (by linarith)]
    ring

/-- Paper: `lem:fusedfactory` (tanh_fused.tex): a tail component uses, beyond
the first sign, `1 + k(1 - z^2)/2` signs on average; with unconditional
probability `2|h_k|` this contributes `|h_k| (2 + k(1-z^2))`. -/
theorem tail_cost (z hk : ℝ) (k : ℕ) :
    (2 * max hk 0 + 2 * max (-hk) 0) * (1 + (1 - z ^ 2) / 2 * k) =
      |hk| * (2 + k * (1 - z ^ 2)) := by
  rcases le_total 0 hk with h | h
  · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]
    ring
  · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]
    ring

/-- Auxiliary: for `1 + z ≥ 0`, `E` is the maximum of the two affine functions
`B(2 - z - z^2) + A(1 - z)` and `B(3 - z^2) - 2Az`. -/
theorem costE_eq_max (A B z : ℝ) (hz : 0 ≤ 1 + z) :
    costE A B z = max (B * (2 - z - z ^ 2) + A * (1 - z)) (B * (3 - z ^ 2) - 2 * A * z) := by
  unfold costE
  rcases le_total B A with h | h
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ A - B), max_eq_left (by nlinarith)]
    ring
  · rw [max_eq_right (by linarith : A - B ≤ 0), max_eq_right (by nlinarith)]
    ring

/-- Paper: `lem:fusedfactory` (tanh_fused.tex): `E` has Lipschitz constant `2`
in `A` and `3` in `B` for `|z| ≤ 1`. -/
theorem costE_lipschitz (A B A' B' z : ℝ) (hz : |z| ≤ 1) :
    |costE A B z - costE A' B' z| ≤ 2 * |A - A'| + 3 * |B - B'| := by
  have hz' := abs_le.mp hz
  have h1z : 0 ≤ 1 + z := by linarith
  rw [costE_eq_max A B z h1z, costE_eq_max A' B' z h1z]
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · have e : B * (2 - z - z ^ 2) + A * (1 - z) - (B' * (2 - z - z ^ 2) + A' * (1 - z)) =
        (B - B') * (2 - z - z ^ 2) + (A - A') * (1 - z) := by ring
    rw [e]
    have q1 : 0 ≤ 2 - z - z ^ 2 := by nlinarith
    have q2 : 2 - z - z ^ 2 ≤ 3 := by nlinarith
    have q3 : 0 ≤ 1 - z := by linarith
    have q4 : 1 - z ≤ 2 := by linarith
    calc |(B - B') * (2 - z - z ^ 2) + (A - A') * (1 - z)|
        ≤ |(B - B') * (2 - z - z ^ 2)| + |(A - A') * (1 - z)| := abs_add_le _ _
      _ = |B - B'| * (2 - z - z ^ 2) + |A - A'| * (1 - z) := by
          rw [abs_mul, abs_mul, abs_of_nonneg q1, abs_of_nonneg q3]
      _ ≤ |B - B'| * 3 + |A - A'| * 2 :=
          add_le_add (mul_le_mul_of_nonneg_left q2 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left q4 (abs_nonneg _))
      _ = 2 * |A - A'| + 3 * |B - B'| := by ring
  · have e : B * (3 - z ^ 2) - 2 * A * z - (B' * (3 - z ^ 2) - 2 * A' * z) =
        (B - B') * (3 - z ^ 2) - 2 * (A - A') * z := by ring
    rw [e]
    have q1 : 0 ≤ 3 - z ^ 2 := by nlinarith
    have q2 : 3 - z ^ 2 ≤ 3 := by nlinarith
    calc |(B - B') * (3 - z ^ 2) - 2 * (A - A') * z|
        ≤ |(B - B') * (3 - z ^ 2)| + |2 * (A - A') * z| := abs_sub _ _
      _ = |B - B'| * (3 - z ^ 2) + 2 * |A - A'| * |z| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg q1, abs_two]
      _ ≤ |B - B'| * 3 + 2 * |A - A'| * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left q2 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hz (by positivity))
      _ = 2 * |A - A'| + 3 * |B - B'| := by ring

/-- The piecewise function `e(u,z)` of `eq:fusedarity`. -/
noncomputable def eFun (u z : ℝ) : ℝ :=
  if u ≤ 1 / 3 then 1 - z ^ 2 / 3 - 2 * u * z else 2 / 3 - z / 3 - z ^ 2 / 3 + u * (1 - z)

/-- Paper: proof of `lem:fusedfactory` (tanh_fused.tex): substitution of
`(A, B) = (uρ^2, ρ^2/3)` gives `E = ρ^2 e(u, z)`. -/
theorem costE_main (ρ u z : ℝ) : costE (u * ρ ^ 2) (ρ ^ 2 / 3) z = ρ ^ 2 * eFun u z := by
  unfold costE eFun
  have hρ : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  split_ifs with h
  · rw [max_eq_right (by nlinarith)]
    ring
  · rw [max_eq_left (by nlinarith)]
    ring

/-- Auxiliary for `eq:fusedarity`: `∑_{j≥0} 2^{-(j+2)} (j + 4) = 5/2`, i.e.
`∑_{k≥2} (k+2) 2^{-k} = 5/2`. -/
theorem hasSum_tail_weights :
    HasSum (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 2) * ((j : ℝ) + 4)) (5 / 2) := by
  have h1 : HasSum (fun j : ℕ => (j : ℝ) * (1 / 2) ^ j) 2 := by
    have := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := 1 / 2) (by norm_num)
    convert this using 1
    norm_num
  have h2 : HasSum (fun j : ℕ => (1 / 2 : ℝ) ^ j) 2 := by
    have := hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    convert this using 1
    norm_num
  have h3 := (h1.add (h2.mul_left 4)).mul_left (1 / 4)
  convert h3 using 1
  · funext j
    rw [pow_add]
    ring
  · norm_num

/-- Paper: `eq:fusedarity` in `lem:fusedfactory` (tanh_fused.tex). Assume the
coefficient bounds of `lem:fusedcoeff`: `|h_0 - uρ^2| ≤ 2ρ^4`,
`|h_1 - ρ^2/3| ≤ 100ρ^4`, and `|h_k| ≤ 200ρ^4 2^{-k}` for `k ≥ 2` (indexed here by
`k = j + 2`). Then the tail is summable and the exact source count satisfies
`A_f = 1 + E(h_0, h_1, z) + ∑_{k≥2} |h_k|(2 + k(1-z^2)) ≤ 1 + ρ^2 e(u,z) + 1000ρ^4`;
the proof gives `804ρ^4`. -/
theorem fused_arity_bound (ρ u z : ℝ) (h : ℕ → ℝ) (hz : |z| ≤ 1)
    (h0 : |h 0 - u * ρ ^ 2| ≤ 2 * ρ ^ 4) (h1 : |h 1 - ρ ^ 2 / 3| ≤ 100 * ρ ^ 4)
    (htail : ∀ j : ℕ, |h (j + 2)| ≤ 200 * ρ ^ 4 * (1 / 2) ^ (j + 2)) :
    Summable (fun j : ℕ => |h (j + 2)| * (2 + ((j : ℝ) + 2) * (1 - z ^ 2))) ∧
      1 + costE (h 0) (h 1) z +
          ∑' j : ℕ, |h (j + 2)| * (2 + ((j : ℝ) + 2) * (1 - z ^ 2)) ≤
        1 + ρ ^ 2 * eFun u z + 1000 * ρ ^ 4 := by
  have hz2 : 0 ≤ 1 - z ^ 2 := by nlinarith [abs_le.mp hz, sq_abs z]
  have hz3 : 1 - z ^ 2 ≤ 1 := by nlinarith
  have hρ4 : 0 ≤ ρ ^ 4 := by positivity
  have hle : ∀ j : ℕ, |h (j + 2)| * (2 + ((j : ℝ) + 2) * (1 - z ^ 2)) ≤
      200 * ρ ^ 4 * ((1 / 2 : ℝ) ^ (j + 2) * ((j : ℝ) + 4)) := by
    intro j
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have e1 : 2 + ((j : ℝ) + 2) * (1 - z ^ 2) ≤ (j : ℝ) + 4 := by nlinarith
    have e2 : 0 ≤ 2 + ((j : ℝ) + 2) * (1 - z ^ 2) := by positivity
    calc |h (j + 2)| * (2 + ((j : ℝ) + 2) * (1 - z ^ 2))
        ≤ (200 * ρ ^ 4 * (1 / 2) ^ (j + 2)) * ((j : ℝ) + 4) :=
          mul_le_mul (htail j) e1 e2 (by positivity)
      _ = 200 * ρ ^ 4 * ((1 / 2 : ℝ) ^ (j + 2) * ((j : ℝ) + 4)) := by ring
  have hs2 := hasSum_tail_weights.mul_left (200 * ρ ^ 4)
  have hs : Summable (fun j : ℕ => |h (j + 2)| * (2 + ((j : ℝ) + 2) * (1 - z ^ 2))) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hle hs2.summable
  refine ⟨hs, ?_⟩
  have htsum : ∑' j : ℕ, |h (j + 2)| * (2 + ((j : ℝ) + 2) * (1 - z ^ 2)) ≤
      200 * ρ ^ 4 * (5 / 2) := by
    rw [← hs2.tsum_eq]
    exact Summable.tsum_le_tsum hle hs hs2.summable
  have hE := costE_lipschitz (h 0) (h 1) (u * ρ ^ 2) (ρ ^ 2 / 3) z hz
  rw [costE_main] at hE
  have hE' := (abs_le.mp hE).2
  linarith

/-- Paper: `lem:fusedfactory` and the construction before it (tanh_fused.tex):
with `0 ≤ A ≤ 4ρ^2`, `0 ≤ B ≤ ρ^2/3`, `e_0 = 200ρ^4` and `ρ ≤ 1/32`, every category
probability is nonnegative, the categories after either first sign total at most
`9ρ^2 + 200ρ^4 < 1/100`, and the remaining mass ("otherwise return `X_1`") is
nonnegative. -/
theorem fused_categories_valid (ρ A B : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 32)
    (hA0 : 0 ≤ A) (hA : A ≤ 4 * ρ ^ 2) (hB0 : 0 ≤ B) (hB : B ≤ ρ ^ 2 / 3) :
    0 ≤ 2 * max (B - A) 0 ∧ 0 ≤ 2 * B + 2 * min A B ∧ 0 ≤ 2 * max (A - B) 0 ∧
      0 ≤ 200 * ρ ^ 4 ∧
      2 * max (B - A) 0 + 200 * ρ ^ 4 ≤ 9 * ρ ^ 2 + 200 * ρ ^ 4 ∧
      (2 * B + 2 * min A B) + 2 * max (A - B) 0 + 200 * ρ ^ 4 ≤ 9 * ρ ^ 2 + 200 * ρ ^ 4 ∧
      9 * ρ ^ 2 + 200 * ρ ^ 4 < 1 / 100 ∧
      0 ≤ 1 - 2 * max (B - A) 0 - 200 * ρ ^ 4 ∧
      0 ≤ 1 - (2 * B + 2 * min A B) - 2 * max (A - B) 0 - 200 * ρ ^ 4 := by
  have hρ2 : ρ ^ 2 ≤ 1 / 1024 := by nlinarith
  have h1 : 2 * max (B - A) 0 + 200 * ρ ^ 4 ≤ 9 * ρ ^ 2 + 200 * ρ ^ 4 := by
    have : max (B - A) 0 ≤ ρ ^ 2 / 3 := max_le (by linarith) (by positivity)
    nlinarith
  have h2 : (2 * B + 2 * min A B) + 2 * max (A - B) 0 + 200 * ρ ^ 4 ≤
      9 * ρ ^ 2 + 200 * ρ ^ 4 := by
    rcases le_total A B with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]
      nlinarith
    · rw [min_eq_right h, max_eq_left (by linarith)]
      nlinarith
  have h3 : 9 * ρ ^ 2 + 200 * ρ ^ 4 < 1 / 100 := by
    have hρ4 : ρ ^ 4 ≤ (1 / 1024) ^ 2 := by
      have : ρ ^ 4 = (ρ ^ 2) ^ 2 := by ring
      rw [this]
      exact pow_le_pow_left₀ (sq_nonneg ρ) hρ2 2
    nlinarith
  have hmin : 0 ≤ min A B := le_min hA0 hB0
  refine ⟨by positivity, by positivity, by positivity, by positivity, h1, h2, h3, ?_, ?_⟩
  · linarith
  · linarith

/-- Auxiliary for `lem:fusedcoeff`: `sinh x ≤ x cosh x`, i.e. `tanh x ≤ x`, for
`x ≥ 0`, from the series of `x cosh x - sinh x`. -/
theorem sinh_le_mul_cosh (x : ℝ) (hx : 0 ≤ x) : Real.sinh x ≤ x * Real.cosh x := by
  set T : ℕ → ℝ := fun n => x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) with hT
  have hsinh : HasSum T (Real.sinh x) := Real.hasSum_sinh x
  have hcosh : HasSum (fun n : ℕ => (2 * (n : ℝ) + 1) * T n) (x * Real.cosh x) := by
    have := (Real.hasSum_cosh x).mul_left x
    convert this using 1
    funext n
    simp only [hT]
    rw [Nat.factorial_succ]
    push_cast
    have : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
    rw [pow_succ]
    field_simp
  have hdiff := hcosh.sub hsinh
  have := hdiff.nonneg fun n => by
    have hTn : 0 ≤ T n := by simp only [hT]; positivity
    have : (2 * (n : ℝ) + 1) * T n - T n = 2 * (n : ℝ) * T n := by ring
    rw [this]
    positivity
  linarith

/-- Paper: the tail proposal of the fused factory before `lem:fusedfactory`
(tanh_fused.tex): the
acceptance probabilities `(h_k)_+/(200ρ^4 2^{-k})` and `(-h_k)_+/(200ρ^4 2^{-k})` are
valid and sum to at most one when `|h_k| ≤ 200ρ^4 2^{-k}`, and the proposal
`Pr(K = k) = 2^{1-k}`, `k ≥ 2`, has total mass one. -/
theorem tail_proposal_valid (hk w : ℝ) (hw : 0 < w) (hhk : |hk| ≤ w) :
    0 ≤ max hk 0 / w ∧ 0 ≤ max (-hk) 0 / w ∧ max hk 0 / w + max (-hk) 0 / w ≤ 1 ∧
      HasSum (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1)) 1 := by
  refine ⟨by positivity, by positivity, ?_, ?_⟩
  · rw [← add_div, div_le_one hw]
    rcases le_total 0 hk with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]
      rw [abs_of_nonneg h] at hhk
      linarith
    · rw [max_eq_right h, max_eq_left (by linarith)]
      rw [abs_of_nonpos h] at hhk
      linarith
  · have := (hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (1 / 2)
    convert this using 1
    · funext j
      rw [pow_succ]
      ring
    · norm_num

/-! ## The fixed potential bound (`lem:fusedlocal`) -/

/-- The certificate polynomial `P_η(y)` of the proof of `lem:fusedlocal`. -/
def certificate (η y : ℝ) : ℝ :=
  3 * (1 - y) * (2 * y - 1) ^ 2 + η * (6 - 35 * y + 48 * y ^ 2) + η ^ 2 * (3 - 32 * y)

/-- Paper: proof of `lem:fusedlocal` (tanh_fused.tex): with `y = z^2` and
`d = α - y`, the bound `max_u C_η ≤ 17/16` on the branch `u ≤ 1/3` is equivalent to
`P_η(y) ≥ 0`. -/
theorem potential_certificate_identity (η y : ℝ) (ha : 1 + η ≠ 0) (hd : 1 + η - y ≠ 0) :
    ((17 : ℝ) / 16 -
      (1 - η * y / (3 * (1 + η - y)) +
        y * (1 + 2 * η - y) ^ 2 / (4 * (1 + η) * (1 + η - y)))) *
      (48 * (1 + η) * (1 + η - y)) = certificate η y := by
  unfold certificate
  field_simp
  ring

/-- Paper: proof of `lem:fusedlocal` (tanh_fused.tex), the decomposition for
`y = 1/2 + v`. -/
theorem certificate_right_identity (η v : ℝ) :
    certificate η (1 / 2 + v) =
      6 * v ^ 2 * (1 - 2 * v) + η * (13 * v + 48 * v ^ 2) + η * (1 / 2 - 29 * η) +
        η ^ 2 * (16 - 32 * v) := by
  unfold certificate
  ring

/-- Paper: proof of `lem:fusedlocal` (tanh_fused.tex), the decomposition for
`y = 1/2 - v`. -/
theorem certificate_left_identity (η v : ℝ) :
    certificate η (1 / 2 - v) =
      6 * (v - 13 * η / 12) ^ 2 + 12 * v ^ 3 + 48 * η * v ^ 2 + 32 * η ^ 2 * v +
        η * (1 / 2 - 481 * η / 24) := by
  unfold certificate
  ring

/-- Paper: proof of `lem:fusedlocal` (tanh_fused.tex): `P_η(y) ≥ 0` for
`0 ≤ η ≤ 1/64` and `y ≤ 1` (the paper states it for `0 ≤ y ≤ 1`). -/
theorem certificate_nonneg (η y : ℝ) (he0 : 0 ≤ η) (he1 : η ≤ 1 / 64) (hy1 : y ≤ 1) :
    0 ≤ certificate η y := by
  by_cases hhalf : y ≤ 1 / 2
  · have hv0 : 0 ≤ 1 / 2 - y := by linarith
    have hlast : 0 ≤ 1 / 2 - 481 * η / 24 := by linarith
    have hy : y = 1 / 2 - (1 / 2 - y) := by ring
    rw [hy, certificate_left_identity]
    positivity
  · have hv0 : 0 ≤ y - 1 / 2 := by linarith
    have hfirst : 0 ≤ 1 - 2 * (y - 1 / 2) := by linarith
    have hthird : 0 ≤ 1 / 2 - 29 * η := by linarith
    have hfourth : 0 ≤ 16 - 32 * (y - 1 / 2) := by linarith
    have hy : y = 1 / 2 + (y - 1 / 2) := by ring
    rw [hy, certificate_right_identity]
    positivity

/-- The small-bias branch `C_η(u, z)` for `u ≤ 1/3`. -/
noncomputable def C1 (η u z : ℝ) : ℝ :=
  1 - η * z ^ 2 / (3 * (1 + η - z ^ 2)) - z * (1 + η / (1 + η - z ^ 2)) * u -
    (1 + η) / (1 + η - z ^ 2) * u ^ 2

/-- The large-bias branch `C_η(u, z)` for `u ≥ 1/3`. -/
noncomputable def C2 (η u z : ℝ) : ℝ :=
  2 / 3 - z / 3 - η * z ^ 2 / (3 * (1 + η - z ^ 2)) +
    (1 - η * z / (1 + η - z ^ 2)) * u - (1 + η) / (1 + η - z ^ 2) * u ^ 2

/-- The coefficient `C_η = e(u,z) - u^2 + z b(u,z)/d` of `lem:fusedlocal`, with
`b(u,z) = (1 - z^2)(z/3 + u) - u^2 z` and `d = α - z^2`. -/
noncomputable def Ceta (η u z : ℝ) : ℝ :=
  eFun u z - u ^ 2 + z * ((1 - z ^ 2) * (z / 3 + u) - u ^ 2 * z) / (1 + η - z ^ 2)

/-- Paper: proof of `lem:fusedlocal` (tanh_fused.tex): `C_η` equals the two
displayed branch formulas. -/
theorem Ceta_eq (η u z : ℝ) (hd : 1 + η - z ^ 2 ≠ 0) :
    Ceta η u z = if u ≤ 1 / 3 then C1 η u z else C2 η u z := by
  unfold Ceta C1 C2 eFun
  split_ifs <;> field_simp <;> ring

/-- Paper: proof of `lem:fusedlocal` (tanh_fused.tex), branch `u ≤ 1/3`:
`C_η ≤ 17/16`; completing the square in `u` reduces it to `P_η(z^2) ≥ 0`. In fact
the bound holds for every real `u`. -/
theorem C1_le (η u z : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1 / 64) (hz : |z| ≤ 1) :
    C1 η u z ≤ 17 / 16 := by
  have hy1 : z ^ 2 ≤ 1 := by nlinarith [abs_le.mp hz, sq_abs z]
  set d := 1 + η - z ^ 2 with hd
  have hd0 : 0 < d := by linarith
  have hα : 0 < 1 + η := by linarith
  have key : 17 / 16 - C1 η u z = certificate η (z ^ 2) / (48 * (1 + η) * d) +
      (1 + η) / d * (u + z * (d + η) / (2 * (1 + η))) ^ 2 := by
    unfold C1 certificate
    rw [← hd]
    field_simp
    rw [hd]
    ring
  have h1 : 0 ≤ certificate η (z ^ 2) / (48 * (1 + η) * d) :=
    div_nonneg (certificate_nonneg η _ hη0.le hη1 hy1) (by positivity)
  have h2 : 0 ≤ (1 + η) / d * (u + z * (d + η) / (2 * (1 + η))) ^ 2 := by positivity
  linarith

/-- Paper: proof of `lem:fusedlocal` (tanh_fused.tex), branch `u ≥ 1/3`:
`C_η ≤ 17/16`. Either the unconstrained maximum lies below `1/3` and the boundary
value is the first branch, or `z ≥ -3/5` and the maximum is at most
`67/60 + (30η - 9)/(100α) ≤ 21/20 < 17/16`. -/
theorem C2_le (η u z : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1 / 64) (hz : |z| ≤ 1)
    (hu : 1 / 3 ≤ u) : C2 η u z ≤ 17 / 16 := by
  have hz' := abs_le.mp hz
  have hy1 : z ^ 2 ≤ 1 := by nlinarith [sq_abs z]
  set d := 1 + η - z ^ 2 with hd
  have hd0 : 0 < d := by linarith
  have hα : 0 < 1 + η := by linarith
  rcases le_or_gt (d - η * z) (2 * (1 + η) / 3) with hcase | hcase
  · -- the maximum is attained at the boundary `u = 1/3`
    have hb : C2 η (1 / 3) z = C1 η (1 / 3) z := by
      unfold C1 C2
      rw [← hd]
      field_simp
      ring
    have hdiff : C2 η u z - C2 η (1 / 3) z =
        (u - 1 / 3) / d * ((d - η * z) - (1 + η) * (u + 1 / 3)) := by
      unfold C2
      rw [← hd]
      field_simp
      ring
    have hneg : (u - 1 / 3) / d * ((d - η * z) - (1 + η) * (u + 1 / 3)) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos (div_nonneg (by linarith) hd0.le)
      nlinarith
    have := C1_le η (1 / 3) z hη0 hη1 hz
    linarith
  · -- here `z > -3/5`
    have hz35 : -3 / 5 < z := by
      by_contra hcon
      push Not at hcon
      have h1 : z * (z + η) ≥ 3 / 5 * (3 / 5 - η) := by nlinarith
      have : d - η * z ≤ 2 * (1 + η) / 3 := by
        rw [hd]
        nlinarith
      linarith
    -- completing the square in `u`
    have key : 17 / 16 - C2 η u z =
        (17 / 16 - (2 / 3 - z / 3 - η * z ^ 2 / (3 * d) + (d - η * z) ^ 2 / (4 * (1 + η) * d))) +
          (1 + η) / d * (u - (d - η * z) / (2 * (1 + η))) ^ 2 := by
      unfold C2
      rw [← hd]
      field_simp
      ring
    have hsq : 0 ≤ (1 + η) / d * (u - (d - η * z) / (2 * (1 + η))) ^ 2 := by positivity
    -- the maximal value is at most `11/12 - (1/3 + η/(2α)) z - z^2/(4α)`
    have hM : 2 / 3 - z / 3 - η * z ^ 2 / (3 * d) + (d - η * z) ^ 2 / (4 * (1 + η) * d) ≤
        11 / 12 - (1 / 3 + η / (2 * (1 + η))) * z - z ^ 2 / (4 * (1 + η)) := by
      have e : 2 / 3 - z / 3 - η * z ^ 2 / (3 * d) + (d - η * z) ^ 2 / (4 * (1 + η) * d) =
          11 / 12 - (1 / 3 + η / (2 * (1 + η))) * z - z ^ 2 / (4 * (1 + η)) +
            η * z ^ 2 / d * (η / (4 * (1 + η)) - 1 / 3) := by
        have hdne : d ≠ 0 := hd0.ne'
        field_simp
        rw [hd]
        ring
      rw [e]
      have : η / (4 * (1 + η)) - 1 / 3 ≤ 0 := by
        rw [sub_nonpos, div_le_iff₀ (by positivity)]
        linarith
      have : 0 ≤ η * z ^ 2 / d := by positivity
      nlinarith
    have hQ : 11 / 12 - (1 / 3 + η / (2 * (1 + η))) * z - z ^ 2 / (4 * (1 + η)) ≤ 21 / 20 := by
      have e : 11 / 12 - (1 / 3 + η / (2 * (1 + η))) * z - z ^ 2 / (4 * (1 + η)) =
          (11 * (1 + η) / 3 - (4 * (1 + η) / 3 + 2 * η) * z - z ^ 2) / (4 * (1 + η)) := by
        field_simp
        ring
      rw [e, div_le_iff₀ (by positivity)]
      have hb : 0 ≤ (z + 3 / 5) * ((4 * (1 + η) / 3 + 2 * η) + (z - 3 / 5)) := by
        apply mul_nonneg (by linarith)
        nlinarith
      nlinarith
    linarith

/-- Paper: `lem:fusedlocal` (tanh_fused.tex), "we show `C_η ≤ 17/16` throughout
`0 < η ≤ 1/64`", for `|z| ≤ 1` and every real `u` (the paper uses `u = t/ρ ∈ [0, 4]`). -/
theorem Ceta_le (η u z : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1 / 64) (hz : |z| ≤ 1) :
    Ceta η u z ≤ 17 / 16 := by
  have hy1 : z ^ 2 ≤ 1 := by nlinarith [abs_le.mp hz, sq_abs z]
  rw [Ceta_eq η u z (by linarith)]
  split_ifs with h
  · exact C1_le η u z hη0 hη1 hz
  · exact C2_le η u z hη0 hη1 hz (by linarith)

/-- Paper: proof of `lem:fusedlocal` (tanh_fused.tex): at `η = 1/64` the
fourth-order coefficient `1017 + 1000/η + 1089/(2η^2)` equals `2295289 < 2^{22}`. -/
theorem fused_remainder_constant :
    (1017 : ℝ) + 1000 / (1 / 64) + 1089 / (2 * (1 / 64) ^ 2) = 2295289 ∧
      (2295289 : ℝ) < 2 ^ 22 := by
  constructor <;> norm_num

/-- Paper: `thm:fusedcritical` (tanh_fused.tex): the depth power
`(3/2)(17/16) - 1/2 = 35/32` and the supercritical coefficient `3 · 17/16 = 51/16`. -/
theorem fused_exponents :
    (3 / 2 : ℝ) * (17 / 16) - 1 / 2 = 35 / 32 ∧ (3 : ℝ) * (17 / 16) = 51 / 16 := by
  constructor <;> norm_num

/-! ## `x coth x ≤ 1 + x^2/3` (`lem:fusedcoeff`) -/

/-- Paper: proof of `lem:fusedcoeff` (tanh_fused.tex): the coefficient of
`x^{2k+1}` in `(1 + x^2/3) sinh x - x cosh x` is `4k(k-1)/(3(2k+1)!) ≥ 0`, hence
`x cosh x ≤ (1 + x^2/3) sinh x` for `x ≥ 0`. -/
theorem mul_cosh_le (x : ℝ) (hx : 0 ≤ x) :
    x * Real.cosh x ≤ (1 + x ^ 2 / 3) * Real.sinh x := by
  set T : ℕ → ℝ := fun n => x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) with hT
  have hsinh : HasSum T (Real.sinh x) := Real.hasSum_sinh x
  have hcosh : HasSum (fun n : ℕ => (2 * (n : ℝ) + 1) * T n) (x * Real.cosh x) := by
    have := (Real.hasSum_cosh x).mul_left x
    convert this using 1
    funext n
    simp only [hT]
    rw [Nat.factorial_succ]
    push_cast
    have : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
    rw [pow_succ]
    field_simp
  -- `x^2 sinh x / 3 = ∑_m (2m+1)(2m) T_m / 3`
  have hsq : HasSum (fun m : ℕ => (2 * (m : ℝ) + 1) * (2 * (m : ℝ)) * T m / 3)
      (x ^ 2 * Real.sinh x / 3) := by
    have h1 : HasSum (fun n : ℕ => x ^ 2 * T n / 3) (x ^ 2 * Real.sinh x / 3) :=
      (hsinh.mul_left (x ^ 2)).div_const 3
    have h2 : (fun n : ℕ => x ^ 2 * T n / 3) =
        fun n : ℕ => (2 * ((n + 1 : ℕ) : ℝ) + 1) * (2 * ((n + 1 : ℕ) : ℝ)) * T (n + 1) / 3 := by
      funext n
      simp only [hT]
      have hf : ((2 * (n + 1) + 1).factorial : ℝ) =
          (2 * n + 3) * (2 * n + 2) * ((2 * n + 1).factorial : ℝ) := by
        rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by ring, Nat.factorial_succ,
          Nat.factorial_succ]
        push_cast
        ring
      have hp : x ^ (2 * (n + 1) + 1) = x ^ 2 * x ^ (2 * n + 1) := by
        rw [← pow_add]
        ring_nf
      rw [hf, hp]
      have : ((2 * n + 1).factorial : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    rw [h2] at h1
    rw [← hasSum_nat_add_iff' 1]
    simp only [sum_range_one, Nat.cast_zero, mul_zero, zero_mul, zero_div, sub_zero]
    exact h1
  have hall := (hsinh.add hsq).sub hcosh
  have hterm : ∀ m : ℕ, 0 ≤ T m + (2 * (m : ℝ) + 1) * (2 * (m : ℝ)) * T m / 3 -
      (2 * (m : ℝ) + 1) * T m := by
    intro m
    have hTm : 0 ≤ T m := by simp only [hT]; positivity
    have e : T m + (2 * (m : ℝ) + 1) * (2 * (m : ℝ)) * T m / 3 - (2 * (m : ℝ) + 1) * T m =
        4 * (m : ℝ) * (m - 1) / 3 * T m := by ring
    rw [e]
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp
    · have : (1 : ℝ) ≤ m := by exact_mod_cast hpos
      apply mul_nonneg _ hTm
      apply div_nonneg _ (by norm_num)
      nlinarith
  have := hall.nonneg hterm
  linarith

/-- Paper: proof of `lem:fusedcoeff` (tanh_fused.tex): `ρ/tanh ρ ≤ 1 + ρ^2/3` for
`ρ > 0`. -/
theorem div_tanh_le (ρ : ℝ) (hρ : 0 < ρ) : ρ / Real.tanh ρ ≤ 1 + ρ ^ 2 / 3 := by
  have hs : 0 < Real.sinh ρ := Real.sinh_pos_iff.mpr hρ
  have hc := Real.cosh_pos ρ
  have ht : 0 < Real.tanh ρ := by rw [Real.tanh_eq_sinh_div_cosh]; positivity
  rw [div_le_iff₀ ht, Real.tanh_eq_sinh_div_cosh, mul_div_assoc', le_div_iff₀ hc]
  have := mul_cosh_le ρ hρ.le
  linarith

/-- Paper: `lem:fusedcoeff` (tanh_fused.tex): for `ρ > 0` and `0 ≤ a ≤ 4ρ`, with
`q = tanh ρ`, `t = tanh a` and `c = tq`, the first coefficients `h_0 = c` and
`h_1 = (1 - c^2)ρ/q - 1` satisfy `0 ≤ h_0 ≤ 4ρ^2` and `h_1 ≤ ρ^2/3` (the latter from
`ρ/q ≤ 1 + ρ^2/3`, `div_tanh_le`). -/
theorem fused_first_coefficients (ρ a : ℝ) (hρ : 0 < ρ) (ha0 : 0 ≤ a) (ha : a ≤ 4 * ρ) :
    0 ≤ Real.tanh a * Real.tanh ρ ∧ Real.tanh a * Real.tanh ρ ≤ 4 * ρ ^ 2 ∧
      (1 - (Real.tanh a * Real.tanh ρ) ^ 2) * ρ / Real.tanh ρ - 1 ≤ ρ ^ 2 / 3 := by
  have htb : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.tanh x ∧ Real.tanh x ≤ x := by
    intro x hx
    have hc := Real.cosh_pos x
    rw [Real.tanh_eq_sinh_div_cosh]
    refine ⟨div_nonneg (Real.sinh_nonneg_iff.mpr hx) hc.le, ?_⟩
    rw [div_le_iff₀ hc]
    exact sinh_le_mul_cosh x hx
  obtain ⟨ht0, ht1⟩ := htb a ha0
  obtain ⟨hq0, hq1⟩ := htb ρ hρ.le
  have hq : 0 < Real.tanh ρ := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hρ) (Real.cosh_pos ρ)
  refine ⟨mul_nonneg ht0 hq0, ?_, ?_⟩
  · calc Real.tanh a * Real.tanh ρ ≤ a * ρ := mul_le_mul ht1 hq1 hq0 ha0
      _ ≤ 4 * ρ * ρ := mul_le_mul_of_nonneg_right ha hρ.le
      _ = 4 * ρ ^ 2 := by ring
  · have h1 := div_tanh_le ρ hρ
    have hr : 0 ≤ ρ / Real.tanh ρ := div_nonneg hρ.le hq.le
    have e : (1 - (Real.tanh a * Real.tanh ρ) ^ 2) * ρ / Real.tanh ρ =
        (1 - (Real.tanh a * Real.tanh ρ) ^ 2) * (ρ / Real.tanh ρ) := by ring
    rw [e]
    have : (1 - (Real.tanh a * Real.tanh ρ) ^ 2) * (ρ / Real.tanh ρ) ≤ 1 * (ρ / Real.tanh ρ) :=
      mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (Real.tanh a * Real.tanh ρ)]) hr
    linarith

/-- Auxiliary for `lem:fusedcoeff`: `tanh ρ ≤ ρ - 16ρ^5` for `0 ≤ ρ ≤ 1/32`. With
`y = ρ - 16ρ^5`, the odd series gives `log((1+y)/(1-y)) ≥ 2y + 2y^3/3 ≥ 2ρ`, hence
`e^{2ρ} ≤ (1+y)/(1-y)`, which is `tanh ρ ≤ y`. -/
theorem tanh_le_sub_quintic {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 32) :
    Real.tanh ρ ≤ ρ - 16 * ρ ^ 5 := by
  set y := ρ - 16 * ρ ^ 5 with hy
  have hρ2 : ρ ^ 2 ≤ 1 / 1024 := by nlinarith
  have hρ4 : ρ ^ 4 ≤ 1 / 1024 ^ 2 := by
    have : ρ ^ 4 = (ρ ^ 2) ^ 2 := by ring
    rw [this, show (1 : ℝ) / 1024 ^ 2 = (1 / 1024) ^ 2 by norm_num]
    exact pow_le_pow_left₀ (sq_nonneg ρ) hρ2 2
  have hyρ : 99 / 100 * ρ ≤ y := by
    have : 16 * ρ ^ 5 ≤ 1 / 100 * ρ := by
      have : 16 * ρ ^ 5 = 16 * ρ ^ 4 * ρ := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (by nlinarith) hρ0
    linarith
  have hy0 : 0 ≤ y := by nlinarith
  have hy1 : y < 1 := by nlinarith
  have habs : |y| < 1 := by rw [abs_of_nonneg hy0]; exact hy1
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hle := sum_le_hasSum (range 2) (fun i _ => by positivity) hs
  simp only [sum_range_succ, sum_range_zero, zero_add] at hle
  norm_num at hle
  -- `2ρ ≤ 2y + 2y^3/3`
  have hkey : 2 * ρ ≤ 2 * y + 2 / 3 * y ^ 3 := by
    have h3 : (99 / 100 * ρ) ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ (by positivity) hyρ 3
    have h5 : 48 * ρ ^ 5 ≤ 48 / 1024 * ρ ^ 3 := by
      have : ρ ^ 5 = ρ ^ 2 * ρ ^ 3 := by ring
      rw [this]
      have : 0 ≤ ρ ^ 3 := by positivity
      nlinarith
    have h33 : 0 ≤ ρ ^ 3 := by positivity
    nlinarith
  have hpos : 0 < (1 + y) / (1 - y) := div_pos (by linarith) (by linarith)
  have hexp : Real.exp (2 * ρ) ≤ (1 + y) / (1 - y) := by
    rw [← Real.exp_log hpos, Real.log_div (by linarith) (by linarith)]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [le_div_iff₀ (by linarith)] at hexp
  have he2 : Real.exp (2 * ρ) * Real.exp (-ρ) = Real.exp ρ := by
    rw [← Real.exp_add]
    ring_nf
  have hm := Real.exp_pos (-ρ)
  have h := mul_le_mul_of_nonneg_right hexp hm.le
  rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ (Real.cosh_pos ρ), Real.sinh_eq, Real.cosh_eq]
  have e3 : Real.exp (2 * ρ) * (1 - y) * Real.exp (-ρ) = Real.exp ρ * (1 - y) := by
    rw [mul_right_comm, he2]
  nlinarith

/-- Paper: `lem:fusedcoeff` (tanh_fused.tex), "`h_1 ≥ ρ^2/4 - 17ρ^4 > 0`", in the
weaker form needed by the factory: for `0 < ρ ≤ 1/32` and `0 ≤ a ≤ 4ρ`,
`h_1 = (1 - c^2)ρ/q - 1 ≥ 0`, from `c^2 ≤ 16ρ^4` and `tanh ρ ≤ ρ - 16ρ^5`. -/
theorem fused_h1_nonneg (ρ a : ℝ) (hρ0 : 0 < ρ) (hρ : ρ ≤ 1 / 32) (ha0 : 0 ≤ a)
    (ha : a ≤ 4 * ρ) :
    0 ≤ (1 - (Real.tanh a * Real.tanh ρ) ^ 2) * ρ / Real.tanh ρ - 1 := by
  obtain ⟨hc0, hc, -⟩ := fused_first_coefficients ρ a hρ0 ha0 ha
  have hq : 0 < Real.tanh ρ := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hρ0) (Real.cosh_pos ρ)
  have hc2 : (Real.tanh a * Real.tanh ρ) ^ 2 ≤ (4 * ρ ^ 2) ^ 2 := pow_le_pow_left₀ hc0 hc 2
  have ht := tanh_le_sub_quintic hρ0.le hρ
  rw [sub_nonneg, le_div_iff₀ hq, one_mul]
  nlinarith

/-- Paper: `lem:fusedfactory` and `lem:fusedcoeff` (tanh_fused.tex): for an actual
row with `0 < ρ ≤ 1/32` and `0 ≤ a ≤ 4ρ`, the categories built from
`A = h_0 = tanh a tanh ρ` and `B = h_1 = (1 - c^2)ρ/q - 1` are valid probabilities. -/
theorem fused_categories_valid_row (ρ a : ℝ) (hρ0 : 0 < ρ) (hρ : ρ ≤ 1 / 32) (ha0 : 0 ≤ a)
    (ha : a ≤ 4 * ρ) :
    let A := Real.tanh a * Real.tanh ρ
    let B := (1 - (Real.tanh a * Real.tanh ρ) ^ 2) * ρ / Real.tanh ρ - 1
    0 ≤ 2 * max (B - A) 0 ∧ 0 ≤ 2 * B + 2 * min A B ∧ 0 ≤ 2 * max (A - B) 0 ∧
      0 ≤ 1 - 2 * max (B - A) 0 - 200 * ρ ^ 4 ∧
      0 ≤ 1 - (2 * B + 2 * min A B) - 2 * max (A - B) 0 - 200 * ρ ^ 4 := by
  intro A B
  obtain ⟨hA0, hA, hB⟩ := fused_first_coefficients ρ a hρ0 ha0 ha
  have hB0 := fused_h1_nonneg ρ a hρ0 hρ ha0 ha
  obtain ⟨c1, c2, c3, -, -, -, -, c8, c9⟩ :=
    fused_categories_valid ρ A B hρ0.le hρ hA0 hA hB0 hB
  exact ⟨c1, c2, c3, c8, c9⟩

/-! ## Constants of `thm:fusedcritical` and `prop:fusedrate` -/

/-- Paper: proof of `thm:fusedcritical` (tanh_fused.tex), with `J_0 = 2^{25}`
and `M_0 = 2^{22}`: squared radii above the cutoff satisfy `2/J_0 < 1/1024`; on that
interval the derivative of `c_0 v + M_0 v^2` is at most `17/16 + 4M_0/J_0 = 25/16 < 2`;
and `9 M_0/(4(k+1)) ≤ 9/32` for `k ≥ J_0`. -/
theorem fusedcritical_cutoff_constants (v k : ℝ) (hv : v ≤ 2 / 2 ^ 25)
    (hk : 2 ^ 25 ≤ k) :
    (2 : ℝ) / 2 ^ 25 < 1 / 1024 ∧ 17 / 16 + 2 * 2 ^ 22 * v ≤ 25 / 16 ∧ (25 : ℝ) / 16 < 2 ∧
      9 * 2 ^ 22 / (4 * (k + 1)) ≤ 9 / 32 := by
  refine ⟨by norm_num, ?_, by norm_num, ?_⟩
  · have : 2 * 2 ^ 22 * v ≤ 2 * 2 ^ 22 * (2 / 2 ^ 25) :=
      mul_le_mul_of_nonneg_left hv (by norm_num)
    norm_num at this ⊢
    linarith
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

/-- Paper: proof of `thm:fusedcritical` (tanh_fused.tex): `√65 < 9`, `e^2 < 8`,
`(J_0 + 1)^{29/32} < 2^{24}` for `J_0 = 2^{25}`, and
`5617 (J_0+1)^{29/32} < 10^{11}`. -/
theorem fusedcritical_numerics :
    Real.sqrt 65 < 9 ∧ Real.exp 2 < 8 ∧ ((2 : ℝ) ^ 25 + 1) ^ ((29 : ℝ) / 32) < 2 ^ 24 ∧
      5617 * ((2 : ℝ) ^ 25 + 1) ^ ((29 : ℝ) / 32) < 10 ^ 11 := by
  have hJ : ((2 : ℝ) ^ 25 + 1) ^ ((29 : ℝ) / 32) < 2 ^ 24 := by
    have h1 : ((2 : ℝ) ^ 25 + 1) ^ ((29 : ℝ) / 32) ≤ ((2 : ℝ) ^ 26) ^ ((29 : ℝ) / 32) :=
      Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)
    have h2 : ((2 : ℝ) ^ 26) ^ ((29 : ℝ) / 32) = (2 : ℝ) ^ ((26 : ℝ) * (29 / 32)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    have h3 : (2 : ℝ) ^ ((26 : ℝ) * (29 / 32)) < (2 : ℝ) ^ ((24 : ℕ) : ℝ) :=
      (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr (by norm_num)
    rw [Real.rpow_natCast] at h3
    linarith
  refine ⟨?_, ?_, hJ, ?_⟩
  · rw [show (9 : ℝ) = Real.sqrt (9 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · have h := Real.exp_one_lt_d9
    have e : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [e]
    have : Real.exp 1 ^ 2 < 2.7182818286 ^ 2 :=
      pow_lt_pow_left₀ h (Real.exp_pos 1).le (by norm_num)
    linarith [show (2.7182818286 : ℝ) ^ 2 < 8 by norm_num]
  · have : 5617 * ((2 : ℝ) ^ 25 + 1) ^ ((29 : ℝ) / 32) < 5617 * 2 ^ 24 := by linarith
    linarith [show (5617 : ℝ) * 2 ^ 24 < 10 ^ 11 by norm_num]

/-- Paper: proof of `thm:fusedcritical` (tanh_fused.tex): "for `D ≤ J_0`, the
original `80(D+1)^2` bound is smaller than the same displayed estimate"
`10^{11} (D+1)^{35/32}`. -/
theorem fusedcritical_small_depth (D : ℝ) (hD0 : 0 ≤ D) (hD : D ≤ 2 ^ 25) :
    80 * (D + 1) ^ 2 ≤ 10 ^ 11 * (D + 1) ^ ((35 : ℝ) / 32) := by
  have hpos : 0 < D + 1 := by linarith
  have hsplit : (D + 1) ^ 2 = (D + 1) ^ ((29 : ℝ) / 32) * (D + 1) ^ ((35 : ℝ) / 32) := by
    rw [← Real.rpow_add hpos, ← Real.rpow_natCast]
    norm_num
  have h1 : (D + 1) ^ ((29 : ℝ) / 32) ≤ ((2 : ℝ) ^ 25 + 1) ^ ((29 : ℝ) / 32) :=
    Real.rpow_le_rpow hpos.le (by linarith) (by norm_num)
  have h2 := (fusedcritical_numerics).2.2.1
  have h3 : 0 ≤ (D + 1) ^ ((35 : ℝ) / 32) := by positivity
  rw [hsplit]
  have : 80 * (D + 1) ^ ((29 : ℝ) / 32) ≤ 10 ^ 11 := by
    linarith [show (80 : ℝ) * 2 ^ 24 ≤ 10 ^ 11 by norm_num]
  nlinarith

/-- Paper: proof of `prop:fusedrate` (tanh_fused.tex): for `0 < δ ≤ 2^{-16}` and
`J_0 = 2^{25}`, `4δ + 6/J_0 + 24/(100 J_0) < 1/1024`; on `[0, 1/1024]` the
derivative of `17v/16 + 2^{22}v^2` is at most `17/16 + 8192 < H_0 = 2^{14}`. -/
theorem fusedrate_constants (δ v : ℝ) (hδ : δ ≤ (1 / 2) ^ 16) (hv : v ≤ 1 / 1024) :
    4 * δ + 6 / 2 ^ 25 + 24 / (100 * 2 ^ 25) < 1 / 1024 ∧
      17 / 16 + 2 * 2 ^ 22 * v ≤ 17 / 16 + 8192 ∧ (17 / 16 + 8192 : ℝ) < 2 ^ 14 := by
  norm_num at hδ ⊢
  constructor
  · linarith
  · linarith

/-- Paper: proof of `prop:fusedrate` (tanh_fused.tex): with
`Γ_s = (17/16)u_*^2 + 2^{22}u_*^4` and `3δ ≤ u_*^2 ≤ 3δ + (3/2)δ^2`, `0 < δ ≤ 2^{-16}`,
`(51/16)δ ≤ Γ_s ≤ (51/16)δ + (51/32 + 2^{22}(25/8)^2)δ^2 < (51/16)δ + 40960002δ^2`. -/
theorem fusedrate_bounds {δ U : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (1 / 2) ^ 16)
    (hU1 : 3 * δ ≤ U) (hU2 : U ≤ 3 * δ + 3 / 2 * δ ^ 2) :
    51 / 16 * δ ≤ 17 / 16 * U + 2 ^ 22 * U ^ 2 ∧
      17 / 16 * U + 2 ^ 22 * U ^ 2 ≤ 51 / 16 * δ + (51 / 32 + 2 ^ 22 * (25 / 8) ^ 2) * δ ^ 2 ∧
      (51 / 32 + 2 ^ 22 * (25 / 8) ^ 2 : ℝ) < 40960002 := by
  have hU0 : 0 ≤ U := by linarith
  refine ⟨by nlinarith [sq_nonneg U], ?_, by norm_num⟩
  have hδ1 : δ ≤ 1 / 4 := by norm_num at hδ; linarith
  have hU3 : U ≤ 25 / 8 * δ := by nlinarith
  have hU4 : U ^ 2 ≤ (25 / 8 * δ) ^ 2 := pow_le_pow_left₀ hU0 hU3 2
  nlinarith [sq_nonneg δ]

end ExactSampling.FusedFactory
