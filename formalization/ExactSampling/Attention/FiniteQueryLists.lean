import Mathlib

/-!
# A finite known query list: cached lower masses and exact residual sampling

This module formalizes the exactness and charging arguments of `thm:finite-query-list`
(`attention_finite_queries.tex`), also summarized in `main_attention.tex` and in the
"Other positive cases" paragraph of `checkpoint_certificates.tex`.

Formalized here:
* the dyadic grid rounding of a certified lower endpoint into a stored lower bound
  `0 ≤ ℓ_k ≤ p_k` with `p_k - ℓ_k ≤ δ/V`;
* the residual table: with `a_k = (1-δ)ℓ_k` and `r = 1 - ∑ a_k`, one has `0 ≤ a_k ≤ p_k`,
  `δ ≤ r ≤ 1 - (1-δ)^2 ≤ 2δ`, the residual law `b_k = (p_k - a_k)/r` is a probability
  vector, and `a_k + r b_k = p_k` exactly;
* the residual-branch probability `r ≤ 1/(2H)` for `1/(8H) < δ ≤ 1/(4H)`, and the charging of
  the fallback work by this probability;
* the residual cumulative interval width `V 2^{-t_j}/r ≤ 2^{-j}/(16V)`; an undecided comparison
  (overlap of the uniform's interval with a boundary enclosure, both of width at most
  `2^{-j}/(16V)`) puts `U` within `2^{-j}/(8V)` of that boundary; and the union bound: the
  uniforms within `2^{-j}/(8V)` of one of the `V - 1` boundaries have measure at most `2^{-j}/4`;
* almost-sure stopping from a geometric tail;
* the geometric-moment bound for the conditional fallback work and the fact that, multiplied by
  the residual probability `r ≤ 1/(2H)`, it no longer depends on `H`.

Not formalized: the certified evaluation routine and the bit-cost accounting of the
preprocessor.
-/

open Finset Filter MeasureTheory
open scoped BigOperators Topology ENNReal

namespace ExactSampling.FiniteQueryLists

/-- Rounding a certified lower endpoint down to the grid `2^{-t}` and clamping at zero gives a
stored lower bound with `0 ≤ ℓ ≤ p` and `p - ℓ ≤ 2·2^{-t}`; with `2^t ≥ 4V/δ`
(`t₀ = ⌈log₂(V/δ)⌉ + 2`) this is at most `δ/V`.
Paper: `thm:finite-query-list` (attention_finite_queries.tex). -/
theorem grid_lower_bound (p lo : ℝ) (t : ℕ) (hp : 0 ≤ p) (hlo : lo ≤ p)
    (hw : p - lo ≤ (2 : ℝ)⁻¹ ^ t) :
    let ℓ : ℝ := max 0 ((⌊lo * 2 ^ t⌋ : ℝ) / 2 ^ t)
    0 ≤ ℓ ∧ ℓ ≤ p ∧ p - ℓ ≤ 2 * (2 : ℝ)⁻¹ ^ t := by
  intro ℓ
  have h2t : (0 : ℝ) < 2 ^ t := by positivity
  have hfl := Int.floor_le (lo * 2 ^ t)
  have hfl2 := Int.lt_floor_add_one (lo * 2 ^ t)
  have hdown : (⌊lo * 2 ^ t⌋ : ℝ) / 2 ^ t ≤ lo := by
    rw [div_le_iff₀ h2t]; exact hfl
  have hup : lo - (2 : ℝ)⁻¹ ^ t ≤ (⌊lo * 2 ^ t⌋ : ℝ) / 2 ^ t := by
    rw [inv_pow, le_div_iff₀ h2t, sub_mul, inv_mul_cancel₀ h2t.ne']
    linarith
  refine ⟨le_max_left _ _, max_le hp (le_trans hdown hlo), ?_⟩
  have : (⌊lo * 2 ^ t⌋ : ℝ) / 2 ^ t ≤ ℓ := le_max_right _ _
  linarith

/-- With `2^t ≥ 4V/δ`, the grid rounding error `2·2^{-t}` is at most `δ/V`.
Paper: `thm:finite-query-list` (attention_finite_queries.tex), precision `t₀`. -/
theorem grid_precision (V δ : ℝ) (t : ℕ) (hV : 0 < V) (hδ : 0 < δ) (ht : 4 * V / δ ≤ 2 ^ t) :
    2 * (2 : ℝ)⁻¹ ^ t ≤ δ / V := by
  have h2t : (0 : ℝ) < 2 ^ t := by positivity
  rw [inv_pow, le_div_iff₀ hV]
  rw [div_le_iff₀ hδ] at ht
  rw [← div_eq_mul_inv, mul_comm, ← mul_div_assoc, div_le_iff₀ h2t]
  nlinarith

/-- The residual table. With stored lower bounds `0 ≤ ℓ_k ≤ p_k`, `p_k - ℓ_k ≤ δ/V`, and
`0 < δ ≤ 1`, the masses `a_k = (1-δ)ℓ_k` and `r = 1 - ∑ a_k` satisfy `0 ≤ a_k ≤ p_k`,
`δ ≤ r ≤ 1 - (1-δ)^2 ≤ 2δ`; the residual law `b_k = (p_k - a_k)/r` is a probability vector,
and the final probability of token `k` is exactly `a_k + r b_k = p_k`.
Paper: `thm:finite-query-list` (attention_finite_queries.tex). -/
theorem residual_table {V : ℕ} (p ℓ : Fin V → ℝ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hpsum : ∑ k, p k = 1) (hℓ0 : ∀ k, 0 ≤ ℓ k) (hℓp : ∀ k, ℓ k ≤ p k)
    (hgap : ∀ k, p k - ℓ k ≤ δ / V) :
    let a : Fin V → ℝ := fun k => (1 - δ) * ℓ k
    let r : ℝ := 1 - ∑ k, a k
    (∀ k, 0 ≤ a k ∧ a k ≤ p k) ∧ δ ≤ r ∧ r ≤ 1 - (1 - δ) ^ 2 ∧ 1 - (1 - δ) ^ 2 ≤ 2 * δ ∧
      (∀ k, 0 ≤ (p k - a k) / r) ∧ ∑ k, (p k - a k) / r = 1 ∧
      ∀ k, a k + r * ((p k - a k) / r) = p k := by
  intro a r
  have hV : 0 < V := by
    rcases Nat.eq_zero_or_pos V with h | h
    · subst h; simp at hpsum
    · exact h
  have hVr : (0 : ℝ) < V := by exact_mod_cast hV
  have hsumℓ_le : ∑ k, ℓ k ≤ 1 := by
    rw [← hpsum]; exact Finset.sum_le_sum fun k _ => hℓp k
  have hsumℓ_ge : 1 - δ ≤ ∑ k, ℓ k := by
    have : ∑ k, (p k - ℓ k) ≤ ∑ _k : Fin V, δ / V := Finset.sum_le_sum fun k _ => hgap k
    rw [Finset.sum_sub_distrib, hpsum] at this
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    rw [mul_div_cancel₀ _ hVr.ne'] at this
    linarith
  have hr : r = 1 - (1 - δ) * ∑ k, ℓ k := by
    show 1 - ∑ k, (1 - δ) * ℓ k = _
    rw [← Finset.mul_sum]
  have hr_lo : δ ≤ r := by rw [hr]; nlinarith
  have hr_hi : r ≤ 1 - (1 - δ) ^ 2 := by rw [hr]; nlinarith
  have hrpos : 0 < r := lt_of_lt_of_le hδ0 hr_lo
  refine ⟨fun k => ⟨mul_nonneg (by linarith) (hℓ0 k), ?_⟩, hr_lo, hr_hi, by nlinarith, ?_, ?_, ?_⟩
  · show (1 - δ) * ℓ k ≤ p k
    nlinarith [hℓ0 k, hℓp k]
  · intro k
    apply div_nonneg _ hrpos.le
    show 0 ≤ p k - (1 - δ) * ℓ k
    nlinarith [hℓ0 k, hℓp k]
  · rw [← Finset.sum_div, Finset.sum_sub_distrib, hpsum, div_self hrpos.ne']
  · intro k; field_simp; ring

/-- A cached mass plus the exact residual branch returns the original categorical probability.
Paper: `thm:finite-query-list` (attention_finite_queries.tex). -/
theorem cached_residual_exactness (p a r : ℝ) (hr : r ≠ 0) : a + r * ((p - a) / r) = p := by
  field_simp
  ring

/-- The residual gate has at least the deliberately reserved mass.
Paper: `thm:finite-query-list` (attention_finite_queries.tex). -/
theorem residual_gate_lower (delta totalLower : ℝ) (hd : delta ≤ 1) (hs : totalLower ≤ 1) :
    delta ≤ 1 - (1 - delta) * totalLower := by
  have hmul := mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ 1 - delta)
  nlinarith

/-- The total approximation deficit is at most another `δ`.
Paper: `thm:finite-query-list` (attention_finite_queries.tex). -/
theorem residual_gate_upper (delta totalLower : ℝ) (hd1 : delta ≤ 1)
    (hs : 1 - delta ≤ totalLower) : 1 - (1 - delta) * totalLower ≤ 2 * delta := by
  have hmul := mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ 1 - delta)
  nlinarith [sq_nonneg delta]

/-- With `1/(8H) < δ ≤ 1/(4H)`, the residual branch has probability `r ≤ 2δ ≤ 1/(2H)`.
Paper: `thm:finite-query-list` (attention_finite_queries.tex). -/
theorem residual_probability (r δ H : ℝ) (hH : 0 < H) (hr : r ≤ 2 * δ)
    (hδ : δ ≤ 1 / (4 * H)) : r ≤ 1 / (2 * H) := by
  have : 2 * (1 / (4 * H)) = 1 / (2 * H) := by field_simp; ring
  linarith

/-- The deterministic residual-mass bound multiplies the conditional fallback work: if the
fallback costs at most `H W` and `r ≤ 2δ` with `2δH ≤ 1`, its contribution is at most `W`.
Paper: `thm:finite-query-list` (attention_finite_queries.tex). -/
theorem fallback_charging (delta r H W : ℝ) (hW : 0 ≤ W) (hH : 0 ≤ H) (hr : r ≤ 2 * delta)
    (hsmall : 2 * delta * H ≤ 1) : r * (H * W) ≤ W := by
  have hmul := mul_le_mul_of_nonneg_right hr (mul_nonneg hH hW)
  have hmul2 := mul_le_mul_of_nonneg_right hsmall hW
  nlinarith

/-- Residual cumulative intervals: with all `p_k` enclosed to width `2^{-t}`, where
`2^t ≥ 2^j 16V²/δ`, and `r ≥ δ`, each residual cumulative interval has width
`V 2^{-t}/r ≤ 2^{-j}/(16V)`.
Paper: `thm:finite-query-list` (attention_finite_queries.tex). -/
theorem residual_interval_width (V δ r : ℝ) (t j : ℕ) (hV : 0 < V) (hδ : 0 < δ) (hr : δ ≤ r)
    (ht : 2 ^ j * (16 * V ^ 2 / δ) ≤ 2 ^ t) :
    V * (2 : ℝ)⁻¹ ^ t / r ≤ (2 : ℝ)⁻¹ ^ j / (16 * V) := by
  have hrpos : 0 < r := lt_of_lt_of_le hδ hr
  have h2t : (0 : ℝ) < 2 ^ t := by positivity
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  rw [inv_pow, inv_pow, div_le_div_iff₀ hrpos (by positivity)]
  have h1 : 2 ^ j * (16 * V ^ 2) ≤ 2 ^ t * δ := by
    have := mul_le_mul_of_nonneg_right ht hδ.le
    rwa [mul_assoc, div_mul_cancel₀ _ hδ.ne'] at this
  have hlhs : V * (2 ^ t)⁻¹ * (16 * V) = (2 ^ j * (16 * V ^ 2)) * ((2 ^ t)⁻¹ * (2 ^ j)⁻¹) := by
    field_simp
  have hrhs : (2 ^ j)⁻¹ * r = (2 ^ t * r) * ((2 ^ t)⁻¹ * (2 ^ j)⁻¹) := by
    field_simp
  rw [hlhs, hrhs]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  nlinarith

/-- An undecided residual comparison is close to a boundary: if the uniform's interval
`[a, a + w]` contains `U`, a boundary `B` lies in an enclosure `[lo, hi]` of width at most `w`, and
the two intervals overlap, then `|U - B| ≤ 2w`; with `w = 2^{-j}/(16V)` this is `2^{-j}/(8V)`.
Paper: `thm:finite-query-list` (attention_finite_queries.tex), "Failure to decide at stage `j`
places `U` within distance at most `2^{-j}/(8V)` of one of the `V-1` true boundaries". -/
theorem undecided_close (U B a lo hi w : ℝ) (hU : a ≤ U ∧ U ≤ a + w) (hB : lo ≤ B ∧ B ≤ hi)
    (hw : hi - lo ≤ w) (hover : lo ≤ a + w ∧ a ≤ hi) : |U - B| ≤ 2 * w := by
  rw [abs_le]; constructor <;> linarith [hU.1, hU.2, hB.1, hB.2, hover.1, hover.2]

/-- The union bound at stage `j`: the uniforms within `2^{-j}/(8V)` of one of the `V - 1`
interior cumulative boundaries have measure at most `2^{-j}/4`.
Paper: `thm:finite-query-list` (attention_finite_queries.tex). -/
theorem residual_union_bound (B : ℕ → ℝ) (V j : ℕ) (hV : 1 ≤ V) :
    volume (⋃ k ∈ Finset.Ico 1 V, Set.Icc (B k - (2 : ℝ)⁻¹ ^ j / (8 * V))
      (B k + (2 : ℝ)⁻¹ ^ j / (8 * V))) ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ j / 4) := by
  have hVr : (1 : ℝ) ≤ V := by exact_mod_cast hV
  calc volume (⋃ k ∈ Finset.Ico 1 V, Set.Icc (B k - (2 : ℝ)⁻¹ ^ j / (8 * V))
        (B k + (2 : ℝ)⁻¹ ^ j / (8 * V)))
      ≤ ∑ k ∈ Finset.Ico 1 V, volume (Set.Icc (B k - (2 : ℝ)⁻¹ ^ j / (8 * V))
          (B k + (2 : ℝ)⁻¹ ^ j / (8 * V))) := measure_biUnion_finset_le _ _
    _ = ∑ _k ∈ Finset.Ico 1 V, ENNReal.ofReal (2 * ((2 : ℝ)⁻¹ ^ j / (8 * V))) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Real.volume_Icc]; congr 1; ring
    _ = ENNReal.ofReal ((V - 1 : ℕ) * (2 * ((2 : ℝ)⁻¹ ^ j / (8 * V)))) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ j / 4) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : ((V - 1 : ℕ) : ℝ) ≤ V := by exact_mod_cast Nat.sub_le V 1
        have hpos : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ j := by positivity
        have : ((V - 1 : ℕ) : ℝ) * (2 * ((2 : ℝ)⁻¹ ^ j / (8 * V))) ≤
            V * (2 * ((2 : ℝ)⁻¹ ^ j / (8 * V))) := by
          apply mul_le_mul_of_nonneg_right h1; positivity
        calc ((V - 1 : ℕ) : ℝ) * (2 * ((2 : ℝ)⁻¹ ^ j / (8 * V)))
            ≤ V * (2 * ((2 : ℝ)⁻¹ ^ j / (8 * V))) := this
          _ = (2 : ℝ)⁻¹ ^ j / 4 := by field_simp; ring

/-- The geometric moment `∑_{j≥0} 2^{-j}(X + j)^d ≤ 2^{d+1} d! X^d` for `X ≥ 1` (the same
estimate as in `lem:replayexactsampling`), restated here for the residual branch.
Paper: `thm:finite-query-list` (attention_finite_queries.tex), the conditional fallback work. -/
theorem fallback_geometric_moment (d : ℕ) (X : ℝ) (hX : 1 ≤ X) :
    Summable (fun j : ℕ => (2 : ℝ)⁻¹ ^ j * (X + j) ^ d) ∧
      ∑' j : ℕ, (2 : ℝ)⁻¹ ^ j * (X + j) ^ d ≤ 2 ^ (d + 1) * d.factorial * X ^ d := by
  have hbound : ∀ j : ℕ, (2 : ℝ)⁻¹ ^ j * (X + j) ^ d ≤
      X ^ d * d.factorial * (((j + d).choose d : ℝ) * (2 : ℝ)⁻¹ ^ j) := by
    intro j
    have h1 : (j + 1) ^ d ≤ (j + 1).ascFactorial d := Nat.pow_succ_le_ascFactorial (j + 1) d
    rw [Nat.ascFactorial_eq_factorial_mul_choose] at h1
    have h2 : ((j : ℝ) + 1) ^ d ≤ (d.factorial : ℝ) * ((j + d).choose d : ℝ) := by
      exact_mod_cast h1
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h3 : (X + j) ^ d ≤ X ^ d * ((j : ℝ) + 1) ^ d := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by nlinarith) d
    have h4 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ j := by positivity
    have h5 : (0 : ℝ) ≤ X ^ d := pow_nonneg (by linarith) d
    calc (2 : ℝ)⁻¹ ^ j * (X + j) ^ d ≤ (2 : ℝ)⁻¹ ^ j * (X ^ d * ((j : ℝ) + 1) ^ d) := by gcongr
      _ ≤ (2 : ℝ)⁻¹ ^ j * (X ^ d * ((d.factorial : ℝ) * ((j + d).choose d : ℝ))) := by gcongr
      _ = X ^ d * d.factorial * (((j + d).choose d : ℝ) * (2 : ℝ)⁻¹ ^ j) := by ring
  have hs := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) d (r := (2 : ℝ)⁻¹)
    (by norm_num)).mul_left (X ^ d * d.factorial)
  have hsum : Summable (fun j : ℕ => (2 : ℝ)⁻¹ ^ j * (X + j) ^ d) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (by positivity)
      (pow_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j]) _)) hbound hs.summable
  refine ⟨hsum, ?_⟩
  calc ∑' j : ℕ, (2 : ℝ)⁻¹ ^ j * (X + j) ^ d ≤ X ^ d * d.factorial * (1 / (1 - 2⁻¹) ^ (d + 1)) :=
        hasSum_le hbound hsum.hasSum hs
    _ = 2 ^ (d + 1) * d.factorial * X ^ d := by
        have : (1 : ℝ) - 2⁻¹ = 2⁻¹ := by norm_num
        rw [this, one_div, inv_pow, inv_inv]; ring

/-- The residual branch pays for itself: its probability `r ≤ 1/(2H)` times the conditional
fallback work `H ∑_j 2^{-j}(X + j)^d` (with `X ≥ 1` collecting `B + log(V/δ + 2)`) is at most
`2^d d! X^d`, independently of `H`.
Paper: `thm:finite-query-list` (attention_finite_queries.tex). -/
theorem fallback_pays (r H X : ℝ) (d : ℕ) (hH : 0 < H) (hr : r ≤ 1 / (2 * H))
    (hX : 1 ≤ X) :
    r * (H * ∑' j : ℕ, (2 : ℝ)⁻¹ ^ j * (X + j) ^ d) ≤ 2 ^ d * d.factorial * X ^ d := by
  obtain ⟨_, hle⟩ := fallback_geometric_moment d X hX
  have h0 : 0 ≤ ∑' j : ℕ, (2 : ℝ)⁻¹ ^ j * (X + j) ^ d :=
    tsum_nonneg fun j => mul_nonneg (by positivity)
      (pow_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j]) _)
  calc r * (H * ∑' j : ℕ, (2 : ℝ)⁻¹ ^ j * (X + j) ^ d)
      ≤ 1 / (2 * H) * (H * (2 ^ (d + 1) * d.factorial * X ^ d)) := by
        gcongr
    _ = 2 ^ d * d.factorial * X ^ d := by field_simp; ring

/-- If nontermination is bounded by every geometric precision tail, its probability is zero.
Paper: `thm:finite-query-list` (attention_finite_queries.tex). -/
theorem zero_of_geometric_tail (p : ℝ) (hp : 0 ≤ p)
    (htail : ∀ j : ℕ, p ≤ (1 : ℝ) / 4 * ((1 : ℝ) / 2) ^ j) : p = 0 := by
  have hpow : Tendsto (fun j : ℕ => ((1 : ℝ) / 2) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ht : Tendsto (fun j : ℕ => (1 : ℝ) / 4 * ((1 : ℝ) / 2) ^ j) atTop (𝓝 0) := by
    simpa using hpow.const_mul ((1 : ℝ) / 4)
  have hle : p ≤ 0 := ge_of_tendsto ht (Filter.Eventually.of_forall htail)
  linarith

end ExactSampling.FiniteQueryLists
