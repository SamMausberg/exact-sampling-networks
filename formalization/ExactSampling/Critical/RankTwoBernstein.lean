import Mathlib

/-!
# Corrected Bernstein factories in a fixed number of variables

This module formalizes the exactness and counting arithmetic of
`lem:fixed-rank-bernstein` (tanh_bernstein_product.tex), its two-variable case
`lem:rank-two-bernstein` (tanh_rank_two.tex), the gate charge of
`thm:rank-two-critical`, and the rank-three arithmetic of
`thm:rank-three-critical` (tanh_rank_three.tex), including the seven-product
block identities.

Formalized:
* the algebra behind `eq:fixed-rank-coordinate-telescope`: the identity of
  ordered products `∏ b - ∏ a = ∑_j (∏_{i<j} a_i)(b_j - a_j)(∏_{i>j} b_i)` in an
  arbitrary ring (it is not instantiated with the operators `T_{i,m}`, which
  are not defined here);
* the finite telescope, and the convergence of the correction series to
  `f - P_{m_0}` once `P_m → f` is given;
* for every fixed `r`: the correction envelope `Ā ≤ m_0^2/(8r)`, the base
  error `∑_k M_{2k}/(8m_0)^k ≤ 1/16 + (r-1)/(512 r^2) < 3/40`, the exact
  branch-mass and source-count series `r Ā/(3m_0^2)` and `r^2 Ā/m_0`, and the
  source bound `r m_0`;
* the rank-two and rank-three specializations;
* the seven-product identities, `7^6 < 2^17`, `log_2 7 < 17/6`, and the
  logarithmic exponent `27/4 < 7`.

Not formalized: the Bernstein operators themselves, the degree-elevation and
hypergeometric coefficient bound of `lem:correctedbernstein`, the derivative
bounds `‖∂_j^k h‖ ≤ ∑_ℓ M_{k+2ℓ}/(8m)^ℓ`, the product bound
`‖G_{m_0} - f‖ ≤ ∑_k M_{2k}/(8m_0)^k`, tensor Bernstein convergence, and
the finite-bit implementation. Their conclusions enter only as the
hypotheses of the counting lemmas. In `gate_work_bound` the hypothesis
`m_0 ≤ K D` stands in for the analytic induction of `thm:rank-two-critical`
(the radius `ρ_D`, the Bell constants `C_k`, the bounds `E_{k,D}` and `M_k`,
and `m_0 = O(D+1)`; the last step from explicit `M_k` bounds is
`NewBottleneck.rank_two_start`), and the basis-replacement count is not
formalized.
-/

open Finset Filter

namespace ExactSampling.RankTwoBernstein

/-! ## Telescopes -/

/-- Paper: `eq:fixed-rank-coordinate-telescope` (tanh_bernstein_product.tex),
the case of two coordinates:
`A₂B₂ - A₁B₁ = (A₂ - A₁)B₂ + A₁(B₂ - B₁)` for linear operators. -/
theorem operator_telescope {R V : Type*} [Semiring R] [AddCommGroup V] [Module R V]
    (A₂ A₁ B₂ B₁ : V →ₗ[R] V) :
    A₂.comp B₂ - A₁.comp B₁ = (A₂ - A₁).comp B₂ + A₁.comp (B₂ - B₁) := by
  ext x
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, map_sub]
  abel

/-- Ordered product `f j * f (j+1) * ⋯ * f (j+k-1)`. Auxiliary for
`eq:fixed-rank-coordinate-telescope` (tanh_bernstein_product.tex). -/
def rprod {R : Type*} [Monoid R] (f : ℕ → R) : ℕ → ℕ → R
  | _, 0 => 1
  | j, k + 1 => f j * rprod f (j + 1) k

/-- Ordered product `f 0 * ⋯ * f (j-1)`. Auxiliary for
`eq:fixed-rank-coordinate-telescope` (tanh_bernstein_product.tex). -/
def lprod {R : Type*} [Monoid R] (f : ℕ → R) : ℕ → R
  | 0 => 1
  | j + 1 => lprod f j * f j

/-- The two ordered products agree. Auxiliary for
`eq:fixed-rank-coordinate-telescope` (tanh_bernstein_product.tex). -/
theorem lprod_eq_rprod {R : Type*} [Monoid R] (f : ℕ → R) (j : ℕ) :
    lprod f j = rprod f 0 j := by
  have key : ∀ k i, rprod f i k * f (i + k) = rprod f i (k + 1) := by
    intro k
    induction k with
    | zero => intro i; simp [rprod]
    | succ k ih =>
      intro i
      simp only [rprod]
      rw [mul_assoc, show i + (k + 1) = (i + 1) + k by ring, ih (i + 1)]
      rfl
  induction j with
  | zero => rfl
  | succ j ih => rw [lprod, ih, ← key j 0, zero_add]

/-- Paper: `eq:fixed-rank-coordinate-telescope` in `lem:fixed-rank-bernstein`
(tanh_bernstein_product.tex): changing one coordinate operator at a time,
`∏ b - ∏ a = ∑_j (∏_{i<j} a_i)(b_j - a_j)(∏_{i>j} b_i)`, as an identity of ordered
products in any ring (for instance a ring of linear operators), with
`a_i = T_{i,m}` and `b_i = T_{i,2m}`. -/
theorem product_telescope {R : Type*} [Ring R] (a b : ℕ → R) (r : ℕ) :
    rprod b 0 r - rprod a 0 r =
      ∑ j ∈ range r, lprod a j * (b j - a j) * rprod b (j + 1) (r - j - 1) := by
  let X : ℕ → R := fun j => lprod a j * rprod b j (r - j)
  have hstep : ∀ j ∈ range r, X j - X (j + 1) =
      lprod a j * (b j - a j) * rprod b (j + 1) (r - j - 1) := by
    intro j hj
    have hj' : j < r := mem_range.mp hj
    simp only [X]
    have e1 : r - j = (r - j - 1) + 1 := by omega
    have e2 : r - (j + 1) = r - j - 1 := by omega
    rw [e1, e2, rprod, lprod]
    noncomm_ring
  rw [← sum_congr rfl hstep, sum_range_sub']
  simp only [X, Nat.sub_zero, Nat.sub_self, lprod, rprod, one_mul, mul_one]
  rw [lprod_eq_rprod]


/-- Paper: `lem:fixed-rank-bernstein` (tanh_bernstein_product.tex), proof: the
finite exactness telescope `P_0 + ∑_{k<N} (P_{k+1} - P_k) = P_N`. -/
theorem finite_telescope (P : ℕ → ℝ) (N : ℕ) :
    P 0 + ∑ k ∈ range N, (P (k + 1) - P k) = P N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ]
      linarith

/-- Paper: `lem:fixed-rank-bernstein` (tanh_bernstein_product.tex), proof: if
`P_m → f`, the correction series converges to `f - P_{m_0}`; this is the
exactness identity `P_{m_0} + ∑ (P_{2m} - P_m) = f`. The convergence `P_m → f`
(tensor Bernstein convergence) is a hypothesis. -/
theorem telescope_limit (P : ℕ → ℝ) (f : ℝ) (hP : Tendsto P atTop (nhds f)) :
    Tendsto (fun N => ∑ k ∈ range N, (P (k + 1) - P k)) atTop (nhds (f - P 0)) := by
  have heq : (fun N => ∑ k ∈ range N, (P (k + 1) - P k)) = fun N => P N - P 0 := by
    funext N
    have := finite_telescope P N
    linarith
  rw [heq]
  exact hP.sub_const (P 0)

/-- Paper: `lem:fixed-rank-bernstein` (tanh_bernstein_product.tex), proof: a
coefficient `d` sampled on a branch of mass `c > 0` as the sign mean `d/c`
contributes exactly `d`. -/
theorem correction_mean (c d : ℝ) (hc : c ≠ 0) : c * (d / c) = d := by
  field_simp

/-- Paper: `lem:fixed-rank-bernstein` (tanh_bernstein_product.tex), proof: a
coefficient bounded by its branch mass `c > 0` gives a legal sign mean. -/
theorem normalized_coefficient_bounded (d c : ℝ) (hc : 0 < c) (h : |d| ≤ c) :
    |d / c| ≤ 1 := by
  rw [abs_div, abs_of_pos hc]
  exact (div_le_one hc).2 h

/-! ## Counting at a fixed rank `r`

`M k` bounds `‖D^k f‖_{1,ent}` and `S ℓ = M_{2+2ℓ} + M_{3+2ℓ} + M_{4+2ℓ}`.
The starting level `m_0` satisfies `m_0 ≥ 2 M_2` and
`m_0^{ℓ+2} ≥ 8^{1-ℓ} r^2 S_ℓ` for `0 ≤ ℓ < r`. -/

/-- The quantities `S_ℓ` of `lem:fixed-rank-bernstein`. Auxiliary for `lem:fixed-rank-bernstein`
(tanh_bernstein_product.tex). -/
def Sl (M : ℕ → ℝ) (ℓ : ℕ) : ℝ := M (2 + 2 * ℓ) + M (3 + 2 * ℓ) + M (4 + 2 * ℓ)

/-- The starting-level condition in the form `S_ℓ ≤ 8^ℓ m_0^{ℓ+2} / (8 r^2)`. Auxiliary for
`lem:fixed-rank-bernstein`
(tanh_bernstein_product.tex). -/
theorem start_condition_iff (r : ℕ) (m0 Sℓ : ℝ) (ℓ : ℕ) (hr : 1 ≤ r) :
    (8 : ℝ) ^ ((1 : ℤ) - ℓ) * (r : ℝ) ^ 2 * Sℓ ≤ m0 ^ (ℓ + 2) ↔
      Sℓ ≤ 8 ^ ℓ * m0 ^ (ℓ + 2) / (8 * (r : ℝ) ^ 2) := by
  have hr' : (0 : ℝ) < (r : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    positivity
  have h8 : (8 : ℝ) ^ ((1 : ℤ) - ℓ) = 8 / 8 ^ ℓ := by
    rw [zpow_sub₀ (by norm_num), zpow_one, zpow_natCast]
  rw [h8, le_div_iff₀ (by positivity)]
  have h8l : (0 : ℝ) < 8 ^ ℓ := by positivity
  constructor
  · intro h
    have := mul_le_mul_of_nonneg_left h h8l.le
    have e : 8 ^ ℓ * (8 / 8 ^ ℓ * (r : ℝ) ^ 2 * Sℓ) = Sℓ * (8 * (r : ℝ) ^ 2) := by
      field_simp
    linarith
  · intro h
    have e : 8 / 8 ^ ℓ * (r : ℝ) ^ 2 * Sℓ = Sℓ * (8 * (r : ℝ) ^ 2) / 8 ^ ℓ := by
      field_simp
    rw [e, div_le_iff₀ h8l]
    linarith

/-- Paper: `lem:fixed-rank-bernstein` (tanh_bernstein_product.tex), proof: the
correction envelope `Ā = ∑_{ℓ<r} S_ℓ/(8m_0)^ℓ ≤ m_0^2/(8r)`. -/
theorem envelope_le (r : ℕ) (hr : 1 ≤ r) (m0 : ℝ) (hm0 : 0 < m0) (S : ℕ → ℝ)
    (hstart : ∀ ℓ < r, (8 : ℝ) ^ ((1 : ℤ) - ℓ) * (r : ℝ) ^ 2 * S ℓ ≤ m0 ^ (ℓ + 2)) :
    ∑ ℓ ∈ range r, S ℓ / (8 * m0) ^ ℓ ≤ m0 ^ 2 / (8 * r) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hterm : ∀ ℓ ∈ range r, S ℓ / (8 * m0) ^ ℓ ≤ m0 ^ 2 / (8 * (r : ℝ) ^ 2) := by
    intro ℓ hℓ
    have h := (start_condition_iff r m0 (S ℓ) ℓ hr).mp (hstart ℓ (mem_range.mp hℓ))
    rw [div_le_iff₀ (by positivity)]
    calc S ℓ ≤ 8 ^ ℓ * m0 ^ (ℓ + 2) / (8 * (r : ℝ) ^ 2) := h
      _ = m0 ^ 2 / (8 * (r : ℝ) ^ 2) * (8 * m0) ^ ℓ := by rw [mul_pow, pow_add]; ring
  calc ∑ ℓ ∈ range r, S ℓ / (8 * m0) ^ ℓ ≤ ∑ ℓ ∈ range r, m0 ^ 2 / (8 * (r : ℝ) ^ 2) :=
        sum_le_sum hterm
    _ = m0 ^ 2 / (8 * r) := by
        rw [sum_const, card_range, nsmul_eq_mul]; field_simp

/-- Paper: `lem:fixed-rank-bernstein` (tanh_bernstein_product.tex), proof: the
bound `∑_{k=1}^r M_{2k}/(8m_0)^k ≤ 1/16 + (r-1)/(512 r^2) < 3/40` on the base
error; the preceding inequality `‖G_{m_0} - f‖ ≤ ∑_k M_{2k}/(8m_0)^k` is not
formalized. -/
theorem base_error_le (r : ℕ) (hr : 1 ≤ r) (m0 : ℝ) (hm0 : 0 < m0) (M : ℕ → ℝ)
    (hM : ∀ k, 0 ≤ M k) (h2 : 2 * M 2 ≤ m0)
    (hstart : ∀ ℓ < r, (8 : ℝ) ^ ((1 : ℤ) - ℓ) * (r : ℝ) ^ 2 * Sl M ℓ ≤ m0 ^ (ℓ + 2)) :
    ∑ k ∈ range r, M (2 * (k + 1)) / (8 * m0) ^ (k + 1) ≤
        1 / 16 + ((r : ℝ) - 1) / (512 * (r : ℝ) ^ 2) ∧
      ∑ k ∈ range r, M (2 * (k + 1)) / (8 * m0) ^ (k + 1) < 3 / 40 := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hr0 : (0 : ℝ) < (s + 1 : ℕ) := by positivity
  have hfirst : M 2 / (8 * m0) ^ 1 ≤ 1 / 16 := by
    rw [pow_one, div_le_iff₀ (by positivity)]; linarith
  have hrest : ∀ k ∈ range s, M (2 * (k + 1 + 1)) / (8 * m0) ^ (k + 1 + 1) ≤
      1 / (512 * ((s + 1 : ℕ) : ℝ) ^ 2) := by
    intro k hk
    have hk' : k < s + 1 := by have := mem_range.mp hk; omega
    have h := (start_condition_iff (s + 1) m0 (Sl M k) k (by omega)).mp (hstart k hk')
    have hMS : M (2 * (k + 1 + 1)) ≤ Sl M k := by
      simp only [Sl]
      rw [show 2 * (k + 1 + 1) = 4 + 2 * k by ring]
      linarith [hM (2 + 2 * k), hM (3 + 2 * k)]
    rw [div_le_iff₀ (by positivity)]
    calc M (2 * (k + 1 + 1)) ≤ Sl M k := hMS
      _ ≤ 8 ^ k * m0 ^ (k + 2) / (8 * ((s + 1 : ℕ) : ℝ) ^ 2) := h
      _ = 1 / (512 * ((s + 1 : ℕ) : ℝ) ^ 2) * (8 * m0) ^ (k + 1 + 1) := by
          rw [mul_pow, show k + 1 + 1 = k + 2 by ring, pow_add (8 : ℝ) k 2]; field_simp; ring
  have hsum : ∑ k ∈ range (s + 1), M (2 * (k + 1)) / (8 * m0) ^ (k + 1) ≤
      1 / 16 + ((s + 1 : ℕ) - 1 : ℝ) / (512 * ((s + 1 : ℕ) : ℝ) ^ 2) := by
    rw [sum_range_succ']
    have h1 := sum_le_sum hrest
    rw [sum_const, card_range, nsmul_eq_mul] at h1
    have e : ((s + 1 : ℕ) - 1 : ℝ) / (512 * ((s + 1 : ℕ) : ℝ) ^ 2) =
        (s : ℝ) * (1 / (512 * ((s + 1 : ℕ) : ℝ) ^ 2)) := by push_cast; ring
    rw [e]
    simp only [zero_add, mul_one] at hfirst ⊢
    linarith
  refine ⟨hsum, lt_of_le_of_lt hsum ?_⟩
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have e : ((s + 1 : ℕ) - 1 : ℝ) / (512 * ((s + 1 : ℕ) : ℝ) ^ 2) =
      (s : ℝ) / (512 * ((s : ℝ) + 1) ^ 2) := by push_cast; ring
  rw [e]
  have : (s : ℝ) / (512 * ((s : ℝ) + 1) ^ 2) < 1 / 80 := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  linarith

/-- Paper: `lem:fixed-rank-bernstein` (tanh_bernstein_product.tex), proof: with
`‖f‖ ≤ 4/5`, the base coefficients satisfy `‖G_{m_0}‖ < 7/8`. -/
theorem base_coefficient_lt (fnorm err : ℝ) (hf : fnorm ≤ 4 / 5) (herr : err < 3 / 40) :
    fnorm + err < 7 / 8 := by linarith

/-- Paper: `lem:fixed-rank-bernstein` (tanh_bernstein_product.tex), proof: the
correction branches at levels `m = 2^a m_0`, each of the `r` types with mass
`c_m = Ā/(4m^2)`, have total mass `r Ā/(3 m_0^2)`. -/
theorem correction_mass_hasSum (r : ℕ) (m0 A : ℝ) (hm0 : 0 < m0) :
    HasSum (fun a : ℕ => (r : ℝ) * (A / (4 * (2 ^ a * m0) ^ 2)))
      ((r : ℝ) * A / (3 * m0 ^ 2)) := by
  have hg := (hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)).mul_left
    ((r : ℝ) * A / (4 * m0 ^ 2))
  convert hg using 1
  · funext a
    have h4 : ((2 : ℝ) ^ a) ^ 2 = 4 ^ a := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [mul_pow, h4, one_div_pow]
    field_simp
  · field_simp; ring

/-- Paper: `lem:fixed-rank-bernstein` (tanh_bernstein_product.tex), proof: each
correction at level `m` uses at most `2rm` source bits, so the corrections cost
`∑_a 2r^2 (2^a m_0) c_{2^a m_0} = r^2 Ā/m_0` in expectation. -/
theorem correction_sources_hasSum (r : ℕ) (m0 A : ℝ) (hm0 : 0 < m0) :
    HasSum (fun a : ℕ => 2 * (r : ℝ) ^ 2 * (2 ^ a * m0) * (A / (4 * (2 ^ a * m0) ^ 2)))
      ((r : ℝ) ^ 2 * A / m0) := by
  have hg := (hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left
    ((r : ℝ) ^ 2 * A / (2 * m0))
  convert hg using 1
  · funext a
    have h2 : (0 : ℝ) < 2 ^ a := by positivity
    rw [one_div_pow]
    field_simp
    ring
  · field_simp; ring

/-- Paper: `lem:fixed-rank-bernstein` (tanh_bernstein_product.tex), proof: if
`Ā ≤ m_0^2/(8r)` then the correction mass `r Ā/(3m_0^2)` is at most `1/24`,
leaving the fair-sign remainder `1 - 7/8 - rĀ/(3m_0^2) ≥ 1/12`. -/
theorem correction_mass_le (r : ℕ) (hr : 1 ≤ r) (m0 A : ℝ) (hm0 : 0 < m0)
    (hA : A ≤ m0 ^ 2 / (8 * r)) :
    (r : ℝ) * A / (3 * m0 ^ 2) ≤ 1 / 24 ∧ 1 / 12 ≤ 1 - 7 / 8 - (r : ℝ) * A / (3 * m0 ^ 2) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have h : (r : ℝ) * A / (3 * m0 ^ 2) ≤ 1 / 24 := by
    rw [div_le_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at hA
    nlinarith
  exact ⟨h, by linarith⟩

/-- Paper: `lem:fixed-rank-bernstein` (tanh_bernstein_product.tex): the expected
number of source bits is `7r m_0/8 + r^2 Ā/m_0 ≤ r m_0`. -/
theorem fixed_rank_source_bound (r : ℕ) (hr : 1 ≤ r) (m0 A : ℝ) (hm0 : 0 < m0)
    (hA : A ≤ m0 ^ 2 / (8 * r)) :
    7 * (r : ℝ) / 8 * m0 + (r : ℝ) ^ 2 * A / m0 ≤ r * m0 := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have h : (r : ℝ) ^ 2 * A / m0 ≤ r * m0 / 8 := by
    rw [div_le_iff₀ hm0]
    rw [le_div_iff₀ (by positivity)] at hA
    nlinarith
  linarith

/-! ## Two and three variables -/

/-- Paper: `lem:rank-two-bernstein` (tanh_rank_two.tex), proof: the starting
conditions `m_0^2 ≥ 32 S` and `m_0^3 ≥ 4U` give `Ā = S + U/(8m_0) ≤ m_0^2/16`. -/
theorem envelope_bound (m S U : ℝ) (hm : 0 < m)
    (hS : 32 * S ≤ m ^ 2) (hU : 4 * U ≤ m ^ 3) :
    S + U / (8 * m) ≤ m ^ 2 / 16 := by
  have hS' : S ≤ m ^ 2 / 32 := by linarith
  have hU' : U / (8 * m) ≤ m ^ 2 / 32 := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * m)).2
    nlinarith [hU]
  linarith

/-- Paper: `lem:rank-two-bernstein` (tanh_rank_two.tex) via
`lem:fixed-rank-bernstein`: the two-variable base coefficient keeps a strict
margin, `4/5 + M_2/(8m_0) + M_4/(64 m_0^2) < 7/8`. -/
theorem base_margin (m M₂ M₄ : ℝ) (hm : 0 < m)
    (h₂ : 2 * M₂ ≤ m) (h₄ : 32 * M₄ ≤ m ^ 2) :
    (4 : ℝ) / 5 + M₂ / (8 * m) + M₄ / (64 * m ^ 2) < 7 / 8 := by
  have h₂' : M₂ / (8 * m) ≤ (1 : ℝ) / 16 := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * m)).2
    nlinarith
  have h₄' : M₄ / (64 * m ^ 2) ≤ (1 : ℝ) / 2048 := by
    apply (div_le_iff₀ (by positivity : 0 < 64 * m ^ 2)).2
    nlinarith
  linarith

/-- Paper: `lem:rank-two-bernstein` (tanh_rank_two.tex): two correction types
use mass at most `2Ā/(3m_0^2) ≤ 1/24`. -/
theorem correction_mass_bound (m A : ℝ) (hm : 0 < m) (hA : A ≤ m ^ 2 / 16) :
    2 * A / (3 * m ^ 2) ≤ (1 : ℝ) / 24 := by
  apply (div_le_iff₀ (by positivity : 0 < 3 * m ^ 2)).2
  nlinarith

/-- Paper: `lem:rank-two-bernstein` (tanh_rank_two.tex): the source bound
`7m_0/4 + 4Ā/m_0 ≤ 2m_0`. -/
theorem conditional_source_bound (m A : ℝ) (hm : 0 < m) (hA : A ≤ m ^ 2 / 16) :
    (7 : ℝ) / 4 * m + 4 * A / m ≤ 2 * m := by
  have hterm : 4 * A / m ≤ m / 4 := by
    apply (div_le_iff₀ hm).2
    nlinarith
  linarith

/-- Paper: `thm:rank-three-critical` (tanh_rank_three.tex) via
`lem:fixed-rank-bernstein` at `r = 3`: the starting conditions give
`S_0 + S_1/(8m_0) + S_2/(64m_0^2) ≤ m_0^2/24`. -/
theorem rank_three_envelope (m S₀ S₁ S₂ : ℝ) (hm : 0 < m)
    (h₀ : 72 * S₀ ≤ m ^ 2) (h₁ : 9 * S₁ ≤ m ^ 3) (h₂ : 9 * S₂ ≤ 8 * m ^ 4) :
    S₀ + S₁ / (8 * m) + S₂ / (64 * m ^ 2) ≤ m ^ 2 / 24 := by
  have ha : S₀ ≤ m ^ 2 / 72 := by linarith
  have hb : S₁ / (8 * m) ≤ m ^ 2 / 72 := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * m)).2
    nlinarith
  have hc : S₂ / (64 * m ^ 2) ≤ m ^ 2 / 72 := by
    apply (div_le_iff₀ (by positivity : 0 < 64 * m ^ 2)).2
    nlinarith
  linarith

/-- Paper: `thm:rank-three-critical` (tanh_rank_three.tex) via
`lem:fixed-rank-bernstein` at `r = 3`: `21m_0/8 + 9Ā/m_0 ≤ 3m_0`. -/
theorem rank_three_sources (m A : ℝ) (hm : 0 < m) (hA : A ≤ m ^ 2 / 24) :
    (21 : ℝ) / 8 * m + 9 * A / m ≤ 3 * m := by
  have ht : 9 * A / m ≤ (3 : ℝ) / 8 * m := by
    apply (div_le_iff₀ hm).2
    nlinarith
  linarith

/-- Paper: `thm:rank-two-critical` (tanh_rank_two.tex): an amplitude gate
`q ≤ C/s` and conditional work `w ≤ 2m_0`, `m_0 ≤ K s^2`, give unconditional
work `q w ≤ 2CKs`, with `s = √D`. The hypothesis `hm` stands in for the
analytic induction giving `m_0 = O(D+1)` (see the module header). -/
theorem gate_work_bound (q w m C K s : ℝ)
    (hq0 : 0 ≤ q) (hm0 : 0 ≤ m) (hC0 : 0 ≤ C)
    (hs : 0 < s) (hq : q ≤ C / s) (hw : w ≤ 2 * m) (hm : m ≤ K * s ^ 2) :
    q * w ≤ 2 * C * K * s := by
  calc
    q * w ≤ q * (2 * m) := mul_le_mul_of_nonneg_left hw hq0
    _ ≤ (C / s) * (2 * m) := mul_le_mul_of_nonneg_right hq (by positivity)
    _ ≤ (C / s) * (2 * (K * s ^ 2)) := by
      apply mul_le_mul_of_nonneg_left
      · linarith
      · positivity
    _ = 2 * C * K * s := by
      field_simp [ne_of_gt hs]

/-! ## Seven-product block multiplication -/

section Strassen
variable {R : Type*} [Ring R] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : R)

/-- The seven products of `thm:rank-three-critical` (tanh_rank_three.tex). -/
def strassenQ : Fin 7 → R
  | 0 => (a₁₁ + a₂₂) * (b₁₁ + b₂₂)
  | 1 => (a₂₁ + a₂₂) * b₁₁
  | 2 => a₁₁ * (b₁₂ - b₂₂)
  | 3 => a₂₂ * (b₂₁ - b₁₁)
  | 4 => (a₁₁ + a₁₂) * b₂₂
  | 5 => (a₂₁ - a₁₁) * (b₁₁ + b₁₂)
  | 6 => (a₁₂ - a₂₂) * (b₂₁ + b₂₂)

/-- Paper: `thm:rank-three-critical` (tanh_rank_three.tex):
`C₁₁ = Q₁ + Q₄ - Q₅ + Q₇`, over any (noncommutative) ring of blocks. -/
theorem strassen_c11 :
    let Q := strassenQ a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂
    Q 0 + Q 3 - Q 4 + Q 6 = a₁₁ * b₁₁ + a₁₂ * b₂₁ := by
  simp only [strassenQ]; noncomm_ring

/-- Paper: `thm:rank-three-critical` (tanh_rank_three.tex): `C₁₂ = Q₃ + Q₅`. -/
theorem strassen_c12 :
    let Q := strassenQ a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂
    Q 2 + Q 4 = a₁₁ * b₁₂ + a₁₂ * b₂₂ := by
  simp only [strassenQ]; noncomm_ring

/-- Paper: `thm:rank-three-critical` (tanh_rank_three.tex): `C₂₁ = Q₂ + Q₄`. -/
theorem strassen_c21 :
    let Q := strassenQ a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂
    Q 1 + Q 3 = a₂₁ * b₁₁ + a₂₂ * b₂₁ := by
  simp only [strassenQ]; noncomm_ring

/-- Paper: `thm:rank-three-critical` (tanh_rank_three.tex):
`C₂₂ = Q₁ - Q₂ + Q₃ + Q₆`. -/
theorem strassen_c22 :
    let Q := strassenQ a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂
    Q 0 - Q 1 + Q 2 + Q 5 = a₂₁ * b₁₂ + a₂₂ * b₂₂ := by
  simp only [strassenQ]; noncomm_ring

end Strassen

/-- Paper: `thm:rank-three-critical` (tanh_rank_three.tex): `7^6 < 2^17`. -/
theorem seven_product_integer_margin : (7 : ℕ) ^ 6 < 2 ^ 17 := by
  norm_num

/-- Paper: `thm:rank-three-critical` (tanh_rank_three.tex): `ω = log_2 7 < 17/6`. -/
theorem log_two_seven_lt : Real.logb 2 7 < 17 / 6 := by
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
  have h : ((7 : ℝ)) ^ (6 : ℕ) < ((2 : ℝ) ^ ((17 : ℝ) / 6)) ^ (6 : ℕ) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((17 : ℝ) / 6)) 6,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      show (17 : ℝ) / 6 * ((6 : ℕ) : ℝ) = ((17 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
    norm_num
  exact lt_of_pow_lt_pow_left₀ 6 (by positivity) h

/-- Paper: `thm:rank-three-critical` (tanh_rank_three.tex): the dense logarithmic
exponent `3 + (9/2)(ω - 2)` is below `27/4 < 7`. -/
theorem rank_three_dense_exponent :
    3 + 9 / 2 * (Real.logb 2 7 - 2) < 27 / 4 ∧ (27 : ℝ) / 4 < 7 := by
  have h := log_two_seven_lt
  constructor <;> linarith

end ExactSampling.RankTwoBernstein
