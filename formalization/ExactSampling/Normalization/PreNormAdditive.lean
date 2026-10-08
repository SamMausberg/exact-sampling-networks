import Mathlib

/-!
# Additive composition and pre-norm sampling

This module formalizes the quantitative content of `thm:pn-abstract`, `thm:pn-relative` and
`cor:pn-stepsizes` (normalization_additive.tex), restated as `thm:main-additive`
(main_normalization.tex), together with the radius bookkeeping of
`cor:pn-effective-threshold` (normalization_depth_lower.tex).

Indexing. The paper indexes sublayers by `j = 1, …, J`. Here updates are indexed from `0`:
update `k` carries level `k` to level `k+1`, so the paper's `U_j, m_j, L_j` are `U (j-1)`, etc.,
`R j = 1 + ∑_{k<j} U k`, and `P j = ∏_{k<j} (1 + U k m k / R k)` is the paper's `P_j`.

Formalized here:
* exactness of the additive mixture, the identity-chain telescoping, the direct origin law
  (`U_k/R_j` and `1/R_j`, summing to one);
* `eq:pn-leaf-product`: any leaf recurrence `C_{j+1} ≤ ((R_j + U_j m_j)/R_{j+1}) C_j`, `C_0 ≤ 1`
  gives `C_J ≤ P_J/R_J`;
* `eq:pn-bit-product`: the equality majorant `W`, its recurrence, its closed form
  `W_j/P_j = c(2 + ∑_k U_k(1+L_k)/P_{k+1})`, and the domination `R_j T_j ≤ W_j` for every work
  sequence obeying the charging inequality of the proof;
* the uniform bounds: Bernoulli's inequality gives `P_J/R_J ≤ R_J^{m-1}`, and
  `∑_k U_k/P̂_{k+1} ≤ ∑_k U_k/R_{k+1} ≤ log R_J`, hence `eq:pn-sharp-bit-bound`;
* `thm:pn-relative`: the power-of-two gain `2/√γ ≤ G < 4/√γ`, the condition number and natural
  radius of each normalization under the relative floor, the radii `R_{2D} = 1 + D(sG+1)` and,
  with steps, `1 + αD(sG+1)`, and the resulting leaf bound `R_{2D}^{m-1}`.

The bit-work statements (`bit_product`, `sharp_bit_bound`) are formalized at the level of the
work recurrence: the charging inequality `R_j T_j ≤ c(R_j + 1) + ∑_{k<j} U_k(cL_k + m_kT_k)`
for a sequence of finite nonnegative reals `T_j` (the output of conditional charging) is a
hypothesis, and the conclusion is the paper's bound.

Not formalized: the sampler as a randomized algorithm and conditional charging itself; the
prefix-table implementation and its `O(B³)` draw; the weight-preparation cost `O(Dn²B⁶)` of
`thm:pn-relative`; the local factories (`thm:rmsfloor`, `thm:attentionprimitive`,
`cor:comptanhrow`), whose counts enter only as the budgets `m_j, L_j`; the specific constants
`K = 1 + 228k²`, `m_A`, `L_A`, `m_F`, `L_F` of `thm:pn-relative` and `eq:main-prenorm-m`
(main_normalization.tex), which are taken as given budgets; the head bounds of `thm:pn-relative`
(the unnormalized coordinate head `R_{2D}^{m+1}` and `eq:pn-finalnorm`); and the bit-level
`O(B⁴)` accounting inside each step.
-/

open Real Finset
open scoped BigOperators

namespace ExactSampling.PreNormAdditive

/-- The radius prefix `R_j = 1 + ∑_{k<j} U_k`. -/
noncomputable def radius (U : ℕ → ℝ) (j : ℕ) : ℝ := 1 + ∑ k ∈ range j, U k

/-- The product `P_j = ∏_{k<j} (1 + U_k m_k / R_k)`. -/
noncomputable def prodP (U m : ℕ → ℝ) (j : ℕ) : ℝ := ∏ k ∈ range j, (1 + U k * m k / radius U k)

/-- `R_0 = 1`. -/
theorem radius_zero (U : ℕ → ℝ) : radius U 0 = 1 := by simp [radius]

/-- `R_{j+1} = R_j + U_j`. -/
theorem radius_succ (U : ℕ → ℝ) (j : ℕ) : radius U (j + 1) = radius U j + U j := by
  simp [radius, sum_range_succ]; ring

/-- `R_j ≥ 1` for nonnegative update radii. -/
theorem radius_ge_one {U : ℕ → ℝ} (hU : ∀ k, 0 ≤ U k) (j : ℕ) : 1 ≤ radius U j := by
  unfold radius
  have := sum_nonneg (fun k (_ : k ∈ range j) => hU k)
  linarith

/-- `R_j > 0` for nonnegative update radii. -/
theorem radius_pos {U : ℕ → ℝ} (hU : ∀ k, 0 ≤ U k) (j : ℕ) : 0 < radius U j :=
  lt_of_lt_of_le one_pos (radius_ge_one hU j)

/-- `P_{j+1} = P_j (1 + U_j m_j/R_j)`. -/
theorem prodP_succ (U m : ℕ → ℝ) (j : ℕ) :
    prodP U m (j + 1) = prodP U m j * (1 + U j * m j / radius U j) := by
  simp [prodP, prod_range_succ]

/-- `P_j > 0` for nonnegative radii and budgets. -/
theorem prodP_pos {U m : ℕ → ℝ} (hU : ∀ k, 0 ≤ U k) (hm : ∀ k, 0 ≤ m k) (j : ℕ) :
    0 < prodP U m j := by
  unfold prodP
  apply prod_pos
  intro k _
  have := radius_pos hU k
  have := hU k; have := hm k
  positivity

/-! ## Exactness of the additive mixture -/

/-- Exactness of one additive residual mixture: the identity branch with probability `r/(r+u)`
and the update branch with probability `u/(r+u)` have means summing to `(h+f)/(r+u)`.
Paper: proof of `thm:pn-abstract` (normalization_additive.tex). -/
theorem additive_mixture_mean (r u h f : ℝ) (hr : r ≠ 0) (hu : u ≠ 0) (hs : r + u ≠ 0) :
    (r / (r + u)) * (h / r) + (u / (r + u)) * (f / u) = (h + f) / (r + u) := by
  field_simp

/-- Finite identity-chain probabilities telescope.
Paper: proof of `thm:pn-abstract` (normalization_additive.tex). -/
theorem identity_chain_telescope (R : ℕ → ℝ) (hR : ∀ k, R k ≠ 0) (n : ℕ) :
    (∏ k ∈ range n, R k / R (k + 1)) = R 0 / R n := by
  induction n with
  | zero => simp [hR 0]
  | succ n ih =>
    rw [prod_range_succ, ih]
    field_simp [hR n, hR (n + 1)]

/-- Selecting an origin after its identity suffix cancels its radius.
Paper: proof of `thm:pn-abstract` (normalization_additive.tex). -/
theorem origin_probability (r R u : ℝ) (hr : r ≠ 0) (hR : R ≠ 0) : (r / R) * (u / r) = u / R := by
  field_simp

/-- The direct origin law. Starting at level `j`, the first selected update is `k < j` with
probability `(∏_{ℓ=k+1}^{j-1} R_ℓ/R_{ℓ+1}) · U_k/R_{k+1} = U_k/R_j`, and the input is reached
with probability `∏_{ℓ<j} R_ℓ/R_{ℓ+1} = 1/R_j`.
Paper: proof of `thm:pn-abstract` (normalization_additive.tex). -/
theorem direct_origin_law {U : ℕ → ℝ} (hU : ∀ k, 0 ≤ U k) {k j : ℕ} (hkj : k < j) :
    (∏ ℓ ∈ Ico (k + 1) j, radius U ℓ / radius U (ℓ + 1)) * (U k / radius U (k + 1))
        = U k / radius U j ∧
      ∏ ℓ ∈ range j, radius U ℓ / radius U (ℓ + 1) = 1 / radius U j := by
  have hR : ∀ ℓ, radius U ℓ ≠ 0 := fun ℓ => (radius_pos hU ℓ).ne'
  constructor
  · have htel : ∀ n, ∏ ℓ ∈ Ico (k + 1) (k + 1 + n), radius U ℓ / radius U (ℓ + 1)
        = radius U (k + 1) / radius U (k + 1 + n) := by
      intro n
      induction n with
      | zero => simp [div_self (hR _)]
      | succ n ih =>
        rw [← add_assoc, prod_Ico_succ_top (by omega), ih]
        field_simp [hR (k + 1 + n), hR (k + 1 + n + 1)]
    obtain ⟨n, rfl⟩ : ∃ n, j = k + 1 + n := ⟨j - (k + 1), by omega⟩
    rw [htel]
    field_simp [hR (k + 1), hR (k + 1 + n)]
  · rw [identity_chain_telescope _ hR, radius_zero]

/-- The origin masses `1/R_j` and `U_k/R_j` sum to one.
Paper: proof of `thm:pn-abstract` (normalization_additive.tex); `cor:pn-stepsizes`. -/
theorem origin_mass {U : ℕ → ℝ} (hU : ∀ k, 0 ≤ U k) (j : ℕ) :
    1 / radius U j + ∑ k ∈ range j, U k / radius U j = 1 := by
  have hR := (radius_pos hU j).ne'
  rw [← sum_div, ← add_div]
  unfold radius at hR ⊢
  exact div_self hR

/-- The general version over an arbitrary finite index set.
Paper: proof of `thm:pn-abstract` (normalization_additive.tex). -/
theorem origin_mass' {ι : Type*} (S : Finset ι) (U : ι → ℝ) (hR : 1 + ∑ k ∈ S, U k ≠ 0) :
    1 / (1 + ∑ k ∈ S, U k) + (∑ k ∈ S, U k / (1 + ∑ k ∈ S, U k)) = 1 := by
  rw [← Finset.sum_div]
  field_simp

/-! ## The leaf product (`eq:pn-leaf-product`) -/

/-- Radius ratios telescope in the expected offspring product:
`(r + u m)/(r + u) = (r/(r+u))(1 + u m / r)`.
Paper: proof of `thm:pn-abstract` (normalization_additive.tex). -/
theorem offspring_factor (r u m : ℝ) (hr : r ≠ 0) (hs : r + u ≠ 0) :
    (r + u * m) / (r + u) = (r / (r + u)) * (1 + u * m / r) := by
  field_simp

/-- **The leaf product.** If the mean input-leaf counts satisfy `C_0 ≤ 1` and
`C_{j+1} ≤ ((R_j + U_j m_j)/R_{j+1}) C_j`, then `C_J ≤ P_J / R_J`.
Paper: `eq:pn-leaf-product` in `thm:pn-abstract` (normalization_additive.tex);
`thm:main-additive` (main_normalization.tex). -/
theorem leaf_product {U m C : ℕ → ℝ} (hU : ∀ k, 0 ≤ U k) (hm : ∀ k, 0 ≤ m k) (hC0 : C 0 ≤ 1)
    (hrec : ∀ j, C (j + 1) ≤ (radius U j + U j * m j) / radius U (j + 1) * C j) (J : ℕ) :
    C J ≤ prodP U m J / radius U J := by
  induction J with
  | zero => simp [prodP, radius_zero, hC0]
  | succ j ih =>
    have hRj := radius_pos hU j
    have hRj1 := radius_pos hU (j + 1)
    have hcoef : 0 ≤ (radius U j + U j * m j) / radius U (j + 1) := by
      have := hU j; have := hm j; positivity
    calc C (j + 1) ≤ (radius U j + U j * m j) / radius U (j + 1) * C j := hrec j
      _ ≤ (radius U j + U j * m j) / radius U (j + 1) * (prodP U m j / radius U j) :=
          mul_le_mul_of_nonneg_left ih hcoef
      _ = prodP U m (j + 1) / radius U (j + 1) := by
          rw [prodP_succ]
          field_simp

/-! ## The bit-work product (`eq:pn-bit-product`) -/

/-- The equality majorant `W`: `W_0 = 2c`, `W_{j+1} = (1 + U_j m_j/R_j) W_j + c U_j (1 + L_j)`. -/
noncomputable def workMajorant (U m L : ℕ → ℝ) (c : ℝ) : ℕ → ℝ
  | 0 => 2 * c
  | j + 1 => (1 + U j * m j / radius U j) * workMajorant U m L c j + c * U j * (1 + L j)

/-- Subtracting successive equalities: `W_j` is the equality majorant of the charging
recurrence, `W_j = c(R_j + 1) + ∑_{k<j} U_k (c L_k + m_k W_k/R_k)`.
Paper: proof of `thm:pn-abstract` (normalization_additive.tex). -/
theorem workMajorant_eq {U m L : ℕ → ℝ} (hU : ∀ k, 0 ≤ U k) (c : ℝ) (j : ℕ) :
    workMajorant U m L c j = c * (radius U j + 1)
      + ∑ k ∈ range j, U k * (c * L k + m k * (workMajorant U m L c k / radius U k)) := by
  induction j with
  | zero => simp [workMajorant, radius_zero]; ring
  | succ j ih =>
    rw [workMajorant, sum_range_succ, radius_succ, ← add_assoc]
    have hR := (radius_pos hU j).ne'
    have hs : c * (radius U j + U j + 1)
        + ∑ k ∈ range j, U k * (c * L k + m k * (workMajorant U m L c k / radius U k))
        = workMajorant U m L c j + c * U j := by rw [ih]; ring
    rw [hs]
    field_simp
    ring

/-- One step of the heterogeneous additive work certificate:
`(gW + C U(1+L))/(Pg) = W/P + C U(1+L)/(Pg)`.
Paper: proof of `thm:pn-abstract` (normalization_additive.tex). -/
theorem work_majorant_product_step (P g W C U L : ℝ) (hP : P ≠ 0) (hg : g ≠ 0) :
    (g * W + C * U * (1 + L)) / (P * g) = W / P + C * U * (1 + L) / (P * g) := by
  field_simp

/-- Division by `P_j` and summation: `W_j / P_j = c (2 + ∑_{k<j} U_k (1 + L_k)/P_{k+1})`.
Paper: proof of `thm:pn-abstract` (normalization_additive.tex). -/
theorem workMajorant_closed {U m L : ℕ → ℝ} (hU : ∀ k, 0 ≤ U k) (hm : ∀ k, 0 ≤ m k) (c : ℝ)
    (j : ℕ) : workMajorant U m L c j / prodP U m j
      = c * (2 + ∑ k ∈ range j, U k * (1 + L k) / prodP U m (k + 1)) := by
  induction j with
  | zero => simp [workMajorant, prodP]; ring
  | succ j ih =>
    rw [workMajorant, prodP_succ, sum_range_succ]
    have hP := (prodP_pos hU hm j).ne'
    have hg : (1 + U j * m j / radius U j) ≠ 0 := by
      have := radius_pos hU j; have := hU j; have := hm j; positivity
    rw [work_majorant_product_step _ _ _ _ _ _ hP hg, ih, prodP_succ]
    ring

/-- The majorant dominates the work. The work sequence `T_j` (finite real numbers) is assumed
to satisfy the charging inequality `R_j T_j ≤ c(R_j + 1) + ∑_{k<j} U_k (c L_k + m_k T_k)` for
every `j`; this inequality is the output of conditional charging in the paper and is a
hypothesis here. Then `R_j T_j ≤ W_j`.
Paper: proof of `thm:pn-abstract` (normalization_additive.tex). -/
theorem work_le_majorant {U m L T : ℕ → ℝ} {c : ℝ} (hU : ∀ k, 0 ≤ U k) (hm : ∀ k, 0 ≤ m k)
    (hT : ∀ j, radius U j * T j
      ≤ c * (radius U j + 1) + ∑ k ∈ range j, U k * (c * L k + m k * T k)) (j : ℕ) :
    radius U j * T j ≤ workMajorant U m L c j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rw [workMajorant_eq hU c j]
    refine le_trans (hT j) (add_le_add le_rfl ?_)
    apply sum_le_sum
    intro k hk
    have hk' := mem_range.1 hk
    have hR := radius_pos hU k
    have hTk : T k ≤ workMajorant U m L c k / radius U k := by
      rw [le_div_iff₀ hR, mul_comm]; exact ih k hk'
    apply mul_le_mul_of_nonneg_left _ (hU k)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hTk (hm k))

/-- **The bit-work product.** For a finite real work sequence satisfying the charging inequality
(the output of conditional charging, assumed here),
`T_J ≤ c (P_J/R_J) (2 + ∑_{k<J} U_k (1 + L_k)/P_{k+1})`.
Paper: `eq:pn-bit-product` in `thm:pn-abstract` (normalization_additive.tex);
`eq:main-additive-cost` (main_normalization.tex). -/
theorem bit_product {U m L T : ℕ → ℝ} {c : ℝ} (hU : ∀ k, 0 ≤ U k) (hm : ∀ k, 0 ≤ m k)
    (hT : ∀ j, radius U j * T j
      ≤ c * (radius U j + 1) + ∑ k ∈ range j, U k * (c * L k + m k * T k)) (J : ℕ) :
    T J ≤ c * (prodP U m J / radius U J)
      * (2 + ∑ k ∈ range J, U k * (1 + L k) / prodP U m (k + 1)) := by
  have h := work_le_majorant (L := L) hU hm hT J
  have hR := radius_pos hU J
  have hP := prodP_pos hU hm J
  have hc := workMajorant_closed (L := L) hU hm c J
  rw [div_eq_iff hP.ne'] at hc
  rw [hc] at h
  rw [← le_div_iff₀' hR] at h
  calc T J ≤ c * (2 + ∑ k ∈ range J, U k * (1 + L k) / prodP U m (k + 1)) * prodP U m J
        / radius U J := h
    _ = _ := by ring

/-! ## Uniform budgets -/

/-- Bernoulli's inequality across the product: with `m_k ≤ m`, `m ≥ 1`,
`P_J ≤ ∏ (1 + m U_k/R_k) ≤ R_J^m`.
Paper: proof of `thm:pn-abstract` (normalization_additive.tex), the uniform bounds. -/
theorem prodP_le_rpow {U mk : ℕ → ℝ} {m : ℝ} (hU : ∀ k, 0 ≤ U k) (hmk : ∀ k, 0 ≤ mk k)
    (hm1 : 1 ≤ m) (hmm : ∀ k, mk k ≤ m) (J : ℕ) :
    prodP U mk J ≤ radius U J ^ m := by
  induction J with
  | zero => simp [prodP, radius_zero]
  | succ j ih =>
    rw [prodP_succ]
    have hRj := radius_pos hU j
    have hRj1 := radius_pos hU (j + 1)
    have hx : 0 ≤ U j / radius U j := div_nonneg (hU j) hRj.le
    have hbern : 1 + m * (U j / radius U j) ≤ (1 + U j / radius U j) ^ m :=
      one_add_mul_self_le_rpow_one_add (by linarith) hm1
    have hstep : 1 + U j * mk j / radius U j ≤ 1 + m * (U j / radius U j) := by
      have : U j * mk j / radius U j = mk j * (U j / radius U j) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_right (hmm j) hx
      linarith
    have hratio : 1 + U j / radius U j = radius U (j + 1) / radius U j := by
      rw [radius_succ]; field_simp
    have h0 : 0 ≤ 1 + U j * mk j / radius U j := by have := hmk j; have := hU j; positivity
    calc prodP U mk j * (1 + U j * mk j / radius U j)
        ≤ radius U j ^ m * (radius U (j + 1) / radius U j) ^ m := by
          apply mul_le_mul ih (le_trans hstep (by rw [← hratio]; exact hbern)) h0
          exact rpow_nonneg hRj.le _
      _ = radius U (j + 1) ^ m := by
          rw [← mul_rpow hRj.le (div_nonneg hRj1.le hRj.le)]
          congr 1; field_simp

/-- **The uniform leaf bound.** If `m_k ≤ m` with `m ≥ 1`, then `P_J/R_J ≤ R_J^{m-1}`.
Paper: `thm:pn-abstract` (normalization_additive.tex), the bound `R_J^{m-1}`;
`thm:main-additive` (main_normalization.tex). -/
theorem uniform_leaf_bound {U mk : ℕ → ℝ} {m : ℝ} (hU : ∀ k, 0 ≤ U k) (hmk : ∀ k, 0 ≤ mk k)
    (hm1 : 1 ≤ m) (hmm : ∀ k, mk k ≤ m) (J : ℕ) :
    prodP U mk J / radius U J ≤ radius U J ^ (m - 1) := by
  have hR := radius_pos hU J
  rw [div_le_iff₀ hR, rpow_sub hR, rpow_one, div_mul_cancel₀ _ hR.ne']
  exact prodP_le_rpow hU hmk hm1 hmm J

/-- The enlarged product dominates the stored radius: if `R ≤ P` and `c ≥ 1` then
`R + u ≤ P (1 + u c / R)`; this is the induction step of `radius_le_prodP`.
Paper: proof of `thm:pn-abstract` (normalization_additive.tex). -/
theorem prefix_domination_step (P R u c : ℝ) (hR : 0 < R) (hu : 0 ≤ u) (hc : 1 ≤ c)
    (hP : R ≤ P) : R + u ≤ P * (1 + u * c / R) := by
  have hRatio : 1 ≤ P / R := (le_div_iff₀ hR).2 (by simpa using hP)
  have huc : u ≤ u * c := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hRatio (mul_nonneg hu (by linarith : 0 ≤ c))
  have hid : P * (1 + u * c / R) = P + (u * c) * (P / R) := by field_simp
  rw [hid]
  nlinarith

/-- The radius is dominated by the product with a budget `m ≥ 1`: `R_J ≤ ∏ (1 + m U_k/R_k)`.
Paper: proof of `thm:pn-abstract` (normalization_additive.tex), `P̂_j ≥ R_j`. -/
theorem radius_le_prodP {U : ℕ → ℝ} {m : ℝ} (hU : ∀ k, 0 ≤ U k) (hm1 : 1 ≤ m) (J : ℕ) :
    radius U J ≤ prodP U (fun _ => m) J := by
  induction J with
  | zero => simp [prodP, radius_zero]
  | succ j ih =>
    rw [radius_succ, prodP_succ]
    exact prefix_domination_step _ _ _ _ (radius_pos hU j) (hU j) hm1 ih

/-- `∑_{k<J} U_k / R_{k+1} ≤ log R_J`, by integrating `1/r` over each `[R_k, R_{k+1}]`.
Paper: proof of `thm:pn-abstract` (normalization_additive.tex). -/
theorem sum_le_log_radius {U : ℕ → ℝ} (hU : ∀ k, 0 ≤ U k) (J : ℕ) :
    ∑ k ∈ range J, U k / radius U (k + 1) ≤ log (radius U J) := by
  induction J with
  | zero => simp [radius_zero]
  | succ j ih =>
    rw [sum_range_succ]
    have hRj := radius_pos hU j
    have hRj1 := radius_pos hU (j + 1)
    have hstep : U j / radius U (j + 1) ≤ log (radius U (j + 1)) - log (radius U j) := by
      rw [← log_div hRj1.ne' hRj.ne']
      have := one_sub_inv_le_log_of_pos (div_pos hRj1 hRj)
      have e : 1 - (radius U (j + 1) / radius U j)⁻¹ = U j / radius U (j + 1) := by
        have hne : radius U j + U j ≠ 0 := by rw [← radius_succ]; exact hRj1.ne'
        rw [inv_div, radius_succ]; field_simp; ring
      linarith
    linarith

/-- With the uniform budget `m ≥ 1`, `∑_{k<J} U_k / P̂_{k+1} ≤ log R_J`.
Paper: proof of `thm:pn-abstract` (normalization_additive.tex). -/
theorem sum_le_log_prodP {U : ℕ → ℝ} {m : ℝ} (hU : ∀ k, 0 ≤ U k) (hm1 : 1 ≤ m) (J : ℕ) :
    ∑ k ∈ range J, U k / prodP U (fun _ => m) (k + 1) ≤ log (radius U J) := by
  refine le_trans (sum_le_sum (fun k _ => ?_)) (sum_le_log_radius hU J)
  exact div_le_div_of_nonneg_left (hU k) (radius_pos hU (k + 1)) (radius_le_prodP hU hm1 (k + 1))

/-- **The sharp bit bound.** If a finite nonnegative work sequence satisfies the charging
inequality (the output of conditional charging, assumed here) with budgets `m_k ≤ m`, `m ≥ 1`,
and `L_k ≤ L`, `L ≥ 0`, `c ≥ 0`, then `T_J ≤ c (2 + L)(1 + log R_J) R_J^{m-1}`.
Paper: `eq:pn-sharp-bit-bound` in `thm:pn-abstract` (normalization_additive.tex);
`thm:main-additive` (main_normalization.tex). -/
theorem sharp_bit_bound {U mk Lk T : ℕ → ℝ} {c m L : ℝ} (hU : ∀ k, 0 ≤ U k) (hm1 : 1 ≤ m)
    (hmm : ∀ k, mk k ≤ m) (hLL : ∀ k, Lk k ≤ L)
    (hc : 0 ≤ c) (hL : 0 ≤ L) (hT0 : ∀ j, 0 ≤ T j)
    (hT : ∀ j, radius U j * T j
      ≤ c * (radius U j + 1) + ∑ k ∈ range j, U k * (c * Lk k + mk k * T k)) (J : ℕ) :
    T J ≤ c * (2 + L) * (1 + log (radius U J)) * radius U J ^ (m - 1) := by
  -- the same inequality holds with the constant budgets
  have hT' : ∀ j, radius U j * T j ≤ c * (radius U j + 1)
      + ∑ k ∈ range j, U k * (c * (fun _ => L) k + (fun _ => m) k * T k) := by
    intro j
    refine le_trans (hT j) (add_le_add le_rfl (sum_le_sum (fun k _ => ?_)))
    apply mul_le_mul_of_nonneg_left _ (hU k)
    have h1 := mul_le_mul_of_nonneg_left (hLL k) hc
    have h2 := mul_le_mul_of_nonneg_right (hmm k) (hT0 k)
    simp only
    linarith
  have hm0 : ∀ k : ℕ, (0 : ℝ) ≤ (fun _ : ℕ => m) k := fun _ => by simp only; linarith
  have hb := bit_product (L := fun _ => L) hU hm0 hT' J
  have hR := radius_pos hU J
  have hleaf := uniform_leaf_bound (mk := fun _ => m) hU hm0 hm1 (fun _ => le_rfl) J
  have hsum : ∑ k ∈ range J, U k * (1 + L) / prodP U (fun _ => m) (k + 1)
      ≤ (1 + L) * log (radius U J) := by
    have := sum_le_log_prodP hU hm1 J
    calc ∑ k ∈ range J, U k * (1 + L) / prodP U (fun _ => m) (k + 1)
        = ∑ k ∈ range J, (1 + L) * (U k / prodP U (fun _ => m) (k + 1)) := by
          apply sum_congr rfl; intro k _; ring
      _ ≤ (1 + L) * log (radius U J) := by
          rw [← mul_sum]; exact mul_le_mul_of_nonneg_left this (by linarith)
  have hlog : 0 ≤ log (radius U J) := log_nonneg (radius_ge_one hU J)
  have hpow : 0 ≤ radius U J ^ (m - 1) := rpow_nonneg hR.le _
  have hP0 : 0 ≤ prodP U (fun _ => m) J / radius U J :=
    div_nonneg (prodP_pos hU hm0 J).le hR.le
  calc T J ≤ c * (prodP U (fun _ => m) J / radius U J)
        * (2 + ∑ k ∈ range J, U k * (1 + L) / prodP U (fun _ => m) (k + 1)) := hb
    _ ≤ c * radius U J ^ (m - 1) * (2 + (1 + L) * log (radius U J)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hleaf hc) (by linarith)
        · have : 0 ≤ ∑ k ∈ range J, U k * (1 + L) / prodP U (fun _ => m) (k + 1) :=
            sum_nonneg (fun k _ => div_nonneg (mul_nonneg (hU k) (by linarith))
              (prodP_pos hU hm0 _).le)
          linarith
        · exact mul_nonneg hc hpow
    _ ≤ c * (2 + L) * (1 + log (radius U J)) * radius U J ^ (m - 1) := by
        have : 2 + (1 + L) * log (radius U J) ≤ (2 + L) * (1 + log (radius U J)) := by
          nlinarith
        have := mul_le_mul_of_nonneg_left this (mul_nonneg hc hpow)
        linarith

/-- Auxiliary: a finite charge comparison, `∑ charge_k ≤ C ∑ reach_k` when each charge is at most
`C` times its reach. It is not used by the formalized bounds above, which start from the charging
inequality of the proof of `thm:pn-abstract` (normalization_additive.tex). -/
theorem predictable_finite_charge (n : ℕ) (charge reach : ℕ → ℝ) (C : ℝ)
    (hcharge : ∀ k ∈ range n, charge k ≤ C * reach k) :
    (∑ k ∈ range n, charge k) ≤ C * ∑ k ∈ range n, reach k := by
  calc (∑ k ∈ range n, charge k) ≤ ∑ k ∈ range n, C * reach k := sum_le_sum hcharge
    _ = C * ∑ k ∈ range n, reach k := by rw [mul_sum]

/-- Auxiliary: a multiplicative one-step form of a work charge. If `old ≤ C·P`, `R ≤ P` and
`work ≤ old + u m old/R + C u (L+1)`, then `work ≤ C·P·(1 + u(m + L + 1)/R)`. It is not used by
the formalized bounds above; the proof of `thm:pn-abstract` (normalization_additive.tex) uses
the equality majorant `workMajorant` instead. -/
theorem enlarged_work_step (old pre R u m L C work : ℝ) (hm : 0 ≤ m) (hL : 0 ≤ L)
    (hu : 0 ≤ u) (hC : 0 ≤ C) (hR : 0 < R) (hpre : R ≤ pre) (hold : old ≤ C * pre)
    (hwork : work ≤ old + u * m * old / R + C * u * (L + 1)) :
    work ≤ C * pre * (1 + u * (m + L + 1) / R) := by
  have hnon : 0 ≤ u * m / R := div_nonneg (mul_nonneg hu hm) (le_of_lt hR)
  have hOldMul := mul_le_mul_of_nonneg_left hold hnon
  have hRatio : 1 ≤ pre / R := (le_div_iff₀ hR).2 (by simpa using hpre)
  have hCL : 0 ≤ C * u * (L + 1) := by positivity
  have hExtra := mul_le_mul_of_nonneg_left hRatio hCL
  have e1 : u * m * old / R = u * m / R * old := by ring
  have e2 : C * pre * (1 + u * (m + L + 1) / R)
      = C * pre + u * m / R * (C * pre) + C * u * (L + 1) * (pre / R) := by
    field_simp; ring
  rw [e2]
  nlinarith

/-! ## Pre-norm sampling under a relative energy certificate (`thm:pn-relative`) -/

/-- The power-of-two gain: for `γ > 0` there is `G = 2^k` with `2/√γ ≤ G < 4/√γ`.
Paper: `thm:pn-relative` (normalization_additive.tex), choice of `G`; `eq:main-prenorm-m`
(main_normalization.tex). -/
theorem exists_gain {γ : ℝ} (hγ : 0 < γ) :
    ∃ k : ℤ, 2 / √γ ≤ (2 : ℝ) ^ k ∧ (2 : ℝ) ^ k < 4 / √γ := by
  have hx : 0 < 2 / √γ := by have := sqrt_pos.2 hγ; positivity
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hx (by norm_num : (1 : ℝ) < 2)
  refine ⟨n + 1, hn2, ?_⟩
  rw [zpow_add_one₀ (by norm_num)]
  have : (4 : ℝ) / √γ = 2 * (2 / √γ) := by ring
  linarith

/-- A relative energy floor makes the supplied condition number constant: `R²/(γ R²) = 1/γ`.
Paper: proof of `thm:pn-relative` (normalization_additive.tex). -/
theorem relative_condition_ratio (R gamma : ℝ) (hR : R ≠ 0) (hg : gamma ≠ 0) :
    R ^ 2 / (gamma * R ^ 2) = 1 / gamma := by
  field_simp

/-- Under the relative floor `λ_j = γ R_{j-1}²`, the condition number is
`max{1, R_{j-1}²/λ_j} = max{1, γ⁻¹}` (possibly lowered by the replacement `λ ← max{λ, ε}`),
and the natural output radius `2R_{j-1}/√λ_j = 2/√γ` is at most `G`.
Paper: proof of `thm:pn-relative` (normalization_additive.tex). -/
theorem relative_floor_factory {γ R G : ℝ} (hγ : 0 < γ) (hR : 0 < R) (hG : 2 / √γ ≤ G) :
    max 1 (R ^ 2 / (γ * R ^ 2)) = max 1 γ⁻¹ ∧ 2 * R / √(γ * R ^ 2) ≤ G := by
  constructor
  · rw [relative_condition_ratio R γ hR.ne' hγ.ne', one_div]
  · rw [sqrt_mul hγ.le, sqrt_sq hR.le]
    have hs : 0 < √γ := sqrt_pos.2 hγ
    calc 2 * R / (√γ * R) = 2 / √γ := by field_simp
      _ ≤ G := hG

/-- The radii of `D` blocks with alternating update radii `sG` (attention) and `1` (tanh):
`R_{2D} = 1 + D(sG + 1)`.
Paper: `thm:pn-relative` (normalization_additive.tex), the radii; `eq:main-prenorm`
(exact_sampling_networks.tex). -/
theorem alternating_radius (a b : ℝ) (D : ℕ) :
    radius (fun k => if k % 2 = 0 then a else b) (2 * D) = 1 + D * (a + b) := by
  induction D with
  | zero => simp [radius_zero]
  | succ D ih =>
    rw [show 2 * (D + 1) = 2 * D + 1 + 1 by ring, radius_succ, radius_succ, ih]
    have h1 : (2 * D) % 2 = 0 := by omega
    have h2 : (2 * D + 1) % 2 = 1 := by omega
    simp only [h1, h2]
    norm_num
    ring

/-- Explicit radius for a full additive attention/tanh block:
`(1 + D(sG+1)) + sG + 1 = 1 + (D+1)(sG+1)`.
Paper: `thm:pn-relative` (normalization_additive.tex). -/
theorem two_update_radius (D s G : ℝ) :
    (1 + D * (s * G + 1)) + s * G + 1 = 1 + (D + 1) * (s * G + 1) := by
  ring

/-- With a common step `α` on both sublayers the radius is `1 + αD(sG+1)`.
Paper: `cor:pn-stepsizes` (normalization_additive.tex); `cor:pn-effective-threshold`
(normalization_depth_lower.tex). -/
theorem stepped_radius (α a b : ℝ) (D : ℕ) :
    radius (fun k => if k % 2 = 0 then α * a else α * b) (2 * D) = 1 + α * D * (a + b) := by
  rw [show (fun k => if k % 2 = 0 then α * a else α * b)
      = (fun k => if k % 2 = 0 then α * a else α * b) from rfl, alternating_radius]
  ring

/-- Scaling an update by a positive step leaves its normalized sign law unchanged:
`(a F)/(a U) = F/U`.
Paper: proof of `cor:pn-stepsizes` (normalization_additive.tex). -/
theorem step_scaling (a F U : ℝ) (ha : a ≠ 0) : (a * F) / (a * U) = F / U := by
  rw [mul_div_mul_left _ _ ha]

/-- **The polynomial depth bound.** With alternating update radii `sG` and `1`, and local
predecessor budgets `m_j ≤ m`, `m ≥ 1`, every leaf recurrence of the composition is bounded by
`(1 + D(sG+1))^{m-1}`.
Paper: `thm:pn-relative` (normalization_additive.tex), leaf bound `R_{2D}^{m-1}`. -/
theorem prenorm_leaf_bound {s G m : ℝ} {mk C : ℕ → ℝ} (hsG : 0 ≤ s * G) (hmk : ∀ k, 0 ≤ mk k)
    (hm1 : 1 ≤ m) (hmm : ∀ k, mk k ≤ m) (hC0 : C 0 ≤ 1)
    (hrec : ∀ j, C (j + 1) ≤ (radius (fun k => if k % 2 = 0 then s * G else 1) j
        + (fun k => if k % 2 = 0 then s * G else 1) j * mk j)
        / radius (fun k => if k % 2 = 0 then s * G else 1) (j + 1) * C j) (D : ℕ) :
    C (2 * D) ≤ (1 + D * (s * G + 1)) ^ (m - 1) := by
  have hU : ∀ k, (0 : ℝ) ≤ (fun k => if k % 2 = 0 then s * G else 1) k := by
    intro k; simp only; split_ifs <;> linarith
  have h1 := leaf_product hU hmk hC0 hrec (2 * D)
  have h2 := uniform_leaf_bound hU hmk hm1 hmm (2 * D)
  rw [alternating_radius] at h1 h2
  linarith

end ExactSampling.PreNormAdditive
