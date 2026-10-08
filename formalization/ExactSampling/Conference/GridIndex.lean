import Mathlib
import ExactSampling.Conference.RejectionLoop

/-!
# An appendable finite cache: grid cells, cell envelopes and the exact rejection sampler

Paper: `conference.tex`, Section `sec:conf-grid`, Theorem `thm:conf-grid` (appendable finite
cache) with its proof, and the worked example with two repeated keys after it. Full version
`exact_sampling_networks.tex`: Theorem `thm:dynamicfixedrank` and Lemma
`lem:dynamiccellenvelope` (`attention_dynamic_index.tex`).

Scores are `a = (β / n) ⟨q, k⟩` as in `eq:conf-attention`. Within one chart a key is
`k = c₀ + A y` with `|A_{ij}| ≤ 2` and selected coordinates `y = k_I ∈ [-K, K]^d`, `d ≤ r`; the
cell of `y` is the integer tuple `⌊y_i / Δ⌋` with grid width `Δ = K 2^{-h}` and
`h = ⌈log₂ max(1, 8 r β̄ Q K)⌉`.

## What is formalized

* The chart coefficient bound `|(qᵀA)_i| ≤ 2 n Q` and the in-cell score bound: two keys in one
  cell differ in score by less than `2 β r Q Δ ≤ 1/4` (for `0 < β ≤ β̄`).
* The grid exponent: `max(1, x) ≤ 2^h < 2 max(1, x)`; cell indices lie in `[-2^h, 2^h]`, so a
  chart has at most `(2^{h+1} + 1)^d ≤ (5 + 32 r β̄ Q K)^d` cells.
* At most `r + 1` charts: a new chart starts only when the affine dimension of the prefix
  increases, and that dimension is at most `r`. The `M_T` arithmetic
  `∑_{d ≤ r} X^d ≤ (r+1) X^r` and `#cells ≤ T`.
* The cell envelope (`lem:dynamiccellenvelope`): `w_j ≤ e_C < 2 w_j`, `Z > 1/2`, the dyadic
  rounding `e_C ≤ u_C ≤ e_C + 3·2^{-p}`, `u_C ≥ 2^{-p}`, the precision `p = ⌈log₂(64T)⌉`, and
  `Z ≤ W < 2Z + 3/64 < (17/8) Z`.
* Exactness of the rejection sampler: choosing a cell with weight `|C| u_C`, a uniform member
  and accepting with probability `w_j / u_C` gives accepted mass exactly `w_j / W`; the
  first-acceptance series sums to `w_j / Z = e^{a_j} / ∑ₖ e^{a_k}`, and `W / Z < 17/8`.
* Independent proposals on a probability space (`rejection_sampler_iid`, using the module
  `ExactSampling.RejectionLoop`): with this one-proposal law, the first accepted member has the
  attention law and the expected number of proposals is `W / Z < 17/8`.
* A combined statement for a cache stored in at most `r + 1` charts (`thm_conf_grid_law`).
* The worked example: attention mean of the two-key cache, and `tanh(β M)` when balanced.

## What is not formalized

All bit-complexity claims (append and query work, storage, balanced trees, binary append trees,
enclosure of `√n`, the Taylor series with range reduction, uniform-comparison tails) are out of
scope. Repeated independent proposals are expressed by the renewal series in which proposal `m`
is reached with probability `(1 - Z/W)^m`; the companion module `ExactSampling.RejectionLoop`
derives this series from independent, identically distributed proposals. The chart
construction itself is in the companion module `ExactSampling.Chart` on `lem:conf-chart`; here
charts are given by their coefficient matrices with `|A_{ij}| ≤ 2`. A chart of dimension
`d < r` is represented with `r` coordinates by zero padding. In `thm_conf_grid_law` the chart
data (the number of charts `m ≤ r + 1`, the bound `|A_{ij}| ≤ 2`, the offsets `c₀` and the chart
coordinates `y_j ∈ [-K, K]^r`) are hypotheses; they are not built from the key stream, and
`y_j = (k_j)_I` is not required, although `chart_count_le` here and `exists_bounded_chart`,
`chart_repr` in `ExactSampling.Chart` prove the corresponding facts separately. In the
one-proposal law of `rejection_sampler_iid` the stage probabilities are a hypothesis matching
the construction; the cell choice, member choice and acceptance coin are not modeled as
separate random variables. The number of occupied cells in the worked example is not
formalized.
-/

open Real Finset Matrix
open scoped Nat ENNReal

namespace ExactSampling.GridIndex

/-! ### Scores in a chart -/

/-- The attention score `a = (β / n) ⟨q, k⟩`. Paper: `eq:conf-attention` (conference.tex). -/
noncomputable def score {n : ℕ} (β : ℝ) (q k : Fin n → ℝ) : ℝ := β / n * (q ⬝ᵥ k)

/-- Chart coefficients of a query: `|(qᵀA)_i| ≤ 2 n Q` when `|A_{ij}| ≤ 2` and
`q ∈ [-Q, Q]^n`. Paper: proof of `thm:conf-grid` (conference.tex), "a query's coordinate
coefficients obey `|(q^TA)_i| ≤ 2nQ_max`"; full version: proof of `thm:dynamicfixedrank`
(attention_dynamic_index.tex). -/
theorem abs_vecMul_le {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (hA : ∀ i j, |A i j| ≤ 2)
    (q : Fin n → ℝ) {Q : ℝ} (hq : ∀ i, |q i| ≤ Q) (j : Fin d) :
    |(q ᵥ* A) j| ≤ 2 * n * Q := by
  simp only [vecMul, dotProduct]
  calc |∑ i, q i * A i j| ≤ ∑ i, |q i * A i j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, Q * 2 := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul (hq i) (hA i j) (abs_nonneg _) ((abs_nonneg _).trans (hq i))
    _ = 2 * n * Q := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The score of a chart key `k = c₀ + A y` is `(β/n)(⟨q, c₀⟩ + ⟨qᵀA, y⟩)`. Paper: proof of
`thm:conf-grid` (conference.tex), "compute `q^TA` and `⟨q, c₀⟩` once per chart". -/
theorem score_chart {n d : ℕ} (β : ℝ) (q c₀ : Fin n → ℝ) (A : Matrix (Fin n) (Fin d) ℝ)
    (y : Fin d → ℝ) :
    score β q (c₀ + A *ᵥ y) = β / n * (q ⬝ᵥ c₀ + (q ᵥ* A) ⬝ᵥ y) := by
  unfold score
  rw [dotProduct_add, dotProduct_mulVec]

/-- The cell of a coordinate vector: the integer tuple `⌊y_i / Δ⌋`. Paper: proof of
`thm:conf-grid` (conference.tex); full version: proof of `thm:dynamicfixedrank`
(attention_dynamic_index.tex), "the integer cell tuple is `⌊y_i/Δ⌋`". -/
noncomputable def cellIndex {d : ℕ} (Δ : ℝ) (y : Fin d → ℝ) : Fin d → ℤ := fun i => ⌊y i / Δ⌋

/-- Two coordinate vectors in one cell differ by less than `Δ` in every coordinate. Auxiliary
for the in-cell score bound in the proof of `thm:conf-grid` (conference.tex). -/
theorem abs_sub_lt_of_cellIndex_eq {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ) {y y' : Fin d → ℝ}
    (h : cellIndex Δ y = cellIndex Δ y') (i : Fin d) : |y i - y' i| < Δ := by
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun h i)
  rw [← sub_div, abs_div, abs_of_pos hΔ, div_lt_one hΔ] at h1
  exact h1

/-- In-cell score bound with the chart width: if two chart keys have coordinates within `Δ`, their
scores differ by less than `2 β r Q Δ`. Paper: proof of `thm:conf-grid` (conference.tex), "two
keys in a cell have score difference below `2βrQ_maxΔ`"; full version: proof of
`thm:dynamicfixedrank` (attention_dynamic_index.tex), `(β/n) ∑ᵢ |vᵢ| Δ ≤ 2βrQΔ`. -/
theorem abs_score_sub_lt {n d r : ℕ} (hn : 0 < n) (hr : 1 ≤ r) (hd : d ≤ r) {β Q Δ : ℝ}
    (hβ : 0 < β) (hQ : 0 < Q) (hΔ : 0 < Δ) (A : Matrix (Fin n) (Fin d) ℝ)
    (hA : ∀ i j, |A i j| ≤ 2) (q : Fin n → ℝ) (hq : ∀ i, |q i| ≤ Q) (c₀ : Fin n → ℝ)
    (y y' : Fin d → ℝ) (hy : ∀ i, |y i - y' i| < Δ) :
    |score β q (c₀ + A *ᵥ y) - score β q (c₀ + A *ᵥ y')| < 2 * β * r * Q * Δ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [score_chart, score_chart, ← mul_sub, add_sub_add_left_eq_sub, ← dotProduct_sub,
    abs_mul, abs_of_pos (div_pos hβ hn')]
  have hsum : ∑ i, |y i - y' i| < r * Δ := by
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      have : (1 : ℝ) ≤ r := by exact_mod_cast hr
      nlinarith
    · have : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
      calc ∑ i, |y i - y' i| < ∑ _i : Fin d, Δ :=
            Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hy i
        _ = d * Δ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ r * Δ := by gcongr
  have hdot : |(q ᵥ* A) ⬝ᵥ (y - y')| ≤ 2 * n * Q * ∑ i, |y i - y' i| := by
    simp only [dotProduct, Pi.sub_apply]
    calc |∑ i, (q ᵥ* A) i * (y i - y' i)| ≤ ∑ i, |(q ᵥ* A) i * (y i - y' i)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, 2 * n * Q * |y i - y' i| := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (abs_vecMul_le A hA q hq i) (abs_nonneg _)
      _ = 2 * n * Q * ∑ i, |y i - y' i| := by rw [Finset.mul_sum]
  calc β / n * |(q ᵥ* A) ⬝ᵥ (y - y')| ≤ β / n * (2 * n * Q * ∑ i, |y i - y' i|) :=
        mul_le_mul_of_nonneg_left hdot (div_pos hβ hn').le
    _ = 2 * β * Q * ∑ i, |y i - y' i| := by field_simp
    _ < 2 * β * Q * (r * Δ) := by gcongr
    _ = 2 * β * r * Q * Δ := by ring

/-! ### The grid exponent and the cell count -/

/-- `⌈log₂ x⌉` as a natural number. -/
noncomputable def ceilLog2 (x : ℝ) : ℕ := ⌈Real.logb 2 x⌉₊

/-- For `x ≥ 1`, `x ≤ 2^{⌈log₂ x⌉} < 2x`. Auxiliary for the choice of `h` and `p` in the proof of
`thm:conf-grid` (conference.tex). -/
theorem ceilLog2_spec {x : ℝ} (hx : 1 ≤ x) :
    x ≤ (2 : ℝ) ^ ceilLog2 x ∧ (2 : ℝ) ^ ceilLog2 x < 2 * x := by
  have hx0 : 0 < x := by linarith
  have hL : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx
  have hpow : ((2 : ℝ) ^ ceilLog2 x) = (2 : ℝ) ^ ((ceilLog2 x : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
  constructor
  · rw [hpow]
    calc x = (2 : ℝ) ^ Real.logb 2 x := (Real.rpow_logb (by norm_num) (by norm_num) hx0).symm
      _ ≤ (2 : ℝ) ^ ((ceilLog2 x : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  · rw [hpow]
    calc (2 : ℝ) ^ ((ceilLog2 x : ℕ) : ℝ) < (2 : ℝ) ^ (Real.logb 2 x + 1) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (Nat.ceil_lt_add_one hL)
      _ = 2 * x := by
          rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hx0,
            Real.rpow_one]
          ring

/-- The grid exponent `h = ⌈log₂ max(1, x)⌉` with `x = 8 r β̄ Q K`. Paper: proof of
`thm:conf-grid` (conference.tex). -/
noncomputable def gridExp (x : ℝ) : ℕ := ceilLog2 (max 1 x)

/-- `max(1, x) ≤ 2^h < 2 max(1, x)`. Paper: proof of `thm:conf-grid` (conference.tex). -/
theorem gridExp_spec (x : ℝ) :
    max 1 x ≤ (2 : ℝ) ^ gridExp x ∧ (2 : ℝ) ^ gridExp x < 2 * max 1 x :=
  ceilLog2_spec (le_max_left 1 x)

/-- The in-cell score bound of `thm:conf-grid` (conference.tex) with the stated grid: for
`0 < β ≤ β̄`, `Δ = K 2^{-h}` and `h = ⌈log₂ max(1, 8 r β̄ Q K)⌉`, two chart keys in one cell
satisfy `|a - a'| < 2 β r Q Δ ≤ 1/4`. Full version: proof of `thm:dynamicfixedrank`
(attention_dynamic_index.tex). -/
theorem in_cell_score_bound {n d r : ℕ} (hn : 0 < n) (hr : 1 ≤ r) (hd : d ≤ r)
    {β βbar Q K : ℝ} (hβ : 0 < β) (hββ : β ≤ βbar) (hQ : 0 < Q) (hK : 0 < K)
    (A : Matrix (Fin n) (Fin d) ℝ) (hA : ∀ i j, |A i j| ≤ 2) (q : Fin n → ℝ)
    (hq : ∀ i, |q i| ≤ Q) (c₀ : Fin n → ℝ) (y y' : Fin d → ℝ)
    (hcell : cellIndex (K / 2 ^ gridExp (8 * r * βbar * Q * K)) y
      = cellIndex (K / 2 ^ gridExp (8 * r * βbar * Q * K)) y') :
    |score β q (c₀ + A *ᵥ y) - score β q (c₀ + A *ᵥ y')|
        < 2 * β * r * Q * (K / 2 ^ gridExp (8 * r * βbar * Q * K)) ∧
      2 * β * r * Q * (K / 2 ^ gridExp (8 * r * βbar * Q * K)) ≤ 1 / 4 := by
  set h := gridExp (8 * r * βbar * Q * K)
  have hΔ : 0 < K / 2 ^ h := by positivity
  refine ⟨abs_score_sub_lt hn hr hd hβ hQ hΔ A hA q hq c₀ y y'
    (abs_sub_lt_of_cellIndex_eq hΔ hcell), ?_⟩
  have hspec := (gridExp_spec (8 * r * βbar * Q * K)).1
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h1 : 8 * r * β * Q * K ≤ (2 : ℝ) ^ h := by
    have : 8 * r * β * Q * K ≤ 8 * r * βbar * Q * K := by
      have : 0 ≤ (8 : ℝ) * r := by positivity
      have := mul_le_mul_of_nonneg_left hββ this
      have hQK : 0 < Q * K := mul_pos hQ hK
      nlinarith
    exact this.trans ((le_max_right _ _).trans hspec)
  have h2 : (0 : ℝ) < 2 ^ h := by positivity
  rw [mul_div_assoc', div_le_iff₀ h2]
  nlinarith

/-- Cell indices of coordinates in `[-K, K]` lie in `[-2^h, 2^h]`. Paper: proof of
`thm:conf-grid` (conference.tex); full version: proof of `thm:dynamicfixedrank`
(attention_dynamic_index.tex), "in one coordinate there are at most `2^{m+1} + 1` possible cell
indices". -/
theorem floor_mem_Icc {K t : ℝ} (hK : 0 < K) (h : ℕ) (ht : |t| ≤ K) :
    ⌊t / (K / 2 ^ h)⌋ ∈ Finset.Icc (-(2 : ℤ) ^ h) (2 ^ h) := by
  have h2 : (0 : ℝ) < 2 ^ h := by positivity
  have heq : t / (K / 2 ^ h) = t * 2 ^ h / K := by field_simp
  have hb := abs_le.mp ht
  have hlo : -((2 : ℝ) ^ h) ≤ t * 2 ^ h / K := by
    rw [le_div_iff₀ hK]; nlinarith
  have hhi : t * 2 ^ h / K ≤ (2 : ℝ) ^ h := by
    rw [div_le_iff₀ hK]; nlinarith
  rw [Finset.mem_Icc, heq]
  constructor
  · rw [Int.le_floor]; push_cast; exact hlo
  · have := Int.floor_le (t * 2 ^ h / K)
    have : ((⌊t * 2 ^ h / K⌋ : ℤ) : ℝ) ≤ ((2 ^ h : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

/-- Per-coordinate count `2^{h+1} + 1 ≤ 5 + 32 r β̄ Q K` (in fact `<`). Paper: proof of
`thm:conf-grid` (conference.tex); full version: proof of `thm:dynamicfixedrank`
(attention_dynamic_index.tex), "this is at most `5 + 32rβ̄QK`". -/
theorem two_pow_succ_add_one_lt {x : ℝ} (hx : 0 ≤ x) :
    (2 : ℝ) ^ (gridExp x + 1) + 1 < 5 + 4 * x := by
  have h := (gridExp_spec x).2
  have hm : max 1 x ≤ 1 + x := max_le (by linarith) (by linarith)
  rw [pow_succ]
  linarith

/-- The cell count of one chart: a finite set of coordinate vectors in `[-K, K]^d` occupies at
most `(5 + 32 r β̄ Q K)^d` cells of the grid with `Δ = K 2^{-h}`. Paper: proof of
`thm:conf-grid` (conference.tex), "there are at most `(5+32rβ̄Q_maxK)^d` cells in a chart";
full version: proof of `thm:dynamicfixedrank` (attention_dynamic_index.tex). -/
theorem card_cells_le {d r : ℕ} {βbar Q K : ℝ} (hβ : 0 ≤ βbar) (hQ : 0 ≤ Q) (hK : 0 < K)
    (S : Finset (Fin d → ℝ)) (hS : ∀ y ∈ S, ∀ i, |y i| ≤ K) :
    ((S.image (cellIndex (K / 2 ^ gridExp (8 * r * βbar * Q * K)))).card : ℝ)
      ≤ (5 + 32 * r * βbar * Q * K) ^ d := by
  set h := gridExp (8 * r * βbar * Q * K)
  have hsub : S.image (cellIndex (K / 2 ^ h))
      ⊆ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(2 : ℤ) ^ h) (2 ^ h)) := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    rw [Fintype.mem_piFinset]
    intro i
    exact floor_mem_Icc hK h (hS y hy i)
  have hcard := Finset.card_le_card hsub
  rw [Fintype.card_piFinset_const, Int.card_Icc] at hcard
  have hval : ((2 : ℤ) ^ h + 1 - -(2 : ℤ) ^ h).toNat = 2 ^ (h + 1) + 1 := by
    have : (2 : ℤ) ^ h + 1 - -(2 : ℤ) ^ h = ((2 ^ (h + 1) + 1 : ℕ) : ℤ) := by
      push_cast; ring
    rw [this, Int.toNat_natCast]
  rw [hval] at hcard
  have hx : 0 ≤ 8 * (r : ℝ) * βbar * Q * K := by positivity
  have hlt : (2 : ℝ) ^ (h + 1) + 1 < 5 + 4 * (8 * r * βbar * Q * K) :=
    two_pow_succ_add_one_lt hx
  calc ((S.image (cellIndex (K / 2 ^ h))).card : ℝ) ≤ ((2 ^ (h + 1) + 1) ^ d : ℕ) := by
        exact_mod_cast hcard
    _ = ((2 : ℝ) ^ (h + 1) + 1) ^ d := by push_cast; ring
    _ ≤ (5 + 32 * r * βbar * Q * K) ^ d :=
        pow_le_pow_left₀ (by positivity) (by linarith) d

/-! ### At most `r + 1` charts -/

/-- A monotone natural sequence increases at most `f T - f 0` times before `T`. Auxiliary for the
chart count in the proof of `thm:conf-grid` (conference.tex). -/
theorem card_increases_le (f : ℕ → ℕ) (hf : Monotone f) (T : ℕ) :
    ((Finset.range T).filter (fun t => f t < f (t + 1))).card ≤ f T - f 0 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    have h0 : f 0 ≤ f T := hf (Nat.zero_le T)
    have h1 : f T ≤ f (T + 1) := hf (Nat.le_succ T)
    split_ifs with hT
    · calc (insert T ((Finset.range T).filter (fun t => f t < f (t + 1)))).card
          ≤ ((Finset.range T).filter (fun t => f t < f (t + 1))).card + 1 :=
            Finset.card_insert_le _ _
        _ ≤ f (T + 1) - f 0 := by omega
    · omega

/-- The affine dimension of the first `t` keys: the dimension of the direction of their affine
span. Paper: `thm:conf-grid` (conference.tex), "every prefix has affine dimension at most
`r`". -/
noncomputable def prefixDim {n : ℕ} (keys : ℕ → Fin n → ℝ) (t : ℕ) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ (keys '' Set.Iio t)).direction

/-- The affine dimension of a prefix is monotone in its length. Auxiliary for the chart count in
the proof of `thm:conf-grid` (conference.tex). -/
theorem prefixDim_mono {n : ℕ} (keys : ℕ → Fin n → ℝ) : Monotone (prefixDim keys) := by
  intro s t hst
  unfold prefixDim
  apply Submodule.finrank_mono
  apply AffineSubspace.direction_le
  apply affineSpan_mono
  exact Set.image_mono (Set.Iio_subset_Iio hst)

/-- At most `r + 1` charts: one chart is open at the start, and a new chart is started only when
the affine dimension of the prefix increases. If every prefix has affine dimension at most
`r`, there are at most `r` increases, hence at most `r + 1` charts. Paper: proof of
`thm:conf-grid` (conference.tex), "at each increase of rank start a new chart ... at most
`r+1` charts are ever used"; full version: proof of `thm:dynamicfixedrank`
(attention_dynamic_index.tex). -/
theorem chart_count_le {n : ℕ} (keys : ℕ → Fin n → ℝ) (r T : ℕ)
    (hr : ∀ t ≤ T, prefixDim keys t ≤ r) :
    ((Finset.range T).filter (fun t => prefixDim keys t < prefixDim keys (t + 1))).card + 1
      ≤ r + 1 := by
  have := card_increases_le (prefixDim keys) (prefixDim_mono keys) T
  have := hr T le_rfl
  omega

/-- `∑_{d=0}^{r} X^d ≤ (r+1) X^r` for `X ≥ 1`, giving the bound `M_T ≤ (r+1)(5+32rβ̄QK)^r` on
the total number of occupied cells over all charts. Paper: `thm:conf-grid` (conference.tex),
bound on `M_T`; full version: proof of `thm:dynamicfixedrank` (attention_dynamic_index.tex). -/
theorem sum_pow_le {X : ℝ} (hX : 1 ≤ X) (r : ℕ) :
    ∑ d ∈ Finset.range (r + 1), X ^ d ≤ (r + 1) * X ^ r := by
  calc ∑ d ∈ Finset.range (r + 1), X ^ d ≤ ∑ _d ∈ Finset.range (r + 1), X ^ r :=
        Finset.sum_le_sum fun d hd => pow_le_pow_right₀ hX (Nat.lt_succ_iff.mp
          (Finset.mem_range.mp hd))
    _ = (r + 1) * X ^ r := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast; ring

/-! ### The cell envelope and the rejection sampler -/

section Envelope

variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]

/-- Shifted member weights `w_j = e^{a_j - a₀ - 1/4}`. Paper: proof of `thm:conf-grid`
(conference.tex). -/
noncomputable def memberWeight (a : ι → ℝ) (a₀ : ℝ) (j : ι) : ℝ := exp (a j - a₀ - 1 / 4)

/-- Cell envelope weights `e_C = e^{a_C - a₀}`. Paper: proof of `thm:conf-grid`
(conference.tex). -/
noncomputable def cellWeight (aC : κ → ℝ) (a₀ : ℝ) (C : κ) : ℝ := exp (aC C - a₀)

/-- `w_j ≤ e_C < 2 w_j` for a member `j` of cell `C` with `|a_j - a_C| ≤ 1/4`. Paper: proof of
`thm:conf-grid` (conference.tex), "then `w_j ≤ e_C < 2w_j` in that cell"; full version:
`lem:dynamiccellenvelope` (attention_dynamic_index.tex). -/
theorem member_cell_weight {aj aC a₀ : ℝ} (h : |aj - aC| ≤ 1 / 4) :
    exp (aj - a₀ - 1 / 4) ≤ exp (aC - a₀) ∧ exp (aC - a₀) < 2 * exp (aj - a₀ - 1 / 4) := by
  have hb := abs_le.mp h
  constructor
  · exact exp_le_exp.mpr (by linarith)
  · have h1 : exp (aC - a₀) ≤ exp (1 / 2) * exp (aj - a₀ - 1 / 4) := by
      rw [← exp_add]; exact exp_le_exp.mpr (by linarith)
    have h2 : exp (1 / 2 : ℝ) < 2 := by
      have := Real.exp_one_lt_d9
      have hsq : exp (1 / 2 : ℝ) ^ 2 = exp 1 := by rw [← exp_nat_mul]; norm_num
      nlinarith [exp_pos (1 / 2 : ℝ)]
    have h3 : 0 < exp (aj - a₀ - 1 / 4) := exp_pos _
    nlinarith

/-- `e^{-1/2} > 1/2`. Auxiliary for `Z > 1/2` in the proof of `thm:conf-grid`
(conference.tex). -/
theorem half_lt_exp_neg_half : (1 : ℝ) / 2 < exp (-(1 / 2)) := by
  rw [exp_neg, lt_inv_comm₀ (by norm_num) (exp_pos _)]
  have := Real.exp_one_lt_d9
  have hsq : exp (1 / 2 : ℝ) ^ 2 = exp 1 := by rw [← exp_nat_mul]; norm_num
  nlinarith [exp_pos (1 / 2 : ℝ)]

omit [DecidableEq κ] in
/-- `Z = ∑ⱼ wⱼ > 1/2`: a member of a cell whose proxy attains `a₀` has `w_j ≥ e^{-1/2} > 1/2`.
Paper: proof of `thm:conf-grid` (conference.tex), "while `Z = ∑_j w_j > 1/2`"; full version:
`lem:dynamiccellenvelope` (attention_dynamic_index.tex). -/
theorem half_lt_Z (cell : ι → κ) (a : ι → ℝ) (aC : κ → ℝ) (a₀ : ℝ)
    (hprox : ∀ j, |a j - aC (cell j)| ≤ 1 / 4) (hattain : ∃ j, aC (cell j) = a₀) :
    1 / 2 < ∑ j, memberWeight a a₀ j := by
  obtain ⟨j₀, hj₀⟩ := hattain
  have hb := abs_le.mp (hprox j₀)
  calc (1 : ℝ) / 2 < exp (-(1 / 2)) := half_lt_exp_neg_half
    _ ≤ memberWeight a a₀ j₀ := exp_le_exp.mpr (by rw [← hj₀]; linarith)
    _ ≤ ∑ j, memberWeight a a₀ j :=
        Finset.single_le_sum (f := memberWeight a a₀) (fun j _ => (exp_pos _).le)
          (Finset.mem_univ j₀)

/-- The dyadic rounding of an enclosure. If `0 ≤ e ≤ U ≤ e + 2^{-p}`, then rounding `U` up to
the grid `2^{-p}` and adding one grid unit gives a dyadic `u = (⌈U 2^p⌉ + 1) / 2^p` with
`e ≤ u ≤ e + 3·2^{-p}` and `u ≥ 2^{-p}`. Paper: proof of `thm:conf-grid` (conference.tex),
"enclose the negative exponential, round its upper endpoint up to the `2^{-p}` grid, and add
one grid unit"; full version: `lem:dynamiccellenvelope` (attention_dynamic_index.tex). -/
theorem dyadic_round {e U : ℝ} (p : ℕ) (he : 0 ≤ e) (hU1 : e ≤ U) (hU2 : U ≤ e + (2 ^ p)⁻¹) :
    e ≤ (⌈U * 2 ^ p⌉ + 1) / 2 ^ p ∧ (⌈U * 2 ^ p⌉ + 1) / 2 ^ p ≤ e + 3 * (2 ^ p)⁻¹ ∧
      (2 ^ p)⁻¹ ≤ ((⌈U * 2 ^ p⌉ + 1) / 2 ^ p : ℝ) := by
  have h2 : (0 : ℝ) < 2 ^ p := by positivity
  have hc1 := Int.le_ceil (U * 2 ^ p)
  have hc2 := Int.ceil_lt_add_one (U * 2 ^ p)
  have hc0 : (0 : ℝ) ≤ ⌈U * 2 ^ p⌉ := by
    have : (0 : ℤ) ≤ ⌈U * 2 ^ p⌉ := Int.ceil_nonneg (mul_nonneg (he.trans hU1) h2.le)
    exact_mod_cast this
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ h2]; nlinarith
  · rw [div_le_iff₀ h2]
    have : (e + 3 * (2 ^ p)⁻¹) * 2 ^ p = e * 2 ^ p + 3 := by field_simp
    rw [this]
    nlinarith
  · rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right (by linarith) h2.le

/-- The working precision `p = ⌈log₂(64T)⌉` satisfies `64 T ≤ 2^p` for `T ≥ 1`. Paper: proof of
`thm:conf-grid` (conference.tex), "set `p = ⌈log₂(64T)⌉`". -/
theorem precision_spec {T : ℕ} (hT : 1 ≤ T) : 64 * (T : ℝ) ≤ 2 ^ ceilLog2 (64 * T) :=
  (ceilLog2_spec (by have h1 : (1 : ℝ) ≤ T := (by exact_mod_cast hT); linarith)).1

omit [DecidableEq κ] in
/-- The envelope inequality `Z ≤ W < 2Z + 3/64 < (17/8) Z`, where `W = ∑_C |C| u_C` is written
as a sum over members, `e_C ≤ u_C ≤ e_C + 3·2^{-p}`, and `64 T ≤ 2^p`. Paper: proof of
`thm:conf-grid` (conference.tex), "the envelope mass satisfies
`Z ≤ W = ∑_C |C|u_C < 2Z + 3/64 < (17/8)Z`"; full version: `lem:dynamiccellenvelope`
(attention_dynamic_index.tex). -/
theorem envelope_bounds (cell : ι → κ) (a : ι → ℝ) (aC : κ → ℝ) (a₀ : ℝ)
    (hprox : ∀ j, |a j - aC (cell j)| ≤ 1 / 4) (hattain : ∃ j, aC (cell j) = a₀)
    (u : κ → ℝ) (p : ℕ)
    (hu : ∀ j, cellWeight aC a₀ (cell j) ≤ u (cell j) ∧
      u (cell j) ≤ cellWeight aC a₀ (cell j) + 3 * (2 ^ p)⁻¹)
    (hp : 64 * (Fintype.card ι : ℝ) ≤ 2 ^ p) :
    ∑ j, memberWeight a a₀ j ≤ ∑ j, u (cell j) ∧
      ∑ j, u (cell j) < 2 * ∑ j, memberWeight a a₀ j + 3 / 64 ∧
      2 * ∑ j, memberWeight a a₀ j + 3 / 64 < 17 / 8 * ∑ j, memberWeight a a₀ j := by
  have hZ := half_lt_Z cell a aC a₀ hprox hattain
  have hne : (Finset.univ : Finset ι).Nonempty := by
    obtain ⟨j, -⟩ := hattain; exact ⟨j, Finset.mem_univ j⟩
  have hw := fun j => member_cell_weight (a₀ := a₀) (hprox j)
  refine ⟨Finset.sum_le_sum fun j _ => (hw j).1.trans (hu j).1, ?_, by linarith⟩
  have h2p : (0 : ℝ) < 2 ^ p := by positivity
  have hT : (Fintype.card ι : ℝ) * (3 * (2 ^ p)⁻¹) ≤ 3 / 64 := by
    rw [← mul_assoc, mul_comm _ (3 : ℝ), mul_assoc, ← div_eq_mul_inv]
    have : (Fintype.card ι : ℝ) / 2 ^ p ≤ 1 / 64 := by
      rw [div_le_iff₀ h2p]; linarith
    linarith
  calc ∑ j, u (cell j) ≤ ∑ j, (cellWeight aC a₀ (cell j) + 3 * (2 ^ p)⁻¹) :=
        Finset.sum_le_sum fun j _ => (hu j).2
    _ = ∑ j, cellWeight aC a₀ (cell j) + Fintype.card ι * (3 * (2 ^ p)⁻¹) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ < ∑ j, 2 * memberWeight a a₀ j + 3 / 64 := by
        have := Finset.sum_lt_sum_of_nonempty hne fun j _ => (hw j).2
        unfold cellWeight memberWeight
        linarith
    _ = 2 * ∑ j, memberWeight a a₀ j + 3 / 64 := by rw [Finset.mul_sum]

/-- The envelope mass as a sum over occupied cells: `∑ⱼ u_{C(j)} = ∑_C |C| u_C`. Paper: proof of
`thm:conf-grid` (conference.tex), `W = ∑_C |C| u_C`. -/
theorem sum_member_eq_sum_cells (cell : ι → κ) (u : κ → ℝ) :
    ∑ j, u (cell j) = ∑ C ∈ Finset.univ.image cell,
      ((Finset.univ.filter (fun j => cell j = C)).card : ℝ) * u C := by
  rw [Finset.sum_comp]
  simp [nsmul_eq_mul]

/-- Exactness of the rejection sampler. Choose cell `C` with probability `|C| u_C / W`, then a
uniform member `j ∈ C`, and accept with probability `w_j / u_C ≤ 1`. The accepted mass of `j`
is exactly `w_j / W`; the cell choice is a probability vector; the success probability is
`Z / W ∈ (0, 1]`; the first-acceptance series sums to `w_j / Z`; and `∑ₘ (1 - Z/W)^m = W / Z`
with `W / Z < 17/8`. For independent proposals these are the output law and the expected
number of proposals (`rejection_sampler_iid`). Paper: proof of `thm:conf-grid`
(conference.tex), "the accepted mass is exactly `w_j/W`, so the result has the target law and
the expected number of proposals is below `17/8`"; full version: `lem:dynamiccellenvelope`
(attention_dynamic_index.tex). -/
theorem rejection_sampler (cell : ι → κ) (a : ι → ℝ) (aC : κ → ℝ) (a₀ : ℝ)
    (hprox : ∀ j, |a j - aC (cell j)| ≤ 1 / 4) (hattain : ∃ j, aC (cell j) = a₀)
    (u : κ → ℝ) (p : ℕ)
    (hu : ∀ j, cellWeight aC a₀ (cell j) ≤ u (cell j) ∧
      u (cell j) ≤ cellWeight aC a₀ (cell j) + 3 * (2 ^ p)⁻¹)
    (hp : 64 * (Fintype.card ι : ℝ) ≤ 2 ^ p) :
    let W := ∑ j, u (cell j)
    let Z := ∑ j, memberWeight a a₀ j
    let size := fun C => ((Finset.univ.filter (fun j => cell j = C)).card : ℝ)
    (∑ C ∈ Finset.univ.image cell, size C * u C / W = 1) ∧
    (∀ j, 0 ≤ memberWeight a a₀ j / u (cell j) ∧ memberWeight a a₀ j / u (cell j) ≤ 1) ∧
    (∀ j, size (cell j) * u (cell j) / W * (1 / size (cell j))
        * (memberWeight a a₀ j / u (cell j)) = memberWeight a a₀ j / W) ∧
    (∑ j, memberWeight a a₀ j / W = Z / W) ∧ 0 < Z / W ∧ Z / W ≤ 1 ∧
    (∀ j, HasSum (fun m : ℕ => (1 - Z / W) ^ m * (memberWeight a a₀ j / W))
      (memberWeight a a₀ j / Z)) ∧
    HasSum (fun m : ℕ => (1 - Z / W) ^ m) (W / Z) ∧ W / Z < 17 / 8 := by
  intro W Z size
  obtain ⟨hZW, hW1, hW2⟩ := envelope_bounds cell a aC a₀ hprox hattain u p hu hp
  have hZ := half_lt_Z cell a aC a₀ hprox hattain
  have hZpos : 0 < Z := by linarith
  have hWpos : 0 < W := lt_of_lt_of_le hZpos hZW
  have hupos : ∀ j, 0 < u (cell j) := fun j => lt_of_lt_of_le (exp_pos _) (hu j).1
  have hsize : ∀ j, 0 < size (cell j) := by
    intro j
    have : j ∈ Finset.univ.filter (fun j' => cell j' = cell j) := by simp
    have := Finset.card_pos.mpr ⟨j, this⟩
    show (0 : ℝ) < ((Finset.univ.filter (fun j' => cell j' = cell j)).card : ℝ)
    exact_mod_cast this
  have hs0 : 0 < Z / W := div_pos hZpos hWpos
  have hs1 : Z / W ≤ 1 := (div_le_one hWpos).mpr hZW
  refine ⟨?_, fun j => ?_, fun j => ?_, ?_, hs0, hs1, fun j => ?_, ?_, ?_⟩
  · rw [← Finset.sum_div, ← sum_member_eq_sum_cells cell u]
    exact div_self hWpos.ne'
  · have hw := member_cell_weight (a₀ := a₀) (hprox j)
    exact ⟨div_nonneg (exp_pos _).le (hupos j).le,
      (div_le_one (hupos j)).mpr (hw.1.trans (hu j).1)⟩
  · have := hsize j
    have := hupos j
    field_simp
  · rw [← Finset.sum_div]
  · have h := hasSum_geometric_of_lt_one (r := 1 - Z / W) (by linarith) (by linarith)
    have h' := h.mul_right (memberWeight a a₀ j / W)
    convert h' using 1
    rw [sub_sub_cancel]
    field_simp
  · have h := hasSum_geometric_of_lt_one (r := 1 - Z / W) (by linarith) (by linarith)
    convert h using 1
    rw [sub_sub_cancel, inv_div]
  · rw [div_lt_iff₀ hZpos]
    linarith

/-- The target law: the normalized member weights are the attention probabilities,
`w_j / Z = e^{a_j} / ∑ₖ e^{a_k}`. Paper: proof of `thm:conf-grid` (conference.tex), "the result
has the target law"; full version: `thm:dynamicfixedrank` (attention_dynamic_index.tex), "the
output index has probabilities proportional to `exp(β⟨q,k_j⟩/n)`". -/
theorem memberWeight_div_sum (a : ι → ℝ) (a₀ : ℝ) (j : ι) :
    memberWeight a a₀ j / ∑ k, memberWeight a a₀ k = exp (a j) / ∑ k, exp (a k) := by
  unfold memberWeight
  have hs : ∀ k, exp (a k - a₀ - 1 / 4) = exp (-a₀ - 1 / 4) * exp (a k) := by
    intro k; rw [← exp_add]; ring_nf
  simp_rw [hs]
  rw [← Finset.mul_sum, mul_div_mul_left _ _ (exp_pos _).ne']

open MeasureTheory ProbabilityTheory in
/-- The rejection sampler as independent proposals. Let the proposal records `Y m = (member,
accepted)` be independent and identically distributed, with one-proposal law given by the
construction: the proposal is member `j` and it is accepted with probability
`(|C| u_C / W) (1 / |C|) (w_j / u_C)` where `C` is the cell of `j`. Then the first accepted
member has the attention law `e^{a_j} / ∑ₖ e^{a_k}` and the expected number of proposals is
`W / Z < 17/8`. This applies `first_success_law` and `expected_trials` of
`ExactSampling.RejectionLoop`. Paper: proof of `thm:conf-grid` (conference.tex), "the accepted
mass is exactly `w_j/W`, so the result has the target law and the expected number of proposals
is below `17/8`"; full version: `lem:dynamiccellenvelope` (attention_dynamic_index.tex). -/
theorem rejection_sampler_iid [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (cell : ι → κ) (a : ι → ℝ) (aC : κ → ℝ) (a₀ : ℝ)
    (hprox : ∀ j, |a j - aC (cell j)| ≤ 1 / 4) (hattain : ∃ j, aC (cell j) = a₀)
    (u : κ → ℝ) (p : ℕ)
    (hu : ∀ j, cellWeight aC a₀ (cell j) ≤ u (cell j) ∧
      u (cell j) ≤ cellWeight aC a₀ (cell j) + 3 * (2 ^ p)⁻¹)
    (hp : 64 * (Fintype.card ι : ℝ) ≤ 2 ^ p)
    (Y : ℕ → Ω → ι × Bool) (hY : iIndepFun Y P) (hid : ∀ m, P.map (Y m) = P.map (Y 0))
    (hmeas : ∀ m, Measurable (Y m))
    (hmass : ∀ j, P (Y 0 ⁻¹' {(j, true)}) = ENNReal.ofReal
      (((Finset.univ.filter (fun i => cell i = cell j)).card : ℝ) * u (cell j)
          / (∑ i, u (cell i)) * (1 / ((Finset.univ.filter (fun i => cell i = cell j)).card : ℝ))
        * (memberWeight a a₀ j / u (cell j)))) :
    (∀ j, P {ω | ∃ m, ω ∈ ExactSampling.RejectionLoop.Reached Y {r | r.2 = true} m ∧
        Y m ω ∈ ({(j, true)} : Set (ι × Bool))}
      = ENNReal.ofReal (exp (a j) / ∑ k, exp (a k))) ∧
    ∫⁻ ω, ∑' m, (ExactSampling.RejectionLoop.Reached Y {r | r.2 = true} m).indicator
        (fun _ => (1 : ℝ≥0∞)) ω ∂P
      = ENNReal.ofReal ((∑ j, u (cell j)) / ∑ j, memberWeight a a₀ j) ∧
    (∑ j, u (cell j)) / ∑ j, memberWeight a a₀ j < 17 / 8 := by
  classical
  obtain ⟨-, -, hstage, hsum, hs0, -, -, -, hlt⟩ :=
    rejection_sampler cell a aC a₀ hprox hattain u p hu hp
  have hms : ∀ t : Set (ι × Bool), MeasurableSet t := fun t => (Set.to_countable t).measurableSet
  have hZ := half_lt_Z cell a aC a₀ hprox hattain
  have hZpos : 0 < ∑ j, memberWeight a a₀ j := by linarith
  have hWpos : 0 < ∑ j, u (cell j) :=
    lt_of_lt_of_le hZpos (envelope_bounds cell a aC a₀ hprox hattain u p hu hp).1
  have hmass' : ∀ j, P (Y 0 ⁻¹' {(j, true)})
      = ENNReal.ofReal (memberWeight a a₀ j / ∑ i, u (cell i)) := fun j => by
    rw [hmass j]
    congr 1
    exact hstage j
  have hS : P (Y 0 ⁻¹' {r | r.2 = true})
      = ENNReal.ofReal ((∑ j, memberWeight a a₀ j) / ∑ i, u (cell i)) := by
    have hU : Y 0 ⁻¹' {r : ι × Bool | r.2 = true}
        = ⋃ j ∈ (Finset.univ : Finset ι), Y 0 ⁻¹' {(j, true)} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_singleton_iff,
        Finset.mem_univ, exists_const]
      constructor
      · intro h; exact ⟨(Y 0 ω).1, Prod.ext rfl h⟩
      · rintro ⟨j, hj⟩; rw [hj]
    rw [hU, measure_biUnion_finset]
    · rw [← hsum, ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (f := fun j => memberWeight a a₀ j / ∑ i, u (cell i))
        (fun j _ => div_nonneg (exp_pos _).le hWpos.le)]
      exact Finset.sum_congr rfl fun j _ => hmass' j
    · intro i _ j _ hij
      refine Disjoint.preimage _ (Set.disjoint_left.mpr fun r hr hr' => hij ?_)
      rw [Set.mem_singleton_iff] at hr hr'
      rw [hr] at hr'
      exact congrArg Prod.fst hr'
    · intro j _
      exact hmeas 0 (hms _)
  refine ⟨fun j => ?_, ?_, hlt⟩
  · rw [ExactSampling.RejectionLoop.first_success_law Y hY hid hmeas (hms _) (hms _)
      (fun r hr => by rw [Set.mem_singleton_iff] at hr; rw [hr]; rfl), hmass' j, hS,
      ← ENNReal.ofReal_div_of_pos hs0, ← memberWeight_div_sum a a₀ j]
    congr 1
    field_simp
  · rw [ExactSampling.RejectionLoop.expected_trials Y hY hid hmeas (hms _), hS,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_div_of_pos hs0]
    congr 1
    field_simp

end Envelope

/-- At temperature zero all scores vanish and the attention law is uniform. Paper: proof of
`thm:conf-grid` (conference.tex), "the case `β = 0` is uniform sampling". -/
theorem zero_temperature {n T : ℕ} (q : Fin n → ℝ) (k : Fin T → Fin n → ℝ)
    (j : Fin T) : exp (score 0 q (k j)) / ∑ i, exp (score 0 q (k i)) = 1 / T := by
  simp [score]

/-! ### The combined statement for a cache stored in charts -/

/-- `thm:conf-grid` (conference.tex), exact attention-index law for a cache stored in charts.
Members `ι` (a nonempty cache of `T` keys) are stored in charts `ch j ∈ Fin m` with `m ≤ r + 1`;
member `j` has key `k_j = c₀(ch j) + A(ch j) y_j` with `|A_{ab}| ≤ 2` and `y_j ∈ [-K, K]^r`.
The cell of `j` is `(ch j, ⌊y_j / Δ⌋)` with `Δ = K 2^{-h}`, `h = ⌈log₂ max(1, 8rβ̄QK)⌉`, and
each cell's proxy score is the score of a representative member of the same cell. Let
`a₀ = max_C a_C`, and let `u_C` satisfy `e_C ≤ u_C ≤ e_C + 3·2^{-p}` with `64 T ≤ 2^p`. Then
every proxy is within `1/4` of its members' scores, the first-acceptance series of the rejection
sampler sums to the attention law `e^{a_j} / ∑ₖ e^{a_k}`, the envelope ratio is `W/Z < 17/8`,
and the number of occupied cells is at most `min{T, (r+1)(5 + 32 r β̄ Q K)^r}`. For independent
proposals, `rejection_sampler_iid` (applied to these cells and weights) identifies the series
with the output law and `W/Z` with the expected number of proposals. The chart data are
hypotheses here and are not built from the key stream. Full version:
`thm:dynamicfixedrank` and `lem:dynamiccellenvelope` (attention_dynamic_index.tex). -/
theorem thm_conf_grid_law {ι : Type*} [Fintype ι] [Nonempty ι] {n r m : ℕ} (hn : 0 < n)
    (hr : 1 ≤ r) (hm : m ≤ r + 1) {β βbar Q K : ℝ} (hβ : 0 < β) (hββ : β ≤ βbar)
    (hQ : 0 < Q) (hK : 0 < K) (q : Fin n → ℝ) (hq : ∀ i, |q i| ≤ Q)
    (ch : ι → Fin m) (c₀ : Fin m → Fin n → ℝ) (A : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (hA : ∀ t a b, |A t a b| ≤ 2) (y : ι → Fin r → ℝ) (hy : ∀ j i, |y j i| ≤ K)
    (rep : ι → ι)
    (hrep : ∀ j, ch (rep j) = ch j ∧ cellIndex (K / 2 ^ gridExp (8 * r * βbar * Q * K)) (y (rep j))
      = cellIndex (K / 2 ^ gridExp (8 * r * βbar * Q * K)) (y j))
    (u : Fin m × (Fin r → ℤ) → ℝ) (p : ℕ) :
    let Δ := K / 2 ^ gridExp (8 * r * βbar * Q * K)
    let a : ι → ℝ := fun j => score β q (c₀ (ch j) + A (ch j) *ᵥ y j)
    let cell : ι → Fin m × (Fin r → ℤ) := fun j => (ch j, cellIndex Δ (y j))
    let aC : Fin m × (Fin r → ℤ) → ℝ := fun C =>
      if h : ∃ j, cell j = C then a (rep h.choose) else 0
    let a₀ := Finset.univ.sup' Finset.univ_nonempty (fun j => aC (cell j))
    (∀ j, cellWeight aC a₀ (cell j) ≤ u (cell j) ∧
      u (cell j) ≤ cellWeight aC a₀ (cell j) + 3 * (2 ^ p)⁻¹) →
    64 * (Fintype.card ι : ℝ) ≤ 2 ^ p →
    (∀ j, |a j - aC (cell j)| < 1 / 4) ∧
    (∀ j, HasSum (fun m : ℕ => (1 - (∑ k, memberWeight a a₀ k) / ∑ k, u (cell k)) ^ m
        * (memberWeight a a₀ j / ∑ k, u (cell k))) (exp (a j) / ∑ k, exp (a k))) ∧
    (∑ k, u (cell k)) / (∑ k, memberWeight a a₀ k) < 17 / 8 ∧
    ((Finset.univ.image cell).card : ℝ) ≤ Fintype.card ι ∧
    ((Finset.univ.image cell).card : ℝ) ≤ (r + 1) * (5 + 32 * r * βbar * Q * K) ^ r := by
  intro Δ a cell aC a₀ hu hp
  have hΔ : 0 < Δ := by positivity
  -- the proxy of a member's cell is the score of a member of the same cell
  have haC : ∀ j, ∃ j', cell j' = cell j ∧ aC (cell j) = a j' := by
    intro j
    have hex : ∃ j', cell j' = cell j := ⟨j, rfl⟩
    refine ⟨rep hex.choose, ?_, ?_⟩
    · have h1 := hrep hex.choose
      have h2 := hex.choose_spec
      have e1 : ch hex.choose = ch j := congrArg Prod.fst h2
      have e2 : cellIndex Δ (y hex.choose) = cellIndex Δ (y j) := congrArg Prod.snd h2
      exact Prod.ext (h1.1.trans e1) (h1.2.trans e2)
    · show (if h : ∃ j', cell j' = cell j then a (rep h.choose) else 0) = a (rep hex.choose)
      exact dite_eq_left_of_eq_true (eq_true hex)
  have hclose : ∀ j, |a j - aC (cell j)| < 1 / 4 := by
    intro j
    obtain ⟨j', hj', hval⟩ := haC j
    rw [hval]
    simp only [cell, Prod.ext_iff] at hj'
    have hcl := in_cell_score_bound hn hr le_rfl hβ hββ hQ hK (A (ch j)) (hA (ch j)) q hq
      (c₀ (ch j)) (y j) (y j') hj'.2.symm
    have : a j' = score β q (c₀ (ch j) + A (ch j) *ᵥ y j') := by
      simp only [a, hj'.1]
    rw [this]
    exact lt_of_lt_of_le hcl.1 hcl.2
  have hprox : ∀ j, |a j - aC (cell j)| ≤ 1 / 4 := fun j => (hclose j).le
  have hattain : ∃ j, aC (cell j) = a₀ := by
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun j => aC (cell j))
    exact ⟨j, hj.symm⟩
  have hrej := rejection_sampler cell a aC a₀ hprox hattain u p hu hp
  obtain ⟨-, -, -, -, -, -, hlaw, -, hprop⟩ := hrej
  refine ⟨hclose, fun j => ?_, hprop, ?_, ?_⟩
  · rw [← memberWeight_div_sum a a₀ j]
    exact hlaw j
  · have := Finset.card_image_le (s := Finset.univ) (f := cell)
    rw [Finset.card_univ] at this
    exact_mod_cast this
  · -- cells lie in `Fin m × piFinset`, with per-chart count bounded as in `card_cells_le`
    set h := gridExp (8 * r * βbar * Q * K)
    have hsub : Finset.univ.image cell ⊆ (Finset.univ : Finset (Fin m)) ×ˢ
        Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(2 : ℤ) ^ h) (2 ^ h)) := by
      intro z hz
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz
      rw [Finset.mem_product]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Fintype.mem_piFinset]
      intro i
      exact floor_mem_Icc hK h (hy j i)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, Fintype.card_piFinset_const,
      Int.card_Icc] at hcard
    have hval : ((2 : ℤ) ^ h + 1 - -(2 : ℤ) ^ h).toNat = 2 ^ (h + 1) + 1 := by
      have : (2 : ℤ) ^ h + 1 - -(2 : ℤ) ^ h = ((2 ^ (h + 1) + 1 : ℕ) : ℤ) := by
        push_cast; ring
      rw [this, Int.toNat_natCast]
    rw [hval] at hcard
    have hx : 0 ≤ 8 * (r : ℝ) * βbar * Q * K := by
      have : 0 ≤ βbar := hβ.le.trans hββ
      positivity
    have hlt : (2 : ℝ) ^ (h + 1) + 1 < 5 + 4 * (8 * r * βbar * Q * K) :=
      two_pow_succ_add_one_lt hx
    have hm' : (m : ℝ) ≤ r + 1 := by exact_mod_cast hm
    calc ((Finset.univ.image cell).card : ℝ) ≤ ((m * (2 ^ (h + 1) + 1) ^ r : ℕ) : ℝ) := by
          exact_mod_cast hcard
      _ = m * ((2 : ℝ) ^ (h + 1) + 1) ^ r := by push_cast; ring
      _ ≤ (r + 1) * (5 + 32 * r * βbar * Q * K) ^ r :=
          mul_le_mul hm' (pow_le_pow_left₀ (by positivity) (by linarith) r) (by positivity)
            (by positivity)

/-! ### Worked example: two repeated keys -/

/-- The attention mean `u = ∑ⱼ e^{a_j} v_j / ∑ⱼ e^{a_j}`. Paper: `eq:conf-attention`
(conference.tex). -/
noncomputable def attnMean {ι : Type*} [Fintype ι] (a v : ι → ℝ) : ℝ :=
  (∑ j, exp (a j) * v j) / ∑ j, exp (a j)

/-- Worked example after `thm:conf-grid` (conference.tex): a cache with `N₊` copies of the
all-ones key with value `+1` and `N₋` copies of its negative with value `-1` has attention
mean `(N₊ e^{βM} - N₋ e^{-βM}) / (N₊ e^{βM} + N₋ e^{-βM})`, where `M = n⁻¹ ∑ᵢ qᵢ`, and its
keys occupy at most two distinct points. The paper's count of occupied cells is not formalized:
cells depend on the chart history, and for example the append order `+1, -1, +1` occupies three
cells in two charts. -/
theorem worked_example {n : ℕ} (Np Nm : ℕ) (β : ℝ) (q : Fin n → ℝ) :
    attnMean (fun j : Fin Np ⊕ Fin Nm =>
        score β q (Sum.elim (fun _ : Fin Np => fun _ : Fin n => (1 : ℝ))
          (fun _ : Fin Nm => fun _ : Fin n => (-1 : ℝ)) j))
      (Sum.elim (fun _ => (1 : ℝ)) (fun _ => (-1 : ℝ)))
      = (Np * exp (β * ((∑ i, q i) / n)) - Nm * exp (-(β * ((∑ i, q i) / n))))
        / (Np * exp (β * ((∑ i, q i) / n)) + Nm * exp (-(β * ((∑ i, q i) / n)))) ∧
    ((Finset.univ : Finset (Fin Np ⊕ Fin Nm)).image
        (Sum.elim (fun _ : Fin Np => fun _ : Fin n => (1 : ℝ))
          (fun _ : Fin Nm => fun _ : Fin n => (-1 : ℝ)))).card ≤ 2 := by
  constructor
  · have h1 : score β q (fun _ : Fin n => (1 : ℝ)) = β * ((∑ i, q i) / n) := by
      simp only [score, dotProduct, mul_one]
      ring
    have h2 : score β q (fun _ : Fin n => (-1 : ℝ)) = -(β * ((∑ i, q i) / n)) := by
      simp only [score, dotProduct, mul_neg, mul_one, Finset.sum_neg_distrib]
      ring
    unfold attnMean
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, h1, h2, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, mul_neg]
    ring
  · calc ((Finset.univ : Finset (Fin Np ⊕ Fin Nm)).image
          (Sum.elim (fun _ : Fin Np => fun _ : Fin n => (1 : ℝ))
            (fun _ : Fin Nm => fun _ : Fin n => (-1 : ℝ)))).card
        ≤ ({fun _ => (1 : ℝ), fun _ => (-1 : ℝ)} : Finset (Fin n → ℝ)).card := by
          apply Finset.card_le_card
          intro z hz
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz
          cases j <;> simp
      _ ≤ 2 := Finset.card_le_two

/-- Worked example after `thm:conf-grid` (conference.tex): for a balanced cache `N₊ = N₋ ≥ 1`
the attention mean is `tanh(β M)`. -/
theorem worked_example_balanced {n : ℕ} (N : ℕ) (hN : 0 < N) (β : ℝ) (q : Fin n → ℝ) :
    attnMean (fun j : Fin N ⊕ Fin N =>
        score β q (Sum.elim (fun _ : Fin N => fun _ : Fin n => (1 : ℝ))
          (fun _ : Fin N => fun _ : Fin n => (-1 : ℝ)) j))
      (Sum.elim (fun _ => (1 : ℝ)) (fun _ => (-1 : ℝ)))
      = tanh (β * ((∑ i, q i) / n)) := by
  rw [(worked_example N N β q).1, Real.tanh_eq]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← mul_sub, ← mul_add, mul_div_mul_left _ _ hN'.ne']

end ExactSampling.GridIndex
