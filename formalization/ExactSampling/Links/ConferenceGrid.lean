import ExactSampling.Conference.GridIndex
import ExactSampling.Links.ChartBasis

/-!
# The appendable finite cache built from a key stream

Paper: `conference.tex`, Theorem `thm:conf-grid` (appendable finite cache) and its proof, with
Lemma `lem:conf-chart`; full version `thm:dynamicfixedrank` and `lem:dynamicchart`
(`attention_dynamic_index.tex`).

`ExactSampling.GridIndex.thm_conf_grid_law` takes the chart data of the cache as hypotheses:
the chart of every member, chart offsets `c₀`, chart coefficients with `|A_{ij}| ≤ 2`, chart
coordinates `y_j ∈ [-K, K]^r` and the keys `k_j = c₀ + A y_j`. Here the chart data are built
from the key stream itself, following the proof of `thm:conf-grid`: "fix the first key `c`.
Maintain a basis of differences `k_j - c`. At each increase of rank start a new chart from
Lemma `lem:conf-chart` ... Within one chart, `k = c₀ + A k_I`, where `c₀ = c - A c_I` and
`k_I ∈ [-K, K]^d`."

## Construction

The keys are a stream `keys : ℕ → Fin n → ℝ`; the cache holds the first `T` keys, and every
prefix has affine dimension `GridIndex.prefixDim keys t ≤ r` for `t ≤ T`. Member `j` belongs to
the chart indexed by the affine dimension `d` of the prefix `k_0, ..., k_j` (`chartIdx`), so a
new chart starts exactly when the dimension increases, and there are at most `r + 1` chart
indices. The space of chart `d` is the direction of the affine span of the longest prefix of
dimension at most `d` (`chartSpace`); its dimension is at most `d`, and `k_j - k_0` lies in it
for every member of the chart. `ChartBasis.exists_bounded_chart` (from
`Chart.exists_bounded_chart` and `Chart.chart_repr`) gives the selected rows `I`, the
coefficients `A` with `|A_{ij}| ≤ 1`, and `k_j = c₀ + A (k_j)_I` with `c₀ = k_0 - A (k_0)_I`.
A chart of dimension `d < r` is padded with zero columns and zero coordinates to the `r`
coordinates used by `GridIndex` (`padMat`, `padVec`).

## Main result

`stream_grid_law`: for the cache of the first `T ≥ 1` keys of such a stream, with keys in
`[-K, K]^n`, every chart hypothesis of `GridIndex.thm_conf_grid_law` is discharged, and the
conclusions are stated for the actual scores `a_j = (β/n)⟨q, k_j⟩`: each cell proxy is within
`1/4` of its members' scores, the first-acceptance series of the rejection sampler sums to the
attention law `e^{a_j} / ∑ₖ e^{a_k}`, the envelope ratio is `W/Z < 17/8`, and the number of
occupied cells is at most `min{T, (r+1)(5 + 32rβ̄QK)^r}`. `stream_chart_data` records the chart
facts themselves, and `stream_chart_count` bounds the number of charts used by one more than
the number of increases of the prefix dimension, hence by `r + 1` (`GridIndex.chart_count_le`).
`stream_grid_law` assumes `r ≥ 1`, as `GridIndex.thm_conf_grid_law` does; for `r = 0` (a
constant stream) it applies with `r = 1`, and `stream_cells_rank_zero` shows that the cache then
occupies a single cell.

## Not formalized

As in `ExactSampling.GridIndex`: all bit-complexity claims, the data structures (balanced
trees, append trees), and the cost of a chart change. The construction describes the cache
after `T` appends; that an append never changes an earlier chart (the chart space of a
dimension is already spanned when that dimension is first reached) is not stated. The case
`β = 0` (uniform sampling) is `GridIndex.zero_temperature` and is not repeated here.
-/

namespace ExactSampling.Links.ConferenceGrid

open Matrix Module GridIndex

/-! ## Zero padding -/

/-- A vector with `d` coordinates padded with zeros to `r` coordinates. Paper: `GridIndex`
represents a chart of dimension `d < r` with `r` coordinates (proof of `thm:conf-grid`,
conference.tex). -/
def padVec {d r : ℕ} (v : Fin d → ℝ) : Fin r → ℝ :=
  fun l => if h : (l : ℕ) < d then v ⟨l, h⟩ else 0

/-- A matrix with `d` columns padded with zero columns to `r` columns. -/
def padMat {n d r : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) : Matrix (Fin n) (Fin r) ℝ :=
  fun i l => if h : (l : ℕ) < d then A i ⟨l, h⟩ else 0

/-- Zero padding does not change a sum: `∑_{l < r} f̃(l) = ∑_{l < d} f(l)` for `d ≤ r`.
Auxiliary for `padMat_mulVec_padVec`. -/
theorem sum_pad {d r : ℕ} (hd : d ≤ r) (f : Fin d → ℝ) :
    ∑ l : Fin r, (if h : (l : ℕ) < d then f ⟨l, h⟩ else 0) = ∑ l : Fin d, f l := by
  set g : ℕ → ℝ := fun m => if h : m < d then f ⟨m, h⟩ else 0 with hg
  have h1 : ∑ l : Fin r, (if h : (l : ℕ) < d then f ⟨l, h⟩ else 0) = ∑ l : Fin r, g l := rfl
  have h2 : ∑ l : Fin d, f l = ∑ l : Fin d, g l :=
    Finset.sum_congr rfl fun l _ => by simp [hg, l.isLt]
  rw [h1, h2, Fin.sum_univ_eq_sum_range g r, Fin.sum_univ_eq_sum_range g d,
    ← Finset.sum_range_add_sum_Ico g hd]
  have h3 : ∑ m ∈ Finset.Ico d r, g m = 0 :=
    Finset.sum_eq_zero fun m hm => by
      have := (Finset.mem_Ico.mp hm).1
      simp [hg, not_lt.mpr this]
  rw [h3, add_zero]

/-- `Ã ỹ = A y` for the zero paddings of `A` and `y` when `d ≤ r`. Auxiliary for the chart
representation in the proof of `thm:conf-grid` (conference.tex). -/
theorem padMat_mulVec_padVec {n d r : ℕ} (hd : d ≤ r) (A : Matrix (Fin n) (Fin d) ℝ)
    (y : Fin d → ℝ) : padMat A *ᵥ (padVec y : Fin r → ℝ) = A *ᵥ y := by
  funext i
  simp only [mulVec, dotProduct, padMat, padVec]
  rw [← sum_pad hd]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

/-- Padding keeps the bound `|A_{ij}| ≤ 2`. Auxiliary for `thm:conf-grid` (conference.tex). -/
theorem abs_padMat_le {n d r : ℕ} {A : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ i j, |A i j| ≤ c) (i : Fin n) (l : Fin r) : |padMat A i l| ≤ c := by
  unfold padMat
  split_ifs
  · exact hA _ _
  · simpa using hc

/-- Padding keeps the bound `|y_i| ≤ K`. Auxiliary for `thm:conf-grid` (conference.tex). -/
theorem abs_padVec_le {d r : ℕ} {y : Fin d → ℝ} {K : ℝ} (hK : 0 ≤ K) (hy : ∀ i, |y i| ≤ K)
    (l : Fin r) : |(padVec y : Fin r → ℝ) l| ≤ K := by
  unfold padVec
  split_ifs
  · exact hy _
  · simpa using hK

/-! ## Charts of a key stream -/

variable {n : ℕ}

/-- The empty prefix has affine dimension zero. Auxiliary for the chart construction in the proof
of `thm:conf-grid` (conference.tex). -/
theorem prefixDim_zero (keys : ℕ → Fin n → ℝ) : prefixDim keys 0 = 0 := by
  simp [prefixDim]

/-- The longest prefix of the first `T` keys whose affine dimension is at most `d`. Paper:
proof of `thm:conf-grid` (conference.tex), the prefix on which the rank stays at most `d`. -/
noncomputable def chartEnd (keys : ℕ → Fin n → ℝ) (T d : ℕ) : ℕ :=
  Nat.findGreatest (fun t => prefixDim keys t ≤ d) T

/-- The space of the chart for dimension `d`: the span of the differences of the keys in the
longest prefix of dimension at most `d`. Paper: proof of `thm:conf-grid` (conference.tex),
"Maintain a basis of differences `k_j - c`". -/
noncomputable def chartSpace (keys : ℕ → Fin n → ℝ) (T d : ℕ) : Submodule ℝ (Fin n → ℝ) :=
  (affineSpan ℝ (keys '' Set.Iio (chartEnd keys T d))).direction

/-- The chart space for dimension `d` has dimension at most `d`. Auxiliary for the proof of
`thm:conf-grid` (conference.tex), "`k_I ∈ [-K,K]^d`" with `d ≤ r`. -/
theorem finrank_chartSpace_le (keys : ℕ → Fin n → ℝ) (T d : ℕ) :
    finrank ℝ (chartSpace keys T d) ≤ d :=
  Nat.findGreatest_spec (P := fun t => prefixDim keys t ≤ d) (Nat.zero_le T)
    (by rw [prefixDim_zero]; exact Nat.zero_le d)

/-- If the prefix `k_0, ..., k_j` has dimension at most `d`, then `k_j - k_0` lies in the chart
space for dimension `d`. Paper: proof of `thm:conf-grid` (conference.tex), "Membership in the
current span". -/
theorem sub_mem_chartSpace (keys : ℕ → Fin n → ℝ) {T d j : ℕ} (hjT : j + 1 ≤ T)
    (hj : prefixDim keys (j + 1) ≤ d) : keys j - keys 0 ∈ chartSpace keys T d := by
  have hle : j + 1 ≤ chartEnd keys T d :=
    Nat.le_findGreatest (P := fun t => prefixDim keys t ≤ d) hjT hj
  have h1 : keys j ∈ affineSpan ℝ (keys '' Set.Iio (chartEnd keys T d)) :=
    mem_affineSpan ℝ ⟨j, by simp only [Set.mem_Iio]; omega, rfl⟩
  have h0 : keys 0 ∈ affineSpan ℝ (keys '' Set.Iio (chartEnd keys T d)) :=
    mem_affineSpan ℝ ⟨0, by simp only [Set.mem_Iio]; omega, rfl⟩
  have := AffineSubspace.vsub_mem_direction h1 h0
  rwa [vsub_eq_sub] at this

/-- The selected rows of the chart for dimension `d`, from `ChartBasis.exists_bounded_chart`.
Paper: proof of `thm:conf-grid` (conference.tex), "start a new chart from Lemma
`lem:conf-chart`". -/
noncomputable def chartRows (keys : ℕ → Fin n → ℝ) (T d : ℕ) :
    Fin (finrank ℝ (chartSpace keys T d)) → Fin n :=
  (ChartBasis.exists_bounded_chart (chartSpace keys T d)).choose

/-- The chart coefficients `A = U (U_I)⁻¹` of the chart for dimension `d`. Paper:
`lem:conf-chart` (conference.tex). -/
noncomputable def chartCoeff (keys : ℕ → Fin n → ℝ) (T d : ℕ) :
    Matrix (Fin n) (Fin (finrank ℝ (chartSpace keys T d))) ℝ :=
  Chart.coeff (ChartBasis.basisMatrix (chartSpace keys T d)) (chartRows keys T d)

/-- The chart index of member `j`: the affine dimension of the prefix `k_0, ..., k_j` (capped at
`r`, which is never active under the rank hypothesis). Paper: proof of `thm:conf-grid`
(conference.tex), "At each increase of rank start a new chart". -/
noncomputable def chartIdx (keys : ℕ → Fin n → ℝ) (r j : ℕ) : Fin (r + 1) :=
  ⟨min (prefixDim keys (j + 1)) r, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The offset `c₀ = c - A c_I` of a chart, with `c = k_0` the first key. Paper: proof of
`thm:conf-grid` (conference.tex). -/
noncomputable def streamOffset (keys : ℕ → Fin n → ℝ) (r T : ℕ) (c : Fin (r + 1)) :
    Fin n → ℝ :=
  keys 0 - chartCoeff keys T c *ᵥ (fun l => keys 0 (chartRows keys T c l))

/-- The coefficients of a chart, padded to `r` columns. Paper: proof of `thm:conf-grid`
(conference.tex). -/
noncomputable def streamCoeff (keys : ℕ → Fin n → ℝ) (r T : ℕ) (c : Fin (r + 1)) :
    Matrix (Fin n) (Fin r) ℝ :=
  padMat (chartCoeff keys T c)

/-- The chart coordinates `y_j = (k_j)_I` of member `j` in its chart, padded to `r`
coordinates. Paper: proof of `thm:conf-grid` (conference.tex), "`k_I ∈ [-K,K]^d`". -/
noncomputable def streamCoord (keys : ℕ → Fin n → ℝ) (r T j : ℕ) : Fin r → ℝ :=
  padVec (fun l => keys j (chartRows keys T (chartIdx keys r j) l))

/-- Paper: proof of `thm:conf-grid` (conference.tex), the chart data of the cache, built from
the key stream: every chart index is at most `r`, the chart index of member `j` is the affine
dimension of its prefix, the (padded) chart coefficients satisfy `|A_{ij}| ≤ 2`, the chart
coordinates lie in `[-K, K]^r`, and every member's key has the chart representation
`k_j = c₀ + A y_j`. This discharges the chart hypotheses of `GridIndex.thm_conf_grid_law`.
Full version: proof of `thm:dynamicfixedrank` (attention_dynamic_index.tex). -/
theorem stream_chart_data (keys : ℕ → Fin n → ℝ) {r T : ℕ}
    (hdim : ∀ t ≤ T, prefixDim keys t ≤ r) {K : ℝ} (hK : 0 ≤ K)
    (hkeys : ∀ j < T, ∀ i, |keys j i| ≤ K) :
    (∀ j < T, (chartIdx keys r j : ℕ) = prefixDim keys (j + 1)) ∧
    (∀ c a b, |streamCoeff keys r T c a b| ≤ 2) ∧
    (∀ j < T, ∀ l, |streamCoord keys r T j l| ≤ K) ∧
    ∀ j < T, keys j = streamOffset keys r T (chartIdx keys r j) +
      streamCoeff keys r T (chartIdx keys r j) *ᵥ streamCoord keys r T j := by
  have hidx : ∀ j < T, (chartIdx keys r j : ℕ) = prefixDim keys (j + 1) := fun j hj =>
    min_eq_left (hdim (j + 1) hj)
  refine ⟨hidx, fun c a b => ?_, fun j hj l => ?_, fun j hj => ?_⟩
  · exact abs_padMat_le (by norm_num)
      (ChartBasis.exists_bounded_chart (chartSpace keys T c)).choose_spec.2.2.2.2.1 a b
  · exact abs_padVec_le hK (fun l => hkeys j hj _) l
  · set c := chartIdx keys r j with hc
    have hspec := (ChartBasis.exists_bounded_chart (chartSpace keys T c)).choose_spec
    have hmem : keys j - keys 0 ∈ chartSpace keys T c :=
      sub_mem_chartSpace keys hj (le_of_eq (hidx j hj).symm)
    have hrepr := hspec.2.2.2.2.2 (keys 0) (keys j) hmem
    have hdr : finrank ℝ (chartSpace keys T c) ≤ r :=
      (finrank_chartSpace_le keys T c).trans (Nat.lt_succ_iff.mp c.isLt)
    unfold streamOffset streamCoeff streamCoord
    rw [← hc, padMat_mulVec_padVec hdr]
    exact hrepr

/-- For a monotone `f : ℕ → ℕ`, the values `f(1), ..., f(T)` number at most one more than the
increases `f(t) < f(t+1)` with `t < T`. Auxiliary for `stream_chart_count`. -/
theorem card_image_succ_le (f : ℕ → ℕ) (hf : Monotone f) (T : ℕ) :
    ((Finset.range T).image (fun j => f (j + 1))).card ≤
      ((Finset.range T).filter (fun t => f t < f (t + 1))).card + 1 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.range_add_one, Finset.image_insert, Finset.filter_insert]
    have hT : T ∉ (Finset.range T).filter (fun t => f t < f (t + 1)) := by simp
    by_cases hlt : f T < f (T + 1)
    · simp only [hlt, ↓reduceIte]
      rw [Finset.card_insert_of_notMem hT]
      exact (Finset.card_insert_le _ _).trans (by omega)
    · simp only [hlt, ↓reduceIte]
      have heq : f (T + 1) = f T := le_antisymm (not_lt.mp hlt) (hf (Nat.le_succ T))
      rcases T with _ | T
      · simp
      · have hmem : f (T + 1 + 1) ∈ (Finset.range (T + 1)).image (fun j => f (j + 1)) :=
          Finset.mem_image.mpr ⟨T, by simp, heq.symm⟩
        rw [Finset.insert_eq_of_mem hmem]
        exact ih

/-- Paper: proof of `thm:conf-grid` (conference.tex), "At each increase of rank start a new
chart ... At most `r+1` charts are ever used": the number of charts used by the first `T`
keys is at most one more than the number of increases of the prefix dimension, hence at most
`r + 1` by `GridIndex.chart_count_le`. Full version: proof of `thm:dynamicfixedrank`
(attention_dynamic_index.tex). -/
theorem stream_chart_count (keys : ℕ → Fin n → ℝ) {r T : ℕ}
    (hdim : ∀ t ≤ T, prefixDim keys t ≤ r) :
    ((Finset.range T).image (chartIdx keys r)).card ≤
        ((Finset.range T).filter (fun t => prefixDim keys t < prefixDim keys (t + 1))).card + 1 ∧
      ((Finset.range T).image (chartIdx keys r)).card ≤ r + 1 := by
  have hval : ((Finset.range T).image (chartIdx keys r)).card =
      ((Finset.range T).image (fun j => prefixDim keys (j + 1))).card := by
    rw [← Finset.card_image_of_injective _ Fin.val_injective, Finset.image_image]
    congr 1
    refine Finset.image_congr fun j hj => ?_
    exact min_eq_left (hdim (j + 1) (Finset.mem_range.mp hj))
  have h1 := card_image_succ_le (prefixDim keys) (prefixDim_mono keys) T
  rw [hval]
  exact ⟨h1, h1.trans (chart_count_le keys r T hdim)⟩

/-- Paper: `thm:conf-grid` (conference.tex), exact attention-index law for the cache of the
first `T ≥ 1` keys (`NeZero T`) of a stream in `[-K, K]^n` whose prefixes have affine
dimension at most `r`, with the chart data built from the stream (`stream_chart_data`)
instead of assumed. With
the scores `a_j = (β/n)⟨q, k_j⟩` of the actual keys, the cells `(chart, ⌊y_j / Δ⌋)`, the grid
width `Δ = K 2^{-h}`, `h = ⌈log₂ max(1, 8rβ̄QK)⌉`, cell proxies given by representatives `rep`
in the same cell (for example `rep = id`), `a₀ = max_C a_C`, and upper bounds
`e_C ≤ u_C ≤ e_C + 3·2^{-p}` with `64 T ≤ 2^p`: every proxy is within `1/4` of its members'
scores, the first-acceptance series of the rejection sampler sums to the attention law
`e^{a_j} / ∑ₖ e^{a_k}`, the envelope ratio is `W/Z < 17/8`, and the number of occupied cells is
at most `min{T, (r+1)(5 + 32rβ̄QK)^r}`. Obtained from `GridIndex.thm_conf_grid_law`; for
independent proposals `GridIndex.rejection_sampler_iid` identifies the series with the output
law and `W/Z` with the expected number of proposals. Full version: `thm:dynamicfixedrank` and
`lem:dynamiccellenvelope` (attention_dynamic_index.tex). The hypothesis `r ≥ 1` comes from
`GridIndex.thm_conf_grid_law`; the rank-zero case of `thm:conf-grid` (a constant stream) is
this theorem with `r = 1` together with `stream_cells_rank_zero`. -/
theorem stream_grid_law (keys : ℕ → Fin n → ℝ) {r T : ℕ} [NeZero T] (hn : 0 < n)
    (hr : 1 ≤ r) (hdim : ∀ t ≤ T, prefixDim keys t ≤ r) {β βbar Q K : ℝ} (hβ : 0 < β)
    (hββ : β ≤ βbar) (hQ : 0 < Q) (hK : 0 < K) (hkeys : ∀ j < T, ∀ i, |keys j i| ≤ K)
    (q : Fin n → ℝ) (hq : ∀ i, |q i| ≤ Q) (rep : Fin T → Fin T)
    (hrep : ∀ j : Fin T, chartIdx keys r (rep j) = chartIdx keys r j ∧
      cellIndex (K / 2 ^ gridExp (8 * r * βbar * Q * K)) (streamCoord keys r T (rep j)) =
        cellIndex (K / 2 ^ gridExp (8 * r * βbar * Q * K)) (streamCoord keys r T j))
    (u : Fin (r + 1) × (Fin r → ℤ) → ℝ) (p : ℕ) :
    let Δ := K / 2 ^ gridExp (8 * r * βbar * Q * K)
    let a : Fin T → ℝ := fun j => score β q (keys j)
    let cell : Fin T → Fin (r + 1) × (Fin r → ℤ) := fun j =>
      (chartIdx keys r j, cellIndex Δ (streamCoord keys r T j))
    let aC : Fin (r + 1) × (Fin r → ℤ) → ℝ := fun C =>
      haveI := Fintype.decidableExistsFintype (p := fun j : Fin T => cell j = C)
      if h : ∃ j, cell j = C then a (rep h.choose) else 0
    let a₀ := Finset.univ.sup' Finset.univ_nonempty (fun j => aC (cell j))
    (∀ j, cellWeight aC a₀ (cell j) ≤ u (cell j) ∧
      u (cell j) ≤ cellWeight aC a₀ (cell j) + 3 * (2 ^ p)⁻¹) →
    64 * (T : ℝ) ≤ 2 ^ p →
    (∀ j, |a j - aC (cell j)| < 1 / 4) ∧
    (∀ j, HasSum (fun m : ℕ => (1 - (∑ k, memberWeight a a₀ k) / ∑ k, u (cell k)) ^ m
        * (memberWeight a a₀ j / ∑ k, u (cell k))) (Real.exp (a j) / ∑ k, Real.exp (a k))) ∧
    (∑ k, u (cell k)) / (∑ k, memberWeight a a₀ k) < 17 / 8 ∧
    ((Finset.univ.image cell).card : ℝ) ≤ T ∧
    ((Finset.univ.image cell).card : ℝ) ≤ (r + 1) * (5 + 32 * r * βbar * Q * K) ^ r := by
  intro Δ a cell aC a₀ hu hp
  obtain ⟨-, hA, hy, hrepr⟩ := stream_chart_data keys hdim hK.le hkeys
  have e : a = fun j : Fin T => score β q (streamOffset keys r T (chartIdx keys r j) +
      streamCoeff keys r T (chartIdx keys r j) *ᵥ streamCoord keys r T j) := by
    funext j
    show score β q (keys j) = _
    rw [← hrepr j j.isLt]
  clear_value a
  subst e
  have h := thm_conf_grid_law (ι := Fin T) hn hr le_rfl hβ hββ hQ hK q hq
    (fun j => chartIdx keys r j) (streamOffset keys r T) (streamCoeff keys r T) hA
    (fun j => streamCoord keys r T j) (fun j i => hy j j.isLt i) rep hrep u p
  have hcard : (Fintype.card (Fin T) : ℝ) = T := by simp
  obtain ⟨h1, h2, h3, h4, h5⟩ := h hu (by rw [hcard]; exact hp)
  exact ⟨h1, h2, h3, by rw [← hcard]; exact h4, h5⟩

/-- Paper: `thm:conf-grid` (conference.tex) at key rank `r = 0`: a stream whose prefixes have
affine dimension zero is constant, `M_T ≤ min{T, (0+1)(5 + 0)^0} = 1`. `stream_grid_law` assumes
`r ≥ 1` (as `GridIndex.thm_conf_grid_law` does, for its in-cell bound); a rank-zero stream also
has every prefix of dimension at most one, so `stream_grid_law` applies with `r = 1`, and this
theorem shows that the cache then occupies a single cell, as the rank-zero bound states. -/
theorem stream_cells_rank_zero (keys : ℕ → Fin n → ℝ) {T : ℕ}
    (hdim : ∀ t ≤ T, prefixDim keys t ≤ 0) (Δ : ℝ) :
    ((Finset.univ : Finset (Fin T)).image (fun j : Fin T =>
      (chartIdx keys 1 j, cellIndex Δ (streamCoord keys 1 T j)))).card ≤ 1 := by
  have key : ∀ j : Fin T, (chartIdx keys 1 j, cellIndex Δ (streamCoord keys 1 T j)) =
      ((0 : Fin 2), cellIndex Δ 0) := by
    intro j
    have hd : prefixDim keys (j + 1) = 0 := Nat.le_zero.mp (hdim _ j.isLt)
    have hcv : (chartIdx keys 1 j : ℕ) = 0 := by simp [chartIdx, hd]
    have hle := finrank_chartSpace_le keys T (chartIdx keys 1 j)
    have hy : streamCoord keys 1 T j = 0 := by
      funext l
      unfold streamCoord padVec
      split_ifs with h
      · exact absurd h (by omega)
      · rfl
    have hc : chartIdx keys 1 j = 0 := Fin.ext (by rw [hcv]; rfl)
    rw [hc, hy]
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j', -, rfl⟩ := Finset.mem_image.mp hb
  rw [key j, key j']

end ExactSampling.Links.ConferenceGrid
