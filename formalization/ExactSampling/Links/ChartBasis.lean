import ExactSampling.Conference.Chart

/-!
# Bounded charts of a linear subspace

Paper: `conference.tex`, Lemma `lem:conf-chart` as it is applied in the proofs of
`thm:conf-grid` ("Maintain a basis of differences `k_j - c`. At each increase of rank start a
new chart from Lemma `lem:conf-chart`") and `lem:conf-stability` ("Apply Lemma `lem:conf-chart`
to a column basis of `W_K`"). Full version: `lem:dynamicchart` (`attention_dynamic_index.tex`).

`ExactSampling.Chart` proves `lem:conf-chart` for a full-column-rank matrix `U`. Both
applications start from a subspace instead: the span of the key differences, or the column
space of the key matrix `W_K`. This module supplies the column basis. For a subspace `S` of
`ℝⁿ` of dimension `d`, `basisMatrix S` is an `n × d` matrix whose columns form a basis of `S`;
it has rank `d` (`rank_basisMatrix`) and its column span is `S` (`mem_iff_exists_mulVec`).
`exists_bounded_chart` then gives selected rows `I` with chart coefficients
`A = U (U_I)⁻¹` satisfying `A_I = I_d` and `|A_{ij}| ≤ 1 ≤ 2`, and every vector `k` with
`k - c ∈ S` has the chart representation `k = c₀ + A k_I`, `c₀ = c - A c_I`.

Not formalized: the bit lengths of the chart (the dyadic entries, Cramer's rule and the work
bound of `lem:conf-chart`); see `ExactSampling.Chart`.
-/

namespace ExactSampling.Links.ChartBasis

open Matrix Module

variable {n : ℕ}

/-- The `n × d` matrix whose columns are the vectors of the standard finite basis of a
subspace `S` of dimension `d`. Paper: proof of `thm:conf-grid` (conference.tex), "a basis of
differences `k_j - c`"; proof of `lem:conf-stability` (conference.tex), "a column basis of
`W_K`". -/
noncomputable def basisMatrix (S : Submodule ℝ (Fin n → ℝ)) :
    Matrix (Fin n) (Fin (finrank ℝ S)) ℝ :=
  Matrix.of fun i l => ((Module.finBasis ℝ S l : S) : Fin n → ℝ) i

/-- `U z = ∑_l z_l b_l` for the basis vectors `b_l` of `S`. Auxiliary for the column basis in
the proofs of `thm:conf-grid` and `lem:conf-stability` (conference.tex). -/
theorem basisMatrix_mulVec (S : Submodule ℝ (Fin n → ℝ)) (z : Fin (finrank ℝ S) → ℝ) :
    basisMatrix S *ᵥ z = ((∑ l, z l • Module.finBasis ℝ S l : S) : Fin n → ℝ) := by
  funext i
  simp [basisMatrix, mulVec, dotProduct, Finset.sum_apply, mul_comm]

/-- The column span of `basisMatrix S` is `S`. Auxiliary for the column basis in the proofs of
`thm:conf-grid` and `lem:conf-stability` (conference.tex). -/
theorem mem_iff_exists_mulVec (S : Submodule ℝ (Fin n → ℝ)) (v : Fin n → ℝ) :
    v ∈ S ↔ ∃ z, v = basisMatrix S *ᵥ z := by
  constructor
  · intro hv
    refine ⟨fun l => (Module.finBasis ℝ S).repr ⟨v, hv⟩ l, ?_⟩
    rw [basisMatrix_mulVec, (Module.finBasis ℝ S).sum_repr ⟨v, hv⟩]
  · rintro ⟨z, rfl⟩
    rw [basisMatrix_mulVec]
    exact Submodule.coe_mem _

/-- The image of `basisMatrix S` is `S`. Auxiliary for `rank_basisMatrix`. -/
theorem range_mulVecLin_basisMatrix (S : Submodule ℝ (Fin n → ℝ)) :
    LinearMap.range (basisMatrix S).mulVecLin = S := by
  ext v
  rw [LinearMap.mem_range, mem_iff_exists_mulVec]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩

/-- `basisMatrix S` has full column rank `d = dim S`, the hypothesis of `lem:conf-chart`.
Paper: `lem:conf-chart` (conference.tex), "an `n × d` full-column-rank matrix `U`". -/
theorem rank_basisMatrix (S : Submodule ℝ (Fin n → ℝ)) :
    (basisMatrix S).rank = finrank ℝ S := by
  unfold Matrix.rank
  rw [range_mulVecLin_basisMatrix]

/-- A bounded chart of a subspace. For a subspace `S` of dimension `d`, there are distinct
selected rows `I` of the column basis `U = basisMatrix S` with nonsingular `U_I`, such that the
chart coefficients `A = U (U_I)⁻¹` satisfy `A_I = I_d` and `|A_{ij}| ≤ 1`, hence `≤ 2`, and
every `k` with `k - c ∈ S` satisfies `k = c₀ + A k_I` with `c₀ = c - A c_I`.
Paper: `lem:conf-chart` (conference.tex) applied in the proofs of `thm:conf-grid` ("within one
chart, `k = c₀ + A k_I`, where `c₀ = c - A c_I`") and `lem:conf-stability`; full version
`lem:dynamicchart` (attention_dynamic_index.tex). -/
theorem exists_bounded_chart (S : Submodule ℝ (Fin n → ℝ)) :
    ∃ I : Fin (finrank ℝ S) → Fin n, Function.Injective I ∧
      (Chart.rows (basisMatrix S) I).det ≠ 0 ∧
      Chart.rows (Chart.coeff (basisMatrix S) I) I = 1 ∧
      (∀ i j, |Chart.coeff (basisMatrix S) I i j| ≤ 1) ∧
      (∀ i j, |Chart.coeff (basisMatrix S) I i j| ≤ 2) ∧
      ∀ c k : Fin n → ℝ, k - c ∈ S →
        k = (c - Chart.coeff (basisMatrix S) I *ᵥ (fun l => c (I l))) +
          Chart.coeff (basisMatrix S) I *ᵥ (fun l => k (I l)) := by
  obtain ⟨I, hinj, hdet, hid, h1, h2⟩ :=
    Chart.exists_bounded_chart (basisMatrix S) (rank_basisMatrix S)
  refine ⟨I, hinj, hdet, hid, h1, h2, fun c k hk => ?_⟩
  exact Chart.chart_repr (basisMatrix S) I hdet c k ((mem_iff_exists_mulVec S _).mp hk)

end ExactSampling.Links.ChartBasis
