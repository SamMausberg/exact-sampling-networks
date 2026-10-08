import Mathlib

/-!
# A fixed finite model: polylogarithmic per-token cost

This module formalizes the proof of the corollary `cor:conf-fixed-model` ("A fixed finite
model", conference.tex, end of section `sec:conf-replay`).  The corollary substitutes into the
explicit per-token bound `eq:conf-explicit` (conference.tex) and then invokes `lem:conf-replay`.
The full-version statement is `cor:fixedmodelcontext` (attention_moment_decoder.tex), with the
explicit bound `eq:momentexplicitcost`.  The corollary specializes the cost of the sampler of
`thm:conf-decoder`; the key rank `r` is an arbitrary natural number, so full key rank `r = n`
is included.

Main result, `fixedModel_expected_isBigO`: for a fixed model, define the deterministic cost
`fixedCost p T` of `eq:conf-explicit` at routine accuracy `p` and context length `T`, with
working precision `P = p + G₀` (a fixed guard), Taylor degree `m = ⌈8(P + κ + 3H + 7)⌉`
(`eq:conf-features` at precision `P + κ`, with fixed `κ` rescaling bits and fixed `H`) and
integer length `L = C_r{m[P + b + log(n+m+D+V+2)] + log(T+2) + 1}`.  We prove
`fixedCost p T ≤ A (p + log(T+2))^(2r+12)` for `p ≥ 1` (`fixedCost_le_pow`), so the exponent
`2r + 12` is derived from `eq:conf-explicit`.  Feeding this cost function into `lem:conf-replay`
then gives expected per-token cost `O(log^(2r+12)(T+2))`.

Stand-in: `lem:conf-replay` itself, as the hypothesis `hreplay` of
`fixedModel_expected_isBigO`.  It says that for every cost function `G` with `G(u) ≤ A u^k` for
`u ≥ 1`, if the deterministic evaluator at accuracy `p ≥ 1` costs at most `G(p + log(T+2))`
per (re)played token, then the expected per-token cost is at most `C_k (A S^k + S)`, with
`S = 1 + log(V+2) + log(T+2)`.  The hypothesis only concerns `G`; the exponent is not assumed.

Also formalized, as `Asymptotics.IsBigO` statements along `Filter.atTop`: from a working
precision `P = O(log(T+2))` alone, the Taylor degree is `O(log(T+2))`, the integer length is
`O(log²(T+2))`, and the explicit bound is `O(log^(2r+12)(T+2))` (`fixedModel_cost_isBigO`).
The operation counting that produces `eq:conf-explicit` itself is not formalized.
-/

namespace ExactSampling.FixedModel

open Asymptotics Filter

/-- `log(T+2)`, natural logarithm.  `ExactSampling.Replay` states `lem:conf-replay` with
`log₂`; `ExactSampling.Links.ConferenceDecoder` converts between the two. -/
noncomputable def lg (T : ℕ) : ℝ := Real.log ((T : ℝ) + 2)

/-- `log 2 ≤ log(T+2)`.  Auxiliary for `cor:conf-fixed-model`
(conference.tex). -/
theorem log_two_le_lg (T : ℕ) : Real.log 2 ≤ lg T :=
  Real.log_le_log (by norm_num) (by linarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)])

/-- `log(T+2) > 0`.  Auxiliary for `cor:conf-fixed-model`
(conference.tex). -/
theorem lg_pos (T : ℕ) : 0 < lg T :=
  lt_of_lt_of_le (Real.log_pos one_lt_two) (log_two_le_lg T)

/-- `1 = O(log(T+2))`.  Auxiliary for `cor:conf-fixed-model`
(conference.tex). -/
theorem one_isBigO_lg : (fun _ : ℕ => (1 : ℝ)) =O[atTop] lg := by
  refine IsBigO.of_bound (1 / Real.log 2) (Eventually.of_forall fun T => ?_)
  have h2 := Real.log_pos one_lt_two
  rw [norm_one, Real.norm_of_nonneg (lg_pos T).le, div_mul_eq_mul_div, one_mul,
    le_div_iff₀ h2, one_mul]
  exact log_two_le_lg T

/-- Constants are `O(log(T+2))`.  Auxiliary for `cor:conf-fixed-model`
(conference.tex). -/
theorem const_isBigO_lg (c : ℝ) : (fun _ : ℕ => c) =O[atTop] lg :=
  (isBigO_const_one ℝ c atTop).trans one_isBigO_lg

/-- `log(T+2) = O(log^k(T+2))` for `k ≥ 1`.  Auxiliary for `cor:conf-fixed-model`
(conference.tex). -/
theorem lg_isBigO_lg_pow {k : ℕ} (hk : 1 ≤ k) : lg =O[atTop] (fun T => lg T ^ k) := by
  have h := (isBigO_refl lg atTop).mul (one_isBigO_lg.pow (k - 1))
  refine h.congr (fun T => by simp) (fun T => ?_)
  rw [← pow_succ', Nat.sub_add_cancel hk]

/-- Constants are `O(log^k(T+2))` for `k ≥ 1`.  Auxiliary for `cor:conf-fixed-model`
(conference.tex). -/
theorem const_isBigO_lg_pow (c : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (fun _ : ℕ => c) =O[atTop] (fun T => lg T ^ k) :=
  (const_isBigO_lg c).trans (lg_isBigO_lg_pow hk)

/-- The Taylor degree `m = ⌈8(P + κ + 3H + 7)⌉` used at working precision `P`: the degree of
`eq:conf-features` (conference.tex) at precision `P + κ`, where `κ` counts the fixed bits needed
to rescale values, and `H` is the fixed Taylor parameter.  For integer arguments the ceiling is
exact. -/
def taylorDegree (κ H P : ℕ) : ℕ := 8 * (P + κ + 3 * H + 7)

/-- Paper: proof of `cor:conf-fixed-model` (conference.tex): if the
working precision is `O(log(T+2))`, so is the Taylor degree `m = ⌈8(P + κ + 3H + 7)⌉`. -/
theorem taylorDegree_isBigO (κ H : ℕ) (P : ℕ → ℕ) (hP : (fun T => (P T : ℝ)) =O[atTop] lg) :
    (fun T => (taylorDegree κ H (P T) : ℝ)) =O[atTop] lg :=
  ((hP.const_mul_left 8).add (const_isBigO_lg (8 * ((κ : ℝ) + 3 * H + 7)))).congr
    (fun T => by simp only [taylorDegree]; push_cast; ring) (fun _ => rfl)

/-- Auxiliary for `cor:conf-fixed-model` (conference.tex): for fixed
`C_r, b, n, D, V` and `P, m = O(log(T+2))`, the integer length
`L = C_r{m[P + b + log(n+m+D+V+2)] + log(T+2) + 1}` of `eq:conf-explicit` is
`O(log²(T+2))`. -/
theorem integerLength_isBigO (Cr b n D V : ℝ) (hn : 0 ≤ n) (hD : 0 ≤ D) (hV : 0 ≤ V)
    (m P : ℕ → ℕ) (hm : (fun T => (m T : ℝ)) =O[atTop] lg)
    (hP : (fun T => (P T : ℝ)) =O[atTop] lg) :
    (fun T => Cr * ((m T : ℝ) * ((P T : ℝ) + b + Real.log (n + m T + D + V + 2)) + lg T + 1))
      =O[atTop] (fun T => lg T ^ 2) := by
  have hlog : (fun T => Real.log (n + m T + D + V + 2)) =O[atTop] lg := by
    have h1 : (fun T => Real.log (n + m T + D + V + 2)) =O[atTop]
        (fun T => (n + D + V + 2) + (m T : ℝ)) := by
      refine IsBigO.of_bound 1 (Eventually.of_forall fun T => ?_)
      have hmT : (0 : ℝ) ≤ m T := Nat.cast_nonneg _
      have hx : (1 : ℝ) ≤ n + m T + D + V + 2 := by linarith
      rw [Real.norm_of_nonneg (Real.log_nonneg hx), one_mul,
        Real.norm_of_nonneg (by linarith)]
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < n + m T + D + V + 2)
      linarith
    exact h1.trans ((const_isBigO_lg _).add hm)
  have hinner : (fun T => (P T : ℝ) + b + Real.log (n + m T + D + V + 2)) =O[atTop] lg :=
    (hP.add (const_isBigO_lg b)).add hlog
  have hprod : (fun T => (m T : ℝ) * ((P T : ℝ) + b + Real.log (n + m T + D + V + 2)))
      =O[atTop] (fun T => lg T ^ 2) :=
    (hm.mul hinner).congr (fun _ => rfl) (fun T => (sq (lg T)).symm)
  have hsum := (hprod.add (lg_isBigO_lg_pow (k := 2) (by norm_num))).add
    (const_isBigO_lg_pow 1 (k := 2) (by norm_num))
  exact hsum.const_mul_left Cr

/-- Auxiliary for `cor:conf-fixed-model` (conference.tex): with
`m = O(log(T+2))` and `L = O(log²(T+2))`, the explicit per-token bound
`C_r(D+1)(n+V+1)²(m+1)^(2r+4) L⁴` of `eq:conf-explicit` is `O(log^(2r+12)(T+2))`; full version
`eq:momentexplicitcost` (attention_moment_decoder.tex). -/
theorem explicitCost_isBigO (Cr D n V : ℝ) (r : ℕ) (m : ℕ → ℕ) (L : ℕ → ℝ)
    (hm : (fun T => (m T : ℝ)) =O[atTop] lg) (hL : L =O[atTop] (fun T => lg T ^ 2)) :
    (fun T => Cr * (D + 1) * (n + V + 1) ^ 2 * ((m T : ℝ) + 1) ^ (2 * r + 4) * L T ^ 4)
      =O[atTop] (fun T => lg T ^ (2 * r + 12)) := by
  have hm1 : (fun T => (m T : ℝ) + 1) =O[atTop] lg := hm.add one_isBigO_lg
  have h := ((hm1.pow (2 * r + 4)).mul (hL.pow 4)).const_mul_left
    (Cr * (D + 1) * (n + V + 1) ^ 2)
  exact h.congr (fun T => by ring) (fun T => by ring)

/-- Paper: proof of `cor:conf-fixed-model` (conference.tex),
deterministic part: for fixed parameters and working precision `P = O(log(T+2))`, the Taylor
degree `m = ⌈8(P + κ + 3H + 7)⌉` and the integer length give
`eq:conf-explicit = O(log^(2r+12)(T+2))`; full version `cor:fixedmodelcontext`
(attention_moment_decoder.tex). -/
theorem fixedModel_cost_isBigO (Cr b n D V : ℝ) (hn : 0 ≤ n) (hD : 0 ≤ D) (hV : 0 ≤ V)
    (r κ H : ℕ) (P : ℕ → ℕ) (hP : (fun T => (P T : ℝ)) =O[atTop] lg) :
    (fun T => Cr * (D + 1) * (n + V + 1) ^ 2 * ((taylorDegree κ H (P T) : ℝ) + 1) ^ (2 * r + 4) *
        (Cr * ((taylorDegree κ H (P T) : ℝ) * ((P T : ℝ) + b +
          Real.log (n + taylorDegree κ H (P T) + D + V + 2)) + lg T + 1)) ^ 4)
      =O[atTop] (fun T => lg T ^ (2 * r + 12)) :=
  explicitCost_isBigO Cr D n V r (fun T => taylorDegree κ H (P T)) _
    (taylorDegree_isBigO κ H P hP)
    (integerLength_isBigO Cr b n D V hn hD hV _ P (taylorDegree_isBigO κ H P hP) hP)

/-- Paper: `cor:conf-fixed-model` (conference.tex), polynomial form
needed to apply `lem:conf-replay`: if `u ≥ 1`, `m ≤ c u`, `P ≤ c u` and `log(T+2) ≤ u`, then the
integer length satisfies `L ≤ c' u²` and the explicit bound `eq:conf-explicit` is at most
`A u^(2r+12)` with `A` depending only on the fixed parameters.  Here `u` plays the role of
`p + log(T+2)` in `lem:conf-replay`. -/
theorem explicitCost_le_pow (Cr b n D V c : ℝ) (r : ℕ) (hCr : 0 ≤ Cr) (hb : 0 ≤ b)
    (hn : 0 ≤ n) (hD : 0 ≤ D) (hV : 0 ≤ V) (hc : 0 ≤ c) {u m P lT : ℝ} (hu : 1 ≤ u)
    (hm0 : 0 ≤ m) (hm : m ≤ c * u) (hP0 : 0 ≤ P) (hP : P ≤ c * u) (hlT0 : 0 ≤ lT)
    (hlT : lT ≤ u) :
    let L := Cr * (m * (P + b + Real.log (n + m + D + V + 2)) + lT + 1)
    0 ≤ L ∧ L ≤ Cr * (c * (2 * c + b + n + D + V + 1) + 2) * u ^ 2 ∧
      Cr * (D + 1) * (n + V + 1) ^ 2 * (m + 1) ^ (2 * r + 4) * L ^ 4 ≤
        Cr * (D + 1) * (n + V + 1) ^ 2 * (c + 1) ^ (2 * r + 4) *
          (Cr * (c * (2 * c + b + n + D + V + 1) + 2)) ^ 4 * u ^ (2 * r + 12) := by
  intro L
  have hu0 : 0 ≤ u := by linarith
  have hx : (1 : ℝ) ≤ n + m + D + V + 2 := by linarith
  have hlog0 : 0 ≤ Real.log (n + m + D + V + 2) := Real.log_nonneg hx
  have hlog : Real.log (n + m + D + V + 2) ≤ (n + D + V + 1 + c) * u := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < n + m + D + V + 2)
    nlinarith
  have hbu : b ≤ b * u := by nlinarith
  have hinner0 : 0 ≤ P + b + Real.log (n + m + D + V + 2) := by positivity
  have hinner : P + b + Real.log (n + m + D + V + 2) ≤ (2 * c + b + n + D + V + 1) * u := by
    nlinarith
  have hmi : m * (P + b + Real.log (n + m + D + V + 2)) ≤
      c * (2 * c + b + n + D + V + 1) * u ^ 2 := by
    calc m * (P + b + Real.log (n + m + D + V + 2))
        ≤ (c * u) * ((2 * c + b + n + D + V + 1) * u) :=
          mul_le_mul hm hinner hinner0 (by positivity)
      _ = c * (2 * c + b + n + D + V + 1) * u ^ 2 := by ring
  have hu2 : u ≤ u ^ 2 := by nlinarith
  have hL : L ≤ Cr * (c * (2 * c + b + n + D + V + 1) + 2) * u ^ 2 := by
    have : m * (P + b + Real.log (n + m + D + V + 2)) + lT + 1 ≤
        (c * (2 * c + b + n + D + V + 1) + 2) * u ^ 2 := by nlinarith
    calc L = Cr * (m * (P + b + Real.log (n + m + D + V + 2)) + lT + 1) := rfl
      _ ≤ Cr * ((c * (2 * c + b + n + D + V + 1) + 2) * u ^ 2) := by gcongr
      _ = Cr * (c * (2 * c + b + n + D + V + 1) + 2) * u ^ 2 := by ring
  have hL0 : 0 ≤ L := mul_nonneg hCr (by positivity)
  refine ⟨hL0, hL, ?_⟩
  have hm1 : m + 1 ≤ (c + 1) * u := by nlinarith
  calc Cr * (D + 1) * (n + V + 1) ^ 2 * (m + 1) ^ (2 * r + 4) * L ^ 4
      ≤ Cr * (D + 1) * (n + V + 1) ^ 2 * ((c + 1) * u) ^ (2 * r + 4) *
          (Cr * (c * (2 * c + b + n + D + V + 1) + 2) * u ^ 2) ^ 4 := by
        gcongr
    _ = Cr * (D + 1) * (n + V + 1) ^ 2 * (c + 1) ^ (2 * r + 4) *
          (Cr * (c * (2 * c + b + n + D + V + 1) + 2)) ^ 4 * u ^ (2 * r + 12) := by
        rw [mul_pow, mul_pow, ← pow_mul,
          show u ^ (2 * r + 12) = u ^ (2 * r + 4) * u ^ (2 * 4) by rw [← pow_add]]
        generalize Cr * (D + 1) * (n + V + 1) ^ 2 = K0
        generalize (c + 1) ^ (2 * r + 4) = α
        generalize (Cr * (c * (2 * c + b + n + D + V + 1) + 2)) ^ 4 = β
        generalize u ^ (2 * r + 4) = γ
        ring

/-- The constant `c = 8(1 + G₀ + κ + 3H + 7)` with `m, P ≤ c u` for `u = p + log(T+2)`,
`p ≥ 1`. -/
def fixedC (κ H G₀ : ℕ) : ℝ := 8 * (1 + G₀ + κ + 3 * H + 7)

/-- The deterministic per-token cost bound `eq:conf-explicit` (conference.tex) of a fixed model at
routine accuracy `p` and context length `T`: working precision `P = p + G₀`, Taylor degree
`m = taylorDegree κ H P`, and integer length `L = C_r{m[P + b + log(n+m+D+V+2)] + log(T+2) + 1}`;
the value is `C_r(D+1)(n+V+1)²(m+1)^(2r+4) L⁴`. -/
noncomputable def fixedCost (Cr b n D V : ℝ) (r κ H G₀ p T : ℕ) : ℝ :=
  Cr * (D + 1) * (n + V + 1) ^ 2 * ((taylorDegree κ H (p + G₀) : ℝ) + 1) ^ (2 * r + 4) *
    (Cr * ((taylorDegree κ H (p + G₀) : ℝ) * (((p + G₀ : ℕ) : ℝ) + b +
      Real.log (n + (taylorDegree κ H (p + G₀) : ℝ) + D + V + 2)) + lg T + 1)) ^ 4

/-- The coefficient `A` of `fixedCost_le_pow`; it depends only on the fixed model. -/
noncomputable def fixedCostCoeff (Cr b n D V : ℝ) (r κ H G₀ : ℕ) : ℝ :=
  Cr * (D + 1) * (n + V + 1) ^ 2 * (fixedC κ H G₀ + 1) ^ (2 * r + 4) *
    (Cr * (fixedC κ H G₀ * (2 * fixedC κ H G₀ + b + n + D + V + 1) + 2)) ^ 4

/-- Paper: `cor:conf-fixed-model` (conference.tex): for a fixed model and
`p ≥ 1`, the deterministic cost `eq:conf-explicit` satisfies
`fixedCost p T ≤ A (p + log(T+2))^(2r+12)`, which is the hypothesis `G(u) ≤ A u^k` of
`lem:conf-replay` with `u = p + log(T+2)` and `k = 2r + 12`. -/
theorem fixedCost_le_pow (Cr b n D V : ℝ) (hCr : 0 ≤ Cr) (hb : 0 ≤ b) (hn : 0 ≤ n)
    (hD : 0 ≤ D) (hV : 0 ≤ V) (r κ H G₀ p T : ℕ) (hp : 1 ≤ p) :
    fixedCost Cr b n D V r κ H G₀ p T ≤
      fixedCostCoeff Cr b n D V r κ H G₀ * ((p : ℝ) + lg T) ^ (2 * r + 12) := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hlg := lg_pos T
  set u : ℝ := (p : ℝ) + lg T with hu_def
  have hu : 1 ≤ u := by linarith
  have hc0 : 0 ≤ fixedC κ H G₀ := by unfold fixedC; positivity
  have hm : ((taylorDegree κ H (p + G₀) : ℕ) : ℝ) ≤ fixedC κ H G₀ * u := by
    have h1 : ((taylorDegree κ H (p + G₀) : ℕ) : ℝ) ≤ fixedC κ H G₀ * p := by
      simp only [taylorDegree, fixedC]
      push_cast
      have : (0 : ℝ) ≤ (G₀ : ℝ) + κ + 3 * H + 7 := by positivity
      nlinarith
    calc ((taylorDegree κ H (p + G₀) : ℕ) : ℝ) ≤ fixedC κ H G₀ * p := h1
      _ ≤ fixedC κ H G₀ * u := mul_le_mul_of_nonneg_left (by linarith) hc0
  have hP : ((p + G₀ : ℕ) : ℝ) ≤ fixedC κ H G₀ * u := by
    have h1 : ((p + G₀ : ℕ) : ℝ) ≤ fixedC κ H G₀ * p := by
      simp only [fixedC]
      push_cast
      have : (0 : ℝ) ≤ (G₀ : ℝ) + κ + 3 * H + 7 := by positivity
      nlinarith
    calc ((p + G₀ : ℕ) : ℝ) ≤ fixedC κ H G₀ * p := h1
      _ ≤ fixedC κ H G₀ * u := mul_le_mul_of_nonneg_left (by linarith) hc0
  obtain ⟨-, -, h3⟩ := explicitCost_le_pow Cr b n D V (fixedC κ H G₀) r hCr hb hn hD hV hc0 hu
    (Nat.cast_nonneg _) hm (Nat.cast_nonneg _) hP hlg.le (by linarith)
  exact h3

/-- `S = 1 + log(V+2) + log(T+2)` of `lem:conf-replay` (conference.tex). -/
noncomputable def replayS (V : ℝ) (T : ℕ) : ℝ := 1 + Real.log (V + 2) + lg T

/-- Auxiliary for `cor:conf-fixed-model` (conference.tex): for a fixed
vocabulary size `V`, `S = 1 + log(V+2) + log(T+2)` is `O(log(T+2))`, so a nonnegative quantity
bounded by `C(A S^k + S)` with `k ≥ 1` is `O(log^k(T+2))`.  This is arithmetic only; the
exponent `k` is an input here. -/
theorem isBigO_of_le_replay_bound (A C V : ℝ) {k : ℕ} (hk : 1 ≤ k) (E : ℕ → ℝ)
    (hE0 : ∀ T, 0 ≤ E T) (hE : ∀ T, E T ≤ C * (A * replayS V T ^ k + replayS V T)) :
    E =O[atTop] (fun T => lg T ^ k) := by
  have hS : replayS V =O[atTop] lg :=
    ((const_isBigO_lg (1 + Real.log (V + 2))).add (isBigO_refl lg atTop)).congr
      (fun _ => rfl) (fun _ => rfl)
  have hbound : (fun T => C * (A * replayS V T ^ k + replayS V T)) =O[atTop]
      (fun T => lg T ^ k) :=
    (((hS.pow k).const_mul_left A).add (hS.trans (lg_isBigO_lg_pow hk))).const_mul_left C
  refine IsBigO.trans ?_ hbound
  refine IsBigO.of_bound 1 (Eventually.of_forall fun T => ?_)
  rw [one_mul, Real.norm_of_nonneg (hE0 T)]
  exact (hE T).trans (le_abs_self _)

/-- Paper: `cor:conf-fixed-model` (conference.tex, "A fixed finite model"), via
`eq:conf-explicit` and `lem:conf-replay`; full version `cor:fixedmodelcontext`
(attention_moment_decoder.tex).  For a fixed model, the expected per-token cost `E(T)` of the
exact sampler is `O(log^(2r+12)(T+2))`.

The hypothesis `hreplay` is the stand-in for `lem:conf-replay`: for every cost function `G`
with `G(u) ≤ A u^k` for `u ≥ 1`, if the deterministic evaluator at accuracy `p ≥ 1` and context
length `T` costs at most `G(p + log(T+2))` per (re)played token, then
`E(T) ≤ C_k (A S^k + S)`.  The proof supplies `G(u) = A u^(2r+12)` from `fixedCost_le_pow`, so
the exponent `2r + 12` is derived from `eq:conf-explicit`, not assumed. -/
theorem fixedModel_expected_isBigO (Cr b n D V : ℝ) (hCr : 0 ≤ Cr) (hb : 0 ≤ b) (hn : 0 ≤ n)
    (hD : 0 ≤ D) (hV : 0 ≤ V) (r κ H G₀ : ℕ) (E : ℕ → ℝ) (Crep : ℕ → ℝ)
    (hE0 : ∀ T, 0 ≤ E T)
    (hreplay : ∀ (G : ℝ → ℝ) (A : ℝ) (k : ℕ), (∀ u, 1 ≤ u → G u ≤ A * u ^ k) →
      (∀ p T, 1 ≤ p → fixedCost Cr b n D V r κ H G₀ p T ≤ G ((p : ℝ) + lg T)) →
      ∀ T, E T ≤ Crep k * (A * replayS V T ^ k + replayS V T)) :
    E =O[atTop] (fun T => lg T ^ (2 * r + 12)) := by
  have hE := hreplay (fun u => fixedCostCoeff Cr b n D V r κ H G₀ * u ^ (2 * r + 12))
    (fixedCostCoeff Cr b n D V r κ H G₀) (2 * r + 12) (fun _ _ => le_rfl)
    (fun p T hp => fixedCost_le_pow Cr b n D V hCr hb hn hD hV r κ H G₀ p T hp)
  exact isBigO_of_le_replay_bound _ _ V (by omega) E hE0 hE

end ExactSampling.FixedModel
