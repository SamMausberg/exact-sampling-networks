import Mathlib

/-!
# A finite moment evaluator with certified error

This module formalizes the mathematical content of the proof of `lem:conf-moments`
(conference.tex, section `sec:conf-moments`, equation `eq:conf-features`).  The same lemma
appears in the full version as `lem:finitemomentindex` (attention_moment_decoder.tex), with the
Taylor estimate `eq:momenttaylorerror`, and is summarized after `thm:main-decoder`
(main_normalization.tex).  It is the attention evaluator used in the proof of
`thm:conf-decoder`.

Formalized:
* the Taylor tail bound for the exponential, the factorial inequality `N! ≥ (N/e)^N`, and the
  complete chain `sup_{|x| ≤ H} |e^x - E_m(x)| ≤ e^H H^(m+1)/(m+1)! ≤ 2^(2H-m-1) ≤ 2^(-q)` with
  `q = p + 2H + 6` and `m = ⌈8(p+3H+7)⌉`, including the side conditions `m + 1 ≥ 8H` and `e < 4`;
* the multinomial identity `E_m(⟨t,z⟩) = ∑_{|ν| ≤ m} t^ν z^ν / ν!` over `Fin r`;
* the count `N_m = binom(m+r, r)` of multi-indices and the count `(a+1) N_m` of counters;
* exactness of the moment counters under append, and equality of the counter evaluator with the
  direct truncated sums at every context length `T`;
* the counters are integers over the denominator `2^(P(m+1))` when the records lie on the grid
  `2^(-P)`, with stored sums bounded by `T` in absolute value;
* the ratio error `|Ñ/Z̃ - N/Z| ≤ 2δ/(Z-δ) ≤ 4δe^H ≤ 2^(-p-4)`, positivity of the truncated
  denominator and the lower bound `Z̃ ≥ e^(-H)/2`, assembled into a theorem about the counter
  evaluator of an actual record list;
* the final enclosure width: a division interval of width `2^(-p-2)` enlarged by the Taylor error
  has width less than `2^(-p)`;
* the denominator claim `d_t^m m!` (via `ν! ∣ m!`), the parity split `A + B/√n` with rational
  `A, B` for `t_i = c_i/√n`, and its common denominator `d_c^m n^⌊m/2⌋ m!`.

Not formalized: the bit-length and operation-count accounting, the certified rational division
and square-root bisection algorithms, and the interval arithmetic implementation itself.  The
numerator magnitude bound `2^(P(m+1)) T` is proved; its translation into bit lengths is not.
-/

namespace ExactSampling.Moments

open Finset

/-! ## Taylor truncation of the exponential -/

/-- The truncated exponential `E_m(x) = ∑_{d=0}^m x^d/d!`. -/
noncomputable def expTrunc (m : ℕ) (x : ℝ) : ℝ :=
  ∑ d ∈ range (m + 1), x ^ d / (d.factorial : ℝ)

/-- Taylor tail of the complex exponential: `‖e^x - ∑_{k<n} x^k/k!‖ ≤ ‖x‖^n/n! · e^‖x‖`.
Auxiliary step for the Taylor estimate in the proof of `lem:conf-moments` (conference.tex). -/
theorem complex_exp_tail_le (x : ℂ) (n : ℕ) :
    ‖Complex.exp x - ∑ m ∈ range n, x ^ m / m.factorial‖ ≤
      ‖x‖ ^ n / n.factorial * Real.exp ‖x‖ := by
  rw [← CauSeq.lim_const (abv := norm) (∑ m ∈ range n, _), Complex.exp, sub_eq_add_neg,
    ← CauSeq.lim_neg, CauSeq.lim_add, ← Complex.lim_norm]
  refine CauSeq.lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  change ‖(∑ m ∈ range j, x ^ m / m.factorial) - ∑ m ∈ range n, x ^ m / m.factorial‖ ≤ _
  rw [← sum_Ico_eq_sub _ hj]
  calc
    ‖∑ m ∈ Ico n j, (x ^ m / m.factorial : ℂ)‖
        ≤ ∑ m ∈ Ico n j, ‖(x ^ m / m.factorial : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Ico n j, ‖x‖ ^ n / n.factorial * (‖x‖ ^ (m - n) / (m - n).factorial) := by
      gcongr with i hi
      rw [mem_Ico] at hi
      rw [norm_div, norm_pow, Complex.norm_natCast]
      have hfac : ((n.factorial : ℝ) * (i - n).factorial) ≤ i.factorial := by
        have := Nat.factorial_mul_factorial_dvd_factorial hi.1
        exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) this
      have hpos1 : (0 : ℝ) < n.factorial := by positivity
      have hpos2 : (0 : ℝ) < (i - n).factorial := by positivity
      rw [div_mul_div_comm, ← pow_add, Nat.add_sub_cancel' hi.1]
      gcongr
    _ = ‖x‖ ^ n / n.factorial * ∑ m ∈ range (j - n), ‖x‖ ^ m / m.factorial := by
      rw [mul_sum, sum_Ico_eq_sum_range]
      simp
    _ ≤ ‖x‖ ^ n / n.factorial * Real.exp ‖x‖ := by
      gcongr
      exact Real.sum_le_exp_of_nonneg (norm_nonneg _) _

/-- The remainder estimate `|e^x - E_m(x)| ≤ e^|x| |x|^(m+1)/(m+1)!` used in the proof of
`lem:conf-moments` (conference.tex); `eq:momenttaylorerror` in attention_moment_decoder.tex. -/
theorem exp_sub_expTrunc_le (m : ℕ) (x : ℝ) :
    |Real.exp x - expTrunc m x| ≤ Real.exp |x| * |x| ^ (m + 1) / (m + 1).factorial := by
  have h := complex_exp_tail_le (x : ℂ) (m + 1)
  have h2 : (Complex.exp (x : ℂ) - ∑ k ∈ range (m + 1), (x : ℂ) ^ k / k.factorial) =
      ((Real.exp x - ∑ k ∈ range (m + 1), x ^ k / k.factorial : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [h2, Complex.norm_real, Complex.norm_real] at h
  rw [expTrunc]
  have h3 : Real.exp |x| * |x| ^ (m + 1) / ((m + 1).factorial : ℝ) =
      |x| ^ (m + 1) / ((m + 1).factorial : ℝ) * Real.exp |x| := by ring
  rw [h3]
  simpa [Real.norm_eq_abs] using h

/-- The factorial inequality `N! ≥ (N/e)^N` used in the proof of `lem:conf-moments`
(conference.tex). -/
theorem pow_div_exp_one_le_factorial (N : ℕ) :
    ((N : ℝ) / Real.exp 1) ^ N ≤ N.factorial := by
  have h := Real.pow_div_factorial_le_exp (x := (N : ℝ)) (Nat.cast_nonneg N) N
  have hf : (0 : ℝ) < N.factorial := by positivity
  rw [div_pow, Real.exp_one_pow, div_le_iff₀ (Real.exp_pos _)]
  rw [div_le_iff₀ hf] at h
  linarith

/-- `e < 4`, the numerical fact used in the proof of `lem:conf-moments` (conference.tex). -/
theorem exp_one_lt_four : Real.exp 1 < 4 := by
  have := Real.exp_one_lt_d9
  linarith

/-- `e^H ≤ 4^H = 2^(2H)` for natural `H`. Auxiliary step for `lem:conf-moments`
(conference.tex). -/
theorem exp_nat_le_four_pow (H : ℕ) : Real.exp (H : ℝ) ≤ (4 : ℝ) ^ H := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le exp_one_lt_four.le H

/-- The middle step of the Taylor chain in the proof of `lem:conf-moments` (conference.tex):
if `m + 1 ≥ 8H` then `e^H H^(m+1)/(m+1)! ≤ 2^(2H-m-1)`.  The proof uses `N! ≥ (N/e)^N` and
`e < 4`, as in the paper. -/
theorem exp_mul_pow_div_factorial_le (H m : ℕ) (hm : 8 * H ≤ m + 1) :
    Real.exp H * (H : ℝ) ^ (m + 1) / (m + 1).factorial ≤
      (2 : ℝ) ^ (2 * (H : ℤ) - m - 1) := by
  set N := m + 1 with hN
  have hNpos : (0 : ℝ) < N := by positivity
  have he := Real.exp_pos 1
  have he4 := exp_one_lt_four
  have hfac := pow_div_exp_one_le_factorial N
  have hNe : (0 : ℝ) < ((N : ℝ) / Real.exp 1) ^ N := by positivity
  -- `H^N / N! ≤ (eH/N)^N ≤ (1/2)^N`
  have h1 : (H : ℝ) ^ N / N.factorial ≤ (1 / 2 : ℝ) ^ N := by
    calc (H : ℝ) ^ N / N.factorial ≤ (H : ℝ) ^ N / ((N : ℝ) / Real.exp 1) ^ N := by
          gcongr
      _ = (Real.exp 1 * H / N) ^ N := by
          rw [← div_pow]; congr 1; field_simp
      _ ≤ (1 / 2 : ℝ) ^ N := by
          apply pow_le_pow_left₀ (by positivity)
          rw [div_le_iff₀ hNpos]
          have hH8 : (8 : ℝ) * H ≤ N := by exact_mod_cast hm
          have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
          nlinarith
  have h2 : (2 : ℝ) ^ (2 * (H : ℤ) - m - 1) = (4 : ℝ) ^ H * (1 / 2 : ℝ) ^ N := by
    rw [show 2 * (H : ℤ) - m - 1 = ((2 * H : ℕ) : ℤ) - ((N : ℕ) : ℤ) by
      rw [hN]; push_cast; ring]
    rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast, pow_mul, one_div, inv_pow]
    norm_num
    rw [div_eq_mul_inv]
  rw [h2, mul_div_assoc]
  exact mul_le_mul (exp_nat_le_four_pow H) h1 (by positivity) (by positivity)

/-- The precision `q = p + 2H + 6` of the proof of `lem:conf-moments` (conference.tex). -/
def precQ (p H : ℕ) : ℕ := p + 2 * H + 6

/-- The Taylor degree `m = ⌈8(p+3H+7)⌉` of `eq:conf-features` (conference.tex).  For integer
`p, H` the ceiling is exact; see `momentDegree_eq_ceil`. -/
def momentDegree (p H : ℕ) : ℕ := 8 * (p + 3 * H + 7)

/-- The defining ceiling of `eq:conf-features` (conference.tex) agrees with `momentDegree`. -/
theorem momentDegree_eq_ceil (p H : ℕ) :
    momentDegree p H = ⌈(8 : ℝ) * ((p : ℝ) + 3 * H + 7)⌉₊ := by
  rw [momentDegree]
  have : (8 : ℝ) * ((p : ℝ) + 3 * H + 7) = ((8 * (p + 3 * H + 7) : ℕ) : ℝ) := by push_cast; ring
  rw [this, Nat.ceil_natCast]

/-- The side condition `m + 1 ≥ 8H` in the proof of `lem:conf-moments` (conference.tex). -/
theorem eight_mul_le_momentDegree_succ (p H : ℕ) : 8 * H ≤ momentDegree p H + 1 := by
  unfold momentDegree; omega

/-- The final exponent comparison `2^(2H-m-1) ≤ 2^(-q)` in the proof of `lem:conf-moments`
(conference.tex), valid because `m + 1 ≥ 2H + q`. -/
theorem two_zpow_le_two_zpow_neg_q (p H : ℕ) :
    (2 : ℝ) ^ (2 * (H : ℤ) - momentDegree p H - 1) ≤ (2 : ℝ) ^ (-(precQ p H : ℤ)) := by
  apply zpow_le_zpow_right₀ (by norm_num)
  unfold momentDegree precQ
  push_cast
  omega

/-- Paper: `lem:conf-moments` (conference.tex), the displayed Taylor chain
`sup_{|x| ≤ H} |e^x - E_m(x)| ≤ e^H H^(m+1)/(m+1)! ≤ 2^(2H-m-1) ≤ 2^(-q)`, with
`q = p + 2H + 6` and `m = ⌈8(p+3H+7)⌉`; full version `eq:momenttaylorerror`
(attention_moment_decoder.tex).  All three inequalities are stated. -/
theorem taylor_chain (p H : ℕ) {x : ℝ} (hx : |x| ≤ H) :
    |Real.exp x - expTrunc (momentDegree p H) x| ≤
        Real.exp H * (H : ℝ) ^ (momentDegree p H + 1) / (momentDegree p H + 1).factorial ∧
      Real.exp H * (H : ℝ) ^ (momentDegree p H + 1) / (momentDegree p H + 1).factorial ≤
        (2 : ℝ) ^ (2 * (H : ℤ) - momentDegree p H - 1) ∧
      (2 : ℝ) ^ (2 * (H : ℤ) - momentDegree p H - 1) ≤ (2 : ℝ) ^ (-(precQ p H : ℤ)) := by
  refine ⟨?_, exp_mul_pow_div_factorial_le H _ (eight_mul_le_momentDegree_succ p H),
    two_zpow_le_two_zpow_neg_q p H⟩
  refine (exp_sub_expTrunc_le _ x).trans ?_
  gcongr

/-- Paper: `lem:conf-moments` (conference.tex), the uniform Taylor error
`sup_{|x| ≤ H} |e^x - E_m(x)| ≤ 2^(-q)`; full version `eq:momenttaylorerror`
(attention_moment_decoder.tex). -/
theorem taylor_sup_error (p H : ℕ) {x : ℝ} (hx : |x| ≤ H) :
    |Real.exp x - expTrunc (momentDegree p H) x| ≤ (2 : ℝ) ^ (-(precQ p H : ℤ)) := by
  obtain ⟨h1, h2, h3⟩ := taylor_chain p H hx
  exact h1.trans (h2.trans h3)

/-! ## Multi-indices and the multinomial identity -/

/-- The multi-indices `ν ∈ ℕ^r` with `|ν| ≤ m`. -/
def multiIdx (r m : ℕ) : Finset (Fin r → ℕ) :=
  (range (m + 1)).biUnion fun d => piAntidiag univ d

/-- Membership in `multiIdx r m` is `|ν| ≤ m`.  Auxiliary for `lem:conf-moments`
(conference.tex). -/
theorem mem_multiIdx {r m : ℕ} {ν : Fin r → ℕ} : ν ∈ multiIdx r m ↔ ∑ i, ν i ≤ m := by
  simp [multiIdx, mem_piAntidiag]

/-- The monomial `t^ν = ∏ t_i^ν_i`. -/
def mono {r : ℕ} (ν : Fin r → ℕ) (t : Fin r → ℝ) : ℝ := ∏ i, t i ^ ν i

/-- The multi-factorial `ν! = ∏ ν_i!`. -/
def mfact {r : ℕ} (ν : Fin r → ℕ) : ℕ := ∏ i, (ν i).factorial

/-- `ν! > 0`.  Auxiliary for `lem:conf-moments` (conference.tex). -/
theorem mfact_pos {r : ℕ} (ν : Fin r → ℕ) : 0 < mfact ν :=
  prod_pos fun _ _ => Nat.factorial_pos _

/-- The inner product `⟨t, z⟩`. -/
def dotp {r : ℕ} (t z : Fin r → ℝ) : ℝ := ∑ i, t i * z i

/-- One homogeneous degree of the multinomial identity: `⟨t,z⟩^d/d! = ∑_{|ν|=d} t^ν z^ν/ν!`.
Auxiliary step for `lem:conf-moments` (conference.tex). -/
theorem dotp_pow_div_factorial (r d : ℕ) (t z : Fin r → ℝ) :
    dotp t z ^ d / d.factorial =
      ∑ ν ∈ piAntidiag (univ : Finset (Fin r)) d, mono ν t * mono ν z / mfact ν := by
  rw [dotp, sum_pow_eq_sum_piAntidiag, sum_div]
  apply sum_congr rfl
  intro ν hν
  have hs : ∑ i, ν i = d := (mem_piAntidiag.1 hν).1
  have spec := Nat.multinomial_spec (univ : Finset (Fin r)) ν
  rw [hs] at spec
  have hd : (d.factorial : ℝ) = (mfact ν : ℝ) * (Nat.multinomial univ ν : ℝ) := by
    simp only [mfact]; exact_mod_cast spec.symm
  have hmn : (0 : ℝ) < Nat.multinomial univ ν := by exact_mod_cast Nat.multinomial_pos _ _
  have hmf : (0 : ℝ) < mfact ν := by exact_mod_cast mfact_pos ν
  rw [hd]
  have hprod : ∏ i, (t i * z i) ^ ν i = mono ν t * mono ν z := by
    simp only [mono, mul_pow, prod_mul_distrib]
  rw [hprod]
  field_simp

/-- Paper: `lem:conf-moments` (conference.tex), the multinomial identity
`E_m(⟨t,z⟩) = ∑_{|ν| ≤ m} t^ν z^ν / ν!`; also in the proof of `lem:finitemomentindex`
(attention_moment_decoder.tex). -/
theorem expTrunc_dotp_eq (r m : ℕ) (t z : Fin r → ℝ) :
    expTrunc m (dotp t z) = ∑ ν ∈ multiIdx r m, mono ν t * mono ν z / mfact ν := by
  rw [expTrunc, multiIdx, sum_biUnion]
  · exact sum_congr rfl fun d _ => dotp_pow_div_factorial r d t z
  · intro d₁ _ d₂ _ hne
    rw [Function.onFun, disjoint_left]
    intro ν h1 h2
    rw [mem_piAntidiag] at h1 h2
    exact hne (h1.1.symm.trans h2.1)

/-! ## The feature count `N_m = binom(m+r, r)` -/

/-- The number of `ν ∈ ℕ^r` with `|ν| = d` is `binom(r+d-1, d)`.  Auxiliary for the feature
count in `eq:conf-features` (conference.tex). -/
theorem card_piAntidiag_univ (r d : ℕ) :
    #(piAntidiag (univ : Finset (Fin r)) d) = (r + d - 1).choose d := by
  have h : #((univ : Finset (Fin r)).finsuppAntidiag d) =
      #(piAntidiag (univ : Finset (Fin r)) d) := by
    rw [finsuppAntidiag, card_map, card_attach]
  rw [← h, card_finsuppAntidiag_nat_eq_choose, card_univ, Fintype.card_fin]

/-- Paper: `eq:conf-features` (conference.tex), the feature count: the number of multi-indices
`ν ∈ ℕ^r` with `|ν| ≤ m` is `N_m = binom(m+r, r)`. -/
theorem card_multiIdx (r m : ℕ) : #(multiIdx r m) = (m + r).choose r := by
  induction m with
  | zero =>
    have : multiIdx r 0 = {0} := by
      ext ν
      simp only [mem_multiIdx, Nat.le_zero, sum_eq_zero_iff, mem_univ, true_implies,
        mem_singleton]
      exact ⟨fun h => funext h, fun h i => by simp [h]⟩
    rw [this, card_singleton, zero_add, Nat.choose_self]
  | succ m ih =>
    have hsplit : multiIdx r (m + 1) =
        multiIdx r m ∪ piAntidiag (univ : Finset (Fin r)) (m + 1) := by
      ext ν
      have e : univ.sum ν = ∑ i, ν i := rfl
      simp only [mem_union, mem_multiIdx, mem_piAntidiag, mem_univ, implies_true, and_true]
      rw [e]
      omega
    have hdisj : Disjoint (multiIdx r m) (piAntidiag (univ : Finset (Fin r)) (m + 1)) := by
      rw [disjoint_left]
      intro ν h1 h2
      have e : univ.sum ν = ∑ i, ν i := rfl
      rw [mem_multiIdx] at h1
      rw [mem_piAntidiag, e] at h2
      omega
    rw [hsplit, card_union_of_disjoint hdisj, ih, card_piAntidiag_univ]
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr; simp
    · obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
      rw [show k + 1 + (m + 1) - 1 = m + 1 + k by omega,
        show m + 1 + (k + 1) = (m + 1 + k) + 1 by omega, Nat.choose_succ_succ,
        Nat.choose_symm_add, show m + (k + 1) = m + 1 + k by omega]
      ring

/-- Paper: `lem:conf-moments` (conference.tex): the index has `(a+1) N_m` counters, namely
`S_ν` and `M_{ν,i}` for `|ν| ≤ m`, `i < a`. -/
theorem card_counters (r m a : ℕ) :
    #(multiIdx r m ×ˢ (univ : Finset (Option (Fin a)))) = (a + 1) * (m + r).choose r := by
  rw [card_product, card_multiIdx, card_univ, Fintype.card_option, Fintype.card_fin, mul_comm]

/-! ## Exact moment counters -/

/-- A stored record: key coordinates `z ∈ ℝ^r` and value `v ∈ ℝ^a`. -/
structure Record (r a : ℕ) where
  /-- chart coordinates of the key -/
  z : Fin r → ℝ
  /-- value vector -/
  v : Fin a → ℝ

variable {r a : ℕ}

/-- The counter `S_ν = ∑_{j ≤ T} z_j^ν`. -/
noncomputable def momS {T : ℕ} (rec : Fin T → Record r a) (ν : Fin r → ℕ) : ℝ :=
  ∑ j, mono ν (rec j).z

/-- The counter `M_{ν,i} = ∑_{j ≤ T} z_j^ν v_{j,i}`. -/
noncomputable def momM {T : ℕ} (rec : Fin T → Record r a) (ν : Fin r → ℕ) (i : Fin a) : ℝ :=
  ∑ j, mono ν (rec j).z * (rec j).v i

/-- Paper: `lem:conf-moments` (conference.tex), exactness under insertion: appending one record
adds exactly its monomial to every counter `S_ν`. -/
theorem momS_snoc {T : ℕ} (rec : Fin T → Record r a) (x : Record r a) (ν : Fin r → ℕ) :
    momS (Fin.snoc rec x : Fin (T + 1) → Record r a) ν = momS rec ν + mono ν x.z := by
  simp [momS, Fin.sum_univ_castSucc]

/-- Paper: `lem:conf-moments` (conference.tex), exactness under insertion for the
value-weighted counters `M_{ν,i}`. -/
theorem momM_snoc {T : ℕ} (rec : Fin T → Record r a) (x : Record r a) (ν : Fin r → ℕ)
    (i : Fin a) :
    momM (Fin.snoc rec x : Fin (T + 1) → Record r a) ν i = momM rec ν i + mono ν x.z * x.v i := by
  simp [momM, Fin.sum_univ_castSucc]

/-- The truncated denominator evaluated from the counters, `∑_ν t^ν S_ν / ν!`. -/
noncomputable def denomEval {T : ℕ} (m : ℕ) (t : Fin r → ℝ) (rec : Fin T → Record r a) : ℝ :=
  ∑ ν ∈ multiIdx r m, mono ν t / mfact ν * momS rec ν

/-- The truncated numerator evaluated from the counters, `∑_ν t^ν M_{ν,i} / ν!`. -/
noncomputable def numerEval {T : ℕ} (m : ℕ) (t : Fin r → ℝ) (rec : Fin T → Record r a)
    (i : Fin a) : ℝ :=
  ∑ ν ∈ multiIdx r m, mono ν t / mfact ν * momM rec ν i

/-- Paper: `lem:conf-moments` (conference.tex): the counter evaluator equals the direct
truncated sum `∑_j E_m(⟨t, z_j⟩)` at every context length `T`. -/
theorem denomEval_eq {T : ℕ} (m : ℕ) (t : Fin r → ℝ) (rec : Fin T → Record r a) :
    denomEval m t rec = ∑ j, expTrunc m (dotp t (rec j).z) := by
  simp only [denomEval, momS, mul_sum, expTrunc_dotp_eq]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun ν _ => ?_
  ring

/-- Paper: `lem:conf-moments` (conference.tex): the counter evaluator of the numerator equals
the direct truncated sum `∑_j E_m(⟨t, z_j⟩) v_{j,i}` at every context length `T`. -/
theorem numerEval_eq {T : ℕ} (m : ℕ) (t : Fin r → ℝ) (rec : Fin T → Record r a) (i : Fin a) :
    numerEval m t rec i = ∑ j, expTrunc m (dotp t (rec j).z) * (rec j).v i := by
  simp only [numerEval, momM, mul_sum, expTrunc_dotp_eq, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun ν _ => ?_
  ring

/-- Paper: `lem:conf-moments` (conference.tex): appending a record changes the evaluated
truncated denominator by exactly the new record's truncated exponential; the index acquires no
error with age. -/
theorem denomEval_snoc {T : ℕ} (m : ℕ) (t : Fin r → ℝ) (rec : Fin T → Record r a)
    (x : Record r a) :
    denomEval m t (Fin.snoc rec x : Fin (T + 1) → Record r a) =
      denomEval m t rec + expTrunc m (dotp t x.z) := by
  simp only [denomEval, momS_snoc, mul_add, sum_add_distrib, expTrunc_dotp_eq]
  congr 1
  refine sum_congr rfl fun ν _ => ?_
  ring

/-- Paper: `lem:conf-moments` (conference.tex): the numerator analogue of `denomEval_snoc`. -/
theorem numerEval_snoc {T : ℕ} (m : ℕ) (t : Fin r → ℝ) (rec : Fin T → Record r a)
    (x : Record r a) (i : Fin a) :
    numerEval m t (Fin.snoc rec x : Fin (T + 1) → Record r a) i =
      numerEval m t rec i + expTrunc m (dotp t x.z) * x.v i := by
  simp only [numerEval, momM_snoc, mul_add, sum_add_distrib, expTrunc_dotp_eq, sum_mul]
  congr 1
  refine sum_congr rfl fun ν _ => ?_
  ring

/-! ## Integer numerators over `2^(P(m+1))` -/

/-- `y` lies on the dyadic grid `2^(-P)`: `2^P y` is an integer. -/
def OnGrid (P : ℕ) (y : ℝ) : Prop := ∃ k : ℤ, y * 2 ^ P = k

/-- A point of the grid `2^(-P)` lies on every finer grid `2^(-P')`.  Auxiliary for
`lem:conf-moments` (conference.tex). -/
theorem OnGrid.mono {P P' : ℕ} {y : ℝ} (h : OnGrid P y) (hP : P ≤ P') : OnGrid P' y := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k * 2 ^ (P' - P), ?_⟩
  rw [show P' = P + (P' - P) by omega, pow_add, ← mul_assoc, hk]
  push_cast
  rw [Nat.add_sub_cancel_left]

/-- Grid points are closed under addition.  Auxiliary for `lem:conf-moments`
(conference.tex). -/
theorem OnGrid.add {P : ℕ} {y y' : ℝ} (h : OnGrid P y) (h' : OnGrid P y') :
    OnGrid P (y + y') := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨k', hk'⟩ := h'
  exact ⟨k + k', by rw [add_mul, hk, hk']; push_cast; ring⟩

/-- Products of grid points lie on the product grid.  Auxiliary for `lem:conf-moments`
(conference.tex). -/
theorem OnGrid.mul {P P' : ℕ} {y y' : ℝ} (h : OnGrid P y) (h' : OnGrid P' y') :
    OnGrid (P + P') (y * y') := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨k', hk'⟩ := h'
  exact ⟨k * k', by rw [pow_add]; push_cast; rw [← hk, ← hk']; ring⟩

/-- `0` is a grid point.  Auxiliary for `lem:conf-moments` (conference.tex). -/
theorem OnGrid.zero (P : ℕ) : OnGrid P 0 := ⟨0, by simp⟩

/-- Finite sums of grid points are grid points.  Auxiliary for `lem:conf-moments`
(conference.tex). -/
theorem OnGrid.sum {P : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h : ∀ i ∈ s, OnGrid P (f i)) : OnGrid P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using OnGrid.zero P
  | insert i s hi ih =>
    rw [sum_insert hi]
    exact (h i (mem_insert_self i s)).add (ih fun j hj => h j (mem_insert_of_mem hj))

/-- A monomial of grid coordinates is on the grid `2^(-P|ν|)`.  Auxiliary for
`lem:conf-moments` (conference.tex). -/
theorem mono_onGrid {P : ℕ} (ν : Fin r → ℕ) (z : Fin r → ℝ) (hz : ∀ i, OnGrid P (z i)) :
    OnGrid (P * ∑ i, ν i) (mono ν z) := by
  choose k hk using hz
  refine ⟨∏ i, k i ^ ν i, ?_⟩
  rw [mono, pow_mul, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  push_cast
  refine prod_congr rfl fun i _ => ?_
  rw [← hk i, mul_pow]

/-- Paper: `lem:conf-moments` (conference.tex): for records on the grid `2^(-P)` and `|ν| ≤ m`,
the increment `z^ν` and the increment `z^ν v_i` added at an insertion are integers over
`2^(P(m+1))`. -/
theorem increment_onGrid {P m : ℕ} (x : Record r a) (hz : ∀ i, OnGrid P (x.z i))
    (hv : ∀ i, OnGrid P (x.v i)) {ν : Fin r → ℕ} (hν : ∑ i, ν i ≤ m) :
    OnGrid (P * (m + 1)) (mono ν x.z) ∧ ∀ i, OnGrid (P * (m + 1)) (mono ν x.z * x.v i) := by
  refine ⟨(mono_onGrid ν x.z hz).mono ?_, fun i => ((mono_onGrid ν x.z hz).mul (hv i)).mono ?_⟩
  · exact Nat.mul_le_mul_left P (by omega)
  · rw [show P * (m + 1) = P * m + P by ring]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left P hν) P

/-- Paper: `lem:conf-moments` (conference.tex): the counters `S_ν` and `M_{ν,i}` are integer
numerators over the single denominator `2^(P(m+1))`. -/
theorem counters_onGrid {P m T : ℕ} (rec : Fin T → Record r a)
    (hz : ∀ j i, OnGrid P ((rec j).z i)) (hv : ∀ j i, OnGrid P ((rec j).v i))
    {ν : Fin r → ℕ} (hν : ∑ i, ν i ≤ m) :
    OnGrid (P * (m + 1)) (momS rec ν) ∧ ∀ i, OnGrid (P * (m + 1)) (momM rec ν i) :=
  ⟨OnGrid.sum _ _ fun j _ => (increment_onGrid (rec j) (hz j) (hv j) hν).1,
    fun i => OnGrid.sum _ _ fun j _ => (increment_onGrid (rec j) (hz j) (hv j) hν).2 i⟩

/-- `|z^ν| ≤ 1` for `z ∈ [-1,1]^r`.  Auxiliary for `lem:conf-moments` (conference.tex). -/
theorem abs_mono_le_one {ν : Fin r → ℕ} {z : Fin r → ℝ} (hz : ∀ i, |z i| ≤ 1) :
    |mono ν z| ≤ 1 := by
  rw [mono, abs_prod]
  exact prod_le_one₀ (fun i _ => abs_nonneg _) fun i _ => by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hz i)

/-- Paper: `lem:conf-moments` (conference.tex): every stored sum has absolute value at most `T`
for records in `[-1,1]`, so each integer numerator is at most `2^(P(m+1)) T` in absolute
value. -/
theorem counters_abs_le {T : ℕ} (rec : Fin T → Record r a)
    (hz : ∀ j i, |(rec j).z i| ≤ 1) (hv : ∀ j i, |(rec j).v i| ≤ 1) (ν : Fin r → ℕ) :
    |momS rec ν| ≤ T ∧ ∀ i, |momM rec ν i| ≤ T := by
  constructor
  · calc |momS rec ν| ≤ ∑ j, |mono ν (rec j).z| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin T, (1 : ℝ) := sum_le_sum fun j _ => abs_mono_le_one (hz j)
      _ = T := by simp
  · intro i
    calc |momM rec ν i| ≤ ∑ j, |mono ν (rec j).z * (rec j).v i| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin T, (1 : ℝ) := sum_le_sum fun j _ => by
          rw [abs_mul]
          calc |mono ν (rec j).z| * |(rec j).v i| ≤ 1 * 1 :=
                mul_le_mul (abs_mono_le_one (hz j)) (hv j i) (abs_nonneg _) zero_le_one
            _ = 1 := one_mul 1
      _ = T := by simp

/-- Paper: `lem:conf-moments` (conference.tex): the integer numerator `k = 2^(P(m+1)) y` of a
stored sum with `|y| ≤ T` has magnitude at most `2^(P(m+1)) T`. -/
theorem counter_numerator_abs_le {T P m : ℕ} {y : ℝ} {k : ℤ} (hk : y * 2 ^ (P * (m + 1)) = k)
    (hy : |y| ≤ T) : |(k : ℝ)| ≤ 2 ^ (P * (m + 1)) * T := by
  have h2 : (0 : ℝ) < 2 ^ (P * (m + 1)) := by positivity
  rw [← hk, abs_mul, abs_of_pos h2, mul_comm]
  exact mul_le_mul_of_nonneg_left hy h2.le

/-! ## The ratio error -/

/-- Paper: `lem:conf-moments` (conference.tex), the first ratio inequality
`|Ñ/Z̃ - N/Z| ≤ 2δ/(Z-δ)` together with positivity of the truncated denominator; also in the
proof of `lem:finitemomentindex` (attention_moment_decoder.tex). -/
theorem ratio_error {N Z Nt Zt δ : ℝ} (hNZ : |N| ≤ Z) (hδ : 0 ≤ δ) (hδZ : δ < Z)
    (hZt : |Zt - Z| ≤ δ) (hNt : |Nt - N| ≤ δ) :
    0 < Zt ∧ |Nt / Zt - N / Z| ≤ 2 * δ / (Z - δ) := by
  have hZpos : 0 < Z := lt_of_le_of_lt hδ hδZ
  have hZt_ge : Z - δ ≤ Zt := by have := (abs_le.1 hZt).1; linarith
  have hZtpos : 0 < Zt := by linarith
  refine ⟨hZtpos, ?_⟩
  have key : Nt / Zt - N / Z = ((Nt - N) * Z - N * (Zt - Z)) / (Zt * Z) := by
    field_simp
    ring
  rw [key, abs_div, abs_of_pos (mul_pos hZtpos hZpos)]
  have hnum : |(Nt - N) * Z - N * (Zt - Z)| ≤ 2 * δ * Z := by
    calc |(Nt - N) * Z - N * (Zt - Z)| ≤ |(Nt - N) * Z| + |N * (Zt - Z)| := abs_sub _ _
      _ = |Nt - N| * Z + |N| * |Zt - Z| := by rw [abs_mul, abs_mul, abs_of_pos hZpos]
      _ ≤ δ * Z + Z * δ := by
          gcongr
      _ = 2 * δ * Z := by ring
  rw [div_le_div_iff₀ (by positivity) (by linarith)]
  calc |(Nt - N) * Z - N * (Zt - Z)| * (Z - δ) ≤ 2 * δ * Z * (Z - δ) := by
        gcongr
    _ = 2 * δ * ((Z - δ) * Z) := by ring
    _ ≤ 2 * δ * (Zt * Z) := by gcongr

/-- Paper: `lem:conf-moments` (conference.tex), the second ratio inequality
`2δ/(Z-δ) ≤ 4δe^H` under `Z ≥ e^(-H)` and `2δ ≤ Z`. -/
theorem ratio_bound_exp {Z δ H : ℝ} (hδ : 0 ≤ δ) (hZ : Real.exp (-H) ≤ Z) (h2δ : 2 * δ ≤ Z) :
    2 * δ / (Z - δ) ≤ 4 * δ * Real.exp H := by
  have hE : 0 < Real.exp (-H) := Real.exp_pos _
  have hZd : Real.exp (-H) / 2 ≤ Z - δ := by linarith
  have hpos : 0 < Z - δ := by linarith
  rw [div_le_iff₀ hpos]
  have hmul : Real.exp H * Real.exp (-H) = 1 := by rw [← Real.exp_add]; simp
  calc 2 * δ = 4 * δ * Real.exp H * (Real.exp (-H) / 2) := by
        rw [mul_div_assoc', mul_assoc (4 * δ), hmul]; ring
    _ ≤ 4 * δ * Real.exp H * (Z - δ) := by gcongr

/-- `δ = 2^(-q)` satisfies `2δ ≤ e^(-H)`, so `δ ≤ Z/2`.  Auxiliary step for
`lem:conf-moments` (conference.tex); this is "the choice of `q` makes `δ ≤ Z/2`" in the proof of
`lem:finitemomentindex` (attention_moment_decoder.tex). -/
theorem two_delta_le_exp_neg (p H : ℕ) :
    2 * (2 : ℝ) ^ (-(precQ p H : ℤ)) ≤ Real.exp (-(H : ℝ)) := by
  have h4 := exp_nat_le_four_pow H
  have hinv : ((4 : ℝ) ^ H)⁻¹ ≤ Real.exp (-(H : ℝ)) := by
    rw [Real.exp_neg]; exact inv_anti₀ (Real.exp_pos _) h4
  refine le_trans ?_ hinv
  have : (4 : ℝ) ^ H = (2 : ℝ) ^ ((2 * H : ℕ) : ℤ) := by
    rw [zpow_natCast, pow_mul]; norm_num
  rw [this, ← zpow_neg, show (2 : ℝ) * 2 ^ (-(precQ p H : ℤ)) = 2 ^ (1 - (precQ p H : ℤ)) by
    rw [zpow_sub₀ (by norm_num), zpow_neg, zpow_one, div_eq_mul_inv]]
  apply zpow_le_zpow_right₀ (by norm_num)
  unfold precQ; push_cast; omega

/-- Paper: `lem:conf-moments` (conference.tex), the third ratio inequality
`4δe^H ≤ 2^(-p-4)` for `δ = 2^(-q)`, `q = p + 2H + 6`. -/
theorem four_delta_exp_le (p H : ℕ) :
    4 * (2 : ℝ) ^ (-(precQ p H : ℤ)) * Real.exp H ≤ (2 : ℝ) ^ (-(p : ℤ) - 4) := by
  have h4 := exp_nat_le_four_pow H
  have : (4 : ℝ) ^ H = (2 : ℝ) ^ ((2 * H : ℕ) : ℤ) := by
    rw [zpow_natCast, pow_mul]; norm_num
  rw [this] at h4
  calc 4 * (2 : ℝ) ^ (-(precQ p H : ℤ)) * Real.exp H
      ≤ (2 : ℝ) ^ (2 : ℤ) * (2 : ℝ) ^ (-(precQ p H : ℤ)) * (2 : ℝ) ^ ((2 * H : ℕ) : ℤ) := by
        rw [show (2 : ℝ) ^ (2 : ℤ) = 4 by norm_num]; gcongr
    _ = (2 : ℝ) ^ (-(p : ℤ) - 4) := by
        rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
        congr 1
        unfold precQ; push_cast; ring

/-- The true (exponential) denominator `∑_j e^⟨t,z_j⟩`. -/
noncomputable def trueDen {T : ℕ} (t : Fin r → ℝ) (rec : Fin T → Record r a) : ℝ :=
  ∑ j, Real.exp (dotp t (rec j).z)

/-- The true numerator `∑_j e^⟨t,z_j⟩ v_{j,i}`. -/
noncomputable def trueNum {T : ℕ} (t : Fin r → ℝ) (rec : Fin T → Record r a) (i : Fin a) : ℝ :=
  ∑ j, Real.exp (dotp t (rec j).z) * (rec j).v i

/-- `|⟨t,z⟩| ≤ ‖t‖₁` for `z ∈ [-1,1]^r`, so every exponent lies in `[-H, H]`.  Auxiliary for
`lem:conf-moments` (conference.tex). -/
theorem abs_dotp_le {t z : Fin r → ℝ} (hz : ∀ i, |z i| ≤ 1) : |dotp t z| ≤ ∑ i, |t i| := by
  calc |dotp t z| ≤ ∑ i, |t i * z i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |t i| := sum_le_sum fun i _ => by
        rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hz i)

/-- Paper: `lem:conf-moments` (conference.tex), the error part of the lemma.  For records with
`z_j ∈ [-1,1]^r`, `v_j ∈ [-1,1]^a`, `T ≥ 1`, and `‖t‖₁ ≤ H`, the counter evaluator with
`m = ⌈8(p+3H+7)⌉` has a positive truncated denominator, at least `T e^(-H)/2`, and the ratio
of the counter-evaluated numerator and denominator is within `2^(-p-4)` of every coordinate of
the attention mean `A(t)`.  Full version: proof of `lem:finitemomentindex`
(attention_moment_decoder.tex). -/
theorem moment_ratio_error (p H : ℕ) {T : ℕ} (hT : 0 < T) (t : Fin r → ℝ)
    (rec : Fin T → Record r a) (hz : ∀ j i, |(rec j).z i| ≤ 1) (hv : ∀ j i, |(rec j).v i| ≤ 1)
    (ht : ∑ i, |t i| ≤ H) :
    0 < denomEval (momentDegree p H) t rec ∧
      T * Real.exp (-(H : ℝ)) / 2 ≤ denomEval (momentDegree p H) t rec ∧
      ∀ i, |numerEval (momentDegree p H) t rec i / denomEval (momentDegree p H) t rec -
          trueNum t rec i / trueDen t rec| ≤ (2 : ℝ) ^ (-(p : ℤ) - 4) := by
  set m := momentDegree p H
  set δ : ℝ := (2 : ℝ) ^ (-(precQ p H : ℤ)) with hδdef
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hδ0 : 0 ≤ δ := by positivity
  have hdot : ∀ j, |dotp t (rec j).z| ≤ H := fun j => (abs_dotp_le (hz j)).trans ht
  have htay : ∀ j, |Real.exp (dotp t (rec j).z) - expTrunc m (dotp t (rec j).z)| ≤ δ :=
    fun j => taylor_sup_error p H (hdot j)
  -- averaged quantities
  set Z := trueDen t rec / T
  set Zt := denomEval m t rec / T
  have hZ : Real.exp (-(H : ℝ)) ≤ Z := by
    rw [le_div_iff₀ hTpos, trueDen]
    calc Real.exp (-(H : ℝ)) * T = ∑ _j : Fin T, Real.exp (-(H : ℝ)) := by simp; ring
      _ ≤ ∑ j, Real.exp (dotp t (rec j).z) := sum_le_sum fun j _ =>
          Real.exp_le_exp.2 (neg_le_of_abs_le (hdot j))
  have h2δ : 2 * δ ≤ Z := (two_delta_le_exp_neg p H).trans hZ
  have hδZ : δ < Z := by
    have : 0 < Real.exp (-(H : ℝ)) := Real.exp_pos _
    have : (0 : ℝ) < 2 ^ (-(precQ p H : ℤ)) := by positivity
    linarith
  have hZt : |Zt - Z| ≤ δ := by
    rw [← sub_div, abs_div, abs_of_pos hTpos, div_le_iff₀ hTpos, denomEval_eq, trueDen,
      ← sum_sub_distrib]
    calc |∑ j, (expTrunc m (dotp t (rec j).z) - Real.exp (dotp t (rec j).z))|
        ≤ ∑ j, |expTrunc m (dotp t (rec j).z) - Real.exp (dotp t (rec j).z)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin T, δ := sum_le_sum fun j _ => by rw [abs_sub_comm]; exact htay j
      _ = δ * T := by simp; ring
  have hNZ : ∀ i, |trueNum t rec i / T| ≤ Z := by
    intro i
    rw [abs_div, abs_of_pos hTpos, show Z = trueDen t rec / T from rfl]
    gcongr
    calc |trueNum t rec i| ≤ ∑ j, |Real.exp (dotp t (rec j).z) * (rec j).v i| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, Real.exp (dotp t (rec j).z) := sum_le_sum fun j _ => by
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          exact mul_le_of_le_one_right (Real.exp_pos _).le (hv j i)
  have hNt : ∀ i, |numerEval m t rec i / T - trueNum t rec i / T| ≤ δ := by
    intro i
    rw [← sub_div, abs_div, abs_of_pos hTpos, div_le_iff₀ hTpos, numerEval_eq, trueNum,
      ← sum_sub_distrib]
    calc |∑ j, (expTrunc m (dotp t (rec j).z) * (rec j).v i -
            Real.exp (dotp t (rec j).z) * (rec j).v i)|
        ≤ ∑ j, |expTrunc m (dotp t (rec j).z) * (rec j).v i -
            Real.exp (dotp t (rec j).z) * (rec j).v i| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin T, δ := sum_le_sum fun j _ => by
          rw [← sub_mul, abs_mul, abs_sub_comm]
          calc |Real.exp (dotp t (rec j).z) - expTrunc m (dotp t (rec j).z)| * |(rec j).v i|
              ≤ δ * 1 := mul_le_mul (htay j) (hv j i) (abs_nonneg _) hδ0
            _ = δ := mul_one δ
      _ = δ * T := by simp; ring
  have hlow : Z - δ ≤ Zt := by have := (abs_le.1 hZt).1; linarith
  have hZtpos : 0 < Zt := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have := hZtpos
    simp only [Zt] at this
    exact (div_pos_iff_of_pos_right hTpos).1 this
  · have : Z / 2 ≤ Zt := by linarith
    have h2 : Real.exp (-(H : ℝ)) / 2 ≤ Zt := by linarith
    simp only [Zt] at h2
    rw [le_div_iff₀ hTpos] at h2
    linarith
  · intro i
    obtain ⟨_, hrat⟩ := ratio_error (hNZ i) hδ0 hδZ hZt (hNt i)
    have hcancel1 : numerEval m t rec i / T / Zt =
        numerEval m t rec i / denomEval m t rec := by
      simp only [Zt]; rw [div_div_div_cancel_right₀ hTpos.ne']
    have hcancel2 : trueNum t rec i / T / Z = trueNum t rec i / trueDen t rec := by
      simp only [Z]; rw [div_div_div_cancel_right₀ hTpos.ne']
    rw [hcancel1, hcancel2] at hrat
    exact hrat.trans ((ratio_bound_exp hδ0 hZ h2δ).trans (four_delta_exp_le p H))

/-- Paper: `lem:conf-moments` (conference.tex): "Rational division to width `2^(-p-2)`, enlarged
by this error, gives the required interval."  An interval of width at most `2^(-p-2)` around
the computed ratio, enlarged by `2^(-p-4)` on both sides, contains the true value and has width
less than `2^(-p)`. -/
theorem enclosure_width (p : ℕ) {A R lo hi : ℝ} (hR : |R - A| ≤ (2 : ℝ) ^ (-(p : ℤ) - 4))
    (hlo : lo ≤ R) (hhi : R ≤ hi) (hw : hi - lo ≤ (2 : ℝ) ^ (-(p : ℤ) - 2)) :
    lo - (2 : ℝ) ^ (-(p : ℤ) - 4) ≤ A ∧ A ≤ hi + (2 : ℝ) ^ (-(p : ℤ) - 4) ∧
      (hi + (2 : ℝ) ^ (-(p : ℤ) - 4)) - (lo - (2 : ℝ) ^ (-(p : ℤ) - 4)) <
        (2 : ℝ) ^ (-(p : ℤ)) := by
  have hR' := abs_le.1 hR
  refine ⟨by linarith, by linarith, ?_⟩
  have e4 : (2 : ℝ) ^ (-(p : ℤ) - 4) = (2 : ℝ) ^ (-(p : ℤ)) / 16 := by
    rw [zpow_sub₀ (by norm_num)]; norm_num
  have e2 : (2 : ℝ) ^ (-(p : ℤ) - 2) = (2 : ℝ) ^ (-(p : ℤ)) / 4 := by
    rw [zpow_sub₀ (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := by positivity
  rw [e4]
  rw [e2] at hw
  linarith

/-! ## Denominators of the Taylor coefficients -/

/-- `ν! ∣ |ν|! ∣ m!` for `|ν| ≤ m`, as used in the proof of `lem:conf-moments`
(conference.tex). -/
theorem mfact_dvd_factorial {m : ℕ} {ν : Fin r → ℕ} (hν : ∑ i, ν i ≤ m) :
    mfact ν ∣ m.factorial :=
  (Nat.prod_factorial_dvd_factorial_sum univ ν).trans (Nat.factorial_dvd_factorial hν)

/-- Paper: `lem:conf-moments` (conference.tex): if `d_t` is a common denominator of the
rational coordinates of `t`, the Taylor coefficients `t^ν/ν!`, `|ν| ≤ m`, have denominators
dividing `d_t^m m!`. -/
theorem coeff_denominator {m : ℕ} (d : ℕ) (t : Fin r → ℝ) (ht : ∀ i, ∃ k : ℤ, (d : ℝ) * t i = k)
    {ν : Fin r → ℕ} (hν : ∑ i, ν i ≤ m) :
    ∃ k : ℤ, ((d : ℝ) ^ m * m.factorial) * (mono ν t / mfact ν) = k := by
  choose k hk using ht
  obtain ⟨c, hc⟩ := mfact_dvd_factorial hν
  refine ⟨(d : ℤ) ^ (m - ∑ i, ν i) * (∏ i, k i ^ ν i) * c, ?_⟩
  have hmf : (mfact ν : ℝ) ≠ 0 := by exact_mod_cast (mfact_pos ν).ne'
  have hprod : (d : ℝ) ^ (∑ i, ν i) * mono ν t = ∏ i, ((k i : ℝ)) ^ (ν i) := by
    rw [mono, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => by rw [← mul_pow, hk]
  have hpow : (d : ℝ) ^ m = (d : ℝ) ^ (m - ∑ i, ν i) * (d : ℝ) ^ (∑ i, ν i) := by
    rw [← pow_add, Nat.sub_add_cancel hν]
  rw [hc]
  push_cast
  rw [hpow]
  field_simp
  rw [← hprod]
  ring

/-! ## Standard scaling: the parity split -/

/-- `(√n)^d = n^⌊d/2⌋` for even `d` and `n^⌊d/2⌋ √n` for odd `d`.  Auxiliary for the parity
split in `lem:conf-moments` (conference.tex). -/
theorem sqrt_pow_parity (n d : ℕ) :
    (Real.sqrt n) ^ d = (n : ℝ) ^ (d / 2) * (if d % 2 = 0 then 1 else Real.sqrt n) := by
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  conv_lhs => rw [← Nat.div_add_mod d 2, pow_add, pow_mul, hsq]
  rcases Nat.mod_two_eq_zero_or_one d with h | h <;> simp [h]

/-- `(c/√n)^ν = c^ν/(√n)^|ν|`.  Auxiliary for the parity split in `lem:conf-moments`
(conference.tex). -/
theorem mono_div_sqrt (n : ℕ) (c : Fin r → ℝ) (ν : Fin r → ℕ) :
    mono ν (fun i => c i / Real.sqrt n) = mono ν c / (Real.sqrt n) ^ (∑ i, ν i) := by
  rw [mono, mono, ← prod_pow_eq_pow_sum, ← prod_div_distrib]
  exact prod_congr rfl fun i _ => div_pow _ _ _

/-- The even part `A` of the parity split. -/
noncomputable def evenPart (n m : ℕ) (c : Fin r → ℝ) (w : (Fin r → ℕ) → ℝ) : ℝ :=
  ∑ ν ∈ (multiIdx r m).filter (fun ν => (∑ i, ν i) % 2 = 0),
    mono ν c / (mfact ν * (n : ℝ) ^ ((∑ i, ν i) / 2)) * w ν

/-- The odd part `B` of the parity split. -/
noncomputable def oddPart (n m : ℕ) (c : Fin r → ℝ) (w : (Fin r → ℕ) → ℝ) : ℝ :=
  ∑ ν ∈ (multiIdx r m).filter (fun ν => ¬ (∑ i, ν i) % 2 = 0),
    mono ν c / (mfact ν * (n : ℝ) ^ ((∑ i, ν i) / 2)) * w ν

/-- Paper: `lem:conf-moments` (conference.tex): for `t_i = c_i/√n`, splitting the multi-indices
by the parity of `|ν|` writes every truncated sum `∑_ν t^ν w_ν/ν!` as `A + B/√n`, where `A` is
the even-degree part and `B` the odd-degree part; full version: proof of
`lem:finitemomentindex` (attention_moment_decoder.tex). -/
theorem parity_split (n m : ℕ) (hn : 0 < n) (c : Fin r → ℝ) (w : (Fin r → ℕ) → ℝ) :
    ∑ ν ∈ multiIdx r m, mono ν (fun i => c i / Real.sqrt n) / mfact ν * w ν =
      evenPart n m c w + oddPart n m c w / Real.sqrt n := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← sum_filter_add_sum_filter_not (multiIdx r m) (fun ν => (∑ i, ν i) % 2 = 0),
    evenPart, oddPart, sum_div]
  congr 1
  · refine sum_congr rfl fun ν hν => ?_
    rw [mem_filter] at hν
    rw [mono_div_sqrt, sqrt_pow_parity]
    simp only [hν.2, ↓reduceIte]
    have : (0 : ℝ) < mfact ν := by exact_mod_cast mfact_pos ν
    field_simp
  · refine sum_congr rfl fun ν hν => ?_
    rw [mem_filter] at hν
    rw [mono_div_sqrt, sqrt_pow_parity]
    simp only [hν.2, ↓reduceIte]
    have : (0 : ℝ) < mfact ν := by exact_mod_cast mfact_pos ν
    field_simp

/-- Paper: `lem:conf-moments` (conference.tex): with rational `c_i` and rational counter values,
each truncated sum at `t_i = c_i/√n` equals `A + B/√n` with rational `A, B`; `√n` is kept
exact. -/
theorem parity_split_rat (n m : ℕ) (hn : 0 < n) (c : Fin r → ℚ) (w : (Fin r → ℕ) → ℚ) :
    ∃ A B : ℚ, ∑ ν ∈ multiIdx r m,
        mono ν (fun i => (c i : ℝ) / Real.sqrt n) / mfact ν * (w ν : ℝ) =
      A + B / Real.sqrt n := by
  refine ⟨∑ ν ∈ (multiIdx r m).filter (fun ν => (∑ i, ν i) % 2 = 0),
      (∏ i, c i ^ ν i) / (mfact ν * (n : ℚ) ^ ((∑ i, ν i) / 2)) * w ν,
    ∑ ν ∈ (multiIdx r m).filter (fun ν => ¬ (∑ i, ν i) % 2 = 0),
      (∏ i, c i ^ ν i) / (mfact ν * (n : ℚ) ^ ((∑ i, ν i) / 2)) * w ν, ?_⟩
  rw [parity_split n m hn (fun i => (c i : ℝ)) (fun ν => (w ν : ℝ)), evenPart, oddPart]
  push_cast
  rfl

/-- Paper: `lem:conf-moments` (conference.tex): at standard scaling `t_i = c_i/√n`, with `d_c` a
common denominator of the `c_i`, the coefficients `c^ν/(ν! n^⌊|ν|/2⌋)` of the parity split have
a common denominator dividing `d_c^m n^⌊m/2⌋ m!`. -/
theorem parity_coeff_denominator {m : ℕ} (n d : ℕ) (c : Fin r → ℝ)
    (hc : ∀ i, ∃ k : ℤ, (d : ℝ) * c i = k) (hn : 0 < n) {ν : Fin r → ℕ}
    (hν : ∑ i, ν i ≤ m) :
    ∃ k : ℤ, ((d : ℝ) ^ m * (n : ℝ) ^ (m / 2) * m.factorial) *
        (mono ν c / (mfact ν * (n : ℝ) ^ ((∑ i, ν i) / 2))) = k := by
  obtain ⟨k, hk⟩ := coeff_denominator d c hc hν
  have hle : (∑ i, ν i) / 2 ≤ m / 2 := Nat.div_le_div_right hν
  refine ⟨k * (n : ℤ) ^ (m / 2 - (∑ i, ν i) / 2), ?_⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmf : (mfact ν : ℝ) ≠ 0 := by exact_mod_cast (mfact_pos ν).ne'
  have hpow : (n : ℝ) ^ (m / 2) = (n : ℝ) ^ (m / 2 - (∑ i, ν i) / 2) *
      (n : ℝ) ^ ((∑ i, ν i) / 2) := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  push_cast
  rw [← hk, hpow]
  field_simp

end ExactSampling.Moments
