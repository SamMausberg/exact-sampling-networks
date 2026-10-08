import Mathlib

/-!
# The search obstruction at a fresh context

Paper: `conference.tex`, Section `sec:conf-scalar`, the paragraph beginning "Here is the search
obstruction in its simplest form": at the all-negative sign context with scores `A x_j` and
values `x_j`, flipping coordinate `i` gives positive attention mass `e^{2A} / (T - 1 + e^{2A})`;
coupling the random tapes of an exact sampler on the two inputs shows that coordinate `i` is
read with probability at least the total-variation distance of the target laws; summing over
`i` forces `Ω(min{T, e^{2A}})` probes. Full version `exact_sampling_networks.tex`:
`lem:attentioncoupling`, `thm:attentionpositionlower` and the family
`eq:binaryattentionfamily` (`attention_primitives.tex`).

## The model

An adaptive query algorithm is a map `next : Ω → List (ι × α) → ι ⊕ β`: given its random tape
`ω` (which includes all preprocessing randomness) and the transcript of the coordinates read so
far with their answers, it either reads one more coordinate or halts with an output. On input
`x` the transcript evolves deterministically from `ω`. Coordinate `i` is *read* on `(x, ω)` if
some step queries it, and the run *outputs* `y` if some step halts with `y`. The tape carries an
arbitrary measure `μ`; no measurability is needed for the coupling inequality, and the
expected number of distinct probes is computed under measurability of the read events.

The target law of the sampler on a sign context `x` is the law of the value at an
attention-sampled index (equivalently a sign of mean equal to the attention mean); its
probability of `+1` is the positive attention mass.

## What is formalized

* If `x` and `x'` differ only at `i` and `i` is not read on `(x, ω)`, the two transcripts agree
  at every step, so the runs read the same coordinates and give the same outputs.
* The coupling inequality: for every set `S` of outputs,
  `μ(out_x ∈ S) ≤ μ(out_{x'} ∈ S) + μ(i read on x)` and symmetrically, hence for an exact
  sampler `|ν_x(S) - ν_{x'}(S)| ≤ μ(i read on x)`.
* The attention computation: positive mass `0` at the all-negative context and
  `e^{2A} / (T - 1 + e^{2A})` after flipping one coordinate; the attention mean `-1 + 2p`.
* The expected number of distinct probes is `∑ᵢ μ(i read)`, and for an exact sampler on the
  all-negative context it is at least `T e^{2A} / (T - 1 + e^{2A}) ≥ min{T, e^{2A}} / 2`.
* The head of the full version (`thm:attentionpositionlower`): on `[-1, 1]` the tanh and the
  convex residual gate increase at rate at least `1/4` and the binary-softmax token probability
  at rate at least `1/8` (from `cosh 1 < 2`), so flipping coordinate `j` raises the token
  probability by at least `(α p + (1 - α)[j = last]) / 16`; an exact token sampler has expected
  probe count at least `((1 - α) + α T p)/16 ≥ (1 + α min{T, e^{2A}})/64`.

## What is not formalized

The matching upper bound `Θ(1 + α min{T, e^{2βs^2}})` of the full version
(`thm:binaryattentionlaw`), the consequence `2√n s^2 ≥ log T`, and the remark that an index
built from the context avoids the coupling are not formalized. From
`thm:attentionpositionlower`, the variant with `x_T` fixed in advance
(`eq:attentionpositionlowerprefix`, the bound `(α/32) min{T - 1, E}`) and the remark that
`β s^2 ≥ (1/2) log T` forces `Ω(α T)` probes are not formalized either.
-/

open Real MeasureTheory Finset
open scoped ENNReal

namespace ExactSampling.SearchObstruction

/-! ### Adaptive query algorithms with a random tape -/

/-- An adaptive query algorithm with random tape `ω : Ω`: given the tape and the transcript of
previous (coordinate, answer) pairs, it either queries a coordinate (`Sum.inl i`) or halts with
an output (`Sum.inr y`). Paper: the coupling paragraph in `sec:conf-scalar` (conference.tex);
full version: `lem:attentioncoupling` (attention_primitives.tex). -/
structure QueryAlg (Ω ι α β : Type*) where
  /-- The next action as a function of the tape and the transcript. -/
  next : Ω → List (ι × α) → ι ⊕ β

variable {Ω ι α β : Type*}

/-- One step of the run on input `x`: append the answer to the next query, or stay halted. -/
def step (M : QueryAlg Ω ι α β) (x : ι → α) (ω : Ω) (t : List (ι × α)) : List (ι × α) :=
  match M.next ω t with
  | Sum.inl i => t ++ [(i, x i)]
  | Sum.inr _ => t

/-- The transcript after `m` steps of the run on input `x` with tape `ω`. -/
def transcript (M : QueryAlg Ω ι α β) (x : ι → α) (ω : Ω) (m : ℕ) : List (ι × α) :=
  (step M x ω)^[m] []

/-- Coordinate `i` is read on input `x` with tape `ω`. -/
def Reads (M : QueryAlg Ω ι α β) (x : ι → α) (ω : Ω) (i : ι) : Prop :=
  ∃ m, M.next ω (transcript M x ω m) = Sum.inl i

/-- The run on input `x` with tape `ω` halts with output `y`. -/
def Outputs (M : QueryAlg Ω ι α β) (x : ι → α) (ω : Ω) (y : β) : Prop :=
  ∃ m, M.next ω (transcript M x ω m) = Sum.inr y

/-- One step depends on the input only through the coordinate it queries. Auxiliary for the
coupling paragraph in `sec:conf-scalar` (conference.tex). -/
theorem step_congr (M : QueryAlg Ω ι α β) {x x' : ι → α} (ω : Ω) (t : List (ι × α))
    (h : ∀ j, M.next ω t = Sum.inl j → x j = x' j) : step M x ω t = step M x' ω t := by
  rcases hn : M.next ω t with j | y
  · simp only [step, hn, h j hn]
  · simp only [step, hn]

/-- Transcripts agree until the changed coordinate is read: if `x` and `x'` agree off `i` and
`i` is never read on `(x, ω)`, the transcripts on `x` and `x'` agree at every step. Paper: the
coupling paragraph in `sec:conf-scalar` (conference.tex), "their outputs can differ only after
coordinate `i` is read"; full version: proof of `lem:attentioncoupling`
(attention_primitives.tex), "the transcripts agree until coordinate `j` is queried". -/
theorem transcript_eq (M : QueryAlg Ω ι α β) {x x' : ι → α} {i : ι}
    (hxx : ∀ j, j ≠ i → x j = x' j) (ω : Ω) (h : ¬ Reads M x ω i) (m : ℕ) :
    transcript M x ω m = transcript M x' ω m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [transcript, Function.iterate_succ_apply'] at ih ⊢
    rw [← ih]
    apply step_congr
    intro j hj
    apply hxx j
    rintro rfl
    exact h ⟨m, hj⟩

/-- Unread coordinates do not change reads or outputs: if `x` and `x'` agree off `i` and `i` is
not read on `(x, ω)`, the runs read the same coordinates and give the same outputs. Paper: the
coupling paragraph in `sec:conf-scalar` (conference.tex); full version: proof of
`lem:attentioncoupling` (attention_primitives.tex). -/
theorem reads_outputs_iff (M : QueryAlg Ω ι α β) {x x' : ι → α} {i : ι}
    (hxx : ∀ j, j ≠ i → x j = x' j) (ω : Ω) (h : ¬ Reads M x ω i) :
    (∀ k, Reads M x ω k ↔ Reads M x' ω k) ∧ (∀ y, Outputs M x ω y ↔ Outputs M x' ω y) := by
  have ht := transcript_eq M hxx ω h
  exact ⟨fun k => by simp only [Reads, ht], fun y => by simp only [Outputs, ht]⟩

/-- The coupling inequality for one set of outputs: with the same tape on `x` and `x'` (which
differ only at `i`), `μ(out_x ∈ S) ≤ μ(out_{x'} ∈ S) + μ(i read on x)` and
`μ(out_{x'} ∈ S) ≤ μ(out_x ∈ S) + μ(i read on x)`. Paper: the coupling paragraph in
`sec:conf-scalar` (conference.tex); full version: `lem:attentioncoupling`
(attention_primitives.tex). -/
theorem coupling_le [MeasurableSpace Ω] (μ : Measure Ω) (M : QueryAlg Ω ι α β) {x x' : ι → α}
    {i : ι} (hxx : ∀ j, j ≠ i → x j = x' j) (S : Set β) :
    μ {ω | ∃ y ∈ S, Outputs M x ω y}
        ≤ μ {ω | ∃ y ∈ S, Outputs M x' ω y} + μ {ω | Reads M x ω i} ∧
      μ {ω | ∃ y ∈ S, Outputs M x' ω y}
        ≤ μ {ω | ∃ y ∈ S, Outputs M x ω y} + μ {ω | Reads M x ω i} := by
  constructor
  · refine (measure_mono ?_).trans (measure_union_le _ _)
    intro ω ⟨y, hy, hout⟩
    by_cases hr : Reads M x ω i
    · exact Or.inr hr
    · exact Or.inl ⟨y, hy, ((reads_outputs_iff M hxx ω hr).2 y).mp hout⟩
  · refine (measure_mono ?_).trans (measure_union_le _ _)
    intro ω ⟨y, hy, hout⟩
    by_cases hr : Reads M x ω i
    · exact Or.inr hr
    · exact Or.inl ⟨y, hy, ((reads_outputs_iff M hxx ω hr).2 y).mpr hout⟩

/-- The read probability bounds the total-variation distance of the target laws. If the sampler
is exact, `μ(out_z ∈ S) = ν_z(S)` for `z = x, x'`, then for every set `S`,
`|ν_x(S) - ν_{x'}(S)| ≤ μ(i read on x)`. Paper: the coupling paragraph in `sec:conf-scalar`
(conference.tex), "the probability of that read is at least the total-variation distance of the
target laws"; full version: `lem:attentioncoupling` (attention_primitives.tex). -/
theorem tv_le_read [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (M : QueryAlg Ω ι α β) {x x' : ι → α} {i : ι} (hxx : ∀ j, j ≠ i → x j = x' j)
    (S : Set β) {px px' : ℝ} (hx : μ {ω | ∃ y ∈ S, Outputs M x ω y} = ENNReal.ofReal px)
    (hx' : μ {ω | ∃ y ∈ S, Outputs M x' ω y} = ENNReal.ofReal px') (hpx : 0 ≤ px)
    (hpx' : 0 ≤ px') : |px - px'| ≤ μ.real {ω | Reads M x ω i} := by
  obtain ⟨h1, h2⟩ := coupling_le μ M hxx S
  rw [hx, hx'] at h1 h2
  have hfin : μ {ω | Reads M x ω i} ≠ ∞ := measure_ne_top μ _
  have hR : μ {ω | Reads M x ω i} = ENNReal.ofReal (μ.real {ω | Reads M x ω i}) := by
    rw [measureReal_def, ENNReal.ofReal_toReal hfin]
  rw [hR, ← ENNReal.ofReal_add hpx' measureReal_nonneg] at h1
  rw [hR, ← ENNReal.ofReal_add hpx measureReal_nonneg] at h2
  have h1' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  have h2' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
  rw [abs_le]
  constructor <;> linarith

open scoped Classical in
/-- The expected number of distinct coordinates read equals `∑ᵢ μ(i read)`. Paper: the coupling
paragraph in `sec:conf-scalar` (conference.tex), "summing over `i`"; full version: proof of
`thm:attentionpositionlower` (attention_primitives.tex). -/
theorem lintegral_card_reads [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω)
    (M : QueryAlg Ω ι α β) (x : ι → α) (hmeas : ∀ i, MeasurableSet {ω | Reads M x ω i}) :
    ∫⁻ ω, ((Finset.univ.filter (fun i => Reads M x ω i)).card : ℝ≥0∞) ∂μ
      = ∑ i, μ {ω | Reads M x ω i} := by
  classical
  have hcard : ∀ ω, ((Finset.univ.filter (fun i => Reads M x ω i)).card : ℝ≥0∞)
      = ∑ i, Set.indicator {ω | Reads M x ω i} 1 ω := by
    intro ω
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : Reads M x ω i <;> simp [h]
  simp_rw [hcard]
  rw [lintegral_finsetSum _ (fun i _ => (measurable_one.indicator (hmeas i)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact lintegral_indicator_one (hmeas i)

/-! ### The binary attention family at a fresh context -/

/-- The positive attention mass `∑_{x_j = 1} e^{A x_j} / ∑ⱼ e^{A x_j}` for scores `A x_j` and
values `x_j`. Paper: the coupling paragraph in `sec:conf-scalar` (conference.tex); full version:
`eq:binaryattentionfamily` (attention_primitives.tex). -/
noncomputable def posMass {T : ℕ} (A : ℝ) (x : Fin T → ℝ) : ℝ :=
  (∑ j, if x j = 1 then exp (A * x j) else 0) / ∑ j, exp (A * x j)

/-- The attention mean `Y(x) = ∑ⱼ e^{A x_j} x_j / ∑ⱼ e^{A x_j}`. Paper: `eq:conf-attention`
(conference.tex) for this family; full version: `eq:binaryattentionfamily`
(attention_primitives.tex). -/
noncomputable def attnMean {T : ℕ} (A : ℝ) (x : Fin T → ℝ) : ℝ :=
  (∑ j, exp (A * x j) * x j) / ∑ j, exp (A * x j)

/-- The all-negative sign context. -/
def negCtx (T : ℕ) : Fin T → ℝ := fun _ => -1

/-- The context with only coordinate `i` flipped to `+1`. -/
noncomputable def flipCtx {T : ℕ} (i : Fin T) : Fin T → ℝ := Function.update (negCtx T) i 1

/-- The flipped context agrees with the all-negative context off the flipped coordinate.
Auxiliary for the coupling paragraph in `sec:conf-scalar` (conference.tex). -/
theorem flipCtx_agree {T : ℕ} (i : Fin T) : ∀ j, j ≠ i → negCtx T j = flipCtx i j := by
  intro j hj
  simp [flipCtx, Function.update_of_ne hj]

/-- The all-negative context has positive attention mass zero and attention mean `-1`. Paper:
the coupling paragraph in `sec:conf-scalar` (conference.tex); full version: proof of
`thm:attentionpositionlower` (attention_primitives.tex), `Y(x⁻) = -1`. -/
theorem negCtx_mass {T : ℕ} (hT : 0 < T) (A : ℝ) :
    posMass A (negCtx T) = 0 ∧ attnMean A (negCtx T) = -1 := by
  have : Nonempty (Fin T) := ⟨⟨0, hT⟩⟩
  have hpos : 0 < ∑ _j : Fin T, exp (A * -1) :=
    Finset.sum_pos (fun _ _ => exp_pos _) Finset.univ_nonempty
  constructor
  · unfold posMass negCtx
    norm_num
  · unfold attnMean negCtx
    simp only [mul_neg_one]
    rw [show (∑ _j : Fin T, -exp (-A)) = -∑ _j : Fin T, exp (-A) by
      rw [Finset.sum_neg_distrib]]
    have : 0 < ∑ _j : Fin T, exp (-A) := by simpa using hpos
    field_simp

/-- Sum over the flipped context: `∑ⱼ f(x_j) = f(1) + (T - 1) f(-1)`. Auxiliary for the
coupling paragraph in `sec:conf-scalar` (conference.tex). -/
theorem sum_flipCtx {T : ℕ} (i : Fin T) (f : ℝ → ℝ) :
    ∑ j, f (flipCtx i j) = f 1 + ((T : ℝ) - 1) * f (-1) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have h1 : flipCtx i i = 1 := by simp [flipCtx]
  have h2 : ∀ j ∈ Finset.univ.erase i, f (flipCtx i j) = f (-1) := by
    intro j hj
    rw [← flipCtx_agree i j (Finset.ne_of_mem_erase hj)]
    rfl
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_erase_of_mem
    (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hT : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact i.elim0)
  push_cast [hT]
  ring

/-- Flipping one coordinate of the all-negative context gives positive attention mass
`e^{2A} / (T - 1 + e^{2A})` and attention mean `-1 + 2 e^{2A} / (T - 1 + e^{2A})`. Paper: the
coupling paragraph in `sec:conf-scalar` (conference.tex), "changing only coordinate `i` makes
its positive attention mass `e^{2A}/(T-1+e^{2A})`"; full version: proof of
`thm:attentionpositionlower` (attention_primitives.tex). -/
theorem flipCtx_mass {T : ℕ} (i : Fin T) (A : ℝ) :
    posMass A (flipCtx i) = exp (2 * A) / (T - 1 + exp (2 * A)) ∧
      attnMean A (flipCtx i) = -1 + 2 * (exp (2 * A) / (T - 1 + exp (2 * A))) := by
  have hT : (1 : ℝ) ≤ T := by
    have : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact i.elim0)
    exact_mod_cast this
  have hden : ∑ j, exp (A * flipCtx i j) = exp A + ((T : ℝ) - 1) * (exp A)⁻¹ := by
    rw [sum_flipCtx i (fun t => exp (A * t))]
    simp only [mul_one, mul_neg_one, Real.exp_neg]
  have e2 : exp (2 * A) = exp A * exp A := by rw [← exp_add]; ring_nf
  have hE := exp_pos A
  have hD : 0 < exp A + ((T : ℝ) - 1) * (exp A)⁻¹ := by
    have : 0 ≤ ((T : ℝ) - 1) * (exp A)⁻¹ := mul_nonneg (by linarith) (inv_pos.mpr hE).le
    linarith
  have hP : 0 < (T : ℝ) - 1 + exp A * exp A := by nlinarith
  constructor
  · have hnum : ∑ j, (if flipCtx i j = 1 then exp (A * flipCtx i j) else 0) = exp A := by
      rw [sum_flipCtx i (fun t => if t = 1 then exp (A * t) else 0)]
      norm_num
    unfold posMass
    rw [hnum, hden, e2]
    field_simp
    ring
  · have hnum : ∑ j, exp (A * flipCtx i j) * flipCtx i j
        = exp A - ((T : ℝ) - 1) * (exp A)⁻¹ := by
      rw [sum_flipCtx i (fun t => exp (A * t) * t)]
      simp only [mul_one, mul_neg_one, Real.exp_neg]
      ring
    unfold attnMean
    rw [hnum, hden, e2]
    have key : (exp A - ((T : ℝ) - 1) * (exp A)⁻¹) / (exp A + ((T : ℝ) - 1) * (exp A)⁻¹)
        = (exp A * exp A - ((T : ℝ) - 1)) / ((T : ℝ) - 1 + exp A * exp A) := by
      rw [div_eq_div_iff hD.ne' hP.ne']
      field_simp
      ring
    rw [key, mul_div_assoc', add_div' _ _ _ hP.ne']
    congr 1
    ring

/-- `T e^{2A} / (T - 1 + e^{2A}) ≥ min{T, e^{2A}} / 2` for `T ≥ 1`, `A ≥ 0`. Paper: the coupling
paragraph in `sec:conf-scalar` (conference.tex), "forces `Ω(min{T, e^{2A}})` probes"; full
version: proof of `thm:attentionpositionlower` (attention_primitives.tex), "for positive `a,b`,
`ab/(a+b) ≥ min{a,b}/2`". -/
theorem min_le_sum_tv {T : ℕ} (hT : 1 ≤ T) {A : ℝ} (hA : 0 ≤ A) :
    min (T : ℝ) (exp (2 * A)) / 2 ≤ T * (exp (2 * A) / (T - 1 + exp (2 * A))) := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hE : 1 ≤ exp (2 * A) := one_le_exp (by linarith)
  have hpos : 0 < (T : ℝ) - 1 + exp (2 * A) := by linarith
  rw [mul_div_assoc', le_div_iff₀ hpos]
  rcases le_total (T : ℝ) (exp (2 * A)) with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

open scoped Classical in
/-- The search obstruction. Let `M` be an adaptive query algorithm on sign contexts
`x ∈ {-1, 1}^T` whose output is exact: on every sign context its probability of outputting
`true` (`+1`) is the positive attention mass for scores `A x_j` and values `x_j`. Then, on the
all-negative context, coordinate `i` is read with probability at least
`e^{2A} / (T - 1 + e^{2A})` for every `i`, and if the read events are measurable the expected
number of distinct probes is at least `T e^{2A} / (T - 1 + e^{2A}) ≥ min{T, e^{2A}} / 2`.
Paper: the coupling paragraph in `sec:conf-scalar` (conference.tex), "summing over `i` forces
`Ω(min{T, e^{2A}})` probes"; full version: `lem:attentioncoupling` and
`thm:attentionpositionlower` (attention_primitives.tex). -/
theorem search_lower_bound [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : ℕ} (hT : 1 ≤ T) {A : ℝ} (hA : 0 ≤ A) (M : QueryAlg Ω (Fin T) ℝ Bool)
    (hexact : ∀ x : Fin T → ℝ, (∀ j, x j = 1 ∨ x j = -1) →
      μ {ω | ∃ y ∈ ({true} : Set Bool), Outputs M x ω y} = ENNReal.ofReal (posMass A x)) :
    (∀ i, exp (2 * A) / (T - 1 + exp (2 * A)) ≤ μ.real {ω | Reads M (negCtx T) ω i}) ∧
    ((∀ i, MeasurableSet {ω | Reads M (negCtx T) ω i}) →
      ENNReal.ofReal (min (T : ℝ) (exp (2 * A)) / 2)
        ≤ ∫⁻ ω, ((Finset.univ.filter (fun i => Reads M (negCtx T) ω i)).card : ℝ≥0∞) ∂μ) := by
  have hTpos : 0 < T := hT
  have hneg : ∀ j, negCtx T j = 1 ∨ negCtx T j = -1 := fun j => Or.inr rfl
  have hflip : ∀ (i : Fin T) j, flipCtx i j = 1 ∨ flipCtx i j = -1 := by
    intro i j
    by_cases h : j = i
    · subst h; left; simp [flipCtx]
    · right; rw [← flipCtx_agree i j h]; rfl
  have hEpos : 0 < exp (2 * A) / (T - 1 + exp (2 * A)) := by
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have := exp_pos (2 * A)
    positivity
  have hread : ∀ i, exp (2 * A) / (T - 1 + exp (2 * A)) ≤ μ.real {ω | Reads M (negCtx T) ω i} := by
    intro i
    have h1 := hexact (negCtx T) hneg
    have h2 := hexact (flipCtx i) (hflip i)
    rw [(negCtx_mass hTpos A).1] at h1
    rw [(flipCtx_mass i A).1] at h2
    have := tv_le_read μ M (flipCtx_agree i) {true} h1 h2 le_rfl hEpos.le
    rwa [zero_sub, abs_neg, abs_of_pos hEpos] at this
  refine ⟨hread, fun hmeas => ?_⟩
  rw [lintegral_card_reads μ M (negCtx T) hmeas]
  have hsum : ENNReal.ofReal (∑ i : Fin T, μ.real {ω | Reads M (negCtx T) ω i})
      = ∑ i, μ {ω | Reads M (negCtx T) ω i} := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => measureReal_nonneg)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
  rw [← hsum]
  apply ENNReal.ofReal_le_ofReal
  calc min (T : ℝ) (exp (2 * A)) / 2 ≤ T * (exp (2 * A) / (T - 1 + exp (2 * A))) :=
        min_le_sum_tv hT hA
    _ = ∑ _i : Fin T, exp (2 * A) / (T - 1 + exp (2 * A)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ i : Fin T, μ.real {ω | Reads M (negCtx T) ω i} :=
        Finset.sum_le_sum fun i _ => hread i

/-! ### A bounded tanh and binary-softmax head with a convex residual gate -/

/-- `cosh 1 < 2`. Auxiliary for the head gap in the search obstruction of `sec:conf-scalar`
(conference.tex); full version: proof of `thm:attentionpositionlower`
(attention_primitives.tex), "the inequalities follow from `cosh 1 < 2`". -/
theorem cosh_one_lt_two : cosh 1 < 2 := by
  rw [Real.cosh_eq]
  have h1 := Real.exp_one_lt_d9
  have h2 : exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

/-- On `[-1, 1]`, `tanh` increases at rate at least `1/4`: `tanh b - tanh a ≥ (b - a)/4` for
`-1 ≤ a ≤ b ≤ 1` (since `sech² ≥ 1/4` there). Paper: the search obstruction paragraph in
`sec:conf-scalar` (conference.tex), "a bounded tanh and binary-softmax head preserve the gap up
to an absolute constant"; full version: proof of `thm:attentionpositionlower`
(attention_primitives.tex). -/
theorem tanh_sub_ge {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hab : a ≤ b) :
    (b - a) / 4 ≤ tanh b - tanh a := by
  have hca : cosh a < 2 :=
    lt_of_le_of_lt (Real.cosh_le_cosh.mpr (by rwa [abs_one])) cosh_one_lt_two
  have hcb : cosh b < 2 :=
    lt_of_le_of_lt (Real.cosh_le_cosh.mpr (by rwa [abs_one])) cosh_one_lt_two
  have hpa := Real.cosh_pos a
  have hpb := Real.cosh_pos b
  have hid : tanh b - tanh a = sinh (b - a) / (cosh a * cosh b) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Real.sinh_sub]
    field_simp
  have hs : b - a ≤ sinh (b - a) := Real.self_le_sinh_iff.mpr (by linarith)
  have hprod : cosh a * cosh b ≤ 4 := by nlinarith
  rw [hid, div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith

/-- The convex residual gate `g(u) = (1 - α) u + α tanh u` of the full-version head. -/
noncomputable def gate (α u : ℝ) : ℝ := (1 - α) * u + α * tanh u

/-- The gate increases at rate at least `1/4` on `[-1, 1]`. Paper: the search obstruction
paragraph in `sec:conf-scalar` (conference.tex); full version: proof of
`thm:attentionpositionlower` (attention_primitives.tex), `(1-α) + α sech² u ≥ 1/4`. -/
theorem gate_sub_ge {α a b : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hab : a ≤ b) : (b - a) / 4 ≤ gate α b - gate α a := by
  unfold gate
  have := tanh_sub_ge ha hb hab
  nlinarith

/-- The gate maps `[-1, 1]` into itself. Auxiliary for `thm:attentionpositionlower`
(attention_primitives.tex). -/
theorem abs_gate_le {α u : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hu : |u| ≤ 1) : |gate α u| ≤ 1 := by
  unfold gate
  have ht := (abs_tanh_lt_one u).le
  calc |(1 - α) * u + α * tanh u| ≤ |(1 - α) * u| + |α * tanh u| := abs_add_le _ _
    _ = (1 - α) * |u| + α * |tanh u| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - α), abs_of_nonneg hα0]
    _ ≤ (1 - α) * 1 + α * 1 := by gcongr
    _ = 1 := by ring

/-- The stream value `U(x) = (1 - α) x_last + α Y(x)` at the query position `last`. Full version:
`eq:binaryattentionfamily` (attention_primitives.tex). -/
noncomputable def headU {T : ℕ} (α A : ℝ) (last : Fin T) (x : Fin T → ℝ) : ℝ :=
  (1 - α) * x last + α * attnMean A x

/-- The token-one probability `P(x) = (1 + tanh Z(x))/2` with `Z = (1 - α) U + α tanh U`. Full
version: `eq:binaryattentiontoken` (attention_primitives.tex). -/
noncomputable def headP {T : ℕ} (α A : ℝ) (last : Fin T) (x : Fin T → ℝ) : ℝ :=
  (1 + tanh (gate α (headU α A last x))) / 2

/-- The head preserves the attention gap: flipping coordinate `j` of the all-negative context
raises the token-one probability by at least `(α p + (1 - α) [j = last]) / 16`, where
`p = e^{2A} / (T - 1 + e^{2A})`. Paper: the search obstruction paragraph in `sec:conf-scalar`
(conference.tex), "a bounded tanh and binary-softmax head preserve the gap up to an absolute
constant; a convex residual gate multiplies it by its weight `α`"; full version: proof of
`thm:attentionpositionlower` (attention_primitives.tex). -/
theorem head_gap {T : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (A : ℝ) (last j : Fin T) :
    (α * (exp (2 * A) / (T - 1 + exp (2 * A))) + (1 - α) * (if j = last then 1 else 0)) / 16
      ≤ headP α A last (flipCtx j) - headP α A last (negCtx T) := by
  set p := exp (2 * A) / (T - 1 + exp (2 * A)) with hp
  have hT : (1 : ℝ) ≤ T := by
    have : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact j.elim0)
    exact_mod_cast this
  have hp0 : 0 ≤ p := by have := exp_pos (2 * A); positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one (by linarith [exp_pos (2 * A)])]; linarith
  have hU0 : headU α A last (negCtx T) = -1 := by
    unfold headU
    rw [(negCtx_mass (Fin.pos j) A).2]
    simp only [negCtx]
    ring
  have hlast : flipCtx j last = if j = last then 1 else -1 := by
    by_cases h : j = last
    · subst h; simp [flipCtx]
    · rw [← flipCtx_agree j last (Ne.symm h)]; simp [h, negCtx]
  have hU1 : headU α A last (flipCtx j)
      = -1 + 2 * α * p + 2 * (1 - α) * (if j = last then 1 else 0) := by
    unfold headU
    rw [(flipCtx_mass j A).2, hlast, ← hp]
    split_ifs <;> ring
  have hind0 : (0 : ℝ) ≤ if j = last then 1 else 0 := by split_ifs <;> norm_num
  have hind1 : (if j = last then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hUb : |headU α A last (flipCtx j)| ≤ 1 := by
    rw [hU1, abs_le]
    constructor <;> split_ifs <;> nlinarith
  have hUa : |headU α A last (negCtx T)| ≤ 1 := by rw [hU0]; norm_num
  have hle : headU α A last (negCtx T) ≤ headU α A last (flipCtx j) := by
    rw [hU0, hU1]; nlinarith
  have hg := gate_sub_ge hα0 hα1 hUa hUb hle
  have hgle : gate α (headU α A last (negCtx T)) ≤ gate α (headU α A last (flipCtx j)) := by
    linarith
  have ht := tanh_sub_ge (abs_gate_le hα0 hα1 hUa) (abs_gate_le hα0 hα1 hUb) hgle
  unfold headP
  rw [hU0, hU1] at hg
  rw [hU0] at ht ⊢
  rw [hU1] at ht ⊢
  nlinarith

open scoped Classical in
/-- The positional lower bound for the one-block head. If `M` samples the token exactly on every
sign context (it outputs `true` with probability `P(x)`), then on the all-negative context its
expected number of distinct probes is at least `((1 - α) + α T p) / 16`, which is at least
`(1 + α min{T, e^{2A}}) / 64`. Paper: the search obstruction paragraph in `sec:conf-scalar`
(conference.tex); full version: `thm:attentionpositionlower`, `eq:attentionpositionlower`
(attention_primitives.tex). -/
theorem head_lower_bound [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : ℕ} (hT : 1 ≤ T) {A α : ℝ} (hA : 0 ≤ A) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (last : Fin T)
    (M : QueryAlg Ω (Fin T) ℝ Bool)
    (hexact : ∀ x : Fin T → ℝ, (∀ j, x j = 1 ∨ x j = -1) →
      μ {ω | ∃ y ∈ ({true} : Set Bool), Outputs M x ω y} = ENNReal.ofReal (headP α A last x))
    (hmeas : ∀ i, MeasurableSet {ω | Reads M (negCtx T) ω i}) :
    (1 + α * min (T : ℝ) (exp (2 * A))) / 64
        ≤ ((1 - α) + α * T * (exp (2 * A) / (T - 1 + exp (2 * A)))) / 16 ∧
      ENNReal.ofReal (((1 - α) + α * T * (exp (2 * A) / (T - 1 + exp (2 * A)))) / 16)
        ≤ ∫⁻ ω, ((Finset.univ.filter (fun i => Reads M (negCtx T) ω i)).card : ℝ≥0∞) ∂μ := by
  set p := exp (2 * A) / (T - 1 + exp (2 * A)) with hp
  have hneg : ∀ j, negCtx T j = 1 ∨ negCtx T j = -1 := fun j => Or.inr rfl
  have hflip : ∀ (i : Fin T) j, flipCtx i j = 1 ∨ flipCtx i j = -1 := by
    intro i j
    by_cases h : j = i
    · subst h; left; simp [flipCtx]
    · right; rw [← flipCtx_agree i j h]; rfl
  have hP0 : ∀ x, 0 ≤ headP α A last x := fun x => by
    unfold headP; linarith [neg_one_lt_tanh (gate α (headU α A last x))]
  have hread : ∀ i, (α * p + (1 - α) * (if i = last then 1 else 0)) / 16
      ≤ μ.real {ω | Reads M (negCtx T) ω i} := by
    intro i
    have h1 := hexact (negCtx T) hneg
    have h2 := hexact (flipCtx i) (hflip i)
    have htv := tv_le_read μ M (flipCtx_agree i) {true} h1 h2 (hP0 _) (hP0 _)
    have hgap := head_gap hα0 hα1 A last i
    rw [abs_sub_comm] at htv
    exact hgap.trans ((le_abs_self _).trans htv)
  constructor
  · have hmin := min_le_sum_tv hT hA
    rw [← hp] at hmin
    have hM : 1 ≤ min (T : ℝ) (exp (2 * A)) :=
      le_min (by exact_mod_cast hT) (one_le_exp (by linarith))
    nlinarith
  · rw [lintegral_card_reads μ M (negCtx T) hmeas]
    have hsum : ENNReal.ofReal (∑ i : Fin T, μ.real {ω | Reads M (negCtx T) ω i})
        = ∑ i, μ {ω | Reads M (negCtx T) ω i} := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => measureReal_nonneg)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
    rw [← hsum]
    apply ENNReal.ofReal_le_ofReal
    have hlast_sum : ∑ i : Fin T, (if i = last then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_ite_eq' Finset.univ last]; simp
    have hs1 : ∑ _i : Fin T, α * p = α * T * p := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    have hs2 : ∑ i : Fin T, (1 - α) * (if i = last then (1 : ℝ) else 0) = 1 - α := by
      rw [← Finset.mul_sum, hlast_sum, mul_one]
    calc ((1 - α) + α * T * p) / 16
        = ∑ i : Fin T, (α * p + (1 - α) * (if i = last then 1 else 0)) / 16 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, hs1, hs2]
          ring
      _ ≤ ∑ i : Fin T, μ.real {ω | Reads M (negCtx T) ω i} :=
          Finset.sum_le_sum fun i _ => hread i

end ExactSampling.SearchObstruction
