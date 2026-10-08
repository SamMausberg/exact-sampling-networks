import Mathlib

/-!
# Query lower bounds from transcripts and couplings

Paper files and results covered:
* tanh_lower.tex (`sec:lower`): `lem:transcript`, `eq:tanhlower`, `eq:chainlower`,
  `eq:derivativelower`, the three bounds of `thm:lower` (`eq:lowerexact`, `eq:lowersuper`,
  `eq:lowercritical`, stated in tanh_model.tex), `eq:dyadicgain`, `eq:windowexplicit` and the
  lower side of `cor:window`, and `prop:evaluation`;
* tanh_mean.tex: the reciprocal-square inequality behind `eq:chainrange`, `eq:chainrange`,
  `eq:balancedinfluence`, and the lower bounds of `thm:finitejoint` and `thm:finitecritical`;
* exact_sampling_networks.tex: `eq:main-information`, `eq:main-coupling`, and the `Ω(√D)`
  probe lower bound in `thm:main-depth`;
* instance_information.tex: `lem:multivariate-transcript` (`eq:multivariate-information`,
  `eq:multivariate-curvature`), `eq:instance-certificate`, the
  probe-cost statements of `prop:magnitude-obstruction` and `prop:profile-obstruction`;
* instance_hardness.tex: the parity cost gap used in `prop:instance-hardness-eight` and
  `thm:instance-hardness`;
* attention_primitives.tex and main_attention.tex: `lem:attentioncoupling` and
  `thm:attentionpositionlower` (the lower half of `eq:main-binary-law` in
  `thm:main-attention`);
* tanh_new_critical.tex: `cor:new-integer-score` for finite transcripts. The specialization to
  `G_r(z) = tanh(rz)/tanh r` needs factories with finite expected work
  (`lem:new-finite-score`, not formalized): `G_r` is not a polynomial, so no finite mixture of
  decision trees samples it exactly.

## Model

A randomized query algorithm on `m` sign inputs is a `Sampler`: a finite mixture of
deterministic decision trees. The index of the mixture is the class of the random tape
(preprocessing and online randomness together), and the leaf value of a tree is the conditional
mean of the returned sign at that leaf; leaves in `{-1,1}` are the special case of a sampler
that returns a sign deterministically at a leaf. For the numerical evaluators of
`prop:evaluation`, the leaf value is instead the returned number, and the tapes are grouped by
tree together with the set of contexts answered correctly. Queries along a path are to distinct
coordinates (`NoRepeat`); this is no restriction, since answering repeated queries from a cache
gives a sampler with the same output law and the same distinct probes (`Sampler.prune_spec`).
The cost `Sampler.cost x` is `E[Q | x]`, the expected number of distinct probes on input `x`.
Unused input coordinates are fixed, so inputs range over the relevant coordinates only.
Product laws `∏ᵢ (1 + sᵢ xᵢ)/2` are finite sums over `{-1,1}^m`.

The paper's reduction from an almost surely terminating algorithm with an infinite random tape
to such a mixture (fix the tape, collapse computation between distinct probes into a decision
tree of depth at most `m`, and group tapes by tree) is the modelling step and is not formalized
here. Within the model all statements are proved without further assumptions: the transcript
identities, both transcript inequalities, the coupling inequality, and the complete lower-bound
chains of `thm:lower`, `cor:window`, `prop:evaluation`, `thm:finitejoint`,
`thm:finitecritical` and `thm:attentionpositionlower`.

## Not formalized here

* The tape-to-mixture reduction above, and the bit-complexity cost model: only distinct input
  probes are counted, which is the quantity bounded in the paper's lower bounds.
* The matching upper bounds that complete `cor:window`, `cor:threshold`, `prop:evaluation`,
  `thm:finitejoint`, `thm:finitecritical` and `thm:main-depth`.
* The realization of the mean chain and of the attention family as legal networks on the
  parameter grid (see `ExactSampling.WeightObstructions` for the network constructions of
  `prop:magnitude-obstruction` and `prop:profile-obstruction`).
* The finite-mean extension `lem:new-finite-score` of the integer score bound.
-/

namespace ExactSampling.TranscriptLowerBounds

open Finset

noncomputable section

/-! ## Sign inputs and product laws -/

/-- The sign `±1` encoded by a Boolean input bit (`true ↦ 1`, `false ↦ -1`). -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- `sgn true = 1`. -/
@[simp] lemma sgn_true : sgn true = 1 := rfl
/-- `sgn false = -1`. -/
@[simp] lemma sgn_false : sgn false = -1 := rfl

/-- Negating a bit negates its sign. Auxiliary for the pairing arguments in the proofs of
`prop:evaluation` (tanh_lower.tex) and `prop:instance-hardness-eight` (instance_hardness.tex). -/
lemma sgn_not (b : Bool) : sgn (!b) = -sgn b := by cases b <;> simp [sgn]

/-- Signs square to one. Auxiliary for `lem:transcript` (tanh_lower.tex). -/
lemma sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by cases b <;> norm_num [sgn]

/-- Signs have absolute value one. Auxiliary for `lem:transcript` (tanh_lower.tex). -/
lemma abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> norm_num [sgn]

variable {m : ℕ}

/-- Weight of the input `x` under the product law with mean vector `s`:
`∏ᵢ (1 + sᵢ xᵢ) / 2`. For `s ∈ [-1,1]^m` this is a probability law on `{-1,1}^m`. -/
def prodLaw (s : Fin m → ℝ) (x : Fin m → Bool) : ℝ :=
  ∏ i, (1 + s i * sgn (x i)) / 2

/-- Expectation of `g` under the product law with mean vector `s`. -/
def prodExp (s : Fin m → ℝ) (g : (Fin m → Bool) → ℝ) : ℝ :=
  ∑ x, prodLaw s x * g x

/-- Product weights are nonnegative on `[-1,1]^m`. Auxiliary for the transcript identities in
the proof of `lem:transcript` (tanh_lower.tex) and `lem:multivariate-transcript`
(instance_information.tex). -/
lemma prodLaw_nonneg {s : Fin m → ℝ} (hs : ∀ i, |s i| ≤ 1) (x : Fin m → Bool) :
    0 ≤ prodLaw s x := by
  unfold prodLaw
  refine Finset.prod_nonneg fun i _ => ?_
  have h1 := abs_le.mp (hs i)
  have h2 : |s i * sgn (x i)| ≤ 1 := by rw [abs_mul, abs_sgn, mul_one]; exact hs i
  have h3 := abs_le.mp h2
  linarith [h3.1]

/-- Product weights sum to one, for every real mean vector. Auxiliary for the transcript
identities in the proof of `lem:transcript` (tanh_lower.tex) and `lem:multivariate-transcript`
(instance_information.tex). -/
lemma sum_prodLaw (s : Fin m → ℝ) : ∑ x, prodLaw s x = 1 := by
  classical
  unfold prodLaw
  rw [← Fintype.prod_sum (fun i (b : Bool) => (1 + s i * sgn b) / 2)]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Fintype.sum_bool]
  simp [sgn]
  ring

/-- Expectation of a constant. Auxiliary for the transcript identities in the proof of
`lem:transcript` (tanh_lower.tex) and `lem:multivariate-transcript` (instance_information.tex). -/
lemma prodExp_const (s : Fin m → ℝ) (c : ℝ) : prodExp s (fun _ => c) = c := by
  unfold prodExp
  rw [← Finset.sum_mul, sum_prodLaw, one_mul]

/-- Additivity of the product-law expectation. Auxiliary for the transcript identities in the
proof of `lem:transcript` (tanh_lower.tex) and `lem:multivariate-transcript`
(instance_information.tex). -/
lemma prodExp_add (s : Fin m → ℝ) (g₁ g₂ : (Fin m → Bool) → ℝ) :
    prodExp s (fun x => g₁ x + g₂ x) = prodExp s g₁ + prodExp s g₂ := by
  unfold prodExp
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- Homogeneity of the product-law expectation. Auxiliary for the transcript identities in the
proof of `lem:transcript` (tanh_lower.tex) and `lem:multivariate-transcript`
(instance_information.tex). -/
lemma prodExp_mul_const (s : Fin m → ℝ) (c : ℝ) (g : (Fin m → Bool) → ℝ) :
    prodExp s (fun x => c * g x) = c * prodExp s g := by
  unfold prodExp
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- Expectation of a finite sum. Auxiliary for the transcript identities in the proof of
`lem:transcript` (tanh_lower.tex) and `lem:multivariate-transcript` (instance_information.tex). -/
lemma prodExp_sum {κ : Type*} (t : Finset κ) (s : Fin m → ℝ)
    (g : κ → (Fin m → Bool) → ℝ) :
    prodExp s (fun x => ∑ k ∈ t, g k x) = ∑ k ∈ t, prodExp s (g k) := by
  unfold prodExp
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-- Monotonicity of the product-law expectation. Auxiliary for the transcript identities in the
proof of `lem:transcript` (tanh_lower.tex) and `lem:multivariate-transcript`
(instance_information.tex). -/
lemma prodExp_mono {s : Fin m → ℝ} (hs : ∀ i, |s i| ≤ 1) {g₁ g₂ : (Fin m → Bool) → ℝ}
    (h : ∀ x, g₁ x ≤ g₂ x) : prodExp s g₁ ≤ prodExp s g₂ :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (prodLaw_nonneg hs x)

/-- An average under a product law is at most the largest value. Paper: "an average over
contexts is at most their maximum", proof of `thm:lower` (tanh_lower.tex). -/
lemma exists_ge_prodExp {s : Fin m → ℝ} (hs : ∀ i, |s i| ≤ 1) (g : (Fin m → Bool) → ℝ) :
    ∃ x, prodExp s g ≤ g x := by
  obtain ⟨x, -, hx⟩ := Finset.exists_max_image Finset.univ g Finset.univ_nonempty
  refine ⟨x, ?_⟩
  calc prodExp s g ≤ prodExp s (fun _ => g x) :=
        prodExp_mono hs fun y => hx y (Finset.mem_univ y)
    _ = g x := prodExp_const s (g x)

/-- Flip the input bit `i`. -/
def flipAt (i : Fin m) (x : Fin m → Bool) : Fin m → Bool := Function.update x i (!x i)

/-- Flipping a bit twice is the identity. Auxiliary for the coupling and pairing arguments
(`eq:main-coupling`, exact_sampling_networks.tex). -/
lemma flipAt_flipAt (i : Fin m) (x : Fin m → Bool) : flipAt i (flipAt i x) = x := by
  unfold flipAt
  rw [Function.update_idem, Function.update_self, Bool.not_not, Function.update_eq_self]

/-- Flipping bit `i`, as a permutation of the inputs. -/
def flipPerm (i : Fin m) : Equiv.Perm (Fin m → Bool) :=
  Function.Involutive.toPerm (flipAt i) (flipAt_flipAt i)

/-- The flip permutation acts by `flipAt`. -/
@[simp] lemma flipPerm_apply (i : Fin m) (x : Fin m → Bool) : flipPerm i x = flipAt i x := rfl

/-- The flipped bit. Auxiliary for the coupling and pairing arguments (`eq:main-coupling`,
exact_sampling_networks.tex). -/
lemma flipAt_self (i : Fin m) (x : Fin m → Bool) : flipAt i x i = !x i := by
  simp [flipAt]

/-- Other bits are unchanged by a flip. Auxiliary for the coupling and pairing arguments
(`eq:main-coupling`, exact_sampling_networks.tex). -/
lemma flipAt_ne {i j : Fin m} (h : j ≠ i) (x : Fin m → Bool) : flipAt i x j = x j := by
  simp [flipAt, Function.update_of_ne h]

/-- Splitting a product-law expectation on one coordinate. If `g₁` and `g₂` do not depend on
coordinate `i`, branching on `xᵢ` averages them with weights `(1 ± sᵢ)/2`. Auxiliary for the
decision-tree reduction in the proof of `lem:transcript` (tanh_lower.tex). -/
lemma prodExp_ite (s : Fin m → ℝ) (i : Fin m) (g₁ g₂ : (Fin m → Bool) → ℝ)
    (h₁ : ∀ x b, g₁ (Function.update x i b) = g₁ x)
    (h₂ : ∀ x b, g₂ (Function.update x i b) = g₂ x) :
    prodExp s (fun x => if x i then g₁ x else g₂ x) =
      (1 + s i) / 2 * prodExp s g₁ + (1 - s i) / 2 * prodExp s g₂ := by
  classical
  set c : Bool → ℝ := fun b => (1 + s i * sgn b) / 2 with hc
  set ρ : (Fin m → Bool) → ℝ :=
    fun x => ∏ j ∈ Finset.univ.erase i, (1 + s j * sgn (x j)) / 2 with hρ
  have hμ : ∀ x, prodLaw s x = c (x i) * ρ x := fun x =>
    (Finset.mul_prod_erase Finset.univ (fun j => (1 + s j * sgn (x j)) / 2)
      (Finset.mem_univ i)).symm
  have hρflip : ∀ x, ρ (flipAt i x) = ρ x := fun x =>
    Finset.prod_congr rfl fun j hj => by
      rw [flipAt_ne (Finset.ne_of_mem_erase hj)]
  have hcsum : ∀ b, c b + c (!b) = 1 := fun b => by
    cases b <;> simp [hc, sgn] <;> ring
  -- pairing: the full average equals the `ρ`-weighted sum over one half
  have hpair : ∀ (ψ : (Fin m → Bool) → ℝ), (∀ x, ψ (flipAt i x) = ψ x) → ∀ b₀,
      ∑ x, prodLaw s x * ψ x = ∑ x, (if x i = b₀ then ρ x * ψ x else 0) := by
    intro ψ hψ b₀
    have hsplit : ∀ x, prodLaw s x * ψ x =
        (if x i = b₀ then c b₀ * (ρ x * ψ x) else 0) +
          (if x i = b₀ then 0 else c (!b₀) * (ρ x * ψ x)) := by
      intro x
      rw [hμ]
      by_cases hx : x i = b₀
      · simp [hx]; ring
      · have : x i = !b₀ := by cases h : x i <;> cases b₀ <;> simp_all
        simp [this]; ring
    have hre : ∑ x, (if x i = b₀ then 0 else c (!b₀) * (ρ x * ψ x)) =
        ∑ x, (if x i = b₀ then c (!b₀) * (ρ x * ψ x) else 0) := by
      rw [← Equiv.sum_comp (flipPerm i)]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [flipPerm_apply, flipAt_self, hρflip, hψ]
      by_cases hx : x i = b₀
      · simp [hx]
      · have : (!x i) = b₀ := by cases h : x i <;> cases b₀ <;> simp_all
        simp [hx, this]
    rw [Finset.sum_congr rfl fun x _ => hsplit x, Finset.sum_add_distrib, hre,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x i = b₀
    · simp only [hx, ite_true]
      rw [← add_mul, hcsum, one_mul]
    · simp [hx]
  have hind : ∀ (g : (Fin m → Bool) → ℝ), (∀ x b, g (Function.update x i b) = g x) →
      ∀ b₀, ∑ x, prodLaw s x * (if x i = b₀ then g x else 0) =
        c b₀ * ∑ x, prodLaw s x * g x := by
    intro g hg b₀
    have hgflip : ∀ x, g (flipAt i x) = g x := fun x => by
      unfold flipAt; rw [hg]
    rw [hpair g hgflip b₀, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hμ]
    by_cases hx : x i = b₀
    · simp only [hx, ite_true]; ring
    · simp [hx]
  have hdecomp : ∀ x, (if x i then g₁ x else g₂ x) =
      (if x i = true then g₁ x else 0) + (if x i = false then g₂ x else 0) := by
    intro x; cases x i <;> simp
  unfold prodExp
  simp_rw [hdecomp, mul_add]
  rw [Finset.sum_add_distrib, hind g₁ h₁ true, hind g₂ h₂ false]
  simp only [hc, sgn_true, sgn_false]
  ring

/-! ## Decision trees -/

/-- A deterministic decision tree on `m` sign inputs. A node queries coordinate `i` and
continues in `pos` if `xᵢ = 1` and in `neg` if `xᵢ = -1`; a leaf returns a real value, which
for a sign sampler is the conditional mean of the returned sign. -/
inductive DTree (m : ℕ) : Type
  | leaf (y : ℝ) : DTree m
  | node (i : Fin m) (pos neg : DTree m) : DTree m

namespace DTree

/-- Leaf value reached on input `x`. -/
def out : DTree m → (Fin m → Bool) → ℝ
  | leaf y, _ => y
  | node i T₁ T₂, x => if x i then out T₁ x else out T₂ x

/-- The set of coordinates queried along the path of input `x`. -/
def path : DTree m → (Fin m → Bool) → Finset (Fin m)
  | leaf _, _ => ∅
  | node i T₁ T₂, x => insert i (if x i then path T₁ x else path T₂ x)

/-- All coordinates queried anywhere in the tree. -/
def queried : DTree m → Finset (Fin m)
  | leaf _ => ∅
  | node i T₁ T₂ => insert i (queried T₁ ∪ queried T₂)

/-- No coordinate is queried twice along a path. Repeated queries can be answered from a cache,
so this is no restriction for counting distinct probes. -/
def NoRepeat : DTree m → Prop
  | leaf _ => True
  | node i T₁ T₂ => i ∉ queried T₁ ∧ i ∉ queried T₂ ∧ NoRepeat T₁ ∧ NoRepeat T₂

/-- All leaf values lie in `[-1,1]`. -/
def Bounded : DTree m → Prop
  | leaf y => |y| ≤ 1
  | node _ T₁ T₂ => Bounded T₁ ∧ Bounded T₂

/-- Bounded leaves give bounded outputs. Auxiliary for `lem:transcript` and `eq:main-coupling`. -/
lemma abs_out_le {T : DTree m} (hT : T.Bounded) (x : Fin m → Bool) : |T.out x| ≤ 1 := by
  induction T with
  | leaf y => exact hT
  | node i T₁ T₂ ih₁ ih₂ =>
    simp only [out]
    split
    · exact ih₁ hT.1
    · exact ih₂ hT.2

/-- The coordinates read on a path are queried by the tree. Auxiliary for the decision-tree
reduction in the proof of `lem:transcript` (tanh_lower.tex). -/
lemma path_subset (T : DTree m) (x : Fin m → Bool) : T.path x ⊆ T.queried := by
  induction T with
  | leaf y => simp [path]
  | node i T₁ T₂ ih₁ ih₂ =>
    simp only [path, queried]
    split
    · exact Finset.insert_subset_insert _ (ih₁.trans Finset.subset_union_left)
    · exact Finset.insert_subset_insert _ (ih₂.trans Finset.subset_union_right)

/-- A coordinate never queried by the tree does not affect its output. Auxiliary for the
decision-tree reduction in the proof of `lem:transcript` (tanh_lower.tex). -/
lemma out_update_of_not_mem {T : DTree m} {i : Fin m} (h : i ∉ T.queried)
    (x : Fin m → Bool) (b : Bool) : T.out (Function.update x i b) = T.out x := by
  induction T with
  | leaf y => rfl
  | node j T₁ T₂ ih₁ ih₂ =>
    simp only [queried, Finset.mem_insert, Finset.mem_union, not_or] at h
    have hji : j ≠ i := fun e => h.1 e.symm
    simp only [out, Function.update_of_ne hji, ih₁ h.2.1, ih₂ h.2.2]

/-- A coordinate never queried by the tree does not affect its paths. Auxiliary for the
decision-tree reduction in the proof of `lem:transcript` (tanh_lower.tex). -/
lemma path_update_of_not_mem {T : DTree m} {i : Fin m} (h : i ∉ T.queried)
    (x : Fin m → Bool) (b : Bool) : T.path (Function.update x i b) = T.path x := by
  induction T with
  | leaf y => rfl
  | node j T₁ T₂ ih₁ ih₂ =>
    simp only [queried, Finset.mem_insert, Finset.mem_union, not_or] at h
    have hji : j ≠ i := fun e => h.1 e.symm
    simp only [path, Function.update_of_ne hji, ih₁ h.2.1, ih₂ h.2.2]

/-- If coordinate `i` is not read on the path of `x`, changing it does not change the
transcript: the path and the leaf are the same. Paper: proof of `lem:attentioncoupling`
(attention_primitives.tex), "the transcripts agree until coordinate `j` is queried". -/
lemma out_path_update_of_not_mem_path {T : DTree m} {i : Fin m} {x : Fin m → Bool}
    (h : i ∉ T.path x) (b : Bool) :
    T.out (Function.update x i b) = T.out x ∧ T.path (Function.update x i b) = T.path x := by
  induction T with
  | leaf y => exact ⟨rfl, rfl⟩
  | node j T₁ T₂ ih₁ ih₂ =>
    simp only [path, Finset.mem_insert, not_or] at h
    have hji : j ≠ i := fun e => h.1 e.symm
    simp only [out, path, Function.update_of_ne hji]
    cases hx : x j
    · simp only [hx, Bool.false_eq_true, ite_false] at h ⊢
      obtain ⟨h1, h2⟩ := ih₂ h.2
      exact ⟨h1, by rw [h2]⟩
    · simp only [hx, ite_true] at h ⊢
      obtain ⟨h1, h2⟩ := ih₁ h.2
      exact ⟨h1, by rw [h2]⟩

/-! ### Recursive averages over the leaves -/

/-- Mean output under the product law with means `s`, computed along the tree. -/
def rH (s : Fin m → ℝ) : DTree m → ℝ
  | leaf y => y
  | node i T₁ T₂ => (1 + s i) / 2 * rH s T₁ + (1 - s i) / 2 * rH s T₂

/-- Mean squared output along the tree. -/
def rY2 (s : Fin m → ℝ) : DTree m → ℝ
  | leaf y => y ^ 2
  | node i T₁ T₂ => (1 + s i) / 2 * rY2 s T₁ + (1 - s i) / 2 * rY2 s T₂

/-- Mean of `∑_{queried i} wᵢ` along the tree. -/
def rW (s w : Fin m → ℝ) : DTree m → ℝ
  | leaf _ => 0
  | node i T₁ T₂ => w i + ((1 + s i) / 2 * rW s w T₁ + (1 - s i) / 2 * rW s w T₂)

/-- First directional derivative (in direction `v`) of `rH`, computed along the tree. -/
def D1 (s v : Fin m → ℝ) : DTree m → ℝ
  | leaf _ => 0
  | node i T₁ T₂ => v i / 2 * (rH s T₁ - rH s T₂) +
      ((1 + s i) / 2 * D1 s v T₁ + (1 - s i) / 2 * D1 s v T₂)

/-- Second directional derivative (in direction `v`) of `rH`, computed along the tree. -/
def D2 (s v : Fin m → ℝ) : DTree m → ℝ
  | leaf _ => 0
  | node i T₁ T₂ => v i * (D1 s v T₁ - D1 s v T₂) +
      ((1 + s i) / 2 * D2 s v T₁ + (1 - s i) / 2 * D2 s v T₂)

/-- Law of total expectation along a decision tree: the product-law mean of the leaf value
equals the recursive average. Paper: leaf likelihoods in the proof of `lem:transcript`
(tanh_lower.tex). -/
lemma prodExp_out {T : DTree m} (hT : T.NoRepeat) (s : Fin m → ℝ) :
    prodExp s T.out = T.rH s := by
  induction T with
  | leaf y => exact prodExp_const s y
  | node i T₁ T₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂, hn₁, hn₂⟩ := hT
    change prodExp s (fun x => if x i then T₁.out x else T₂.out x) = _
    rw [prodExp_ite s i _ _ (fun x b => out_update_of_not_mem h₁ x b)
      (fun x b => out_update_of_not_mem h₂ x b), ih₁ hn₁, ih₂ hn₂]
    rfl

/-- Law of total expectation for weighted query counts. Auxiliary for `E_t Z² = E_t A = E_t Q/(1
- t²)` in the proof of `lem:transcript` (tanh_lower.tex). -/
lemma prodExp_path_sum {T : DTree m} (hT : T.NoRepeat) (s w : Fin m → ℝ) :
    prodExp s (fun x => ∑ j ∈ T.path x, w j) = T.rW s w := by
  induction T with
  | leaf y => simp [path, rW, prodExp_const]
  | node i T₁ T₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂, hn₁, hn₂⟩ := hT
    have hrw : ∀ x, ∑ j ∈ (node i T₁ T₂).path x, w j =
        w i + (if x i then ∑ j ∈ T₁.path x, w j else ∑ j ∈ T₂.path x, w j) := by
      intro x
      simp only [path]
      split
      · rw [Finset.sum_insert fun hm => h₁ (path_subset T₁ x hm)]
      · rw [Finset.sum_insert fun hm => h₂ (path_subset T₂ x hm)]
    simp_rw [hrw]
    rw [prodExp_add, prodExp_const, prodExp_ite s i _ _
      (fun x b => by rw [path_update_of_not_mem h₁])
      (fun x b => by rw [path_update_of_not_mem h₂]), ih₁ hn₁, ih₂ hn₂]
    rfl

/-! ### Differentiating along a direction -/

/-- The output mean along a line is differentiable with derivative `D1`. Paper: leaf
differentiation in the proof of `lem:transcript` (tanh_lower.tex). -/
lemma hasDerivAt_rH (T : DTree m) (s v : Fin m → ℝ) (u : ℝ) :
    HasDerivAt (fun u => T.rH (s + u • v)) (T.D1 (s + u • v) v) u := by
  induction T with
  | leaf y => exact hasDerivAt_const u y
  | node i T₁ T₂ ih₁ ih₂ =>
    have hsi : HasDerivAt (fun u => (s + u • v) i) (v i) u := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      simpa using (hasDerivAt_mul_const (v i)).const_add (s i)
    have hp : HasDerivAt (fun u => (1 + (s + u • v) i) / 2) (v i / 2) u :=
      (hsi.const_add 1).div_const 2
    have hm : HasDerivAt (fun u => (1 - (s + u • v) i) / 2) (-v i / 2) u :=
      (hsi.const_sub 1).div_const 2
    refine ((hp.mul ih₁).add (hm.mul ih₂)).congr_deriv ?_
    simp only [D1]
    ring

/-- Differentiating the first directional derivative once more along the line. Leaf
differentiation in the proof of `lem:transcript` (tanh_lower.tex). -/
lemma hasDerivAt_D1 (T : DTree m) (s v : Fin m → ℝ) (u : ℝ) :
    HasDerivAt (fun u => T.D1 (s + u • v) v) (T.D2 (s + u • v) v) u := by
  induction T with
  | leaf y => exact hasDerivAt_const u 0
  | node i T₁ T₂ ih₁ ih₂ =>
    have hsi : HasDerivAt (fun u => (s + u • v) i) (v i) u := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      simpa using (hasDerivAt_mul_const (v i)).const_add (s i)
    have hp : HasDerivAt (fun u => (1 + (s + u • v) i) / 2) (v i / 2) u :=
      (hsi.const_add 1).div_const 2
    have hm : HasDerivAt (fun u => (1 - (s + u • v) i) / 2) (-v i / 2) u :=
      (hsi.const_sub 1).div_const 2
    have hH := ((hasDerivAt_rH T₁ s v u).sub (hasDerivAt_rH T₂ s v u)).const_mul (v i / 2)
    refine (hH.add ((hp.mul ih₁).add (hm.mul ih₂))).congr_deriv ?_
    simp only [D2]
    ring

/-! ### Transcript scores

`ev s v φ T z a` is the leaf average of `φ (Y, Z, A)`, where along the path the first score
`Z` and the observed information `A` start at `z`, `a` and a fresh coordinate `i` with answer
`xᵢ` adds `vᵢ xᵢ / (1 + sᵢ xᵢ)` to `Z` and its square to `A`. -/

/-- Leaf average of a function of the output, the score and the observed information. -/
def ev (s v : Fin m → ℝ) (φ : ℝ → ℝ → ℝ → ℝ) : DTree m → ℝ → ℝ → ℝ
  | leaf y, z, a => φ y z a
  | node i T₁ T₂, z, a =>
      (1 + s i) / 2 * ev s v φ T₁ (z + v i / (1 + s i)) (a + (v i / (1 + s i)) ^ 2) +
      (1 - s i) / 2 * ev s v φ T₂ (z - v i / (1 - s i)) (a + (v i / (1 - s i)) ^ 2)

/-- Additivity of the leaf average. Auxiliary for the transcript identities in the proof of
`lem:transcript` (tanh_lower.tex) and `lem:multivariate-transcript` (instance_information.tex). -/
lemma ev_add (s v : Fin m → ℝ) (φ ψ : ℝ → ℝ → ℝ → ℝ) (T : DTree m) (z a : ℝ) :
    ev s v (fun y z a => φ y z a + ψ y z a) T z a = ev s v φ T z a + ev s v ψ T z a := by
  induction T generalizing z a with
  | leaf y => rfl
  | node i T₁ T₂ ih₁ ih₂ => simp only [ev, ih₁, ih₂]; ring

/-- Homogeneity of the leaf average. Auxiliary for the transcript identities in the proof of
`lem:transcript` (tanh_lower.tex) and `lem:multivariate-transcript` (instance_information.tex). -/
lemma ev_const_mul (s v : Fin m → ℝ) (c : ℝ) (φ : ℝ → ℝ → ℝ → ℝ) (T : DTree m) (z a : ℝ) :
    ev s v (fun y z a => c * φ y z a) T z a = c * ev s v φ T z a := by
  induction T generalizing z a with
  | leaf y => rfl
  | node i T₁ T₂ ih₁ ih₂ => simp only [ev, ih₁, ih₂]; ring

/-- Positivity and monotonicity of the leaf average, under an invariant of the accumulated
score data that is preserved by each fresh query. Auxiliary for the Cauchy--Schwarz and
curvature steps of `lem:multivariate-transcript` (instance_information.tex). -/
lemma ev_mono {s v : Fin m → ℝ} (hs : ∀ i, |s i| ≤ 1) (P : ℝ → ℝ → Prop)
    (hP : ∀ i z a, P z a → P (z + v i / (1 + s i)) (a + (v i / (1 + s i)) ^ 2) ∧
      P (z - v i / (1 - s i)) (a + (v i / (1 - s i)) ^ 2))
    {φ ψ : ℝ → ℝ → ℝ → ℝ} (h : ∀ y z a, |y| ≤ 1 → P z a → φ y z a ≤ ψ y z a)
    {T : DTree m} (hT : T.Bounded) {z a : ℝ} (hza : P z a) :
    ev s v φ T z a ≤ ev s v ψ T z a := by
  induction T generalizing z a with
  | leaf y => exact h y z a hT hza
  | node i T₁ T₂ ih₁ ih₂ =>
    have h1 := abs_le.mp (hs i)
    have hp : 0 ≤ (1 + s i) / 2 := by linarith
    have hm : 0 ≤ (1 - s i) / 2 := by linarith
    obtain ⟨hP₁, hP₂⟩ := hP i z a hza
    simp only [ev]
    exact add_le_add (mul_le_mul_of_nonneg_left (ih₁ hT.1 hP₁) hp)
      (mul_le_mul_of_nonneg_left (ih₂ hT.2 hP₂) hm)

/-- Score data `(Z, A)` with `A ≥ 0`. Auxiliary for the curvature step of
`lem:multivariate-transcript` (instance_information.tex). -/
lemma nonneg_invariant (s v : Fin m → ℝ) (i : Fin m) (a : ℝ) (ha : 0 ≤ a) :
    0 ≤ a + (v i / (1 + s i)) ^ 2 ∧ 0 ≤ a + (v i / (1 - s i)) ^ 2 :=
  ⟨by positivity, by positivity⟩

section Identities

variable {s : Fin m → ℝ} (v : Fin m → ℝ)

/-- The weight `vᵢ² / (1 - sᵢ²)`: the conditional variance of a fresh score increment. -/
def infoWeight (s v : Fin m → ℝ) (i : Fin m) : ℝ := v i ^ 2 / (1 - s i ^ 2)

/-- The leaf weights sum to one. Auxiliary for the transcript identities in the proof of
`lem:transcript` (tanh_lower.tex) and `lem:multivariate-transcript` (instance_information.tex). -/
lemma ev_one (T : DTree m) (z a : ℝ) : ev s v (fun _ _ _ => 1) T z a = 1 := by
  induction T generalizing z a with
  | leaf y => rfl
  | node i T₁ T₂ ih₁ ih₂ => simp only [ev, ih₁, ih₂]; ring

/-- The leaf average of the output is the output mean `H`. Auxiliary for the transcript
identities in the proof of `lem:transcript` (tanh_lower.tex) and `lem:multivariate-transcript`
(instance_information.tex). -/
lemma ev_Y (T : DTree m) (z a : ℝ) : ev s v (fun y _ _ => y) T z a = T.rH s := by
  induction T generalizing z a with
  | leaf y => rfl
  | node i T₁ T₂ ih₁ ih₂ => simp only [ev, ih₁, ih₂, rH]

/-- The leaf average of the squared output. Auxiliary for the transcript identities in the proof
of `lem:transcript` (tanh_lower.tex) and `lem:multivariate-transcript`
(instance_information.tex). -/
lemma ev_Y2 (T : DTree m) (z a : ℝ) : ev s v (fun y _ _ => y ^ 2) T z a = T.rY2 s := by
  induction T generalizing z a with
  | leaf y => rfl
  | node i T₁ T₂ ih₁ ih₂ => simp only [ev, ih₁, ih₂, rY2]

variable (hs : ∀ i, |s i| < 1)
include hs

/-- `1 + sᵢ > 0` in the interior. Auxiliary for the transcript identities in the proof of
`lem:transcript` (tanh_lower.tex) and `lem:multivariate-transcript` (instance_information.tex). -/
lemma one_add_pos (i : Fin m) : 0 < 1 + s i := by
  have := abs_lt.mp (hs i); linarith

/-- `1 - sᵢ > 0` in the interior. Auxiliary for the transcript identities in the proof of
`lem:transcript` (tanh_lower.tex) and `lem:multivariate-transcript` (instance_information.tex). -/
lemma one_sub_pos (i : Fin m) : 0 < 1 - s i := by
  have := abs_lt.mp (hs i); linarith

/-- The score is a martingale: its leaf average is its initial value. Paper: `E Z = 0` in the
proof of `lem:multivariate-transcript` (instance_information.tex). -/
lemma ev_Z (T : DTree m) (z a : ℝ) : ev s v (fun _ z _ => z) T z a = z := by
  induction T generalizing z a with
  | leaf y => rfl
  | node i T₁ T₂ ih₁ ih₂ =>
    have h1 := (one_add_pos hs i).ne'
    have h2 := (one_sub_pos hs i).ne'
    simp only [ev, ih₁, ih₂]
    field_simp
    ring

/-- The observed information accumulates the conditional score variances. Paper: `E A = I_v` in
the proof of `lem:multivariate-transcript` (instance_information.tex). -/
lemma ev_A (T : DTree m) (z a : ℝ) :
    ev s v (fun _ _ a => a) T z a = a + T.rW s (infoWeight s v) := by
  induction T generalizing z a with
  | leaf y => simp [ev, rW]
  | node i T₁ T₂ ih₁ ih₂ =>
    have h1 := (one_add_pos hs i).ne'
    have h2 := (one_sub_pos hs i).ne'
    have h3 : (1 - s i ^ 2) ≠ 0 := by
      have : 1 - s i ^ 2 = (1 + s i) * (1 - s i) := by ring
      rw [this]; exact mul_ne_zero h1 h2
    simp only [ev, ih₁, ih₂, rW, infoWeight]
    field_simp
    ring

/-- Second moment of the stopped score (the stopped-martingale isometry). Paper: `E Z² = I_v` in
the proof of `lem:multivariate-transcript` (instance_information.tex). -/
lemma ev_Z2 (T : DTree m) (z a : ℝ) :
    ev s v (fun _ z _ => z ^ 2) T z a = z ^ 2 + T.rW s (infoWeight s v) := by
  induction T generalizing z a with
  | leaf y => simp [ev, rW]
  | node i T₁ T₂ ih₁ ih₂ =>
    have h1 := (one_add_pos hs i).ne'
    have h2 := (one_sub_pos hs i).ne'
    have h3 : (1 - s i ^ 2) ≠ 0 := by
      have : 1 - s i ^ 2 = (1 + s i) * (1 - s i) := by ring
      rw [this]; exact mul_ne_zero h1 h2
    simp only [ev, ih₁, ih₂, rW, infoWeight]
    field_simp
    ring

/-- Leaf differentiation, first order: `D1 = E[Y Z]`. Paper: `v · ∇𝓗 = E[Y Z]` in the proof of
`lem:multivariate-transcript` (instance_information.tex). -/
lemma ev_YZ (T : DTree m) (z a : ℝ) :
    ev s v (fun y z _ => y * z) T z a = z * T.rH s + T.D1 s v := by
  induction T generalizing z a with
  | leaf y => simp [ev, rH, D1, mul_comm]
  | node i T₁ T₂ ih₁ ih₂ =>
    have h1 := (one_add_pos hs i).ne'
    have h2 := (one_sub_pos hs i).ne'
    simp only [ev, ih₁, ih₂, rH, D1]
    field_simp
    ring

/-- Leaf differentiation, second order: `D2 = E[Y (Z² - A)]`. Paper: `vᵀ ∇²𝓗 v = E[Y(Z² - A)]`
in the proof of `lem:multivariate-transcript` (instance_information.tex). -/
lemma ev_YZ2A (T : DTree m) (z a : ℝ) :
    ev s v (fun y z a => y * (z ^ 2 - a)) T z a =
      (z ^ 2 - a) * T.rH s + 2 * z * T.D1 s v + T.D2 s v := by
  induction T generalizing z a with
  | leaf y => simp [ev, rH, D1, D2]; ring
  | node i T₁ T₂ ih₁ ih₂ =>
    have h1 := (one_add_pos hs i).ne'
    have h2 := (one_sub_pos hs i).ne'
    simp only [ev, ih₁, ih₂, rH, D1, D2]
    field_simp
    ring

end Identities

/-- `E[Y²] ≤ 1` for outputs in `[-1,1]`. Auxiliary for the Cauchy--Schwarz step of
`lem:multivariate-transcript` (instance_information.tex). -/
lemma rY2_le_one {s : Fin m → ℝ} (hs : ∀ i, |s i| ≤ 1) {T : DTree m} (hT : T.Bounded) :
    T.rY2 s ≤ 1 := by
  induction T with
  | leaf y =>
    simp only [rY2]
    have hy : |y| ≤ 1 := hT
    have : |y| ^ 2 ≤ 1 := by
      have := abs_nonneg y
      nlinarith
    simpa [sq_abs] using this
  | node i T₁ T₂ ih₁ ih₂ =>
    have h1 := abs_le.mp (hs i)
    simp only [rY2]
    have := ih₁ hT.1
    have := ih₂ hT.2
    nlinarith

/-- Weighted query counts with nonnegative weights are nonnegative. Auxiliary for the transcript
identities in the proof of `lem:transcript` (tanh_lower.tex) and `lem:multivariate-transcript`
(instance_information.tex). -/
lemma rW_nonneg {s w : Fin m → ℝ} (hs : ∀ i, |s i| ≤ 1) (hw : ∀ i, 0 ≤ w i) (T : DTree m) :
    0 ≤ T.rW s w := by
  induction T with
  | leaf y => exact le_refl 0
  | node i T₁ T₂ ih₁ ih₂ =>
    have h1 := abs_le.mp (hs i)
    simp only [rW]
    have := hw i
    have : 0 ≤ (1 + s i) / 2 * T₁.rW s w := mul_nonneg (by linarith) ih₁
    have : 0 ≤ (1 - s i) / 2 * T₂.rW s w := mul_nonneg (by linarith) ih₂
    linarith

end DTree

/-! ## Randomized samplers -/

/-- A randomized query algorithm on `m` sign inputs, presented as a finite mixture of
decision trees. The index `ω` ranges over classes of random tapes (preprocessing and online
randomness together) that induce the same decision tree, and `p ω` is the probability of the
class. A leaf value is the conditional mean of the returned sign given the leaf. -/
structure Sampler (m : ℕ) (ι : Type*) [Fintype ι] where
  /-- Probability of each tape class. -/
  p : ι → ℝ
  /-- Decision tree followed on each tape class. -/
  tree : ι → DTree m
  p_nonneg : ∀ ω, 0 ≤ p ω
  p_sum : ∑ ω, p ω = 1

namespace Sampler

variable {ι : Type*} [Fintype ι] (S : Sampler m ι)

/-- Mean of the returned sign on input `x`. -/
def mean (x : Fin m → Bool) : ℝ := ∑ ω, S.p ω * (S.tree ω).out x

/-- Probability that coordinate `i` is probed on input `x`. -/
def probe (i : Fin m) (x : Fin m → Bool) : ℝ :=
  ∑ ω, S.p ω * (if i ∈ (S.tree ω).path x then 1 else 0)

/-- Conditional expected number `E[Q | x]` of distinct probes on input `x`. -/
def cost (x : Fin m → Bool) : ℝ := ∑ ω, S.p ω * ((S.tree ω).path x).card

/-- Every tree of the mixture queries each coordinate at most once along a path. -/
def NoRepeat : Prop := ∀ ω, (S.tree ω).NoRepeat

/-- Every leaf value lies in `[-1,1]`. -/
def Bounded : Prop := ∀ ω, (S.tree ω).Bounded

/-- `S` samples the sign of mean `f x` exactly on every input `x`. -/
def Exact (f : (Fin m → Bool) → ℝ) : Prop := ∀ x, S.mean x = f x

/-- Distinct probes counted coordinatewise. Auxiliary for the transcript identities in the proof
of `lem:transcript` (tanh_lower.tex) and `lem:multivariate-transcript`
(instance_information.tex). -/
lemma card_path_eq_sum (T : DTree m) (x : Fin m → Bool) :
    ((T.path x).card : ℝ) = ∑ i, (if i ∈ T.path x then 1 else 0) := by
  rw [Finset.sum_boole]
  congr 2
  ext i
  simp

/-- `E[Q | x] = ∑ᵢ P_x(i is probed)`. Auxiliary for the transcript identities in the proof of
`lem:transcript` (tanh_lower.tex) and `lem:multivariate-transcript` (instance_information.tex);
also the summation step after `eq:main-coupling` (exact_sampling_networks.tex). -/
lemma cost_eq_sum_probe (x : Fin m → Bool) : S.cost x = ∑ i, S.probe i x := by
  unfold cost probe
  simp_rw [card_path_eq_sum, Finset.mul_sum]
  exact Finset.sum_comm

/-- Probe probabilities are nonnegative. Auxiliary for the transcript identities in the proof of
`lem:transcript` (tanh_lower.tex) and `lem:multivariate-transcript` (instance_information.tex). -/
lemma probe_nonneg (i : Fin m) (x : Fin m → Bool) : 0 ≤ S.probe i x :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (S.p_nonneg ω) (by split <;> norm_num)

/-- Expected probe counts are nonnegative. Auxiliary for the transcript identities in the proof
of `lem:transcript` (tanh_lower.tex) and `lem:multivariate-transcript`
(instance_information.tex). -/
lemma cost_nonneg (x : Fin m → Bool) : 0 ≤ S.cost x :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (S.p_nonneg ω) (Nat.cast_nonneg _)

/-- The output mean of a bounded sampler lies in `[-1,1]`. Auxiliary for `eq:main-information`
(exact_sampling_networks.tex). -/
lemma abs_mean_le (hB : S.Bounded) (x : Fin m → Bool) : |S.mean x| ≤ 1 := by
  unfold mean
  calc |∑ ω, S.p ω * (S.tree ω).out x| ≤ ∑ ω, |S.p ω * (S.tree ω).out x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ω, S.p ω * 1 := Finset.sum_le_sum fun ω _ => by
        rw [abs_mul, abs_of_nonneg (S.p_nonneg ω)]
        exact mul_le_mul_of_nonneg_left (DTree.abs_out_le (hB ω) x) (S.p_nonneg ω)
    _ = 1 := by simp [S.p_sum]

/-- Mixture form of the product-law mean of the output. Auxiliary for
`lem:multivariate-transcript` (instance_information.tex). -/
lemma prodExp_mean (hN : S.NoRepeat) (s : Fin m → ℝ) :
    prodExp s S.mean = ∑ ω, S.p ω * (S.tree ω).rH s := by
  unfold mean
  rw [prodExp_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [prodExp_mul_const, DTree.prodExp_out (hN ω)]

/-- Mixture form of weighted probe probabilities. Paper: `I_v = ∑ᵢ vᵢ² qᵢ/(1 - tᵢ²)` in
`lem:multivariate-transcript` (instance_information.tex). -/
lemma sum_rW (hN : S.NoRepeat) (s w : Fin m → ℝ) :
    ∑ ω, S.p ω * (S.tree ω).rW s w = ∑ i, w i * prodExp s (S.probe i) := by
  have h1 : ∀ ω, (S.tree ω).rW s w =
      ∑ i, w i * prodExp s (fun x => if i ∈ (S.tree ω).path x then 1 else 0) := by
    intro ω
    rw [← DTree.prodExp_path_sum (hN ω)]
    simp_rw [← prodExp_mul_const]
    rw [← prodExp_sum]
    congr 1
    funext x
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold probe
  rw [prodExp_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [prodExp_mul_const]
  ring

/-- `E_s Q = ∑ᵢ qᵢ(s)`. Auxiliary for the transcript identities in the proof of `lem:transcript`
(tanh_lower.tex) and `lem:multivariate-transcript` (instance_information.tex). -/
lemma prodExp_cost (s : Fin m → ℝ) : prodExp s S.cost = ∑ i, prodExp s (S.probe i) := by
  have : S.cost = fun x => ∑ i, S.probe i x := funext S.cost_eq_sum_probe
  rw [this]
  exact prodExp_sum _ _ _

end Sampler

/-! ## Answering repeated queries from a cache -/

namespace DTree

/-- Prune a tree against a cache `κ` of known answers: a query to a cached coordinate is
answered from the cache, and a fresh query records its answer. -/
def prune : DTree m → (Fin m → Option Bool) → DTree m
  | leaf y, _ => leaf y
  | node i T₁ T₂, κ =>
      match κ i with
      | some true => prune T₁ κ
      | some false => prune T₂ κ
      | none => node i (prune T₁ (Function.update κ i (some true)))
          (prune T₂ (Function.update κ i (some false)))

/-- The input `x` agrees with the cache `κ`. -/
def Consistent (κ : Fin m → Option Bool) (x : Fin m → Bool) : Prop :=
  ∀ i b, κ i = some b → x i = b

/-- Recording a consistent answer keeps the cache consistent. Auxiliary for
`Sampler.prune_spec`. -/
lemma consistent_update {κ : Fin m → Option Bool} {x : Fin m → Bool} (h : Consistent κ x)
    (i : Fin m) : Consistent (Function.update κ i (some (x i))) x := by
  intro j b hj
  by_cases hji : j = i
  · subst hji; simp at hj; exact hj
  · rw [Function.update_of_ne hji] at hj; exact h j b hj

/-- Pruning preserves the output and removes exactly the cached coordinates from the set of
probed coordinates. Paper: "queries to fixed or previously read coordinates may be answered
without cost" (`sec:lower`, tanh_lower.tex). -/
lemma prune_out_path (T : DTree m) {κ : Fin m → Option Bool} {x : Fin m → Bool}
    (hκ : Consistent κ x) :
    (T.prune κ).out x = T.out x ∧
      (T.prune κ).path x = (T.path x).filter (fun i => κ i = none) := by
  induction T generalizing κ with
  | leaf y => simp [prune, out, path]
  | node i T₁ T₂ ih₁ ih₂ =>
    have hins : ∀ (S : Finset (Fin m)) (b : Bool),
        insert i (S.filter (fun j => Function.update κ i (some b) j = none)) =
          insert i (S.filter (fun j => κ j = none)) := by
      intro S b
      ext j
      by_cases hji : j = i
      · subst hji; simp
      · simp [Finset.mem_insert, Finset.mem_filter, hji]
    rcases hκi : κ i with _ | b
    · -- a fresh query
      simp only [prune, hκi]
      cases hxi : x i
      · have hc : Consistent (Function.update κ i (some false)) x := by
          have := consistent_update hκ i; rwa [hxi] at this
        obtain ⟨h1, h2⟩ := ih₂ hc
        simp only [out, path, hxi, Bool.false_eq_true, ite_false]
        refine ⟨h1, ?_⟩
        rw [h2, hins, Finset.filter_insert, ite_eq_left hκi]
      · have hc : Consistent (Function.update κ i (some true)) x := by
          have := consistent_update hκ i; rwa [hxi] at this
        obtain ⟨h1, h2⟩ := ih₁ hc
        simp only [out, path, hxi, ite_true]
        refine ⟨h1, ?_⟩
        rw [h2, hins, Finset.filter_insert, ite_eq_left hκi]
    · -- a cached query
      have hxi : x i = b := hκ i b hκi
      have hne : ¬ κ i = none := by rw [hκi]; simp
      cases b
      · simp only [prune, hκi]
        obtain ⟨h1, h2⟩ := ih₂ hκ
        simp only [out, path, hxi, Bool.false_eq_true, ite_false]
        refine ⟨h1, ?_⟩
        rw [h2, Finset.filter_insert, ite_eq_right hne]
      · simp only [prune, hκi]
        obtain ⟨h1, h2⟩ := ih₁ hκ
        simp only [out, path, hxi, ite_true]
        refine ⟨h1, ?_⟩
        rw [h2, Finset.filter_insert, ite_eq_right hne]

/-- Pruned trees query only uncached coordinates, each at most once along a path. Auxiliary for
`Sampler.prune_spec` (`sec:lower`, tanh_lower.tex). -/
lemma prune_noRepeat (T : DTree m) (κ : Fin m → Option Bool) :
    (∀ i ∈ (T.prune κ).queried, κ i = none) ∧ (T.prune κ).NoRepeat := by
  induction T generalizing κ with
  | leaf y => simp [prune, queried, NoRepeat]
  | node i T₁ T₂ ih₁ ih₂ =>
    rcases hκi : κ i with _ | b
    · simp only [prune, hκi]
      obtain ⟨q₁, n₁⟩ := ih₁ (Function.update κ i (some true))
      obtain ⟨q₂, n₂⟩ := ih₂ (Function.update κ i (some false))
      refine ⟨fun j hj => ?_, ?_, ?_, n₁, n₂⟩
      · simp only [queried, Finset.mem_insert, Finset.mem_union] at hj
        rcases hj with rfl | hj | hj
        · exact hκi
        · have := q₁ j hj
          by_cases hji : j = i
          · subst hji; simp at this
          · rwa [Function.update_of_ne hji] at this
        · have := q₂ j hj
          by_cases hji : j = i
          · subst hji; simp at this
          · rwa [Function.update_of_ne hji] at this
      · intro hi; have := q₁ i hi; simp at this
      · intro hi; have := q₂ i hi; simp at this
    · cases b
      · simp only [prune, hκi]; exact ih₂ κ
      · simp only [prune, hκi]; exact ih₁ κ

/-- Pruning preserves bounded leaves. Auxiliary for `Sampler.prune_spec` (`sec:lower`,
tanh_lower.tex). -/
lemma prune_bounded {T : DTree m} (hT : T.Bounded) (κ : Fin m → Option Bool) :
    (T.prune κ).Bounded := by
  induction T generalizing κ with
  | leaf y => exact hT
  | node i T₁ T₂ ih₁ ih₂ =>
    rcases hκi : κ i with _ | b
    · simp only [prune, hκi]; exact ⟨ih₁ hT.1 _, ih₂ hT.2 _⟩
    · cases b
      · simp only [prune, hκi]; exact ih₂ hT.2 κ
      · simp only [prune, hκi]; exact ih₁ hT.1 κ

end DTree

/-- Pruning every tree of a sampler with the empty cache. -/
def Sampler.prune {ι : Type*} [Fintype ι] (S : Sampler m ι) : Sampler m ι where
  p := S.p
  tree ω := (S.tree ω).prune (fun _ => none)
  p_nonneg := S.p_nonneg
  p_sum := S.p_sum

/-- **Distinct queries are no restriction.** Answering repeated queries from a cache turns any
sampler into one with distinct queries along every path, the same output law and the same
number of distinct probes on every input. Hence every theorem of this file stated for
`NoRepeat` samplers applies to arbitrary finite mixtures of decision trees.

Paper: "queries to fixed or previously read coordinates may be answered without cost"
(`sec:lower`, tanh_lower.tex). -/
theorem Sampler.prune_spec {ι : Type*} [Fintype ι] (S : Sampler m ι) :
    S.prune.NoRepeat ∧ (∀ x, S.prune.mean x = S.mean x) ∧ (∀ x, S.prune.cost x = S.cost x) ∧
      (S.Bounded → S.prune.Bounded) := by
  have hc : ∀ x : Fin m → Bool, DTree.Consistent (fun _ => none) x := fun x i b h => by
    simp at h
  refine ⟨fun ω => (DTree.prune_noRepeat _ _).2, fun x => ?_, fun x => ?_,
    fun hB ω => DTree.prune_bounded (hB ω) _⟩
  · unfold Sampler.mean
    exact Finset.sum_congr rfl fun ω _ => by
      rw [show S.prune.tree ω = (S.tree ω).prune (fun _ => none) from rfl,
        (DTree.prune_out_path _ (hc x)).1]
      rfl
  · unfold Sampler.cost
    exact Finset.sum_congr rfl fun ω _ => by
      rw [show S.prune.tree ω = (S.tree ω).prune (fun _ => none) from rfl,
        (DTree.prune_out_path _ (hc x)).2, Finset.filter_true_of_mem (fun i _ => rfl)]
      rfl


/-! ## Directional transcript inequalities -/

/-- The product extension along a line: `u ↦ 𝓗(s + u v)` with
`𝓗(s) = ∑ₓ f(x) ∏ᵢ (1 + sᵢ xᵢ)/2`. -/
def dirProfile (f : (Fin m → Bool) → ℝ) (s v : Fin m → ℝ) (u : ℝ) : ℝ :=
  prodExp (s + u • v) f

/-- The directional information `I_v(s) = ∑ᵢ vᵢ² qᵢ(s) / (1 - sᵢ²)`, where `qᵢ(s)` is the
probability that coordinate `i` is probed under the product law with means `s`. -/
def info {ι : Type*} [Fintype ι] (S : Sampler m ι) (s v : Fin m → ℝ) : ℝ :=
  ∑ i, v i ^ 2 / (1 - s i ^ 2) * prodExp s (S.probe i)

section Directional

variable {ι : Type*} [Fintype ι] (S : Sampler m ι)

/-- For an exact sampler, the product extension along a line is the mixture of tree averages.
Finite likelihood differentiation in the proof of `lem:multivariate-transcript`
(instance_information.tex). -/
lemma dirProfile_eq (hN : S.NoRepeat) {f : (Fin m → Bool) → ℝ} (hf : S.Exact f)
    (s v : Fin m → ℝ) : dirProfile f s v =
      fun u => ∑ ω, S.p ω * (S.tree ω).rH (s + u • v) := by
  funext u
  unfold dirProfile
  rw [← S.prodExp_mean hN]
  congr 1
  funext x
  exact (hf x).symm

/-- First derivative of the product extension along a line. Finite likelihood differentiation in
the proof of `lem:multivariate-transcript` (instance_information.tex). -/
lemma hasDerivAt_dirProfile (hN : S.NoRepeat) {f : (Fin m → Bool) → ℝ} (hf : S.Exact f)
    (s v : Fin m → ℝ) (u : ℝ) :
    HasDerivAt (dirProfile f s v) (∑ ω, S.p ω * (S.tree ω).D1 (s + u • v) v) u := by
  rw [dirProfile_eq S hN hf]
  exact HasDerivAt.fun_sum fun ω _ => (DTree.hasDerivAt_rH _ s v u).const_mul _

/-- First derivative of the product extension along a line, as a function. Finite likelihood
differentiation in the proof of `lem:multivariate-transcript` (instance_information.tex). -/
lemma deriv_dirProfile (hN : S.NoRepeat) {f : (Fin m → Bool) → ℝ} (hf : S.Exact f)
    (s v : Fin m → ℝ) : deriv (dirProfile f s v) =
      fun u => ∑ ω, S.p ω * (S.tree ω).D1 (s + u • v) v := by
  funext u
  exact (hasDerivAt_dirProfile S hN hf s v u).deriv

/-- Second derivative of the product extension along a line. Finite likelihood differentiation
in the proof of `lem:multivariate-transcript` (instance_information.tex). -/
lemma hasDerivAt_deriv_dirProfile (hN : S.NoRepeat) {f : (Fin m → Bool) → ℝ}
    (hf : S.Exact f) (s v : Fin m → ℝ) (u : ℝ) :
    HasDerivAt (deriv (dirProfile f s v)) (∑ ω, S.p ω * (S.tree ω).D2 (s + u • v) v) u := by
  rw [deriv_dirProfile S hN hf]
  exact HasDerivAt.fun_sum fun ω _ => (DTree.hasDerivAt_D1 _ s v u).const_mul _

/-- **Directional transcript inequalities.** For every exact sign sampler with finitely many
decision trees, every interior mean vector `s`, and every direction `v`,
`(v·∇𝓗(s))² ≤ (1 - 𝓗(s)²) I_v(s)` and `|vᵀ ∇²𝓗(s) v| ≤ 2 I_v(s)`.

Paper: `lem:multivariate-transcript`, `eq:multivariate-information` and
`eq:multivariate-curvature` (instance_information.tex). With `v = (1,…,1)` and
`s = (t,…,t)` this gives `lem:transcript` (tanh_lower.tex) and `eq:main-information`
(exact_sampling_networks.tex). -/
theorem multivariate_transcript (hN : S.NoRepeat) (hB : S.Bounded)
    {f : (Fin m → Bool) → ℝ} (hf : S.Exact f) (s v : Fin m → ℝ) (hs : ∀ i, |s i| < 1) :
    deriv (dirProfile f s v) 0 ^ 2 ≤ (1 - prodExp s f ^ 2) * info S s v ∧
      |deriv (deriv (dirProfile f s v)) 0| ≤ 2 * info S s v := by
  have hs' : ∀ i, |s i| ≤ 1 := fun i => (hs i).le
  have hs0 : s + (0 : ℝ) • v = s := by simp
  have hd1 : deriv (dirProfile f s v) 0 = ∑ ω, S.p ω * (S.tree ω).D1 s v := by
    rw [(hasDerivAt_dirProfile S hN hf s v 0).deriv, hs0]
  have hd2 : deriv (deriv (dirProfile f s v)) 0 = ∑ ω, S.p ω * (S.tree ω).D2 s v := by
    rw [(hasDerivAt_deriv_dirProfile S hN hf s v 0).deriv, hs0]
  have hH : prodExp s f = ∑ ω, S.p ω * (S.tree ω).rH s := by
    rw [← S.prodExp_mean hN]
    congr 1
    funext x
    exact (hf x).symm
  have hI : info S s v = ∑ ω, S.p ω * (S.tree ω).rW s (DTree.infoWeight s v) := by
    rw [S.sum_rW hN]
    rfl
  set H := prodExp s f with hHdef
  set I := info S s v with hIdef
  set d1 := ∑ ω, S.p ω * (S.tree ω).D1 s v
  set y2 := ∑ ω, S.p ω * (S.tree ω).rY2 s
  have hI0 : 0 ≤ I := by
    rw [hI]
    refine Finset.sum_nonneg fun ω _ => mul_nonneg (S.p_nonneg ω) ?_
    refine DTree.rW_nonneg hs' (fun i => ?_) _
    unfold DTree.infoWeight
    have := abs_lt.mp (hs i)
    have : 0 < 1 - s i ^ 2 := by nlinarith
    positivity
  have hy2 : y2 ≤ 1 := by
    calc y2 ≤ ∑ ω, S.p ω * 1 := Finset.sum_le_sum fun ω _ =>
          mul_le_mul_of_nonneg_left (DTree.rY2_le_one hs' (hB ω)) (S.p_nonneg ω)
      _ = 1 := by simp [S.p_sum]
  constructor
  · -- Cauchy--Schwarz through the nonnegative quadratic `E[(Y - H + λ Z)²]`.
    have hquad : ∀ l : ℝ, 0 ≤ I * (l * l) + (2 * d1) * l + (y2 - H ^ 2) := by
      intro l
      have hpt : ∀ ω, (S.tree ω).ev s v (fun y z _ => (y - H + l * z) ^ 2) 0 0 =
          (S.tree ω).rY2 s - 2 * H * (S.tree ω).rH s + H ^ 2 +
            2 * l * (S.tree ω).D1 s v + l ^ 2 * (S.tree ω).rW s (DTree.infoWeight s v) := by
        intro ω
        have hexp : (fun y z (_ : ℝ) => (y - H + l * z) ^ 2) = fun y z a =>
            (fun y _ _ => y ^ 2) y z a + ((-2 * H) * (fun y _ _ => y) y z a +
              (H ^ 2 * (fun _ _ _ => (1 : ℝ)) y z a + ((2 * l) * (fun y z _ => y * z) y z a +
                ((-2 * H * l) * (fun _ z _ => z) y z a + l ^ 2 *
                  (fun _ z _ => z ^ 2) y z a)))) := by
          funext y z a; ring
        rw [hexp]
        simp only [DTree.ev_add, DTree.ev_const_mul]
        rw [DTree.ev_Y2, DTree.ev_Y, DTree.ev_one, DTree.ev_YZ v hs, DTree.ev_Z v hs,
          DTree.ev_Z2 v hs]
        ring
      have hnn : 0 ≤ ∑ ω, S.p ω * (S.tree ω).ev s v (fun y z _ => (y - H + l * z) ^ 2) 0 0 :=
        Finset.sum_nonneg fun ω _ => mul_nonneg (S.p_nonneg ω) (by
          have := DTree.ev_mono (v := v) (φ := fun _ _ _ => 0) hs' (fun _ _ => True)
            (fun _ _ _ _ => ⟨trivial, trivial⟩) (fun y z a _ _ => sq_nonneg (y - H + l * z))
            (hB ω) (z := 0) (a := 0) trivial
          have h0 : (S.tree ω).ev s v (fun _ _ _ => (0 : ℝ)) 0 0 = 0 := by
            have := DTree.ev_const_mul s v 0 (fun _ _ _ => (1 : ℝ)) (S.tree ω) 0 0
            simpa using this
          linarith)
      simp_rw [hpt] at hnn
      have hsplit : ∑ ω, S.p ω * ((S.tree ω).rY2 s - 2 * H * (S.tree ω).rH s + H ^ 2 +
            2 * l * (S.tree ω).D1 s v + l ^ 2 * (S.tree ω).rW s (DTree.infoWeight s v)) =
          y2 - 2 * H * (∑ ω, S.p ω * (S.tree ω).rH s) + H ^ 2 * ∑ ω, S.p ω +
            2 * l * d1 + l ^ 2 * ∑ ω, S.p ω * (S.tree ω).rW s (DTree.infoWeight s v) := by
        have e : ∀ ω, S.p ω * ((S.tree ω).rY2 s - 2 * H * (S.tree ω).rH s + H ^ 2 +
            2 * l * (S.tree ω).D1 s v + l ^ 2 * (S.tree ω).rW s (DTree.infoWeight s v)) =
            S.p ω * (S.tree ω).rY2 s + (-2 * H) * (S.p ω * (S.tree ω).rH s) +
              H ^ 2 * S.p ω + (2 * l) * (S.p ω * (S.tree ω).D1 s v) +
              l ^ 2 * (S.p ω * (S.tree ω).rW s (DTree.infoWeight s v)) := fun ω => by ring
        rw [Finset.sum_congr rfl fun ω _ => e ω]
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
      rw [hsplit, ← hH, ← hI, S.p_sum] at hnn
      nlinarith
    have hdisc := discrim_le_zero hquad
    unfold discrim at hdisc
    have : d1 ^ 2 ≤ I * (y2 - H ^ 2) := by nlinarith
    rw [hd1]
    calc d1 ^ 2 ≤ I * (y2 - H ^ 2) := this
      _ ≤ I * (1 - H ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hI0
      _ = (1 - H ^ 2) * I := by ring
  · -- Curvature: `|E[Y (Z² - A)]| ≤ E[Z² + A] = 2 I`.
    have hpt : ∀ ω, |(S.tree ω).D2 s v| ≤
        2 * (S.tree ω).rW s (DTree.infoWeight s v) := by
      intro ω
      have hD2 : (S.tree ω).D2 s v =
          (S.tree ω).ev s v (fun y z a => y * (z ^ 2 - a)) 0 0 := by
        rw [DTree.ev_YZ2A v hs]; ring
      have hZA : (S.tree ω).ev s v (fun _ z a => z ^ 2 + a) 0 0 =
          2 * (S.tree ω).rW s (DTree.infoWeight s v) := by
        have := DTree.ev_add s v (fun _ z _ => z ^ 2) (fun _ _ a => a) (S.tree ω) 0 0
        rw [this, DTree.ev_Z2 v hs, DTree.ev_A v hs]
        ring
      have hinv : ∀ (i : Fin m) (_z a : ℝ), 0 ≤ a → 0 ≤ a + (v i / (1 + s i)) ^ 2 ∧
          0 ≤ a + (v i / (1 - s i)) ^ 2 := fun i _ a ha =>
        DTree.nonneg_invariant s v i a ha
      have hup := DTree.ev_mono (v := v) hs' (fun _ a => 0 ≤ a) hinv
        (φ := fun y z a => y * (z ^ 2 - a)) (ψ := fun _ z a => z ^ 2 + a)
        (fun y z a hy ha => by
          have h1 : |y * (z ^ 2 - a)| ≤ z ^ 2 + a := by
            rw [abs_mul]
            have : |z ^ 2 - a| ≤ z ^ 2 + a := by
              rw [abs_le]; constructor <;> nlinarith [sq_nonneg z]
            calc |y| * |z ^ 2 - a| ≤ 1 * (z ^ 2 + a) :=
                  mul_le_mul hy this (abs_nonneg _) zero_le_one
              _ = z ^ 2 + a := one_mul _
          exact (abs_le.mp h1).2)
        (hB ω) (z := 0) (a := 0) (le_refl (0 : ℝ))
      have hlo := DTree.ev_mono (v := v) hs' (fun _ a => 0 ≤ a) hinv
        (φ := fun y z a => (-1) * (y * (z ^ 2 - a))) (ψ := fun _ z a => z ^ 2 + a)
        (fun y z a hy ha => by
          have h1 : |y * (z ^ 2 - a)| ≤ z ^ 2 + a := by
            rw [abs_mul]
            have : |z ^ 2 - a| ≤ z ^ 2 + a := by
              rw [abs_le]; constructor <;> nlinarith [sq_nonneg z]
            calc |y| * |z ^ 2 - a| ≤ 1 * (z ^ 2 + a) :=
                  mul_le_mul hy this (abs_nonneg _) zero_le_one
              _ = z ^ 2 + a := one_mul _
          have := (abs_le.mp h1).1
          linarith)
        (hB ω) (z := 0) (a := 0) (le_refl (0 : ℝ))
      rw [DTree.ev_const_mul] at hlo
      rw [hD2, abs_le]
      constructor <;> linarith
    rw [hd2, hI, Finset.mul_sum]
    calc |∑ ω, S.p ω * (S.tree ω).D2 s v| ≤ ∑ ω, |S.p ω * (S.tree ω).D2 s v| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ω, 2 * (S.p ω * (S.tree ω).rW s (DTree.infoWeight s v)) :=
          Finset.sum_le_sum fun ω _ => by
            rw [abs_mul, abs_of_nonneg (S.p_nonneg ω)]
            have := mul_le_mul_of_nonneg_left (hpt ω) (S.p_nonneg ω)
            linarith

/-- The common-mean profile `H(t) = E_t f(X)` of a target `f`. -/
def meanProfile (f : (Fin m → Bool) → ℝ) (t : ℝ) : ℝ := prodExp (fun _ => t) f

/-- Expected number of distinct probes under the common-mean product law. -/
def expCost (t : ℝ) : ℝ := prodExp (fun _ => t) S.cost

/-- The diagonal direction recovers the common-mean profile `H`. Auxiliary for deducing
`lem:transcript` (tanh_lower.tex) from `lem:multivariate-transcript`. -/
lemma dirProfile_const (f : (Fin m → Bool) → ℝ) (t : ℝ) :
    dirProfile f (fun _ => t) (fun _ => 1) = fun u => meanProfile f (t + u) := by
  funext u
  unfold dirProfile meanProfile
  congr 1
  funext i
  simp

/-- The common-mean profile `H` is twice differentiable. Auxiliary for the curvature step in the
proof of `thm:lower` (tanh_lower.tex). -/
lemma meanProfile_hasDerivAt (hN : S.NoRepeat) {f : (Fin m → Bool) → ℝ} (hf : S.Exact f)
    (t : ℝ) : HasDerivAt (meanProfile f) (deriv (meanProfile f) t) t ∧
      HasDerivAt (deriv (meanProfile f)) (deriv (deriv (meanProfile f)) t) t := by
  have hshift : ∀ g : ℝ → ℝ, (fun u => g (0 + u)) = g := fun g => by funext u; simp
  have h0 := dirProfile_const f 0
  have hd := hasDerivAt_dirProfile S hN hf (fun _ => 0) (fun _ => 1) t
  rw [h0, hshift] at hd
  have hdd := hasDerivAt_deriv_dirProfile S hN hf (fun _ => 0) (fun _ => 1) t
  rw [h0, hshift] at hdd
  exact ⟨hd.differentiableAt.hasDerivAt, hdd.differentiableAt.hasDerivAt⟩

/-- On the diagonal, `I_v = E_t Q/(1 - t²)`. Auxiliary for deducing `lem:transcript`
(tanh_lower.tex) from `lem:multivariate-transcript`. -/
lemma info_const (t : ℝ) :
    info S (fun _ => t) (fun _ => 1) = expCost S t / (1 - t ^ 2) := by
  unfold info expCost
  rw [S.prodExp_cost, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Transcript derivatives.** For an exact sign sampler and `-1 < t < 1`,
`E_t Q ≥ (1 - t²) H'(t)²` and `E_t Q ≥ (1 - t²)/2 · |H''(t)|`, together with the centered
form `(1 - H(t)²) E_t Q ≥ (1 - t²) H'(t)²`. Here `H(t) = E_t f(X)` and `Q` counts distinct
probes.

Paper: `lem:transcript` (tanh_lower.tex), `eq:transcript`; the centered form (first conjunct)
is `eq:transcript-variance` (tanh_lower.tex) and `eq:main-information`
(exact_sampling_networks.tex), multiplied out so that no condition `|H(t)| < 1` is needed. -/
theorem transcript (hN : S.NoRepeat) (hB : S.Bounded) {f : (Fin m → Bool) → ℝ}
    (hf : S.Exact f) {t : ℝ} (ht : |t| < 1) :
    (1 - t ^ 2) * deriv (meanProfile f) t ^ 2 ≤
        (1 - meanProfile f t ^ 2) * expCost S t ∧
      (1 - t ^ 2) * deriv (meanProfile f) t ^ 2 ≤ expCost S t ∧
      (1 - t ^ 2) / 2 * |deriv (deriv (meanProfile f)) t| ≤ expCost S t := by
  have hmain := multivariate_transcript S hN hB hf (fun _ => t) (fun _ => 1) (fun _ => ht)
  rw [dirProfile_const, info_const] at hmain
  have hd1 : deriv (fun u => meanProfile f (t + u)) 0 = deriv (meanProfile f) t := by
    rw [deriv_comp_const_add, add_zero]
  have hd2 : deriv (deriv (fun u => meanProfile f (t + u))) 0 =
      deriv (deriv (meanProfile f)) t := by
    have : deriv (fun u => meanProfile f (t + u)) = fun u => deriv (meanProfile f) (t + u) := by
      funext u; exact deriv_comp_const_add _ _ _
    rw [this, deriv_comp_const_add, add_zero]
  rw [hd1, hd2] at hmain
  have hpos : 0 < 1 - t ^ 2 := by
    have := abs_lt.mp ht; nlinarith
  have hH : |meanProfile f t| ≤ 1 := by
    have hfb : ∀ x, |f x| ≤ 1 := fun x => hf x ▸ S.abs_mean_le hB x
    unfold meanProfile prodExp
    have hs' : ∀ _ : Fin m, |t| ≤ 1 := fun _ => ht.le
    calc |∑ x, prodLaw (fun _ => t) x * f x| ≤ ∑ x, |prodLaw (fun _ => t) x * f x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, prodLaw (fun _ => t) x * 1 := Finset.sum_le_sum fun x _ => by
          rw [abs_mul, abs_of_nonneg (prodLaw_nonneg hs' x)]
          exact mul_le_mul_of_nonneg_left (hfb x) (prodLaw_nonneg hs' x)
      _ = 1 := by simp [sum_prodLaw]
  have hEQ : 0 ≤ expCost S t := by
    unfold expCost
    have := prodExp_mono (s := fun _ => t) (fun _ => ht.le) (g₁ := fun _ => 0)
      (g₂ := S.cost) S.cost_nonneg
    rwa [prodExp_const] at this
  have hH2 : meanProfile f t ^ 2 ≤ 1 := by
    have := abs_nonneg (meanProfile f t)
    nlinarith [sq_abs (meanProfile f t)]
  obtain ⟨h1, h2⟩ := hmain
  have hmp : prodExp (fun _ => t) f = meanProfile f t := rfl
  rw [hmp] at h1
  have hA : (1 - t ^ 2) * deriv (meanProfile f) t ^ 2 ≤
      (1 - meanProfile f t ^ 2) * expCost S t := by
    have := mul_le_mul_of_nonneg_left h1 hpos.le
    rw [show (1 - t ^ 2) * ((1 - meanProfile f t ^ 2) * (expCost S t / (1 - t ^ 2))) =
      (1 - meanProfile f t ^ 2) * expCost S t by field_simp] at this
    exact this
  refine ⟨hA, ?_, ?_⟩
  · calc (1 - t ^ 2) * deriv (meanProfile f) t ^ 2 ≤
          (1 - meanProfile f t ^ 2) * expCost S t := hA
      _ ≤ 1 * expCost S t := mul_le_mul_of_nonneg_right (by nlinarith) hEQ
      _ = expCost S t := one_mul _
  · have := mul_le_mul_of_nonneg_left h2 hpos.le
    rw [show (1 - t ^ 2) * (2 * (expCost S t / (1 - t ^ 2))) = 2 * expCost S t by
      field_simp] at this
    linarith

end Directional

/-! ## The coupling inequality -/

/-- Total-variation distance between the laws on `{-1,1}` with means `μ₁` and `μ₂`. -/
def signTV (μ₁ μ₂ : ℝ) : ℝ := (|(1 + μ₁) / 2 - (1 + μ₂) / 2| + |(1 - μ₁) / 2 - (1 - μ₂) / 2|) / 2

/-- Total variation between two sign laws is half the difference of means. Auxiliary for
`eq:main-coupling` (exact_sampling_networks.tex). -/
lemma signTV_eq (μ₁ μ₂ : ℝ) : signTV μ₁ μ₂ = |μ₁ - μ₂| / 2 := by
  unfold signTV
  rw [show (1 + μ₁) / 2 - (1 + μ₂) / 2 = (μ₁ - μ₂) / 2 by ring,
    show (1 - μ₁) / 2 - (1 - μ₂) / 2 = -((μ₁ - μ₂) / 2) by ring, abs_neg, abs_div]
  norm_num

/-- **Coupling inequality.** Run the algorithm on `x` and on `x` with coordinate `i` changed,
with the same random tape. The transcripts agree until coordinate `i` is read, so the
probability of reading it on `x` is at least the total-variation distance of the two output
laws.

Paper: `eq:main-coupling` (exact_sampling_networks.tex) and `lem:attentioncoupling`
(attention_primitives.tex). -/
theorem coupling {ι : Type*} [Fintype ι] (S : Sampler m ι) (hB : S.Bounded)
    {f : (Fin m → Bool) → ℝ} (hf : S.Exact f) (x : Fin m → Bool) (i : Fin m) (b : Bool) :
    signTV (f x) (f (Function.update x i b)) ≤ S.probe i x := by
  rw [signTV_eq, ← hf, ← hf]
  unfold Sampler.mean Sampler.probe
  have hpt : ∀ ω, |(S.tree ω).out x - (S.tree ω).out (Function.update x i b)| ≤
      2 * (if i ∈ (S.tree ω).path x then 1 else 0) := by
    intro ω
    by_cases h : i ∈ (S.tree ω).path x
    · simp only [h, ite_true, mul_one]
      calc |(S.tree ω).out x - (S.tree ω).out (Function.update x i b)| ≤
            |(S.tree ω).out x| + |(S.tree ω).out (Function.update x i b)| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add (DTree.abs_out_le (hB ω) _) (DTree.abs_out_le (hB ω) _)
        _ = 2 := by norm_num
    · simp only [h, ite_false, mul_zero]
      rw [(DTree.out_path_update_of_not_mem_path h b).1, sub_self, abs_zero]
  rw [← Finset.sum_sub_distrib]
  calc |∑ ω, (S.p ω * (S.tree ω).out x - S.p ω * (S.tree ω).out (Function.update x i b))| / 2
      ≤ (∑ ω, |S.p ω * (S.tree ω).out x - S.p ω * (S.tree ω).out (Function.update x i b)|) /
          2 := by gcongr; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ ω, S.p ω * (2 * (if i ∈ (S.tree ω).path x then 1 else 0))) / 2 := by
        gcongr with ω
        rw [← mul_sub, abs_mul, abs_of_nonneg (S.p_nonneg ω)]
        exact mul_le_mul_of_nonneg_left (hpt ω) (S.p_nonneg ω)
    _ = ∑ ω, S.p ω * (if i ∈ (S.tree ω).path x then 1 else 0) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun ω _ => ?_
        ring

/-- Summing the coupling inequality over coordinates: the conditional expected number of
distinct probes on `x` is at least the sum of the total-variation distances to the
one-coordinate changes of `x`.

Paper: summation step after `eq:main-coupling` (exact_sampling_networks.tex); proof of
`thm:attentionpositionlower` (attention_primitives.tex). -/
theorem cost_ge_sum_signTV {ι : Type*} [Fintype ι] (S : Sampler m ι) (hB : S.Bounded)
    {f : (Fin m → Bool) → ℝ} (hf : S.Exact f) (x : Fin m → Bool) (b : Fin m → Bool) :
    ∑ i, signTV (f x) (f (Function.update x i (b i))) ≤ S.cost x := by
  rw [S.cost_eq_sum_probe]
  exact Finset.sum_le_sum fun i _ => coupling S hB hf x i (b i)

/-! ## Elementary facts about `tanh` -/

/-- `tanh' = 1 - tanh²`. Auxiliary for `eq:chainlower` and `prop:evaluation`
(tanh_lower.tex). -/
lemma hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have h : Real.tanh = Real.sinh / Real.cosh := by
    funext y; rw [Pi.div_apply, Real.tanh_eq_sinh_div_cosh]
  have hc := (Real.cosh_pos x).ne'
  have hd := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  rw [← h] at hd
  refine hd.congr_deriv ?_
  rw [Real.tanh_eq_sinh_div_cosh, div_pow]
  field_simp

/-- `tanh` is strictly increasing. Auxiliary for `eq:tanhlower` and `eq:chainlower`
(tanh_lower.tex). -/
lemma tanh_strictMono : StrictMono Real.tanh :=
  strictMono_of_hasDerivAt_pos hasDerivAt_tanh fun x => by
    have := Real.tanh_sq_lt_one x; linarith

/-- `tanh` is positive on positive arguments. Auxiliary for `eq:chainlower` (tanh_lower.tex). -/
lemma tanh_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  have := tanh_strictMono hx; rwa [Real.tanh_zero] at this

/-- `tanh` is nonnegative on nonnegative arguments. Auxiliary for `eq:chainlower`
(tanh_lower.tex). -/
lemma tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  rcases hx.lt_or_eq with h | h
  · exact (tanh_pos h).le
  · rw [← h, Real.tanh_zero]

/-- `tanh u ≥ u / √(1 + u²)` for `u ≥ 0`.

Paper: `eq:tanhlower` (tanh_lower.tex). -/
lemma tanh_ge_div_sqrt {u : ℝ} (hu : 0 ≤ u) : u / Real.sqrt (1 + u ^ 2) ≤ Real.tanh u := by
  rw [← Real.tanh_arsinh]
  apply tanh_strictMono.monotone
  calc Real.arsinh u ≤ Real.arsinh (Real.sinh u) :=
        Real.arsinh_le_arsinh.mpr (Real.self_le_sinh_iff.mpr hu)
    _ = u := Real.arsinh_sinh u

/-- The secant-squared lower bound `tanh v - tanh u ≥ (v - u)/4` on `[-1,1]`, from
`cosh 1 < 2`. Paper: proofs of `prop:evaluation` (tanh_lower.tex) and
`thm:attentionpositionlower` (attention_primitives.tex). -/
lemma tanh_sub_ge {u v : ℝ} (hu : -1 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    (v - u) / 4 ≤ Real.tanh v - Real.tanh u := by
  have hsq : ∀ w, -1 ≤ w → w ≤ 1 → Real.tanh w ^ 2 ≤ 3 / 4 := by
    intro w hw1 hw2
    have hc : Real.cosh w ≤ 2 := by
      have h1 : Real.cosh w ≤ Real.exp (w ^ 2 / 2) := Real.cosh_le_exp_half_sq w
      have h2 : w ^ 2 / 2 ≤ 1 / 2 := by nlinarith
      have h3 : Real.exp (1 / 2) ≤ 2 := by
        have := Real.exp_one_lt_d9
        have h4 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
          rw [← Real.exp_nat_mul]; norm_num
        nlinarith [Real.exp_pos (1 / 2)]
      linarith [Real.exp_le_exp.mpr h2]
    have hpos := Real.cosh_pos w
    have ht : Real.tanh w ^ 2 = 1 - 1 / Real.cosh w ^ 2 := by
      rw [Real.tanh_eq_sinh_div_cosh, div_pow, Real.cosh_sq]
      field_simp
      ring
    rw [ht]
    have : 1 / 4 ≤ 1 / Real.cosh w ^ 2 := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    linarith
  -- `g w = tanh w - w/4` is monotone on `[-1,1]`
  have hmono : MonotoneOn (fun w => Real.tanh w - w / 4) (Set.Icc (-1) 1) := by
    have hd : ∀ w, HasDerivAt (fun w => Real.tanh w - w / 4) (1 - Real.tanh w ^ 2 - 1 / 4) w :=
      fun w => (hasDerivAt_tanh w).sub ((hasDerivAt_id w).div_const 4)
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact fun w _ => (hd w).continuousAt.continuousWithinAt
    · exact fun w _ => (hd w).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      rw [(hd w).deriv]
      have := hsq w hw.1.le hw.2.le
      linarith
  have := hmono ⟨hu, huv.trans hv⟩ ⟨hu.trans huv, hv⟩ huv
  simp only at this
  linarith

/-! ## The scalar mean chain -/

/-- The mean chain `F_{a,0}(z) = z`, `F_{a,d+1}(z) = tanh(a F_{a,d}(z))`. -/
def F (a : ℝ) : ℕ → ℝ → ℝ
  | 0, z => z
  | d + 1, z => Real.tanh (a * F a d z)

/-- `H_D = ∑_{j<D} a^{-2j}`. -/
def HD (a : ℝ) (D : ℕ) : ℝ := ∑ j ∈ Finset.range D, ((a ^ 2)⁻¹) ^ j

/-- The mean chain is odd ("Oddness handles negative `z`"). Auxiliary for `eq:chainlower` and
`thm:lower` (tanh_lower.tex). -/
lemma F_neg (a : ℝ) (d : ℕ) (z : ℝ) : F a d (-z) = -F a d z := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [F, ih, mul_neg, Real.tanh_neg]

/-- The mean chain is monotone for `a ≥ 0`. Auxiliary for the range bound `|H(t)| ≤ R_D` in the
proof of `thm:lower` (tanh_lower.tex). -/
lemma F_mono {a : ℝ} (ha : 0 ≤ a) (d : ℕ) : Monotone (F a d) := by
  induction d with
  | zero => exact monotone_id
  | succ d ih =>
    intro z w h
    exact tanh_strictMono.monotone (mul_le_mul_of_nonneg_left (ih h) ha)

/-- The mean chain is positive on positive arguments. Auxiliary for `eq:chainlower`
(tanh_lower.tex). -/
lemma F_pos {a : ℝ} (ha : 0 < a) (d : ℕ) {z : ℝ} (hz : 0 < z) : 0 < F a d z := by
  induction d with
  | zero => exact hz
  | succ d ih => exact tanh_pos (mul_pos ha ih)

/-- The recursion `H_{D+1} = 1 + a^{-2} H_D`. Auxiliary for the reciprocal-square induction of
`eq:chainlower` (tanh_lower.tex). -/
lemma HD_succ (a : ℝ) (D : ℕ) : HD a (D + 1) = 1 + (a ^ 2)⁻¹ * HD a D := by
  unfold HD
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_succ, pow_zero]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The reciprocal-square induction behind the chain lower bound. Paper: "induction in the
reciprocal square" for `eq:chainlower` (tanh_lower.tex). -/
lemma F_recip_sq {a : ℝ} (ha : 0 < a) {z : ℝ} (hz : 0 < z) (D : ℕ) :
    1 / F a D z ^ 2 ≤ ((a ^ 2)⁻¹) ^ D / z ^ 2 + HD a D := by
  induction D with
  | zero => simp [F, HD]
  | succ d ih =>
    have hF := F_pos ha d hz
    set w := a * F a d z with hw
    have hwpos : 0 < w := mul_pos ha hF
    have ht := tanh_ge_div_sqrt hwpos.le
    have hsq : 0 < Real.sqrt (1 + w ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have hlow : 0 < w / Real.sqrt (1 + w ^ 2) := div_pos hwpos hsq
    have hstep : 1 / Real.tanh w ^ 2 ≤ 1 / w ^ 2 + 1 := by
      have h1 : (w / Real.sqrt (1 + w ^ 2)) ^ 2 ≤ Real.tanh w ^ 2 :=
        pow_le_pow_left₀ hlow.le ht 2
      have h2 : (w / Real.sqrt (1 + w ^ 2)) ^ 2 = w ^ 2 / (1 + w ^ 2) := by
        rw [div_pow, Real.sq_sqrt (by positivity)]
      rw [h2] at h1
      calc 1 / Real.tanh w ^ 2 ≤ 1 / (w ^ 2 / (1 + w ^ 2)) :=
            one_div_le_one_div_of_le (by positivity) h1
        _ = 1 / w ^ 2 + 1 := by field_simp
    have hrw : 1 / w ^ 2 = (a ^ 2)⁻¹ * (1 / F a d z ^ 2) := by
      rw [hw]; field_simp
    show 1 / Real.tanh w ^ 2 ≤ _
    rw [HD_succ]
    calc 1 / Real.tanh w ^ 2 ≤ 1 / w ^ 2 + 1 := hstep
      _ = (a ^ 2)⁻¹ * (1 / F a d z ^ 2) + 1 := by rw [hrw]
      _ ≤ (a ^ 2)⁻¹ * (((a ^ 2)⁻¹) ^ d / z ^ 2 + HD a d) + 1 := by
          gcongr
      _ = ((a ^ 2)⁻¹) ^ (d + 1) / z ^ 2 + (1 + (a ^ 2)⁻¹ * HD a d) := by ring

/-- `H_D ≥ 0`. Auxiliary for `eq:chainlower` (tanh_lower.tex). -/
lemma HD_nonneg (a : ℝ) (D : ℕ) : 0 ≤ HD a D :=
  Finset.sum_nonneg fun j _ => pow_nonneg (inv_nonneg.mpr (sq_nonneg a)) j

/-- The chain lower bound `F_D(z) ≥ a^D z / √(1 + a^{2D} H_D z²)` for `z > 0`.

Paper: `eq:chainlower` (tanh_lower.tex). -/
theorem chain_lower {a : ℝ} (ha : 0 < a) {z : ℝ} (hz : 0 < z) (D : ℕ) :
    a ^ D * z / Real.sqrt (1 + a ^ (2 * D) * HD a D * z ^ 2) ≤ F a D z := by
  have hF := F_pos ha D hz
  have hrec := F_recip_sq ha hz D
  have hH := HD_nonneg a D
  have hK : 0 < 1 + a ^ (2 * D) * HD a D * z ^ 2 := by positivity
  apply le_of_pow_le_pow_left₀ two_ne_zero hF.le
  rw [div_pow, Real.sq_sqrt hK.le]
  have hA : (0 : ℝ) < a ^ (2 * D) := by positivity
  have hinv : ((a ^ 2)⁻¹) ^ D * a ^ (2 * D) = 1 := by
    rw [inv_pow, ← pow_mul, mul_comm 2 D]; exact inv_mul_cancel₀ (by positivity)
  -- `1/F² ≤ (1 + A H z²) / (A z²)`
  have h1 : 1 / F a D z ^ 2 ≤ (1 + a ^ (2 * D) * HD a D * z ^ 2) / (a ^ (2 * D) * z ^ 2) := by
    calc 1 / F a D z ^ 2 ≤ ((a ^ 2)⁻¹) ^ D / z ^ 2 + HD a D := hrec
      _ = (1 + a ^ (2 * D) * HD a D * z ^ 2) / (a ^ (2 * D) * z ^ 2) := by
          have hr : ((a ^ 2)⁻¹) ^ D = 1 / a ^ (2 * D) := by
            rw [inv_pow, ← pow_mul, one_div]
          rw [hr]
          field_simp
  have hpos2 : 0 < F a D z ^ 2 := by positivity
  rw [div_le_div_iff₀ hpos2 (by positivity)] at h1
  rw [mul_pow, ← pow_mul, mul_comm D 2, div_le_iff₀ hK]
  linarith

/-! ## Uniform-law moments of the sign sum -/

/-- The sum `T(x) = ∑ᵢ xᵢ` of the input signs. -/
def signSum (x : Fin m → Bool) : ℝ := ∑ i, sgn (x i)

/-- `T_m ≤ m`. Auxiliary for the proofs of `thm:lower` and `prop:evaluation` (tanh_lower.tex). -/
lemma signSum_le (x : Fin m → Bool) : signSum x ≤ m := by
  unfold signSum
  calc ∑ i, sgn (x i) ≤ ∑ _i : Fin m, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => by cases x i <;> norm_num [sgn]
    _ = m := by simp

/-- `T_m ≥ -m`. Auxiliary for the proof of `prop:evaluation` (tanh_lower.tex). -/
lemma neg_le_signSum (x : Fin m → Bool) : -(m : ℝ) ≤ signSum x := by
  unfold signSum
  calc -(m : ℝ) = ∑ _i : Fin m, (-1 : ℝ) := by simp
    _ ≤ ∑ i, sgn (x i) := Finset.sum_le_sum fun i _ => by cases x i <;> norm_num [sgn]

/-- Splitting off the first input bit. Auxiliary for the moments `E T_m² = m`, `E T_m⁴ = 3m² -
2m` in the proof of `thm:lower` (tanh_lower.tex). -/
lemma sum_cons {n : ℕ} (g : (Fin (n + 1) → Bool) → ℝ) :
    ∑ x, g x = ∑ b : Bool, ∑ x : Fin n → Bool, g (Fin.cons b x) := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The sign sum after splitting off the first bit. Auxiliary for the moment computation in the
proof of `thm:lower` (tanh_lower.tex). -/
lemma signSum_cons {n : ℕ} (b : Bool) (x : Fin n → Bool) :
    signSum (Fin.cons b x : Fin (n + 1) → Bool) = sgn b + signSum x := by
  unfold signSum
  rw [Fin.sum_univ_succ]
  simp

/-- `∑ₓ T(x)² = n 2ⁿ`. Auxiliary for `E T_m² = m` in the proof of `thm:lower` (tanh_lower.tex). -/
lemma sum_signSum_sq : ∀ n : ℕ, ∑ x : Fin n → Bool, signSum x ^ 2 = n * 2 ^ n
  | 0 => by simp [signSum]
  | n + 1 => by
    rw [sum_cons]
    simp only [signSum_cons, Fintype.sum_bool, sgn_true, sgn_false]
    have h := sum_signSum_sq n
    have hc : ∑ _x : Fin n → Bool, (1 : ℝ) = 2 ^ n := by simp
    have e : ∀ x : Fin n → Bool, (1 + signSum x) ^ 2 + (-1 + signSum x) ^ 2 =
        2 * signSum x ^ 2 + 2 * 1 := fun x => by ring
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun x _ => e x,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h, hc]
    push_cast
    ring

/-- `∑ₓ T(x)⁴ = (3n² - 2n) 2ⁿ`. Auxiliary for `E T_m⁴ = 3m² - 2m` in the proof of `thm:lower`
(tanh_lower.tex). -/
lemma sum_signSum_four : ∀ n : ℕ,
    ∑ x : Fin n → Bool, signSum x ^ 4 = (3 * n ^ 2 - 2 * n) * 2 ^ n
  | 0 => by simp [signSum]
  | n + 1 => by
    rw [sum_cons]
    simp only [signSum_cons, Fintype.sum_bool, sgn_true, sgn_false]
    have h := sum_signSum_four n
    have h2 := sum_signSum_sq n
    have hc : ∑ _x : Fin n → Bool, (1 : ℝ) = 2 ^ n := by simp
    have e : ∀ x : Fin n → Bool, (1 + signSum x) ^ 4 + (-1 + signSum x) ^ 4 =
        2 * signSum x ^ 4 + (12 * signSum x ^ 2 + 2 * 1) := fun x => by ring
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun x _ => e x,
      Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, h, h2, hc]
    push_cast
    ring

/-- The fair product law is uniform. Auxiliary for the proof of `thm:lower` (tanh_lower.tex). -/
lemma prodLaw_zero (x : Fin m → Bool) : prodLaw (fun _ => 0) x = (1 / 2) ^ m := by
  simp [prodLaw, Finset.prod_const]

/-- Expectation under the fair product law. Auxiliary for the proof of `thm:lower`
(tanh_lower.tex). -/
lemma prodExp_zero (g : (Fin m → Bool) → ℝ) :
    prodExp (fun _ => 0) g = (1 / 2) ^ m * ∑ x, g x := by
  unfold prodExp
  simp_rw [prodLaw_zero]
  rw [Finset.mul_sum]

/-- Under the uniform law, `E T_m² = m`. Paper: proof of `thm:lower`, tanh_lower.tex. -/
lemma uniform_second_moment : prodExp (fun _ => 0) (fun x : Fin m → Bool => signSum x ^ 2) = m := by
  rw [prodExp_zero, sum_signSum_sq]
  have h2 : (1 / 2 : ℝ) ^ m * 2 ^ m = 1 := by rw [← mul_pow]; norm_num
  calc (1 / 2 : ℝ) ^ m * (m * 2 ^ m) = m * ((1 / 2) ^ m * 2 ^ m) := by ring
    _ = m := by rw [h2, mul_one]

/-- Under the uniform law, `E T_m⁴ = 3m² - 2m`. Paper: proof of `thm:lower`, tanh_lower.tex. -/
lemma uniform_fourth_moment :
    prodExp (fun _ => 0) (fun x : Fin m → Bool => signSum x ^ 4) = 3 * m ^ 2 - 2 * m := by
  rw [prodExp_zero, sum_signSum_four]
  have h2 : (1 / 2 : ℝ) ^ m * 2 ^ m = 1 := by rw [← mul_pow]; norm_num
  calc (1 / 2 : ℝ) ^ m * ((3 * (m : ℝ) ^ 2 - 2 * m) * 2 ^ m) =
        (3 * (m : ℝ) ^ 2 - 2 * m) * ((1 / 2) ^ m * 2 ^ m) := by ring
    _ = 3 * (m : ℝ) ^ 2 - 2 * m := by rw [h2, mul_one]

/-! ## The derivative of the input likelihood at zero -/

/-- The derivative of the input likelihood at the fair point is `2^{-m} T(x)`. Paper: "the
derivative of the input likelihood at zero is `T_m`", proof of `thm:lower` (tanh_lower.tex). -/
lemma hasDerivAt_prodLaw_zero (x : Fin m → Bool) :
    HasDerivAt (fun t => prodLaw (fun _ => t) x) ((1 / 2) ^ m * signSum x) 0 := by
  classical
  unfold prodLaw
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ) (x := (0 : ℝ))
    (f := fun i t => (1 + t * sgn (x i)) / 2) (f' := fun i => sgn (x i) / 2)
    (fun i _ => by
      simpa using ((hasDerivAt_mul_const (sgn (x i))).const_add 1).div_const 2)
  refine h.congr_deriv ?_
  simp only [zero_mul, add_zero, smul_eq_mul, Finset.prod_const]
  cases m with
  | zero => simp [signSum]
  | succ k =>
    simp only [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, Nat.add_sub_cancel]
    unfold signSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ]
    ring

/-- `H'(0) = E₀[f(X) T_m]`: differentiating the input likelihood at the fair point.
Paper: proof of `thm:lower` (tanh_lower.tex). -/
lemma hasDerivAt_meanProfile_zero (f : (Fin m → Bool) → ℝ) :
    HasDerivAt (meanProfile f) (prodExp (fun _ => 0) (fun x => f x * signSum x)) 0 := by
  unfold meanProfile prodExp
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun x _ => (hasDerivAt_prodLaw_zero x).mul_const (f x))
  refine h.congr_deriv ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [prodLaw_zero]
  ring

/-! ## A weighted Jensen step -/

/-- Tangent-line form of the convexity of `v ↦ (1 + c v)^{-1/2}`. Auxiliary for the Jensen step
of `eq:derivativelower` (tanh_lower.tex). -/
lemma tangent_line {c X v₀ : ℝ} (hc : 0 ≤ c) (hX : 0 ≤ X) (hv : 0 ≤ v₀) :
    1 / Real.sqrt (1 + c * v₀) -
        c * (X - v₀) / (2 * (1 + c * v₀) * Real.sqrt (1 + c * v₀)) ≤
      1 / Real.sqrt (1 + c * X) := by
  set α := Real.sqrt (1 + c * X) with hα
  set β := Real.sqrt (1 + c * v₀) with hβ
  have hα2 : α ^ 2 = 1 + c * X := Real.sq_sqrt (by positivity)
  have hβ2 : β ^ 2 = 1 + c * v₀ := Real.sq_sqrt (by positivity)
  have hαp : 0 < α := Real.sqrt_pos.mpr (by positivity)
  have hβp : 0 < β := Real.sqrt_pos.mpr (by positivity)
  have hlhs : 1 / β - c * (X - v₀) / (2 * (1 + c * v₀) * β) =
      (3 * β ^ 2 - α ^ 2) / (2 * β ^ 3) := by
    rw [← hβ2, show c * (X - v₀) = α ^ 2 - β ^ 2 by rw [hα2, hβ2]; ring]
    field_simp
    ring
  rw [hlhs, div_le_div_iff₀ (by positivity) hαp]
  nlinarith [mul_nonneg (sq_nonneg (α - β)) (add_pos hαp (mul_pos two_pos hβp)).le]

/-- `E₀[T²/√(1 + c T²)] ≥ m / √(1 + c(3m - 2))`: weight the uniform law by `T²/m`, whose
mean value of `T²` is `3m - 2`, and use convexity.

Paper: second line of `eq:derivativelower` (tanh_lower.tex). -/
lemma jensen_step (hm : 1 ≤ m) {c : ℝ} (hc : 0 ≤ c) :
    m / Real.sqrt (1 + c * (3 * m - 2)) ≤
      prodExp (fun _ => 0)
        (fun x : Fin m → Bool => signSum x ^ 2 / Real.sqrt (1 + c * signSum x ^ 2)) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set v₀ : ℝ := 3 * m - 2 with hv₀
  have hv : 0 ≤ v₀ := by rw [hv₀]; linarith
  set β := Real.sqrt (1 + c * v₀)
  have hβp : 0 < β := Real.sqrt_pos.mpr (by positivity)
  have hpt : ∀ x : Fin m → Bool, signSum x ^ 2 * (1 / β) -
      (c / (2 * (1 + c * v₀) * β)) * (signSum x ^ 4 - v₀ * signSum x ^ 2) ≤
      signSum x ^ 2 / Real.sqrt (1 + c * signSum x ^ 2) := by
    intro x
    have h := tangent_line hc (sq_nonneg (signSum x)) hv
    have hX := sq_nonneg (signSum x)
    have := mul_le_mul_of_nonneg_left h hX
    calc signSum x ^ 2 * (1 / β) -
          (c / (2 * (1 + c * v₀) * β)) * (signSum x ^ 4 - v₀ * signSum x ^ 2) =
          signSum x ^ 2 * (1 / β - c * (signSum x ^ 2 - v₀) / (2 * (1 + c * v₀) * β)) := by
            ring
      _ ≤ signSum x ^ 2 * (1 / Real.sqrt (1 + c * signSum x ^ 2)) := this
      _ = signSum x ^ 2 / Real.sqrt (1 + c * signSum x ^ 2) := by ring
  have hmono := prodExp_mono (s := fun _ => (0 : ℝ)) (fun _ => by norm_num) hpt
  have hlin : prodExp (fun _ => 0) (fun x : Fin m → Bool => signSum x ^ 2 * (1 / β) -
      (c / (2 * (1 + c * v₀) * β)) * (signSum x ^ 4 - v₀ * signSum x ^ 2)) =
      m * (1 / β) - (c / (2 * (1 + c * v₀) * β)) * ((3 * m ^ 2 - 2 * m) - v₀ * m) := by
    have e : (fun x : Fin m → Bool => signSum x ^ 2 * (1 / β) -
        (c / (2 * (1 + c * v₀) * β)) * (signSum x ^ 4 - v₀ * signSum x ^ 2)) =
        fun x => (1 / β - (c / (2 * (1 + c * v₀) * β)) * (-v₀)) * signSum x ^ 2 +
          (-(c / (2 * (1 + c * v₀) * β))) * signSum x ^ 4 := by
      funext x; ring
    rw [e, prodExp_add, prodExp_mul_const, prodExp_mul_const, uniform_second_moment,
      uniform_fourth_moment]
    ring
  rw [hlin] at hmono
  have hz : (3 * m ^ 2 - 2 * m : ℝ) - v₀ * m = 0 := by rw [hv₀]; ring
  rw [hz, mul_zero, sub_zero] at hmono
  calc (m : ℝ) / β = m * (1 / β) := by ring
    _ ≤ _ := hmono

/-! ## Universal lower bounds for the mean chain -/

/-- The mean-chain target `F_{a,D}(m⁻¹ ∑ⱼ xⱼ)`. -/
def chainTarget (a : ℝ) (D : ℕ) (x : Fin m → Bool) : ℝ := F a D (signSum x / m)

/-- Pointwise comparison `F_D(T/m) T ≥ (a^D/m) T² / √(1 + c T²)` with
`c = a^{2D} H_D / m²`, from `eq:chainlower` and oddness. -/
lemma chainTarget_mul_signSum_ge {a : ℝ} (ha : 0 < a) (hm : 1 ≤ m) (D : ℕ)
    (x : Fin m → Bool) :
    a ^ D / m * (signSum x ^ 2 /
        Real.sqrt (1 + a ^ (2 * D) * HD a D / (m : ℝ) ^ 2 * signSum x ^ 2)) ≤
      chainTarget a D x * signSum x := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold chainTarget
  set T := signSum x
  have hK : ∀ z : ℝ, 1 + a ^ (2 * D) * HD a D * z ^ 2 =
      1 + a ^ (2 * D) * HD a D / (m : ℝ) ^ 2 * (m * z) ^ 2 := fun z => by
    field_simp
  rcases lt_trichotomy T 0 with hT | hT | hT
  · have hz : 0 < -T / m := div_pos (neg_pos.mpr hT) hm'
    have h := chain_lower ha hz D
    rw [hK, show (m : ℝ) * (-T / m) = -T by field_simp, neg_sq] at h
    have hneg : F a D (T / m) = -F a D (-T / m) := by
      rw [show -T / m = -(T / m) by ring, F_neg, neg_neg]
    rw [hneg]
    have := mul_le_mul_of_nonneg_left h (neg_pos.mpr hT).le
    calc a ^ D / m * (T ^ 2 / Real.sqrt (1 + a ^ (2 * D) * HD a D / (m : ℝ) ^ 2 * T ^ 2)) =
          -T * (a ^ D * (-T / m) /
            Real.sqrt (1 + a ^ (2 * D) * HD a D / (m : ℝ) ^ 2 * T ^ 2)) := by ring
      _ ≤ -T * F a D (-T / m) := this
      _ = -F a D (-T / m) * T := by ring
  · rw [hT]; simp
  · have hz : 0 < T / m := div_pos hT hm'
    have h := chain_lower ha hz D
    rw [hK, show (m : ℝ) * (T / m) = T by field_simp] at h
    have := mul_le_mul_of_nonneg_left h hT.le
    calc a ^ D / m * (T ^ 2 / Real.sqrt (1 + a ^ (2 * D) * HD a D / (m : ℝ) ^ 2 * T ^ 2)) =
          T * (a ^ D * (T / m) /
            Real.sqrt (1 + a ^ (2 * D) * HD a D / (m : ℝ) ^ 2 * T ^ 2)) := by ring
      _ ≤ T * F a D (T / m) := this
      _ = F a D (T / m) * T := by ring

/-- `H'(0) ≥ a^D / √(1 + c(3m - 2))` with `c = a^{2D} H_D / m²`.

Paper: `eq:derivativelower` (tanh_lower.tex). -/
theorem derivative_lower {a : ℝ} (ha : 0 < a) (hm : 1 ≤ m) (D : ℕ) :
    a ^ D / Real.sqrt (1 + a ^ (2 * D) * HD a D / (m : ℝ) ^ 2 * (3 * m - 2)) ≤
      deriv (meanProfile (chainTarget a D : (Fin m → Bool) → ℝ)) 0 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [(hasDerivAt_meanProfile_zero _).deriv]
  set c := a ^ (2 * D) * HD a D / (m : ℝ) ^ 2
  have hc : 0 ≤ c := by have := HD_nonneg a D; positivity
  have h1 := prodExp_mono (s := fun _ => (0 : ℝ)) (fun _ => by norm_num)
    (chainTarget_mul_signSum_ge ha hm D)
  rw [prodExp_mul_const] at h1
  have h2 := jensen_step hm hc
  calc a ^ D / Real.sqrt (1 + c * (3 * m - 2)) =
        a ^ D / m * (m / Real.sqrt (1 + c * (3 * m - 2))) := by field_simp
    _ ≤ a ^ D / m * prodExp (fun _ => 0)
          (fun x : Fin m → Bool => signSum x ^ 2 / Real.sqrt (1 + c * signSum x ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ _ := h1

/-- **Universal query lower bound (exact form).** For the mean chain on `m ≥ 1` input signs and
every `a > 0`, every exact sampler has some context `x` with
`E[Q | x] ≥ a^{2D} / (1 + (3m - 2) a^{2D} H_D / m²)`.

Paper: `thm:lower`, `eq:lowerexact` (tanh_model.tex; proof in tanh_lower.tex). This is also the
lower bound for the second network of `prop:magnitude-obstruction` (instance_information.tex),
whose output is the mean chain. -/
theorem lower_exact {ι : Type*} [Fintype ι] (S : Sampler m ι) (hN : S.NoRepeat)
    (hB : S.Bounded) {a : ℝ} (ha : 0 < a) (hm : 1 ≤ m) (D : ℕ)
    (hf : S.Exact (chainTarget a D)) :
    ∃ x, a ^ (2 * D) / (1 + (3 * m - 2) * a ^ (2 * D) * HD a D / (m : ℝ) ^ 2) ≤ S.cost x := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨-, h2, -⟩ := transcript S hN hB hf (t := 0) (by norm_num)
  have hd := derivative_lower ha hm D
  set c := a ^ (2 * D) * HD a D / (m : ℝ) ^ 2
  have hc : 0 ≤ c := by have := HD_nonneg a D; positivity
  have hK : 0 < 1 + c * (3 * m - 2) := by nlinarith
  have hsq : a ^ (2 * D) / (1 + c * (3 * m - 2)) ≤
      deriv (meanProfile (chainTarget a D : (Fin m → Bool) → ℝ)) 0 ^ 2 := by
    have h0 : 0 ≤ a ^ D / Real.sqrt (1 + c * (3 * m - 2)) := by positivity
    have := pow_le_pow_left₀ h0 hd 2
    rwa [div_pow, Real.sq_sqrt hK.le, ← pow_mul, mul_comm D 2] at this
  obtain ⟨x, hx⟩ := exists_ge_prodExp (s := fun _ => (0 : ℝ)) (fun _ => by norm_num) S.cost
  refine ⟨x, ?_⟩
  have he : 1 + (3 * m - 2) * a ^ (2 * D) * HD a D / (m : ℝ) ^ 2 = 1 + c * (3 * m - 2) := by
    simp only [c]; ring
  rw [he]
  simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, one_mul] at h2
  unfold expCost at h2
  linarith

/-- `H_D ≤ a²/(a² - 1)` for `a > 1`. Paper: proof of `eq:lowersuper` (tanh_lower.tex). -/
lemma HD_le {a : ℝ} (ha : 1 < a) (D : ℕ) : HD a D ≤ a ^ 2 / (a ^ 2 - 1) := by
  have ha2 : 1 < a ^ 2 := by nlinarith
  set r := (a ^ 2)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ ha2
  have hgeom : HD a D * (1 - r) = 1 - r ^ D := by
    unfold HD
    rw [← hr]
    induction D with
    | zero => simp
    | succ d ih => rw [Finset.sum_range_succ, add_mul, ih]; ring
  have : HD a D * (1 - r) ≤ 1 := by rw [hgeom]; linarith [pow_nonneg hr0 D]
  have h1r : 0 < 1 - r := by linarith
  have hval : 1 / (1 - r) = a ^ 2 / (a ^ 2 - 1) := by
    rw [hr]; field_simp
  rw [← hval, le_div_iff₀ h1r]
  linarith

/-- The elementary minimum comparison `A/(1 + C A/m) ≥ min{A, m}/(1 + C)`.

Paper: proof of `eq:lowersuper` (tanh_lower.tex). -/
lemma rational_bound_ge_min {A M C : ℝ} (hA : 0 < A) (hM : 0 < M) (hC : 0 ≤ C) :
    min A M / (1 + C) ≤ A / (1 + C * A / M) := by
  have hden : 0 < 1 + C * A / M := by positivity
  rcases le_total A M with hAM | hMA
  · rw [min_eq_left hAM]
    have hratio : C * A / M ≤ C := by
      rw [div_le_iff₀ hM]; nlinarith
    exact div_le_div_of_nonneg_left hA.le hden (by linarith)
  · rw [min_eq_right hMA, div_le_div_iff₀ (by linarith) hden]
    have hcancel : M * (C * A / M) = C * A := by field_simp
    nlinarith

/-- **Universal query lower bound above unit norm.** For `a > 1`, every exact sampler for the
mean chain has a context with `E[Q | x] ≥ (a² - 1)/(4a² - 1) · min{a^{2D}, m}`.

Paper: `thm:lower`, `eq:lowersuper` (tanh_model.tex; proof in tanh_lower.tex); the `a > 1`
statement of `prop:magnitude-obstruction`. This is the finite-parameter input to the lower side
of `eq:explicitexponents` and the supercritical lower bound of `thm:main-depth`; the steps
`a^{2L} = s^{2L}(1 + o(1))` and the conversion to `n^{min(2 log₂ s, 1)}` are not formalized. -/
theorem lower_super {ι : Type*} [Fintype ι] (S : Sampler m ι) (hN : S.NoRepeat)
    (hB : S.Bounded) {a : ℝ} (ha : 1 < a) (hm : 1 ≤ m) (D : ℕ)
    (hf : S.Exact (chainTarget a D)) :
    ∃ x, (a ^ 2 - 1) / (4 * a ^ 2 - 1) * min (a ^ (2 * D)) m ≤ S.cost x := by
  obtain ⟨x, hx⟩ := lower_exact S hN hB (by linarith) hm D hf
  refine ⟨x, le_trans ?_ hx⟩
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ha2 : 1 < a ^ 2 := by nlinarith
  set A := a ^ (2 * D)
  have hA : 0 < A := by positivity
  set C := 3 * a ^ 2 / (a ^ 2 - 1)
  have hC : 0 ≤ C := by positivity
  have hmin := rational_bound_ge_min hA (by linarith : (0 : ℝ) < m) hC
  have hcoef : (a ^ 2 - 1) / (4 * a ^ 2 - 1) = 1 / (1 + C) := by
    have h1C : 1 + C = (4 * a ^ 2 - 1) / (a ^ 2 - 1) := by
      simp only [C]
      have : a ^ 2 - 1 ≠ 0 := by linarith
      field_simp
      ring
    rw [h1C, one_div_div]
  have hden : (1 : ℝ) + (3 * m - 2) * A * HD a D / (m : ℝ) ^ 2 ≤ 1 + C * A / m := by
    have hH := HD_le ha D
    have hH0 := HD_nonneg a D
    have h1 : (3 * m - 2) / (m : ℝ) ^ 2 ≤ 3 / m := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have h2 : (3 * m - 2) * A * HD a D / (m : ℝ) ^ 2 =
        (3 * m - 2) / (m : ℝ) ^ 2 * (A * HD a D) := by ring
    have h3 : C * A / m = 3 / m * (A * (a ^ 2 / (a ^ 2 - 1))) := by simp only [C]; ring
    rw [h2, h3]
    have hAH : A * HD a D ≤ A * (a ^ 2 / (a ^ 2 - 1)) := mul_le_mul_of_nonneg_left hH hA.le
    have hpos : 0 ≤ (3 * m - 2) / (m : ℝ) ^ 2 := by
      apply div_nonneg _ (by positivity); linarith
    nlinarith [mul_le_mul h1 hAH (by positivity) (by positivity)]
  calc (a ^ 2 - 1) / (4 * a ^ 2 - 1) * min A m = min A m / (1 + C) := by rw [hcoef]; ring
    _ ≤ A / (1 + C * A / m) := hmin
    _ ≤ A / (1 + (3 * m - 2) * A * HD a D / (m : ℝ) ^ 2) := by
        apply div_le_div_of_nonneg_left hA.le _ hden
        have : 0 ≤ (3 * m - 2) * A * HD a D / (m : ℝ) ^ 2 := by
          have := HD_nonneg a D
          apply div_nonneg _ (by positivity)
          apply mul_nonneg (mul_nonneg (by linarith) hA.le) this
        linarith

/-! ## Curvature at unit norm -/

/-- `sinh r ≤ r + r³/6 + r⁵/100` on `[0,1]`, from the exponential series. Auxiliary for the
radius estimate in the proof of `thm:lower` (tanh_lower.tex). -/
lemma sinh_le_poly {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.sinh r ≤ r + r ^ 3 / 6 + r ^ 5 / 100 := by
  have h1 : |r| ≤ 1 := by rw [abs_of_nonneg hr0]; exact hr1
  have h2 : |-r| ≤ 1 := by rw [abs_neg]; exact h1
  have e1 := Real.exp_bound h1 (n := 5) (by norm_num)
  have e2 := Real.exp_bound h2 (n := 5) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, abs_neg,
    abs_of_nonneg hr0] at e1 e2
  norm_num at e1 e2
  rw [Real.sinh_eq]
  have := (abs_le.mp e1).2
  have := (abs_le.mp e2).1
  nlinarith

/-- `tanh² r ≤ r² / (1 + r²/6)` on `[0,1]`: one critical tanh step lowers the reciprocal square
of the radius by at least `1/6`. Auxiliary for the radius estimate `R_D ≤ √(6/(D + 6))` in the
proof of `thm:lower` (tanh_lower.tex). -/
lemma tanh_sq_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.tanh r ^ 2 ≤ r ^ 2 / (1 + r ^ 2 / 6) := by
  have hs := sinh_le_poly hr0 hr1
  have hs0 : 0 ≤ Real.sinh r := Real.sinh_nonneg_iff.mpr hr0
  have hc := Real.cosh_pos r
  rw [Real.tanh_eq_sinh_div_cosh, div_pow, div_le_div_iff₀ (by positivity) (by positivity),
    Real.cosh_sq]
  set S := Real.sinh r
  set y := r ^ 2 with hy
  have hy0 : 0 ≤ y := sq_nonneg r
  have hy1 : y ≤ 1 := by nlinarith
  -- `S ≤ r P` with `P = 1 + y/6 + y²/100`
  have hSP : S ≤ r * (1 + y / 6 + y ^ 2 / 100) := by
    calc S ≤ r + r ^ 3 / 6 + r ^ 5 / 100 := hs
      _ = r * (1 + y / 6 + y ^ 2 / 100) := by rw [hy]; ring
  have hP0 : 0 ≤ r * (1 + y / 6 + y ^ 2 / 100) := by positivity
  have hS2 : S ^ 2 ≤ y * (1 + y / 6 + y ^ 2 / 100) ^ 2 := by
    have := pow_le_pow_left₀ hs0 hSP 2
    calc S ^ 2 ≤ (r * (1 + y / 6 + y ^ 2 / 100)) ^ 2 := this
      _ = y * (1 + y / 6 + y ^ 2 / 100) ^ 2 := by rw [hy]; ring
  have hpoly : (1 + y / 6 + y ^ 2 / 100) ^ 2 * (1 - 5 * y / 6) ≤ 1 := by
    nlinarith [mul_nonneg hy0 hy0, mul_nonneg (mul_nonneg hy0 hy0) hy0,
      mul_nonneg (mul_nonneg hy0 hy0) (mul_nonneg hy0 hy0),
      mul_nonneg (mul_nonneg (mul_nonneg hy0 hy0) (mul_nonneg hy0 hy0)) hy0]
  have h56 : 0 ≤ 1 - 5 * y / 6 := by linarith
  have := mul_le_mul_of_nonneg_right hS2 h56
  nlinarith

/-- The critical radius `R_D = F_{1,D}(1)` satisfies `R_D² ≤ 6/(D + 6)`.

Paper: the radius estimate used in the curvature step of `thm:lower` (tanh_lower.tex). -/
lemma radius_sq_le (D : ℕ) : 0 < F 1 D 1 ∧ F 1 D 1 ≤ 1 ∧ F 1 D 1 ^ 2 ≤ 6 / (D + 6) := by
  have key : ∀ d : ℕ, 0 < F 1 d 1 ∧ F 1 d 1 ≤ 1 ∧ 1 + d / 6 ≤ 1 / F 1 d 1 ^ 2 := by
    intro d
    induction d with
    | zero => simp [F]
    | succ d ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      have hF : F 1 (d + 1) 1 = Real.tanh (F 1 d 1) := by simp [F]
      rw [hF]
      refine ⟨tanh_pos h0, (Real.tanh_lt_one _).le, ?_⟩
      have ht := tanh_sq_le h0.le h1
      have htp : 0 < Real.tanh (F 1 d 1) ^ 2 := by have := tanh_pos h0; positivity
      have : 1 / (F 1 d 1 ^ 2 / (1 + F 1 d 1 ^ 2 / 6)) ≤ 1 / Real.tanh (F 1 d 1) ^ 2 :=
        one_div_le_one_div_of_le htp ht
      have e : 1 / (F 1 d 1 ^ 2 / (1 + F 1 d 1 ^ 2 / 6)) = 1 / F 1 d 1 ^ 2 + 1 / 6 := by
        field_simp
      push_cast
      linarith
  obtain ⟨h0, h1, h2⟩ := key D
  refine ⟨h0, h1, ?_⟩
  have hp : 0 < F 1 D 1 ^ 2 := by positivity
  have h3 := mul_le_mul_of_nonneg_right h2 hp.le
  rw [one_div, inv_mul_cancel₀ hp.ne'] at h3
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- Bending forces curvature. If `H(0) = 0`, `H'(0) = h`, `hT = 2R` and `H(T) ≤ R`, then
`|H''(t)| ≥ h²/(2R)` at some `t ∈ [0,T]`. This replaces the integral form of Taylor's theorem.

Paper: the bending argument before `eq:bending` (tanh_lower.tex). -/
lemma bending {H H1 H2 : ℝ → ℝ} {h R T : ℝ} (hT : 0 < T) (hR : 0 < R)
    (hH : ∀ t, HasDerivAt H (H1 t) t) (hH1 : ∀ t, HasDerivAt H1 (H2 t) t)
    (h0 : H 0 = 0) (h1 : H1 0 = h) (hlin : h * T = 2 * R) (hend : H T ≤ R) :
    ∃ t ∈ Set.Icc 0 T, h ^ 2 / (2 * R) ≤ |H2 t| := by
  by_contra hcon
  push Not at hcon
  set K := h ^ 2 / (2 * R) with hK
  have hKT : K * T ^ 2 = 2 * R := by
    rw [hK]
    have : h ^ 2 * T ^ 2 = (h * T) ^ 2 := by ring
    field_simp
    rw [this, hlin]
    ring
  -- `H1 t + K t` is strictly increasing on `[0,T]`
  have hd1 : ∀ t, HasDerivAt (fun t => H1 t + K * t) (H2 t + K * 1) t :=
    fun t => (hH1 t).add ((hasDerivAt_id' t).const_mul K)
  have hg1 : StrictMonoOn (fun t => H1 t + K * t) (Set.Icc 0 T) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 T) ?_ ?_
    · exact fun t _ => (hd1 t).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hd1 t).deriv]
      have := hcon t ⟨ht.1.le, ht.2.le⟩
      have := neg_abs_le (H2 t)
      linarith
  have hH1lb : ∀ t ∈ Set.Ioc 0 T, h - K * t < H1 t := by
    intro t ht
    have := hg1 ⟨le_refl 0, hT.le⟩ ⟨ht.1.le, ht.2⟩ ht.1
    simp only [mul_zero, add_zero, h1] at this
    linarith
  -- `H t - h t + K t²/2` is strictly increasing on `[0,T]`
  have hg2 : StrictMonoOn (fun t => H t - h * t + K * t ^ 2 / 2) (Set.Icc 0 T) := by
    have hd : ∀ t, HasDerivAt (fun t => H t - h * t + K * t ^ 2 / 2)
        (H1 t - h + K * t) t := by
      intro t
      have := ((hH t).sub ((hasDerivAt_id' t).const_mul h)).add
        (((hasDerivAt_pow 2 t).const_mul K).div_const 2)
      refine this.congr_deriv ?_
      push_cast
      ring
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 T) ?_ ?_
    · exact fun t _ => (hd t).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hd t).deriv]
      have := hH1lb t ⟨ht.1, ht.2.le⟩
      linarith
  have := hg2 ⟨le_refl 0, hT.le⟩ ⟨hT.le, le_refl T⟩ hT
  simp only [h0, mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div, add_zero] at this
  have hKT2 : K * T ^ 2 / 2 = R := by rw [hKT]; ring
  linarith

/-- **The bending bound.** Under the hypotheses of `bending` with `T ≤ 1/2`, any cost `M` with
`M ≥ (1 - t²)|H''(t)|/2` for every `t ∈ [0, T]` satisfies `M ≥ 3h²/(16R)`.

Paper: `eq:bending` (tanh_lower.tex). -/
theorem bending_cost {H H1 H2 : ℝ → ℝ} {h R T M : ℝ} (hT : 0 < T) (hT2 : T ≤ 1 / 2) (hR : 0 < R)
    (hH : ∀ t, HasDerivAt H (H1 t) t) (hH1 : ∀ t, HasDerivAt H1 (H2 t) t)
    (h0 : H 0 = 0) (h1 : H1 0 = h) (hlin : h * T = 2 * R) (hend : H T ≤ R)
    (hM : ∀ t ∈ Set.Icc 0 T, (1 - t ^ 2) / 2 * |H2 t| ≤ M) :
    3 * h ^ 2 / (16 * R) ≤ M := by
  obtain ⟨t, ht, hb⟩ := bending hT hR hH hH1 h0 h1 hlin hend
  have htt : t ^ 2 ≤ 1 / 4 := by nlinarith [ht.1, ht.2]
  have h34 : 3 / 8 ≤ (1 - t ^ 2) / 2 := by linarith
  calc 3 * h ^ 2 / (16 * R) = 3 / 8 * (h ^ 2 / (2 * R)) := by field_simp; ring
    _ ≤ (1 - t ^ 2) / 2 * |H2 t| := mul_le_mul h34 hb (by positivity) (by linarith)
    _ ≤ M := hM t ht

/-- The global sign flip `x ↦ -x`. -/
def negAll (x : Fin m → Bool) : Fin m → Bool := fun i => !x i

/-- The global sign flip is an involution. Auxiliary for `H(0) = 0` in the proof of `thm:lower`
(tanh_lower.tex). -/
lemma negAll_negAll (x : Fin m → Bool) : negAll (negAll x) = x := by
  funext i; simp [negAll]

/-- The global sign flip negates the sign sum. Auxiliary for `H(0) = 0` in the proof of
`thm:lower` (tanh_lower.tex). -/
lemma signSum_negAll (x : Fin m → Bool) : signSum (negAll x) = -signSum x := by
  unfold signSum negAll
  simp only [sgn_not, Finset.sum_neg_distrib]

/-- The mean-chain profile vanishes at the fair point. Paper: `H` is odd, proof of
`eq:lowercritical` (tanh_lower.tex). -/
lemma meanProfile_chain_zero (a : ℝ) (D : ℕ) :
    meanProfile (chainTarget a D : (Fin m → Bool) → ℝ) 0 = 0 := by
  unfold meanProfile
  rw [prodExp_zero]
  have hsum : ∑ x : Fin m → Bool, chainTarget a D x =
      ∑ x : Fin m → Bool, -chainTarget a D x := by
    refine Fintype.sum_bijective negAll (Function.Involutive.bijective negAll_negAll) _ _ ?_
    intro x
    simp only [chainTarget, signSum_negAll, neg_div, F_neg, neg_neg]
  rw [Finset.sum_neg_distrib] at hsum
  have : ∑ x : Fin m → Bool, chainTarget a D x = 0 := by linarith
  rw [this, mul_zero]

/-- The profile stays below the radius: `H(t) ≤ F_{a,D}(1)` for `|t| ≤ 1`. Paper: `|H(t)| ≤
R_D`, proof of `eq:lowercritical` (tanh_lower.tex). -/
lemma meanProfile_chain_le {a : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m) (D : ℕ) {t : ℝ} (ht : |t| ≤ 1) :
    meanProfile (chainTarget a D : (Fin m → Bool) → ℝ) t ≤ F a D 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold meanProfile
  calc prodExp (fun _ => t) (chainTarget a D) ≤ prodExp (fun _ => t) (fun _ => F a D 1) :=
        prodExp_mono (fun _ => ht) fun x => F_mono ha D (by
          rw [div_le_one hm']; exact signSum_le x)
    _ = F a D 1 := prodExp_const _ _

/-- **Universal query lower bound at unit norm.** For `a = 1` and `1 ≤ D ≤ m`, every exact
sampler for the critical mean chain has a context with `E[Q | x] ≥ √D / 100`.

Paper: `thm:lower`, `eq:lowercritical` (tanh_model.tex; proof in tanh_lower.tex); the
`Ω(√D)` lower bound in `thm:main-depth` (exact_sampling_networks.tex). -/
theorem lower_critical {ι : Type*} [Fintype ι] (S : Sampler m ι) (hN : S.NoRepeat)
    (hB : S.Bounded) {D : ℕ} (hD : 1 ≤ D) (hDm : D ≤ m) (hf : S.Exact (chainTarget 1 D)) :
    ∃ x, Real.sqrt D / 100 ≤ S.cost x := by
  have hm : 1 ≤ m := hD.trans hDm
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDm' : (D : ℝ) ≤ m := by exact_mod_cast hDm
  set f : (Fin m → Bool) → ℝ := chainTarget 1 D
  set H := meanProfile f
  set h := deriv H 0 with hh
  -- `h ≥ 1/2`
  have hHD : HD 1 D = D := by simp [HD]
  have hh2 : 1 / 2 ≤ h := by
    have hd := derivative_lower (m := m) (a := 1) one_pos hm D
    rw [one_pow, one_pow, hHD, one_mul] at hd
    have hnn : 0 ≤ (D : ℝ) / m ^ 2 * (3 * m - 2) :=
      mul_nonneg (by positivity) (by linarith)
    have hden : (D : ℝ) / m ^ 2 * (3 * m - 2) ≤ 3 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    have hsqrt : Real.sqrt (1 + (D : ℝ) / m ^ 2 * (3 * m - 2)) ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; linarith
    have hpos : 0 < Real.sqrt (1 + (D : ℝ) / m ^ 2 * (3 * m - 2)) :=
      Real.sqrt_pos.mpr (by linarith)
    calc (1 : ℝ) / 2 ≤ 1 / Real.sqrt (1 + (D : ℝ) / m ^ 2 * (3 * m - 2)) :=
          one_div_le_one_div_of_le hpos hsqrt
      _ ≤ h := hd
  have hders := meanProfile_hasDerivAt S hN hf
  by_cases hsmall : D < 384
  · -- the first transcript bound at the fair point
    obtain ⟨-, h2, -⟩ := transcript S hN hB hf (t := 0) (by norm_num)
    obtain ⟨x, hx⟩ := exists_ge_prodExp (s := fun _ => (0 : ℝ)) (fun _ => by norm_num) S.cost
    refine ⟨x, ?_⟩
    have hEQ : 1 / 4 ≤ expCost S 0 := by
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
        one_mul] at h2
      nlinarith
    have hs : Real.sqrt D ≤ 20 := by
      rw [Real.sqrt_le_left (by norm_num)]
      have : (D : ℝ) < 384 := by exact_mod_cast hsmall
      linarith
    unfold expCost at hEQ
    linarith
  · push Not at hsmall
    have hD384 : (384 : ℝ) ≤ D := by exact_mod_cast hsmall
    obtain ⟨hR0, -, hR2⟩ := radius_sq_le D
    set R := F 1 D 1
    have hR8 : R ≤ 1 / 8 := by
      have : R ^ 2 ≤ (1 / 8) ^ 2 := by
        calc R ^ 2 ≤ 6 / (D + 6) := hR2
          _ ≤ (1 / 8) ^ 2 := by rw [div_le_iff₀ (by positivity)]; nlinarith
      exact le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) this
    have hhpos : 0 < h := by linarith
    set T := 2 * R / h
    have hT0 : 0 < T := by positivity
    have hT2 : T ≤ 1 / 2 := by
      rw [div_le_iff₀ hhpos]; nlinarith
    have hend : H T ≤ R := meanProfile_chain_le zero_le_one hm D (by
      rw [abs_of_pos hT0]; linarith)
    obtain ⟨t, ht, hbend⟩ := bending (H := H) (H1 := deriv H) (H2 := deriv (deriv H)) hT0 hR0
      (fun t => (hders t).1) (fun t => (hders t).2) (meanProfile_chain_zero 1 D) hh.symm
      (by simp only [T]; field_simp) hend
    have ht1 : |t| < 1 := by rw [abs_of_nonneg ht.1]; linarith [ht.2]
    obtain ⟨-, -, h3⟩ := transcript S hN hB hf ht1
    obtain ⟨x, hx⟩ := exists_ge_prodExp (s := fun _ => t) (fun _ => ht1.le) S.cost
    refine ⟨x, ?_⟩
    have htt : t ^ 2 ≤ 1 / 4 := by nlinarith [ht.1, ht.2]
    -- `E_t Q ≥ 3 h²/(16 R) ≥ 3/(64 R)`
    have hcurv : 3 / (64 * R) ≤ expCost S t := by
      have hK : 1 / (8 * R) ≤ h ^ 2 / (2 * R) := by
        have hh4 : 1 / 4 ≤ h ^ 2 := by nlinarith
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right hh4 (by positivity : (0 : ℝ) ≤ 8 * R)]
      have hc : 1 / (8 * R) ≤ |deriv (deriv H) t| := hK.trans hbend
      have h34 : 3 / 8 ≤ (1 - t ^ 2) / 2 := by linarith
      calc 3 / (64 * R) = 3 / 8 * (1 / (8 * R)) := by field_simp; ring
        _ ≤ (1 - t ^ 2) / 2 * |deriv (deriv H) t| :=
            mul_le_mul h34 hc (by positivity) (by linarith)
        _ ≤ expCost S t := h3
    have hRD : R * Real.sqrt D ≤ 3 := by
      have hsq : (R * Real.sqrt D) ^ 2 ≤ 3 ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        have : R ^ 2 * D ≤ 6 / (D + 6) * D := mul_le_mul_of_nonneg_right hR2 (by positivity)
        have h6 : 6 / ((D : ℝ) + 6) * D ≤ 6 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
        nlinarith
      exact le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) hsq
    have hfinal : Real.sqrt D / 100 ≤ 3 / (64 * R) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    unfold expCost at hcurv
    linarith

/-! ## The transition window -/

/-- Parameter arithmetic for the transition window: if `s = 1 + δ` with `2η ≤ δ ≤ 1` and the
dyadic gain satisfies `s - η < a ≤ s`, then `a - 1 ≥ δ/2`, `(a² - 1)/(4a² - 1) ≥ δ/15` and
`log a ≥ δ/3`.

Paper: `eq:dyadicgain` and the window estimates (tanh_lower.tex). -/
lemma window_parameters {δ η a : ℝ} (hη : 0 < η) (hδη : 2 * η ≤ δ) (hδ1 : δ ≤ 1)
    (ha1 : 1 + δ - η < a) (ha2 : a ≤ 1 + δ) :
    δ / 2 ≤ a - 1 ∧ δ / 15 ≤ (a ^ 2 - 1) / (4 * a ^ 2 - 1) ∧ δ / 3 ≤ Real.log a := by
  have hδ0 : 0 < δ := by linarith
  have hda : δ / 2 ≤ a - 1 := by linarith
  refine ⟨hda, ?_, ?_⟩
  · have h1 : δ ≤ a ^ 2 - 1 := by nlinarith
    have h2 : 4 * a ^ 2 - 1 ≤ 15 := by nlinarith
    rw [le_div_iff₀ (by nlinarith)]
    nlinarith
  · have hapos : 0 < a := by linarith
    have hlog := Real.one_sub_inv_le_log_of_pos hapos
    have : δ / 3 ≤ 1 - a⁻¹ := by
      rw [inv_eq_one_div, le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hapos]
      nlinarith
    linarith

/-- The dyadic gain `a = η ⌊s/η⌋` lies in `(s - η, s]`.

Paper: `eq:dyadicgain` (tanh_lower.tex). -/
lemma dyadic_gain_bounds {s η : ℝ} (hη : 0 < η) :
    s - η < η * ⌊s / η⌋ ∧ η * ⌊s / η⌋ ≤ s := by
  have h1 := Int.floor_le (s / η)
  have h2 := Int.lt_floor_add_one (s / η)
  constructor
  · have := mul_lt_mul_of_pos_left h2 hη
    rw [mul_div_cancel₀ s hη.ne', mul_add, mul_one] at this
    linarith
  · have := mul_le_mul_of_nonneg_left h1 hη.le
    rwa [mul_div_cancel₀ s hη.ne'] at this

/-- The window lower bound `(δ/30) e^{δL/2}`: with `D = L`, `m ≥ 2^{L-1}` and the dyadic gain
of the previous lemma, every exact sampler has a context with
`E[Q | x] ≥ (δ/30) e^{δ L/2}`. The paper's "for all sufficiently large `L`" is replaced by the
explicit hypotheses `2η ≤ δ` and `1 + δ - η < a ≤ 1 + δ`; the grid property of `a` and the
inequality `2η ≤ δ` for large `L` are not derived here.

Paper: `eq:windowexplicit` (tanh_lower.tex), lower side of `cor:window` (tanh_model.tex). -/
theorem window_explicit {ι : Type*} [Fintype ι] (S : Sampler m ι) (hN : S.NoRepeat)
    (hB : S.Bounded) {δ η a : ℝ} {L : ℕ} (hL : 1 ≤ L) (hη : 0 < η) (hδη : 2 * η ≤ δ)
    (hδ1 : δ ≤ 1) (ha1 : 1 + δ - η < a) (ha2 : a ≤ 1 + δ) (hm : (2 : ℝ) ^ (L - 1) ≤ m)
    (hf : S.Exact (chainTarget a L)) :
    ∃ x, δ / 30 * Real.exp (δ * L / 2) ≤ S.cost x := by
  obtain ⟨hda, hcoef, hlog⟩ := window_parameters hη hδη hδ1 ha1 ha2
  have hδ0 : 0 < δ := by linarith
  have ha : 1 < a := by linarith
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ 2 ^ (L - 1) := one_le_pow₀ (by norm_num)
    exact_mod_cast this.trans hm
  obtain ⟨x, hx⟩ := lower_super S hN hB ha hm1 L hf
  refine ⟨x, le_trans ?_ hx⟩
  have hE : 0 < Real.exp (δ * L / 2) := Real.exp_pos _
  -- both branches of the minimum are at least `e^{δL/2}/2`
  have hpow : Real.exp (δ * L / 2) / 2 ≤ a ^ (2 * L) := by
    have : a ^ (2 * L) = Real.exp (2 * L * Real.log a) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith)]
      push_cast; ring_nf
    rw [this]
    have h2 : δ * L / 2 ≤ 2 * L * Real.log a := by
      have hL' : (0 : ℝ) ≤ L := by positivity
      nlinarith
    have := Real.exp_le_exp.mpr h2
    linarith
  have hmm : Real.exp (δ * L / 2) / 2 ≤ m := by
    have h2 : Real.exp (δ * L / 2) ≤ 2 ^ L := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
      apply Real.exp_le_exp.mpr
      have := Real.log_two_gt_d9
      have hL' : (0 : ℝ) ≤ L := by positivity
      nlinarith
    have h3 : (2 : ℝ) ^ L = 2 * 2 ^ (L - 1) := by
      rw [← pow_succ']; congr 1; omega
    linarith
  have hmin : Real.exp (δ * L / 2) / 2 ≤ min (a ^ (2 * L)) m := le_min hpow hmm
  calc δ / 30 * Real.exp (δ * L / 2) = δ / 15 * (Real.exp (δ * L / 2) / 2) := by ring
    _ ≤ (a ^ 2 - 1) / (4 * a ^ 2 - 1) * min (a ^ (2 * L)) m :=
        mul_le_mul hcoef hmin (by positivity) (le_trans (by positivity) hcoef)

/-- Converting the window bound into `e^{δL/4}`: if `w = δL ≥ 4 log(30L)` then
`(δ/30) e^{w/2} ≥ e^{w/4}`.

Paper: last paragraph of the window estimates (tanh_lower.tex), `cor:window`
(tanh_model.tex). -/
lemma window_exponent {δ : ℝ} {L : ℕ} (hL : 1 ≤ L) (hδ : 0 < δ)
    (hw : 4 * Real.log (30 * L) ≤ δ * L) :
    Real.exp (δ * L / 4) ≤ δ / 30 * Real.exp (δ * L / 2) := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h30 : 0 < (30 : ℝ) * L := by positivity
  have hlog30 : 1 ≤ Real.log (30 * L) := by
    rw [Real.le_log_iff_exp_le h30]
    have := Real.exp_one_lt_d9
    nlinarith
  have hw1 : 1 ≤ δ * L := by linarith
  -- `log(δ/30) = log w - log (30 L) ≥ -log(30L)`
  have hpos : 0 < δ / 30 := by positivity
  have hkey : Real.log (30 * L) ≤ δ * L / 4 := by linarith
  have hlogd : -(δ * L / 4) ≤ Real.log (δ / 30) := by
    have e : δ / 30 = (δ * L) / (30 * L) := by field_simp
    rw [e, Real.log_div (by positivity) h30.ne']
    have : 0 ≤ Real.log (δ * L) := Real.log_nonneg hw1
    linarith
  have h1 : Real.exp (-(δ * L / 4)) ≤ δ / 30 := by
    calc Real.exp (-(δ * L / 4)) ≤ Real.exp (Real.log (δ / 30)) := Real.exp_le_exp.mpr hlogd
      _ = δ / 30 := Real.exp_log hpos
  have e2 : Real.exp (δ * L / 4) = Real.exp (-(δ * L / 4)) * Real.exp (δ * L / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [e2]
  exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le

/-- **The transition window, quantitative lower side.** Under the hypotheses of
`window_explicit` and `δL ≥ 4 log(30L)`, some context requires at least `e^{δL/4}` expected
input probes. As in `window_explicit`, the paper's "for all sufficiently large `L`" is replaced
by the explicit hypotheses `2η ≤ δ` and `1 + δ - η < a ≤ 1 + δ`, which are not derived.

Paper: `cor:window` (tanh_model.tex; proof in tanh_lower.tex). -/
theorem window_lower {ι : Type*} [Fintype ι] (S : Sampler m ι) (hN : S.NoRepeat)
    (hB : S.Bounded) {δ η a : ℝ} {L : ℕ} (hL : 1 ≤ L) (hη : 0 < η) (hδη : 2 * η ≤ δ)
    (hδ1 : δ ≤ 1) (ha1 : 1 + δ - η < a) (ha2 : a ≤ 1 + δ) (hm : (2 : ℝ) ^ (L - 1) ≤ m)
    (hw : 4 * Real.log (30 * L) ≤ δ * L) (hf : S.Exact (chainTarget a L)) :
    ∃ x, Real.exp (δ * L / 4) ≤ S.cost x := by
  obtain ⟨x, hx⟩ := window_explicit S hN hB hL hη hδη hδ1 ha1 ha2 hm hf
  exact ⟨x, (window_exponent hL (by linarith) hw).trans hx⟩

/-- Dyadic input size: with `m = 2^{⌊log₂ n⌋}` and `L = ⌈log₂ n⌉`, `m ≤ n < 2m` and
`2^{L-1} ≤ m`. Paper: the choice of `m` before `thm:lower` (tanh_model.tex) and
`m ≥ 2^{L-1}` in the window estimates (tanh_lower.tex). -/
lemma dyadic_size (n : ℕ) (hn : 1 ≤ n) :
    2 ^ Nat.log 2 n ≤ n ∧ n < 2 * 2 ^ Nat.log 2 n ∧ 2 ^ (Nat.clog 2 n - 1) ≤ 2 ^ Nat.log 2 n := by
  have h1 := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  have h2 := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) n
  rw [pow_succ] at h2
  have h3 : Nat.clog 2 n ≤ Nat.log 2 n + 1 :=
    Nat.clog_le_of_le_pow (by rw [pow_succ]; omega)
  refine ⟨h1, by omega, Nat.pow_le_pow_right (by norm_num) (by omega)⟩

/-- **The critical lower bound at width `n`.** For `1 ≤ D` and `2D ≤ n`, every exact sampler
for the critical mean chain on `m = 2^{⌊log₂ n⌋}` inputs has a context with
`E[Q | x] ≥ √D/100`.

Paper: the `Ω(√D)` lower bound for `D ≤ n/2` in `thm:main-depth`
(exact_sampling_networks.tex), from `eq:lowercritical` (tanh_model.tex). -/
theorem lower_critical_width {n D : ℕ} {ι : Type*} [Fintype ι]
    (S : Sampler (2 ^ Nat.log 2 n) ι) (hN : S.NoRepeat) (hB : S.Bounded) (hD : 1 ≤ D)
    (h2D : 2 * D ≤ n) (hf : S.Exact (chainTarget 1 D)) :
    ∃ x, Real.sqrt D / 100 ≤ S.cost x := by
  obtain ⟨-, h2, -⟩ := dyadic_size n (by omega)
  exact lower_critical S hN hB hD (by omega) hf

/-! ## Unread coordinates: a pairing of inputs -/

namespace DTree

/-- `x` is read completely by `T`. -/
def FullRead (T : DTree m) (x : Fin m → Bool) : Prop := T.path x = Finset.univ

instance (T : DTree m) (x : Fin m → Bool) : Decidable (T.FullRead x) := by
  unfold FullRead; infer_instance

/-- Flip the least coordinate that `T` leaves unread on `x` (identity on fully read inputs). -/
def pairMap (T : DTree m) (x : Fin m → Bool) : Fin m → Bool :=
  if h : (Finset.univ \ T.path x).Nonempty then flipAt ((Finset.univ \ T.path x).min' h) x
  else x

/-- An input is not read completely iff some coordinate is unread. Auxiliary for the pairing
arguments of `prop:evaluation` (tanh_lower.tex) and `prop:instance-hardness-eight`
(instance_hardness.tex). -/
lemma not_fullRead_iff (T : DTree m) (x : Fin m → Bool) :
    ¬T.FullRead x ↔ (Finset.univ \ T.path x).Nonempty := by
  unfold FullRead
  rw [Finset.sdiff_nonempty]
  constructor
  · intro h hsub; exact h (Finset.Subset.antisymm (Finset.subset_univ _) hsub)
  · intro h heq; exact h (heq ▸ Finset.Subset.refl _)

/-- The paired input flips an unread coordinate. Auxiliary for the pairing arguments of
`prop:evaluation` and `prop:instance-hardness-eight`. -/
lemma pairMap_spec {T : DTree m} {x : Fin m → Bool} (h : (Finset.univ \ T.path x).Nonempty) :
    T.pairMap x = flipAt ((Finset.univ \ T.path x).min' h) x ∧
      ((Finset.univ \ T.path x).min' h) ∉ T.path x := by
  refine ⟨by simp [pairMap, h], ?_⟩
  have := Finset.min'_mem _ h
  rw [Finset.mem_sdiff] at this
  exact this.2

/-- Paired inputs share their transcript and leaf. Auxiliary for the pairing arguments of
`prop:evaluation` and `prop:instance-hardness-eight`. -/
lemma out_path_pairMap (T : DTree m) (x : Fin m → Bool) :
    T.out (T.pairMap x) = T.out x ∧ T.path (T.pairMap x) = T.path x := by
  by_cases h : (Finset.univ \ T.path x).Nonempty
  · obtain ⟨he, hi⟩ := pairMap_spec h
    rw [he]
    exact out_path_update_of_not_mem_path hi _
  · simp [pairMap, h]

/-- The pairing is an involution. Auxiliary for the pairing arguments of `prop:evaluation` and
`prop:instance-hardness-eight`. -/
lemma pairMap_pairMap (T : DTree m) (x : Fin m → Bool) : T.pairMap (T.pairMap x) = x := by
  by_cases h : (Finset.univ \ T.path x).Nonempty
  · have hp := (out_path_pairMap T x).2
    have h' : (Finset.univ \ T.path (T.pairMap x)).Nonempty := by rwa [hp]
    obtain ⟨he, -⟩ := pairMap_spec h
    obtain ⟨he', -⟩ := pairMap_spec h'
    rw [he']
    have hmin : (Finset.univ \ T.path (T.pairMap x)).min' h' =
        (Finset.univ \ T.path x).min' h := by
      congr 1
      rw [hp]
    rw [hmin, he, flipAt_flipAt]
  · simp [pairMap, h]

/-- The pairing preserves complete reads. Auxiliary for the pairing arguments of
`prop:evaluation` and `prop:instance-hardness-eight`. -/
lemma fullRead_pairMap (T : DTree m) (x : Fin m → Bool) :
    T.FullRead (T.pairMap x) ↔ T.FullRead x := by
  unfold FullRead; rw [(out_path_pairMap T x).2]

/-- The pairing as a permutation of inputs. -/
def pairPerm (T : DTree m) : Equiv.Perm (Fin m → Bool) :=
  Function.Involutive.toPerm T.pairMap T.pairMap_pairMap

/-- Pairing identity: over the inputs that are not read completely, every sum equals the sum of
its paired values. Paper: proofs of `prop:evaluation` (tanh_lower.tex) and
`prop:instance-hardness-eight` (instance_hardness.tex). -/
lemma sum_unread_pair (T : DTree m) (g : (Fin m → Bool) → ℝ) :
    ∑ x, (if T.FullRead x then 0 else g x) =
      ∑ x, (if T.FullRead x then 0 else g (T.pairMap x)) := by
  rw [← Equiv.sum_comp T.pairPerm]
  refine Finset.sum_congr rfl fun x _ => ?_
  change (if T.FullRead (T.pairMap x) then 0 else g (T.pairMap x)) = _
  by_cases h : T.FullRead x
  · have h' : T.FullRead (T.pairMap x) := (fullRead_pairMap T x).mpr h
    simp [h, h']
  · have h' : ¬T.FullRead (T.pairMap x) := fun hh => h ((fullRead_pairMap T x).mp hh)
    simp [h, h']

/-- A flip changes the input. Auxiliary for the pairing arguments of `prop:evaluation` and
`prop:instance-hardness-eight`. -/
lemma flipAt_ne_self (i : Fin m) (x : Fin m → Bool) : flipAt i x ≠ x := by
  intro h
  have := congrFun h i
  rw [flipAt_self] at this
  cases hx : x i <;> simp_all

/-- An input that is not read completely is paired with a different input. Auxiliary for the
pairing arguments of `prop:evaluation` and `prop:instance-hardness-eight`. -/
lemma pairMap_ne_self {T : DTree m} {x : Fin m → Bool} (h : ¬T.FullRead x) :
    T.pairMap x ≠ x := by
  rw [not_fullRead_iff] at h
  rw [(pairMap_spec h).1]
  exact flipAt_ne_self _ _

/-- A complete read probes all `m` coordinates. Auxiliary for `E Q ≥ m P(Q = m)` in the proofs
of `prop:evaluation` and `prop:instance-hardness-eight`. -/
lemma card_path_of_fullRead {T : DTree m} {x : Fin m → Bool} (h : T.FullRead x) :
    ((T.path x).card : ℝ) = m := by
  unfold FullRead at h; rw [h]; simp

end DTree

/-- The input differs from its pairing in exactly one coordinate that is unread on its path.
Paper: proofs of `prop:evaluation` (tanh_lower.tex) and `prop:instance-hardness-eight`
(instance_hardness.tex). -/
lemma DTree.pairMap_eq_update {T : DTree m} {x : Fin m → Bool} (h : ¬T.FullRead x) :
    ∃ i, i ∉ T.path x ∧ T.pairMap x = flipAt i x := by
  rw [DTree.not_fullRead_iff] at h
  obtain ⟨he, hi⟩ := DTree.pairMap_spec h
  exact ⟨_, hi, he⟩

/-! ## Numerical evaluation needs the inputs -/

/-- Changing one sign moves the sign sum by two. Paper: "a single input flip changes the mean by
`2/m`", proof of `prop:evaluation` (tanh_lower.tex). -/
lemma signSum_flipAt (i : Fin m) (x : Fin m → Bool) :
    signSum (flipAt i x) = signSum x - 2 * sgn (x i) := by
  unfold signSum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ (fun j => sgn (x j)) (Finset.mem_univ i)]
  have : ∑ j ∈ Finset.univ.erase i, sgn (flipAt i x j) =
      ∑ j ∈ Finset.univ.erase i, sgn (x j) :=
    Finset.sum_congr rfl fun j hj => by rw [flipAt_ne (Finset.ne_of_mem_erase hj)]
  rw [this, flipAt_self, sgn_not]
  ring

/-- Critical chain values stay in `[-1,1]`. Auxiliary for the proof of `prop:evaluation`
(tanh_lower.tex). -/
lemma abs_F_one_le (d : ℕ) {z : ℝ} (hz : |z| ≤ 1) : |F 1 d z| ≤ 1 := by
  cases d with
  | zero => exact hz
  | succ d => exact (Real.abs_tanh_lt_one _).le

/-- On `[-1,1]` the critical chain has slope at least `4^{-L}`:
`F_{1,L}(z') - F_{1,L}(z) ≥ (z' - z)/4^L`.

Paper: derivative bound in the proof of `prop:evaluation` (tanh_lower.tex). -/
lemma F_one_sub_ge (L : ℕ) {z z' : ℝ} (hz : -1 ≤ z) (hzz : z ≤ z') (hz' : z' ≤ 1) :
    (z' - z) / 4 ^ L ≤ F 1 L z' - F 1 L z := by
  induction L with
  | zero => simp [F]
  | succ L ih =>
    have hb : ∀ w, |w| ≤ 1 → -1 ≤ F 1 L w ∧ F 1 L w ≤ 1 := fun w hw =>
      abs_le.mp (abs_F_one_le L hw)
    have h1 := hb z (abs_le.mpr ⟨hz, hzz.trans hz'⟩)
    have h2 := hb z' (abs_le.mpr ⟨hz.trans hzz, hz'⟩)
    have hmono : F 1 L z ≤ F 1 L z' := F_mono zero_le_one L hzz
    have ht := tanh_sub_ge h1.1 hmono h2.2
    simp only [F, one_mul]
    rw [pow_succ]
    calc (z' - z) / (4 ^ L * 4) = ((z' - z) / 4 ^ L) / 4 := by ring
      _ ≤ (F 1 L z' - F 1 L z) / 4 := by gcongr
      _ ≤ _ := ht

/-- Two-sided form of the slope bound `F'_{1,L} ≥ 4^{-L}` on `[-1,1]`. Paper: proof of
`prop:evaluation` (tanh_lower.tex). -/
lemma F_one_abs_sub_ge (L : ℕ) {z z' : ℝ} (hz : |z| ≤ 1) (hz' : |z'| ≤ 1) :
    |z - z'| / 4 ^ L ≤ |F 1 L z - F 1 L z'| := by
  have h1 := abs_le.mp hz
  have h2 := abs_le.mp hz'
  rcases le_total z z' with h | h
  · have := F_one_sub_ge L h1.1 h h2.2
    have hm : F 1 L z ≤ F 1 L z' := F_mono zero_le_one L h
    rw [abs_sub_comm z, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    exact this
  · have := F_one_sub_ge L h2.1 h h1.2
    have hm : F 1 L z' ≤ F 1 L z := F_mono zero_le_one L h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact this

/-- Neighbouring contexts have well separated critical activations:
`|F_{1,L}(T(x)/m) - F_{1,L}(T(x')/m)| > 2 · 2^{-20L}` whenever `x'` changes one sign of `x`,
`L ≥ 1` and `m ≤ 2^L`.

Paper: proof of `prop:evaluation` (tanh_lower.tex). -/
lemma critical_separation {L : ℕ} (hL : 1 ≤ L) (hm : 1 ≤ m) (hmL : (m : ℝ) ≤ 2 ^ L)
    (x : Fin m → Bool) (i : Fin m) :
    2 * (2 : ℝ)⁻¹ ^ (20 * L) <
      |chainTarget 1 L x - chainTarget 1 L (flipAt i x)| := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold chainTarget
  rw [signSum_flipAt]
  have hlo := neg_le_signSum x
  have hhi := signSum_le x
  have hlo' := neg_le_signSum (flipAt i x)
  have hhi' := signSum_le (flipAt i x)
  rw [signSum_flipAt] at hlo' hhi'
  have hz : |signSum x / m| ≤ 1 := by
    rw [abs_le, le_div_iff₀ hm', div_le_one hm']; constructor <;> linarith
  have hz' : |(signSum x - 2 * sgn (x i)) / m| ≤ 1 := by
    rw [abs_le, le_div_iff₀ hm', div_le_one hm']; constructor <;> linarith
  have key := F_one_abs_sub_ge L hz hz'
  have hdiff : |signSum x / m - (signSum x - 2 * sgn (x i)) / m| = 2 / m := by
    rw [show signSum x / m - (signSum x - 2 * sgn (x i)) / m = 2 * sgn (x i) / m by ring,
      abs_div, abs_mul, abs_sgn, abs_of_pos hm']
    norm_num
  rw [hdiff] at key
  refine lt_of_lt_of_le ?_ key
  -- `m 4^L ≤ 2^{3L} < 2^{20 L}`
  have h4 : (4 : ℝ) ^ L = 2 ^ L * 2 ^ L := by rw [← mul_pow]; norm_num
  have hlt : (m : ℝ) * 4 ^ L < 2 ^ (20 * L) := by
    calc (m : ℝ) * 4 ^ L ≤ 2 ^ L * 4 ^ L := mul_le_mul_of_nonneg_right hmL (by positivity)
      _ = 2 ^ (3 * L) := by rw [h4, ← pow_add, ← pow_add]; ring_nf
      _ < 2 ^ (20 * L) := pow_lt_pow_right₀ (by norm_num) (by omega)
  rw [inv_pow, ← one_div, mul_one_div, div_div]
  exact div_lt_div_of_pos_left two_pos (by positivity) hlt

/-- An always-correct evaluator (deterministic decision tree) for a target whose neighbouring
values are more than `2ε` apart reads every coordinate on every input. Paper: proof of
`prop:evaluation` (tanh_lower.tex). -/
theorem always_correct_reads_all {g : (Fin m → Bool) → ℝ} {ε : ℝ}
    (hsep : ∀ x i, 2 * ε < |g x - g (flipAt i x)|) {E : DTree m}
    (hE : ∀ x, |E.out x - g x| ≤ ε) (x : Fin m → Bool) : E.path x = Finset.univ := by
  by_contra hfull
  obtain ⟨i, hi, -⟩ := DTree.pairMap_eq_update (T := E) (x := x) hfull
  have hout := (DTree.out_path_update_of_not_mem_path hi (!x i)).1
  have h1 := hE x
  have h2 := hE (flipAt i x)
  unfold flipAt at h2
  rw [hout] at h2
  have := hsep x i
  unfold flipAt at this
  have h3 : |g x - g (Function.update x i (!x i))| ≤ 2 * ε := by
    calc |g x - g (Function.update x i (!x i))| =
          |(g x - E.out x) + (E.out x - g (Function.update x i (!x i)))| := by ring_nf
      _ ≤ |g x - E.out x| + |E.out x - g (Function.update x i (!x i))| := abs_add_le _ _
      _ ≤ ε + ε := by
          rw [abs_sub_comm] at h1
          exact add_le_add h1 h2
      _ = 2 * ε := by ring
  linarith

/-- **Separation from numerical evaluation, always-correct part.** Every randomized evaluator
that returns `F_{1,L}(m⁻¹ ∑ⱼ xⱼ)` with absolute error at most `2^{-20L}` on every tape class of
positive probability probes all `m` coordinates on every input (`L ≥ 1`, `m ≤ 2^L`). Here the
leaves of the trees are the returned numbers (not conditional means of a sign); tapes are
grouped by tree.

Paper: `prop:evaluation` (tanh_model.tex; proof in tanh_lower.tex). -/
theorem evaluation_always_correct {ι : Type*} [Fintype ι] (S : Sampler m ι) {L : ℕ}
    (hL : 1 ≤ L) (hm : 1 ≤ m) (hmL : (m : ℝ) ≤ 2 ^ L)
    (hcorrect : ∀ ω, S.p ω ≠ 0 → ∀ x,
      |(S.tree ω).out x - chainTarget 1 L x| ≤ (2 : ℝ)⁻¹ ^ (20 * L))
    (x : Fin m → Bool) : S.cost x = m := by
  unfold Sampler.cost
  have : ∀ ω, S.p ω * ((S.tree ω).path x).card = S.p ω * m := by
    intro ω
    by_cases hp : S.p ω = 0
    · simp [hp]
    · rw [always_correct_reads_all (fun x i => critical_separation hL hm hmL x i)
        (hcorrect ω hp) x]
      simp
  rw [Finset.sum_congr rfl fun ω _ => this ω, ← Finset.sum_mul, S.p_sum, one_mul]

/-- Pairing bound for a single tree: among inputs that are not read completely, at most half
can be answered correctly, because paired inputs share the leaf but need far apart answers.
Paper: proof of `prop:evaluation` (tanh_lower.tex), "success is at most
`P(Q = m) + P(Q < m)/2`". -/
lemma tree_success_le {g : (Fin m → Bool) → ℝ} {ε : ℝ}
    (hsep : ∀ x i, 2 * ε < |g x - g (flipAt i x)|) (E : DTree m) :
    ∑ x, (if |E.out x - g x| ≤ ε then (1 : ℝ) else 0) ≤
      ∑ x, (if E.FullRead x then (1 : ℝ) else 0) +
        (∑ x, (if E.FullRead x then (0 : ℝ) else 1)) / 2 := by
  set c : (Fin m → Bool) → ℝ := fun x => if |E.out x - g x| ≤ ε then 1 else 0 with hc
  have hsplit : ∀ x, c x = (if E.FullRead x then c x else 0) + (if E.FullRead x then 0 else c x) :=
    fun x => by split <;> simp
  have hc1 : ∀ y, c y ≤ 1 := fun y => by simp only [hc]; split <;> norm_num
  have hpair : ∀ x, ¬E.FullRead x → c x + c (E.pairMap x) ≤ 1 := by
    intro x hx
    obtain ⟨i, hi, he⟩ := DTree.pairMap_eq_update hx
    have hout := (DTree.out_path_update_of_not_mem_path hi (!x i)).1
    rw [he]
    by_cases h1 : |E.out x - g x| ≤ ε
    · by_cases h2 : |E.out (flipAt i x) - g (flipAt i x)| ≤ ε
      · exfalso
        have := hsep x i
        unfold flipAt at h2 this
        rw [hout] at h2
        have h3 : |g x - g (Function.update x i (!x i))| ≤ 2 * ε := by
          calc |g x - g (Function.update x i (!x i))| =
                |(g x - E.out x) + (E.out x - g (Function.update x i (!x i)))| := by ring_nf
            _ ≤ |g x - E.out x| + |E.out x - g (Function.update x i (!x i))| := abs_add_le _ _
            _ ≤ ε + ε := add_le_add (by rw [abs_sub_comm]; exact h1) h2
            _ = 2 * ε := by ring
        linarith
      · have h0 : c (flipAt i x) = 0 := by simp [hc, h2]
        linarith [hc1 x]
    · have h0 : c x = 0 := by simp [hc, h1]
      linarith [hc1 (flipAt i x)]
  have hsum := DTree.sum_unread_pair E c
  have hhalf : ∑ x, (if E.FullRead x then 0 else c x) ≤
      (∑ x, (if E.FullRead x then (0 : ℝ) else 1)) / 2 := by
    have h2 : 2 * ∑ x, (if E.FullRead x then 0 else c x) =
        ∑ x, (if E.FullRead x then 0 else c x + c (E.pairMap x)) := by
      rw [two_mul]
      nth_rewrite 2 [hsum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      split <;> simp
    have h3 : ∑ x, (if E.FullRead x then 0 else c x + c (E.pairMap x)) ≤
        ∑ x, (if E.FullRead x then (0 : ℝ) else 1) :=
      Finset.sum_le_sum fun x _ => by
        split
        · exact le_refl 0
        · next h => exact hpair x h
    linarith
  have hfull : ∑ x, (if E.FullRead x then c x else 0) ≤
      ∑ x, (if E.FullRead x then (1 : ℝ) else 0) :=
    Finset.sum_le_sum fun x _ => by
      split
      · simp only [hc]; split <;> norm_num
      · exact le_refl 0
  rw [Finset.sum_congr rfl fun x _ => hsplit x, Finset.sum_add_distrib]
  linarith

/-- Bounded-error evaluation needs many probes: if every context is answered within `ε` with
probability at least `2/3`, and neighbouring targets are more than `2ε` apart, then the
expected number of distinct probes under uniform inputs is at least `m/3`. Paper: proof of
`prop:evaluation` (tanh_lower.tex). -/
theorem bounded_error_cost {ι : Type*} [Fintype ι] (S : Sampler m ι)
    {g : (Fin m → Bool) → ℝ} {ε : ℝ} (hsep : ∀ x i, 2 * ε < |g x - g (flipAt i x)|)
    (hsucc : ∀ x, 2 / 3 ≤ ∑ ω, S.p ω *
      (if |(S.tree ω).out x - g x| ≤ ε then (1 : ℝ) else 0)) :
    (m : ℝ) / 3 ≤ prodExp (fun _ => 0) S.cost := by
  set u : ℝ := (1 / 2) ^ m
  have hu : u * 2 ^ m = 1 := by simp only [u]; rw [← mul_pow]; norm_num
  have hcard : ∑ _x : Fin m → Bool, (1 : ℝ) = 2 ^ m := by simp
  -- probability of a full read
  set P : ℝ := ∑ ω, S.p ω * (u * ∑ x, (if (S.tree ω).FullRead x then (1 : ℝ) else 0))
  have hcompl : ∀ ω, ∑ x, (if (S.tree ω).FullRead x then (0 : ℝ) else 1) =
      2 ^ m - ∑ x, (if (S.tree ω).FullRead x then (1 : ℝ) else 0) := by
    intro ω
    rw [← hcard, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split <;> norm_num
  have hP : 1 / 3 ≤ P := by
    have h1 : 2 / 3 ≤ u * ∑ x, ∑ ω, S.p ω *
        (if |(S.tree ω).out x - g x| ≤ ε then (1 : ℝ) else 0) := by
      have := Finset.sum_le_sum (s := Finset.univ) fun x _ => hsucc x
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul] at this
      push_cast at this
      calc (2 : ℝ) / 3 = u * (2 ^ m * (2 / 3)) := by rw [← mul_assoc, hu, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
    rw [Finset.sum_comm] at h1
    have h2 : u * ∑ ω, ∑ x, S.p ω *
        (if |(S.tree ω).out x - g x| ≤ ε then (1 : ℝ) else 0) ≤
        ∑ ω, S.p ω * (u * (∑ x, (if (S.tree ω).FullRead x then (1 : ℝ) else 0) +
          (2 ^ m - ∑ x, (if (S.tree ω).FullRead x then (1 : ℝ) else 0)) / 2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun ω _ => ?_
      rw [← Finset.mul_sum, ← hcompl]
      have := tree_success_le hsep (S.tree ω)
      have hp := S.p_nonneg ω
      have hu0 : 0 ≤ u := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hu0 hp)]
    have h3 : ∑ ω, S.p ω * (u * (∑ x, (if (S.tree ω).FullRead x then (1 : ℝ) else 0) +
          (2 ^ m - ∑ x, (if (S.tree ω).FullRead x then (1 : ℝ) else 0)) / 2)) =
        P / 2 + 1 / 2 := by
      have e : ∀ ω, S.p ω * (u * (∑ x, (if (S.tree ω).FullRead x then (1 : ℝ) else 0) +
          (2 ^ m - ∑ x, (if (S.tree ω).FullRead x then (1 : ℝ) else 0)) / 2)) =
          S.p ω * (u * ∑ x, (if (S.tree ω).FullRead x then (1 : ℝ) else 0)) / 2 +
            S.p ω * (1 / 2) := fun ω => by
        linear_combination (S.p ω / 2) * hu
      rw [Finset.sum_congr rfl fun ω _ => e ω, Finset.sum_add_distrib, ← Finset.sum_div,
        ← Finset.sum_mul, S.p_sum]
      ring
    linarith
  -- `E[Q] ≥ m · P(full read)`
  have hcost : (m : ℝ) * P ≤ prodExp (fun _ => 0) S.cost := by
    rw [prodExp_zero]
    unfold Sampler.cost
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun ω _ => ?_
    rw [← Finset.mul_sum]
    have : (m : ℝ) * (u * ∑ x, (if (S.tree ω).FullRead x then (1 : ℝ) else 0)) ≤
        u * ∑ x, (((S.tree ω).path x).card : ℝ) := by
      rw [← mul_assoc, mul_comm (m : ℝ), mul_assoc, Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_) (by positivity)
      split
      · next h => rw [mul_one, DTree.card_path_of_fullRead h]
      · simp
    have hp := S.p_nonneg ω
    calc (m : ℝ) * (S.p ω * (u * ∑ x, (if (S.tree ω).FullRead x then (1 : ℝ) else 0))) =
          S.p ω * ((m : ℝ) * (u * ∑ x, (if (S.tree ω).FullRead x then (1 : ℝ) else 0))) := by
            ring
      _ ≤ S.p ω * (u * ∑ x, (((S.tree ω).path x).card : ℝ)) :=
          mul_le_mul_of_nonneg_left this hp
      _ = u * (S.p ω * ∑ x, (((S.tree ω).path x).card : ℝ)) := by ring
  have hm0 : (0 : ℝ) ≤ m := by positivity
  nlinarith

/-- **Separation from numerical evaluation, bounded-error part.** If a randomized evaluator
returns `F_{1,L}(m⁻¹ ∑ⱼ xⱼ)` within `2^{-20L}` with probability at least `2/3` on every
context, then under uniform inputs it makes at least `m/3` distinct probes in expectation. The
leaves of the trees are the returned numbers; a general randomized evaluator reduces to this
form by grouping tapes by tree together with the set of contexts answered correctly.

Paper: `prop:evaluation` (tanh_model.tex; proof in tanh_lower.tex). -/
theorem evaluation_bounded_error {ι : Type*} [Fintype ι] (S : Sampler m ι) {L : ℕ}
    (hL : 1 ≤ L) (hm : 1 ≤ m) (hmL : (m : ℝ) ≤ 2 ^ L)
    (hsucc : ∀ x, 2 / 3 ≤ ∑ ω, S.p ω *
      (if |(S.tree ω).out x - chainTarget 1 L x| ≤ (2 : ℝ)⁻¹ ^ (20 * L) then (1 : ℝ) else 0)) :
    (m : ℝ) / 3 ≤ prodExp (fun _ => 0) S.cost :=
  bounded_error_cost S (fun x i => critical_separation hL hm hmL x i) hsucc

/-! ## Parity transcripts -/

/-- The parity `χ(y) = ∏ᵢ yᵢ`. -/
def parity (y : Fin m → Bool) : ℝ := ∏ i, sgn (y i)

/-- Flipping one bit negates the parity. Auxiliary for the parity transcript argument in the
proof of `prop:instance-hardness-eight` (instance_hardness.tex). -/
lemma parity_flipAt (i : Fin m) (y : Fin m → Bool) : parity (flipAt i y) = -parity y := by
  unfold parity
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ (fun j => sgn (y j)) (Finset.mem_univ i)]
  have : ∏ j ∈ Finset.univ.erase i, sgn (flipAt i y j) =
      ∏ j ∈ Finset.univ.erase i, sgn (y j) :=
    Finset.prod_congr rfl fun j hj => by rw [flipAt_ne (Finset.ne_of_mem_erase hj)]
  rw [this, flipAt_self, sgn_not]
  ring

/-- Parity values are `±1`. Auxiliary for the parity transcript argument in the proof of
`prop:instance-hardness-eight` (instance_hardness.tex). -/
lemma abs_parity (y : Fin m → Bool) : |parity y| = 1 := by
  unfold parity
  rw [Finset.abs_prod]
  exact Finset.prod_eq_one fun i _ => abs_sgn _

/-- A transcript that leaves a parity bit unread has no correlation with the parity:
`∑_y out(y) χ(y) ≤ #{y : all bits read}`. Paper: proof of `prop:instance-hardness-eight`
(instance_hardness.tex), "conditional on any transcript that leaves at least one of them
unqueried, their parity is uniform". -/
lemma tree_parity_corr_le {T : DTree m} (hT : T.Bounded) :
    ∑ y, T.out y * parity y ≤ ∑ y, (if T.FullRead y then (1 : ℝ) else 0) := by
  set h : (Fin m → Bool) → ℝ := fun y => T.out y * parity y
  have hsplit : ∀ y, h y = (if T.FullRead y then h y else 0) + (if T.FullRead y then 0 else h y) :=
    fun y => by split <;> simp
  have hanti : ∀ y, ¬T.FullRead y → h (T.pairMap y) = -h y := by
    intro y hy
    obtain ⟨i, hi, he⟩ := DTree.pairMap_eq_update hy
    simp only [h]
    rw [(DTree.out_path_pairMap T y).1, he, parity_flipAt]
    ring
  have hzero : ∑ y, (if T.FullRead y then 0 else h y) = 0 := by
    have hs := DTree.sum_unread_pair T h
    have : ∑ y, (if T.FullRead y then 0 else h (T.pairMap y)) =
        -∑ y, (if T.FullRead y then 0 else h y) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      split
      · simp
      · next hy => exact hanti y hy
    linarith
  have hfull : ∑ y, (if T.FullRead y then h y else 0) ≤
      ∑ y, (if T.FullRead y then (1 : ℝ) else 0) :=
    Finset.sum_le_sum fun y _ => by
      split
      · simp only [h]
        have := abs_le.mp (show |T.out y * parity y| ≤ 1 by
          rw [abs_mul, abs_parity, mul_one]; exact DTree.abs_out_le hT y)
        exact this.2
      · exact le_refl 0
  rw [Finset.sum_congr rfl fun y _ => hsplit y, Finset.sum_add_distrib, hzero, add_zero]
  exact hfull

/-- **Parity cost gap.** If an exact sign sampler has target `g` with parity correlation
`χ(y) g(y) ≥ α` on every input, then some input requires at least `α m` expected distinct
probes. With `α = 1/2` this is the bound `Q^*(W_φ) ≥ m/2`, and with `α = c/4` the bound
`Q^*(W_φ) ≥ cm/4`.

Paper: cost gap in the proof of `prop:instance-hardness-eight` and in the proof of
`thm:instance-hardness` (instance_hardness.tex). -/
theorem parity_cost_gap {ι : Type*} [Fintype ι] (S : Sampler m ι) (hB : S.Bounded)
    {g : (Fin m → Bool) → ℝ} (hf : S.Exact g) {α : ℝ} (hα : ∀ y, α ≤ parity y * g y) :
    ∃ y, α * m ≤ S.cost y := by
  set u : ℝ := (1 / 2) ^ m
  have hu : u * 2 ^ m = 1 := by simp only [u]; rw [← mul_pow]; norm_num
  have hu0 : 0 ≤ u := by positivity
  set P : ℝ := ∑ ω, S.p ω * (u * ∑ y, (if (S.tree ω).FullRead y then (1 : ℝ) else 0))
  -- correlation is at most the probability of a full read
  have hcorr : α ≤ P := by
    have h1 : α ≤ u * ∑ y, parity y * g y := by
      have := Finset.sum_le_sum (s := Finset.univ) fun y _ => hα y
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul] at this
      push_cast at this
      calc α = u * (2 ^ m * α) := by rw [← mul_assoc, hu, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left this hu0
    have h2 : ∑ y, parity y * g y = ∑ ω, S.p ω * ∑ y, (S.tree ω).out y * parity y := by
      have hf' : ∀ y, g y = S.mean y := fun y => (hf y).symm
      simp_rw [hf', Sampler.mean, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [h2, Finset.mul_sum] at h1
    refine h1.trans (Finset.sum_le_sum fun ω _ => ?_)
    have := tree_parity_corr_le (hB ω)
    have hp := S.p_nonneg ω
    calc u * (S.p ω * ∑ y, (S.tree ω).out y * parity y) =
          S.p ω * (u * ∑ y, (S.tree ω).out y * parity y) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this hu0) hp
  have hcost : (m : ℝ) * P ≤ prodExp (fun _ => 0) S.cost := by
    rw [prodExp_zero]
    unfold Sampler.cost
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun ω _ => ?_
    rw [← Finset.mul_sum]
    have : (m : ℝ) * (u * ∑ y, (if (S.tree ω).FullRead y then (1 : ℝ) else 0)) ≤
        u * ∑ y, (((S.tree ω).path y).card : ℝ) := by
      rw [← mul_assoc, mul_comm (m : ℝ), mul_assoc, Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) hu0
      split
      · next h => rw [mul_one, DTree.card_path_of_fullRead h]
      · simp
    have hp := S.p_nonneg ω
    calc (m : ℝ) * (S.p ω * (u * ∑ y, (if (S.tree ω).FullRead y then (1 : ℝ) else 0))) =
          S.p ω * ((m : ℝ) * (u * ∑ y, (if (S.tree ω).FullRead y then (1 : ℝ) else 0))) := by
            ring
      _ ≤ S.p ω * (u * ∑ y, (((S.tree ω).path y).card : ℝ)) :=
          mul_le_mul_of_nonneg_left this hp
      _ = u * (S.p ω * ∑ y, (((S.tree ω).path y).card : ℝ)) := by ring
  obtain ⟨y, hy⟩ := exists_ge_prodExp (s := fun _ => (0 : ℝ)) (fun _ => by norm_num) S.cost
  refine ⟨y, ?_⟩
  have hm0 : (0 : ℝ) ≤ m := by positivity
  nlinarith

/-! ## The multivariate information certificate -/

namespace DTree

/-- The first directional derivative is linear in the direction. Auxiliary for
`eq:instance-certificate` (instance_information.tex). -/
lemma D1_eq_sum (s v : Fin m → ℝ) (T : DTree m) :
    T.D1 s v = ∑ i, v i * T.D1 s (Pi.single i 1) := by
  induction T with
  | leaf y => simp [D1]
  | node j T₁ T₂ ih₁ ih₂ =>
    simp only [D1]
    rw [ih₁, ih₂]
    have hv : v j = ∑ i, v i * (Pi.single i (1 : ℝ) : Fin m → ℝ) j := by
      simp [Pi.single_apply]
    rw [hv, Finset.sum_div, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

end DTree

/-- The partial derivative `∂ᵢ𝓗(s)` of the product extension. -/
def partialDeriv (f : (Fin m → Bool) → ℝ) (s : Fin m → ℝ) (i : Fin m) : ℝ :=
  deriv (dirProfile f s (Pi.single i 1)) 0

section Certificate

variable {ι : Type*} [Fintype ι] (S : Sampler m ι)

/-- The directional derivative of the product extension at `u = 0`. Auxiliary for
`eq:instance-certificate` (instance_information.tex). -/
lemma deriv_dirProfile_zero (hN : S.NoRepeat) {f : (Fin m → Bool) → ℝ} (hf : S.Exact f)
    (s v : Fin m → ℝ) : deriv (dirProfile f s v) 0 = ∑ ω, S.p ω * (S.tree ω).D1 s v := by
  rw [(hasDerivAt_dirProfile S hN hf s v 0).deriv]
  simp

/-- The directional derivative is `v · ∇𝓗`. Auxiliary for `eq:instance-certificate`
(instance_information.tex). -/
lemma deriv_dirProfile_eq_sum (hN : S.NoRepeat) {f : (Fin m → Bool) → ℝ} (hf : S.Exact f)
    (s v : Fin m → ℝ) : deriv (dirProfile f s v) 0 = ∑ i, v i * partialDeriv f s i := by
  unfold partialDeriv
  simp_rw [deriv_dirProfile_zero S hN hf, DTree.D1_eq_sum s v, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ω _ => ?_
  ring

/-- For admissible directions (`vᵢ² ≤ 1 - sᵢ²`) the directional information is at most the
expected number of distinct probes. Paper: directions with `vᵢ² ≤ 1 - tᵢ²` in
`eq:instance-certificate` (instance_information.tex). -/
lemma info_le_cost (s v : Fin m → ℝ) (hs : ∀ i, |s i| < 1) (hv : ∀ i, v i ^ 2 ≤ 1 - s i ^ 2) :
    info S s v ≤ prodExp s S.cost := by
  unfold info
  rw [S.prodExp_cost]
  refine Finset.sum_le_sum fun i _ => ?_
  have hpos : 0 < 1 - s i ^ 2 := by have := abs_lt.mp (hs i); nlinarith
  have hq : 0 ≤ prodExp s (S.probe i) := by
    have := prodExp_mono (s := s) (fun j => (hs j).le) (g₁ := fun _ => 0) (S.probe_nonneg i)
    rwa [prodExp_const] at this
  have h1 : v i ^ 2 / (1 - s i ^ 2) ≤ 1 := by rw [div_le_one hpos]; exact hv i
  calc v i ^ 2 / (1 - s i ^ 2) * prodExp s (S.probe i) ≤ 1 * prodExp s (S.probe i) :=
        mul_le_mul_of_nonneg_right h1 hq
    _ = prodExp s (S.probe i) := one_mul _

/-- **The multivariate information certificate.** At every interior mean vector `s`, some context
satisfies `(∑ᵢ √(1 - sᵢ²) |∂ᵢ𝓗(s)|)² ≤ (1 - 𝓗(s)²) E[Q | x]` and, for every admissible
direction `v` (`vᵢ² ≤ 1 - sᵢ²`), `|vᵀ∇²𝓗(s) v| / 2 ≤ E[Q | x]`.

Paper: `eq:instance-certificate` (instance_information.tex). -/
theorem instance_certificate (hN : S.NoRepeat) (hB : S.Bounded) {f : (Fin m → Bool) → ℝ}
    (hf : S.Exact f) (s : Fin m → ℝ) (hs : ∀ i, |s i| < 1) :
    ∃ x, (∑ i, Real.sqrt (1 - s i ^ 2) * |partialDeriv f s i|) ^ 2 ≤
        (1 - prodExp s f ^ 2) * S.cost x ∧
      ∀ v : Fin m → ℝ, (∀ i, v i ^ 2 ≤ 1 - s i ^ 2) →
        |deriv (deriv (dirProfile f s v)) 0| / 2 ≤ S.cost x := by
  obtain ⟨x, hx⟩ := exists_ge_prodExp (fun i => (hs i).le) S.cost
  refine ⟨x, ?_, ?_⟩
  · set v : Fin m → ℝ := fun i => Real.sqrt (1 - s i ^ 2) * SignType.sign (partialDeriv f s i)
    have hpos : ∀ i, 0 ≤ 1 - s i ^ 2 := fun i => by have := abs_lt.mp (hs i); nlinarith
    have hv : ∀ i, v i ^ 2 ≤ 1 - s i ^ 2 := by
      intro i
      simp only [v, mul_pow, Real.sq_sqrt (hpos i)]
      have : ((SignType.sign (partialDeriv f s i) : ℝ)) ^ 2 ≤ 1 := by
        rcases lt_trichotomy (partialDeriv f s i) 0 with h | h | h <;> simp [h]
      nlinarith [hpos i]
    have hdir : deriv (dirProfile f s v) 0 =
        ∑ i, Real.sqrt (1 - s i ^ 2) * |partialDeriv f s i| := by
      rw [deriv_dirProfile_eq_sum S hN hf]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [v]
      rw [mul_assoc, sign_mul_self]
    have hmain := (multivariate_transcript S hN hB hf s v hs).1
    rw [hdir] at hmain
    have hI := info_le_cost S s v hs hv
    have hH : prodExp s f ^ 2 ≤ 1 := by
      have hfb : ∀ y, |f y| ≤ 1 := fun y => hf y ▸ S.abs_mean_le hB y
      have h1 : |prodExp s f| ≤ 1 := by
        unfold prodExp
        calc |∑ y, prodLaw s y * f y| ≤ ∑ y, |prodLaw s y * f y| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ y, prodLaw s y * 1 := Finset.sum_le_sum fun y _ => by
              rw [abs_mul, abs_of_nonneg (prodLaw_nonneg (fun i => (hs i).le) y)]
              exact mul_le_mul_of_nonneg_left (hfb y) (prodLaw_nonneg (fun i => (hs i).le) y)
          _ = 1 := by simp [sum_prodLaw]
      nlinarith [abs_nonneg (prodExp s f), sq_abs (prodExp s f)]
    calc (∑ i, Real.sqrt (1 - s i ^ 2) * |partialDeriv f s i|) ^ 2 ≤
          (1 - prodExp s f ^ 2) * info S s v := hmain
      _ ≤ (1 - prodExp s f ^ 2) * S.cost x :=
          mul_le_mul_of_nonneg_left (hI.trans hx) (by linarith)
  · intro v hv
    have h2 := (multivariate_transcript S hN hB hf s v hs).2
    have hI := info_le_cost S s v hs hv
    linarith

end Certificate

/-! ## A positional lower bound for attention -/

section Attention

variable {n : ℕ}

/-- Attention average `Y(x) = ∑ⱼ e^{A xⱼ} xⱼ / ∑ⱼ e^{A xⱼ}` over `n + 1` positions. -/
def attnY (A : ℝ) (x : Fin (n + 1) → Bool) : ℝ :=
  (∑ j, Real.exp (A * sgn (x j)) * sgn (x j)) / ∑ j, Real.exp (A * sgn (x j))

/-- First residual stream `U(x) = (1 - α) x_T + α Y(x)`. -/
def attnU (α A : ℝ) (x : Fin (n + 1) → Bool) : ℝ :=
  (1 - α) * sgn (x (Fin.last n)) + α * attnY A x

/-- Second residual stream `Z(x) = (1 - α) U(x) + α tanh U(x)`. -/
def attnZ (α A : ℝ) (x : Fin (n + 1) → Bool) : ℝ :=
  (1 - α) * attnU α A x + α * Real.tanh (attnU α A x)

/-- Mean of the output sign, `2P(x) - 1 = tanh Z(x)` for the token probability
`P(x) = (1 + tanh Z(x))/2`. -/
def attnTarget (α A : ℝ) (x : Fin (n + 1) → Bool) : ℝ := Real.tanh (attnZ α A x)

/-- `Y(x⁻) = -1` at the all-negative context. Paper: proof of `thm:attentionpositionlower`
(attention_primitives.tex). -/
lemma attnY_allFalse (A : ℝ) : attnY A (fun _ : Fin (n + 1) => false) = -1 := by
  unfold attnY
  simp only [sgn_false, mul_neg, mul_one, Finset.sum_neg_distrib]
  have : ∑ _j : Fin (n + 1), Real.exp (-A) ≠ 0 := by
    rw [Finset.sum_const]; simp [Real.exp_ne_zero, Nat.cast_add_one_ne_zero]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- Sums over a context with a single positive position. Auxiliary for the proof of
`thm:attentionpositionlower` (attention_primitives.tex). -/
lemma sum_update_allFalse (φ : Bool → ℝ) (j : Fin (n + 1)) :
    ∑ k, φ (Function.update (fun _ : Fin (n + 1) => false) j true k) = φ true + n * φ false := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have : ∀ k ∈ Finset.univ.erase j,
      φ (Function.update (fun _ : Fin (n + 1) => false) j true k) = φ false := by
    intro k hk
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin, Function.update_self, nsmul_eq_mul]
  simp

/-- `Y(x^{(j)}) = -1 + 2p` with `p = E/(T - 1 + E)`. Paper: proof of
`thm:attentionpositionlower` (attention_primitives.tex). -/
lemma attnY_update (A : ℝ) (j : Fin (n + 1)) :
    attnY A (Function.update (fun _ => false) j true) =
      -1 + 2 * (Real.exp (2 * A) / (n + Real.exp (2 * A))) := by
  unfold attnY
  rw [sum_update_allFalse (fun b => Real.exp (A * sgn b) * sgn b),
    sum_update_allFalse (fun b => Real.exp (A * sgn b))]
  simp only [sgn_true, sgn_false, mul_one, mul_neg]
  have hE : Real.exp (2 * A) = Real.exp A * Real.exp A := by rw [← Real.exp_add]; ring_nf
  have hinv : Real.exp (-A) * Real.exp A = 1 := by rw [← Real.exp_add]; simp
  have h1 : 0 < Real.exp A := Real.exp_pos A
  have h2 : 0 < Real.exp (-A) := Real.exp_pos (-A)
  have hn : (0 : ℝ) ≤ n := by positivity
  have : Real.exp (-A) = 1 / Real.exp A := by rw [Real.exp_neg, one_div]
  rw [hE, this]
  field_simp
  ring

/-- One flipped position at the all-negative context raises the token probability by at least
`(α p + (1 - α)[j = T])/16`, with `p = E/(T - 1 + E)`: the two scalar maps have slope at least
`1/4` on `[-1, 1]`. Paper: proof of `thm:attentionpositionlower` (attention_primitives.tex). -/
lemma attn_flip_step {α A : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (j : Fin (n + 1)) :
    (α * (Real.exp (2 * A) / (n + Real.exp (2 * A))) +
        (1 - α) * (if j = Fin.last n then 1 else 0)) / 16 ≤
      signTV (attnTarget α A (fun _ : Fin (n + 1) => false))
        (attnTarget α A (Function.update (fun _ => false) j true)) := by
  set E := Real.exp (2 * A) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  have hn : (0 : ℝ) ≤ n := by positivity
  set p := E / (n + E) with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by rw [hp, div_le_one (by linarith)]; linarith
  set x0 : Fin (n + 1) → Bool := fun _ => false
  have hU0 : attnU α A x0 = -1 := by
    simp only [attnU, x0, sgn_false, attnY_allFalse]; ring
  set x1 := Function.update x0 j true
  have hY1 : attnY A x1 = -1 + 2 * p := attnY_update A j
  have hlast : sgn (x1 (Fin.last n)) = -1 + 2 * (if j = Fin.last n then 1 else 0) := by
    by_cases hj : j = Fin.last n
    · simp [x1, hj]; norm_num
    · have : Fin.last n ≠ j := fun h => hj h.symm
      simp [x1, Function.update_of_ne this, x0, hj]
  have hU1 : attnU α A x1 = -1 + 2 * (α * p + (1 - α) * (if j = Fin.last n then 1 else 0)) := by
    simp only [attnU, hY1, hlast]; ring
  set δ := α * p + (1 - α) * (if j = Fin.last n then 1 else 0) with hδ
  have hδ0 : 0 ≤ δ := by
    have : (0 : ℝ) ≤ (if j = Fin.last n then 1 else 0) := by split <;> norm_num
    positivity
  have hδ1 : δ ≤ 1 := by
    have : (if j = Fin.last n then (1 : ℝ) else 0) ≤ 1 := by split <;> norm_num
    nlinarith
  -- the scalar maps have slope at least `1/4` on `[-1,1]`
  have hZ : (attnU α A x1 - attnU α A x0) / 4 ≤ attnZ α A x1 - attnZ α A x0 := by
    have hu : -1 ≤ attnU α A x0 := by rw [hU0]
    have huu : attnU α A x0 ≤ attnU α A x1 := by rw [hU0, hU1]; linarith
    have hu1 : attnU α A x1 ≤ 1 := by rw [hU1]; linarith
    have ht := tanh_sub_ge hu huu hu1
    simp only [attnZ]
    nlinarith
  have hZb : ∀ x : Fin (n + 1) → Bool, -1 ≤ attnU α A x → attnU α A x ≤ 1 →
      -1 ≤ attnZ α A x ∧ attnZ α A x ≤ 1 := by
    intro x h1 h2
    have := abs_le.mp (Real.abs_tanh_lt_one (attnU α A x)).le
    simp only [attnZ]
    constructor <;> nlinarith
  have hZ0 := hZb x0 (by rw [hU0]) (by rw [hU0]; norm_num)
  have hZ1 := hZb x1 (by rw [hU1]; linarith) (by rw [hU1]; linarith)
  have hZle : attnZ α A x0 ≤ attnZ α A x1 := by
    have : 0 ≤ (attnU α A x1 - attnU α A x0) / 4 := by rw [hU0, hU1]; linarith
    linarith
  have hT := tanh_sub_ge hZ0.1 hZle hZ1.2
  rw [signTV_eq]
  unfold attnTarget
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [hU0, hU1] at hZ
  linarith

/-- **Positional lower bound for the final token.** For the binary attention family on
`T = n + 1` positions, with residual weight `0 ≤ α ≤ 1` and score scale `A ≥ 0`, every exact
sampler of the output token has, on the all-negative context,
`E[Q] ≥ ((1 - α) + α T E/(T - 1 + E))/16 ≥ (1 + α min{T, E})/64`, where `E = e^{2A}`.

Paper: `thm:attentionpositionlower`, `eq:attentionpositionlower` (attention_primitives.tex);
the lower half of `eq:main-binary-law` in `thm:main-attention` (main_attention.tex). -/
theorem attention_position_lower {ι : Type*} [Fintype ι] (S : Sampler (n + 1) ι)
    (hB : S.Bounded) {α A : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hA : 0 ≤ A)
    (hf : S.Exact (attnTarget α A)) :
    ((1 - α) + α * (n + 1) * Real.exp (2 * A) / (n + Real.exp (2 * A))) / 16 ≤
        S.cost (fun _ => false) ∧
      (1 + α * min ((n : ℝ) + 1) (Real.exp (2 * A))) / 64 ≤ S.cost (fun _ => false) := by
  set E := Real.exp (2 * A) with hEdef
  have hE1 : 1 ≤ E := by rw [hEdef]; exact Real.one_le_exp (by linarith)
  have hn : (0 : ℝ) ≤ n := by positivity
  set p := E / (n + E) with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by rw [hp, div_le_one (by linarith)]; linarith
  set x0 : Fin (n + 1) → Bool := fun _ => false
  have hU0 : attnU α A x0 = -1 := by
    simp only [attnU, x0, sgn_false, attnY_allFalse]; ring
  have hstep : ∀ j : Fin (n + 1),
      (α * p + (1 - α) * (if j = Fin.last n then 1 else 0)) / 16 ≤
        signTV (attnTarget α A x0) (attnTarget α A (Function.update x0 j true)) :=
    fun j => attn_flip_step hα0 hα1 j
  have hsum := cost_ge_sum_signTV S hB hf x0 (fun _ => true)
  have hlow : ((1 - α) + α * (n + 1) * E / (n + E)) / 16 ≤
      ∑ j : Fin (n + 1), signTV (attnTarget α A x0) (attnTarget α A
        (Function.update x0 j (true))) := by
    calc ((1 - α) + α * (n + 1) * E / (n + E)) / 16 =
          ∑ j : Fin (n + 1), (α * p + (1 - α) * (if j = Fin.last n then 1 else 0)) / 16 := by
            rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum,
              Finset.sum_ite_eq']
            simp only [Finset.card_univ, Fintype.card_fin, Finset.mem_univ, ite_true,
              nsmul_eq_mul, hp]
            push_cast
            field_simp
            ring
      _ ≤ _ := Finset.sum_le_sum fun j _ => hstep j
  have h1 := hlow.trans hsum
  refine ⟨h1, le_trans ?_ h1⟩
  -- `T E/(T - 1 + E) ≥ min{T, E}/2` and `3 - 4α + α M ≥ 0`
  set M := min ((n : ℝ) + 1) E
  have hM1 : 1 ≤ M := le_min (by linarith) hE1
  have hmin : M / 2 ≤ (n + 1) * E / (n + E) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    have hMa : M ≤ (n : ℝ) + 1 := min_le_left _ _
    have hMb : M ≤ E := min_le_right _ _
    nlinarith [mul_le_mul hMa hMb (by linarith) (by linarith)]
  have hα' : α * (M / 2) ≤ α * ((n + 1) * E / (n + E)) := mul_le_mul_of_nonneg_left hmin hα0
  have : α * (n + 1) * E / (n + E) = α * ((n + 1) * E / (n + E)) := by ring
  rw [this]
  nlinarith

/-- The prefix target: the position `T` is fixed to `-1`, and the output is a function of the
first `n = T - 1` positions. -/
def prefixTarget (α A : ℝ) (y : Fin n → Bool) : ℝ :=
  attnTarget α A (Fin.snoc y false : Fin (n + 1) → Bool)

/-- Appending `-1` to the all-negative prefix. Auxiliary for `eq:attentionpositionlowerprefix`
(attention_primitives.tex). -/
lemma snoc_allFalse : (Fin.snoc (fun _ : Fin n => false) false : Fin (n + 1) → Bool) =
    fun _ => false := by
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp
  · simp

/-- Appending `-1` to a prefix with one positive position. Auxiliary for
`eq:attentionpositionlowerprefix` (attention_primitives.tex). -/
lemma snoc_update (j : Fin n) :
    (Fin.snoc (Function.update (fun _ : Fin n => false) j true) false : Fin (n + 1) → Bool) =
      Function.update (fun _ => false) (Fin.castSucc j) true := by
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · have : Fin.last n ≠ Fin.castSucc j := (Fin.castSucc_lt_last j).ne'
    simp [Function.update_of_ne this]
  · simp only [Fin.snoc_castSucc]
    by_cases hk : k = j
    · subst hk; simp
    · have : Fin.castSucc k ≠ Fin.castSucc j := fun h => hk (Fin.castSucc_injective n h)
      simp [Function.update_of_ne hk, Function.update_of_ne this]

/-- **Positional lower bound with the last position known.** If `x_T` is fixed to `-1` and only
the `T - 1` earlier positions are probed, every exact sampler of the output token has, on the
all-negative context, `E[Q] ≥ α (T-1) E/(16 (T - 1 + E)) ≥ (α/32) min{T - 1, E}`.

Paper: `eq:attentionpositionlowerprefix` in `thm:attentionpositionlower`
(attention_primitives.tex). -/
theorem attention_prefix_lower {ι : Type*} [Fintype ι] (S : Sampler n ι) (hB : S.Bounded)
    {α A : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hf : S.Exact (prefixTarget α A)) :
    α * n * Real.exp (2 * A) / (n + Real.exp (2 * A)) / 16 ≤ S.cost (fun _ => false) ∧
      α / 32 * min (n : ℝ) (Real.exp (2 * A)) ≤ S.cost (fun _ => false) := by
  set E := Real.exp (2 * A) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  have hn : (0 : ℝ) ≤ n := by positivity
  have hsum := cost_ge_sum_signTV S hB hf (fun _ => false) (fun _ => true)
  have hstep : ∀ j : Fin n, α * (E / (n + E)) / 16 ≤
      signTV (prefixTarget α A (fun _ : Fin n => false))
        (prefixTarget α A (Function.update (fun _ => false) j true)) := by
    intro j
    have h := attn_flip_step (n := n) (A := A) hα0 hα1 (Fin.castSucc j)
    have hne : Fin.castSucc j ≠ Fin.last n := (Fin.castSucc_lt_last j).ne
    simp only [hne, ite_false, mul_zero, add_zero] at h
    unfold prefixTarget
    rw [snoc_allFalse, snoc_update]
    exact h
  have h1 : α * n * E / (n + E) / 16 ≤ S.cost (fun _ => false) := by
    calc α * n * E / (n + E) / 16 = ∑ _j : Fin n, α * (E / (n + E)) / 16 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => hstep j
      _ ≤ _ := hsum
  refine ⟨h1, le_trans ?_ h1⟩
  have hmin : min (n : ℝ) E / 2 ≤ n * E / (n + E) := by
    rcases hn.lt_or_eq with hpos | hzero
    · rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      have hMa : min (n : ℝ) E ≤ n := min_le_left _ _
      have hMb : min (n : ℝ) E ≤ E := min_le_right _ _
      have hM0 : 0 ≤ min (n : ℝ) E := le_min hn hE0.le
      nlinarith [mul_le_mul hMa hMb hM0 hn]
    · rw [← hzero]; simp [hE0.le]
  have : α * n * E / (n + E) / 16 = α / 16 * (n * E / (n + E)) := by ring
  rw [this]
  calc α / 32 * min (n : ℝ) E = α / 16 * (min (n : ℝ) E / 2) := by ring
    _ ≤ α / 16 * (n * E / (n + E)) := mul_le_mul_of_nonneg_left hmin (by positivity)

end Attention

/-! ## Sign relabelings and trivial samplers -/

/-- Coordinatewise sign flip by a mask: `xᵢ ↦ -xᵢ` where `σᵢ = true`. -/
def xorMask (σ x : Fin m → Bool) : Fin m → Bool := fun i => xor (σ i) (x i)

/-- A sign mask is an involution. Auxiliary for the reduction in the proof of
`prop:profile-obstruction` (instance_information.tex). -/
lemma xorMask_xorMask (σ x : Fin m → Bool) : xorMask σ (xorMask σ x) = x := by
  funext i; simp [xorMask]

namespace DTree

/-- Relabel a tree so that it runs on sign-flipped inputs: branches are exchanged at every node
querying a flipped coordinate. -/
def relabel (σ : Fin m → Bool) : DTree m → DTree m
  | leaf y => leaf y
  | node i T₁ T₂ => if σ i then node i (relabel σ T₂) (relabel σ T₁)
      else node i (relabel σ T₁) (relabel σ T₂)

/-- A relabeled tree runs the original tree on the masked input. Paper: proof of
`prop:profile-obstruction` (instance_information.tex), "a query to either input can be answered
by one query to its image and a deterministic sign flip". -/
lemma out_path_relabel (σ : Fin m → Bool) (T : DTree m) (x : Fin m → Bool) :
    (T.relabel σ).out x = T.out (xorMask σ x) ∧ (T.relabel σ).path x = T.path (xorMask σ x) := by
  induction T with
  | leaf y => exact ⟨rfl, rfl⟩
  | node i T₁ T₂ ih₁ ih₂ =>
    simp only [relabel]
    cases hσ : σ i <;> cases hx : x i <;>
      simp [out, path, hσ, hx, xorMask, (ih₁).1, (ih₁).2, (ih₂).1, (ih₂).2]

/-- Relabeling preserves bounded leaves. Auxiliary for the proof of `prop:profile-obstruction`
(instance_information.tex). -/
lemma bounded_relabel (σ : Fin m → Bool) {T : DTree m} (hT : T.Bounded) :
    (T.relabel σ).Bounded := by
  induction T with
  | leaf y => exact hT
  | node i T₁ T₂ ih₁ ih₂ =>
    simp only [relabel]
    split
    · exact ⟨ih₂ hT.2, ih₁ hT.1⟩
    · exact ⟨ih₁ hT.1, ih₂ hT.2⟩

/-- Relabeling preserves the queried coordinates. Auxiliary for the proof of
`prop:profile-obstruction` (instance_information.tex). -/
lemma queried_relabel (σ : Fin m → Bool) (T : DTree m) :
    (T.relabel σ).queried = T.queried := by
  induction T with
  | leaf y => rfl
  | node i T₁ T₂ ih₁ ih₂ =>
    simp only [relabel]
    split <;> simp [queried, ih₁, ih₂, Finset.union_comm]

/-- Relabeling preserves distinct queries. Auxiliary for the proof of `prop:profile-obstruction`
(instance_information.tex). -/
lemma noRepeat_relabel (σ : Fin m → Bool) {T : DTree m} (hT : T.NoRepeat) :
    (T.relabel σ).NoRepeat := by
  induction T with
  | leaf y => trivial
  | node i T₁ T₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂, hn₁, hn₂⟩ := hT
    simp only [relabel]
    split
    · exact ⟨by rwa [queried_relabel], by rwa [queried_relabel], ih₂ hn₂, ih₁ hn₁⟩
    · exact ⟨by rwa [queried_relabel], by rwa [queried_relabel], ih₁ hn₁, ih₂ hn₂⟩

end DTree

/-- Relabeling a sampler. -/
def Sampler.relabel {ι : Type*} [Fintype ι] (S : Sampler m ι) (σ : Fin m → Bool) :
    Sampler m ι where
  p := S.p
  tree ω := (S.tree ω).relabel σ
  p_nonneg := S.p_nonneg
  p_sum := S.p_sum

/-- **Sign flips preserve query cost.** A sampler for `g` yields, by exchanging branches, a sampler
for `x ↦ g(σ ⊕ x)` with identical probe counts at corresponding inputs. Hence a target and its
partially sign-flipped version have the same optimal worst-input expected query cost.

Paper: `prop:profile-obstruction` (instance_information.tex), reduction between the signed and
unsigned mean chains. -/
theorem relabel_sampler {ι : Type*} [Fintype ι] (S : Sampler m ι) (σ : Fin m → Bool)
    {g : (Fin m → Bool) → ℝ} (hg : S.Exact g) :
    (S.relabel σ).Exact (fun x => g (xorMask σ x)) ∧
      (∀ x, (S.relabel σ).cost x = S.cost (xorMask σ x)) ∧
      (S.NoRepeat → (S.relabel σ).NoRepeat) ∧ (S.Bounded → (S.relabel σ).Bounded) := by
  refine ⟨fun x => ?_, fun x => ?_, fun h ω => DTree.noRepeat_relabel σ (h ω),
    fun h ω => DTree.bounded_relabel σ (h ω)⟩
  · show (S.relabel σ).mean x = g (xorMask σ x)
    rw [← hg]
    unfold Sampler.mean
    exact Finset.sum_congr rfl fun ω _ => by
      rw [show (S.relabel σ).tree ω = (S.tree ω).relabel σ from rfl,
        (DTree.out_path_relabel σ _ x).1]
      rfl
  · unfold Sampler.cost
    exact Finset.sum_congr rfl fun ω _ => by
      rw [show (S.relabel σ).tree ω = (S.tree ω).relabel σ from rfl,
        (DTree.out_path_relabel σ _ x).2]
      rfl

/-- The signed mean chain inherits the exact-form lower bound of the unsigned chain.

Paper: `prop:profile-obstruction` (instance_information.tex) together with `eq:lowerexact`. -/
theorem signed_chain_lower {ι : Type*} [Fintype ι] (S : Sampler m ι) (hN : S.NoRepeat)
    (hB : S.Bounded) (σ : Fin m → Bool) {a : ℝ} (ha : 0 < a) (hm : 1 ≤ m) (D : ℕ)
    (hf : S.Exact (fun x => chainTarget a D (xorMask σ x))) :
    ∃ x, a ^ (2 * D) / (1 + (3 * m - 2) * a ^ (2 * D) * HD a D / (m : ℝ) ^ 2) ≤ S.cost x := by
  obtain ⟨hex, hcost, hN', hB'⟩ := relabel_sampler S σ hf
  have hex' : (S.relabel σ).Exact (chainTarget a D) := fun x => by
    have := hex x
    simp only [xorMask_xorMask] at this
    exact this
  obtain ⟨x, hx⟩ := lower_exact (S.relabel σ) (hN' hN) (hB' hB) ha hm D hex'
  exact ⟨xorMask σ x, by rw [← hcost]; exact hx⟩

/-- The signed mean chain `F_{a,D}(m⁻¹ ∑ⱼ εⱼ xⱼ)` with `εⱼ = 1` on the first half and `-1` on the
second half of the coordinates (the target of `prop:profile-obstruction`). -/
def signedTarget (a : ℝ) (D : ℕ) (x : Fin m → Bool) : ℝ :=
  F a D ((∑ j : Fin m, (if 2 * (j : ℕ) < m then (1 : ℝ) else -1) * sgn (x j)) / m)

/-- The mask flipping the second half of the coordinates. -/
def halfMask : Fin m → Bool := fun j => decide (m ≤ 2 * (j : ℕ))

/-- The signed chain is the unsigned chain composed with the half mask. Paper: proof of
`prop:profile-obstruction` ("replacing `xᵢ` by `-xᵢ` in the second half maps this function to
the unsigned mean chain"). -/
lemma signedTarget_eq (a : ℝ) (D : ℕ) (x : Fin m → Bool) :
    signedTarget a D x = chainTarget a D (xorMask halfMask x) := by
  unfold signedTarget chainTarget signSum
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [xorMask, halfMask]
  by_cases hj : 2 * (j : ℕ) < m
  · have : ¬ m ≤ 2 * (j : ℕ) := by omega
    simp [hj, this]
  · have : m ≤ 2 * (j : ℕ) := by omega
    simp only [hj, this, ite_false, decide_true, Bool.true_xor, sgn_not]
    ring

/-- **The signed mean chain is as hard as the unsigned one.** Every exact sampler for the
signed chain of `prop:profile-obstruction` has a context with
`E[Q | x] ≥ a^{2D}/(1 + (3m - 2) a^{2D} H_D/m²)`.

Paper: `prop:profile-obstruction` (instance_information.tex), with `eq:lowerexact`. -/
theorem signed_target_lower {ι : Type*} [Fintype ι] (S : Sampler m ι) (hN : S.NoRepeat)
    (hB : S.Bounded) {a : ℝ} (ha : 0 < a) (hm : 1 ≤ m) (D : ℕ)
    (hf : S.Exact (signedTarget a D)) :
    ∃ x, a ^ (2 * D) / (1 + (3 * m - 2) * a ^ (2 * D) * HD a D / (m : ℝ) ^ 2) ≤ S.cost x :=
  signed_chain_lower S hN hB halfMask ha hm D fun x => by rw [hf x, signedTarget_eq]

/-- A sampler that makes no probe: it returns a fair sign. -/
def fairSampler : Sampler m Unit where
  p _ := 1
  tree _ := DTree.leaf 0
  p_nonneg _ := zero_le_one
  p_sum := by simp

/-- A network whose output is identically zero is sampled exactly with no input probe and one
fair bit.

Paper: `prop:magnitude-obstruction` (instance_information.tex); the unsatisfiable case
`Q^*(W_φ) = 0` in the proof of `prop:instance-hardness-eight` (instance_hardness.tex). -/
theorem fairSampler_spec :
    (fairSampler (m := m)).Exact (fun _ => 0) ∧ ∀ x, (fairSampler (m := m)).cost x = 0 := by
  refine ⟨fun x => ?_, fun x => ?_⟩ <;> simp [Sampler.mean, Sampler.cost, fairSampler,
    DTree.out, DTree.path]

/-! ## The integer score bound for finite transcripts -/

/-- `(2k + 1)|v| ≤ v² + k(k + 1)` for every integer `v`: no integer lies strictly between
`k` and `k + 1`.

Paper: proof of `cor:new-integer-score` (tanh_new_critical.tex). -/
lemma integer_score_line (v : ℤ) (k : ℕ) :
    (2 * k + 1) * |(v : ℝ)| ≤ (v : ℝ) ^ 2 + k * (k + 1) := by
  have h : |v| ≤ k ∨ k + 1 ≤ |v| := by omega
  have hsq : (v : ℝ) ^ 2 = |(v : ℝ)| ^ 2 := (sq_abs _).symm
  rcases h with h | h
  · have hc : |(v : ℝ)| ≤ k := by exact_mod_cast h
    have h0 : 0 ≤ |(v : ℝ)| := abs_nonneg _
    nlinarith
  · have hc : (k : ℝ) + 1 ≤ |(v : ℝ)| := by exact_mod_cast h
    nlinarith

/-- **Integer score bound.** At the fair point, the first transcript score of a finite
decision-tree factory is integer valued, so
`E₀ Q ≥ (2k + 1)|H'(0)| - k(k + 1)` for every integer `k ≥ 0`, where `H(t) = E_t Y` is the
output mean of the sampler under common input mean `t`.

Paper: `cor:new-integer-score` (tanh_new_critical.tex), for factories given by finitely many
decision trees; the finite-mean extension uses `lem:new-finite-score`, not formalized here. The
specialization to `G_r(z) = tanh(rz)/tanh r` needs that extension, since `G_r` is not a
polynomial and no finite mixture of decision trees samples it exactly. -/
theorem integer_score_bound {ι : Type*} [Fintype ι] (S : Sampler m ι) (hN : S.NoRepeat)
    (hB : S.Bounded) (k : ℕ) :
    (2 * k + 1) * |deriv (meanProfile S.mean) 0| - k * (k + 1) ≤ expCost S 0 := by
  have hf : S.Exact S.mean := fun _ => rfl
  set s : Fin m → ℝ := fun _ => 0
  set v : Fin m → ℝ := fun _ => 1
  have hs : ∀ i, |s i| < 1 := fun _ => by simp [s]
  have hs' : ∀ i, |s i| ≤ 1 := fun i => (hs i).le
  have hd : deriv (meanProfile S.mean) 0 = ∑ ω, S.p ω * (S.tree ω).D1 s v := by
    have h := deriv_dirProfile_zero S hN hf s v
    rw [show dirProfile S.mean s v = fun u => meanProfile S.mean (0 + u) from
      dirProfile_const S.mean 0] at h
    rw [← h, deriv_comp_const_add, add_zero]
  have hEQ : ∑ ω, S.p ω * (S.tree ω).rW s (DTree.infoWeight s v) = expCost S 0 := by
    rw [S.sum_rW hN]
    unfold expCost
    rw [S.prodExp_cost]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [DTree.infoWeight, s, v]
  -- integrality of the stopped score
  have hinv : ∀ (i : Fin m) (z _a : ℝ), (∃ n : ℤ, z = n) →
      (∃ n : ℤ, z + v i / (1 + s i) = n) ∧ (∃ n : ℤ, z - v i / (1 - s i) = n) := by
    rintro i z _ ⟨n, rfl⟩
    exact ⟨⟨n + 1, by simp [s, v]⟩, ⟨n - 1, by simp [s, v]⟩⟩
  have hpt : ∀ (c : ℝ), c = 1 ∨ c = -1 → ∀ ω,
      (2 * k + 1) * (c * (S.tree ω).D1 s v) ≤
        (S.tree ω).rW s (DTree.infoWeight s v) + k * (k + 1) := by
    intro c hc ω
    have hD1 : (S.tree ω).D1 s v = (S.tree ω).ev s v (fun y z _ => y * z) 0 0 := by
      rw [DTree.ev_YZ v hs]; ring
    have hup := DTree.ev_mono (v := v) hs' (fun z _ => ∃ n : ℤ, z = n) hinv
      (φ := fun y z _ => ((2 * k + 1) * c) * (y * z))
      (ψ := fun _ z _ => z ^ 2 + k * (k + 1) * 1)
      (fun y z a hy ⟨n, hn⟩ => by
        subst hn
        have h1 := integer_score_line n k
        have h2 : c * (y * n) ≤ |(n : ℝ)| := by
          have : |c * (y * n)| ≤ |(n : ℝ)| := by
            rw [abs_mul, abs_mul]
            rcases hc with rfl | rfl <;> simp only [abs_one, abs_neg, one_mul] <;>
              exact mul_le_of_le_one_left (abs_nonneg _) hy
          exact (abs_le.mp this).2
        have hk : (0 : ℝ) ≤ 2 * k + 1 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h2 hk])
      (hB ω) (z := 0) (a := 0) ⟨0, by simp⟩
    rw [DTree.ev_const_mul, DTree.ev_add, DTree.ev_Z2 v hs, DTree.ev_const_mul,
      DTree.ev_one] at hup
    rw [hD1]
    nlinarith
  have hsum : ∀ c : ℝ, c = 1 ∨ c = -1 →
      (2 * k + 1) * (c * deriv (meanProfile S.mean) 0) ≤ expCost S 0 + k * (k + 1) := by
    intro c hc
    rw [hd, ← hEQ, Finset.mul_sum, Finset.mul_sum]
    calc ∑ ω, (2 * k + 1) * (c * (S.p ω * (S.tree ω).D1 s v)) =
          ∑ ω, S.p ω * ((2 * k + 1) * (c * (S.tree ω).D1 s v)) :=
            Finset.sum_congr rfl fun ω _ => by ring
      _ ≤ ∑ ω, S.p ω * ((S.tree ω).rW s (DTree.infoWeight s v) + k * (k + 1)) :=
          Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpt c hc ω) (S.p_nonneg ω)
      _ = ∑ ω, S.p ω * (S.tree ω).rW s (DTree.infoWeight s v) + k * (k + 1) := by
          rw [Finset.sum_congr rfl fun ω _ => mul_add _ _ _, Finset.sum_add_distrib,
            ← Finset.sum_mul, S.p_sum, one_mul]
  have h1 := hsum 1 (Or.inl rfl)
  have h2 := hsum (-1) (Or.inr rfl)
  rcases le_total 0 (deriv (meanProfile S.mean) 0) with h | h
  · rw [abs_of_nonneg h]; linarith
  · rw [abs_of_nonpos h]; linarith


/-! ## Finite inputs and arbitrary depth -/

/-- `cosh r ≤ 1 + r²/2 + r⁴/24 + r⁶/600` on `[0,1]`, from the exponential series.
Auxiliary for `eq:chainrange` (tanh_mean.tex). -/
lemma cosh_le_poly {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.cosh r ≤ 1 + r ^ 2 / 2 + r ^ 4 / 24 + r ^ 6 / 600 := by
  have h1 : |r| ≤ 1 := by rw [abs_of_nonneg hr0]; exact hr1
  have h2 : |-r| ≤ 1 := by rw [abs_neg]; exact h1
  have e1 := Real.exp_bound h1 (n := 6) (by norm_num)
  have e2 := Real.exp_bound h2 (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, abs_neg,
    abs_of_nonneg hr0] at e1 e2
  norm_num at e1 e2
  rw [Real.cosh_eq]
  have := (abs_le.mp e1).2
  have := (abs_le.mp e2).2
  nlinarith [pow_nonneg hr0 6]

/-- A polynomial inequality on `[0, 3/4]`. Auxiliary for `eq:chainrange` (tanh_mean.tex). -/
lemma chainrange_poly {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 3 / 4) :
    ((1 + w / 6 + w ^ 2 / 100) * (1 + w / 2 + w ^ 2 / 24 + w ^ 3 / 600)) ^ 2 * (3 - 4 * w) ≤
      3 := by
  have hP : (1 + w / 6 + w ^ 2 / 100) * (1 + w / 2 + w ^ 2 / 24 + w ^ 3 / 600) ≤
      1 + 2 * w / 3 + 3 * w ^ 2 / 20 := by
    nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0,
      mul_nonneg (mul_nonneg h0 h0) (mul_nonneg h0 h0),
      mul_nonneg (mul_nonneg (mul_nonneg h0 h0) (mul_nonneg h0 h0)) h0]
  have hP0 : 0 ≤ (1 + w / 6 + w ^ 2 / 100) * (1 + w / 2 + w ^ 2 / 24 + w ^ 3 / 600) := by
    positivity
  have h34 : 0 ≤ 3 - 4 * w := by linarith
  have hsq := pow_le_pow_left₀ hP0 hP 2
  calc ((1 + w / 6 + w ^ 2 / 100) * (1 + w / 2 + w ^ 2 / 24 + w ^ 3 / 600)) ^ 2 * (3 - 4 * w)
      ≤ (1 + 2 * w / 3 + 3 * w ^ 2 / 20) ^ 2 * (3 - 4 * w) :=
        mul_le_mul_of_nonneg_right hsq h34
    _ ≤ 3 := by
        nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0,
          mul_nonneg (mul_nonneg h0 h0) (mul_nonneg h0 h0),
          mul_nonneg (mul_nonneg (mul_nonneg h0 h0) (mul_nonneg h0 h0)) h0]

/-- `sinh² u (3 - u²) ≤ 3u²` for `u ≥ 0`, through `sinh u = 2 sinh(u/2) cosh(u/2)` and series
bounds at `u/2 ≤ √3/2`. Auxiliary for `eq:chainrange` (tanh_mean.tex). -/
lemma sinh_sq_bound {u : ℝ} (hu : 0 ≤ u) : Real.sinh u ^ 2 * (3 - u ^ 2) ≤ 3 * u ^ 2 := by
  by_cases hbig : 3 ≤ u ^ 2
  · have : Real.sinh u ^ 2 * (3 - u ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
    nlinarith [sq_nonneg u]
  push Not at hbig
  set v := u / 2 with hv
  have hv0 : 0 ≤ v := by positivity
  have hv1 : v ≤ 1 := by nlinarith
  set w := v ^ 2 with hw
  have hw0 : 0 ≤ w := sq_nonneg v
  have hw1 : w ≤ 3 / 4 := by rw [hw, hv]; nlinarith
  have hsinh : Real.sinh u = 2 * Real.sinh v * Real.cosh v := by
    rw [← Real.sinh_two_mul]; congr 1; rw [hv]; ring
  have hs0 : 0 ≤ Real.sinh v := Real.sinh_nonneg_iff.mpr hv0
  have hc0 : 0 ≤ Real.cosh v := (Real.cosh_pos v).le
  have hs : Real.sinh v ≤ v * (1 + w / 6 + w ^ 2 / 100) := by
    calc Real.sinh v ≤ v + v ^ 3 / 6 + v ^ 5 / 100 := sinh_le_poly hv0 hv1
      _ = v * (1 + w / 6 + w ^ 2 / 100) := by rw [hw]; ring
  have hc : Real.cosh v ≤ 1 + w / 2 + w ^ 2 / 24 + w ^ 3 / 600 := by
    calc Real.cosh v ≤ 1 + v ^ 2 / 2 + v ^ 4 / 24 + v ^ 6 / 600 := cosh_le_poly hv0 hv1
      _ = 1 + w / 2 + w ^ 2 / 24 + w ^ 3 / 600 := by rw [hw]; ring
  have hsu : Real.sinh u ≤
      u * ((1 + w / 6 + w ^ 2 / 100) * (1 + w / 2 + w ^ 2 / 24 + w ^ 3 / 600)) := by
    rw [hsinh]
    have := mul_le_mul hs hc hc0 (by positivity)
    calc 2 * Real.sinh v * Real.cosh v = 2 * (Real.sinh v * Real.cosh v) := by ring
      _ ≤ 2 * (v * (1 + w / 6 + w ^ 2 / 100) * (1 + w / 2 + w ^ 2 / 24 + w ^ 3 / 600)) := by
          linarith
      _ = _ := by rw [hv]; ring
  have hsu0 : 0 ≤ Real.sinh u := by rw [hsinh]; positivity
  have hsq := pow_le_pow_left₀ hsu0 hsu 2
  have h34 : 0 ≤ 3 - u ^ 2 := by linarith
  have hkey := chainrange_poly hw0 hw1
  have hu2 : u ^ 2 = 4 * w := by rw [hw, hv]; ring
  calc Real.sinh u ^ 2 * (3 - u ^ 2) ≤
        (u * ((1 + w / 6 + w ^ 2 / 100) * (1 + w / 2 + w ^ 2 / 24 + w ^ 3 / 600))) ^ 2 *
          (3 - u ^ 2) := mul_le_mul_of_nonneg_right hsq h34
    _ = u ^ 2 * (((1 + w / 6 + w ^ 2 / 100) * (1 + w / 2 + w ^ 2 / 24 + w ^ 3 / 600)) ^ 2 *
          (3 - 4 * w)) := by rw [hu2]; ring
    _ ≤ u ^ 2 * 3 := mul_le_mul_of_nonneg_left hkey (sq_nonneg u)
    _ = 3 * u ^ 2 := by ring

/-- **The lower reciprocal-square inequality** `coth² u ≥ u^{-2} + 2/3`, in the form
`tanh² u · (1 + 2u²/3) ≤ u²` for all `u ≥ 0`.

Paper: the reciprocal-square inequalities before `eq:chainrange` (tanh_mean.tex). -/
theorem tanh_sq_le_two_thirds {u : ℝ} (hu : 0 ≤ u) :
    Real.tanh u ^ 2 * (1 + 2 * u ^ 2 / 3) ≤ u ^ 2 := by
  have hc := Real.cosh_pos u
  rw [Real.tanh_eq_sinh_div_cosh, div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity),
    Real.cosh_sq]
  have := sinh_sq_bound hu
  nlinarith

/-- The geometric sum `A = ∑_{j=1}^D s^{2j}`. -/
def chainA (s : ℝ) (D : ℕ) : ℝ := ∑ j ∈ Finset.range D, s ^ (2 * (j + 1))

/-- `A_{D+1} = A_D + s^{2(D+1)}`. Auxiliary for `eq:chainrange` (tanh_mean.tex). -/
lemma chainA_succ (s : ℝ) (D : ℕ) : chainA s (D + 1) = chainA s D + s ^ (2 * (D + 1)) := by
  simp [chainA, Finset.sum_range_succ]

/-- `A ≥ 0`. Auxiliary for `eq:chainrange` (tanh_mean.tex). -/
lemma chainA_nonneg (s : ℝ) (D : ℕ) : 0 ≤ chainA s D :=
  Finset.sum_nonneg fun j _ => by rw [pow_mul]; positivity

/-- `s^{2D} H_D = A`. Auxiliary for `eq:chainrange` (tanh_mean.tex). -/
lemma pow_mul_HD {s : ℝ} (hs : 0 < s) (D : ℕ) : s ^ (2 * D) * HD s D = chainA s D := by
  induction D with
  | zero => simp [HD, chainA]
  | succ D ih =>
    rw [HD_succ, chainA_succ, ← ih]
    have hs2 : s ^ 2 ≠ 0 := by positivity
    rw [show 2 * (D + 1) = 2 * D + 2 by ring, pow_add, pow_mul]
    field_simp
    ring

/-- **The range comparison `eq:chainrange`.** For `s > 0`, with `λ = s^D` and
`A = ∑_{j=1}^D s^{2j}`, the radius `R = F_{s,D}(1)` satisfies
`λ/√(1 + A) ≤ R` and `R² ≤ λ²/(1 + 2A/3)`.

Paper: `eq:chainrange` (tanh_mean.tex). -/
theorem chainrange {s : ℝ} (hs : 0 < s) (D : ℕ) :
    s ^ D / Real.sqrt (1 + chainA s D) ≤ F s D 1 ∧
      F s D 1 ^ 2 ≤ (s ^ D) ^ 2 / (1 + 2 * chainA s D / 3) := by
  constructor
  · have h := chain_lower hs one_pos D
    rwa [one_pow, mul_one, mul_one, pow_mul_HD hs] at h
  · -- reciprocal-square induction with the lower inequality
    have key : ∀ d : ℕ, 0 < F s d 1 ∧ 1 + 2 * chainA s d / 3 ≤ s ^ (2 * d) / F s d 1 ^ 2 := by
      intro d
      induction d with
      | zero => simp [F, chainA]
      | succ d ih =>
        obtain ⟨h0, h1⟩ := ih
        have hw : 0 < s * F s d 1 := mul_pos hs h0
        have hF : F s (d + 1) 1 = Real.tanh (s * F s d 1) := rfl
        have ht := tanh_sq_le_two_thirds hw.le
        have htp : 0 < Real.tanh (s * F s d 1) := tanh_pos hw
        refine ⟨by rw [hF]; exact htp, ?_⟩
        rw [hF, chainA_succ]
        -- `1/tanh²(sF) ≥ 1/(s²F²) + 2/3`
        have hrec : 1 / (s * F s d 1) ^ 2 + 2 / 3 ≤ 1 / Real.tanh (s * F s d 1) ^ 2 := by
          rw [div_add' _ _ _ (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have hpow : s ^ (2 * (d + 1)) = s ^ (2 * d) * s ^ 2 := by
          rw [show 2 * (d + 1) = 2 * d + 2 by ring, pow_add]
        have hmain : s ^ (2 * d) / F s d 1 ^ 2 + 2 / 3 * s ^ (2 * (d + 1)) ≤
            s ^ (2 * (d + 1)) / Real.tanh (s * F s d 1) ^ 2 := by
          have hp : 0 ≤ s ^ (2 * (d + 1)) := by positivity
          have := mul_le_mul_of_nonneg_left hrec hp
          have e : s ^ (2 * (d + 1)) * (1 / (s * F s d 1) ^ 2 + 2 / 3) =
              s ^ (2 * d) / F s d 1 ^ 2 + 2 / 3 * s ^ (2 * (d + 1)) := by
            rw [hpow]; field_simp
          rw [e] at this
          calc _ ≤ _ := this
            _ = s ^ (2 * (d + 1)) / Real.tanh (s * F s d 1) ^ 2 := by ring
        linarith
    obtain ⟨h0, h1⟩ := key D
    have hpos : 0 < 1 + 2 * chainA s D / 3 := by have := chainA_nonneg s D; positivity
    rw [le_div_iff₀ (by positivity)] at h1
    rw [le_div_iff₀ hpos, ← pow_mul, mul_comm D 2]
    nlinarith

/-- **Any two inputs.** Under the common tape, outputs on two inputs can differ only on tapes
that probe at least once, so `|E[Y | x] - E[Y | x']|/2 ≤ E[Q | x]`.

Paper: endpoint coupling in the proofs of `thm:uniformchain` and `thm:finitejoint`
(tanh_mean.tex). -/
theorem mean_diff_le_cost {ι : Type*} [Fintype ι] (S : Sampler m ι) (hB : S.Bounded)
    (x x' : Fin m → Bool) : |S.mean x - S.mean x'| / 2 ≤ S.cost x := by
  unfold Sampler.mean Sampler.cost
  have hpt : ∀ ω, |(S.tree ω).out x - (S.tree ω).out x'| ≤
      2 * (((S.tree ω).path x).card : ℝ) := by
    intro ω
    cases hT : S.tree ω with
    | leaf y => simp [DTree.out]
    | node i T₁ T₂ =>
      have hcard : (1 : ℝ) ≤ ((DTree.node i T₁ T₂).path x).card := by
        simp only [DTree.path]
        exact_mod_cast Finset.card_pos.mpr (Finset.insert_nonempty _ _)
      have hb := hB ω
      rw [hT] at hb
      calc |(DTree.node i T₁ T₂).out x - (DTree.node i T₁ T₂).out x'| ≤
            |(DTree.node i T₁ T₂).out x| + |(DTree.node i T₁ T₂).out x'| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add (DTree.abs_out_le hb _) (DTree.abs_out_le hb _)
        _ ≤ 2 * ((DTree.node i T₁ T₂).path x).card := by linarith
  rw [← Finset.sum_sub_distrib, div_le_iff₀ two_pos]
  calc |∑ ω, (S.p ω * (S.tree ω).out x - S.p ω * (S.tree ω).out x')| ≤
        ∑ ω, |S.p ω * (S.tree ω).out x - S.p ω * (S.tree ω).out x'| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ω, S.p ω * (2 * (((S.tree ω).path x).card : ℝ)) :=
        Finset.sum_le_sum fun ω _ => by
          rw [← mul_sub, abs_mul, abs_of_nonneg (S.p_nonneg ω)]
          exact mul_le_mul_of_nonneg_left (hpt ω) (S.p_nonneg ω)
    _ = (∑ ω, S.p ω * (((S.tree ω).path x).card : ℝ)) * 2 := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun ω _ => by ring

/-- A balanced input exists for even `m`. Auxiliary for `eq:balancedinfluence`
(tanh_mean.tex). -/
lemma exists_balanced (hm : Even m) : ∃ x : Fin m → Bool, signSum x = 0 := by
  obtain ⟨h, rfl⟩ := hm
  refine ⟨fun i => decide ((i : ℕ) < h), ?_⟩
  unfold signSum
  rw [Fin.sum_univ_eq_sum_range (fun i => sgn (decide (i < h))), show h + h = h + h from rfl,
    Finset.sum_range_add]
  have h1 : ∑ i ∈ Finset.range h, sgn (decide (i < h)) = ∑ _i ∈ Finset.range h, (1 : ℝ) :=
    Finset.sum_congr rfl fun i hi => by rw [Finset.mem_range] at hi; simp [sgn, hi]
  have h2 : ∑ i ∈ Finset.range h, sgn (decide (h + i < h)) =
      ∑ _i ∈ Finset.range h, (-1 : ℝ) :=
    Finset.sum_congr rfl fun i _ => by simp [sgn]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1 h2
  rw [h1, h2]; ring

/-- **Balanced-input coupling.** At a balanced input, flipping any one sign moves the mean by
`2/m`, so `E[Q | x] ≥ (m/2) F_{s,D}(2/m) ≥ λ/√(1 + 4A/m²)`.

Paper: `eq:balancedinfluence` (tanh_mean.tex) and the case `m < 100` in the proof of
`thm:finitejoint`. -/
theorem balanced_lower {ι : Type*} [Fintype ι] (S : Sampler m ι) (hB : S.Bounded) {s : ℝ}
    (hs : 0 < s) (hm : 1 ≤ m) (D : ℕ) (hf : S.Exact (chainTarget s D)) {x : Fin m → Bool}
    (hx : signSum x = 0) :
    (m : ℝ) / 2 * F s D (2 / m) ≤ S.cost x ∧
      s ^ D / Real.sqrt (1 + 4 * chainA s D / (m : ℝ) ^ 2) ≤ S.cost x := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hsum := cost_ge_sum_signTV S hB hf x (fun i => !x i)
  have hF0 : F s D 0 = 0 := by
    have h := F_neg s D 0; rw [neg_zero] at h; linarith
  have hz : 0 < 2 / (m : ℝ) := by positivity
  have hchain := chain_lower hs hz D
  rw [pow_mul_HD hs] at hchain
  have hFpos : 0 ≤ F s D (2 / m) := (F_pos hs D hz).le
  have hterm : ∀ i : Fin m, F s D (2 / m) / 2 ≤
      signTV (chainTarget s D x) (chainTarget s D (Function.update x i (!x i))) := by
    intro i
    rw [signTV_eq]
    have hflip : Function.update x i (!x i) = flipAt i x := rfl
    rw [hflip]
    unfold chainTarget
    rw [signSum_flipAt, hx]
    cases hxi : x i
    · simp only [sgn_false, zero_div, hF0]
      rw [show (0 - 2 * -1) / (m : ℝ) = 2 / m by ring, zero_sub, abs_neg, abs_of_nonneg hFpos]
    · simp only [sgn_true, zero_div, hF0]
      rw [show (0 - 2 * 1) / (m : ℝ) = -(2 / m) by ring, F_neg, sub_neg_eq_add, zero_add,
        abs_of_nonneg hFpos]
  have hsumF : (m : ℝ) * (F s D (2 / m) / 2) ≤ S.cost x := by
    calc (m : ℝ) * (F s D (2 / m) / 2) = ∑ _i : Fin m, F s D (2 / m) / 2 := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => hterm i
      _ ≤ S.cost x := hsum
  have hK : 1 + chainA s D * (2 / (m : ℝ)) ^ 2 = 1 + 4 * chainA s D / (m : ℝ) ^ 2 := by ring
  rw [hK] at hchain
  refine ⟨by linarith, ?_⟩
  calc s ^ D / Real.sqrt (1 + 4 * chainA s D / (m : ℝ) ^ 2) =
        (m : ℝ) * (s ^ D * (2 / m) / Real.sqrt (1 + 4 * chainA s D / (m : ℝ) ^ 2) / 2) := by
          field_simp
    _ ≤ (m : ℝ) * (F s D (2 / m) / 2) := by gcongr
    _ ≤ S.cost x := hsumF

/-! ### Case analyses of `thm:finitejoint` and `thm:finitecritical` -/

/-- `min{ρ, M/ρ} ≤ √M`. Auxiliary for the case `m < 100` of `thm:finitejoint`. -/
lemma min_le_sqrt {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) : min ρ (M / ρ) ≤ Real.sqrt M := by
  rcases le_total ρ (Real.sqrt M) with h | h
  · exact (min_le_left _ _).trans h
  · refine (min_le_right _ _).trans ?_
    rw [div_le_iff₀ hρ]
    calc M = Real.sqrt M * Real.sqrt M := (Real.mul_self_sqrt hM).symm
      _ ≤ Real.sqrt M * ρ := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)

/-- **The lower bound of `thm:finitejoint`, case analysis.** Write `ρ = √(1 + A)` and
`Ξ = λ min{ρ, m/ρ}`. Suppose
* `λ/ρ ≤ R ≤ λ/√(1 + 2A/3)` (`eq:chainrange`),
* `R ≤ Q` (endpoint coupling),
* `λ/√(1 + 3A/m) ≤ h` (`eq:derivativelower` with `(3m - 2)/m² ≤ 3/m`),
* `2R/h ≤ 1/2 → 3h²/(16R) ≤ Q` (bending and the second transcript bound),
* `m < 100 → λ/√(1 + 4A/m²) ≤ Q` (coupling at a balanced input).

Then `Ξ/128 ≤ Q`.

Paper: lower bound in the proof of `thm:finitejoint` (tanh_mean.tex). -/
theorem finitejoint_arith {lam A M R h Q : ℝ} (hlam : 0 < lam) (hA : 0 ≤ A) (hM : 2 ≤ M)
    (hRlo : lam / Real.sqrt (1 + A) ≤ R) (hRhi : R ≤ lam / Real.sqrt (1 + 2 * A / 3))
    (hQR : R ≤ Q) (hh : lam / Real.sqrt (1 + 3 * A / M) ≤ h)
    (hbend : 2 * R / h ≤ 1 / 2 → 3 * h ^ 2 / (16 * R) ≤ Q)
    (hbal : M < 100 → lam / Real.sqrt (1 + 4 * A / M ^ 2) ≤ Q) :
    lam * min (Real.sqrt (1 + A)) (M / Real.sqrt (1 + A)) / 128 ≤ Q := by
  set ρ := Real.sqrt (1 + A) with hρdef
  have hρ2 : ρ ^ 2 = 1 + A := Real.sq_sqrt (by linarith)
  have hρ1 : 1 ≤ ρ := by rw [hρdef]; exact Real.one_le_sqrt.mpr (by linarith)
  have hρ0 : 0 < ρ := by linarith
  have hM0 : 0 < M := by linarith
  set Ξ := lam * min ρ (M / ρ) with hΞ
  have hΞ1 : Ξ ≤ lam * ρ := mul_le_mul_of_nonneg_left (min_le_left _ _) hlam.le
  have hΞ2 : Ξ ≤ lam * (M / ρ) := mul_le_mul_of_nonneg_left (min_le_right _ _) hlam.le
  have hΞ0 : 0 ≤ Ξ := mul_nonneg hlam.le (le_min hρ0.le (by positivity))
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hRlo
  by_cases hA100 : A < 100
  · -- `Q ≥ R ≥ λ/ρ ≥ Ξ/(1 + A) ≥ Ξ/101`
    have h1 : Ξ / ρ ^ 2 ≤ lam / ρ := by
      rw [div_le_div_iff₀ (by positivity) hρ0]
      calc Ξ * ρ ≤ lam * ρ * ρ := mul_le_mul_of_nonneg_right hΞ1 hρ0.le
        _ = lam * ρ ^ 2 := by ring
    have h2 : Ξ / 128 ≤ Ξ / ρ ^ 2 := by
      apply div_le_div_of_nonneg_left hΞ0 (by positivity); rw [hρ2]; linarith
    linarith
  push Not at hA100
  by_cases hM100 : M < 100
  · have hQ := hbal hM100
    have hden : 0 < 1 + 4 * A / M ^ 2 := by positivity
    by_cases hAM : A ≤ M ^ 2
    · -- `Q ≥ λ/√5` and `Ξ ≤ λ √M ≤ 10 λ`
      have h5 : Real.sqrt (1 + 4 * A / M ^ 2) ≤ Real.sqrt 5 := Real.sqrt_le_sqrt (by
        have : 4 * A / M ^ 2 ≤ 4 := by rw [div_le_iff₀ (by positivity)]; linarith
        linarith)
      have hs5 : Real.sqrt 5 ≤ 5 / 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have hQ' : lam / (5 / 2) ≤ Q := le_trans (div_le_div_of_nonneg_left hlam.le
        (Real.sqrt_pos.mpr hden) (h5.trans hs5)) hQ
      have hsq : Real.sqrt M ≤ 10 := by
        rw [Real.sqrt_le_left (by norm_num)]; linarith
      have hΞ3 : Ξ ≤ lam * 10 :=
        (mul_le_mul_of_nonneg_left (min_le_sqrt hρ0 hM0.le) hlam.le).trans
          (mul_le_mul_of_nonneg_left hsq hlam.le)
      linarith
    · -- `Q ≥ λ M/√(5A) ≥ Ξ/√5`
      push Not at hAM
      have hA0 : 0 < A := lt_of_le_of_lt (sq_nonneg M) hAM
      have hle : 1 + 4 * A / M ^ 2 ≤ 5 * A / M ^ 2 := by
        have h1 : 1 ≤ A / M ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
        have : 5 * A / M ^ 2 = A / M ^ 2 + 4 * A / M ^ 2 := by ring
        linarith
      have hsq : Real.sqrt (1 + 4 * A / M ^ 2) ≤ Real.sqrt (5 * A / M ^ 2) :=
        Real.sqrt_le_sqrt hle
      have hs5A : Real.sqrt (5 * A / M ^ 2) = Real.sqrt 5 * Real.sqrt A / M := by
        rw [Real.sqrt_div' _ (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq hM0.le]
      have hQ' : lam * M / (Real.sqrt 5 * Real.sqrt A) ≤ Q := by
        have := le_trans (div_le_div_of_nonneg_left hlam.le (Real.sqrt_pos.mpr hden) hsq) hQ
        rw [hs5A] at this
        calc lam * M / (Real.sqrt 5 * Real.sqrt A) = lam / (Real.sqrt 5 * Real.sqrt A / M) := by
              field_simp
          _ ≤ Q := this
      -- `Ξ ≤ λ M/ρ ≤ λ M/√A`
      have hρA : Real.sqrt A ≤ ρ := Real.sqrt_le_sqrt (by linarith)
      have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA0
      have hΞ4 : Ξ ≤ lam * M / Real.sqrt A := by
        calc Ξ ≤ lam * (M / ρ) := hΞ2
          _ ≤ lam * (M / Real.sqrt A) :=
              mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hM0.le hsA hρA) hlam.le
          _ = lam * M / Real.sqrt A := by ring
      have hs5 : Real.sqrt 5 ≤ 128 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have : lam * M / Real.sqrt A / 128 ≤ lam * M / (Real.sqrt 5 * Real.sqrt A) := by
        rw [div_div]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        have := mul_le_mul_of_nonneg_right hs5 hsA.le
        linarith
      linarith
  push Not at hM100
  -- large `A` and large `m`: bending applies
  have hpos3 : 0 < 1 + 3 * A / M := by positivity
  have hpos2 : 0 < 1 + 2 * A / 3 := by positivity
  have hh0 : 0 < h := lt_of_lt_of_le (by positivity) hh
  -- `h² ≥ λ²/(1 + 3A/m)` and `R² ≤ λ²/(1 + 2A/3)`
  have hh2 : lam ^ 2 / (1 + 3 * A / M) ≤ h ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hh 2
    rwa [div_pow, Real.sq_sqrt hpos3.le] at this
  have hR2 : R ^ 2 ≤ lam ^ 2 / (1 + 2 * A / 3) := by
    have := pow_le_pow_left₀ hR0.le hRhi 2
    rwa [div_pow, Real.sq_sqrt hpos2.le] at this
  -- `T² = 4R²/h² ≤ 6/A + 18/m ≤ 0.24`
  have hT : 2 * R / h ≤ 1 / 2 := by
    have hT2 : (2 * R / h) ^ 2 ≤ (1 / 2) ^ 2 := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      have key : 4 * (1 + 3 * A / M) ≤ (1 / 4) * (1 + 2 * A / 3) := by
        have h1 : 3 * A / M ≤ 3 * A / 100 := div_le_div_of_nonneg_left (by positivity)
          (by norm_num) hM100
        linarith
      have e1 : (2 * R) ^ 2 = 4 * R ^ 2 := by ring
      rw [e1]
      have h3 : 4 * R ^ 2 ≤ 4 * (lam ^ 2 / (1 + 2 * A / 3)) := by linarith
      have h4 : 4 * (lam ^ 2 / (1 + 2 * A / 3)) ≤ (1 / 2) ^ 2 * (lam ^ 2 / (1 + 3 * A / M)) := by
        rw [mul_div_assoc', mul_div_assoc', div_le_div_iff₀ hpos2 hpos3]
        have := mul_le_mul_of_nonneg_left key (sq_nonneg lam)
        linarith
      have h5 : (1 / 2) ^ 2 * (lam ^ 2 / (1 + 3 * A / M)) ≤ (1 / 2) ^ 2 * h ^ 2 :=
        mul_le_mul_of_nonneg_left hh2 (by norm_num)
      linarith
    exact le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) hT2
  have hQb := hbend hT
  -- `3h²/(16R) ≥ 3λ√(1 + 2A/3)/(16(1 + 3A/m))`
  have hsq3 : 0 < Real.sqrt (1 + 2 * A / 3) := Real.sqrt_pos.mpr hpos2
  have hRle : R ≤ lam / Real.sqrt (1 + 2 * A / 3) := hRhi
  have hstep1 : 3 * lam * Real.sqrt (1 + 2 * A / 3) / (16 * (1 + 3 * A / M)) ≤
      3 * h ^ 2 / (16 * R) := by
    have hinvR : Real.sqrt (1 + 2 * A / 3) / lam ≤ 1 / R := by
      rw [div_le_div_iff₀ hlam hR0]
      rw [le_div_iff₀ hsq3] at hRle
      linarith
    calc 3 * lam * Real.sqrt (1 + 2 * A / 3) / (16 * (1 + 3 * A / M)) =
          3 / 16 * (lam ^ 2 / (1 + 3 * A / M)) * (Real.sqrt (1 + 2 * A / 3) / lam) := by
            field_simp
      _ ≤ 3 / 16 * h ^ 2 * (1 / R) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hh2 (by norm_num)) hinvR
            (by positivity) (by positivity)
      _ = 3 * h ^ 2 / (16 * R) := by field_simp
  -- `√(1 + 2A/3) ≥ (4/5) ρ` and `1 + 3A/m ≤ 4 max{1, ρ²/m}`
  have hsqrt45 : 4 / 5 * ρ ≤ Real.sqrt (1 + 2 * A / 3) := by
    rw [Real.le_sqrt (by positivity) hpos2.le, mul_pow, hρ2]
    linarith
  have hfinal : Ξ / 128 ≤ 3 * lam * Real.sqrt (1 + 2 * A / 3) / (16 * (1 + 3 * A / M)) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have hX : 3 * lam * (4 / 5 * ρ) ≤ 3 * lam * Real.sqrt (1 + 2 * A / 3) :=
      mul_le_mul_of_nonneg_left hsqrt45 (by positivity)
    rcases le_total (1 + A) M with hcase | hcase
    · -- `1 + 3A/m ≤ 4`, use `Ξ ≤ λ ρ`
      have h4 : 1 + 3 * A / M ≤ 4 := by
        have : 3 * A / M ≤ 3 := by rw [div_le_iff₀ hM0]; linarith
        linarith
      have : Ξ * (16 * (1 + 3 * A / M)) ≤ lam * ρ * 64 :=
        mul_le_mul hΞ1 (by linarith) (by positivity) (by positivity)
      have hlr : 0 ≤ lam * ρ := by positivity
      linarith
    · -- `1 + 3A/m ≤ 4(1 + A)/m = 4ρ²/m`, use `Ξ ≤ λ M/ρ`
      have h4 : 1 + 3 * A / M ≤ 4 * ρ ^ 2 / M := by
        have e1 : 1 + 3 * A / M = (M + 3 * A) / M := by field_simp
        rw [hρ2, e1, div_le_div_iff_of_pos_right hM0]
        linarith
      have h5 : Ξ * (16 * (1 + 3 * A / M)) ≤ lam * (M / ρ) * (16 * (4 * ρ ^ 2 / M)) :=
        mul_le_mul hΞ2 (by linarith) (by positivity) (by positivity)
      have e : lam * (M / ρ) * (16 * (4 * ρ ^ 2 / M)) = lam * ρ * 64 := by
        field_simp
        ring
      have hlr : 0 ≤ lam * ρ := by positivity
      linarith
  linarith


/-- **The lower bound of `thm:finitecritical`, case analysis.** At `s = 1` (`λ = 1`, `A = D`),
write `ψ = min{√D, m/√D}`. From the range comparison, endpoint coupling, the derivative bound,
the bending bound and the balanced-input bound (as in `finitejoint_arith`), `ψ/100 ≤ Q`.

Paper: lower bound in the proof of `thm:finitecritical` (tanh_mean.tex). -/
theorem finitecritical_arith {D : ℕ} {M R h Q : ℝ} (hD : 1 ≤ D) (hM : 2 ≤ M)
    (hRlo : 1 / Real.sqrt (1 + D) ≤ R) (hRhi : R ≤ 1 / Real.sqrt (1 + 2 * D / 3))
    (hQR : R ≤ Q) (hh : 1 / Real.sqrt (1 + 3 * D / M) ≤ h)
    (hbend : 2 * R / h ≤ 1 / 2 → 3 * h ^ 2 / (16 * R) ≤ Q)
    (hbal : M < 100 → 1 / Real.sqrt (1 + 4 * D / M ^ 2) ≤ Q) :
    min (Real.sqrt D) (M / Real.sqrt D) / 100 ≤ Q := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  set σ := Real.sqrt (D : ℝ) with hσdef
  have hσ2 : σ ^ 2 = D := Real.sq_sqrt (by linarith)
  have hσ1 : 1 ≤ σ := by rw [hσdef]; exact Real.one_le_sqrt.mpr hD'
  have hσ0 : 0 < σ := by linarith
  have hM0 : 0 < M := by linarith
  set ψ := min σ (M / σ) with hψ
  have hψ1 : ψ ≤ σ := min_le_left _ _
  have hψ2 : ψ ≤ M / σ := min_le_right _ _
  have hψ0 : 0 ≤ ψ := le_min hσ0.le (by positivity)
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hRlo
  by_cases hD100 : D < 100
  · -- `Q ≥ R ≥ 1/10 ≥ ψ/100`
    have hD99 : (D : ℝ) ≤ 99 := by exact_mod_cast Nat.lt_succ_iff.mp hD100
    have hs : Real.sqrt (1 + D) ≤ 10 := by
      rw [Real.sqrt_le_left (by norm_num)]; linarith
    have hR10 : 1 / 10 ≤ R :=
      le_trans (one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity)) hs) hRlo
    have hσ10 : σ ≤ 10 := by rw [hσdef, Real.sqrt_le_left (by norm_num)]; linarith
    linarith
  push Not at hD100
  have hD100' : (100 : ℝ) ≤ D := by exact_mod_cast hD100
  by_cases hM100 : M < 100
  · have hQ := hbal hM100
    have hden : 0 < 1 + 4 * (D : ℝ) / M ^ 2 := by positivity
    by_cases hDM : (D : ℝ) ≤ M ^ 2
    · have h5 : Real.sqrt (1 + 4 * D / M ^ 2) ≤ 5 / 2 := by
        rw [Real.sqrt_le_left (by norm_num)]
        have : 4 * (D : ℝ) / M ^ 2 ≤ 4 := by rw [div_le_iff₀ (by positivity)]; linarith
        linarith
      have hQ' : 2 / 5 ≤ Q := by
        have := le_trans (one_div_le_one_div_of_le (Real.sqrt_pos.mpr hden) h5) hQ
        linarith
      have hsq : Real.sqrt M ≤ 10 := by rw [Real.sqrt_le_left (by norm_num)]; linarith
      have hψ3 : ψ ≤ 10 := (min_le_sqrt hσ0 hM0.le).trans hsq
      linarith
    · push Not at hDM
      have hle : 1 + 4 * (D : ℝ) / M ^ 2 ≤ 5 * D / M ^ 2 := by
        have h1 : 1 ≤ (D : ℝ) / M ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
        have : 5 * (D : ℝ) / M ^ 2 = D / M ^ 2 + 4 * D / M ^ 2 := by ring
        linarith
      have hsq : Real.sqrt (1 + 4 * D / M ^ 2) ≤ Real.sqrt 5 * σ / M := by
        calc Real.sqrt (1 + 4 * D / M ^ 2) ≤ Real.sqrt (5 * D / M ^ 2) := Real.sqrt_le_sqrt hle
          _ = Real.sqrt 5 * σ / M := by
              rw [Real.sqrt_div' _ (by positivity), Real.sqrt_mul (by norm_num),
                Real.sqrt_sq hM0.le]
      have hQ' : M / (Real.sqrt 5 * σ) ≤ Q := by
        have := le_trans (one_div_le_one_div_of_le (Real.sqrt_pos.mpr hden) hsq) hQ
        calc M / (Real.sqrt 5 * σ) = 1 / (Real.sqrt 5 * σ / M) := by field_simp
          _ ≤ Q := this
      have hs5 : Real.sqrt 5 ≤ 100 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have h5p : 0 < Real.sqrt 5 := by positivity
      have : M / σ / 100 ≤ M / (Real.sqrt 5 * σ) := by
        rw [div_div]
        apply div_le_div_of_nonneg_left hM0.le (by positivity)
        have := mul_le_mul_of_nonneg_right hs5 hσ0.le
        linarith
      have : ψ / 100 ≤ M / σ / 100 := by linarith
      linarith
  push Not at hM100
  have hpos3 : 0 < 1 + 3 * (D : ℝ) / M := by positivity
  have hpos2 : 0 < 1 + 2 * (D : ℝ) / 3 := by positivity
  have hh0 : 0 < h := lt_of_lt_of_le (by positivity) hh
  have hh2 : 1 / (1 + 3 * (D : ℝ) / M) ≤ h ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hh 2
    rwa [div_pow, one_pow, Real.sq_sqrt hpos3.le] at this
  have hR2 : R ^ 2 ≤ 1 / (1 + 2 * (D : ℝ) / 3) := by
    have := pow_le_pow_left₀ hR0.le hRhi 2
    rwa [div_pow, one_pow, Real.sq_sqrt hpos2.le] at this
  have hT : 2 * R / h ≤ 1 / 2 := by
    have hT2 : (2 * R / h) ^ 2 ≤ (1 / 2) ^ 2 := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      have key : 4 * (1 + 3 * (D : ℝ) / M) ≤ (1 / 4) * (1 + 2 * (D : ℝ) / 3) := by
        have h1 : 3 * (D : ℝ) / M ≤ 3 * D / 100 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hM100
        linarith
      have h3 : (2 * R) ^ 2 ≤ 4 * (1 / (1 + 2 * (D : ℝ) / 3)) := by nlinarith
      have h4 : 4 * (1 / (1 + 2 * (D : ℝ) / 3)) ≤ (1 / 2) ^ 2 * (1 / (1 + 3 * (D : ℝ) / M)) := by
        rw [mul_one_div, mul_one_div, div_le_div_iff₀ hpos2 hpos3]
        linarith
      have h5 : (1 / 2) ^ 2 * (1 / (1 + 3 * (D : ℝ) / M)) ≤ (1 / 2) ^ 2 * h ^ 2 :=
        mul_le_mul_of_nonneg_left hh2 (by norm_num)
      linarith
    exact le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) hT2
  have hQb := hbend hT
  have hsq3 : 0 < Real.sqrt (1 + 2 * (D : ℝ) / 3) := Real.sqrt_pos.mpr hpos2
  have hstep1 : 3 * Real.sqrt (1 + 2 * (D : ℝ) / 3) / (16 * (1 + 3 * (D : ℝ) / M)) ≤
      3 * h ^ 2 / (16 * R) := by
    have hinvR : Real.sqrt (1 + 2 * (D : ℝ) / 3) ≤ 1 / R := by
      rw [le_div_iff₀ hR0]
      have := hRhi
      rw [le_div_iff₀ hsq3] at this
      linarith
    calc 3 * Real.sqrt (1 + 2 * (D : ℝ) / 3) / (16 * (1 + 3 * (D : ℝ) / M)) =
          3 / 16 * (1 / (1 + 3 * (D : ℝ) / M)) * Real.sqrt (1 + 2 * (D : ℝ) / 3) := by
            field_simp
      _ ≤ 3 / 16 * h ^ 2 * (1 / R) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hh2 (by norm_num)) hinvR
            (by positivity) (by positivity)
      _ = 3 * h ^ 2 / (16 * R) := by field_simp
  have hsqrt45 : 4 / 5 * σ ≤ Real.sqrt (1 + 2 * (D : ℝ) / 3) := by
    rw [Real.le_sqrt (by positivity) hpos2.le, mul_pow, hσ2]
    linarith
  have hfinal : ψ / 100 ≤ 3 * Real.sqrt (1 + 2 * (D : ℝ) / 3) / (16 * (1 + 3 * (D : ℝ) / M)) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have hX : 3 * (4 / 5 * σ) ≤ 3 * Real.sqrt (1 + 2 * (D : ℝ) / 3) := by linarith
    rcases le_total (D : ℝ) M with hcase | hcase
    · have h4 : 1 + 3 * (D : ℝ) / M ≤ 4 := by
        have : 3 * (D : ℝ) / M ≤ 3 := by rw [div_le_iff₀ hM0]; linarith
        linarith
      have : ψ * (16 * (1 + 3 * (D : ℝ) / M)) ≤ σ * 64 :=
        mul_le_mul hψ1 (by linarith) (by positivity) (by positivity)
      linarith
    · have h4 : 1 + 3 * (D : ℝ) / M ≤ 4 * σ ^ 2 / M := by
        have e1 : 1 + 3 * (D : ℝ) / M = (M + 3 * D) / M := by field_simp
        rw [hσ2, e1, div_le_div_iff_of_pos_right hM0]
        linarith
      have h5 : ψ * (16 * (1 + 3 * (D : ℝ) / M)) ≤ M / σ * (16 * (4 * σ ^ 2 / M)) :=
        mul_le_mul hψ2 (by linarith) (by positivity) (by positivity)
      have e : M / σ * (16 * (4 * σ ^ 2 / M)) = σ * 64 := by field_simp; ring
      linarith
  linarith

/-- Values of the mean chain at the two constant inputs: `±F_{a,D}(1)`. Auxiliary for endpoint
coupling in the proofs of `thm:uniformchain` and `thm:finitejoint` (tanh_mean.tex). -/
lemma chainTarget_const (a : ℝ) (D : ℕ) (hm : 1 ≤ m) :
    chainTarget a D (fun _ : Fin m => true) = F a D 1 ∧
      chainTarget a D (fun _ : Fin m => false) = -F a D 1 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm' : (m : ℝ) ≠ 0 := by positivity
  constructor
  · unfold chainTarget signSum
    simp [hm']
  · unfold chainTarget signSum
    simp only [sgn_false, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_neg, mul_one]
    rw [neg_div, div_self hm', F_neg]

/-- The common hypotheses of the finite-input case analyses, proved for every exact sampler of
the mean chain. Auxiliary for `thm:finitejoint` and `thm:finitecritical` (tanh_mean.tex). -/
theorem finite_chain_inputs {ι : Type*} [Fintype ι] (S : Sampler m ι) (hN : S.NoRepeat)
    (hB : S.Bounded) {s : ℝ} (hs : 0 < s) (D : ℕ) (hm2 : 2 ≤ m) (heven : Even m)
    (hf : S.Exact (chainTarget s D)) :
    s ^ D / Real.sqrt (1 + chainA s D) ≤ F s D 1 ∧
      F s D 1 ≤ s ^ D / Real.sqrt (1 + 2 * chainA s D / 3) ∧
      F s D 1 ≤ Finset.univ.sup' Finset.univ_nonempty S.cost ∧
      s ^ D / Real.sqrt (1 + 3 * chainA s D / m) ≤
        deriv (meanProfile (chainTarget s D : (Fin m → Bool) → ℝ)) 0 ∧
      (2 * F s D 1 / deriv (meanProfile (chainTarget s D : (Fin m → Bool) → ℝ)) 0 ≤ 1 / 2 →
        3 * deriv (meanProfile (chainTarget s D : (Fin m → Bool) → ℝ)) 0 ^ 2 / (16 * F s D 1) ≤
          Finset.univ.sup' Finset.univ_nonempty S.cost) ∧
      s ^ D / Real.sqrt (1 + 4 * chainA s D / (m : ℝ) ^ 2) ≤
        Finset.univ.sup' Finset.univ_nonempty S.cost := by
  set Qm := Finset.univ.sup' Finset.univ_nonempty S.cost with hQmdef
  set R := F s D 1 with hRdef
  set h := deriv (meanProfile (chainTarget s D : (Fin m → Bool) → ℝ)) 0 with hhdef
  have hm1 : 1 ≤ m := by omega
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hQ : ∀ b x, b ≤ S.cost x → b ≤ Qm := fun b x hx =>
    hx.trans (Finset.le_sup' S.cost (Finset.mem_univ x))
  set A := chainA s D with hAdef
  have hA0 : 0 ≤ A := chainA_nonneg s D
  have hlam : 0 < s ^ D := by positivity
  obtain ⟨hRlo, hR2⟩ := chainrange hs D
  have hR0 : 0 < R := F_pos hs D one_pos
  have hpos2 : 0 < 1 + 2 * A / 3 := by positivity
  have hRhi : R ≤ s ^ D / Real.sqrt (1 + 2 * A / 3) := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hpos2)]
    have : (R * Real.sqrt (1 + 2 * A / 3)) ^ 2 ≤ (s ^ D) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hpos2.le]
      rwa [le_div_iff₀ hpos2] at hR2
    exact le_of_pow_le_pow_left₀ two_ne_zero hlam.le this
  -- endpoint coupling
  have hQR : R ≤ Qm := by
    have h1 := mean_diff_le_cost S hB (fun _ => true) (fun _ => false)
    rw [hf, hf, (chainTarget_const s D hm1).1, (chainTarget_const s D hm1).2] at h1
    rw [sub_neg_eq_add, ← two_mul, abs_of_pos (by positivity), mul_div_cancel_left₀ _
      two_ne_zero] at h1
    exact hQ _ _ h1
  -- derivative bound
  have hh : s ^ D / Real.sqrt (1 + 3 * A / m) ≤ h := by
    have hd := derivative_lower (m := m) hs hm1 D
    rw [pow_mul_HD hs] at hd
    refine le_trans ?_ hd
    apply div_le_div_of_nonneg_left hlam.le
    · apply Real.sqrt_pos.mpr
      have : 0 ≤ A / (m : ℝ) ^ 2 * (3 * m - 2) := mul_nonneg (by positivity) (by linarith)
      linarith
    · apply Real.sqrt_le_sqrt
      have : A / (m : ℝ) ^ 2 * (3 * m - 2) ≤ 3 * A / m := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
  refine ⟨hRlo, hRhi, hQR, hh, ?_, ?_⟩
  · -- bending and the second transcript bound
    intro hT
    have hpos3 : 0 < 1 + 3 * A / m := by positivity
    have hh0 : 0 < h := lt_of_lt_of_le (div_pos hlam (Real.sqrt_pos.mpr hpos3)) hh
    set T := 2 * R / h with hTdef
    have hT0 : 0 < T := by positivity
    have hend : meanProfile (chainTarget s D : (Fin m → Bool) → ℝ) T ≤ R :=
      meanProfile_chain_le hs.le hm1 D (by rw [abs_of_pos hT0]; linarith)
    have hders := meanProfile_hasDerivAt S hN hf
    obtain ⟨t, ht, hbend⟩ := bending (H := meanProfile (chainTarget s D : (Fin m → Bool) → ℝ))
      (H1 := deriv (meanProfile (chainTarget s D : (Fin m → Bool) → ℝ)))
      (H2 := deriv (deriv (meanProfile (chainTarget s D : (Fin m → Bool) → ℝ))))
      hT0 hR0 (fun t => (hders t).1) (fun t => (hders t).2) (meanProfile_chain_zero s D)
      hhdef.symm (by rw [hTdef]; field_simp) hend
    have ht1 : |t| < 1 := by rw [abs_of_nonneg ht.1]; linarith [ht.2]
    obtain ⟨-, -, h3⟩ := transcript S hN hB hf ht1
    obtain ⟨x, hx⟩ := exists_ge_prodExp (s := fun _ => t) (fun _ => ht1.le) S.cost
    have htt : t ^ 2 ≤ 1 / 4 := by nlinarith [ht.1, ht.2]
    have h34 : 3 / 8 ≤ (1 - t ^ 2) / 2 := by linarith
    have hcurv : 3 * h ^ 2 / (16 * R) ≤ expCost S t := by
      calc 3 * h ^ 2 / (16 * R) = 3 / 8 * (h ^ 2 / (2 * R)) := by field_simp; ring
        _ ≤ (1 - t ^ 2) / 2 * |deriv (deriv (meanProfile (chainTarget s D :
              (Fin m → Bool) → ℝ))) t| :=
            mul_le_mul h34 hbend (by positivity) (by linarith)
        _ ≤ expCost S t := h3
    exact hQ _ x (hcurv.trans hx)
  · -- balanced-input coupling
    obtain ⟨x, hx⟩ := exists_balanced heven
    exact hQ _ x (balanced_lower S hB hs hm1 D hf hx).2

/-- **Uniform finite-input complexity, lower bound.** For even `m ≥ 2`, `s > 0`, `λ = s^D` and
`A = ∑_{j=1}^D s^{2j}`, every exact sampler for the mean chain on `m` inputs has a context with
`E[Q | x] ≥ Ξ/128`, where `Ξ = λ min{√(1 + A), m/√(1 + A)}`.

Paper: lower bound of `thm:finitejoint`, `eq:finitejoint` (tanh_mean.tex). -/
theorem finitejoint_lower {ι : Type*} [Fintype ι] (S : Sampler m ι) (hN : S.NoRepeat)
    (hB : S.Bounded) {s : ℝ} (hs : 0 < s) (D : ℕ) (hm2 : 2 ≤ m) (heven : Even m)
    (hf : S.Exact (chainTarget s D)) :
    ∃ x, s ^ D * min (Real.sqrt (1 + chainA s D)) (m / Real.sqrt (1 + chainA s D)) / 128 ≤
      S.cost x := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := finite_chain_inputs S hN hB hs D hm2 heven hf
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have := finitejoint_arith (by positivity) (chainA_nonneg s D) hm' h1 h2 h3 h4 h5 fun _ => h6
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty S.cost
  exact ⟨x, hx ▸ this⟩

/-- **Finite critical mean chain, lower bound.** For even `m ≥ 2` and `D ≥ 1`, every exact
sampler for `F_{1,D}(m⁻¹ ∑ⱼ xⱼ)` has a context with `E[Q | x] ≥ min{√D, m/√D}/100`.

Paper: lower bound of `thm:finitecritical` (tanh_mean.tex). -/
theorem finitecritical_lower {ι : Type*} [Fintype ι] (S : Sampler m ι) (hN : S.NoRepeat)
    (hB : S.Bounded) {D : ℕ} (hD : 1 ≤ D) (hm2 : 2 ≤ m) (heven : Even m)
    (hf : S.Exact (chainTarget 1 D)) :
    ∃ x, min (Real.sqrt D) (m / Real.sqrt D) / 100 ≤ S.cost x := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := finite_chain_inputs S hN hB one_pos D hm2 heven hf
  have hA : chainA 1 D = D := by simp [chainA]
  simp only [one_pow, hA] at h1 h2 h4 h6
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have := finitecritical_arith hD hm' h1 h2 h3 h4 h5 fun _ => h6
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty S.cost
  exact ⟨x, hx ▸ this⟩


/-- **The first integer line for `G_r`.** For `r > 0`, `3 r coth r - 2 ≥ 1 + r² - r⁴/6`, so the
bound `E₀T ≥ 3 r coth r - 2` of `cor:new-integer-score` is `1 + r² + O(r⁴)` from below; it
uses `coth² r ≥ r^{-2} + 2/3`.

Paper: `cor:new-integer-score` (tanh_new_critical.tex). This is the arithmetic of the `G_r`
specialization only; that `E₀T ≥ 3 r coth r - 2` holds for factories of `G_r` needs
`lem:new-finite-score` (not formalized). -/
theorem three_r_coth_lower {r : ℝ} (hr : 0 < r) :
    1 + r ^ 2 - r ^ 4 / 6 ≤ 3 * (r / Real.tanh r) - 2 := by
  have ht := tanh_pos hr
  set c := r / Real.tanh r with hc
  have hc0 : 0 < c := div_pos hr ht
  have hc2 : 1 + 2 * r ^ 2 / 3 ≤ c ^ 2 := by
    have h := tanh_sq_le_two_thirds hr.le
    rw [hc, div_pow, le_div_iff₀ (by positivity)]
    linarith
  set q := 1 + r ^ 2 / 3 - r ^ 4 / 18 with hq
  have hqc : q ≤ c := by
    by_cases hq0 : q ≤ 0
    · linarith
    push Not at hq0
    have hy : r ^ 2 ≤ 12 := by
      by_contra hcon
      push Not at hcon
      have : q < 0 := by rw [hq]; nlinarith
      linarith
    have hq2 : q ^ 2 ≤ 1 + 2 * r ^ 2 / 3 := by
      have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
      have e : q ^ 2 = 1 + 2 * r ^ 2 / 3 - (r ^ 2) ^ 3 / 27 + (r ^ 2) ^ 4 / 324 := by
        rw [hq]; ring
      rw [e]
      have : (r ^ 2) ^ 4 / 324 ≤ (r ^ 2) ^ 3 / 27 := by
        have h3 : 0 ≤ (r ^ 2) ^ 3 := by positivity
        have : (r ^ 2) ^ 4 = (r ^ 2) ^ 3 * r ^ 2 := by ring
        rw [this]
        nlinarith
      linarith
    exact le_of_pow_le_pow_left₀ two_ne_zero hc0.le (hq2.trans hc2)
  rw [hq] at hqc
  linarith

end

end ExactSampling.TranscriptLowerBounds
