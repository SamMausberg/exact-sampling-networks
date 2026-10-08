import Mathlib

/-!
# The background schedule for routine precision

This file formalizes the background schedule in the proof of `lem:conf-replay`
(Section `sec:conf-replay` of `paper/conference.tex`; full version `lem:replayexactsampling`
in `paper/attention_moment_decoder.tex`).

Let `N` be the least power of two at least the prompt length `T0`. The routine evaluator is
built at precision `p_{2N}` during prefill and used alone until length `N`. At length `N` an
empty future evaluator at precision `p_{4N}` is started; each of the next `N` appends updates
the current evaluator once and replays two history tokens into the future evaluator. When the
future evaluator has replayed the whole history (at length `2N`) it becomes current, `N` is
doubled, and a new empty future evaluator is started.

The schedule is modeled as a state machine `step` on `State` (phase parameter `N`, history
length `len`, and number `done` of history tokens replayed into the future evaluator). We prove
the invariants of the paper: after `j ≤ N` appends in a phase the future evaluator has replayed
`2 j ≤ N + j` tokens, the two tokens replayed at each append exist, the future evaluator is
complete exactly at length `2N`, and the routine horizon `2N` satisfies `len ≤ 2N ≤ 4 len`.
The number of tokens replayed at an append (`replayed`) is read off the transition: off a
switch it is the growth of `done`, and at a switch it completes the history. It is `0` before
length `N` and `2` afterwards, so every append performs at most three token evaluations.

Not formalized here: the evaluators themselves and their costs (see `Replay.lean`, where the
precision growth `p_{4N} ≤ p_{2N} + 3` is `pR_two_mul_le`).
-/

namespace ExactSampling.ReplaySchedule

/-- The least power of two at least the prompt length `T0`.
Paper: proof of `lem:conf-replay` (conference.tex), "Let N be the least power of two at least T_0";
`lem:replayexactsampling` (attention_moment_decoder.tex). -/
def firstHorizon (T0 : ℕ) : ℕ := 2 ^ Nat.clog 2 T0

/-- `T0 ≤ N`; hence the prefill horizon `2N` is at least `2 T0`.
Paper: proof of `lem:replayexactsampling` (attention_moment_decoder.tex), "This horizon is at least
2T_0". -/
lemma le_firstHorizon (T0 : ℕ) : T0 ≤ firstHorizon T0 := Nat.le_pow_clog (by norm_num) T0

/-- The least power of two at least `T0 ≥ 1` is less than `2 T0`. Auxiliary for `horizons_fit`,
supporting the proof of `lem:conf-replay` (conference.tex). -/
lemma firstHorizon_lt (T0 : ℕ) (hT0 : 1 ≤ T0) : firstHorizon T0 < 2 * T0 := by
  unfold firstHorizon
  rcases Nat.lt_or_ge 1 T0 with h | h
  · have hpos : 0 < Nat.clog 2 T0 := Nat.clog_pos (by norm_num) h
    have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    rw [Nat.pred_eq_sub_one] at hlt
    have : 2 ^ Nat.clog 2 T0 = 2 * 2 ^ (Nat.clog 2 T0 - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  · have : T0 = 1 := by omega
    subst this
    simp

/-- `firstHorizon T0` is below every power of two that is at least `T0`.
Paper: proof of `lem:conf-replay` (conference.tex), "the least power of two". -/
lemma firstHorizon_least (T0 e : ℕ) (h : T0 ≤ 2 ^ e) : firstHorizon T0 ≤ 2 ^ e :=
  Nat.pow_le_pow_right (by norm_num) (Nat.clog_le_of_le_pow h)

/-- State of the background schedule: phase parameter `N` (routine horizon `2N`, future horizon
`4N`), length `len` of the true history, and number `done` of history tokens replayed into the
future evaluator.
Paper: proof of `lem:conf-replay` (conference.tex); `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
structure State where
  /-- Phase parameter: routine horizon `2N`, future horizon `4N`. -/
  N : ℕ
  /-- Length of the true history. -/
  len : ℕ
  /-- History tokens replayed into the future evaluator. -/
  done : ℕ
deriving DecidableEq

/-- State after prefill: `N` is the least power of two at least `T0`, the history has length `T0`,
and no future evaluator has started.
Paper: proof of `lem:conf-replay` (conference.tex), "During prefill build the routine evaluator at
p_2N". -/
def init (T0 : ℕ) : State := ⟨firstHorizon T0, T0, 0⟩

/-- One append. Before length `N` only the current evaluator is updated. From length `N` on, the
current evaluator is updated and two history tokens are replayed into the future evaluator. Once the
future evaluator has replayed the whole history, it becomes current, `N` is doubled, and a new empty
future evaluator starts.
Paper: proof of `lem:conf-replay` (conference.tex), the schedule paragraph;
`lem:replayexactsampling` (attention_moment_decoder.tex). -/
def step (s : State) : State :=
  if s.len < s.N then ⟨s.N, s.len + 1, s.done⟩
  else if s.done + 2 = s.len + 1 then ⟨2 * s.N, s.len + 1, 0⟩
  else ⟨s.N, s.len + 1, s.done + 2⟩

/-- Invariant of the reachable states.
Paper: proof of `lem:conf-replay` (conference.tex); `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
structure Inv (T0 : ℕ) (s : State) : Prop where
  /-- `N` is a power of two. -/
  pow_two : ∃ e, s.N = 2 ^ e
  /-- `N` is at least the prompt length. -/
  T0_le_N : T0 ≤ s.N
  /-- The history contains the prompt. -/
  T0_le_len : T0 ≤ s.len
  /-- `N ≤ 2 len`, so the routine horizon `2N` is at most `4 len`. -/
  N_le_two_len : s.N ≤ 2 * s.len
  /-- Before length `N` no future evaluator is running. -/
  before : s.len < s.N → s.done = 0
  /-- In a phase, after `j = len - N` appends the future evaluator has replayed `2 j` tokens. -/
  phase : s.N ≤ s.len → s.len < 2 * s.N ∧ s.done = 2 * (s.len - s.N)

/-- The invariant holds after prefill. Auxiliary for the proof of `lem:conf-replay`
(conference.tex). -/
theorem inv_init (T0 : ℕ) (hT0 : 1 ≤ T0) : Inv T0 (init T0) where
  pow_two := ⟨_, rfl⟩
  T0_le_N := le_firstHorizon T0
  T0_le_len := le_rfl
  N_le_two_len := (firstHorizon_lt T0 hT0).le
  before := fun _ => rfl
  phase := fun h => by
    have := le_firstHorizon T0
    have h1 : (init T0).len = T0 := rfl
    have h2 : (init T0).N = firstHorizon T0 := rfl
    have h3 : (init T0).done = 0 := rfl
    have := firstHorizon_lt T0 hT0
    omega

/-- The invariant is preserved by every append. Auxiliary for the proof of `lem:conf-replay`
(conference.tex). -/
theorem inv_step {T0 : ℕ} {s : State} (h : Inv T0 s) : Inv T0 (step s) := by
  obtain ⟨⟨e, he⟩, h1, h2, h3, h4, h5⟩ := h
  unfold step
  split_ifs with hlt hsw
  · exact ⟨⟨e, he⟩, h1, by simp; omega, by simp; omega, fun _ => h4 hlt,
      fun h' => by simp at h' ⊢; omega⟩
  · have hph := h5 (not_lt.mp hlt)
    refine ⟨⟨e + 1, by simp [he, pow_succ, mul_comm]⟩, by simp; omega, by simp; omega,
      by simp; omega, fun _ => rfl, fun h' => by simp at h' ⊢; omega⟩
  · have hph := h5 (not_lt.mp hlt)
    refine ⟨⟨e, he⟩, h1, by simp; omega, by simp; omega, fun h' => by simp at h'; omega,
      fun h' => by simp at h' ⊢; omega⟩

/-- Every state reached after prefill and any number of appends satisfies the invariant.
Paper: proof of `lem:conf-replay` (conference.tex), the schedule paragraph;
`lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem inv_iterate {T0 : ℕ} (hT0 : 1 ≤ T0) (m : ℕ) : Inv T0 (step^[m] (init T0)) := by
  induction m with
  | zero => exact inv_init T0 hT0
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact inv_step ih

/-- Each append increases the history length by one. Auxiliary for the proof of `lem:conf-replay`
(conference.tex). -/
theorem len_step (s : State) : (step s).len = s.len + 1 := by
  unfold step; split_ifs <;> rfl

/-- After `m` appends the history has length `T0 + m`.
Paper: proof of `lem:conf-replay` (conference.tex). -/
theorem len_iterate (T0 m : ℕ) : (step^[m] (init T0)).len = T0 + m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', len_step, ih]
    omega

/-- History tokens replayed into the future evaluator during the append from `s`, read off the
transition `step`. Off a switch it is the growth of `done`; at a switch (the future evaluator
completes and becomes current) it is the number of tokens still needed to cover the history
after the append, `(step s).len - done`.
Paper: proof of `lem:conf-replay` (conference.tex), "replay two historical tokens into the
future evaluator". -/
def replayed (s : State) : ℕ :=
  if ¬ s.len < s.N ∧ s.done + 2 = s.len + 1 then (step s).len - s.done
  else (step s).done - s.done

/-- Off a switch, the future evaluator advances by exactly the replayed tokens.
Paper: proof of `lem:conf-replay` (conference.tex). -/
theorem step_done_of_not_switch (s : State) (h : ¬ (¬ s.len < s.N ∧ s.done + 2 = s.len + 1)) :
    (step s).done = s.done + replayed s := by
  unfold replayed
  split_ifs
  unfold step
  split_ifs <;> dsimp only <;> omega

/-- At a switch, the replayed tokens complete the future evaluator's pass over the whole
history after the append; it becomes current, `N` doubles, and the next future evaluator is
empty.
Paper: proof of `lem:conf-replay` (conference.tex), "At length 2N it is current. Switch, double
N, and start the next future evaluator". -/
theorem step_of_switch (s : State) (h : ¬ s.len < s.N ∧ s.done + 2 = s.len + 1) :
    s.done + replayed s = (step s).len ∧ (step s).N = 2 * s.N ∧ (step s).done = 0 := by
  have hstep : step s = ⟨2 * s.N, s.len + 1, 0⟩ := by
    unfold step
    split_ifs with h1 h2
    · exact absurd h1 h.1
    · rfl
    · exact absurd h.2 h2
  have hrep : replayed s = (step s).len - s.done := by
    unfold replayed
    split_ifs
    rfl
  rw [hrep, hstep]
  dsimp only
  refine ⟨?_, rfl, rfl⟩
  omega

/-- Before length `N` no token is replayed; from length `N` on, exactly two history tokens are
replayed at every append.
Paper: proof of `lem:conf-replay` (conference.tex), "After each of the next N appends, update the
current evaluator once and replay two historical tokens into the future evaluator". -/
theorem replayed_eq (s : State) : replayed s = if s.len < s.N then 0 else 2 := by
  unfold replayed step
  split_ifs <;> dsimp only <;> omega

/-- At most two history tokens are replayed per append.
Paper: proof of `lem:conf-replay` (conference.tex). -/
theorem replayed_le_two (s : State) : replayed s ≤ 2 := by
  rw [replayed_eq]
  split_ifs <;> omega

/-- Deterministic token evaluations performed by the append from `s`: one update of the current
evaluator plus the history tokens replayed into the future evaluator.
Paper: proof of `lem:conf-replay` (conference.tex). -/
def evals (s : State) : ℕ := 1 + replayed s

/-- Every append performs at most three deterministic token evaluations.
Paper: proof of `lem:conf-replay` (conference.tex), "Thus every append performs at most three
deterministic token evaluations"; `lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem evals_le_three (s : State) : evals s ≤ 3 := by
  have := replayed_le_two s
  unfold evals
  omega

/-- The two history tokens replayed at each append exist: `done + 2 ≤ len + 1`, where `len + 1` is
the history length after the append.
Paper: proof of `lem:replayexactsampling` (attention_moment_decoder.tex), "Since 2j ≤ N+j for j ≤ N,
the next replay tokens always exist". -/
theorem replay_tokens_available {T0 : ℕ} {s : State} (h : Inv T0 s) (hN : s.N ≤ s.len) :
    s.done + 2 ≤ s.len + 1 := by
  have := h.phase hN
  omega

/-- The future evaluator completes (has replayed the entire history) exactly when the history
reaches length `2N`.
Paper: proof of `lem:conf-replay` (conference.tex), "At length 2N it is current";
`lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem switch_iff {T0 : ℕ} {s : State} (h : Inv T0 s) (hN : s.N ≤ s.len) :
    s.done + 2 = s.len + 1 ↔ s.len + 1 = 2 * s.N := by
  have := h.phase hN
  omega

/-- The current routine horizon `2N` covers the history length, so the prefactor bound (`T ≤ R`)
applies at every sampling step.
Paper: proof of `lem:conf-replay` (conference.tex), "For T ≤ R". -/
theorem len_le_horizon {T0 : ℕ} {s : State} (h : Inv T0 s) : s.len ≤ 2 * s.N := by
  by_cases hN : s.N ≤ s.len
  · have := h.phase hN
    omega
  · omega

/-- Within a phase: after `j < N` appends from length `N`, the history has length `N + j` and the
future evaluator has replayed `2 j` tokens.
Paper: proof of `lem:conf-replay` (conference.tex), "After j appends, the true history has length
N+j and the future evaluator has processed 2j ≤ N+j tokens"; `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
theorem phase_iterate (N j : ℕ) (hj : j < N) :
    step^[j] ⟨N, N, 0⟩ = ⟨N, N + j, 2 * j⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    unfold step
    dsimp only
    split_ifs with h1 h2
    · exact absurd h1 (by omega)
    · exact absurd h2 (by omega)
    · congr 1

/-- After `N` appends from length `N`, the future evaluator has become current, `N` has been
doubled, and the next future evaluator is empty.
Paper: proof of `lem:conf-replay` (conference.tex), "At length 2N it is current. Switch, double N,
and start the next future evaluator"; `lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem phase_complete (N : ℕ) (hN : 1 ≤ N) :
    step^[N] ⟨N, N, 0⟩ = ⟨2 * N, 2 * N, 0⟩ := by
  obtain ⟨j, rfl⟩ : ∃ j, N = j + 1 := ⟨N - 1, by omega⟩
  rw [Function.iterate_succ_apply', phase_iterate (j + 1) j (by omega)]
  unfold step
  dsimp only
  split_ifs with h1 h2
  · exact absurd h1 (by omega)
  · congr 1
    omega
  · exact absurd h2 (by omega)

/-- `2 j ≤ N + j` for `j ≤ N`.
Paper: proof of `lem:conf-replay` (conference.tex), "2j ≤ N+j"; `lem:replayexactsampling`
(attention_moment_decoder.tex). -/
theorem phase_done_le (N j : ℕ) (hj : j ≤ N) : 2 * j ≤ N + j := by omega

/-- The future evaluator never runs ahead of the true history.
Paper: proof of `lem:conf-replay` (conference.tex), "2j ≤ N+j". -/
theorem done_le_len {T0 : ℕ} {s : State} (h : Inv T0 s) : s.done ≤ s.len := by
  by_cases hN : s.N ≤ s.len
  · have := h.phase hN
    omega
  · have := h.before (by omega)
    omega

/-- At the switch the future evaluator has replayed the entire history and becomes current: the next
state has doubled `N`, length `2N`, and an empty future evaluator.
Paper: proof of `lem:conf-replay` (conference.tex), "At length 2N it is current. Switch, double N";
`lem:replayexactsampling` (attention_moment_decoder.tex). -/
theorem step_switch {T0 : ℕ} {s : State} (h : Inv T0 s) (hN : s.N ≤ s.len)
    (hlen : s.len + 1 = 2 * s.N) :
    s.done + 2 = s.len + 1 ∧ step s = ⟨2 * s.N, 2 * s.N, 0⟩ := by
  have hd : s.done + 2 = s.len + 1 := (switch_iff h hN).mpr hlen
  refine ⟨hd, ?_⟩
  unfold step
  split_ifs with h1
  · omega
  · rw [hlen]

/-- Horizons fit the context length: the routine horizon `R = 2N` and the future horizon `R' = 4N`
satisfy `len ≤ R ≤ 8 len` and `R' ≤ 8 len`, the hypotheses of the per-token bound
`expected_token_work_le` in `Replay.lean`.
Paper: proof of `lem:conf-replay` (conference.tex), "For T ≤ R" and "p_R = O(S)". -/
theorem horizons_fit {T0 : ℕ} {s : State} (h : Inv T0 s) :
    s.len ≤ 2 * s.N ∧ 2 * s.N ≤ 8 * s.len ∧ 4 * s.N ≤ 8 * s.len := by
  have h1 := len_le_horizon h
  have h2 := h.N_le_two_len
  omega

end ExactSampling.ReplaySchedule
