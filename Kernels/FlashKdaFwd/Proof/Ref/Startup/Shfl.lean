-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Trace
public import Kernels.FlashKdaFwd.Proof.Thread.Never
public import Kernels.FlashKdaFwd.Proof.Ref.Kinds.Count
public import Lemmas.Flow.WarpScan

@[expose] public section

/-! # The shuffles of the startup phase return the warp index; the invariant without hypothesis

The invariant of the startup phase states the role of a thread, and the role is decided by what
the thread's three shuffles returned (instructions 48, 55 and 87: `shfl.sync.idx` of the warp
index from lane 0). `Trace.lean` takes this as a hypothesis (`ShflWarp X g`, or `ShflBefore X g
n` for the events before position `n`): a shuffle of thread `g` returned a value whose word is
the thread's warp index. This file proves it for the first three shuffles of every thread
(`shfl_first`), which is all the invariant needs, and so states the invariant with no
returned-value hypothesis and no premise left to the later phases:

    theorem startup_inv (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
        (hg : g < L.threads) (hk : k < (X.tr g).length)
        (hσ : Frame.stateAt (code L) X g k = some (some s)) : Inv P X g k s ∨ Left P L X g k

(The lemmas of this file take the soundness of the machine as the hypothesis `hC`, like
`Trace.lean`; `startup_inv` discharges it with `Thread.sound`, in the form `Ref.sounds`.)

**Proof of `shfl_first`**, by induction on the ordinal `n < 3` of a shuffle among the shuffles
of its thread (Core's `Execution.ShflK`), for all threads at once. Take the `n`-th shuffle of
thread `g`, at trace position `k`.

1. The shuffles of `g` before `k` have smaller ordinals, so the invariant holds up to `k`
   (`startup_inv_upto`) and the machine has followed the thread up to `k` (`followed_upto`: the
   machine's only give-up is at a load of the offsets array, excluded inside the phase by
   `startup_followed`). The thread has not left the phase: a thread that has left it has made
   three shuffles (the ledger of the exit, `Left.shfls`), and this one has made `n < 3`.
2. So the state before the shuffle is at a shuffle position (`shfl_shape`): the event is
   `shfl.sync.idx` of the word of the thread's warp index with lane operand 0 and clamp 31.
3. Core's rule for shuffles (`Consistent.shfl`) says the value received is the operand of the
   `n`-th shuffle of the source lane, which for these operands is lane 0 of the same warp
   (`shflSource_idx`), or that the source lane exited before its `n`-th shuffle. In the first
   case step 2 for the source thread gives the operand: the word of the warp index. The second
   case is impossible (`exit_shfls`): a thread that exits with fewer than three shuffles would
   be inside the phase at its exit, and no position of the phase fires an exit.

**Proof of `startup_inv`.** If at most three shuffles precede position `k`, every shuffle
before `k` is one of the first three and `startup_inv_upto` applies. Otherwise take the fourth
shuffle, at a position `m < k`: the invariant up to `m` says the thread is at a shuffle position
with three shuffles before it, which no position has, or has left the phase at or before `m`.

**What the later phases owe** is needed only for tracking (`Startup/Tracked.lean`), not here:
`Later P L X` says that a followed state of a thread that has left the startup phase (`Left`)
is at no site of the startup phase. Each later phase's invariant says at which sites its states
are, so the assembly discharges `Later` by a comparison of sites. `Later.notLoad`: such a state
is at none of the 21 loads of the offsets array (the machine's only give-up). With the fact
of `Ref/Kinds/Event.lean` "an event of kind shuffle is fired only at a shuffle site"
(`shfl_sites`), `Later.noShfl`: a thread that has left the phase makes no shuffle, and so
*every* shuffle returns the warp index (`Tracked.lean: shflWarp`; no theorem of the phase needs
this complete form). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### After the phase -/

/-- The thread left the startup phase at or before its event `k`: the exit condition `Out` held
at an earlier position. -/
def Left (P : Params) (L : Launch) (X : Execution) (g k : Nat) : Prop :=
  ∃ j ≤ k, ∃ s0, Frame.stateAt (code L) X g j = some (some s0) ∧ Out P X g j s0

/-- **What the startup phase needs from the later phases** (for tracking only): a followed
state of a launched thread that has left the startup phase is at no site of the startup
phase. -/
def Later (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ g k s, g < L.threads → Left P L X g k → Frame.stateAt (code L) X g k = some (some s) →
    ∀ pos : Pos, s.site ≠ pos.site

/-- The thread left the startup phase at or before its event `k`, with the count of its warp
collectives at the exit (`OutE`). -/
def LeftE (P : Params) (L : Launch) (X : Execution) (g k : Nat) : Prop :=
  ∃ j ≤ k, ∃ s0, Frame.stateAt (code L) X g j = some (some s0) ∧ OutE P X g j s0

theorem LeftE.left {k : Nat} (h : LeftE P L X g k) : Left P L X g k :=
  let ⟨j, hj, s0, h1, h2⟩ := h
  ⟨j, hj, s0, h1, h2.1⟩

theorem Left.mono {j k : Nat} (h : Left P L X g j) (hjk : j ≤ k) : Left P L X g k :=
  let ⟨i, hi, s0, h1, h2⟩ := h
  ⟨i, by omega, s0, h1, h2⟩

/-- A thread that has left the phase has made its three shuffles. -/
theorem Left.shfls {k : Nat} (h : Left P L X g k) :
    3 ≤ ((X.tr g).take k).countP Execution.isShfl := by
  obtain ⟨j, hj, s0, -, -, hl⟩ := h
  have h3 : ((X.tr g).take j).countP Execution.isShfl = 3 := congrArg Led.shfls hl
  have := countP_take_mono Execution.isShfl (X.tr g) hj
  omega

/-- A thread that has left the phase has polled successfully. -/
theorem Left.polls {k : Nat} (h : Left P L X g k) : 1 ≤ ((X.tr g).take k).countP isOkPoll := by
  obtain ⟨j, hj, s0, -, -, hl⟩ := h
  have h1 : ((X.tr g).take j).countP isOkPoll = 1 := congrArg Led.polls hl
  have := countP_take_mono isOkPoll (X.tr g) hj
  omega

/-- No position of the phase has a successful poll before it. -/
theorem led_polls (g : Nat) (pos : Pos) : (led g pos).polls = 0 := by
  cases pos <;> simp only [led] <;> repeat' split
  all_goals rfl

/-- At most three shuffles precede a position. -/
theorem led_shfls_le (g : Nat) (pos : Pos) : (led g pos).shfls ≤ 3 := by
  cases pos <;> simp only [led] <;> repeat' split
  all_goals (first | exact Nat.le_refl 3 | (simp only; omega))

/-- Exactly `j` shuffles precede the `j`-th shuffle position. -/
theorem led_shfl (g : Nat) (j : Fin 3) : (led g (.shfl j)).shfls = j.val := by
  fin_cases j <;> rfl

/-- **A thread inside the phase has not left it.** -/
theorem Inv.not_left {k : Nat} {s : D} (h : Inv P X g k s) : ¬ Left P L X g k := by
  obtain ⟨pos, -, hl⟩ := h
  intro hleft
  have h1 := Left.polls hleft
  have h0 : ((X.tr g).take k).countP isOkPoll = (led g pos).polls := congrArg Led.polls hl
  rw [led_polls] at h0
  omega

/-- The indices of the 21 loads of the offsets array. -/
theorem offsetLoads_lt {j : Nat} (h : offsetLoads.contains j = true) : j < 21 := by
  simp only [offsetLoads, List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false,
    decide_eq_true_eq] at h
  omega

/-- **After the phase a state is at none of the 21 loads of the offsets array** (the
machine's only give-up). -/
theorem Later.notLoad (h : Later P L X) (g k : Nat) (s : D) (j : Fin 178)
    (hg : g < L.threads) (hl : Left P L X g k)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hs : s.site = .load j) :
    offsetLoads.contains j.val = false := by
  by_contra hc
  have hj := offsetLoads_lt (by simpa using hc)
  exact h g k s hg hl hσ (.load ⟨j.val, hj⟩) (by rw [hs]; rfl)

/-- **After the phase a thread makes no shuffle**: a shuffle event is fired only at one of the
three shuffle sites (`Ref/Kinds/Event.lean: shfl_sites`), which are sites of the phase. -/
theorem Later.noShfl (h : Later P L X) (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) {k pc b c : Nat}
    {md : ShflMode} {a v : Value} {ok : Bool} {s : D} (hg : g < L.threads)
    (hl : Left P L X g k) (hσ : Frame.stateAt (code L) X g k = some (some s))
    (he : X.get (g, k) = some ⟨pc, .shfl md a b c v ok⟩) : False := by
  obtain ⟨j, hj⟩ := shfl_sites hpre hX g k s pc md a b c v ok hg hσ he
  exact h g k s hg hl hσ (.shfl j) hj

/-- The warp of lane 0 of a thread's warp is the thread's. -/
theorem warp_lane0 (g : Nat) : warp (g - lane g) = warp g := by
  unfold warp lane
  omega

section
variable (hpre : Pre P L mem0) (hC : ∀ g < L.threads, (code L g).Sound)
  (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hC hX

/-! ### The machine follows a thread through its first three shuffles -/

/-- **Prefix tracking**: when the shuffles of thread `g` before `n` returned the warp index and
fewer than three shuffles precede `n`, the machine has not given up at any position up to
`n`. -/
theorem followed_upto (hg : g < L.threads) {n : Nat} (hS : ShflBefore X g n)
    (h3 : ((X.tr g).take n).countP Execution.isShfl < 3) :
    ∀ k, k ≤ n → k ≤ (X.tr g).length → Frame.stateAt (code L) X g k ≠ some none := by
  intro k
  induction k with
  | zero => intro _ _; rw [Frame.stateAt_zero]; simp
  | succ k ih =>
    intro hkn hk
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [Frame.stateAt_succ he]
    cases hs : Frame.stateAt (code L) X g k with
    | none => intro h; cases h
    | some σ =>
      cases σ with
      | none => exact absurd hs (ih (by omega) (by omega))
      | some d =>
        simp only [Option.bind_some]
        intro hn
        obtain ⟨j, hsite, hj, a, bs, v, hkind, -, -⟩ := next_giveUp L g d e hn
        rcases startup_inv_upto hpre hC hX hg hS (by omega) (by omega) hs with hI | hleft
        · exact startup_followed hpre hC hX hg he hs hI (retEv_upto hpre hX hS (by omega) he) hn
        · have h1 := Left.shfls hleft
          have h2 := countP_take_mono Execution.isShfl (X.tr g) (show k ≤ n by omega)
          omega

/-- **The state before one of the first events of a thread**: an event that is not undefined
behaviour, with fewer than three shuffles before it, all of which returned the warp index, is
fired at a state of the startup phase. -/
theorem inv_upto (hg : g < L.threads) {k : Nat} {e : Event} (hS : ShflBefore X g k)
    (h3 : ((X.tr g).take k).countP Execution.isShfl < 3) (he : X.get (g, k) = some e)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) :
    ∃ s, Frame.stateAt (code L) X g k = some (some s) ∧ Inv P X g k s := by
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨s, hσ⟩ : ∃ s, Frame.stateAt (code L) X g k = some (some s) := by
    rcases Frame.fired hC hX he with ⟨σ, o, hσ, -⟩ | ⟨-, pc, f, rfl⟩
    · cases σ with
      | none => exact absurd hσ (followed_upto hpre hC hX hg hS h3 k le_rfl (by omega))
      | some d => exact ⟨d, hσ⟩
    · exact absurd rfl (hub pc f)
  rcases startup_inv_upto hpre hC hX hg hS le_rfl hk hσ with hI | hleft
  · exact ⟨s, hσ, hI⟩
  · have := Left.shfls hleft
    omega

/-- **The shape of one of the first three shuffles**, when the shuffles before it are known:
`shfl.sync.idx` of the word of the thread's warp index from lane 0. -/
theorem shfl_shape (hg : g < L.threads) {k pc b c : Nat} {md : ShflMode} {a v : Value}
    {ok : Bool} (hS : ShflBefore X g k)
    (h3 : ((X.tr g).take k).countP Execution.isShfl < 3)
    (he : X.get (g, k) = some ⟨pc, .shfl md a b c v ok⟩) :
    md = .idx ∧ a = .bits 32 (W (warp g)) ∧ b = 0 ∧ c = 31 := by
  obtain ⟨s, hσ, pos, hr, hl⟩ := inv_upto hpre hC hX hg hS h3 he (fun _ _ h => by cases h)
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site hC hX he hσ
  have hev := ev_full hpre hg pos hr hat hc hf
  rcases pos with j | j | j | j | j | j | _ | j | _ <;>
    simp only [Ev, Event.mk.injEq, reduceCtorEq, and_false, exists_false, exists_const,
      false_and] at hev
  obtain ⟨v', ok', -, hkd⟩ := hev
  cases hkd
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **A thread that exits has made three shuffles**, when the shuffles before the exit are
known: no position of the startup phase fires an exit. -/
theorem exit_shfls (hg : g < L.threads) {k pc : Nat} (hS : ShflBefore X g k)
    (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    3 ≤ ((X.tr g).take k).countP Execution.isShfl := by
  by_contra h3
  obtain ⟨s, hσ, pos, hr, hl⟩ :=
    inv_upto hpre hC hX hg hS (by omega) he (fun _ _ h => by cases h)
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site hC hX he hσ
  have hev := ev_full hpre hg pos hr hat hc hf
  rcases pos with j | j | j | j | j | j | _ | j | _ <;>
    simp only [Ev, Event.mk.injEq, reduceCtorEq, and_false, exists_false, exists_const,
      false_and] at hev

/-! ### The induction on the ordinal of a shuffle -/

/-- **The `n`-th shuffle of every launched thread returned the thread's warp index**, for
`n < 3`. -/
theorem shflWarp_ord (n : Nat) (hn3 : n < 3) :
    ∀ g < L.threads, ∀ {k pc b c : Nat} {md : ShflMode} {a v : Value} {ok : Bool},
      X.get (g, k) = some ⟨pc, .shfl md a b c v ok⟩ →
      ((X.tr g).take k).countP Execution.isShfl = n → wordOf v = some (warp g) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    -- the shuffles of a thread before a position with at most `n` shuffles are known
    have before : ∀ h < L.threads, ∀ k,
        ((X.tr h).take k).countP Execution.isShfl ≤ n → ShflBefore X h k := by
      intro h hh k hle k' pc b c md a v ok hk' he'
      have h1 := count_snoc Execution.isShfl he'
      have h2 := countP_take_mono Execution.isShfl (X.tr h) (show k' + 1 ≤ k by omega)
      simp only [Execution.isShfl, ↓reduceIte] at h1
      exact ih _ (by omega) (by omega) h hh he' rfl
    intro g hg k pc b c md a v ok he hn
    have hSg : ShflBefore X g k := before g hg k (by omega)
    obtain ⟨rfl, rfl, rfl, rfl⟩ := shfl_shape hpre hC hX hg hSg (by omega) he
    have hsrc : g - laneOf L g + (shflSource .idx (laneOf L g) 0 31).1 = g - lane g := by
      rw [shflSource_idx _ (by decide), laneOf_eq hpre]
      exact Nat.add_zero _
    obtain ⟨-, ⟨j, pc', b', c', r', o', hj, hv⟩ | hexit⟩ :=
      hX.shfl g k n pc .idx _ 0 31 v ok he ⟨⟨_, _, _, _, _, _, _, he⟩, hn⟩
    · rw [hsrc] at hj hv
      have hlt : g - lane g < L.threads := by omega
      have hSs : ShflBefore X (g - lane g) j := before _ hlt j (by rw [hj.2])
      obtain ⟨-, rfl, -⟩ := shfl_shape hpre hC hX hlt hSs (by rw [hj.2]; exact hn3) hv
      rw [warp_lane0, wordOf_bits]
      have := warp_lt g
      simp only [W, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]
    · rw [hsrc] at hexit
      obtain ⟨k', pc', hex, hle⟩ := hexit
      have hlt : g - lane g < L.threads := by omega
      have hSx : ShflBefore X (g - lane g) k' := before _ hlt k' hle
      have := exit_shfls hpre hC hX hlt hSx hex
      omega

/-- **The first three shuffles of every launched thread returned its warp index**: the
shuffles before a position that at most three shuffles precede. -/
theorem shfl_first (hg : g < L.threads) {k : Nat}
    (h : ((X.tr g).take k).countP Execution.isShfl ≤ 3) : ShflBefore X g k := by
  intro k' pc b c md a v ok hk' he'
  have h1 := count_snoc Execution.isShfl he'
  have h2 := countP_take_mono Execution.isShfl (X.tr g) (show k' + 1 ≤ k by omega)
  simp only [Execution.isShfl, ↓reduceIte] at h1
  exact shflWarp_ord hpre hC hX _ (by omega) g hg he' rfl

/-- The invariant of the startup phase, with the soundness of the machine as a hypothesis. -/
theorem startup_inv_sound (hg : g < L.threads) {k : Nat} {s : D} (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) : Inv P X g k s ∨ Left P L X g k := by
  by_cases h3 : ((X.tr g).take k).countP Execution.isShfl ≤ 3
  · exact startup_inv_upto hpre hC hX hg (shfl_first hpre hC hX hg h3) le_rfl hk hσ
  · -- the fourth shuffle, at `m < k`: the thread has left the phase before it
    obtain ⟨m, hm, e, he, hsh, hcnt⟩ :=
      exists_nth Execution.isShfl (X.tr g) (n := 3) (k := k) (by omega)
    obtain ⟨sm, hσm⟩ := followed_of_le hσ (show m ≤ k by omega)
    have hSm : ShflBefore X g m := shfl_first hpre hC hX hg (by omega)
    rcases startup_inv_upto hpre hC hX hg hSm le_rfl (by omega) hσm with ⟨pos, hr, hl⟩ | hleft
    · exfalso
      obtain ⟨site, w, p, x⟩ := sm
      obtain rfl : site = pos.site := hr.site
      obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site hC hX he hσm
      obtain ⟨pc, md, a, b, c, v, ok, rfl⟩ :
          ∃ pc md a b c v ok, e = ⟨pc, .shfl md a b c v ok⟩ := by
        obtain ⟨pc, kd⟩ := e
        cases kd <;> first | exact ⟨_, _, _, _, _, _, _, rfl⟩ | cases hsh
      have hev := ev_full hpre hg pos hr hat hc hf
      have hn : ((X.tr g).take m).countP Execution.isShfl = (led g pos).shfls :=
        congrArg Led.shfls hl
      rcases pos with j | j | j | j | j | j | _ | j | _ <;>
        simp only [Ev, Event.mk.injEq, reduceCtorEq, and_false, exists_false, exists_const,
          false_and] at hev
      rw [led_shfl] at hn
      omega
    · exact .inr (Left.mono hleft (by omega))

/-- The invariant with the count of warp collectives (`InvE`), with the soundness of the
machine as a hypothesis: the proof of `startup_inv_sound` on `startup_invE_upto`. -/
theorem startup_invE_sound (hg : g < L.threads) {k : Nat} {s : D} (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) : InvE P X g k s ∨ LeftE P L X g k := by
  by_cases h3 : ((X.tr g).take k).countP Execution.isShfl ≤ 3
  · exact startup_invE_upto hpre hC hX hg (shfl_first hpre hC hX hg h3) le_rfl hk hσ
  · -- the fourth shuffle, at `m < k`: the thread has left the phase before it
    obtain ⟨m, hm, e, he, hsh, hcnt⟩ :=
      exists_nth Execution.isShfl (X.tr g) (n := 3) (k := k) (by omega)
    obtain ⟨sm, hσm⟩ := followed_of_le hσ (show m ≤ k by omega)
    have hSm : ShflBefore X g m := shfl_first hpre hC hX hg (by omega)
    rcases startup_invE_upto hpre hC hX hg hSm le_rfl (by omega) hσm with
      ⟨pos, hr, hl, -⟩ | ⟨j, hj, s0, h1, h2⟩
    · exfalso
      obtain ⟨site, w, p, x⟩ := sm
      obtain rfl : site = pos.site := hr.site
      obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site hC hX he hσm
      obtain ⟨pc, md, a, b, c, v, ok, rfl⟩ :
          ∃ pc md a b c v ok, e = ⟨pc, .shfl md a b c v ok⟩ := by
        obtain ⟨pc, kd⟩ := e
        cases kd <;> first | exact ⟨_, _, _, _, _, _, _, rfl⟩ | cases hsh
      have hev := ev_full hpre hg pos hr hat hc hf
      have hn : ((X.tr g).take m).countP Execution.isShfl = (led g pos).shfls :=
        congrArg Led.shfls hl
      rcases pos with j | j | j | j | j | j | _ | j | _ <;>
        simp only [Ev, Event.mk.injEq, reduceCtorEq, and_false, exists_false, exists_const,
          false_and] at hev
      rw [led_shfl] at hn
      omega
    · exact .inr ⟨j, by omega, s0, h1, h2⟩

end

/-- **The reference invariant of the startup phase**: before each event of a launched thread,
the state of its machine is at a position of the phase with the position's register facts and
ledger (`Inv`), or the thread has left the phase through its exit (`Left`). The hypotheses are
the precondition and consistency; nothing is assumed about returned values or about the later
phases. -/
theorem startup_inv (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) {k : Nat} {s : D} (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) : Inv P X g k s ∨ Left P L X g k :=
  startup_inv_sound hpre (sounds hpre) hX hg hk hσ

/-- **The reference invariant with the count of warp collectives**: `startup_inv` with, on
both sides, the number of the thread's shuffles and elections before the position (`InvE`,
`OutE`): what the progress contract's field `coll` reads. -/
theorem startup_invE (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) {k : Nat} {s : D} (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    InvE P X g k s ∨ LeftE P L X g k :=
  startup_invE_sound hpre (sounds hpre) hX hg hk hσ

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
