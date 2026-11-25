-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.CarryLoad.Trace
public import Kernels.FlashKdaFwd.Proof.Ref.Conversion.Trace
public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Counts
public import Kernels.FlashKdaFwd.Proof.Ref.Compute.Interface
public import Kernels.FlashKdaFwd.Proof.Ref.Store.Interface
public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Exports
public import Lemmas.Kernel.Progress.Warp

@[expose] public section

/-! # The links of the CarryLoad phase: from the Conversion phase, into the three tile loops

**Into the phase.** The entry condition is the Conversion's exit condition
(`in_of_conversion`: the link is the identity).

**Out of the phase.** The exit state at `bar_5` (instruction 1402, before its event) is the
entry of the tile loop of the thread's role: `Compute.In` for a compute thread (thread index
below 128), `Producer.Entered` for a thread of the load warp, `Store.In` for a thread of the
store warp. The registers of the three entry conditions are among the registers that no code
from the startup's exit to 1402 writes (`Conversion.Keep`), so that half is immediate
(`compute_entry`, `producer_entry`, `store_entry`).

The ledgers of the three entries count classes of events that the ledger of the startup,
Conversion and CarryLoad phases (`Startup.Led`, counts by kind) does not have: successful
polls, arrivals and tensor loads *per mbarrier*, and the named barrier, matrix events, tensor
stores, group commits, group waits and writes of global memory, of which there are none
before the tile loops. These counts are known at the **first exit of the startup phase**
(`Startup.FirstOut`, `Startup/Counts.lean`) and do not change afterwards up to `bar_5`,
because every event of the Conversion and CarryLoad phases is a proxy fence, a read or a
write of shared memory, a `bar.sync 0`, or (a conversion store whose value does not convert)
undefined behaviour (`Quiet`, `quiet_event`); none of these is in any of the classes.

So the links take the history of the thread as a hypothesis:

* `Entered P L X g j0 k1`: the thread left the startup phase for the first time at its event
  `j0`, and `k1 = j0 + Conversion.len g` is a followed state with the Conversion's exit
  condition (the entry of the CarryLoad phase). This is what the chain of the phases
  (`Ref/Chain.lean`, with the startup phase taken at its first exit) knows when the CarryLoad
  phase is entered; `entered_of` builds it from the chain's facts.
* `count_keep`: the count of a class without `Quiet` events is, at every followed state from
  `j0` to the exit of the CarryLoad phase, its count at `j0`.
* `Carried P L X g k`: the values of the counts at such a state (`carried`).
* `compute_in`, `producer_entered`, `store_in`: the three entry conditions at the exit state.

Hypotheses everywhere: the precondition `Pre`, consistency, the thread is launched. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.CarryLoad
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (Bar)

noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat} {e : Event}

/-- **The exit of the Conversion phase is the entry of the CarryLoad phase** (the link of the
two phases in the chain): the two conditions are the same statement. -/
theorem in_of_conversion {k0 j : Nat} {s1 : D}
    (h : (Conversion.phase P L X g).Out k0 j s1) : (phase P L X g).In j s1 := h.2

/-! ### The events between the startup's exit and `bar_5` -/

/-- **An event of the Conversion or the CarryLoad phase**, by kind: a proxy fence, a read of
shared memory, a write of shared memory, undefined behaviour (a conversion store whose value
does not convert to 16 bits; the value layer excludes it), or `bar.sync 0`. -/
def Quiet (e : Event) : Prop :=
  (∃ px sc, e.kind = .fenceProxy px sc) ∨ (∃ a bs, e.kind = .rd a bs ∧ a.loc.space = .shared) ∨
    (∃ a bs, e.kind = .wr a bs ∧ a.loc.space = .shared) ∨ (∃ f, e.kind = .ub f) ∨
    e.kind = .bar 0 none .sync

/-- **The thread entered the CarryLoad phase at its event `k1`, having left the startup phase
for the first time at its event `j0`**: `j0` is the first exit of the startup phase, `k1` is
`Conversion.len g` events later, and the state before event `k1` is followed and satisfies the
entry condition of the CarryLoad phase (the Conversion's exit condition). -/
structure Entered (P : Params) (L : Launch) (X : Execution) (g j0 k1 : Nat) : Prop where
  first : Startup.FirstOut P L X g j0
  conv : k1 = j0 + Conversion.len g
  state : ∃ s1, Frame.stateAt (code L) X g k1 = some (some s1) ∧ In P X g k1 s1

/-- `Entered` from the facts of the chain of the phases: the first exit of the startup phase
at `j0`, and the exit of the Conversion phase (entered at `j0`) at a followed state `k1`. -/
theorem entered_of {j0 k1 : Nat} {s1 : D} (h0 : Startup.FirstOut P L X g j0)
    (hσ1 : Frame.stateAt (code L) X g k1 = some (some s1))
    (h1 : (Conversion.phase P L X g).Out j0 k1 s1) : Entered P L X g j0 k1 :=
  ⟨h0, h1.1, s1, hσ1, h1.2⟩

theorem Entered.le {j0 k1 : Nat} (h : Entered P L X g j0 k1) : j0 ≤ k1 := by
  have := h.conv
  omega

/-- `quiet_cls [defs]`: an event of the two phases is not in a class defined by a `match` on
the kind (`defs`: the definitions to unfold). -/
syntax "quiet_cls" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| quiet_cls) => `(tactic| quiet_cls [])
  | `(tactic| quiet_cls [$ls,*]) => `(tactic| (
      rintro ⟨pc, kd⟩ (⟨_, _, h⟩ | ⟨_, _, h, hs⟩ | ⟨_, _, h, hs⟩ | ⟨_, h⟩ | h) <;>
      (simp only at h
       subst h
       first | rfl | simp [hs, $ls,*])))

theorem Quiet.named : ∀ e, Quiet e → Execution.isBarId 8 e = false := by quiet_cls

theorem Quiet.otherBar :
    ∀ e, Quiet e → (Execution.isBar e && !Execution.isBarId 0 e) = false := by quiet_cls

theorem Quiet.matrix : ∀ e, Quiet e → isMatrix e = false := by quiet_cls

theorem Quiet.coll : ∀ e, Quiet e → Sched.isWarpColl e = false := by quiet_cls

theorem Quiet.okPoll (m : Loc) : ∀ e, Quiet e → okPoll m e = false := by
  quiet_cls [okPoll, sourceWaitSuccess]

theorem Quiet.arrivesOn (m : Loc) : ∀ e, Quiet e → arrivesOn m e = false := by
  quiet_cls [arrivesOn, sourceArrive]

theorem Quiet.issuesTo (m : Loc) : ∀ e, Quiet e → issuesTo m e = false := by
  quiet_cls [issuesTo]

theorem Quiet.tstore : ∀ e, Quiet e → Store.isTStore e = false := by quiet_cls

theorem Quiet.commit : ∀ e, Quiet e → Store.isCommit e = false := by quiet_cls

theorem Quiet.bwait : ∀ e, Quiet e → Store.isBWait e = false := by quiet_cls

theorem Quiet.gwrite : ∀ e, Quiet e → Store.isGWrite e = false := by
  quiet_cls [Store.isGWrite]

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads) {j0 k1 : Nat} (hen : Entered P L X g j0 k1)
include hpre hX hg hen

/-- **Every event from the startup's first exit to the exit of the CarryLoad phase is quiet**:
the state before it is a state of the Conversion phase (before `k1`) or of the CarryLoad phase
(from `k1` on), and the closed-form event of each position is of one of the five kinds. -/
theorem quiet_event {i : Nat} {si : D} (hσi : Frame.stateAt (code L) X g i = some (some si))
    (he : X.get (g, i) = some e) (hlo : j0 ≤ i) (hhi : i < k1 + len g) : Quiet e := by
  have hil : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨s0, hσ0, ho0, -⟩ := hen.first
  obtain ⟨s1, hσ1, hin1⟩ := hen.state
  have hconv := hen.conv
  by_cases hi : i < k1
  · rcases Conversion.conversion_inv hpre hX hg hσ0 ho0 hlo hil hσi with hI | ⟨hle, -⟩
    · obtain ⟨pos, hr, -⟩ := hI
      obtain ⟨site, w, p, x⟩ := si
      obtain rfl : site = pos.site := hr.site
      obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
        Frame.fired_site (fun g hg => Thread.sound hpre hg) hX he hσi
      have hev := Conversion.ev_at hpre hg pos hr hat hc hf
      cases pos with
      | fence =>
        obtain rfl : e = _ := hev
        exact .inl ⟨_, _, rfl⟩
      | ld j u =>
        obtain ⟨bs, -, rfl⟩ := hev
        exact .inr (.inl ⟨_, bs, rfl, rfl⟩)
      | st j u =>
        rcases hev with ⟨v', -, rfl⟩ | ⟨f, -, rfl⟩
        · exact .inr (.inr (.inl ⟨_, _, rfl, rfl⟩))
        · exact .inr (.inr (.inr (.inl ⟨f, rfl⟩)))
      | bar j =>
        obtain rfl : e = _ := hev
        exact .inr (.inr (.inr (.inr rfl)))
    · omega
  · rcases carry_inv hpre hX hg hσ1 hin1 (by omega) hil hσi with hI | ⟨hle, -⟩
    · obtain ⟨pos, -, hev, -⟩ := event_at hpre hX hg he hσi hI
      rcases hev.kind_cases with h | h
      · exact .inr (.inl h)
      · exact .inl h
    · omega

/-- **Count transport from the startup's first exit to `bar_5`**: the count of a class without
quiet events is, at a followed state `k` between the first exit `j0` and the exit of the
CarryLoad phase, its count at `j0`. -/
theorem count_keep (c : Event → Bool) (hc : ∀ e, Quiet e → c e = false) {k : Nat} {s : D}
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hj : j0 ≤ k) (hk : k ≤ k1 + len g) :
    ((X.tr g).take k).countP c = ((X.tr g).take j0).countP c :=
  countP_take_eq c hj fun i e h1 h2 he => by
    obtain ⟨si, hσi⟩ := followed_of_le hσ (show i ≤ k by omega)
    exact hc e (quiet_event hpre hX hg hen hσi he h1 (by omega))

end

/-! ### The counts at a state of the phase and at its exit -/

/-- **The counts that the tile loops need and that the phases before them do not change**,
over the first `k` events of thread `g`: no named barrier (so every barrier arrival is a
`bar.sync 0`), no matrix event, no tensor store, no group commit, no group wait, no write of
global memory; and per mbarrier `b` of the thread's block: one successful poll of the state
mbarrier and none of the others; in the load leader (thread 128 of its block) one arrival on
the state mbarrier and 16 tensor loads completing on it, and none of either on the other
mbarriers or in the other threads. -/
structure Carried (P : Params) (L : Launch) (X : Execution) (g k : Nat) : Prop where
  named : ((X.tr g).take k).countP (Execution.isBarId 8) = 0
  bars : ((X.tr g).take k).countP Execution.isBar =
    ((X.tr g).take k).countP (Execution.isBarId 0)
  matrix : ((X.tr g).take k).countP isMatrix = 0
  tstore : ((X.tr g).take k).countP Store.isTStore = 0
  commit : ((X.tr g).take k).countP Store.isCommit = 0
  bwait : ((X.tr g).take k).countP Store.isBWait = 0
  gwrite : ((X.tr g).take k).countP Store.isGWrite = 0
  polls : ∀ b : Bar, okPolls (b.loc L (g / L.block)) ((X.tr g).take k) =
    if b = .state then 1 else 0
  arrs : ∀ b : Bar, arrivals (b.loc L (g / L.block)) ((X.tr g).take k) =
    if b = .state ∧ tid g = 128 then 1 else 0
  issues : ∀ b : Bar, ((X.tr g).take k).countP (issuesTo (b.loc L (g / L.block))) =
    if b = .state ∧ tid g = 128 then 16 else 0

/-- The thread has polled the state mbarrier of its block successfully. -/
theorem Carried.polled {k : Nat} (h : Carried P L X g k) :
    1 ≤ okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take k) := by
  rw [h.polls .state]
  simp

/-- A class that holds of an event only if a narrower class does has the narrower count. -/
theorem countP_eq_of_none {c1 c2 c3 : Event → Bool} {es : List Event}
    (h0 : es.countP c3 = 0) (h : ∀ x, c1 x = c2 x ∨ c3 x = true) :
    es.countP c1 = es.countP c2 := by
  refine List.countP_congr fun x hx => ?_
  rcases h x with h1 | h1
  · rw [h1]
  · have := List.countP_eq_zero.mp h0 x hx
    exact absurd h1 this

/-- A barrier arrival is a `bar.sync 0`, or a barrier arrival that is none. -/
theorem bar_split (x : Event) : Execution.isBar x = Execution.isBarId 0 x ∨
    (Execution.isBar x && !Execution.isBarId 0 x) = true := by
  cases h : Execution.isBarId 0 x
  · cases h' : Execution.isBar x
    · exact .inl rfl
    · exact .inr rfl
  · left
    obtain ⟨pc, kd⟩ := x
    cases kd <;> first | rfl | cases h

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads) {j0 k1 : Nat} (hen : Entered P L X g j0 k1)
include hpre hX hg hen

/-- **The counts at a followed state of the CarryLoad phase or at its exit** are those of the
startup's first exit. -/
theorem carried {k : Nat} {s : D} (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hj : j0 ≤ k) (hk : k ≤ k1 + len g) : Carried P L X g k := by
  have hf := hen.first
  obtain ⟨s0, hσ0, ho0, -⟩ := id hf
  have keep := fun c hc => count_keep hpre hX hg hen c hc hσ hj hk
  have hbar := fun b => Startup.out_bar_counts hpre hX hg hσ0 ho0 b
  have kz : ∀ c : Event → Bool, (∀ e, Quiet e → c e = false) →
      (∀ e, Startup.phaseKind e.kind = true → c e = false) →
      ((X.tr g).take k).countP c = 0 := fun c h1 h2 =>
    (keep c h1).trans (Startup.first_kind_zero hpre hX hg hf c h2)
  have hother : ((X.tr g).take k).countP
      (fun e => Execution.isBar e && !Execution.isBarId 0 e) = 0 := by
    rw [keep _ Quiet.otherBar]
    refine Startup.first_count_zero hpre hX hg hf _ fun pos e hev => ?_
    rcases pos with j | j | j | j | j | j | _ | j | _ <;> simp only [Startup.Ev] at hev
    · obtain ⟨inst, ld, rfl⟩ := hev
      rfl
    · obtain ⟨v, ok, rfl⟩ := hev
      rfl
    · subst hev
      rfl
    · subst hev
      rfl
    · subst hev
      rfl
    · obtain ⟨i, hi, bs, hbs, rfl⟩ := hev
      rfl
    · subst hev
      rfl
    · subst hev
      rfl
    · obtain ⟨ok, rfl⟩ := hev
      rfl
  refine ⟨?_, countP_eq_of_none hother bar_split, ?_, ?_, ?_, ?_, ?_, fun b => ?_, fun b => ?_,
    fun b => ?_⟩
  · exact (keep _ Quiet.named).trans (Startup.first_named_zero hpre hX hg hf)
  · exact (keep _ Quiet.matrix).trans (Startup.first_matrix_zero hpre hX hg hf)
  · refine kz _ Quiet.tstore ?_
    rintro ⟨pc, kd⟩ h
    cases kd <;> first | rfl | cases h
  · refine kz _ Quiet.commit ?_
    rintro ⟨pc, kd⟩ h
    cases kd <;> first | rfl | cases h
  · refine kz _ Quiet.bwait ?_
    rintro ⟨pc, kd⟩ h
    cases kd <;> first | rfl | cases h
  · refine kz _ Quiet.gwrite ?_
    rintro ⟨pc, kd⟩ h
    cases kd <;> first | rfl | cases h
  · exact (keep _ (Quiet.okPoll _)).trans (hbar b).1
  · exact (keep _ (Quiet.arrivesOn _)).trans (hbar b).2.1
  · exact (keep _ (Quiet.issuesTo _)).trans (hbar b).2.2

/-- **The shuffles and elections of a thread at a followed state of the CarryLoad phase or at
its exit** are those of the startup's first exit: the two phases after it make none. -/
theorem coll_keep {k : Nat} {s : D} (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hj : j0 ≤ k) (hk : k ≤ k1 + len g) :
    ((X.tr g).take k).countP Sched.isWarpColl =
      ((X.tr g).take j0).countP Sched.isWarpColl :=
  count_keep hpre hX hg hen _ Quiet.coll hσ hj hk

end

/-! ### The registers of the three entries -/

/-- The entry registers of the Compute phase, from the kept registers at `bar_5`. -/
theorem compute_entry {d : D} (hc : tid g < 128) (h : Exit P g d) : Compute.Entry P g d := by
  obtain ⟨⟨hb, hf, hr, ⟨s1, s2, s3, s4⟩, he⟩, hs⟩ := h
  simp only [Startup.Flags, Startup.flagsOf, Startup.roleFlags, hc, ↓reduceIte,
    Prod.mk.injEq] at hf
  exact ⟨hs, hc, hb.tid, hf.1, hf.2.1, hf.2.2.1, s1, s2, s4, he⟩

/-- The entry registers of the Producer phase, from the kept registers at `bar_5`. -/
theorem producer_entry {d : D} (hw : warp g = 4) (h : Exit P g d) : Producer.Entry P g d :=
  Producer.entry_of_startup hw h.site h.keep.base.tid h.keep.flags h.keep.scan h.keep.elected

/-- The entry registers of the Store phase, from the kept registers at `bar_5`. -/
theorem store_entry {d : D} (hw : warp g = 5) (h : Exit P g d) : Store.Entry P g d := by
  obtain ⟨⟨hb, hf, hr, ⟨s1, s2, s3, s4⟩, he⟩, hs⟩ := h
  exact ⟨hs, hw, hb.tid, s1, s2, hr, he, s4⟩

/-! ### The three entry conditions at `bar_5` -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads) {j0 k1 : Nat} (hen : Entered P L X g j0 k1)
include hpre hX hg hen

/-- **The exit of the CarryLoad phase is the entry of the Compute phase**, for a compute
thread: the state at `bar_5` with the entry registers, five `bar.sync 0`, one successful poll
of the state mbarrier and no other event of the classes of the Compute phase's ledger. -/
theorem compute_in (hc : tid g < 128) {k2 : Nat} {s2 : D}
    (hσ2 : Frame.stateAt (code L) X g k2 = some (some s2))
    (hout : (phase P L X g).Out k1 k2 s2) : Compute.In P L X g k2 s2 := by
  obtain ⟨rfl, hE, hl, -⟩ := hout
  have hC := carried hpre hX hg hen hσ2 (by have := hen.le; omega) le_rfl
  have hb0 : ((X.tr g).take (k1 + len g)).countP (Execution.isBarId 0) = 5 :=
    congrArg Startup.Led.bars hl
  refine ⟨compute_entry hc hE, ?_⟩
  simp only [Compute.ledOf, Compute.ledEntry, hb0, hC.named, hC.matrix, hC.polls, hC.arrs,
    reduceCtorEq, ↓reduceIte, false_and]

/-- **The exit of the CarryLoad phase is the entry of the Producer phase**, for a thread of
the load warp: the state at `bar_5` with the entry registers, the entry ledger (five
`bar.sync 0`; the startup's initialization, arrival and 16 loads in thread 128; one successful
poll; nothing on the mbarriers of the load pipeline), and the successful poll of the state
mbarrier. -/
theorem producer_entered (hw : warp g = 4) {k2 : Nat} {s2 : D}
    (hσ2 : Frame.stateAt (code L) X g k2 = some (some s2))
    (hout : (phase P L X g).Out k1 k2 s2) : Producer.Entered P L X g k2 := by
  obtain ⟨rfl, hE, hl, -⟩ := hout
  have hC := carried hpre hX hg hen hσ2 (by have := hen.le; omega) le_rfl
  have ht := (warp_eq4_iff g).mp hw
  have ht0 : tid g ≠ 0 := by omega
  have h1 : ((X.tr g).take (k1 + len g)).countP (Execution.isBarId 0) = 5 :=
    congrArg Startup.Led.bars hl
  have h2 : ((X.tr g).take (k1 + len g)).countP Startup.isInit =
      if tid g = 128 then 1 else 0 := by
    have := congrArg Startup.Led.inits hl
    simpa [ledExit, Conversion.ledExit, Startup.ledExit, Startup.ledOf, ht0] using this
  have h3 : ((X.tr g).take (k1 + len g)).countP Startup.isArr =
      if tid g = 128 then 1 else 0 := congrArg Startup.Led.arrs hl
  have h4 : ((X.tr g).take (k1 + len g)).countP Startup.isIssue =
      if tid g = 128 then 16 else 0 := congrArg Startup.Led.issues hl
  have h5 : ((X.tr g).take (k1 + len g)).countP Startup.isOkPoll = 1 :=
    congrArg Startup.Led.polls hl
  refine ⟨⟨s2, hσ2, producer_entry hw hE⟩, ?_, hC.polled⟩
  simp only [Producer.ledOf, Producer.ledEntry, Producer.emptyLoc, Producer.fullLoc, h1, h2,
    h3, h4, h5, hC.polls, hC.arrs, hC.issues, reduceCtorEq, ↓reduceIte, false_and]

/-- **The exit of the CarryLoad phase is the entry of the Store phase**, for a thread of the
store warp: the state at `bar_5` with the kept registers, five `bar.sync 0`, one successful
poll of the state mbarrier and no other event of the classes of the Store phase's ledger. -/
theorem store_in (hw : warp g = 5) {k2 : Nat} {s2 : D}
    (hσ2 : Frame.stateAt (code L) X g k2 = some (some s2))
    (hout : (phase P L X g).Out k1 k2 s2) : Store.In P X g k2 s2 := by
  obtain ⟨rfl, hE, hl, -⟩ := hout
  have hC := carried hpre hX hg hen hσ2 (by have := hen.le; omega) le_rfl
  have hb0 : ((X.tr g).take (k1 + len g)).countP (Execution.isBarId 0) = 5 :=
    congrArg Startup.Led.bars hl
  have hcta : cta g = g / L.block := (block_div hpre).symm
  have hS : Store.stateBar P g = Bar.state.loc L (g / L.block) := by
    simp only [Store.stateBar, Bar.loc, Bar.off, hpre.sharedBase, hcta]
  have hF : ∀ o : Fin 2, Store.fullBar P g o.val = (Bar.storeFull o).loc L (g / L.block) := by
    intro o
    simp only [Store.fullBar, Bar.loc, Bar.off, hpre.sharedBase, hcta, Nat.add_assoc]
  have hEm : ∀ o : Fin 2, Store.emptyBar P g o.val = (Bar.storeEmpty o).loc L (g / L.block) := by
    intro o
    simp only [Store.emptyBar, Bar.loc, Bar.off, hpre.sharedBase, hcta, Nat.add_assoc]
  refine ⟨store_entry hw hE, ?_⟩
  have f0 := hF 0
  have f1 := hF 1
  have e0 := hEm 0
  have e1 := hEm 1
  simp only [Fin.val_zero, Fin.val_one] at f0 f1 e0 e1
  simp only [Store.ledOf, Store.ledEntry, hb0, hS, f0, f1, e0, e1, hC.polls, hC.arrs,
    hC.tstore, hC.commit, hC.bwait, hC.gwrite, reduceCtorEq, ↓reduceIte, false_and]

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.CarryLoad
