-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Tracked
public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Contract
public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Direct
public import Kernels.FlashKdaFwd.Proof.Ref.Conversion.Exports
public import Kernels.FlashKdaFwd.Proof.Ref.CarryLoad.Exports
public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Exports
public import Kernels.FlashKdaFwd.Proof.Ref.Store.Exports
public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Contract
public import Kernels.FlashKdaFwd.Proof.Protocol.Export

@[expose] public section

/-!
# The rings and the state copy: four contracts of the protocol layer, from the phases

The protocol layer (`Proof/Protocol/`) proves the synchronization of the kernel from "thread
facts": statements about the events of one thread (who arrives on which memory barrier, with
which count and after which earlier events). This file proves four of its seven structures of
thread facts for every consistent execution of the kernel, from the exports of the phases of
the reference layer and ONE structure of facts about the Compute phase (`ComputeOwes`, stated
here in that phase's vocabulary and proved in `FactsBOwes.lean` from the phase's export file):

* `loadFacts_of : Protocol.LoadFacts L X` (`Protocol/LoadRing.lean`): the load pipeline;
* `storeFacts_of : Protocol.StoreFacts L X` (`Protocol/StoreRing.lean`): the store pipeline;
* `stateFacts_of : Protocol.StateFacts L X` (`Protocol/StateBar.lean`): the barrier of the
  load of the initial state;
* `stateAccFacts_of : Protocol.StateAccFacts L X` (`Protocol/Regions.lean`): who touches the
  bfloat16 copy of the state;
* `facts_of : Protocol.Facts P L X` (`Protocol/Export.lean`): the seven structures together,
  from these four and the three of `FactsA.lean`.

Everything is in the namespace `Ref.Assembly.FactsB`; the final theorems (`loadFacts`,
`storeFacts`, `stateFacts`, `stateAccFacts`, without the hypothesis `ComputeOwes`) are in
`FactsB.lean`.

**Words.** An *mbarrier* is one of the eleven 8-byte synchronization objects of a thread block
(`Protocol.Bar`); a *poll* is an `mbarrier.try_wait`; a *tensor load* (*tensor store*) is an
asynchronous copy of the copy engine from global to shared memory (from shared to global). A
*followed state* of thread `g` at position `k` is the state of the thread's machine before the
thread's `k`-th event (`At (code L) X g k s`). The *phases* of a thread's run are the startup,
the Conversion, the CarryLoad, one of the three tile loops (Compute for a compute thread,
Producer for the load warp, Store for the store warp) and the epilogue; `Stage P L X g k s`
(`Stage.lean`) says which one a followed state is in, with that phase's invariant. The *union
region* is the part of a block's shared memory that the copy engine and the threads share
(`Protocol.InUnion`); `state_acc` is the part before it (`Protocol.InStateAcc`).

**Method.** Every field is about an event of a kind other than undefined behaviour. Such an
event fires from a followed state (`staged`, from the chain's `event_stage`), which is in one
of the seven phases; the phase's exported theorems say what the event is. This is done once
per KIND of event, not once per field:

* `arrive_fact`: an arrival on an mbarrier names one of the eleven mbarriers of the thread's
  own block; `ArriveFact` says, per mbarrier, who the thread is, the operands and the gate, and
  `ArrivePhase` the phase of the arrival where a field needs it;
* `poll_fact` (`PollFact`): the same for a poll;
* `issue_fact` (`IssueFact`): the same for a tensor load and the mbarrier it completes on,
  with the region of the bytes it writes;
* `store_fact`: a tensor store is the store leader's, reads bytes of the union region, and is
  a store of the Store phase or of the epilogue;
* `acc_fact`: a thread's memory access of a byte of `state_acc` is made in the Conversion
  phase or in the Compute phase;
* `async_not_acc`: no asynchronous operation touches `state_acc`.

A field is then one of these with the mbarrier of its hypothesis (`Bar.loc_inj`: the
locations of the mbarriers of the blocks are distinct).

**What comes from where.** Startup: `Startup/Exports.lean`, `Contract.lean`, `Direct.lean`
(its exports have the alternative "the thread has left the phase", excluded by
`Startup.Inv.not_left`). Conversion: `event_at`, `stateAcc_phase`, `stateAcc_owner`. CarryLoad:
`event_at`, `touch_carry`, `ldAddr_frame`. Producer: `producer_good` with the position-level
shapes `arrive_shape`, `poll_shape`, `issue_shape`, `tileLoad_writeLoc`. Store: `store_good`
with `ev_*_inv`, `full_poll_store`, `empty_arrive_store`, `no_issue_store`, `store_store`,
`store_wait_store`. Epilogue: `kind_in`, `ts_in`, `ts_final`, `wr_final`, `no_read`. Compute:
`ComputeOwes`. Kinds of events that the kernel never fires: `Proof/Top/Static.lean`.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.FactsB
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Protocol

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### What the Compute phase owes -/

/-- **The share of the Compute phase** (instructions 2106 to 2944: the tile loop of a compute
thread), in that phase's vocabulary: every field is about an event (or a memory access) of a
compute thread `g` at a followed state `s` with the phase's invariant
`Compute.Inv P L X g j0 k s`, where `j0` is the position of the phase's entry, a followed state
`s0` with the entry condition `Compute.In P L X g j0 s0`. -/
structure ComputeOwes (P : Params) (L : Launch) (X : Execution) : Prop where
  /-- The kinds of the events of the phase: a barrier, a poll, an arrival on an mbarrier, a
  proxy fence, a read, a write, a warp matrix event or undefined behaviour (so: no tensor load,
  no tensor store, no exit). -/
  kinds : ∀ {g j0 k : Nat} {s0 s : D} {e : Event}, g < L.threads → tid g < 128 →
    At (code L) X g j0 s0 → Compute.In P L X g j0 s0 →
    At (code L) X g k s → Compute.Inv P L X g j0 k s → X.get (g, k) = some e →
      (∃ id cnt m, e.kind = .bar id cnt m) ∨ (∃ l q ok acq sc, e.kind = .wait l q ok acq sc) ∨
      (∃ l tx n rel sc, e.kind = .arrive l tx n rel sc) ∨
      (∃ px sc, e.kind = .fenceProxy px sc) ∨ (∃ a bs, e.kind = .rd a bs) ∨
      (∃ a bs, e.kind = .wr a bs) ∨ (∃ op own recv, e.kind = .matrix op own recv) ∨
      ∃ f, e.kind = .ub f
  /-- A poll of the phase acquires; it is a poll of the "full" mbarrier of a load stage of the
  thread's block, with the parity of the thread's earlier successful polls of it, or of the
  "empty" mbarrier of a store stage, with that parity plus one. -/
  poll : ∀ {g j0 k pc p : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope} {s0 s : D},
    g < L.threads → tid g < 128 → At (code L) X g j0 s0 → Compute.In P L X g j0 s0 →
    At (code L) X g k s → Compute.Inv P L X g j0 k s →
    X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
      acq = true ∧
      ((∃ st : Fin 3, m = (Bar.loadFull st).loc L (g / L.block) ∧
          p % 2 = okPolls m ((X.tr g).take k) % 2) ∨
        (∃ o : Fin 2, m = (Bar.storeEmpty o).loc L (g / L.block) ∧
          p % 2 = (okPolls m ((X.tr g).take k) + 1) % 2))
  /-- An arrival of the phase is one release arrival without transaction bytes, on the "empty"
  mbarrier of a load stage of the thread's block after more successful polls of the stage's
  "full" mbarrier than earlier arrivals, or on the "full" mbarrier of a store stage after more
  successful polls of the stage's "empty" mbarrier than earlier arrivals. -/
  arrive : ∀ {g j0 k pc tx cnt : Nat} {m : Loc} {rel : Bool} {sc : MbarScope} {s0 s : D},
    g < L.threads → tid g < 128 → At (code L) X g j0 s0 → Compute.In P L X g j0 s0 →
    At (code L) X g k s → Compute.Inv P L X g j0 k s →
    X.get (g, k) = some ⟨pc, .arrive m tx cnt rel sc⟩ →
      tx = 0 ∧ cnt = 1 ∧ rel = true ∧
      ((∃ st : Fin 3, m = (Bar.loadEmpty st).loc L (g / L.block) ∧
          arrivals m ((X.tr g).take k) + 1 ≤
            okPolls ((Bar.loadFull st).loc L (g / L.block)) ((X.tr g).take k)) ∨
        (∃ o : Fin 2, m = (Bar.storeFull o).loc L (g / L.block) ∧
          arrivals m ((X.tr g).take k) + 1 ≤
            okPolls ((Bar.storeEmpty o).loc L (g / L.block)) ((X.tr g).take k)))
  /-- Between an earlier memory access of the thread that covers a byte of the input buffer of
  load stage `st` and an arrival of the phase on the "empty" mbarrier of that stage, the thread
  executes a `fence.proxy.async.shared::cta` (the fence of the arrival's tile, at instruction
  2914: two events before the arrival). -/
  in_fence : ∀ {g j0 i e pce tx cnt : Nat} {a : Acc} {w : Bool} {l : Loc} {st : Fin 3}
    {rel : Bool} {sc : MbarScope} {s0 se : D},
    g < L.threads → tid g < 128 → At (code L) X g j0 s0 → Compute.In P L X g j0 s0 →
    At (code L) X g e se → Compute.Inv P L X g j0 e se →
    X.get (g, e) = some ⟨pce, .arrive ((Bar.loadEmpty st).loc L (g / L.block)) tx cnt rel sc⟩ →
    X.Access (g, i) a w → a.Covers l → InInput L (g / L.block) st.val l → i < e →
      ∃ f pcf, i < f ∧ f < e ∧
        X.get (g, f) = some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩
  /-- Between an earlier memory access of the thread that covers a byte of the output buffer of
  store stage `o` and an arrival of the phase on the "full" mbarrier of that stage, the thread
  executes a `fence.proxy.async.shared::cta` (the event before the arrival). -/
  out_fence : ∀ {g j0 i e pce tx cnt : Nat} {a : Acc} {w : Bool} {l : Loc} {o : Fin 2}
    {rel : Bool} {sc : MbarScope} {s0 se : D},
    g < L.threads → tid g < 128 → At (code L) X g j0 s0 → Compute.In P L X g j0 s0 →
    At (code L) X g e se → Compute.Inv P L X g j0 e se →
    X.get (g, e) = some ⟨pce, .arrive ((Bar.storeFull o).loc L (g / L.block)) tx cnt rel sc⟩ →
    X.Access (g, i) a w → a.Covers l → InOutput L (g / L.block) o.val l → i < e →
      ∃ f pcf, i < f ∧ f < e ∧
        X.get (g, f) = some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩
  /-- A memory access of the phase that covers a byte of the bfloat16 state copy `state_acc`
  of a block `c` is in the thread's own block, with six `bar.sync 0` before it. -/
  acc_phase : ∀ {g j0 k c : Nat} {a : Acc} {w : Bool} {l : Loc} {s0 s : D},
    g < L.threads → tid g < 128 → At (code L) X g j0 s0 → Compute.In P L X g j0 s0 →
    At (code L) X g k s → Compute.Inv P L X g j0 k s →
    X.Access (g, k) a w → a.Covers l → InStateAcc L c l →
      c = g / L.block ∧ bar0Before X (g, k) = 6
  /-- Two memory accesses of the phase (of compute threads `g` and `h`, each at a state of its
  own invariant) that cover one byte of `state_acc`, one of them a write, are one thread's:
  each compute thread reads and rewrites its own rows only. -/
  acc_owner : ∀ {g h j0 j0' k k' c : Nat} {a b : Acc} {w w' : Bool} {l : Loc} {s0 s s0' s' : D},
    g < L.threads → tid g < 128 → At (code L) X g j0 s0 → Compute.In P L X g j0 s0 →
    At (code L) X g k s → Compute.Inv P L X g j0 k s →
    h < L.threads → tid h < 128 → At (code L) X h j0' s0' → Compute.In P L X h j0' s0' →
    At (code L) X h k' s' → Compute.Inv P L X h j0' k' s' →
    X.Access (g, k) a w → X.Access (h, k') b w' → (w = true ∨ w' = true) →
    a.Covers l → b.Covers l → InStateAcc L c l → g = h

/-! ### The followed state before an event, and small facts about threads and locations -/

/-- **A defined event fires from a followed state, which is in a phase**: the state, its
phase, and that no undefined-behaviour event of the thread precedes it. -/
theorem staged (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) :
    ∃ s, At (code L) X g k s ∧ Stage P L X g k s ∧ NoUb X g k :=
  event_stage hpre hX he fun f h => hub e.pc f (by rw [← h])

/-- The state mbarrier of the block of thread `g`, as the startup phase writes its location. -/
theorem stateLoc_eq (hpre : Pre P L mem0) (g : Nat) :
    (⟨.shared, g / L.block, P.sharedBase + 98384⟩ : Loc) = Bar.state.loc L (g / L.block) := by
  simp only [Bar.loc, Bar.off, hpre.sharedBase]

/-- A thread with index below 128 in its block, in the protocol layer's terms. -/
theorem compute_mod (hpre : Pre P L mem0) (hr : tid g < 128) : g % L.block < 128 := by
  rw [block_mod hpre]
  exact hr

/-- `no_kind h`: closes a goal from `h`, a disjunction of "the event is of kind …" none of
which is the kind of the event at hand. -/
macro "no_kind " h:ident : tactic => `(tactic| (
  simp only [reduceCtorEq, exists_false, exists_const, or_self, false_and, and_false] at $h:ident))

/-! ### Arrivals on an mbarrier -/

/-- **What an arrival on mbarrier `b` of the thread's block is**: who arrives, the transaction
bytes, the count, that it releases, and the gate (the arrival follows more successful polls of
the partner mbarrier than the thread's earlier arrivals; on the state mbarrier it is the
thread's first). -/
@[reducible] def ArriveFact (L : Launch) (X : Execution) (g k tx cnt : Nat) (rel : Bool) :
    Bar → Prop
  | .state => g = loadLeader L (g / L.block) ∧ tx = 65536 ∧ cnt = 1 ∧ rel = true ∧
      arrivals (Bar.state.loc L (g / L.block)) ((X.tr g).take k) = 0
  | .loadFull s => g = loadLeader L (g / L.block) ∧ tx = 17984 ∧ cnt = 1 ∧ rel = true ∧
      arrivals ((Bar.loadFull s).loc L (g / L.block)) ((X.tr g).take k) + 1 ≤
        okPolls ((Bar.loadEmpty s).loc L (g / L.block)) ((X.tr g).take k)
  | .loadEmpty s => g % L.block < 128 ∧ tx = 0 ∧ cnt = 1 ∧ rel = true ∧
      arrivals ((Bar.loadEmpty s).loc L (g / L.block)) ((X.tr g).take k) + 1 ≤
        okPolls ((Bar.loadFull s).loc L (g / L.block)) ((X.tr g).take k)
  | .storeFull o => g % L.block < 128 ∧ tx = 0 ∧ cnt = 1 ∧ rel = true ∧
      arrivals ((Bar.storeFull o).loc L (g / L.block)) ((X.tr g).take k) + 1 ≤
        okPolls ((Bar.storeEmpty o).loc L (g / L.block)) ((X.tr g).take k)
  | .storeEmpty o => g = storeLeader L (g / L.block) ∧ tx = 0 ∧ cnt = 1 ∧ rel = true ∧
      arrivals ((Bar.storeEmpty o).loc L (g / L.block)) ((X.tr g).take k) + 1 ≤
        okPolls ((Bar.storeFull o).loc L (g / L.block)) ((X.tr g).take k)

/-- **The state before event `k` of thread `g` is a state of the Compute phase**: a compute
thread, a followed state with the phase's invariant, and the followed entry state of the
phase. -/
def InCompute (P : Params) (L : Launch) (X : Execution) (g k : Nat) : Prop :=
  tid g < 128 ∧ ∃ j0 s0 s, At (code L) X g j0 s0 ∧ Compute.In P L X g j0 s0 ∧
    At (code L) X g k s ∧ Compute.Inv P L X g j0 k s

/-- **The state before event `k` of thread `g` is a state of the Store phase**: a followed
state with the phase's invariant, and the followed entry state of the phase, at `j0 ≤ k`. -/
def InStore (P : Params) (L : Launch) (X : Execution) (g k : Nat) : Prop :=
  ∃ j0 s0 s, j0 ≤ k ∧ At (code L) X g j0 s0 ∧ Store.In P X g j0 s0 ∧
    At (code L) X g k s ∧ Store.Inv P X g k s

/-- **The phase of an arrival on mbarrier `b`**, where a field needs it: an arrival on the
"empty" mbarrier of a load stage or on the "full" mbarrier of a store stage is made in the
Compute phase, one on the "empty" mbarrier of a store stage in the Store phase. -/
@[reducible] def ArrivePhase (P : Params) (L : Launch) (X : Execution) (g k : Nat) : Bar → Prop
  | .loadEmpty _ | .storeFull _ => InCompute P L X g k
  | .storeEmpty _ => InStore P L X g k
  | _ => True

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hC : ComputeOwes P L X)
include hpre hX hC

/-- **Every arrival on an mbarrier** is on one of the eleven mbarriers of the thread's own
block, with that mbarrier's facts, in that mbarrier's phase. -/
theorem arrive_fact {k pc tx cnt : Nat} {m : Loc} {rel : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .arrive m tx cnt rel sc⟩) :
    ∃ b : Bar, m = b.loc L (g / L.block) ∧ ArriveFact L X g k tx cnt rel b ∧
      ArrivePhase P L X g k b := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s, hσ, hS, hub⟩ := staged hpre hX he (fun _ _ h => by cases h)
  cases hS with
  | startup hI =>
    rcases Startup.arrive_startup hpre hX hg he hσ with ⟨-, rfl, rfl, rfl, rfl, -, h128, hl⟩ | h
    · exact ⟨.state, stateLoc_eq hpre g, ⟨Producer.leader_eq hpre h128, rfl, rfl, rfl,
        Startup.arrivals_zero (congrArg Startup.Led.arrs hl)⟩, trivial⟩
    · exact absurd h hI.inv.not_left
  | conversion past hj hI =>
    obtain ⟨pos, -, -, -, hev⟩ := Conversion.event_at hpre hX hg he hσ hI
    have hk := hev.phaseKind
    simp only [Conversion.PhaseKind] at hk
    no_kind hk
  | carryLoad past hj hI =>
    obtain ⟨pos, -, hev, -⟩ := CarryLoad.event_at hpre hX hg he hσ hI
    have hk := hev.kind_cases
    no_kind hk
  | compute hr past hj hin hI =>
    obtain ⟨rfl, rfl, rfl, h⟩ := hC.arrive hg hr past.state hin hσ hI he
    rcases h with ⟨st, rfl, hgate⟩ | ⟨o, rfl, hgate⟩
    · exact ⟨.loadEmpty st, rfl, ⟨compute_mod hpre hr, rfl, rfl, rfl, hgate⟩,
        hr, _, _, s, past.state, hin, hσ, hI⟩
    · exact ⟨.storeFull o, rfl, ⟨compute_mod hpre hr, rfl, rfl, rfl, hgate⟩,
        hr, _, _, s, past.state, hin, hσ, hI⟩
  | producer hr past hj hen hI =>
    obtain ⟨pos, w, p, x, rfl, hR, hl, hev, -⟩ := Producer.producer_good hpre hX hg hr he hσ hI
    obtain ⟨tt, -, -, rfl, rfl, rfl, rfl, -, h128, ha, hp, -⟩ := Producer.arrive_shape hR hl hev
    refine ⟨.loadFull (Producer.stage tt), rfl,
      ⟨Producer.leader_eq hpre h128, rfl, rfl, rfl, ?_⟩, trivial⟩
    show arrivals (Producer.fullLoc L (g / L.block) (Producer.stage tt)) _ + 1 ≤
      okPolls (Producer.emptyLoc L (g / L.block) (Producer.stage tt)) _
    omega
  | store hr past hj hin hI hW =>
    obtain ⟨t, -, -, -, rfl, hlead, rfl, rfl, rfl, -, -, hgate, -⟩ :=
      Store.empty_arrive_store hpre hX hg he hσ (hI hub)
    exact ⟨.storeEmpty (stageOf t), rfl, ⟨hlead, rfl, rfl, rfl, hgate⟩,
      _, _, s, hj, past.state, hin, hσ, hI hub⟩
  | epilogue past hj hW hI =>
    have hk := Epilogue.kind_in hpre hX hg ⟨_, past.state, past.into⟩ hj he
    no_kind hk

end

/-! ### Polls of an mbarrier -/

/-- **What a poll of mbarrier `b` of the thread's block is**: who polls, the parity (that of
the thread's earlier successful polls of the mbarrier, plus one on an "empty" mbarrier of the
load pipeline or of the store pipeline; 0 on the state mbarrier), and that a successful poll
acquires (on the state mbarrier also that it is the thread's first). -/
@[reducible] def PollFact (L : Launch) (X : Execution) (g k p : Nat) (ok acq : Bool) :
    Bar → Prop
  | .state => p % 2 = 0 ∧
      (ok = true → acq = true ∧
        okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take k) = 0)
  | .loadFull s => g % L.block < 128 ∧
      p % 2 = okPolls ((Bar.loadFull s).loc L (g / L.block)) ((X.tr g).take k) % 2 ∧
      (ok = true → acq = true)
  | .loadEmpty s => g = loadLeader L (g / L.block) ∧
      p % 2 = (okPolls ((Bar.loadEmpty s).loc L (g / L.block)) ((X.tr g).take k) + 1) % 2 ∧
      (ok = true → acq = true)
  | .storeFull o => g = storeLeader L (g / L.block) ∧
      p % 2 = okPolls ((Bar.storeFull o).loc L (g / L.block)) ((X.tr g).take k) % 2 ∧
      (ok = true → acq = true)
  | .storeEmpty o => g % L.block < 128 ∧
      p % 2 = (okPolls ((Bar.storeEmpty o).loc L (g / L.block)) ((X.tr g).take k) + 1) % 2 ∧
      (ok = true → acq = true)

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hC : ComputeOwes P L X)
include hpre hX hC

/-- **Every poll of an mbarrier** is of one of the eleven mbarriers of the thread's own block,
with that mbarrier's facts. -/
theorem poll_fact {k pc q : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait m q ok acq sc⟩) :
    ∃ b : Bar, m = b.loc L (g / L.block) ∧ PollFact L X g k q ok acq b := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s, hσ, hS, hub⟩ := staged hpre hX he (fun _ _ h => by cases h)
  cases hS with
  | startup hI =>
    rcases Startup.wait_startup hpre hX hg he hσ with ⟨-, rfl, rfl, rfl, -, -, hp⟩ | h
    · exact ⟨.state, stateLoc_eq hpre g, rfl, fun _ => ⟨rfl, Startup.okPolls_zero hp⟩⟩
    · exact absurd h hI.inv.not_left
  | conversion past hj hI =>
    obtain ⟨pos, -, -, -, hev⟩ := Conversion.event_at hpre hX hg he hσ hI
    have hk := hev.phaseKind
    simp only [Conversion.PhaseKind] at hk
    no_kind hk
  | carryLoad past hj hI =>
    obtain ⟨pos, -, hev, -⟩ := CarryLoad.event_at hpre hX hg he hσ hI
    have hk := hev.kind_cases
    no_kind hk
  | compute hr past hj hin hI =>
    obtain ⟨rfl, h⟩ := hC.poll hg hr past.state hin hσ hI he
    rcases h with ⟨st, rfl, hpar⟩ | ⟨o, rfl, hpar⟩
    · exact ⟨.loadFull st, rfl, compute_mod hpre hr, hpar, fun _ => rfl⟩
    · exact ⟨.storeEmpty o, rfl, compute_mod hpre hr, hpar, fun _ => rfl⟩
  | producer hr past hj hen hI =>
    obtain ⟨pos, w, p, x, rfl, hR, hl, hev, -⟩ := Producer.producer_good hpre hX hg hr he hσ hI
    obtain ⟨tt, rfl, rfl, rfl, -, h128, hpolls, -, -⟩ := Producer.poll_shape hR hl hev
    refine ⟨.loadEmpty (Producer.stage tt), rfl, Producer.leader_eq hpre h128, ?_,
      fun _ => rfl⟩
    show Producer.par tt % 2 =
      (okPolls (Producer.emptyLoc L (g / L.block) (Producer.stage tt)) _ + 1) % 2
    rw [hpolls]
    simp only [Producer.par]
    omega
  | store hr past hj hin hI hW =>
    obtain ⟨t, -, -, -, rfl, hlead, rfl, -, -, -, hpar, -⟩ :=
      Store.full_poll_store hpre hX hg he hσ (hI hub)
    exact ⟨.storeFull (stageOf t), rfl, hlead, hpar, fun _ => rfl⟩
  | epilogue past hj hW hI =>
    have hk := Epilogue.kind_in hpre hX hg ⟨_, past.state, past.into⟩ hj he
    no_kind hk

end

/-! ### Tensor loads -/

/-- **What a tensor load that completes on mbarrier `b` of the thread's block is**: on the
state mbarrier the load leader's load of 4096 bytes with fewer than 16 predecessors; on the
"full" mbarrier of a load stage the load leader's load at the position, among the 70 loads of
a tile, of its number of predecessors on the mbarrier, after the poll of the stage's "empty"
mbarrier and the arrival on its "full" mbarrier of that use. No load completes on another
mbarrier. -/
@[reducible] def IssueFact (L : Launch) (X : Execution) (g k : Nat) (sp : TensorCopy.Spec) :
    Bar → Prop
  | .state => g = loadLeader L (g / L.block) ∧ TensorTransfer.bytes sp.descriptor = 4096 ∧
      ((X.tr g).take k).countP (issuesTo (Bar.state.loc L (g / L.block))) < 16
  | .loadFull s => g = loadLeader L (g / L.block) ∧
      TensorTransfer.bytes sp.descriptor =
        loadBytes (((X.tr g).take k).countP
          (issuesTo ((Bar.loadFull s).loc L (g / L.block))) % 70) ∧
      ((X.tr g).take k).countP (issuesTo ((Bar.loadFull s).loc L (g / L.block))) / 70 + 1 ≤
        okPolls ((Bar.loadEmpty s).loc L (g / L.block)) ((X.tr g).take k) ∧
      ((X.tr g).take k).countP (issuesTo ((Bar.loadFull s).loc L (g / L.block))) / 70 + 1 ≤
        arrivals ((Bar.loadFull s).loc L (g / L.block)) ((X.tr g).take k)
  | _ => False

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hC : ComputeOwes P L X)
include hpre hX hC

/-- **Every tensor load** completes on the state mbarrier or on the "full" mbarrier of a load
stage of the thread's own block, with that mbarrier's facts, and every byte it writes is a
byte of the union region of that block. -/
theorem issue_fact {k pc al : Nat} {sp : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩) :
    ∃ b : Bar, sp.mbar = b.loc L (g / L.block) ∧ IssueFact L X g k sp b ∧
      ∀ x y z l, TensorCopy.writeLoc sp x y z = some l → InUnion L (g / L.block) l := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s, hσ, hS, hub⟩ := staged hpre hX he (fun _ _ h => by cases h)
  cases hS with
  | startup hI =>
    rcases Startup.issue_startup hpre hX hg he hσ with ⟨j, -, -, rfl, -, -⟩ | h
    · have hm : (Startup.stateSpec P L g j.val).mbar = Bar.state.loc L (g / L.block) :=
        stateLoc_eq hpre g
      rcases Startup.state_issue_startup hpre hX hg he hm hσ with hfact | h
      · refine ⟨.state, hm, hfact, fun x y z l hw => ?_⟩
        obtain ⟨h1, h2, h3, h4⟩ := writeLoc_range (P := P) hw
        have h8 : mapBytes 8 = 4096 := rfl
        have hj := j.isLt
        have hb := hpre.sharedBase
        exact ⟨h1, h2, by omega, by omega⟩
      · exact absurd h hI.inv.not_left
    · exact absurd h hI.inv.not_left
  | conversion past hj hI =>
    obtain ⟨pos, -, -, -, hev⟩ := Conversion.event_at hpre hX hg he hσ hI
    have hk := hev.phaseKind
    simp only [Conversion.PhaseKind] at hk
    no_kind hk
  | carryLoad past hj hI =>
    obtain ⟨pos, -, hev, -⟩ := CarryLoad.event_at hpre hX hg he hσ hI
    have hk := hev.kind_cases
    no_kind hk
  | compute hr past hj hin hI =>
    have hk := hC.kinds hg hr past.state hin hσ hI he
    no_kind hk
  | producer hr past hj hen hI =>
    obtain ⟨pos, w, p, x, rfl, hR, hl, hev, -⟩ := Producer.producer_good hpre hX hg hr he hσ hI
    obtain ⟨tt, i, -, hi, -, -, rfl, h128, hc, hp, ha, -⟩ := Producer.issue_shape hR hl hev
    have hc' : ((X.tr g).take k).countP
        (issuesTo ((Bar.loadFull (Producer.stage tt)).loc L (g / L.block))) =
          70 * (tt / 3) + i := hc
    have hm : (Producer.tileLoad P L g tt i).mbar =
        (Bar.loadFull (Producer.stage tt)).loc L (g / L.block) := by
      rw [Producer.tileLoad, loadSpec_mbar, Producer.fullLoc_eq hpre]
    have hbytes : TensorTransfer.bytes (Producer.tileLoad P L g tt i).descriptor =
        loadBytes i := by
      rw [Producer.tileLoad, loadSpec_bytes]
      exact Producer.mapBytes_eq i hi
    have hmod : (70 * (tt / 3) + i) % 70 = i := by omega
    refine ⟨.loadFull (Producer.stage tt), hm,
      ⟨Producer.leader_eq hpre h128, ?_, ?_, ?_⟩, fun x y z l hw => ?_⟩
    · rw [hc', hmod, hbytes]
    · rw [hc']
      show _ ≤ okPolls (Producer.emptyLoc L (g / L.block) (Producer.stage tt)) _
      omega
    · rw [hc']
      show _ ≤ arrivals (Producer.fullLoc L (g / L.block) (Producer.stage tt)) _
      omega
    · exact InInput.union (Producer.stage tt).isLt (Producer.tileLoad_writeLoc hpre hi hw).1
  | store hr past hj hin hI hW =>
    exact (Store.no_issue_store hpre hX hg he hσ (hI hub)).elim
  | epilogue past hj hW hI =>
    have hk := Epilogue.kind_in hpre hX hg ⟨_, past.state, past.into⟩ hj he
    no_kind hk

/-! ### Tensor stores -/

omit hC in
/-- The kinds of the events of the startup phase, at a state of its invariant. -/
theorem startup_kind {k : Nat} {s : D} {e : Event} (hI : Startup.InvE P X g k s)
    (he : X.get (g, k) = some e) (hσ : At (code L) X g k s) :
    Startup.phaseKind e.kind = true := by
  rcases Startup.event_at hpre hX (Frame.lt_of_get hX he) he hσ with ⟨pos, -, -, hev⟩ | h
  · exact hev.phaseKind
  · exact absurd h hI.inv.not_left

/-- **Every tensor store** is the store leader's; every byte it reads is a byte of the union
region of its block; and it is a store of the Store phase, or (a store of the final state, in
the epilogue) eight `bar.sync 0` precede it. -/
theorem store_fact {k pc al : Nat} {sp : TensorStore.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩) :
    g = storeLeader L (g / L.block) ∧
      (∀ x y z l, TensorStore.readLoc sp x y z = some l → InUnion L (g / L.block) l) ∧
      (InStore P L X g k ∨ bar0Before X (g, k) = 8) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s, hσ, hS, hub⟩ := staged hpre hX he (fun _ _ h => by cases h)
  cases hS with
  | startup hI =>
    have hk := startup_kind hpre hX hI he hσ
    simp [Startup.phaseKind] at hk
  | conversion past hj hI =>
    obtain ⟨pos, -, -, -, hev⟩ := Conversion.event_at hpre hX hg he hσ hI
    have hk := hev.phaseKind
    simp only [Conversion.PhaseKind] at hk
    no_kind hk
  | carryLoad past hj hI =>
    obtain ⟨pos, -, hev, -⟩ := CarryLoad.event_at hpre hX hg he hσ hI
    have hk := hev.kind_cases
    no_kind hk
  | compute hr past hj hin hI =>
    have hk := hC.kinds hg hr past.state hin hσ hI he
    no_kind hk
  | producer hr past hj hen hI =>
    obtain ⟨pos, w, p, x, rfl, hR, hl, hev, -⟩ := Producer.producer_good hpre hX hg hr he hσ hI
    have hk := Producer.ev_kinds hev
    no_kind hk
  | store hr past hj hin hI hW =>
    obtain ⟨pos, hR, hl, hev, -⟩ := Store.store_good hpre hX hg he hσ (hI hub)
    obtain ⟨t, i, rfl, -, rfl⟩ := Store.ev_ts_inv hev
    exact ⟨Store.leader_at hpre hR (by intro h; cases h),
      fun x y z l hrl => (Store.store_store hpre hX hg he hrl hσ (hI hub)).1,
      .inl ⟨_, _, s, hj, past.state, hin, hσ, hI hub⟩⟩
  | epilogue past hj hW hI =>
    have hE : Epilogue.Entered P L X g _ := ⟨_, past.state, past.into⟩
    obtain ⟨i, h160, -, -, -, -, hb⟩ := Epilogue.ts_in hpre hX hg hE hj he
    exact ⟨Epilogue.storeLeader_of hpre h160,
      fun x y z l hrl => (Epilogue.ts_final hpre hX hg hE hj he hrl).2.2, .inr hb⟩

/-! ### Memory accesses and the bfloat16 state copy -/

omit hpre hX hC in
/-- A byte of the union region is no byte of `state_acc`. -/
theorem union_not_acc {c c' : Nat} {l : Loc} (h : InUnion L c l) (h' : InStateAcc L c' l) :
    False := by
  have h1 := h.2.2.1
  have h2 := h'.2.2.2
  omega

/-- **Every memory access of a thread that covers a byte of `state_acc`** of a block is an
access of a thread of that block at a followed state of the Conversion phase, with three
`bar.sync 0` before it, or of the Compute phase, with six. -/
theorem acc_fact {k c : Nat} {a : Acc} {w : Bool} {l : Loc} (hacc : X.Access (g, k) a w)
    (hcov : a.Covers l) (hl : InStateAcc L c l) :
    g < L.threads ∧ c = g / L.block ∧ ∃ s, At (code L) X g k s ∧
      ((bar0Before X (g, k) = 3 ∧ ∃ j0, Conversion.Inv P X g j0 k s) ∨
        (bar0Before X (g, k) = 6 ∧ tid g < 128 ∧ ∃ j0 s0, At (code L) X g j0 s0 ∧
          Compute.In P L X g j0 s0 ∧ Compute.Inv P L X g j0 k s)) := by
  obtain ⟨e, he, hao, hrw⟩ : ∃ e, X.get (g, k) = some e ∧ Frame.AccessOf e a ∧
      ((∃ pc bs, e = ⟨pc, .rd a bs⟩) ∨ ∃ pc bs, e = ⟨pc, .wr a bs⟩) := by
    rcases hacc with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨o, n, pc, he⟩
    · exact ⟨_, he, rfl, .inl ⟨pc, bs, rfl⟩⟩
    · exact ⟨_, he, rfl, .inr ⟨pc, bs, rfl⟩⟩
    · exact absurd he (no_rmw hX)
  have hg := Frame.lt_of_get hX he
  have hb := hpre.sharedBase
  obtain ⟨s, hσ, hS, hub⟩ := staged hpre hX he (by
    rintro pc f rfl
    rcases hrw with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h)
  refine ⟨hg, ?_⟩
  cases hS with
  | startup hI =>
    exfalso
    rcases Startup.touch_startup hpre hX hg he hσ (.inl hao) with
      (⟨i, -, rfl⟩ | ⟨j, -, x, y, z, h | h⟩) | h
    · have h1 : l.space = .global := hcov.1
      rw [hl.1] at h1
      cases h1
    · have h1 : l.space = a.loc.space := hcov.1
      rw [hl.1, Execution.tensor_readLoc_global h] at h1
      cases h1
    · obtain ⟨-, -, h3, -⟩ := writeLoc_range (P := P) h
      have h4 := hcov.2.2.1
      have h5 := hl.2.2.2
      omega
    · exact hI.inv.not_left h
  | conversion past hj hI =>
    obtain ⟨-, h2, h3, -⟩ := Conversion.stateAcc_phase hpre hX hg hσ hI hacc hcov hl
    exact ⟨h2, s, hσ, .inl ⟨h3, _, hI⟩⟩
  | carryLoad past hj hI =>
    exfalso
    obtain ⟨j, rfl, hc⟩ := CarryLoad.touch_carry hpre hX hg he hσ hI (.inl hao)
    obtain ⟨f1, -⟩ := CarryLoad.ldAddr_frame hpre hc j.isLt
    have h4 : CarryLoad.ldAddr P g j.val ≤ l.addr := hcov.2.2.1
    have h5 := hl.2.2.2
    omega
  | compute hr past hj hin hI =>
    obtain ⟨h1, h2⟩ := hC.acc_phase hg hr past.state hin hσ hI hacc hcov hl
    exact ⟨h1, s, hσ, .inr ⟨h2, hr, _, _, past.state, hin, hI⟩⟩
  | producer hr past hj hen hI =>
    exfalso
    obtain ⟨pos, w', p, x, rfl, hR, hl', hev, -⟩ :=
      Producer.producer_good hpre hX hg hr he hσ hI
    have hk := Producer.ev_kinds hev
    rcases hrw with ⟨pc, bs, rfl⟩ | ⟨pc, bs, rfl⟩ <;> no_kind hk
  | store hr past hj hin hI hW =>
    exfalso
    obtain ⟨pos, hR, hl', hev, -⟩ := Store.store_good hpre hX hg he hσ (hI hub)
    rcases hrw with ⟨pc, bs, rfl⟩ | ⟨pc, bs, rfl⟩
    · obtain ⟨t, row, cc, m, -, -, -, rfl, -⟩ := Store.ev_rd_inv hev
      have h4 : P.sharedBase + 4096 * (t % 2) + 16 * row + 86912 + 256 * cc + 4 * m ≤ l.addr :=
        hcov.2.2.1
      have h5 := hl.2.2.2
      omega
    · obtain ⟨t, row, cc, j, -, -, rfl, -⟩ := Store.ev_wr_inv hev
      have h1 : l.space = .global := hcov.1
      rw [hl.1] at h1
      cases h1
  | epilogue past hj hW hI =>
    exfalso
    have hE : Epilogue.Entered P L X g _ := ⟨_, past.state, past.into⟩
    rcases hrw with ⟨pc, bs, rfl⟩ | ⟨pc, bs, rfl⟩
    · exact (Epilogue.no_read hpre hX hg hE hj he).1 a bs rfl
    · exact union_not_acc (Epilogue.wr_final hpre hX hg hE hj he hcov).2.2.1 hl

/-- **No asynchronous operation touches `state_acc`**: a footprint of the operation an event
issues (the bytes a tensor load writes, the bytes a tensor store reads; the kernel issues no
other asynchronous operation into shared memory) covers no byte of `state_acc`. -/
theorem async_not_acc {k c : Nat} {e : Event} {a : Acc} {l : Loc} (he : X.get (g, k) = some e)
    (ha : Frame.AsyncOf e a) (hcov : a.Covers l) (hl : InStateAcc L c l) : False := by
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | tc t => exact Proof.Top.noTc hX (g, k) pc t he
  | tensorStore al sp =>
    obtain ⟨-, x, y, z, h | h⟩ := ha
    · have h1 := ((store_fact hpre hX hC he).2.1 x y z a.loc h).2.2.1
      have h2 := hcov.2.2.1
      have h3 := hl.2.2.2
      omega
    · have h1 : l.space = a.loc.space := hcov.1
      rw [hl.1, Execution.store_writeLoc_global h] at h1
      cases h1
  | tensorIssue al sp =>
    obtain ⟨-, x, y, z, h | h⟩ := ha
    · have h1 : l.space = a.loc.space := hcov.1
      rw [hl.1, Execution.tensor_readLoc_global h] at h1
      cases h1
    · obtain ⟨b, -, -, hw⟩ := issue_fact hpre hX hC he
      have h1 := (hw x y z a.loc h).2.2.1
      have h2 := hcov.2.2.1
      have h3 := hl.2.2.2
      omega
  | tensorPrefetch al sp => exact Proof.Top.noTensorPrefetch hX ⟨pc, he⟩
  | clcIssue sp tg => exact Proof.Top.noClcIssue hX ⟨pc, he⟩
  | copy sp => exact Proof.Top.noCopy hX (g, k) sp ⟨pc, he⟩
  | bulkPrefetch src => exact (noEvents hX).prefetch (g, k) src ⟨pc, he⟩
  | _ => exact ha.elim

end

/-! ### The four contracts, from `ComputeOwes` -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hC : ComputeOwes P L X)
include hpre hX hC

/-- **The thread facts of the state mbarrier** (`Protocol/StateBar.lean`). -/
theorem stateFacts_of : StateFacts L X where
  arrive := by
    intro g i pc tx cnt c rel sc _ he
    obtain ⟨b, hb, hf, -⟩ := arrive_fact hpre hX hC he
    obtain ⟨rfl, rfl⟩ := Bar.loc_inj hb
    exact hf
  issue := by
    intro g i pc al c sp _ he hm
    obtain ⟨b, hb, hf, -⟩ := issue_fact hpre hX hC he
    obtain ⟨rfl, rfl⟩ := Bar.loc_inj (hm.symm.trans hb)
    exact hf
  poll := by
    intro g i pc p c ok acq sc _ he
    obtain ⟨b, hb, hf⟩ := poll_fact hpre hX hC he
    obtain ⟨rfl, rfl⟩ := Bar.loc_inj hb
    exact ⟨rfl, hf⟩

/-- **The thread facts of the load pipeline** (`Protocol/LoadRing.lean`). -/
theorem loadFacts_of : LoadFacts L X where
  full_arrive := by
    intro g i pc tx cnt c s rel sc _ he
    obtain ⟨b, hb, hf, -⟩ := arrive_fact hpre hX hC he
    obtain ⟨rfl, rfl⟩ := Bar.loc_inj hb
    exact hf
  full_issue := by
    intro g i pc al c s sp _ he hm
    obtain ⟨b, hb, hf, -⟩ := issue_fact hpre hX hC he
    obtain ⟨rfl, rfl⟩ := Bar.loc_inj (hm.symm.trans hb)
    exact hf
  full_poll := by
    intro g i pc p c s ok acq sc _ he
    obtain ⟨b, hb, hf⟩ := poll_fact hpre hX hC he
    obtain ⟨rfl, rfl⟩ := Bar.loc_inj hb
    exact ⟨hf.1, rfl, hf.2⟩
  empty_arrive := by
    intro g i pc tx cnt c s rel sc _ he
    obtain ⟨b, hb, hf, -⟩ := arrive_fact hpre hX hC he
    obtain ⟨rfl, rfl⟩ := Bar.loc_inj hb
    exact ⟨hf.1, rfl, hf.2⟩
  empty_poll := by
    intro g i pc p c s ok acq sc _ he
    obtain ⟨b, hb, hf⟩ := poll_fact hpre hX hC he
    obtain ⟨rfl, rfl⟩ := Bar.loc_inj hb
    exact hf
  no_tensor_empty := by
    intro i pc a c s sp he hm
    obtain ⟨g, k⟩ := i
    obtain ⟨b, hb, hf, -⟩ := issue_fact hpre hX hC he
    obtain ⟨rfl, -⟩ := Bar.loc_inj (hm.symm.trans hb)
    exact hf
  in_fence := by
    intro g i e pce tx cnt a w l s rel sc hg hacc hcov hl hie he
    obtain ⟨b, hb, -, hph⟩ := arrive_fact hpre hX hC he
    obtain ⟨rfl, -⟩ := Bar.loc_inj hb
    obtain ⟨hr, j0, s0, se, h0, hin, hσ, hI⟩ := hph
    exact hC.in_fence hg hr h0 hin hσ hI he hacc hcov hl hie

/-- **The thread facts of the store pipeline** (`Protocol/StoreRing.lean`). -/
theorem storeFacts_of : StoreFacts L X where
  full_arrive := by
    intro g i pc tx cnt c o rel sc _ he
    obtain ⟨b, hb, hf, -⟩ := arrive_fact hpre hX hC he
    obtain ⟨rfl, rfl⟩ := Bar.loc_inj hb
    exact ⟨hf.1, rfl, hf.2⟩
  full_poll := by
    intro g i pc p c o ok acq sc _ he
    obtain ⟨b, hb, hf⟩ := poll_fact hpre hX hC he
    obtain ⟨rfl, rfl⟩ := Bar.loc_inj hb
    exact hf
  empty_arrive := by
    intro g i pc tx cnt c o rel sc _ he
    obtain ⟨b, hb, hf, -⟩ := arrive_fact hpre hX hC he
    obtain ⟨rfl, rfl⟩ := Bar.loc_inj hb
    exact hf
  empty_poll := by
    intro g i pc p c o ok acq sc _ he
    obtain ⟨b, hb, hf⟩ := poll_fact hpre hX hC he
    obtain ⟨rfl, rfl⟩ := Bar.loc_inj hb
    exact ⟨hf.1, rfl, hf.2⟩
  no_tensor := by
    intro i pc a c o sp he
    obtain ⟨g, k⟩ := i
    obtain ⟨b, hb, hf, -⟩ := issue_fact hpre hX hC he
    refine ⟨fun hm => ?_, fun hm => ?_⟩
    · obtain ⟨rfl, -⟩ := Bar.loc_inj (hm.symm.trans hb)
      exact hf
    · obtain ⟨rfl, -⟩ := Bar.loc_inj (hm.symm.trans hb)
      exact hf
  out_fence := by
    intro g i e pce tx cnt a w l o rel sc hg hacc hcov hl hie he
    obtain ⟨b, hb, -, hph⟩ := arrive_fact hpre hX hC he
    obtain ⟨rfl, -⟩ := Bar.loc_inj hb
    obtain ⟨hr, j0, s0, se, h0, hin, hσ, hI⟩ := hph
    exact hC.out_fence hg hr h0 hin hσ hI he hacc hcov hl hie
  store_wait := by
    intro c i e pc addr pce tx cnt x y z sp l o rel sc he _ _ hie hee
    have hg := Frame.lt_of_get hX he
    obtain ⟨b, hb, -, hph⟩ := arrive_fact hpre hX hC hee
    obtain ⟨rfl, -⟩ := Bar.loc_inj hb
    obtain ⟨j0e, s0e, se, -, -, -, hσe, hIe⟩ := hph
    rcases (store_fact hpre hX hC he).2.2 with ⟨j0, s0, s, hj, h0, hin, hσ, hI⟩ | h8
    · exact Store.store_wait_store hpre hX hg ⟨s0, h0, hin⟩ hj he hσ hI hie hee hσe hIe
    · exfalso
      obtain ⟨t, -, -, -, -, -, -, -, -, -, -, -, h6⟩ :=
        Store.empty_arrive_store hpre hX hg hee hσe hIe
      have hmono : bar0Before X (storeLeader L c, i) ≤ bar0Before X (storeLeader L c, e) :=
        (List.take_sublist_take_left (Nat.le_of_lt hie)).countP_le
      omega

/-- **The thread facts of the bfloat16 state copy `state_acc`** (`Protocol/Regions.lean`). -/
theorem stateAccFacts_of : StateAccFacts L X where
  thread_only := by
    intro ref a w l c hi hcov hl
    rcases ref with i | ⟨⟨g, k⟩, p⟩
    · exact ⟨i, rfl⟩
    · exfalso
      obtain ⟨e, he, ha⟩ := Frame.asyncFootprint_asyncOf hi.2
      exact async_not_acc hpre hX hC he ha hcov hl
  phase := by
    intro g i a w l c hacc hcov hl
    obtain ⟨hg, hc, s, -, h | h⟩ := acc_fact hpre hX hC hacc hcov hl
    · exact ⟨hg, hc, .inl h.1⟩
    · exact ⟨hg, hc, .inr h.1⟩
  owner := by
    intro g i h j a b w w' l c ha hb hw hca hcb hl heq
    obtain ⟨hg, -, s, hσ, h1 | h1⟩ := acc_fact hpre hX hC ha hca hl <;>
      obtain ⟨hh, -, s', hσ', h2 | h2⟩ := acc_fact hpre hX hC hb hcb hl
    · obtain ⟨-, j0, hI⟩ := h1
      obtain ⟨-, j0', hI'⟩ := h2
      exact Conversion.stateAcc_owner hpre hX hg hh hσ hI hσ' hI' ha hb hca hcb hl
    · have := h1.1
      have := h2.1
      omega
    · have := h1.1
      have := h2.1
      omega
    · obtain ⟨-, hr, j0, s0, h0, hin, hI⟩ := h1
      obtain ⟨-, hr', j0', s0', h0', hin', hI'⟩ := h2
      exact hC.acc_owner hg hr h0 hin hσ hI hh hr' h0' hin' hσ' hI' ha hb hw hca hcb hl

/-- **The contract of the exports layer** (`Protocol/Export.lean: Facts`), from the three
structures of the other half of the fields (barrier events, mbarrier initialization, exits:
`Ref/Assembly/FactsA.lean`). -/
theorem facts_of (hB : BarFacts L X (ctaTiles P)) (hI : InitFacts L X)
    (hLife : LifeFacts L X (ctaTiles P)) : Facts P L X :=
  ⟨hB, hI, loadFacts_of hpre hX hC, storeFacts_of hpre hX hC, stateFacts_of hpre hX hC,
    stateAccFacts_of hpre hX hC, hLife⟩

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.FactsB
