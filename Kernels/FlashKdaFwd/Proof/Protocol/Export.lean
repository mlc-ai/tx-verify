-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Protocol.StoreCover
public import Lemmas.Flow.WriteBytes
public import Lemmas.Flow.NotRmw
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Kernel.Progress.Async
public import Kernels.FlashKdaFwd.Proof.Top.Safety
public import Lemmas.Flow.NotAsyncArrive
public import Lemmas.Flow.NotBulkPrefetch
public import Lemmas.Flow.TensorStoreBase
public import Lemmas.Kernel.Source.LocalOwned
public import Lemmas.Protocol.UnitReachBlocker

@[expose] public section

/-! # What the protocol layer hands to the top skeleton

The top skeleton asks for kernel-specific facts in two structures: `Top.SafetyFacts`
(`Proof/Top/Safety.lean`, the premises of the safety classes) and `Progress.Premises`
(`Proof/Progress/Progress.lean`, the premises of the progress skeleton). This file derives the
fields of the two that belong to the synchronization protocol, from the thread-fact structures
of the protocol layer, bundled as `Facts P L X` (the contract the thread layer's exports have
to meet), from the launch precondition `Pre`, and from scans of the decoded program.

## `SafetyFacts`

| field | here | from |
|---|---|---|
| `mbarInitFirst` | `Facts.mbarInitFirst` | `init`, `bars` |
| `mbarPublished` | `Facts.mbarPublished` | `init`, `bars` |
| `mbarFaultFree` | `Facts.mbarFaultFree` | `init`, `bars`, `load`, `store`, `state` |
| `mbarInitBefore` | `Facts.mbarInitBefore` | `init`, `bars` |
| `sharedOwn` | `Facts.sharedOwn` | `init` and the field `sharedFrame` |
| `asyncFinished` | `Facts.asyncFinished` | all but `stateAcc`, and `sharedFrame` |
| `accOrdered` | `Facts.accOrdered` | `stateAcc`, `bars`, `sharedFrame` |
| `bufOrdered` | `Facts.bufOrdered` | `sharedFrame` and `UnionFacts` (`UnionClass.lean`) |
| `barShape` | `Facts.barShape` | `bars` |
| `wholeBars` | `Facts.wholeBars` | `bars` |

`NoEvents kernel X`, which most of the protocol lemmas take, is proved here from the code
(`noEvents`), so it is no obligation of the thread layer.

`bufOrdered` takes the contract for the union region, `UnionFacts L X (ctaTiles P) O`
(`UnionClass.lean`: the classification of every access of offsets 32768 to 98304, for four
functions `O` that name the writer of a byte). It is kept apart from `Facts` because of the
parameter `O`. `UnionFacts.ordered` is the case split over the classes.

The field `mbarFrame` of `SafetyFacts` also follows from the contract (`mbar_bar`: an event
that names an mbarrier names `b.loc L (g / L.block)` for one of the eleven `b : Bar`); it is
not restated here because its address form (`P.sharedBase + 98304 + 8 * j`) is one unfolding of
`Bar.loc` and `Bar.off` away.

## `Premises` (progress)

* `barGroup`: `barGroup` here, for a relation `G` with `G 0 w` for `w < 6` and `G 8 w` for
  `w < 4`.
* `barLag`, the half "has not exited": `barLag_not_exited` here, for `G 8 w → w < 4`. The half
  "is no later" is about the time table (a thread with at most `n` arrivals on a barrier is at
  a state no later than the state of an arrival with `n` earlier ones) and is not derived.
* `pollState`: `Facts.pollState_of_owner`, `Facts.pollState`, `Facts.pollState_of_two` here;
  see below.
* `pollBlk`: the count-level blockers; see below.
* `tensorSources`: not derived. It is about the route, the descriptor and the global source
  bytes of each load (thread layer and `Pre`); nothing of the protocol.
* `storeSources`: `Facts.storeSources` here, in the type of the field's conclusion, from
  `UnionFacts` and `StoreCover` (`StoreCover.lean`: every byte a store reads lies in the union
  region; a compute thread has written its bytes of an output buffer at its arrival on
  `storeFull`, and its bytes of the final state at its eighth `bar.sync 0`; the write event of
  a `stmatrix` lane carries 16 bytes). That every other write event carries as many bytes as
  its footprint and that there is no atomic are scans of the code (`write_length`, `no_rmw`).
* `coll.released`: no part of the protocol layer. It is about warp collectives (shuffles,
  elections), which no mbarrier and no barrier of this file orders.

`pollState` asks for a state of the polled barrier at a *poll state* of the thread machine.
`Facts.pollState_of_owner` gives it from the count of `bar.sync 0` of the barrier's owner (the
thread that initializes it), `Facts.pollState` from the count of the polling thread `g` itself
(`b.gen + 1 ≤` its `bar.sync 0`) together with the hypothesis that the `bar.sync 0` with
`b.gen` earlier ones is not the last event of `g`, and `Facts.pollState_of_two` from
`b.gen + 2 ≤` the count of `g`, which covers every poll of the ten pipeline barriers. The extra
hypothesis of `Facts.pollState` cannot be dropped: at its first visit of the poll of the state
barrier (384) a thread's last event is its third `bar.sync 0` (379), and that the load leader
has arrived at that barrier, hence has initialized the state barrier, follows only from the
release of the barrier (`Step.Released`), which the field `pollState` does not have among its
hypotheses although its one use (`poll_steps`) has it in scope.

`pollBlk` concludes `Blk M X g`, a statement about the time table. The protocol layer gives
the count-level half: when the polled barrier's phase has the parity at which the poll fails,
which thread or which asynchronous operation the poll waits for.

* `loadFull s`, `LoadFacts.full_blocked`: the load leader's arrival of the use, or a load of
  the use that has not notified.
* `loadEmpty s`, `LoadFacts.empty_blocked`: a compute thread with fewer arrivals than the
  phase.
* `storeFull o`, `StoreFacts.full_blocked`: a compute thread with fewer arrivals than the
  phase.
* `storeEmpty o`, `StoreFacts.empty_blocked`: the store leader's arrival.
* `state`, `StateFacts.short`: the load leader's arrival, or one of the 16 loads.

Each takes the parity hypothesis in terms of the thread's count of successful polls
(`LoadFacts.full_poll` and its siblings give the parity of a poll event from that count, in the
execution `Y` of `pollBlk`). Turning "thread `y` has fewer arrivals than the phase" into
`Blk M X g` needs the time table (`y` is pending at an earlier time). -/

namespace PTX.Kernels.FlashKdaFwd.Protocol
open PTX PTX.Flow PTX.Frame AsyncCopy MBarrier Recurrence

/-- The number of tiles of CTA `c`: the tiles of the sequence `c % N` it works on
(`Top.tilesOf P L g` is `ctaTiles P (g / L.block)`). -/
def ctaTiles (P : Params) (c : Nat) : Nat := tiles (P.length (c % P.sequences))

/-- **The contract of the exports layer**: the thread-fact structures of the protocol layer,
for one execution. `Proof/Thread` has to prove this for every consistent execution. -/
structure Facts (P : Params) (L : Launch) (X : Execution) : Prop where
  /-- Barrier events (`Bars.lean`). -/
  bars : BarFacts L X (ctaTiles P)
  /-- Initialization and use of the mbarriers (`Init.lean`). -/
  init : InitFacts L X
  /-- The load pipeline (`LoadRing.lean`). -/
  load : LoadFacts L X
  /-- The store pipeline (`StoreRing.lean`). -/
  store : StoreFacts L X
  /-- The state barrier (`StateBar.lean`). -/
  state : StateFacts L X
  /-- The bf16 state copy `state_acc` (`Regions.lean`). -/
  stateAcc : StateAccFacts L X
  /-- Exits (`Life.lean`). -/
  life : LifeFacts L X (ctaTiles P)

variable {P : Params} {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {X : Execution} {T : Nat → Nat}

/-! ## The absent kinds, from the code -/

private theorem noAsyncArriveCode :
    kernel.code.all (fun ins => !asyncArriveOp ins.op) = true := by decide +kernel

private theorem noBulkPrefetchCode :
    kernel.code.all (fun ins => !bulkPrefetchOp ins.op) = true := by decide +kernel

/-- **`NoEvents` holds for the kernel**: every field is one scan of the decoded program
(`Proof/Top/Static.lean`, and two scans here). -/
theorem noEvents (hX : Consistent L kernel A mem0 X) : NoEvents kernel X where
  inval := Proof.Top.noMbarInval hX
  asyncArrive := fun _ _ _ ⟨_, he⟩ =>
    no_kind_of_code hX asyncArriveOp (fun k => ∃ m n, k = .asyncArrive m n)
      (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => fires_asyncArrive_op hf hk)
      noAsyncArriveCode he ⟨_, _, rfl⟩
  copy := Proof.Top.noCopy hX
  tc := Proof.Top.noTc hX
  prefetch := fun _ _ ⟨_, he⟩ =>
    no_kind_of_code hX bulkPrefetchOp (fun k => ∃ a, k = .bulkPrefetch a)
      (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_bulkPrefetch_op hf hk)
      noBulkPrefetchCode he ⟨_, rfl⟩
  clc := fun _ _ _ h => Proof.Top.noClcIssue hX h
  spins := fun _ _ _ _ _ _ h => Proof.Top.poll_canonical hX h

private theorem sizedWriteCode :
    OpPcsFast kernel.code (fun op => !sizedWrite op) stmatrixPcs = true := by
  decide +kernel

private theorem noAtomicCode : kernel.code.all (fun ins => !atomicOp ins.op) = true := by
  decide +kernel

/-- **A write event carries as many bytes as its footprint**: for every write instruction but
the 18 `stmatrix` this is a property of the instruction (the scan `sizedWriteCode`); for a
`stmatrix` lane it is the field `matrix_len` of `StoreCover`. -/
theorem write_length {O : Owners} (hX : Consistent L kernel A mem0 X) (C : StoreCover L X O)
    {e : EvId} {pc : Nat} {a : Acc} {bs : List Byte} (he : X.get e = some ⟨pc, .wr a bs⟩) :
    bs.length = a.size := by
  rcases get_source hX he with ⟨_, hu⟩ | ⟨t, ins, o, -, hcode, hf⟩
  · cases hu
  cases hs : sizedWrite ins.op
  · obtain ⟨g, i⟩ := e
    exact C.matrix_len he (OpPcsFast.mem sizedWriteCode hcode (by simp [hs]))
  · exact fires_write_length hf rfl hs

/-- **The kernel has no atomic instruction.** -/
theorem no_rmw (hX : Consistent L kernel A mem0 X) {e : EvId} {pc : Nat} {a : Acc}
    {o : List (Option Byte)} {n : Option (List Byte)} :
    X.get e ≠ some ⟨pc, .rmw a o n⟩ := fun he =>
  no_kind_of_code hX atomicOp (fun k => ∃ a o n, k = .rmw a o n)
    (fun _ ⟨_, _, _, h⟩ => by cases h) (fun hf ⟨_, _, _, hk⟩ => fires_rmw_op hf hk)
    noAtomicCode he ⟨_, _, _, rfl⟩

/-! ## The mbarrier objects -/

section mbar
variable (hI : InitFacts L X) (hB : BarFacts L X T) (hX : Consistent L K A mem0 X)
  (hb : L.block = 192)
include hI hX hb

omit hb in
/-- An event that names an mbarrier names one of the eleven barriers of its thread's CTA. -/
theorem mbar_bar {g k : Nat} {ev : Event} {m : Loc} (hget : X.get (g, k) = some ev)
    (hm : MbarOf ev m) : ∃ b : Bar, m = b.loc L (g / L.block) := by
  have hg := Frame.lt_of_get hX hget
  by_cases hi : ∃ n, ev.kind = .mbInit m n
  · obtain ⟨n, hn⟩ := hi
    obtain ⟨pc, kd⟩ := ev
    simp only at hn
    subst hn
    obtain ⟨b, hmb, -⟩ := hI.init_ev hg hget
    exact ⟨b, hmb⟩
  · push Not at hi
    obtain ⟨b, hmb, -⟩ := hI.use_ev hg hget hm hi
    exact ⟨b, hmb⟩

/-- **Every mbarrier object with a record is one of the eleven barriers of a CTA.** -/
theorem object_bar {m : Loc} {r : Record Ref} (hr : r ∈ X.objects m) :
    ∃ (b : Bar) (c : Nat), c < L.grid ∧ m = b.loc L c := by
  obtain ⟨ev, hget, hm, -⟩ := ObjectInit.record_issuer hX hr
  rcases hiss : r.id.issuer with ⟨g, k⟩
  rw [hiss] at hget
  obtain ⟨b, hmb⟩ := mbar_bar hI hX hget hm
  exact ⟨b, _, cta_lt hb (Frame.lt_of_get hX hget), hmb⟩

include hB

/-- **`SafetyFacts.mbarInitFirst`.** -/
theorem mbarInitFirst : ∀ m, X.objects m ≠ [] → ∃ c, PairTmaRing.InitFirst X m c := by
  intro m hne
  obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨b, c, -, rfl⟩ := object_bar hI hX hb hr
  exact ⟨b.count, hI.initFirst hB hX hb c b⟩

/-- **`SafetyFacts.mbarPublished`.** -/
theorem mbarPublished : ∀ m e c, X.MbInit e m c → ∀ s ∈ X.objects m,
    (∀ n, s.action ≠ .init n) → InitPublished L X e s.id.issuer m := by
  intro m e c he s hs hn
  obtain ⟨ev', hget', hm', hnot⟩ := ObjectInit.record_issuer hX hs
  rcases hiss' : s.id.issuer with ⟨g', k'⟩
  rw [hiss'] at hget'
  have hni : ∀ n, ev'.kind ≠ .mbInit m n := fun n hc' =>
    (hnot ⟨n, hc'⟩).elim fun n' hn' => hn n' hn'
  obtain ⟨b', i, hmb, ⟨pci, hi⟩, hbc⟩ := hI.published hB hX hb hget' hm' hni
  subst hmb
  obtain rfl := (hI.init_site hX he i pci _ hi).1
  exact .inl hbc

/-- **`SafetyFacts.mbarInitBefore`.** -/
theorem mbarInitBefore : ∀ e m, X.UsesMbar e m → (∀ count, ¬ X.MbInit e m count) →
    ∃ i count, X.MbInit i m count ∧ baseCausality L X i e := by
  rintro ⟨g, k⟩ m hu hni
  obtain ⟨e, he, hm⟩ := usesMbar_mbarOf hu
  obtain ⟨b, i, -, hinit, hbc⟩ := hI.published hB hX hb he hm (usesMbar_not_init he hni)
  exact ⟨i, _, hinit, hbc⟩

/-- **`SafetyFacts.mbarFaultFree`** (for every record, initializations included). -/
theorem mbarFaultFree (hLd : LoadFacts L X) (hSt : StoreFacts L X) (hS : StateFacts L X)
    (hN : NoEvents K X) : ∀ m r, r ∈ X.objects m → r.fault = none := by
  intro m r hr
  obtain ⟨b, c, hc, rfl⟩ := object_bar hI hX hb hr
  cases b with
  | loadFull s => exact hLd.full_faultFree hI hB hN hX hb hc s r hr
  | loadEmpty s => exact hLd.empty_faultFree hI hB hN hX hb hc s r hr
  | storeFull o => exact hSt.full_faultFree hI hB hN hX hb hc o r hr
  | storeEmpty o => exact hSt.empty_faultFree hI hB hN hX hb hc o r hr
  | state => exact hS.faultFree hI hB hN hX hb hc r hr

end mbar

/-! ## The shared-memory lifetime -/

/-- A tensor store's source is in its issuer's CTA (generic: the instruction's source operand
is a shared address of the executing thread). -/
theorem store_own (hX : Consistent L K A mem0 X) {i : EvId} {a : Nat} {s : TensorStore.Spec}
    (h : X.TensorStoreIssue i a s) : s.sharedBase.cta = i.1 / L.block := by
  obtain ⟨pc, he⟩ := h
  rcases get_source hX he with ⟨_, hi⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hi
  · exact fires_tensorStore_base hf rfl

/-- A tensor load's destination is shared memory (generic: the route check of the
instruction). -/
theorem load_space (hX : Consistent L K A mem0 X) {i : EvId} {a : Nat} {s : TensorCopy.Spec}
    (h : X.TensorIssue i a s) : s.sharedBase.space = .shared := by
  obtain ⟨pc, he⟩ := h
  rcases get_source hX he with ⟨_, hi⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hi
  · exact fires_tensorIssue_base hf

/-- **`SafetyFacts.sharedOwn`**: every use of shared memory is of the issuer's own CTA.
`hframe` is the first part of the field `sharedFrame` (every access of shared memory, by a
thread or by a stage of an asynchronous operation, is to the issuer's CTA); the mbarrier
operands are of the issuer's CTA by `InitFacts`; the other kinds of use need an instruction the
kernel does not have. -/
theorem sharedOwn (hI : InitFacts L X) (hN : NoEvents K X) (hX : Consistent L K A mem0 X)
    (hframe : ∀ e a, X.MemTouches e a → a.loc.space = .shared →
      a.loc.cta = e.issuer.1 / L.block) :
    ∀ e c, SharedUse L X e c → c = e.issuer.1 / L.block := by
  intro e c huse
  have hmb : ∀ {i : EvId} {ev : Event} {l : Loc}, X.get i = some ev → MbarOf ev l →
      l.cta = i.1 / L.block := by
    rintro ⟨g, k⟩ ev l he hm
    obtain ⟨b, rfl⟩ := mbar_bar hI hX he hm
    rfl
  rcases huse with ⟨hpres, ⟨a, w, hint, hsp, hcta⟩ | ⟨addr, act, hact⟩⟩ |
      ⟨i, s, rfl, hc, -⟩ | ⟨i, address, s, x, y, k, rfl, hi, hsl, hcta⟩ |
      ⟨i, address, s, rfl, hi, hcta⟩ | ⟨i, q, rfl, hfin, hsu⟩
  · exact hcta ▸ hframe e a (.inl ⟨w, hint⟩) hsp
  · have hsrc := objectAction_source
      (r := (⟨e, act, { state := none }, none⟩ : Record Ref)) hact
    have key : ∃ ev, X.get e.issuer = some ev ∧ MbarOf ev ⟨.shared, c, addr⟩ := by
      cases hsrc with
      | init hid he _ | inval hid he _ | arrive hid he _ | wait hid he _
      | increment hid he _ =>
        simp only at hid
        subst hid
        exact ⟨_, he, rfl⟩
      | tensor hid he hm _ =>
        simp only at hid
        subst hid
        exact ⟨_, he, hm⟩
      | arriveOn _ he _ _ _ => exact (hN.asyncArrive _ _ _ ⟨_, he⟩).elim
      | bulk _ he _ _ _ => exact (hN.copy _ _ ⟨_, he⟩).elim
      | commit _ he _ _ => exact (hN.commit _ _ ⟨_, he⟩).elim
      | clc _ he _ _ _ => exact (hN.clc _ _ _ ⟨_, he⟩).elim
    obtain ⟨ev, he, hm⟩ := key
    exact hmb he hm
  · exact (hN.commit _ _ hc).elim
  · -- a byte write of a load: its footprint is an access of shared memory
    obtain ⟨slot, hslot⟩ := Option.isSome_iff_exists.mp hsl
    have hfp : X.Intent (.async i (.write (.load x y k)))
        { loc := s.sharedLoc slot, size := 1 } true :=
      ⟨rfl, s, address, hi, by simp [TensorCopy.writeLoc, hslot], rfl⟩
    have := hframe _ _ (.inl ⟨_, hfp⟩) (load_space hX hi)
    rw [← hcta]
    exact this
  · rw [← hcta]
    exact store_own hX hi
  · rcases hfin with ⟨s, l, hcopy, -⟩ | ⟨s, hcopy, -⟩ | ⟨l, noinc, harr, -⟩ | ⟨-, rfl⟩ |
        ⟨s, tg, c', hcl, -⟩ | ⟨a, s, -, rfl⟩ | ⟨a, s, -, rfl⟩ | ⟨s, rank, l, hcm, -⟩
    · exact (hN.copy _ _ hcopy).elim
    · exact (hN.copy _ _ hcopy).elim
    · exact (hN.asyncArrive _ _ _ harr).elim
    · rcases hsu with ⟨d, s, acc, mask, ⟨pc, he⟩, -⟩ | ⟨cp, ⟨pc, he⟩, -⟩
      · exact (hN.tc _ _ _ he).elim
      · exact (hN.tc _ _ _ he).elim
    · exact (hN.clc _ _ _ hcl).elim
    · obtain ⟨address, s, ⟨pc, he⟩, -, hcta⟩ := hsu
      rw [← hcta]
      exact hmb he rfl
    · exact hsu.elim
    · exact (hN.commit _ _ hcm).elim

/-! ## The two data regions -/

/-- **`SafetyFacts.accOrdered`**: every conflict on the bf16 state copy is ordered. `hframe`: a
part of the field `sharedFrame` (no access of shared memory starts below the window). -/
theorem accOrdered (hA : StateAccFacts L X) (hB : BarFacts L X T)
    (hX : Consistent L K A mem0 X) (hb : L.block = 192)
    (hframe : ∀ e a, X.MemTouches e a → a.loc.space = .shared → L.sharedBase ≤ a.loc.addr) :
    ConflictsOrdered L X fun l => l.space = .shared ∧ l.addr < L.sharedBase + 32768 := by
  intro e f a b l hconf ha hb' hl
  obtain ⟨hsp, hlt⟩ := hl
  obtain ⟨-, we, wf, hie, -, -, -⟩ := id hconf
  obtain ⟨h1, -, h3, -⟩ := id ha
  have hlo := hframe e a (.inl ⟨we, hie⟩) (h1.symm.trans hsp)
  exact hA.ordered hB hX hb l.cta e f a b l hconf ha hb'
    (show l.space = .shared ∧ l.cta = l.cta ∧ L.sharedBase + 0 ≤ l.addr ∧
      l.addr < L.sharedBase + 32768 from ⟨hsp, rfl, by omega, hlt⟩)

/-- **`SafetyFacts.bufOrdered`**: every conflict on the buffer region is ordered, from the
order of each CTA's union region (`hun`; `Regions.unionOrdered` gives it from a classification
of the accesses into epochs, see `Union.lean`). `hframe`: a part of the field `sharedFrame` (no
access of shared memory ends behind the data part of the window). -/
theorem bufOrdered (hun : ∀ c, ConflictsOrdered L X (InUnion L c))
    (hframe : ∀ e a, X.MemTouches e a → a.loc.space = .shared →
      a.loc.addr + a.size ≤ L.sharedBase + 98304) :
    ConflictsOrdered L X fun l => l.space = .shared ∧ L.sharedBase + 32768 ≤ l.addr := by
  intro e f a b l hconf ha hb' hl
  obtain ⟨hsp, hlo⟩ := hl
  obtain ⟨-, we, wf, hie, -, -, -⟩ := id hconf
  obtain ⟨h1, -, -, h4⟩ := id ha
  have hhi := hframe e a (.inl ⟨we, hie⟩) (h1.symm.trans hsp)
  exact hun l.cta e f a b l hconf ha hb'
    (show l.space = .shared ∧ l.cta = l.cta ∧ L.sharedBase + 32768 ≤ l.addr ∧
      l.addr < L.sharedBase + 98304 from ⟨hsp, rfl, hlo, by omega⟩)

/-! ## The barrier schedule -/

/-- The positions of `bar.sync 0` that `Top.barSchedule` reads off the code are `bar0Pcs`. -/
theorem wholeBarPcs_eq : Proof.Top.wholeBarPcs = bar0Pcs := by decide +kernel

/-- The one named barrier is at 2913. -/
theorem namedBarPcs_eq : Proof.Top.namedBarPcs = [2913] := by decide +kernel

/-- Every `bar.sync 0` is an aligned instruction. -/
theorem bar0Pcs_aligned : bar0Pcs.all kernel.alignedAt = true := by decide +kernel

/-- The number of `bar.sync 0` among the first `n` barrier events of a thread: all of them for
a thread of the load or store warp; for a compute thread the first six, then none for `T`
events (the named barriers of the tiles), then all again. -/
def bar0Count (compute : Bool) (T n : Nat) : Nat :=
  if compute = true then (if n ≤ 6 then n else if n ≤ 6 + T then 6 else n - T) else n

theorem bar0Count_succ (cb : Bool) (T n : Nat) :
    bar0Count cb T (n + 1) =
      bar0Count cb T n + (if cb = true ∧ 6 ≤ n ∧ n < 6 + T then 0 else 1) := by
  cases cb
  · simp [bar0Count]
  · simp only [bar0Count, true_and, ite_true]
    split_ifs <;> omega

/-- **A thread's `bar.sync 0` count from its barrier count**, by the schedule. -/
theorem BarFacts.bar0_count (hB : BarFacts L X T) {g : Nat} (hg : g < L.threads) (k : Nat) :
    ((X.tr g).take k).countP (Execution.isBarId 0) =
      bar0Count (decide (g % L.block < 128)) (T (g / L.block))
        (((X.tr g).take k).countP Execution.isBar) := by
  induction k with
  | zero => simp [bar0Count]
  | succ k ih =>
    rw [List.take_add_one]
    cases hk : (X.tr g)[k]? with
    | none => simpa using ih
    | some e =>
      obtain ⟨pc, kd⟩ := e
      simp only [Option.toList_some, List.countP_append, List.countP_singleton]
      by_cases hbar : ∃ id cnt mode, kd = .bar id cnt mode
      · obtain ⟨id, cnt, mode, rfl⟩ := hbar
        have hget : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩ := hk
        have hs := hB.sched hg hget
        unfold barSched at hs
        have hisBar : Execution.isBar ⟨pc, .bar id cnt mode⟩ = true := rfl
        rw [hisBar, ite_eq_left rfl, bar0Count_succ, ← ih]
        split_ifs at hs with hc
        · cases hs
          rw [ite_eq_left hc]
          rfl
        · cases hs
          rw [ite_eq_right hc]
          rfl
      · have h1 : Execution.isBar ⟨pc, kd⟩ = false := by
          cases kd <;> first | rfl | exact absurd ⟨_, _, _, rfl⟩ hbar
        have h2 : Execution.isBarId 0 ⟨pc, kd⟩ = false := by
          cases kd <;> first | rfl | exact absurd ⟨_, _, _, rfl⟩ hbar
        simp [h1, h2, ih]

/-- **`SafetyFacts.barShape`**: every barrier event is at the position and has the id and
count of `Top.barSchedule`. -/
theorem barShape (hB : BarFacts L X (ctaTiles P)) (hX : Consistent L K A mem0 X) :
    ∀ g k pc id cnt mode, X.get (g, k) = some ⟨pc, .bar id cnt mode⟩ →
      (pc, id, cnt) =
        Proof.Top.barSchedule P L g (((X.tr g).take k).countP Execution.isBar) := by
  intro g k pc id cnt mode he
  have hg := Frame.lt_of_get hX he
  have hs := hB.sched hg he
  have hcnt := hB.bar0_count hg k
  unfold barSched at hs
  unfold Proof.Top.barSchedule
  change _ = if g % L.block < 128 then
    (if _ < 6 then _ else if _ < 6 + ctaTiles P (g / L.block) then _ else
      (Proof.Top.wholeBarPcs.getD (_ - ctaTiles P (g / L.block)) 0, 0, none)) else _
  generalize ((X.tr g).take k).countP Execution.isBar = n at hs hcnt ⊢
  split_ifs at hs with hc
  · cases hs
    obtain ⟨hcomp, h6, hlt⟩ := hc
    rw [ite_eq_left (of_decide_eq_true hcomp), ite_eq_right (by omega), ite_eq_left hlt,
      hB.bar8_pc hg he, namedBarPcs_eq]
    rfl
  · cases hs
    have hpc := hB.bar0_pc hg he
    unfold bar0Before at hpc
    simp only at hpc
    rw [hcnt] at hpc
    have hget : ∀ i, bar0Pcs[i]? = some pc → Proof.Top.wholeBarPcs.getD i 0 = pc := by
      intro i hi
      rw [wholeBarPcs_eq, List.getD_eq_getElem?_getD, hi]
      rfl
    by_cases hcomp : g % L.block < 128
    · have hd : decide (g % L.block < 128) = true := decide_eq_true hcomp
      rw [hd] at hpc hc
      simp only [bar0Count, ite_true] at hpc
      rw [ite_eq_left hcomp]
      by_cases h6 : n < 6
      · rw [ite_eq_left h6]
        rw [ite_eq_left (by omega)] at hpc
        rw [hget _ hpc]
      · have hT : ¬ n < 6 + ctaTiles P (g / L.block) := fun h => hc ⟨rfl, by omega, h⟩
        rw [ite_eq_right h6, ite_eq_right hT]
        have : (if n ≤ 6 then n else if n ≤ 6 + ctaTiles P (g / L.block) then 6
            else n - ctaTiles P (g / L.block)) = n - ctaTiles P (g / L.block) := by
          split_ifs <;> omega
        rw [this] at hpc
        rw [hget _ hpc]
    · have hd : decide (g % L.block < 128) = false := decide_eq_false hcomp
      rw [hd] at hpc
      simp only [bar0Count, Bool.false_eq_true, ite_false] at hpc
      rw [ite_eq_right hcomp, hget _ hpc]

/-- On the events of a launched thread, "aligned barrier of the whole CTA" is
"`bar.sync 0`". -/
theorem BarFacts.aligned_eq (hB : BarFacts L X T) {g : Nat} (hg : g < L.threads) {e : Event}
    (he : e ∈ X.tr g) : kernel.isAlignedCtaBar e = Execution.isBarId 0 e := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
  obtain ⟨pc, kd⟩ := e
  by_cases hbar : ∃ id cnt mode, kd = .bar id cnt mode
  · obtain ⟨id, cnt, mode, rfl⟩ := hbar
    have hget : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩ := hk
    obtain ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl, -⟩⟩ := hB.shape hg hget
    · have hmem : pc ∈ bar0Pcs := List.mem_of_getElem? (hB.bar0_pc hg hget)
      have hal := List.all_eq_true.mp bar0Pcs_aligned pc hmem
      simp [Kernel.isAlignedCtaBar, Execution.isBarId, hal]
    · simp [Kernel.isAlignedCtaBar, Execution.isBarId]
  · cases kd <;> first | rfl | exact absurd ⟨_, _, _, rfl⟩ hbar

/-- **`SafetyFacts.wholeBars`**: a thread arrives at most nine times on the whole-CTA barrier,
and nine times if it exits. -/
theorem wholeBars (hB : BarFacts L X T) (hX : Consistent L K A mem0 X) :
    ∀ g, (X.tr g).countP kernel.isAlignedCtaBar ≤ 9 ∧
      ∀ j pc, X.get (g, j) = some ⟨pc, .exit⟩ → (X.tr g).countP kernel.isAlignedCtaBar = 9 := by
  intro g
  by_cases hg : g < L.threads
  · have heq : (X.tr g).countP kernel.isAlignedCtaBar =
        (X.tr g).countP (Execution.isBarId 0) :=
      List.countP_congr fun e he => by rw [hB.aligned_eq hg he]
    rw [heq]
    exact ⟨hB.bar0_le hg, fun j pc hx => hB.bar0_exit hg hx⟩
  · have hnil : X.tr g = [] := hX.outside g (by omega)
    refine ⟨by simp [hnil], fun j pc hx => ?_⟩
    simp [Execution.get, hnil] at hx

/-! ## Progress: barriers -/

/-- **`Premises.barGroup`**: the participant warps of a barrier event's barrier, for a relation
`G` that holds of warps 0 to 5 for barrier 0 and of warps 0 to 3 for barrier 8. -/
theorem barGroup (hB : BarFacts L X T) (hb : L.block = 192) {G : Nat → Nat → Prop}
    (hG0 : ∀ w < 6, G 0 w) (hG8 : ∀ w < 4, G 8 w) {g i pc id : Nat} {cnt : Option Nat}
    {m : BarMode} (hg : g < L.threads) (he : X.get (g, i) = some ⟨pc, .bar id cnt m⟩) :
    ∃ p : Finset Nat, NamedBar.Shape L cnt p id ∧ NamedBar.Sources L X cnt p id ∧
      ∀ w ∈ p, G id w := by
  obtain ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl, -⟩⟩ := hB.shape hg he
  · exact ⟨Finset.range 6, shape0 hb, hB.sources0 hb,
      fun w hw => hG0 w (Finset.mem_range.mp hw)⟩
  · exact ⟨Finset.range 4, shape8 hb, hB.sources8, fun w hw => hG8 w (Finset.mem_range.mp hw)⟩

/-- **The first half of `Premises.barLag`**: a participant that has made no more arrivals on a
barrier than thread `g` had made before its arrival at `j` has not exited (an exited thread has
made all nine `bar.sync 0`, and all its named barriers). `hpart`: a participant of the named
barrier is a compute thread. -/
theorem barLag_not_exited (hB : BarFacts L X T) {g y j pc id : Nat} {cnt : Option Nat}
    (hg : g < L.threads) (hy : y < L.threads) (hcta : y / L.block = g / L.block)
    (hpart : id = 8 → y % L.block < 128)
    (he : X.get (g, j) = some ⟨pc, .bar id cnt .sync⟩)
    (hle : (X.tr y).countP (Execution.isBarId id) ≤
      ((X.tr g).take j).countP (Execution.isBarId id)) :
    ∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩ := by
  intro k pc' hx
  have hlt : ((X.tr g).take j).countP (Execution.isBarId id) + 1 ≤
      (X.tr g).countP (Execution.isBarId id) := by
    have h1 := countP_take_succ (p := Execution.isBarId id) he (by simp [Execution.isBarId])
    have h2 := (List.take_sublist (j + 1) (X.tr g)).countP_le (p := Execution.isBarId id)
    omega
  obtain ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl, hcomp⟩⟩ := hB.shape hg he
  · have h1 := hB.bar0_exit hy hx
    have h2 := hB.bar0_le hg
    omega
  · have h1 := hB.bar8_exit hy (hpart rfl) hx
    have h2 := hB.bar8_le hg hcomp
    rw [hcta] at h1
    omega

/-! ## Progress: the state of a polled barrier -/

/-- **A barrier whose history has a record has a state** (the conclusion of
`Premises.pollState`). -/
theorem bar_state (hI : InitFacts L X) (hB : BarFacts L X T) (hN : NoEvents K X)
    (hX : Consistent L K A mem0 X) (hb : L.block = 192) (c : Nat) (b : Bar)
    (hne : X.objects (b.loc L c) ≠ []) :
    ∃ st, stateBefore (X.objects (b.loc L c)) (X.objects (b.loc L c)).length = some st :=
  MbarRing.Unit.final_of_init hX (hI.initFirst hB hX hb c b)
    (objects_noInval hX.tma.2.2.1 (fun e m => hN.inval e m) _) hne

/-- **Once its owner has executed the publishing `bar.sync 0`, a barrier has a record**: the
owner initialized it before that barrier. -/
theorem objects_ne_nil_of_owner (hI : InitFacts L X) (hB : BarFacts L X T)
    (hX : Consistent L K A mem0 X) {c : Nat} (hc : c < L.grid) (b : Bar)
    (hgen : b.gen + 1 ≤ (X.tr (b.owner L c)).countP (Execution.isBarId 0)) :
    X.objects (b.loc L c) ≠ [] := by
  have hgen' : b.gen + 1 ≤ ((X.tr (b.owner L c)).take
      (X.tr (b.owner L c)).length).countP (Execution.isBarId 0) := by rwa [List.take_length]
  obtain ⟨i, pc, -, hbar, hord⟩ := hB.nth_bar0 hX hgen'
  obtain ⟨j, pcj, -, hinit⟩ := hI.init_done b hc hbar hord
  have hact : objectAction X X.async (b.loc L c) (Ref.thread (b.owner L c, j)) =
      some (.init b.count) := by simp [objectAction, hinit]
  obtain ⟨r, hr, -⟩ := (hX.tma.2.2.1 (b.loc L c)).2.2 _ _ hact
  exact List.ne_nil_of_mem hr

/-! ## The fields of `Top.SafetyFacts`, from the contract -/

namespace Facts

variable (F : Facts P L X) (hP : Pre P L mem0)
  (hX : Consistent L kernel Assumptions.all mem0 X)
include F hP hX

/-- `SafetyFacts.mbarInitFirst`. -/
theorem mbarInitFirst : ∀ m, X.objects m ≠ [] → ∃ c, PairTmaRing.InitFirst X m c :=
  Protocol.mbarInitFirst F.init F.bars hX hP.block

/-- `SafetyFacts.mbarPublished`. -/
theorem mbarPublished : ∀ m e c, X.MbInit e m c → ∀ s ∈ X.objects m,
    (∀ n, s.action ≠ .init n) → InitPublished L X e s.id.issuer m :=
  Protocol.mbarPublished F.init F.bars hX hP.block

/-- `SafetyFacts.mbarFaultFree`. -/
theorem mbarFaultFree : ∀ m r, r ∈ X.objects m → (∀ n, r.action ≠ .init n) →
    r.fault = none :=
  fun m r hr _ => Protocol.mbarFaultFree F.init F.bars hX hP.block F.load F.store F.state
    (noEvents hX) m r hr

/-- `SafetyFacts.mbarInitBefore`. -/
theorem mbarInitBefore : ∀ e m, X.UsesMbar e m → (∀ count, ¬ X.MbInit e m count) →
    ∃ i count, X.MbInit i m count ∧ baseCausality L X i e :=
  Protocol.mbarInitBefore F.init F.bars hX hP.block

omit hP in
/-- `SafetyFacts.sharedOwn`, from the field `sharedFrame`. -/
theorem sharedOwn
    (hframe : ∀ e a, X.MemTouches e a → a.loc.space = .shared →
      a.loc.cta = e.issuer.1 / L.block ∧ P.sharedBase ≤ a.loc.addr ∧
        a.loc.addr + a.size ≤ P.sharedBase + 98304) :
    ∀ e c, SharedUse L X e c → c = e.issuer.1 / L.block :=
  Protocol.sharedOwn F.init (noEvents hX) hX fun e a h hs => (hframe e a h hs).1

/-- `SafetyFacts.asyncFinished`, from the field `sharedFrame`. -/
theorem asyncFinished
    (hframe : ∀ e a, X.MemTouches e a → a.loc.space = .shared →
      a.loc.cta = e.issuer.1 / L.block ∧ P.sharedBase ≤ a.loc.addr ∧
        a.loc.addr + a.size ≤ P.sharedBase + 98304) :
    ∀ i p c, SharedUse L X (.async i p) c → CtaExited L X c →
      SharedFinished L kernel Assumptions.all X (.async i p) c :=
  F.life.asyncFinished (noEvents hX) hX (F.sharedOwn hX hframe)
    (F.life.loads_finished F.load F.state F.store F.init F.bars (noEvents hX) hX hP.block)

/-- `SafetyFacts.accOrdered`, from the field `sharedFrame`. -/
theorem accOrdered
    (hframe : ∀ e a, X.MemTouches e a → a.loc.space = .shared →
      a.loc.cta = e.issuer.1 / L.block ∧ P.sharedBase ≤ a.loc.addr ∧
        a.loc.addr + a.size ≤ P.sharedBase + 98304) :
    ConflictsOrdered L X fun l => l.space = .shared ∧ l.addr < P.sharedBase + 32768 := by
  have h := Protocol.accOrdered F.stateAcc F.bars hX hP.block fun e a ht hs => by
    rw [hP.sharedBase]
    exact (hframe e a ht hs).2.1
  rw [hP.sharedBase] at h
  exact h

/-- `SafetyFacts.bufOrdered`, from the field `sharedFrame` and the contract for the union
region (`UnionFacts`, `UnionClass.lean`): `UnionFacts.ordered` gives the order of every conflict
on the union region of each CTA. -/
theorem bufOrdered {O : Owners} (U : UnionFacts L X (ctaTiles P) O)
    (hframe : ∀ e a, X.MemTouches e a → a.loc.space = .shared →
      a.loc.cta = e.issuer.1 / L.block ∧ P.sharedBase ≤ a.loc.addr ∧
        a.loc.addr + a.size ≤ P.sharedBase + 98304) :
    ConflictsOrdered L X fun l => l.space = .shared ∧ P.sharedBase + 32768 ≤ l.addr := by
  have h := Protocol.bufOrdered
    (U.ordered F.life F.load F.store F.state F.init F.bars (noEvents hX) hX hP.block)
    fun e a ht hs => by
      rw [hP.sharedBase]
      exact (hframe e a ht hs).2.2
  rw [hP.sharedBase] at h
  exact h

/-- **`Premises.storeSources`** (for one execution; the field quantifies over the maximal ones,
which are consistent): every tensor store is a valid plain store, and each byte it reads has a
performed visible source write with a defined byte. From the contract for the union region
(`UnionFacts`) and the contract for the stores' source bytes (`StoreCover`,
`StoreCover.lean`), for the same owner functions `O`. -/
theorem storeSources {O : Owners} (U : UnionFacts L X (ctaTiles P) O)
    (C : StoreCover L X O) : Sched.StoreSources L X := by
  rintro ⟨g, i⟩ a s ⟨pc, hiss⟩
  obtain ⟨hv, -, hr⟩ := Proof.Top.tensorStore_form hX ⟨pc, hiss⟩
  exact ⟨hv, hr, U.visibleReadSources C F.store F.init F.bars (noEvents hX) hX hP.block
    (fun _ _ _ _ he => write_length hX C he) (fun _ _ _ _ _ => no_rmw hX) hiss⟩

/-- **The conclusion of `Premises.pollState`, from the count of the barrier's owner**: once the
thread that initializes barrier `b` has executed `b.gen + 1` `bar.sync 0`, the barrier has a
state. -/
theorem pollState_of_owner {c : Nat} (hc : c < L.grid) (b : Bar) {l : Loc}
    (hl : l = b.loc L c)
    (hgen : b.gen + 1 ≤ (X.tr (b.owner L c)).countP (Execution.isBarId 0)) :
    ∃ before, MBarrier.stateBefore (X.objects l) (X.objects l).length = some before := by
  subst hl
  exact bar_state F.init F.bars (noEvents hX) hX hP.block c b
    (objects_ne_nil_of_owner F.init F.bars hX hc b hgen)

/-- **The conclusion of `Premises.pollState`, from the count of the polling thread.** Thread
`g` polls barrier `b` of its CTA and has executed `b.gen + 1` `bar.sync 0`. `hpassed`: its
`bar.sync 0` with `b.gen` earlier ones is not its last event, so that barrier has released and
the barrier's owner has arrived at it too, after its initialization of `b`.

Without `hpassed` the statement is not provable from facts about events: at its first visit of
the poll of the state barrier (384) a thread's last event is its third `bar.sync 0` (379), and
only the release of that barrier (`Step.Released`, a hypothesis that `pollBlk` has and
`pollState` has not) says that the load leader has arrived and so has initialized the state
barrier. -/
theorem pollState {g : Nat} (hg : g < L.threads) (b : Bar) {l : Loc}
    (hl : l = b.loc L (g / L.block))
    (hgen : b.gen + 1 ≤ (X.tr g).countP (Execution.isBarId 0))
    (hpassed : ∀ j pc cnt mode, X.get (g, j) = some ⟨pc, .bar 0 cnt mode⟩ →
      bar0Before X (g, j) = b.gen → j + 1 < (X.tr g).length) :
    ∃ before, MBarrier.stateBefore (X.objects l) (X.objects l).length = some before := by
  have hb := hP.block
  have hc := cta_lt hb hg
  have hgen' : b.gen + 1 ≤ ((X.tr g).take (X.tr g).length).countP (Execution.isBarId 0) := by
    rwa [List.take_length]
  obtain ⟨j, pc, -, hbar, hord⟩ := F.bars.nth_bar0 hX hgen'
  have hj := hpassed j pc none .sync hbar hord
  have hsucc := countP_take_succ (p := Execution.isBarId 0) hbar (by simp [Execution.isBarId])
  obtain ⟨e, pce, md, he, heq⟩ := F.bars.peer_bar0 hX hb (Bar.owner_lt hb hc b)
    (Bar.owner_div hb b) hj (show b.gen + 1 ≤ bar0Before X (g, j + 1) by
      unfold bar0Before at hord ⊢
      simp only at hord ⊢
      omega)
  refine F.pollState_of_owner hP hX hc b hl ?_
  have h1 := countP_take_succ (p := Execution.isBarId 0) he (by simp [Execution.isBarId])
  have h2 := (List.take_sublist (e + 1) (X.tr (b.owner L (g / L.block)))).countP_le
    (p := Execution.isBarId 0)
  unfold bar0Before at heq
  simp only at heq
  omega

/-- `pollState` for a thread that has executed one more `bar.sync 0` than the barrier needs:
this covers every poll of the ten pipeline barriers (their polls are in the tile loop, after
six `bar.sync 0`, and they need one or two). -/
theorem pollState_of_two {g : Nat} (hg : g < L.threads) (b : Bar) {l : Loc}
    (hl : l = b.loc L (g / L.block))
    (hgen : b.gen + 2 ≤ (X.tr g).countP (Execution.isBarId 0)) :
    ∃ before, MBarrier.stateBefore (X.objects l) (X.objects l).length = some before := by
  refine F.pollState hP hX hg b hl (by omega) fun j pc cnt mode hbar hord => ?_
  by_contra hcon
  have hlen : (X.tr g).length ≤ j + 1 := Nat.le_of_not_gt hcon
  have hsucc := countP_take_succ (p := Execution.isBarId 0) hbar (by simp [Execution.isBarId])
  rw [List.take_of_length_le hlen] at hsucc
  unfold bar0Before at hord
  simp only at hord
  omega

omit hP in
/-- `SafetyFacts.barShape`. -/
theorem barShape : ∀ g k pc id cnt mode, X.get (g, k) = some ⟨pc, .bar id cnt mode⟩ →
    (pc, id, cnt) =
      Proof.Top.barSchedule P L g (((X.tr g).take k).countP Execution.isBar) :=
  Protocol.barShape F.bars hX

omit hP in
/-- `SafetyFacts.wholeBars`. -/
theorem wholeBars : ∀ g, (X.tr g).countP kernel.isAlignedCtaBar ≤ 9 ∧
    ∀ j pc, X.get (g, j) = some ⟨pc, .exit⟩ → (X.tr g).countP kernel.isAlignedCtaBar = 9 :=
  Protocol.wholeBars F.bars hX

end Facts

end PTX.Kernels.FlashKdaFwd.Protocol
