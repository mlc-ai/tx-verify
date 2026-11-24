-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.PairTmaRing.Order
public import Kernels.InklingRelDecode.Proof.Protocol.RingSched

@[expose] public section

/-!
# A slot of the Inkling KV ring as a one-CTA TMA ring slot

`Lemmas/Protocol/PairTmaRing` is a hypothesis structure for a slot of a TMA ring of a
`cta_group::2` pair: two producers (one per CTA), each with its own empty barrier, and `n` copies
per producer and use. The Inkling KV ring has one CTA and a different split of the work, so it
needs its own structure (`Kv.Slot`, `Kv.Hyp`); the generic lemmas that do not mention the slot
(`state_of_init`, `Items.Ring`, `MbarRing.Poll`, `AsyncCopy`, the order lemmas) are reused.

## The slot

Slot `s` of the ring of CTA `c` has the barriers `kvReady c s` (`full`: arrival count 1) and
`kvEmpty c s` (`empty`: count 1). A *use* of the slot is one block `3 u + s`; one use completes one
phase of each barrier:

* `full`, phase `u`: **one** `mbarrier.arrive.expect_tx` of 65536 bytes and the completion of
  **eight** tensor copies of 8192 bytes each. The arrival and the copies of the uses `u ≥ δ` are
  the loader's (`ap`, the thread of lane 0 of the loader warp, arrives; `cp`, the thread its
  elections elect, copies, eight per use in the order of the sites), each use after the loader's
  successful poll of `empty` for it. When the prologue preloads the slot (`δ = 1`, the slot is
  `s < num_pre`) use 0 is the prologue's: the arrival `pArr` and the eight copies `pCp j`, events
  of threads of the default partition, which the loader's polls do not guard.
* `empty`, phase `u`: the commit of the MMA warp's elected lane `cm` for block `3 u + s`
  (a unit arrival), after the commit's thread has polled `full` for the use.

The consumers' polls of `full` are every lane of the MMA warp's (`cm`'s alone gets the exact
phase attribution of `Ring`), the producers' polls of `empty` every lane of the loader warp's.

## Items and kinds

A phase of `full` is completed by items of 9 kinds (`Kind`): kind 0 the arrival, kind `1 + j` the
`j`-th copy of the use. The item of kind `k` and use `u` is the event `opF k u`: the prologue's
(`pArr`, `pCp j`) for `δ = 1`, `u = 0`; else the loader thread's event of its kind with
`kIdx k (u - δ)` earlier events of that kind (`nthEv`). Its record on `full` is the event itself
(the arrival) or the copy's notification. The polls are numbered as the uses they wait for:
`wE n` is the loader thread's successful poll of `empty` with `n - δ` earlier ones, for the use
`n ≥ 1` (the loader's first poll of a preloaded slot waits for use 1), `wF j` is `cm`'s successful
poll of `full` with `j` earlier ones, for the use `j`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Ring.Kv
open PTX PTX.Flow AsyncCopy
open PTX.MBarrier hiding okPolls

noncomputable section

/-- The commit rank of the (single-CTA) commit. -/
def rank0 : Fin 16 := 0

/-- **A slot of the KV ring.** -/
structure Slot where
  /-- The full barrier, `kvReady c s`. -/
  full : Loc
  /-- The empty barrier, `kvEmpty c s`. -/
  empty : Loc
  /-- The arrival thread: lane 0 of the loader warp. -/
  ap : Nat
  /-- The copy thread: the loader warp's elected lane. -/
  cp : Nat
  /-- The consumer thread: the MMA warp's elected lane. -/
  cm : Nat
  /-- `1` if the prologue preloads use 0 of the slot, else `0`. -/
  δ : Nat
  /-- The prologue's arrival (use 0, when `δ = 1`). -/
  pArr : EvId
  /-- The prologue's copies (use 0, when `δ = 1`). -/
  pCp : Fin 8 → EvId

/-- The bytes of a use's arrival. -/
abbrev txBytes : Nat := 65536
/-- The bytes of one copy. -/
abbrev copyBytes : Nat := 8192
/-- The kinds of items of a phase of the full barrier: the arrival and the eight copies. -/
abbrev Kind : Type := Fin 9

/-- The loader thread of kind `k`: lane 0 arrives, the elected lane copies. -/
def kOwner (k : Kind) : Fin 2 := if k.val = 0 then 0 else 1

/-- The thread of producer `a`. -/
def Slot.prod (S : Slot) (a : Fin 2) : Nat := if a = 0 then S.ap else S.cp

/-- The events of kind `k`. -/
def kPred (S : Slot) (k : Kind) : Event → Bool :=
  if k.val = 0 then arrivesOn S.full else issuesTo S.full

/-- The loader thread's count of earlier events of kind `k` at its `m`-th use. -/
def kIdx (k : Kind) (m : Nat) : Nat := if k.val = 0 then m else 8 * m + (k.val - 1)

/-- The event of the item of kind `k` and use `u`. -/
def opF (X : Execution) (S : Slot) (k : Kind) (u : Nat) : EvId :=
  if S.δ = 1 ∧ u = 0 then
    (if k.val = 0 then S.pArr else S.pCp ⟨k.val - 1, by have := k.isLt; omega⟩)
  else (S.prod (kOwner k), nthEv X (kPred S k) (S.prod (kOwner k)) (kIdx k (u - S.δ)))

/-- The record of the item of kind `k` and use `u` on the full barrier. -/
def itF (X : Execution) (S : Slot) (k : Kind) (u : Nat) : Ref :=
  if k.val = 0 then .thread (opF X S k u) else .async (opF X S k u) (.notify .load)

/-- Producer `a`'s successful poll of the empty barrier for use `n ≥ 1`. -/
def wE (X : Execution) (S : Slot) (a : Fin 2) (n : Nat) : EvId :=
  (S.prod a, MbarRing.Poll.nth X S.empty (S.prod a) (n - S.δ))

/-- The consumer's successful poll of the full barrier with `j` earlier ones. -/
def wF (X : Execution) (S : Slot) (_b : Fin 1) (j : Nat) : EvId :=
  (S.cm, MbarRing.Poll.nth X S.full S.cm j)

/-- The consumer's commit to the slot with `t` earlier ones. -/
def cmE (X : Execution) (S : Slot) (_b : Fin 1) (t : Nat) : EvId :=
  (S.cm, nthEv X (commitsTo S.empty) S.cm t)

/-- The notification of the empty barrier by the commit with `t` earlier ones. -/
def note (X : Execution) (S : Slot) (b : Fin 1) (_a : Fin 2) (t : Nat) : Ref :=
  .async (cmE X S b t) (.tcNotify rank0)

/-- A bound on the uses of the slot's items. -/
def useBound (X : Execution) (S : Slot) : Nat :=
  (X.tr S.ap).length + (X.tr S.cp).length + (X.tr S.cm).length + 2

open Classical in
/-- The counted items of the full barrier: those with a fault-free record of their action. -/
def SF (X : Execution) (S : Slot) : Finset (Kind × Nat) :=
  (Finset.univ ×ˢ Finset.range (useBound X S)).filter fun x =>
    ∃ r ∈ X.objects S.full, r.id = itF X S x.1 x.2 ∧ r.fault = none ∧
      (x.1.val = 0 → r.action = .arrive 1 txBytes) ∧
      (x.1.val ≠ 0 → r.action = .completeTx copyBytes)

open Classical in
/-- The counted notifications of the empty barrier: those with a fault-free record. -/
def SE (X : Execution) (S : Slot) : Finset (Fin 1 × Nat) :=
  (Finset.univ ×ˢ Finset.range (useBound X S)).filter fun y =>
    ∃ r ∈ X.objects S.empty, r.id = note X S y.1 0 y.2 ∧ r.fault = none ∧
      r.action = .arrive 1 0

/-- The phase of a full barrier item. -/
def phF (X : Execution) (S : Slot) (x : Kind × Nat) : Nat :=
  MbarRing.Poll.phaseOf X S.full (itF X S x.1 x.2)

/-- The phase of a notification of the empty barrier. -/
def phE (X : Execution) (S : Slot) (y : Fin 1 × Nat) : Nat :=
  MbarRing.Poll.phaseOf X S.empty (note X S y.1 0 y.2)

/-- The completed phase of `full` observed by the consumer's poll with `j` earlier ones. -/
def oF (X : Execution) (S : Slot) (b : Fin 1) (j : Nat) : Nat :=
  MbarRing.Poll.observedOf X S.full (.thread (wF X S b j))

/-- The completed phase of `empty` observed by producer `a`'s poll for use `n`. -/
def oE (X : Execution) (S : Slot) (a : Fin 2) (n : Nat) : Nat :=
  MbarRing.Poll.observedOf X S.empty (.thread (wE X S a n))

/-! ### The sources of the records -/

/-- How a record of the full barrier arises. -/
inductive FullSource (X : Execution) (S : Slot) (r : Record Ref) : Prop
  | init {n : Nat} (ha : r.action = .init n)
  | poll {g j pc p : Nat} {ok acq : Bool} {sc : MbarScope} (hid : r.id = .thread (g, j))
      (he : X.get (g, j) = some ⟨pc, .wait S.full p ok acq sc⟩) (ha : r.action = .pollParity p ok)
  /-- The loader's arrival, lane 0's, after more successful polls of `empty` than its earlier
  arrivals. -/
  | arrive {j pc : Nat} {rel : Bool} {sc : MbarScope} (hid : r.id = .thread (S.ap, j))
      (he : X.get (S.ap, j) = some ⟨pc, .arrive S.full txBytes 1 rel sc⟩)
      (ha : r.action = .arrive 1 txBytes)
      (hb : arrivals S.full ((X.tr S.ap).take j) + 1 ≤
        okPolls S.empty ((X.tr S.ap).take j))
  /-- The prologue's arrival of a preloaded slot. -/
  | preArrive {pc : Nat} {rel : Bool} {sc : MbarScope} (hδ : S.δ = 1) (hid : r.id = .thread S.pArr)
      (he : X.get S.pArr = some ⟨pc, .arrive S.full txBytes 1 rel sc⟩)
      (ha : r.action = .arrive 1 txBytes)
  /-- The loader's copy, the elected lane's, within its budget of eight per poll. -/
  | copy {j pc al : Nat} {sp : TensorCopy.Spec} (hid : r.id = .async (S.cp, j) (.notify .load))
      (he : X.get (S.cp, j) = some ⟨pc, .tensorIssue al sp⟩) (hm : sp.mbar = S.full)
      (ha : r.action = .completeTx copyBytes)
      (hb : ((X.tr S.cp).take j).countP (issuesTo S.full) + 1 ≤
        8 * okPolls S.empty ((X.tr S.cp).take j))
  /-- The prologue's copy `i` of a preloaded slot. -/
  | preCopy {i : Fin 8} {pc al : Nat} {sp : TensorCopy.Spec} (hδ : S.δ = 1)
      (hid : r.id = .async (S.pCp i) (.notify .load))
      (he : X.get (S.pCp i) = some ⟨pc, .tensorIssue al sp⟩) (hm : sp.mbar = S.full)
      (ha : r.action = .completeTx copyBytes)

/-- How a record of the empty barrier arises. -/
inductive EmptySource (X : Execution) (S : Slot) (r : Record Ref) : Prop
  | init {n : Nat} (ha : r.action = .init n)
  | poll {g j pc p : Nat} {ok acq : Bool} {sc : MbarScope} (hid : r.id = .thread (g, j))
      (he : X.get (g, j) = some ⟨pc, .wait S.empty p ok acq sc⟩)
      (ha : r.action = .pollParity p ok)
  /-- The MMA lane's commit to the slot, after more successful polls of `full` than its
  earlier commits. -/
  | notify {j pc : Nat} {sp : TcCommit.Spec}
      (hid : r.id = .async (S.cm, j) (.tcNotify rank0))
      (he : X.get (S.cm, j) = some ⟨pc, .tc (.commit sp)⟩) (hm : sp.mbar = S.empty)
      (htg : TcCommit.target sp rank0 = some S.empty) (ha : r.action = .arrive 1 0)
      (hb : ((X.tr S.cm).take j).countP (commitsTo S.empty) + 1 ≤
        okPolls S.full ((X.tr S.cm).take j))

/-- **The thread-layer hypotheses of a slot of the KV ring.** -/
structure Hyp (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) (S : Slot) :
    Prop where
  /-- The prologue preloads at most use 0. -/
  δ_le : S.δ ≤ 1
  /-- The records of the full barrier. -/
  full_src : ∀ r ∈ X.objects S.full, FullSource X S r
  /-- The records of the empty barrier. -/
  empty_src : ∀ r ∈ X.objects S.empty, EmptySource X S r
  /-- The full barrier is initialized first with count one. -/
  full_init : PairTmaRing.InitFirst X S.full 1
  /-- The empty barrier is initialized first with count one. -/
  empty_init : PairTmaRing.InitFirst X S.empty 1
  /-- No record of the full barrier is an invalidation. -/
  full_noInval : NoInval (X.objects S.full)
  /-- No record of the empty barrier is an invalidation. -/
  empty_noInval : NoInval (X.objects S.empty)
  /-- A successful poll of the full barrier has the parity of the thread's earlier ones. -/
  full_parity : ∀ {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
    X.get (g, k) = some ⟨pc, .wait S.full p true acq sc⟩ →
      p % 2 = (okPolls S.full ((X.tr g).take k) + 0) % 2
  /-- A successful poll of the empty barrier has the parity of the thread's earlier ones plus
  one, less the preloaded use: the first poll of a fresh slot passes on the fresh barrier. -/
  empty_parity : ∀ {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
    X.get (g, k) = some ⟨pc, .wait S.empty p true acq sc⟩ →
      p % 2 = (okPolls S.empty ((X.tr g).take k) + (1 - S.δ)) % 2
  /-- Every successful poll is the poll of a canonical spin (DEP-CANONICAL-SPIN). -/
  spins : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
    ∃ exit, K.CanonicalSpin pc exit
  /-- A successful poll of the full barrier acquires at CTA scope. -/
  full_acq : ∀ {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
    X.get (g, k) = some ⟨pc, .wait S.full p true acq sc⟩ → acq = true ∧ sc = .cta
  /-- A successful poll of the empty barrier acquires at CTA scope. -/
  empty_acq : ∀ {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
    X.get (g, k) = some ⟨pc, .wait S.empty p true acq sc⟩ → acq = true ∧ sc = .cta
  /-- The producers and the consumer are threads of one CTA. -/
  cta : ∀ a, SameCta L (S.prod a) S.cm
  /-- A copy issue completing on the full barrier is the loader's elected lane's, within its budget
  of eight per successful poll of `empty`, or one of the prologue's eight. -/
  issue : ∀ {g k pc al : Nat} {sp : TensorCopy.Spec},
    X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩ → sp.mbar = S.full →
    (g = S.cp ∧ ((X.tr g).take k).countP (issuesTo S.full) + 1 ≤
      8 * okPolls S.empty ((X.tr g).take k)) ∨ (S.δ = 1 ∧ ∃ i : Fin 8, (g, k) = S.pCp i)
  /-- The prologue's copies are issued by threads of the CTA. -/
  pre_cta : S.δ = 1 → ∀ i : Fin 8, SameCta L (S.pCp i).1 S.cm
  /-- The prologue's threads are not the loader's: the prologue's arrival and copies are not
  events of the loader's arrival and copy threads. -/
  pre_ne : S.δ = 1 → S.pArr.1 ≠ S.ap ∧ ∀ i : Fin 8, (S.pCp i).1 ≠ S.cp
  /-- The prologue's eight copies are distinct events. -/
  pre_inj : S.δ = 1 → Function.Injective S.pCp

end
end PTX.Kernels.InklingRelDecode.Proof.Ring.Kv
