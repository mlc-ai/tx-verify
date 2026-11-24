-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.PairTmaRing.Hyp
public import Lemmas.Protocol.ObjectSource

@[expose] public section

/-! # A slot of a single-CTA TMA ring

A proof tool. A slot of a ring of one CTA fed by TMA copies (`Slot`): a full barrier `full`
(arrival count 1) and an empty barrier `empty` (count 1). A use of the slot completes one phase
of each barrier:

* `full`: one arrival of the arrival thread `ap`, expecting the use's `n · bytes` bytes, and the
  completion of `n` copies of `bytes` bytes of the copy thread `cp`, each use after the producer
  threads' successful polls of `empty` for it. When the slot is preloaded (`δ = 1`) use 0 is made
  before the loop by other events, the arrival `pArr` and the copies `pCp i`, which the
  producers' polls do not guard.
* `empty`: one commit of the consumer thread `cm` (a unit arrival), after its successful poll of
  `full` for the use.

The producers' successful polls of `empty` have the parity of their count plus `1 - δ` (the first
poll of a fresh slot passes on the fresh barrier); the polls acquire at scope `sc`.

`Hyp` is what the thread layer supplies for one slot: the sources of the records of the two
barriers, their initializations, the polls' parities, scopes and spins, and the copy issues.
`Decl` declares the slots of a ring once and derives `Hyp` for every slot from the thread-side
events (`Decl.hyp`), by the case analysis over a record's source (`record_source`). -/

namespace PTX.SingleTmaRing

open AsyncCopy Flow
open MBarrier hiding okPolls

/-- The commit rank of a single-CTA commit. -/
def rank0 : Fin 16 := 0

/-- **A slot of a single-CTA TMA ring.** -/
structure Slot where
  full : Loc
  empty : Loc
  /-- The arrival thread. -/
  ap : Nat
  /-- The copy thread. -/
  cp : Nat
  /-- The consumer thread. -/
  cm : Nat
  /-- The copies of a use, and the bytes of one copy. -/
  n : Nat
  bytes : Nat
  /-- `1` if use 0 is preloaded before the loop, else `0`. -/
  δ : Nat
  /-- The preloading arrival and copies (use 0, when `δ = 1`). -/
  pArr : EvId
  pCp : Fin n → EvId

/-- The bytes of a use's arrival. -/
def Slot.tx (S : Slot) : Nat := S.n * S.bytes

/-- The thread of producer `a`: the arrival thread, then the copy thread. -/
def Slot.prod (S : Slot) (a : Fin 2) : Nat := if a = 0 then S.ap else S.cp

/-- How a record of the full barrier arises. -/
inductive FullSource (X : Execution) (S : Slot) (r : Record Ref) : Prop
  | init {n : Nat} (ha : r.action = .init n)
  | poll {g j pc p : Nat} {ok acq : Bool} {sc : MbarScope} (hid : r.id = .thread (g, j))
      (he : X.get (g, j) = some ⟨pc, .wait S.full p ok acq sc⟩) (ha : r.action = .pollParity p ok)
  | arrive {j pc : Nat} {rel : Bool} {sc : MbarScope} (hid : r.id = .thread (S.ap, j))
      (he : X.get (S.ap, j) = some ⟨pc, .arrive S.full S.tx 1 rel sc⟩)
      (ha : r.action = .arrive 1 S.tx)
      (hb : arrivals S.full ((X.tr S.ap).take j) + 1 ≤ okPolls S.empty ((X.tr S.ap).take j))
  | preArrive {pc : Nat} {rel : Bool} {sc : MbarScope} (hδ : S.δ = 1)
      (hid : r.id = .thread S.pArr) (he : X.get S.pArr = some ⟨pc, .arrive S.full S.tx 1 rel sc⟩)
      (ha : r.action = .arrive 1 S.tx)
  | copy {j pc al : Nat} {sp : TensorCopy.Spec} (hid : r.id = .async (S.cp, j) (.notify .load))
      (he : X.get (S.cp, j) = some ⟨pc, .tensorIssue al sp⟩) (hm : sp.mbar = S.full)
      (ha : r.action = .completeTx S.bytes)
      (hb : ((X.tr S.cp).take j).countP (issuesTo S.full) + 1 ≤
        S.n * okPolls S.empty ((X.tr S.cp).take j))
  | preCopy {i : Fin S.n} {pc al : Nat} {sp : TensorCopy.Spec} (hδ : S.δ = 1)
      (hid : r.id = .async (S.pCp i) (.notify .load))
      (he : X.get (S.pCp i) = some ⟨pc, .tensorIssue al sp⟩) (hm : sp.mbar = S.full)
      (ha : r.action = .completeTx S.bytes)

/-- How a record of the empty barrier arises. -/
inductive EmptySource (X : Execution) (S : Slot) (r : Record Ref) : Prop
  | init {n : Nat} (ha : r.action = .init n)
  | poll {g j pc p : Nat} {ok acq : Bool} {sc : MbarScope} (hid : r.id = .thread (g, j))
      (he : X.get (g, j) = some ⟨pc, .wait S.empty p ok acq sc⟩)
      (ha : r.action = .pollParity p ok)
  | notify {j pc : Nat} {sp : TcCommit.Spec} (hid : r.id = .async (S.cm, j) (.tcNotify rank0))
      (he : X.get (S.cm, j) = some ⟨pc, .tc (.commit sp)⟩) (hm : sp.mbar = S.empty)
      (htg : TcCommit.target sp rank0 = some S.empty) (ha : r.action = .arrive 1 0)
      (hb : ((X.tr S.cm).take j).countP (commitsTo S.empty) + 1 ≤
        okPolls S.full ((X.tr S.cm).take j))

/-- **The thread-layer hypotheses of a slot of a single-CTA TMA ring**, whose polls acquire at
scope `sc`. -/
structure Hyp (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) (S : Slot)
    (sc : MbarScope) : Prop where
  δ_le : S.δ ≤ 1
  full_src : ∀ r ∈ X.objects S.full, FullSource X S r
  empty_src : ∀ r ∈ X.objects S.empty, EmptySource X S r
  full_init : PairTmaRing.InitFirst X S.full 1
  empty_init : PairTmaRing.InitFirst X S.empty 1
  full_noInval : NoInval (X.objects S.full)
  empty_noInval : NoInval (X.objects S.empty)
  full_parity : ∀ {g k pc p : Nat} {acq : Bool} {sc' : MbarScope},
    X.get (g, k) = some ⟨pc, .wait S.full p true acq sc'⟩ →
      p % 2 = (okPolls S.full ((X.tr g).take k) + 0) % 2
  empty_parity : ∀ {g k pc p : Nat} {acq : Bool} {sc' : MbarScope},
    X.get (g, k) = some ⟨pc, .wait S.empty p true acq sc'⟩ →
      p % 2 = (okPolls S.empty ((X.tr g).take k) + (1 - S.δ)) % 2
  spins : ∀ w pc m q acq sc', X.get w = some ⟨pc, .wait m q true acq sc'⟩ →
    ∃ exit, K.CanonicalSpin pc exit
  full_acq : ∀ {g k pc p : Nat} {acq : Bool} {sc' : MbarScope},
    X.get (g, k) = some ⟨pc, .wait S.full p true acq sc'⟩ → acq = true ∧ sc' = sc
  empty_acq : ∀ {g k pc p : Nat} {acq : Bool} {sc' : MbarScope},
    X.get (g, k) = some ⟨pc, .wait S.empty p true acq sc'⟩ → acq = true ∧ sc' = sc
  cta : ∀ a, SameCta L (S.prod a) S.cm
  issue : ∀ {g k pc al : Nat} {sp : TensorCopy.Spec},
    X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩ → sp.mbar = S.full →
    (g = S.cp ∧ ((X.tr g).take k).countP (issuesTo S.full) + 1 ≤
      S.n * okPolls S.empty ((X.tr g).take k)) ∨ (S.δ = 1 ∧ ∃ i : Fin S.n, (g, k) = S.pCp i)
  pre_cta : S.δ = 1 → ∀ i : Fin S.n, SameCta L (S.pCp i).1 S.cm
  pre_ne : S.δ = 1 → S.pArr.1 ≠ S.ap ∧ ∀ i : Fin S.n, (S.pCp i).1 ≠ S.cp
  pre_inj : S.δ = 1 → Function.Injective S.pCp

/-! ### Declared rings -/

/-- **A single-CTA TMA ring as data**: `depth` slots with their barriers, the producer and
consumer threads, the copies and bytes of a use, and the preload of each slot. -/
structure Decl where
  depth : Nat
  full : Fin depth → Loc
  empty : Fin depth → Loc
  ap : Nat
  cp : Nat
  cm : Nat
  n : Nat
  bytes : Nat
  δ : Fin depth → Nat
  pArr : Fin depth → EvId
  pCp : Fin depth → Fin n → EvId

/-- Slot `s` of a declared ring. -/
def Decl.slot (R : Decl) (s : Fin R.depth) : Slot :=
  ⟨R.full s, R.empty s, R.ap, R.cp, R.cm, R.n, R.bytes, R.δ s, R.pArr s, R.pCp s⟩

/-- **The thread-side events of a declared ring**, for every slot `s`. -/
structure Decl.Events (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) (R : Decl)
    (sc : MbarScope) : Prop where
  δ_le : ∀ s, R.δ s ≤ 1
  /-- An arrival on a full barrier is the arrival thread's, of one unit expecting the use's
  bytes, within its budget, or the preloading arrival. -/
  arrive : ∀ s {g j pc tx cnt : Nat} {rel : Bool} {sc' : MbarScope},
    X.get (g, j) = some ⟨pc, .arrive (R.full s) tx cnt rel sc'⟩ → tx = (R.slot s).tx ∧ cnt = 1 ∧
    ((g = R.ap ∧ arrivals (R.full s) ((X.tr g).take j) + 1 ≤
      okPolls (R.empty s) ((X.tr g).take j)) ∨ (R.δ s = 1 ∧ (g, j) = R.pArr s))
  arrive_empty : ∀ s {g j pc tx cnt : Nat} {rel : Bool} {sc' : MbarScope},
    X.get (g, j) ≠ some ⟨pc, .arrive (R.empty s) tx cnt rel sc'⟩
  /-- A copy completing on a full barrier is of the use's copy bytes, the copy thread's within
  its budget, or a preloading copy. -/
  issue : ∀ s {g k pc al : Nat} {sp : TensorCopy.Spec},
    X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩ → sp.mbar = R.full s →
    TensorTransfer.bytes sp.descriptor = R.bytes ∧
    ((g = R.cp ∧ ((X.tr g).take k).countP (issuesTo (R.full s)) + 1 ≤
      R.n * okPolls (R.empty s) ((X.tr g).take k)) ∨ (R.δ s = 1 ∧ ∃ i, (g, k) = R.pCp s i))
  issue_empty : ∀ s {g k pc al : Nat} {sp : TensorCopy.Spec},
    X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩ → sp.mbar ≠ R.empty s
  /-- A commit notifying an empty barrier is the consumer's, at rank 0, within its budget. -/
  commit : ∀ s {g j pc : Nat} {sp : TcCommit.Spec} {r : Fin 16},
    X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r = some (R.empty s) →
    g = R.cm ∧ r = rank0 ∧ sp.mbar = R.empty s ∧
      ((X.tr g).take j).countP (commitsTo sp.mbar) + 1 ≤ okPolls (R.full s) ((X.tr g).take j)
  commit_full : ∀ s {g j pc : Nat} {sp : TcCommit.Spec} {r : Fin 16},
    X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r ≠ some (R.full s)
  no_bulk : ∀ {i : EvId} {pc : Nat} {s : AsyncCopy.Spec}, X.get i ≠ some ⟨pc, .copy s⟩
  no_arriveOn : ∀ {i : EvId} {pc : Nat} {m : Loc} {noinc : Bool},
    X.get i ≠ some ⟨pc, .asyncArrive m noinc⟩
  no_clc : ∀ {i : EvId} {pc : Nat} {sp : Clc.Spec} {tg : List Nat},
    X.get i ≠ some ⟨pc, .clcIssue sp tg⟩
  no_inval : ∀ {i : EvId} {pc : Nat} {m : Loc}, X.get i ≠ some ⟨pc, .mbInval m⟩
  full_init : ∀ s, PairTmaRing.InitFirst X (R.full s) 1
  empty_init : ∀ s, PairTmaRing.InitFirst X (R.empty s) 1
  full_parity : ∀ s {g k pc p : Nat} {acq : Bool} {sc' : MbarScope},
    X.get (g, k) = some ⟨pc, .wait (R.full s) p true acq sc'⟩ →
      p % 2 = (okPolls (R.full s) ((X.tr g).take k) + 0) % 2
  empty_parity : ∀ s {g k pc p : Nat} {acq : Bool} {sc' : MbarScope},
    X.get (g, k) = some ⟨pc, .wait (R.empty s) p true acq sc'⟩ →
      p % 2 = (okPolls (R.empty s) ((X.tr g).take k) + (1 - R.δ s)) % 2
  spins : ∀ w pc m q acq sc', X.get w = some ⟨pc, .wait m q true acq sc'⟩ →
    ∃ exit, K.CanonicalSpin pc exit
  full_acq : ∀ s {g k pc p : Nat} {acq : Bool} {sc' : MbarScope},
    X.get (g, k) = some ⟨pc, .wait (R.full s) p true acq sc'⟩ → acq = true ∧ sc' = sc
  empty_acq : ∀ s {g k pc p : Nat} {acq : Bool} {sc' : MbarScope},
    X.get (g, k) = some ⟨pc, .wait (R.empty s) p true acq sc'⟩ → acq = true ∧ sc' = sc
  cta : ∀ a : Fin 2, SameCta L (if a = 0 then R.ap else R.cp) R.cm
  pre_cta : ∀ s, R.δ s = 1 → ∀ i, SameCta L (R.pCp s i).1 R.cm
  pre_ne : ∀ s, R.δ s = 1 → (R.pArr s).1 ≠ R.ap ∧ ∀ i, (R.pCp s i).1 ≠ R.cp
  pre_inj : ∀ s, R.δ s = 1 → Function.Injective (R.pCp s)

/-- **The hypotheses of every slot of a declared single-CTA ring**, from its thread-side events. -/
theorem Decl.hyp {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
    {R : Decl} {sc : MbarScope} (hX : Consistent L K A mem0 X) (hE : R.Events L K A X sc)
    (s : Fin R.depth) : Hyp L K A X (R.slot s) sc where
  δ_le := hE.δ_le s
  full_src r hr := by
    cases record_source hX.tma.2.2.1 hr with
    | init _ _ ha => exact .init ha
    | inval _ he _ => exact absurd he hE.no_inval
    | wait hid he ha => exact .poll hid he ha
    | arrive hid he ha =>
      obtain ⟨rfl, rfl, hw⟩ := hE.arrive s he
      rcases hw with ⟨rfl, hb⟩ | ⟨hδ, hp⟩
      · exact .arrive hid he ha hb
      · rw [hp] at hid he
        exact .preArrive hδ hid he ha
    | @tensor i pc al sp hid he hm ha =>
      obtain ⟨g, k⟩ := i
      obtain ⟨hby, hw⟩ := hE.issue s he hm
      rw [hby] at ha
      rcases hw with ⟨rfl, hb⟩ | ⟨hδ, i, hp⟩
      · exact .copy hid he hm ha hb
      · rw [hp] at hid he
        exact .preCopy (i := i) hδ hid he hm ha
    | increment _ he _ => exact absurd he hE.no_arriveOn
    | arriveOn _ he _ _ _ => exact absurd he hE.no_arriveOn
    | bulk _ he _ _ _ => exact absurd he hE.no_bulk
    | commit _ he htg _ => exact absurd htg (hE.commit_full s he)
    | clc _ he _ _ _ => exact absurd he hE.no_clc
  empty_src r hr := by
    cases record_source hX.tma.2.2.1 hr with
    | init _ _ ha => exact .init ha
    | inval _ he _ => exact absurd he hE.no_inval
    | wait hid he ha => exact .poll hid he ha
    | arrive _ he _ => exact absurd he (hE.arrive_empty s)
    | tensor _ he hm _ => exact absurd hm (hE.issue_empty s he)
    | increment _ he _ => exact absurd he hE.no_arriveOn
    | arriveOn _ he _ _ _ => exact absurd he hE.no_arriveOn
    | bulk _ he _ _ _ => exact absurd he hE.no_bulk
    | @commit i pc sp rank hid he htg ha =>
      obtain ⟨g, j⟩ := i
      obtain ⟨rfl, rfl, hmb, hbud⟩ := hE.commit s he htg
      rw [hmb] at hbud
      exact .notify hid he hmb htg ha hbud
    | clc _ he _ _ _ => exact absurd he hE.no_clc
  full_init := hE.full_init s
  empty_init := hE.empty_init s
  full_noInval := objects_noInval hX.tma.2.2.1 (fun _ _ ⟨_, h⟩ => hE.no_inval h) _
  empty_noInval := objects_noInval hX.tma.2.2.1 (fun _ _ ⟨_, h⟩ => hE.no_inval h) _
  full_parity := hE.full_parity s
  empty_parity := hE.empty_parity s
  spins := hE.spins
  full_acq := hE.full_acq s
  empty_acq := hE.empty_acq s
  cta := hE.cta
  issue he hm := (hE.issue s he hm).2
  pre_cta := hE.pre_cta s
  pre_ne := hE.pre_ne s
  pre_inj := hE.pre_inj s

end PTX.SingleTmaRing
