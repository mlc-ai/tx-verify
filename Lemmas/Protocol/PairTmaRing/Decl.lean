-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.PairTmaRing.Hyp
public import Lemmas.Protocol.ObjectSource

@[expose] public section

/-! # A pair TMA ring as declared data

A ring fed by TMA copies from both CTAs of a `cta_group::2` pair is declared once (`Decl`): its
`depth` slots, each with a full barrier in the leader CTA, an empty barrier in each CTA, its
copies per use and its bytes per copy, and the producer threads and consumer threads that every
slot shares. Slot `s` of the declaration is a `Slot` of the pair TMA ring protocol
(`Decl.slot`).

The thread side of a declared ring is stated once for all its slots (`Decl.Events`): which
thread makes each arrival, copy and commit on a slot's barriers and within which budget of its
successful polls of the partner barrier, that no other event targets them, their
initializations, the polls' parities and scopes. From these, for every slot, the records of the
slot's barriers have the sources the protocol needs, and so the slot has the protocol's
hypotheses (`Decl.hyp`): the case analysis over a record's source (`record_source`) is done here
once, for every ring and depth. -/

namespace PTX.PairTmaRing

open AsyncCopy Flow
open MBarrier hiding okPolls

/-- **A pair TMA ring as data**: `depth` slots, each with its full barrier, its empty barrier
in the CTA of each rank, its copies per use and the bytes of each copy; the producers (one per
CTA) and the `nc` consumers of every slot. -/
structure Decl (nc : Nat) where
  depth : Nat
  full : Fin depth → Loc
  empty : Fin depth → Fin 2 → Loc
  prod : Fin 2 → Nat
  cons : Fin nc → Nat
  copies : Fin depth → Nat
  bytes : Fin depth → Nat

variable {nc : Nat}

/-- Slot `s` of a declared ring. -/
def Decl.slot (R : Decl nc) (s : Fin R.depth) : Slot nc :=
  ⟨R.full s, R.empty s, R.prod, R.cons, R.copies s, R.bytes s⟩

/-- **The thread-side events of a declared ring**, for every slot `s`. -/
structure Decl.Events (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution)
    (R : Decl nc) : Prop where
  copies_pos : ∀ s, 0 < R.copies s
  bytes_pos : ∀ s, 0 < R.bytes s
  nc_pos : 0 < nc
  tx_le : ∀ s, 2 * (R.slot s).tx ≤ limit
  prod_inj : Function.Injective R.prod
  cons_inj : Function.Injective R.cons
  /-- An arrival on a full barrier is producer 0's, with one unit expecting the use's bytes,
  after more successful polls of the empty barrier than its earlier arrivals. -/
  arrive : ∀ s {g j pc tx cnt : Nat} {rel : Bool} {sc : MbarScope},
    X.get (g, j) = some ⟨pc, .arrive (R.full s) tx cnt rel sc⟩ →
    g = R.prod 0 ∧ tx = (R.slot s).tx ∧ cnt = 1 ∧
      arrivals (R.full s) ((X.tr g).take j) + 1 ≤ okPolls (R.empty s 0) ((X.tr g).take j)
  /-- No event arrives on an empty barrier. -/
  arrive_empty : ∀ s a {g j pc tx cnt : Nat} {rel : Bool} {sc : MbarScope},
    X.get (g, j) ≠ some ⟨pc, .arrive (R.empty s a) tx cnt rel sc⟩
  /-- A copy completing on a full barrier is a producer's, of the slot's bytes, within the
  copies its successful polls of its empty barrier allow. -/
  issue : ∀ s {g k pc al : Nat} {sp : TensorCopy.Spec},
    X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩ → sp.mbar = R.full s →
    ∃ a, g = R.prod a ∧ TensorTransfer.bytes sp.descriptor = R.bytes s ∧
      ((X.tr g).take k).countP (issuesTo (R.full s)) + 1 ≤
        R.copies s * okPolls (R.empty s a) ((X.tr g).take k)
  /-- No copy completes on an empty barrier. -/
  issue_empty : ∀ s a {g k pc al : Nat} {sp : TensorCopy.Spec},
    X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩ → sp.mbar ≠ R.empty s a
  /-- A commit notifying the empty barrier of rank `a` is a consumer's, at rank `a`, with the
  leader's empty barrier as its mbarrier, after more successful polls of the full barrier than
  its earlier commits there. -/
  commit : ∀ s a {g j pc : Nat} {sp : TcCommit.Spec} {r : Fin 16},
    X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r = some (R.empty s a) →
    ∃ b, g = R.cons b ∧ r = rankOf a ∧ sp.mbar = R.empty s 0 ∧
      ((X.tr g).take j).countP (commitsTo sp.mbar) + 1 ≤ okPolls (R.full s) ((X.tr g).take j)
  /-- No commit notifies a full barrier. -/
  commit_full : ∀ s {g j pc : Nat} {sp : TcCommit.Spec} {r : Fin 16},
    X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r ≠ some (R.full s)
  /-- The kernel has no linear copy, `cp.async.mbarrier.arrive`, cancellation request or
  barrier invalidation. -/
  no_bulk : ∀ {i : EvId} {pc : Nat} {s : AsyncCopy.Spec}, X.get i ≠ some ⟨pc, .copy s⟩
  no_arriveOn : ∀ {i : EvId} {pc : Nat} {m : Loc} {noinc : Bool},
    X.get i ≠ some ⟨pc, .asyncArrive m noinc⟩
  no_clc : ∀ {i : EvId} {pc : Nat} {sp : Clc.Spec} {tg : List Nat},
    X.get i ≠ some ⟨pc, .clcIssue sp tg⟩
  no_inval : ∀ {i : EvId} {pc : Nat} {m : Loc}, X.get i ≠ some ⟨pc, .mbInval m⟩
  full_init : ∀ s, InitFirst X (R.full s) 1
  empty_init : ∀ s a, InitFirst X (R.empty s a) nc
  full_parity : ∀ s {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
    X.get (g, k) = some ⟨pc, .wait (R.full s) p true acq sc⟩ →
      p % 2 = (okPolls (R.full s) ((X.tr g).take k) + 0) % 2
  empty_parity : ∀ s {a : Fin 2} {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
    X.get (g, k) = some ⟨pc, .wait (R.empty s a) p true acq sc⟩ →
      p % 2 = (okPolls (R.empty s a) ((X.tr g).take k) + 1) % 2
  spins : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
    ∃ exit, K.CanonicalSpin pc exit
  full_acq : ∀ s {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
    X.get (g, k) = some ⟨pc, .wait (R.full s) p true acq sc⟩ → acq = true ∧ sc = .cluster
  empty_acq : ∀ s {a : Fin 2} {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
    X.get (g, k) = some ⟨pc, .wait (R.empty s a) p true acq sc⟩ → acq = true ∧ sc = .cluster
  cluster : ∀ a b, L.clusterOfCta (R.prod a / L.block) = L.clusterOfCta (R.cons b / L.block)

/-- **The hypotheses of every slot of a declared ring**, from its thread-side events. -/
theorem Decl.hyp {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
    {R : Decl nc} (hX : Consistent L K A mem0 X) (hE : R.Events L K A X) (s : Fin R.depth) :
    Hyp L K A X (R.slot s) where
  n_pos := hE.copies_pos s
  bytes_pos := hE.bytes_pos s
  nc_pos := hE.nc_pos
  tx_le := hE.tx_le s
  prod_inj := hE.prod_inj
  cons_inj := hE.cons_inj
  full_src r hr := by
    cases record_source hX.tma.2.2.1 hr with
    | init _ _ ha => exact .init ha
    | inval _ he _ => exact absurd he hE.no_inval
    | wait hid he ha => exact .poll hid he ha
    | arrive hid he ha =>
      obtain ⟨rfl, rfl, rfl, hbud⟩ := hE.arrive s he
      exact .arrive hid he ha hbud
    | tensor hid he hm ha =>
      obtain ⟨a, -, hby, -⟩ := hE.issue s he hm
      exact .copy hid he hm (by rw [ha, hby]; rfl)
    | increment _ he _ => exact absurd he hE.no_arriveOn
    | arriveOn _ he _ _ _ => exact absurd he hE.no_arriveOn
    | bulk _ he _ _ _ => exact absurd he hE.no_bulk
    | commit _ he htg _ => exact absurd htg (hE.commit_full s he)
    | clc _ he _ _ _ => exact absurd he hE.no_clc
  empty_src a r hr := by
    cases record_source hX.tma.2.2.1 hr with
    | init _ _ ha => exact .init ha
    | inval _ he _ => exact absurd he hE.no_inval
    | wait hid he ha => exact .poll hid he ha
    | arrive _ he _ => exact absurd he (hE.arrive_empty s a)
    | tensor _ he hm _ => exact absurd hm (hE.issue_empty s a he)
    | increment _ he _ => exact absurd he hE.no_arriveOn
    | arriveOn _ he _ _ _ => exact absurd he hE.no_arriveOn
    | bulk _ he _ _ _ => exact absurd he hE.no_bulk
    | @commit i pc sp rank hid he htg ha =>
      obtain ⟨g, j⟩ := i
      obtain ⟨b, rfl, rfl, hmb, hbud⟩ := hE.commit s a he htg
      rw [hmb] at hbud
      exact .notify hid he hmb htg ha hbud
    | clc _ he _ _ _ => exact absurd he hE.no_clc
  issue he hm := by
    obtain ⟨a, rfl, -, hbud⟩ := hE.issue s he hm
    exact ⟨a, rfl, hbud⟩
  full_init := hE.full_init s
  empty_init := hE.empty_init s
  full_noInval := objects_noInval hX.tma.2.2.1 (fun _ _ ⟨_, h⟩ => hE.no_inval h) _
  empty_noInval _ := objects_noInval hX.tma.2.2.1 (fun _ _ ⟨_, h⟩ => hE.no_inval h) _
  full_parity := hE.full_parity s
  empty_parity := hE.empty_parity s
  spins := hE.spins
  full_acq := hE.full_acq s
  empty_acq := hE.empty_acq s
  cluster := hE.cluster

end PTX.PairTmaRing
