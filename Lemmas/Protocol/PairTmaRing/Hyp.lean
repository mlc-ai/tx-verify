-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.PairTmaRing
public import Lemmas.Protocol.PollIndex
public import Lemmas.Flow.NthEv
public import Lemmas.Flow.NotTensor
public import Lemmas.Flow.NotCommit

@[expose] public section

/-! # The hypotheses of a pair TMA ring slot

A proof tool. A slot of a ring fed by TMA copies from both CTAs of a `cta_group::2` pair
(`Slot`): one full barrier `full` in the leader CTA, one empty barrier `empty a` in the CTA of
rank `a`; the producer thread `prod a` of each CTA polls its CTA's empty barrier, and `nc`
consumer threads `cons b` poll the full barrier. Per use, the leader's producer arrives once
on `full`, expecting all of the use's `tx = 2 n · bytes` bytes, and each producer issues `n`
copies of `bytes` bytes completing on `full`; each consumer commits once with the leader's
empty barrier as its mbarrier, notifying the empty barrier of every rank (`rankOf a`).

`Hyp` is what the thread layer of a kernel supplies for one slot:

* the sources of the records of `full` (`FullSource`): its initialization, polls, the leader
  producer's arrivals (each after more successful polls of `empty 0` than its earlier
  arrivals), and copy completions; and every copy issue completing on `full` is a producer's,
  after more successful polls of its empty barrier than its earlier issues over `n` (`issue`);
* the sources of the records of `empty a` (`EmptySource`): its initialization, polls, and the
  consumers' commit notifications (each after more successful polls of `full` than its earlier
  commits);
* each barrier is initialized first, once, without fault (`InitFirst`), with count `1` for
  `full` and `nc` for `empty a`, and is never invalidated;
* the polls' parities: a consumer's successful polls of `full` have the parity of their count,
  a producer's of `empty a` the parity of their count plus one; every successful poll is the
  poll of a canonical spin, and a successful poll of the slot's barriers acquires at cluster scope;
* the producers and consumers are threads of one cluster. -/

namespace PTX.PairTmaRing

open AsyncCopy Flow
open MBarrier hiding okPolls

/-- A slot of a pair TMA ring with `nc` consumers. -/
structure Slot (nc : Nat) where
  /-- The full barrier, in the leader CTA. -/
  full : Loc
  /-- The empty barrier of the CTA of rank `a`. -/
  empty : Fin 2 → Loc
  /-- The producer thread of the CTA of rank `a`. -/
  prod : Fin 2 → Nat
  /-- The consumer threads. -/
  cons : Fin nc → Nat
  /-- The copies per use of each producer. -/
  n : Nat
  /-- The bytes of each copy. -/
  bytes : Nat

/-- The bytes of a use: `n` copies of each of the two producers. -/
def Slot.tx {nc : Nat} (S : Slot nc) : Nat := 2 * S.n * S.bytes

/-- The commit rank of producer `a`'s CTA. -/
def rankOf (a : Fin 2) : Fin 16 := ⟨a.val, by omega⟩

/-- Object `m`, once it has a record, is first initialized with count `c`, without fault, and
has no other initialization. -/
def InitFirst (X : Execution) (m : Loc) (c : Nat) : Prop :=
  ∀ r ∈ X.objects m, ∃ r0, (X.objects m)[0]? = some r0 ∧ r0.action = .init c ∧
    r0.fault = none ∧ ∀ q ∈ X.objects m, (∃ n, q.action = .init n) → q = r0

variable {nc : Nat}

/-- How a record of the full barrier arises. -/
inductive FullSource (X : Execution) (S : Slot nc) (r : Record Ref) : Prop
  | init {n : Nat} (ha : r.action = .init n)
  | poll {g j pc p : Nat} {ok acq : Bool} {sc : MbarScope} (hid : r.id = .thread (g, j))
      (he : X.get (g, j) = some ⟨pc, .wait S.full p ok acq sc⟩) (ha : r.action = .pollParity p ok)
  | arrive {j pc : Nat} {rel : Bool} {sc : MbarScope} (hid : r.id = .thread (S.prod 0, j))
      (he : X.get (S.prod 0, j) = some ⟨pc, .arrive S.full S.tx 1 rel sc⟩)
      (ha : r.action = .arrive 1 S.tx)
      (hb : arrivals S.full ((X.tr (S.prod 0)).take j) + 1 ≤
        okPolls (S.empty 0) ((X.tr (S.prod 0)).take j))
  | copy {g j pc al : Nat} {sp : TensorCopy.Spec} (hid : r.id = .async (g, j) (.notify .load))
      (he : X.get (g, j) = some ⟨pc, .tensorIssue al sp⟩) (hm : sp.mbar = S.full)
      (ha : r.action = .completeTx S.bytes)

/-- How a record of the empty barrier of rank `a` arises. -/
inductive EmptySource (X : Execution) (S : Slot nc) (a : Fin 2) (r : Record Ref) : Prop
  | init {n : Nat} (ha : r.action = .init n)
  | poll {g j pc p : Nat} {ok acq : Bool} {sc : MbarScope} (hid : r.id = .thread (g, j))
      (he : X.get (g, j) = some ⟨pc, .wait (S.empty a) p ok acq sc⟩)
      (ha : r.action = .pollParity p ok)
  | notify {b : Fin nc} {j pc : Nat} {sp : TcCommit.Spec}
      (hid : r.id = .async (S.cons b, j) (.tcNotify (rankOf a)))
      (he : X.get (S.cons b, j) = some ⟨pc, .tc (.commit sp)⟩) (hm : sp.mbar = S.empty 0)
      (htg : TcCommit.target sp (rankOf a) = some (S.empty a)) (ha : r.action = .arrive 1 0)
      (hb : ((X.tr (S.cons b)).take j).countP (commitsTo (S.empty 0)) + 1 ≤
        okPolls S.full ((X.tr (S.cons b)).take j))

/-- **The thread-layer hypotheses of a pair TMA ring slot.** -/
structure Hyp (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) (S : Slot nc) :
    Prop where
  /-- Each producer copies at least once per use. -/
  n_pos : 0 < S.n
  /-- Each copy has bytes. -/
  bytes_pos : 0 < S.bytes
  /-- The slot has a consumer. -/
  nc_pos : 0 < nc
  /-- Twice a use's bytes are within the transaction counter's range. -/
  tx_le : 2 * S.tx ≤ limit
  /-- The producers are distinct threads. -/
  prod_inj : Function.Injective S.prod
  /-- The consumers are distinct threads. -/
  cons_inj : Function.Injective S.cons
  /-- The records of the full barrier. -/
  full_src : ∀ r ∈ X.objects S.full, FullSource X S r
  /-- The records of the empty barriers. -/
  empty_src : ∀ a, ∀ r ∈ X.objects (S.empty a), EmptySource X S a r
  /-- A copy issue completing on the full barrier is a producer's, within its budget. -/
  issue : ∀ {g k pc al : Nat} {sp : TensorCopy.Spec},
    X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩ → sp.mbar = S.full →
    ∃ a, g = S.prod a ∧ ((X.tr g).take k).countP (issuesTo S.full) + 1 ≤
      S.n * okPolls (S.empty a) ((X.tr g).take k)
  /-- The full barrier is initialized first with count one. -/
  full_init : InitFirst X S.full 1
  /-- The empty barriers are initialized first with count `nc`. -/
  empty_init : ∀ a, InitFirst X (S.empty a) nc
  /-- No record of the slot's barriers is an invalidation. -/
  full_noInval : NoInval (X.objects S.full)
  empty_noInval : ∀ a, NoInval (X.objects (S.empty a))
  /-- A successful poll of the full barrier has the parity of the thread's earlier ones. -/
  full_parity : ∀ {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
    X.get (g, k) = some ⟨pc, .wait S.full p true acq sc⟩ →
      p % 2 = (okPolls S.full ((X.tr g).take k) + 0) % 2
  /-- A successful poll of an empty barrier has the parity of the thread's earlier ones, plus
  one. -/
  empty_parity : ∀ {a : Fin 2} {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
    X.get (g, k) = some ⟨pc, .wait (S.empty a) p true acq sc⟩ →
      p % 2 = (okPolls (S.empty a) ((X.tr g).take k) + 1) % 2
  /-- Every successful poll is the poll of a canonical spin (DEP-CANONICAL-SPIN). -/
  spins : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
    ∃ exit, K.CanonicalSpin pc exit
  /-- A successful poll of the full barrier acquires at cluster scope. -/
  full_acq : ∀ {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
    X.get (g, k) = some ⟨pc, .wait S.full p true acq sc⟩ → acq = true ∧ sc = .cluster
  /-- A successful poll of an empty barrier acquires at cluster scope. -/
  empty_acq : ∀ {a : Fin 2} {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
    X.get (g, k) = some ⟨pc, .wait (S.empty a) p true acq sc⟩ → acq = true ∧ sc = .cluster
  /-- The producers and the consumers are threads of one cluster. -/
  cluster : ∀ a b, L.clusterOfCta (S.prod a / L.block) = L.clusterOfCta (S.cons b / L.block)

/-- A copy's bytes are at most a use's. -/
theorem Hyp.bytes_le_tx {L : Launch} {K : Kernel} {A : List Assumption} {X : Execution}
    {S : Slot nc} (H : Hyp L K A X S) : S.bytes ≤ S.tx := by
  have := H.n_pos
  unfold Slot.tx
  nlinarith

end PTX.PairTmaRing
