-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.NoIncRing
public import Lemmas.Order.OrderWaits

@[expose] public section

/-! # The order of a no-increment ring slot's copies and the consumer's reads

A proof tool, the `cp.async` counterpart of `SingleTmaRing.copy_before_read` and
`SingleTmaRing.read_before_copy` (lane T1's request for tml-fa4's K/V slots, whose packets are
`cp.async` copies completed by `cp.async.mbarrier.arrive.noinc` arrive-ons). Both are one step of
the chain those lemmas end with, from a record of the full or the empty barrier in the phase a
successful poll observes (the phase is the caller's: the ring's counts pin it):

* **RAW** (`copy_before_read`): a copy tracked by a lane's no-increment arrive-on, whose record
  is in the phase that the consumer's successful acquire poll of the full barrier observes
  (`NoIncObject.observes_copy`), is before every access of the consumer after the poll in program
  order, at every byte both cover;
* **WAR** (`read_before_copy`): an MMA read tracked by a commit, whose notification of the empty
  barrier is in the phase that a producer's successful acquire poll of it observes
  (`Consistent.observed_of_phase`), is before every access of the producer after the poll, in
  particular its next copy into the slot.

The other access is any part of an asynchronous operation issued after the poll (`AsyncBefore`
reaches it through program order from the poll, `po_of_source_not_access`). -/

namespace PTX.MbarRing
open AsyncCopy MBarrier

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- Program order from a poll to a later event of its thread. -/
theorem base_of_poll {c jw k pc parity : Nat} {m : Loc} {acq : Bool} {sc : MbarScope}
    (hw : X.get (c, jw) = some ⟨pc, .wait m parity true acq sc⟩) (hjk : jw < k)
    (hk : k < (X.tr c).length) : baseCausality L X (c, jw) (c, k) :=
  Relation.TransGen.single (Or.inl (po_of_source_not_access rfl hjk hk (by simp [hw, Event.acc])))

/-- **RAW: a copy before the consumer's later access.** A copy tracked by a no-increment
arrive-on whose record lies in the phase that a successful acquire poll of the full barrier
observes is before every access of the poller after the poll, at a byte both cover. -/
theorem NoIncObject.copy_before_read (hX : Consistent L K A mem0 X) {m : Loc} {n : Nat}
    (o : NoIncObject X m n) {u v phase pc parity c jw k : Nat} {r poll : Record Ref}
    {copy i : EvId} {sc : MbarScope} (hr : (X.objects m)[u]? = some r) (hclean : r.fault = none)
    (ha : r.action = .arrive 1 0) (hid : r.id = .async i .arriveOn)
    (hp : (X.objects m)[v]? = some poll) (hpid : poll.id = .thread (c, jw))
    (hsucc : poll.reply.waited = some true) (hphase : phaseAt (X.objects m) u = some phase)
    (hobs : observedAt (X.objects m) v = some phase)
    (hw : X.get (c, jw) = some ⟨pc, .wait m parity true true sc⟩)
    (ht : TracksCpAsync X copy i) (hsc : ScopesMeet L .cluster copy.1 sc c) (hjk : jw < k)
    (hk : k < (X.tr c).length) {b : Part} {l : Loc}
    (hca : AsyncCovers X copy (.write .copy) l) (hcb : AsyncCovers X (c, k) b l) :
    AsyncBefore L X l (copy, .write .copy) ((c, k), b) :=
  ⟨hca, hcb, Or.inl ⟨(c, jw), o.observes_copy hX hr hclean ha hid hp hpid hsucc hphase hobs hw ht
    hsc, base_of_poll hw hjk hk⟩⟩

/-- **WAR: an MMA read before the producer's later access.** An MMA read tracked by a commit
whose notification of the empty barrier lies in the phase that a successful acquire poll of it
observes is before every access of the poller after the poll (its next copy into the slot), at a
byte both cover. -/
theorem read_before_copy (hX : Consistent L K A mem0 X) {m : Loc}
    (hni : NoInval (X.objects m)) {u v phase pc parity c jw k : Nat} {rank : Fin 16}
    {r poll : Record Ref} {rd cmt : EvId} {s : TcCommit.Spec} {sc : MbarScope}
    (hr : (X.objects m)[u]? = some r) (hclean : r.fault = none) (hcu : CounterUpdate r.action)
    (hid : r.id = .async cmt (.tcNotify rank)) (htr : TracksMma X rd cmt)
    (hcm : X.Commit cmt s) (htg : TcCommit.target s rank = some m)
    (hn : rank ∈ X.tcNotified cmt)
    (hp : (X.objects m)[v]? = some poll) (hpid : poll.id = .thread (c, jw))
    (hsucc : poll.reply.waited = some true) (hphase : phaseAt (X.objects m) u = some phase)
    (hobs : observedAt (X.objects m) v = some phase)
    (hw : X.get (c, jw) = some ⟨pc, .wait m parity true true sc⟩)
    (hsc : ScopesMeet L .cluster rd.1 sc c) (hjk : jw < k) (hk : k < (X.tr c).length)
    {isB : Bool} {idx : Nat} {b : Part} {l : Loc}
    (hca : AsyncCovers X rd (.mmaRead isB idx) l) (hcb : AsyncCovers X (c, k) b l) :
    AsyncBefore L X l (rd, .mmaRead isB idx) ((c, k), b) := by
  have hob := hX.observed_of_phase hni hr hclean hcu hp hsucc hphase hobs
  rw [hid, hpid] at hob
  obtain ⟨_, w', m', acq, sc', he, ⟨⟨pc', parity', hget⟩, hbefore⟩, _⟩ := hob
  have hww := Ref.thread.inj he
  subst w'
  rw [hw] at hget
  cases hget
  exact ⟨hca, hcb, Or.inl ⟨(c, jw), Or.inr ⟨sc, ⟨_, m, ⟨cmt, s, rank, rfl, htr, hcm, htg, hn⟩,
    ⟨⟨pc, parity, hw⟩, hbefore⟩⟩, hsc⟩, base_of_poll hw hjk hk⟩⟩

end PTX.MbarRing
