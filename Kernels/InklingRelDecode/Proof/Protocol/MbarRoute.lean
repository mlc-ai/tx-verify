-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SOOdone
public import Lemmas.Protocol.GatedFaults
public import Lemmas.Protocol.MultiObs
public import Lemmas.Order.DependencyWitness
public import Lemmas.Order.WaitOrderObject
public import Lemmas.Execution.ShapeExecution
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount

@[expose] public section

/-!
# The edges of the handshake's dependency paths

Part of the proof of the reuse paths of the S/P/O handshake (`MbarReach`). The paths are
`DepStep` paths (DEP-ORDER) between the issues of thread events and the notifications of commits.
This file has the nodes of the induction, the edges (`poll_guard`, `commit_notify`,
`rendezvous_path`), and the thread-layer and barrier premises the induction takes, as two named
structures:

* `Route`: what the roles' machines say about the order of events of one CTA's handshake
  (**premises, with rows in the development notes, "thread-layer gaps"**);
* `Bar128Witness`: the rendezvous of the 128-thread generations of named barrier 0 as a witness
  of the return of the passed `bar.sync` (what the named-barrier proof owes; its early
  generations are `BarEarly.early_same_ordinal_baseCausality`, in base causality form).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Mbar
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal)

noncomputable section

/-! ### The nodes -/

/-- The thread events of the launch (with a bound on the trace lengths). -/
def evs (L : Launch) (X : Execution) : Finset EvId :=
  Finset.range L.threads ×ˢ
    Finset.range (∑ g ∈ Finset.range L.threads, (X.tr g).length + 1)

open Classical in
/-- The nodes of the induction: the issues of the thread events and their commit
notifications. -/
def nodes (L : Launch) (X : Execution) : Finset (Ref × Bool) :=
  (evs L X).image (fun e => ((.thread e : Ref), false)) ∪
    (evs L X ×ˢ (Finset.univ : Finset (Fin 16))).image
      (fun q => ((.async q.1 (.tcNotify q.2) : Ref), false))

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

theorem evs_mem (hX : Consistent L K A mem0 X) {e : EvId} {ev : Event}
    (he : X.get e = some ev) : e ∈ evs L X := by
  have hg := event_thread_lt hX he
  have hl := len_of_get he
  have h3 := Finset.single_le_sum (f := fun g => (X.tr g).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hg)
  exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hg, Finset.mem_range.mpr (by omega)⟩

theorem thread_mem (hX : Consistent L K A mem0 X) {e : EvId} {ev : Event}
    (he : X.get e = some ev) : ((.thread e : Ref), false) ∈ nodes L X := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (evs_mem hX he))

theorem notify_mem (hX : Consistent L K A mem0 X) {e : EvId} {ev : Event} (rank : Fin 16)
    (he : X.get e = some ev) : ((.async e (.tcNotify rank) : Ref), false) ∈ nodes L X := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(e, rank),
    Finset.mem_product.mpr ⟨evs_mem hX he, Finset.mem_univ _⟩, rfl⟩)

/-! ### The edges -/

/-- A spinning successful poll resumes each later event with more successful polls before it. -/
theorem poll_guard
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, K.CanonicalSpin pc exit)
    {g k n : Nat} {m : Loc} (hk : k < (X.tr g).length) (h : n + 1 ≤ okPolls m ((X.tr g).take k)) :
    DepStep L K X (.thread (g, MbarRing.Poll.nth X m g n), true) (.thread (g, k), false) :=
  DepStep.of_resumes L (MbarRing.Poll.guard hspin hk h)

/-- A thread with more than `n` successful polls of `m` before an event made the poll with `n`
earlier ones. -/
theorem poll_lt {g k n : Nat} {m : Loc} (hk : k ≤ (X.tr g).length)
    (h : n + 1 ≤ okPolls m ((X.tr g).take k)) : n < okPolls m (X.tr g) := by
  have := MbarRing.Poll.okPolls_mono m (X.tr g) hk
  rw [List.take_of_length_le (le_refl _)] at this
  omega

/-- **The issue of a commit precedes its recorded notification.** -/
theorem commit_notify {y : EvId} {pc : Nat} {sp : TcCommit.Spec} {rank : Fin 16}
    (hy : X.get y = some ⟨pc, .tc (.commit sp)⟩) (hr : rank ∈ X.tcNotified y) :
    DepStep L K X (.thread y, false) (.async y (.tcNotify rank), false) :=
  DepStep.issue ⟨_, hy⟩ hr (fun _ h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h)

/-- **A record of a notification is a present commit's** targeting the object. -/
theorem notify_rec (hX : Consistent L K A mem0 X) {m : Loc} {r : MBarrier.Record Ref}
    {y : EvId} {rank : Fin 16} (hr : r ∈ X.objects m) (hid : r.id = .async y (.tcNotify rank)) :
    ∃ pc sp, X.get y = some ⟨pc, .tc (.commit sp)⟩ ∧ TcCommit.target sp rank = some m ∧
      rank ∈ X.tcNotified y := by
  have hp := object_record_present hX.tma hr
  rw [hid] at hp
  cases record_source hX.tma.2.2.1 hr with
  | init hid' => rw [hid] at hid'; cases hid'
  | inval hid' => rw [hid] at hid'; cases hid'
  | arrive hid' => rw [hid] at hid'; cases hid'
  | wait hid' => rw [hid] at hid'; cases hid'
  | tensor hid' => rw [hid] at hid'; cases hid'
  | increment hid' => rw [hid] at hid'; cases hid'
  | arriveOn hid' => rw [hid] at hid'; cases hid'
  | bulk hid' => rw [hid] at hid'; cases hid'
  | clc hid' => rw [hid] at hid'; cases hid'
  | commit hid' he ht =>
    rw [hid] at hid'
    cases hid'
    exact ⟨_, _, he, ht, hp⟩

/-- A witness of a `bar.sync`'s return precedes each later event of its thread. -/
theorem rendezvous_path {e f : EvId} {pc id : Nat} {cnt : Option Nat}
    (hf : X.get f = some ⟨pc, .bar id cnt .sync⟩) (hr : Witness L X (.thread e) f) {k : Nat}
    (hfk : f.2 < k) (hk : k < (X.tr f.1).length) :
    Relation.TransGen (DepStep L K X) (.thread e, false) (.thread (f.1, k), false) :=
  (Relation.TransGen.single (DepStep.of_witness L hr)).tail
    (DepStep.of_resumes L (Resumes.of_blocking (b := false) hf rfl ⟨rfl, hfk, hk⟩))

/-! ### The premises -/

/-- **The rendezvous of the 128-thread generations of named barrier 0.** Two threads of the
default partition of one CTA at `bar.sync 0, 128` events of the same ordinal (the number of their
earlier events on barrier 0) are in one generation: the event of the first is a witness of the
return of the second's passed `bar.sync` (`Witness.of_ctaBarCounted`: the arrival is counted by
the release the `bar.sync` waits for). It is what the named-barrier generation proof of barrier
0 owes in this form (`BarEarly.early_same_ordinal_baseCausality` is the base-causality form of
the first two generations); the development notes, "Protocol `Mbar`: premises". -/
def Bar128Witness (L : Launch) (X : Execution) : Prop :=
  ∀ {g p a y pc pc' : Nat}, g < L.threads → p < L.threads → g / L.block = p / L.block →
    g % L.block < 128 → p % L.block < 128 →
    X.get (g, a) = some ⟨pc, .bar 0 (some 128) .sync⟩ →
    X.get (p, y) = some ⟨pc', .bar 0 (some 128) .sync⟩ → y + 1 < (X.tr p).length →
    ((X.tr g).take a).countP (Execution.isBarId 0) = ((X.tr p).take y).countP
      (Execution.isBarId 0) →
    Witness L X (.thread (g, a)) (p, y)

/-- **What the roles' machines say about the order of events of one CTA's handshake.** CTA `c`,
the MMA warp's committing lane `cm`, the default partition's thread 0 `p0`, the softmax threads
`Soft` and the MMA warp's lanes `Mma`. Premises, one per row of "thread-layer gaps"
(the development notes, "Protocol `Mbar`: premises"); each is a statement about the events of the
roles' machines and none is a fact of the protocol. -/
structure Route (L : Launch) (K : Kernel) (X : Execution) (c cm p0 : Nat)
    (Soft Mma : Nat → Prop) : Prop where
  /-- Every poll spins (DEP-CANONICAL-SPIN). -/
  spin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
    ∃ exit, K.CanonicalSpin pc exit
  p0_soft : Soft p0
  cm_mma : Mma cm
  /-- A softmax thread is a launched thread of the default partition of CTA `c`. -/
  soft_thread : ∀ {h : Nat}, Soft h → h < L.threads ∧ h / L.block = c ∧ h % L.block < 128
  /-- Thread 0's arrival of use `u` on `p_ready b` follows its own polls of `s_ready b` for the
  uses up to `u` (the poll of the iteration comes first). -/
  arrive_polls : ∀ {i pc b : Nat} {sc : MbarScope}, b < 2 →
    X.get (p0, i) = some ⟨pc, .arrive (pReady L c b) 0 1 true sc⟩ →
      arrivals (pReady L c b) ((X.tr p0).take i) + 1 ≤ okPolls (sReady L c b) ((X.tr p0).take i)
  /-- **The meeting before the arrival.** Thread 0's arrival of use `u` on `p_ready b` (block
  `2 u + b`) is after a `bar.sync 0, 128` that every softmax thread also reaches, at the same
  ordinal, after its polls of `s_ready b` for the uses up to `u` and of `o_done` for the blocks up
  to `2 u + b` (the `o_done` poll of iteration `i` is its `i`-th). -/
  soft_bar : ∀ {i pc b h : Nat} {sc : MbarScope}, b < 2 →
    X.get (p0, i) = some ⟨pc, .arrive (pReady L c b) 0 1 true sc⟩ → Soft h →
      ∃ y a pc1 pc2, y < i ∧ X.get (p0, y) = some ⟨pc1, .bar 0 (some 128) .sync⟩ ∧
        X.get (h, a) = some ⟨pc2, .bar 0 (some 128) .sync⟩ ∧
        ((X.tr h).take a).countP (Execution.isBarId 0) =
          ((X.tr p0).take y).countP (Execution.isBarId 0) ∧
        arrivals (pReady L c b) ((X.tr p0).take i) + 1 ≤
          okPolls (sReady L c b) ((X.tr h).take a) ∧
        (1 ≤ 2 * arrivals (pReady L c b) ((X.tr p0).take i) + b →
          2 * arrivals (pReady L c b) ((X.tr p0).take i) + b ≤
            okPolls (oDone L c) ((X.tr h).take a))
  /-- The commit to `s_ready b` of use `t` follows the committing lane's polls of `p_ready b`
  for the uses before `t` (the PV half of the previous iteration). -/
  qk_polls : ∀ {i pc b : Nat} {sp : TcCommit.Spec}, b < 2 →
    X.get (cm, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = sReady L c b →
      ((X.tr cm).take i).countP (commitsTo (sReady L c b)) ≤
        okPolls (pReady L c b) ((X.tr cm).take i)
  /-- The commit to `o_done` of use `t` (the PV commit of block `t`) follows the lane's polls
  of `p_ready` for every block up to `t`: block `s` is the `(s / 2)`-th use of `p_ready (s % 2)`. -/
  pv_polls : ∀ {i pc : Nat} {sp : TcCommit.Spec},
    X.get (cm, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = oDone L c →
      ∀ s, s ≤ ((X.tr cm).take i).countP (commitsTo (oDone L c)) →
        s / 2 + 1 ≤ okPolls (pReady L c (s % 2)) ((X.tr cm).take i)
  /-- **The lanes of the MMA warp** (DEP-WARP-ELECT): a lane's poll of `p_ready b` for use `j`
  precedes, in the dependency order, the committing lane's commit to `s_ready b` of a use above
  `j`: the lane takes part in the election before the commit. -/
  lane_commit : ∀ {h b j i pc : Nat} {sp : TcCommit.Spec}, Mma h → h ≠ cm → b < 2 →
    X.get (cm, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = sReady L c b →
    j < ((X.tr cm).take i).countP (commitsTo (sReady L c b)) →
      j < okPolls (pReady L c b) (X.tr h) ∧
        Relation.TransGen (DepStep L K X)
          (.thread (h, MbarRing.Poll.nth X (pReady L c b) h j), true) (.thread (cm, i), false)

end
end PTX.Kernels.InklingRelDecode.Proof.Mbar
