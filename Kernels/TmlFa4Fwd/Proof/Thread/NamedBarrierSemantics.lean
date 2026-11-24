-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarriers
public import Kernels.TmlFa4Fwd.Proof.Thread.Exit
import Lemmas.Protocol.NamedBarMember
import Lemmas.Order.DependencyWitness

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX CtaBarrier NamedBar

/-- The trace cursor of a named barrier observed by one thread. -/
def observedBarrierOrdinal (X : Execution) (i : EvId) (id : Nat) : Nat :=
  ((X.tr i.1).take i.2).countP (Execution.isBarId id)

/-- A recorded arrival increases the lane's count beyond its own arrival ordinal. -/
theorem barrierArrivalExtent {X : Execution} {g pos id : Nat} {count : Option Nat} {mode : BarMode}
    (h : BarrierArrival X (g,pos) id count mode) :
    observedBarrierOrdinal X (g,pos) id < (X.tr g).countP (Execution.isBarId id) := by
  obtain ⟨e, he, hk⟩ := h
  change (X.tr g)[pos]? = some e at he
  have hCount : ((X.tr g).take (pos + 1)).countP (Execution.isBarId id) =
      observedBarrierOrdinal X (g,pos) id + 1 := by
    rw [List.take_add_one, he]
    simp [observedBarrierOrdinal, hk, Execution.isBarId]
  calc
    observedBarrierOrdinal X (g,pos) id < ((X.tr g).take (pos+1)).countP
        (Execution.isBarId id) := by rw [hCount]; omega
    _ ≤ (X.tr g).countP (Execution.isBarId id) := (List.take_sublist _ _).countP_le

variable {l : Launch} {m : Mem0} {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
include hX

/-- A synchronization with a later continuing event reached a released named generation. -/
theorem barrierSyncReturned {i : EvId} {id : Nat} {count : Option Nat}
    (hWait : BarrierArrival X i id count .sync) (hPass : i.2+1 < (X.tr i.1).length) :
    ∃ key, CtaBarK l X i key ∧ CtaBarDone l X (i.1/l.block) key := by
  obtain ⟨⟨pc,kind⟩, he, hk⟩ := hWait
  change kind = _ at hk
  subst kind
  exact ctaBarDone_of_returned hX he hPass

/-- Each participant is witnessed at a released synchronization by its generation's arrival
or by an exit counted by the same barrier history. -/
theorem releasedMemberWitness {p : Finset Nat} {f : EvId} {id : Nat} {count : Option Nat} {g : Nat}
    (hSrc : NamedBar.Sources l X count p id) (hShape : NamedBar.Shape l count p id)
    (hWait : BarrierArrival X f id count .sync) (hPass : f.2+1 < (X.tr f.1).length)
    (hCta : g/l.block = f.1/l.block) (hMember : g % l.block /32 ∈ p) :
    ∃ j, Witness l X (.thread (g,j)) f ∧
      ((∃ mode, BarrierArrival X (g,j) id count mode ∧
          observedBarrierOrdinal X (g,j) id = observedBarrierOrdinal X f id) ∨
        ∃ e, X.get (g,j) = some e ∧ e.kind = .exit) := by
  obtain ⟨⟨pc,kind⟩, he, hk⟩ := hWait
  change kind = _ at hk
  subst kind
  obtain ⟨key, hf, hReleased⟩ := ctaBarDone_of_returned hX he hPass
  let ordinal := observedBarrierOrdinal X f id
  let cta := f.1/l.block
  let lane := g % l.block
  have hKey : key = id + 16 * ordinal :=
    hSrc.arrival_key hX hShape he (CtaBarK.arrival hf)
  have hIdBound := hShape.id_lt
  have hRem : key % 16 = id := by omega
  have hQuot : key / 16 = ordinal := by omega
  obtain ⟨finish, hReleaseKey⟩ := hReleased
  have hComplete : CompletesAt l.block (X.barriers cta) finish id ordinal := by
    simpa only [hRem, hQuot] using hReleaseKey
  obtain ⟨r, s, t, hr, hs, ht, _, hAfter⟩ := hComplete
  have hRun : CtaBarrier.run l.block {} ((X.barriers cta).take (finish+1)) = .ok t := by
    rw [List.take_add_one, hr, run_append, hs]
    simp [CtaBarrier.run, ht, Except.bind]
  have hCtaLt : cta < l.grid := cta_lt hf.1
  have hLane : lane < l.block := Nat.mod_lt _ (block_pos_of_thread_lt hf.1)
  have hGlobal : cta*l.block + lane = g := by
    dsimp [cta, lane]
    rw [← hCta, Nat.mul_comm]
    exact Nat.div_add_mod g l.block
  have hAt {k : Nat} {row : Record EvId}
      (hx : ((X.barriers cta).take (finish+1))[k]? = some row) :
      k ≤ finish ∧ (X.barriers cta)[k]? = some row := by
    have hLen := (List.getElem?_eq_some_iff.mp hx).1
    simp only [List.length_take] at hLen
    have hk : k < finish+1 := by omega
    exact ⟨by omega, List.getElem?_take_of_lt hk ▸ hx⟩
  by_cases hExit : lane ∈ t.exited
  · obtain ⟨event, hMem⟩ := run_exited_mem hRun hExit
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hMem
    obtain ⟨hBefore, hRow⟩ := hAt hk
    obtain ⟨_, hOwner, site, hGet⟩ :=
      (hX.ctaBar.2 cta hCtaLt).2.1 _ (List.mem_of_getElem? hRow)
    have hLaneEvent : event.1 = g := hOwner.trans hGlobal
    obtain ⟨other,j⟩ := event
    change other = g at hLaneEvent
    subst other
    have hRefs : (g,j) ∈ (Record.exit lane (g,j)).refs := by simp [Record.refs]
    have hCount : CtaBarCounted l X f (g,j) :=
      ⟨key, finish, hf, hReleaseKey, k, _, hRow, hRefs, hBefore, .inr ⟨lane,rfl⟩⟩
    have need := ctaBarCounted_witnessed l X f (g,j) he
      (List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? hRow, hRefs⟩) hCount
    exact ⟨j, Witness.of_need l need ⟨_,hGet⟩ rfl, .inr ⟨⟨site,.exit⟩,hGet,rfl⟩⟩
  · obtain ⟨k, lanes, event, hPrefix, hIn, hGen⟩ := completed_participant_record
      (phase := ordinal) (hSrc.completed hX hCtaLt (finish+1))
      hShape.pos hShape.target rfl hShape.bound hRun (by rw [hAfter]; omega)
      hLane hMember hExit
    obtain ⟨_, hRow⟩ := hAt hPrefix
    obtain ⟨_, hOwner, site, mode, hGet⟩ :=
      (hX.ctaBar.2 cta hCtaLt).2.1 _ (List.mem_of_getElem? hRow) (lane,event) hIn
    have hLaneEvent : event.1 = g := hOwner.trans hGlobal
    obtain ⟨other,j⟩ := event
    change other = g at hLaneEvent
    subst other
    have hThread : g < l.threads := by
      rw [← hGlobal]
      exact cta_thread_lt hCtaLt hLane
    have hGenFull : GenerationOf l.block (X.barriers (g/l.block)) (g,j) id ordinal := by
      change g/l.block = cta at hCta
      rw [hCta]
      simpa only [List.take_append_drop] using hGen.append (ys := (X.barriers cta).drop (finish+1))
    have hArrival := CtaBarArrivalK.of_generation (e := (g,j)) hX.ctaBar hThread hIdBound hGenFull
    have hArrivalKey := hSrc.arrival_key hX hShape hGet hArrival
    have hId : observedBarrierOrdinal X (g,j) id = ordinal := by
      change id + 16 * ordinal = id + 16 * observedBarrierOrdinal X (g,j) id at hArrivalKey
      omega
    rw [← hKey] at hArrival
    exact ⟨j, Witness.of_ctaBarCounted hf hReleaseKey hArrival hCta,
      .inl ⟨mode, ⟨⟨site,.bar id count mode⟩,hGet,rfl⟩, hId⟩⟩

/-- A participant with sufficient extent has an arrival of the synchronization's generation. -/
theorem memberBarrierArrival {p : Finset Nat} {f : EvId} {id : Nat} {count : Option Nat} {g : Nat}
    (hSrc : NamedBar.Sources l X count p id) (hShape : NamedBar.Shape l count p id)
    (hWait : BarrierArrival X f id count .sync) (hPass : f.2+1 < (X.tr f.1).length)
    (hCta : g/l.block = f.1/l.block) (hMember : g % l.block /32 ∈ p)
    (hExited : Exited X g → ∃ j mode, BarrierArrival X (g,j) id count mode ∧
      observedBarrierOrdinal X (g,j) id = observedBarrierOrdinal X f id) :
    ∃ j mode, BarrierArrival X (g,j) id count mode ∧
      observedBarrierOrdinal X (g,j) id = observedBarrierOrdinal X f id := by
  obtain ⟨⟨pc,kind⟩, he, hk⟩ := hWait
  change kind = _ at hk
  subst kind
  obtain ⟨j, site, mode, hj, hn⟩ :=
    hSrc.member_arrival_any hX hShape he hPass hCta hMember (by
      rintro ⟨stop,site,hExit⟩
      obtain ⟨k, mode, ⟨⟨source,kind⟩, hGet, hKind⟩, hOrd⟩ :=
        hExited ⟨stop,⟨site,.exit⟩,hExit,rfl⟩
      change kind = _ at hKind
      subst kind
      exact ⟨k,source,mode,hGet,hOrd⟩)
  exact ⟨j,mode,⟨⟨site,.bar id count mode⟩,hj,rfl⟩,hn⟩

/-- The observed kind participates in the already released generation at its trace ordinal. -/
theorem barrierArrivalKeyOfReleased {p : Finset Nat} {i : EvId} {id : Nat} {count : Option Nat}
    {mode : BarMode} (hSrc : NamedBar.Sources l X count p id) (hShape : NamedBar.Shape l count p id)
    (hArrives : BarrierArrival X i id count mode)
    (hReleased : CtaBarrier.Released l.block (X.barriers (i.1/l.block)) id
      (observedBarrierOrdinal X i id)) :
    CtaBarArrivalK l X i (id + 16 * observedBarrierOrdinal X i id) := by
  obtain ⟨⟨pc,kind⟩, he, hk⟩ := hArrives
  change kind = _ at hk
  subst kind
  exact hSrc.key_of_released hX hShape he (Step.CtaBar.thread_lt_of_get hX he) hReleased

end PTX.Kernels.TmlFa4Fwd.Thread
