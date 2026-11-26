-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Query.Lag
public import Lemmas.Protocol.TmaUnitsBlock
public import Lemmas.Protocol.UnitReachBlocker
public import Lemmas.Protocol.MbarUnitTx

@[expose] public section

/-! # The `qTma` wait row

The MMA lane waits on `qTma` at pc 1931 for its own arrival and its own eight tensor loads, so
the lane is its own producer and no time fact is needed: at the wait it has made the arrival and
the eight loads (`qTma_pre`), the object is used for one phase (its one arrival record of
count 1 bounds the phase by 1), and while the phase is 0 some load has not completed
(`TmaUnits.Obj.short`): an open tensor obligation, the blocker of `Sched.Blk`. The object's
records are fault-free by safety (`hff`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A lane with an arrival on `qTma` of CTA `c` is the CTA's MMA lane. -/
theorem qTma_lane (hR : MbarRows P L X) (hO : MmaOne L X) {c y : Nat} (hy : y < L.threads)
    (hA : 0 < arrivals (mbarLoc L c .qTma) (X.tr y)) : y = mmaLane L X c := by
  obtain ⟨e, hmem, hpe⟩ := List.countP_pos_iff.mp hA
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
  have he : X.get (y, k) = some e := hk
  obtain ⟨pc, kind⟩ := e
  cases kind with
  | arrive l tx cnt rel sc =>
    have hl : l = mbarLoc L c .qTma := by simpa [arrivesOn, sourceArrive] using hpe
    subst hl
    rcases qTma_use hR hy he rfl with ⟨n, hk'⟩ | ⟨hat, hc, -⟩
    · cases hk'
    · have := laneOn_eq hO he (fun _ h => by cases h) hat
      rw [hc] at this
      exact this
  | _ => simp [arrivesOn, sourceArrive] at hpe

/-- A checked history holds at most one record of a given identity. -/
theorem countP_id_le_one {ι : Type} [DecidableEq ι] {log : List (MBarrier.Record ι)}
    (hch : MBarrier.CheckedLog log) (R : ι) : log.countP (fun r => decide (r.id = R)) ≤ 1 := by
  have h := List.nodup_iff_count_le_one.mp hch.1 R
  rw [List.count, List.countP_map] at h
  exact (List.countP_congr fun r _ => by simp).trans_le h

/-- **The `qTma` wait row**: a lane whose next event is a failed poll of `qTma` of CTA `c` with
parity 0 is the CTA's MMA lane, and it is blocked as `Sched.WaitBlk` states. -/
theorem qTma_blk (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hRY : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows P L Y)
    (hI : InitRows L X) (hB : Bar0Rows L X) (hO : MmaOne L X) {c y pc : Nat} {ok : Bool}
    {sc : MbarScope}
    (hff : ∀ r ∈ X.objects (mbarLoc L c .qTma), r.fault = none)
    (hn : Sched.NextEv L kernel Assumptions.all m X y
      ⟨pc, .wait (mbarLoc L c .qTma) 0 ok true sc⟩) :
    y = mmaLane L X c ∧ Sched.WaitBlk (timed P L) X y (mbarLoc L c .qTma) 0 := by
  have hR := hRY X hX
  obtain ⟨hA1, hN8⟩ := qTma_pre hp hX hFw hRY hn
  have hy := qTma_lane hR hO (c := c) hn.lt (by omega)
  subst hy
  refine ⟨rfl, ?_⟩
  have o := qTma_obj hp hX hFw hR hI hB hO (c := c)
  have hitems := fun x (hx : x ∈ TmaUnits.S X _ _ 8 8192) => qTma_items o hN8.le hA1.le hx
  have hrec := Unit.arrivals_le_unitRec hX hff (mmaLane L X c)
  have hne : X.objects (mbarLoc L c .qTma) ≠ [] := by
    intro h
    rw [h, List.countP_nil] at hrec
    omega
  obtain ⟨st, hst⟩ := Unit.final_of_init hX o.init o.noInval hne
  refine ⟨st, hst, fun hpar => ?_⟩
  -- the phase is at most the arrival units, at most the one arrival record
  have hch := X.objects_checked hX (mbarLoc L c .qTma)
  have hexp := PairTmaRing.expected_of_init hX o.init o.noInval hst
  have hacc := (hch.accounted o.noInval le_rfl).2 st hst
  rw [hexp] at hacc
  simp only [MBarrier.unitsBefore, List.take_length] at hacc
  have hau := MBarrier.arrivalUnits_le_countP
    (xs := X.objects (mbarLoc L c .qTma))
    (fun r => decide (r.id = TmaUnits.it X (mbarLoc L c .qTma) (mmaLane L X c) 8 0 0))
    (fun r hr hf cnt tx ha => by
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
      obtain ⟨x, hx, h0, hid⟩ := TmaUnits.Obj.rec_zero o (by decide) hk hf ha
      have hx1 : x.1 = 0 := Finset.mem_singleton.mp h0
      have hx2 := hitems x hx
      refine ⟨(o.arrive hk ha).1, ?_⟩
      rw [hid, hx1, hx2]
      exact decide_eq_true rfl)
  have h1 := countP_id_le_one hch (TmaUnits.it X (mbarLoc L c .qTma) (mmaLane L X c) 8 0 0)
  by_cases htens : Descent.Obl L X .tensor
  · exact .inl ⟨.tensor, .inr (.inr (.inl rfl)), htens⟩
  · rcases TmaUnits.Obj.short hX o (by decide) hff htens hst
      (fun x hx => by rw [hitems x hx]; omega) with h | h <;> omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
