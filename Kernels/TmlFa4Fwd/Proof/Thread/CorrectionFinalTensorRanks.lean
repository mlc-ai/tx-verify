-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTensorSchedule
public import Kernels.TmlFa4Fwd.Proof.OutputProtection
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTensorSchedule
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionRescalePass
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionRescaleSlots

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof Epilogue Prologue
open _root_.PTX.Kernels.TmlFa4Fwd.Correction

/-- Tensor collectives selected by this lane's actual rescale ballots. -/
def correctionFinalTensorBase (X : Execution) (g : Nat) : Nat :=
  (rescaleVoteSchedule (rescaleVoteLabels (X.tr g))).length

private theorem rescaleTensorBeforeFinal {votes : List (Fin 2 × BitVec 32)} {x : Nat × Fin 4}
    (h : x ∈ rescaleVoteSchedule votes) : x.1 < 8447 := by
  obtain ⟨⟨stage,word⟩,_,hm⟩ := List.mem_flatMap.mp h
  change x ∈ (if word = 0 then [] else rescaleSchedule stage) at hm
  split at hm
  · cases hm
  · have bound : (rescaleSchedule stage).all (fun ev => decide (ev.1 < 8447)) = true := by
      fin_cases stage <;> decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp bound x hm)

private theorem finalIndexOfSchedule {p : Params} {l : Launch} {X : Execution} {g n rank : Nat}
    (a : CorrectionSchedule p l X g) {label : Nat × Fin 4} (late : 8447 ≤ label.1)
    (known : (correctionTensorLabels (X.tr g))[n]? = some label)
    (plan : correctionFinalSchedule[rank]? = some label) :
    a.final = true ∧ n = correctionFinalTensorBase X g + rank := by
  let body := rescaleVoteSchedule (rescaleVoteLabels (X.tr g))
  obtain ⟨bound,elem⟩ := List.getElem?_eq_some_iff.mp known
  have atPlan := List.prefix_iff_getElem?.mp a.labels n bound
  rw [elem] at atPlan
  change (body ++ if a.final then correctionFinalSchedule else [])[n]? = some label at atPlan
  have lower : body.length ≤ n := by
    by_contra! h
    rw [List.getElem?_append_left h] at atPlan
    exact Nat.not_lt_of_ge late (rescaleTensorBeforeFinal (List.mem_of_getElem? atPlan))
  rw [List.getElem?_append_right lower] at atPlan
  have finish : a.final = true := by
    by_contra! h
    simp [h] at atPlan
  simp only [finish,↓reduceIte] at atPlan
  have k : n-body.length = rank :=
    (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.mp atPlan).1
      (by decide +kernel : correctionFinalSchedule.Nodup)).mp (atPlan.trans plan.symm)
  exact ⟨finish,by change n = body.length+rank; omega⟩

private theorem actualFinalIndex {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (frame : OutputFootprint p X)
    {g j rank : Nat} (lo : 8 ≤ warpIndex l g) (hi : warpIndex l g < 12)
    {e : Event} (he : X.get (g,j) = some e) (coll : isTcColl e = true)
    {op : Fin 4} (how : correctionTensorOperation e.kind = some op) (late : 8447 ≤ e.pc)
    (plan : correctionFinalSchedule[rank]? = some (e.pc,op)) :
    X.TcK (g,j) (correctionFinalTensorBase X g+rank) ∧
      ∃ a : CorrectionSchedule p l X g, a.final = true := by
  let n := ((X.tr g).take j).countP isTcColl
  have tc : X.TcK (g,j) n := ⟨⟨_,he,coll⟩,rfl⟩
  obtain ⟨-,hk⟩ := frame.metadataProtected hp
  obtain ⟨a⟩ := actualCorrectionSchedule hp hX hk lo hi tc
  obtain ⟨op',had,label⟩ := correctionTensorLabelAt (fun x hx => by
    obtain ⟨i,hi'⟩ := List.mem_iff_getElem?.mp hx
    exact correctionEventClass hp hX hi (show X.get (g,i) = some x from hi')) he coll
      (show _ = n from rfl)
  obtain rfl := Option.some.inj (had.symm.trans how)
  obtain ⟨final,index⟩ := finalIndexOfSchedule a late label plan
  exact ⟨index ▸ tc,a,final⟩

private theorem finalLoadLate (stage : Fin 2) (chunk : Fin 16) :
    8447 ≤ finalizeLoadPc stage chunk := by decide +revert

/-- The actual accumulator load ordinal includes every tensor operation
selected by previous rescale votes, for any number of KV visits. -/
theorem finalLoadRankOfRescales {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (frame : OutputFootprint p X)
    {g j : Nat} (lo : 8 ≤ warpIndex l g) (hi : warpIndex l g < 12) (stage : Fin 2) (chunk : Fin 16)
    {addr : Nat} {words : List Value}
    (he : X.get (g,j) = some ⟨finalizeLoadPc stage chunk,.tc (.ld addr words .s32x32b)⟩) :
    X.TcK (g,j) (correctionFinalTensorBase X g+(32*stage.val+2*chunk.val)) :=
  (actualFinalIndex hp hX frame lo hi he rfl rfl
    (finalLoadLate stage chunk) (finalScheduleLoadAt stage chunk)).1

/-- Two peers that have reached final loads completed the same rescale ballot
sequence. Their terminal Tensor Memory ordinals therefore start at the same base. -/
theorem finalLoadBasesAgree {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (frame : OutputFootprint p X)
    {g h j k : Nat} (hw : SameWarp l g h) (lo : 8 ≤ warpIndex l g) (hi : warpIndex l g < 12)
    (stage : Fin 2) (chunk : Fin 16) {a b : Nat} {u v : List Value}
    (left : X.get (g,j) = some ⟨finalizeLoadPc stage chunk,.tc (.ld a u .s32x32b)⟩)
    (right : X.get (h,k) = some ⟨finalizeLoadPc stage chunk,.tc (.ld b v .s32x32b)⟩) :
    correctionFinalTensorBase X g = correctionFinalTensorBase X h := by
  have late := finalLoadLate stage chunk
  have w : warpIndex l g = warpIndex l h := hw.2
  obtain ⟨_,a,ha⟩ := actualFinalIndex hp hX frame lo hi left rfl rfl late (finalScheduleLoadAt ..)
  obtain ⟨_,b,hb⟩ := actualFinalIndex hp hX frame (w ▸ lo) (w ▸ hi) right rfl rfl late
    (finalScheduleLoadAt ..)
  have equal : (rescaleVoteLabels (X.tr g)).length = (rescaleVoteLabels (X.tr h)).length :=
    (a.full ha).trans ((correctionScheduleBudget hw a b).trans (b.full hb).symm)
  obtain ⟨-,hk⟩ := frame.metadataProtected hp
  have same := correctionProjectedVotesPrefix hp hX hk hw lo hi a b equal.le
  exact congrArg (fun votes => (rescaleVoteSchedule votes).length) (same.eq_of_length_le equal.ge)

end PTX.Kernels.TmlFa4Fwd.Thread
