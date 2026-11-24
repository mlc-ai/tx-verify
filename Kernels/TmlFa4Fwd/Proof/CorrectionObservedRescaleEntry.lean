-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionLseWriters
public import Kernels.TmlFa4Fwd.Proof.CorrectionWarpRescaleSetup

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue Prologue

noncomputable section

private theorem nextAfterEarlierEvent {X : Execution} {g pos index : Nat}
    {first target : Event} (hStart : pos ≤ index)
    (he : X.get (g,pos) = some first) (hTarget : X.get (g,index) = some target)
    (hPC : first.pc < target.pc) : pos+1 ≤ index := by
  have hNe : pos ≠ index := by
    intro h
    subst index
    obtain rfl := Option.some.inj (he.symm.trans hTarget)
    omega
  omega

/-- A lane that reaches the body after the first two waits has read the protected request
lengths and entered the rescale decision with the selected tile's exact trip count. -/
theorem correctionLaneBeforeRescaleOfEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g batch lane pos index : Nat} {target : Event} {s : TState} {result : Option TState}
    (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch+1) * p.heads)
    (hs : At s 7932 (correctionActiveTileFacts p l g batch lane))
    (hr : Run kernel Assumptions.all l (warpLane l g lane) s
      ((X.tr (warpLane l g lane)).drop pos) result)
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4*i)).at k))
    (hPos : pos ≤ index) (hLate : 7988 < target.pc)
    (he : X.get (warpLane l g lane,index) = some target) :
    let thread := warpLane l g lane
    ∃ u, At u 7989 (correctionBeforeRescale p l g batch lane) ∧ pos+6 ≤ index ∧
      X.get (thread,pos+3) = some ⟨7985,.bar (statsBarrierId l thread 0) (some 64) .sync⟩ ∧
      X.get (thread,pos+4) =
        some ⟨7987,.arrive ⟨.shared,thread/l.block,l.sharedBase+192⟩ 0 1 true .cta⟩ ∧
      X.get (thread,pos+5) = some ⟨7988,.bar (statsBarrierId l thread 1) (some 64) .sync⟩ ∧
      Run kernel Assumptions.all l thread u ((X.tr thread).drop (pos+6)) result := by
  dsimp only
  let tile := (assignedCoordinates p batch (g/l.block)).1
  let thread := warpLane l g lane
  let F := tileSetupFrame p l g batch lane
  let H := (1634,b32 (p.qOffset batch)) :: (1635,b32 (p.qLength batch)) :: F
  have hLen : index < (X.tr thread).length := (List.getElem?_eq_some_iff.mp he).1
  have hMore {n : Nat} (hn : n ≤ index) : (X.tr thread).drop n ≠ [] := by
    intro h
    have hDrop := List.drop_eq_nil_iff.mp h
    omega
  obtain ⟨t,ht,hAt⟩ := correctionInputRun hp hb hs
  have hT : At t 7955 (correctionInputFacts p batch tile ++ F) := by
    simpa only [tile,F,tileSetupFrame,List.append_assoc] using hAt
  have hF : ∀ rv ∈ F, rv.1 ∉ [1634,5958,5959] := by
    intro rv hm hRead
    have hm' := List.mem_map_of_mem (f := Prod.fst) hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRead
    rcases hRead with h | h | h <;> rw [h] at hm' <;>
      exact (of_decide_eq_true rfl : _ ∉ F.map Prod.fst) hm'
  obtain ⟨v,hV,hv,he0,he1,he2,_⟩ := correctionTripReadsFromSuffix hp hX hb hT hF
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (hUsedK batch hb)
    (hr.after_local_nonempty (run_rtg ht) (hMore hPos))
    (.inr ⟨index,target,hPos,by omega,he⟩)
  have hPos1 := nextAfterEarlierEvent hPos he0 he (by change 7955 < target.pc; omega)
  have hPos2 := nextAfterEarlierEvent hPos1 he1 he (by change 7956 < target.pc; omega)
  have hPos3 := nextAfterEarlierEvent hPos2 he2 he (by change 7959 < target.pc; omega)
  have hOld : Holds v.regs H :=
    ⟨hV.2.2.2.2.2.2.2.1,hV.2.2.2.2.2.2.1,hV.2.2.2.2.2.2.2.2⟩
  have hCountAt : At v 7960
      ([(5959,b32 (p.kLength batch)),(7276,b32 tile),(1635,b32 (p.qLength batch))] ++ H) :=
    hV.mono ⟨hV.2.2.2.2.1,hV.2.2.2.2.2.1,hV.2.2.2.2.2.2.1,hOld⟩
  have hTile : 256*tile < p.qLength batch := (assignedCoordinates_valid hp hLo hHi).1
  obtain ⟨w,hw,hW⟩ := correctionTripAndRowWithFrame hp thread hb hTile
    (by set_option maxRecDepth 100000 in kernel_rfl) v hCountAt
  have hFrame : At w 7985 (correctionBeforeRescale p l g batch lane) := hW
  have hPos3' : pos+3 ≤ index := by omega
  obtain ⟨u,he3,he4,he5,hU,hu⟩ := observeCorrectionStartSyncPrefix hp hFrame
    (by simp [correctionBeforeRescale,tileSetupFrame,correctionTileGeometryFacts])
    (by simp [correctionBeforeRescale,tileSetupFrame,correctionTileGeometryFacts])
    (by simp [correctionBeforeRescale,tileSetupFrame,correctionActiveTileFacts,
      correctionTileFrame,afterCreditFacts,creditFacts,entryFacts,nonzeroBarrierFacts])
    (by
      intro rv hm
      have hm' := List.mem_map_of_mem (f := Prod.fst) hm
      constructor <;> intro h <;> rw [h] at hm' <;>
        exact (of_decide_eq_true rfl : _ ∉
          (correctionBeforeRescale p l g batch lane).map Prod.fst) hm')
    (hv.after_local_nonempty (run_rtg hw) (hMore hPos3'))
    (.inr ⟨index,target,hPos3',hLate,he⟩)
  have hPos4 := nextAfterEarlierEvent hPos3' he3 he (by change 7985 < target.pc; omega)
  have hPos5 := nextAfterEarlierEvent hPos4 he4 he (by change 7987 < target.pc; omega)
  have hPos6 := nextAfterEarlierEvent hPos5 he5 he (by change 7988 < target.pc; omega)
  exact ⟨u,hU,by omega,he3,he4,he5,hu⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
