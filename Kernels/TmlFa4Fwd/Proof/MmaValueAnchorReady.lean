-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaValueAnchorTrace

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- Project shuffles in the two value paths after their common release election. -/
def valueAnchorShuffle (e : Event) : Option Event :=
  if (2307 ≤ e.pc ∧ e.pc < 2534 ∨ 2558 ≤ e.pc) ∧ Execution.isShfl e then some e else none

private theorem valueAnchorErases (i : Fin 3) (e : Event)
    (h : (readyInterval (([2,3,7] : List (Fin 9))[i])).lo ≤ e.pc ∧
      e.pc < (readyInterval (([2,3,7] : List (Fin 9))[i])).hi) :
    valueAnchorShuffle e = none := by
  fin_cases i <;> simp [readyInterval] at h <;>
    simp [valueAnchorShuffle, show ¬ (2307 ≤ e.pc ∧ e.pc < 2534 ∨ 2558 ≤ e.pc) by omega]

private theorem valueWaitFromAnchor {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s 2272 (readyFrame l)) (hw : Walk kernel Assumptions.all l g s es vs)
    (hSome : es.filterMap valueAnchorShuffle ≠ []) :
    ∃ steady u pre tail post, es = pre ++ tail ∧ pre.filterMap valueAnchorShuffle = [] ∧
      At u (waitSite (initialValueWaitSite steady)).pc (initialValueWaitFacts l steady) ∧
      Walk kernel Assumptions.all l g u tail post :=
  initialValueWaitThroughRoute valueAnchorShuffle valueAnchorErases
    ⟨rfl,hs.2⟩ (by rw [hs.1]; decide) hw hSome hp

/-- Any observed shuffle after the common value branch passed the actual slot-one wait. -/
theorem valueSuccessFromAnchor {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s 2272 (readyFrame l)) (hw : Walk kernel Assumptions.all l g s es vs)
    (hSome : es.filterMap valueAnchorShuffle ≠ []) :
    ∃ steady u pre tail post, es = pre ++ tail ∧ pre.filterMap valueAnchorShuffle = [] ∧
      At u ((waitSite (initialValueWaitSite steady)).pc + 3) (initialValueWaitFacts l steady) ∧
      Walk kernel Assumptions.all l g u tail post ∧
      0 < (pre.filterMap readyEvent).length := by
  obtain ⟨steady,t,pre,fromWait,visits,hSplit,hPre,ht,htWalk⟩ := valueWaitFromAnchor hp hs hw hSome
  have hFrom : fromWait.filterMap valueAnchorShuffle ≠ [] := by
    simpa [hSplit,hPre] using hSome
  let i := initialValueWaitSite steady
  have hAddr : readyAddr l 1 < 2^32 := by
    have := hp.shared.2.1
    simp [readyAddr, readyStage, MbarRing.Index.slot] at ⊢
    omega
  have hAlign : readyAddr l 1 % 8 = 0 := by
    have := hp.shared.1
    simp [readyAddr, readyStage, MbarRing.Index.slot] at ⊢
    omega
  have hFresh : ∀ pair ∈ initialValueWaitFacts l steady, pair.1 ≠ (waitSite i).result := by
    cases steady <;> simp [i,initialValueWaitFacts,initialValueWaitSite,waitSite,ringFrame,
      readyFrame]
  have hBase : ((waitSite i).base, b32 (readyAddr l 1)) ∈ initialValueWaitFacts l steady := by
    simp [i,initialValueWaitFacts]
  have hPhase : ((waitSite i).phase, b32 0) ∈ initialValueWaitFacts l steady := by
    cases steady <;> simp [i,initialValueWaitFacts,initialValueWaitSite,waitSite,ringFrame,
      readyWord,MbarRing.Index.round]
  rcases waitWalk i hAddr hAlign (show 0 < 2 by decide) hFresh hBase hPhase ht htWalk with
    ⟨n,hOnly⟩ | ⟨n,tail,hAfter,hReturn⟩
  · exact (hFrom (by simp [hOnly, valueAnchorShuffle, Execution.isShfl])).elim
  have hClean (ok : Bool) : valueAnchorShuffle
      ⟨(waitSite i).pc, .wait ⟨.shared,g/l.block,readyAddr l 1⟩ 0 ok true .cta⟩ = none := by
    simp [valueAnchorShuffle, Execution.isShfl]
  rcases hReturn with rfl | ⟨u,post,_,hu,huWalk⟩
  · exact (hFrom (by simp [hAfter, hClean, List.filterMap_append])).elim
  let seen : List Event := List.replicate n
    ⟨(waitSite i).pc, .wait ⟨.shared,g/l.block,readyAddr l 1⟩ 0 false true .cta⟩ ++
    [⟨(waitSite i).pc, .wait ⟨.shared,g/l.block,readyAddr l 1⟩ 0 true true .cta⟩]
  refine ⟨steady,u,pre++seen,tail,post,?_,?_,hu,huWalk,?_⟩
  · simp [hSplit,hAfter,seen,List.append_assoc]
  · simp [seen,hPre,hClean]
  · have hSite : (List.finRange 4).any (fun j => readyHead j == (waitSite i).pc) = true := by
      cases steady <;> decide
    have hMark : readyEvent
        ⟨(waitSite i).pc,.wait ⟨.shared,g/l.block,readyAddr l 1⟩ 0 true true .cta⟩ =
        some (⟨.shared,g/l.block,readyAddr l 1⟩,0) := by
      simp [readyEvent,hSite]
    simp [seen,hMark,List.filterMap_append]

end
end PTX.Kernels.TmlFa4Fwd.Mma
