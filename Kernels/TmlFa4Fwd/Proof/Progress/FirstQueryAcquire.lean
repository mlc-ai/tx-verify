-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.FirstQueryReadyPhase
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReady
import Kernels.TmlFa4Fwd.Proof.Thread.FirstQueryReadyOperands
import Kernels.TmlFa4Fwd.Proof.Thread.MmaFirstGroupShuffles
import Kernels.TmlFa4Fwd.Proof.Thread.MmaFirstQueryProgress
import Kernels.TmlFa4Fwd.Proof.Protocol.QueryFaults
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.AsyncCopy PTX.MBarrier Prologue Thread.Output Epilogue

private theorem queryReadyPhaseOfPriorSuccess {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} {r : Record Ref} (hr : r ∈ X.objects (queryObject l cta 0))
    (hSuccess : r.reply.waited = some true) :
    let log := X.objects (queryObject l cta 0)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  let loc := queryObject l cta 0
  let log := X.objects loc
  obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hr
  have hChecked := X.objects_checked hX loc
  obtain ⟨initial,q,hInitial,hAction,hParity,_⟩ := hChecked.okPoll hj hSuccess
  have hZero : q = 0 := by
    cases record_source hX.tma.2.2.1 hr with
    | wait _ he ha =>
      have hSame := (Action.pollParity.inj (hAction.symm.trans ha)).1
      exact hSame.trans (firstQueryReadyPollParity hp hX he rfl)
    | init _ _ ha | inval _ _ ha | arrive _ _ ha | increment _ _ ha
    | tensor _ _ _ ha | commit _ _ _ ha | arriveOn _ _ _ _ ha | bulk _ _ _ _ ha
    | clc _ _ _ _ ha => rw [hAction] at ha; cases ha
  have hPositive : 0 < initial.phase := by
    subst q
    omega
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  obtain ⟨s,hs,hMono⟩ := hChecked.phase_mono hNo (List.getElem?_eq_some_iff.mp hj).1.le
    (Nat.le_refl _) hInitial
  have hUpper := (Protocol.Query.queryHistoryRange hp hX 0 hr (Nat.le_refl _) hs).1
  exact ⟨s,hs,by omega⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
include hp hMax hFrame

/-- Once the Q0 object has reached phase one, the selected MMA lane records its opening
Q acquire. It also records its opening K acquire if the K0 object is in phase one. -/
theorem openingAcquiresOfReadyPhase {g batch : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hReady : let log := X.objects (queryObject l (g/l.block) 0)
      ∃ s, stateBefore log log.length = some s ∧ s.phase = 1) :
    (∃ j e, X.get (g,j) = some e ∧
      e.kind = .wait (queryObject l (g/l.block) 0) 0 true true .cta) ∧
    ((let log := X.objects (Thread.Mma.Observation.readyObject l g 0)
      ∃ s, stateBefore log log.length = some s ∧ s.phase = 1) →
      ∃ j, Thread.Mma.ReadyPoll l X g j 0 0 true .cta ∧
        (Thread.Mma.atPrefix l X g j).kvAcquires 0 = 0) := by
  have hCuQ : DrainCuQProtected p X :=
    hp.cuQ_protected (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame)
  have hUsedK : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4*batch)).at k) := by
    intro k hk w a bs hWrite
    apply hFrame.input_unwritten hp (region := ⟨p.usedKBase,4*p.batch⟩)
    · simp [Params.inputRegions]
    · exact ⟨rfl,rfl,by dsimp [globalLoc,Loc.at]; omega,by dsimp [globalLoc,Loc.at]; omega⟩
    · exact hWrite
  obtain ⟨pos,t,u,o,hPos,hBound,_,_,hRelease,hAt,hPrefix,hLocal,hRun⟩ :=
    Thread.Allocation.mmaMetadataOfMaximal hp hMax hg hw hCuQ hb hLo hHi
  obtain ⟨n,after,v,he,hPast,hTail,hStep,hV⟩ := Mma.selectedFirstQueryWaitOfMaximal hp hMax hg hb
    (assignedCoordinates_valid hp hLo hHi).1 hAt
    (fun lane hl => hCuQ _ (by omega)) hUsedK hReady hPrefix hLocal hRun hPos hBound hRelease
  refine ⟨⟨pos+3+n,_,he,rfl⟩,fun hKey => ?_⟩
  exact Mma.firstKeyWaitAfterQueryOfMaximal hp hMax hg hw
    (hV.mono ⟨hV.2.2.2.2.1,hV.2.2.2.2.2.1,trivial⟩) hKey hPast hStep hTail
    (Nat.succ_pos _) (len_of_get he) (releasedIfLast he (by intro h; cases h))

/-- An active CTA reaches Q0 phase one after the selected loader delivers its two boxes.
A prior successful acquire gives the same phase from the object history. -/
theorem openingQueryReadyPhaseOfMaximal {cta batch : Nat} (hc : cta < l.grid) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ cta) (hHi : cta < tilePrefix p (batch + 1) * p.heads) :
    let log := X.objects (queryObject l cta 0)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  by_cases hSome : ∃ r ∈ X.objects (queryObject l cta 0), r.reply.waited = some true
  · obtain ⟨r, hr, hSuccess⟩ := hSome
    exact queryReadyPhaseOfPriorSuccess hp hMax.1 hr hSuccess
  · let loader := cta * l.block + 448
    have hCta : loader / l.block = cta := by dsimp [loader]; rw [hp.block]; omega
    have hw : warpIndex l loader = 14 := by
      simp only [warpIndex, loader, hp.block]
      omega
    have hg : loader < l.threads := by simp only [Launch.threads, loader, hp.block]; omega
    exact hCta ▸ selectedQueryReadyPhaseOfMaximal hp hMax hFrame hg hw hb
      (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (hCta.symm ▸ hSome)

end PTX.Kernels.TmlFa4Fwd.Progress
