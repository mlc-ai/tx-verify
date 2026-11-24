-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.EpilogueOutputProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputReadyHistory
import Lemmas.Step.PollProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof

noncomputable section

private theorem writebackModel {l : Launch} {g : Nat} {u : TState} (hu : WritebackPc u.pc) :
    out kernel Assumptions.all l g u = out kernel [] l g u :=
  epilogue_out_all_eq_nil (.inl ⟨by omega,by omega⟩)

variable {p : Params}

private theorem readyContinuation {l : Launch} {m : Mem0} (hp : Pre p l m) {g batch tile head : Nat}
    (hb : batch < p.batch) (ht : 256 * tile < p.qLength batch) (stage : Fin 2) (ok : Bool)
    {u : TState} {F : List (Nat × Value)} (hF : ∀ item ∈ F, item.1 ∉ writebackWrites)
    (hAt : At u (writebackPc (some (.ready stage)))
      (writebackFacts p l batch head tile (some (.ready stage)))) (hRegs : Holds u.regs F) :
    ∃ v, Relation.ReflTransGen (Tau kernel Assumptions.all l g)
      (next (setReg u (readyReg stage) (.pred ok))) v ∧
      At v (writebackPc (writebackSuccessor (.ready stage) ok))
        (writebackFacts p l batch head tile (writebackSuccessor (.ready stage) ok)) ∧
      Holds v.regs F := by
  have hFired : Fires u.pc (writebackTemplate p l g batch head tile (.ready stage) u)
      ⟨u.pc,.wait (readyLoc l g stage) 0 ok true .cta⟩
      (some (next (setReg u (readyReg stage) (.pred ok)))) :=
    ⟨ok,rfl,rfl⟩
  obtain ⟨_,v,n,hr,hv,hFrame,_⟩ := writebackStep hp g (.ready stage) hb ht hAt hFired
  have hRange : WritebackPc (next (setReg u (readyReg stage) (.pred ok))).pc := by
    change WritebackPc (u.pc+1)
    rw [hAt.1]
    fin_cases stage <;> decide
  refine ⟨v,writebackLiftLocal (fun h => writebackModel h) hRange (run_rtg hr),?_,?_⟩
  · simpa only [writebackSucceeded] using hv
  · apply holdsSchedulerFrame (regs := F.map Prod.fst) hRegs
    · intro r hr
      obtain ⟨item,hm,rfl⟩ := List.mem_map.mp hr
      exact hFrame item.1 (hF item hm)
    · intro item hm
      exact List.mem_map_of_mem hm

/-- An output lane at a ready wait acquires the stage after its correction cohort publishes. -/
theorem outputReadyPollOfMaximal {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch tile head : Nat} (hg : g < l.threads)
    (hb : batch < p.batch) (hh : head < p.heads) (ht : 256 * tile < p.qLength batch) (stage : Fin 2)
    (hPublished : ∀ lane < 128, ∃ j,
      Thread.CorrectionReady X (Thread.Output.sourceLane l (g,0) lane,j) stage)
    {F : List (Nat × Value)} (hF : ∀ item ∈ F, item.1 ∉ writebackWrites) {pos : Nat}
    {before t : TState} {ending : Option TState} (hPositive : 0 < pos)
    (hBound : pos ≤ (X.tr g).length) (hRelease : pos = (X.tr g).length → Step.Released l X g)
    (hAt : At t (writebackPc (some (.ready stage)))
      (writebackFacts p l batch head tile (some (.ready stage)))) (hRegs : Holds t.regs F)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some before))
    (hTail : Run kernel Assumptions.all l g before ((X.tr g).drop pos) ending)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before t) :
    ∃ j ≥ pos, ∃ v w,
      X.get (g,j) = some ⟨pollPc stage,.wait (readyLoc l g stage) 0 true true .cta⟩ ∧
      At w (writebackPc (some (.store stage 0)))
        (writebackFacts p l batch head tile (some (.store stage 0))) ∧
      Holds w.regs F ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some v) ∧
      Run kernel Assumptions.all l g v ((X.tr g).drop (j+1)) ending ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) v w ∧
      (X.tr g).drop pos =
        List.replicate (j-pos) ⟨pollPc stage,.wait (readyLoc l g stage) 0 false true .cta⟩ ++
        (⟨pollPc stage,.wait (readyLoc l g stage) 0 true true .cta⟩ :: (X.tr g).drop (j+1)) := by
  let pred := fun u : TState => At u (writebackPc (some (.ready stage)))
    (writebackFacts p l batch head tile (some (.ready stage))) ∧ Holds u.regs F
  let resume := fun u ok => next (setReg u (readyReg stage) (.pred ok))
  have hOut (u : TState) (hu : pred u) :
      u.pc = pollPc stage ∧
        out kernel Assumptions.all l g u =
          .ev (.wait (readyLoc l g stage) 0 (resume u) true .cta) := by
    have hPc := hu.1.1
    have hRange : WritebackPc u.pc := by rw [hPc]; fin_cases stage <;> decide
    exact ⟨hPc,(writebackModel hRange).trans (writebackOut hp g _ u hb hh ht hu.1)⟩
  have hRetry (u : TState) (hu : pred u) :
      ∃ v, Relation.ReflTransGen (Tau kernel Assumptions.all l g) (resume u false) v ∧ pred v := by
    obtain ⟨v,hLocal,hAt,hSaved⟩ := readyContinuation hp (g := g) hb ht stage false hF hu.1 hu.2
    exact ⟨v,hLocal,hAt,hSaved⟩
  have hReady : ∃ s, MBarrier.stateBefore (X.objects (readyLoc l g stage))
      (X.objects (readyLoc l g stage)).length = some s ∧ s.phase % 2 ≠ 0 % 2 := by
    obtain ⟨s,hState,hPhase⟩ :=
      Thread.Output.finalReadyPhaseOfPublications hp hMax.1 stage hPublished
    exact ⟨s,hState,by rw [hPhase]; decide⟩
  obtain ⟨n,u,hu,he,hRecorded,hRemaining,hTrace⟩ := Step.retrying_poll_of_maximal hMax
    Assumptions.wfStep hg hOut hRetry (fun _ _ _ => hReady)
    hPositive hBound hRelease ⟨hAt,hRegs⟩ hPrefix hTail hLocal
  obtain ⟨v,hPath,hv,hSaved⟩ := readyContinuation hp (g := g) hb ht stage true hF hu.1 hu.2
  exact ⟨pos+n,Nat.le_add_right ..,resume u true,v,he,hv,hSaved,hRecorded,hRemaining,hPath,
    by simpa only [Nat.add_sub_cancel_left] using hTrace⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
