-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.AllocationTerminalExit
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxIdleArrival
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionIdleArrival
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Kernels.TmlFa4Fwd.Proof.OutputRegionTransparency
import Kernels.TmlFa4Fwd.Flow.Code.Part120
import Kernels.TmlFa4Fwd.Flow.Code.Part121
import Kernels.TmlFa4Fwd.Flow.Code.Part143

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof Prologue Epilogue MBarrier

noncomputable section

private theorem softmaxTerminalNext {l : Launch} {g : Nat} (warp : Fin 8) {t : TState}
    (ht : At t 7742 (Softmax.idleCarry l warp)) :
    ∃ v, v.pc = 9205 ∧ Next kernel Assumptions.all l g t v .exit := by
  let u := next (setReg t 5867 (b32 (warp.val/4*4)))
  let v := next (setReg u 681 (.pred true))
  have hFirst : run kernel [] l g 1 t = some u := by
    apply run_local Flow.code_7742 rfl ht
    rw [execLocalA_nil, execLocal_int rfl]
    have hWarp := ht.2.2.2.2.1
    fin_cases warp <;>
      simp only [execInt, readBits, readReg, hWarp, bind, Except.bind, pure, Except.pure, u] <;>
      rfl
  have hu : At u 7743 [(5867,b32 (warp.val/4*4))] :=
    (ht.set (r := 5867) (v := b32 (warp.val/4*4)) (by simp [Softmax.idleCarry])).mono
      ⟨rfl,trivial⟩
  have hSecond : run kernel [] l g 1 u = some v := by
    apply run_local Flow.code_7743 rfl hu
    rw [execLocalA_nil, execLocal_int rfl]
    have hReg := hu.2.2.2.2.1
    fin_cases warp <;>
      simp only [execInt, readBits, readReg, hReg, bind, Except.bind, pure, Except.pure, v] <;>
      rfl
  have hv : At v 7744 [(681,.pred true)] :=
    (hu.set (r := 681) (v := .pred true) (by simp)).mono ⟨rfl,trivial⟩
  obtain ⟨w, hThird, hw⟩ := run_bra (L := l) (g := g) (A := []) Flow.code_7744 true hv
    hv.2.2.2.2.1 (by simp)
  have hSteps : run kernel Assumptions.all l g 3 t = some w := by
    have model {s : TState} {p : Nat} {i : Instr} (h : s.pc = p)
        (hh : p ∈ [7742,7743,7744]) (hc : kernel.code[p]? = some i)
        (hi : Assumptions.coreOp i.op = true) :
        tauStep kernel Assumptions.all l g s = tauStep kernel [] l g s := by
      apply Assumptions.tauStep_all_eq_nil _ (h.symm ▸ hc) hi
      rw [h]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl | rfl <;> decide
    have h1 : run kernel Assumptions.all l g 1 t = some u := by
      simpa only [run, model ht.1 (by decide) Flow.code_7742 rfl] using hFirst
    have h2 : run kernel Assumptions.all l g 1 u = some v := by
      simpa only [run, model hu.1 (by decide) Flow.code_7743 rfl] using hSecond
    have h3 : run kernel Assumptions.all l g 1 v = some w := by
      simpa only [run, model hv.1 (by decide) Flow.code_7744 rfl] using hThird
    exact run_comp (run_comp h1 h2) h3
  have hOut : out kernel Assumptions.all l g w = .ev .exit := by
    rw [epilogue_out_all_eq_nil (by unfold EpiloguePc; rw [hw.1]; decide),
      out_event hw.2.2.2.1 (by rw [hw.1]; exact Flow.code_9205) rfl rfl]
    rfl
  exact ⟨w,hw.1,run_rtg hSteps,hOut⟩

private theorem idleSoftmaxExitFromArrival {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g j : Nat} (hg : g < l.threads) (hw : warpIndex l g < 8)
    {d : EvId} (hCta : g/l.block = d.1/l.block) (hDealloc : Deallocation X d)
    {t : TState} {o : Option TState} (he : FinalAllocationArrival X (g,j) .arrive)
    (ht : At t 7742 (Softmax.idleCarry l ⟨warpIndex l g,hw⟩))
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some t))
    (hTail : Run kernel Assumptions.all l g t ((X.tr g).drop (j+1)) o) :
    ∃ j e, X.get (g,j) = some e ∧ e.kind = .exit := by
  obtain ⟨u, _, hn⟩ := softmaxTerminalNext ⟨warpIndex l g,hw⟩ ht
  obtain ⟨site, _, hGet⟩ := he.decoded
  exact ⟨j+1,_,exitAtMaximalCursor hMax hg (by omega) (by exact len_of_get hGet)
    hPrefix hTail hn (fun h => he.releasedOfDeallocation hp hMax.1 hCta h hDealloc),rfl⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
include hp hMax hg

/-- The idle softmax lane records its actual exit after the allocator's deallocation. -/
theorem idleSoftmaxExitsOfDeallocationForBatches (hw : warpIndex l g < 8)
    (hCuQ : DrainCuQProtected p X) (hIdle : tilePrefix p p.batch * p.heads ≤ g/l.block)
    (hReady : ∀ stage : Fin 2,
      let log := X.objects (Correction.statsCreditLoc l (g/l.block) stage)
      ∃ s, stateBefore log log.length = some s ∧ s.phase = 0) {d : EvId}
    (hCta : g/l.block = d.1/l.block) (hDealloc : Deallocation X d) :
    ∃ j e, X.get (g,j) = some e ∧ e.kind = .exit := by
  obtain ⟨j,t,o,he,ht,hPrefix,hTail⟩ :=
    Softmax.idleFinalArrivalPrefixOfAllGroups hp hMax hg hw hCuQ hIdle hReady
  exact idleSoftmaxExitFromArrival hp hMax hg hw hCta hDealloc he ht hPrefix hTail

end
end PTX.Kernels.TmlFa4Fwd.Thread
