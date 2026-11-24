-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.FirstBiasRendezvous
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadRendezvous
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasPolls
import Kernels.TmlFa4Fwd.Proof.LoaderBiasTensorActor
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasVector

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Proof PTX.Assumption PTX.MBarrier PTX.AsyncCopy Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Softmax
open Thread.Loader

/-- A performed word read in the initial Bias vector sequence. -/
@[no_expose] def FirstBiasWordRead (X : Execution) (i : EvId) : Prop :=
  ∃ (vector : Fin 16) (a : Acc) (values : List (Option Byte)),
    X.get i = some ⟨biasReadPc false vector,.rd a values⟩

theorem FirstBiasWordRead.ofDecoded {X : Execution} {i : EvId} {v : Fin 16} {a : Acc}
    {values : List (Option Byte)} (he : X.get i = some ⟨biasReadPc false v,.rd a values⟩) :
    FirstBiasWordRead X i := ⟨v,a,values,he⟩

/-- A performed first Bias word is ordered through its actual proxy fence and
stage rendezvous whenever a Bias-empty return is already recorded. -/
theorem FirstBiasWordRead.fenceBeforeReturnInPrefix {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g read wait : Nat} {stage : Fin 2} (hWord : FirstBiasWordRead X (g,read))
    (hWait : FirstBiasAcquire l X g wait stage) (hWarp : warpIndex l g < 8)
    {empty : EvId} (hEmpty : X.Arrive empty (biasEmptyObject l (g/l.block) stage) 0 1 true .cta) :
    ∃ fence : Nat, X.IsProxyFence (g,fence) (.async (some (.shared .cta))) none ∧
      g < l.threads ∧ baseCausality l X (g,read) (g,fence) ∧ baseCausality l X (g,fence) empty := by
  have hReady : X.get (g,wait) = some ⟨3498,.wait (waitLoc l g stage 2) 0 true true .cta⟩ :=
    hWait
  have hAddr := congrArg Loc.addr (biasReadyWaitAddress hp hX hReady (by decide))
  have hStage : warpIndex l g/4 = stage.val := by
    change l.sharedBase+(320+8*stage.val) = l.sharedBase+(320+8*(warpIndex l g/4)) at hAddr
    omega
  obtain ⟨v,a,bytes,hDecoded⟩ := hWord
  have hRead : BiasVectorRead X (g,read) false v a bytes := hDecoded
  have hOrdinal := initialBiasReadOrdinal hp hX stage hRead
  obtain ⟨peer,ret⟩ := empty
  obtain ⟨site,hRet⟩ := hEmpty
  have hSite := actualBiasEmptyArrivalSite hp hX stage hRet rfl
  obtain ⟨_,_,_,_,_,hTarget⟩ := biasEmptyArriveFacts hp hX hRet hSite
  have hCta : g/l.block = peer/l.block := congrArg Loc.cta hTarget
  exact biasReadFenceBeforeReturn hp hX stage hRead hWarp hStage ⟨site,hRet⟩ hCta
    (hOrdinal.symm ▸ Nat.zero_le _)

/-- The actual loader wait observing a Bias-empty arrival is an acquire at CTA scope
and uses the exact same object as the arrival. -/
theorem reuseWaitObservesAtCTA {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {tensor empty : EvId} {stage half : Fin 2} {spec : TensorCopy.Spec} {k : Nat}
    (hIssue : BiasSubbox p l X tensor stage half spec)
    (hEmpty : X.Arrive empty (biasEmptyObject l (tensor.1/l.block) stage) 0 1 true .cta)
    (hObserve : MbarObserved X (.thread empty) (.thread (tensor.1,k))) :
    WaitObserves X (.thread empty) (tensor.1,k) (biasEmptyObject l (tensor.1/l.block) stage)
      true .cta := by
  obtain ⟨_,guard,loc,acq,scope,hGuard,hSeen,_⟩ := hObserve
  obtain rfl : guard = (tensor.1,k) := (Ref.thread.inj hGuard).symm
  obtain ⟨source,phase,hWait⟩ := hSeen.1
  obtain ⟨_,_,release,_,_,hRelease,hId,_⟩ := hSeen.2
  obtain ⟨pc,hArrive⟩ := hEmpty
  have hAction := ((hX.tma.2.2.1 loc).2.1 release (List.mem_of_getElem? hRelease)).1
  rw [hId] at hAction
  simp only [objectAction,hArrive] at hAction
  have hEqual : biasEmptyObject l (tensor.1/l.block) stage = loc := by
    by_contra hNe
    simp [hNe] at hAction
  subst loc
  have hWarp := PTX.Kernels.TmlFa4Fwd.Loader.biasTensorActorWarp hp hX hIssue
  obtain ⟨_,_,rfl,rfl⟩ := biasEmptyLoaderPollShape hp hX stage hWarp.ge hWait
  exact hSeen

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
