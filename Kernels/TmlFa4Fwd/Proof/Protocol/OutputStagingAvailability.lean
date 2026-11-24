-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.IdleOutputFree
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputReadyHistory
import Kernels.TmlFa4Fwd.Proof.OutputBarrierFacts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX PTX.MBarrier Prologue Epilogue Correction Thread.Output

private theorem freeCreditReadyAcquire {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} {i : EvId} {stage : Fin 2} (h : FreeCredit l X cta stage i) :
    ReadyAcquire l X i stage := by
  obtain ⟨⟨site, kind⟩, he, hPc, hKind⟩ := h
  change site = freePc stage at hPc
  change kind = _ at hKind
  subst site kind
  exact OutputWarp.readyBeforeFree hp hX stage he

/-- When one correction row has yet to publish, the output warp has not
returned any credit for that stage, and its original staging slot is available. -/
theorem freePhaseZeroBeforeCorrectionPublication {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    (stage : Fin 2) (hAbsent : ∀ j, ¬ Thread.CorrectionReady X (g,j) stage) :
    let log := X.objects (freeObject l (g/l.block) stage)
    ∃ state, stateBefore log log.length = some state ∧ state.phase = 0 := by
  apply freePhaseZeroOfNoUpdates hp hMax (NamedBar.cta_lt hg) stage
  intro record hr hUpdate
  obtain ⟨lane,pos,_,hCredit,_⟩ := freeUpdate hp hMax.1 stage hr hUpdate
  let issuer := outputLane l (g/l.block) lane
  have hCta : issuer/l.block = g/l.block := by
    unfold issuer outputLane
    rw [hp.block]
    have := lane.isLt
    omega
  let row := rowOf l g
  have hRow : row < 128 := Nat.mod_lt _ (by decide)
  have hSource : sourceLane l (issuer,pos) row = g := by
    unfold sourceLane row rowOf
    change issuer/l.block*l.block+256+(g%l.block)%128 = g
    rw [hCta]
    have hParts := Nat.div_add_mod g l.block
    change 8 ≤ (g%l.block)/32 ∧ (g%l.block)/32 < 12 at hWarp
    rw [hp.block] at hParts hWarp ⊢
    omega
  obtain ⟨pub,hPub⟩ := actualReadyIncludesEveryRow hp hMax.1
    (freeCreditReadyAcquire hp hMax.1 hCredit) (lane := row) hRow
  change Thread.CorrectionReady X (sourceLane l (issuer,pos) row,pub) stage at hPub
  exact hAbsent pub (by simpa only [hSource] using hPub)

end PTX.Kernels.TmlFa4Fwd.Protocol.Output
