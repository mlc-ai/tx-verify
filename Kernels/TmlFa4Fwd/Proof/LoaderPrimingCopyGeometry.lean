-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderCopyGeometry
public import Kernels.TmlFa4Fwd.Proof.LoaderReuseCheckpoint
import Kernels.TmlFa4Fwd.Proof.LoaderSwizzleSetup

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The initial swizzle feeds both priming packets; V selects the second slot
using the constant immediate on each decoded copy. -/
def primingSwizzleFrame (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(1083, b32 (kvCopyAddress l.sharedBase 0 (g % l.block) 0 false)),
   (1084, b32 (kvCopyAddress l.sharedBase 0 (g % l.block) 1 false))]

private theorem primingSwizzlePreserved (stage : Fin 2) :
    ((kernel.code.drop 371).take (copyCommitPc (primingPacketSite stage) - 371)).all
      (fun ins => loaderPipelineCutOp 371 (copyCommitPc (primingPacketSite stage))
        (copyCommitPc (primingPacketSite stage) - 1) [1083, 1084] ins.op) = true := by
  fin_cases stage <;> (set_option maxRecDepth 100000 in kernel_rfl)

/-- Every actual priming copy from the initial swizzle covers its precise
CTA-local 16-byte vector, for every pair and either plane. -/
theorem primingCopyDestinationFromSwizzle {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g lower : Nat} (stage : Fin 2) (group : Fin 16) (upper : Bool)
    (hScope : lower ≤ 371)
    {s : TState} {events : List Event} {visits : List Visit}
    (hs : At s 371 (primingSwizzleFrame l g))
    (hw : Walk kernel Assumptions.all l g s events visits) {spec : AsyncCopy.Spec}
    (hSeen : ⟨packetPlanePc (primingPacketSite stage) group upper, .copy spec⟩ ∈
      loaderSliceEvents lower (copyCommitPc (primingPacketSite stage)) visits) :
    spec.dst = {loc := ⟨.shared, g / l.block,
      kvCopyAddress l.sharedBase stage (g % l.block) group upper⟩, size := 16} := by
  have hLimit : copyCommitPc (primingPacketSite stage) ≤ 1901 := by fin_cases stage <;> decide
  obtain ⟨t, u, hPc, hReg, hFire⟩ := loaderCopyWithRegisters (F := primingSwizzleFrame l g)
    hScope (by decide) hLimit (primingSwizzlePreserved stage) hw hs.1.ge
    (ringShapeOfAt hs) hs.2.2.2.2 hSeen rfl
  have hStage : packetStageShift (primingPacketSite stage) = stage := by fin_cases stage <;> decide
  have hRegDst : t.regs (packetDstReg (primingPacketSite stage) group) =
      some (b32 (kvCopyAddress l.sharedBase 0 (g % l.block) (group.val % 2) false)) := by
    have hEven : packetDstReg (primingPacketSite stage) group =
        if group.val % 2 = 0 then 1083 else 1084 := by fin_cases stage <;> rfl
    rw [hEven]
    split
    · simpa only [show group.val % 2 = 0 by assumption] using hReg.1
    · have h := Nat.mod_lt group.val (by decide : 0 < 2)
      simpa only [show group.val % 2 = 1 by omega] using hReg.2.1
  have h := packetCopyDestination hp (stage := 0) (primingPacketSite stage) group upper
    (by rw [hStage]; have := stage.isLt; omega) hPc hRegDst (by rw [hPc]; exact hFire)
  simpa only [hStage, Nat.zero_add] using h

/-- The swizzle computed before the priming packets is the one used by
the observed copy, retaining the original visit slice and trace. -/
theorem primingCopyDestinationFromEntry {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} (stage : Fin 2) (group : Fin 16) (upper : Bool)
    {s : TState} {events : List Event} {visits : List Visit}
    (hs : At s 356 [(1061, b32 (g % l.block)), (2535, b32 l.sharedBase)])
    (hw : Walk kernel Assumptions.all l g s events visits) {spec : AsyncCopy.Spec}
    (hSeen : ⟨packetPlanePc (primingPacketSite stage) group upper, .copy spec⟩ ∈
      loaderSliceEvents 356 (copyCommitPc (primingPacketSite stage)) visits) :
    spec.dst = {loc := ⟨.shared, g / l.block,
      kvCopyAddress l.sharedBase stage (g % l.block) group upper⟩, size := 16} := by
  obtain ⟨t, hr, ht⟩ := initialKvSwizzleRun hp hs
  obtain ⟨_, hTail, _, hMem⟩ := loaderEventAfterLocal hr hw hSeen
  exact primingCopyDestinationFromSwizzle hp stage group upper (by decide)
    (ht.mono ⟨ht.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.1, trivial⟩) hTail hMem

end
end PTX.Kernels.TmlFa4Fwd.Loader
