-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.ScheduleGeometry
public import Kernels.TmlFa4Fwd.Proof.SchedulerArith
public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Kernels.TmlFa4Fwd.Flow.Code.Part046
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Flow.Sites.Part000
public import Lemmas.Flow.Run
public import Lemmas.Flow.MemTmpl
public import Lemmas.Isa.Rule
public import Mathlib.Tactic.FinCases
public import Lemmas.Flow.WarpScan
public import Kernels.TmlFa4Fwd.Flow.Code.Part044
public import Kernels.TmlFa4Fwd.Flow.Code.Part045
public import Kernels.TmlFa4Fwd.Flow.Code.Part047
public import Lemmas.Arith.WarpPrefix
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Local
public import Lemmas.Flow.SegChain
public import Kernels.TmlFa4Fwd.Proof.OutputGeometry
public import Kernels.TmlFa4Fwd.Proof.OutputLayout
public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The two shuffle operands are bounded before a scheduler addition. -/
theorem groupPrefixOperands_fit {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {first lane : Nat} (hf : first ≤ p.batch) (hl : lane < 32) (stage : Fin 5) :
    prefixWindow (groupLaneTiles p first) (2 ^ stage.val) lane +
        prefixWindow (groupLaneTiles p first) (2 ^ stage.val)
          (shflSource .up lane (2 ^ stage.val) 0).1 < 2 ^ 32 := by
  have hLeft := hp.groupWindow_signed hf hl (2 ^ stage.val)
  have hSource : (shflSource .up lane (2 ^ stage.val) 0).1 < 32 := by
    rw [firstScanSource]
    split
    · exact lt_of_le_of_lt (Nat.sub_le ..) hl
    · exact hl
  have hRight := hp.groupWindow_signed hf hSource (2 ^ stage.val)
  omega

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
