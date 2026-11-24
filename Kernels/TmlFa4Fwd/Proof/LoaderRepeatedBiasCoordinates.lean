-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderBiasWarmCount
public import Kernels.TmlFa4Fwd.Proof.LoaderInputSites
import Kernels.TmlFa4Fwd.Flow.Code.Part018
import Kernels.TmlFa4Fwd.Flow.Code.Part021
import Lemmas.Flow.SegChain

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

/-- The two halves cover consecutive 64-column blocks of a warm Bias visit. -/
def warmBiasColumn (stage half : Fin 2) (iteration residualBit : Nat) : Nat :=
  128 * (8 + (if stage = 0 then residualBit else 0) - iteration) + 64 * half.val

def warmColumnStart (stage half : Fin 2) : Nat :=
  if stage = 0 then (if half = 0 then 1157 else 1167)
  else (if half = 0 then 1186 else 1195)

def warmColumnLength (stage : Fin 2) : Nat := if stage = 0 then 4 else 2

/-- The decoded warm Bias half among the loader's input instructions. -/
def warmBiasInputSite (stage half : Fin 2) : Fin 14 := ⟨8+2*stage.val+half.val,by
  have := stage.isLt
  have := half.isLt
  omega⟩

/-- The warm replay and the tensor form use the same physical issue. -/
theorem warmBiasInputSite_pc (stage half : Fin 2) :
    (inputSite (warmBiasInputSite stage half)).pc = warmBiasIssueSite stage half := by
  fin_cases stage <;> fin_cases half <;> rfl

/-- The decoded warm arithmetic uses the actual loop counter and the lower-stage
residual bit to produce the source column of its Bias half. -/
theorem warmBiasColumnSegment {l : Launch} {g iteration residualBit : Nat}
    (stage half : Fin 2) (hIteration : iteration < 9) (hBit : residualBit ≤ 1) :
    let site := inputSite (warmBiasInputSite stage half)
    Seg kernel [] l g (warmColumnLength stage) (warmColumnStart stage half)
      [(1090,b32 0),(7174,b32 iteration),(1117,b32 residualBit)]
      (warmColumnStart stage half + warmColumnLength stage)
      [(site.colReg,b32 (warmBiasColumn stage half iteration residualBit))] := by
  dsimp only
  fin_cases stage <;> fin_cases half <;> intro t ht
  all_goals
    dsimp [warmColumnLength,warmColumnStart,warmBiasColumn,inputSite,warmBiasInputSite] at ht ⊢
    seg_fp ht using
      (nf_simp [Nat.shiftLeft_eq]
       all_goals omega)

/-- A lower-stage residual Bias half uses the counter after the warm loop. -/
def residualBiasColumn (half : Fin 2) (counter : Nat) : Nat :=
  128*(9-counter) + 64*half.val

/-- After the warm loop, the optional Bias visit takes its column from the
remaining traversal counter and the selected half. -/
theorem residualBiasColumnSegment {l : Launch} {g counter : Nat}
    (half : Fin 2) (hCounter : counter ≤ 9) :
    let site := inputSite ⟨12+half.val,by have := half.isLt; omega⟩
    let start := if half = 0 then 1373 else 1380
    Seg kernel [] l g 1 start [(1143,b32 (128*counter))] (start+1)
      [(site.colReg,b32 (residualBiasColumn half counter))] := by
  dsimp only
  fin_cases half <;> intro t ht
  all_goals
    dsimp [residualBiasColumn,inputSite] at ht ⊢
    seg_fp ht using
      (nf_simp [Nat.shiftLeft_eq]
       all_goals omega)

end PTX.Kernels.TmlFa4Fwd.Loader
