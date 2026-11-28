-- SPDX-License-Identifier: Apache-2.0
-- iface: MbarRow.Place producer=C status=row-proved domain=consistent ahead=1
module

public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Startup
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Prologue
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Softmax
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Epilogue
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Dispatch
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Loader
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Mma

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX MbarRow

/-- Every launched lane naming a barrier meets the warp and PC conditions of its role. -/
def MbarRow.Place (_Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k e l}, g < L.threads → X.get (g,k) = some e → Frame.MbarOf e l →
    StartupAt L g e.pc ∨
    PrologueAt L g e.pc ∨
    SoftmaxAt L g e.pc ∨
    EpilogueAt L g e.pc ∨
    DispatchAt L g e.pc ∨
    LoaderAt L g e.pc ∨
    MmaAt L g e.pc

end PTX.Kernels.InklingRelDecode.Proof
