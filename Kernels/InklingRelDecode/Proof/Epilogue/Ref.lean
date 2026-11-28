-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Cnt

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue
open PTX PTX.Flow PTX.Proof Control

def Ref (d : D) (n : Nat) : Prop := n = polls d

theorem ref_init : Ref {} 0 := rfl

end PTX.Kernels.InklingRelDecode.Proof.Epilogue
