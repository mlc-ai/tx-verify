-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Access
public import Lemmas.Flow.MinCore
public import Lemmas.Flow.Regs

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof

/-- The register value a 32-bit load produces from the bytes it read. -/
noncomputable def loadWord (bs : List (Option Byte)) : Value := (rebuild 3 bs).toOption.getD (b32 0)

/-- The value register 1544 holds after the first minimum of the rescale decision. -/
noncomputable def minWord (x y : Value) : Value := (MinCore.minE [x, y]).toOption.getD (b32 0)

end PTX.Kernels.InklingRelDecode.Proof.Lib
