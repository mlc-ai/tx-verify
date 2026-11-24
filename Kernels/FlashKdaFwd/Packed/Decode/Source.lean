-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Transfers
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed
open PTX

def prepared : Except String Decode.Prepared :=
  let m := Generated.FlashKdaPacked.module
  Decode.prepare m.globals m.functions[0]!

set_option maxRecDepth 60000 in
set_option maxHeartbeats 8000000 in
theorem source_count : prepared.toOption.map (fun p => p.instrs.length) = some 3835 := by rfl

end FlashKda.Packed
