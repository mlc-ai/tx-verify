-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Table
import Kernels.InklingRelDecode.Proof.Common.Time

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof

/-- **A lane without events is at the allocation (pc 11) or the first barrier (pc 12).** -/
theorem init_pc {Q : Params} {L : Launch} {g : Nat} :
    (thread Q L g).pc (thread Q L g).init = 11 ∨ (thread Q L g).pc (thread Q L g).init = 12 := by
  have hi : (thread Q L g).pc (thread Q L g).init = (Startup.init L g).site.pc := by
    let P := Startup.code Q L g
    let R := Code.withStubs (frag Q L g) Startup.Entry.pc
    let E := Code.gatedExit (P := P) Startup.enterOf (sel L g)
    change (Code.glue P R E).pc (Code.enter P R E (Startup.init L g)) = _
    rw [Code.enter_none (Code.gatedExit_none.mpr (by unfold Startup.init; split <;> rfl))]
  rw [hi]
  unfold Startup.init
  split <;> simp [Startup.Site.pc]

end PTX.Kernels.InklingRelDecode.Proof
