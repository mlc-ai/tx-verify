-- SPDX-License-Identifier: Apache-2.0
-- iface: MbarRow.Softmax producer=S status=row-proved domain=consistent ahead=1
module

public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Base

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
namespace MbarRow
open PTX PTX.Flow PTX.MbarRow

def SoftmaxAt (L : Launch) (g pc : Nat) : Prop :=
  g % L.block / 32 < 4 ∧ ((574 ≤ pc ∧ pc < 2331) ∨ (2560 ≤ pc ∧ pc < 2565))

def softmaxSites : List PTX.MbarRow.Site :=
  [⟨1013, some (177, false), .arrive (.imm 0)⟩,
   ⟨1257, none, .wait (.reg 875)⟩,
   ⟨2239, none, .wait (.reg 1532)⟩]

theorem softmax_sites : regionOk kernel.code 574 2331 softmaxSites = true := by
  decide +kernel

theorem softmax_sites_1 : regionOk kernel.code 2560 2565 [] = true := by
  decide +kernel

/-- The producer proves the register values selecting each object and parity
and the number of bytes of any tensor copy. The site check certifies the decoded operands. -/
inductive SoftmaxUse (L : Launch) (X : Execution) (g k : Nat) (e : Event) (l : Loc) : Prop where
  | pArrive (pc : e.pc = 1013) (lead : g % L.block = 0)
      (addr : l = loc L g (Iface.pReady (slot2 (((X.tr g).take k).countP (fun a => a.pc == 1013)))))
      (arr : Arrive e l 0)
  | sWait (pc : e.pc = 1257) (addr : l = loc L g (Iface.sReady (slot2 (roundAt X g k 1257))))
      (wait : Wait e l (roundAt X g k 1257 / 2 % 2))
  | oWait (pc : e.pc = 2239) (addr : l = loc L g Iface.oDone)
      (wait : Wait e l (roundAt X g k 2239 % 2))

end MbarRow

def MbarRow.Softmax (_Q : Params) (L : Launch) (X : Execution) : Prop :=
  Row L X (SoftmaxAt L) (SoftmaxUse L X)

end PTX.Kernels.InklingRelDecode.Proof
