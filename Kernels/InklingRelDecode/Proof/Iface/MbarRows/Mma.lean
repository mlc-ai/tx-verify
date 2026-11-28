-- SPDX-License-Identifier: Apache-2.0
-- iface: MbarRow.Mma producer=W status=row-proved domain=consistent ahead=1
module

public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Base

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
namespace MbarRow
open PTX PTX.Flow PTX.MbarRow

def MmaAt (L : Launch) (g pc : Nat) : Prop :=
  g % L.block / 32 = 7 ∧ (2422 ≤ pc ∧ pc < 2557)

def mmaSites : List PTX.MbarRow.Site :=
  [⟨2462, none, .wait (.reg 545)⟩,
   ⟨2499, some (10, false), .commit⟩,
   ⟨2510, none, .wait (.reg 558)⟩,
   ⟨2546, some (15, false), .commit⟩,
   ⟨2548, some (15, false), .commit⟩,
   ⟨2553, some (18, false), .commit⟩]

theorem mma_sites : regionOk kernel.code 2422 2557 mmaSites = true := by
  decide +kernel

/-- The producer proves the register values selecting each object and parity
and the number of bytes of any tensor copy. The site check certifies the decoded operands. -/
inductive MmaUse (L : Launch) (X : Execution) (g k : Nat) (e : Event) (l : Loc) : Prop where
  | readyWait (pc : e.pc = 2462) (addr : l = loc L g (Iface.kvReady (slot3 (roundAt X g k 2462))))
      (wait : Wait e l (roundAt X g k 2462 / 3 % 2))
  | pWait (pc : e.pc = 2510) (addr : l = loc L g (Iface.pReady (slot2 (roundAt X g k 2510))))
      (wait : Wait e l (roundAt X g k 2510 / 2 % 2))
  | sCommit (pc : e.pc = 2499) (addr : l = loc L g (Iface.sReady (slot2 (roundAt X g k 2462 - 1))))
      (commit : Commit e l)
  | emptyCommit (pc : e.pc = 2546)
      (addr : l = loc L g (Iface.kvEmpty (slot3 (roundAt X g k 2510 - 1))))
      (commit : Commit e l)
  | doneCommit (pc : e.pc = 2548) (addr : l = loc L g Iface.oDone) (commit : Commit e l)
  | finalCommit (pc : e.pc = 2553) (addr : l = loc L g Iface.oFinal) (commit : Commit e l)

end MbarRow

def MbarRow.Mma (_Q : Params) (L : Launch) (X : Execution) : Prop :=
  Row L X (MmaAt L) (MmaUse L X)

end PTX.Kernels.InklingRelDecode.Proof
