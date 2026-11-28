-- SPDX-License-Identifier: Apache-2.0
-- iface: MbarRow.Epilogue producer=E status=row-proved domain=consistent ahead=1
module

public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Base

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
namespace MbarRow
open PTX PTX.Flow PTX.MbarRow

def EpilogueAt (L : Launch) (g pc : Nat) : Prop :=
  g % L.block / 32 < 4 ∧ ((2565 ≤ pc ∧ pc < 2853) ∨ (2855 ≤ pc ∧ pc < 2856))

def epilogueSites : List PTX.MbarRow.Site :=
  [⟨2565, none, .wait (.reg 1760)⟩]

theorem epilogue_sites : regionOk kernel.code 2565 2853 epilogueSites = true := by
  decide +kernel

theorem epilogue_sites_1 : regionOk kernel.code 2855 2856 [] = true := by
  decide +kernel

/-- The producer proves the register values selecting each object and parity
and the number of bytes of any tensor copy. The site check certifies the decoded operands. -/
inductive EpilogueUse (L : Launch) (X : Execution) (g k : Nat) (e : Event) (l : Loc) : Prop where
  | finalWait (pc : e.pc = 2565) (addr : l = loc L g Iface.oFinal) (wait : Wait e l 0)

end MbarRow

def MbarRow.Epilogue (_Q : Params) (L : Launch) (X : Execution) : Prop :=
  Row L X (EpilogueAt L) (EpilogueUse L X)

end PTX.Kernels.InklingRelDecode.Proof
