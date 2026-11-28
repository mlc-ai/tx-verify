-- SPDX-License-Identifier: Apache-2.0
-- iface: MbarRow.Loader producer=W status=row-proved domain=consistent ahead=1
module

public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Base

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
namespace MbarRow
open PTX PTX.Flow PTX.MbarRow

def LoaderAt (L : Launch) (g pc : Nat) : Prop :=
  g % L.block / 32 = 6 ∧ (2344 ≤ pc ∧ pc < 2422)

def loaderSites : List PTX.MbarRow.Site :=
  [⟨2374, none, .wait (.reg 579)⟩,
   ⟨2378, some (20, false), .arrive (.imm 65536)⟩,
   ⟨2389, some (21, false), .issue .tile⟩,
   ⟨2391, some (21, false), .issue .tile⟩,
   ⟨2394, some (22, false), .issue .tile⟩,
   ⟨2396, some (22, false), .issue .tile⟩,
   ⟨2404, some (23, false), .issue .tile⟩,
   ⟨2406, some (23, false), .issue .tile⟩,
   ⟨2410, some (24, false), .issue .tile⟩,
   ⟨2412, some (24, false), .issue .tile⟩]

theorem loader_sites : regionOk kernel.code 2344 2422 loaderSites = true := by
  decide +kernel

def loaderRound (Q : Params) (L : Launch) (X : Execution) (g k : Nat) :=
  Iface.preloadCount Q L (g / L.block) + roundAt X g k 2374

/-- The producer proves the register values selecting each object and parity
and the number of bytes of any tensor copy. The site check certifies the decoded operands. -/
inductive LoaderUse (Q : Params) (L : Launch) (X : Execution)
    (g k : Nat) (e : Event) (l : Loc) : Prop where
  | emptyWait (pc : e.pc = 2374)
      (addr : l = loc L g (Iface.kvEmpty (slot3 (loaderRound Q L X g k))))
      (wait : Wait e l (1 - loaderRound Q L X g k / 3 % 2))
  | readyArrive (pc : e.pc = 2378) (positive : 0 < roundAt X g k 2374)
      (addr : l = loc L g (Iface.kvReady (slot3 (loaderRound Q L X g k - 1))))
      (arr : Arrive e l 65536)
  | readyCopy (pc : e.pc ∈ [2389,2391,2394,2396,2404,2406,2410,2412])
      (positive : 0 < roundAt X g k 2374)
      (addr : l = loc L g (Iface.kvReady (slot3 (loaderRound Q L X g k - 1))))
      (issue : Issue e l 8192)

end MbarRow

def MbarRow.Loader (Q : Params) (L : Launch) (X : Execution) : Prop :=
  Row L X (LoaderAt L) (LoaderUse Q L X)

end PTX.Kernels.InklingRelDecode.Proof
