-- SPDX-License-Identifier: Apache-2.0
-- iface: MbarRow.Prologue producer=P status=row-proved domain=consistent ahead=1
module

public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Base
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
namespace MbarRow
open PTX PTX.Flow PTX.MbarRow

def PrologueAt (L : Launch) (g pc : Nat) : Prop :=
  g % L.block / 32 < 4 ∧ (27 ≤ pc ∧ pc < 574)

def prologueSites : List PTX.MbarRow.Site :=
  [⟨134, some (26, false), .init (.imm 1)⟩,
   ⟨138, some (27, false), .init (.imm 1)⟩,
   ⟨142, some (28, false), .init (.imm 1)⟩,
   ⟨146, some (29, false), .init (.imm 1)⟩,
   ⟨150, some (30, false), .init (.imm 1)⟩,
   ⟨154, some (31, false), .init (.imm 1)⟩,
   ⟨158, some (32, false), .init (.imm 1)⟩,
   ⟨162, some (33, false), .init (.imm 1)⟩,
   ⟨166, some (34, false), .init (.imm 1)⟩,
   ⟨170, some (35, false), .init (.imm 1)⟩,
   ⟨174, some (36, false), .init (.imm 1)⟩,
   ⟨178, some (37, false), .init (.imm 1)⟩,
   ⟨193, some (177, false), .arrive (.imm 65536)⟩,
   ⟨211, some (54, false), .issue .tile⟩,
   ⟨217, some (55, false), .issue .tile⟩,
   ⟨226, some (56, false), .issue .tile⟩,
   ⟨231, some (57, false), .issue .tile⟩,
   ⟨237, some (177, false), .arrive (.imm 65536)⟩,
   ⟨253, some (64, false), .issue .tile⟩,
   ⟨259, some (65, false), .issue .tile⟩,
   ⟨268, some (66, false), .issue .tile⟩,
   ⟨273, some (67, false), .issue .tile⟩,
   ⟨279, some (177, false), .arrive (.imm 65536)⟩,
   ⟨295, some (73, false), .issue .tile⟩,
   ⟨301, some (74, false), .issue .tile⟩,
   ⟨310, some (75, false), .issue .tile⟩,
   ⟨315, some (76, false), .issue .tile⟩]

theorem prologue_sites : regionOk kernel.code 27 574 prologueSites = true := by
  decide +kernel

def initOffset (j : Fin 12) : Nat :=
  [213216,213248,213224,213256,213232,213264,213280,213296,213288,213304,213312,213328][j.val]!

def preloadCopies (s : Fin 3) : List Nat :=
  [[211,217,226,231],[253,259,268,273],[295,301,310,315]][s.val]!

/-- The producer proves the register values selecting each object and parity
and the number of bytes of any tensor copy. The site check certifies the decoded operands. -/
inductive PrologueUse (L : Launch) (X : Execution) (g k : Nat) (e : Event) (l : Loc) : Prop where
  | init (j : Fin 12) (pc : e.pc = 134 + 4*j.val)
      (addr : l = loc L g (initOffset j)) (kind : e.kind = .mbInit l 1)
      (warp : g % L.block < 32)
      (elect : ∃ i inst, i < k ∧
        X.get (g,i) = some ⟨(if j.val = 0 then 130 else e.pc-3),
          .elect 4294967295 inst (laneOf L g)⟩)
      (first : ((X.tr g).take k).countP (fun a => a.pc == e.pc) = 0)
      (bar0 : ((X.tr g).take k).countP (Execution.isBarId 0) = 2)
      (bar1 : ((X.tr g).take k).countP (Execution.isBarId 1) = 0)
  | preloadArrive (s : Fin 3) (pc : e.pc = ([193,237,279] : List Nat)[s.val]!)
      (addr : l = loc L g (Iface.kvReady s)) (arr : Arrive e l 65536)
  | preloadCopy (s : Fin 3) (pc : e.pc ∈ preloadCopies s)
      (addr : l = loc L g (Iface.kvReady s)) (issue : Issue e l 8192)

end MbarRow

def MbarRow.Prologue (Q : Params) (L : Launch) (X : Execution) : Prop :=
  Iface.KvPreload Q L X ∧ Row L X (PrologueAt L) (PrologueUse L X)

end PTX.Kernels.InklingRelDecode.Proof
