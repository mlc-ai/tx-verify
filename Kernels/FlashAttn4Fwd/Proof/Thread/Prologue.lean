-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Common
public import Kernels.FlashAttn4Fwd.Proof.Bars

@[expose] public section

/-! # The common prologue as abstract states

All 512 threads of a CTA run the prologue (PTX lines 39-249). Each thread reads the parameter
words the roles use (`seqlen_k`, the two divmod objects), broadcasts the dynamic shared base and
its warp index from lane 0 (`shfl0`, `shfl1`, `shfl2`). Warp 12 elects a lane that initializes
the Tensor Memory handshake barrier (`elect12`, `init320`); every thread fences the
initializations (`fence0`). Warp 0 prefetches the four tensor maps and runs fourteen elections
(`elect e`), the leader of each initializing a group of the 36 other barriers in offset order
(`init j` initializes `FBar.ofInit j`); every thread broadcasts its cluster rank (`shfl3`) between
the second and the third election. Every thread then fences again (`fence1`), arrives on and
waits at the cluster barrier (`clArrive`, `clWait`), and goes to its role by its warp index
(`RoleKind.ofWarp`): every role starts at its own `setmaxnreg`.

A shuffle is followed only when it returns lane 0's operand (the shared base, the warp index,
the cluster rank), which is what a full-warp `shfl.sync.idx` from lane 0 of a warp-uniform
operand returns; the machine gives up (`some none`) otherwise, and the execution layer shows
that this never happens (`tracked`). So the warp index the code branches on is the thread's own
(`warpOf`), and the abstract state is the site alone.

Every register is a function of the launch and the thread (`values`): the parameter words as
`ld.param` assembles them, the shared base and the barrier addresses above it, the warp-index
tests, the cluster rank and the derived multicast mask (`3`) and leader rank (`0`), the
barrier counts, the tensor-map parameter addresses, and the item count each role loads before
its `setmaxnreg`. An election's predicate is the event's, and is stated explicitly by the step
that follows it. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The roles a thread takes after the prologue. -/
inductive RoleKind where
  | loader | mma | store | softmax | corr | idle
  deriving DecidableEq

/-- The role of warp `w`: warps 0-7 compute the softmax, 8-11 correct, 12 issues the MMAs, 13
stores the output, 14 loads, 15 idles. -/
def RoleKind.ofWarp (w : Nat) : RoleKind :=
  if w = 14 then .loader
  else if w = 15 then .idle
  else if w = 12 then .mma
  else if w = 13 then .store
  else if w < 8 then .softmax
  else .corr

/-- The role's first instruction, its `setmaxnreg`. -/
def RoleKind.entry : RoleKind → Nat
  | .idle => Flow.setMaxReg_0
  | .loader => Flow.setMaxReg_1
  | .mma => Flow.setMaxReg_2
  | .store => Flow.setMaxReg_3
  | .softmax => Flow.setMaxReg_4
  | .corr => Flow.setMaxReg_5

namespace Prologue

/-- The prologue's sites. -/
inductive Site where
  | shfl0 | shfl1 | shfl2
  /-- Warp 12's election and its leader's initialization of the handshake barrier. -/
  | elect12 | init320
  | fence0
  /-- Warp 0's election `e` (`elect_{e+1}`). -/
  | elect (e : Fin 14)
  /-- Warp 0's initialization `j` (`mbarInit_{j+1}`), of `FBar.ofInit j`. -/
  | init (j : Fin 36)
  | shfl3 | fence1 | clArrive | clWait
  deriving DecidableEq

def Site.pc : Site → Nat
  | .shfl0 => Flow.shfl_0
  | .shfl1 => Flow.shfl_1
  | .shfl2 => Flow.shfl_2
  | .elect12 => Flow.elect_0
  | .init320 => Flow.mbarInit_0
  | .fence0 => Flow.fenceMbarInit_0
  | .elect e => Flow.elect.getD (e.val + 1) 0
  | .init j => Flow.mbarInit.getD (j.val + 1) 0
  | .shfl3 => Flow.shfl_3
  | .fence1 => Flow.fenceMbarInit_1
  | .clArrive => Flow.clusterArrive_0
  | .clWait => Flow.clusterWait_0

/-- A prologue state: the next event. -/
structure D where
  site : Site

/-! ### Warp 0's elections and their initialization groups -/

/-- The election whose leader performs initialization `j`: elections 0, 1 initialize two
barriers each, elections 2, 3 six each, the others two each. -/
def groupOf (j : Fin 36) : Fin 14 :=
  ⟨if j.val < 4 then j.val / 2 else if j.val < 16 then 2 + (j.val - 4) / 6
    else 4 + (j.val - 16) / 2, by split_ifs <;> omega⟩

/-- The first initialization of election `e`'s group. -/
def groupStart (e : Fin 14) : Fin 36 :=
  ⟨if e.val < 2 then 2 * e.val else if e.val < 4 then 4 + 6 * (e.val - 2)
    else 16 + 2 * (e.val - 4), by split_ifs <;> omega⟩

/-- The size of election `e`'s group. -/
def groupSize (e : Fin 14) : Nat := if e.val = 2 ∨ e.val = 3 then 6 else 2

/-- Where warp 0 goes after election `e`'s group, or after the election for the lanes it did
not elect: the next election, the rank broadcast after election 1, the fence after the last. -/
def afterGroup (e : Fin 14) : Site :=
  if e.val = 1 then .shfl3
  else if h : e.val + 1 < 14 then .elect ⟨e.val + 1, h⟩
  else .fence1

/-- The site after initialization `j`: the next of its group, or the site after the group. -/
def initNext (j : Fin 36) : Site :=
  if h : j.val + 1 < 36 ∧ j.val + 1 < (groupStart (groupOf j)).val + groupSize (groupOf j) then
    .init ⟨j.val + 1, h.1⟩
  else afterGroup (groupOf j)

/-! ### Register values -/

/-- A shared address `off` bytes above the dynamic shared base. -/
def sb (L : Launch) (off : Nat) : Value := b32 (L.sharedBase + off)

/-- The prologue's registers, as functions of the launch, the thread, its warp index `w` and its
cluster rank `rk` (`warpOf L g`, `rankOf L g`; parameters, so that a step that knows them
evaluates the tests on them). -/
def values (L : Launch) (g w rk : Nat) : List (Nat × Value) :=
  [(665, b32 (skOf L)), (666, b32 (divWord L "11" 0)), (667, b32 (divWord L "11" 1)),
   (668, b32 (divWord L "12" 0)), (669, b32 (divWord L "12" 1)),
   (309, .bits 16 (BitVec.ofNat 64 (divShift L "11" 0))),
   (310, .bits 16 (BitVec.ofNat 64 (divShift L "11" 1))),
   (311, .bits 16 (BitVec.ofNat 64 (divShift L "12" 0))),
   (312, .bits 16 (BitVec.ofNat 64 (divShift L "12" 1))),
   (3941, .ptr 64 false (.param (param "7")) 0), (3942, .ptr 64 false (.param (param "6")) 0),
   (3943, .ptr 64 false (.param (param "5")) 0), (3944, .ptr 64 false (.param (param "4")) 0),
   (4065, .ptr 64 true (.param (param "4")) 0), (4066, .ptr 64 true (.param (param "5")) 0),
   (4067, .ptr 64 true (.param (param "6")) 0), (4068, .ptr 64 true (.param (param "7")) 0),
   (670, sb L 0), (337, sb L 0), (678, b32 (w)), (679, b32 (w)),
   (336, b32 (w)), (338, b32 (ctaOf L g % 2)), (687, b32 (rk)),
   (339, b32 (rk)), (689, b32 (rk)), (690, b32 0),
   (308, .bits 16 (BitVec.ofNat 64 3)), (342, b32 0), (3936, b32 (clusterOf L g)),
   (956, sb L 320), (756, sb L 16), (340, sb L 128), (341, sb L 144), (935, sb L 160),
   (3250, sb L 192), (343, sb L 240), (970, sb L 256), (3251, sb L 272),
   (682, b32 32), (684, b32 1), (686, b32 1), (698, b32 1), (700, b32 1), (702, b32 1),
   (704, b32 512), (709, b32 8), (711, b32 1), (713, b32 1), (715, b32 256), (717, b32 128),
   (719, b32 128), (721, b32 128), (723, b32 32),
   (1, .pred (decide (w ≠ 0))), (2, .pred (decide (w ≠ 12))),
   (5, .pred (decide (w ≠ 0))), (8, .pred (decide (w ≠ 0))),
   (11, .pred (decide (w ≠ 0))), (14, .pred (decide (w ≠ 0))),
   (19, .pred (decide (w ≠ 0))), (22, .pred (decide (w ≠ 0))),
   (28, .pred (decide (w ≠ 0))), (33, .pred (decide (w ≠ 0))),
   (38, .pred (decide (w ≠ 0))), (43, .pred (decide (w ≠ 0))),
   (46, .pred (decide (w = 14))), (47, .pred (decide (w ≠ 15))),
   (100, .pred (decide (w ≠ 12))), (137, .pred (decide (w ≠ 13))),
   (140, .pred (decide (7 < w))), (290, .pred (decide (w / 4 ≠ 2))),
   (3903, b32 (totOf L)), (3904, b32 (totOf L)), (3905, b32 (totOf L)), (3906, b32 (totOf L)),
   (3907, b32 (totOf L))]

def valueOf (L : Launch) (g w rk : Nat) (r : Nat) : Value :=
  ((values L g w rk).lookup r).getD (b32 0)

/-- The registers live at `pc`, valued by the table. -/
def factsAt (L : Launch) (g w rk pc : Nat) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf L g w rk)

abbrev facts (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  factsAt L g (warpOf L g) (rankOf L g) d.site.pc

/-- Only warp 0 runs the elections and initializations of the 36 barriers, only warp 12 the
handshake barrier's. -/
structure Inv (L : Launch) (g : Nat) (d : D) : Prop where
  warp0 : (∃ e, d.site = .elect e) ∨ (∃ j, d.site = .init j) → warpOf L g = 0
  warp12 : d.site = .elect12 ∨ d.site = .init320 → warpOf L g = 12

/-- The abstract successor after event `e`; at the cluster wait, the thread's role. -/
def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option (D ⊕ RoleKind)) :=
  match d.site with
  | .shfl0 =>
    match e.kind with
    | .shfl _ _ _ _ (.bits wd v) _ =>
      some (if wd = 32 ∧ v = BitVec.ofNat 64 L.sharedBase then some (.inl ⟨.shfl1⟩) else none)
    | .shfl .. => some none
    | _ => none
  | .shfl1 =>
    match e.kind with
    | .shfl _ _ _ _ (.bits wd v) _ =>
      some (if wd = 32 ∧ v = BitVec.ofNat 64 (warpOf L g) then some (.inl ⟨.shfl2⟩) else none)
    | .shfl .. => some none
    | _ => none
  | .shfl2 =>
    match e.kind with
    | .shfl _ _ _ _ (.bits wd v) _ =>
      some (if wd = 32 ∧ v = BitVec.ofNat 64 (warpOf L g) then
        some (.inl ⟨if warpOf L g = 12 then .elect12 else .fence0⟩) else none)
    | .shfl .. => some none
    | _ => none
  | .elect12 =>
    match e.kind with
    | .elect _ _ ld => some (some (.inl ⟨if laneOf L g = ld then .init320 else .fence0⟩))
    | _ => none
  | .init320 => some (some (.inl ⟨.fence0⟩))
  | .fence0 => some (some (.inl ⟨if warpOf L g = 0 then .elect 0 else .shfl3⟩))
  | .elect k =>
    match e.kind with
    | .elect _ _ ld =>
      some (some (.inl ⟨if laneOf L g = ld then .init (groupStart k) else afterGroup k⟩))
    | _ => none
  | .init j => some (some (.inl ⟨initNext j⟩))
  | .shfl3 =>
    match e.kind with
    | .shfl _ _ _ _ (.bits wd v) _ =>
      some (if wd = 32 ∧ v = BitVec.ofNat 64 (rankOf L g) then
        some (.inl ⟨if warpOf L g = 0 then .elect 2 else .fence1⟩) else none)
    | .shfl .. => some none
    | _ => none
  | .fence1 => some (some (.inl ⟨.clArrive⟩))
  | .clArrive => some (some (.inl ⟨.clWait⟩))
  | .clWait => some (some (.inr (RoleKind.ofWarp (warpOf L g))))

/-- The table's values, as `simp` reduces them after a segment's evaluation. -/
macro "pro_values" : tactic =>
  `(tactic| simp only [valueOf, PTX.Flow.lookupLit, Option.getD_some, Option.getD_none])

end Prologue

end
end PTX.Kernels.FlashAttn4Fwd.Proof
