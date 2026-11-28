-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec

@[expose] public section

/-!
# The memory regions of a CTA and the placement statements

The layout of the shared window: the base word `[0, 4)`, the K and V rings
`[4, 196608)`, the Q tile `[196608, 212992)`, the pair `(num_pre, num_iters)` `[212992, 213000)`,
the scratch words `[213000, 213008)`, the mbarriers `[213216, 213336)` and the role word
`[213336, 213340)`, all from `L.sharedBase`; and the input and output bytes of global memory.
`SharedPlaced` and `GlobalPlaced` are the placement statements the safety layer
uses to classify execution accesses.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Iface
open PTX

noncomputable section

/-! ### Regions -/

/-- A byte of a CTA's Tensor Memory base word. -/
def InBase (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase ≤ l.addr ∧ l.addr < L.sharedBase + 4

/-- A byte of a CTA's K and V rings (the K slot 0 bytes of the base word are `InBase`). -/
def InKv (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase + 4 ≤ l.addr ∧ l.addr < L.sharedBase + 196608

/-- A byte of a CTA's Q tile. -/
def InQ (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase + 196608 ≤ l.addr ∧ l.addr < L.sharedBase + 212992

/-- A byte of ring slot `s`: its K tile `[32768 s, 32768 (s+1))` or its V tile
`[98304 + 32768 s, 98304 + 32768 (s+1))`, from `L.sharedBase`. -/
def InSlot (L : Launch) (s a : Nat) : Prop :=
  (L.sharedBase + 32768 * s ≤ a ∧ a < L.sharedBase + 32768 * (s + 1)) ∨
    (L.sharedBase + 98304 + 32768 * s ≤ a ∧ a < L.sharedBase + 98304 + 32768 * (s + 1))

theorem inSlot_unique {L : Launch} {s s' a : Nat} (hs : s < 3) (hs' : s' < 3)
    (h : InSlot L s a) (h' : InSlot L s' a) : s = s' := by
  unfold InSlot at h h'
  omega

theorem inSlot_kv {L : Launch} {s a : Nat} (hs : s < 3) (h : InSlot L s a) :
    L.sharedBase ≤ a ∧ a < L.sharedBase + 196608 := by
  unfold InSlot at h
  omega

/-- A byte of the pair `(num_pre, num_iters)` the default partition passes to the workers. -/
def InCount (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase + 212992 ≤ l.addr ∧ l.addr < L.sharedBase + 213000

/-- A byte of the scratch words above the pair `(num_pre, num_iters)`: warps 2 and 3's words of
the softmax region's min-exchange (words 0 and 1 are the pair, `InCount`). -/
def InScratch (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase + 213000 ≤ l.addr ∧ l.addr < L.sharedBase + 213008

/-- A byte of the role table. -/
def InRole (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase + 213336 ≤ l.addr ∧ l.addr < L.sharedBase + 213340

/-- A byte of one of the regions generic accesses touch. -/
def InRegions (L : Launch) (l : Loc) : Prop :=
  InBase L l ∨ InKv L l ∨ InQ L l ∨ InCount L l ∨ InScratch L l ∨ InRole L l

/-- The mbarrier arena, separate from the regions of ordinary accesses. -/
def InMbar (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase + 213216 ≤ l.addr ∧ l.addr < L.sharedBase + 213336

theorem regions_cover {L : Launch} {l : Loc} (hs : l.space = .shared)
    (lo : L.sharedBase ≤ l.addr) (hi : l.addr < L.sharedBase + 213340)
    (gap : l.addr < L.sharedBase + 213008 ∨ L.sharedBase + 213216 ≤ l.addr) :
    InRegions L l ∨ InMbar L l := by
  simp only [InRegions, InBase, InKv, InQ, InCount, InScratch, InRole, InMbar, hs, true_and]
  omega

/-- A global byte one of the output arrays holds. -/
def InOut (Q : Params) (l : Loc) : Prop :=
  l.space = .global ∧ l.cta = 0 ∧
    ((Q.oBase ≤ l.addr ∧ l.addr < Q.oBase + oBytes Q) ∨
      (Q.lseBase ≤ l.addr ∧ l.addr < Q.lseBase + lseBytes Q))

/-- A global byte the kernel reads as an input. -/
def InInput (Q : Params) (l : Loc) : Prop :=
  l.space = .global ∧ l.cta = 0 ∧ Q.reads l.addr

/-! ### Placement: facts of the thread layer -/

/-- **Shared placement**: every shared byte an access touches is in a region of a launched
CTA. -/
def SharedPlaced (L : Launch) (X : Execution) : Prop :=
  ∀ e a l, X.MemTouches e a → a.Covers l → l.space = .shared → l.cta < L.grid ∧ InRegions L l

/-- **Global placement**: every byte outside shared memory that an access touches is an input
byte or an output byte. -/
def GlobalPlaced (Q : Params) (X : Execution) : Prop :=
  ∀ e a l, X.MemTouches e a → a.Covers l → l.space ≠ .shared → InInput Q l ∨ InOut Q l

end
end PTX.Kernels.InklingRelDecode.Proof.Iface
