-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.RefNext
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots

@[expose] public section

/-! # The MMA warp's local time

The role's states in the order of its events (`place`): the prologue's sites in program order
(`Site.ord`, the two length loads and the trap apart), then block `r`'s sites at
`mmaBlk0 + stride * r + off` (`Site.off`: the block's events before the site up to the commit to
`qk_done`, then the wait on `so_ready` at the pad `mmaSo` and its successors; `Lib/Slots.lean`),
the CTA barrier at `endSlot` (glued) and the exit after it. Every step the
machine follows either stays (a failed poll) or moves to a later place (`place_next`), and under
the loop words every place is at most `top` (`place_le`). The glued table (`Common/Time.lean`)
places it after warpgroup 1's head; the termination measure is the place capped at `top`
(`Mma/Measure.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- The prologue's order (a loop site at its block place). -/
def Site.ord : Site → Nat
  | .elect => 0
  | .loadTopk | .leave _ => 1
  | .loadExtra => 2
  | .trap => 3
  | .qLoad k => 4 + k.val
  | .qArrive => 12
  | .qWait => 13
  | .qFence => 14
  | .qCopy k => 15 + k.val
  | .qCopyCommit => 31
  | .qCopyWait => 32
  | .qCopyFence => 33
  | s => 34 + s.idx

/-- A loop site's place in its block: its events before it up to the commit to `qk_done`, the
wait on `so_ready` and its successors from the pad `mmaSo` on. -/
def Site.off : Site → Nat
  | .soWait => mmaSo
  | .soFence => mmaSo + 1
  | .pv k => mmaSo + 2 + k.val
  | .pvCommit => mmaPvc
  | s => s.idx

/-- The local place of the CTA barrier: glued `endSlot`. -/
def endPlace : Nat := endSlot - mmaOrg

/-- **The place of a state** in the role's order. -/
def place (d : D) : Nat :=
  match d.site with
  | .outBar => endPlace
  | .exit => endPlace + 1
  | s => if s.inLoop then mmaBlk0 + stride * d.cnt.toNat + s.off else s.ord

/-- The largest place: the exit. -/
def top : Nat := endPlace + 1

/-- **The local time of a state**: its place. -/
def time (d : D) : Nat := place d

theorem idx_le (s : Site) : s.idx ≤ 29 := by
  cases s <;> simp only [Site.idx] <;> omega

theorem off_le (s : Site) : s.off ≤ mmaPvc := by
  cases s <;> simp only [Site.off, Site.idx, mmaSo, mmaPvc] <;> (try have := ‹Fin _›.isLt) <;> omega

/-- **Every place is at most `top`** at a state with the reference invariant. -/
theorem place_le {d : D} {n : Cnt → Nat} (hJ : RefCore L g d n) :
    place d ≤ top := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  have hi := off_le s
  have hi' := idx_le s
  unfold place top
  split
  · omega
  · omega
  · split_ifs with h
    · obtain ⟨⟨-, -, hR', hr, -⟩, -⟩ := (core_loop h).1 hJ
      simp only at hR' hr ⊢
      simp only [endPlace, endSlot, mmaOrg, mmaBlk0, loopBase, mmaOff, stride, blockCap,
        mmaPvc] at hi ⊢
      omega
    · cases s <;> simp only [Site.ord, endPlace, endSlot, mmaOrg, loopBase, stride, blockCap] <;>
        omega

/-- The place of a prologue state, and of a loop state. -/
theorem place_pro {d : D} (h : ProSite d.site) : place d = d.site.ord := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold place
  split
  · contradiction
  · contradiction
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]

theorem place_loop {d : D} (h : d.site.inLoop = true) :
    place d = mmaBlk0 + stride * d.cnt.toNat + d.site.off := by
  unfold place
  split
  · rename_i hs; rw [hs] at h; cases h
  · rename_i hs; rw [hs] at h; cases h
  · simp only [h, ↓reduceIte]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
