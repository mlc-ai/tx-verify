-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.RefNext
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots

@[expose] public section

/-! # The TMA warp's local time

The role's states in the order of its events (`place`): the prologue's sites in program order
(`Site.ord`: the election, the two length loads, the waits on `bar_q_utccp` and
`bar_last_store_done`), then block `r`'s sites at `tmaBlk0 + stride * r + idx` (`Site.idx`: the
block's events before the site, its stage plus its reads plus its gathers; `Lib/Slots.lean`), the
CTA barrier at glued `endSlot` and the exit after it. Every step the machine follows stays (a
failed poll) or moves to a later place (`Tma/Measure.lean`), and under the reference invariant
every place is at most `top` (`place_le`).

The glued table (`Common/Time.lean`) places the role at `idleBase + 29 + place`, so that the wait
on `bar_q_utccp` (place 3) is at the slot of the MMA lane's commit (`qUtccpSlot = idleBase + 32`)
and every later state is above it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {L : Launch} {g : Nat}

/-- A block's events before a site. -/
def Site.idx (s : Site) : Nat := s.stage + s.rdN + s.gN

/-- The prologue's order (a loop site at its block place). -/
def Site.ord : Site → Nat
  | .elect => 0
  | .loadTopk | .leave _ => 1
  | .loadExtra => 2
  | .qWait => 3
  | .storeWait => 4
  | s => 5 + s.idx

/-- The local place of the CTA barrier: glued `endSlot`. -/
def endPlace : Nat := endSlot - tmaOrg

/-- **The place of a state** in the role's order: a prologue site at its order, a loop site at
its block's place, the barrier and the exit after the last block. -/
def place (d : D) : Nat :=
  match d.site with
  | .outBar => endPlace
  | .exit => endPlace + 1
  | s => if s.inLoop then tmaBlk0 + stride * d.cnt.toNat + s.idx else s.ord

/-- **The local time of a state**: its place. -/
def time (d : D) : Nat := place d

/-- The largest place: the exit. -/
def top : Nat := endPlace + 1

/-- A block's place before its end. -/
theorem idx_le (s : Site) : s.idx ≤ 83 := by
  cases s <;> simp only [Site.idx, Site.stage, Site.rdN, Site.gN] <;>
    first | omega | (rename_i k; have := k.isLt; split_ifs <;> omega)

/-- A prologue state is at its site's order. -/
theorem place_pro {d : D} (h : ProSite d.site) : place d = d.site.ord := by
  obtain ⟨hl, hx, hb⟩ := h
  unfold place
  split
  next hs => exact absurd hs hb
  next hs => exact absurd hs hx
  next => simp only [hl, Bool.false_eq_true, ↓reduceIte]

/-- A loop state is at its block's place. -/
theorem place_loop {d : D} (h : d.site.inLoop = true) :
    place d = tmaBlk0 + stride * d.cnt.toNat + d.site.idx := by
  unfold place
  split
  next hs => rw [hs] at h; exact absurd h (by decide)
  next hs => rw [hs] at h; exact absurd h (by decide)
  next => simp only [h, ↓reduceIte]

/-- **Every place is at most `top`** at a state with the reference invariant. -/
theorem place_le {d : D} {n : Cnt → Nat} (hJ : RefCore L g d n) :
    place d ≤ top := by
  have hi := idx_le d.site
  have ho : d.site.ord ≤ 5 + d.site.idx := by cases d.site <;> simp only [Site.ord] <;> omega
  simp only [place, top, endPlace, endSlot, tmaOrg, loopBase, stride, blockCap, tmaBlk0, tmaOff,
    Site.idx, Site.stage, Site.rdN, Site.gN] at hi ho ⊢
  split
  · omega
  · omega
  · split_ifs with h
    · obtain ⟨⟨-, -, hR', hr, -⟩, -⟩ := (core_loop h).1 hJ
      omega
    · omega

/-- **The wait on `bar_q_utccp` is at place 3**, and every place from it on is at least 3. -/
theorem place_qWait {d : D} (h : d.site = .qWait) : place d = 3 := by
  rw [place_pro (by rw [h]; exact ⟨rfl, by simp, by simp⟩), h]; rfl

/-- A block's site before its arrivals is at most 81 events in. -/
theorem idx_mid (s : Site) : s.idx ≤ 81 ∨ s = .rawArrive ∨ s = .coordFree := by
  cases s <;> simp only [Site.idx, Site.stage, Site.rdN, Site.gN, reduceCtorEq, or_false,
    or_true] <;> first | omega | (rename_i k; have := k.isLt; split_ifs <;> omega)

/-- Only the arrival on `valid_coord_free` is at stage 3. -/
theorem stage_lt (s : Site) (h : s ≠ .coordFree) : s.stage < 3 := by
  cases s <;> simp only [Site.stage] <;> first | omega | exact absurd rfl h

/-- A prologue site after the election is at place at most 4. -/
theorem place_pro_le {d : D} (h : ProSite d.site) : place d ≤ 4 := by
  rw [place_pro h]
  obtain ⟨hl, hx, hb⟩ := h
  cases hs : d.site <;> rw [hs] at hl hx hb <;> simp_all [Site.ord, Site.inLoop]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
