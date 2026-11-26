-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.RefArith
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots

@[expose] public section

/-! # Warpgroup 2's local time

The role's states in the order of its events (`place`): the set-up's sites at `0`–`3` (the Q poll
`wq` at `3`), block `i`'s sites at `deqBlk0 + stride * i + idx` (`Site.idx`: the raw-ready poll `0`,
the SV-done poll `1`, row `r`'s scale load at `2 + 20 r` plus its element (at most `3`), its raw
loads and stores in program order from `6 + 20 r`, the fence `82`, the arrivals `83` and `84`), the
closing barrier at glued `endSlot` (`Lib/Slots.lean`) and the exit after it. The block of a loop
state is read off its counter (`blk`: `cnt + R` modulo `2 ^ 32`; `blk_eq`: block `i` under the block
words). The glued table (`Common/Time.lean`) places the role at `idleBase + 29 + place`, so the Q
poll is at `qUtccpSlot`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

/-- A raw load's place in its row after the scale load. -/
def rawI (s : Fin 8) : Nat := if s.val = 0 then 0 else 2 * s.val - 1
/-- A store's place in its row after the scale load. -/
def storeI (s : Fin 8) : Nat := if s.val = 7 then 15 else 2 * s.val + 2

/-- A loop site's place in its block. -/
def Site.idx : Site → Nat
  | .wraw => 0
  | .wsv => 1
  | .scale r => 2 + 20 * r.val
  | .raw r s => 6 + 20 * r.val + rawI s
  | .store r s => 6 + 20 * r.val + storeI s
  | .fpx => 82
  | .arrD => 83
  | .arrF => 84
  | _ => 0

/-- A loop site (not a set-up site, the barrier or the exit). -/
def Site.inLoop : Site → Bool
  | .smr | .lenA | .lenB | .wq | .bar | .exit => false
  | _ => true

/-- The element of a scale load read so far (at most `3`); `0` elsewhere. -/
def elOff (d : D) : Nat :=
  match d.site with
  | .scale _ => min d.el 3
  | _ => 0

/-- The block of a loop state: its counter plus the block count, modulo `2 ^ 32`. -/
def blk (d : D) : Nat := (d.cnt.toNat + rounds d.l0 d.l1) % 2 ^ 32

/-- The local place of the closing barrier: glued `endSlot`. -/
def endPlace : Nat := endSlot - deqOrg

/-- **The place of a state** in the role's order. -/
def place (d : D) : Nat :=
  match d.site with
  | .smr => 0
  | .lenA => 1
  | .lenB => 2
  | .wq => 3
  | .bar => endPlace
  | .exit => endPlace + 1
  | _ => deqBlk0 + stride * blk d + d.site.idx + elOff d

/-- **The local time of a state**: its place. -/
def time (d : D) : Nat := place d

theorem idx_le (s : Site) : s.idx ≤ 84 := by
  cases s with
  | raw r s => have := r.isLt; have := s.isLt; simp only [Site.idx, rawI]; split_ifs <;> omega
  | store r s => have := r.isLt; have := s.isLt; simp only [Site.idx, storeI]; split_ifs <;> omega
  | scale r => have := r.isLt; simp only [Site.idx]; omega
  | _ => simp only [Site.idx]; omega

theorem elOff_le (d : D) : elOff d ≤ 3 := by
  unfold elOff; split <;> omega

/-- **A loop site's place in its block is before the arrivals** (`deqArrD = 83`). -/
theorem idx_el_le (d : D) (hD : d.site ≠ .arrD) (hF : d.site ≠ .arrF) :
    d.site.idx + elOff d ≤ 82 := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases s with
  | arrD => exact absurd rfl hD
  | arrF => exact absurd rfl hF
  | raw r s =>
    have := r.isLt; have := s.isLt
    simp only [Site.idx, rawI, elOff]; split_ifs <;> omega
  | store r s =>
    have := r.isLt; have := s.isLt
    simp only [Site.idx, storeI, elOff]; split_ifs <;> omega
  | scale r => have := r.isLt; simp only [Site.idx, elOff]; omega
  | _ => simp only [Site.idx, elOff]; omega

/-- The place of a loop state. -/
theorem place_loop {d : D} (h : d.site.inLoop = true) :
    place d = deqBlk0 + stride * blk d + d.site.idx + elOff d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases s <;> first | rfl | cases h

/-- **Block `i`'s counter is read as block `i`.** -/
theorem blk_eq {d : D} {i : Nat} (hw : LoopWords d i) : blk d = i := by
  obtain ⟨hi, hR, hc⟩ := hw
  unfold blk
  rw [hc, toNat_W (by omega)]
  omega

/-- The block count is below `2 ^ 26`. -/
theorem rounds_lt (l0 l1 : BitVec 64) : rounds l0 l1 < 2 ^ 26 := by
  cases h : scmpi .lt .s (r57 l0 l1) 64
  · exact (blocks_pos h).2.1
  · simp [rounds, h]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
