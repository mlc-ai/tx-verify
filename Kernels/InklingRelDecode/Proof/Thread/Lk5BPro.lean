-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.Lk5BSm
public import Kernels.InklingRelDecode.Proof.Thread.ClassBt

@[expose] public section

/-!
# The prologue's `bar.sync 0, 128` before a state

The prologue has one `bar.sync 0, 128` (`bar2`, pc 180) and, in each preloaded block `j < 3`, the
five `pbA_j` … `pbE_j`. A block is preloaded when its guard holds (`ProA.Gate`: the number
`%r31` of blocks is not 0, not 1, not below 3), so after the blocks the count is `1 + 5 nb` with
`nb` the number of preloaded blocks (`nbOf`, a function of the guards).

* `proOff L g d`: the number of the prologue's `bar.sync 0, 128` before a prologue state;
* `pro_b0At`: the barrier-0 instructions of the prologue's sites (`bar.sync 0, 128` only);
* `proOff_next`: a step at a state that satisfies `Gate` adds its own instruction's
  `bar.sync 0, 128`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk5B
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-- The number of preloaded blocks, from the three guards. -/
def nbOf (L : Launch) (g : Nat) (dt : ProA.Dat) : Nat :=
  if ProA.v_p53 L g dt = false then 0 else if ProA.v_p63 L g dt = true then 1
  else if ProA.v_p72 L g dt = true then 2 else 3

/-- The offset of a block's site from the block's first `bar.sync 0, 128`, and the block. -/
def blkOff : ProA.Site → Option (Nat × Nat)
  | .pbA0 => some (0, 0) | .arr0 => some (0, 1) | .lbA0 => some (0, 1) | .pbB0 => some (0, 1)
  | .psh0 => some (0, 2) | .pel0_0 => some (0, 2) | .ptc0_0 => some (0, 2)
  | .pbC0 => some (0, 2) | .pel0_1 => some (0, 3) | .ptc0_1 => some (0, 3)
  | .lbB0 => some (0, 3) | .pbD0 => some (0, 3) | .pel0_2 => some (0, 4)
  | .ptc0_2 => some (0, 4) | .pbE0 => some (0, 4) | .pel0_3 => some (0, 5)
  | .ptc0_3 => some (0, 5)
  | .pbA1 => some (1, 0) | .arr1 => some (1, 1) | .lbA1 => some (1, 1) | .pbB1 => some (1, 1)
  | .psh1 => some (1, 2) | .pel1_0 => some (1, 2) | .ptc1_0 => some (1, 2)
  | .pbC1 => some (1, 2) | .pel1_1 => some (1, 3) | .ptc1_1 => some (1, 3)
  | .lbB1 => some (1, 3) | .pbD1 => some (1, 3) | .pel1_2 => some (1, 4)
  | .ptc1_2 => some (1, 4) | .pbE1 => some (1, 4) | .pel1_3 => some (1, 5)
  | .ptc1_3 => some (1, 5)
  | .pbA2 => some (2, 0) | .arr2 => some (2, 1) | .lbA2 => some (2, 1) | .pbB2 => some (2, 1)
  | .psh2 => some (2, 2) | .pel2_0 => some (2, 2) | .ptc2_0 => some (2, 2)
  | .pbC2 => some (2, 2) | .pel2_1 => some (2, 3) | .ptc2_1 => some (2, 3)
  | .lbB2 => some (2, 3) | .pbD2 => some (2, 3) | .pel2_2 => some (2, 4)
  | .ptc2_2 => some (2, 4) | .pbE2 => some (2, 4) | .pel2_3 => some (2, 5)
  | .ptc2_3 => some (2, 5)
  | _ => none

/-- The number of the prologue's `bar.sync 0, 128` before a prologue state. -/
def proOff (L : Launch) (g : Nat) (d : ProA.D) : Nat :=
  match blkOff d.site with
  | some (j, o) => 1 + 5 * j + o
  | none => if d.site.ctorIdx ≤ ProA.Site.bar2.ctorIdx then 0 else 1 + 5 * nbOf L g d.dt

/-- The barrier-0 instruction of a prologue site. -/
def proB0 (s : ProA.Site) : Nat :=
  match s with
  | .bar2 | .pbA0 | .pbB0 | .pbC0 | .pbD0 | .pbE0 | .pbA1 | .pbB1 | .pbC1 | .pbD1 | .pbE1
  | .pbA2 | .pbB2 | .pbC2 | .pbD2 | .pbE2 => 2
  | _ => 0

theorem pro_b0At (s : ProA.Site) : b0At s.pc = proB0 s := by
  cases s <;> decide +kernel

/-- The increment of a prologue site: its `bar.sync 0, 128`. -/
def proInc (s : ProA.Site) : Nat := if proB0 s = 2 then 1 else 0

theorem proOff_qSite (L : Launch) (g : Nat) (dt dt' : ProA.Dat) (G : Nat) :
    proOff L g ⟨ProA.qSite L g dt G, dt'⟩ = 1 + 5 * nbOf L g dt' := by
  unfold ProA.qSite
  split <;> (repeat' split) <;> rfl

/-- **A prologue step adds its own instruction's `bar.sync 0, 128`.** -/
theorem proOff_next {L : Launch} {g : Nat} {s : ProA.Site} {dt : ProA.Dat} {d' : ProA.D}
    {e : Event} (h : ProA.next L g ⟨s, dt⟩ e = some (some d'))
    (hG : ProA.Gate L g s dt) :
    proOff L g d' = proOff L g ⟨s, dt⟩ + proInc s := by
  obtain ⟨g0, g1, g2⟩ := hG
  cases s <;> simp only [ProA.next] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h; subst h
       first
       | (simp only [proOff_qSite]
          simp_all (config := { decide := true }) [proOff, blkOff, nbOf, proInc,
            ProA.gp_elDt, ProA.gp_q])
       | (simp_all (config := { decide := true }) [proOff, blkOff, nbOf, proInc,
            ProA.gp_elDt, ProA.gp_q]))

end
end PTX.Kernels.InklingRelDecode.Proof.Lk5B
