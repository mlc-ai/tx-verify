-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Place
import Kernels.TmlFa4Fwd.Flow.Code.Part002
import Kernels.TmlFa4Fwd.Proof.Correction.Export.BarPc
import Kernels.TmlFa4Fwd.Proof.Lib.NoBar
import Kernels.TmlFa4Fwd.Proof.Mma.Export.BarPc
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.BarPc
import Lemmas.Kernel.Safety.Schedule
import Lemmas.Protocol.CountNth
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The barrier class of ERR-ALIGNED-MISMATCH

A lane's `k`-th barrier event is at the position `barPc` gives (`bar_pc`), one for the lanes of a
warp (`bar_not_divergent`), and every thread makes the startup's barrier event, the only one without
a thread count, before it exits (`bar_not_exited`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **Every barrier event of a lane is at its ordinal's position.** -/
theorem bar_pc {k pc id : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩) :
    pc = barPc p L g (((X.tr g).take k).countP Execution.isBar) := by
  unfold barPc
  split_ifs with h8 h12
  · exact soft_bar_pc hp hX hFw h8 he
  · exact corr_bar_pc hp hX hFw (by omega) (by omega) he
  · rcases Nat.lt_or_ge 12 (Prologue.warpIndex L g) with h | h
    · exact late_bar_pc hp hX hFw h he
    · exact mma_bar_pc hp hX hFw (by omega) he

/-- **The lanes of a warp make their `k`-th barrier event at one position.** -/
theorem bar_not_divergent : ¬ AlignedClass.bar.Divergent L kernel X := by
  rintro ⟨⟨g, i⟩, ⟨h, j⟩, pe, pf, ke, kf, hw, he, hf, hme, hmf, hk, -, hne⟩
  cases ke <;> simp [AlignedClass.member, Execution.isBar] at hme
  cases kf <;> simp [AlignedClass.member, Execution.isBar] at hmf
  have e1 := bar_pc hp hX hFw he
  have e2 := bar_pc hp hX hFw hf
  have hk' : ((X.tr g).take i).countP Execution.isBar =
      ((X.tr h).take j).countP Execution.isBar := hk
  rw [← hk', ← barPc_warp hp hw, ← e1] at e2
  exact hne.elim (fun h => h e2.symm) (fun h => h rfl)

/-- **Every thread makes the startup's barrier event before it exits.** -/
theorem bar_not_exited : ¬ AlignedClass.bar.Exited L kernel X := by
  rintro ⟨⟨g, i⟩, ⟨h, j⟩, ⟨pe, ke⟩, hcta, he, hm, -, ⟨pc, hx⟩, hshort⟩
  -- the exited thread made a barrier event
  have hh := Frame.lt_of_get hX hx
  have hb : 1 ≤ ((X.tr h).take j).countP Execution.isBar := by
    refine (exit_bar0 hp hX (table_shape_of hp hFw) (table_followed hp hX hFw) hx).trans_le
      (List.countP_mono_left fun x _ hx => ?_)
    obtain ⟨pcx, kx⟩ := x
    cases kx <;> simp_all [Execution.isBarId, Execution.isBar]
  obtain ⟨b, ev, hbg, hbk, hb0⟩ := MbarRing.Slot.exists_nth_countP Execution.isBar
    (show 0 + 1 ≤ ((X.tr h).take j).countP Execution.isBar by omega)
  have hbj : b < j := by
    have := (List.getElem?_eq_some_iff.mp hbg).1
    simp only [List.length_take] at this
    omega
  have hgb : X.get (h, b) = some ev := by
    change (X.tr h)[b]? = _
    rw [← hbg, List.getElem?_take, ite_eq_left hbj]
  rw [List.take_take, Nat.min_eq_left hbj.le] at hb0
  obtain ⟨pcb, kb⟩ := ev
  cases kb <;> simp [Execution.isBar] at hbk
  have hs := bar_sched hp hX hFw hh hgb
  have hpb := bar_pc hp hX hFw hgb
  rw [hb0, schedB_zero] at hs
  simp only [Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl, rfl⟩ := hs
  have h173 : pcb = 173 := by
    rw [hpb, hb0, barPc_zero]
  subst h173
  have hal : kernel.isAlignedCtaBar ⟨173, .bar 0 none .sync⟩ = true := by
    show kernel.alignedAt 173 = true
    unfold Kernel.alignedAt
    rw [Flow.code_173]
    rfl
  have hone := Frame.countP_take_lt_countP (P := kernel.isAlignedCtaBar) (es := X.tr h) (i := b)
    hgb hal
  -- the other thread's event is its first
  have hzero : ((X.tr g).take i).countP kernel.isAlignedCtaBar = 0 := by
    cases ke <;> simp only [AlignedClass.exitMember, Kernel.isAlignedCtaBar,
      Bool.false_eq_true] at hm
    rename_i id cnt mode
    cases cnt with
    | some c => simp at hm
    | none =>
      have hs := bar_sched hp hX hFw (Frame.lt_of_get hX he) he
      have h0 : ((X.tr g).take i).countP Execution.isBar = 0 := by
        by_contra hne
        exact schedB_some (p := p) (L := L) (g := g) hne (by rw [← hs])
      refine Nat.eq_zero_of_le_zero (h0 ▸ List.countP_mono_left fun x _ hx => ?_)
      obtain ⟨pcx, kx⟩ := x
      cases kx <;> simp_all [Kernel.isAlignedCtaBar, Execution.isBar]
  have hshort' : (X.tr h).countP kernel.isAlignedCtaBar ≤
      ((X.tr g).take i).countP kernel.isAlignedCtaBar := hshort
  omega

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
