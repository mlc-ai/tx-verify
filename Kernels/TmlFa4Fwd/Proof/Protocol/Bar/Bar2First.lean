-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Match
import Lemmas.Protocol.CountNth
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A lane's first barrier-2 event is a `bar.sync`

Every barrier event has its ordinal's operands in the lane's schedule (`bar_sched`): ordinal 0 is
the startup's barrier 0, ordinal 1 is `bar.sync 2, 416` for every warp. So a barrier-2 event with
no barrier-2 event before it has ordinal 1 (at ordinal 2 or later, the event of ordinal 1 before
it was a barrier-2 event) and is a sync (`first_bar2_sync`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem schedB_one : schedB p L g 1 = (2, some 416, .sync) := by
  simp only [schedB, softB, corrB]
  split_ifs <;> simp_all

/-- **A barrier-2 event with no barrier-2 event before it is a sync.** -/
theorem first_bar2_sync (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {j pc : Nat}
    {cnt : Option Nat} {mode : BarMode} (he : X.get (g, j) = some ⟨pc, .bar 2 cnt mode⟩)
    (h0 : ((X.tr g).take j).countP (Execution.isBarId 2) < 1) : mode = .sync := by
  have hg := Frame.lt_of_get hX he
  have hs := bar_sched hp hX hFw hg he
  rcases ho : ((X.tr g).take j).countP Execution.isBar with _ | _ | o
  · rw [ho, schedB_zero] at hs; simp at hs
  · rw [ho, schedB_one] at hs; simp only [Prod.mk.injEq] at hs; exact hs.2.2
  · exfalso
    obtain ⟨i, ev, hi, hbi, hci⟩ := MbarRing.Slot.exists_nth_countP Execution.isBar
      (show 1 + 1 ≤ ((X.tr g).take j).countP Execution.isBar by omega)
    have hij : i < j := by
      have := (List.getElem?_eq_some_iff.mp hi).1
      simp only [List.length_take] at this
      omega
    have hgi : X.get (g, i) = some ev := by
      change (X.tr g)[i]? = some ev
      rw [← hi, List.getElem?_take, ite_eq_left hij]
    rw [List.take_take, Nat.min_eq_left hij.le] at hci
    obtain ⟨pci, ki⟩ := ev
    cases ki with
    | bar idi cnti modei =>
      have hsi := bar_sched hp hX hFw hg hgi
      rw [hci, schedB_one] at hsi
      simp only [Prod.mk.injEq] at hsi
      obtain ⟨rfl, -, -⟩ := hsi
      have hmem : (⟨pci, .bar 2 cnti modei⟩ : Event) ∈ (X.tr g).take j :=
        List.mem_of_getElem? hi
      have := List.countP_pos_iff (p := Execution.isBarId 2) |>.mpr ⟨_, hmem, rfl⟩
      omega
    | _ => cases hbi

end
end PTX.Kernels.TmlFa4Fwd.Proof
