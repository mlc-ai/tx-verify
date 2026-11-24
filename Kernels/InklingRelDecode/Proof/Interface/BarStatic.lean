-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.BarOrdinal

@[expose] public section

/-!
# The named-barrier events of the kernel, from the program text

An audit by `decide +kernel`: every named-barrier instruction of the kernel is `bar.sync b` or
`barrier.sync b` of an immediate barrier `b < 16`, or `bar.sync 0, 128`; there is no `bar.arrive`
and no barrier named by a register. So an event on barrier 1 is a `barrier.sync 1` without a
thread count (`bar_one_static`), and every barrier event is a `bar.sync` (`bar_sync_static`).
These statements need no machine: they follow from the instruction at the event's position.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The forms a named-barrier instruction of the kernel takes. -/
def barForm : Op → Bool
  | .barSync (.imm i) _ => decide (0 ≤ i ∧ i < 16)
  | .barSyncN (.imm 0) (.imm 128) _ => true
  | .barSync .. | .barSyncN .. | .barArrive .. => false
  | _ => true

theorem kernel_barForm : kernel.code.all (fun ins => barForm ins.op) = true := by
  decide +kernel

/-- **A barrier event is `bar.sync b` without a count (`b < 16`) or `bar.sync 0, 128`.** -/
theorem bar_event_static (hX : Consistent L kernel asms mem0 X) (hb : L.block ≠ 128)
    {i : EvId} {pc id : Nat} {cnt : Option Nat} {m : BarMode}
    (he : X.get i = some ⟨pc, .bar id cnt m⟩) :
    m = .sync ∧ ((cnt = none ∧ id < 16) ∨ (id = 0 ∧ cnt = some 128)) := by
  rcases Flow.get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hf
  · simp only at hc hf
    have hop := fires_bar_op hf (show (⟨pc, .bar id cnt m⟩ : Event).kind = .bar id cnt m from rfl)
    have hall := List.all_eq_true.mp kernel_barForm ins (List.mem_of_getElem? hc)
    cases hins : ins.op with
    | barSync b al =>
      rw [hins] at hf hall
      cases b with
      | imm v =>
        simp only [barForm, decide_eq_true_eq] at hall
        obtain ⟨n, rfl⟩ : ∃ n : Nat, v = n := ⟨v.toNat, (Int.toNat_of_nonneg hall.1).symm⟩
        have := EvD.fires_barSync_imm (by omega) hf
        simp only [Event.mk.injEq, Kind.bar.injEq, true_and] at this
        obtain ⟨rfl, rfl, rfl⟩ := this
        exact ⟨rfl, .inl ⟨rfl, by omega⟩⟩
      | _ => simp [barForm] at hall
    | barSyncN b c al =>
      rw [hins] at hf hall
      cases b with
      | imm v =>
        cases c with
        | imm w =>
          by_cases h0 : v = 0
          · by_cases h1 : w = 128
            · subst h0 h1
              have := EvD.fires_barSyncN_128 hb hf
              simp only [Event.mk.injEq, Kind.bar.injEq, true_and] at this
              obtain ⟨rfl, rfl, rfl⟩ := this
              exact ⟨rfl, .inr ⟨rfl, rfl⟩⟩
            · simp [barForm, h0, h1] at hall
          · simp [barForm, h0] at hall
        | _ => simp [barForm] at hall
      | _ => simp [barForm] at hall
    | barArrive b c al =>
      rw [hins] at hall
      simp [barForm] at hall
    | _ =>
      rw [hins] at hop
      simp [barOp] at hop

/-- **A barrier-1 event has no thread count**: it is `barrier.sync 1`. -/
theorem bar_one_static (hX : Consistent L kernel asms mem0 X) (hb : L.block ≠ 128)
    {i : EvId} {pc : Nat} {cnt : Option Nat} {m : BarMode}
    (he : X.get i = some ⟨pc, .bar 1 cnt m⟩) : cnt = none ∧ m = .sync := by
  obtain ⟨hm, h | ⟨h, -⟩⟩ := bar_event_static hX hb he
  · exact ⟨h.1, hm⟩
  · omega

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
