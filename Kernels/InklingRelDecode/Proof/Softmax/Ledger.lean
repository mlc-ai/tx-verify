-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Ref

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Flow Control

theorem counts_loop (e : Entry) (t i : Nat) (v : Carry) :
    counts t ⟨loopSite e t i,i,v⟩ = ⟨i,i-1,if t%128=0 then i else 0⟩ := by
  unfold loopSite
  split <;> first | rfl | (split <;> rfl)

/-- Away from the three object sites none of the three counts changes. -/
theorem bump_other (c : Cnt) (ev : Event) (hs : ev.pc ≠ 1257) (ho : ev.pc ≠ 2239)
    (hp : ev.pc ≠ 1013) : c.bump ev = c := by
  have ok (pc : Nat) (hne : ev.pc ≠ pc) : okPollAt pc ev = false := by
    obtain ⟨p,k⟩ := ev
    cases k <;> try rfl
    rename_i _ _ success _ _
    cases success <;> simp_all [okPollAt]
  simp [Cnt.bump,ok _ hs,ok _ ho,beq_eq_false_iff_ne.mpr hp]

theorem bias_other (b : Bool) (j : Fin 64) :
    let p := if b then (Site.pre j).pc else (Site.nxt j).pc
    p ≠ 1257 ∧ p ≠ 2239 ∧ p ≠ 1013 := by
  revert b j; decide +kernel

end PTX.Kernels.InklingRelDecode.Proof.Softmax
