-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Machine

@[expose] public section

/-! # The allocation word the MMA warp keeps

The MMA warp's role records the word it reads back after the allocation (`ta`, at `ldAlloc`) and
never changes it afterwards: every step from a site past the read keeps the word and stays past
the read (`Mma.succ_ta`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {g : Nat}

/-- A site of the MMA warp's role after the read of the allocation word. -/
def Mma.past : Mma.Site → Bool
  | .bar1 | .ldAlloc => false
  | _ => true

theorem Mma.past_wtNext : ∀ k, Mma.past (Mma.wtNext k) = true := by decide
theorem Mma.past_shNext : ∀ k, Mma.past (Mma.shNext k) = true := by decide
theorem Mma.past_qkDone : ∀ k, Mma.past (Mma.qkDone k) = true := by decide
theorem Mma.past_pvDone : ∀ k, Mma.past (Mma.pvDone k) = true := by decide

theorem Mma.ta_setS (v : Mma.V) (x : BitVec 64) (k : Fin 14) : (Mma.setS v x k).ta = v.ta := by
  fin_cases k <;> rfl

theorem Mma.ta_passStart (late : Bool) (d : Mma.D) :
    (Mma.passStart p L g late d).v.ta = d.v.ta ∧ Mma.past (Mma.passStart p L g late d).site := by
  cases late <;> simp only [Mma.passStart] <;> split_ifs <;> exact ⟨rfl, rfl⟩

theorem Mma.ta_enterLoop (d : Mma.D) :
    (Mma.enterLoop p L g d).v.ta = d.v.ta ∧ Mma.past (Mma.enterLoop p L g d).site := by
  simp only [Mma.enterLoop]; split <;> exact ⟨rfl, rfl⟩

theorem Mma.ta_loopEnd (d : Mma.D) :
    (Mma.loopEnd d).v.ta = d.v.ta ∧ Mma.past (Mma.loopEnd d).site := by
  simp only [Mma.loopEnd]; split <;> exact ⟨rfl, rfl⟩

theorem Mma.ta_ceNext (d : Mma.D) (c : Fin 12) :
    (Mma.ceNext p L g d c).v.ta = d.v.ta ∧ Mma.past (Mma.ceNext p L g d c).site := by
  fin_cases c <;> simp only [Mma.ceNext, Mma.enterLoop, Mma.loopEnd] <;> (try split) <;>
    first | exact Mma.ta_passStart true d | exact ⟨rfl, rfl⟩ | exact ⟨trivial, rfl⟩

theorem Mma.ta_afterTotal (k : Epilogue.Scan) (d : Mma.D) (x : BitVec 64) :
    (Mma.afterTotal p L g k d x).v.ta = d.v.ta ∧ Mma.past (Mma.afterTotal p L g k d x).site := by
  cases k <;> simp only [Mma.afterTotal, Mma.scanExit, Mma.loopHead] <;> split_ifs <;>
    exact ⟨rfl, rfl⟩

theorem Mma.ta_afterTiles {d d' : Mma.D} {x : BitVec 64}
    (h : Mma.afterTiles p L g d x = some d') : d'.v.ta = d.v.ta ∧ Mma.past d'.site := by
  dsimp only [Mma.afterTiles] at h
  split_ifs at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    exact ⟨rfl, rfl⟩

set_option maxHeartbeats 8000000 in
/-- **A step from a state past the read keeps its allocation word.** -/
theorem Mma.succ_ta {d d' : Mma.D} {e : Event} (hp : Mma.past d.site = true)
    (h : Mma.succ p L g d e = some (some d')) : d'.v.ta = d.v.ta ∧ Mma.past d'.site := by
  obtain ⟨s, v⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [Mma.past, Bool.false_eq_true] at hp <;>
    simp only [Mma.succ, Mma.word32] at h
  all_goals (repeat' split at h)
  all_goals first
    | (cases h; done)
    | (simp only [Option.some.injEq, reduceCtorEq] at h; subst h; exact ⟨rfl, rfl⟩)
    | (simp only [Option.some.injEq] at h; subst h; exact Mma.ta_afterTotal _ _ _)
    | (simp only [Option.map_eq_some_iff, Option.some.injEq] at h
       obtain ⟨d0, h0, rfl⟩ := h
       exact Mma.ta_afterTiles h0)
    | (simp only [Option.some.injEq, reduceCtorEq] at h; subst h
       first
         | exact Mma.ta_ceNext _ _
         | exact Mma.ta_passStart _ _
         | exact ⟨rfl, Mma.past_wtNext _⟩
         | exact ⟨Mma.ta_setS _ _ _, Mma.past_shNext _⟩
         | exact ⟨rfl, Mma.past_qkDone _⟩
         | exact ⟨rfl, Mma.past_pvDone _⟩
         | (refine ⟨rfl, ?_⟩; (repeat' split) <;> first | rfl | (simp_all [Mma.past]; done)))

end
end PTX.Kernels.TmlFa4Fwd.Proof
