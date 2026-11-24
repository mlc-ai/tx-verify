-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
import Lemmas.Flow.Step.SiteShape
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A global word load faults only when misaligned (library candidate)

`fires_load_reg` (`Lemmas/Flow/Step/ShapeRegs.lean`) with the fault's condition kept: a global
32-bit load from a 64-bit address register reads the word at the address plus the offset, or is
undefined behaviour with that address not 4-aligned. -/

namespace PTX.Flow

open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat}

theorem fires_load_reg_al {t : TState} {dst base : Nat} {off : Int} {pc : Nat} {e : Event}
    {o : Option TState} {x : BitVec 64} (hs : t.sub = 0) (hr : t.regs base = some (.bits 64 x))
    (hf : Fires pc (loadTmpl A L g t .global false 32 [dst] base off) e o) {f : Fault}
    (hk : e.kind = .ub f) : (truncBits 64 x + BitVec.ofInt 64 off).toNat % 4 ≠ 0 := by
  simp only [loadTmpl, effAddr, readBits, readReg, hr, bind, Except.bind, pure, Except.pure,
    elemAcc, hs, Bool.false_eq_true, ↓reduceIte] at hf
  split_ifs at hf
  all_goals first
    | (simp only [List.length_cons, List.length_nil, Nat.reduceDiv, Nat.zero_add, Nat.mul_one,
        OfNat.ofNat_ne_zero, false_or, not_not] at *; omega)
    | (simp only [Fires] at hf
       obtain ⟨bs, -, he, -⟩ := hf
       rw [congrArg Event.kind he] at hk
       cases hk)

/-- A load located by its address register faults only when misaligned (`shape_ldM`). -/
theorem fires_load_al {t : TState} {sp : Space} {w : Nat} {ds : List Nat} {base : Nat}
    {off : Int} {loc : Loc} {j pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (loadTmpl A L g t sp false w ds base off) e o)
    (hea : effAddr L g t sp base off = .ok loc) (hs : t.sub = j) {f : Fault}
    (hk : e.kind = .ub f) : w / 8 = 0 ∨ loc.addr % (w / 8 * ds.length) ≠ 0 :=
  shape_ldM (P := fun e => e.kind = .ub f → w / 8 = 0 ∨ loc.addr % (w / 8 * ds.length) ≠ 0)
    hf hea hs (fun _ _ h => by cases h) (fun hm _ => hm) hk

end

end PTX.Flow
