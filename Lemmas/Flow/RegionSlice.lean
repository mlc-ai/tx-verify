-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.RegionFrame

@[expose] public section

/-! # `regionB` on a slice of the code

A proof tool, generic over the kernel (promoted from tml-fa4's `Proof2/Lib/RegionSlice.lean`).
`regionB K lo hi R` looks each position up in the whole code (`K.code[lo + i]?`), which the kernel
evaluates from the start of the list for every position; over a region of several hundred positions
that dominates a module's check. `regionS` walks the slice `(K.code.drop lo).take (hi + 1 - lo)`
once and decides the same condition (`regionB_of_S`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {K : Kernel}

/-- The condition of `regionB` at one instruction at position `pc`. -/
def regionOk (lo hi : Nat) (R : List Nat) (pc : Nat) (ins : Instr) : Bool :=
  if ins.op.isLocal then
    R.all (fun r => !(writesRegs ins.op).contains r) && Nat.blt pc hi &&
      (match ins.op with
        | .bra tgt _ => Nat.ble lo tgt && Nat.ble tgt hi
        | .brx .. => false
        | _ => true)
  else ins.guard.isNone || Nat.blt pc hi

/-- `regionOk` at every instruction of a slice starting at position `pc`. -/
def regionS (lo hi : Nat) (R : List Nat) : Nat → List Instr → Bool
  | _, [] => true
  | pc, ins :: rest => regionOk lo hi R pc ins && regionS lo hi R (pc + 1) rest

theorem regionS_get {lo hi : Nat} {R : List Nat} :
    ∀ {pc : Nat} {l : List Instr}, regionS lo hi R pc l = true →
      ∀ i (h : i < l.length), regionOk lo hi R (pc + i) l[i] = true
  | _, [], _, i, h => absurd h (by simp)
  | pc, ins :: rest, hs, i, h => by
    simp only [regionS, Bool.and_eq_true] at hs
    cases i with
    | zero => simpa using hs.1
    | succ i =>
      have := regionS_get hs.2 i (by simpa using h)
      rw [show pc + (i + 1) = pc + 1 + i by omega]
      simpa using this

/-- **`regionB` from the slice.** -/
theorem regionB_of_S {lo hi : Nat} {R : List Nat}
    (h : regionS lo hi R lo ((K.code.drop lo).take (hi + 1 - lo)) = true) :
    regionB K lo hi R = true := by
  unfold regionB
  refine List.all_eq_true.mpr fun i hi' => ?_
  have hi'' := List.mem_range.mp hi'
  cases hc : K.code[lo + i]? with
  | none => rfl
  | some ins =>
    have hlt : lo + i < K.code.length := by
      rcases Nat.lt_or_ge (lo + i) K.code.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at hc; cases hc
    have hlen : i < ((K.code.drop lo).take (hi + 1 - lo)).length := by
      simp only [List.length_take, List.length_drop]
      omega
    have hget : ((K.code.drop lo).take (hi + 1 - lo))[i] = ins := by
      have e : ((K.code.drop lo).take (hi + 1 - lo))[i]? = K.code[lo + i]? := by
        rw [List.getElem?_take_of_lt hi'', List.getElem?_drop]
      rw [hc, List.getElem?_eq_getElem hlen] at e
      exact Option.some.inj e
    have := regionS_get h i hlen
    rw [hget] at this
    exact this

end
end PTX.Flow
