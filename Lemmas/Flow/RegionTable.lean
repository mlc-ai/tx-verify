-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.RegionFrame

@[expose] public section

/-! # `regionB` from one scan of the code

A proof tool, generic over the kernel. `regionB K lo hi R` indexes the code once per position,
which a kernel evaluation pays in full for every `lo`. Here the code from `lo0 to hi` is scanned
once as a list: its structure (`instrOk`: positions before `hi`, forward jumps) and the positions
that write each register (`writersL`). A register whose writers all lie before `lo` is kept by the
region from `lo` on, for every `lo` of the scan (`regionB_of_scan`). -/

namespace PTX.Flow
open PTX PTX.Proof PTX.EventFrame

noncomputable section

/-- The structure of one position: a local instruction continues before `hi` (a jump goes forward,
not past `hi`); an unguarded event stops, a guarded one may be skipped before `hi`. -/
def instrOk (hi : Nat) (ins : Instr) (pc : Nat) : Bool :=
  if ins.op.isLocal then Nat.blt pc hi && (match ins.op with
      | .bra tgt _ => Nat.blt pc tgt && Nat.ble tgt hi
      | .brx .. => false
      | _ => true)
  else ins.guard.isNone || Nat.blt pc hi

/-- Every instruction of the list, at its position from `n`, passes `P`. -/
def scanL (P : Instr → Nat → Bool) : List Instr → Nat → Bool
  | [], _ => true
  | ins :: xs, n => P ins n && scanL P xs (n + 1)

/-- The positions of local instructions that write `r`. -/
def writersL (r : Nat) : List Instr → Nat → List Nat
  | [], _ => []
  | ins :: xs, n =>
    (if ins.op.isLocal && (writesRegs ins.op).contains r then [n] else []) ++ writersL r xs (n + 1)

theorem scanL_get {P : Instr → Nat → Bool} :
    ∀ {xs : List Instr} {n i : Nat} {ins : Instr}, scanL P xs n = true → xs[i]? = some ins →
      P ins (n + i) = true
  | [], _, _, _, _, h => by simp at h
  | x :: xs, n, 0, ins, h, hx => by
    obtain rfl : x = ins := by simpa using hx
    simpa [scanL] using (Bool.and_eq_true_iff.mp h).1
  | x :: xs, n, i + 1, ins, h, hx => by
    have := scanL_get (Bool.and_eq_true_iff.mp h).2 (by simpa using hx)
    rwa [show n + 1 + i = n + (i + 1) by omega] at this

theorem mem_writersL {r : Nat} :
    ∀ {xs : List Instr} {n i : Nat} {ins : Instr}, xs[i]? = some ins → ins.op.isLocal = true →
      (writesRegs ins.op).contains r = true → n + i ∈ writersL r xs n
  | [], _, _, _, h, _, _ => by simp at h
  | x :: xs, n, 0, ins, hx, hl, hw => by
    obtain rfl : x = ins := by simpa using hx
    have hw' : r ∈ writesRegs x.op := by simpa using hw
    simp [writersL, hl, hw']
  | x :: xs, n, i + 1, ins, hx, hl, hw => by
    have := mem_writersL (n := n + 1) (r := r) (by simpa using hx) hl hw
    rw [show n + 1 + i = n + (i + 1) by omega] at this
    simp [writersL, this]

theorem regionB_of_scan {K : Kernel} {lo0 hi lo : Nat} {R : List Nat} (h0 : lo0 ≤ lo)
    (hs : scanL (instrOk hi) ((K.code.drop lo0).take (hi + 1 - lo0)) lo0 = true)
    (hw : ∀ r ∈ R, ∀ pc ∈ writersL r ((K.code.drop lo0).take (hi + 1 - lo0)) lo0, pc < lo) :
    regionB K lo hi R = true := by
  unfold regionB
  rw [List.all_eq_true]
  intro i hi'
  have hi2 := List.mem_range.mp hi'
  cases hc : K.code[lo + i]? with
  | none => rfl
  | some ins =>
    have hx : ((K.code.drop lo0).take (hi + 1 - lo0))[lo + i - lo0]? = some ins := by
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
        show lo0 + (lo + i - lo0) = lo + i by omega]
      exact hc
    have hok := scanL_get hs hx
    rw [show lo0 + (lo + i - lo0) = lo + i by omega] at hok
    simp only [instrOk] at hok
    by_cases hl : ins.op.isLocal = true
    · simp only [hl, ↓reduceIte, Bool.and_eq_true] at hok ⊢
      refine ⟨⟨?_, hok.1⟩, ?_⟩
      · rw [List.all_eq_true]
        intro r hr
        by_contra hn
        have hn' : (writesRegs ins.op).contains r = true := by simpa using hn
        have := mem_writersL (n := lo0) (r := r) hx hl hn'
        have := hw r hr _ (by rwa [show lo0 + (lo + i - lo0) = lo + i by omega] at this)
        omega
      · have hm := hok.2
        revert hm
        cases ins.op <;> simp only [Nat.blt_eq, Nat.ble_eq, Bool.and_eq_true, imp_self,
          Bool.false_eq_true]
        omega
    · simp only [Bool.not_eq_true] at hl
      simpa [hl] using hok

end
end PTX.Flow
