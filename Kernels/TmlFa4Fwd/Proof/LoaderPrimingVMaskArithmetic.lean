-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKPacket
import Lemmas.Flow.SignedBits

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

def primingMaskWord (len tile tid : Nat) : Nat :=
  (len + 2 ^ 32 - kvCopyRow tile tid 0) % 2 ^ 32

def primingMaskFact (len tile tid : Nat) (pair : Fin 16) : Nat × Value :=
  (kCopyByteReg pair, b32 (kvCopySize len tile tid pair))

def primingMaskPred (len tile tid : Nat) (pair : Fin 16) : Nat × Value :=
  (124 + pair.val, .pred (decide (kvCopyRow tile tid pair < len)))

private def primingMaskCompareInstr (pair : Fin 16) : IntInstr where
  op := .setp .gt none
  ty := .int .s 32
  dsts := [some (124 + pair.val)]
  srcs := [.reg 1852, .imm (8 * pair.val : Nat)]

private def isInteger (expected : IntInstr) (code : Option Instr) : Bool :=
  code.any fun ins => ins.guard.isNone && match ins.op with
    | .int actual => decide (actual = expected)
    | _ => false

private theorem isInteger_sound {code : Option Instr} {expected : IntInstr}
    (h : isInteger expected code = true) :
    code = some ⟨none, .int expected⟩ := by
  cases code with
  | none => contradiction
  | some ins =>
    obtain ⟨guard, op⟩ := ins
    cases guard <;> cases op <;> simp [isInteger] at h
    subst_vars
    rfl

private theorem primingMaskCompareCode (pair : Fin 16) (hPair : 0 < pair.val) :
    kernel.code[primingKPredicatePc pair]? = some ⟨none, .int (primingMaskCompareInstr pair)⟩ := by
  have hTable : (List.finRange 16).all (fun j => j.val == 0 ||
      isInteger (primingMaskCompareInstr j) (kernel.code[primingKPredicatePc j]?)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply isInteger_sound
  have h := List.all_eq_true.mp hTable pair (List.mem_finRange pair)
  simpa [Nat.ne_of_gt hPair] using h

theorem primingMaskCompareNonvector (pair : Fin 16) (hPair : 0 < pair.val) :
    ∃ ins, kernel.code[primingKPredicatePc pair]? = some ins ∧ loaderVector ins.op = false :=
  ⟨_, primingMaskCompareCode pair hPair, rfl⟩

/-- All later K pairs compare the retained residual with the decoded row offset. -/
theorem primingMaskCompare {l : Launch} {g len tile tid : Nat}
    (hLen : len < 2 ^ 31) (hRow : kvCopyRow tile tid 0 < 2 ^ 31)
    (pair : Fin 16) (hPair : 0 < pair.val) :
    Seg kernel [] l g 1 (primingKPredicatePc pair) [(1852, b32 (primingMaskWord len tile tid))]
      (primingKPredicatePc pair + 1) [primingMaskPred len tile tid pair] := by
  let j : Fin 15 := ⟨pair.val - 1, by have := pair.isLt; omega⟩
  have hPair' : primingKLaterPair j = pair := by
    apply Fin.ext
    change pair.val - 1 + 1 = pair.val
    omega
  simpa only [hPair', primingMaskWord, primingMaskPred] using
    primingKLaterMaskForAll (l := l) (g := g) hLen hRow j

private def primingMaskSelectInstr (pair : Fin 16) : IntInstr where
  op := .selp
  ty := .int .b 32
  dsts := [some (kCopyByteReg pair)]
  srcs := [.imm 16, .imm 0, .reg (124 + pair.val)]

private theorem primingMaskSelectCode (pair : Fin 16) :
    kernel.code[kCopyPc pair - 1]? = some ⟨none, .int (primingMaskSelectInstr pair)⟩ := by
  have hTable : (List.finRange 16).all (fun j =>
      isInteger (primingMaskSelectInstr j) (kernel.code[kCopyPc j - 1]?)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  exact isInteger_sound (List.all_eq_true.mp hTable pair (List.mem_finRange pair))

theorem primingMaskSelectNonvector (pair : Fin 16) :
    ∃ ins, kernel.code[kCopyPc pair - 1]? = some ins ∧ loaderVector ins.op = false :=
  ⟨_, primingMaskSelectCode pair, rfl⟩

/-- Every mask setter saves the exact byte length later reused by the V vector. -/
theorem primingMaskSelect {l : Launch} {g len tile tid : Nat} (pair : Fin 16) :
    Seg kernel [] l g 1 (kCopyPc pair - 1) [primingMaskPred len tile tid pair]
      (kCopyPc pair) [primingMaskFact len tile tid pair] := by
  let inst := primingMaskSelectInstr pair
  have hCode := primingMaskSelectCode pair
  intro t ht
  let live := decide (kvCopyRow tile tid pair < len)
  let u := next (setReg t (kCopyByteReg pair) (b32 (kvCopySize len tile tid pair)))
  have hReg : t.regs (124 + pair.val) = some (.pred live) := ht.2.2.2.2.1
  have hExec : execLocalA [] l g t (.int inst) = .ok u := by
    rw [execLocalA_nil, execLocal_selp (i := inst) rfl]
    by_cases h : kvCopyRow tile tid pair < len
    all_goals simp [inst, primingMaskSelectInstr, execMove, readReg, readValue, readBits, hReg,
      live, h, kvCopySize, u, b32, DType.width, Value.bytes, bind, Except.bind, pure, Except.pure]
    all_goals rfl
  have hPc : kCopyPc pair - 1 + 1 = kCopyPc pair := by fin_cases pair <;> decide
  have hu : At u (kCopyPc pair) [primingMaskFact len tile tid pair] := hPc ▸
    (ht.mono (show Holds t.regs [] from trivial)).set (by simp)
  have hr : run kernel [] l g 1 t = some u :=
    run_local (K := kernel) (pc := kCopyPc pair - 1) hCode rfl ht hExec
  exact ⟨u, hr, hu⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
