-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Run
public import Lemmas.Flow.Regs
public import Lemmas.Flow.Hooks
public import Lemmas.Flow.SegFree

@[expose] public section

/-! # Offsetting a shared pointer by a register

A proof tool, the register form of `exec_add_sharedPtr` (`Lemmas/Flow/Local.lean`): adding an
integer register to a symbolic shared pointer register keeps the pointer's representation and
CTAs and moves its offset (THREAD-POINTER-OFFSET). With a symbolic offset the window check
does not reduce by evaluation, so a segment proof cuts at such an instruction and takes it as
one step whose result is computed here. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- Adding an integer register `q` (holding `k`) to a shared pointer register `r` whose
offset stays in the 32-bit window. -/
theorem exec_add_sharedPtr_reg {A : List Assumption} {L : Launch} {g w wq : Nat} {gen : Bool}
    {t : TState} {d r q : Nat} {i c a k b : Nat} {ik : IType}
    (hr : t.regs r = some (.ptr w gen (.shared i c) (BitVec.ofNat 64 a)))
    (hq : t.regs q = some (.bits wq (BitVec.ofNat 64 k))) (hw : w = 32 ∨ w = 64)
    (ha : a + k < 2 ^ 32) (hk : k < 2 ^ 31) (hb : a + k = b)
    (hik : ik ≠ .b := by decide)
    (hL : ∀ as ∈ A,
      as.localRule L g t (.int ⟨.add, .int ik w, false, [some d], [.reg r, .reg q]⟩) = none)
    (hA : Assumption.SegFreePc A t.pc := by seg_free) :
    execLocalA A L g t (.int ⟨.add, .int ik w, false, [some d], [.reg r, .reg q]⟩) =
      .ok (next (setReg t d (.ptr w gen (.shared i c) (BitVec.ofNat 64 b)))) := by
  subst hb
  have hka : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hkk : (truncBits w (BitVec.ofNat 64 k)).toNat = k := by
    rcases hw with rfl | rfl <;> simp only [truncBits, BitVec.toNat_ofNat] <;> omega
  have hs : toSigned w (truncBits w (BitVec.ofNat 64 k)) = k := by
    rcases hw with rfl | rfl <;> unfold toSigned <;>
      simp only [BitVec.toNat_ofNat, truncBits] <;> split_ifs <;> omega
  have hv : BitVec.ofInt 64 ((a : Int) + k) = BitVec.ofNat 64 (a + k) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega
  have hrule : (IntInstr.mk .add (.int ik w) false [some d] [.reg r, .reg q]).rule =
      some .threadInt := by
    rcases hw with rfl | rfl <;> cases ik <;> first | rfl | exact absurd rfl hik
  simp only [(hA.at rfl).exec, execLocalRule_of_none hL, execLocal_int hrule, execInt,
    DType.width,
    readValue, readReg, hr, hq, bind, Except.bind, pure, Except.pure]
  have hpa : a < 4294967296 := by omega
  have hlo : (0 : Int) ≤ (a : Int) + k := by omega
  have hhi : (a : Int) + k < 4294967296 := by omega
  simp [readBits, readReg, hq, offsetPointer, hka, hs, hv, hw, hpa, hlo, hhi, bind, Except.bind,
    pure, Except.pure]

/-- One local step: adding an integer register to a shared pointer register. -/
theorem run_add_sharedPtr_reg {K : Kernel} {A : List Assumption} {L : Launch} {g pc : Nat}
    {t : TState} {F : List (Nat × Value)} {d r q wq : Nat} {i c a k b : Nat}
    {ik : IType}
    (hc : K.code[pc]? = some ⟨none, .int ⟨.add, .int ik 32, false, [some d], [.reg r, .reg q]⟩⟩)
    (h : At t pc F)
    (hr : (r, .ptr 32 false (.shared i c) (BitVec.ofNat 64 a)) ∈ F)
    (hq : (q, .bits wq (BitVec.ofNat 64 k)) ∈ F) (ha : a + k < 2 ^ 32) (hk : k < 2 ^ 31)
    (hb : a + k = b) (hik : ik ≠ .b := by decide)
    (hL : ∀ as ∈ A,
      as.localRule L g t (.int ⟨.add, .int ik 32, false, [some d], [.reg r, .reg q]⟩) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc) :
    run K A L g 1 t =
      some (next (setReg t d (.ptr 32 false (.shared i c) (BitVec.ofNat 64 b)))) := by
  have he := exec_add_sharedPtr_reg (A := A) (L := L) (g := g) (d := d)
    (holds_mem h.2.2.2.2 hr) (holds_mem h.2.2.2.2 hq) (.inl rfl) ha hk hb hik hL (h.1 ▸ hA)
  simp only [run, tauStep, out, h.2.2.2.1, h.1, hc, guardHolds, Op.isLocal, he]
  rfl

end
end PTX.Flow
