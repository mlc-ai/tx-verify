-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.RawArith
public import Lemmas.Flow.Arith32Word

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof Arith32

variable {L : Launch} {g r dst δ : Nat} {t u : TState} {w : Value} {op : Opnd}

noncomputable def addBase (v : Value) (δ : Nat) : Value :=
  match v with
  | .ptr _ gen target off => .ptr 32 gen target (BitVec.ofInt 64 ((off.toNat : Int) + δ))
  | _ => b32 (((word v).toNat + δ) % 2^32)

theorem addBase_bits (n δ : Nat) :
    addBase (b32 (n % 2^32)) δ = b32 ((n+δ)%2^32) := by
  apply congrArg b32
  change ((truncBits 32 (BitVec.ofNat 64 (n % 2^32))).toNat+δ)%2^32 = _
  simp only [truncBits,BitVec.toNat_ofNat]
  omega

private theorem bits_sum (v : Value) (n : Nat) :
    .bits 32 (truncBits 32 (truncBits 32 (v.regBits.getD 0) + W n)) =
      b32 (((word v).toNat + n) % 2 ^ 32) := by
  unfold b32 word
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_add]
  omega

set_option linter.unusedSimpArgs false in
/-- Scalar addition may preserve a symbolic pointer. Its displacement is nonnegative
and less than 2^31 at all three uses. Any failing evaluation ends the crossing. -/
theorem raw_add (flip : Bool) (hr : t.regs r = some w) (hδ : δ < 2 ^ 31)
    (hv : readValue L g t 32 op = .ok (b32 δ)) (hb : readBits L g t 32 op = .ok (W δ))
    (he : execInt L g t ⟨.add, .int .s 32, false, [some dst],
      if flip then [op,.reg r] else [.reg r,op]⟩ = .ok u) :
    u = PTX.next (setReg t dst (addBase w δ)) := by
  have hv' : readValue L g t 32 (.reg r) = .ok w := by simp [readValue,readReg,hr]; rfl
  have sign := toSigned_W hδ
  have hb' := bits_sum w δ
  cases flip <;> simp only [Bool.false_eq_true, ↓reduceIte, execInt, DType.width, hv', hv,
    b32, bind, Except.bind, hb, sign] at he
  all_goals
    cases hx : readBits L g t 32 (.reg r) with
    | ok x =>
      have ha := Lib.readBits_eq_pattern hr hx
      cases w with
      | ptr =>
        obtain ⟨_,hf⟩ := readBits_regBits_none (w := 32) (L := L) (g := g) hr rfl
        rw [hx] at hf
        cases hf
      | _ =>
        simp only [hx, hb, pure, Except.pure, ha] at he
        rw [← Except.ok.inj he]
        first | exact congrArg (fun v => PTX.next (setReg t dst v)) hb' |
          (rw [BitVec.add_comm]; exact congrArg (fun v => PTX.next (setReg t dst v)) hb')
    | error f =>
      cases w with
      | ptr pw gen space off =>
        cases space <;>
          simp only [hx, hb, sign, offsetPointer, bind, Except.bind, pure, Except.pure] at he
        all_goals repeat' split at he
        all_goals first | contradiction |
          (rename_i hp; split_ifs at hp; cases hp; exact (Except.ok.inj he).symm)
      | _ => simp only [hx, hb] at he; contradiction

theorem sum_span {L : Launch} {g : Nat} {V : Nat → Value} {rs rs' : List Nat}
    {pc dst r δ : Nat} {op : Opnd} (flip : Bool) (hδ : δ < 2 ^ 31)
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.add, .int .s 32, false, [some dst],
      if flip then [op,.reg r] else [.reg r,op]⟩⟩) (hs : Assumptions.emuSites.contains pc = false)
    (hr : r ∈ rs) (hval : V dst = addBase (V r) δ)
    (hOp : ∀ t, Holds t.regs (factsFrom rs V) → readValue L g t 32 op = .ok (b32 δ) ∧
      readBits L g t 32 op = .ok (W δ))
    (live : ∀ x ∈ rs', x = dst ∨ x ∈ rs)
    (hl : (Op.int ⟨.add, .int .s 32, false, [some dst],
      if flip then [op,.reg r] else [.reg r,op]⟩).isLocal = true := by rfl) :
    SegU kernel Assumptions.all L g pc (factsFrom rs V) (pc + 1) (factsFrom rs' V) := by
  apply Lib.scalarStepU hc hl (by cases flip <;> rfl) hs (v := V dst)
  · intro t u hR he
    rw [hval]
    obtain ⟨hv,hb⟩ := hOp t hR
    exact raw_add flip (holds_mem hR (mem_factsFrom hr)) hδ hv hb he
  · exact fun _ => Lib.writeLive live

theorem delta_reg {L : Launch} {g r δ : Nat} {rs : List Nat} {V : Nat → Value}
    {t : TState} (h : Holds t.regs (factsFrom rs V))
    (hr : r ∈ rs) (hv : V r = b32 δ) (hδ : δ < 2 ^ 32) :
    readValue L g t 32 (.reg r) = .ok (b32 δ) ∧ readBits L g t 32 (.reg r) = .ok (W δ) := by
  have hh := hv ▸ holds_mem h (mem_factsFrom hr)
  exact ⟨by simp [readValue, readReg, hh]; rfl, (readBits_regBits (L := L) (g := g) (w := 32) hh
    (show _ = some (W δ) from rfl)).trans (congrArg Except.ok (r32_W hδ))⟩

end PTX.Kernels.InklingRelDecode.Proof.Lib
