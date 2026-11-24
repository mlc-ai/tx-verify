-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.StatelessSites
import Kernels.FlashKdaFwd.Audit.StatelessCarry
import Lemmas.Flow.FloatOutcome
import Lemmas.Flow.MemTmpl

/-! Execute the carry instructions and the scalar store on the observed register values.
The registers outside each instruction's operands are arbitrary. -/
namespace FlashKda.Stateless.Trace
open PTX PTX.Flow Carry Carry.Output
noncomputable section

def word (w n : Nat) : Value := .bits w (BitVec.ofNat 64 n)
abbrev afterFma (t : TState) := PTX.next (setReg t 1953 ((FVal.fin lower).toValue .f32))

theorem fma_from_registers (L : Launch) (g : Nat) (t : TState)
    (a : t.regs 1953 = some (word 32 0x3fc00000))
    (b : t.regs 1818 = some (word 32 0x3f2caaaa))
    (c : t.regs 1487 = some (word 32 0xa3020000)) :
    execLocal L g t (.float carryUpdate) = .ok (afterFma t) := by
  have run := execLocal_fma_core (rnd := .rn) (fz := true) (d := 1953)
    (OpndIs.reg (L := L) (g := g) a) (OpndIs.reg b) (OpndIs.reg c)
  have result : coreFloat (fmaI .rn true)
      [word 32 0x3fc00000, word 32 0x3f2caaaa, word 32 0xa3020000] =
      .ok ((FVal.fin lower).toValue .f32) := by
    have ca : classify .f32 (word 32 0x3fc00000) = .ok (.fin incoming) :=
      classify_bits (by decide) operand_bits.1
    have cb : classify .f32 (word 32 0x3f2caaaa) = .ok (.fin multiplier) :=
      classify_bits (by decide) operand_bits.2.1
    have cc : classify .f32 (word 32 0xa3020000) = .ok (.fin delta) :=
      classify_bits (by decide) operand_bits.2.2
    have lane : (fmaI .rn true).lane [.fin incoming,.fin multiplier,.fin delta] =
        some (.val (.fin lower)) := machine_update
    simp only [coreFloat, fmaI, ty1, List.range, List.range.loop, List.mapM_cons, List.mapM_nil,
      floatLane, ite_true, ca, cb, cc, bind, Except.bind, pure, Except.pure] at lane ⊢
    rw [lane]
  rw [result] at run
  exact run

theorem conversion (L : Launch) (g : Nat) (t : TState)
    (h : t.regs 1953 = some ((FVal.fin lower).toValue .f32)) :
    execLocal L g t (.cvt narrow) =
      .ok (PTX.next (setReg t 129 ((FVal.fin (129/128)).toValue .bf16))) := by
  have read : readCvtFloat true t .f32 (.reg 1953) = .ok (.fin lower) := by
    rw [readCvtFloat_reg h (by rfl)]
    change classify .f32 (.float .f32 (lower : ℝ)) = _
    obtain ⟨q,eq,hq⟩ := classify_float_repr (fmt := .f32) (x := (lower : ℝ))
      ⟨0x3f817fff,lower,by decide +kernel,rfl⟩
    have same : q = lower := by exact_mod_cast eq
    rw [same] at hq
    exact hq.trans (by rw [show FVal.ofRat lower = .fin lower by decide +kernel])
  have v : cvtNum narrow .bf16 bf .rn false 1 (.fin lower) = .ok (.fin (129/128)) := by
    simp [cvtNum, cvtSpecial, cvtRound, narrow, next_tile_views.1, cvtFinish,
      bind, Except.bind, pure, Except.pure]
  change (do
    let x ← readCvtFloat true t .f32 (.reg 1953)
    let y ← cvtNum narrow .bf16 bf .rn false 1 x
    pure (PTX.next (setReg t 129 (y.toValue .bf16)))) = _
  rw [read]
  change (do let y ← cvtNum narrow .bf16 bf .rn false 1 (.fin lower)
             pure (PTX.next (setReg t 129 (y.toValue .bf16)))) = _
  rw [v]
  rfl

theorem converted_update (L : Launch) (g : Nat) (t : TState)
    (a : t.regs 1953 = some (word 32 0x3fc00000))
    (b : t.regs 1818 = some (word 32 0x3f2caaaa))
    (c : t.regs 1487 = some (word 32 0xa3020000)) :
    (do let s ← execLocal L g t (.float carryUpdate); execLocal L g s (.cvt narrow)) =
      .ok (PTX.next (setReg (afterFma t) 129 ((FVal.fin (129/128)).toValue .bf16))) := by
  rw [fma_from_registers L g t a b c]
  exact conversion L g _ (by simp [PTX.next,setReg])

def destination (base : Nat) : Acc :=
  {loc := ⟨.global,0,base+8192⟩, size := 2}

/-- For any aligned output buffer, the decoded store emits exactly the two bytes for token
32, channel zero. Its base register points eight bytes beyond that element. -/
theorem store (L : Launch) (g base : Nat) (t : TState) (sub : t.sub = 0)
    (align : base % 2 = 0) (fits : base+8200 < 2^64)
    (ptr : t.regs 2030 = some (word 64 (base+8200)))
    (src : t.regs 79 = some (word 16 0x3f81)) :
    memTmpl [] L g t lastStore = .write (destination base) (word 16 0x3f81).toBytes
      (afterStore t [.reg 79]) := by
  have addr : effAddr L g t .global 2030 (-8) = .ok ⟨.global,0,base+8192⟩ := by
    have arithmetic : (BitVec.ofNat 64 (base+8200) + BitVec.ofInt 64 (-8)).toNat = base+8192 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
      have hn : (BitVec.ofInt 64 (-8)).toNat = 18446744073709551608 := by decide
      rw [hn]
      omega
    have readptr : readBits L g t 64 (.reg 2030) = .ok (BitVec.ofNat 64 (base+8200)) := by
      simp [readBits,readReg,ptr,word,truncBits,bind,Except.bind,pure,Except.pure]
      exact congrArg (BitVec.ofNat 64)
        (Nat.mod_eq_of_lt (show base+8200 < 18446744073709551616 from fits))
    simp only [effAddr,readptr,bind,Except.bind,pure,Except.pure,arithmetic]
  change storeTmpl L g t .global 16 2030 (-8) [.reg 79] = _
  have aligned : (base+8192)%2=0 := by omega
  simp [storeTmpl,addr,elemAcc,sub,aligned,readValue,readReg,src,storeValue,word,
    Value.bytes,destination,bind,Except.bind,pure,Except.pure,Loc.at]

theorem bytes : (word 16 0x3f81).toBytes.map byteBits = [some 0x81, some 0x3f] := by
  decide +kernel

end
end FlashKda.Stateless.Trace
