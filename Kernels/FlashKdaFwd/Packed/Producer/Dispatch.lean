-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Entry
import all Kernels.FlashKdaFwd.Packed.Producer

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX PTX.Proof Producer

private def dispatch : List Instr :=
  [integer .b .and 666 [.reg 307,.imm 224], integer .b (.setp .ne none) 31 [.reg 666,.imm 128],
   integer .b (.setp .eq none) 32 [.reg 486,.imm 0],
   ⟨none,.int ⟨.or,.pred,false,[some 33],[.reg 31,.reg 32]⟩⟩, ⟨some (33,false),.bra 2105 false⟩,
   integer .s (.setp .lt none) 34 [.reg 314,.imm 1], move (.int .b 32) 2104 (.imm 1),
   move (.int .b 32) 2105 (.imm 0), ⟨some (34,false),.bra 2072 false⟩]

set_option maxRecDepth 60000 in
private theorem dispatch_site : Transfers.slice 1402 9 = some dispatch := by kernel_rfl

private def inputs (t : TState) :=
  setReg (setReg (setReg {t with pc := 1402, fault := none} 307 (b32 129))
    486 (b32 1)) 314 (b32 1)

private theorem set_same {t : TState} {r : Nat} {v : Value} (val : t.regs r = some v) :
    setReg t r v = t := by
  simp [setReg,← val,Function.update_eq_self]

set_option maxRecDepth 60000 in
private theorem taken (base : Nat → Nat → Nat) (L : Launch) (t : TState) :
    (Producer.limited (Producer.model 1402 dispatch) (Prologue.assumptions base) L 129
      1402 1411 9 (inputs t)).map (fun s => (s.pc,s.fault,s.regs 88)) =
      some (1411,none,t.regs 88) := by kernel_rfl

theorem one_token_dispatch (base : Nat → Nat → Nat) (L : Launch) (t : TState)
    (pc : t.pc = 1402) (clear : t.fault = none) (threadId : t.regs 307 = some (b32 129))
    (chosen : t.regs 486 = some (b32 1)) (length : t.regs 314 = some (b32 1)) :
    ∃ u, run kernel (Prologue.assumptions base) L 129 9 t = some u ∧
      u.pc = 1411 ∧ u.fault = none ∧ u.regs 88 = t.regs 88 := by
  have same : inputs t = t := by
    unfold inputs
    rw [← pc,← clear]
    simp only [set_same threadId,set_same chosen,set_same length]
  have h := taken base L t
  rw [same] at h
  obtain ⟨u,steps,flags⟩ := Option.map_eq_some_iff.mp h
  refine ⟨u,Producer.agrees (src := Producer.model 1402 dispatch) ?_ steps,?_⟩
  · intro p low high
    obtain ⟨i,rfl⟩ : ∃ i, p = 1402+i := ⟨p-1402,by omega⟩
    rw [fetch (pc := 1402) (i := i) (by decide) (by omega) dispatch_site]
    change dispatch[i]? = (List.replicate 1402 Election.stop ++ dispatch)[1402+i]?
    have fits : (List.replicate 1402 Election.stop).length ≤ 1402+i := by
      simp only [List.length_replicate]
      omega
    rw [List.getElem?_append_right fits,List.length_replicate,Nat.add_sub_cancel_left]
  · simpa using flags

end FlashKda.Packed.ProducerControl
