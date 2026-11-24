-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.ProducerControl
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX

def startupEvent : Op → Bool
  | .warp w => match w.kind with
    | .shfl _ | .elect => true
    | _ => false
  | .mbarInit .. | .fenceMbarInit | .barSync .. => true
  | _ => false

private def forward : Op → Bool
  | .bra dst _ => decide (48 ≤ dst ∧ dst ≤ 111)
  | .brx .. | .exit | .ret => false
  | _ => true

def startupRegs := [307,2247,88]

private def startupCheck (i : Instr) :=
  forward i.op && (i.op.isLocal || startupEvent i.op) &&
    startupRegs.all fun r => !(writes i.op).contains r

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked : (Transfers.slice 48 63).map (List.all · startupCheck) = some true := by
  kernel_rfl

theorem startup_site {pc : Nat} {i : Instr} (lo : 48 ≤ pc) (hi : pc < 111)
    (site : kernel.code[pc]? = some i) :
    (∀ dst, dst = Proof.nextPc i.op pc ∨ Proof.BrxTarget i.op dst → 48 ≤ dst ∧ dst ≤ 111) ∧
    i.op ≠ .ret ∧ i.op ≠ .exit ∧ (i.op.isLocal = false → startupEvent i.op = true) ∧
    ∀ r ∈ startupRegs, r ∉ writes i.op := by
  have h := checked
  rw [instructions (pc := 48) (n := 63) (by decide)] at h
  have member : i ∈ (kernel.code.drop 48).take 63 := by
    apply List.mem_of_getElem?
    rw [List.getElem?_take_of_lt (show pc-48 < 63 by omega),List.getElem?_drop,
      show 48+(pc-48)=pc by omega,site]
  have ok := List.all_eq_true.mp (Option.some.inj h) i member
  simp [startupCheck,Bool.and_eq_true,Bool.or_eq_true,List.all_eq_true] at ok
  obtain ⟨⟨jump,kind⟩,regs⟩ := ok
  refine ⟨?_,?_,?_,fun ne => kind.resolve_left (by simp [ne]),regs⟩
  · intro dst edge
    have range : 48 ≤ pc+1 ∧ pc+1 ≤ 111 := by omega
    cases op : i.op <;> simp_all [forward,Proof.nextPc,Proof.BrxTarget]
  all_goals intro eq; simp [eq,forward] at jump

end FlashKda.Packed.ProducerControl
