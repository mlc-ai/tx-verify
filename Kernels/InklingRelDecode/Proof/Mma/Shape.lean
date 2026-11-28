-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Machine
public import Kernels.InklingRelDecode.Proof.Iface.Objects
import Kernels.InklingRelDecode.Gen.StepMma
import Kernels.InklingRelDecode.Gen.StepMma01
import Lemmas.Flow.Step.ShapeRegs

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {w : Value} {regs : Nat → Value}
  {i : Nat} {v : Value} {t : TState} {e : Event} {o : Option TState} {ins : Instr}

private theorem aligned_poll {pc dst base par a q : Nat}
    (ha : a < 2 ^ 32) (hal : a % 8 = 0) (hq : q < 2)
    (hb : t.regs base = some (b32 a)) (hr : t.regs par = some (b32 q))
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.mbarWait dst base 0 (.reg par) true .cta)) e o) :
    ∃ ok, e.kind = .wait ⟨.shared, g / L.block, a⟩ q ok true .cta := by
  have loc : smLoc L g (BitVec.ofNat 64 a) 0 = ⟨.shared, g / L.block, a⟩ := by
    unfold smLoc
    congr 1
    simp [truncBits, BitVec.toNat_ofNat]
    omega
  have parity : (truncBits 32 (BitVec.ofNat 64 q)).toNat % 2 = q := by
    simp only [truncBits, BitVec.toNat_ofNat]
    omega
  have hh := fires_wait_reg_al (by rfl) hb hr hf
  rw [loc, parity] at hh
  rcases hh with ok | ⟨_, _, hm⟩
  · exact ok
  · exact (hm hal).elim

theorem ready_poll (hp : Pre Q L mem0) (ht : (code L g regs w).AtD ⟨.kvWait,i,v⟩ t)
    (hc : kernel.code[2462]? = some ins)
    (hf : Fires 2462 (eventTmpl Assumptions.all L g t ins.op) e o) :
    ∃ ok, e.kind = .wait ⟨.shared, g / L.block, L.sharedBase +
      Iface.kvReady ⟨i % 3, by omega⟩⟩ (i / 3 % 2) ok true .cta := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2462)
  obtain ⟨_, _, _, _, hR⟩ := ht
  let V := valueOf L regs w ⟨.kvWait,i,v⟩
  have reg (r : Nat) (hr : r ∈ Flow.live 2462) : t.regs r = some (V r) :=
    holds_mem hR (mem_factsFrom hr)
  have hs := hp.sharedRange
  unfold sharedBytes at hs
  have ha := hp.sharedAlignment
  simp only [Iface.kvReady, ← Nat.add_assoc]
  exact aligned_poll (by omega) (by omega) (by omega) (reg 474 (by decide)) (reg 545 (by decide)) hf

theorem p_poll (hp : Pre Q L mem0) (ht : (code L g regs w).AtD ⟨.pWait,i,v⟩ t)
    (hc : kernel.code[2510]? = some ins)
    (hf : Fires 2510 (eventTmpl Assumptions.all L g t ins.op) e o) :
    ∃ ok, e.kind = .wait ⟨.shared, g / L.block, L.sharedBase +
      Iface.pReady ⟨(i - 1) % 2, by omega⟩⟩ ((i - 1) / 2 % 2) ok true .cta := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2510)
  obtain ⟨_, _, _, _, hR⟩ := ht
  let V := valueOf L regs w ⟨.pWait,i,v⟩
  have reg (r : Nat) (hr : r ∈ Flow.live 2510) : t.regs r = some (V r) :=
    holds_mem hR (mem_factsFrom hr)
  have hs := hp.sharedRange
  unfold sharedBytes at hs
  have ha := hp.sharedAlignment
  simp only [Iface.pReady, ← Nat.add_assoc]
  exact aligned_poll (by omega) (by omega) (by omega) (reg 557 (by decide)) (reg 558 (by decide)) hf

end PTX.Kernels.InklingRelDecode.Proof.Mma
