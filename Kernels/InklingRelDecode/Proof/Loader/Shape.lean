-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Machine
public import Lemmas.Flow.Step.ShapeRegs
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
import Lemmas.Flow.Step.SiteShape
import Lemmas.Flow.Bits
import Kernels.InklingRelDecode.Proof.Loader.Ring
import Kernels.InklingRelDecode.Gen.StepLoader

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Proof PTX.Flow Arith32

noncomputable section

/-- Barrier displacement before the empty-ring base is added. -/
def slotBytes (i : Value) : BitVec 64 :=
  mad32 (quotient (bits i)) (i32 (-24)) (shl (bits i) 3)

def emptyWord (L : Launch) (i : Value) : BitVec 64 :=
  addi (add32 (r32 (BitVec.ofNat 64 L.sharedBase)) (slotBytes i)) 213248

def pollParity (i : Value) : BitVec 64 := andi (not32 (quotient (bits i))) 1

/-- The barrier address expression reduces to the slot number even when the intermediate
shift or the product by -24 wraps. -/
theorem slotBytes_eq (i : Value) (hi : (bits i).toNat < 2 ^ 31) :
    slotBytes i = BitVec.ofNat 64 (8 * ((bits i).toNat % 3)) := by
  unfold slotBytes
  rw [quotient_eq hi]
  generalize (bits i) = x at hi ⊢
  have he : x = BitVec.ofNat 64 x.toNat := by simp
  generalize x.toNat = n at hi he ⊢
  rw [he]
  nf_simp [mad32, shl, i32, r32]
  omega

theorem empty_location {L : Launch} (g : Nat) (i : Value)
    (hs : L.sharedBase + 213340 ≤ 2 ^ 18) (hi : (bits i).toNat < 2 ^ 31) :
    smLoc L g (emptyWord L i) 0 =
      ⟨.shared, g / L.block, L.sharedBase + Iface.kvEmpty ⟨(bits i).toNat % 3, by omega⟩⟩ := by
  unfold smLoc emptyWord
  rw [slotBytes_eq i hi]
  apply congrArg (Loc.mk .shared (g / L.block))
  nf_simp [addi, add32, r32, i32, Iface.kvEmpty]
  omega

theorem parity_eq (i : Value) (hi : (bits i).toNat < 2 ^ 31) :
    (r32 (pollParity i)).toNat % 2 = 1 - (bits i).toNat / 3 % 2 := by
  unfold pollParity
  rw [quotient_eq hi]
  generalize (bits i).toNat = n at hi ⊢
  change (r32 (r32 (not32 (BitVec.ofNat 64 (n / 3))) &&& BitVec.ofNat 64 1)).toNat % 2 = _
  simp only [not32, r32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_and,
    BitVec.toNat_not, Nat.reducePow, Nat.reduceMod, Nat.and_one_is_mod]
  omega

/-- The event at the empty-ring poll, for any input counter, including its alignment fault. -/
theorem poll_shape {L : Launch} {g : Nat} {w : Value} {regs : Nat → Value}
    {i n a b : Value} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (ht : (code L g w regs).AtD ⟨.poll,i,n,a,b⟩ t)
    (hc : kernel.code[2374]? = some ins)
    (hf : Fires 2374 (eventTmpl Assumptions.all L g t ins.op) e o) :
    (∃ ok, e.kind = .wait (smLoc L g (emptyWord L i) 0)
      ((r32 (pollParity i)).toNat % 2) ok true .cta) ∨
      ∃ f, e.kind = .ub f ∧ (smLoc L g (emptyWord L i) 0).addr % 8 ≠ 0 := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2374)
  obtain ⟨_, _, _, _, hregs⟩ := ht
  let val := valueOf L g w regs ⟨.poll,i,n,a,b⟩
  have hreg (r : Nat) (hr : r ∈ Flow.live 2374) : t.regs r = some (val r) :=
    holds_mem hregs (mem_factsFrom hr)
  exact fires_wait_reg_al (by rfl) (hreg 578 (by decide)) (hreg 579 (by decide)) hf

/-- In the reachable counter range the poll cannot fault, and its slot and phase
are determined by the loop iteration. -/
theorem poll_slot {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {w : Value}
    {regs : Nat → Value} {i n a b : Value} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hp : Pre Q L mem0) (hi : (bits i).toNat < 2 ^ 31)
    (ht : (code L g w regs).AtD ⟨.poll,i,n,a,b⟩ t) (hc : kernel.code[2374]? = some ins)
    (hf : Fires 2374 (eventTmpl Assumptions.all L g t ins.op) e o) :
    ∃ ok, e.kind = .wait ⟨.shared, g / L.block, L.sharedBase +
        Iface.kvEmpty ⟨(bits i).toNat % 3, by omega⟩⟩
      (1 - (bits i).toNat / 3 % 2) ok true .cta := by
  have hh := poll_shape ht hc hf
  rw [empty_location g i hp.sharedRange hi, parity_eq i hi] at hh
  rcases hh with h | ⟨_, _, bad⟩
  · exact h
  · have hal := hp.sharedAlignment
    simp only [Iface.kvEmpty] at bad
    omega

def readyWord (L : Launch) (i : Value) : BitVec 64 :=
  addi (add32 (r32 (BitVec.ofNat 64 L.sharedBase)) (slotBytes i)) 213216

theorem ready_location {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {i : Value}
    {t : TState} (hp : Pre Q L mem0) (hi : (bits i).toNat < 2 ^ 31)
    (hr : t.regs 580 = some (.bits 32 (readyWord L i))) :
    mbarLoc L g t 580 0 = .ok (Iface.kvReadyLoc L (g / L.block)
      ⟨(bits i).toNat % 3, by omega⟩) := by
  have room := hp.sharedRange
  change L.sharedBase + 213340 ≤ 2 ^ 18 at room
  have hb : (r32 (r32 (readyWord L i) + BitVec.ofInt 64 0)).toNat =
      L.sharedBase + (213216 + 8 * ((bits i).toNat % 3)) := by
    unfold readyWord
    rw [slotBytes_eq i hi]
    nf_simp [r32, add32, addi, i32]
    omega
  have hal := hp.sharedAlignment
  simp only [mbarLoc, effAddr, sharedEffAddr, readBits, readReg, hr, bind, Except.bind, pure,
    Except.pure]
  change (if (r32 (r32 (readyWord L i) + BitVec.ofInt 64 0)).toNat % 8 = 0 then _ else _) = _
  rw [hb, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
  rfl

/-- The lane-zero producer credits the ready barrier with one arrival and eight boxes'
worth of bytes. -/
theorem arrive_slot {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {w : Value}
    {regs : Nat → Value} {i n a b : Value} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hp : Pre Q L mem0) (hi : (bits i).toNat < 2 ^ 31)
    (ht : (code L g w regs).AtD ⟨.arrive,i,n,a,b⟩ t) (hc : kernel.code[2378]? = some ins)
    (hf : Fires 2378 (eventTmpl Assumptions.all L g t ins.op) e o) :
    e.kind = .arrive (Iface.kvReadyLoc L (g / L.block) ⟨(bits i).toNat % 3, by omega⟩)
      65536 1 true .cta := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2378)
  let bar := addi (add32 (r32 (BitVec.ofNat 64 L.sharedBase)) (slotBytes i)) 213216
  obtain ⟨_, _, _, _, hregs⟩ := ht
  have hr : t.regs 580 = some (.bits 32 bar) :=
    holds_mem hregs (mem_factsFrom (val := valueOf L g w regs ⟨.arrive,i,n,a,b⟩)
      (show 580 ∈ Flow.live 2378 by decide))
  exact fires_arrive_exact (by rfl) (ready_location hp hi hr) (by rfl) (by rfl) hf

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
