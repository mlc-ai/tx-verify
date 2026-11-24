-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderLoop
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Objects
public import Lemmas.Flow.Events
public import Kernels.Fp16Gemm8192.Proof.Thread.Cluster

@[expose] public section

/-! # The loader's input-ring events

At block `b` of a trip the loader polls slot `b % 4`'s empty barrier in its own CTA with
the block's parity; on the cluster's leader CTA it then arrives on the slot's full barrier,
expecting the tile's 98304 bytes. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000


def waitBase : Fin 8 → Nat
  | 0 => 656 | 1 => 675 | 2 => 694 | 3 => 713
  | 4 => 732 | 5 => 752 | 6 => 772 | 7 => 792

def waitPar : Fin 8 → Nat
  | 0 => 657 | 1 => 676 | 2 => 695 | 3 => 714
  | 4 => 733 | 5 => 753 | 6 => 773 | 7 => 793

theorem code_wait_ops : ∀ b : Fin 8, kernel.code[(Site.wait b).pc]? =
    some ⟨none, .mbarWait (waitPred b) (waitBase b) 0 (.reg (waitPar b)) true .cta⟩
  | 0 => Flow.code_mbarWait_0 | 1 => Flow.code_mbarWait_1 | 2 => Flow.code_mbarWait_2
  | 3 => Flow.code_mbarWait_3 | 4 => Flow.code_mbarWait_4 | 5 => Flow.code_mbarWait_5
  | 6 => Flow.code_mbarWait_6 | 7 => Flow.code_mbarWait_7

theorem waitBase_live : ∀ b : Fin 8, waitBase b ∈ Flow.live (Site.wait b).pc := by
  intro b
  fin_cases b <;> table_decide

theorem waitPar_live : ∀ b : Fin 8, waitPar b ∈ Flow.live (Site.wait b).pc := by
  intro b
  fin_cases b <;> table_decide

theorem waitBase_value (L : Launch) (g : Nat) (d : D) (b : Fin 8) :
    valueOf L g d (waitBase b) = b32 (L.sharedBase + 40 + 8 * (b.val % 4)) := by
  fin_cases b <;> simp only [waitBase] <;> loader_values

theorem waitPar_value (L : Launch) (g : Nat) (d : D) (b : Fin 8) :
    valueOf L g d (waitPar b) = b32 (InputRing.producerParity b) := by
  fin_cases b <;> simp only [waitPar, InputRing.producerParity] <;> loader_values <;> simp

/-- The poll at block `b` names slot `b % 4`'s empty barrier in the loader's CTA and the
block's parity. -/
theorem wait_event {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState} {o :
    Option TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (b : Fin 8) (hs : d.site = .wait b)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ ok acq sc, e = ⟨d.site.pc, .wait (InputRing.emptyLoc L (g / L.block) (InputRing.slotOf b))
      (InputRing.producerParity b) ok acq sc⟩ := by
  obtain ⟨s, m, n, q, cp, r, x⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  rw [code_wait_ops b] at hc
  cases hc
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hb : t.regs (waitBase b) = some (b32 (L.sharedBase + 40 + 8 * (b.val % 4))) :=
    (waitBase_value L g _ b) ▸ holds_mem h.2.2.2.2 (Flow.mem_factsFrom (waitBase_live b))
  have hp : t.regs (waitPar b) = some (b32 (InputRing.producerParity b)) :=
    (waitPar_value L g _ b) ▸ holds_mem h.2.2.2.2 (Flow.mem_factsFrom (waitPar_live b))
  have hm := mbarLoc_b32 (L := L) (g := g) hb (by omega) (by omega)
  have hq : readBits L g t 32 (.reg (waitPar b)) =
      .ok (truncBits 32 (BitVec.ofNat 64 (InputRing.producerParity b))) := by
    simp [readBits, readReg, hp, b32, bind, Except.bind, pure, Except.pure]
  obtain ⟨ok, acq, sc, he, -⟩ := fires_wait_at hm hq hf
  have hpar : (truncBits 32 (BitVec.ofNat 64 (InputRing.producerParity b))).toNat % 2 =
      InputRing.producerParity b := by
    unfold InputRing.producerParity; split_ifs <;> decide
  exact ⟨ok, acq, sc, by rw [he, hpar]; rfl⟩

def arriveBase : Fin 8 → Nat
  | 0 => 750 | 1 => 770 | 2 => 790 | 3 => 810
  | 4 => 750 | 5 => 770 | 6 => 790 | 7 => 810

def arriveTx : Fin 8 → Nat
  | 0 => 674 | 1 => 693 | 2 => 712 | 3 => 731
  | 4 => 751 | 5 => 771 | 6 => 791 | 7 => 811

theorem code_arrive_ops : ∀ b : Fin 8, kernel.code[(Site.arrive b).pc]? =
    some ⟨none, .mbarArrive (arriveBase b) 0 (.reg (arriveTx b)) (.imm 1) true true .cta⟩
  | 0 => Flow.code_mbarArrive_0 | 1 => Flow.code_mbarArrive_1 | 2 => Flow.code_mbarArrive_2
  | 3 => Flow.code_mbarArrive_3 | 4 => Flow.code_mbarArrive_4 | 5 => Flow.code_mbarArrive_5
  | 6 => Flow.code_mbarArrive_6 | 7 => Flow.code_mbarArrive_7

theorem arriveBase_live : ∀ b : Fin 8, arriveBase b ∈ Flow.live (Site.arrive b).pc := by
  intro b
  fin_cases b <;> table_decide

theorem arriveTx_live : ∀ b : Fin 8, arriveTx b ∈ Flow.live (Site.arrive b).pc := by
  intro b
  fin_cases b <;> table_decide

theorem arriveBase_value (L : Launch) (g : Nat) (d : D) (b : Fin 8) :
    valueOf L g d (arriveBase b) = .ptr 32 false (.shared (g / L.block) (2 * ((g / L.block) / 2)))
        (BitVec.ofNat 64 (L.sharedBase + 8 + 8 * (b.val % 4))) := by
  fin_cases b <;> simp only [arriveBase] <;> loader_values

theorem arriveTx_value (L : Launch) (g : Nat) (d : D) (b : Fin 8) :
    valueOf L g d (arriveTx b) = b32 98304 := by
  fin_cases b <;> simp only [arriveTx] <;> loader_values

/-- The arrival at block `b` names slot `b % 4`'s full barrier in the cluster's leader CTA,
expecting 98304 bytes, with arrival count 1. -/
theorem arrive_event {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState} {o :
    Option TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads) (b : Fin 8)
    (hs : d.site = .arrive b) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ rel sc, e = ⟨d.site.pc, .arrive (InputRing.fullLoc L ((g / L.block) / 2) (InputRing.slotOf b))
      98304 1 rel sc⟩ := by
  obtain ⟨s, m, n, q, cp, r, x⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  rw [code_arrive_ops b] at hc
  cases hc
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hcta := cta_lt hpre hg
  have hb := (arriveBase_value L g _ b) ▸
    holds_mem h.2.2.2.2 (Flow.mem_factsFrom (arriveBase_live b))
  have htx := (arriveTx_value L g _ b) ▸ holds_mem h.2.2.2.2 (Flow.mem_factsFrom (arriveTx_live b))
  have hm := mbarClusterLoc_ptr hb hg (by rw [hpre.grid] at hcta ⊢; omega)
    (by simp only [clusterOfCta_eq hpre]; omega) (by omega) (by omega)
  obtain ⟨rel, sc, he, -⟩ := fires_arrive_at (cluster := true) (by simpa using hm)
    (show readBits L g t 32 (.reg (arriveTx b)) = .ok (truncBits 32 (BitVec.ofNat 64 98304)) by
      simp [readBits, readReg, htx, b32, bind, Except.bind, pure, Except.pure])
    (show readBits L g t 32 (.imm 1) = .ok (truncBits 32 (BitVec.ofInt 64 1)) by
      simp [readBits, pure, Except.pure]) hf
  exact ⟨rel, sc, by rw [he]; rfl⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof.Loader
