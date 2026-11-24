-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Mma
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Objects
public import Lemmas.Flow.Events
public import Kernels.Fp16Gemm8192.Proof.Thread.Cluster
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # The MMA warps' input-ring events

At slot `s` of a trip the MMA thread polls slot `s`'s full barrier in its own CTA (the
cluster's leader) with the trip's full parity, and after its four MMAs commits to slot `s`'s
empty barriers in both CTAs of the cluster (mask 3). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000


def fullBase : Fin 4 → Nat
  | 0 => 859 | 1 => 865 | 2 => 867 | 3 => 869

def fullPred : Fin 4 → Nat
  | 0 => 1006 | 1 => 1011 | 2 => 1016 | 3 => 1021

theorem code_full_ops : ∀ s : Fin 4, kernel.code[(Site.full s).pc]? =
    some ⟨none, .mbarWait (fullPred s) (fullBase s) 0 (.reg 885) true .cta⟩
  | 0 => Flow.code_mbarWait_17 | 1 => Flow.code_mbarWait_18 | 2 => Flow.code_mbarWait_19
  | 3 => Flow.code_mbarWait_20

theorem fullBase_live : ∀ s : Fin 4, fullBase s ∈ Flow.live (Site.full s).pc := by
  intro s
  fin_cases s <;> table_decide

theorem fullPar_live : ∀ s : Fin 4, 885 ∈ Flow.live (Site.full s).pc := by
  intro s
  fin_cases s <;> table_decide

theorem fullBase_value (L : Launch) (g : Nat) (d : D) (s : Fin 4) :
    valueOf L g d (fullBase s) = b32 (L.sharedBase + 8 + 8 * s.val) := by
  fin_cases s <;> simp only [fullBase] <;> mma_values

/-- The poll at slot `s` names slot `s`'s full barrier in the thread's CTA and the trip's full
parity. -/
theorem full_event {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}
    {o : Option TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (s : Fin 4) (hs : d.site = .full s)
    (hi : Inv d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ ok acq sc, e = ⟨d.site.pc, .wait ⟨.shared, g / L.block, L.sharedBase + 8 + 8 * s.val⟩
      d.fp ok acq sc⟩ := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  rw [code_full_ops s] at hc
  cases hc
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hfp : fp < 2 := hi.fp
  have hb := (fullBase_value L g _ s) ▸ holds_mem h.2.2.2.2 (Flow.mem_factsFrom (fullBase_live s))
  have hp : t.regs 885 = some (b32 fp) :=
    (show valueOf L g ⟨.full s, w, q, fp, ap, cp, r, x⟩ 885 = b32 fp by mma_values) ▸
      holds_mem h.2.2.2.2 (Flow.mem_factsFrom (fullPar_live s))
  have hm := mbarLoc_b32 (L := L) (g := g) hb (by omega) (by omega)
  obtain ⟨ok, acq, sc, he, -⟩ := fires_wait_at hm
    (show readBits L g t 32 (.reg 885) = .ok (truncBits 32 (BitVec.ofNat 64 fp)) by
      simp [readBits, readReg, hp, b32, bind, Except.bind, pure, Except.pure]) hf
  have hpar : (truncBits 32 (BitVec.ofNat 64 fp)).toNat % 2 = fp := by
    rcases (by omega : fp = 0 ∨ fp = 1) with rfl | rfl <;> decide
  exact ⟨ok, acq, sc, by rw [he, hpar]⟩

def commitBase : Fin 4 → Nat
  | 0 => 864 | 1 => 866 | 2 => 868 | 3 => 870

theorem code_commit_ops : ∀ s : Fin 4, kernel.code[(Site.commit s).pc]? =
    some ⟨none, .tcCommit .two (commitBase s) 0 (some (.reg 44))⟩
  | 0 => Flow.code_tcCommit_0 | 1 => Flow.code_tcCommit_1 | 2 => Flow.code_tcCommit_2
  | 3 => Flow.code_tcCommit_3

theorem commitBase_live : ∀ s : Fin 4, commitBase s ∈ Flow.live (Site.commit s).pc := by
  intro s
  fin_cases s <;> table_decide

theorem commitMask_live : ∀ s : Fin 4, 44 ∈ Flow.live (Site.commit s).pc := by
  intro s
  fin_cases s <;> table_decide

theorem commitBase_value (L : Launch) (g : Nat) (d : D) (s : Fin 4) :
    valueOf L g d (commitBase s) = b32 (L.sharedBase + 40 + 8 * s.val) := by
  fin_cases s <;> simp only [commitBase] <;> mma_values

/-- The commit specification of slot `s`: the thread's copy of the slot's empty barrier,
mask 3, over the thread's cluster. -/
def commitSpec (L : Launch) (g : Nat) (s : Fin 4) : TcCommit.Spec :=
  ⟨.two, ⟨.shared, g / L.block, L.sharedBase + 40 + 8 * s.val⟩, 3, (g / L.block) / 2 * 2, 2⟩

/-- The commit at slot `s` resolves to `commitSpec`. -/
theorem commit_event {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}
    {o : Option TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads) (s : Fin 4)
    (hs : d.site = .commit s) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    e = ⟨d.site.pc, .tc (.commit (commitSpec L g s))⟩ := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  rw [code_commit_ops s] at hc
  cases hc
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hcta := cta_lt hpre hg
  have hb := (commitBase_value L g _ s) ▸
    holds_mem h.2.2.2.2 (Flow.mem_factsFrom (commitBase_live s))
  have hk : t.regs 44 = some (.bits 16 (BitVec.ofNat 64 3)) :=
    (show valueOf L g ⟨.commit s, w, q, fp, ap, cp, r, x⟩ 44 = .bits 16 (BitVec.ofNat 64 3)
      by mma_values) ▸ holds_mem h.2.2.2.2 (Flow.mem_factsFrom (commitMask_live s))
  have hm := mbarClusterLoc_b32 (L := L) (g := g) hb (by omega) (by omega)
  refine (fires_tcCommit_at hg hm
    (show readBits L g t 16 (.reg 44) = .ok (truncBits 16 (BitVec.ofNat 64 3)) by
      simp [readBits, readReg, hk, bind, Except.bind, pure, Except.pure]) ?_ hf).1
  have hv := hpre.oneDimLaunch
  simp [TcCommit.resolve, commitSpec, clusterOfCta_eq hpre, clusterStart_eq hpre,
    clusterSizeOf_eq hpre, Launch.oneDimLaunch_clusterGridValid hv, hcta, truncBits]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Mma
