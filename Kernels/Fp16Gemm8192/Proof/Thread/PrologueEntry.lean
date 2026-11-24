-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.PrologueEvents
public import Kernels.Fp16Gemm8192.Proof.Thread.Claims

@[expose] public section

/-! # Warp 11's election and the loader's entry

The elected lane computes the tile its CTA starts with from the CTA index, converts the
leader CTA's first full barrier to a cluster shared address and enters the K loop; the other
lanes go to the common exit. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Prologue
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000


set_option maxHeartbeats 20000000 in
/-- Warp 11's election: the leader enters the loader's K loop with its CTA's tile; the other
lanes go to the common exit. -/
theorem step_roleElect {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads) (hs : d.site = .roleElect)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s, w⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_1)
  obtain ⟨mk, inst, leader, rfl, rfl⟩ := fires_elect hf
  simp only [Option.elim]
  by_cases hw : w = 11
  · subst hw
    right
    have h0 : At t Site.roleElect.pc (facts L g ⟨.roleElect, 11⟩) := h
    have h1 := At.set (r := 977) (v := .pred (laneOf L g == leader)) h0
      (not_mem_factsFrom (live := Flow.live Site.roleElect.pc) (by table_decide))
    have hcta := cta_lt hpre hg
    have hc1024 : g / L.block < 1024 := hpre.grid ▸ hcta
    cases hb : (laneOf L g == leader)
    · rw [hb] at h1
      have hne : laneOf L g ≠ leader := by simpa using hb
      obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 4
          (PTX.next (setReg t 977 (.pred false))) = some t' ∧
          At t' loaderIdle.site.pc (Loader.facts L g loaderIdle) := by
        loader_seg h1 hpre
      refine ⟨.inr (.loader loaderIdle), t', ?_, run_rtg hr, ht', ?_⟩
      · simp [next, hne]
      · exact ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide⟩,
          fun b hb => by simp [loaderIdle] at hb⟩
    · rw [hb] at h1
      have heq : laneOf L g = leader := by simpa using hb
      have hbase := hpre.sharedRange
      unfold sharedBytes at hbase
      obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel Prod L g 6
          (PTX.next (setReg t 977 (.pred true))) = some t1 ∧
          At t1 (Site.roleElect.pc + 7) (factsAt L g (Site.roleElect.pc + 7) ⟨.roleElect, 11⟩) := by
        pro_seg h1 hpre [claimN_of hc1024, sregValue,
          truncBits_ofNat (show g / L.block < 2 ^ 32 by omega) (by decide)]
      have h33 : t1.regs 926 =
          some (.ptr 64 true (.shared (g / L.block) (2 *
            ((g / L.block) / 2))) (BitVec.ofNat 64 (L.sharedBase + 8))) :=
        reg_val ht1 (by table_decide) (by pro_values)
      have hoff : (BitVec.ofNat 64 (L.sharedBase + 8)).toNat = L.sharedBase + 8 := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have hl := readSharedAddress_ptr (gen := true) (cl := true) h33 (.inr rfl) hg
        (by rw [hpre.grid] at hcta ⊢; omega)
        (by simp only [clusterOfCta_eq hpre]; omega) (.inl rfl) (.inl rfl) (by rw [hoff]; omega)
      rw [hoff] at hl
      obtain ⟨t2, hr2, ht2⟩ : ∃ t2, run kernel Prod L g 1 t1 = some t2 ∧
          At t2 (Site.roleElect.pc + 8)
            ((925, .ptr 64 false (.shared (g / L.block) (2 *
              ((g / L.block) / 2))) (BitVec.ofNat 64 (L.sharedBase + 8))) ::
              factsAt L g (Site.roleElect.pc + 7) ⟨.roleElect, 11⟩) :=
        ⟨_, run_local Flow.code_103 rfl ht1 (exec_cvtaShared hl
          (hL := prod_localRule_none (by simp [Assumption.FloatForm.ofOp]) L g t1)),
          At.set ht1 (not_mem_factsFrom (by table_decide))⟩
      have hm := (Loader.claim_lt (g / L.block)).1
      rw [claimM_of hc1024] at hm
      obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 15 t2 = some t3 ∧
          At t3 (loaderStart L g).site.pc (Loader.facts L g (loaderStart L g)) := by
        loader_seg ht2 hpre [loaderStart, valueOf, values, List.lookup_cons, Nat.reduceBEq,
          Option.getD_some, claimM_of hc1024, claimN_of hc1024, start_bits _ hc1024,
          Loader.row_bits _ hm]
      refine ⟨.inr (.loader (loaderStart L g)), t3, ?_, run_rtg (run_comp (run_comp hr1 hr2) hr3),
        ht3, ?_⟩
      · simp [next, heq]
      · have hmn := Loader.claim_lt (g / L.block)
        exact ⟨⟨hmn.1, hmn.2, by show 0 < 128; omega, by show 0 % 8 = 0; rfl,
          by show 0 < 2; omega, by show g / L.block < 2 ^ 32; omega⟩,
          fun b hb => by simp [loaderStart] at hb⟩
  · left
    simp [next, hw]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Prologue
