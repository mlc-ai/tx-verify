-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Data.QueryGate
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.CopyElection
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Election

@[expose] public section

/-! # The election of the last copy issue: the data step

A thread that lost the election, or that is not in the first half of the warp group, skips the
last issue: it goes on to the next block or to the query part. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

noncomputable section

theorem elect3_fetch (b : Fin 3) : ∃ r p, kernel.code[(Site.pel b 3).pc]? =
    some ⟨none, .warp ⟨.elect, none, [some r, some p], [], some (.imm (-1))⟩⟩ ∧
    r ∉ ctlLive (Site.pel b 3).pc ∧ p ∉ ctlLive (Site.pel b 3).pc ∧ p = copyVote b 3 ∧
    (∀ τ ∈ tags (.pel b 3), τ.reg ≠ r ∧ τ.reg ≠ p) ∧
    (ctlLive (Site.pel b 3).pc).all (fun k => !voteReg k) = true := by
  fin_cases b
  · exact ⟨700, 62, Flow.code_228, by decide +kernel⟩
  · exact ⟨722, 71, Flow.code_270, by decide +kernel⟩
  · exact ⟨744, 80, Flow.code_312, by decide +kernel⟩

theorem pel3_nb : ∀ b : Fin 3, ¬ Bare (.pel b 3) ∧ Tag.scale ∈ tags (.pel b 3) ∧
    qside (.pel b 3) = true ∧ isQ (.pel b 3) = false ∧ Site.ptc b 3 ∈ succs (.pel b 3) ∧
    (Site.pel b 3).pc + 1 ≤ 316 ∧ 27 ≤ (Site.pel b 3).pc + 1 := by decide +kernel

theorem pel3_step {Q L g w m} (hp : Pre Q L m) (d : D) (b : Fin 3) (hs : d.c.site = .pel b 3) :
    DataStep (code Q L g w) (dF Q L g) d := by
  obtain ⟨r, pv, hcode, hr, hpf, hpe, htag, hkeys⟩ := elect3_fetch b
  obtain ⟨hnb, hsc, hq, hnq, hptc, hpp1, hpp2⟩ := pel3_nb b
  rw [← hs] at hnb hsc hq hnq hptc
  have hc : kernel.code[(code Q L g w).pc d]? =
      some ⟨none, .warp ⟨.elect, none, [some r, some pv], [], some (.imm (-1))⟩⟩ := by
    show kernel.code[d.c.site.pc]? = _
    rw [hs]; exact hcode
  apply DataStep.elect (C' := code Q L g w) (r := r) (p := pv) hc
  intro hi mk inst ld d' t hn' hat'
  obtain ⟨hp0, hs0, ha0, hf0, hr0⟩ := hat'
  have hF' : Holds (PTX.next (setReg (setReg t r (.bits 32 (BitVec.ofNat 64 ld))) pv
      (.pred (laneOf L g == ld)))).regs ((pv, Value.pred (laneOf L g == ld)) ::
      ((checkedCode Q L g w).facts d.c ++ dF Q L g d)) :=
    ⟨by simp [PTX.next, setReg], holds_update_update hr0
      (fresh_facts (by rw [hs]; exact hr) fun τ hτ => by rw [hs] at hτ; exact (htag τ hτ).1)
      (fresh_facts (by rw [hs]; exact hpf) fun τ hτ => by rw [hs] at hτ; exact (htag τ hτ).2)⟩
  obtain ⟨c, hnc, rfl⟩ := succ_split hn'
  simp only [Control.next, hs, Option.some.injEq] at hnc
  have hat : At (PTX.next (setReg (setReg t r (.bits 32 (BitVec.ofNat 64 ld))) pv
      (.pred (laneOf L g == ld)))) ((Site.pel b 3).pc + 1) ((pv, Value.pred (laneOf L g == ld)) ::
      ((checkedCode Q L g w).facts d.c ++ dF Q L g d)) :=
    ⟨by show t.pc + 1 = _; rw [hp0]; show d.c.site.pc + 1 = _; rw [hs],
      hs0.trans (by show d.c.site.sub = 0; rw [hs]; rfl), ha0.trans rfl, hf0, hF'⟩
  suffices hR : Reach kernel Assumptions.all L g ((Site.pel b 3).pc + 1)
      ((pv, Value.pred (laneOf L g == ld)) :: ((checkedCode Q L g w).facts d.c ++ dF Q L g d))
      (dF Q L g ⟨c, record d ⟨(code Q L g w).pc d, .elect mk inst ld⟩⟩) from hR _ hat
  have hrec : ∀ e, record d e = d.v := fun e => record_keep (fun b' h' e' => by
    rw [hs] at e'; cases e') (fun j e' => by rw [hs] at e'; cases e')
  by_cases hw : (decide (g % L.block % 128 < 64) && laneOf L g == ld) = true
  · have hsite : c.site = .ptc b 3 := by rw [← hnc]; simp only [hw, ↓reduceIte]
    have hd' : isQ c.site = false := by rw [hsite]; rfl
    refine reach_carry (d := d) (d' := ⟨c, _⟩) (fun τ hτ => ?_) ?_
      (by rw [hs]; omega) hpp2 (by omega)
    · exact qcarry _ hq hnq _ (by show c.site ∈ _; rw [hsite]; exact hptc) hd' τ hτ
    · exact fun x hx => List.mem_cons_of_mem _ (List.mem_append_right _
        (carry_sub_q hq hnq hnb hn' hd' x hx))
  · have hsite : c.site = afterCopy d.c (g % L.block) (preloadN Q L g d.c) b 3 := by
      rw [← hnc]; simp only [hw]; rfl
    rcases afterCopy3 d.c (g % L.block) (preloadN Q L g d.c) b with ⟨b', hb', hmem⟩ | ⟨hq', h0, h1⟩
    · have hsite' : c.site = .pb b' 0 := hsite.trans hb'
      have hd' : isQ c.site = false := by rw [hsite']; rfl
      refine reach_carry (d := d) (d' := ⟨c, _⟩) (fun τ hτ => ?_) ?_
        (by rw [hs]; omega) hpp2 (by omega)
      · exact qcarry _ hq hnq _ (by
          rw [hs]; show c.site ∈ _; rw [hsite']; exact List.mem_cons_of_mem _ hmem) hd' τ hτ
      · exact fun x hx => List.mem_cons_of_mem _ (List.mem_append_right _
          (carry_sub_q hq hnq hnb hn' hd' x hx))
    · have hscale : (525, scaleVal L) ∈ dF Q L g d := scale_dF d hsc
      have hno : (decide (g % L.block % 128 < 64) &&
          ({d.c with elected := laneOf L g == ld} : Control.D).elected) = false := by
        simpa using hw
      have hkeys' : (ctlLive (pelPc b 3)).all (fun k => !voteReg k) = true := hkeys
      refine entry_reach (w := w) hp {d.c with elected := laneOf L g == ld} ⟨c, _⟩
        (p := (Site.pel b 3).pc + 1)
        (SegU.sub_start (elect_lose_316 (Q := Q) (L := L) (g := g) (w := w)
          {d.c with elected := laneOf L g == ld} b hno h0 h1) ?_)
        (by show c.site = _; rw [hsite]; exact hq') (fun n => by rw [← hnc]; rfl)
        (List.mem_cons_of_mem _ (List.mem_append_right _ hscale)) hpp2 hpp1
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hpe]; exact List.mem_cons_self ..
      · refine List.mem_cons_of_mem _ (List.mem_append_left _ ?_)
        rw [← elect_facts (Q := Q) (L := L) (g := g) (w := w) d.c (pelPc b 3)
          (laneOf L g == ld) hkeys'] at hx
        show x ∈ Control.facts Q L g w d.c d.c.site.pc
        rw [hs]; exact hx

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
