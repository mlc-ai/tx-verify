-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EpiGen
public import Lemmas.Flow.TcLdUb

@[expose] public section

/-! # The first steps of the epilogue

The broadcast of the warp index (pc 2603) and the Tensor Memory load (pc 2607). The poll of
`o_final` (pc 2565) is in `EpiPoll`: its successor, after the local code of pcs 2567-2600, may be
the first store site (`num_iters < 1`), whose run is proved with the stores. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {t u : TState} {e : Event} {ins : Instr}

/-- The invariant at another site of the same data, with the same loaded words. -/
theorem inv_site {d : D} (hi : Inv d) (s : Site)
    (hl : LoadedSite s → d.sk = false → d.o.length = 64)
    (hp : s = .shfl ∨ s = .ld ∨ s = .waitLd → d.sk = false)
    (hr : StoreSite s → d.pr.rv = true) (hd : s = .stLse → d.pr.lead = true)
    (hp3 : s = .dealloc → d.pr.p3 = true := by intro h; cases h) :
    Inv { d with site := s } :=
  ⟨hi.ok, hl, hi.sk, hp, hr, hd, hp3, hi.lane⟩

/-! ### The Tensor Memory load -/

/-- The 64 destination registers of the load. -/
def ldRegs : List Nat := (List.range 64).map (1763 + ·)

theorem ldRegs_nodup : ldRegs.Nodup := by decide

theorem ldRegs_length : ldRegs.length = 64 := by decide

/-- The facts at the load's wait: the destinations hold the words, the other registers keep
their values. -/
theorem holds_ld (d : D) (vals : List Value) (hlen : vals.length = 64) (t : TState)
    (hh : Holds t.regs (factsAt 2607 d)) :
    Holds (setRegs t ldRegs vals).regs (factsAt 2608 { d with site := .waitLd, o := vals }) := by
  have hcov : ∀ r ∈ Flow.live 2608, r ∈ ldRegs ∨ (r ∉ ldRegs ∧ r ∈ Flow.live 2607) := by
    decide +kernel
  have hsc : ∀ r ∈ Flow.live 2607, Free r := by decide +kernel
  have hw := holds_setRegs t ldRegs vals (valueOf { d with site := .waitLd, o := vals })
    ldRegs_nodup (by rw [hlen, ldRegs_length]) (fun p hp => by
      have hp' : p < 64 := by simpa [ldRegs_length] using hp
      have : ldRegs.getD p 0 = 1763 + p := by
        simp [ldRegs, List.getD_eq_getElem?_getD, hp']
      rw [this]
      exact valueOf_o _ hp')
  refine Flow.holds_of_pointwise fun r hr => ?_
  rcases hcov r hr with hd | ⟨hd, hl⟩
  · exact holds_mem hw (Flow.mem_factsFrom hd)
  · rw [setRegs_other t ldRegs vals r hd, reg_of hh hl]
    congr 1
    exact (valueOf_free_eq (d := d) (d' := { d with site := .waitLd, o := vals }) rfl rfl
      (hsc r hl)).symm

theorem code_ld : kernel.code[(Site.ld).pc]? =
    some ⟨none, .tcLd ldRegs 1827 (.s16x32bx2 64)⟩ := by
  rw [show (Site.ld).pc = 2607 from rfl, Flow.code_2607]
  rfl

/-- **The Tensor Memory load** of the 64 words: the destinations hold the words the event
returned. -/
theorem step_ld (pr : Prm) (o : List Value) (sk : Bool) (hi : Inv ⟨.ld, pr, o, sk⟩)
    (h : At t (Site.ld).pc (facts ⟨.ld, pr, o, sk⟩))
    (hc : kernel.code[(Site.ld).pc]? = some ins)
    (hf : Fires (Site.ld).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g ⟨.ld, pr, o, sk⟩ e u := by
  obtain rfl := Option.some.inj (hc.symm.trans code_ld)
  obtain ⟨a, vals, hl, rfl, rfl⟩ := fires_tcLd (L := L) (g := g) (A := asms)
    (by intro s hs; cases hs) (h.1 ▸ hf) (by hooks_off)
  have hlen : vals.length = 64 := by rw [hl, ldRegs_length]
  obtain ⟨hpc, hsub, hacc, hfl⟩ := setRegs_skel (PTX.next t) ldRegs vals
  refine .inl (.inr ⟨⟨.waitLd, pr, vals, sk⟩, _, by simp [next, hlen], .refl,
    ⟨by rw [hpc]; simp [PTX.next, h.1, Site.pc], by rw [hsub]; exact h.2.1,
      by rw [hacc]; exact h.2.2.1, by rw [hfl]; exact h.2.2.2.1, ?_⟩, ?_⟩)
  · rw [setRegs_next_regs]
    exact holds_ld ⟨.ld, pr, o, sk⟩ vals hlen t h.2.2.2.2
  · refine ⟨hi.ok, fun _ _ => hlen, fun hsk => ?_, fun _ => hi.pre (Or.inr (Or.inl rfl)),
      fun h => absurd h (by simp [StoreSite]), fun h => absurd h (by simp),
      (fun h => by cases h), hi.lane⟩
    exact absurd ((hi.pre (Or.inr (Or.inl rfl)) : sk = false) ▸ hsk) (by simp)

/-! ### The broadcast -/

/-- `shl.b32 %r1368, %r1367, 21` (pc 2604) of a received word that reads as `m`. -/
theorem seg_shl (d : D) {recv : Value} {m : Nat} (hw : Raw.word32Of recv = some m) :
    Seg kernel asms L g 1 2604 ((1828, recv) :: factsAt 2603 d) 2605
      ((1829, b32 (m * 2097152 % 2 ^ 32)) :: factsAt 2603 d) := by
  refine Raw.seg_int1 (d := 1829) (v := b32 (m * 2097152 % 2 ^ 32)) Flow.code_2604 rfl rfl
    (segFree (by norm_num)) (fun t h => ?_) (fun R hR => ?_)
  · exact Raw.execInt_shl21 (holds_mem h.2.2.2.2 (List.mem_cons_self ..)) hw
  · exact ⟨Function.update_self .., holds_update hR.2 (facts_ne (by table_decide))⟩

/-- `and.b32 %r1369, %r1368, 0x600000` and `add.s32 %r1366, %r1369, %r30` (pcs 2605, 2606): the
address of the load, with the lane bits `m % 4` recorded. -/
theorem seg_lane (d : D) (m : Nat) :
    SegE L g 2605 ((1829, b32 (m * 2097152 % 2 ^ 32)) :: factsAt 2603 d) 2607
      (factsAt 2607 { d with site := .ld, pr := { d.pr with bw := m % 4 } }) :=
  ⟨2, fun t h => by epi_seg h [Prm.taddr, Raw.and_lane]⟩

/-- The lane field of the address `b · 2 ^ 21 + c0` is accepted only for the lane bits 0 and the
warp index. -/
theorem addr_bad {pr : Prm} (hok : pr.Ok) (hw : pr.w = g % L.block / 32) {b : Nat} (hb4 : b < 4)
    (hb : ¬ (b = 0 ∨ b = pr.w)) :
    tcDataAddressOk L g (.s16x32bx2 64) ((b * 2097152 + pr.c0) % M32) = false := by
  have h1 := hok.c0col
  have h2 := hok.w
  have he : (b * 2097152 + pr.c0) % M32 / 2 ^ 16 = 32 * b := by
    unfold M32
    omega
  simp only [tcDataAddressOk, TcShape.splitOk, tmemLaneFieldOk, laneBase, TcShape.lanes, he,
    Bool.and_eq_false_iff, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  right
  omega

/-- **The broadcast of the warp index** follows every received word: where it reads as `m` and
`m % 4` is 0 or the warp index, the address arithmetic follows with the lane bits recorded and the
load is next; a word without bits faults at the shift, and other lane bits give a load whose
lane field leaves the warp's lanes (undefined behaviour): the thread is dead. -/
theorem step_shfl (pr : Prm) (o : List Value) (sk : Bool) (hi : Inv ⟨.shfl, pr, o, sk⟩)
    (hw : pr.w = g % L.block / 32)
    (h : At t (Site.shfl).pc (facts ⟨.shfl, pr, o, sk⟩))
    (hc : kernel.code[(Site.shfl).pc]? = some ins)
    (hf : Fires (Site.shfl).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g ⟨.shfl, pr, o, sk⟩ e u := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_15)
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := none) hf
  have h1 : At (PTX.next (setReg t 1828 recv)) 2604
      ((1828, recv) :: factsAt 2603 ⟨.shfl, pr, o, sk⟩) :=
    At.set (r := 1828) (v := recv) h (facts_ne (by table_decide))
  cases hm : Raw.word32Of recv with
  | none =>
    refine .inr ⟨by simp [next, Raw.laneOk, hm], ?_⟩
    refine Raw.dead_int1 Flow.code_2604 rfl rfl (segFree (by norm_num)) (fun t' h' => ?_) h1
    exact Raw.execInt_shl21_none (holds_mem h'.2.2.2.2 (List.mem_cons_self ..)) hm
  | some m =>
    obtain ⟨t2, hr2, ht2⟩ := (SegE.of_seg (seg_shl (L := L) (g := g) _ hm)).rtg h1
    obtain ⟨t3, hr3, ht3⟩ := (seg_lane (L := L) (g := g) ⟨.shfl, pr, o, sk⟩ m).rtg ht2
    have hm4 : m % 4 < 4 := Nat.mod_lt _ (by decide)
    by_cases hl : m % 4 = 0 ∨ m % 4 = pr.w
    · have hn : next ⟨.shfl, pr, o, sk⟩ ⟨Flow.shfl_15, .shfl .idx av bv cv recv ok⟩ =
          some (some ⟨.ld, { pr with bw := m % 4 }, o, sk⟩) := by
        simp [next, Raw.laneOk, hm, hl]
      refine .inl (.inr ⟨_, t3, hn, hr2.trans hr3, ht3, ?_⟩)
      exact ⟨hi.ok.bw _, fun h => absurd h (by simp [LoadedSite]), hi.sk,
        fun _ => hi.pre (Or.inl rfl), fun h => absurd h (by simp [StoreSite]),
        fun h => absurd h (by simp), (fun h => by cases h), hl⟩
    · refine .inr ⟨by simp [next, Raw.laneOk, hm, hl], ?_⟩
      have hr : t3.regs 1827 = some (b32 ((m % 4 * 2097152 + pr.c0) % M32)) := by
        have := holds_mem ht3.2.2.2.2 (Flow.mem_factsFrom
          (val := valueOf ⟨.ld, { pr with bw := m % 4 }, o, sk⟩)
          (show 1827 ∈ Flow.live 2607 by table_decide))
        simpa [valueOf, D.table, D.scalars, lookupLit, Prm.taddr] using this
      obtain ⟨t4, f, h4, hf4⟩ := tcLd_dead (K := kernel) (A := asms) (L := L) (g := g)
        (hc := by rw [ht3.1]; exact code_ld) ht3.2.2.2.1 hr (Nat.mod_lt _ (by decide))
        (addr_bad hi.ok hw hm4 hl) (by hooks_off)
      exact ⟨t4, f, (hr2.trans hr3).trans h4, hf4⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
