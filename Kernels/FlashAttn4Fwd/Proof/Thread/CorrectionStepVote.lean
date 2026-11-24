-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepBase

@[expose] public section

/-! # The vote of a trip (both outcomes)

`vote.sync.ballot.b32 b, α < 1, -1` writes the warp's ballot; `setp.eq.b32 p, b, 0` and
`@p bra` skip the rescale when no lane voted: a zero ballot reaches the O-free arrival on the
leader (`mov.b32 %r2656, 1` between), a nonzero ballot the first rescale load. The thread's own
vote is `α < 1` for the `α` of its state. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The vote of stage 0: the event votes `α < 1`; a zero ballot skips the rescale. -/
theorem step_vote0 {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : D} {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0)
    (hs : d.site = .vote 0) (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    (∃ m b, e = ⟨Flow.vote_0, .vote m (ltOne d.aw) b⟩) ∧ Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_vote_0)
  have hp : readPred L g t (.reg 299) = .ok (ltOne aw) := by
    have hr := holds_lookup h.2.2.2.2 (r := 299) (v := .pred (ltOne aw))
      (by simp only [facts, valueOf, values, chunkValues, loadValues, Site.extra,
        PTX.Flow.lookupLit, Option.getD_some])
    simp [readPred, readReg, hr, bind, Except.bind, pure, Except.pure]
  obtain ⟨m, b, rfl, rfl⟩ := fires_vote hp hf
  refine ⟨⟨m, b, by simp; rfl⟩, ?_⟩
  have h1 := At.set (r := 2734) (v := .bits 32 (BitVec.ofNat 64 b.toNat)) h
    (not_mem_factsFrom (show 2734 ∉ Flow.live Flow.vote_0 ++ [] by table_decide))
  have hiv : ∀ s, s.inTrip = true → Inv L g ⟨s, i, tt, aw, a, o⟩ := fun s hs' =>
    inv_same (d := ⟨.vote 0, i, tt, aw, a, o⟩) s hi (by cases s <;> simp_all [Site.inTrip,
      Site.inItem]) (.inl (by cases s <;> simp_all [Site.inTrip, Site.inItem]))
      (fun _ => rfl) (fun _ => by
        have := hi.alpha
        cases s <;> simp_all [Site.rescale]) (fun hh => by
        rcases hh with rfl | rfl | ⟨st, rfl⟩ <;> simp [Site.inTrip] at hs')
  by_cases hb : b = 0
  · subst hb
    refine step_of_run (d' := ⟨.oFree 0 false, i, tt, aw, a, o⟩) (by simp [next])
      (hiv _ rfl) rfl ⟨3, ?_⟩
    corr_seg h1 hpre
  · have hb1 : b.toNat ≠ 0 := fun h0 => hb (BitVec.eq_of_toNat_eq (by simpa using h0))
    have hb2 : b.toNat < 2 ^ 32 := b.isLt
    have hcmp : PTX.compare .eq .b 32 (truncBits 32 (BitVec.ofNat 64 b.toNat))
        (truncBits 32 (BitVec.ofInt 64 0)) = false := by
      have h64 : b.toNat < 2 ^ 64 := by omega
      simp only [PTX.compare, truncBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64,
        Nat.mod_eq_of_lt hb2]
      simp [hb1]
    obtain ⟨t2, hr2, ht2⟩ : ∃ t2, run kernel asms L g 1
        (PTX.next (setReg t 2734 (.bits 32 (BitVec.ofNat 64 b.toNat)))) = some t2 ∧
        At t2 Flow.bra_3857 (factsX L g Flow.bra_3857 ⟨.rld 0 0, i, tt, aw, a, o⟩
          [(300, .pred false)]) := by
      seg_fp h1 using
        try simp only [valueX, valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit,
          Option.getD_some, Option.getD_none]
        all_goals rw [hcmp]
    obtain ⟨t3, hr3, ht3⟩ := run_bra (K := kernel) (A := asms) (L := L) (g := g)
      (show kernel.code[Flow.bra_3857]? = _ from Flow.code_3857) false ht2
      (holds_mem ht2.2.2.2.2 (List.mem_map.mpr ⟨300, by table_decide, by simp [valueX]⟩))
      asms_localRule_none
    simp only [Bool.false_eq_true, ↓reduceIte] at ht3
    obtain ⟨t4, hr4, ht4⟩ : ∃ t4, run kernel asms L g 0 t3 = some t4 ∧
        At t4 (Site.rld 0 0).pc (facts L g ⟨.rld 0 0, i, tt, aw, a, o⟩) := by
      corr_seg ht3 hpre
    have hn : next L g ⟨.vote 0, i, tt, aw, a, o⟩
        ⟨Flow.vote_0, .vote m (ltOne aw != false) b⟩ =
        some (some ⟨.rld 0 0, i, tt, aw, a, o⟩) := by
      simp only [next]
      split_ifs
      simp_all
    exact step_of_run (d' := ⟨.rld 0 0, i, tt, aw, a, o⟩) hn (hiv _ rfl) rfl
      ⟨_, t4, run_comp (run_comp hr2 hr3) hr4, ht4⟩

/-- The vote of stage 1: the event votes `α < 1`; a zero ballot skips the rescale. -/
theorem step_vote1 {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : D} {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0)
    (hs : d.site = .vote 1) (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    (∃ m b, e = ⟨Flow.vote_1, .vote m (ltOne d.aw) b⟩) ∧ Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_vote_1)
  have hp : readPred L g t (.reg 301) = .ok (ltOne aw) := by
    have hr := holds_lookup h.2.2.2.2 (r := 301) (v := .pred (ltOne aw))
      (by simp only [facts, valueOf, values, chunkValues, loadValues, Site.extra,
        PTX.Flow.lookupLit, Option.getD_some])
    simp [readPred, readReg, hr, bind, Except.bind, pure, Except.pure]
  obtain ⟨m, b, rfl, rfl⟩ := fires_vote hp hf
  refine ⟨⟨m, b, by simp; rfl⟩, ?_⟩
  have h1 := At.set (r := 2992) (v := .bits 32 (BitVec.ofNat 64 b.toNat)) h
    (not_mem_factsFrom (show 2992 ∉ Flow.live Flow.vote_1 ++ [] by table_decide))
  have hiv : ∀ s, s.inTrip = true → Inv L g ⟨s, i, tt, aw, a, o⟩ := fun s hs' =>
    inv_same (d := ⟨.vote 1, i, tt, aw, a, o⟩) s hi (by cases s <;> simp_all [Site.inTrip,
      Site.inItem]) (.inl (by cases s <;> simp_all [Site.inTrip, Site.inItem]))
      (fun _ => rfl) (fun _ => by
        have := hi.alpha
        cases s <;> simp_all [Site.rescale]) (fun hh => by
        rcases hh with rfl | rfl | ⟨st, rfl⟩ <;> simp [Site.inTrip] at hs')
  by_cases hb : b = 0
  · subst hb
    refine step_of_run (d' := ⟨.oFree 1 false, i, tt, aw, a, o⟩) (by simp [next])
      (hiv _ rfl) rfl ⟨3, ?_⟩
    corr_seg h1 hpre
  · have hb1 : b.toNat ≠ 0 := fun h0 => hb (BitVec.eq_of_toNat_eq (by simpa using h0))
    have hb2 : b.toNat < 2 ^ 32 := b.isLt
    have hcmp : PTX.compare .eq .b 32 (truncBits 32 (BitVec.ofNat 64 b.toNat))
        (truncBits 32 (BitVec.ofInt 64 0)) = false := by
      have h64 : b.toNat < 2 ^ 64 := by omega
      simp only [PTX.compare, truncBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64,
        Nat.mod_eq_of_lt hb2]
      simp [hb1]
    obtain ⟨t2, hr2, ht2⟩ : ∃ t2, run kernel asms L g 1
        (PTX.next (setReg t 2992 (.bits 32 (BitVec.ofNat 64 b.toNat)))) = some t2 ∧
        At t2 Flow.bra_4076 (factsX L g Flow.bra_4076 ⟨.rld 1 0, i, tt, aw, a, o⟩
          [(302, .pred false)]) := by
      seg_fp h1 using
        try simp only [valueX, valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit,
          Option.getD_some, Option.getD_none]
        all_goals rw [hcmp]
    obtain ⟨t3, hr3, ht3⟩ := run_bra (K := kernel) (A := asms) (L := L) (g := g)
      (show kernel.code[Flow.bra_4076]? = _ from Flow.code_4076) false ht2
      (holds_mem ht2.2.2.2.2 (List.mem_map.mpr ⟨302, by table_decide, by simp [valueX]⟩))
      asms_localRule_none
    simp only [Bool.false_eq_true, ↓reduceIte] at ht3
    obtain ⟨t4, hr4, ht4⟩ : ∃ t4, run kernel asms L g 0 t3 = some t4 ∧
        At t4 (Site.rld 1 0).pc (facts L g ⟨.rld 1 0, i, tt, aw, a, o⟩) := by
      corr_seg ht3 hpre
    have hn : next L g ⟨.vote 1, i, tt, aw, a, o⟩
        ⟨Flow.vote_1, .vote m (ltOne aw != false) b⟩ =
        some (some ⟨.rld 1 0, i, tt, aw, a, o⟩) := by
      simp only [next]
      split_ifs
      simp_all
    exact step_of_run (d' := ⟨.rld 1 0, i, tt, aw, a, o⟩) hn (hiv _ rfl) rfl
      ⟨_, t4, run_comp (run_comp hr2 hr3) hr4, ht4⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
