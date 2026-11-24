-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftBase
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftRegs

@[expose] public section

/-! # The softmax warps' polls and arrivals

A softmax thread polls its stage's credit barrier at a `statsW` site, with the parity of its
successful polls of the barrier plus one (the register `%r3599` or `%r1975` holds the parity of
the statistics poll index), and its stage's S-full barrier at a `sW` site, with the parity of
its successful polls of it (`%r3600`, the score tile index) (`soft_wait`). It arrives, once
without transaction bytes, on the leader's P-ready barriers of its stage (`soft_arrive`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An arrival on the leader CTA's barrier at `off`, through its `mapa` pointer: one arrival
without transaction bytes. -/
theorem ev_arriveLead1 {g : Nat} {t u : TState} {e : Event} {ins : Instr} {pc r c off : Nat}
    (hpre : Pre P L mem0) (hg : g < L.threads)
    (hc : kernel.code[pc]? = some ⟨none, .mbarArrive r 0 (.imm 0) (.reg c) true true .cta none⟩)
    (hr : t.regs r = some (Softmax.leadPtr L g off)) (hcnt : t.regs c = some (b32 1))
    (hoff : off < 1024) (h8 : off % 8 = 0) (hins : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ rel sc, e.kind = .arrive (Softmax.leadLoc L g off) 0 1 rel sc := by
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  have hbase := hpre.sharedRange
  have hal := hpre.sharedAlignment
  unfold sharedBytes at hbase
  have hcta : g / L.block < L.grid := cta_lt hg
  have hgr := hpre.grid
  have hcl := hpre.cluster
  have hm := mbarClusterLoc_ptr (L := L) (g := g) (t := t) (base := r)
    (cta := 2 * (g / L.block / 2)) (a := L.sharedBase + off) hr hg (by omega)
    (by simp only [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hcl]; omega) (by omega)
    (by omega)
  obtain ⟨rel, sc, he, -⟩ := fires_arrive_at (L := L) (g := g) (A := asms) (cluster := true)
    (by simpa using hm) (rfl : readBits L g t 32 (.imm 0) = _) (readBits_b32' hcnt) hf
  exact ⟨rel, sc, by rw [he]; rfl⟩

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **A softmax thread's poll**: of its stage's credit barrier at a `statsW` site, with the
parity of its successful polls of the barrier plus one, or of its stage's S-full barrier at a
`sW` site, with the parity of its successful polls of it. -/
theorem soft_wait {g i pc p : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}
    (hw : warpOf L g < 8) (he : X.get (g, i) = some ⟨pc, .wait m p ok acq sc⟩) :
    ∃ d : Softmax.D, Frame.stateAt (code L) X g i = some (some (.inr (.softmax d))) ∧
      Softmax.Counts L g d ((X.tr g).take i) ∧ Softmax.Inv L g d ∧ d.site.pc = pc ∧
      ((∃ w, d.site = .statsW w ∧ m = Softmax.ownLoc L g (240 + 8 * Softmax.stOf L g) ∧
          p % 2 = (okPolls m ((X.tr g).take i) + 1) % 2) ∨
        (∃ lp, d.site = .sW lp ∧ m = Softmax.ownLoc L g (128 + 8 * Softmax.stOf L g) ∧
          p % 2 = okPolls m ((X.tr g).take i) % 2)) := by
  obtain ⟨d, t, ins, o, hσ, hc, hi, hat, hcode, hf, hev⟩ :=
    soft_state hpre hX ht he hw (fun _ _ h => by cases h) (by simp [Prologue.ProKind])
  have hpc : d.site.pc = pc := (fires_pc hf).symm
  have hst : Softmax.stOf L g < 2 := by have := hi.warp; simp only [Softmax.stOf]; omega
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
  refine ⟨d, hσ, hc, hi, hpc, ?_⟩
  have h4 := hat.2.2.2.2
  have hs := hc.stats
  have hS := hc.score
  have ht0 := hi.tile0
  have htl := hi.tail
  cases hsd : d.site with
  | statsW w =>
    refine .inl ⟨w, rfl, ?_⟩
    rw [hsd] at hcode hf ht0 htl
    rcases Softmax.fin4_cases w with rfl | rfl | rfl | rfl
    · obtain ⟨h1, h2⟩ := Softmax.regs_statsW0 hsd h4
      obtain ⟨ok', acq', sc', hk⟩ := ev_waitPar hpre Flow.code_mbarWait_30 h1 h2 (by omega)
        (by omega) hcode hf
      injection hk with hm hp
      subst hm hp
      refine ⟨rfl, ?_⟩
      rw [hs]
      have := ht0 rfl
      simp [Softmax.statsIdx, Softmax.statsPos, Softmax.Site.inItem, hsd] at this ⊢
      omega
    · obtain ⟨h1, h2⟩ := Softmax.regs_statsW1 hsd h4
      obtain ⟨ok', acq', sc', hk⟩ := ev_waitPar hpre Flow.code_mbarWait_32 h1 h2 (by omega)
        (by omega) hcode hf
      injection hk with hm hp
      subst hm hp
      refine ⟨rfl, ?_⟩
      rw [hs]
      have := ht0 rfl
      simp [Softmax.statsIdx, Softmax.statsPos, Softmax.Site.inItem, Softmax.Site.tile0, hsd]
        at this ⊢
      omega
    · obtain ⟨h1, h2⟩ := Softmax.regs_statsW2 hsd h4
      obtain ⟨ok', acq', sc', hk⟩ := ev_waitPar hpre Flow.code_mbarWait_34 h1 h2 (by omega)
        (by omega) hcode hf
      injection hk with hm hp
      subst hm hp
      refine ⟨rfl, ?_⟩
      rw [hs]
      simp [Softmax.statsIdx, Softmax.statsPos, Softmax.Site.inItem, Softmax.Site.tile0, hsd]
      omega
    · obtain ⟨h1, h2⟩ := Softmax.regs_statsW3 hsd h4
      obtain ⟨ok', acq', sc', hk⟩ := ev_waitPar hpre Flow.code_mbarWait_35 h1 h2 (by omega)
        (by omega) hcode hf
      injection hk with hm hp
      subst hm hp
      refine ⟨rfl, ?_⟩
      rw [hs]
      have := (htl (.inl rfl)).2
      simp [Softmax.statsIdx, Softmax.tailPos, Softmax.Site.inItem, hsd] at this ⊢
      omega
  | sW lp =>
    refine .inr ⟨lp, rfl, ?_⟩
    rw [hsd] at hcode hf ht0
    cases lp
    · obtain ⟨h1, h2⟩ := Softmax.regs_sW0 hsd h4
      obtain ⟨ok', acq', sc', hk⟩ := ev_waitPar hpre Flow.code_mbarWait_31 h1 h2 (by omega)
        (by omega) hcode hf
      injection hk with hm hp
      subst hm hp
      refine ⟨rfl, ?_⟩
      rw [hS]
      have := ht0 rfl
      simp [Softmax.tileIdx, Softmax.sPos, hsd, Softmax.Site.tile0Ld, Softmax.Site.tile0,
        Softmax.Site.inTrip] at this ⊢
    · obtain ⟨h1, h2⟩ := Softmax.regs_sW1 hsd h4
      obtain ⟨ok', acq', sc', hk⟩ := ev_waitPar hpre Flow.code_mbarWait_33 h1 h2 (by omega)
        (by omega) hcode hf
      injection hk with hm hp
      subst hm hp
      refine ⟨rfl, ?_⟩
      rw [hS]
      simp [Softmax.tileIdx, Softmax.sPos, hsd, Softmax.Site.tile0]
      omega
  | _ => all_goals exfalso; simp [Softmax.Ev, hsd] at hev

/-- **A softmax thread's arrival**: one arrival without transaction bytes, at a `pArr` site on
the leader's P-ready barrier of its stage or at a `p2Arr` site on the leader's second P-ready
barrier of its stage. -/
theorem soft_arrive {g i pc tx cnt : Nat} {m : Loc} {rel : Bool} {sc : MbarScope}
    (hw : warpOf L g < 8) (he : X.get (g, i) = some ⟨pc, .arrive m tx cnt rel sc⟩) :
    ∃ d : Softmax.D, Frame.stateAt (code L) X g i = some (some (.inr (.softmax d))) ∧
      Softmax.Counts L g d ((X.tr g).take i) ∧ Softmax.Inv L g d ∧ d.site.pc = pc ∧
      tx = 0 ∧ cnt = 1 ∧
      ((∃ lp, d.site = .pArr lp ∧ m = Softmax.leadLoc L g (144 + 8 * Softmax.stOf L g)) ∨
        (∃ lp, d.site = .p2Arr lp ∧ m = Softmax.leadLoc L g (160 + 8 * Softmax.stOf L g))) := by
  obtain ⟨d, t, ins, o, hσ, hc, hi, hat, hcode, hf, hev⟩ :=
    soft_state hpre hX ht he hw (fun _ _ h => by cases h) (by simp [Prologue.ProKind])
  have hg := Frame.lt_of_get hX he
  have hpc : d.site.pc = pc := (fires_pc hf).symm
  have hst : Softmax.stOf L g < 2 := by have := hi.warp; simp only [Softmax.stOf]; omega
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
  refine ⟨d, hσ, hc, hi, hpc, ?_⟩
  have h4 := hat.2.2.2.2
  have hin {l : Loc} (h : ∃ rel' sc', Kind.arrive m tx cnt rel sc = Kind.arrive l 0 1 rel' sc') :
      m = l ∧ tx = 0 ∧ cnt = 1 := by
    obtain ⟨_, _, h⟩ := h
    injection h with h1 h2 h3
    exact ⟨h1, h2, h3⟩
  cases hsd : d.site with
  | pArr lp =>
    rw [hsd] at hcode hf
    cases lp
    · obtain ⟨r1, r2⟩ := Softmax.regs_pArr0 hsd h4
      obtain ⟨h1, h2, h3⟩ := hin (ev_arriveLead1 hpre hg Flow.code_mbarArrive_10 r1 r2
        (by omega) (by omega) hcode hf)
      exact ⟨h2, h3, .inl ⟨false, rfl, h1⟩⟩
    · obtain ⟨r1, r2⟩ := Softmax.regs_pArr1 hsd h4
      obtain ⟨h1, h2, h3⟩ := hin (ev_arriveLead1 hpre hg Flow.code_mbarArrive_12 r1 r2
        (by omega) (by omega) hcode hf)
      exact ⟨h2, h3, .inl ⟨true, rfl, h1⟩⟩
  | p2Arr lp =>
    rw [hsd] at hcode hf
    cases lp
    · obtain ⟨r1, r2⟩ := Softmax.regs_p2Arr0 hsd h4
      obtain ⟨h1, h2, h3⟩ := hin (ev_arriveLead1 hpre hg Flow.code_mbarArrive_11 r1 r2
        (by omega) (by omega) hcode hf)
      exact ⟨h2, h3, .inr ⟨false, rfl, h1⟩⟩
    · obtain ⟨r1, r2⟩ := Softmax.regs_p2Arr1 hsd h4
      obtain ⟨h1, h2, h3⟩ := hin (ev_arriveLead1 hpre hg Flow.code_mbarArrive_13 r1 r2
        (by omega) (by omega) hcode hf)
      exact ⟨h2, h3, .inr ⟨true, rfl, h1⟩⟩
  | _ => all_goals exfalso; simp [Softmax.Ev, hsd] at hev

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
