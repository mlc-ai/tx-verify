-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaCountsSite
public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaFullCommitElect
public import Lemmas.Flow.EventCont

@[expose] public section

/-! # `Counts` along the MMA warp's run

`counts_init`: the invariant holds at the role's first state after a prologue without polls,
arrivals, commits or MMAs. `counts_step`: a step of the site machine keeps it (the `hs` premise
of `Code.run_inv`): each count moves by the site's event (`MmaCountsEv`) as its formula moves
along the step (`cnt_next`); the election conjuncts follow the election's outcome, and a step
into a site of the elected lane from another site is an election that returned the lane, with
the full member mask (`elect_lead_event`). The start and end conjuncts follow the site events
of `MmaCountsSite` and the site checks `check_start`, `check_done`; the carried address changes
only at the read-back (`next_base`, `next_ldBase`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section


variable {L : Launch} {g : Nat} {d d' : D} {e : Event} {pre : List Event}

/-- An election site continues only after an election. -/
theorem elect_of_next (hs : d.site.isElect = true) (hn : next L g d e = some (some d')) :
    ∃ mk inst ld, e.kind = .elect mk inst ld := by
  obtain ⟨site, i, t, base, pro⟩ := d
  cases site <;> simp only [Site.isElect, Bool.false_eq_true] at hs <;> simp only [next] at hn <;>
    split at hn <;> first | exact ⟨_, _, _, ‹_›⟩ | cases hn

theorem outcome_elect {mk inst ld : Nat} (h : e.kind = .elect mk inst ld) :
    outcome L g e = decide (laneOf L g = ld) := by
  simp [outcome, waitOk, electLead, h]

/-- The elected lane's step is one `leadValid` follows. -/
theorem lead_valid (hJ : ∀ k, d.site ≠ .p2Wait k false) (hL : ElectLead L g (pre ++ [e]))
    (hn : next L g d e = some (some d')) : leadValid d.site (outcome L g e) = true := by
  cases hs : d.site.isElect
  · obtain ⟨site, i, t, base, pro⟩ := d
    cases site
    case p2Wait k ld =>
      cases ld
      · exact absurd rfl (hJ k)
      · rfl
    all_goals simp_all [Site.isElect, leadValid]
  · obtain ⟨mk, inst, ld, h⟩ := elect_of_next hs hn
    have hl := ((electLead_snoc_elect h).mp hL).2
    obtain ⟨site, i, t, base, pro⟩ := d
    cases site <;> simp only [Site.isElect, Bool.false_eq_true] at hs <;>
      simp [leadValid, outcome_elect h, hl]

/-- The other lanes' elections return another lane. -/
theorem nonLead_outcome (hN : ElectNonLead L g (pre ++ [e]))
    (hn : next L g d e = some (some d')) : (d.site.isElect && outcome L g e) = false := by
  cases hs : d.site.isElect
  · rfl
  · obtain ⟨mk, inst, ld, h⟩ := elect_of_next hs hn
    have hl := ((electNonLead_snoc_elect h).mp hN).2
    simp [outcome_elect h, Ne.symm hl]

/-- A site that is no elected lane's commits nothing and fires no MMA. -/
theorem quiet_of_notLead (hev : Ev L g d e) (h : d.site.lead = false) :
    (∀ m, commitsTo m e = false) ∧ isMma e = false := by
  obtain ⟨site, i, t, base, pro⟩ := d
  refine ⟨fun m => commitsTo_none hev ?_ m, isMma_ev hev ?_⟩ <;>
    cases site <;> simp_all [Site.lead, commitBar, Site.isMma]

/-- The odd CTA's sites commit nothing and fire no MMA. -/
theorem quiet_of_notItem (hev : Ev L g d e) (h : ¬ ItemSite d.site) :
    (∀ m, commitsTo m e = false) ∧ isMma e = false := by
  obtain ⟨site, i, t, base, pro⟩ := d
  refine ⟨fun m => commitsTo_none hev ?_ m, isMma_ev hev ?_⟩ <;>
    cases site <;> simp_all [ItemSite, commitBar, Site.isMma]

theorem countP_snoc {p : Event → Bool} (es : List Event) (e : Event) :
    (es ++ [e]).countP p = es.countP p + if p e then 1 else 0 := by
  simp [List.countP_append]

theorem slots_step (N : Nat) (b : Bool) (s : Fin 6) :
    slots N s + (if (b && decide (N % 6 = s.val)) = true then 1 else 0) =
      slots (N + if b = true then 1 else 0) s := by
  cases b <;> simp [slots_succ]

/-- The carried address changes only at the read-back. -/
theorem next_base (hs : d.site ≠ .ldBase) (hn : next L g d e = some (some d')) :
    d'.base = d.base := by
  obtain ⟨site, i, t, base, pro⟩ := d
  cases site <;> simp only [next] at hn
  case ldBase => exact absurd rfl hs
  case commit c =>
    obtain rfl := Option.some.inj (Option.some.inj hn)
    fin_cases c <;> simp [afterCommit] <;> split_ifs <;> rfl
  case elC c =>
    split at hn
    · split_ifs at hn
      · obtain rfl := Option.some.inj (Option.some.inj hn)
        rfl
      · obtain rfl := Option.some.inj (Option.some.inj hn)
        fin_cases c <;> simp [afterCommit] <;> split_ifs <;> rfl
    · cases hn
  all_goals repeat' split at hn
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try subst hn)
  all_goals (try rfl)
  all_goals (try simp [start]; split_ifs <;> rfl)

/-- At the read-back the carried address is the value its bytes rebuild. -/
theorem next_ldBase (hs : d.site = .ldBase) (hn : next L g d e = some (some d')) :
    ∃ a bs, e.kind = .rd a bs ∧ rebuild 3 bs = .ok d'.base := by
  obtain ⟨site, i, t, base, pro⟩ := d
  simp only at hs
  subst hs
  simp only [next] at hn
  split at hn
  · rename_i a bs hk
    split at hn
    · rename_i v hv
      obtain rfl := Option.some.inj (Option.some.inj hn)
      exact ⟨a, bs, hk, hv⟩
    · cases hn
  · cases hn

/-- One step of an MMA run keeps the run invariant. -/
theorem counts_step {P : Params} {mem0 : Mem0} {t : TState} {ins : Instr} {u : TState}
    (hpre : Pre P L mem0) (hg : g < L.threads) (hJ : Counts L g d pre)
    (hat : t.pc = d.site.pc ∧ t.sub = d.site.sub ∧ t.acc = [] ∧ t.fault = none ∧
      Holds t.regs (facts L g d))
    (hi : Inv L g d) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u))
    (hn : next L g d e = some (some d')) : Counts L g d' (pre ++ [e]) := by
  have hev := site_event hpre hg hat.2.2.2.2 hc hf
  have hP := hJ.pre
  refine
    { pre := fun h' => ?_
      qFull := fun k => ?_
      kvFull := fun s => ?_
      pReady := fun k => ?_
      pReady2 := fun k => ?_
      dealloc := ?_
      handoff := ?_
      sFull := fun hL k => ?_
      kvEmpty := fun hL s => ?_
      qEmpty := fun hL k => ?_
      oFull := fun hL k => ?_
      mmas := fun hL => ?_
      leadSite := fun hL k h' => ?_
      nonLead := fun hN => ?_
      odd := fun hr => ?_
      elected := fun h' => ?_
      tmem := ?_
      bar2 := ?_
      bar2Sync := fun x hx hb => ?_
      allocWrite := fun h' => ?_
      wrote := fun hl h' => ?_
      baseRead := fun h' => ?_
      done := fun h' hr => ?_
      commits := fun hL => ?_
      commitElect := fun c h' => ?_
      elects := ?_
      pollsAt := fun s0 hs0 => ?_ }
  · obtain ⟨hs, hit⟩ := next_eq hn
    have h := all_of check_pre d.site (outcome L g e) (cond L g d)
    rw [← hs] at h
    simp only [h', bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.2] at hit
    simp only [Upd.apply, Prod.mk.injEq] at hit
    rw [hit.1]
    exact hP h.1
  · rw [okPolls_snoc, hJ.qFull k, okPoll_q hev, cnt_next (check_q k) hi hP hn rfl]
  · rw [okPolls_snoc, hJ.kvFull s, okPoll_kv hev, cnt_next check_kv hi hP hn rfl]
    exact slots_step _ _ s
  · rw [okPolls_snoc, hJ.pReady k, okPoll_p hev, cnt_next (check_p k) hi hP hn rfl]
  · rw [okPolls_snoc, hJ.pReady2 k, okPoll_p2 hev, cnt_next (check_p2 k) hi hP hn rfl]
  · have h := cnt_next (L := L) check_dealloc hi hP hn rfl
    simp only [cnt, Nat.zero_mul, Nat.zero_add, Nat.add_zero] at h
    rw [okPolls_snoc, hJ.dealloc, okPoll_dealloc hev, h]
  · have h := cnt_next (L := L) check_handoff hi hP hn rfl
    simp only [cnt, Nat.zero_mul, Nat.zero_add, Nat.add_zero] at h
    rw [arrivals_snoc, hJ.handoff, arrivesOn_handoff hev, h]
  · have hv := lead_valid (hJ.leadSite hL.of_snoc) hL hn
    rw [countP_snoc, hJ.sFull hL.of_snoc k,
      commitsTo_class hev k.val _ fun c => (cBar_class L d c).1 k,
      cnt_next (check_s k) hi hP hn hv]
  · have hv := lead_valid (hJ.leadSite hL.of_snoc) hL hn
    rw [countP_snoc, hJ.kvEmpty hL.of_snoc s, commitsTo_kv hev, cnt_next check_rel hi hP hn hv]
    exact slots_step _ _ s
  · have hv := lead_valid (hJ.leadSite hL.of_snoc) hL hn
    rw [countP_snoc, hJ.qEmpty hL.of_snoc k,
      commitsTo_class hev (3 + k.val) _ fun c => (cBar_class L d c).2.1 k,
      cnt_next (check_qe k) hi hP hn hv]
  · have hv := lead_valid (hJ.leadSite hL.of_snoc) hL hn
    rw [countP_snoc, hJ.oFull hL.of_snoc k,
      commitsTo_class hev (5 + k.val) _ fun c => (cBar_class L d c).2.2 k,
      cnt_next (check_of k) hi hP hn hv]
  · have hv := lead_valid (hJ.leadSite hL.of_snoc) hL hn
    rw [countP_snoc, hJ.mmas hL.of_snoc, isMma_eq hev, cnt_next check_mma hi hP hn hv]
  · have hv := lead_valid (hJ.leadSite hL.of_snoc) hL hn
    obtain ⟨hs, -⟩ := next_eq hn
    have h := all_of check_lead d.site (outcome L g e) (cond L g d)
    rw [← hs, h', hv] at h
    simp [Site.p2Other] at h
  · obtain ⟨hl, hc0, hm0⟩ := hJ.nonLead hN.of_snoc
    obtain ⟨hcq, hmq⟩ := quiet_of_notLead hev hl
    obtain ⟨hs, -⟩ := next_eq hn
    have h := all_of check_nonLead d.site (outcome L g e) (cond L g d)
    rw [← hs, hl, nonLead_outcome hN hn] at h
    simp only [Bool.false_or, Bool.not_eq_true'] at h
    refine ⟨h, fun m => ?_, ?_⟩
    · rw [countP_snoc, hc0 m, hcq m]
      rfl
    · rw [countP_snoc, hm0, hmq]
      rfl
  · obtain ⟨hc0, hm0⟩ := hJ.odd hr
    obtain ⟨hcq, hmq⟩ := quiet_of_notItem hev fun h => hr (hi.i h).2
    refine ⟨fun m => ?_, ?_⟩
    · rw [countP_snoc, hc0 m, hcq m]
      rfl
    · rw [countP_snoc, hm0, hmq]
      rfl
  · by_cases hl : d.site.lead = true
    · obtain ⟨e', hm, inst, hk⟩ := hJ.elected hl
      exact ⟨e', List.mem_append_left _ hm, inst, hk⟩
    · obtain ⟨hs, -⟩ := next_eq hn
      have h := all_of check_nonLead d.site (outcome L g e) (cond L g d)
      rw [← hs, h'] at h
      simp only [hl, Bool.false_or, Bool.not_true, Bool.or_false, Bool.and_eq_true] at h
      obtain ⟨inst, hk⟩ := elect_lead_event h.1 hc hf h.2
      exact ⟨e, List.mem_append_right _ (List.mem_singleton_self e), inst, hk⟩
  · have h := cnt_next (L := L) check_tmem hi hP hn rfl
    rw [cnt_zero, cnt_zero] at h
    have hJt := hJ.tmem
    unfold Tmem.Pair.tmemOps at hJt ⊢
    rw [countP_snoc, hJt, tmemOp_site hpre hat.2.1 hat.2.2.2.2 hc hf, h]
  · have h := cnt_next (L := L) check_bar2 hi hP hn rfl
    rw [cnt_zero, cnt_zero] at h
    rw [countP_snoc, hJ.bar2, (bar2_site hpre hc hf).1, h]
  · rcases List.mem_append.mp hx with hx | hx
    · exact hJ.bar2Sync x hx hb
    · rw [List.mem_singleton.mp hx] at hb ⊢
      exact (bar2_site hpre hc hf).2 hb
  · obtain ⟨hs, -⟩ := next_eq hn
    have h := all_of check_start d.site (outcome L g e) (cond L g d)
    rw [← hs, h'] at h
    simp only [decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨hda, hy⟩ := h.1.1
    have hl : laneOf L g = 0 := by simpa [cond, hda] using hy
    refine ⟨hl, e, by simp, alloc_site hpre hda ?_ hat.2.2.2.2 hc hf⟩
    rw [hat.2.1, hda]
    rfl
  · obtain ⟨hs, -⟩ := next_eq hn
    have h := all_of check_start d.site (outcome L g e) (cond L g d)
    rw [← hs] at h
    simp only [h', decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at h
    rcases h.1.2 with (h3 | ha) | ⟨ha, hy⟩
    · obtain ⟨x, hx, hk⟩ := hJ.wrote hl h3
      exact ⟨x, List.mem_append_left _ hx, hk⟩
    · obtain ⟨a, bs, hk, hloc, hsz, -⟩ := allocWrite_site hpre ha (by rw [hat.2.1, ha]; rfl)
        hat.2.2.2.2 hc hf
      exact ⟨e, by simp, a, bs, hk, hloc, hsz⟩
    · simp [cond, ha, hl] at hy
  · obtain ⟨hs, -⟩ := next_eq hn
    have h := all_of check_start d.site (outcome L g e) (cond L g d)
    rw [← hs] at h
    simp only [h', decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at h
    rcases h.2 with h5 | hb
    · have hb : d.site ≠ .ldBase := fun hb => by rw [hb] at h5; simp [Site.start] at h5
      obtain ⟨x, hx, hk⟩ := hJ.baseRead h5
      rw [next_base hb hn]
      exact ⟨x, List.mem_append_left _ hx, hk⟩
    · obtain ⟨a, bs, hk, hloc, hsz⟩ := ldBase_site hpre hb (by rw [hat.2.1, hb]; rfl)
        hat.2.2.2.2 hc hf
      obtain ⟨a', bs', hk', hv⟩ := next_ldBase hb hn
      rw [hk] at hk'
      obtain ⟨rfl, rfl⟩ := Kind.rd.inj hk'
      exact ⟨e, by simp, a, bs, hk, hloc, hsz, hv⟩
  · obtain ⟨hs, hit⟩ := next_eq hn
    have h := all_of check_done d.site (outcome L g e) (cond L g d)
    rw [← hs, h'] at h
    simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      Bool.not_eq_true', decide_eq_true_eq] at h
    rcases h with ⟨hp, hk⟩ | ⟨hy, ⟨hq, hk⟩ | ⟨hq, hk⟩⟩
    · rw [hk] at hit
      simp only [Upd.apply, Prod.mk.injEq] at hit
      rw [hit.1]
      exact hJ.done hp hr
    · rw [hk] at hit
      simp only [Upd.apply, Prod.mk.injEq] at hit
      rw [hit.1]
      simp only [cond, hq, decide_eq_false_iff_not, not_and, not_lt] at hy
      exact hy hr
    · rw [hk] at hit
      simp only [Upd.apply, Prod.mk.injEq] at hit
      rw [hit.1]
      have hy' : condC L g d 11 = false := by
        rcases hq with hq | hq <;> simpa [cond, hq] using hy
      simpa [condC] using hy'
  · have hv := lead_valid (hJ.leadSite hL.of_snoc) hL hn
    rw [countP_snoc, hJ.commits hL.of_snoc, isTcCommit_ev hev, cnt_next check_com hi hP hn hv]
  · obtain ⟨hs, -⟩ := next_eq hn
    have h := all_of check_commitElect d.site (outcome L g e) (cond L g d)
    rw [← hs, h'] at h
    simp only [List.all_eq_true, List.mem_finRange, forall_const] at h
    have h := h c
    simp only [decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨hd, ho⟩ := h
    obtain ⟨inst, hk⟩ := elect_lead_event (by rw [hd]; rfl) hc hf ho
    exact ⟨e, inst, by simp, hk⟩
  · have hev' : isElectE e = d.site.isElect := by
      cases hs : d.site.isElect
      · exact notElect_site hc hf hs
      · obtain ⟨mk, inst, ld, hk⟩ := elect_of_next hs hn
        simp [isElectE, hk]
    rw [countP_snoc, hJ.elects, hev', cnt_next (L := L) check_elect hi hP hn rfl, Nat.add_assoc]
  · rw [countP_snoc, hJ.pollsAt s0 hs0, okPollAt_ev hev (fires_pc hf)]
    by_cases h1 : s0 = .waitDealloc
    · subst h1
      have h := cnt_next (L := L) check_pollsDealloc hi hP hn rfl
      simp only [cnt, Nat.zero_mul, Nat.zero_add, Nat.add_zero] at h
      simp only [pollCnt, ite_true]
      exact h.symm
    by_cases h2 : region s0 = 2
    · have hck : checkL (fun s => s.inTrip s0.ord) (pollEv s0) allValid = true := by
        have h := List.all_eq_true.mp check_pollsLoop s0 (mem_allSites s0)
        simpa [hs0, h2] using h
      simp only [pollCnt, h1, h2, ite_true, ite_false]
      exact (cntL_next hck hi hP hn rfl).symm
    · have hck : check (fun s => s.after s0.ord) 0 1 (pollEv s0) allValid = true := by
        have h := List.all_eq_true.mp check_pollsItem s0 (mem_allSites s0)
        simpa [hs0, h1, h2] using h
      simp only [pollCnt, h1, h2, ite_false]
      exact (cnt_next hck hi hP hn rfl).symm

/-- The invariant at the role's first state, after a prologue `pre` without successful polls,
arrivals, commits or MMAs. -/
theorem counts_init (base : Value) (pro : Nat → Value) (hp : ∀ m, okPolls m pre = 0)
    (ha : ∀ m, arrivals m pre = 0) (hcm : ∀ m, pre.countP (commitsTo m) = 0)
    (hm : pre.countP isMma = 0) (hr : Tmem.Pair.tmemOps pre = 0)
    (hb : pre.countP (Execution.isBarId 2) = 0) (hel : pre.countP isElectE = 1) :
    Counts L g ⟨.setMaxReg, 0, 0, base, pro⟩ pre := by
  have hc : ∀ (A : Site → Nat) (m k : Nat), A .setMaxReg = 0 →
      cnt L A m k ⟨.setMaxReg, 0, 0, base, pro⟩ = 0 := by
    intro A m k h
    simp [cnt, h]
  refine
    { pre := fun _ => rfl
      qFull := fun k => by rw [hp, hc _ _ _ (by simp [qA, Site.after, Site.ord])]
      kvFull := fun s => by
        rw [hp, hc _ _ _ (by simp [kvA, Site.after, Site.inTrip, Site.ord])]
        simp [slots]
        omega
      pReady := fun k => by rw [hp, hc _ _ _ (by simp [pA, Site.after, Site.inTrip, Site.ord])]
      pReady2 := fun k => by
        rw [hp, hc _ _ _ (by simp [p2A, Site.after, Site.inTrip, Site.ord])]
      dealloc := by rw [hp]; rfl
      handoff := by rw [ha]; rfl
      sFull := fun _ k => by
        rw [hcm, hc _ _ _ (by simp [sA, Site.after, Site.inTrip, Site.ord])]
      kvEmpty := fun _ s => by
        rw [hcm, hc _ _ _ (by simp [relA, Site.after, Site.inTrip, Site.ord])]
        simp [slots]
        omega
      qEmpty := fun _ k => by rw [hcm, hc _ _ _ (by simp [qeA, Site.after, Site.ord])]
      oFull := fun _ k => by rw [hcm, hc _ _ _ (by simp [ofA, Site.after, Site.ord])]
      mmas := fun _ => by
        rw [hm, hc _ _ _ (by simp [mmaA, Site.after, Site.inTrip, Site.ord, blockPos])]
      leadSite := fun _ k h => by cases h
      nonLead := fun _ => ⟨rfl, hcm, hm⟩
      odd := fun _ => ⟨hcm, hm⟩
      elected := fun h => by cases h
      tmem := hr
      bar2 := hb
      bar2Sync := fun x hx hx2 => absurd hb (List.countP_pos_iff.mpr ⟨x, hx, hx2⟩).ne'
      allocWrite := fun h => by cases h
      wrote := fun _ h => by simp [Site.start] at h
      baseRead := fun h => by simp [Site.start] at h
      done := fun h => by cases h
      commits := fun _ => by
        rw [hc _ _ _ (by simp [comA, sA, relA, qeA, ofA, Site.after, Site.inTrip, Site.ord])]
        refine List.countP_eq_zero.mpr fun x hx hk => ?_
        unfold isTcCommit at hk
        split at hk
        · rename_i sp hsp
          have := List.countP_pos_iff.mpr ⟨x, hx, (commitsTo_of_kind hsp (m := sp.mbar)).trans
            (by simp)⟩
          rw [hcm] at this
          exact absurd this (by decide)
        · cases hk
      commitElect := fun _ h => by cases h
      elects := by
        rw [hel, hc _ _ _ (by simp [elA, Site.after, Site.inTrip, Site.ord])]
      pollsAt := fun s0 _ => by
        have h0 : pollCnt L s0 ⟨.setMaxReg, 0, 0, base, pro⟩ = 0 := by
          unfold pollCnt cntL
          split_ifs <;> simp [deallocA, cnt, Site.after, Site.inTrip, Site.loop, Site.ord]
        rw [h0]
        refine List.countP_eq_zero.mpr fun x hx hk => ?_
        unfold okPollAt at hk
        split at hk
        · rename_i pc' l p acq sc
          have := List.countP_pos_iff.mpr ⟨_, hx, (show okPoll l ⟨pc', .wait l p true acq sc⟩ =
            true by simp [okPoll, sourceWaitSuccess])⟩
          rw [show pre.countP (okPoll l) = okPolls l pre from rfl, hp] at this
          exact absurd this (by decide)
        · cases hk }

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
