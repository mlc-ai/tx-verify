-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaCountsGen

@[expose] public section

/-! # The counted events of a site

Each count of `Counts` moves on a site's event exactly as its site predicate (`qEv`, `kvEv`,
`cEv`, …) of the event's outcome says: the polls by the site's poll barrier (`okPoll_ev`), the
commits by its commit barrier (`commitsTo_ev`), the MMAs at the MMA sites (`isMma_eq`). The
KV ring's slot is the count of ring uses so far, modulo six (`kv_cnt`, `rel_cnt`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {g : Nat} {d : D} {e : Event}

/-- At a poll the outcome is the poll's. -/
theorem outcome_wait {l : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (h : e.kind = .wait l p ok acq sc) : outcome L g e = ok := by
  simp [outcome, waitOk, electLead, h]

/-- Opens the event of a poll site and closes the outcome. -/
macro "ev_cases" hev:ident : tactic => `(tactic| (
  obtain ⟨site, i, t, base, pro⟩ := d
  cases site <;> simp only [Ev] at $hev:ident <;>
    simp only [pollBar, qEv, kvEv, pEv, p2Ev, deallocEv, Bool.and_false, decide_false,
      reduceCtorEq, Bool.false_and]
  all_goals first
    | (simp; done)
    | (obtain ⟨ok, acq, sc, h⟩ := $hev:ident
       simp [outcome_wait h, waitOk_of h, stOf, Fin.ext_iff])))

theorem okPoll_q (hev : Ev L g d e) (k : Fin 2) :
    okPoll (bar L g (.qFull k)) e = qEv k d.site (outcome L g e) := by
  rw [okPoll_ev hev]
  ev_cases hev

theorem okPoll_p (hev : Ev L g d e) (k : Fin 2) :
    okPoll (bar L g (.pReady k)) e = pEv k d.site (outcome L g e) := by
  rw [okPoll_ev hev]
  ev_cases hev

theorem okPoll_p2 (hev : Ev L g d e) (k : Fin 2) :
    okPoll (bar L g (.pReady2 k)) e = p2Ev k d.site (outcome L g e) := by
  rw [okPoll_ev hev]
  ev_cases hev

theorem okPoll_dealloc (hev : Ev L g d e) :
    okPoll (bar L g .dealloc) e = deallocEv d.site (outcome L g e) := by
  rw [okPoll_ev hev]
  ev_cases hev

/-- The ring use counted at KV poll `k` is the use it polls. -/
theorem kv_cnt (k : Fin 4) (i t : Nat) (b : Value) (p : Nat → Value) :
    cnt L kvA 2 0 ⟨.kvWait k, i, t, b, p⟩ = kvUse L i (kvU k t) := by
  fin_cases k <;>
    simp [cnt, kvA, Site.after, Site.inTrip, Site.loop, Site.ord, kvOrd, kvU, kvUse, kvBase] <;>
    ring

/-- The ring use a KV-empty commit releases. -/
def relU (c : Fin 12) (t : Nat) : Nat :=
  if c = 2 then 0 else if c = 6 then 2 + 2 * t else 1 + 2 * t

theorem rel_cnt (c : Fin 12) (hc : cKind c = 2) (i t : Nat) (b : Value) (p : Nat → Value) :
    cnt L relA 2 0 ⟨.commit c, i, t, b, p⟩ = kvUse L i (relU c t) := by
  fin_cases c <;> simp [cKind] at hc <;>
    simp [cnt, relA, Site.after, Site.inTrip, Site.loop, Site.ord, elCOrd, relU, kvUse,
      kvBase] <;> ring

theorem okPoll_kv (hev : Ev L g d e) (s : Fin 6) :
    okPoll (bar L g (.kvFull s)) e =
      (kvEv d.site (outcome L g e) && decide (cnt L kvA 2 0 d % 6 = s.val)) := by
  rw [okPoll_ev hev]
  obtain ⟨site, i, t, base, pro⟩ := d
  cases site <;> simp only [Ev] at hev <;>
    simp only [pollBar, kvEv, Bool.and_false, Bool.false_and, reduceCtorEq, decide_false]
  case kvWait k =>
    obtain ⟨ok, acq, sc, h⟩ := hev
    rw [kv_cnt]
    simp [outcome_wait h, waitOk_of h, slotOf, kvSlot, Fin.ext_iff]
  all_goals simp

theorem cBar_class (L : Launch) (d : D) (c : Fin 12) :
    (∀ k : Fin 2, cBar L d c = .sFull k ↔ cKind c = k.val) ∧
    (∀ k : Fin 2, cBar L d c = .qEmpty k ↔ cKind c = 3 + k.val) ∧
    (∀ k : Fin 2, cBar L d c = .oFull k ↔ cKind c = 5 + k.val) := by
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_⟩ <;> fin_cases c <;> fin_cases k <;>
    simp [cBar, cKind]

/-- The commits of a site to a barrier of a class. -/
theorem commitsTo_class (hev : Ev L g d e) (j : Nat) (b : FBar)
    (hb : ∀ c : Fin 12, cBar L d c = b ↔ cKind c = j) :
    commitsTo (bar L g b) e = cEv j d.site (outcome L g e) := by
  rw [commitsTo_ev hev]
  obtain ⟨site, i, t, base, pro⟩ := d
  cases site <;> simp only [commitBar, cEv, reduceCtorEq, decide_false]
  case commit c => simp [hb c]

theorem commitsTo_kv (hev : Ev L g d e) (s : Fin 6) :
    commitsTo (bar L g (.kvEmpty s)) e =
      (cEv 2 d.site (outcome L g e) && decide (cnt L relA 2 0 d % 6 = s.val)) := by
  rw [commitsTo_ev hev]
  obtain ⟨site, i, t, base, pro⟩ := d
  cases site <;> simp only [commitBar, cEv, reduceCtorEq, decide_false, Bool.false_and]
  case commit c =>
    by_cases hc : cKind c = 2
    · rw [rel_cnt c hc]
      fin_cases c <;> simp [cKind] at hc <;>
        simp [cBar, cKind, relU, slotOf, kvSlot, Fin.ext_iff]
    · have : ∀ s', cBar L ⟨.commit c, i, t, base, pro⟩ c ≠ .kvEmpty s' := by
        fin_cases c <;> simp [cKind] at hc <;> simp [cBar]
      simp [this, hc]

theorem isMma_eq (hev : Ev L g d e) :
    isMma e = mmaEv d.site (outcome L g e) := by
  simp only [mmaEv]
  cases h : d.site.isMma
  · exact isMma_ev hev h
  · exact isMma_ev_mma hev h

theorem arrivesOn_handoff (hev : Ev L g d e) :
    arrivesOn (FBar.loc L (peer L g) .dealloc) e = handoffEv d.site (outcome L g e) := by
  rw [arrivesOn_ev hev]
  simp [handoffEv]

/-- The commits of a site's event: at the commit sites. -/
theorem isTcCommit_ev (hev : Ev L g d e) : isTcCommit e = comEv d.site (outcome L g e) := by
  have hq : ¬ ObjectKind e.kind → isTcCommit e = false := fun h => by
    unfold isTcCommit
    split
    · rename_i sp hk
      exact absurd (by rw [hk]; trivial) h
    · rfl
  obtain ⟨site, i, t, base, pro⟩ := d
  cases site <;> simp only [Ev] at hev <;> simp only [comEv]
  case commit c => simp [isTcCommit, hev]
  case qWait k | kvWait k | pWait k | p2Wait k _ | waitDealloc =>
    obtain ⟨ok, acq, sc, h⟩ := hev
    simp [isTcCommit, h]
  case arrivePeer =>
    obtain ⟨rel, sc, h⟩ := hev
    simp [isTcCommit, h]
  case mma b j => exact hq (notObject_of_mma hev)
  all_goals exact hq hev.1

/-- The successful polls at a position of a site's event: at a poll site of that position. -/
theorem okPollAt_ev (hev : Ev L g d e) (hpc : e.pc = d.site.pc) (s0 : Site) :
    okPollAt s0.pc e = pollEv s0 d.site (outcome L g e) := by
  obtain ⟨epc, ek⟩ := e
  simp only at hpc
  subst hpc
  have hq : ¬ ObjectKind ek → okPollAt s0.pc ⟨d.site.pc, ek⟩ = false := fun h => by
    unfold okPollAt
    split
    · rename_i heq
      simp only [Event.mk.injEq] at heq
      exact absurd (by rw [heq.2]; trivial) h
    · rfl
  obtain ⟨site, i, t, base, pro⟩ := d
  cases site <;> simp only [Ev] at hev <;> simp only [pollEv, Site.isPoll, Bool.and_false,
    Bool.false_and]
  case qWait k | kvWait k | pWait k | p2Wait k _ | waitDealloc =>
    obtain ⟨ok, acq, sc, h⟩ := hev
    subst h
    cases ok <;> simp [okPollAt, outcome, waitOk, electLead]
    exact Bool.eq_iff_iff.mpr (by simp)
  case arrivePeer =>
    obtain ⟨rel, sc, h⟩ := hev
    subst h
    rfl
  case commit c =>
    subst hev
    rfl
  case mma b j => exact hq (notObject_of_mma hev)
  all_goals exact hq hev.1

/-- The ring uses `U < N + 1` of a slot. -/
theorem slots_succ (N : Nat) (s : Fin 6) :
    slots (N + 1) s = slots N s + if N % 6 = s.val then 1 else 0 := by
  have := s.isLt
  simp only [slots]
  split_ifs <;> omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
