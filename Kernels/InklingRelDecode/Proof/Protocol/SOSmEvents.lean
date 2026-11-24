-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SOSmCount
public import Kernels.InklingRelDecode.Proof.Protocol.SOMmaEvents
public import Lemmas.Flow.NotArrive

@[expose] public section

/-!
# What the softmax region's fired events are, as counts on the handshake barriers

* `WaitOShape`: **the thread-layer fact this file needs and the thread layer does not have yet**
  (row of "thread-layer gaps", the development notes): the poll at the site `waitO` is a poll of
  `o_done` of the
  thread's CTA with parity `oDoneParity i = (i + 1) % 2` (the register is `iteration xor 1`),
  acquire at CTA scope. `Sm.Shape` is `True` at that site. It is a copy of `Sm.shape_waitS_loc`
  with the registers of `waitO`, and is a premise here only because the thread layer's files are
  not edited by this layer.
* `sm_okPoll_s`: a successful poll of `s_ready b` exactly at the `waitS` site of an iteration in
  buffer `b`.
* `sm_arrivesOn_p`: an arrival on `p_ready b` exactly at the `arrive` site of an iteration in buffer
  `b`.
* `sm_okPoll_o`: a successful poll of `o_done` exactly at the `waitO` site.

At a site without an event shape the event is not a poll and not an arrival because no other
instruction of the program polls or arrives (`SOSites`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.SO
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Ring (okW)
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal)

noncomputable section
set_option maxRecDepth 100000

/-! ### The barriers by function, as the locations of the other shapes -/

theorem loc_sReadyOf (L : Launch) (c i : Nat) :
    (EvD.sReadyOf i).loc L c = sReady L c (i % 2) := by
  simp only [EvD.sReadyOf, EvD.Bar.loc, EvD.Bar.off, sReady, EvW.barLoc, EvW.sReadyOff]

theorem loc_pReadyOf (L : Launch) (c i : Nat) :
    (EvD.pReadyOf i).loc L c = pReady L c (i % 2) := by
  simp only [EvD.pReadyOf, EvD.Bar.loc, EvD.Bar.off, pReady, EvW.barLoc, EvW.pReadyOff]

theorem loc_oFinal (L : Launch) (c : Nat) : EvD.Bar.loc L c .oFinal = oFinal L c := by
  simp only [EvD.Bar.loc, EvD.Bar.off, oFinal, EvW.barLoc, EvW.oFinalOff]

theorem loc_oDone (L : Launch) (c : Nat) : EvD.Bar.loc L c .oDone = oDone L c := by
  simp only [EvD.Bar.loc, EvD.Bar.off, oDone, EvW.barLoc, EvW.oDoneOff]

/-! ### The poll at `waitO` -/

/-- **The event shape of the site `waitO`**, which `Sm.Shape` leaves as `True`: the poll of
`o_done` of the thread's CTA, with parity `(i + 1) % 2`, acquire at CTA scope. -/
def WaitOShape (L : Launch) : Prop :=
  ∀ (g : Nat) (d : Sm.D) (e : Event) (u : TState), Sm.Fired L g d e (some u) →
    d.site = .waitO →
    ∃ ok, e = ⟨Sm.evPc d.site, .wait (oDone L (g / L.block)) (oDoneParity d.i) ok true .cta⟩

/-! ### Sites that poll and arrive, by pc -/

theorem sm_pc_notWait (s : Sm.Site) (h1 : s ≠ .waitS) (h2 : s ≠ .waitO) :
    s.pc ∉ waitSites := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals try (exact absurd rfl h1)
  all_goals try (exact absurd rfl h2)
  all_goals decide +kernel

theorem sm_pc_notArrive (s : Sm.Site) (h1 : s ≠ .arrive) : s.pc ∉ arriveSites := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals try (exact absurd rfl h1)
  all_goals decide +kernel

variable {L : Launch} {g : Nat} {d : Sm.D} {e : Event} {u : TState}

/-- The template of a state whose pc is no poll site does not poll. -/
theorem sm_tmpl_notWait {t : TState} (hs : d.site.pc ∉ waitSites) :
    NotWait ((Sm.code Sm.asms L g d).tmpl (some d) t) := by
  show NotWait (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl Sm.asms L g t ins.op
    | none => Tmpl.ub .pcOutOfRange)
  split
  · rename_i ins hc
    exact eventTmpl_notWait (fun p b o par a s h => hs (wait_pc hc h))
  · trivial

/-- **A fired event at a site that is no poll site is not a poll.** -/
theorem sm_fired_notWait (hs : d.site.pc ∉ waitSites) (hF : Sm.Fired L g d e (some u)) :
    ∀ l p ok acq sc, e.kind ≠ .wait l p ok acq sc := by
  obtain ⟨t, ha, -, hf⟩ := hF
  have hpc : t.pc = d.site.pc := ha.1
  rw [hpc] at hf
  exact fires_notWait (sm_tmpl_notWait hs) hf

/-- The template of a state whose pc is no arrival site does not arrive. -/
theorem sm_tmpl_notArrive {t : TState} (hs : d.site.pc ∉ arriveSites) :
    NotArrive ((Sm.code Sm.asms L g d).tmpl (some d) t) := by
  show NotArrive (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl Sm.asms L g t ins.op
    | none => Tmpl.ub .pcOutOfRange)
  split
  · rename_i ins hc
    refine eventTmpl_notArrive (fun base off tx count cl rel sc st h => hs ?_)
    exact site_of_filter (P := fun op => match op with | .mbarArrive .. => true | _ => false)
      arrive_sites hc (by simp [h])
  · trivial

/-- **A fired event at a site that is no arrival site is not an arrival.** -/
theorem sm_fired_notArrive (hs : d.site.pc ∉ arriveSites) (hF : Sm.Fired L g d e (some u)) :
    ∀ l tx c rel sc, e.kind ≠ .arrive l tx c rel sc := by
  obtain ⟨t, ha, -, hf⟩ := hF
  have hpc : t.pc = d.site.pc := ha.1
  rw [hpc] at hf
  exact fires_notArrive (sm_tmpl_notArrive hs) hf

/-! ### The events as counts -/

/-- **The event of a softmax state, as a count of `s_ready` polls.** -/
theorem sm_okPoll_s (hS : Sm.SharedOk L) (hW : WaitOShape L)
    (hF : Sm.Fired L g d e (some u)) {b : Nat} (hb : b < 2) :
    okPoll (sReady L (g / L.block) b) e =
      (decide (d.site = .waitS ∧ d.i % 2 = b) && okW e) := by
  by_cases h1 : d.site = .waitS
  · obtain ⟨ok, he⟩ := Sm.shape_waitS_loc hS hF h1
    rw [he, loc_sReadyOf]
    cases ok <;> simp [okPoll, sourceWaitSuccess, okW, h1, sReady_eq_iff]
  by_cases h2 : d.site = .waitO
  · obtain ⟨ok, he⟩ := hW g d e u hF h2
    rw [he]
    cases ok
    · simp [okPoll, sourceWaitSuccess, okW, h1]
    · simp [okPoll, sourceWaitSuccess, okW, h1, oDone_ne_sReady hb]
  · have hnw := sm_fired_notWait (sm_pc_notWait d.site h1 h2) hF
    have hk : okPoll (sReady L (g / L.block) b) e = false := okPoll_notWait hnw
    have hw : okW e = false := by
      obtain ⟨pc, k⟩ := e
      cases k <;> first | rfl | exact absurd rfl (hnw _ _ _ _ _)
    rw [hk, hw]
    simp

/-- **The event of a softmax state, as a count of `o_done` polls.** -/
theorem sm_okPoll_o (hS : Sm.SharedOk L) (hW : WaitOShape L)
    (hF : Sm.Fired L g d e (some u)) :
    okPoll (oDone L (g / L.block)) e = (decide (d.site = .waitO) && okW e) := by
  by_cases h2 : d.site = .waitO
  · obtain ⟨ok, he⟩ := hW g d e u hF h2
    rw [he]
    cases ok <;> simp [okPoll, sourceWaitSuccess, okW, h2]
  by_cases h1 : d.site = .waitS
  · obtain ⟨ok, he⟩ := Sm.shape_waitS_loc hS hF h1
    rw [he, loc_sReadyOf]
    cases ok <;> simp [okPoll, sourceWaitSuccess, okW, h2, sReady_ne_oDone (b := d.i % 2)
      (by omega)]
  · have hnw := sm_fired_notWait (sm_pc_notWait d.site h1 h2) hF
    have hk : okPoll (oDone L (g / L.block)) e = false := okPoll_notWait hnw
    have hw : okW e = false := by
      obtain ⟨pc, k⟩ := e
      cases k <;> first | rfl | exact absurd rfl (hnw _ _ _ _ _)
    rw [hk, hw]
    simp

/-- A kind that is not an arrival is no arrival on any barrier. -/
theorem arrivesOn_false {m : Loc} {e : Event}
    (h : ∀ l tx c rel sc, e.kind ≠ .arrive l tx c rel sc) : arrivesOn m e = false := by
  obtain ⟨pc, k⟩ := e
  cases k <;> first | rfl | exact absurd rfl (h _ _ _ _ _)

/-- **The event of a softmax state, as a count of `p_ready` arrivals.** -/
theorem sm_arrivesOn_p (hS : Sm.SharedOk L) (hF : Sm.Fired L g d e (some u)) {b : Nat} :
    arrivesOn (pReady L (g / L.block) b) e = decide (d.site = .arrive ∧ d.i % 2 = b) := by
  by_cases h1 : d.site = .arrive
  · obtain ⟨-, he⟩ := Sm.shape_arrive hS hF h1
    rw [he, loc_pReadyOf]
    simp [arrivesOn, sourceArrive, h1, pReady_eq_iff]
  · have hna := sm_fired_notArrive (sm_pc_notArrive d.site h1) hF
    rw [arrivesOn_false hna]
    simp [h1]

end
end PTX.Kernels.InklingRelDecode.Proof.SO
