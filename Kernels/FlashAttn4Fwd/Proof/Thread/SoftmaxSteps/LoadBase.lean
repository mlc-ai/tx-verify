-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxBase
public import Kernels.FlashAttn4Fwd.Audit.TcLdConsumed0a0
public import Kernels.FlashAttn4Fwd.Audit.TcLdConsumed0a1
public import Kernels.FlashAttn4Fwd.Audit.TcLdConsumed0b0
public import Kernels.FlashAttn4Fwd.Audit.TcLdConsumed0b1
public import Kernels.FlashAttn4Fwd.Audit.TcLdConsumed0c
public import Kernels.FlashAttn4Fwd.Audit.TcLdConsumed0d

@[expose] public section

/-! # A score load and its implicit wait

Each `tcgen05.ld` of 32 score columns has the implicit `tcgen05.wait::ld` (ASM-TCLD-DATAFLOW):
its sub-step 0 loads at the address its register holds, writes the 32 destinations and stays at
the instruction, at sub-step 1 (`ld_step`). The state at the wait records the loaded values,
whatever they are, as the words of the load's columns (`loadW`); the facts of the registers
live before the load are unchanged (the words of the other columns are), and each destination
holds its column's word. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The state at the wait of load `c`, after loading `vals`. -/
abbrev atWait (d : D) (lp : Bool) (c : Fin 4) (vals : List Value) : D :=
  { d with site := .ldW lp c, w := loadW d.w c.val vals }

/-- A listed load that passes the data-flow check has the implicit wait. -/
theorem tcLdWait_of {pc : Nat} (hs : Assumptions.tcLdSites.contains pc = true)
    (hc : Assumption.ldConsumedAt kernel pc = true) : asms.any (·.tcLdWait pc) = true :=
  List.any_eq_true.mpr ⟨Assumptions.tcLd, by simp [asms, Assumptions.all],
    by simpa [Assumptions.tcLd, Assumption.tcLdDataflowAt, hc] using hs⟩

/-- The score loads have the implicit wait (the audit's data-flow checks). -/
theorem tcLdWait_ld (lp : Bool) (c : Fin 4) : asms.any (·.tcLdWait (Site.ld lp c).pc) = true := by
  have c0 := List.all_eq_true.mp Assumptions.tcLdSites_consumed_0c
  have d0 := List.all_eq_true.mp Assumptions.tcLdSites_consumed_0d
  cases lp <;> rcases fin4_cases c with rfl | rfl | rfl | rfl
  · exact tcLdWait_of (pc := 1266) (by decide) (by simpa using Assumptions.tcLdSites_consumed_0a0)
  · exact tcLdWait_of (pc := 1283) (by decide) (by simpa using Assumptions.tcLdSites_consumed_0a1)
  · exact tcLdWait_of (pc := 1300) (by decide) (by simpa using Assumptions.tcLdSites_consumed_0b0)
  · exact tcLdWait_of (pc := 1317) (by decide) (by simpa using Assumptions.tcLdSites_consumed_0b1)
  · exact tcLdWait_of (pc := 2728) (by decide) (c0 _ (by simp))
  · exact tcLdWait_of (pc := 2745) (by decide) (c0 _ (by simp))
  · exact tcLdWait_of (pc := 2762) (by decide) (d0 _ (by simp))
  · exact tcLdWait_of (pc := 2779) (by decide) (d0 _ (by simp))

/-- A register write keeps the registers outside its destinations. -/
theorem holds_setRegs_frame {t : TState} {ds : List Nat} {vs : List Value}
    {live : List Nat} {val : Nat → Value} (h : Holds t.regs (Flow.factsFrom live val))
    (hd : ∀ r ∈ live, r ∉ ds) : Holds (setRegs t ds vs).regs (Flow.factsFrom live val) := by
  refine holds_of_pointwise fun r hr => ?_
  rw [setRegs_other t ds vs r (hd r hr)]
  exact holds_mem h (List.mem_map.mpr ⟨r, hr, rfl⟩)

theorem ld_step {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {lp : Bool}
    {c : Fin 4} {ds : List Nat} {ta a : Nat} (hs : d.site = .ld lp c) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d))
    (hw : asms.any (·.tcLdWait d.site.pc) = true)
    (hr : t.regs ta = some (b32 a)) (ha : a < 2 ^ 32)
    (hds : ds = ldRegs lp c.val) (hnd : ds.Nodup) (hdisj : ∀ r ∈ Flow.live d.site.pc, r ∉ ds)
    (hframe : ∀ vals, Holds t.regs (factsAt L g d.site.pc d) →
      Holds t.regs (factsAt L g d.site.pc (atWait d lp c vals)))
    (hval : ∀ vals : List Value, vals.length = 32 → ∀ p < ds.length,
      valueOf L g (atWait d lp c vals) (ds.getD p 0) = vals.getD p (b32 0))
    (hf : Fires d.site.pc (eventTmpl asms L g t (.tcLd ds ta)) e (some u)) : Step L g d e u := by
  rw [← h.1] at hf hw
  obtain ⟨vals, hl, rfl, rfl⟩ := fires_tcLd_load (fun _ => by simp) hw h.2.1 hr ha hf
  have hx : d.site.extra = [] := by rw [hs]; rfl
  have hF : Holds t.regs (factsAt L g d.site.pc d) := by
    have := h.2.2.2.2
    simpa [facts, factsAt, hx] using this
  have hvl : vals.length = 32 := by
    have : ds.length = 32 := by
      subst hds
      cases lp <;> rcases fin4_cases c with rfl | rfl | rfl | rfl <;> rfl
    omega
  obtain ⟨-, -, hacc, hfl⟩ := setRegs_skel (PTX.next t) ds vals
  refine .inr ⟨atWait d lp c vals, _, by simp [next, hs], .refl, ⟨?_, rfl, ?_, ?_, ?_⟩, ?_⟩
  · show t.pc = _
    rw [h.1, hs]
    cases lp <;> rfl
  · exact hacc.trans h.2.2.1
  · exact hfl.trans h.2.2.2.1
  · show Holds (setRegs (PTX.next t) ds _).regs _
    rw [setRegs_next_regs]
    have hpc : (atWait d lp c vals).site.pc = d.site.pc := by rw [hs]; cases lp <;> rfl
    simp only [facts, hpc, Site.extra, Flow.factsFrom, List.map_append, holds_append]
    refine ⟨holds_setRegs_frame (hframe vals hF) hdisj, ?_⟩
    rw [← hds]
    refine holds_setRegs t ds _ _ hnd (by simp [hl]) fun p hp => ?_
    rw [hval vals hvl p hp]
  · have hsub : d.site.inItem = true := by rw [hs]; rfl
    refine inv_move hi hsub rfl rfl rfl (fun h0 => ?_) (fun h0 => ?_) (by simp)
    · rw [hs]; cases lp <;> simp_all [Site.tile0]
    · rw [hs]; cases lp <;> simp_all [Site.inTrip]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
