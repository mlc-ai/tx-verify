-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.RoleRun
public import Kernels.Fp16Gemm8192.Proof.Thread.ClcSites

@[expose] public section

/-! # Where the scheduler uses the CLC barriers

The elected lane of warp 10 runs the task loop of its CTA. A leader CTA polls the
acknowledgement barrier of its own CTA with the parity `ap` and, on success, requests the next
CTA; then every scheduler arrives on its own CTA's CLC response barrier and polls it with the
parity `cp`. After the response is read, the scheduler acknowledges on the leader CTA's
acknowledgement barrier. These are its only polls, arrivals and requests (`wait_site`,
`arrive_site`, `clcIssue_site`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

namespace Scheduler

/-- The CLC response barrier of the thread's own CTA: its response arrival and its CLC poll. -/
abbrev respBar (L : Launch) (g : Nat) : Loc := Bar.loc L (g / L.block) ⟨.clc, 0, true⟩

/-- The acknowledgement barrier of the thread's own CTA: the leader's acknowledgement poll. -/
abbrev ackBar (L : Launch) (g : Nat) : Loc := Bar.loc L (g / L.block) ⟨.clc, 0, false⟩

/-- The acknowledgement barrier of the cluster's leader CTA: the acknowledgement arrival. -/
abbrev leadAck (L : Launch) (g : Nat) : Loc := Bar.loc L (2 * (g / L.block / 2)) ⟨.clc, 0, false⟩

/-- The sites whose instruction uses an mbarrier object or issues a cluster launch control
request. -/
def Site.object : Site → Bool
  | .ackWait | .tryCancel | .arriveTx | .clcWait | .ack => true
  | _ => false


/-- The instruction of a site that uses no mbarrier object. -/
theorem code_object (s : Site) (hs : s.object = false) {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins) : objectOp ins.op = false := by
  cases s <;> simp only [Site.object, Bool.true_eq_false] at hs
  all_goals (code_at hc; subst hc; rfl)


set_option maxHeartbeats 4000000 in
/-- The acknowledgement poll names the own CTA's acknowledgement barrier and polls with `ap`. -/
theorem ackWait_event {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}
    {o : Option TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hi : Inv d)
    (hs : d.site = .ackWait) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ ok acq sc, e = ⟨d.site.pc, .wait (ackBar L g) d.ap ok acq sc⟩ := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  obtain ⟨site, ap, cp, resp, x⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_13)
  have hap : ap < 2 := hi.ap
  have hr : t.regs 632 = some (b32 (L.sharedBase + 128)) :=
    (holds_mem h.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by sched_values))
  have hp : t.regs 881 = some (b32 ap) :=
    (holds_mem h.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by sched_values))
  have hm := mbarLoc_b32 (L := L) (g := g) hr (by omega) (by omega)
  obtain ⟨ok, acq, sc, he, -⟩ := fires_wait_at hm
    (show readBits L g t 32 (.reg 881) = .ok (truncBits 32 (BitVec.ofNat 64 ap)) by
      simp [readBits, readReg, hp, b32, bind, Except.bind, pure, Except.pure]) hf
  have hpar : (truncBits 32 (BitVec.ofNat 64 ap)).toNat % 2 = ap := by
    rcases (by omega : ap = 0 ∨ ap = 1) with rfl | rfl <;> decide
  have hl : (⟨.shared, g / L.block, L.sharedBase + 128⟩ : Loc) = ackBar L g := by
    simp [ackBar, Bar.loc, Bar.off]
  exact ⟨ok, acq, sc, by rw [he, hpar, hl]⟩

set_option maxHeartbeats 4000000 in
/-- The CLC poll names the own CTA's CLC response barrier and polls with `cp`. -/
theorem clcWait_event {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}
    {o : Option TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hi : Inv d)
    (hs : d.site = .clcWait) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ ok acq sc, e = ⟨d.site.pc, .wait (respBar L g) d.cp ok acq sc⟩ := by
  obtain ⟨site, ap, cp, resp, x⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_14)
  have hcp : cp < 2 := hi.cp
  have hr : t.regs 637 = some (b32 (L.sharedBase + 104)) :=
    (holds_mem h.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by sched_values))
  have hp : t.regs 880 = some (b32 cp) :=
    (holds_mem h.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by sched_values))
  obtain ⟨ok, acq, sc, he⟩ := clcWait_fire hpre hr hp hf
  exact ⟨ok, acq, sc, by rw [he, truncBits_phase hcp]⟩

set_option maxHeartbeats 4000000 in
/-- The response arrival is on the own CTA's CLC response barrier. -/
theorem arriveTx_event {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}
    {o : Option TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .arriveTx)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ tx c rel sc, e = ⟨d.site.pc, .arrive (respBar L g) tx c rel sc⟩ := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  obtain ⟨site, ap, cp, resp, x⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_9)
  have hr : t.regs 637 = some (b32 (L.sharedBase + 104)) :=
    (holds_mem h.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by sched_values))
  have hb : t.regs 638 = some (b32 16) :=
    (holds_mem h.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by sched_values))
  have hm := mbarLoc_b32 (L := L) (g := g) hr (by omega) (by omega)
  obtain ⟨rel, sc, he, -⟩ := fires_arrive_at (cluster := false) (by simpa using hm)
    (show readBits L g t 32 (.reg 638) = .ok (truncBits 32 (BitVec.ofNat 64 16)) by
      simp [readBits, readReg, hb, b32, bind, Except.bind, pure, Except.pure])
    (show readBits L g t 32 (.imm 1) = .ok (truncBits 32 (BitVec.ofInt 64 1)) by
      simp [readBits, pure, Except.pure]) hf
  have hl : (⟨.shared, g / L.block, L.sharedBase + 104⟩ : Loc) = respBar L g := by
    simp [respBar, Bar.loc, Bar.off]
  exact ⟨(truncBits 32 (BitVec.ofNat 64 16)).toNat, (truncBits 32 (BitVec.ofInt 64 1)).toNat,
    rel, sc, by rw [he, hl]⟩

set_option maxHeartbeats 4000000 in
/-- The acknowledgement is an arrival on the leader CTA's acknowledgement barrier. -/
theorem ack_event {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}
    {o : Option TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hs : d.site = .ack) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ tx c rel sc, e = ⟨d.site.pc, .arrive (leadAck L g) tx c rel sc⟩ := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hcta := cta_lt hpre hg
  obtain ⟨site, ap, cp, resp, x⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_10)
  have hv : t.regs 645 = some (.ptr 32 false (.shared (g / L.block) (2 * ((g / L.block) / 2)))
      (BitVec.ofNat 64 (L.sharedBase + 128))) :=
    (holds_mem h.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by sched_values))
  have hm := mbarClusterLoc_ptr hv hg (by rw [hpre.grid] at hcta ⊢; omega)
    (by simp only [clusterOfCta_eq hpre]; omega) (by omega) (by omega)
  obtain ⟨rel, sc, he, -⟩ := fires_arrive_at (cluster := true) (by simpa using hm)
    (show readBits L g t 32 (.imm 0) = .ok (truncBits 32 (BitVec.ofInt 64 0)) by
      simp [readBits, pure, Except.pure])
    (show readBits L g t 32 (.imm 1) = .ok (truncBits 32 (BitVec.ofInt 64 1)) by
      simp [readBits, pure, Except.pure]) hf
  have hl : (⟨.shared, 2 * (g / L.block / 2), L.sharedBase + 128⟩ : Loc) = leadAck L g := by
    simp [leadAck, Bar.loc, Bar.off]
  exact ⟨(truncBits 32 (BitVec.ofInt 64 0)).toNat, (truncBits 32 (BitVec.ofInt 64 1)).toNat,
    rel, sc, by rw [he, hl]⟩

/-! ## The steps, site by site -/


theorem wait_site {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState} (hi : Inv d)
    (hat : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o)
    {m : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope} (hk : e.kind = .wait m p ok acq sc) :
    (d.site = .ackWait ∧ m = ackBar L g ∧ p = d.ap) ∨
      (d.site = .clcWait ∧ m = respBar L g ∧ p = d.cp) := by
  obtain ⟨site, ap, cp, resp, x⟩ := d
  simp only at hi hat hc hf hk ⊢
  cases hs : site.object
  · exact absurd (by rw [hk]; trivial) (notObject_of_op (code_object site hs hc) hf)
  cases site <;> simp only [Site.object, Bool.false_eq_true] at hs
  · obtain ⟨ok', acq', sc', he⟩ := ackWait_event hpre hi rfl hat hc hf
    rw [he] at hk
    simp only [Kind.wait.injEq] at hk
    exact .inl ⟨rfl, hk.1.symm, hk.2.1.symm⟩
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcIssue_0)
    rcases fires_clcTryCancel_kind hf with ⟨_, _, h'⟩ | ⟨_, h'⟩ <;> rw [hk] at h' <;> cases h'
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_9)
    rcases fires_mbarArrive_kind hf with ⟨_, _, _, _, _, h'⟩ | ⟨_, h'⟩ <;> rw [hk] at h' <;>
      cases h'
  · obtain ⟨ok', acq', sc', he⟩ := clcWait_event hpre hi rfl hat hc hf
    rw [he] at hk
    simp only [Kind.wait.injEq] at hk
    exact .inr ⟨rfl, hk.1.symm, hk.2.1.symm⟩
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_10)
    rcases fires_mbarArrive_kind hf with ⟨_, _, _, _, _, h'⟩ | ⟨_, h'⟩ <;> rw [hk] at h' <;>
      cases h'

/-- A response arrival is on the own CTA's response barrier, and an acknowledgement is on the
leader CTA's acknowledgement barrier. -/
theorem arrive_site {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hat : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o)
    {m : Loc} {tx c : Nat} {rel : Bool} {sc : MbarScope} (hk : e.kind = .arrive m tx c rel sc) :
    (d.site = .arriveTx ∧ m = respBar L g) ∨ (d.site = .ack ∧ m = leadAck L g) := by
  obtain ⟨site, ap, cp, resp, x⟩ := d
  simp only at hat hc hf ⊢
  cases hs : site.object
  · exact absurd (by rw [hk]; trivial) (notObject_of_op (code_object site hs hc) hf)
  cases site <;> simp only [Site.object, Bool.false_eq_true] at hs
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_13)
    rcases fires_mbarWait_kind hf with ⟨_, _, _, _, _, h'⟩ | ⟨_, h'⟩ <;> rw [hk] at h' <;>
      cases h'
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcIssue_0)
    rcases fires_clcTryCancel_kind hf with ⟨_, _, h'⟩ | ⟨_, h'⟩ <;> rw [hk] at h' <;> cases h'
  · obtain ⟨tx', c', rel', sc', he⟩ :=
      arriveTx_event (d := ⟨.arriveTx, ap, cp, resp, x⟩) hpre rfl hat hc hf
    rw [he] at hk
    simp only [Kind.arrive.injEq] at hk
    exact .inl ⟨rfl, hk.1.symm⟩
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_14)
    rcases fires_mbarWait_kind hf with ⟨_, _, _, _, _, h'⟩ | ⟨_, h'⟩ <;> rw [hk] at h' <;>
      cases h'
  · obtain ⟨tx', c', rel', sc', he⟩ :=
      ack_event (d := ⟨.ack, ap, cp, resp, x⟩) hpre hg rfl hat hc hf
    rw [he] at hk
    simp only [Kind.arrive.injEq] at hk
    exact .inr ⟨rfl, hk.1.symm⟩

/-- A cancellation request is issued at the scheduler's cancellation site. -/
theorem clcIssue_site {L : Launch} {g : Nat} {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hat : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o)
    {sp : Clc.Spec} {tg : List Nat} (hk : e.kind = .clcIssue sp tg) : d.site = .tryCancel := by
  obtain ⟨site, ap, cp, resp, x⟩ := d
  simp only at hat hc hf ⊢
  cases hs : site.object
  · exfalso
    have hq := (quiet (code_object site hs hc) hf sp.mbar).2.2.2.2
    have hk' : clcIssuesTo sp.mbar e = true := by simp [clcIssuesTo, hk]
    rw [hk'] at hq
    exact absurd hq (by decide)
  cases site <;> simp only [Site.object, Bool.false_eq_true] at hs
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_13)
    rcases fires_mbarWait_kind hf with ⟨_, _, _, _, _, h'⟩ | ⟨_, h'⟩ <;> rw [hk] at h' <;>
      cases h'
  · rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_9)
    rcases fires_mbarArrive_kind hf with ⟨_, _, _, _, _, h'⟩ | ⟨_, h'⟩ <;> rw [hk] at h' <;>
      cases h'
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_14)
    rcases fires_mbarWait_kind hf with ⟨_, _, _, _, _, h'⟩ | ⟨_, h'⟩ <;> rw [hk] at h' <;>
      cases h'
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_10)
    rcases fires_mbarArrive_kind hf with ⟨_, _, _, _, _, h'⟩ | ⟨_, h'⟩ <;> rw [hk] at h' <;>
      cases h'

end Scheduler

end
end PTX.Kernels.Fp16Gemm8192.Proof
