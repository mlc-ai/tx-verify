-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ClcCount
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaDiscipline
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerAcc
public import Kernels.Fp16Gemm8192.Proof.Thread.SchedulerSites
public import Kernels.Fp16Gemm8192.Proof.Thread.ClcSites
public import Lemmas.Flow.EndSite
public import Lemmas.Flow.Retry

@[expose] public section

/-! # The CLC polls of every role, with both outcomes

A thread at its CLC poll site polls its CTA's response barrier with the exact phase `cp` of its
state, and either outcome fires; after a failed poll it is still at that site (`clc_poll`). The
scheduler's acknowledgement poll at its `ackWait` site is the same, on the acknowledgement barrier
with the exact phase `ap` (`sched_ack_poll`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

namespace Loader

set_option maxHeartbeats 8000000 in
/-- The loader's CLC poll names the CTA's response barrier, with the exact phase of its state. -/
theorem clcWait_exact {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {l : D} {t : TState}
    {o : Option TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : l.site = .clcWait)
    (hi : Inv l) (h : At t l.site.pc (facts L g l)) (hc : kernel.code[l.site.pc]? = some ins)
    (hf : Fires l.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ ok acq sc, e = ⟨l.site.pc, .wait (clcResp L g) l.cp ok acq sc⟩ := by
  obtain ⟨s, m, n, q, cp, r, x⟩ := l
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_8)
  have hb : t.regs 812 = some (b32 (L.sharedBase + 104)) :=
    (show valueOf L g ⟨.clcWait, m, n, q, cp, r, x⟩ 812 = b32 (L.sharedBase + 104) by
      loader_values) ▸ holds_mem h.2.2.2.2
        (Flow.mem_factsFrom (show 812 ∈ Flow.live Site.clcWait.pc by table_decide))
  have hp : t.regs 876 = some (b32 cp) :=
    (show valueOf L g ⟨.clcWait, m, n, q, cp, r, x⟩ 876 = b32 cp by loader_values) ▸
      holds_mem h.2.2.2.2
        (Flow.mem_factsFrom (show 876 ∈ Flow.live Site.clcWait.pc by table_decide))
  obtain ⟨ok, acq, sc, he⟩ := clcWait_fire hpre hb hp hf
  exact ⟨ok, acq, sc, by rw [he, truncBits_phase hi.cp]⟩

/-- The loader's CLC poll site: its instruction is the response wait with the acquire flag. -/
theorem clcWait_op {l : D} {ins : Instr} (hs : l.site = .clcWait)
    (hc : kernel.code[l.site.pc]? = some ins) :
    ∃ p b off par, ins.op = .mbarWait p b off par true .cta := by
  have h8 : kernel.code[l.site.pc]? = some ⟨none, .mbarWait 986 812 0
      (.reg 876) true .cta⟩ := by
    rw [hs]; exact Flow.code_mbarWait_8
  obtain rfl := Option.some.inj (hc.symm.trans h8)
  exact ⟨_, _, _, _, rfl⟩

/-- A loader's CLC poll step with a failed poll leaves the loader at its CLC poll. -/
theorem clcWait_next {L : Launch} {g : Nat} {l : D} (hs : l.site = .clcWait) {m : Loc} {p : Nat}
    {acq : Bool} {sc : MbarScope} :
    (code L g).next (.inr (.loader l)) ⟨l.site.pc, .wait m p false acq sc⟩ =
      some (some (.inr (.loader l))) := by
  obtain ⟨s, m', n, q, cp, r, x⟩ := l
  simp only at hs
  subst hs
  simp [code, Loader.next]

end Loader

namespace Mma

set_option maxHeartbeats 8000000 in
/-- The MMA thread's CLC poll names the CTA's response barrier, with the exact phase of its state.
-/
theorem clcWait_exact {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}
    {o : Option TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .clcWait)
    (hi : Inv d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ ok acq sc, e = ⟨d.site.pc, .wait (clcResp L g) d.cp ok acq sc⟩ := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_15)
  have hb : t.regs 849 = some (b32 (L.sharedBase + 104)) :=
    (show valueOf L g ⟨.clcWait, w, q, fp, ap, cp, r, x⟩ 849 = b32 (L.sharedBase + 104) by
      mma_values) ▸ holds_mem h.2.2.2.2
        (Flow.mem_factsFrom (show 849 ∈ Flow.live Site.clcWait.pc by table_decide))
  have hp : t.regs 883 = some (b32 cp) :=
    (show valueOf L g ⟨.clcWait, w, q, fp, ap, cp, r, x⟩ 883 = b32 cp by mma_values) ▸
      holds_mem h.2.2.2.2
        (Flow.mem_factsFrom (show 883 ∈ Flow.live Site.clcWait.pc by table_decide))
  obtain ⟨ok, acq, sc, he⟩ := clcWait_fire hpre hb hp hf
  exact ⟨ok, acq, sc, by rw [he, truncBits_phase hi.cp]⟩

theorem clcWait_op {d : D} {ins : Instr} (hs : d.site = .clcWait)
    (hc : kernel.code[d.site.pc]? = some ins) :
    ∃ p b off par, ins.op = .mbarWait p b off par true .cta := by
  have h15 : kernel.code[d.site.pc]? = some ⟨none, .mbarWait 1001 849 0
      (.reg 883) true .cta⟩ := by
    rw [hs]; exact Flow.code_mbarWait_15
  obtain rfl := Option.some.inj (hc.symm.trans h15)
  exact ⟨_, _, _, _, rfl⟩

theorem clcWait_next {L : Launch} {g : Nat} {d : D} (hs : d.site = .clcWait) {m : Loc} {p : Nat}
    {acq : Bool} {sc : MbarScope} :
    (code L g).next (.inr (.mma d)) ⟨d.site.pc, .wait m p false acq sc⟩ =
      some (some (.inr (.mma d))) := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := d
  simp only at hs
  subst hs
  simp [code, Mma.next]

end Mma

namespace Consumer

set_option maxHeartbeats 8000000 in
/-- A consumer's CLC poll names the CTA's response barrier, with the exact phase of its state. -/
theorem clcWait_exact (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hs : d.site = .clcWait) (hi : Inv d) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ ok acq sc, e = ⟨d.site.pc, .wait (clcResp L g) d.cp ok acq sc⟩ := by
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  code_at hc
  subst hc
  have hb : t.regs 140 = some (b32 (L.sharedBase + 104)) :=
    (holds_mem h (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by cons_values))
  have hp : t.regs 889 = some (b32 cp) :=
    (holds_mem h (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by cons_values))
  obtain ⟨ok, acq, sc, he⟩ := clcWait_fire hpre hb hp hf
  exact ⟨ok, acq, sc, by rw [he, truncBits_phase hi.cp]⟩

/-- The consumer's CLC poll site: its instruction is the response wait with the acquire flag. -/
theorem clcWait_op {d : D} {ins : Instr} (hs : d.site = .clcWait)
    (hc : kernel.code[d.site.pc]? = some ins) :
    ∃ p b off par, ins.op = .mbarWait p b off par true .cta := by
  have h21 : kernel.code[d.site.pc]? = some ⟨none, .mbarWait 1026 140 0
      (.reg 889) true .cta⟩ := by
    rw [hs]; exact Flow.code_mbarWait_21
  obtain rfl := Option.some.inj (hc.symm.trans h21)
  exact ⟨_, _, _, _, rfl⟩

/-- A consumer's CLC poll step with a failed poll leaves it at its CLC poll. -/
theorem clcWait_next {L : Launch} {g : Nat} {d : D} (hs : d.site = .clcWait) {m : Loc} {p : Nat}
    {acq : Bool} {sc : MbarScope} :
    (code L g).next (.inr (.cons d)) ⟨d.site.pc, .wait m p false acq sc⟩ =
      some (some (.inr (.cons d))) := by
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs
  subst hs
  simp [code, Consumer.next]

end Consumer

namespace Scheduler

/-- The scheduler's CLC poll site: its instruction is the response wait with the acquire flag. -/
theorem clcWait_op {d : D} {ins : Instr} (hs : d.site = .clcWait)
    (hc : kernel.code[d.site.pc]? = some ins) :
    ∃ p b off par, ins.op = .mbarWait p b off par true .cta := by
  have h14 : kernel.code[d.site.pc]? = some ⟨none, .mbarWait 996 637 0
      (.reg 880) true .cta⟩ := by
    rw [hs]; exact Flow.code_mbarWait_14
  obtain rfl := Option.some.inj (hc.symm.trans h14)
  exact ⟨_, _, _, _, rfl⟩

/-- The scheduler's acknowledgement poll site: its instruction is the acknowledgement wait with the
acquire flag. -/
theorem ackWait_op {d : D} {ins : Instr} (hs : d.site = .ackWait)
    (hc : kernel.code[d.site.pc]? = some ins) :
    ∃ p b off par, ins.op = .mbarWait p b off par true .cta := by
  have h13 : kernel.code[d.site.pc]? = some ⟨none, .mbarWait 995 632 0
      (.reg 881) true .cta⟩ := by
    rw [hs]; exact Flow.code_mbarWait_13
  obtain rfl := Option.some.inj (hc.symm.trans h13)
  exact ⟨_, _, _, _, rfl⟩

/-- A scheduler's CLC poll step with a failed poll leaves it at its CLC poll. -/
theorem clcWait_next {L : Launch} {g : Nat} {d : D} (hs : d.site = .clcWait) {m : Loc} {p : Nat}
    {acq : Bool} {sc : MbarScope} :
    (code L g).next (.inr (.sched d)) ⟨d.site.pc, .wait m p false acq sc⟩ =
      some (some (.inr (.sched d))) := by
  obtain ⟨site, ap, cp, resp, x⟩ := d
  simp only at hs
  subst hs
  simp [code, Scheduler.next]

/-- A scheduler's acknowledgement poll step with a failed poll leaves it at that poll. -/
theorem ackWait_next {L : Launch} {g : Nat} {d : D} (hs : d.site = .ackWait) {m : Loc} {p : Nat}
    {acq : Bool} {sc : MbarScope} :
    (code L g).next (.inr (.sched d)) ⟨d.site.pc, .wait m p false acq sc⟩ =
      some (some (.inr (.sched d))) := by
  obtain ⟨site, ap, cp, resp, x⟩ := d
  simp only at hs
  subst hs
  simp [code, Scheduler.next]

end Scheduler

/-- The CLC poll of a thread state, by its role: its instruction is a wait with the acquire flag. -/
theorem clc_op {g : Nat} {L : Launch} {d : ThreadD} {ins : Instr} (hd : d.AtClcWait)
    (hc : kernel.code[(code L g).pc d]? = some ins) :
    ∃ p b off par, ins.op = .mbarWait p b off par true .cta := by
  rcases d with p | (l | m | s | c)
  · exact hd.elim
  · exact Loader.clcWait_op (l := l) hd hc
  · exact Mma.clcWait_op (d := m) hd hc
  · exact Scheduler.clcWait_op (d := s) hd hc
  · exact Consumer.clcWait_op (d := c) hd hc

/-- A thread state at its CLC poll site fires its poll at its own site on its CTA's response
barrier, with the phase of its state. -/
theorem clc_event {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : ThreadD} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hinv : (code L g).inv d) (hd : d.AtClcWait) (hat : (code L g).AtD d t)
    (hc : kernel.code[(code L g).pc d]? = some ins)
    (hf : Fires ((code L g).pc d) (eventTmpl Prod L g t ins.op) e o) :
    ∃ ok acq sc, e = ⟨(code L g).pc d, .wait (clcResp L g) d.cpOf ok acq sc⟩ := by
  rcases d with p | (l | m | s | c)
  · exact hd.elim
  · exact Loader.clcWait_exact hpre hd hinv.1 hat hc hf
  · exact Mma.clcWait_exact hpre hd hinv.1 hat hc hf
  · exact Scheduler.clcWait_event hpre hinv.1 hd hat hc hf
  · exact Consumer.clcWait_exact hpre hd hinv.1 hat.2.2.2.2 hc hf

/-- A thread state at its CLC poll site stays there after a failed poll. -/
theorem clc_next {L : Launch} {g : Nat} {d : ThreadD} (hd : d.AtClcWait) {m : Loc} {p : Nat}
    {acq : Bool} {sc : MbarScope} :
    (code L g).next d ⟨(code L g).pc d, .wait m p false acq sc⟩ = some (some d) := by
  rcases d with p' | (l | m' | s | c)
  · exact hd.elim
  · exact Loader.clcWait_next hd
  · exact Mma.clcWait_next hd
  · exact Scheduler.clcWait_next hd
  · exact Consumer.clcWait_next hd

set_option maxHeartbeats 8000000 in
/-- A thread at a poll site of the barrier `loc` with the phase `ph` of its state, after its whole
trace, can poll it with that phase, succeeding or failing; after a failed poll it is still at that
site. The site's instruction is a wait with the acquire flag (`hop`), its poll is the wait with the
phase (`hev`), and a failed poll keeps the state (`hnext`). -/
theorem poll_gen {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}
    (hpre : Pre P L mem0) (hg : g < L.threads) {d : ThreadD} {loc : Loc} {ph : Nat}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) = some (some d))
    (hop : ∀ {ins : Instr}, kernel.code[(code L g).pc d]? = some ins →
      ∃ p b off par, ins.op = .mbarWait p b off par true .cta)
    (hev : ∀ {t : TState} {ins : Instr} {e : Event} {o : Option TState}, (code L g).inv d →
      (code L g).AtD d t → kernel.code[(code L g).pc d]? = some ins →
      Fires ((code L g).pc d) (eventTmpl Prod L g t ins.op) e o →
      ∃ ok acq sc, e = ⟨(code L g).pc d, .wait loc ph ok acq sc⟩)
    (hnext : ∀ {m : Loc} {p : Nat} {acq : Bool} {sc : MbarScope},
      (code L g).next d ⟨(code L g).pc d, .wait m p false acq sc⟩ = some (some d))
    {t : TState} (hr : Run kernel Prod L g {} (X.tr g) (some t)) (ok : Bool) :
    ∃ t1 u sc, Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨(code L g).pc d, .wait loc ph ok true sc⟩ (some u) ∧
      (ok = false → (code L g).toMachine.after (some (code L g).init) (X.tr g ++
        [⟨(code L g).pc d, .wait loc ph false true sc⟩]) = some (some d)) := by
  obtain ⟨t1, hl, hgood⟩ := Code.end_site (sound hpre hg) hr hσ
  obtain ⟨ins, hc, -⟩ := ((sound hpre hg).steps d).site hgood.2
  obtain ⟨p, b, off, par, hop'⟩ := hop hc
  have hout := Code.site_out (sound hpre hg) hgood
  simp only [Code.tmpl, hc] at hout
  rcases mbarWait_tmpl (A := Prod) (L := L) (g := g) (t := t1) (p' := p) (b := b) (off := off)
      (par := par) (acq := true) (sc := .cta) with ⟨f, hw⟩ | ⟨m0, q, k, acq', sc', hw⟩
  · exfalso
    have hf : Fires ((code L g).pc d) (eventTmpl Prod L g t1 ins.op)
        ⟨(code L g).pc d, .ub f⟩ none := by
      rw [hop', hw]; exact ⟨rfl, rfl⟩
    obtain ⟨ok', acq0, sc0, he⟩ := hev hgood.2 hgood.1 hc hf
    cases he
  · have hf : Fires ((code L g).pc d) (eventTmpl Prod L g t1 ins.op)
        ⟨(code L g).pc d, .wait m0 q ok acq' sc'⟩ (some (k ok)) := by
      rw [hop', hw]; exact ⟨ok, rfl, rfl⟩
    obtain ⟨ok', acq0, sc0, he⟩ := hev hgood.2 hgood.1 hc hf
    simp only [Event.mk.injEq, Kind.wait.injEq] at he
    obtain ⟨-, hm, hq, -, -, -⟩ := he
    subst m0
    subst q
    obtain ⟨p1, b1, o1, q1, s1, hop1, -⟩ := fires_wait_flags hf rfl
    rw [hop'] at hop1
    simp only [Op.mbarWait.injEq] at hop1
    obtain ⟨-, -, -, -, rfl, -⟩ := hop1
    have htpc : t1.pc = (code L g).pc d := hgood.1.1
    have hf' : Fires t1.pc (eventTmpl Prod L g t1 ins.op)
        ⟨(code L g).pc d, .wait loc ph ok true sc'⟩ (some (k ok)) := by
      rw [htpc]; exact hf
    refine ⟨t1, k ok, sc', hl, ⟨eventTmpl Prod L g t1 ins.op, hout, hf'⟩, ?_⟩
    intro hok
    subst hok
    rw [Machine.after_snoc (code L g).toMachine (some (code L g).init) (X.tr g), hσ]
    exact hnext

set_option maxHeartbeats 8000000 in
/-- A thread at its CLC poll site, after its whole trace, can poll its CTA's response barrier with
the phase of its state, succeeding or failing; after a failed poll it is still at that site. -/
theorem clc_poll {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}
    (hpre : Pre P L mem0) (hg : g < L.threads) {d : ThreadD}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) = some (some d))
    (hd : d.AtClcWait) {t : TState} (hr : Run kernel Prod L g {} (X.tr g) (some t)) (ok : Bool) :
    ∃ t1 u sc, Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨(code L g).pc d, .wait (clcResp L g) d.cpOf ok true sc⟩ (some u) ∧
      (ok = false → (code L g).toMachine.after (some (code L g).init) (X.tr g ++
        [⟨(code L g).pc d, .wait (clcResp L g) d.cpOf false true sc⟩]) = some (some d)) :=
  poll_gen hpre hg hσ (fun hc => clc_op hd hc) (fun hinv hat hc hf =>
    clc_event hpre hinv hd hat hc hf)
    (fun {_ _ _ _} => clc_next hd) hr ok

set_option maxHeartbeats 8000000 in
/-- A leader scheduler at its acknowledgement poll, after its whole trace, can poll the
acknowledgement barrier of its CTA with the phase of its state, succeeding or failing; after a
failed poll it is still at that poll. -/
theorem sched_ack_poll {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}
    (hpre : Pre P L mem0) (hg : g < L.threads) {sd : Scheduler.D} {t : TState}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.sched sd))))
    (hs : sd.site = .ackWait) (hr : Run kernel Prod L g {} (X.tr g) (some t)) (ok : Bool) :
    ∃ t1 u sc, Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨sd.site.pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩)
        sd.ap ok true sc⟩ (some u) ∧
      (ok = false → (code L g).toMachine.after (some (code L g).init) (X.tr g ++
        [⟨sd.site.pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) sd.ap false true sc⟩]) =
          some (some (.inr (.sched sd)))) :=
  poll_gen hpre hg hσ (fun hc => Scheduler.ackWait_op hs hc)
    (fun hinv hat hc hf => Scheduler.ackWait_event hpre hinv.1 hs hat hc hf)
    (fun {_ _ _ _} => Scheduler.ackWait_next hs) hr ok

end

end PTX.Kernels.Fp16Gemm8192.Proof
