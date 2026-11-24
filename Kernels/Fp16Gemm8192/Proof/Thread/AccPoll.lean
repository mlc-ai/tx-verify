-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.MmaDiscipline
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerAcc
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaPoll

@[expose] public section

/-! # The accumulator polls of the MMA and consumer threads

An MMA thread at its accumulator-empty wait polls its warp's buffer `w % 2` on the leader CTA's
empty barrier with its accumulator parity `ap`, succeeding or failing (`mma_acc_poll`). A consumer
thread at its accumulator-full wait polls its CTA's full barrier of its accumulator with its
parity `ap` (`cons_acc_poll`). After a failed poll each is still at that wait. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
/-- An MMA thread at its accumulator-empty wait can poll its buffer's empty barrier, succeeding
or failing, with its accumulator parity `ap`; after a failed poll it is still at that wait. -/
theorem mma_acc_poll {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}
    (hpre : Pre P L mem0) (hg : g < L.threads) {m : Mma.D} {t : TState}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.mma m))))
    (hs : m.site = .accWait) (hr : Run kernel Prod L g {} (X.tr g) (some t)) (ok : Bool) :
    ∃ t1 u sc, Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨m.site.pc,
        .wait ⟨.shared, g / L.block, L.sharedBase + 8 * (m.w % 2) + 88⟩ m.ap ok true sc⟩ (some u) ∧
      (ok = false → (code L g).toMachine.after (some (code L g).init) (X.tr g ++
        [⟨m.site.pc, .wait ⟨.shared, g / L.block, L.sharedBase + 8 * (m.w % 2) + 88⟩ m.ap false true
          sc⟩]) =
          some (some (.inr (.mma m)))) := by
  obtain ⟨t1, hl, hgood⟩ := Code.end_site (sound hpre hg) hr hσ
  have hat := hgood.1
  have hout := Code.site_out (sound hpre hg) hgood
  have hc : kernel.code[m.site.pc]? = some ⟨none, .mbarWait 1005 857 0 (.reg 882)
      true .cta⟩ := by
    rw [hs]; exact Flow.code_mbarWait_16
  simp only [Code.tmpl, hc] at hout
  have htpc : t1.pc = m.site.pc := hat.1
  rcases mbarWait_tmpl (A := Prod) (L := L) (g := g) (t := t1) (p' := 1005)
      (b := 857) (off := 0) (par := .reg 882) (acq := true) (sc := .cta)
      with ⟨f, hw⟩ | ⟨m0, q, k, acq', sc', hw⟩
  · exfalso
    have hf : Fires m.site.pc (eventTmpl Prod L g t1 (.mbarWait 1005 857 0
        (.reg 882) true .cta)) ⟨m.site.pc, .ub f⟩ none := by
      rw [hw]; exact ⟨rfl, rfl⟩
    obtain ⟨ok', acq0, sc0, he⟩ := Mma.accWait_event hpre hs hgood.2.1 hat hc hf
    cases he
  · have hf : Fires m.site.pc (eventTmpl Prod L g t1 (.mbarWait 1005 857 0
        (.reg 882) true .cta)) ⟨m.site.pc, .wait m0 q ok acq' sc'⟩ (some (k ok)) := by
      rw [hw]; exact ⟨ok, rfl, rfl⟩
    obtain ⟨ok', acq0, sc0, he⟩ := Mma.accWait_event hpre hs hgood.2.1 hat hc hf
    simp only [Event.mk.injEq, Kind.wait.injEq] at he
    obtain ⟨-, rfl, rfl, -, -, -⟩ := he
    obtain ⟨p1, b1, o1, q1, s1, hop, -⟩ := fires_wait_flags hf rfl
    simp only [Op.mbarWait.injEq] at hop
    obtain ⟨-, -, -, -, rfl, -⟩ := hop
    refine ⟨t1, k ok, sc', hl, ⟨.wait ⟨.shared, g / L.block, L.sharedBase + 8 * (m.w % 2) + 88⟩
      m.ap k true sc', hout.trans (by rw [hw]), ?_⟩, ?_⟩
    · rw [htpc, hs]
      exact ⟨ok, rfl, rfl⟩
    · intro hok
      subst hok
      have hn : Mma.next L g m ⟨m.site.pc, .wait ⟨.shared, g / L.block, L.sharedBase + 8 * (m.w %
        2) + 88⟩
          m.ap false true sc'⟩ = some (some m) := by
        obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := m
        simp only at hs
        subst hs
        simp [Mma.next]
      rw [Machine.after_snoc (code L g).toMachine (some (code L g).init) (X.tr g), hσ]
      simp [Code.toMachine, code, hn]

set_option maxHeartbeats 8000000 in
/-- A consumer thread at its accumulator-full wait can poll its CTA's full barrier of its
accumulator, succeeding or failing, with its phase `ap`; after a failed poll it is still at that
wait. -/
theorem cons_acc_poll {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}
    (hpre : Pre P L mem0) (hg : g < L.threads) {c : Consumer.D} {t : TState}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.cons c))))
    (hs : c.site = .accWait) (hr : Run kernel Prod L g {} (X.tr g) (some t)) (ok : Bool) :
    ∃ t1 u sc, Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨Consumer.Site.accWait.pc,
        .wait (Consumer.accFull L g (Consumer.accIdx L g)) c.ap ok true sc⟩ (some u) ∧
      (ok = false → (code L g).toMachine.after (some (code L g).init) (X.tr g ++
        [⟨Consumer.Site.accWait.pc,
          .wait (Consumer.accFull L g (Consumer.accIdx L g)) c.ap false true sc⟩]) =
          some (some (.inr (.cons c)))) := by
  obtain ⟨t1, hl, hgood⟩ := Code.end_site (sound hpre hg) hr hσ
  have hat := hgood.1
  have hout := Code.site_out (sound hpre hg) hgood
  have hc : kernel.code[c.site.pc]? = some ⟨none, .mbarWait 1030 157 0 (.reg 890)
      true .cta⟩ := by
    rw [hs]; exact Flow.code_mbarWait_22
  simp only [Code.tmpl, hc] at hout
  have htpc : t1.pc = c.site.pc := hat.1
  rcases mbarWait_tmpl (A := Prod) (L := L) (g := g) (t := t1) (p' := 1030)
      (b := 157) (off := 0) (par := .reg 890) (acq := true) (sc := .cta)
      with ⟨f, hw⟩ | ⟨m0, q, k, acq', sc', hw⟩
  · exfalso
    have hf : Fires c.site.pc (eventTmpl Prod L g t1 (.mbarWait 1030 157 0
        (.reg 890) true .cta)) ⟨c.site.pc, .ub f⟩ none := by
      rw [hw]; exact ⟨rfl, rfl⟩
    obtain ⟨ok', acq0, sc0, he⟩ := Consumer.accWait_event hpre hs hgood.2.1 hat.2.2.2.2 hc hf
    cases he
  · have hf : Fires c.site.pc (eventTmpl Prod L g t1 (.mbarWait 1030 157 0
        (.reg 890) true .cta)) ⟨c.site.pc, .wait m0 q ok acq' sc'⟩ (some (k ok)) := by
      rw [hw]; exact ⟨ok, rfl, rfl⟩
    obtain ⟨ok', acq0, sc0, he⟩ := Consumer.accWait_event hpre hs hgood.2.1 hat.2.2.2.2 hc hf
    simp only [Event.mk.injEq, Kind.wait.injEq] at he
    obtain ⟨-, rfl, rfl, -, -, -⟩ := he
    obtain ⟨p1, b1, o1, q1, s1, hop, -⟩ := fires_wait_flags hf rfl
    simp only [Op.mbarWait.injEq] at hop
    obtain ⟨-, -, -, -, rfl, -⟩ := hop
    refine ⟨t1, k ok, sc', hl, ⟨.wait (Consumer.accFull L g (Consumer.accIdx L g)) c.ap
      k true sc', hout.trans (by rw [hw]), ?_⟩, ?_⟩
    · rw [htpc, hs]
      exact ⟨ok, rfl, rfl⟩
    · intro hok
      subst hok
      have hn : Consumer.next L g c ⟨Consumer.Site.accWait.pc,
          .wait (Consumer.accFull L g (Consumer.accIdx L g)) c.ap false true sc'⟩ = some (some c) :=
            by
        obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := c
        simp only at hs
        subst hs
        simp [Consumer.next]
      rw [Machine.after_snoc (code L g).toMachine (some (code L g).init) (X.tr g), hσ]
      simp [Code.toMachine, code, hn]

end

end PTX.Kernels.Fp16Gemm8192.Proof
