-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderRetry
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaEvents

@[expose] public section

/-! # The MMA thread's poll of an input full barrier

An MMA thread at slot `s`'s full wait polls that slot's full barrier in its own CTA with its full
parity, succeeding or failing. After a failed poll it is still at that wait (`mma_poll`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
/-- The full wait at slot `s` names slot `s`'s full barrier in the thread's CTA, with the parity
`fp % 2` of the thread's full parity. -/
theorem full_wait_event {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}
    {o : Option TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (s : Fin 4)
    (hs : d.site = .full s) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ ok acq sc, e = ⟨d.site.pc, .wait ⟨.shared, g / L.block, L.sharedBase + 8 + 8 * s.val⟩
      (d.fp % 2) ok acq sc⟩ := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  rw [code_full_ops s] at hc
  cases hc
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hb := (fullBase_value L g _ s) ▸ holds_mem h.2.2.2.2 (Flow.mem_factsFrom (fullBase_live s))
  have hp : t.regs 885 = some (b32 fp) :=
    (show valueOf L g ⟨.full s, w, q, fp, ap, cp, r, x⟩ 885 = b32 fp by mma_values) ▸
      holds_mem h.2.2.2.2 (Flow.mem_factsFrom (fullPar_live s))
  have hm := mbarLoc_b32 (L := L) (g := g) hb (by omega) (by omega)
  obtain ⟨ok, acq, sc, he, -⟩ := fires_wait_at hm
    (show readBits L g t 32 (.reg 885) = .ok (truncBits 32 (BitVec.ofNat 64 fp)) by
      simp [readBits, readReg, hp, b32, bind, Except.bind, pure, Except.pure]) hf
  have hpar : (truncBits 32 (BitVec.ofNat 64 fp)).toNat % 2 = fp % 2 := by
    simp only [truncBits, BitVec.toNat_ofNat]
    norm_num
  exact ⟨ok, acq, sc, by rw [he, hpar]⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof.Mma

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
/-- An MMA thread at slot `s`'s full wait after its whole trace can poll that slot's full barrier,
succeeding or failing; after a failed poll it is still at that wait. -/
theorem mma_poll {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}
    (hpre : Pre P L mem0) (hg : g < L.threads) {m : Mma.D} {s : Fin 4} {t : TState}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.mma m))))
    (hs : m.site = .full s) (hr : Run kernel Prod L g {} (X.tr g) (some t)) (ok : Bool) :
    ∃ t1 u sc, Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨m.site.pc,
        .wait ⟨.shared, g / L.block, L.sharedBase + 8 + 8 * s.val⟩ (m.fp % 2) ok true sc⟩ (some u) ∧
      (ok = false → (code L g).toMachine.after (some (code L g).init) (X.tr g ++
        [⟨m.site.pc, .wait ⟨.shared, g / L.block, L.sharedBase + 8 + 8 * s.val⟩ (m.fp % 2) false
          true sc⟩]) = some (some (.inr (.mma m)))) := by
  obtain ⟨t1, hl, hgood⟩ := Code.end_site (sound hpre hg) hr hσ
  have hat := hgood.1
  have hpc : (code L g).pc (.inr (.mma m)) = (Mma.Site.full s).pc := by
    show m.site.pc = _
    rw [hs]
  have hout := Code.site_out (sound hpre hg) hgood
  have hc : kernel.code[m.site.pc]? = some ⟨none, .mbarWait (Mma.fullPred s) (Mma.fullBase s) 0
      (.reg 885) true .cta⟩ := by
    rw [hs]; exact Mma.code_full_ops s
  rw [Code.tmpl, hpc, Mma.code_full_ops s] at hout
  dsimp only at hout
  have htpc : t1.pc = m.site.pc := hat.1
  rcases mbarWait_tmpl (A := Prod) (L := L) (g := g) (t := t1) (p' := Mma.fullPred s)
      (b := Mma.fullBase s) (off := 0) (par := .reg 885) (acq := true) (sc := .cta)
      with ⟨f, hw⟩ | ⟨m0, q, k, acq', sc', hw⟩
  · exfalso
    have hf : Fires m.site.pc (eventTmpl Prod L g t1 (.mbarWait (Mma.fullPred s)
        (Mma.fullBase s) 0 (.reg 885) true .cta)) ⟨m.site.pc, .ub f⟩ none := by
      rw [hw]; exact ⟨rfl, rfl⟩
    obtain ⟨ok', acq0, sc0, he⟩ := Mma.full_wait_event hpre s hs hat hc hf
    cases he
  · have hf : Fires m.site.pc (eventTmpl Prod L g t1 (.mbarWait (Mma.fullPred s)
        (Mma.fullBase s) 0 (.reg 885) true .cta))
        ⟨m.site.pc, .wait m0 q ok acq' sc'⟩ (some (k ok)) := by
      rw [hw]; exact ⟨ok, rfl, rfl⟩
    obtain ⟨ok', acq0, sc0, he⟩ := Mma.full_wait_event hpre s hs hat hc hf
    simp only [Event.mk.injEq, Kind.wait.injEq] at he
    obtain ⟨-, rfl, rfl, -, -, -⟩ := he
    obtain ⟨p1, b1, o1, q1, s1, hop, -⟩ := fires_wait_flags hf rfl
    simp only [Op.mbarWait.injEq] at hop
    obtain ⟨-, -, -, -, rfl, -⟩ := hop
    refine ⟨t1, k ok, sc', hl, ⟨.wait ⟨.shared, g / L.block, L.sharedBase + 8 + 8 * s.val⟩
      (m.fp % 2) k true sc', hout.trans (by rw [hw]), ?_⟩, ?_⟩
    · rw [htpc, hs]
      exact ⟨ok, rfl, rfl⟩
    · intro hok
      subst hok
      have hn : Mma.next L g m ⟨m.site.pc, .wait ⟨.shared, g / L.block, L.sharedBase + 8 + 8 *
        s.val⟩
          (m.fp % 2) false true sc'⟩ = some (some m) := by
        obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := m
        simp only at hs
        subst hs
        simp [Mma.next]
      rw [Machine.after_snoc (code L g).toMachine (some (code L g).init) (X.tr g), hσ]
      simp [Code.toMachine, code, hn]

end
end PTX.Kernels.Fp16Gemm8192.Proof
