-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEntry.Base
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEntry.tile_seg

@[expose] public section

/-! The consumer's entry steps whose local segments are short: the accumulator arrival and poll, and
the
acknowledgement. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The last load's full arrival on the accumulator barrier, then the epilogue's drain. -/
theorem step_accArrive {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .accArrive) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    entry_cont L g d e u := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_913)
  obtain rfl := fires_next (show AdvancesOp (PTX.Op.mbarArrive _ _ _ _ _ _ _) from trivial) hf
  have h1 := At.next h
  obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 0 (PTX.next t) = some t' ∧
      At t' (Site.drain 0).pc (facts L g ⟨.drain 0, m, n, m', n', cp, ap, resp, x, acc, base⟩) := by
    cons_seg h1 hpre
  right
  refine ⟨⟨.drain 0, m, n, m', n', cp, ap, resp, x, acc, base⟩, t', ?_, run_rtg hr, ht',
    ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6, hi.7⟩⟩
  simp [next]

/-- The accumulator poll: a failed poll returns to it, a successful one reaches the first load. -/
theorem step_accWait {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .accWait) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    entry_cont L g d e u := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_746)
  rw [← h.1] at hf
  obtain ⟨mb, parity, ok, sc, rfl, rfl⟩ := fires_wait hf
  have h1 := At.set (r := 1030) (v := .pred ok) h
    (Flow.not_mem_factsFrom (live := Flow.live Site.accWait.pc) (by table_decide))
  cases ok with
  | false =>
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 2
        (PTX.next (setReg t 1030 (.pred false))) = some t' ∧
        At t' Site.accWait.pc (facts L g ⟨.accWait, m, n, m', n', cp, ap, resp, x, acc, base⟩) := by
      cons_seg h1 hpre
    right
    refine ⟨⟨.accWait, m, n, m', n', cp, ap, resp, x, acc, base⟩, t', ?_, run_rtg hr, ht',
      ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6, hi.7⟩⟩
    simp [next]
  | true =>
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 1
        (PTX.next (setReg t 1030 (.pred true))) = some t' ∧
        At t' (Site.load 0).pc (facts L g ⟨.load 0, m, n, m', n', cp, ap, resp, x, acc, base⟩) := by
      cons_seg h1 hpre
    right
    refine ⟨⟨.load 0, m, n, m', n', cp, ap, resp, x, acc, base⟩, t', ?_, run_rtg hr, ht',
      ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6, hi.7⟩⟩
    simp [next]

/-- The acknowledgement: the claimed tile is set, and the accumulator poll is reached. -/
theorem step_ack {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .ack) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    entry_cont L g d e u := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_728)
  obtain rfl := fires_next (show AdvancesOp (PTX.Op.mbarArrive _ _ _ _ _ _ _) from trivial) hf
  have h1 := At.next h
  have hF : Holds (PTX.next t).regs (factsAt L g (Flow.bra_721 + 8)
      ⟨.ack, m, n, m', n', cp, ap, resp, x, acc, base⟩) :=
    Flow.holds_factsFrom_mono (live := Flow.live Site.ack.pc) h1.2.2.2.2 (by table_decide)
  obtain ⟨k, t', hr, ht'⟩ := tile_seg hpre hi ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, hF⟩
  right
  refine ⟨⟨.accWait, m, n, (nextTile ⟨.ack, m, n, m', n', cp, ap, resp, x, acc, base⟩).1,
    (nextTile ⟨.ack, m, n, m', n', cp, ap, resp, x, acc, base⟩).2, cp, ap, resp, x, acc, base⟩,
    t', ?_, run_rtg hr, ht', ⟨hi.1, hi.2, (nextTile_lt hi).1, (nextTile_lt hi).2, hi.5, hi.6, hi.7⟩⟩
  simp [next]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
