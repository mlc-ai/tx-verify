-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbRoles
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerTrace

public section

/-! # Defined softmax named barriers -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbWg0

open PTX PTX.Proof PTX.Flow Wg0

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The softmax and peer-exchange named barriers before output staging. -/
@[expose] def LoopBarrier : Wg0.Site → Prop
  | .wg0Sync | .wg0Sync2 | .pairBar | .lseBar | .lseBar2 => True
  | _ => False

private theorem barrier_kind (hpre : Pre P L mem0) {d : D} {e : Event} {o : Option TState}
    (hBar : LoopBarrier d.site)
    (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e o) :
    ∃ id n, e.kind = .bar id (some n) .sync := by
  by_cases hPair : d.site = .pairBar
  · exact ⟨_, _, Wg0PeerTrace.pair_kind hpre hf hPair⟩
  · have h9 : Wg0BarrierTrace.Bar9Site d.site := by
      cases h : d.site <;> simp [h, LoopBarrier] at hBar <;>
        simp [h, Wg0BarrierTrace.Bar9Site] at hPair ⊢
    exact ⟨_, _, Wg0BarrierTrace.bar9_kind hpre hf h9⟩

/-- All barriers in the softmax loop and LSE handoff have defined templates. -/
theorem barrier_tmpl_ok (hpre : Pre P L mem0)
    {d : D} {t : TState} {ins : Instr} (ha : (Wg0.code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins) (hBar : LoopBarrier d.site) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  intro hu
  have hf : (Machine.machine P L g).Fired (some (.wg0 d)) ⟨t.pc, .ub f⟩ none := by
    refine ⟨t, ⟨ha, hi⟩, ?_⟩
    change Fires t.pc (match kernel.code[d.site.pc]? with
      | some ins => eventTmpl Assumptions.all L g t ins.op
      | none => .ub .pcOutOfRange) ⟨t.pc, .ub f⟩ none
    rw [hc]
    change Fires t.pc (eventTmpl Assumptions.all L g t ins.op) ⟨t.pc, .ub f⟩ none
    rw [hu]
    exact ⟨rfl, rfl⟩
  obtain ⟨_, _, hk⟩ := barrier_kind hpre hBar hf
  cases hk

/-- The named barrier events keep the represented softmax successor. -/
theorem barrier_next_live (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    {i : Nat} {e : Event} {d : D} (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hBar : LoopBarrier d.site) : Machine.next P L g (.wg0 d) e ≠ none := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, hf⟩ := RingEvents.fired_of_trace hX (hs g hg).machine he hd
  obtain ⟨_, _, hk⟩ := barrier_kind hpre hBar hf
  cases h : d.site <;> simp only [h, LoopBarrier] at hBar <;>
    simp [Machine.next, Wg0.next, nextSite, h, hk]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbWg0
