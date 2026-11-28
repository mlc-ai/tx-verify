-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.WindowFwd
public import Kernels.InklingRelDecode.Proof.Lib.RegionTop
public import Lemmas.Execution.EventFrameSource
public import Lemmas.Flow.RegionFrame

@[expose] public section

/-! # A local path inside a window starts at the event before it

A state of a lane between two events that reaches a pc of the straight window `[lo, hi)` is
reached by local steps from the state after the event at `lo - 1` (`win_entry`): no jump lands in
the window, the only events of the code near it are at `lo - 1` and `hi`, and the state after
an event is at its pc or the next one (`post_pc`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow

variable {L : Launch} {g : Nat}

/-- A jump of the instruction does not land in `[a, b]`. -/
def jumpsAvoid (a b : Nat) (ins : Instr) : Bool :=
  match ins.op with
  | .bra tgt _ => decide (tgt < a ∨ b < tgt)
  | .brx _ ts _ => ts.all fun q => decide (q < a ∨ b < q)
  | _ => true

/-- The window `[lo, hi)` is entered only after the event at `lo - 1`. -/
def entryOk (lo hi : Nat) : Bool :=
  fwdWin lo hi && kernel.code.all (jumpsAvoid lo hi) && Assumptions.emuSites.all (lo ≤ ·) &&
    match kernel.code[lo - 1]? with
    | some ins => ins.guard.isNone && !ins.op.isLocal
    | none => false

theorem entryOk_fwd {lo hi : Nat} (hw : entryOk lo hi = true) : fwdWin lo hi = true := by
  simp only [entryOk, Bool.and_eq_true] at hw
  exact hw.1.1.1

/-- **The state after an event is at its pc or the next one.** -/
theorem post_pc {s u : TState} {e : Event}
    (he : EStep kernel Assumptions.all L g s e (some u)) :
    s.pc ≤ u.pc ∧ u.pc ≤ s.pc + 1 := by
  obtain ⟨ins, hc, hnl, hf⟩ := EventFrame.estep_event_source he
  have hemu : Assumptions.emuSites.contains s.pc = false := by
    cases h : Assumptions.emuSites.contains s.pc
    · rfl
    · exfalso
      have := List.all_eq_true.mp (emu_local) s.pc (by simpa using h)
      simp [hc] at this
      simp [this] at hnl
  have hS := segFree hemu
  have := EventFrame.callbackFrame_fires (eventTmpl_return_frame_at
    (fun op u' h => execLocalA_frame rulesFrame h hS)) hf
  omega

/-- **A local step into the window comes from the window.** -/
theorem tau_pred {lo hi : Nat} (hw : entryOk lo hi = true) {u u1 : TState}
    (ht : Tau kernel Assumptions.all L g u u1) (h1 : lo ≤ u1.pc) (h2 : u1.pc ≤ hi) :
    lo ≤ u.pc ∧ u.pc ≤ hi := by
  simp only [entryOk, Bool.and_eq_true, List.all_eq_true] at hw
  obtain ⟨⟨⟨-, hj⟩, hemus⟩, hprev⟩ := hw
  unfold Tau out at ht
  cases hf : u.fault with
  | some f => simp [hf] at ht
  | none =>
    simp only [hf] at ht
    cases hc : kernel.code[u.pc]? with
    | none => simp [hc] at ht
    | some ins =>
      simp only [hc] at ht
      have hne : u.pc ≠ lo - 1 := by
        intro e
        rw [e] at hc
        rw [hc] at hprev
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true'] at hprev
        obtain ⟨hg, hl⟩ := hprev
        simp [hg, hl, guardHolds, pure, Except.pure] at ht
      have hja := hj ins (List.mem_of_getElem? hc)
      cases hg : guardHolds u ins.guard with
      | error e => simp [hg] at ht
      | ok b =>
        simp only [hg] at ht
        cases b with
        | false =>
          simp only [Out.tau.injEq] at ht
          subst ht
          simp only [skip] at h1 h2
          omega
        | true =>
          by_cases hl : ins.op.isLocal = true
          · simp only [hl, ↓reduceIte] at ht
            cases he : execLocalA Assumptions.all L g u ins.op with
            | error e => simp [he] at ht
            | ok t' =>
              simp only [he, Out.tau.injEq] at ht
              subst ht
              rcases localA_pc_emu he with (h | h) | ⟨h, hs⟩
              · cases hop : ins.op <;> simp only [hop, nextPc, jumpsAvoid] at h hja <;>
                  first | omega | (simp only [decide_eq_true_eq] at hja; omega)
              · cases hop : ins.op <;> simp only [hop, BrxTarget, jumpsAvoid] at h hja
                case brx a ts b =>
                  have := List.all_eq_true.mp hja _ h
                  simp only [decide_eq_true_eq] at this
                  omega
              · have := hemus u.pc (by simpa using hs)
                simp only [decide_eq_true_eq] at this
                omega
          · simp [hl] at ht

/-- Local steps into the window come from states of the window. -/
theorem rtg_pred {lo hi : Nat} (hw : entryOk lo hi = true) {u v : TState}
    (h : Relation.ReflTransGen (Tau kernel Assumptions.all L g) u v) (h1 : lo ≤ v.pc)
    (h2 : v.pc ≤ hi) : lo ≤ u.pc ∧ u.pc ≤ hi := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨h1, h2⟩
  | head ht _ ih => exact tau_pred hw ht ih.1 ih.2

/-- **Entering the window**: a local path from the state after an event that reaches a pc of the
window below its end starts at the event before the window, at the window's first pc. -/
theorem win_entry {lo hi : Nat} (hw : entryOk lo hi = true) {s t0 v : TState} {e : Event}
    (he : EStep kernel Assumptions.all L g s e (some t0))
    (hr : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t0 v) (h1 : lo ≤ v.pc)
    (h2 : v.pc < hi) : s.pc + 1 = lo ∧ t0.pc = lo := by
  have hfw := entryOk_fwd hw
  obtain ⟨a1, a2⟩ := rtg_pred hw hr h1 h2.le
  obtain ⟨b1, -⟩ := rtg_fwd hfw hr a1 a2
  have hp := post_pc he
  obtain ⟨ins, hc, hnl, -⟩ := EventFrame.estep_event_source he
  by_cases hs : lo ≤ s.pc ∧ s.pc < hi
  · obtain ⟨-, hl⟩ := fwdWin_at hfw hs.1 hs.2 hc
    simp [hl] at hnl
  · omega

end PTX.Kernels.InklingRelDecode.Proof.Lib
