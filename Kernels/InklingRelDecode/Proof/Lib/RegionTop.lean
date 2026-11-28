-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.LocalLanding
public import Lemmas.Flow.RunLoClosed
import Lemmas.Flow.BarSyncNone
import Lemmas.Flow.RegionFrame
import Kernels.InklingRelDecode.Flow.Code.Part008

@[expose] public section

/-! # The softmax and the epilogue are never left

Every instruction from position 574 on falls through to a position from 574 on, its jumps (the
`brx.idx` included) land from 574 on, and the barrier before it (position 573) continues at 574.
So a lane that has an event at position 573 or later has only events from 574 on afterwards
(`LoClosed`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow

set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- The jumps of an instruction land from `lo` on. -/
def jumpsUp (lo : Nat) (ins : Instr) : Bool :=
  match ins.op with
  | .bra tgt _ => decide (lo ≤ tgt)
  | .brx _ ts _ => ts.all fun q => decide (lo ≤ q)
  | _ => true

/-- Every instruction from `lo` on jumps to `lo` or above. -/
def JumpsUp (lo : Nat) : Prop := (kernel.code.drop lo).all (jumpsUp lo) = true

theorem jumps_574 : JumpsUp 574 := by unfold JumpsUp; decide +kernel

theorem emu_local : Assumptions.emuSites.all (fun pc => match kernel.code[pc]? with
    | some ins => ins.op.isLocal
    | none => true) = true := by decide +kernel

theorem jumps_at {lo pc : Nat} {ins : Instr} (hj : JumpsUp lo) (h : lo ≤ pc)
    (hc : kernel.code[pc]? = some ins) : jumpsUp lo ins = true := by
  refine List.all_eq_true.mp hj ins (List.mem_of_getElem? (i := pc - lo) ?_)
  rw [List.getElem?_drop, show lo + (pc - lo) = pc by omega]
  exact hc

theorem jump_ok {lo : Nat} {ins : Instr} {pc q : Nat} (hj : jumpsUp lo ins = true)
    (hp : q = nextPc ins.op pc ∨ BrxTarget ins.op q) (h : lo ≤ pc) : lo ≤ q := by
  obtain ⟨gd, op⟩ := ins
  dsimp only at hp
  cases op with
  | brx a ts b =>
    rcases hp with hp | hp
    · simp only [nextPc] at hp; omega
    · have hall : ts.all (fun q => decide (lo ≤ q)) = true := by simpa [jumpsUp] using hj
      simpa using List.all_eq_true.mp hall q hp
  | bra tgt c => simp only [jumpsUp, nextPc, BrxTarget, decide_eq_true_eq, or_false] at hj hp; omega
  | _ => simp only [nextPc, BrxTarget, or_false] at hp; omega

theorem land_up {lo : Nat} (hj : JumpsUp lo) {t u : TState} {ins : Instr} (h : lo ≤ t.pc)
    (hc : kernel.code[t.pc]? = some ins)
    (hu : execLocalA Assumptions.all L g t ins.op = .ok u) : lo ≤ u.pc := by
  have hj := jumps_at hj h hc
  rcases localA_pc hu with hp | hp
  · exact jump_ok hj hp h
  · omega

theorem tau_up {lo : Nat} (hj : JumpsUp lo) {t u : TState} (h : lo ≤ t.pc)
    (ht : Tau kernel Assumptions.all L g t u) : lo ≤ u.pc := by
  unfold Tau out at ht
  cases hf : t.fault with
  | some f => simp [hf] at ht
  | none =>
    simp only [hf] at ht
    cases hc : kernel.code[t.pc]? with
    | none => simp [hc] at ht
    | some ins =>
      simp only [hc] at ht
      cases hg : guardHolds t ins.guard with
      | error e => simp [hg] at ht
      | ok b =>
        simp only [hg] at ht
        cases b with
        | false =>
          simp only [Out.tau.injEq] at ht
          subst ht
          simp only [skip]
          omega
        | true =>
          by_cases hl : ins.op.isLocal = true
          · simp only [hl, ↓reduceIte] at ht
            cases he : execLocalA Assumptions.all L g t ins.op with
            | error e => simp [he] at ht
            | ok t' =>
              simp only [he, Out.tau.injEq] at ht
              subst ht
              exact land_up hj h hc he
          · simp [hl] at ht

theorem ret_up {lo : Nat} {t u : TState} {e : Event} (h : lo ≤ t.pc)
    (hs : EStep kernel Assumptions.all L g t e (some u)) : lo ≤ u.pc := by
  obtain ⟨ins, hc, hnl, hf⟩ := EventFrame.estep_event_source hs
  by_cases he : Assumptions.emuSites.contains t.pc = true
  · have := List.all_eq_true.mp emu_local t.pc (by simpa using he)
    simp only [hc] at this
    rw [this] at hnl
    cases hnl
  · have hseg := segFree (by simpa using he)
    have hloc : ∀ op u, execLocalA Assumptions.all L g t op = .ok u → LocalFrame op t u :=
      fun op u hx => execLocalA_frame rulesFrame hx hseg
    rcases EventFrame.callbackFrame_fires (eventTmpl_return_frame_at (op := ins.op) hloc) hf with
      hp | hp <;> omega

theorem enter_up {t u : TState} {e : Event} (h : t.pc + 1 = 574)
    (hs : EStep kernel Assumptions.all L g t e (some u)) : 574 ≤ u.pc := by
  obtain ⟨ins, hc, hnl, hf⟩ := EventFrame.estep_event_source hs
  have h573 : t.pc = 573 := by omega
  rw [h573, Flow.code_573] at hc
  cases hc
  have := fires_barSync_next hf
  subst this
  simp [PTX.next, h573]

/-- **The positions from `lo` on are never left**, given the jumps and the event below `lo`. -/
theorem loClosed_of {lo : Nat} (hj : JumpsUp lo)
    (hen : ∀ g (t : TState) e u, t.pc + 1 = lo →
      EStep kernel Assumptions.all L g t e (some u) → lo ≤ u.pc) :
    LoClosed kernel Assumptions.all L lo where
  tau _ _ _ h ht := tau_up hj h ht
  ret _ _ _ _ h hs := ret_up h hs
  enter _ _ _ _ h hs := hen _ _ _ _ h hs
/-- **No local step and no event continuation of the kernel leaves the positions from 574 on.** -/
theorem loClosed : LoClosed kernel Assumptions.all L 574 :=
  loClosed_of jumps_574 fun _ _ _ _ h hs => enter_up h hs
