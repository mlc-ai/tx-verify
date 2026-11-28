-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.LocalLanding
public import Lemmas.Flow.RunFrame

@[expose] public section

/-! # Local steps inside a straight window only move forward

In a window of pcs `[lo, hi)` without jumps, whose software `exp2` blocks end inside it, and
whose end `hi` holds an unguarded event, every local step moves the pc forward and stays in
`[lo, hi]`, and no local step leaves `hi`. So two states of one local path at the same pc of the
window are the same state (`rtg_fwd_unique`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow

variable {L : Launch} {g : Nat}

/-- The window `[lo, hi)`: no jump in it, the software `exp2` blocks end inside it, and an
unguarded event at `hi`. -/
def fwdWin (lo hi : Nat) : Bool :=
  ((kernel.code.drop lo).take (hi - lo)).all (fun ins => noJump ins.op && ins.op.isLocal) &&
  Assumptions.emuSites.all (fun q => decide (q + 11 ≤ hi)) &&
  match kernel.code[hi]? with
  | some ins => ins.guard.isNone && !ins.op.isLocal
  | none => false

/-- The instruction at a pc of the window is a local non-jump. -/
theorem fwdWin_at {lo hi : Nat} (hw : fwdWin lo hi = true) {pc : Nat} (h1 : lo ≤ pc)
    (h2 : pc < hi) {ins : Instr} (hc : kernel.code[pc]? = some ins) :
    noJump ins.op = true ∧ ins.op.isLocal = true := by
  simp only [fwdWin, Bool.and_eq_true, List.all_eq_true] at hw
  have hm : ins ∈ (kernel.code.drop lo).take (hi - lo) := by
    refine List.mem_of_getElem? (i := pc - lo) ?_
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, show lo + (pc - lo) = pc by omega]
    exact hc
  simpa using hw.1.1 ins hm

/-- **A local step in the window moves forward** and stays in it. -/
theorem tau_fwd {lo hi : Nat} (hw : fwdWin lo hi = true) {u u1 : TState}
    (ht : Tau kernel Assumptions.all L g u u1) (h1 : lo ≤ u.pc) (h2 : u.pc ≤ hi) :
    u.pc < hi ∧ u.pc < u1.pc ∧ u1.pc ≤ hi := by
  have hw' := hw
  simp only [fwdWin, Bool.and_eq_true, List.all_eq_true] at hw
  obtain ⟨⟨-, hemus⟩, hend⟩ := hw
  unfold Tau out at ht
  cases hf : u.fault with
  | some f => simp [hf] at ht
  | none =>
    simp only [hf] at ht
    cases hc : kernel.code[u.pc]? with
    | none => simp [hc] at ht
    | some ins =>
      simp only [hc] at ht
      have hlt : u.pc < hi := by
        by_contra hge
        obtain rfl : u.pc = hi := by omega
        rw [hc] at hend
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true'] at hend
        obtain ⟨hg, hl⟩ := hend
        simp [hg, hl, guardHolds, pure, Except.pure] at ht
      obtain ⟨hnj, -⟩ := fwdWin_at hw' h1 hlt hc
      refine ⟨hlt, ?_⟩
      cases hg : guardHolds u ins.guard with
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
            cases he : execLocalA Assumptions.all L g u ins.op with
            | error e => simp [he] at ht
            | ok t' =>
              simp only [he, Out.tau.injEq] at ht
              subst ht
              rcases localA_pc_emu he with (h | h) | ⟨h, hs⟩
              · rw [h, nextPc_noJump hnj] at *
                omega
              · exact absurd h (brx_noJump hnj _)
              · have := hemus u.pc (by simpa using hs)
                simp only [decide_eq_true_eq] at this
                omega
          · simp [hl] at ht

/-- Local steps in the window never go back. -/
theorem rtg_fwd {lo hi : Nat} (hw : fwdWin lo hi = true) {u v : TState}
    (h : Relation.ReflTransGen (Tau kernel Assumptions.all L g) u v) (h1 : lo ≤ u.pc)
    (h2 : u.pc ≤ hi) : u.pc ≤ v.pc ∧ v.pc ≤ hi := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨le_rfl, h2⟩
  | head ht _ ih =>
    obtain ⟨-, a2, a3⟩ := tau_fwd hw ht h1 h2
    obtain ⟨b1, b2⟩ := ih (by omega) a3
    omega

/-- **Two states of a local path at one pc of the window are one state.** -/
theorem rtg_fwd_unique {lo hi : Nat} (hw : fwdWin lo hi = true) {u v : TState}
    (h : Relation.ReflTransGen (Tau kernel Assumptions.all L g) u v) (h1 : lo ≤ u.pc)
    (h2 : u.pc ≤ hi) (e : v.pc = u.pc) : v = u := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, hc, hct⟩
  · rfl
  · obtain ⟨-, a2, a3⟩ := tau_fwd hw hc h1 h2
    obtain ⟨b1, -⟩ := rtg_fwd hw hct (by omega) a3
    omega

end PTX.Kernels.InklingRelDecode.Proof.Lib
