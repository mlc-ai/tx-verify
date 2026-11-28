-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.WinFacts
public import Kernels.InklingRelDecode.Proof.Lib.WinLane

@[expose] public section

/-! # From the last round's barrier to pc 2562

The local steps from the barrier of pc 1012 or the arrival of pc 1013 stay in the positions
1012 to 1257 or reach pc 2560 to 2565 by the branch of pc 1050, and write none of the registers
1915 (the sum), 1914 (the maximum) and 498 (the scale). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow

variable {L : Launch} {g : Nat}

/-- The positions the local steps from the last round's barrier reach. -/
def exS : List (Nat × Nat) := [(1012, 1257), (2560, 2565)]

/-- The registers the exit keeps: the sum, the maximum, the scale. -/
def exR : List Nat := [1915, 1914, 498]

/-- The events of the last round write none of the registers. -/
def exEw : Bool :=
  scanCode (fun pc ins => (pc != 1012 && pc != 1013) ||
    exR.all (fun r => !(EventFrame.eventWrites ins.op).contains r)) kernel.code 0

theorem ex_fwd : fwdOk exS exR = true := by decide +kernel
theorem ex_ew : exEw = true := by decide +kernel

/-- **The sum, the maximum and the scale at pc 2562** are those before the event of pc 1012 or
1013 that came last. -/
theorem exit_regs {s t0 t : TState} {e : Event}
    (hes : EStep kernel Assumptions.all L g s e (some t0)) (hpc : s.pc = 1012 ∨ s.pc = 1013)
    (ht : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t0 t) :
    ∀ r ∈ exR, t.regs r = s.regs r := by
  obtain ⟨ins, hc, -, -⟩ := EventFrame.estep_event_source hes
  have hp := post_pc hes
  have h0 : inS exS t0.pc = true := by
    rcases hpc with h | h <;> simp only [inS, exS, List.any_cons, List.any_nil, h] at hp ⊢ <;>
      simp only [decide_eq_true_eq, Bool.or_eq_true] <;> omega
  intro r hr
  have h2 := scanCode_get ex_ew hc
  rw [Nat.zero_add] at h2
  rw [(win_keep ex_fwd ht h0).2 r hr]
  refine estep_keeps hes ins hc r ?_
  simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true,
    Bool.not_eq_true'] at h2
  rcases h2 with h | h
  · exact absurd hpc (by omega)
  · simpa using h r hr

/-- The positions from which a local run can reach pc 2562. -/
def exB : List (Nat × Nat) := [(576, 948), (1013, 1050), (2560, 2562)]

/-- **The backward scan**: a local step into the positions starts in them. -/
def bwdOk (B : List (Nat × Nat)) : Bool :=
  scanCode (fun pc ins => inS B pc || !((ins.guard.isSome && inS B (pc + 1)) ||
    (ins.op.isLocal && (succs pc ins.op).any (inS B)))) kernel.code 0

/-- The events whose continuation is in `exB` are inside the softmax's range. -/
def exLo : Bool :=
  scanCode (fun pc ins => ins.op.isLocal || !(inS exB pc || inS exB (pc + 1)) ||
    (decide (574 < pc) && decide (pc < 2331))) kernel.code 0

theorem ex_bwd : bwdOk exB = true := by decide +kernel
theorem ex_lo : exLo = true := by decide +kernel
theorem ex_zero : inS exB 0 = false := by decide +kernel

theorem back_in {B} (hb : bwdOk B = true) {u v : TState}
    (h : Relation.ReflTransGen (Tau kernel Assumptions.all L g) u v) (hv : inS B v.pc = true) :
    inS B u.pc = true := by
  induction h with
  | refl => exact hv
  | @tail b c _ ht ih =>
    refine ih ?_
    by_contra hn
    obtain ⟨ins, hc, -, hk⟩ := win_cases ht
    have := scanCode_get hb hc
    rw [Nat.zero_add] at this
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
    rcases this with h1 | h1
    · exact hn h1
    rcases hk with ⟨hs, hp, -⟩ | ⟨hl, hp, -⟩
    · rw [hp] at hv
      simp [hs, hv] at h1
    · have hq : ∃ q ∈ succs b.pc ins.op, inS B q = true := ⟨c.pc, hp, hv⟩
      simp [hl] at h1
      obtain ⟨q, hq1, hq2⟩ := hq
      simp [h1.2 q hq1] at hq2

/-- **The last event before pc 2562 is a softmax event.** -/
theorem exit_range {s t0 t : TState} {e : Event}
    (hes : EStep kernel Assumptions.all L g s e (some t0))
    (ht : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t0 t) (hpc : t.pc = 2562) :
    574 < s.pc ∧ s.pc < 2331 := by
  obtain ⟨ins, hc, hnl, -⟩ := EventFrame.estep_event_source hes
  have hp := post_pc hes
  have h0 := back_in ex_bwd ht (by rw [hpc]; decide)
  have h1 := scanCode_get ex_lo hc
  rw [Nat.zero_add] at h1
  simp only [hnl, Bool.false_or, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true,
    decide_eq_true_eq] at h1
  rcases h1 with h | h
  · exfalso
    rcases (by omega : t0.pc = s.pc ∨ t0.pc = s.pc + 1) with e1 | e1 <;> rw [e1] at h0 <;>
      simp_all
  · exact h

end PTX.Kernels.InklingRelDecode.Proof.Lib
