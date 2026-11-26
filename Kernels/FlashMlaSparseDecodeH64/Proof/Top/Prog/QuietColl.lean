-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QuietRows
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CollKey
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CollPcs
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Followed
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.CollRel
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.Group
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.NextEnv
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Store
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.QuietWait

@[expose] public section

/-! # Quiet instructions and warp collectives

`Prog.quietColl`: a released pending lane whose next event is at an instruction that is quiet
(`quietOk`) or a warp collective with a static part (`CollIns`) steps; the collective's facts are
`coll_rel`, with every barrier's participant group (`bar_group`). `code_scan` turns a static check
of a pc range of the code into a statement about the instruction at each pc. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0}

/-- **A check of a pc range of the code**, as a statement about each pc of the range. -/
theorem code_scan {a n : Nat} {F : Nat → Instr → Bool}
    (h : (((kernel.code.drop a).take n).zipIdx).all (fun p => F (p.2 + a) p.1) = true) :
    ∀ pc, a ≤ pc → pc < a + n → ∀ ins, kernel.code[pc]? = some ins → F pc ins = true := by
  intro pc hlo hhi ins hins
  have hm : (ins, pc - a) ∈ ((kernel.code.drop a).take n).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_take, List.getElem?_drop]
    simpa [show pc - a < n by omega, show a + (pc - a) = pc by omega] using hins
  have := List.all_eq_true.mp h _ hm
  rwa [show pc - a + a = pc by omega] at this

/-- **A check of a pc range**: every pc holds a pc of the list `ps`, a quiet instruction or a warp
collective. -/
theorem Prog.scanOf {a n : Nat} {ps : List Nat}
    (h : (((kernel.code.drop a).take n).zipIdx).all
      (fun p => decide (p.2 + a ∈ ps) || quietOk p.1.op || collInsB p.1) = true) :
    ∀ pc, a ≤ pc → pc < a + n → ∀ ins, kernel.code[pc]? = some ins →
      pc ∈ ps ∨ quietOk ins.op = true ∨ CollIns ins := by
  intro pc hlo hhi ins hins
  have := code_scan (F := fun pc i => decide (pc ∈ ps) || quietOk i.op || collInsB i) h pc hlo hhi
    ins hins
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with (h | h) | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (by simpa [collInsB, CollIns] using h))

/-- **The pcs of a list hold waits.** -/
theorem Prog.waitPcs {ps : List Nat}
    (h : ps.all (fun pc => kernel.code[pc]?.any fun i => Sched.waitOp i.op) = true) :
    ∀ pc ∈ ps, ∃ ins, kernel.code[pc]? = some ins ∧ Sched.waitOp ins.op = true := by
  intro pc hpc
  have := List.all_eq_true.mp h pc hpc
  cases hc : kernel.code[pc]? with
  | none => simp [hc] at this
  | some ins => simp only [hc, Option.any_some] at this; exact ⟨ins, rfl, this⟩

/-- **A released pending lane at a quiet instruction or a warp collective steps.** -/
theorem Prog.quietColl (hIn : Top.Inputs P L m) (hp : Pre P L m) (hpub : Prog.StorePub P L m)
    (hs : SafeGoal kernel Assumptions.all L m) {X : Execution}
    (hmax : Maximal L kernel Assumptions.all m X) {g : Nat} {e : Event}
    (hpd : Frame.Pending L X g) (hrel : Step.Released L X g)
    (hn : Sched.NextEv L kernel Assumptions.all m X g e) (hub : ∀ f, e.kind ≠ .ub f)
    (hk : ∀ ins, kernel.code[e.pc]? = some ins → quietOk ins.op = true ∨ CollIns ins) :
    Sched.Steps (timed P L) m X (.thread g) := by
  by_cases hq : ∀ ins, kernel.code[e.pc]? = some ins → quietOk ins.op = true
  · exact Prog.quietIns hp hpub hs hmax hpd hrel hn hub hq
  have hX := hmax.1
  have hFw := follow_of hp X hX
  have hnu := Sched.safe_noUb (hs.2 X hX)
  have hR := hIn.bar hp X hX hFw
  refine coll_quiet_steps hp (Prog.nextEnv hp hs hmax) hs hFw
    (fun h => Prog.drained hp hpub hs hmax h)
    (coll_rel hp hX hFw hnu fun hg he => ?_) hpd hrel hn hub fun ins hins => ?_
  · obtain ⟨q, h1, h2, -⟩ := bar_group hp hR hg he
    exact ⟨q, h1, h2⟩
  · rcases hk ins hins with h | h
    · exact (hq fun ins' h' => by rw [hins] at h'; cases h'; exact h).elim
    · exact h

/-- **A quiet row of a role with waits** (`Wp`: the pcs of its waits). Every pc of the role
(`At`) holds a quiet instruction, a warp collective with a static part, or a wait; a wait that
cannot fail as a next event polls an object of the lane's CTA (`hloc`) with a final state
(`Prog.objFinal`) and steps by the role's `<role>_quietWait` (`hstep`). -/
theorem Prog.rowGen (hIn : Top.Inputs P L m) (hp : Pre P L m) (hpub : Prog.StorePub P L m)
    (X : Execution) {At : Nat → Nat → Prop} {Wp : Nat → Prop}
    (hscan : ∀ {g pc}, At g pc → ∀ ins, kernel.code[pc]? = some ins →
      Wp pc ∨ quietOk ins.op = true ∨ CollIns ins)
    (hwait : ∀ {pc}, Wp pc → ∃ ins, kernel.code[pc]? = some ins ∧ Sched.waitOp ins.op = true)
    (hloc : ∀ {g pc l q ok sc}, At g pc → Wp pc → Consistent L kernel Assumptions.all m X →
      Follow P L X → Sched.NextEv L kernel Assumptions.all m X g ⟨pc, .wait l q ok true sc⟩ →
      ∃ f, l = MbarRow.loc L g f ∧ 97 < pc)
    (hstep : ∀ {g pc l q ok sc}, At g pc → Wp pc → Follow P L X →
      Maximal L kernel Assumptions.all m X → ¬ HasUb X → Frame.Pending L X g →
      Step.Released L X g → Sched.NextEv L kernel Assumptions.all m X g ⟨pc, .wait l q ok true sc⟩ →
      ¬ FailsAt L m X g pc →
      (∃ before, MBarrier.stateBefore (X.objects l) (X.objects l).length = some before) →
      Sched.Steps (timed P L) m X (.thread g)) :
    NextRow.Quiet P L m X At := by
  intro hs hmax g e hpd hrel hn hub hat hf
  have hX := hmax.1
  have hFw := follow_of hp X hX
  have hnu := Sched.safe_noUb (hs.2 X hX)
  by_cases hw : Wp e.pc
  · obtain ⟨ins, hins, hwo⟩ := hwait hw
    obtain ⟨l, q, ok, sc, hkd⟩ := next_wait hn hub hins hwo
    obtain ⟨pc, kd⟩ := e
    simp only at hkd hw hat hf
    subst hkd
    obtain ⟨f, rfl, h97⟩ := hloc hat hw hX hFw hn
    exact hstep hat hw hFw hmax hnu hpd hrel hn hf (Prog.objFinal hIn hp hX hrel hn hub h97 hpd.1 f)
  · refine Prog.quietColl hIn hp hpub hs hmax hpd hrel hn hub fun ins hins => ?_
    rcases hscan hat ins hins with h | h | h
    · exact (hw h).elim
    · exact .inl h
    · exact .inr h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
