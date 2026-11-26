-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Quiet
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Inputs
public import Lemmas.Quiet.Progress.Other
public import Lemmas.Kernel.Progress.Issue
public import Lemmas.Kernel.Progress.TcSt
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.NextEnv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Quiet
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.QuietWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Followed
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Bar0
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.ObjNe
import Lemmas.Flow.NotBulk

@[expose] public section

/-! # The quiet rows of the roles

A released pending lane whose next event is at an instruction that needs no partner steps
(`Prog.quietIns`): an instruction outside `Rest` (`Prog.ordinary`), a non-coherent load, a
`tcgen05` fence, copy or shift, a Tensor Memory store or store wait (`other_steps`), or the
register request (`reg_quiet_steps`). A role's quiet row is then a static check of its code (every
pc holds such an instruction or a wait) and, at a wait that cannot fail, the polled object's final
state (`objects_final`: the lane is past barrier 0, `bar0_next`).

Proved: warpgroup 2's row (`Prog.dequantRow`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0}

/-- The instructions a released lane performs without a partner. -/
def quietOp (op : Op) : Bool :=
  !(Descent.opKind op).Rest || Descent.otherOp op || Sched.tcStoreOp op || Sched.regOp op

/-- `quietOp`, or an instruction at which no next event without undefined behaviour is: a local
instruction or `trap`. -/
def quietOk (op : Op) : Bool :=
  quietOp op || op.isLocal || match op with | .trap => true | _ => false

/-- **A released pending lane at an instruction of `quietOk` steps.** -/
theorem Prog.quietIns (hp : Pre P L m) (hpub : Prog.StorePub P L m)
    (hs : SafeGoal kernel Assumptions.all L m) {X : Execution}
    (hmax : Maximal L kernel Assumptions.all m X) {g : Nat} {e : Event}
    (hpd : Frame.Pending L X g) (hrel : Step.Released L X g)
    (hn : Sched.NextEv L kernel Assumptions.all m X g e) (hub : ∀ f, e.kind ≠ .ub f)
    (hk : ∀ ins, kernel.code[e.pc]? = some ins → quietOk ins.op = true) :
    Sched.Steps (timed P L) m X (.thread g) := by
  have hc := Prog.nextEnv hp hs hmax
  have hFw := follow_of hp X hmax.1
  obtain ⟨ins, hins, hloc⟩ := next_site hp hFw hn hub
  have hone : ∀ {Q : Instr → Prop}, Q ins → ∀ ins', kernel.code[e.pc]? = some ins' → Q ins' :=
    fun hq ins' h' => by
      rw [hins] at h'
      cases h'
      exact hq
  have htrap : ∀ {gd}, ins ≠ ⟨gd, .trap⟩ := by
    rintro gd rfl
    obtain ⟨Y, hY, -, he⟩ := hn
    rcases get_source hY he with ⟨f, hf⟩ | ⟨t, ins', o, -, hc', hfire⟩
    · exact hub f hf
    rw [hins] at hc'
    cases hc'
    obtain ⟨he', -⟩ := hfire
    exact hub _ (by rw [he'])
  have h := hk ins hins
  have hq : quietOp ins.op = true := by
    obtain ⟨gd, op⟩ := ins
    cases op <;> simp_all [quietOk]
  simp only [quietOp, Bool.or_eq_true, Bool.not_eq_true'] at hq
  rcases hq with ((h | h) | h) | h
  · exact Prog.ordinary hp hpub hs hmax hpd hrel hn hub (hone (Q := fun i => _ = _) h)
  · exact other_steps hp hc hFw hpd hrel hn hub
      (hone (Q := fun i => _ = _) (by simp [h]))
  · exact other_steps hp hc hFw hpd hrel hn hub
      (hone (Q := fun i => _ = _) (by simp [h]))
  · exact reg_quiet_steps hp hc hFw hpd hrel hn hub (hone (Q := fun i => _ = _) h)

/-- **The polled object of a lane past pc 97 has a final state**, for a family of its CTA. -/
theorem Prog.objFinal (hIn : Top.Inputs P L m) (hp : Pre P L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) {g : Nat} {e : Event}
    (hrel : Step.Released L X g) (hn : Sched.NextEv L kernel Assumptions.all m X g e)
    (hub : ∀ f, e.kind ≠ .ub f) (hpc : 97 < e.pc) (hg : g < L.threads) (f : MbarFam) :
    ∃ st, MBarrier.stateBefore (X.objects (MbarRow.loc L g f))
      (X.objects (MbarRow.loc L g f)).length = some st := by
  have hFw := follow_of hp X hX
  have hb := bar0_next hp hFw hn hub hpc
  rw [← List.take_length (l := X.tr g)] at hb
  exact objects_final hp hX hFw (hIn.mbar hp X hX hFw) (hIn.initRows hp X hX hFw)
    (hIn.bar0 hp X hX hFw) hg (.inr ⟨rfl, hrel⟩) hb f

private theorem deq_code_all : (((kernel.code.drop 2606).take 1005).zipIdx).all
    (fun p => p.2 + 2606 == 2644 || p.2 + 2606 == 2677 || p.2 + 2606 == 2684 ||
      quietOk p.1.op) = true := by
  decide +kernel

/-- Warpgroup 2's code: every pc holds a quiet instruction or one of its three waits. -/
private theorem deq_code : ∀ pc, 2606 ≤ pc → pc < 2606 + 1005 → ∀ ins,
    kernel.code[pc]? = some ins → pc = 2644 ∨ pc = 2677 ∨ pc = 2684 ∨ quietOk ins.op = true := by
  intro pc hlo hhi ins hins
  have hm : (ins, pc - 2606) ∈ ((kernel.code.drop 2606).take 1005).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_take, List.getElem?_drop]
    simpa [show pc - 2606 < 1005 by omega, show 2606 + (pc - 2606) = pc by omega] using hins
  have h := List.all_eq_true.mp deq_code_all _ hm
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h
  · exact .inl (by omega)
  · exact .inr (.inl (by omega))
  · exact .inr (.inr (.inl (by omega)))
  · exact .inr (.inr (.inr h))

private theorem deq_wait : ∀ pc ∈ [2644, 2677, 2684], ∀ ins, kernel.code[pc]? = some ins →
    Sched.waitOp ins.op = true := by
  have : [2644, 2677, 2684].all (fun pc => kernel.code[pc]?.all fun i => Sched.waitOp i.op) =
      true := by decide +kernel
  intro pc hpc ins hins
  have h := List.all_eq_true.mp this pc hpc
  rw [hins] at h
  simpa using h

/-- **Warpgroup 2's quiet row.** -/
theorem Prog.dequantRow (hIn : Top.Inputs P L m) (hp : Pre P L m) (hpub : Prog.StorePub P L m)
    (X : Execution) : NextRow.Quiet P L m X (MbarRow.DequantAt L) := by
  intro hs hmax g e hpd hrel hn hub hat hf
  obtain ⟨-, -, hlo, hhi⟩ := hat
  have hX := hmax.1
  have hFw := follow_of hp X hX
  have hnu := Sched.safe_noUb (hs.2 X hX)
  by_cases hw : e.pc = 2644 ∨ e.pc = 2677 ∨ e.pc = 2684
  · obtain ⟨ins, hins⟩ : ∃ ins, kernel.code[e.pc]? = some ins :=
      Option.isSome_iff_exists.mp (by rcases hw with h | h | h <;> rw [h] <;> decide +kernel)
    have hwo := deq_wait e.pc (by rcases hw with h | h | h <;> simp [h]) ins hins
    obtain ⟨l, q, ok, sc, hkd⟩ := next_wait hn hub hins hwo
    obtain ⟨pc, kd⟩ := e
    simp only at hkd hlo hhi hw hf hins
    subst hkd
    have hfin := Prog.objFinal hIn hp hX hrel hn hub (by show 97 < pc; omega) hpd.1
    rcases dequant_next hp hFw hn hub ⟨hlo, by show pc ≤ 3610; omega⟩ with
      ⟨-, ok', hk⟩ | ⟨-, b, q', ok', hk⟩ | ⟨-, b, q', ok', hk⟩ | ⟨h3610, -⟩ | ⟨hnw, -⟩
    · simp only [Kind.wait.injEq] at hk
      obtain ⟨rfl, -⟩ := hk
      exact dequant_quietWait hp hFw hmax hnu hpd hrel ⟨hlo, by omega⟩ hn hf (hfin .qUtccp)
    · simp only [Kind.wait.injEq] at hk
      obtain ⟨rfl, -⟩ := hk
      exact dequant_quietWait hp hFw hmax hnu hpd hrel ⟨hlo, by omega⟩ hn hf (hfin _)
    · simp only [Kind.wait.injEq] at hk
      obtain ⟨rfl, -⟩ := hk
      exact dequant_quietWait hp hFw hmax hnu hpd hrel ⟨hlo, by omega⟩ hn hf (hfin _)
    · simp only at h3610
      omega
    · exact (hnw l q ok true sc rfl).elim
  · refine Prog.quietIns hp hpub hs hmax hpd hrel hn hub fun ins hins => ?_
    rcases deq_code e.pc hlo (by omega) ins hins with h | h | h | h
    · exact (hw (.inl h)).elim
    · exact (hw (.inr (.inl h))).elim
    · exact (hw (.inr (.inr h))).elim
    · exact h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
