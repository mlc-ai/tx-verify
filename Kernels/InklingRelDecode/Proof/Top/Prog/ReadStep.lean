-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Prog.NextEnv
public import Kernels.InklingRelDecode.Proof.Common.Occurs
import Kernels.InklingRelDecode.Proof.Lib.ReadWf
import Kernels.InklingRelDecode.Proof.Protocol.Shared.GlobalReads
import Kernels.InklingRelDecode.Proof.Top.Result.Frame
import Kernels.InklingRelDecode.Proof.Top.Safe.NoAssumptionUb
import Lemmas.Step.ReadSource

@[expose] public section

/-! # A released lane at a plain read steps

A plain read is appended with a source for each byte (`Step.read_source_counted_extension`). The
read-only constraint of the 203 input sites holds of the extension when the lane's read address is
an input (`Lib.wf_snoc_read`); the address is a fact of the lane's state, which the roles export
for the event the lane is about to perform (`Protocol.Shared.occurs_input`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0}

/-- **A released pending lane whose template is a plain read steps.** -/
theorem Prog.read_step (hp : Pre Q L m) (hs : SafeGoal kernel Assumptions.all L m) {X : Execution}
    (hm : Maximal L kernel Assumptions.all m X) (hf : Follow Q L X) {g : Nat}
    (hpd : Frame.Pending L X g) (hne : X.tr g ≠ []) (hrel : Step.Released L X g)
    {t t1 : TState} (hrun : Run kernel Assumptions.all L g {} (X.tr g) (some t))
    (hl : TauTo L g t t1) {a : Acc}
    {k : List (Option Byte) → TState}
    (hout : out kernel Assumptions.all L g t1 = .ev (.read a k)) :
    Sched.Steps (schedule Q L) m X (.thread g) := by
  have hX := hm.1
  have hub := Sched.safe_noUb (hs.2 X hX)
  have nub : ¬ Assumptions.inputReadOnly.ub L m X := fun h =>
    hs.2 X hX (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨_, by simp [Assumptions.all], h⟩))))))))
  have nu : Frame.NoUbBefore X g (X.tr g).length := fun j _ e he f hf' =>
    hub ⟨(g, j), e.pc, f, by obtain ⟨pc, kd⟩ := e; simp only at hf'; subst hf'; exact he⟩
  refine .inl (Step.read_source_counted_extension hX hpd.1 hne hrel hrun hl hout
    (fun bs r hr => Lib.wf_snoc_read hp hX nub (fun site => ?_) (hr _))
    (Prog.nextEnv hp hs hm hf).guard)
  exact Protocol.Shared.occurs_input hp hX hf
    (.inr ⟨hpd.1, rfl, nu, t, t1, _, _, hrun, hl, hout, bs, (hr ⟨t1.pc, .rd a bs⟩).len, rfl, rfl⟩)
    (by simpa using site)

end PTX.Kernels.InklingRelDecode.Proof.Top
