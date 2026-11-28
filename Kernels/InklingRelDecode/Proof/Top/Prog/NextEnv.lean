-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Prog.Tc
public import Lemmas.Quiet.Progress.ReleasedG
import Kernels.InklingRelDecode.Proof.Top.Safe.NoTmemSource
import Kernels.InklingRelDecode.Proof.Mma.Export.Operands
import Kernels.InklingRelDecode.Proof.Protocol.Shared.BaseZero
import Kernels.InklingRelDecode.Proof.Top.Inputs
import Kernels.InklingRelDecode.Proof.Lib.NoStrong
import Kernels.InklingRelDecode.Proof.Lib.TmemWords
import Kernels.InklingRelDecode.Proof.Lib.AssumptionStep

@[expose] public section

/-! # The execution facts of a released lane's step (`Descent.NextEnvG`)

In a maximal execution of a safe launch the facts the library's steps use hold: no undefined
behaviour, the quiet extensions keep the assumptions, synchronization is guarded, no releasing
store, atomic or thread fence, the MMAs' layouts are injective, every Tensor Memory word is 4
bytes wide, and the conflicting accesses of the read bytes are ordered (no race, no mixed-size
conflict, no strong operation). The constraint of a plain read at the read-only input sites is not
a fact of the execution: a read steps at an address that is an input (`Prog.read_step`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

/-- **Every MMA is `kind::f16` with bf16 inputs and an f32 accumulator.** -/
theorem Prog.mmaKind (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) :
    ∀ i d s acc mask, X.MmaIssue i d s acc mask → s.descriptor.kind = .f16 .bf16 .f32 := by
  rintro ⟨g, k⟩ d s acc mask ⟨pc, he⟩
  rcases (Mma.Export.operands hp hX hf he).1 with h | h <;> rw [h] <;> rfl

/-- **The execution facts of a released lane's step**, from safety. -/
theorem Prog.nextEnv (hp : Pre Q L m) (hs : SafeGoal kernel Assumptions.all L m) {X : Execution}
    (hmax : Maximal L kernel Assumptions.all m X) (hf : Follow Q L X) :
    Descent.NextEnvG L kernel Assumptions.all m X where
  max := hmax
  noUb := Sched.safe_noUb (hs.2 X hmax.1)
  wf := Lib.assumptions_step.wfQuiet
  reads :=
    have hu := hs.2 X hmax.1
    ReadsOrdered.of_safe (fun h => hu (.inr (.inr (.inr (.inl h)))))
      (fun h => hu (.inr (.inr (.inl h)))) (Lib.strongOrdered hmax.1)
  guard := Safe.guarded hp hmax.1 hf (mbarRows_of hp hmax.1 hf) (initRows_of hp hmax.1 hf)
  no_release _ _ _ _ h := Lib.noReleasingStore hmax.1 h
  no_release_rmw _ _ _ _ _ h := (Lib.noAtomicEvent hmax.1 h).elim
  no_fence _ _ _ := Lib.noThreadFence hmax.1
  layout := Prog.layoutInjective hp hmax.1 hf (Protocol.Shared.base_read hp hmax.1 hf)
  words := Lib.tmem_words hmax.1 (Prog.mmaKind hp hmax.1 hf)

end PTX.Kernels.InklingRelDecode.Proof.Top
