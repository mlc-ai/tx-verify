-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Inputs
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.TensorSource
public import Kernels.InklingRelDecode.Proof.Top.Prog.ScalarBlocker
public import Lemmas.Kernel.Progress.Blocked

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX Protocol

def Prog.Poll (Q : Params) (L : Launch) (m : Mem0) (pc : Nat) : Prop :=
  SafeGoal kernel Assumptions.all L m → ∀ X, Maximal L kernel Assumptions.all m X →
    Follow Q L X → ∀ {g}, Frame.Pending L X g → Step.Released L X g →
    FailsAt L m X g pc → Sched.Steps (schedule Q L) m X (.thread g)

def Prog.Named (Q : Params) (L : Launch) (m : Mem0) : Prop :=
  SafeGoal kernel Assumptions.all L m → ∀ X, Maximal L kernel Assumptions.all m X →
    Follow Q L X → ∀ {g}, Frame.Pending L X g → ¬ Step.Released L X g →
    (Sched.RegWait L X g ∨ Sched.TmemWait L X g ∨ Sched.BarWait L X g ∨ Sched.TcWait L X g) →
    Sched.Steps (schedule Q L) m X (.thread g)

def Prog.Async (Q : Params) (L : Launch) (m : Mem0) (os : List Descent.Obligation) : Prop :=
  SafeGoal kernel Assumptions.all L m → ∀ X, Maximal L kernel Assumptions.all m X →
    Follow Q L X → ∀ o ∈ os, Descent.Obl L X o → Sched.Steps (schedule Q L) m X o

end PTX.Kernels.InklingRelDecode.Proof.Top
