-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.AsyncSrc
public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Defs
import Kernels.TmlFa4Fwd.Proof.Lib.Guarded
import Kernels.TmlFa4Fwd.Proof.Lib.MmaLayout
import Kernels.TmlFa4Fwd.Proof.Protocol.Operands
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Stores
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.CopySource
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.AApart
import Kernels.TmlFa4Fwd.Proof.Top.Prog.AsyncTmem
import Kernels.TmlFa4Fwd.Proof.Top.Released
import Kernels.TmlFa4Fwd.Proof.Top.Safety

@[expose] public section

/-! # The asynchronous obligations step

`Prog.async` proves this progress class, given safety (`SafeGoal`, rule P3: progress reads
safety only through it).

`async_steps` steps every obligation from the operations' sources. The TMA copies' sources are the
launch's (`tensorSources`, `noInputWrite`), the row copies read K/V elements (`cpInputs`), the MMA
operands' and the output stores' bytes have visible writes (`operandVisible`, `storeSources`), the
MMAs' Tensor Memory operands are apart from their accumulators (`aTmemApart`), synchronization is
guarded by safety, and the Tensor Memory resources drain (`tmem_obl_steps`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0}

/-- **The asynchronous obligations step**, for every consistent execution. -/
theorem Prog.async (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m) :
    ∀ X o, Maximal L kernel Assumptions.all m X → (∀ g, o ≠ .thread g) →
      Descent.Obl L X o → StepsAt p L m X o := by
  intro X o hmax hth ho
  have hX := hmax.1
  have hFw := launchFollow hp hX
  have hIn := inputsUnwritten hp (noInputWrite hp hX hFw)
  exact async_steps hp hmax hFw (guardedOfTmaSafe hX (noTma_of_safe hs hX))
    { tensor := tensorSources hp hX hFw hIn
      cp := cpSources hX hIn (cpInputs hp (cpSrc hp hX hFw))
      mma := operandVisible hp hX hFw hIn
      apart := aTmemApart hp hX hFw
      layout := Mma.actualMmaLayoutInjective hX
      store := storeSources hp hX hFw } (tmem_obl_steps hp hs hmax) o hth ho

end PTX.Kernels.TmlFa4Fwd.Proof.Top
