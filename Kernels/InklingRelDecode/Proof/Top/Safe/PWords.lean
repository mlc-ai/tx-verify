-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Top.Safe.NoTmemInstruction
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows
public import Lemmas.Flow.OutKinds
public import Kernels.InklingRelDecode.Proof.Iface.PWords
public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.InitFirst
import Kernels.InklingRelDecode.Proof.Top.Safe.ValEnv
import Kernels.InklingRelDecode.Proof.Protocol.Values.LdsWord
import Kernels.InklingRelDecode.Proof.Protocol.Alpha.RoundNi
import Kernels.InklingRelDecode.Proof.Softmax.Export.PWordsAt

@[expose] public section

/-! # The probability store writes numbers -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX Protocol.Values

variable {Q : Params} {L : Launch} {m : Mem0}

/-- **Every word a score load returns is a number** (`ld_s_fl`). -/
theorem Safe.scoreWords (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hou : NoUbOutside L X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) :
    ∀ g k a vals sh, X.get (g, k) = some ⟨1265, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, Flow.SK.fl.Has x := fun g k a vals sh he => by
  obtain ⟨base, words, hG, hws, ht, hmd, form⟩ := Safe.valEnv hp hX hf safe rows init
  exact ld_s_fl hp hX hf hou safe base rows init hG hws ht hmd words nub form he

/-- **The probability store writes pairs of `bf16` numbers**: the score loads return numbers
(`ld_s_fl`), so the words the shuffles of pc 1838 send and bring are numbers or `-inf`
(`shfl5_ni`), and the value thread's pack of the exponentials is typed (`pword_event`). -/
theorem Safe.pWords (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hou : NoUbOutside L X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) : Iface.PWords X := by
  have hS := Safe.scoreWords hp hX hf hou safe rows init nub
  intro t sk a vals sh get
  exact Softmax.Export.pword_event hp hX hf (hS t)
    (fun lane k mode sent b c recv ok g1 => Protocol.Shared.shfl5_ni hp hX hf hS lane g1) get

end PTX.Kernels.InklingRelDecode.Proof.Top
