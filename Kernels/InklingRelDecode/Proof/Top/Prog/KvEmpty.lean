-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.InklingRelDecode.Proof.Top.Prog.WaitStep
public import Kernels.InklingRelDecode.Proof.Top.Prog.Classes
import Kernels.InklingRelDecode.Proof.Top.Prog.EmptyBlk
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX Protocol

theorem Prog.kvEmpty {Q L m} (hp : Pre Q L m)
    (followed : ∀ Y, Consistent L kernel Assumptions.all m Y → Follow Q L Y) :
    Prog.Poll Q L m 2374 := by
  rintro hs X hmax hf g hg hr ⟨l,q,sc,hn⟩
  have hX := hmax.1
  have hu := Sched.safe_noUb (hs.2 X hX)
  apply Export.loader_wait_step hp hmax hu hf hg hr hn
  exact KV.empty_blk hp hX hu hf (fun Y hY => mbarRows_of hp hY (followed Y hY))
    (initRows_of hp hX hf)
    (KV.wonCommit hp hX hf) (fun get => Shared.role_bytes hp hX get) hn

end PTX.Kernels.InklingRelDecode.Proof.Top
