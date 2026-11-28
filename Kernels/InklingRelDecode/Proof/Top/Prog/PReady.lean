-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.InklingRelDecode.Proof.Top.Prog.WaitStep
public import Kernels.InklingRelDecode.Proof.Top.Prog.Classes
import Kernels.InklingRelDecode.Proof.Top.Prog.PObserve
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX Protocol

theorem Prog.pReady {Q L m} (hp : Pre Q L m)
    (followed : ∀ Y, Consistent L kernel Assumptions.all m Y → Follow Q L Y) :
    Prog.Poll Q L m 2510 := by
  rintro hs X hm hf g hg hr ⟨l,q,sc,hn⟩
  have hu := Sched.safe_noUb (hs.2 X hm.1)
  apply Export.mma_wait_step hp hm hu hf hg hr (Or.inr rfl) hn
  apply P.wait_blk hp hm.1 hu followed (fun Y hY => mbarRows_of hp hY (followed Y hY))
    (initRows_of hp hm.1 hf) (fun he => Shared.role_bytes hp hm.1 he) _ hn
  intro r hr
  cases fault : r.fault with
  | none => rfl
  | some f =>
    exact (hs.2 X hm.1
      (.inr (.inr (.inr (.inr (.inr (.inl (.inl ⟨l,r,hr,by simp [fault]⟩)))))))).elim

end PTX.Kernels.InklingRelDecode.Proof.Top
