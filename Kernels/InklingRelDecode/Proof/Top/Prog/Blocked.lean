-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Prog.Classes
import Kernels.InklingRelDecode.Proof.Top.Prog.TmemBlocked
import Kernels.InklingRelDecode.Proof.Top.Prog.BarSteps
import Kernels.InklingRelDecode.Proof.Top.Prog.CollSteps
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Kernels.InklingRelDecode.Proof.Common.Export.RegBand
import Kernels.InklingRelDecode.Proof.Lib.StaticCode
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Lemmas.Flow.NotAsyncWait
import Lemmas.Flow.NotClc

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX PTX.Flow PTX.Sched

private theorem async_free : kernel.code.all (fun i => !asyncWaitOp i.op) = true := by
  decide +kernel

private theorem bulk_free : kernel.code.all (fun i => !bulkWaitOp i.op) = true := by
  decide +kernel

/-- Only four kinds of recorded last event can block a pending Inkling thread. -/
public theorem Prog.blocked_kind {Q L m X g} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (pending : Frame.Pending L X g)
    (blocked : ¬ Step.Released L X g) :
    RegWait L X g ∨ TmemWait L X g ∨ BarWait L X g ∨ TcWait L X g := by
  have hw : ∀ pc n, X.get (g,(X.tr g).length-1) ≠ some ⟨pc,.asyncWait n⟩ := fun _ n he =>
    no_kind_of_code hX asyncWaitOp (fun k => ∃ n, k = .asyncWait n)
      (fun _ ⟨_,h⟩ => by cases h) (fun hf ⟨_,hk⟩ => fires_asyncWait_op hf hk)
      async_free he ⟨n,rfl⟩
  rcases thread_cases hX pending.1 hw blocked with h | h | h | h | h | h | h
  · obtain ⟨_,_,he,_⟩ := h
    exact (Lib.noClusterEvent hX he).elim
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))
  · obtain ⟨_,_,_,he,_⟩ := h
    cases (Lib.recorded_bar hX hp.block he).1
  · obtain ⟨_,mode,n,he,_⟩ := h
    exact (no_kind_of_code hX bulkWaitOp (fun k => ∃ mode n, k = .bulkWait mode n)
      (fun _ ⟨_,_,h⟩ => by cases h) (fun hf ⟨_,_,hk⟩ => fires_bulkWait_op hf hk)
      bulk_free he ⟨mode,n,rfl⟩).elim

/-- **A lane blocked at a register request, a Tensor Memory resource operation, a named barrier
or a collective `tcgen05` event steps.** -/
public theorem Prog.named {Q L m} (hp : Pre Q L m) : Prog.Named Q L m := by
  intro hs X hm hf g hpd hrel hw
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hm.1 h
  rcases hw with hw | hw | hw | hw
  · exact reg_steps hp hs hm hf words hpd hrel hw
  · exact Prog.tmem_steps hp hs hm hf hpd hrel hw
  · exact Prog.bar_steps hp hs hm hf words hpd hrel hw
  · exact Prog.tc_steps hp hs hm hf hpd hrel hw

end PTX.Kernels.InklingRelDecode.Proof.Top
