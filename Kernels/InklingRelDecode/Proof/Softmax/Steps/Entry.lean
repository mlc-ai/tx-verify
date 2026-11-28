-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.LastPre
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.PreAddress
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.PreGate
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.PrePointers
import Kernels.InklingRelDecode.Flow.Code.Part008

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
variable {e : Entry} {L : Launch} {g : Nat} {v : Carry}
local notation "tid" => g % L.block
local notation "F" => facts e L g (D.mk Softmax.Site.bar0 0 v)

private theorem setup (ok : e.Ok) (thread : tid < 256) :
    SegU kernel Assumptions.all L g 576 (F 575) 680 (F 680) :=
  (pre_index thread ok).comp ((pre_address ok).comp ((pre_gate ok).comp pre_pointers))

theorem step_bar0 {i} : (code e L g).StepAtU ⟨.bar0,i,v⟩ := by
  apply step_of_inv
  intro hi
  have eq := hi.init (.inr rfl)
  change i = 0 at eq
  subst i
  by_cases en : preEnabled e tid
  · have hInv : Inv e tid ⟨.pre 0,0,v⟩ :=
      ⟨hi.entry,hi.thread,hi.bound,fun _ => rfl,fun _ _ => ⟨rfl,en⟩,fun _ => nofun,nofun,
        fun _ _ _ h => (h _ rfl).elim⟩
    apply Code.advanceU (C := code e L g) (d := ⟨.bar0,0,v⟩) (dn := ⟨.pre 0,0,v⟩)
      Flow.code_575 rfl (fun hf => Option.some.inj hf.2) (fun _ => by simp [next,en])
      rfl rfl rfl rfl hInv
    exact setup hi.entry hi.thread
  · let z := loopSite e tid 0
    have hInv : Inv e tid ⟨z,0,v⟩ := loop_inv hi.entry hi.thread (Nat.zero_le _)
    apply Code.advanceU (C := code e L g) (d := ⟨.bar0,0,v⟩) (dn := ⟨z,0,v⟩)
      Flow.code_575 rfl (fun hf => Option.some.inj hf.2) (fun _ => by simp [next,en,z])
      rfl rfl rfl rfl hInv
    apply (setup hi.entry hi.thread).comp
    apply (Bias.skip_all (e := e) (L := L) (g := g) (i := 0) (v := v) .pre
      (congrArg Value.pred (Bool.eq_false_iff.mpr en))).comp
    exact (after_pre hi.entry hi.thread).comp (loop_route hi.entry (Nat.zero_le _))

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
