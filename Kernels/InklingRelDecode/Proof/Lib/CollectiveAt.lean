-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Flow.ElectMask
public import Lemmas.Flow.NotShfl
public import Lemmas.Order.ElectOrdinal

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

noncomputable def canElect (pc : Nat) := kernel.code[pc]?.any (fun ins => electOp ins.op)
noncomputable def canShuffle (pc : Nat) := kernel.code[pc]?.any (fun ins => ins.op.isShfl)

structure CollectiveAt (pc : Nat) (ev : Event) : Prop where
  pc_eq : ev.pc=pc
  election : canElect pc=false → isElectEv ev=false
  shuffle : canShuffle pc=false → Execution.isShfl ev=false

theorem collective_at {L g pc t ins ev o} (fetch : kernel.code[pc]?=some ins)
    (fire : Fires pc (eventTmpl Assumptions.all L g t ins.op) ev o) : CollectiveAt pc ev := by
  refine ⟨EventFrame.fires_source_pc fire,?_,?_⟩
  · intro off
    simp only [canElect,fetch,Option.any_some] at off
    obtain ⟨p,k⟩ := ev
    cases k <;> try rfl
    exact False.elim (fires_notElect (eventTmpl_notElect off) fire _ _ _ rfl)
  · intro off
    simp only [canShuffle,fetch,Option.any_some] at off
    cases yes : Execution.isShfl ev
    · rfl
    · exact Bool.noConfusion (off.symm.trans (fires_shfl_op fire yes))

end PTX.Kernels.InklingRelDecode.Proof.Lib
