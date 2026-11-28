-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Prog.Classes
import Kernels.InklingRelDecode.Proof.Lib.NoEvents

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

/-- The decoded kernel cannot issue these four asynchronous operations. -/
theorem Prog.other {Q L m} : Prog.Async Q L m [.bulk,.arriveOn,.clc,.store] := by
  intro _ X hm _ o member obligation
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact (obligation fun _ _ ⟨_,event⟩ => (Lib.no_copy hm.1 event).elim).elim
  · exact (obligation fun _ _ _ ⟨_,event⟩ => (Lib.no_asyncArrive hm.1 event).elim).elim
  · exact (obligation fun _ _ _ ⟨_,event⟩ => (Lib.no_clc hm.1 event).elim).elim
  · exact (obligation fun _ _ _ ⟨_,event⟩ => (Lib.no_tensorStore hm.1 event).elim).elim

end PTX.Kernels.InklingRelDecode.Proof.Top
