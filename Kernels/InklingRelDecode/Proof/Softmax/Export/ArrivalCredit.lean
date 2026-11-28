-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.SoftmaxEvent

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow

/-- Before publishing P for block r, lane zero has consumed r outputs and r+1 scores. -/
public theorem arrival_polls {Q L m X g k l tx cnt rel sc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g,k)=some ⟨1013,.arrive l tx cnt rel sc⟩) :
    let es := (X.tr g).take k
    let n := es.countP (fun e : Event => e.pc==1013)
    pollRound 2239 es=n ∧ pollRound 1257 es=n+1 := by
  obtain ⟨_,⟨s,i,v⟩,_,_,_,_,inv,pc,_,_,ref⟩ := softmax_event hp hX hf get (fun _ => nofun)
    (by decide : 574<1013) (by decide : 1013<2331)
  have only (s : Site) : 1013=s.pc → s=.arrive := by
    cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
  obtain rfl := only s pc
  have lead := inv.lead rfl
  have p := congrArg Cnt.p ref.ledger
  have o := congrArg Cnt.o ref.ledger
  have score := congrArg Cnt.s ref.ledger
  change _ = (if g%L.block%128=0 then i else 0) at p
  simp only [lead,ite_true] at p
  dsimp only
  rw [p]
  exact ⟨o,score⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
