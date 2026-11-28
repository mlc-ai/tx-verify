-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.SoftmaxEvent

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow

private theorem site_polls (s : Site) (h : s.pc=999 ∨ s.pc=1012 ∨ s.pc=2326) :
    s.afterS=true ∧ s.afterO=true := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- At the mandatory rendezvous after the score and output polls of a round, one more score
poll than output polls has succeeded. -/
public theorem bar_polls {Q L m X g k pc c} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g,k)=some ⟨pc,.bar 0 c .sync⟩) (site : pc=999 ∨ pc=1012 ∨ pc=2326) :
    pollRound 2239 ((X.tr g).take k)+1=pollRound 1257 ((X.tr g).take k) := by
  have lo : 574<pc := by omega
  have hi : pc<2331 := by omega
  obtain ⟨_,⟨s,i,v⟩,_,_,_,_,_,eq,_,_,ref⟩ := softmax_event hp hX hf get (fun _ => nofun) lo hi
  have a := congrArg Cnt.s ref.ledger
  have b := congrArg Cnt.o ref.ledger
  obtain ⟨as,ao⟩ := site_polls s (eq ▸ site)
  change pollRound 1257 _=i+s.afterS.toNat at a
  change pollRound 2239 _=(if s.afterO then i else i-1) at b
  rw [as] at a
  rw [ao] at b
  simp only [Bool.toNat_true,ite_true] at a b
  omega

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
