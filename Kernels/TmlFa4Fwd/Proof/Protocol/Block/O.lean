-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Channels
public import Kernels.TmlFa4Fwd.Proof.Protocol.O.Hist
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Who blocks a poll of a final O barrier

The stage's O barrier takes one commit. When its final phase is even (the parity of its only polls)
the stage's commit is not issued, or a commit's notification is undelivered (`o_blocked`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **O**: no commit to the stage's O barrier is issued, or one is undelivered. -/
theorem o_blocked (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (g : Nat) (st : Fin 2) {f : MBarrier.State}
    (hst : Final X (obj L g (oOff st)) f) (hpar : f.phase % 2 = 0) :
    (∀ i pc s rank, X.get i = some ⟨pc, .tc (.commit s)⟩ →
      TcCommit.target s rank ≠ some (obj L g (oOff st))) ∨ CommitOpen X := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨⟨z, jc⟩, pc, s, rank, he, ht⟩, hall⟩ := hcon
  have hn : rank ∈ X.tcNotified (z, jc) := hall _ _ _ _ ⟨pc, he⟩ ht
  have hc : z / L.block = g / L.block := (mma_commit_of hp hX hFw he ht).2.1
  have ht' : TcCommit.target s rank = some (obj L z (oOff st)) := by rw [obj_cta hc]; exact ht
  have H := o_hist hp hX hFw he ht'
  rw [obj_cta hc] at H
  have hact : objectAction X X.async (obj L g (oOff st)) (.async (z, jc) (.tcNotify rank)) =
      some (.arrive 1 0) := by
    simp [objectAction, he, ht, hn]
  obtain ⟨r, hr, hid, -⟩ := H.arrive_recorded hX (List.mem_singleton_self _) hact
  obtain ⟨s', hs', -, hiff⟩ := H.final_state hX (List.ne_nil_of_mem hr)
  have hfs : some f = some s' := hst.symm.trans hs'
  cases hfs
  have h1 := hiff.mpr ⟨fun a ha => by
    rw [List.mem_singleton] at ha
    subst ha
    exact ⟨r, hr, hid⟩, by simp⟩
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
