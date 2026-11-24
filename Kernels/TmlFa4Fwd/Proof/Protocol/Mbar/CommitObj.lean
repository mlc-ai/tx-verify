-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Obj
public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
public import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
public import Lemmas.Protocol.MbarCommitObj

@[expose] public section

/-! # A mbarrier object without a transaction

The ring's barriers are waited on and committed, never bound to a tensor operation: an object of
the ring whose uses are the waits of its consumers or the commits of the MMA warp's election, and
whose init count is one, has no transaction (`commitObj_unit_of`). Each barrier's offsets are then
a unit transaction, whatever the role that owns the barrier. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **A mbarrier object of the ring has no transaction**: its init count is one and each of its
uses is a wait or the commit of an election, so its history is a unit transaction without bytes. -/
theorem commitObj_unit_of (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {o : Nat} (hinit : ∃ q : Fin 34, initOff q = o ∧ initCnt q = 1)
    (hU : ∀ {h k : Nat} {e : Event}, X.get (h, k) = some e → MbarOf e (obj L g o) →
      (∀ c, e.kind ≠ .mbInit (obj L g o) c) →
      (∃ par ok acq sc, e.kind = .wait (obj L g o) par ok acq sc) ∨
        ∃ s, e.kind = .tc (.commit s) ∧ Prologue.warpIndex L h = 12 ∧ s.mbar = obj L g o ∧
          ∃ j pc' inst, X.get (h, j) = some ⟨pc', .elect (2 ^ 32 - 1) inst (laneOf L h)⟩) :
    MBarrier.UnitTx (X.objects (obj L g o)) 0 := by
  obtain ⟨q, hq, hc⟩ := hinit
  have hfirst : PairTmaRing.InitFirst X (obj L g o) 1 := by
    have := obj_initFirst hp hX hFw g q
    rwa [hq, hc] at this
  refine MbarRing.Blocker.commitObj_unitTx hX hfirst (fun {h i pc tx cnt rel sc} he => ?_)
    (fun {i pc a sp} he hm => ?_) (fun {i pc s} he hm => ?_) (fun {i pc m' noinc} he hm => ?_)
    (fun {i pc sp tg} he => no_clc hp hX hFw i.1 i.2 pc sp tg he)
    (fun {i pc m'} he => no_inval hp hX hFw i m' ⟨pc, he⟩)
  · rcases hU he rfl (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨_, hk, -⟩ <;> cases hk
  · rcases hU he hm (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨_, hk, -⟩ <;> cases hk
  · rcases hU he hm (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨_, hk, -⟩ <;> cases hk
  · subst hm
    rcases hU he rfl (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨_, hk, -⟩ <;> cases hk

end
end PTX.Kernels.TmlFa4Fwd.Proof
