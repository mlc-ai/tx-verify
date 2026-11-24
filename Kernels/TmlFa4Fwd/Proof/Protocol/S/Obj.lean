-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Start
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.CommitObj
public import Lemmas.Kernel.Safety.Classes
public import Lemmas.Protocol.MbarUnitTx
public import Lemmas.Tcgen05.TcFence
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Use
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Obj
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
import Lemmas.Protocol.MbarCommitObj
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The S-full barriers

The S-full barriers (shared offsets 80 and 88, count 1: the MMA warp's QK commits signal that a
stage's scores are written) are named only by polls (the stage's softmax lanes') and the MMA
warp's Tensor Core commits (`sfull_use`, the cases of T1's `empty_use`), so each is an object
completed by commits alone (`sfullObj`: `UnitTx`, the library's `commitObj_unitTx`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The S-full barriers. -/
abbrev SOff (o : Nat) : Prop := o = 80 ∨ o = 88

/-- **Who names an S-full barrier**: a poll, or an MMA lane's commit. -/
theorem sfull_use (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {h k o : Nat}
    {e : Event} (ho : SOff o) (he : X.get (h, k) = some e) (hm : MbarOf e (obj L g o))
    (hni : ∀ c, e.kind ≠ .mbInit (obj L g o) c) :
    (∃ par ok acq sc, e.kind = .wait (obj L g o) par ok acq sc) ∨
      ∃ s, e.kind = .tc (.commit s) ∧ Prologue.warpIndex L h = 12 ∧ s.mbar = obj L g o ∧
        ∃ j pc' inst, X.get (h, j) = some ⟨pc', .elect (2 ^ 32 - 1) inst (laneOf L h)⟩ :=
  commit_use hp hX hFw (by omega) he hm hni

theorem sfull_init {o : Nat} (ho : SOff o) : ∃ q : Fin 34, initOff q = o ∧ initCnt q = 1 := by
  rcases ho with rfl | rfl
  · exact ⟨10, rfl, rfl⟩
  · exact ⟨11, rfl, rfl⟩

set_option maxHeartbeats 8000000 in
/-- **An S-full barrier is completed by commits alone**: a unit-transaction history without
bytes. -/
theorem sfullObj (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {o : Nat} (ho : SOff o)
    (g : Nat) : MBarrier.UnitTx (X.objects (obj L g o)) 0 :=
  commitObj_unit_of hp hX hFw (sfull_init ho)
    (fun he hm hni => sfull_use hp hX hFw ho he hm hni)

end
end PTX.Kernels.TmlFa4Fwd.Proof
