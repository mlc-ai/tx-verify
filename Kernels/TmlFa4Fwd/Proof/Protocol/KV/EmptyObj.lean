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

/-! # The K/V ring's empty barriers

The empty barriers of the K/V ring (shared offsets 56, 64, 72, count 1) are named only by polls
(the loader's) and the MMA warp's Tensor Core commits (`empty_use`), so each is an object
completed by commits alone (`emptyObj`: `UnitTx`, the library's `commitObj_unitTx`), whose
arrival units are its phase number (`commitObj_blocked`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The K/V ring's empty barriers. -/
abbrev EmptyOff (o : Nat) : Prop := o = 56 ∨ o = 64 ∨ o = 72

/-- **Who names an empty barrier**: a poll, or an MMA lane's commit. -/
theorem empty_use (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {h k o : Nat}
    {e : Event} (ho : EmptyOff o) (he : X.get (h, k) = some e) (hm : MbarOf e (obj L g o))
    (hni : ∀ c, e.kind ≠ .mbInit (obj L g o) c) :
    (∃ par ok acq sc, e.kind = .wait (obj L g o) par ok acq sc) ∨
      ∃ s, e.kind = .tc (.commit s) ∧ Prologue.warpIndex L h = 12 ∧ s.mbar = obj L g o ∧
        ∃ j pc' inst, X.get (h, j) = some ⟨pc', .elect (2 ^ 32 - 1) inst (laneOf L h)⟩ :=
  commit_use hp hX hFw (by omega) he hm hni

theorem empty_init {o : Nat} (ho : EmptyOff o) : ∃ q : Fin 34, initOff q = o ∧ initCnt q = 1 := by
  rcases ho with rfl | rfl | rfl
  · exact ⟨7, rfl, rfl⟩
  · exact ⟨8, rfl, rfl⟩
  · exact ⟨9, rfl, rfl⟩

set_option maxHeartbeats 8000000 in
/-- **An empty barrier is completed by commits alone**: a unit-transaction history without
bytes, whose arrival units are its phase number. -/
theorem emptyObj (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {o : Nat} (ho : EmptyOff o)
    (g : Nat) : MBarrier.UnitTx (X.objects (obj L g o)) 0 :=
  commitObj_unit_of hp hX hFw (empty_init ho)
    (fun he hm hni => empty_use hp hX hFw ho he hm hni)

end
end PTX.Kernels.TmlFa4Fwd.Proof
