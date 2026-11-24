-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Ideal
import Kernels.TmlFa4Fwd.Proof.Lib.ScheduleCoords
import Kernels.TmlFa4Fwd.Proof.Epilogue.Assign
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Safe
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.Epilogue.Steps
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The output warp's tensor stores are no undefined behaviour

At a store site under the reference values (`Fits`), the store's operands are the CTA's work
item (`storeVals_eq`): the O map pointer, the policy word, the staging slot of the stage (aligned
to 128 bytes), and coordinate words whose origins are nonnegative and box-aligned (the old tree's
`Epilogue.storeOrigin`). So `tensorStoreSpec` returns a specification and the store's event is
the tensor store, not undefined behaviour (`store_safe`). With the reads (`Safe.lean`), no
event a state of the output warp fires under its reference values is undefined behaviour
(`fired_safe`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ent : Nat → Value}

set_option maxHeartbeats 4000000 in
/-- **A tensor store of the output warp under its reference values is no undefined
behaviour.** -/
theorem store_safe (hp : Pre p L m) (hg : g < L.threads) {d : D} {st : Fin 2} {b : Fin 4}
    (hs : d.site = .store st b) {ns nv : Nat} (hF : Fits p L g d ns nv) {e : Event}
    {o : Option TState} (hf : (code p L g ent).toMachine.Fired (some d) e o) (f : Fault) :
    e.kind ≠ .ub f := by
  obtain ⟨t, hfire, hptr, hpol, hshared, hcoords⟩ := store_reads hp hg hs hf
  obtain ⟨site, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  simp only at hs
  subst hs
  have hpolicy : cachePolicyRead L g t (some (.reg 7869)) = .ok () := by
    simp [cachePolicyRead, readBits, readReg, hpol, bind, Except.bind, pure, Except.pure]
  have h128 : (Epilogue.sharedSlot L g st b).addr % 128 = 0 := by
    have := hp.shared.1
    change (L.sharedBase + (3072 + 65536 * st.val + 16384 * b.val)) % 128 = 0
    omega
  obtain ⟨R, bal', hC, hc0, hc1⟩ := hF
  obtain ⟨bb, hb, hlo, hhi, hch, hco⟩ := chosen_spec hp hg hC
  have hbb := batch_lt hp
  simp only at hch hc0 hc1
  rw [hch, qv_W hp (by omega)] at hc0
  rw [hch, addi1_W (by omega), qv_W hp (by omega)] at hc1
  have hvals := storeVals_eq (st := st) (bx := b) hp hb hlo hhi (by rw [hco]) (by rw [hco])
    hc0 hc1
  obtain ⟨ht, hh⟩ := Epilogue.assignedCoordinates_valid hp hlo hhi
  rw [hvals] at hcoords
  have hOrigin := Epilogue.storeOrigin hp hb hh ht st b
  have hNonneg : ∀ axis : Fin 4, 0 ≤ (BitVec.ofNat 32 ((Epilogue.storeWords p bb
      (Epilogue.assignedCoordinates p bb (g / L.block)).2
      (Epilogue.assignedCoordinates p bb (g / L.block)).1 st b).getD axis.val 0).toNat).toInt := by
    have h := congrFun hOrigin
    intro axis
    rw [show (BitVec.ofNat 32 _).toInt = Epilogue.originOf _ axis from rfl, h axis]
    fin_cases axis <;> simp [PTX.Kernels.TmlFa4Fwd.oCoordinate]
    omega
  have hAligned : requireBoxAligned p.oMap (fun axis => (BitVec.ofNat 32 ((Epilogue.storeWords p
      bb (Epilogue.assignedCoordinates p bb (g / L.block)).2
      (Epilogue.assignedCoordinates p bb (g / L.block)).1 st b).getD axis.val 0).toNat).toInt) =
      .ok () := by
    refine (requireBoxAligned_eq_ok _ _).2 ?_
    show TensorDescriptor.BoxAligned p.oMap (Epilogue.originOf _)
    rw [hOrigin]
    simp [TensorDescriptor.BoxAligned, PTX.Kernels.TmlFa4Fwd.oCoordinate, Params.oMap,
      TensorDescriptor.Format.bytes]
    omega
  have hTensor := Epilogue.outputMapOperand hp g t (Epilogue.storeCoords st b) hptr rfl
  simp only [tensorStoreTmpl, Epilogue.storeOp, tensorStoreSpec, hTensor, hcoords, hshared, h128,
    hpolicy, bind, Except.bind, pure, Except.pure, Option.all_none, ↓reduceIte,
    TensorMode.transfer, TensorMode.rowCoordinates, hNonneg, forall_const, true_or, hAligned,
    ofExec, Fires] at hfire
  intro hk
  rw [hfire.1] at hk
  cases hk

/-- **No event a state of the output warp fires under its reference values is undefined
behaviour.** -/
theorem fired_safe (hp : Pre p L m) (hg : g < L.threads) {d : D} {ns nv : Nat}
    (hF : Fits p L g d ns nv) {e : Event} {o : Option TState}
    (hf : (code p L g ent).toMachine.Fired (some d) e o) (f : Fault) : e.kind ≠ .ub f := by
  by_cases hst : ∃ st b, d.site = .store st b
  · obtain ⟨st, b, hs⟩ := hst
    exact store_safe hp hg hs hF hf f
  · have hev := (Code.Shape.fired (shape hp) (stepAt hp hg) hf).1
    have hA := (Code.Shape.fired shapeA (stepAt hp hg) hf).1
    exact ref_safe hp hF hev hA (fun st b h => hst ⟨st, b, h⟩) f

end
end PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
