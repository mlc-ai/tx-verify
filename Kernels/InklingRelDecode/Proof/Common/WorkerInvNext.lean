-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Roles
import Kernels.InklingRelDecode.Proof.Dispatch.InvNext
import Kernels.InklingRelDecode.Proof.Loader.InvNext
import Kernels.InklingRelDecode.Proof.Mma.InvNext

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow

private theorem enter_worker_inv {Q L g w x} (d : Dispatch.D)
    (ok : d.site=.exitDealloc → g%L.block<32) :
    (workerCode Q L g w x).inv (Code.enter (Dispatch.code L g (startRegs Q L g w x) x 0)
      (workerFrag Q L g w x) workerEntry d) := by
  obtain ⟨s,r⟩ := d
  cases s <;> first | exact ⟨ok,rfl⟩ | exact ⟨rfl,rfl⟩ | exact ⟨nofun,rfl⟩

private theorem return_worker_inv {Q L g w x i} (d : (workerFrag Q L g w x i).D)
    (ok : (workerFrag Q L g w x i).inv d) :
    (workerCode Q L g w x).inv (Code.backEnter (Dispatch.code L g (startRegs Q L g w x) x 0)
      (workerFrag Q L g w x) workerEntry (workerBack Q L g w x) i d) := by
  cases i <;> obtain ⟨s,rest⟩ := d <;> cases s <;> first | exact ⟨ok,rfl⟩ | exact ⟨nofun,rfl⟩

theorem worker_inv_next {Q L g w x d dn ev} (hi : (workerCode Q L g w x).inv d)
    (move : (workerCode Q L g w x).next d ev=some (some dn)) : (workerCode Q L g w x).inv dn := by
  rcases d with d|⟨i,d⟩
  · change (Dispatch.next L g d ev).map _ = _ at move
    obtain ⟨_,step,h⟩ := Option.map_eq_some_iff.mp move
    obtain ⟨sn,rfl,rfl⟩ := Option.map_eq_some_iff.mp h
    exact enter_worker_inv _ (Dispatch.inv_next step)
  · change ((workerFrag Q L g w x i).next d ev).map _ = _ at move
    obtain ⟨_,step,h⟩ := Option.map_eq_some_iff.mp move
    obtain ⟨sn,rfl,rfl⟩ := Option.map_eq_some_iff.mp h
    apply return_worker_inv
    cases i with
    | loader => exact Loader.inv_next step
    | mma => exact Mma.inv_next hi.1 step

end PTX.Kernels.InklingRelDecode.Proof
