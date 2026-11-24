-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Program
public import Core.Assembly.Correctness
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed
open PTX

private def launchFields (k : Kernel) :=
  (k.maxThreads, k.reqThreads, k.ptrParams.isEmpty)

private theorem header_fields {m : Except String Decode.Prepared} {k : Kernel}
    (h : Transfers.finish m = .ok k) :
    m.toOption.map (fun p => launchFields p.header) = some (launchFields k) := by
  cases m with
  | error e => cases h
  | ok p =>
    cases d : Decode.code p.env 0 p.instrs with
    | error e => simp [Transfers.finish,bind,Except.bind,d] at h
    | ok ys =>
      simp [Transfers.finish,bind,Except.bind,d,pure,Except.pure] at h
      cases h
      rfl

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem launch_fields : launchFields kernel = (some 192, none, true) := by
  have h := header_fields (m := prepared) (k := kernel) decode_eq
  have header : prepared.toOption.map (fun p => launchFields p.header) =
      some (some 192,none,true) := by kernel_rfl
  exact Option.some.inj (h.symm.trans header)

theorem valid_launch (L : Launch) (grid : L.clusterGridValid) (block : L.block = 192) :
    L.Valid kernel := by
  have h := launch_fields
  simp only [launchFields,Prod.mk.injEq] at h
  obtain ⟨maxThreads,req,noPtrs⟩ := h
  refine ⟨grid,?_,?_,?_⟩
  · intro n hn
    rw [maxThreads] at hn
    cases hn
    exact block.le
  · intro s hs
    rw [req] at hs
    cases hs
  · intro name p v member _
    have hp : kernel.ptrParams = [] := List.isEmpty_iff.mp noPtrs
    simp [hp] at member

end FlashKda.Packed
