-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Machine
import Kernels.TmlFa4Fwd.Proof.Correction.Control.LseSpan
import Kernels.TmlFa4Fwd.Flow.Code.Part141
import Lemmas.Flow.ArriveU
import Lemmas.Flow.StoreU

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Flow PTX.Proof

set_option maxRecDepth 100000

private theorem erase_ite (q : Bool) (x y : Correction.D) :
    erase (Correction.D.ite q x y) = if q then erase x else erase y := by cases q <;> rfl

private theorem late_zero {p L g v} : (lateD p L g v).k = 0 := by
  unfold lateD passStart
  simp only [↓reduceIte]
  rw [erase_ite]
  split <;> rfl

private theorem second_zero {p L g v} : (secondD p L g v).k = 0 := by
  unfold secondD
  split
  · exact late_zero
  · rfl

private theorem first_zero {p L g v} : (firstD p L g v).k = 0 := by
  unfold firstD
  split
  · exact second_zero
  · rfl

variable {p L m g} (hp : Pre p L m)
include hp

theorem stepAt_lseU (i : Fin 2) (v : V) : (code p L g).StepAtU ⟨.lse i,v,0⟩ := by
  fin_cases i
  · refine Code.scalarStoreU (dn := secondD p L g v) Flow.code_9073 rfl rfl rfl ?_
      rfl rfl (congrArg Fin.val second_zero) rfl (.inl second_zero) (second_span hp v)
    intro e
    change some (some (erase (afterLse p L g _ 0))) = _
    simp only [afterLse, erase_ite]
    rfl
  · exact Code.scalarStoreU (dn := lateD p L g v) Flow.code_9082 rfl rfl rfl (fun _ => rfl)
      rfl rfl (congrArg Fin.val late_zero) rfl (.inl late_zero) (late_entry hp v)

theorem stepAt_fdone_lseU (v : V) : (code p L g).StepAtU ⟨.fdone 1 1,v,0⟩ := by
  refine Code.arriveU (dn := firstD p L g v) Flow.code_9056 ?_ ?_ rfl rfl
    (congrArg Fin.val first_zero) rfl (.inl first_zero) (first_span hp v)
  · change 9521 ∉ (factsFrom (liveAt (.fdone 1 1)) _).map Prod.fst
    have keys {rs : List Nat} {val : Nat → Value} : (factsFrom rs val).map Prod.fst = rs := by
      simp only [factsFrom, List.map_map, Function.comp_def]
      exact List.map_id _
    rw [keys]
    decide +kernel
  · intro e
    change some (some (erase (afterFinal p L g _))) = _
    simp only [afterFinal, erase_ite]
    rfl

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
