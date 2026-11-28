-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Adv
public import Lemmas.Flow.SegQFSat
import Kernels.InklingRelDecode.Gen.TypedLateLane02
import Kernels.InklingRelDecode.Gen.TypedLate02
import Kernels.InklingRelDecode.Flow.Code.Part019
import Kernels.InklingRelDecode.Flow.Code.Part034
import Kernels.InklingRelDecode.Flow.Code.Part035

@[expose] public section

/-! # The strict steps of the two polls of the softmax (pcs 1257 and 2239) -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

set_option maxRecDepth 100000

variable {e : Control.Entry} {L : Launch} {g i : Nat} {v : Control.Carry} {w : Data.Vals}

/-- The span after a poll that fails: the branch back to the poll, the facts kept. -/
theorem poll_fail {F : List (Nat × Value)} {pc p : Nat} {uni : Bool}
    (hc : kernel.code[pc]? = some ⟨some (p, true), .bra (pc - 1) uni⟩)
    (hp : (p, Value.pred false) ∈ F) (hS : Assumption.SegFreePc Assumptions.all pc)
    (hq : tagsSatF (lateQt (pc - 1)) (lateQt pc) = true) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) pc F (pc - 1) F :=
  SegQ.tauAll _ (SegQF.braNotS false hc (fun _ hR => holds_mem hR hp)
    (fun t _ ha => Lib.bra_rule t _ ha) hS hq)

/-- The span after a poll that succeeds: the branch falls through. -/
theorem poll_pass {F : List (Nat × Value)} {pc p target : Nat} {uni : Bool}
    (hc : kernel.code[pc]? = some ⟨some (p, true), .bra target uni⟩)
    (hp : (p, Value.pred true) ∈ F) (hS : Assumption.SegFreePc Assumptions.all pc)
    (hq : tagsSatF (lateQt (pc + 1)) (lateQt pc) = true) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) pc F (pc + 1) F :=
  SegQ.tauAll _ (SegQF.braNotS true hc (fun _ hR => holds_mem hR hp)
    (fun t _ ha => Lib.bra_rule t _ ha) hS hq)

theorem sstep_waitS (e0 : Control.Entry) (ev : Event) :
    (Data.code {e0 with base := b32 0} L g).StepForQP (QTF lateQt)
      (TauAll kernel Assumptions.all L g (LateR' L g)) LWf ⟨⟨.waitS, i, v⟩, w⟩ ev := by
  refine wait_soft (d := ⟨⟨.waitS, i, v⟩, w⟩)
    (dst := fun ok => ⟨⟨if ok then .shfl4 else .waitS, i, v⟩, w⟩) (p := 1257) rfl
    Flow.code_1257 ⟨?_, ?_⟩ (fun m q ok s => by cases ok <;> rfl)
    (fun ok h => by cases ok; exact h; exact Control.body_inv h rfl rfl) (by decide +kernel)
    (fun ok => ?_) ev
  · rw [factsFrom_keys]
    decide +kernel
  · change 2511 ∉ (Data.dFS L .waitS w).map Prod.fst
    rw [Data.dFS_keys]
    decide +kernel
  · cases ok
    · exact (poll_fail Flow.code_1258 (List.mem_cons_self ..) (segFree (by decide))
        (by decide +kernel)).comp (SegQ.weaken fun _ hR => holds_of_forall fun q hq =>
          holds_mem hR (List.mem_cons_of_mem _ hq))
    · refine (poll_pass Flow.code_1258 (List.mem_cons_self ..) (segFree (by decide))
        (by decide +kernel)).comp ?_
      change SegQ kernel Assumptions.all L g _ 1259
        ((2511, Value.pred true) :: (_ ++ factsFrom (Control.ctlLive 1257) _)) 1261
        (_ ++ factsFrom (Control.ctlLive 1261) _)
      refine SegQ.tauAll _ ?_
      refine SegQ.cut (m := 1260) ?_ ?_ <;> simp only [Data.dF, Data.dFS, Data.inRound,
        Bool.false_eq_true, ↓reduceIte, List.append_nil, List.cons_append, List.nil_append]
      · late_ctl 1259, 1260 using late_vals
      · late_ctl 1260, 1261 using late_vals

theorem sstep_waitO (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.waitO, i, v⟩, w⟩ ev := by
  refine wait_soft (d := ⟨⟨.waitO, i, v⟩, w⟩)
    (dst := fun ok => ⟨⟨if ok then .bar22 else .waitO, i, v⟩, w⟩) (p := 2239) rfl
    Flow.code_2239 ⟨?_, ?_⟩ (fun m q ok s => by cases ok <;> rfl)
    (fun ok h => by cases ok; exact h; exact Control.body_inv h rfl rfl) (by decide +kernel)
    (fun ok => ?_) ev
  · rw [factsFrom_keys]
    decide +kernel
  · change 2608 ∉ (Data.dFS L .waitO w).map Prod.fst
    rw [Data.dFS_keys]
    decide +kernel
  · cases ok
    · exact (poll_fail Flow.code_2240 (List.mem_cons_self ..) (segFree (by decide))
        (by decide +kernel)).comp (SegQ.weaken fun _ hR => holds_of_forall fun q hq =>
          holds_mem hR (List.mem_cons_of_mem _ hq))
    · exact (poll_pass Flow.code_2240 (List.mem_cons_self ..) (segFree (by decide))
        (by decide +kernel)).comp (SegQ.weaken fun _ hR => holds_of_forall fun q hq =>
          holds_mem hR (List.mem_cons_of_mem _
          (sub_facts (fun _ h => h) (by (try dsimp only); decide +kernel) q hq)))

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
