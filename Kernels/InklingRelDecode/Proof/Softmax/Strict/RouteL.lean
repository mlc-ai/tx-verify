-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Arrive
public import Lemmas.Flow.SegQFBraB
import Kernels.InklingRelDecode.Gen.TypedLateLane02
import Kernels.InklingRelDecode.Gen.TypedLateLane03
import Kernels.InklingRelDecode.Gen.TypedLateLane04
import Kernels.InklingRelDecode.Gen.TypedLate02
import Kernels.InklingRelDecode.Gen.TypedLate03
import Kernels.InklingRelDecode.Gen.TypedLate04
import Kernels.InklingRelDecode.Flow.Code
import Lemmas.Flow.DataElems
import Kernels.InklingRelDecode.Flow.Code.Part034
@[expose] public section
/-! # The strict step of the wait for the score tile: pcs 1299 to 1838

The control facts pass through the masks' two branches; each arm is a chain of lane windows. -/
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt
set_option maxRecDepth 100000
variable {e : Control.Entry} {L : Launch} {g : Nat}

/-- The span from pc `a` to the shuffle, one window after the other. -/
theorem wl_tail (w : Data.Vals) (V : Nat → Value) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 1756
      (LF L w 1838 V) 1838 (LF L w 1838 V) := by
  refine SegQ.comp (b := 1764) (G := LF L w 1838 V) ?_ ?_
  · win lw_l04_1756
  · win lw_l04_1764

/-- The span from the second mask's branch (pc 1466) to the shuffle. -/
theorem wl_b2 (w : Data.Vals) (V : Nat → Value) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 1466
      (LF L w 1838 V) 1838 (LF L w 1838 V) := by
  refine SegQF.braB (qt := lateQt) Flow.code_1466 (by decide +kernel)
    (fun t _ ha => Lib.bra_rule t _ ha) (segFree (by decide)) (by decide +kernel)
    (by decide +kernel) (SegQ.comp (b := 1764) (G := LF L w 1838 V) ?_ ?_)
    (SegQ.comp (b := 1756) (G := LF L w 1838 V) ?_ (wl_tail w V))
  · win lw_l04_1756
  · win lw_l04_1764
  · win lw_l04_1467

/-- The span from the first mask's branch target to the second mask's branch. -/
theorem wl_mid (w : Data.Vals) (V : Nat → Value) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 1303
      (LF L w 1838 V) 1466 (LF L w 1838 V) := by
  refine SegQ.comp (b := 1311) (G := LF L w 1838 V) ?_ ?_
  · winh lw_l02_1303
  refine SegQ.comp (b := 1319) (G := LF L w 1838 V) ?_ ?_
  · winh lw_l02_1311
  refine SegQ.comp (b := 1327) (G := LF L w 1838 V) ?_ ?_
  · winh lw_l02_1319
  refine SegQ.comp (b := 1335) (G := LF L w 1838 V) ?_ ?_
  · winh lw_l02_1327
  refine SegQ.comp (b := 1343) (G := LF L w 1838 V) ?_ ?_
  · winh lw_l02_1335
  refine SegQ.comp (b := 1351) (G := LF L w 1838 V) ?_ ?_
  · winh lw_l02_1343
  refine SegQ.comp (b := 1359) (G := LF L w 1838 V) ?_ ?_
  · winh lw_l02_1351
  refine SegQ.comp (b := 1367) (G := LF L w 1838 V) ?_ ?_
  · winh lw_l02_1359
  refine SegQ.comp (b := 1375) (G := LF L w 1838 V) ?_ ?_
  · winh lw_l02_1367
  refine SegQ.comp (b := 1383) (G := LF L w 1838 V) ?_ ?_
  · winh lw_l03_1375
  refine SegQ.comp (b := 1391) (G := LF L w 1838 V) ?_ ?_
  · winh lw_l03_1383
  refine SegQ.comp (b := 1399) (G := LF L w 1838 V) ?_ ?_
  · winh lw_l03_1391
  refine SegQ.comp (b := 1407) (G := LF L w 1838 V) ?_ ?_
  · winh lw_l03_1399
  refine SegQ.comp (b := 1415) (G := LF L w 1838 V) ?_ ?_
  · winh lw_l03_1407
  refine SegQ.comp (b := 1423) (G := LF L w 1838 V) ?_ ?_
  · winh lw_l03_1415
  winh lw_l03_1423

/-- **The wait for the score tile**: the control facts pass through the two masks. -/
theorem wl_span (w : Data.Vals) (V : Nat → Value) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 1299
      (LF L w 1838 V) 1838 (LF L w 1838 V) := by
  refine SegQ.comp (b := 1302) (G := LF L w 1838 V) ?_ ?_
  · win lw_l02_1299
  refine SegQF.braB (qt := lateQt) Flow.code_1302 (by decide +kernel)
    (fun t _ ha => Lib.bra_rule t _ ha) (segFree (by decide)) (by decide +kernel)
    (by decide +kernel) ?_ ((wl_mid w V).comp (wl_b2 w V))
  win lw_l04_1764

variable {i : Nat} {v : Control.Carry} {w : Data.Vals}

/-- **The wait for the score tile continues** at the first shuffle. -/
theorem sstep_waitLd (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.waitLd, i, v⟩, w⟩ ev := by
  apply adv_soft (d := ⟨⟨.waitLd, i, v⟩, w⟩) (dn := ⟨⟨.shfl5, i, v⟩, w⟩) (p := 1298) rfl
    Flow.code_1298 (fun _ => Code.fires_tcWaitLd_next)
    (fun ev => by obtain ⟨_, k⟩ := ev; cases k <;> rfl)
    (fun hi => Control.body_inv hi rfl rfl) (by decide +kernel) (by decide +kernel)
  exact SegQ.fromFacts (sub_facts (fun _ h => h) (by dsimp only; decide +kernel)) (wl_span w _)
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
