-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Stable
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.QueryStart
public import Kernels.InklingRelDecode.Proof.Prologue.Data.QueryMove
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Step
public import Lemmas.Flow.SegQFH

@[expose] public section

/-! # The strict query entry: from the end of the copy tail to the first query site -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged PTX.Assumption Control Arith32

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

theorem qe_mov (c : Control.D) :
    SegQ kernel Assumptions.all L g (QT proQt) 386 ([(525, Data.scaleVal L)] ++ facts Q L g w c
        386) 388
      ([(198, Data.zeroV), (199, Data.zeroV), (525, Data.scaleVal L)] ++ facts Q L g w c 388) := by
  simp only [List.cons_append, List.nil_append]
  segq_ctlt proQt, (plainRules_pro (a := 27) (b := 574) le_rfl),
    (plainSegs_pro (a := 27) (b := 574) le_rfl), Lib.rulesFrame using pro_vals


/-- Facts at a later pc whose live control registers are among those of the earlier one. -/
theorem holds_ctl_mono {R : Nat → Option Value} {D : List (Nat × Value)} {c : Control.D}
    {pc pc' : Nat} (hl : (ctlLive pc').isSublist (ctlLive pc) = true) :
    Holds R (D ++ facts Q L g w c pc) → Holds R (D ++ facts Q L g w c pc') := by
  intro h
  rw [holds_append] at h ⊢
  exact ⟨h.1, holds_factsFrom_mono h.2 (List.isSublist_iff_sublist.mp hl).subset⟩

/-- **The grid-dependency wait** (pc 320) changes nothing. -/
theorem seg_grid (F : List (Nat × Value)) :
    SegQ kernel Assumptions.all L g (QT proQt) 320 F 321 F := by
  refine TyG.SegQ.local1 (A := Assumptions.all) Flow.code_320 rfl (fun _ h => h) fun t ht hq => ?_
  have hp : t.pc = 320 := ht.1
  have hn : execLocalA Assumptions.all L g t (.misc (.gridDep true)) = .ok (PTX.next t) := by
    rw [execLocalA_noSegment (fun a ha => plainSegs_pro (a := 27) (b := 574) le_rfl 320
      (by omega) (by omega) a ha L g t hp), execLocalRule_of_none (rules_none (by simp
          [FloatForm.ofOp]) (by simp [ApproxForm.ofOp])
      (Lib.other_rules_none (by omega) (by omega) (by omega) (by simp))) ]
    rfl
  refine ⟨PTX.next t, hn, by simp [PTX.next, hp], rfl, rfl, rfl, fun _ _ => rfl, fun _ => ?_⟩
  exact Code.QT.after (ws := []) hq (typed_nil') hp (by simp [PTX.next, hp]) (fun r tg h => by
      simp at h)
    (fun _ _ => rfl) (by decide +kernel)

/-- An old exact stretch of the control machine under the launch's scale fact, as a strict one. -/
macro "pro_bq" t:term : tactic => `(tactic|
  exact PTX.Flow.Havoc.SegQ.of_seg_pre (Dk := [525]) (fun p hp => by simp_all) Lib.rulesFrame $t
  rfl (by decide +kernel) (by decide +kernel)
  (PTX.Flow.Havoc.PlainSegs.mono (plainSegs_pro (a := 27) (b := 574) le_rfl) (by decide +kernel)
    (by decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem qe_sum (hw : w = b32 0) (c : Control.D) :
    SegQ kernel Assumptions.all L g (QT proQt) 319 ([(525, Data.scaleVal L)] ++ facts Q L g w c 319)
      320 ([(525, Data.scaleVal L)] ++ facts Q L g w c 320) := by
  subst hw
  simp only [List.cons_append, List.nil_append]
  segq_ctlt proQt, (plainRules_pro (a := 27) (b := 574) le_rfl),
    (plainSegs_pro (a := 27) (b := 574) le_rfl), Lib.rulesFrame using pro_vals

/-- **The entry**: from the end of the copy tail to the first query site, the zero halves of the
loads' registers made. -/
theorem qe_entry {m} (hp : Pre Q L m) (hw : w = b32 0) (c : Control.D) :
    SegQ kernel Assumptions.all L g (QT proQt) 316 ([(525, Data.scaleVal L)] ++ facts Q L g w c 316)
      388 ([(198, Data.zeroV), (199, Data.zeroV), (525, Data.scaleVal L)] ++ facts Q L g w c 388)
          := by
  refine SegQ.comp (b := 319) (G := [(525, Data.scaleVal L)] ++ facts Q L g w c 319) ?_
    ((qe_sum hw c).comp ((seg_grid _).comp (SegQ.comp (b := 321) (G := [(525, Data.scaleVal L)] ++
      facts Q L g w c 321) (SegQ.weaken fun R h => holds_ctl_mono (by decide +kernel) h) ?_)))
  · pro_bq (seg_query_params_pre hp)
  · refine SegQ.comp (b := 386) (G := [(525, Data.scaleVal L)] ++ facts Q L g w c 386) ?_ (qe_mov c)
    pro_bq (seg_col.comp (((seg_lanes0.comp seg_lanes1).comp seg_lanes2).comp seg_lanes3))

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
