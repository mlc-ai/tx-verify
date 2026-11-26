-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictF
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part002

@[expose] public section

/-! # Warpgroup 0's strict segment after the sink's load

`sinkSegS`: from the control facts at pc 158 to the site after the sink (`afterSink`): the batch
test, then the first length's load or parameter. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m : Mem0}

set_option hygiene false in
local macro "ldp_at " c:term:max ty:term:max off:term:max d:term:max n:term:max x:term:max :
    tactic => `(tactic| (
  refine ldp_ex (ty := $ty) (off := $off) (d := $d) (n := $n) (x := $x) hp $c (by decide)
    (by decide) (by decide) (by simp [p0fields])
    (by repeat (first | exact mem_factsFrom_eq (by decide +kernel) rfl |
      apply List.mem_cons_of_mem))
    (by simp only [List.map_cons, factsFrom_keys]; decide +kernel) ?_))

theorem sinkSegS (hp : Pre P L m) (d : D) :
    ∃ n, Seg kernel Assumptions.all L g n 158 (factsFrom (ctlLive 158) (valueOf P L g w d))
      ((code P L g w).pc (afterSink P L g w d)) ((code P L g w).facts (afterSink P L g w d)) := by
  ldp_at Flow.code_158 (.int .b 32) 0 933 4 P.b
  refine Seg.comp_ex (q := 160) (H := factsFrom (ctlLive 160) (valueOf P L g w d))
    (by seg_sym using w0_segS) ?_
  cases h1 : scmp .ge .s (r2W L g) (pw P.b)
  · refine Seg.pred_ex (p := 71) (c := scmp .ge .s (r2W L g) (pw P.b)) (c' := false)
      (mem_factsFrom_eq (by decide +kernel) rfl) h1 ?_
    refine Seg.comp_ex (q := 163) (H := factsFrom (ctlLive 163) (valueOf P L g w d))
      (by seg_sym using w0_segS) ?_
    ldp_at Flow.code_163 (.int .b 64) 80 3002 8 (P.topkLenBase.getD 0)
    refine Seg.comp_ex (q := 165) (H := factsFrom (ctlLive 165) (valueOf P L g w d))
      (by seg_sym using w0_segS) ?_
    cases h2 : eqz64 (pw8 (P.topkLenBase.getD 0))
    · rw [show afterSink P L g w d = { d with site := .lenA } by
        simp only [afterSink, h1, h2, Bool.false_eq_true, ↓reduceIte]]
      refine Seg.pred_ex (p := 72) (c := eqz64 (pw8 (P.topkLenBase.getD 0))) (c' := false)
        (mem_factsFrom_eq (by decide +kernel) rfl) h2 ?_
      dsimp only [code, facts, Site.pc]
      seg_sym using w0_segS
    · rw [show afterSink P L g w d = afterA P { d with l0 := pw P.topk } by
        simp only [afterSink, h1, h2, Bool.false_eq_true, ↓reduceIte]]
      refine Seg.pred_ex (p := 72) (c := eqz64 (pw8 (P.topkLenBase.getD 0))) (c' := true)
        (mem_factsFrom_eq (by decide +kernel) rfl) h2 ?_
      refine Seg.comp_ex (q := 170) (H := factsFrom (ctlLive 170) (valueOf P L g w d))
        (by seg_sym using w0_segS) ?_
      ldp_at Flow.code_170 (.int .b 32) 40 2881 4 P.topk
      refine Seg.comp_ex (q := 176)
        (H := factsFrom (ctlLive 176) (valueOf P L g w { d with l0 := pw P.topk }))
        (by seg_sym using w0_segS) ?_
      exact lenA_succ hp d (pw P.topk)
  · rw [show afterSink P L g w d = finish w d by simp only [afterSink, h1, ↓reduceIte]]
    refine Seg.pred_ex (p := 71) (c := scmp .ge .s (r2W L g) (pw P.b)) (c' := true)
      (mem_factsFrom_eq (by decide +kernel) rfl) h1 ?_
    cases hw : scmpi .ne .b w 0
    · simp only [finish, hw, Bool.false_eq_true, ↓reduceIte]
      dsimp only [code, facts, Site.pc]
      seg_sym using w0_segS
    · simp only [finish, hw, ↓reduceIte]
      dsimp only [code, facts, Site.pc]
      seg_sym using w0_segS

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
