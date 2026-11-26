-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictF
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part018

@[expose] public section

/-! # Warpgroup 0's strict segments of the row guard (pcs 1159-1161)

From the control facts after the row-sum read: the head bound's parameter load, the comparison and
the branch, to the LSE computation (pc 1162) or over it (pc 1179). -/

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

/-- The row is inside the heads: the stretch falls through to pc 1162. -/
theorem eldSegSF (hp : Pre P L m) (d : D) (h : scmp .ge .s (r5W L g) (pw 64) = false) :
    ∃ n, Seg kernel Assumptions.all L g n 1159 (factsFrom (ctlLive 1159) (valueOf P L g w d))
      1162 (factsFrom (ctlLive 1162) (valueOf P L g w d)) := by
  ldp_at Flow.code_1159 (.int .b 32) 8 1729 4 64
  refine Seg.comp_ex (q := 1161) (H := factsFrom (ctlLive 1161) (valueOf P L g w d))
    (by seg_sym using w0_segS) ?_
  refine Seg.pred_ex (p := 118) (c := scmp .ge .s (r5W L g) (pw 64)) (c' := false)
    (mem_factsFrom_eq (by decide +kernel) rfl) h ?_
  seg_sym using w0_segS

/-- The row is beyond the heads: the stretch jumps to pc 1179. -/
theorem eldSegST (hp : Pre P L m) (d : D) (h : scmp .ge .s (r5W L g) (pw 64) = true) :
    ∃ n, Seg kernel Assumptions.all L g n 1159 (factsFrom (ctlLive 1159) (valueOf P L g w d))
      1179 (factsFrom (ctlLive 1179) (valueOf P L g w d)) := by
  ldp_at Flow.code_1159 (.int .b 32) 8 1729 4 64
  refine Seg.comp_ex (q := 1161) (H := factsFrom (ctlLive 1161) (valueOf P L g w d))
    (by seg_sym using w0_segS) ?_
  refine Seg.pred_ex (p := 118) (c := scmp .ge .s (r5W L g) (pw 64)) (c' := true)
    (mem_factsFrom_eq (by decide +kernel) rfl) h ?_
  seg_sym using w0_segS

/-- The stretch after the logarithm's run, to the LSE store (pc 1178). -/
theorem lseSegS (hp : Pre P L m) (d : D) :
    ∃ n, Seg kernel Assumptions.all L g n 1167 (factsFrom (ctlLive 1167) (valueOf P L g w d))
      1178 (factsFrom (ctlLive 1178) (valueOf P L g w d)) := by
  ldp_at Flow.code_1167 (.int .b 64) 96 3566 8 P.lseBase
  refine Seg.comp_ex (q := 1169) (H := factsFrom (ctlLive 1169) (valueOf P L g w d))
    (by seg_sym using w0_segS) ?_
  ldp_at Flow.code_1169 (.int .b 32) 180 1734 4 (P.s_q * 64)
  refine Seg.comp_ex (q := 1171) (H := factsFrom (ctlLive 1171) (valueOf P L g w d))
    (by seg_sym using w0_segS) ?_
  ldp_at Flow.code_1171 (.int .b 32) 184 1735 4 64
  seg_sym using w0_segS

/-- The stretch over the LSE computation, to the poll (pc 1184). -/
theorem wsvSegS (d : D) :
    ∃ n, Seg kernel Assumptions.all L g n 1179 (factsFrom (ctlLive 1179) (valueOf P L g w d))
      1184 (factsFrom (ctlLive 1184) (valueOf P L g w d)) := by
  seg_sym using w0_segS

/-- The grid-dependency instruction (pc 1188) keeps the control facts. -/
theorem gridSegS (d : D) :
    ∃ n, Seg kernel Assumptions.all L g n 1188 (factsFrom (ctlLive 1188) (valueOf P L g w d))
      1189 (factsFrom (ctlLive 1189) (valueOf P L g w d)) := by
  seg_sym using w0_segS

/-- The descriptor address (pc 1197, under `Pre`) and the staging test (pc 1198), up to the pair
move (pc 1199). -/
theorem facSegS (hp : Pre P L m) (d : D) :
    ∃ n, Seg kernel Assumptions.all L g n 1197 (factsFrom (ctlLive 1197) (valueOf P L g w d))
      1199 (factsFrom (ctlLive 1199) (valueOf P L g w d)) := by
  refine Seg.comp_ex (q := 1198) ⟨1, fun t ht => ⟨_, run_paramAdd (pc := 1197) (k := 512)
    Flow.code_1197 ht (by decide) (holds_mem (atHolds ht) (mem_factsFrom_eq
      (by decide +kernel) rfl)) hp.param1Object (by decide),
    At.set ht (fresh_live (by decide +kernel))⟩⟩ ?_
  seg_sym using w0_segS

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
