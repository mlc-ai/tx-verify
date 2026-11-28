-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.StepForBase
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Steps.Entry
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LdParam
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part040
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part041
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part056
import Lemmas.Flow.CtlStepsU
import Lemmas.Flow.IssueNext
import Lemmas.Flow.RoleTemplates
import Lemmas.Flow.Step.Combinators
import Kernels.FlashMlaSparseDecodeH64.Gen.StepDequant

@[expose] public section

/-! # Warpgroup 2's strict step at its `setmaxnreg` (pcs 2606-2630)

`stepAt_smrS`: the exact step obligation (`Code.StepAt`) at the `setmaxnreg`, for a state at
element 0. The walk to the successor (`smrSeg_*`) is exact: the five `ld.param` of `param_0` are
`seg_ldp` pieces under `Pre` (`ldp_ex`), the stretches between them `seg_sym` cut after each
group, and the tests on the parameters are decided by the case split's hypotheses (a literal
predicate through `Seg.pred_ex` where the symbolic decision is too slow). One lemma per
successor keeps each declaration small. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m : Mem0}

theorem ldp_ex (hp : Pre P L m) {pc d off x n b : Nat} {ty : DType} {F G : List (Nat × Value)}
    (hc : kernel.code[pc]? = some (ldpIns ty off d))
    (hty : (ty = .int .b 32 ∧ n = 4) ∨ (ty = .int .b 64 ∧ n = 8)) (hal : off % n = 0)
    (hoff : off + n ≤ 304) (hf : (off, x, n) ∈ p0fields P L)
    (h2991 : (2991, .ptr 64 false (.param (param "0")) 0) ∈ F) (hd : d ∉ F.map Prod.fst)
    (rest : ∃ k, Seg kernel Assumptions.all L g k (pc + 1)
      ((d, .bits (8 * n) (BitVec.ofNat 64 (leNat x 0 n))) :: F) b G) :
    ∃ k, Seg kernel Assumptions.all L g k pc F b G :=
  Seg.comp_ex ⟨1, seg_ldp hp hc hty hal hoff hf h2991
    fun _ hq he => hd (by rw [← he]; exact List.mem_map_of_mem hq)⟩ rest

set_option hygiene false in
local macro "ldp_at " c:term:max ty:term:max off:term:max d:term:max n:term:max x:term:max :
    tactic => `(tactic| (
  refine ldp_ex (ty := $ty) (off := $off) (d := $d) (n := $n) (x := $x) hp $c (by decide)
    (by decide) (by decide) (by simp [p0fields])
    (by repeat (first | exact mem_factsFrom_eq (by decide +kernel) rfl |
      apply List.mem_cons_of_mem))
    (by simp only [List.map_cons, factsFrom_keys]; decide +kernel) ?_))

set_option hygiene false in
local macro "cut_at " q:term:max : tactic => `(tactic| (
  refine Seg.comp_ex (q := $q) (H := factsFrom (ctlLive $q)
    (valueOf P L g ⟨.smr, 0, ac, pw P.topk, pw P.extra_topk, cnt, sb, pb⟩))
    (by seg_sym using dq_segS) ?_))

set_option hygiene false in
local macro "smr_pre" : tactic => `(tactic| (
  cut_at 2609
  ldp_at Flow.code_2609 (.int .b 32) 0 2429 4 P.b
  cut_at 2612))

set_option hygiene false in
local macro "smr_lens" : tactic => `(tactic| (
  ldp_at Flow.code_2612 (.int .b 64) 80 3017 8 (P.topkLenBase.getD 0)
  ldp_at Flow.code_2613 (.int .b 32) 40 2985 4 P.topk
  ldp_at Flow.code_2614 (.int .b 64) 144 3018 8 (P.extraTopkLenBase.getD 0)
  ldp_at Flow.code_2615 (.int .b 32) 120 2986 4 P.extra_topk))

/-- The set-up's walk to the first length load (pc 2607 to 2620). -/
theorem smrSeg_lenA (hp : Pre P L m) (ac : List Value) (l0 l1 cnt : BitVec 64) (sb pb : Bool)
    (h1 : scmp .ge .s (r2W L g) (pw P.b) = false)
    (h2 : eqz64 (pw8 (P.topkLenBase.getD 0)) = false) :
    ∃ n, Seg kernel Assumptions.all L g n (2606 + 1)
      (factsFrom (ctlLive 2606) (valueOf P L g ⟨.smr, 0, ac, l0, l1, cnt, sb, pb⟩)) 2620
      (factsFrom (ctlLive 2620)
        (valueOf P L g ⟨.lenA, 0, ac, pw P.topk, pw P.extra_topk, cnt, sb, pb⟩)) := by
  smr_pre; smr_lens
  cut_at 2617
  seg_sym using dq_segS

/-- To the second length load (pc 2630): the first pointer is null. -/
theorem smrSeg_lenB (hp : Pre P L m) (ac : List Value) (l0 l1 cnt : BitVec 64) (sb pb : Bool)
    (h1 : scmp .ge .s (r2W L g) (pw P.b) = false)
    (h2 : eqz64 (pw8 (P.topkLenBase.getD 0)) = true)
    (h3 : eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = false) :
    ∃ n, Seg kernel Assumptions.all L g n (2606 + 1)
      (factsFrom (ctlLive 2606) (valueOf P L g ⟨.smr, 0, ac, l0, l1, cnt, sb, pb⟩)) 2630
      (factsFrom (ctlLive 2630)
        (valueOf P L g ⟨.lenB, 0, ac, pw P.topk, pw P.extra_topk, cnt, sb, pb⟩)) := by
  smr_pre; smr_lens
  cut_at 2627
  refine Seg.pred_ex (p := 132) (c := eqz64 (pw8 (P.extraTopkLenBase.getD 0))) (c' := _)
    (mem_factsFrom_eq (show 132 ∈ ctlLive 2627 by decide +kernel) rfl) h3 ?_
  seg_sym using dq_segS

/-- To the Q poll (pc 2644): both pointers are null. -/
theorem smrSeg_wq (hp : Pre P L m) (ac : List Value) (l0 l1 cnt : BitVec 64) (sb pb : Bool)
    (h1 : scmp .ge .s (r2W L g) (pw P.b) = false)
    (h2 : eqz64 (pw8 (P.topkLenBase.getD 0)) = true)
    (h3 : eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = true) :
    ∃ n, Seg kernel Assumptions.all L g n (2606 + 1)
      (factsFrom (ctlLive 2606) (valueOf P L g ⟨.smr, 0, ac, l0, l1, cnt, sb, pb⟩)) 2644
      (factsFrom (ctlLive 2644)
        (valueOf P L g ⟨.wq, 0, ac, pw P.topk, pw P.extra_topk, cnt, sb, pb⟩)) := by
  smr_pre; smr_lens
  cut_at 2627
  refine Seg.pred_ex (p := 132) (c := eqz64 (pw8 (P.extraTopkLenBase.getD 0))) (c' := _)
    (mem_factsFrom_eq (show 132 ∈ ctlLive 2627 by decide +kernel) rfl) h3 ?_
  seg_sym using dq_segS

/-- To the return (pc 3611): the CTA is beyond the batch. -/
theorem smrSeg_exit (hp : Pre P L m) (ac : List Value) (l0 l1 cnt : BitVec 64) (sb pb : Bool)
    (h1 : scmp .ge .s (r2W L g) (pw P.b) = true) :
    ∃ n, Seg kernel Assumptions.all L g n (2606 + 1)
      (factsFrom (ctlLive 2606) (valueOf P L g ⟨.smr, 0, ac, l0, l1, cnt, sb, pb⟩)) 3611
      (factsFrom (ctlLive 3611)
        (valueOf P L g ⟨.exit, 0, ac, pw P.topk, pw P.extra_topk, cnt, sb, pb⟩)) := by
  cut_at 2609
  ldp_at Flow.code_2609 (.int .b 32) 0 2429 4 P.b
  seg_sym using dq_segS

set_option hygiene false in
local macro "smr_to " S:term:max " using " hs:Lean.Parser.Tactic.simpLemma,+ : tactic => `(tactic| (
  refine Code.StepAt.of (fun _ => ⟨_, Flow.code_2606, rfl, trivial⟩)
    (Code.step_issue (C := code P L g w)
      (dn := ⟨$S, 0, ac, pw P.topk, pw P.extra_topk, cnt, sb, pb⟩) Flow.code_2606
      (fun hf => fires_setMaxReg_next hf)
      (fun _ => by simp only [code, succ, afterSmr, afterA, $hs,*, Bool.false_eq_true,
        ↓reduceIte])
      rfl rfl ⟨fun _ => ?_, rfl, rfl, fun _ => Nat.one_pos⟩)
  dsimp only [code, facts, Site.pc, rowBase]))

theorem stepAt_smrS (hp : Pre P L m) (d : D) (hs : d.site = .smr) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  dq_state d
  simp only at hs he
  subst he hs
  cases h1 : scmp .ge .s (r2W L g) (pw P.b)
  · cases h2 : eqz64 (pw8 (P.topkLenBase.getD 0))
    · smr_to .lenA using h1, h2
      exact smrSeg_lenA hp ac l0 l1 cnt sb pb h1 h2
    · cases h3 : eqz64 (pw8 (P.extraTopkLenBase.getD 0))
      · smr_to .lenB using h1, h2, h3
        exact smrSeg_lenB hp ac l0 l1 cnt sb pb h1 h2 h3
      · smr_to .wq using h1, h2, h3
        exact smrSeg_wq hp ac l0 l1 cnt sb pb h1 h2 h3
  · smr_to .exit using h1
    exact smrSeg_exit hp ac l0 l1 cnt sb pb h1
end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
