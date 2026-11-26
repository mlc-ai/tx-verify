-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Loop.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Loop.StepsPeer
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Loop.StepsRescale
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Loop.StepsSetup
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part004
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part005
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part009
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part011
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part017
import Lemmas.Flow.IssueNext

@[expose] public section

/-! # Warpgroup 0's obligations in the Loop half

`Wg0.Loop.stepAt`: every state at a site before the epilogue (`Site.inLoop`, pc < 1147) steps,
under `Pre`. -/

/-! # Warpgroup 0's obligations at the rescale vote and the P stores (pcs 578–710)

The rescale vote (`vote`, its result `%p1` and the negation `%p110` decide the branch at pc 581,
whose two arms meet before the first P store) and the four four-element P stores (`ost`); after
the last, the branch at pc 710 on `%p112` (`bi = 1 ∨ ¬vt`) to the proxy fence or the rescale arm. -/

/-! # Warpgroup 0's obligations at the head of a block (pcs 256–289)

The named barrier 9 (`bar0`), the polls of the valid-mask and QK barriers (`wv`, `wq`), the
`tcgen05` fence and the stage's branch to its score-load order (`tcfa`, pc 276 on `%p76`), the
two score loads in either order (`sld`), their wait and fence (`sldw`, `tcfb`), and the
valid-mask word (`vm`). -/

/-! # Warpgroup 0's obligation at the end of a block (pcs 1122–1154)

The arrival on the softmax-ready barrier (`arrS`), then the loop's advance: unless the block is
the last (`%p113`, `cnt = 0`, pc 1124) the two rings move on; the counters advance, and the
branch at pc 1146 on `%p117` (`cnt + 1 ≠ 1`) goes back to the next block's barrier (pc 253) or on
to the epilogue's first barrier (pc 1154). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Flow PTX.Proof PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

set_option hygiene false in
/-- A `selp` of two immediates on the symbolic predicate `c` held in register `r`: name the
predicate's fact, then each of its two values steps exactly. -/
local macro "w0_selp " r:term:max ", " c:term : tactic => `(tactic| (
  refine SegU.pick (r := $r) (x := .pred $c) (mem_factsFrom_eq (by decide +kernel) rfl) ?_
  generalize $c = b
  cases b <;> w0_seg))

/-- The rings' advance (pcs 1125–1145, taken when the block is not the last) carries the loop's
control facts to the branch at pc 1146. The three `selp`s of the parities (pcs 1130, 1133, 1136)
pick on a symbolic predicate: the stretch is cut before each and its predicate split (the wrap
test `%p116` is stated outside the value table, so that splitting `%p115` reaches it). -/
theorem ringSeg (a0 : Value) (l0 l1 cnt bi vs pv sl ps : BitVec 64) (vt : Bool) :
    SegU kernel Assumptions.all L g 1125
      (factsFrom (ctlLive 1124)
        (valueOf P L g w ⟨.arrS, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩))
      1146 (factsFrom (ctlLive 1146) (valueOf P L g w ⟨.bar0, 0, a0, l0, l1, addi cnt 1, addi bi 1,
        nvs vs, npv vs pv, andi (not32 sl) 1, nps sl ps, vt⟩)) := by
  refine SegU.comp (b := 1130) (G := factsFrom (ctlLive 1130)
    (valueOf P L g w ⟨.arrS, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩)) (by w0_seg) ?_
  refine SegU.comp (b := 1133) (G := factsFrom (ctlLive 1133)
    (valueOf P L g w ⟨.arrS, 0, a0, l0, l1, cnt, bi, vs, pv, andi (not32 sl) 1,
      sel (psc sl ps) (i16 1) (i16 0), vt⟩)) (by w0_selp 114, psc sl ps) ?_
  refine SegU.comp (b := 1136) (G := (116, .pred (pvc vs pv)) ::
    factsFrom ((ctlLive 1136).erase 116) (valueOf P L g w ⟨.arrS, 0, a0, l0, l1, cnt, bi, vs,
      pv, andi (not32 sl) 1, nps sl ps, vt⟩)) ?_ ?_
  · refine SegU.pick (r := 115) (x := .pred (scmpi .eq .b vs 3))
      (mem_factsFrom_eq (by decide +kernel) rfl) ?_
    dsimp only [pvc]
    generalize scmpi .eq .b vs 3 = b
    cases b <;> w0_seg
  dsimp only [npv]
  generalize pvc vs pv = b
  cases b <;> w0_seg

set_option hygiene false in
local macro "arr_step " dn:term:max " by " ring:tacticSeq : tactic => `(tactic| (
  refine Code.advanceU (C := code P L g w) (dn := $dn) Flow.code_1122 rfl
    (fun hf => Code.fires_arrive_next hf)
    (fun _ => by
      simp only [code, succ, advance, hz, hb, Bool.false_eq_true, ↓reduceIte]) rfl rfl rfl rfl
    (Nat.zero_lt_succ _) ?_
  refine SegU.comp (b := 1124) (G := factsFrom (ctlLive 1124)
    (valueOf P L g w ⟨.arrS, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩)) (by w0_seg) ?_
  refine SegU.pick (r := 113) (x := .pred (scmpi .eq .b cnt 0))
    (mem_factsFrom_eq (show 113 ∈ ctlLive 1124 by decide +kernel) rfl) ?_
  refine SegU.comp (SegU.branch _ Flow.code_1124 bra_rule noSegments.segFreePc) ?_
  rw [hz]
  refine SegU.comp (b := 1146) (G := factsFrom (ctlLive 1146) (valueOf P L g w $dn))
    (by $ring) ?_
  refine SegU.pick (r := 117) (x := .pred (scmpi .ne .b (addi cnt 1) 1))
    (mem_factsFrom_eq (show 117 ∈ ctlLive 1146 by decide +kernel) rfl) ?_
  refine SegU.comp (SegU.branch _ Flow.code_1146 bra_rule noSegments.segFreePc) ?_
  rw [hb]
  w0_seg))

/-- The softmax-ready arrival and the loop's advance. -/
theorem stepAt_arrS (d : D) (hs : d.site = .arrS) :
    (code P L g w).StepAtU d := by
  w0_site
  cases hz : scmpi .eq .b cnt 0 <;> cases hb : scmpi .ne .b (addi cnt 1) 1
  · arr_step ⟨.ebar0, 0, a0, l0, l1, addi cnt 1, addi bi 1, nvs vs, npv vs pv,
      andi (not32 sl) 1, nps sl ps, vt⟩ by exact ringSeg a0 l0 l1 cnt bi vs pv sl ps vt
  · arr_step ⟨.bar0, 0, a0, l0, l1, addi cnt 1, addi bi 1, nvs vs, npv vs pv,
      andi (not32 sl) 1, nps sl ps, vt⟩ by exact ringSeg a0 l0 l1 cnt bi vs pv sl ps vt
  · arr_step ⟨.ebar0, 0, a0, l0, l1, addi cnt 1, addi bi 1, vs, pv, sl, ps, vt⟩ by w0_seg
  · arr_step ⟨.bar0, 0, a0, l0, l1, addi cnt 1, addi bi 1, vs, pv, sl, ps, vt⟩ by w0_seg

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Flow PTX.Proof PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

theorem stepAt_bar0 (d : D) (hs : d.site = .bar0) : (code P L g w).StepAtU d := by
  w0_site
  w0_adv Flow.code_256 by exact fires_barSyncN_next hf
  w0_seg

theorem stepAt_wv (d : D) (hs : d.site = .wv) : (code P L g w).StepAtU d := by
  w0_site
  w0_poll .wq via Flow.code_264, Flow.code_265, Flow.code_266

theorem stepAt_wq (d : D) (hs : d.site = .wq) : (code P L g w).StepAtU d := by
  w0_site
  w0_poll .tcfa via Flow.code_272, Flow.code_273, Flow.code_274

/-- The fence, then the stage's branch on `%p76` (`w > 1`) to its score-load order. -/
theorem stepAt_tcfa (d : D) (hs : d.site = .tcfa) : (code P L g w).StepAtU d := by
  w0_site
  w0_adv Flow.code_275 by exact Code.fires_tcPlain_next (.inl rfl) hf
  refine SegU.pick (r := 76) (x := .pred (scmpi .gt .s w 1))
    (mem_factsFrom_eq (show 76 ∈ ctlLive 275 by decide +kernel) rfl) ?_
  refine SegU.comp (SegU.branch _ Flow.code_276 bra_rule noSegments.segFreePc) ?_
  generalize scmpi .gt .s w 1 = b
  cases b <;> w0_seg

set_option hygiene false in
local macro "ld_at " pc:term:max code:term:max : tactic => `(tactic| (
  refine Code.tcLoadU (live := ctlLive $pc) $code (fun _ h => by cases h) (noLdWait _) rfl
    (by decide +kernel)
    (fun _ _ => rfl) rfl rfl rfl rfl Nat.one_pos ?_))

/-- The two score loads, in the stage's order. -/
theorem stepAt_sld (d : D) (a : Bool) (k : Fin 2) (hs : d.site = .sld a k) :
    (code P L g w).StepAtU d := by
  w0_site
  cases a <;> fin_cases k
  · ld_at 278 Flow.code_278; w0_seg
  · ld_at 280 Flow.code_280
    exact SegU.comp (SegU.of_seg (seg_jmp Flow.code_281 (fun t _ => bra_rule t)
      noSegments.segFreePc)) (by w0_seg)
  · ld_at 283 Flow.code_283; w0_seg
  · ld_at 285 Flow.code_285; w0_seg

theorem stepAt_sldw (d : D) (hs : d.site = .sldw) : (code P L g w).StepAtU d := by
  w0_site
  w0_adv Flow.code_286 by exact Code.fires_tcPlain_next (.inr (.inr rfl)) hf
  w0_seg

theorem stepAt_tcfb (d : D) (hs : d.site = .tcfb) : (code P L g w).StepAtU d := by
  w0_site
  w0_adv Flow.code_287 by exact Code.fires_tcPlain_next (.inr (.inl rfl)) hf
  w0_seg

/-- The valid-mask word: any payload continues to the peer stores. -/
theorem stepAt_vm (d : D) (hs : d.site = .vm) : (code P L g w).StepAtU d := by
  w0_site
  refine Code.step_loadU Flow.code_289 rfl rfl rfl rfl rfl rfl rfl rfl rfl (fun _ _ => rfl)
    Nat.one_pos (by
      change _ ∉ (factsFrom _ _).map Prod.fst; rw [factsFrom_keys]
      show _ ∉ ctlLive 289; decide +kernel) ?_
  w0_seg

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Flow PTX.Proof PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The vote: its result is recorded, and both arms of the branch on its negation reach the
first P store. -/
theorem stepAt_vote (d : D) (hs : d.site = .vote) : (code P L g w).StepAtU d := by
  w0_site
  refine Code.voteAnyU (dst := fun r => ⟨.ost 0, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, r⟩)
    Flow.code_578 (by
      change _ ∉ (factsFrom _ _).map Prod.fst; rw [factsFrom_keys]
      show _ ∉ ctlLive 578; decide +kernel)
    (fun _ _ _ => rfl) rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => Nat.zero_lt_succ _)
    (fun r => ?_)
  refine SegU.comp (b := 581) (G := (110, .pred (!r)) :: (110, .pred (!r)) :: (1, .pred r) ::
    facts P L g w ⟨.vote, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩) (by w0_seg) ?_
  refine SegU.comp (SegU.branch (!r) Flow.code_581 bra_rule noSegments.segFreePc) ?_
  cases r <;> w0_seg

set_option hygiene false in
local macro "st4 " S:term:max code:term:max : tactic => `(tactic| (
  refine ostU $S rfl (by rfl) $code rfl rfl rfl rfl (Nat.zero_lt_succ _) ?_
  w0_seg))

/-- The first three P stores. -/
theorem stepAt_ost (d : D) (k : Fin 4) (hs : d.site = .ost k) (hk : k.val < 3) :
    (code P L g w).StepAtU d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  dsimp only at hs; subst hs
  fin_cases k
  · st4 (.ost 1) Flow.code_704
  · st4 (.ost 2) Flow.code_705
  · st4 (.ost 3) Flow.code_706
  · exact absurd hk (by decide)

set_option hygiene false in
local macro "last_st " S:term:max : tactic => `(tactic| (
  refine ostU $S rfl (by rfl) Flow.code_707 rfl rfl rfl
    (by show (if scmpi .eq .b bi 1 || !vt then Site.fpx else .rsf) = _; rw [hb]; rfl)
    (Nat.zero_lt_succ _) ?_
  refine SegU.comp (b := 710) (G := (112, .pred (scmpi .eq .b bi 1 || !vt)) ::
    facts P L g w ⟨.ost 3, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩) (by w0_seg) ?_
  refine SegU.comp (SegU.branch _ Flow.code_710 bra_rule noSegments.segFreePc) ?_
  rw [hb]
  w0_seg))

/-- The last P store, then the branch to the proxy fence (first block or no rescale) or to the
rescale arm. -/
theorem stepAt_ost_last (d : D) (hs : d.site = .ost 3) : (code P L g w).StepAtU d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  dsimp only at hs; subst hs
  cases hb : (scmpi .eq .b bi 1 || !vt)
  · last_st .rsf
  · last_st .fpx

/-- The four P stores. -/
theorem stepAt_ost_any (d : D) (k : Fin 4) (hs : d.site = .ost k) : (code P L g w).StepAtU d := by
  by_cases hk : k.val < 3
  · exact stepAt_ost d k hs hk
  · have h3 : k = 3 := Fin.ext (by have := k.isLt; show k.val = 3; omega)
    subst h3
    exact stepAt_ost_last d hs

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Loop
open PTX PTX.Flow Wg0.Control

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

/-- **The Loop half's step obligations.** -/
theorem stepAt (hp : Pre P L m) (d : D) (hl : d.site.inLoop = true) :
    (code P L g w).StepAtU d := by
  cases hs : d.site <;> rw [hs] at hl
  case smr => exact stepAt_smr hp d hs
  case sink => exact stepAt_sink hp d hs
  case lenA => exact stepAt_lenA hp d hs
  case lenB => exact stepAt_lenB d hs
  case bwait => exact stepAt_bwait d hs
  case arrL => exact stepAt_arrL d hs
  case bar0 => exact stepAt_bar0 d hs
  case wv => exact stepAt_wv d hs
  case wq => exact stepAt_wq d hs
  case tcfa => exact stepAt_tcfa d hs
  case sld a k => exact stepAt_sld d a k hs
  case sldw => exact stepAt_sldw d hs
  case tcfb => exact stepAt_tcfb d hs
  case vm => exact stepAt_vm d hs
  case pst k => exact stepAt_pst d k hs
  case bar1 => exact stepAt_bar1 d hs
  case pld k => exact stepAt_pld d k hs
  case mst => exact stepAt_mst d hs
  case bar2 => exact stepAt_bar2 d hs
  case arrV => exact stepAt_arrV d hs
  case mld => exact stepAt_mld d hs
  case vote => exact stepAt_vote d hs
  case ost k => exact stepAt_ost_any d k hs
  case rsf => exact stepAt_rsf d hs
  case rld c => exact stepAt_rld d c hs
  case rldw c => exact stepAt_rldw d c hs
  case rst c => exact stepAt_rst d c hs
  case rstw c => exact stepAt_rstw d c hs
  case rsfb => exact stepAt_rsfb d hs
  case fpx => exact stepAt_fpx d hs
  case arrS => exact stepAt_arrS d hs
  case old c | oldw c | ofpx c | obar c | oel c | otma c =>
    fin_cases c <;> exact absurd hl (by decide)
  case ost2 c k => fin_cases c <;> fin_cases k <;> exact absurd hl (by decide)
  all_goals exact absurd hl (by decide)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Loop
