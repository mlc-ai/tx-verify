-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Steps.Base
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part041
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part056
import Lemmas.Flow.IssueNext
import Lemmas.Flow.RoleTemplates
import Lemmas.Flow.Step.Combinators

@[expose] public section

/-! # Warpgroup 2's obligations at the block's polls and after its stores

The polls of the raw-ready and SV-done barriers of the slot (`wraw`, `wsv`), the proxy fence and
the dequant-ready arrival (`fpx`, `arrD`), named barrier 12 (`bar`) and the return (`exit`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
open PTX PTX.Flow PTX.Proof PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

theorem stepAt_wraw (d : D) (hs : d.site = .wraw) : (code P L g w).StepAtU d := by
  dq_site
  dq_poll .wsv via Flow.code_2677, Flow.code_2678, Flow.code_2679

set_option hygiene false in
/-- The SV-done poll at slot `b` (a literal: the slot's buffer bases are `selp` on it). -/
local macro "wsv_at " b:term:max : tactic => `(tactic| (
  refine pollTo (Control.D.mk (.scale 0) 0 ac l0 l1 cnt $b pb) (by rfl) Flow.code_2684
    (by decide +kernel) (fun m q ok s => by cases ok <;> rfl) rfl rfl (by dsimp only; decide) rfl
    (SegU.comp (SegU.branch false Flow.code_2685 bra_rule noSegments.segFreePc)
      (SegU.of_seg (seg_jmp Flow.code_2686 (fun t _ => bra_rule t) noSegments.segFreePc)))
    (SegU.comp (SegU.branch true Flow.code_2685 bra_rule noSegments.segFreePc) ?_)
  dq_seg))

/-- The SV-done poll, then the slot's bases (pcs 2687–2694, by the slot). -/
theorem stepAt_wsv (d : D) (hs : d.site = .wsv) : (code P L g w).StepAtU d := by
  dq_site
  cases sb
  · wsv_at false
  · wsv_at true

theorem stepAt_fpx (d : D) (hs : d.site = .fpx) : (code P L g w).StepAtU d := by
  dq_site
  ctl_adv Flow.code_3595 by exact Option.some.inj (fires_fence_proxy hf).2
  dq_seg

theorem stepAt_arrD (d : D) (hs : d.site = .arrD) : (code P L g w).StepAtU d := by
  dq_site
  ctl_adv Flow.code_3597 by exact Code.fires_arrive_next hf
  dq_seg

theorem stepAt_bar (d : D) (hs : d.site = .bar) : (code P L g w).StepAtU d := by
  dq_site
  ctl_adv Flow.code_3610 by exact fires_barSyncN_next hf
  dq_seg

/-- The ring's advance (pcs 3600–3606: the parity's `selp.b16` on `%p136`, i.e. `%rs351` against
`slot & 255`, the slot's `(~slot) & 1`, the counter's increment) carries the control facts to the
back-edge's branch at pc 3607. The stretch is cut before the `selp` (pc 3603): the checkpoint
states `%p136` as `pb != sb`, which is then split, so the `selp` picks on a literal. -/
theorem ringSeg (ac : List Value) (l0 l1 cnt : BitVec 64) (sb pb : Bool) :
    SegU kernel Assumptions.all L g 3600
      (factsFrom (ctlLive 3599) (valueOf P L g ⟨.arrF, 0, ac, l0, l1, cnt, sb, pb⟩))
      3607 (factsFrom (ctlLive 3607)
        (valueOf P L g ⟨.bar, 0, ac, l0, l1, addi cnt 1, !sb, pb != sb⟩)) := by
  refine SegU.comp (b := 3603) (G := (136, .pred (pb != sb)) ::
    factsFrom ((ctlLive 3603).erase 136) (valueOf P L g ⟨.arrF, 0, ac, l0, l1, cnt, sb, pb⟩)) ?_ ?_
  · cases sb <;> cases pb <;> dq_seg
  · generalize (pb != sb) = c
    cases c <;> cases sb <;> dq_seg

set_option hygiene false in
/-- The raw-free arrival and the back-edge to the site `S` (`hz`: the counter's test). -/
local macro "arr_step " S:term:max : tactic => `(tactic| (
  refine Code.advanceU (C := code P L g w)
    (dn := ⟨$S, 0, ac, l0, l1, addi cnt 1, !sb, pb != sb⟩) Flow.code_3599 rfl
    (fun hf => Code.fires_arrive_next hf)
    (fun _ => by simp only [code, succ, advance, hz, Bool.false_eq_true, ↓reduceIte])
    rfl rfl rfl rfl Nat.one_pos ?_
  refine SegU.comp (ringSeg ac l0 l1 cnt sb pb) ?_
  refine SegU.pick (r := 137) (x := .pred (scmpi .ne .b (addi cnt 1) 0))
    (mem_factsFrom_eq (show 137 ∈ ctlLive 3607 by decide +kernel) rfl) ?_
  refine SegU.comp (SegU.branch _ Flow.code_3607 bra_rule noSegments.segFreePc) ?_
  rw [hz]
  dq_seg))

/-- The raw-free arrival and the loop's advance (pcs 3599–3607): the counter advances, the slot
flips, the parity flips after slot 1 (`ringSeg`), and the branch on `%p137` (counter `≠ 0`) goes
back to the next block's raw-ready poll or on to named barrier 12. -/
theorem stepAt_arrF (d : D) (hs : d.site = .arrF) :
    (code P L g w).StepAtU d := by
  dq_site
  cases hz : scmpi .ne .b (addi cnt 1) 0
  · arr_step .bar
  · arr_step .wraw

/-- The return ends the thread: no step reaches a state. -/
theorem stepAt_exit (d : D) (hs : d.site = .exit) : (code P L g w).StepAtU d := by
  have hp : (code P L g w).pc d = 3611 := by show d.site.pc = 3611; rw [hs]; rfl
  refine ⟨fun _ => ⟨⟨none, .ret⟩, by rw [hp]; exact Flow.code_3611, rfl, trivial⟩,
    fun ins _ _ hc hf => ?_⟩
  rw [hp, Flow.code_3611] at hc
  obtain rfl := Option.some.inj hc
  simp [eventTmpl, Fires] at hf

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
