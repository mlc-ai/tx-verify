-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Steps.Base
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part040
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part041
import Lemmas.Flow.NcLoadU

@[expose] public section

/-! # Warpgroup 2's obligations in its set-up (pcs 2620–2676)

The two length loads (`lenA`, `lenB`, followed on their word), and the poll of the Q barrier (`wq`)
with the test for no block (pc 2648, to named barrier 12) and the loop's set-up. Every branch on
a parameter or a length is stepped by naming its predicate (`SegU.pick`) and splitting on it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
open PTX PTX.Flow PTX.Proof PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

set_option hygiene false in
/-- Cut the segment at the branch at `pc` (code lemma `c`) on predicate `p` of value `x`, the facts
there those of state `d`; the goal is left at the branch's target `if x then … else pc + 1`. -/
local macro "br_at " pc:term:max p:term:max x:term:max d:term:max c:term:max : tactic =>
  `(tactic| (
  refine SegU.comp (b := $pc) (G := factsFrom (ctlLive $pc) (valueOf P L g $d)) (by dq_seg) ?_
  refine SegU.pick (r := $p) (x := .pred $x)
    (mem_factsFrom_eq (show $p ∈ ctlLive $pc by decide +kernel) rfl) ?_
  refine SegU.comp (SegU.branch _ $c bra_rule noSegments.segFreePc) ?_))

set_option hygiene false in
/-- The Q poll to the state `dn` (`hz`: the test for no block). -/
local macro "wq_to " dn:term:max : tactic => `(tactic| (
  refine pollTo $dn (by rfl) Flow.code_2644 (by decide +kernel)
    (fun m q ok s => by cases ok <;> simp only [code, succ, loopEntry, hz, Bool.false_eq_true,
      ↓reduceIte]) rfl rfl (by dsimp only; decide) rfl
    (SegU.comp (SegU.branch false Flow.code_2645 bra_rule noSegments.segFreePc)
      (SegU.of_seg (seg_jmp Flow.code_2646 (fun t _ => bra_rule t) noSegments.segFreePc)))
    (SegU.comp (SegU.branch true Flow.code_2645 bra_rule noSegments.segFreePc) ?_)
  br_at 2648 133 (scmpi .lt .s (r57 l0 l1) 64) ⟨.wq, 0, ac, l0, l1, cnt, sb, pb⟩ Flow.code_2648
  rw [hz]
  dq_seg))

/-- The Q poll: on success the test for no block (pc 2648) and the loop's set-up. -/
theorem stepAt_wq (d : D) (hs : d.site = .wq) : (code P L g w).StepAtU d := by
  dq_site
  cases hz : scmpi .lt .s (r57 l0 l1) 64
  · wq_to ⟨.wraw, 0, ac, l0, l1, neg32 (nblk l0 l1), false, false⟩
  · wq_to ⟨.bar, 0, ac, l0, l1, cnt, sb, pb⟩

set_option hygiene false in
/-- A length load at code lemma `c` into register `r` at `pc`, whose word `x` goes on to `f x`;
`t` proves the segment. -/
local macro "len_at " c:term:max r:term:max pc:term:max f:term:max " from " hn:term:max :
    tactic => `(tactic| (
  refine Code.step_loadNcU (f := $f) $c rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl $hn
    (fun p hp he => by
      have hm := List.mem_map_of_mem (f := Prod.fst) hp
      rw [he] at hm
      change $r ∈ (factsFrom _ _).map Prod.fst at hm
      rw [factsFrom_keys] at hm
      exact absurd hm (by decide +kernel : ($r : Nat) ∉ ctlLive $pc))
    (fun x => ⟨rfl, rfl, ?_, ?_⟩)))

set_option hygiene false in
/-- The first length load to the site `S` (`hz`: the second pointer's test). -/
local macro "lenA_to " S:term:max : tactic => `(tactic| (
  len_at Flow.code_2620 2985 2620 (fun x => ⟨$S, 0, ac, x, l1, cnt, sb, pb⟩) from
    (fun _ _ => by simp only [code, succ, afterA, hz, Bool.false_eq_true, ↓reduceIte])
  · exact Nat.one_pos
  · br_at 2627 132 (eqz64 (pw8 (P.extraTopkLenBase.getD 0)))
      ⟨.lenA, 0, ac, x, l1, cnt, sb, pb⟩ Flow.code_2627
    rw [hz]
    dq_seg))

theorem stepAt_lenA (d : D) (hs : d.site = .lenA) : (code P L g w).StepAtU d := by
  dq_site
  cases hz : eqz64 (pw8 (P.extraTopkLenBase.getD 0))
  · lenA_to .lenB
  · lenA_to .wq

theorem stepAt_lenB (d : D) (hs : d.site = .lenB) : (code P L g w).StepAtU d := by
  dq_site
  len_at Flow.code_2630 2986 2630 (fun x => ⟨.wq, 0, ac, l0, x, cnt, sb, pb⟩) from
    (fun _ _ => rfl)
  · exact Nat.one_pos
  · dq_seg

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
