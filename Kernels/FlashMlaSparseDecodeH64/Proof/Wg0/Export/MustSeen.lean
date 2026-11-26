-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PrevPc
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidSnoc
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain

@[expose] public section

/-! # What a block has read before an event of its body

An event of a lane of warpgroup 0 at a pc of the body of a block (`w0Body`) has behind it, in the
block in progress, events at the pcs `w0Must` names: a group of pcs is seen when some event of the
block is at one of them (the two score loads of an arm, the mask word, the peer pairs before it,
the exchange word). The facts follow the events one by one from `w0_prev_pc`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

/-- The groups of the peer pairs `0` to `n - 1`. -/
def w0PldGroups (n : Nat) : List (List Nat) := (List.range n).map fun i => [477 + 5 * i]

/-- The groups of pcs a block has behind an event at the body pc `p`: each group has an event of
the block at one of its pcs. -/
def w0Must (p : Nat) : List (List Nat) :=
  if p = 278 then [[278]] else if p = 280 then [[278], [280]]
  else if p = 283 then [[283]] else if p = 285 then [[283], [285]]
  else if p = 286 ∨ p = 287 then [[280, 283], [278, 285]]
  else if p = 289 then [[280, 283], [278, 285], [289]]
  else if 403 ≤ p ∧ p ≤ 475 then [[280, 283], [278, 285], [289]]
  else if 477 ≤ p ∧ p ≤ 512 then
    [[280, 283], [278, 285], [289]] ++ w0PldGroups ((p - 477) / 5 + 1)
  else if 566 ≤ p ∧ p ≤ 571 then [[280, 283], [278, 285], [289]] ++ w0PldGroups 8
  else if p = 572 then [[280, 283], [278, 285], [289]] ++ w0PldGroups 8 ++ [[572]]
  else if p = 578 then [[280, 283], [278, 285], [289]] ++ w0PldGroups 8 ++ [[572], [578]]
  else if 704 ≤ p ∧ p ≤ 1121 then [[578]]
  else []

private theorem must_tbl : ∀ p ∈ w0BodyPcs, p ≠ 1122 →
    ∀ f ∈ w0Prev p, f ≠ 1122 ∧ ∀ grp ∈ w0Must p,
      p ∈ grp ∨ (w0Body f = true ∧ ∃ g' ∈ w0Must f, ∀ x ∈ g', x ∈ grp) := by
  decide +kernel

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The groups behind an event of the body**: the event at index `i ≤ k` of a lane of
warpgroup 0 with a valid trace through `k`, at a pc of the body, has an event at one of the pcs
of each group of `w0Must` in the block in progress through it. -/
theorem w0_must (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k : Nat} (hal : LaneAlive X g k) (hw : warp L g < 4)
    (hv : W0Valid P.scale ((X.tr g).take k)) :
    ∀ i, i ≤ k → ∀ e, X.get (g, i) = some e → w0Body e.pc = true → e.pc ≠ 1122 →
      ∀ grp ∈ w0Must e.pc, ∃ ev ∈ (w0Scan ((X.tr g).take (i + 1))).2, ev.pc ∈ grp := by
  intro i
  induction i with
  | zero =>
    intro _ e he hb _
    exfalso
    have hr : 103 ≤ e.pc ∧ e.pc < 1842 := by
      simp only [w0Body, w0BodyPcs, List.mem_cons, List.not_mem_nil, or_false,
        decide_eq_true_eq] at hb
      omega
    exact Wg0.w0_not_first hp hX hFw he (hal 0 e he (by omega)) hr
  | succ j ih =>
    intro hjk e he hb hn1 grp hgrp
    have hvj : W0Valid P.scale ((X.tr g).take (j + 1)) := Wg0.W0Valid.take_le hv hjk
    obtain ⟨f, hf, hfp⟩ := w0_prev_pc hp hX hFw hw he (hal (j + 1) e he hjk) hb hvj
    have hne : e.pc ≠ w0ArrSPc := hn1
    have hsc : (w0Scan ((X.tr g).take (j + 1 + 1))).2 =
        (w0Scan ((X.tr g).take (j + 1))).2 ++ [e] := by
      rw [trace_take_succ he, w0Scan_snoc]
      simp [hne]
    rw [hsc]
    have hbody : e.pc ∈ w0BodyPcs := by
      simpa [w0Body] using hb
    obtain ⟨hf1, htb⟩ := must_tbl e.pc hbody hn1 f.pc hfp
    rcases htb grp hgrp with h | ⟨hfb, g', hg', hsub⟩
    · exact ⟨e, by simp, h⟩
    · obtain ⟨ev, hev, hevp⟩ := ih (by omega) f hf hfb hf1 g' hg'
      exact ⟨ev, by simp [hev], hsub _ hevp⟩

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
