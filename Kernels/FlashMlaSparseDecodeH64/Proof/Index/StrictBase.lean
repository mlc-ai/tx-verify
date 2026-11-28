-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StrictQt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexWalk
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.RulesFrame
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Seg
public import Lemmas.Flow.HavocTyped
public import Lemmas.Flow.SegQCtl
public import Lemmas.Flow.SegQOps
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # The strict index walks: the tactics

The index warp's walks (`Lib/IndexWalk.lean`, `Index/Walk.lean`) restated as strict segments
(`SegQ`) under the tag invariant `QT ixQt` (`Index/StrictQt.lean`): no dead alternative, the
registers the data stretches read are tagged. A strict walk takes the plain-stretch hypotheses
`hN`, `hS` (`Index/StrictPlain.lean`) as variables.

* `ixq_seg`: a control segment between two tables' facts (`segq_ctl`).
* `ixq_br`: cut at the branch at `pc` on predicate `p` of value `x`. -/

/-! # No assumption touches the index warp's plain stretches

`Havoc.PlainRules`/`PlainSegs` for `Assumptions.all` over the index warp's pcs `2332`–`2599`:
the typed crossing (`Lemmas/Flow/HavocTyped.lean`) needs that no assumption's local rule takes an
integer, move or integer conversion instruction there, and that no assumption takes a segment. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Assumptions

variable {L : Launch} {g : Nat}

/-- An instruction the typed run accepts is an integer, a move or an integer conversion. -/
theorem absOp_shape {env : Env} {op : Op} (h : (absOp env op).isSome) :
    (∃ i, op = .int i) ∨ (∃ m, op = .move m) ∨ (∃ c k w, op = .cvt c ∧ c.dst = .int k w) := by
  cases op <;> simp only [absOp, Option.isSome_none, Bool.false_eq_true] at h
  · exact .inl ⟨_, rfl⟩
  · exact .inr (.inl ⟨_, rfl⟩)
  · rename_i c
    obtain ⟨dst, src, rnd, ftz, sat, relu, satfinite, pzo, scaled, pack, d', ext, srcs⟩ := c
    unfold absCvt at h
    simp only at h
    split at h
    · rename_i k w _ _ _
      exact .inr (.inr ⟨_, k, w, rfl, rfl⟩)
    · simp at h

private theorem float_none {op : Op}
    (h : (∃ i, op = .int i) ∨ (∃ m, op = .move m) ∨ (∃ c k w, op = .cvt c ∧ c.dst = .int k w)) :
    Assumption.FloatForm.ofOp op = none ∧ Assumption.ApproxForm.ofOp op = none := by
  rcases h with ⟨i, rfl⟩ | ⟨m, rfl⟩ | ⟨c, k, w, rfl, hd⟩
  · simp [Assumption.FloatForm.ofOp, Assumption.ApproxForm.ofOp]
  · simp [Assumption.FloatForm.ofOp, Assumption.ApproxForm.ofOp]
  · simp [Assumption.FloatForm.ofOp, Assumption.ApproxForm.ofOp, CvtInstr.widenF16?,
      CvtInstr.packF16?, hd]

/-- The pcs of the index warp's stretch are no site of a pc-gated assumption. -/
private theorem pc_free : (List.range 268).all (fun i =>
    !paramAdds.contains (2332 + i) && !prefetchTensorMapSites.contains (2332 + i) &&
    !sharedBitsSites.contains (2332 + i) && (deadPackWords (2332 + i)).isNone &&
    (peerPack (2332 + i)).isNone) = true := by
  decide +kernel

private theorem pc_free_of {pc : Nat} (ha : 2332 ≤ pc) (hb : pc < 2600) :
    paramAdds.contains pc = false ∧ prefetchTensorMapSites.contains pc = false ∧
    sharedBitsSites.contains pc = false ∧ deadPackWords pc = none ∧ peerPack pc = none := by
  have h := List.all_eq_true.mp pc_free (pc - 2332) (List.mem_range.mpr (by omega))
  rw [show 2332 + (pc - 2332) = pc by omega] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at h
  tauto

theorem plainRules_index : PlainRules Assumptions.all L g 2332 2600 := by
  intro t ha hb op ⟨env, hop⟩ x hx
  have hs := absOp_shape hop
  obtain ⟨hf, hap⟩ := float_none hs
  obtain ⟨h1, h2, h3, h4, h5⟩ := pc_free_of ha hb
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Assumption.idealReal_localRule_none fun f hf' => by simp [hf] at hf'
  · exact Assumption.approxExact_localRule_none fun f hf' => by simp [hap] at hf'
  · rcases hs with ⟨i, rfl⟩ | ⟨m, rfl⟩ | ⟨c, k, w, rfl, hd⟩ <;> rfl
  · rcases hs with ⟨i, rfl⟩ | ⟨m, rfl⟩ | ⟨c, k, w, rfl, hd⟩
    · rfl
    · rfl
    · simp [cvtBf16x2, hd]
  · rcases hs with ⟨i, rfl⟩ | ⟨m, rfl⟩ | ⟨c, k, w, rfl, hd⟩
    · rfl
    · rfl
    · simp [cvtUe8m0, hd]
  · rcases hs with ⟨i, rfl⟩ | ⟨m, rfl⟩ | ⟨c, k, w, rfl, hd⟩ <;> rfl
  · rfl
  · have h1' : t.pc ∉ paramAdds := by simpa using h1
    have h2' : t.pc ∉ prefetchTensorMapSites := by simpa using h2
    simp [paramPointers, h1', h2']
  · rfl
  · have h3' : t.pc ∉ sharedBitsSites := by simpa using h3
    simp [sharedBits, h3', deadPackRule_of_none h4, peerPackRule_of_none h5]
  · rfl

/-- No assumption of the kernel takes a segment at any pc of the stretch. -/
theorem plainSegs_index : PlainSegs Assumptions.all 2332 2600 :=
  fun _ _ _ => noSegments.segFreePc

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Flow.Havoc PTX.Flow.Tagged

set_option maxRecDepth 100000

/-- The plain-stretch hypotheses of a strict walk. -/
structure Plain (L : Launch) (g : Nat) : Prop where
  rules : PlainRules Assumptions.all L g 2332 2600
  segs : PlainSegs Assumptions.all 2332 2600

theorem Plain.mk' {L : Launch} {g : Nat} : Plain L g := ⟨plainRules_index, plainSegs_index⟩

set_option hygiene false in
/-- A strict control segment of the index warp between two tables' facts. -/
macro "ixq_seg" : tactic => `(tactic| (
  try dsimp only [ixFacts, IxSite.pc, Bool.false_eq_true, ↓reduceIte]
  segq_ctl ixQt, hP.rules, hP.segs, rulesFrame using rfl))

set_option hygiene false in
/-- Cut the strict segment at the branch at `pc` (code lemma `cb`) on predicate `p` of value `x`,
the facts there the table's for the words `c`; `h` fixes the branch's outcome (`x = b`), so that
the target's tags are checked for that outcome only. -/
macro "ixq_br " pc:term:max p:term:max x:term:max c:term:max cb:term:max " with " h:term:max :
    tactic => `(tactic| (
  refine SegQ.comp (b := $pc) (G := factsFrom (ixLive $pc) (ixVal P L g $c)) (by ixq_seg) ?_
  refine SegQ.pick (r := $p) (x := .pred $x)
    (mem_factsFrom_eq (show $p ∈ ixLive $pc by decide +kernel) rfl) ?_
  refine SegQ.comp (SegQ.branch _ $cb bra_rule noSegments.segFreePc ?_) ?_
  · rw [($h : _)]; decide +kernel
  rw [($h : _)]))

set_option hygiene false in
/-- The branch at the code lemma `cb` as a strict segment whose predicate fact has the outcome
`h : x = b`. -/
macro "ixq_bra " cb:term:max " with " h:term:max : tactic => `(tactic| (
  refine SegQ.comp (SegQ.branch _ $cb bra_rule noSegments.segFreePc ?_) ?_
  · (try rw [($h : _)]); decide +kernel
  try rw [($h : _)]))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
