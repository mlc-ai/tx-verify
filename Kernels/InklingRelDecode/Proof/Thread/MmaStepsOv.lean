-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.MmaStepBase

@[expose] public section

/-! # The MMA warp's sites that `site_cases` does not discharge

Three sites read a word whose value the evaluation does not know, and stop the machine on a word
without bits:

* `bar0` (`barrier.sync 1`): the start of the loop compares the loaded `num_iters` word (`%r10`)
  with `2 ^ 31 - 1` and with the iteration; a word without bits faults at the first comparison;
* `qkShfl`, `pvShfl`: the test `setp.ne.b32` of the received broadcast word; a word without bits
  faults at the test (`stepOk_bcast`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {tm0 : Nat} {pro0 : Nat → Value}

/-- `barrier.sync 1`: the loop starts, or is skipped when `num_iters` is zero or too large; a
word without bits faults at the first instruction after the barrier. -/
theorem ov_bar0 (hpre : Pre P L mem0) (i n tm : Nat) (pro : Nat → Value) :
    (code asms L g tm0 pro0).StepOk ⟨.bar0, i, n, tm, pro⟩ := by
  refine ⟨fun {t e u} ins h hi hc hf => ?_⟩
  have hi : Inv ⟨.bar0, i, n, tm, pro⟩ := hi
  have h : At t (Site.bar0).pc (facts L ⟨.bar0, i, n, tm, pro⟩) := h
  have hc : kernel.code[(Site.bar0).pc]? = some ins := hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_30)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSync _ _) from trivial) hf
  have hi0 : i = 0 := hi.pre trivial
  cases hw : Raw.word32Of (pro 471) with
  | none =>
    refine .inr ⟨by simp [code, next, hw], ?_⟩
    refine Raw.dead_int1 (F := factsAt L 2425 ⟨.bar0, i, n, tm, pro⟩) Flow.code_2425 rfl rfl
      (Raw.asms_segFree (by decide +kernel)) (fun t' h' => ?_)
      ((At.next h).mono (holds_live h.2.2.2.2 rfl (by table_decide)))
    obtain ⟨f, hf⟩ := Raw.readBits_word32_none (L := L) (g := g)
      (reg_471 (d := ⟨.bar0, i, n, tm, pro⟩) h' (by table_decide)) hw
    exact ⟨f, by simp only [execInt, hf, DType.width]; rfl⟩
  | some m =>
    obtain rfl : m = n := hi.wd0 rfl m hw
    have hs := seg_start (L := L) (g := g) (d := ⟨.bar0, i, m, tm, pro⟩) (pre_shared hpre)
      hw hi0 hi.tm
    obtain ⟨t', hr, ht'⟩ := (hs.live_start (s' := 2424) (d := ⟨.bar0, i, m, tm, pro⟩) rfl
      (by table_decide)).rtg (At.next h)
    refine .inl (.inr ⟨start ⟨.bar0, i, m, tm, pro⟩, t', by simp [code, next, hw], hr, ht', ?_⟩)
    unfold start
    split_ifs with hs'
    · exact ⟨hi.n, hi.tm, hi.col, fun h => False.elim h, fun h => False.elim h,
        fun h => False.elim h, fun _ => hw, (fun h => by cases h), fun _ _ => hs'⟩
    · refine ⟨hi.n, hi.tm, hi.col, fun h => False.elim h, fun _ => ?_, fun h => False.elim h,
        fun _ => hw, (fun h => by cases h), fun h => False.elim h⟩
      have hs'' : ¬ (m = 0 ∨ 2147483646 < m) := hs'
      show i < m ∧ m ≤ 2147483646
      omega

/-- The broadcast of the warp index before the QK MMAs and its test: a word that reads as 7
reaches `qkBar2`, another word with bits `qkSkip`, a word without bits faults. -/
theorem ov_qkShfl (i n tm : Nat) (pro : Nat → Value) :
    (code asms L g tm0 pro0).StepOk ⟨.qkShfl, i, n, tm, pro⟩ :=
  stepOk_bcast (sOk := .qkBar2) (sSkip := .qkSkip) Flow.code_shfl_13 Flow.code_2465
    (show Assumption.SegFreePc asms 2465 from Raw.asms_segFree (by decide +kernel))
    (by show 546 ∉ Flow.live Flow.shfl_13; table_decide)
    (fun _ _ _ _ _ _ hw => by simp [next, hw]) (fun _ _ _ _ _ _ _ hw => by simp [next, hw])
    (fun k => by split_ifs <;> rfl) (fun k => by split_ifs <;> (ink_values; simp_all))
    (show ∀ q ∈ Flow.live 2466, q = 8 ∨ (q ∈ Flow.live 2464 ∧ q ≠ 8 ∧ q ≠ 13) by table_decide)
    (fun hi k => by
      split_ifs <;>
        exact inv_site hi _ (fun h => False.elim h) (fun _ => hi.qk trivial)
          (fun h => False.elim h))

/-- The broadcast of the warp index before the PV MMAs and its test. -/
theorem ov_pvShfl (i n tm : Nat) (pro : Nat → Value) :
    (code asms L g tm0 pro0).StepOk ⟨.pvShfl, i, n, tm, pro⟩ :=
  stepOk_bcast (sOk := .pvBar2) (sSkip := .pvSkip) Flow.code_shfl_14 Flow.code_2513
    (show Assumption.SegFreePc asms 2513 from Raw.asms_segFree (by decide +kernel))
    (by show 563 ∉ Flow.live Flow.shfl_14; table_decide)
    (fun _ _ _ _ _ _ hw => by simp [next, hw]) (fun _ _ _ _ _ _ _ hw => by simp [next, hw])
    (fun k => by split_ifs <;> rfl) (fun k => by split_ifs <;> (ink_values; simp_all))
    (show ∀ q ∈ Flow.live 2514, q = 13 ∨ (q ∈ Flow.live 2512 ∧ q ≠ 8 ∧ q ≠ 13) by table_decide)
    (fun hi k => by
      split_ifs <;>
        exact inv_site hi _ (fun h => False.elim h) (fun h => False.elim h)
          (fun _ => hi.pv trivial))

end
end PTX.Kernels.InklingRelDecode.Proof.Mma
