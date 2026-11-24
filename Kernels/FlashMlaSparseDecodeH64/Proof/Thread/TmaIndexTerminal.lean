-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmaIndexTrace

@[expose] public section

/-! # A closing gather lane has released every index block -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmaIndexTrace

open PTX PTX.Flow
open Wg1Tma (D)

private def closing (d : D) : Prop := d.site = .barrier ∨ d.site = .exit

private def total (P : Params) (L : Launch) (g : Nat) : Nat :=
  totalBlocks (P.topkLen (ctaidY L g)) (P.extraTopkLen (ctaidY L g))

private theorem after_free_closes {P : Params} {L : Launch} {g : Nat} {d : D}
    (hi : Wg1Tma.Inv P L g d) (hd : d.site = .coordFree) (hEnd : closing (Wg1Tma.afterFree d)) :
    (Wg1Tma.afterFree d).block = total P L g := by
  have hBlock : d.block < totalBlocks d.len0 d.len1 := by
    have h := hi.block_le
    simpa [hd] using h
  unfold Wg1Tma.afterFree at hEnd ⊢
  by_cases hNext : d.block + 1 < totalBlocks d.len0 d.len1
  · simp [hNext, closing] at hEnd
  · have hEq : total P L g = totalBlocks d.len0 d.len1 := by
      rw [hi.len0, hi.len1]
      rfl
    simp only [ite_eq_right hNext, hEq]
    omega

private theorem terminal_next {P : Params} {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hi : Wg1Tma.Inv P L g d) (old : closing d → d.block = total P L g)
    (hn : Wg1Tma.next P L g d e = some (some d')) (hEnd : closing d') :
    d'.block = total P L g := by
  cases hd : d.site
  case coordFree =>
    cases hk : e.kind <;> simp only [Wg1Tma.next, hd, hk, reduceCtorEq] at hn
    split at hn
    · cases hn
      exact after_free_closes hi hd hEnd
    · cases hn
  case barrier =>
    have hTotal := old (.inl hd)
    cases hk : e.kind <;> simp only [Wg1Tma.next, hd, hk, reduceCtorEq] at hn
    split at hn <;> cases hn <;> exact hTotal
  all_goals
    have hPositive := totalBlocks_pos d.len0 d.len1
    have hNonzero : totalBlocks d.len0 d.len1 ≠ 0 := by omega
    cases hk : e.kind <;>
    simp only [Wg1Tma.next, hd, hk, Option.some.injEq, reduceCtorEq] at hn
    all_goals try simp only [ite_eq_right hNonzero] at hn
  all_goals repeat' split at hn
  all_goals try simp only [Option.some.injEq, reduceCtorEq] at hn
  all_goals rw [← hn] at hEnd ⊢
  all_goals
    try simp only [closing, hd, Wg1Tma.beginLoop, Wg1Tma.firstLenSite,
      Wg1Tma.afterCoord, Wg1Tma.afterIssue] at hEnd
    repeat' split at hEnd
    all_goals simp_all

private def terminalBlock (P : Params) (L : Launch) (g : Nat) :
    Option Machine.ThreadD → Prop
  | some (.tma d) => closing d → d.block = total P L g
  | _ => True

private theorem terminal_step {P : Params} {L : Launch} {g : Nat}
    {s s' : Option Machine.ThreadD} {e : Event} {o : Option TState}
    (hOld : terminalBlock P L g s)
    (hf : (Machine.machine P L g).Fired s e o)
    (hn : (Machine.machine P L g).next s e = some s') : terminalBlock P L g s' := by
  cases s with
  | none =>
    change some none = some s' at hn
    cases hn
    trivial
  | some s =>
    change Machine.next P L g s e = some s' at hn
    cases s
    case prologue st =>
      simp only [Machine.next] at hn
      repeat' split at hn
      all_goals cases hn
      all_goals first | trivial | (rename_i w _ _; fin_cases w <;> trivial)
    case head =>
      cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
      simp only [Machine.headStart] at hn
      split_ifs at hn <;> cases hn <;> try trivial
      simp [terminalBlock, closing, Wg1Tma.init]
    case tma d =>
      simp only [Machine.next] at hn
      split at hn
      · rename_i d' hNext
        cases hn
        obtain ⟨_, ⟨_, hi⟩, _⟩ := hf
        exact terminal_next hi hOld hNext
      · split_ifs at hn <;> cases hn <;> trivial
      · split_ifs at hn
        cases hn
        trivial
    all_goals
      simp only [Machine.next] at hn
      repeat' split at hn
      all_goals cases hn
      all_goals trivial

/-- A closing gather role's block count accounts for every release of the CTA's index ring. -/
theorem terminal_block {P : Params} {L : Launch} {g i : Nat} {es : List Event} {d : D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.tma d))) (hd : d.site = .barrier ∨ d.site = .exit) :
    d.block = totalBlocks (P.topkLen (ctaidY L g)) (P.extraTopkLen (ctaidY L g)) :=
  ht.prefix_induction (fun q _ => terminalBlock P L g q) trivial
    (fun _ _ _ _ _ => terminal_step) i (some (.tma d)) hs hd

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmaIndexTrace
