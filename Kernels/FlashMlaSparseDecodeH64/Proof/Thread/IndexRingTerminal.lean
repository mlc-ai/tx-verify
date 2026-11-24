-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.IndexRingTrace

@[expose] public section

/-! # The final index state has published all of its row's blocks -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.IndexRingTrace

open PTX PTX.Flow
open Wg1Index (D)

private theorem terminal_next {P : Params} {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hi : Wg1Index.Inv P L g d)
    (hn : Wg1Index.next P L g d e = some (some d')) (hEnd : d'.site = .barrier) :
    d'.block + 1 = totalBlocks (P.topkLen (ctaidY L g)) (P.extraTopkLen (ctaidY L g)) := by
  have hBound := hi.block
  cases hd : d.site <;> cases hk : e.kind <;>
    simp only [Wg1Index.next, Wg1Index.nextSite, hd, hk, Option.some.injEq, reduceCtorEq] at hn
  all_goals repeat' split at hn
  all_goals try simp only [Option.some.injEq, reduceCtorEq] at hn
  all_goals rw [← hn] at hEnd ⊢
  all_goals try (rw [hd] at hEnd; cases hEnd)
  all_goals
    try simp only [Wg1Index.afterPairFirst, Wg1Index.afterReady] at hEnd ⊢
    repeat' split at hEnd
    all_goals try contradiction
  all_goals
    simp only [ite_eq_right (show ¬ d.block + 1 < numOrigBlocks d.len0 from by assumption),
      ite_eq_right (show ¬ d.block + 1 < totalBlocks d.len0 d.len1 from by assumption)]
    change d.block + 1 = totalBlocks (P.topkLen (Wg1Index.eOf L g))
      (P.extraTopkLen (Wg1Index.eOf L g))
    rw [← hi.len0, ← hi.len1]
    omega

private def terminalBlock (P : Params) (L : Launch) (g : Nat) :
    Option Machine.ThreadD → Prop
  | some (.index d) => d.site = .barrier →
      d.block + 1 = totalBlocks (P.topkLen (ctaidY L g)) (P.extraTopkLen (ctaidY L g))
  | _ => True

private theorem terminal_step {P : Params} {L : Launch} {g : Nat}
    {s s' : Option Machine.ThreadD} {e : Event} {o : Option TState}
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
      intro h
      simp only [Wg1Index.init, Wg1Index.firstSite] at h
      split_ifs at h
    case index d =>
      simp only [Machine.next] at hn
      split at hn
      · rename_i d' hNext
        cases hn
        obtain ⟨_, ⟨_, hi⟩, _⟩ := hf
        exact terminal_next hi hNext
      · split at hn <;> cases hn <;> trivial
      · cases hn
    all_goals
      simp only [Machine.next] at hn
      repeat' split at hn
      all_goals cases hn
      all_goals trivial

/-- Closing the index role means that it published every logical block of its row. -/
theorem terminal_block {P : Params} {L : Launch} {g i : Nat} {es : List Event} {d : D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.index d))) (hd : d.site = .barrier) :
    d.block + 1 = totalBlocks (P.topkLen (ctaidY L g)) (P.extraTopkLen (ctaidY L g)) :=
  ht.prefix_induction (fun q _ => terminalBlock P L g q) trivial
    (fun _ _ _ _ _ _ => terminal_step) i (some (.index d)) hs hd

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.IndexRingTrace
