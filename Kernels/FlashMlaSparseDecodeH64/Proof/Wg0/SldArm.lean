-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.OutSeq

@[expose] public section

/-! # The stage of warpgroup 0's score loads

The two score loads of a block are one of two sites (`sld arm k`, pcs 278 and 280 or 283 and 285):
`arm` is the machine's warp word's comparison with `1`, fixed when the block's fence is passed
(`tcfa`), and carried to the second load. So a step into a score-load site keeps the invariant
"every score-load site's `arm` is that comparison" (`sld_succ`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The `arm` of a score-load site is the warp word's comparison. -/
def SldOk (w : BitVec 64) (d : D) : Prop :=
  ∀ a k, d.site = .sld a k → a = scmpi .gt .s w 1

private theorem getD_not_sld {l : List Site} {n : Nat} {dflt : Site}
    (hl : ∀ x ∈ l, ∀ a k, x ≠ .sld a k) (hd : ∀ a k, dflt ≠ .sld a k) :
    ∀ a k, l.getD n dflt ≠ .sld a k := by
  rw [List.getD_eq_getElem?_getD, List.getD_getElem?]
  split
  · exact hl _ (List.getElem_mem _)
  · exact hd

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
/-- **A step keeps the score loads' arm.** -/
theorem sld_succ {d d' : D} {e : Event} (hn : succ P L g w d e = some (some d'))
    (hd : SldOk w d) : SldOk w d' := by
  intro a k hk
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases s
  case tcfa =>
    simp only [succ, Option.some.injEq] at hn
    subst hn
    simp only [Site.sld.injEq] at hk
    exact hk.1.symm
  case sld arm k0 =>
    have h0 := hd arm k0 rfl
    have hk0 : k0 = 0 ∨ k0 = 1 := by omega
    rcases hk0 with rfl | rfl <;> simp only [succ, tcLoad] at hn <;> split at hn <;>
      simp only [Option.some.injEq, reduceCtorEq] at hn <;> (try subst hn) <;>
      (try (cases hk; done)) <;> (try simp only [Site.sld.injEq] at hk) <;>
      (try simp only [hk.1] at h0) <;> try exact h0
  all_goals
    simp only [succ, afterSmr, afterSink, afterA, finish, loopEntry, afterObar, nextChunk,
      afterEld, elemNext, afterOst, dataRd, ncWord, poll, tcLoad, advance] at hn
    (try split at hn) <;> (try split at hn) <;> (try split at hn) <;> (try split at hn) <;>
    simp only [Option.some.injEq, reduceCtorEq] at hn <;>
    (try split_ifs at hn) <;> (try subst hn) <;> (try simp only at hk) <;>
      (try (cases hk; done)) <;>
      (try exact absurd hk (getD_not_sld (by simp) (by simp) _ _))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
