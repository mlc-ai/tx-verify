-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Addr
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Sites

@[expose] public section

/-! # Warpgroup 0's LSE store site

The LSE store (`lse`, pc 1178) is entered only from the row-sum read (`eld`), and only when the
thread index word is below 64 (`afterEld`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

private theorem tcLoad_eq {e : Event} {d d' : D} {s : Site}
    (h : tcLoad e d s = some (some d')) : d' = { d with site := s } := by
  unfold tcLoad at h; split at h
  · exact (Option.some.inj (Option.some.inj h)).symm
  · cases h

set_option linter.unusedSimpArgs false in
/-- **The state before the LSE store's** is the row-sum read, with the word below 64. -/
theorem lse_pred {d d' : D} {e : Event} (hn : succ P L g w d e = some (some d'))
    (hs : d'.site = .lse) : d.site = .eld ∧ scmp .ge .s (r5W L g) (pw 64) = false := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  have nn : ∀ {x : Option (Option D)}, x = some (some d') →
      (∀ y, x = some (some y) → y.site ≠ Site.lse) → False := fun hx hy => by
    exact hy _ hx hs
  cases s
  case eld =>
    refine ⟨rfl, ?_⟩
    simp only [succ, dataRd] at hn; split at hn <;>
      simp only [Option.some.injEq, reduceCtorEq] at hn
    all_goals subst hn; revert hs; unfold afterEld; split_ifs with h <;> simp [h]
  case exit => simp [succ] at hn
  case sink =>
    exfalso; refine nn hn fun y hy => ?_
    simp only [succ, dataRd] at hy; split at hy <;>
      simp only [Option.some.injEq, reduceCtorEq] at hy
    all_goals subst hy; unfold afterSink afterA finish; split_ifs <;> simp
  case vm | mld =>
    exfalso; refine nn hn fun y hy => ?_
    simp only [succ, dataRd] at hy; split at hy <;>
      simp only [Option.some.injEq, reduceCtorEq] at hy
    all_goals subst hy; simp
  case lenA | lenB =>
    exfalso; refine nn hn fun y hy => ?_
    simp only [succ, ncWord] at hy; split at hy
    · split at hy <;>
      simp only [Option.some.injEq, reduceCtorEq] at hy
      subst hy
      (try unfold afterA); (try split_ifs) <;> simp
    · cases hy
  case wv | wq | wsv =>
    exfalso; refine nn hn fun y hy => ?_
    simp only [succ, poll] at hy; split at hy <;>
      simp only [Option.some.injEq, reduceCtorEq] at hy
    subst hy; split_ifs <;> simp
  case sld a k =>
    exfalso; refine nn hn fun y hy => ?_
    fin_cases k <;> simp only [succ] at hy <;> rw [tcLoad_eq hy] <;> simp
  case rld k | old k =>
    exfalso; refine nn hn fun y hy => ?_
    simp only [succ] at hy; rw [tcLoad_eq hy]; simp
  case pld k =>
    exfalso; refine nn hn fun y hy => ?_
    simp only [succ] at hy; split at hy
    · split at hy <;> simp only [Option.some.injEq] at hy <;> subst hy
      · simp
      · fin_cases k <;> simp
    · cases hy
  case vote =>
    exfalso; refine nn hn fun y hy => ?_
    simp only [succ] at hy; split at hy <;>
      simp only [Option.some.injEq, reduceCtorEq] at hy
    subst hy; simp
  case arrS =>
    exfalso; refine nn hn fun y hy => ?_
    simp only [succ] at hy; split at hy <;> simp only [Option.some.injEq] at hy <;> subst hy <;>
      simp
  case oel k =>
    exfalso; refine nn hn fun y hy => ?_
    simp only [succ] at hy; split at hy
    · cases hy; split_ifs <;> (try fin_cases k) <;> simp [nextChunk]
    · cases hy
  all_goals simp only [succ, Option.some.injEq] at hn
  all_goals subst hn
  case smr => exfalso; revert hs; unfold afterSmr afterSink afterA finish; split_ifs <;> simp
  case arrL => exfalso; revert hs; unfold loopEntry; split_ifs <;> simp
  case pst k => exfalso; revert hs; fin_cases k <;> simp
  case ost k =>
    exfalso; revert hs; unfold elemNext afterOst; fin_cases k <;> split_ifs <;> simp
  case rstw k => exfalso; revert hs; fin_cases k <;> simp
  case ost2 cc k =>
    exfalso; revert hs; unfold elemNext; fin_cases k <;> split_ifs <;> simp
  case obar k =>
    exfalso; revert hs; unfold afterObar nextChunk; split_ifs <;> fin_cases k <;> simp
  case otma k => exfalso; revert hs; unfold nextChunk; fin_cases k <;> simp
  case ebar => exfalso; revert hs; unfold finish; split_ifs <;> simp
  all_goals exfalso; simp at hs


set_option linter.unusedSimpArgs false in
/-- **The state before the sink's** is the first state, with the pointer set and the head
below 64. -/
theorem sink_pred {d d' : D} {e : Event} (hn : succ P L g w d e = some (some d'))
    (hs : d'.site = .sink) : d.site = .smr ∧ eqz64 (pw8 (P.sinkBase.getD 0)) = false ∧
      scmp .ge .s (r10W L g) (pw 64) = false := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  have nn : ∀ {x : Option (Option D)}, x = some (some d') →
      (∀ y, x = some (some y) → y.site ≠ Site.sink) → False := fun hx hy => by
    exact hy _ hx hs
  cases s
  case smr =>
    refine ⟨rfl, ?_⟩
    simp only [succ, Option.some.injEq] at hn
    subst hn
    revert hs
    unfold afterSmr
    split_ifs with h
    · unfold afterSink afterA finish; split_ifs <;> simp
    · intro _
      simpa [Bool.or_eq_true] using h
  case exit => simp [succ] at hn
  case sink =>
    exfalso; refine nn hn fun y hy => ?_
    simp only [succ, dataRd] at hy; split at hy <;>
      simp only [Option.some.injEq, reduceCtorEq] at hy
    all_goals subst hy; unfold afterSink afterA finish; split_ifs <;> simp
  case eld =>
    exfalso; refine nn hn fun y hy => ?_
    simp only [succ, dataRd] at hy; split at hy <;>
      simp only [Option.some.injEq, reduceCtorEq] at hy
    all_goals subst hy; unfold afterEld; split_ifs <;> simp
  case vm | mld =>
    exfalso; refine nn hn fun y hy => ?_
    simp only [succ, dataRd] at hy; split at hy <;>
      simp only [Option.some.injEq, reduceCtorEq] at hy
    all_goals subst hy; simp
  case lenA | lenB =>
    exfalso; refine nn hn fun y hy => ?_
    simp only [succ, ncWord] at hy; split at hy
    · split at hy <;>
      simp only [Option.some.injEq, reduceCtorEq] at hy
      subst hy
      (try unfold afterA); (try split_ifs) <;> simp
    · cases hy
  case wv | wq | wsv =>
    exfalso; refine nn hn fun y hy => ?_
    simp only [succ, poll] at hy; split at hy <;>
      simp only [Option.some.injEq, reduceCtorEq] at hy
    subst hy; split_ifs <;> simp
  case sld a k =>
    exfalso; refine nn hn fun y hy => ?_
    fin_cases k <;> simp only [succ] at hy <;> rw [tcLoad_eq hy] <;> simp
  case rld k | old k =>
    exfalso; refine nn hn fun y hy => ?_
    simp only [succ] at hy; rw [tcLoad_eq hy]; simp
  case pld k =>
    exfalso; refine nn hn fun y hy => ?_
    simp only [succ] at hy; split at hy
    · split at hy <;> simp only [Option.some.injEq] at hy <;> subst hy
      · simp
      · fin_cases k <;> simp
    · cases hy
  case vote =>
    exfalso; refine nn hn fun y hy => ?_
    simp only [succ] at hy; split at hy <;>
      simp only [Option.some.injEq, reduceCtorEq] at hy
    subst hy; simp
  case arrS =>
    exfalso; refine nn hn fun y hy => ?_
    simp only [succ] at hy; split at hy <;> simp only [Option.some.injEq] at hy <;> subst hy <;>
      simp
  case oel k =>
    exfalso; refine nn hn fun y hy => ?_
    simp only [succ] at hy; split at hy
    · cases hy; split_ifs <;> (try fin_cases k) <;> simp [nextChunk]
    · cases hy
  all_goals simp only [succ, Option.some.injEq] at hn
  all_goals subst hn
  case arrL => exfalso; revert hs; unfold loopEntry; split_ifs <;> simp
  case pst k => exfalso; revert hs; fin_cases k <;> simp
  case ost k =>
    exfalso; revert hs; unfold elemNext afterOst; fin_cases k <;> split_ifs <;> simp
  case rstw k => exfalso; revert hs; fin_cases k <;> simp
  case ost2 cc k =>
    exfalso; revert hs; unfold elemNext; fin_cases k <;> split_ifs <;> simp
  case obar k =>
    exfalso; revert hs; unfold afterObar nextChunk; split_ifs <;> fin_cases k <;> simp
  case otma k => exfalso; revert hs; unfold nextChunk; fin_cases k <;> simp
  case ebar => exfalso; revert hs; unfold finish; split_ifs <;> simp
  all_goals exfalso; simp at hs

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
