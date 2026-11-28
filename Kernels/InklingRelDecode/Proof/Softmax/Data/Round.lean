-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Shape
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Site

@[expose] public section

/-! # The words of the rounds, from the shuffles of pc 1838

The running maximum and the round's new maximum of the value machine as functions of the words the
thread's shuffles of pc 1838 sent and received (`roundWords`): the running maximum after the
rounds before is the fold of `mNext` over them. `RoundInv` is what the value state keeps of the
words, and `round_step` that it survives every step of the machine. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow Control

noncomputable section

/-- What a value state keeps of the words of the rounds before. -/
def RoundInv (L : Launch) (ps : List (Value × Value)) (y : D) : Prop :=
  (early y.c.site = true → ps = []) ∧
  (inRound y.c.site = false → y.v.m = mAfter (scaleW L) ps) ∧
  (inRound y.c.site = true → ∃ ps0 p, ps = ps0 ++ [p] ∧ y.v.m = mAfter (scaleW L) ps0 ∧
    y.v.mx = Lib.mxWord y.v.m p.1 p.2)

theorem round_init (L : Launch) : RoundInv L [] ({} : D) := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun h => ?_⟩
  cases h

private theorem site_1838 (s : Site) (h : s.pc = 1838) : s = .shfl5 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem round_early (s : Site) (h : early s = true) : inRound s = false := by
  cases s <;> simp_all [early, inRound]

/-- **The words survive a step.** -/
theorem round_step {e : Entry} {L : Launch} {g : Nat} {ps : List (Value × Value)} {old y : D}
    {ev : Event} (inv : RoundInv L ps old) (hn : succ e L g old ev = some (some y))
    (pc : ev.pc = old.c.site.pc) (kind : old.c.site = .shfl5 → ∃ m a b c r ok,
      ev.kind = .shfl m a b c r ok) : RoundInv L (ps ++ wordOf ev) y := by
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  obtain ⟨s5, out, inn, back⟩ := next_shape hnc
  obtain ⟨e1, e2, e3⟩ := inv
  by_cases h5 : old.c.site = .shfl5
  · obtain ⟨m, a, b, c, r, ok, hk⟩ := kind h5
    have hpc : ev.pc = 1838 := by rw [pc, h5]; rfl
    obtain ⟨p, k⟩ := ev
    change p = 1838 at hpc
    subst hpc
    change k = _ at hk
    subst hk
    have s6 := s5 h5
    have e2' := e2 (by rw [h5]; rfl)
    refine ⟨fun h => ?_, fun h => ?_, fun _ => ⟨ps, (a, r), rfl, ?_, ?_⟩⟩
    · rw [s6] at h; cases h
    · rw [s6] at h; cases h
    · simpa [record, h5] using e2'
    · simp [record, h5, e2']
  · have w : wordOf ev = [] := by
      obtain ⟨p, k⟩ := ev
      change p = old.c.site.pc at pc
      have : p ≠ 1838 := fun h => h5 (site_1838 _ (pc ▸ h))
      cases k <;> simp [wordOf, this]
    rw [w, List.append_nil]
    by_cases hr : inRound old.c.site = true
    · obtain ⟨ps0, p, hps, hm, hmx⟩ := e3 hr
      rcases inn hr with hr' | ⟨hb, hs⟩
      · have keep : (record L old ev c'.site).m = old.v.m ∧
            (record L old ev c'.site).mx = old.v.mx := by
          have nb : c'.site ≠ .bar20 := fun h => by rw [h] at hr'; cases hr'
          cases hs : old.c.site <;> simp_all [record, inRound]
          split <;> simp_all
        refine ⟨fun h => ?_, fun h => ?_, fun _ => ⟨ps0, p, hps, ?_, ?_⟩⟩
        · rw [e1 (back h)] at hps; simp at hps
        · rw [hr'] at h; cases h
        · exact keep.1.trans hm
        · exact keep.2.trans (hmx.trans (by rw [keep.1]))
      · have upd : (record L old ev c'.site).m = Lib.mNext (scaleW L) old.v.m old.v.mx := by
          rcases hs with hs | hs | hs <;> simp [record, hs, hb]
        refine ⟨fun h => ?_, fun _ => ?_, fun h => ?_⟩
        · rw [hb] at h; cases h
        · rw [upd, hps, mAfter_append]
          simp [hm, hmx]
        · rw [hb] at h; cases h
    · have hr0 : inRound old.c.site = false := by simpa using hr
      have n1 := out h5 hr0
      have back' : early c'.site = true → ps = [] := fun h => e1 (back h)
      refine ⟨back', fun h => ?_, fun h => by rw [n1] at h; cases h⟩
      by_cases hearly : early old.c.site = true
      · have ps0 := e1 hearly
        subst ps0
        have hm : old.v.m = b32 4286578688 := by simpa [mAfter] using e2 hr0
        simp only [mAfter, List.foldl_nil]
        cases hs : old.c.site <;> simp only [early, hs, Bool.false_eq_true] at hearly
        · simp [record, hs, hm]
        · simp only [record, hs]; split <;> simp_all
        · simp only [record, hs]; split <;> (try split_ifs) <;> simp_all
      · have keep : (record L old ev c'.site).m = old.v.m := by
          refine record_m ev _ (fun h => ?_) (fun h => ?_) (fun h => ?_) (fun h => ?_)
            (fun j h => ?_) <;> simp_all [early, inRound]
        simpa [keep] using e2 hr0

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
