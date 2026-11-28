-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Seg
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexEntry
public import Lemmas.Flow.ShflU

@[expose] public section

/-! # Warpgroup 1's head and idle code: their obligations

The head's `setmaxnreg` steps to the shuffle; the shuffle's successor is the code's dispatch on
its word: the TMA or MMA election, the idle code's first event (`idleFirst`, by its cases), or
the index warp's first event (`ixFirst`, by its parameter prefix `ixw_entry`). The idle code's
loads continue by the extra pointer's test, its barrier to the return. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The facts after the head shuffle returned the word `x` with validity `ok`. -/
abbrev hshFacts (L : Launch) (g : Nat) (x : BitVec 64) (ok : Bool) : List (Nat × Value) :=
  (10, .pred ok) :: (558, .bits 32 x) :: Flow.factsFrom (Flow.live 1843) (entryVal L g)

theorem head_tma (x : BitVec 64) (ok : Bool) (h7 : ¬ scmpi .eq .b x 7 = true)
    (h5 : scmpi .eq .b x 5 = true) :
    ∃ n, Seg kernel Assumptions.all L g n 1844 (hshFacts L g x ok) 2165
      (Flow.factsFrom (Flow.live 2165) (entryVal L g)) := by
  seg_sym using w1_seg

theorem head_mma (x : BitVec 64) (ok : Bool) (h7 : ¬ scmpi .eq .b x 7 = true)
    (h5 : ¬ scmpi .eq .b x 5 = true) (h4 : ¬ scmpi .ne .b x 4 = true) :
    ∃ n, Seg kernel Assumptions.all L g n 1844 (hshFacts L g x ok) 1853
      (Flow.factsFrom (Flow.live 1853) (entryVal L g)) := by
  seg_sym using w1_seg

/-- **The head's dispatch to the idle code**: the dispatch's tests to pc 2587, then the idle
code's walk (`IdleWalk.walk`). -/
theorem head_idle (hp : Pre P L m) (x : BitVec 64) (ok : Bool)
    (h7 : ¬ scmpi .eq .b x 7 = true) (h5 : ¬ scmpi .eq .b x 5 = true)
    (h4 : scmpi .ne .b x 4 = true) :
    ∃ n, Seg kernel Assumptions.all L g n 1844 (hshFacts L g x ok) (idleFirst P L g).pc
      (idleEnd P L g (idleFirst P L g)) :=
  Seg.comp_ex (q := 2587) (H := idleWk0 L g) (by seg_sym using w1_seg) (IdleWalk.walk hp)

/-- **The head's dispatch to the index warp**: the dispatch's test to pc 2332, then the index
warp's parameter prefix (`ixw_entry`). -/
theorem head_index (hp : Pre P L m) (x : BitVec 64) (ok : Bool) (h7 : scmpi .eq .b x 7 = true) :
    SegU kernel Assumptions.all L g 1844 (hshFacts L g x ok) (ixFirst P L g).1.pc
      (ixFacts P L g (ixFirst P L g).2 (ixFirst P L g).1) := by
  obtain ⟨n, h⟩ : ∃ n, Seg kernel Assumptions.all L g n 1844 (hshFacts L g x ok) 2332
      (Flow.factsFrom (Flow.live 2332) (entryVal L g)) := by seg_sym using w1_seg
  exact SegU.comp (SegU.of_seg h) (ixw_entry hp)

/-- The head's sites but the shuffle: the `setmaxnreg` steps to the shuffle. -/
theorem stepAt_head0 (s : Site) (hx : exitOf s = none) (hh : s ≠ .hsh) :
    (code P L g).StepAt s := by
  site_cases s except [.hsh => (absurd rfl hh)]
    skip_by (simp [exitOf] at hx)
    trans [succ, dispatch]
    seg_by (w1_seg) inv_by (exact fun _ => trivial) guard_by (trivial)

/-- The dispatch never stops on a received word. -/
theorem dispatch_ne (v : Value) : dispatch v ≠ none := by
  simp only [dispatch]
  split
  · split_ifs <;> simp
  · simp

/-- **The head's shuffle**: its successor is the dispatch on its word, reached by the dispatch's
walk (`head_index`, `head_tma`, `head_idle`, `head_mma`). -/
theorem stepAt_hsh (hp : Pre P L m) : (code P L g).StepAtU .hsh := by
  refine Code.step_shflU (nv := fun v _ => dispatch v)
    (by code_lookup) (by fact_free) (by fact_free) (by decide) (fun _ _ _ _ _ _ => rfl) rfl rfl
    (fun v _ => dispatch_ne v) ?_
  intro v ok d' hv
  simp only [dispatch] at hv
  split at hv
  · rename_i x
    split_ifs at hv with h7 h5 h4 <;> simp only [Option.some.injEq] at hv <;>
      subst hv
    · exact ⟨rfl, rfl, trivial, head_index hp x ok h7⟩
    · obtain ⟨_, h⟩ := head_tma (L := L) (g := g) x ok h7 h5
      exact ⟨rfl, rfl, trivial, SegU.of_seg h⟩
    · obtain ⟨_, h⟩ := head_idle hp x ok h7 h5 h4
      exact ⟨rfl, rfl, trivial, SegU.of_seg h⟩
    · obtain ⟨_, h⟩ := head_mma (L := L) (g := g) x ok h7 h5 h4
      exact ⟨rfl, rfl, trivial, SegU.of_seg h⟩
  · simp at hv

/-- **The head**: its `setmaxnreg` steps to the shuffle, and the shuffle's successor is the
dispatch on its word. -/
theorem stepAt_head (hp : Pre P L m) (s : Site) (hx : exitOf s = none) :
    (code P L g).StepAtU s := by
  by_cases hh : s = .hsh
  · subst hh
    exact stepAt_hsh hp
  · exact (stepAt_head0 s hx hh).toStepAtU

/-- **The idle code.** -/
theorem stepAt_idle (hp : Pre P L m) (s : IdleSite) : (idle P L g).StepAt s := by
  have _hobj := p0_eq hp
  site_cases s
    trans [isucc, idleAfterA, afterNc]
    seg_by (w1_seg) inv_by (exact fun _ => trivial) guard_by (trivial)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1
