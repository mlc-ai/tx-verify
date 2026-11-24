-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvWLoaderSpec
public import Lemmas.Flow.AllocTmpl

@[expose] public section

/-!
# The loader's block-table words: the pure part

Moved from the first tree's `Proof/Interface/ShapeLoaderPage.lean` (`slabPage`, `LoaderPage` and
its step lemmas, `slabPage_lt`) and `Proof/Result/MmaOperand.lean` (`blk_lt`), names and namespaces
unchanged, so the second tree states the loader's page invariant without the first tree's
interface. `LoaderPage`: from the read of `num_iters` on, the loop bound is the CTA's
`num_iters`; from the load of `p0` (`p1`) on, it is the page of the slab of the iteration.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX PTX.Proof

/-- **A block below `num_iters` is a block of the request.** -/
theorem blk_lt {Q : Params} {r s i : Nat} (hs : 0 < Q.splits)
    (h : i < Q.numIters r s) : s + i * Q.splits < Q.blocks r := by
  unfold Params.numIters at h
  have h1 := (Nat.le_div_iff_mul_le hs).mp (show i + 1 ≤ _ from h)
  have h2 : (i + 1) * Q.splits = i * Q.splits + Q.splits := by ring
  omega

end PTX.Kernels.InklingRelDecode.Proof.Result.Mma

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0}

/-- The block-table word of slab `slab` of iteration `i` of the CTA of thread `g`. -/
def slabPage (Q : Params) (L : Launch) (g i slab : Nat) : Nat :=
  Q.page (ProA.cta L g .z) (2 * (ProA.cta L g .x + i * Q.splits) + slab)

/-- The sites from the load of `p0` on, within the iteration. -/
def p0Site : Loader.Site → Bool
  | .wb1 | .el0 | .cp0a | .cp0b | .wb2 | .el1 | .cp1a | .cp1b | .ldb1 | .wb3 | .el2 | .cp2a
  | .cp2b | .wb4 | .el3 | .cp3a | .cp3b => true
  | _ => false

/-- The sites from the load of `p1` on, within the iteration. -/
def p1Site : Loader.Site → Bool
  | .wb3 | .el2 | .cp2a | .cp2b | .wb4 | .el3 | .cp3a | .cp3b => true
  | _ => false

/-- The sites before `num_iters` is read. -/
def preLoop : Loader.Site → Bool
  | .setMaxDec | .ld0 | .ld1 => true
  | _ => false

/-- **What a loader state keeps about the words.** From the read of `num_iters` on, `n` is the
CTA's `num_iters`; from the load of `p0` (`p1`) on, it is the page of the slab of the current
iteration. -/
def LoaderPage (Q : Params) (L : Launch) (g : Nat) (d : Loader.D) : Prop :=
  (preLoop d.site = false → d.n = Q.numIters (ProA.cta L g .z) (ProA.cta L g .x)) ∧
  (p0Site d.site = true → d.p0 = slabPage Q L g d.i 0) ∧
  (p1Site d.site = true → d.p1 = slabPage Q L g d.i 1)

theorem lp_step_other {g : Nat} {d d' : Loader.D} {e : Event}
    (hd : LoaderPage Q L g d) (hs1 : d.site ≠ .ld1) (hs2 : d.site ≠ .ldb0)
    (hs3 : d.site ≠ .ldb1) (h : Loader.next L g d e = some (some d')) :
    LoaderPage Q L g d' := by
  obtain ⟨hn, hp0, hp1⟩ := hd
  unfold Loader.next Loader.afterIter at h
  cases hsite : d.site <;> rw [hsite] at h hn hp0 hp1 <;> dsimp only at h <;>
    simp only [preLoop, p0Site, p1Site, Bool.false_eq_true, Bool.true_eq_false,
      forall_const] at hn hp0 hp1
  all_goals first
    | exact absurd hsite hs1
    | exact absurd hsite hs2
    | exact absurd hsite hs3
    | (repeat' split at h
       all_goals first
         | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
         | (simp only [Option.some.injEq] at h
            subst h
            refine ⟨?_, ?_, ?_⟩ <;> simp [preLoop, p0Site, p1Site, Loader.readI] <;> simp_all))

/-- The read of `num_iters` sets `n`. -/
theorem lp_step_ld1 {g : Nat} {d d' : Loader.D} {e : Event} {pc : Nat} {ac : Acc}
    {bs : List (Option Byte)} (hd : LoaderPage Q L g d) (hs : d.site = .ld1)
    (he : e = ⟨pc, .rd ac bs⟩)
    (hN : Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) < 2 ^ 32)
    (hbs : bs = (b32 (Q.numIters (ProA.cta L g .z) (ProA.cta L g .x))).toBytes.map some)
    (h : Loader.next L g d e = some (some d')) : LoaderPage Q L g d' := by
  obtain ⟨hn, hp0, hp1⟩ := hd
  subst he hbs
  unfold Loader.next at h
  rw [hs] at h hn hp0 hp1
  dsimp only at h
  simp only [rebuild_b32, Option.some.injEq] at h
  subst h
  refine ⟨fun _ => ?_, ?_, ?_⟩
  · simp only [Loader.readN, Raw.word32Of_b32, Option.getD_some]
    exact Nat.mod_eq_of_lt hN
  · simp [Loader.readN, p0Site]
  · simp [Loader.readN, p1Site]

/-- The block-table loads set `p0` and `p1`. -/
theorem lp_step_ldb {g : Nat} {d d' : Loader.D} {e : Event} {pc : Nat} {ac : Acc}
    {bs : List (Option Byte)} {slab : Nat} (hd : LoaderPage Q L g d)
    (hs : (slab = 0 ∧ d.site = .ldb0) ∨ (slab = 1 ∧ d.site = .ldb1))
    (he : e = ⟨pc, .rd ac bs⟩) (hpg : slabPage Q L g d.i slab < 2 ^ 32)
    (hbs : bs = (b32 (slabPage Q L g d.i slab)).toBytes.map some)
    (h : Loader.next L g d e = some (some d')) : LoaderPage Q L g d' := by
  obtain ⟨hn, hp0, hp1⟩ := hd
  subst he hbs
  unfold Loader.next at h
  rcases hs with ⟨rfl, hs⟩ | ⟨rfl, hs⟩
  · rw [hs] at h hn hp0 hp1
    dsimp only at h
    simp only [rebuild_b32] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      rename_i x hx
      have : x = slabPage Q L g d.i 0 := by
        rw [Raw.word32Of_b32] at hx
        simp only [Option.some.injEq] at hx
        rw [← hx]
        exact Nat.mod_eq_of_lt (by omega)
      refine ⟨by simpa [preLoop] using hn, ?_, ?_⟩ <;> simp [p0Site, p1Site, this]
    · cases h
  · rw [hs] at h hn hp0 hp1
    dsimp only at h
    simp only [rebuild_b32] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      rename_i x hx
      have : x = slabPage Q L g d.i 1 := by
        rw [Raw.word32Of_b32] at hx
        simp only [Option.some.injEq] at hx
        rw [← hx]
        exact Nat.mod_eq_of_lt (by omega)
      refine ⟨by simpa [preLoop] using hn, ?_, ?_⟩
      · simpa [p0Site] using hp0
      · simp [p1Site, this]
    · cases h

theorem loaderPage_start {g : Nat} {d : Loader.D} (h : d.site = .setMaxDec) :
    LoaderPage Q L g d := by
  simp [LoaderPage, preLoop, p0Site, p1Site, h]

/-- **A page is a row below `2 ^ 31`**: the slab of a block that exists lies inside the map. -/
theorem slabPage_lt (hpre : Pre Q L mem0) {g : Nat} (hg : g < L.threads) {i : Nat}
    (hi : i < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x)) {slab : Nat} (hs : slab ≤ 1) :
    slabPage Q L g i slab < 2 ^ 31 := by
  obtain ⟨hx, hy, hz⟩ := ProA.cta_lt hpre hg
  have hblk := Result.Mma.blk_lt hpre.splitsPos hi
  have hin := hpre.slabInside _ hz (2 * (ProA.cta L g .x + i * Q.splits) + slab) (by omega)
    (ProA.cta L g .y) hy
  have hrr := hpre.rowsRange
  have hpr := hpre.pageRowsPos
  have : slabPage Q L g i slab ≤ slabPage Q L g i slab * Q.pageRows :=
    Nat.le_mul_of_pos_right _ hpr
  unfold slabPage at *
  omega

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
