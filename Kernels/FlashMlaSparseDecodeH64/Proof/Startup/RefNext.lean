-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Ref
public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Shape
import Lemmas.Flow.AllocTmpl

@[expose] public section

/-! # The startup's reference invariant is kept by every step

`refNext`: from a state with `Ref` and `RefW` (with `mi` initializations, `b0` barrier-0 events
and `sh` shuffles before it), an event of its shape leads to a state with both, at the counts
bumped by the event (the ledger `up`). One fact comes from other lanes, as a premise: `hrecv`,
the shuffle's word: what the source lane sent, the launch's warpgroup word at the first shuffle
and its warp word at the second (`Common/Recv.lean`, `startup_recv`). The read-back at pc 92
may read any word: a zero word goes on to the relinquishment, any other to the `trap`, which
keeps the read-back's counts. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

/-- The count of a class after event `e`. -/
abbrev up (p : Event → Bool) (n : Nat) (e : Event) : Nat := n + if p e then 1 else 0

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The warp word is `0` only in warp 0. -/
theorem warpW_ne (hp : Pre P L m) :
    scmpi .ne .b (warpW L g) 0 = decide (warpOf L g ≠ 0) := by
  have := warpOf_lt (g := g) hp
  exact scmpi_ne_b_W (by omega) (by decide) (by decide)

/-- **The first state has the reference invariant** (no event before it). -/
theorem ref_init : Ref (code L g).init 0 0 ∧ RefW L g (code L g).init 0 := by
  simp [Ref, RefW]

/-- **The reference invariant is kept by every startup step.** -/
theorem refNext (hp : Pre P L m) {d d' : D} {e : Event} {mi b0 sh : Nat}
    (hR : Ref d mi b0) (hW : RefW L g d sh) (hev : Ev L g d e)
    (hs : succ L g d e = some (some d'))
    (hrecv : ∀ a r ok, e.kind = .shfl .idx a 0 31 r ok →
      r = w32 (if sh = 0 then wgW L g else warpW L g)) :
    Ref d' (up isMbInit mi e) (up isBar0 b0 e) ∧ RefW L g d' (up Execution.isShfl sh e) := by
  obtain ⟨pc, kd⟩ := e
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | sh j =>
    rcases j with ⟨_ | _ | _, hj⟩
    · obtain ⟨r, ok, hk⟩ := hev
      simp only at hk
      subst hk
      obtain ⟨hsh, -⟩ := hW
      have hr := hrecv _ r ok rfl
      simp only at hsh
      subst hsh
      simp only [↓reduceIte] at hr
      subst hr
      simp only [succ, word32, Option.some.injEq] at hs
      subst hs
      obtain ⟨h1, h2⟩ := hR
      simp [Ref, RefW, up, isMbInit, isBar0, Execution.isShfl, h1, h2]
    · obtain ⟨r, ok, hk⟩ := hev
      simp only at hk
      subst hk
      obtain ⟨hsh, hx1⟩ := hW
      have hr := hrecv _ r ok rfl
      dsimp only at hx1
      simp only [Nat.zero_add] at hsh
      subst hsh
      simp only [one_ne_zero, ↓reduceIte] at hr
      subst hr
      have hx1' := hx1 rfl
      obtain ⟨h1, h2⟩ := hR
      simp only [succ, word32, warpW_ne hp] at hs
      by_cases hw : warpOf L g = 0
      · simp only [hw, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
          Option.some.injEq] at hs
        subst hs
        simp [Ref, RefW, up, isMbInit, isBar0, Execution.isShfl, h1, h2, hx1', hw]
      · simp only [hw, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, Option.some.injEq] at hs
        subst hs
        simp [Ref, RefW, up, isMbInit, isBar0, Execution.isShfl, h1, h2, hx1']
    · omega
  | elect j =>
    obtain ⟨inst, ld, -, hk⟩ := hev
    simp only at hk
    subst hk
    obtain ⟨h1, h2⟩ := hR
    obtain ⟨hsh, hx1, hx2, hw⟩ := hW
    dsimp only at hx1 hx2
    rcases j with ⟨_ | _ | _, hj⟩
    · simp only [succ, Option.some.injEq] at hs
      subst hs
      simp [Ref, RefW, up, isMbInit, isBar0, Execution.isShfl, h1, h2, hsh, hx1, hx2, hw]
    · simp only [succ, Option.some.injEq] at hs
      split_ifs at hs <;> subst hs <;>
        simp [Ref, RefW, up, isMbInit, isBar0, Execution.isShfl, h1, h2, hsh, hx1, hx2, hw]
    · omega
  | init n =>
    simp only [Ev] at hev
    subst hev
    obtain ⟨h1, h2⟩ := hR
    obtain ⟨hsh, hx1, hx2, hw⟩ := hW
    dsimp only at hx1 hx2
    simp only [succ, Option.some.injEq] at hs
    subst hs
    simp only [initSucc]
    split
    · simp [Ref, RefW, up, isMbInit, isBar0, Execution.isShfl, h1, h2, hsh, hx1, hx2, hw]
    · rename_i hlt
      have hn : n.val = 22 := by have := n.isLt; omega
      simp [Ref, RefW, up, isMbInit, isBar0, Execution.isShfl, h1, h2, hsh, hx1, hx2, hw, hn]
  | fence =>
    simp only [Ev] at hev
    subst hev
    obtain ⟨h1, h2⟩ := hR
    obtain ⟨hsh, hx1, hx2, hw⟩ := hW
    dsimp only at hx1 hx2
    simp only [succ, Option.some.injEq] at hs
    subst hs
    simp [Ref, RefW, up, isMbInit, isBar0, Execution.isShfl, h1, h2, hsh, hx1, hx2, hw]
  | alloc =>
    simp only [Ev] at hev
    subst hev
    obtain ⟨h1, h2⟩ := hR
    obtain ⟨hsh, hx1, hx2, hw⟩ := hW
    dsimp only at hx1 hx2
    simp only [succ, Option.some.injEq] at hs
    split_ifs at hs <;> subst hs <;>
      simp [Ref, RefW, up, isMbInit, isBar0, Execution.isShfl, h1, h2, hsh, hx1, hx2, hw]
  | allocSt =>
    obtain ⟨col, -, hk⟩ := hev
    simp only at hk
    subst hk
    obtain ⟨h1, h2⟩ := hR
    obtain ⟨hsh, hx1, hx2, hw⟩ := hW
    dsimp only at hx1 hx2
    simp only [succ, Option.some.injEq] at hs
    subst hs
    simp [Ref, RefW, up, isMbInit, isBar0, Execution.isShfl, h1, h2, hsh, hx1, hx2, hw]
  | ld =>
    obtain ⟨h1, h2⟩ := hR
    obtain ⟨hsh, hx1, hx2, hw⟩ := hW
    dsimp only at hx1 hx2
    simp only [succ] at hs
    split at hs
    · split at hs
      · simp only [afterLd] at hs
        split at hs
        · split_ifs at hs <;> simp only [Option.some.injEq] at hs <;> subst hs <;>
            simp [Ref, RefW, up, isMbInit, isBar0, Execution.isShfl, h1, h2, hsh, hx1, hx2, hw]
        · cases hs
      · cases hs
    · cases hs
  | trap => simp [succ] at hs
  | relinq =>
    simp only [Ev] at hev
    subst hev
    obtain ⟨h1, h2⟩ := hR
    obtain ⟨hsh, hx1, hx2, hw⟩ := hW
    dsimp only at hx1 hx2
    simp only [succ, Option.some.injEq] at hs
    subst hs
    simp [Ref, RefW, up, isMbInit, isBar0, Execution.isShfl, h1, h2, hsh, hx1, hx2]
  | bar =>
    simp only [Ev] at hev
    subst hev
    obtain ⟨h1, h2⟩ := hR
    obtain ⟨hsh, hx1, hx2⟩ := hW
    dsimp only at hx1 hx2
    simp only [succ, Option.some.injEq] at hs
    subst hs
    simp only [enterOf]
    split_ifs <;>
      simp [Ref, RefW, up, isMbInit, isBar0, Execution.isShfl, h1, h2, hsh, hx1, hx2]
  | enter r => simp [succ] at hs

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
