-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoader
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsBar2
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsWarp
public import Lemmas.Flow.NotTcAny

@[expose] public section

/-! # The loader's part of the warp-level premises

No loader site is a `tcgen05` instruction (`kernel_tc_pcs`, `Loader.site_not_tc`), so a thread
of warp 14 makes no `tcgen05` event (`Cross.loader_no_tc`), and no named-barrier event
(`bar_warp13`). The premises `TcAgree`, `TcExitAgree`, `TcExitAbove` and `BarAgree` hold for
two lanes of warp 14 vacuously or with both counts zero. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Loader

/-- The kernel's `tcgen05` instructions. -/
abbrev tcPcs : List Nat :=
  Flow.tmemAlloc.toList ++ Flow.mma.toList ++ Flow.tcCommit.toList ++
    Flow.tmemRelinquish.toList ++ Flow.tmemDealloc.toList ++ Flow.tmemLoad.toList ++
    Flow.tmemStore.toList ++ Flow.tmemWait.toList

theorem kernel_tc_pcs : OpPcsFast kernel.code tcAnyOp tcPcs = true := by
  decide +kernel

theorem site_not_tc (s : Site) : s.pc ∉ tcPcs := by
  cases s <;> site_decide

end Loader

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **A thread of warp 14 makes no `tcgen05` event.** -/
theorem Cross.loader_no_tc {g k pc : Nat} {kd : TcKind} (hw : warpOf L g = 14) :
    X.get (g, k) ≠ some ⟨pc, .tc kd⟩ := by
  intro he
  obtain ⟨d, t, ins, o, -, -, -, -, hc, hf⟩ :=
    Loader.origin hpre hX ht he nofun (by simp [Prologue.ProKind]) hw
  have hop : tcAnyOp ins.op = true := by
    by_contra hne
    exact fires_notTc (by simpa using hne) hf kd rfl
  exact Loader.site_not_tc d.site (OpPcsFast.mem Loader.kernel_tc_pcs hc hop)

/-- A thread of warp 14 makes no warp-collective `tcgen05` event. -/
theorem Cross.loader_tcColl {g k : Nat} {ev : Event} (hw : warpOf L g = 14)
    (he : X.get (g, k) = some ev) : isTcColl ev = false := by
  obtain ⟨pc, kd⟩ := ev
  cases kd <;> try rfl
  exact absurd he (Cross.loader_no_tc hpre hX ht hw)

theorem Cross.loader_tcColl_count {g k : Nat} (hw : warpOf L g = 14) :
    ((X.tr g).take k).countP isTcColl = 0 := by
  refine List.countP_eq_zero.mpr fun ev hev => ?_
  obtain ⟨j, -, hj⟩ := get_of_mem_take hev
  simp [Cross.loader_tcColl hpre hX ht hw hj]

/-- **`Cross.TcAgree` for warp 14**: vacuous. -/
theorem Cross.TcAgree_loader : ∀ {g h k k' pc pc' n : Nat} {kd kd' : TcKind} {d d' : ThreadD},
    warpOf L g = 14 → SameWarp L g h →
    St L X g k = some (some d) → St L X h k' = some (some d') →
    X.get (g, k) = some ⟨pc, .tc kd⟩ → X.get (h, k') = some ⟨pc', .tc kd'⟩ →
    X.TcK (g, k) n → X.TcK (h, k') n → pc = pc' ∧ tcStatic kd = tcStatic kd' := by
  intro g h k k' pc pc' n kd kd' d d' hw _ _ _ he
  exact absurd he (Cross.loader_no_tc hpre hX ht hw)

/-- **`Cross.TcExitAgree` for warp 14**: both lanes exit with no `tcgen05` event. -/
theorem Cross.TcExitAgree_loader : ∀ {g h k k' pc pc' : Nat} {d d' : ThreadD},
    warpOf L g = 14 → SameWarp L g h →
    St L X g k = some (some d) → St L X h k' = some (some d') →
    X.get (g, k) = some ⟨pc, .exit⟩ → X.get (h, k') = some ⟨pc', .exit⟩ →
    ((X.tr g).take k).countP isTcColl = ((X.tr h).take k').countP isTcColl := by
  intro g h k k' pc pc' d d' hw hs _ _ _ _
  rw [Cross.loader_tcColl_count hpre hX ht hw,
    Cross.loader_tcColl_count hpre hX ht (by have := hs.2; simp only [warpOf] at hw ⊢; omega)]

/-- **`Cross.TcExitAbove` for warp 14**: vacuous. -/
theorem Cross.TcExitAbove_loader : ∀ {g h k k' pc n : Nat} {d d' : ThreadD},
    warpOf L g = 14 → SameWarp L g h →
    St L X g k = some (some d) → St L X h k' = some (some d') →
    X.get (h, k') = some ⟨pc, .exit⟩ → X.TcK (g, k) n →
    n < ((X.tr h).take k').countP isTcColl := by
  intro g h k k' pc n d d' hw _ _ _ _ hK
  obtain ⟨⟨ev, he, hc⟩, -⟩ := hK
  rw [Cross.loader_tcColl hpre hX ht hw he] at hc
  cases hc

/-- **`Cross.BarAgree` for warp 14**: vacuous (no thread of warps 13-15 makes a named-barrier
event, `bar_warp13`). -/
theorem Cross.BarAgree_loader : ∀ {g h i j : Nat} {x y : Event}, warpOf L g = 14 →
    SameWarp L g h → X.get (g, i) = some x → X.get (h, j) = some y →
    Execution.isBar x = true → Execution.isBar y = true →
    ((X.tr g).take i).countP Execution.isBar = ((X.tr h).take j).countP Execution.isBar →
      x = y := by
  intro g h i j x y hw _ hx _ hbx _ _
  obtain ⟨pc, kd⟩ := x
  cases kd <;> simp only [Execution.isBar, Bool.false_eq_true] at hbx
  have := Cross.bar_warp13 hpre hX ht hx
  omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof
