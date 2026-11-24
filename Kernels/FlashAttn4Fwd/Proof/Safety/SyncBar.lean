-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Stats
public import Lemmas.Protocol.NamedBarWarp
public import Lemmas.CtaBarrier.CtaBarrierExecution
public import Lemmas.Execution.ShapeExecution

@[expose] public section

/-! # `BarMismatch` and the `barrier{.cta}` aligned clauses, from the statistics facts

The two clauses of `BarMismatch`:

1. Two lanes of a warp at one barrier ordinal make the same event (`StatsFacts.bar_warp`).
2. `BarArriveMismatch`: again the lanes of a warp make the same event
   (`NamedBar.WarpBars.not_barArriveMismatch`).

The `barrier{.cta}` clauses of `AlignedMismatch`: lanes of a warp at one barrier ordinal make the
same event, so they do not diverge (`no_barDivergent`), and no barrier is a whole-CTA aligned
barrier, since every `bar` names its thread count (`no_barExited`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Safety

open PTX PTX.Proof NamedBar

noncomputable section

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **No barrier mismatch.** -/
theorem no_barMismatch (ht : StatsFacts L X) : ¬ BarMismatch L X := by
  rintro (⟨g, h, i, j, id, id', count, count', pc, pc', hs, hgi, hhj, hord, hne⟩ | h)
  · have heq := ht.bar_warp.same_event hs (fun _ h => h) hgi hhj (by simp [Execution.isBar])
      (by simp [Execution.isBar]) hord
    simp only [Event.mk.injEq, Kind.bar.injEq] at heq
    obtain ⟨rfl, rfl, rfl, -⟩ := heq
    simp at hne
  · exact ht.bar_warp.not_barArriveMismatch h

/-- **No two lanes of a warp diverge at a `barrier{.cta}`**: at one barrier ordinal they make
the same event, at the same position. -/
theorem no_barDivergent (ht : StatsFacts L X) : ¬ AlignedClass.bar.Divergent L kernel X := by
  rw [AlignedClass.divergent_bar_iff]
  rintro ⟨g, h, i, j, id, id', count, count', mode, mode', pc, pc', hs, hgi, hhj, hord, -, hne⟩
  have heq := ht.bar_warp.same_event hs (fun _ h => h) hgi hhj (by simp [Execution.isBar])
    (by simp [Execution.isBar]) hord
  simp only [Event.mk.injEq] at heq
  exact hne heq.1

/-- **No whole-CTA aligned barrier**: every `bar` of the kernel names its thread count. -/
theorem no_barExited (hX : Consistent L kernel asms mem0 X) (ht : StatsFacts L X) :
    ¬ AlignedClass.bar.Exited L kernel X := by
  rw [AlignedClass.exited_bar_iff]
  rintro ⟨⟨g, i⟩, -, -, -, ⟨⟨pc, k⟩, hev, hal⟩, -⟩
  have hg := event_thread_lt hX hev
  cases k with
  | bar id cnt m =>
    cases m with
    | sync =>
      rcases ht.bar_form hg hev with ⟨-, rfl⟩ | ⟨rfl, -⟩ <;>
        simp [Kernel.isAlignedCtaBar] at hal
    | arrive =>
      rcases ht.bar_form hg hev with ⟨-, rfl⟩ | ⟨rfl, -⟩ <;>
        simp [Kernel.isAlignedCtaBar] at hal
  | _ => simp [Kernel.isAlignedCtaBar] at hal

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Safety
