-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Staged.Early
public import Kernels.InklingRelDecode.Proof.Lib.NoBarArrive
public import Kernels.InklingRelDecode.Proof.Lib.Sources
public import Lemmas.Kernel.Safety.HandoffEarly

@[expose] public section

/-! # Barrier 0's first two instances

Every thread's first two barrier-0 events are the startup's `bar.sync 0` at pcs 12 and 14, of
all eight warps with no thread count (`bar0_sources`, from the first stage of the following,
`early_at`), and no thread exits before them (`bar0_exit`). So the first two instances hand off
from every thread of the CTA to every other (`bar0_before`, `Handoff.of_barEarly` with `N = 1`):
an event of `g` with at most one barrier-0 event up to and including it happens before an event
of `h` after more barrier-0 events of `h`. Nothing here depends on `BaseRead`. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode

noncomputable section

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- An early startup state's event that is a barrier-0 event is `bar.sync 0` with no count. -/
theorem early_bar {s : Startup.D} {e : Event}
    (hs : s.site = .alloc ∨ s.site = .allocWr ∨ s.site = .bar0 ∨ s.site = .ld0 ∨
      s.site = .bar1) (hev : Startup.Ev L g s e) :
    (Execution.isBarId 0 e = true → ∃ pc, e = ⟨pc, .bar 0 none .sync⟩) ∧ e.kind ≠ .exit := by
  obtain ⟨site, tm, x, bw⟩ := s
  simp only at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp only [Startup.Ev] at hev
  · subst hev; simp [Execution.isBarId]
  · obtain ⟨col, -, rfl⟩ := hev; simp [Execution.isBarId]
  · subst hev; exact ⟨fun _ => ⟨_, rfl⟩, by simp⟩
  · obtain ⟨ac, bs, rfl, -⟩ := hev; simp [Execution.isBarId]
  · subst hev; exact ⟨fun _ => ⟨_, rfl⟩, by simp⟩

/-- **The sources of barrier 0's first two instances**: all eight warps, no thread count. -/
theorem bar0_sources (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    NamedBar.EarlySources L X none (Finset.range (CtaBarrier.warps L.block)) 0 1 := by
  intro e pc cnt ⟨mode, he⟩ hg hn
  have hu : ∀ f, (⟨pc, .bar 0 cnt mode⟩ : Event).kind ≠ .ub f := by simp
  obtain ⟨s, n, -, hs, -, hev⟩ := early_at (Q := Q) hp hX he hu hn
  obtain ⟨pc', heq⟩ := (early_bar hs hev).1 (by simp [Execution.isBarId])
  simp only [Event.mk.injEq, Kind.bar.injEq] at heq
  refine ⟨?_, heq.2.2.1⟩
  have hb : L.block = 256 := hp.block
  simp only [Finset.mem_range, CtaBarrier.warps, hb]
  omega

/-- **No thread exits before its second barrier-0 event.** -/
theorem bar0_exit (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {j pc : Nat}
    (he : X.get (g, j) = some ⟨pc, .exit⟩) : 1 + 1 ≤ c0 X g j := by
  by_contra hlt
  obtain ⟨s, n, -, hs, -, hev⟩ := early_at (Q := Q) hp hX he (by simp) (by omega)
  exact (early_bar hs hev).2 rfl

/-- **Barrier 0's first two instances order the CTA**: an event of `g` with at most one
barrier-0 event up to and including it happens before an event of `h` of the same CTA after more
barrier-0 events of `h`. -/
theorem bar0_before (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {h e f : Nat}
    (hsame : SameCta L g h) (hf : f < (X.tr h).length) (hlt : c0 X g (e + 1) < c0 X h f)
    (hle : c0 X g (e + 1) ≤ 1) : baseCausality L X (g, e) (h, f) := by
  have hb : L.block = 256 := hp.block
  refine Frame.Handoff.of_barEarly hX (n := CtaBarrier.warps L.block)
    (by simp [CtaBarrier.warps, hb]) rfl (Finset.card_range _)
    (fun w hw => by simp only [Finset.mem_range, CtaBarrier.warps, hb] at hw ⊢; omega)
    (by decide) (bar0_sources (Q := Q) hp hX) (fun g _ _ j pc he => bar0_exit (Q := Q) hp hX he)
    hsame ?_ hf hlt hle
  simp only [Finset.mem_range, CtaBarrier.warps, hb]
  omega

end
end PTX.Kernels.InklingRelDecode.Proof
