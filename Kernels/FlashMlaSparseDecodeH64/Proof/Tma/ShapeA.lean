-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Ev
public import Lemmas.Flow.Step.ShapeClasses
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # The TMA warp's shape obligations: election, lengths, polls, barrier

One declaration per site: the election with the full mask, the two `.nc` length reads, the four
polls (parity 0 for the set-up waits; the ring's and the tile's parity words in a block), the CTA
barrier `12` of 384 threads, the exit and the hand-back. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_elect (d : D) (hs : d.site = .elect) : (code P L g).ShapeAt (EvK L g) d := by
  tma_state d
  cases hs
  tma_open
  rcases fires_elect_mask (readBits_reg (rg 663)) hf with ⟨inst, ld, rfl⟩ | ⟨f, rfl⟩
  · exact .inl ⟨inst, ld, rfl⟩
  · exact .inr ⟨f, rfl⟩

theorem shapeAt_lens (d : D) (hs : d.site = .loadTopk ∨ d.site = .loadExtra) :
    (code P L g).ShapeAt (EvK L g) d := by
  tma_state d
  rcases hs with hs | hs <;> cases hs <;> tma_open <;> exact fires_ncLoad_kind hf

theorem shapeAt_qWait (d : D) (hs : d.site = .qWait) : (code P L g).ShapeAt (EvK L g) d := by
  tma_state d
  cases hs
  tma_open
  exact fires_wait_reg (by rw [hpc]; decide) (rg 669) (rg 670) hf

theorem shapeAt_storeWait (d : D) (hs : d.site = .storeWait) :
    (code P L g).ShapeAt (EvK L g) d := by
  tma_state d
  cases hs
  tma_open
  exact fires_wait_reg (by rw [hpc]; decide) (rg 672) (rg 670) hf

theorem shapeAt_coordWait (d : D) (hs : d.site = .coordWait) :
    (code P L g).ShapeAt (EvK L g) d := by
  tma_state d
  cases hs
  tma_open
  exact fires_wait_reg (by rw [hpc]; decide) (rg 685) (rg 686) hf

theorem shapeAt_rawWait (d : D) (hs : d.site = .rawWait) : (code P L g).ShapeAt (EvK L g) d := by
  tma_state d
  cases hs
  tma_open
  exact fires_wait_reg (by rw [hpc]; decide) (rg 688) (rg 689) hf

theorem shapeAt_outBar (hp : Pre P L m) (d : D) (hs : d.site = .outBar) :
    (code P L g).ShapeAt (EvK L g) d := by
  tma_state d
  cases hs
  tma_open
  exact shape_barSyncN_block (P := fun e : Event => e.kind = .bar 12 none .sync) hf
    (readBits_reg (rg 790)) (by decide) (readBits_reg (rg 791)) (by rw [hp.block]; rfl)
    (by rw [hp.block]) rfl

theorem shapeAt_exit (d : D) (hs : d.site = .exit) : (code P L g).ShapeAt (EvK L g) d := by
  tma_state d
  cases hs
  tma_open
  simp only [eventTmpl, Fires] at hf
  exact congrArg Event.kind hf.1

theorem shapeAt_leave (d : D) {s : IdleSite} (hs : d.site = .leave s) :
    (code P L g).ShapeAt (EvK L g) d := fun _ _ _ _ => by simp only [EvK, hs]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
