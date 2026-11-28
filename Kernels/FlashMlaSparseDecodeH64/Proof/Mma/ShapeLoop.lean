-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Ev
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Lemmas.Flow.Step.TcCpWs
import Lemmas.Flow.CommitSelf

@[expose] public section

/-! # The MMA warp's events by state: the block loop, the CTA barrier and the exit

One declaration per site family (`shape_open`, then the inversion lemma of its instruction). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_kvWait (d : D) (hs : d.site = .kvWait) : (code P L g).ShapeAt (EvK L g) d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  shape_open
  exact fires_wait_reg (by rw [hpc]; decide) (rg 855) (rg 879) hf

theorem shapeAt_soWait (d : D) (hs : d.site = .soWait) : (code P L g).ShapeAt (EvK L g) d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  shape_open
  exact fires_wait_reg (by rw [hpc]; decide) (rg 878) (rg 879) hf

theorem shapeAt_qkCommit (d : D) (hs : d.site = .qkCommit) : (code P L g).ShapeAt (EvK L g) d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  shape_open
  exact fires_commit_self (rg 877) hf

theorem shapeAt_pvCommit (d : D) (hs : d.site = .pvCommit) : (code P L g).ShapeAt (EvK L g) d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  shape_open
  exact fires_commit_self (rg 883) hf

theorem shapeAt_qk (d : D) (hs : ∃ k, d.site = .qk k) : (code P L g).ShapeAt (EvK L g) d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  obtain ⟨k, hs⟩ := hs
  cases hs
  fin_cases k <;> shape_open <;>
    exact mmaTmem_ev hf ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rg_ rg_ rg_ rg_ rg_ rfl
      (by decide) (by decide) (by decide)

theorem shapeAt_pv (d : D) (hs : ∃ k, d.site = .pv k) : (code P L g).ShapeAt (EvK L g) d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  obtain ⟨k, hs⟩ := hs
  cases hs
  fin_cases k <;> shape_open <;>
    exact mmaSmem_ev hf ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rg_ rg_ rg_ rg_ rg_ rfl rfl
      (by decide) (by decide)

theorem shapeAt_outBar (hp : Pre P L m) (d : D) (hs : d.site = .outBar) :
    (code P L g).ShapeAt (EvK L g) d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  shape_open
  exact shape_barSyncN_block (P := fun e : Event => e.kind = .bar 12 none .sync) hf
    (readBits_of (rg 918)) (by decide) (readBits_of (rg 919)) (by rw [hp.block]; rfl)
    (by rw [hp.block]) rfl

theorem shapeAt_exit (d : D) (hs : d.site = .exit) : (code P L g).ShapeAt (EvK L g) d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  shape_open
  simp only [eventTmpl, Fires] at hf
  exact congrArg Event.kind hf.1

theorem shapeAt_leave (d : D) {s : IdleSite} (hs : d.site = .leave s) :
    (code P L g).ShapeAt (EvK L g) d := by
  intro t ins e o _ _ _ _
  simp only [EvK, hs]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
