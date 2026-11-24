-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmPack
public import Kernels.InklingRelDecode.Proof.Thread.SmMask

@[expose] public section

/-! # From the last preload to the first loop bias load (pcs 807-1124)

The straight-line stretch the thread walks after the first block's last preload: the setup of
`SmPack` (pcs 807-948), the jump to the loop test, the test that does not leave the loop (pcs
1049-1050), the mask of the next block's loads (`SmMask`), the next block's key and pointers and
the zero fill of the first destination (`SmSegB`). All pieces are between the table's facts of
one state `d`: the preloaded block (`cw = 64`) is in the registers, the first iteration's start
values are the running maximum and sum, and the loop counter is zero. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false

variable {L : Launch} {g : Nat}

theorem live_goto : ∀ r ∈ Flow.live 1049, r ∈ Flow.live 948 := by decide +kernel
theorem emu_948 : Assumptions.emuSites.contains 948 = false := by decide +kernel

/-- `bra.uni` to the loop test (pc 948), between the table's facts. -/
theorem seg_948 (d : D) :
    Seg kernel asms L g 1 948 (factsAt L g 948 d) 1049 (factsAt L g 1049 d) :=
  (seg_goto (L := L) (g := g) Flow.code_948 emu_948).weaken_end fun _ hR =>
    Flow.holds_factsFrom_mono hR live_goto

/-- **The setup after the last preload** (pcs 807 to 948), into the loop test at pc 1049. -/
theorem seg_setupB (d : D) (hT : g % L.block < 128) (hok : d.e.Ok)
    (hwb : ∀ k, (d.w k).bytes = 2) (hi0 : d.i = 0) (hm : d.m = b32 4286578688)
    (hl : d.l = b32 0) :
    Seg kernel asms L g 142 807 (factsAt L g 807 d) 1049 (factsAt L g 1049 d) := by
  have h1 := (seg_807 d).comp (seg_808 d hT)
  have h2 := h1.comp (seg_812 d hT)
  have h3 := h2.comp (seg_813 d hT hok)
  have h4 := h3.comp (seg_words d hwb 32 (le_refl 32))
  have h5 := h4.comp (seg_848 d)
  have h6 := h5.comp (seg_849 d)
  have h7 := h6.comp (seg_pairs d 31 (le_refl 31))
  have h8 := h7.comp (seg_943 d hT hok hi0 hm hl)
  have h9 := h8.comp (seg_948 d)
  exact Seg.of_len h9 rfl

/-- **The loop test to the first bias load** (pcs 1049 to 1124): the test does not leave the
loop, the mask and the pointers of the next block, the zero fill of the first destination. -/
theorem seg_loopTop (d : D) (hT : g % L.block < 128) (hok : d.e.Ok) (hlt : d.i < d.e.r26)
    (hcv : d.cv = 0) :
    Seg kernel asms L g 75 1049 (factsAt L g 1049 d) 1124 (factsAt L g 1124 d) := by
  have hi32 : d.i < 2 ^ 32 := by have := hok.r26_lt; omega
  have h1 := (seg_1049 d hT hok hi32).comp (seg_1050 d hlt)
  have h2 := h1.comp (seg_mask d hT hok hlt.le)
  have h3 := h2.comp (seg_next d hT hok hcv)
  exact Seg.of_len h3 rfl

/-- **The first pass's stretch** (pcs 807 to 1124): from the last preload to the first loop
bias load. -/
theorem seg_first (d : D) (hT : g % L.block < 128) (hok : d.e.Ok)
    (hwb : ∀ k, (d.w k).bytes = 2) (hi0 : d.i = 0) (hm : d.m = b32 4286578688)
    (hl : d.l = b32 0) (hlt : d.i < d.e.r26) (hcv : d.cv = 0) :
    Seg kernel asms L g 217 807 (factsAt L g 807 d) 1124 (factsAt L g 1124 d) :=
  Seg.of_len ((seg_setupB d hT hok hwb hi0 hm hl).comp (seg_loopTop d hT hok hlt hcv)) rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
