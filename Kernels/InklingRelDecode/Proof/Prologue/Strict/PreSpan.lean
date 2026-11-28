-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.PreFrame
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.BlockRead
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.CopyElection
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.CopySpan
public import Lemmas.Flow.SegQFam

@[expose] public section

/-! # The strict spans of a preload block

Each family has one theorem per block (`seg_fam`); a span states its sites by equations
(`s = .arr bk`) so that one proof text serves the three blocks. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

-- The block pointer and the table load: from the arrival to the block-table load.
seg_fam pa (bk 3) : ∀ (c : Control.D) (v : Data.Vals) (s s' : Site), s = .arr bk →
    s' = .lb bk 0 → SegQ kernel Assumptions.all L g (QT proQt) ((Site.arr bk).pc + 1)
      (dFacts Q L g w (dq c v s)) (Site.lb bk 0).pc (dFacts Q L g w (dq c v s')) :=
  intro c v s s' hs hs'
  refine SegQ.comp (b := s'.pc - 1) (G := dFactsAt Q L g w (dq c v s) (s'.pc - 1)) ?_ ?_
  · subst hs hs'
    first
    | pre_br [525, 529, 530, 531, 494, 495], (Control.seg_s194.comp Control.seg_s195)
    | pre_br [525, 529, 530, 531, 494, 495], (Control.seg_s238.comp Control.seg_s239)
    | pre_br [525, 529, 530, 531, 494, 495], (Control.seg_s280.comp Control.seg_s281)
  · subst hs hs'
    pre_seg

-- The load of half `h` of a block's table words: the row of the page and the head's offsets.
seg_fam lbA (bk 3) (hk 2) : ∀ (c : Control.D) (v : Data.Vals) (x : Nat) (s s' : Site),
    s = .lb bk hk → s' = lbBar bk hk →
    SegQ kernel Assumptions.all L g (QT proQt) ((Site.lb bk hk).pc + 1)
      ([(lbDst bk hk, b32 x)] ++ dFacts Q L g w (dq c v s))
      (lbBar bk hk).pc
      (dFacts Q L g w (dq c (payUp v bk hk (b32 x)) s')) :=
  intro c v x s s' hs hs'
  subst hs hs'
  pre_seg

-- After the second copy: the next table address.
seg_fam pxA (bk 3) : ∀ (c : Control.D) (v : Data.Vals) (s s' : Site), s = .ptc bk 1 →
    s' = .lb bk 1 → SegQ kernel Assumptions.all L g (QT proQt) ((Site.ptc bk 1).pc + 1)
      (dFacts Q L g w (dq c v s)) (Site.lb bk 1).pc (dFacts Q L g w (dq c v s')) :=
  intro c v s s' hs hs'
  refine SegQ.comp (b := s'.pc - 1) (G := dFactsAt Q L g w (dq c v s) (s'.pc - 1)) ?_ ?_
  · subst hs hs'
    first
    | pre_br [525, 529, 494, 495, 684, 683, 686], Control.seg_s218
    | pre_br [525, 529, 494, 495, 704, 703, 706], Control.seg_s260
    | pre_br [525, 529, 494, 495, 726, 725, 728], Control.seg_s302
  · subst hs hs'
    pre_seg

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
