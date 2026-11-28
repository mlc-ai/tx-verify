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

-- The election of a copy up to its guard: the destination and the column of the box.
seg_fam pelA (bk 3) (jk 4) : ∀ (c : Control.D) (x : BitVec 64) (v : Data.Vals) (ld : Nat)
    (win : Bool) (s s' : Site), s = .pel bk jk → s' = .ptc bk jk →
    SegQ kernel Assumptions.all L g (QT proQt) ((Site.pel bk jk).pc + 1)
      ([(copyVote bk jk, .pred win), (pelLeader bk jk, .bits 32 (BitVec.ofNat 64 ld))] ++
        dFacts Q L g w (dq {c with elected := win, broadcast := .bits 32 x} v s))
      (Site.ptc bk jk).pc
      (dFacts Q L g w (dq {c with elected := win, broadcast := .bits 32 x} v s')) :=
  intro c x v ld win s s' hs hs'
  refine SegQ.comp (b := s.pc + 1 + (s'.pc - s.pc - 1) / 3) (G := dFactsAt Q L g w
    (dq {c with elected := win, broadcast := .bits 32 x} v s)
    (s.pc + 1 + (s'.pc - s.pc - 1) / 3)) ?_ (SegQ.comp
    (b := s.pc + 1 + (s'.pc - s.pc - 1) * 2 / 3) (G := dFactsAt Q L g w
    (dq {c with elected := win, broadcast := .bits 32 x} v s)
    (s.pc + 1 + (s'.pc - s.pc - 1) * 2 / 3)) ?_ ?_)
  all_goals subst hs hs'
  all_goals pre_seg


end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
