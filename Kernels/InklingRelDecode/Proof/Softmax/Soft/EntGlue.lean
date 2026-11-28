-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Soft.CurDefs
public import Kernels.InklingRelDecode.Proof.Softmax.Data.IntWord
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Common.BiasEntry
import Kernels.InklingRelDecode.Proof.Common.LaunchRounds
import Kernels.InklingRelDecode.Proof.Softmax.Data.MaskConst
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Kernels.InklingRelDecode.Proof.Lib.Geometry
public import Kernels.InklingRelDecode.Proof.Lib.SoftLane
public import Kernels.InklingRelDecode.Proof.Lib.QueryCoord
import Lemmas.Flow.Arith32Norm

@[expose] public section

/-! # What the entry of a softmax state says about the launch

At a softmax state of a data lane the entry's split, number of splits and first block with relative
logits are the launch's, the words past the first token are the request's `past`, and the entry's
iteration count is the launch's. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Flow PTX.Proof Arith32

theorem sub_b32 (a b : Nat) (hab : b ≤ a) (ha : a < 2 ^ 32) :
    Prologue.Control.subValue (b32 a) (b32 b) = b32 (a - b) := by
  have w1 : Lib.word (b32 a) = W a := r32_W ha
  have w2 : Lib.word (b32 b) = W b := r32_W (by omega)
  show Value.bits 32 (sub32 (Lib.word (b32 a)) (Lib.word (b32 b))) = _
  rw [w1, w2, sub32_W hab ha]
  rfl

/-- **The entry of a softmax state is the launch's.** -/
theorem ent_glue {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {w : Value}
    {ent : Control.Entry} {d : Control.D} {n}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    (hk : k ≤ (X.tr g).length)
    (hs : Frame.stateAt (thread Q L) X g k = some (some (softState w ent d n))) :
    EntSp Q L g ent ∧
      ent.prior = Data.w32 ((Q.past ((L.ctaidOf (g / L.block)).get .z) : Nat) : ℤ) ∧
      ent.limit = Q.numIters ((L.ctaidOf (g / L.block)).get .z)
        ((L.ctaidOf (g / L.block)).get .x) ∧
      ent.qlen = Q.qLen ((L.ctaidOf (g / L.block)).get .z) := by
  have nums := reached_numbers hp hX hg hk hs
  have words := reached_words hp hX hg hk hs
  obtain ⟨-, first, qlen⟩ := nums
  obtain ⟨d1, h1, seq, last⟩ := words
  have first' : d1.first = b32 (Q.qStart ((L.ctaidOf (g / L.block)).get .z)) := by
    rw [h1] at first; exact first
  obtain ⟨hnb, -⟩ := entry_nbias hp hg first' last seq
  obtain ⟨hx, hy, hz⟩ := Lib.coordinate_bounds hp hg
  have lim := reached_limit hp hX hg hk hs
  have mono := hp.cuMono _ hz
  have bound := (Lib.qStart_mono hp (r := (L.ctaidOf (g / L.block)).get .z + 1)
    (r' := Q.b) (by omega) le_rfl).trans hp.cuEnd
  have len := hp.qLenSeq _ hz
  have seqb := hp.seqRange _ hz
  have tok := hp.nTokRange
  refine ⟨⟨by rw [h1]; rfl, by rw [h1]; rfl, by rw [h1]; exact hnb⟩, ?_, lim, qlen⟩
  rw [h1]
  show Prologue.Control.subValue d1.seq (Prologue.Control.subValue d1.last d1.first) = _
  rw [first', last, seq, sub_b32 _ _ mono (by omega)]
  change Prologue.Control.subValue (b32 _) (b32 (Q.qLen _)) = _
  rw [sub_b32 _ _ len (by omega)]
  exact Data.b32_iw (by omega)

/-- **A row of the request loads** for the entry's control. -/
theorem valid_row {Q : Params} {L : Launch} {g : Nat} {ent : Control.Entry}
    (hq : ent.qlen = Q.qLen ((L.ctaidOf (g / L.block)).get .z))
    (hle : Q.qLen ((L.ctaidOf (g / L.block)).get .z) ≤ 10)
    (hv : Lib.QRowValid Q L (g / L.block) (Lib.softRow (g % L.block))) :
    Control.validRow ent (g % L.block) = true := by
  obtain ⟨h1, h2⟩ := hv
  have tk : ∀ r < 64, r * 43 / 256 = r / 6 := by decide
  have h3 : Control.token (g % L.block) = Lib.softRow (g % L.block) / 6 :=
    tk (Control.row (g % L.block)) (by unfold Control.row; omega)
  have h4 : Control.row (g % L.block) < 60 := h1
  simp only [Control.validRow, Control.tokenFits, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨h4, ?_, by omega⟩
  rw [hq, h3]
  exact h2

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
