-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.BiasEv
public import Kernels.InklingRelDecode.Proof.Lib.ScoreEv
public import Kernels.InklingRelDecode.Proof.Lib.WinHalf
public import Kernels.InklingRelDecode.Proof.Lib.EvWord
import Kernels.InklingRelDecode.Proof.Softmax.Soft.SentState
import Kernels.InklingRelDecode.Proof.Softmax.Soft.WinState
import Kernels.InklingRelDecode.Proof.Softmax.Soft.WinMax
import Kernels.InklingRelDecode.Proof.Softmax.Soft.EntGlue
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Kernels.InklingRelDecode.Proof.Lib.Rows

/-! # The word a lane sends at pc 1838 is its half's maximum

For a row that loads, the word the lane sends at the shuffle of pc 1838 is exactly the maximum, over
the 64 columns of its half of the round's block, of the visible keys' scores plus biases. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow Control Data Soft

variable {Q : Params} {L : Launch} {g : Nat}

/-- **The sent word is the half's maximum.** -/
public theorem sent_half {m : Mem0} {X : Execution} {k : Nat} {mode : ShflMode} {b c : Nat}
    {recv : Value} {ok : Bool} {sent : Value} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hB : Lib.BiasEv Q L g X) (hS : Lib.ScoreEv Q L g X)
    (hv : Lib.QRowValid Q L (g / L.block) (Lib.softRow (g % L.block)))
    (get : X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩) :
    pollRound 1257 ((X.tr g).take k) - 1 < Q.numIters ((L.ctaidOf (g / L.block)).get .z)
      ((L.ctaidOf (g / L.block)).get .x) ∧
    Lib.Ev sent (Lib.halfMax Q ((L.ctaidOf (g / L.block)).get .z)
      ((L.ctaidOf (g / L.block)).get .x) (Lib.softRow (g % L.block) / 6) (Lib.laneHead L g)
      (pollRound 1257 ((X.tr g).take k) - 1) (g % L.block / 16 % 2)) := by
  obtain ⟨w, ent, d, y, n, hsc, inv, hs, -, site, rfl⟩ := sent_state hp hX hf get
  have hg := Frame.lt_of_get hX get
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have nub := Frame.noUbBefore_of_get hX get
  obtain ⟨E, hP, lim, hq⟩ := ent_glue hp hX hg len hsc
  obtain ⟨hx, hy, hz⟩ := Lib.coordinate_bounds hp hg
  have vr := valid_row hq (hp.qLenLe _ hz) hv
  obtain ⟨led, inv', cur, sc⟩ := soft_win hp hX hB k len _ hs nub w ent y n rfl inv.entry E
  obtain ⟨k', a, sh, hk', hg', hpr⟩ := sc.ev (by rw [site]; rfl)
  have hs64 : ∀ j < 64, y.v.s[j]? = some (.float .f32 (Lib.laneScore Q L g y.c.i j)) := by
    intro j hj
    have := hS k' a y.v.s sh hg' hv j hj
    rwa [hpr, Nat.add_sub_cancel] at this
  have hc64 := (cur vr).cur (by rw [site]; rfl)
  have hlt : y.c.i < ent.limit := inv'.loop (by rw [site]; decide) (by rw [site]; decide)
    (by rw [site]; decide) (fun j => by rw [site]; nofun)
  rw [lim] at hlt
  have hn := Lib.blk_lt hp.splitsPos hlt
  have hseq := hp.seqRange _ hz
  have rd : pollRound 1257 ((X.tr g).take k) - 1 = y.c.i := by
    have := led
    simp only [Led, site, Site.afterS, Bool.toNat_true] at this
    omega
  rw [rd]
  refine ⟨hlt, ?_⟩
  have hn' : Q.splits * y.c.i + (L.ctaidOf (g / L.block)).get .x <
      Q.blocks ((L.ctaidOf (g / L.block)).get .z) := by
    have := Nat.mul_comm Q.splits y.c.i
    omega
  exact w1_half hp E hP inv'.thread hn' hseq hs64 hc64

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
