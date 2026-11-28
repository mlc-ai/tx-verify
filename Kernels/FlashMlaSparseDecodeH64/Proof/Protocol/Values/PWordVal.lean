-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.LseSum
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.VoteAgree
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.W0Slots
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.EvBlock
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Value
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.VoteBlock

@[expose] public section

/-! # The probabilities a lane stores are the reference's weights

A probability store of lane `y` (the lane `g` or its partner) of block `d` writes the word `n < 32`
of the block in progress (`w0PWord`): the weight `weight` of the slot `32 half + n` of block `d`
times `2 ^ (-M)`, `M` the maximum lane `g` carries after block `d` (`pword_val`): the words of the
block are those of its finished entry (`w0_ev_block`), the lanes of a pair carry the same maximum
(`carry_agree`), and the scores and masks read as the reference's (`ScoreRead`, `MaskRead`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The block of an event past the vote** (valid rows): the finished block `d` of the whole
trace has the words of the block in progress at the event, and the maximum after it is the one
the block in progress computes. -/
theorem w0_max_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {y j K d : Nat} {e : Event} (hw : warp L y < 4)
    (hv : W0Trace P X y) (he : X.get (y, j) = some e) (hpc : 579 ≤ e.pc ∧ e.pc < 1122)
    (hd : (w0Fin ((X.tr y).take j)).1.length = d)
    (hK : d < (w0Fin ((X.tr y).take K)).1.length) :
    ∃ s, (w0Fin (X.tr y)).1[d]? = some s ∧ w0Words s = w0Words (w0Fin ((X.tr y).take j)).2 ∧
      (w0Fin ((X.tr y).take j)).1 = (w0Fin (X.tr y)).1.take d ∧
      w0Max P.scale (w0Carry P.scale (w0Fin ((X.tr y).take j)).1).1
        (w0Words (w0Fin ((X.tr y).take j)).2) =
        (w0Carry P.scale ((w0Fin (X.tr y)).1.take (d + 1))).1 := by
  have hk : (w0Fin ((X.tr y).take j)).1.length < (w0Fin ((X.tr y).take K)).1.length := by
    rw [hd]; exact hK
  obtain ⟨s, hs, hpre, hws⟩ := w0_ev_block hp hX hFw hnu hw hv he hpc hk
  have hfin := fin_take_eq hp hX hFw hnu hw (k := K)
  have hF : (w0Fin ((X.tr y).take K)).1 =
      (w0Fin (X.tr y)).1.take (w0Fin ((X.tr y).take K)).1.length := hfin
  have htk : (w0Fin ((X.tr y).take j)).1 = (w0Fin (X.tr y)).1.take d := by
    rw [hpre, hF, List.take_take, Nat.min_eq_left (by omega), hd]
  have hs' : (w0Fin (X.tr y)).1[d]? = some s := by
    rw [hF, hd, List.getElem?_take_of_lt hK] at hs
    exact hs
  refine ⟨s, hs', hws, htk, ?_⟩
  rw [List.take_add_one, hs', htk, ← hws]
  simp only [Option.toList_some, w0Carry_snoc, w0Next]

/-- **A block without a rise keeps the maximum** (valid rows): the vote at index `j` of lane `y`
is false and the block `d` of its trace is finished: the maximum after block `d` is the one
before. -/
theorem w0_max_novote (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {y j K d mm : Nat} {q : VoteMode}
    {a : Bool}
    (hw : warp L y < 4) (hv : W0Trace P X y)
    (hj : X.get (y, j) = some ⟨578, .voteMode q mm a false⟩)
    (hd : (w0Fin ((X.tr y).take j)).1.length = d)
    (hK : d < (w0Fin ((X.tr y).take K)).1.length) :
    (w0Carry P.scale ((w0Fin (X.tr y)).1.take (d + 1))).1 =
      (w0Carry P.scale ((w0Fin (X.tr y)).1.take d)).1 := by
  have hk : (w0Fin ((X.tr y).take j)).1.length < (w0Fin ((X.tr y).take K)).1.length := by
    rw [hd]; exact hK
  obtain ⟨s, hs, -, hvt, -, -⟩ := w0_vote_block hp hX hFw hnu hw hv hj rfl hk
  have hfin := fin_take_eq hp hX hFw hnu hw (k := K)
  have hs' : (w0Fin (X.tr y)).1[d]? = some s := by
    rw [hfin, hd, List.getElem?_take_of_lt hK] at hs
    exact hs
  have hvf : (w0Words s).vt = false := hvt q mm a false rfl
  rw [List.take_add_one, hs']
  simp only [Option.toList_some, w0Carry_snoc, w0Next, w0Max, hvf]
  simp

/-- **The probability a lane stores is the slot's weight** (valid rows, complete). -/
theorem pword_val (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hR : BarRows P L X) (hC : Complete L X)
    (hV : W0Rows P L X) (hS : ScoreRead P L X hV) (hM : MaskRead P L X hV)
    {g y kst K n d : Nat} {e e1 : Event} (hw : warp L g < 4) (hg : g < L.threads)
    (hy : y = g ∨ y = w0Partner L g) (he : X.get (y, kst) = some e)
    (hpc : 704 ≤ e.pc ∧ e.pc < 708) (hK : X.get (y, K) = some e1) (hpc1 : e1.pc = 1157)
    (hKn : (w0Fin ((X.tr y).take K)).1.length = blocksOf P L (g / L.block))
    (hd : (w0Fin ((X.tr y).take kst)).1.length = d) (hdb : d < blocksOf P L (g / L.block))
    (hn : n < 32) :
    w0PWord P.scale ((X.tr y).take kst) n =
      weight P (w0Batch L y) (w0Query L y) (w0Head L y) (w0BlockExtra P (w0Batch L y) d)
          (w0BlockSlot P (w0Batch L y) d (32 * w0Half L y + n)) *
        (2 : ℝ) ^ (-(w0Carry P.scale ((w0Fin (X.tr g)).1.take (d + 1))).1) := by
  have hV' : ∀ y, warp L y < 4 → W0Trace P X y := fun y hy => w0Trace_of_rows hV hX hy
  have hwy : warp L y < 4 := by
    obtain ⟨-, hwh, -, -⟩ := w0Partner_facts hp hw hg
    rcases hy with rfl | rfl <;> assumption
  have hyl : y < L.threads := Frame.lt_of_get hX hK
  have hdle : d + 1 ≤ blocksOf P L (g / L.block) := hdb
  obtain ⟨s, hs', hws, -, hcs⟩ := w0_max_at hp hX hFw hnu hwy (hV' y hwy) he
    ⟨by omega, by omega⟩ hd (K := K) (by rw [hKn]; exact hdb)
  have hcar : (w0Carry P.scale ((w0Fin (X.tr y)).1.take (d + 1))).1 =
      (w0Carry P.scale ((w0Fin (X.tr g)).1.take (d + 1))).1 := by
    rcases hy with rfl | rfl
    · rfl
    · exact (carry_agree hp hX hFw hnu hR hC hV' (d + 1) hg hw hdle).symm
  have hfin := fin_take_eq hp hX hFw hnu hwy (k := K)
  have hsd : (w0Fin ((X.tr y).take K)).1[d]? = some s := by
    rw [hfin, List.getElem?_take_of_lt (by rw [hKn]; exact hdb)]
    exact hs'
  unfold w0PWord
  rw [hcs, ← hws, w0Prob_eq, hcar]
  congr 1
  have h1 := hS y K e1 hyl hK hpc1 d s hsd n hn
  have h2 := hM y K e1 hyl hK hpc1 d s hsd n hn
  exact w0Wt_eq_weight rfl h1 h2

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
