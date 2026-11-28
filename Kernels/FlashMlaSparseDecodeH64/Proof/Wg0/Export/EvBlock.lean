-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Epi
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockTail
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.VoteBlock
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockList
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockLoad
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FinLen
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.WordsExt
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceBase

@[expose] public section

/-! # The block an event after the vote belongs to

An event of lane `y` at a pc from 579 to 1121 (after the vote, before the closing arrival) lies in
the block with `t` finished blocks before it. At any later prefix with more than `t` finished
blocks, entry `t` of the finished blocks is that block, and its words are those of the block in
progress at the event (`w0_ev_block`): the later events of the block are past the words' pcs. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}

/-- Events at pcs past the vote leave the block's words unchanged. -/
theorem w0Words_ext_late (seg ex : List Event) (h : ∀ e ∈ ex, 579 ≤ e.pc) :
    w0Words (seg ++ ex) = w0Words seg := by
  obtain ⟨hlo, hhi, hmw, hpw⟩ := w0Words_ext seg ex (fun e he => by have := h e he; omega)
  have hpm : (w0Words (seg ++ ex)).pm = (w0Words seg).pm := by
    simp only [w0Words]
    rw [w0Last_ext _ _ _ _ (fun f hf => by have := h f hf; simp; omega)]
  have hvt : (w0Words (seg ++ ex)).vt = (w0Words seg).vt := by
    simp only [w0Words]
    rw [w0Last_ext _ _ _ _ (fun f hf => by have := h f hf; simp; omega)]
  cases h1 : w0Words (seg ++ ex)
  cases h2 : w0Words seg
  rw [h1, h2] at hlo hhi hmw hpw hpm hvt
  simp only at hlo hhi hmw hpw hpm hvt
  subst hlo hhi hmw hpm hvt
  congr 1
  funext j
  exact hpw j

/-- **The finished block of an event after the vote** (valid rows): the event at index `j` (pc 579
to 1121) of lane `y` with `t` finished blocks before it, at a later prefix `k` with more than `t`
finished blocks, has entry `t` of the finished blocks with the words of its block in progress. -/
theorem w0_ev_block (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hw : warp L y < 4) (hv : W0Trace P X y) {j k : Nat}
    {e : Event} (he : X.get (y, j) = some e) (hpc : 579 ≤ e.pc ∧ e.pc < 1122)
    (hk : (w0Fin ((X.tr y).take j)).1.length < (w0Fin ((X.tr y).take k)).1.length) :
    ∃ s, (w0Fin ((X.tr y).take k)).1[(w0Fin ((X.tr y).take j)).1.length]? = some s ∧
      (w0Fin ((X.tr y).take j)).1 =
        (w0Fin ((X.tr y).take k)).1.take (w0Fin ((X.tr y).take j)).1.length ∧
      w0Words s = w0Words (w0Fin ((X.tr y).take j)).2 := by
  have hnE := w0_noEarly hp hX hFw hnu hw
  have hLj : w0Closed ((X.tr y).take j) = (w0Fin ((X.tr y).take j)).1.length :=
    (w0Fin_length (hnE j)).symm
  have hLk : (w0Fin ((X.tr y).take j)).1.length < w0Closed ((X.tr y).take k) := by
    rw [← w0Fin_length (hnE k)]; exact hk
  obtain ⟨Kc, cE, hKcl, hKp1, hLK⟩ := w0_close_idx hLk
  have hKlt : Kc < k := by
    have := (List.getElem?_eq_some_iff.mp hKcl).1
    simp only [List.length_take] at this
    omega
  have hK : X.get (y, Kc) = some cE := by
    rw [List.getElem?_take_of_lt hKlt] at hKcl
    exact hKcl
  rw [List.take_take, Nat.min_eq_left hKlt.le] at hLK
  have hjlt : j < Kc := by
    by_contra hge
    have hnj : Kc ≠ j := fun h => by
      subst h; rw [he] at hK; cases hK; omega
    have hsplit : (X.tr y).take (Kc + 1) = (X.tr y).take Kc ++ [cE] := by
      have : (X.tr y)[Kc]? = some cE := hK
      rw [List.take_add_one, this]; rfl
    have hA1 : w0Closed ((X.tr y).take (Kc + 1)) = w0Closed ((X.tr y).take Kc) + 1 := by
      unfold w0Closed
      rw [hsplit, List.countP_append]
      simp [hKp1, w0ArrSPc]
    have hA2 := w0Closed_mono (l := X.tr y) (show Kc + 1 ≤ j by omega)
    omega
  have hnoc := w0_noClose_between (X := X) (g := y) (k := j) (K := Kc) (by rw [hLK, hLj])
  have hKlen : Kc < (X.tr y).length := (List.getElem?_eq_some_iff.mp hK).1
  obtain ⟨ex, hexE, hfinB, hfinA⟩ := w0_tail hp hX hFw hw (hv.take _) he (by omega) (by omega)
    (lo := 579) (by omega) (fun e' he' hu => by
      have := Wg0.w0_pc_mono hp hX hFw hw (hv.take (j + 1)) (i := j) 1 le_rfl he he' hu
        (by omega)
        (fun q hq ev hev => by
          obtain rfl : q = 0 := by omega
          rw [Nat.add_zero, he] at hev
          cases hev
          omega)
      omega) hjlt hKlen (fun q hq => hnoc q hq.le)
  have hlenE : (w0Fin ((X.tr y).take Kc)).1.length = (w0Fin ((X.tr y).take j)).1.length := by
    rw [hfinA]
  have hblkE := w0Fin_block_of_close hp hX hFw hw hK hKp1 hKlt hnu
  rw [hlenE] at hblkE
  refine ⟨_, hblkE, ?_, ?_⟩
  · rw [← hfinA]
    exact List.prefix_iff_eq_take.mp (w0Fin_take_prefix hp hX hFw hnu hw hKlt.le)
  rw [hfinB, List.append_assoc]
  exact w0Words_ext_late _ _ (fun f hf => by
    rcases List.mem_append.mp hf with h | h
    · rw [List.mem_singleton.mp h]; omega
    · have := (hexE f h).1; omega)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
