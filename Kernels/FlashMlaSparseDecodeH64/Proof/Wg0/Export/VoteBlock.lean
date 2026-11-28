-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Epi
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockTail
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockList
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockLoad
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FinLen
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.WordsExt
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceBase

@[expose] public section

/-! # The block a vote belongs to

A vote at pc 578 of lane `y` lies in the block with `t` finished blocks before it. At any later
prefix with more than `t` finished blocks, entry `t` of the finished blocks is that block: it has
the vote's result as its vote word and the words that the vote's input was made of (the exchange
word and the lane's own maximum). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}

/-- **The finished blocks of a prefix are a prefix of those of a longer one.** -/
theorem w0Fin_take_prefix (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hw : warp L y < 4) {K k : Nat} (hKk : K ≤ k) :
    (w0Fin ((X.tr y).take K)).1 <+: (w0Fin ((X.tr y).take k)).1 := by
  have hno := w0_noEarly hp hX hFw hnu hw
  have hdrop : (X.tr y).take k = (X.tr y).take K ++ ((X.tr y).take k).drop K := by
    have h1 : ((X.tr y).take k).take K = (X.tr y).take K := by
      rw [List.take_take, Nat.min_eq_left hKk]
    conv_lhs => rw [← List.take_append_drop K ((X.tr y).take k), h1]
  have hpf := w0Scan_prefix ((X.tr y).take K) (((X.tr y).take k).drop K)
  rw [← hdrop, ← w0Fin_eq_scan (hno K), ← w0Fin_eq_scan (hno k)] at hpf
  exact hpf

/-- **The finished block of a vote** (valid rows): the vote at index `j` (pc 578) with `t`
finished blocks before it is followed, at a prefix of `k` events with more than `t` finished
blocks, by entry `t` of those, whose vote word is the vote's result and whose own maximum and
exchange word are those of the block in progress at the vote. -/
theorem w0_vote_block (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hw : warp L y < 4) (hv : W0Trace P X y) {j k : Nat}
    {e : Event} (he : X.get (y, j) = some e) (hpc : e.pc = 578)
    (hk : (w0Fin ((X.tr y).take j)).1.length < (w0Fin ((X.tr y).take k)).1.length) :
    ∃ s, (w0Fin ((X.tr y).take k)).1[(w0Fin ((X.tr y).take j)).1.length]? = some s ∧
      (w0Fin ((X.tr y).take j)).1 =
        (w0Fin ((X.tr y).take k)).1.take (w0Fin ((X.tr y).take j)).1.length ∧
      (∀ q mm a r, e.kind = .voteMode q mm a r → (w0Words s).vt = r) ∧
      w0Loc P.scale (w0Words s) = w0Loc P.scale (w0Words (w0Fin ((X.tr y).take j)).2) ∧
      (w0Words s).pm = (w0Words (w0Fin ((X.tr y).take j)).2).pm := by
  have hno := w0_noEarly hp hX hFw hnu hw
  have hcj : w0Closed ((X.tr y).take j) = (w0Fin ((X.tr y).take j)).1.length :=
    (w0Fin_length (hno j)).symm
  have hck : (w0Fin ((X.tr y).take j)).1.length < w0Closed ((X.tr y).take k) := by
    rw [← w0Fin_length (hno k)]; exact hk
  obtain ⟨K, c, hKc, hKpc, hct⟩ := w0_close_idx hck
  have hKk : K < k := by
    have := (List.getElem?_eq_some_iff.mp hKc).1
    simp only [List.length_take] at this
    omega
  have hK : X.get (y, K) = some c := by
    rw [List.getElem?_take_of_lt hKk] at hKc
    exact hKc
  rw [List.take_take, Nat.min_eq_left hKk.le] at hct
  have hjK : j < K := by
    by_contra hge
    have hne : K ≠ j := fun h => by
      subst h; rw [he] at hK; cases hK; omega
    have hpre : (X.tr y).take (K + 1) = (X.tr y).take K ++ [c] := by
      have : (X.tr y)[K]? = some c := hK
      rw [List.take_add_one, this]; rfl
    have h1 : w0Closed ((X.tr y).take (K + 1)) = w0Closed ((X.tr y).take K) + 1 := by
      unfold w0Closed
      rw [hpre, List.countP_append]
      simp [hKpc, w0ArrSPc]
    have h2 := w0Closed_mono (l := X.tr y) (show K + 1 ≤ j by omega)
    omega
  have hfirst := w0_noClose_between (X := X) (g := y) (k := j) (K := K) (by rw [hct, hcj])
  have hKl : K < (X.tr y).length := (List.getElem?_eq_some_iff.mp hK).1
  obtain ⟨ex, hexpc, hfin2, hfin1⟩ := w0_tail hp hX hFw hw (hv.take _) he (by omega) (by omega)
    (lo := 579) (by omega) (fun e' he' hu =>
      Wg0.w0_next_578 hp hX hFw hw he hpc he' hu hv) hjK hKl
    (fun q hq => hfirst q hq.le)
  have hlen : (w0Fin ((X.tr y).take K)).1.length = (w0Fin ((X.tr y).take j)).1.length := by
    rw [hfin1]
  have hblk := w0Fin_block_of_close hp hX hFw hw hK hKpc hKk hnu
  rw [hlen] at hblk
  refine ⟨_, hblk, ?_, ?_⟩
  · rw [← hfin1]
    exact List.prefix_iff_eq_take.mp (w0Fin_take_prefix hp hX hFw hnu hw hKk.le)
  have hall : ∀ f ∈ [e] ++ ex, 578 ≤ f.pc := fun f hf => by
    rcases List.mem_append.mp hf with h | h
    · rw [List.mem_singleton.mp h, hpc]
    · have := (hexpc f h).1; omega
  have hfin2' : (w0Fin ((X.tr y).take K)).2 = (w0Fin ((X.tr y).take j)).2 ++ ([e] ++ ex) := by
    rw [hfin2, List.append_assoc]
  obtain ⟨-, hhi, hmw, hpw⟩ := w0Words_ext (w0Fin ((X.tr y).take j)).2 ([e] ++ ex)
    (fun f hf => by have := hall f hf; omega)
  refine ⟨?_, ?_, ?_⟩
  · intro q mm a r hkd
    simp only [w0Words]
    rw [hfin2, w0Last_ext _ _ _ _ (fun f hf => by have := (hexpc f hf).1; simp; omega),
      Wg0.Data.w0Last_snoc]
    simp [hpc, w0VoteOf, hkd]
  · have hs : w0Score (w0Words (w0Fin ((X.tr y).take K)).2) =
        w0Score (w0Words (w0Fin ((X.tr y).take j)).2) := by
      funext i
      rw [hfin2']
      simp only [w0Score, w0PeerF, hhi, hmw, hpw]
    simp only [w0Loc, hs]
  · simp only [w0Words]
    rw [hfin2', w0Last_ext _ _ _ _ (fun f hf => by have := hall f hf; simp; omega)]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
