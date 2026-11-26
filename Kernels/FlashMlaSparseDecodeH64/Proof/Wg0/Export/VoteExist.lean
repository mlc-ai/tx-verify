-- SPDX-License-Identifier: Apache-2.0
-- domain: complete
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Vote
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Epi
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Lemmas.Kernel.FullVote
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.StepPlumb
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0VoteLag
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0TcLag
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.VoteIn
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FinLen
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Closed
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockList
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.VoteCmp

@[expose] public section

/-! # The vote of every block of a complete lane

A lane of warpgroup 0 that exits has made one full-mask vote per block (`vote_cnt_exit`): for
each block `t` below the CTA's block count its `t`-th vote exists, is the `any` vote at pc 578
with the block's own `t` finished blocks before it, records `w0VoteIn` of the trace before it
(`w0_vote_input`), and is followed by the closing event of its block. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}

/-- **The `t`-th vote of a lane** (complete, valid rows): the lane's `t`-th full-mask vote is at
pc 578, the `any` vote of the full mask, has `t` votes and `t` finished blocks before it, records
`w0VoteIn`, and the lane closes `t + 1` blocks in all. -/
theorem w0_vote_exists (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hw : warp L y < 4) (hy : y < L.threads)
    (hv : W0Trace P X y) (hC : Complete L X)
    (hex103 : ∀ k pc, X.get (y, k) = some ⟨pc, .exit⟩ → 103 ≤ pc)
    {t : Nat} (ht : t < blocksOf P L (y / L.block)) :
    ∃ j a r, X.get (y, j) = some ⟨578, .voteMode .any (2 ^ 32 - 1) a r⟩ ∧
      ((X.tr y).take j).countP (voteWith (2 ^ 32 - 1)) = t ∧
      (w0Fin ((X.tr y).take j)).1.length = t ∧ a = w0VoteIn P.scale ((X.tr y).take j) ∧
      t + 1 ≤ (w0Fin (X.tr y)).1.length := by
  obtain ⟨pcx, hlast⟩ := (hC.1 _ hy).resolve_left (noCanceled hX _)
  have hlast' := hlast
  rw [List.getLast?_eq_getElem?] at hlast'
  have hex : X.get (y, (X.tr y).length - 1) = some ⟨pcx, .exit⟩ := hlast'
  have h103 := hex103 _ _ hex
  obtain ⟨σ, hσ, -, -, -, -⟩ := ev_at hp hX hFw hex (fun _ h => by cases h)
  have hcnt := vote_cnt_exit hp hX hFw hnu hw hy hσ hex
  obtain ⟨j, e, hjk, he, hvw, hc⟩ := exists_nthEv (X := X) (p := voteWith (2 ^ 32 - 1)) (g := y)
    (k := (X.tr y).length - 1) (n := t) (by unfold vCnt at hcnt; omega)
  obtain ⟨hpc, a, r, hk⟩ := w0_voteKind hp hX hFw hnu hw hy he hvw
  obtain ⟨hc2, -⟩ := w0_vote_ord hp hX hFw hnu hw he hpc
  have hin := w0_vote_input hp hX hFw hw he hpc (hv.take (j + 1)) _ a r hk
  obtain ⟨pc, kd⟩ := e
  simp only at hpc hk
  subst hpc hk
  refine ⟨j, a, r, he, hc, hc2.symm.trans hc, hin, ?_⟩
  obtain ⟨K, c, hjK, hK, hKpc⟩ := w0_closed_of_exit hp hX hFw hw hv hlast h103 j _ he
    (by show 566 ≤ 578; omega) (by show 578 ≤ 1121; omega)
  have hno := w0_noEarly hp hX hFw hnu hw
  have h1 : w0Closed ((X.tr y).take (K + 1)) = w0Closed ((X.tr y).take K) + 1 := by
    have hpre : (X.tr y).take (K + 1) = (X.tr y).take K ++ [c] := by
      have : (X.tr y)[K]? = some c := hK
      rw [List.take_add_one, this]; rfl
    unfold w0Closed
    rw [hpre, List.countP_append]
    simp [hKpc, w0ArrSPc]
  have h2 := w0Closed_mono (l := X.tr y) (show j ≤ K by omega)
  have h3 := w0Closed_mono (l := X.tr y) (show K + 1 ≤ (X.tr y).length by
    exact (List.getElem?_eq_some_iff.mp hK).1)
  rw [List.take_length] at h3
  have hlt : (w0Fin (X.tr y)).1.length = w0Closed (X.tr y) := by
    have := w0Fin_length (hno (X.tr y).length)
    rwa [List.take_length] at this
  have hj : (w0Fin ((X.tr y).take j)).1.length = w0Closed ((X.tr y).take j) :=
    w0Fin_length (hno j)
  have hjt : (w0Fin ((X.tr y).take j)).1.length = t := hc2.symm.trans hc
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
