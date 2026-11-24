-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPrefixSaved
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSecondPrefix
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderInputOrder
import Kernels.TmlFa4Fwd.Flow.Code.Part010
import Lemmas.Flow.NotShfl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame Prologue Epilogue

noncomputable section

/-- A peer whose actual shuffle ordinal is beyond the 32 K broadcasts must
have passed its initial K commit and the V pointer preparation. -/
theorem primingVPeerFirstBroadcastFloor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g lane batch j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    {e : Event} (he : X.get (warpLane l g lane, j) = some e) (hPc : 543 < e.pc)
    (hMark : Execution.isShfl e = true)
    (hDemand : primingSearchShuffleCount batch + 32 ≤
      ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl) :
    805 ≤ e.pc := by
  obtain ⟨b, hb', hlo, hhi, hTile, index, s, ending, hs, hr, _, hRank, read, a, bytes, _,
    hRead, hSaved⟩ := loaderPrimingKPointerAndSavedOfActiveEvent hp hX hg hw hl writes hCTA he
      (by decide : 543 ≤ 543) hPc
  obtain ⟨selected, _, only⟩ := tileBatch_existsUnique p hCTA
  have hEq : b = batch := (only b ⟨hb', hlo, hhi⟩).trans (only batch ⟨hb, hLo, hHi⟩).symm
  subst b
  let thread := warpLane l g lane
  have hSafe : ∀ f, e.kind ≠ .ub f := by
    intro f hf
    cases e with
    | mk pc kind =>
      change kind = .ub f at hf
      subst kind
      cases hMark
  have hBefore : index ≤ j := by
    by_contra! hEarly
    have hLe := Flow.countP_take_mono Execution.isShfl (X.tr thread) hEarly.le
    rw [hRank] at hLe
    change primingSearchShuffleCount batch + 32 ≤ ((X.tr thread).take j).countP
      Execution.isShfl at hDemand
    omega
  have hWarp : warpIndex l g = warpIndex l thread :=
    (Step.sameWarp_lane (by rw [hp.block]) hg hl).1.2
  have hLoader : 14 ≤ warpIndex l thread := hWarp ▸ hw
  have hh := (assignedCoordinates_valid hp hLo hHi).2
  have hHead : (assignedCoordinates p batch (g / l.block)).2 / 6 < p.kvHeads := by
    unfold Params.heads at hh
    omega
  obtain ⟨u, pos, stop, hPos, hu, huRun, huRank⟩ :=
    primingKSecondPointerInPrefix hp hX (rank := primingSearchShuffleCount batch)
      hLoader hb hHead hTile hs hr hRank hRead hSaved he hBefore
      (.inr ⟨hMark, Nat.le_trans (Nat.add_le_add_left (by decide : 16 ≤ 32) _) hDemand⟩) hSafe
  have hCount : loaderShuffleTail 673 610 = 16 := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hLater : 673 ≤ e.pc ∨ (Execution.isShfl e = true ∧
      ((X.tr thread).take pos).countP Execution.isShfl + loaderShuffleTail 673 610 ≤
      ((X.tr thread).take j).countP Execution.isShfl) := by
    right
    refine ⟨hMark, ?_⟩
    rw [huRank, hCount, Nat.add_assoc]
    exact hDemand
  obtain ⟨v, front, stop', _, hv, hvRun, _, hvPos⟩ :=
    prefixCountedShuffleCut (start := 610) (stop := 673) (F := []) (by decide)
      (by intro branch; set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      ⟨_, Flow.code_673, rfl⟩ (hu.mono trivial) huRun he hPos hLater hSafe
  have hMore := traceAfterObservedEvent he hvPos
  obtain ⟨hCommit, _⟩ := primingKCommitAdvanceInPrefix hv hvRun hMore
  have hFloor : 673 ≤ e.pc := by
    by_contra! hEarly
    have hAudit : ∀ branch, ((kernel.code.drop 673).take (1901 - 673)).all
        (fun ins => loaderPipelineCutOp 673 1901 branch [2535, 1062] ins.op) = true := by
      intro branch
      set_option maxRecDepth 100000 in kernel_rfl
    have hBad := Thread.Loader.eventBeforeClosedCut hp hX hLoader (cut := 673) (by decide)
      hAudit hCommit he hvPos (by omega) hEarly
    exact Nat.lt_irrefl _ hBad
  by_contra! hEarlier
  rcases get_source hX he with ⟨f, hf⟩ | ⟨u, ins, _, _, hCode, hFire⟩
  · exact hSafe f hf
  have hGet : ((kernel.code.drop 673).take (805 - 673))[e.pc - 673]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hFloor]
    exact hCode
  have hAudit : ((kernel.code.drop 673).take (805 - 673)).all (fun i => !i.op.isShfl) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hNo := List.all_eq_true.mp hAudit _ (List.mem_of_getElem? hGet)
  rw [fires_shfl_op hFire hMark] at hNo
  cases hNo

end
end PTX.Kernels.TmlFa4Fwd.Loader
