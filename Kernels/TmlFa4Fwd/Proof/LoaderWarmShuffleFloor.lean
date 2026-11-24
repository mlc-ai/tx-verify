-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPrefixOrigins
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmPointerReload
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.SoftmaxScheduleWarp
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderInputOrder
import Lemmas.Flow.NotShfl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue Prologue

noncomputable section

set_option maxRecDepth 100000 in
/-- A shuffle of at least the first warm ordinal is beyond both initial packets. -/
theorem warmShuffleFloor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g lane batch j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    {e : Event} (he : X.get (warpLane l g lane, j) = some e) (hLate : 804 < e.pc)
    (hShfl : Execution.isShfl e = true)
    (hRank : primingSearchShuffleCount batch + 64 ≤
      ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl) :
    1004 ≤ e.pc := by
  have hSafe : ∀ f, e.kind ≠ .ub f := by
    intro f h
    obtain ⟨pc, kind⟩ := e
    change kind = .ub f at h
    subst kind
    cases hShfl
  obtain ⟨b, hb', hlo, hhi, pos, hBefore, s, ending, hs, hr, hsRank, _⟩ :=
    loaderPrimingVFirstPointerAndSavedOfActiveEvent hp hX hg hw hl writes hCTA he hLate hSafe
  obtain ⟨witness, _, only⟩ := tileBatch_existsUnique p hCTA
  have heq : b = batch := (only b ⟨hb', hlo, hhi⟩).trans (only batch ⟨hb, hLo, hHi⟩).symm
  subst b
  have hStart : At s 805 [] := hs.mono trivial
  have hAudit : ∀ bound, ((kernel.code.drop 805).take (903 - 805)).all
      (fun ins => loaderPipelineCutOp 805 903 bound [] ins.op) = true := by
    intro bound
    set_option maxRecDepth 100000 in kernel_rfl
  have hCounted : (((kernel.code.drop 805).take (903 - 805)).zipIdx 805).all
      (fun (ins, pc) => LoaderRankedInstr 903 pc ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hCount : loaderShuffleTail 903 805 = 32 := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨v, front, stop, _, hV, hvRun, _, hvOrder⟩ :=
    prefixRankedShuffleCut (by decide) hAudit hCounted hStart hr he hBefore
      (.inr ⟨hShfl, by rw [hsRank, hCount, Nat.add_assoc]; exact hRank⟩) hSafe
  have hMore : (X.tr (warpLane l g lane)).drop (pos + front.length) ≠ [] := by
    intro h
    have hGet := he
    change (X.tr (warpLane l g lane))[j]? = some e at hGet
    rw [← Nat.add_sub_of_le hvOrder, ← List.getElem?_drop, h] at hGet
    cases hGet
  have hNext : Next kernel Assumptions.all l (warpLane l g lane) v v
      (.asyncCommit (next v)) := by
    refine ⟨.refl, ?_⟩
    rw [out_event hV.2.2.2.1 (by rw [hV.1]; exact Flow.code_903) rfl rfl]
    rfl
  obtain ⟨_, _, hCommit, ⟨rfl, _⟩, _⟩ := hNext.continuing_at_nonempty (by
    rintro e ⟨_, h⟩
    cases h) hvRun hMore
  rw [hV.1] at hCommit
  have hLower : 903 ≤ e.pc := by
    by_contra! hEarly
    have hwLane : 14 ≤ warpIndex l (warpLane l g lane) := by
      have same : warpIndex l g = warpIndex l (warpLane l g lane) :=
        (Step.sameWarp_lane (by rw [hp.block]) hg hl).1.2
      rw [← same]
      exact hw
    have audit (bound : Nat) : ((kernel.code.drop 903).take (1901 - 903)).all
        (fun ins => loaderPipelineCutOp 903 1901 bound [2535, 1062] ins.op) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    exact (Nat.lt_irrefl 903)
      (Thread.Loader.eventBeforeClosedCut hp hX hwLane (cut := 903) (by decide)
        audit hCommit he hvOrder (by omega) hEarly)
  by_contra! hEarlier
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, _, _, hCode, hFire⟩
  · exact hSafe f hf
  have hGet : ((kernel.code.drop 903).take (1004 - 903))[e.pc - 903]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le hLower]
    exact hCode
  have hNoShuffle : ((kernel.code.drop 903).take (1004 - 903)).all
      (fun ins => !ins.op.isShfl) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hNo := List.all_eq_true.mp hNoShuffle _ (List.mem_of_getElem? hGet)
  rw [fires_shfl_op hFire hShfl] at hNo
  cases hNo

end
end PTX.Kernels.TmlFa4Fwd.Loader
