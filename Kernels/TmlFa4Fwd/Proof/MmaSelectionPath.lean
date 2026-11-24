-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaSelectionReads
public import Kernels.TmlFa4Fwd.Proof.EpilogueSelectionPath
import Kernels.TmlFa4Fwd.Proof.MmaModel
import Kernels.TmlFa4Fwd.Flow.Code.Part032

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue

/-- A nonzero batch index names the preceding lane while keeping the selection frame. -/
theorem selectedPreviousLane {l : Launch} {g n : Nat} {t : TState}
    {F : List (Nat × Value)} (hn : 0 < n) (hn32 : n < 32)
    (ht : At t 2055 F) (hPred : t.regs 363 = some (.pred (decide (n = 0))))
    (hRelative : (1187, b32 n) ∈ F) (hFresh : ∀ pair ∈ F, pair.1 ≠ 2501) :
    ∃ u, run kernel Assumptions.all l g 2 t = some u ∧ At u 2057 ((2501, b32 (n - 1)) :: F) := by
  obtain ⟨v, hV, hv⟩ := selectedPrefixBranch ht hPred (l := l) (g := g)
  have hAt : At v 2056 F := by simpa only [ite_eq_right hn.ne'] using hv
  obtain ⟨u, hRun, hu⟩ := selectedPreviousPrefixIndex l g hn hn32 v
    (hAt.mono ⟨holds_mem hAt.2.2.2.2 hRelative, trivial⟩)
  exact ⟨u, run_comp hV (localRun (by decide) (by decide) hAt.1 (by decide) hRun),
    schedulerOneStepFrame hAt hu Flow.code_2056 hRun (fun pair hm => by
      simpa [writesRegs] using hFresh pair hm)⟩

/-- The exclusive prefix supplies the selected batch's work offset in its group. -/
theorem selectedPreviousWork {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {t : TState} {F : List (Nat × Value)} {first batch : Nat}
    (hFirst : first ≤ batch) (hGroup : batch < first + 31) (hBatch : batch < p.batch)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ 7201) (hHeads : (7139, b32 p.heads) ∈ F) :
    let sum := ∑ lane ∈ Finset.range (batch - first), groupLaneTiles p first lane
    At t 2058 ((2502, b32 sum) :: F) →
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧
      At u 2059 ((7201, b32 (sum * p.heads)) :: F) := by
  dsimp only
  intro ht
  let sum := ∑ lane ∈ Finset.range (batch - first), groupLaneTiles p first lane
  have hPrefix := hp.prefixWork_signed (Nat.le_of_lt hBatch)
  have hPrev := precedingGroupWork p hFirst hBatch hGroup
  have hWork : sum * p.heads < 2 ^ 32 := by
    change tilePrefix p first * p.heads + sum * p.heads = _ at hPrev
    omega
  have hPositive : 0 < p.heads := by
    unfold Params.heads
    have := hp.shape.2.2.1
    omega
  have hSum := (Nat.le_mul_of_pos_right sum hPositive).trans_lt hWork
  have hHead := hp.heads_signed.trans (by decide : 2 ^ 31 < 2 ^ 32)
  obtain ⟨u, hu, hU⟩ := selectedPreviousPrefixWork l g hSum hHead hWork t
    (ht.mono ⟨ht.2.2.2.2.1, holds_mem ht.2.2.2.2.2 hHeads, trivial⟩)
  exact ⟨u, localRun (by decide) (by decide) ht.1 (by decide) hu,
    schedulerOneStepFrame (ht.mono ht.2.2.2.2.2) hU Flow.code_2058 hu (fun pair hm => by
      simpa [writesRegs] using hFresh pair hm)⟩

end PTX.Kernels.TmlFa4Fwd.Mma
