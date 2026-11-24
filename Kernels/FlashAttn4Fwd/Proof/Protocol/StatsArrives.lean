-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.StatsGen
public import Kernels.FlashAttn4Fwd.Proof.Protocol.StatsCreditGate
public import Kernels.FlashAttn4Fwd.Proof.Interface.Older
public import Lemmas.Protocol.NamedBarMember

@[expose] public section

/-! # The partner arrivals of the statistics barriers

`SoftArrives`, the premise of the statistics credit gate, holds (`softArrives`): a passed
`bar.sync` on statistics barrier `statsId st k` is a correction thread's (`Stats.stats_of_bar`),
and every lane of softmax warp `k + 4 st` of its CTA has its event on the barrier of the same
ordinal (`NamedBar.Sources.member_arrival_any`). A lane that exited made it before its exit: the
`bar.sync` is of an item that passed the loop test, with fewer earlier events on the barrier
than `kvBlocks + 1` per item up to it (`OlderFacts.corr_stats_sync`), and at its exit the lane
made that many (`OlderFacts.soft_stats_exit`); the items of two threads of one CTA are the
same. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

namespace Stats

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- **The partner arrivals**: a passed `bar.sync` of a statistics barrier has, for every lane of
the barrier's softmax warp, its event on the barrier of the same ordinal. -/
theorem softArrives (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (ht : StatsFacts L X)
    (ho : OlderFacts P L X) : SoftArrives L X := by
  intro y j pc st k h hst hk hb hpassed hh hcta hw
  have hy : y < L.threads := Frame.lt_of_get hX hb
  obtain ⟨-, st', k', -, hk', hid, hwy⟩ :=
    stats_of_bar ht hy hb (by unfold statsId; omega)
  obtain ⟨rfl, rfl⟩ := statsId_inj hk hk' hid
  have hwy' : warpOf L y = 8 + k := by
    rcases hwy with ⟨-, h⟩ | ⟨h, -⟩
    · cases h
    · exact h
  have hcta' : h / L.block = (y, j).1 / L.block := hcta
  have hmem : (h % L.block) / 32 ∈ pair st k := by
    simp only [pair, Finset.mem_insert, Finset.mem_singleton]
    exact .inl hw
  obtain ⟨i, pc', m, hi, hc⟩ := NamedBar.Sources.member_arrival_any hX (sources ht hk)
    (shape hpre hst hk) hb hpassed hcta' hmem (fun ⟨jx, pcx, hx⟩ => by
      obtain ⟨u, hu, hlt⟩ := ho.corr_stats_sync hy (by omega) (by omega) hb
        (by unfold statsId; omega)
      have hwork : workOf L h u = workOf L y u := by
        simp only [workOf, clusterOf, hcta]
      have hge := ho.soft_stats_exit hh (by omega) hx (hwork ▸ hu)
      rw [hw, show k + 4 * st + 3 = statsId st k by unfold statsId; omega] at hge
      obtain ⟨y', pcy, cnt, my, -, hy', hyo⟩ :=
        exists_bar (X := X) (g := h) (x := jx) (c := barOrd X y j (statsId st k))
          (id := statsId st k) (by omega)
      obtain ⟨hcnt, -⟩ := stats_of_bar ht hh hy' (by unfold statsId; omega)
      rw [hcnt] at hy'
      exact ⟨y', pcy, my, hy', hyo⟩)
  exact ⟨i, pc', some 64, m, hi, hc⟩

end Stats

end
end PTX.Kernels.FlashAttn4Fwd.Proof
