-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Dequant
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantLane

@[expose] public section

/-! # Warpgroup 2's mbarrier row

`mbarRow_dequant`: an event of a warpgroup-2 lane at a pc of its code that names an mbarrier is
fired from a warpgroup-2 state (`dequant_at`, `Common/Where.lean`) whose site is one of the
role's mbarrier sites, on the site's object (`Dequant/Objs.lean`); the reference invariant's
counts are the lane's prefix counts of successful polls and arrivals (`wg2_okPolls`,
`wg2_arrivals`, `Common/DequantLane.lean`): in block `i` each family's two slots were used `i`
times, slot `i % 2` of them `i / 2` times, which give the ring slots and parities of
`DequantUse`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Row `MbarRow.Dequant`**: every event of a warpgroup-2 lane at a pc of its code that names an
mbarrier is one of `DequantUse`. -/
theorem mbarRow_dequant (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : MbarRow.Dequant P L X := by
  intro g k e l _ he hat hm
  have hub : ∀ f, e.kind ≠ .ub f := by
    intro f hk
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    subst hk
    simp [Frame.MbarOf] at hm
  obtain ⟨hw8, hw12, hr1, hr2⟩ := hat
  obtain ⟨d, hR, hev, hw⟩ := dequant_at hp hX hFw he hub ⟨hr1, hr2⟩
  have hc := hR (wg2_take_noUb hX he)
  have hP := wg2_okPolls hp hX hFw hw k
  have hA := wg2_arrivals hp hX hFw hw k
  obtain ⟨hpc, hk⟩ := hev
  obtain ⟨pc, kd⟩ := e
  simp only at hpc hk hub ⊢
  subst hpc
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases site with
  | wq =>
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · subst hk
      simp only [Frame.MbarOf] at hm
      have hl' := hm.trans (Dequant.q_loc hp)
      obtain ⟨h0, -⟩ := hc
      dsimp only at h0
      refine .qWait rfl hl' ⟨ok, by rw [hm]; rfl⟩ ?_
      rw [hP, hl']
      exact h0
    · exact absurd hk (hub f)
  | wraw =>
    obtain ⟨i, -, hsb, hpb, hn⟩ := hc
    dsimp only [Dequant.SlotCounts] at hsb hpb hn
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · subst hk
      simp only [Frame.MbarOf] at hm
      have h2 : polls2 L g .rawReady ((X.tr g).take k) = i := by
        unfold polls2
        rw [hP, hP, (hn 0).1, (hn 1).1]
        exact Dequant.uses_sum i
      have hl' : l = loc L g (.rawReady (slot2 i)) := by
        rw [hm, Dequant.raw_loc hp, hsb, Dequant.slotF_slot2]
      refine .rawWait rfl (by rw [h2]; exact hl') ⟨ok, ?_⟩
      rw [← hm, hP, hl', (hn _).1, Dequant.rawPar_bit, hpb]
      simp only [Dequant.incR, Nat.add_zero, Dequant.uses_slot, decide_eq_true_eq]
      congr 1
      split_ifs <;> omega
    · exact absurd hk (hub f)
  | wsv =>
    obtain ⟨i, -, hsb, hpb, hn⟩ := hc
    dsimp only [Dequant.SlotCounts] at hsb hpb hn
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · subst hk
      simp only [Frame.MbarOf] at hm
      have h2 : polls2 L g .svDone ((X.tr g).take k) = i := by
        unfold polls2
        rw [hP, hP, (hn 0).2.1, (hn 1).2.1]
        exact Dequant.uses_sum i
      have hl' : l = loc L g (.svDone (slot2 i)) := by
        rw [hm, Dequant.sv_loc hp, hsb, Dequant.slotF_slot2]
      refine .svWait rfl (by rw [h2]; exact hl') ⟨ok, ?_⟩
      rw [← hm, hP, hl', (hn _).2.1, Dequant.svPar_bit, hpb]
      simp only [Dequant.incS, Nat.add_zero, Dequant.uses_slot, decide_eq_true_eq]
      congr 1
      split_ifs <;> omega
    · exact absurd hk (hub f)
  | arrD =>
    obtain ⟨i, -, hsb, -, hn⟩ := hc
    dsimp only [Dequant.SlotCounts] at hsb hn
    simp only [Dequant.EvK] at hk
    subst hk
    simp only [Frame.MbarOf] at hm
    have h2 : arrs2 L g .dequantReady ((X.tr g).take k) = i := by
      unfold arrs2
      rw [hA, hA, (hn 0).2.2.1, (hn 1).2.2.1]
      exact Dequant.uses_sum i
    have hl' : l = loc L g (.dequantReady (slot2 i)) := by
      rw [hm, Dequant.ready_loc hp, hsb, Dequant.slotF_slot2]
    exact .readyArrive rfl (by rw [h2]; exact hl') (by rw [hm]; rfl)
  | arrF =>
    obtain ⟨i, -, hsb, -, hn⟩ := hc
    dsimp only [Dequant.SlotCounts] at hsb hn
    simp only [Dequant.EvK] at hk
    subst hk
    simp only [Frame.MbarOf] at hm
    have h2 : arrs2 L g .rawFree ((X.tr g).take k) = i := by
      unfold arrs2
      obtain ⟨-, -, -, h0⟩ := hn 0
      obtain ⟨-, -, -, h1⟩ := hn 1
      rw [hA, hA, h0, h1]
      exact Dequant.uses_sum i
    have hl' : l = loc L g (.rawFree (slot2 i)) := by
      rw [hm, Dequant.free_loc hp, hsb, Dequant.slotF_slot2]
    exact .freeArrive rfl (by rw [h2]; exact hl') (by rw [hm]; rfl)
  | smr =>
    obtain ⟨inst, hk⟩ := hk
    subst hk; simp [Frame.MbarOf] at hm
  | lenA | lenB =>
    rcases hk with ⟨_, _, hk⟩ | ⟨f, hk⟩
    · subst hk; simp [Frame.MbarOf] at hm
    · exact absurd hk (hub f)
  | scale _ | raw _ _ =>
    rcases hk with ⟨_, _, hk, -⟩ | ⟨f, hk⟩
    · subst hk; simp [Frame.MbarOf] at hm
    · exact absurd hk (hub f)
  | store _ _ =>
    rcases hk with ⟨_, _, hk, -⟩ | ⟨f, hk⟩
    · subst hk; simp [Frame.MbarOf] at hm
    · exact absurd hk (hub f)
  | fpx | bar | exit =>
    simp only [Dequant.EvK] at hk
    subst hk
    simp [Frame.MbarOf] at hm

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
