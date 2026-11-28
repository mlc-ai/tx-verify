-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Index
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLane

@[expose] public section

/-! # The index warp's mbarrier row

`mbarRow_index`: an event of a warp-7 lane at a pc of the index code that names an mbarrier is
fired from an index state (`index_at`, `Common/Where.lean`) at a poll of `valid_coord_free` or an
arrival on `valid_coord_ready` of the state's slot (`Index/Objs.lean`); the reference invariant's
counts are the lane's prefix counts (`ix_okPolls`, `ix_arrivals`, `Common/IndexLane.lean`): in
block `i` each slot `s` was used `ringUses 4 s i` times, `i` in all, so the slot is
`slot4 i` and the block's slot was polled `i / 4` times, whose parity the wait's word negates. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Row `MbarRow.Index`**: every event of a warp-7 lane at a pc of the index code that names
an mbarrier is one of `IndexUse`. -/
theorem mbarRow_index (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : MbarRow.Index P L X := by
  intro g k e l _ he hat hm
  have hub : ∀ f, e.kind ≠ .ub f := by
    intro f hk
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    subst hk
    simp [Frame.MbarOf] at hm
  obtain ⟨hw, hr1, hr2⟩ := hat
  obtain ⟨d, hR, hev, -⟩ := index_at hp hX hFw he hub ⟨hr1, hr2⟩
  obtain ⟨i, -, hsl, hpa, hc, -⟩ := hR (ix_take_noUb hX he)
  simp only [Index.RingCounts] at hc
  have hP := ix_okPolls hp hX hFw hw k
  have hA := ix_arrivals hp hX hFw hw k
  have hpolls : polls4 L g .coordFree ((X.tr g).take k) = i + Index.incW d.site := by
    unfold polls4
    rw [hP, hP, hP, hP, (hc 0).1, (hc 1).1, (hc 2).1, (hc 3).1]
    exact Index.ring_sum _
  have harrs : arrs4 L g .coordReady ((X.tr g).take k) = i := by
    unfold arrs4
    rw [hA, hA, hA, hA, (hc 0).2, (hc 1).2, (hc 2).2, (hc 3).2]
    exact Index.ring_sum _
  obtain ⟨hpc, hk⟩ := hev
  obtain ⟨pc, kd⟩ := e
  simp only at hpc hk hub ⊢
  subst hpc
  obtain ⟨site, el, ac, c⟩ := d
  dsimp only at hsl hpa hc hpolls harrs
  cases site with
  | wA | wB =>
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · subst hk
      simp only [Frame.MbarOf] at hm
      have hl' : l = loc L g (.coordFree (slot4 i)) := by
        rw [hm, Index.free_loc hp, hsl]
      simp only [Index.incW, Nat.add_zero] at hpolls
      refine .freeWait (by first | exact .inl rfl | exact .inr rfl) (by rw [hpolls]; exact hl')
        ⟨ok, ?_⟩
      have hq : okPolls l ((X.tr g).take k) = i / 4 := by
        rw [hP, hl', (hc _).1]
        simp only [Index.incW, Nat.add_zero]
        exact Index.ring_here i
      rw [hq]
      dsimp only
      rw [← hm, Index.parW_bit, hpa]
      congr 1
      rcases Nat.mod_two_eq_zero_or_one (i / 4) with h | h <;> simp [h] <;> omega
    · exact absurd hk (hub f)
  | arrA | arrB =>
    simp only [Index.EvK] at hk
    subst hk
    simp only [Frame.MbarOf] at hm
    have hl' : l = loc L g (.coordReady (slot4 i)) := by
      rw [hm, Index.ready_loc hp, hsl]
    exact .readyArrive (by first | exact .inl rfl | exact .inr rfl) (by rw [harrs]; exact hl')
      (by rw [hm]; rfl)
  | lenA | lenB =>
    rcases hk with ⟨_, _, hk⟩ | ⟨f, hk⟩
    · subst hk; simp [Frame.MbarOf] at hm
    · exact absurd hk (hub f)
  | pre | pf | xpre | xpf =>
    rcases hk with ⟨_, _, hk, -⟩ | ⟨f, hk⟩
    · subst hk; simp [Frame.MbarOf] at hm
    · exact absurd hk (hub f)
  | sA1 | sA2 | sB1 | sB2 =>
    rcases hk with ⟨_, _, _, _, _, hk⟩ | ⟨f, hk⟩
    · subst hk; simp [Frame.MbarOf] at hm
    · exact absurd hk (hub f)
  | stA | stB | bA | bB =>
    rcases hk with ⟨_, _, hk, -⟩ | ⟨f, hk⟩
    · subst hk; simp [Frame.MbarOf] at hm
    · exact absurd hk (hub f)
  | bar | exit =>
    simp only [Index.EvK] at hk
    subst hk; simp [Frame.MbarOf] at hm

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
