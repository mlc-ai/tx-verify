-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollIxFacts
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollIdle
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowHead
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View

@[expose] public section

/-! # The index warp's collectives: the state at a collective, and the times

`ix_at`, `ix_time_at`, `ix_time_lt`, `ix_exit`: the facts of `CollCls` for the lanes of warp 7 of
a CTA, over the startup's, the head's and the index code's states. The slot of the `n`-th
collective is the startup's and the head's for `n < 3`, then block `(n - 3) / 2`'s shuffle
(`ixSlot`: `frame` of the block plus the shuffle's place, 7 or 8). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {x : Nat}

/-- The slots of warp 7's collectives. -/
def ixSlot (n : Nat) : Nat :=
  if n < 3 then idleSlot n else idleBase + ixBlk0 + stride * ((n - 3) / 2) + 7 + (n - 3) % 2

theorem ixSlot_blk (b r : Nat) (hr : r < 2) :
    ixSlot (3 + 2 * b + r) = idleBase + ixBlk0 + stride * b + 7 + r := by
  have h1 : (3 + 2 * b + r - 3) / 2 = b := by omega
  have h2 : (3 + 2 * b + r - 3) % 2 = r := by omega
  have h3 : ¬ (3 + 2 * b + r < 3) := by omega
  simp only [ixSlot, h1, h2, h3, ite_false]

theorem ixSlot_ge {b n : Nat} (hn : 3 + 2 * b ≤ n) :
    idleBase + ixBlk0 + stride * b + 7 ≤ ixSlot n := by
  have h3 : ¬ (n < 3) := by omega
  have : stride * b ≤ stride * ((n - 3) / 2) := Nat.mul_le_mul_left _ (by omega)
  simp only [ixSlot, h3, ite_false]
  omega

theorem ixSlot_ge2 {b n : Nat} (hn : 5 + 2 * b ≤ n) :
    idleBase + ixBlk0 + stride * b + 128 + 7 ≤ ixSlot n := by
  have h3 : ¬ (n < 3) := by omega
  have : stride * (b + 1) ≤ stride * ((n - 3) / 2) := Nat.mul_le_mul_left _ (by omega)
  have h4 : stride * (b + 1) = stride * b + 128 := by simp [stride, Nat.mul_add]
  simp only [ixSlot, h3, ite_false]
  omega

theorem idleSlot_le (n : Nat) : idleSlot n ≤ 101 := by
  unfold idleSlot
  split_ifs with h
  · interval_cases n <;> simp
  · omega

theorem ixSlot_mono {a b c : Nat} (hab : a < b) (hb : (ixCn P L c b).isSome = true) :
    ixSlot a < ixSlot b := by
  have hb3 : b < 3 ∨ 3 ≤ b := by omega
  rcases hb3 with hb3 | hb3
  · interval_cases b <;> interval_cases a <;> simp [ixSlot, idleSlot]
  · by_cases ha : a < 3
    · have := idleSlot_le a
      have h5 := ixSlot_ge (b := 0) (n := b) (by omega)
      have ea : ixSlot a = idleSlot a := by simp [ixSlot, ha]
      simp only [ixBlk0, idleBase, roleBase, loopBase, ixOff, ixOrg, stride] at h5
      omega
    · simp only [ixSlot, ha, show ¬ b < 3 by omega, ite_false, stride]
      omega

/-- A site's pc is a collective's exactly at a shuffle site. -/
theorem ix_coll_site {d : Index.D} {n : Cls → Nat} :
    CollAt P L x (ixS P L x d n) ↔ (d.site = .sA1 ∨ d.site = .sA2 ∨ d.site = .sB1 ∨
      d.site = .sB2) := by
  rw [collAt_iff]
  change d.site.pc ∈ collPcs ↔ _
  cases d.site <;> simp [IxSite.pc, collPcs]

/-- **A state of a lane of warp 7**, with the head's ghost count. -/
theorem ix_cls2 (hFw : Follow P L X) (hx : x < L.threads) (hw : warpOf L x = 7) {k : Nat}
    {σ : (thread P L x).D} (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) :
    (∃ d n, σ = (.inl d, n) ∧ Startup.RefW L x d (n .shfl) ∧ Startup.exitOf d = none) ∨
    (∃ s n, σ = (.inr ⟨.inl .wg1, .inl s⟩, n) ∧ (s = .smr ∨ s = .hsh) ∧ n .shfl = 2) ∨
      ∃ d n, σ = ixS P L x d n := by
  rcases ix_cls hFw hx hw hσ with h | ⟨s, n, rfl, hs⟩ | h
  · exact .inl h
  · right; left
    have hJ := (follow_iff.mp hFw x hx k).2 _ hσ
    obtain ⟨-, hR, -, -⟩ := hJ
    refine ⟨s, n, rfl, hs, ?_⟩
    rcases hs with rfl | rfl
    · exact (show Wg1.HRef L x .smr (n .shfl) from hR).1
    · exact (show Wg1.HRef L x .hsh (n .shfl) from hR).1
  · exact .inr (.inr h)

theorem startup_shfl_two {d : Startup.D} {n : Cls → Nat} (hW : Startup.RefW L x d (n .shfl))
    (h : ∀ j, d.site ≠ .sh j) : n .shfl = 2 := by
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | sh j => exact absurd rfl (h j)
  | _ => exact hW.1

/-- **A state of a lane of warp 7 is at a collective exactly when its pc is the list's entry at
its ghost count.** -/
theorem ix_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hx : x < L.threads) (hw : warpOf L x = 7) {k : Nat}
    {σ : (thread P L x).D} (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) :
    CollAt P L x σ ↔ ixCn P L (x / L.block) (σ.2 .shfl) = some ((thread P L x).pc σ) := by
  rcases ix_cls2 hFw hx hw hσ with ⟨d, n, rfl, hW, hxd⟩ | ⟨s, n, rfl, hs, hn⟩ | ⟨d, n, rfl⟩
  · rw [collAt_iff, pc_startup]
    show d.site.pc ∈ collPcs ↔ ixCn P L (x / L.block) (n .shfl) = some d.site.pc
    by_cases hc : d.site.pc ∈ collPcs
    · obtain ⟨j, hj⟩ := sh_site (by omega) hW hc
      obtain ⟨site, x1, x2⟩ := d
      simp only at hj
      subst hj
      obtain ⟨h1, -⟩ := hW
      simp only [hc, true_iff, h1]
      fin_cases j <;> simp [ixCn, Startup.Site.pc]
    · simp only [hc, false_iff]
      have h2 := startup_shfl_two hW fun j hj => hc (by rw [hj]; exact (by fin_cases j <;> decide))
      have hle := Startup.Site.pc_le d.site fun r hr => by simp [Startup.exitOf, hr] at hxd
      rw [h2]
      simp [ixCn]
      omega
  · rcases hs with rfl | rfl
    · rw [collAt_iff, pc_smr]
      change _ ↔ ixCn P L (x / L.block) (n .shfl) = _
      rw [hn]
      simp [ixCn, collPcs]
    · rw [collAt_iff, pc_hsh]
      change _ ↔ ixCn P L (x / L.block) (n .shfl) = _
      rw [hn]
      simp [ixCn, collPcs]
  · obtain ⟨b, hsh, -, hel, h1, h2, h3⟩ := ix_facts hp hX hFw (noUbBefore_of_noUb hub) hσ hx hw
    rw [ix_coll_site]
    show _ ↔ ixCn P L (x / L.block) (n .shfl) = some d.site.pc
    rw [hsh]
    by_cases hs : d.site = .sA1 ∨ d.site = .sA2 ∨ d.site = .sB1 ∨ d.site = .sB2
    · rcases hs with hs | hs | hs | hs
      · obtain ⟨hM, hR⟩ := h1 (.inl hs)
        rw [hs]
        have h0 := ixCn_blk (P := P) (L := L) (x / L.block) b 0 (by omega)
        rw [Nat.add_zero] at h0
        simp [Index.soff, h0, hM, hR, IxSite.pc]
      · obtain ⟨hM, hR⟩ := h1 (.inr hs)
        rw [hs]
        have := ixCn_blk (P := P) (L := L) (x / L.block) b 1 (by omega)
        rw [show 3 + 2 * b + Index.soff .sA2 = 3 + 2 * b + 1 from rfl, this]
        simp [hM, hR, IxSite.pc]
      · obtain ⟨hM, hR⟩ := h2 (.inl hs)
        rw [hs]
        have h0 := ixCn_blk (P := P) (L := L) (x / L.block) b 0 (by omega)
        rw [Nat.add_zero] at h0
        simp [Index.soff, h0, not_lt.mpr hM, hR, IxSite.pc]
      · obtain ⟨hM, hR⟩ := h2 (.inr hs)
        rw [hs]
        have := ixCn_blk (P := P) (L := L) (x / L.block) b 1 (by omega)
        rw [show 3 + 2 * b + Index.soff .sB2 = 3 + 2 * b + 1 from rfl, this]
        simp [not_lt.mpr hM, hR, IxSite.pc]
    · simp only [hs, false_iff]
      intro h
      rcases ixCn_val h with ⟨h3', -⟩ | h4
      · omega
      · revert hs h4
        cases d.site <;> simp [IxSite.pc]

theorem ixSlot_two {n : Nat} (hn : 2 ≤ n) : 101 ≤ ixSlot n := by
  by_cases h : n < 3
  · have : n = 2 := by omega
    subst this
    simp [ixSlot, idleSlot]
  · have := ixSlot_ge (b := 0) (n := n) (by omega)
    simp only [ixBlk0, idleBase, roleBase, loopBase, ixOff, ixOrg, stride] at this
    omega

theorem placeAt_le0 {b el : Nat} {s : IxSite} (hel : el < s.elems) (h1 : Index.soff s = 0)
    (h2 : s ≠ .bar) (h3 : s ≠ .exit) (h4 : s ≠ .sA1) (h5 : s ≠ .sB1) :
    Index.placeAt b s el ≤ ixBlk0 + stride * b + 6 := by
  cases s <;> simp_all [Index.placeAt, Index.ord, IxSite.elems, Index.soff] <;> omega

theorem placeAt_le {b el : Nat} {s : IxSite} (hel : el < s.elems)
    (h2 : s ≠ .bar) (h3 : s ≠ .exit) : Index.placeAt b s el ≤ ixBlk0 + stride * b + 13 := by
  cases s <;> simp_all [Index.placeAt, Index.ord, IxSite.elems] <;> omega

/-- **The time of a state at a collective is its slot.** -/
theorem ix_time_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hx : x < L.threads) (hw : warpOf L x = 7) {k : Nat}
    {σ : (thread P L x).D} (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (hc : CollAt P L x σ) : time P L x σ = ixSlot (σ.2 .shfl) := by
  have hc' := collAt_iff.mp hc
  rcases ix_cls2 hFw hx hw hσ with ⟨d, n, rfl, hW, -⟩ | ⟨s, n, rfl, hs, hn⟩ | ⟨d, n, rfl⟩
  · rw [pc_startup] at hc'
    obtain ⟨j, hj⟩ := sh_site (by omega) hW hc'
    show Startup.time d = ixSlot (n .shfl)
    obtain ⟨site, x1, x2⟩ := d
    simp only at hj
    subst hj
    obtain ⟨h1, -⟩ := hW
    rw [Startup.time_of_ne (by simp), h1]
    fin_cases j <;> simp [Startup.Site.pc, ixSlot, idleSlot]
  · rcases hs with rfl | rfl
    · rw [pc_smr] at hc'; simp [collPcs] at hc'
    · change _ = ixSlot (n .shfl)
      rw [hn]
      simp [time, fragTime, wg1Time, Wg1.time, roleBase, ixSlot, idleSlot]
  · obtain ⟨b, hsh, hbl, hel, h1, h2, h3⟩ := ix_facts hp hX hFw (noUbBefore_of_noUb hub) hσ hx hw
    have hs := ix_coll_site.mp hc
    show idleBase + Index.time L x d (fun c => n (.index c)) = ixSlot (n .shfl)
    rw [hsh]
    unfold Index.time Index.place
    rw [hbl]
    rcases hs with hs | hs | hs | hs <;> rw [hs] at hel ⊢ <;> simp only [IxSite.elems] at hel <;>
      have hel0 : d.el = 0 := by omega
    all_goals
      first
        | rw [show 3 + 2 * b + Index.soff .sA1 = 3 + 2 * b + 0 from rfl, ixSlot_blk b 0 (by omega)]
        | rw [show 3 + 2 * b + Index.soff .sA2 = 3 + 2 * b + 1 from rfl, ixSlot_blk b 1 (by omega)]
        | rw [show 3 + 2 * b + Index.soff .sB1 = 3 + 2 * b + 0 from rfl, ixSlot_blk b 0 (by omega)]
        | rw [show 3 + 2 * b + Index.soff .sB2 = 3 + 2 * b + 1 from rfl, ixSlot_blk b 1 (by omega)]
    all_goals simp [Index.placeAt, Index.ord, hel0]; omega

theorem ix_time_lt (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hx : x < L.threads) (hw : warpOf L x = 7) {k : Nat}
    {σ : (thread P L x).D} (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (hc : ¬ CollAt P L x σ) {n : Nat} (hn : (ixCn P L (x / L.block) n).isSome = true)
    (hle : σ.2 .shfl ≤ n) : time P L x σ < ixSlot n := by
  rcases ix_cls2 hFw hx hw hσ with ⟨d, n0, rfl, hW, hxd⟩ | ⟨s, n0, rfl, hs, hn0⟩ | ⟨d, n0, rfl⟩
  · have hc' : (thread P L x).pc (.inl d, n0) ∉ collPcs := fun h => hc (collAt_iff.mpr h)
    rw [pc_startup] at hc'
    have h2 := startup_shfl_two hW fun j hj => hc' (by rw [hj]; fin_cases j <;> decide)
    have hlt := Startup.time_lt hxd
    have := ixSlot_two (n := n) (by simp only at hle; omega)
    show Startup.time d < _
    omega
  · rcases hs with rfl | rfl
    · have := ixSlot_two (n := n) (by simp only at hle; omega)
      simp only [time, fragTime, wg1Time, Wg1.time, roleBase]
      omega
    · exact absurd (collAt_iff.mpr (by rw [pc_hsh]; simp [collPcs])) hc
  · obtain ⟨b, hsh, hbl, hel, h1, h2, h3⟩ := ix_facts hp hX hFw (noUbBefore_of_noUb hub) hσ hx hw
    have hcs : ¬ (d.site = .sA1 ∨ d.site = .sA2 ∨ d.site = .sB1 ∨ d.site = .sB2) :=
      fun h => hc (ix_coll_site.mpr h)
    have hle' : 3 + 2 * b + Index.soff d.site ≤ n := by
      have : (ixS P L x d n0).2 .shfl = n0 .shfl := rfl
      omega
    show idleBase + Index.time L x d (fun c => n0 (.index c)) < _
    unfold Index.time Index.place
    rw [hbl]
    by_cases hbe : d.site = .bar ∨ d.site = .exit
    · exfalso
      have hR := h3 hbe
      have hs0 : Index.soff d.site = 0 := by rcases hbe with h | h <;> rw [h] <;> rfl
      have := ixCn_none hn (by omega)
      omega
    · push Not at hbe
      by_cases hs0 : Index.soff d.site = 0
      · have := placeAt_le0 (b := b) hel hs0 hbe.1 hbe.2 (fun h => hcs (.inl h))
          (fun h => hcs (.inr (.inr (.inl h))))
        have := ixSlot_ge (b := b) (n := n) (by omega)
        omega
      · have := placeAt_le (b := b) hel hbe.1 hbe.2
        have hs2 : Index.soff d.site = 2 := by
          cases hsite : d.site <;> simp_all [Index.soff]
        have := ixSlot_ge2 (b := b) (n := n) (by omega)
        omega

theorem ix_exit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hx : x < L.threads) (hw : warpOf L x = 7)
    {k pc : Nat} {σ : (thread P L x).D}
    (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (he : X.get (x, k) = some ⟨pc, .exit⟩) {n : Nat}
    (hn : (ixCn P L (x / L.block) n).isSome = true) : n < σ.2 .shfl := by
  have hpc : pc = (thread P L x).pc σ :=
    Frame.event_pcU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ (fun f h => by cases h)
  have h3 : pc = 3611 := exit_event_pc hX he
  rcases ix_cls2 hFw hx hw hσ with ⟨d, n0, rfl, hW, hxd⟩ | ⟨s, n0, rfl, hs, hn0⟩ | ⟨d, n0, rfl⟩
  · have hle := Startup.Site.pc_le d.site fun r hr => by simp [Startup.exitOf, hr] at hxd
    rw [pc_startup] at hpc
    omega
  · rcases hs with rfl | rfl
    · rw [pc_smr] at hpc; omega
    · rw [pc_hsh] at hpc; omega
  · obtain ⟨b, hsh, hbl, hel, h1, h2, h3'⟩ := ix_facts hp hX hFw (noUbBefore_of_noUb hub) hσ hx hw
    have hs : d.site = .exit := by
      have : 3611 = d.site.pc := by rw [← h3]; exact hpc
      revert this
      cases d.site <;> simp [IxSite.pc]
    have hR := h3' (.inr hs)
    show n < n0 .shfl
    rw [hsh, hs]
    by_cases hn3 : n < 3
    · simp [Index.soff]; omega
    · have := ixCn_none hn (by omega)
      simp [Index.soff]
      omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
