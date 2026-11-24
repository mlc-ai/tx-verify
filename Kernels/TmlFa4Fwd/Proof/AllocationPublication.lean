-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.AllocationBarrierGeneration

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue

/-- The actual allocator lane-zero store publishes its shared address to each warp-12 allocation
read through the initial generation of barrier 2. This holds on any finite consistent prefix. -/
theorem allocationStorePublished {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {acc : Acc} {bytes : List (Option Byte)}
    (hr : X.get (g,j) = some ⟨1911, .rd acc bytes⟩) :
    ∃ owner pos col, col < 2^16 ∧ SameWarp l owner g ∧ laneOf l owner = 0 ∧
      X.get (owner,pos) =
        some ⟨1909, .wr {loc := allocationSlot l g, size := 4} (b32 col).toBytes⟩ ∧
      CtaBarSync l X (owner,pos) (g,j) := by
  have hBody := roleBodyPcOfEvent hp hX (g := g) hr
    (show 173 < 1911 by decide) (show 1911 ∉ registerHintSites by decide)
  change roleBodyPc (warpIndex l g) 1911 at hBody
  have hw : warpIndex l g = 12 := by
    rcases hBody with h | h
    · exact (by decide : ¬1911 = 9205) h |>.elim
    · change (if 14 ≤ warpIndex l g then _ else if warpIndex l g = 13 then _ else
        if warpIndex l g = 12 then _ else if warpIndex l g < 8 then _ else _) at h
      split_ifs at h <;> omega
  have hg := Step.CtaBar.thread_lt_of_get hX hr
  obtain ⟨_, wait, hLe, hWait, _, _⟩ :=
    allocationPrefixAtBarrierReadOrExit hp hX hg hw hr (.inr (.inr rfl))
  have hLt : wait < j := by
    rcases Nat.eq_or_lt_of_le hLe with rfl | h
    · rw [hWait] at hr
      exact Kind.noConfusion (congrArg Event.kind (Option.some.inj hr))
    · exact h
  obtain ⟨hDone, user, hUser, hUserKey⟩ :=
    allocationGenerationZeroBefore hp hX (g := g) hg (by omega) hLt hr hWait
  let owner := warpLane l g 0
  have hOwner := Step.sameWarp_lane (L := l) (g := g) (lane := 0)
    (by rw [hp.block]) hg (by decide)
  change SameWarp l g owner ∧ laneOf l owner = 0 at hOwner
  have hWarp : SameWarp l owner g := sameWarp_symm hOwner.1
  have hTid : owner < l.threads := hWarp.1.1
  have hCta : owner/l.block = g/l.block := hWarp.1.2.2
  have hRole : warpIndex l owner = 12 := hWarp.2.trans hw
  obtain ⟨mark, site, hSite, hMark, hMarkKey⟩ :=
    allocationGenerationZeroMember hp hX hTid (by omega) (by simpa only [hCta] using hDone)
  have hSitePc : site = 1910 := by
    have hR := allocationEntryRole hp hX hSite hMark
    omega
  subst site
  obtain ⟨n, k, hK, hBar, _, hStore⟩ :=
    allocationPrefixAtBarrierReadOrExit hp hX hTid hRole hMark (.inr (.inl rfl))
  have hEq : k = mark := by
    rcases Nat.eq_or_lt_of_le hK with h | h
    · exact h
    · exact (CtaBarrier.not_generationZero_after_sync hX (by decide) h hBar hMarkKey.2.2).elim
  subst mark
  obtain ⟨col, hCol, hBefore, hGet⟩ := hStore hOwner.2
  have hSameSlot : allocationSlot l owner = allocationSlot l g := by
    simp only [allocationSlot, hCta]
  rw [hSameSlot] at hGet
  exact ⟨owner, n+1, col, hCol, hWarp, hOwner.2, hGet,
    hWarp.1, 2, k, user, hMarkKey.arrival, hUserKey, hBefore, hUser,
    (List.getElem?_eq_some_iff.mp hr).1⟩

end PTX.Kernels.TmlFa4Fwd.Mma
