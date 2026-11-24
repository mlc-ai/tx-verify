-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Safety.Memory

@[expose] public section

/-!
# The mbarrier branch of `Unsafe`

`TmaUnsafe` has five disjuncts. Two are decided by the program text: the kernel has no `cp.async`
and no masked bulk copy (`no_copy`), so no `cp.async` group overlaps (`CpAsyncOverlap`) and no
masked range is unallocated (`MaskedRangeUnalloc`). One is decided by the memory regions: no
generic access touches the bytes of an mbarrier (a touched shared byte is in `InRegions`, which
stops short of the barrier objects at `[213216, 213336)`). The two that remain are the object
histories: no record faults, and every record lies in an initialized lifetime published to its
issue (`ObjectPublished`). They are facts of the barrier protocols (counts, phases, the
initialization before use) and enter as fields of `Protocol` (`recordsOk`, `objectsPublished`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The barrier objects lie above `[0, 213216)` and below the role table. -/
theorem bar_off_bounds (b : EvD.Bar) : 213216 ≤ b.off ∧ b.off + 8 ≤ 213336 := by
  cases b with
  | kvReady s => have := s.isLt; simp only [EvD.Bar.off]; omega
  | kvEmpty s => have := s.isLt; simp only [EvD.Bar.off]; omega
  | sReady s => have := s.isLt; simp only [EvD.Bar.off]; omega
  | pReady s => have := s.isLt; simp only [EvD.Bar.off]; omega
  | oDone => simp only [EvD.Bar.off]; omega
  | oFinal => simp only [EvD.Bar.off]; omega

/-- **No generic access touches an mbarrier's bytes**: a touched shared byte is in a region, and
no region contains a barrier object. -/
theorem no_access_to_mbar (hsh : SharedPlaced L X) (hmb : MbarPlaced L X) {e : AsyncCopy.Ref}
    {a : Acc} (ha : X.MemTouches e a) {i : EvId} {m : Loc} {c : Nat} (hi : X.MbInit i m c)
    {l : Loc} (hl : a.Covers l) (hm : Acc.Covers { loc := m, size := 8 } l) : False := by
  obtain ⟨b, cta, hcta, rfl⟩ := hmb i m (Execution.UsesMbar.of_init hi)
  obtain ⟨hs, -, hlo, hhi⟩ := hm
  have hsp : l.space = .shared := hs
  obtain ⟨-, hr⟩ := hsh e a l ha hl hsp
  have hb := bar_off_bounds b
  simp only [EvD.Bar.loc] at hlo hhi
  unfold InRegions InBase InKv InQ InCount InScratch InRole at hr
  omega

/-- **No linear copy is a `cp.async`, and none is masked**: the kernel has no linear copy. -/
theorem no_cpAsyncOverlap (hX : Consistent L kernel asms mem0 X) : ¬ CpAsyncOverlap X :=
  not_cpAsyncOverlap_of_none fun _ _ ⟨_, hc⟩ _ => no_copy hX hc

theorem no_maskedRangeUnalloc (hX : Consistent L kernel asms mem0 X) :
    ¬ MaskedRangeUnalloc mem0 X :=
  not_maskedRangeUnalloc_of_none fun _ _ _ ⟨_, hc⟩ _ => no_copy hX hc

/-- **The mbarrier branch.** -/
theorem no_tmaUnsafe (hX : Consistent L kernel asms mem0 X) (hsh : SharedPlaced L X)
    (hmb : MbarPlaced L X) (hrec : ¬ ∃ m r, r ∈ X.objects m ∧ r.fault.isSome)
    (hpub : ∀ m r, r ∈ X.objects m → ObjectPublished L X m r) : ¬ TmaUnsafe L mem0 X := by
  rintro (h | ⟨m, r, hr, hn⟩ | ⟨e, a, w, i, m, c, l, hint, hi, hl, hm, -⟩ | h | h)
  · exact hrec h
  · exact hn (hpub m r hr)
  · exact no_access_to_mbar hsh hmb (.inl ⟨w, hint⟩) hi hl hm
  · exact no_cpAsyncOverlap hX h
  · exact no_maskedRangeUnalloc hX h

end
end PTX.Kernels.InklingRelDecode.Proof.Safety
