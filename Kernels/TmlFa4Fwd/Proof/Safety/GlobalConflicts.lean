-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.MemoryOwnership
public import Kernels.TmlFa4Fwd.Proof.OutputProtection
public import Kernels.TmlFa4Fwd.Proof.Thread.MetadataReads
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyBacking
import Lemmas.Tensor.TensorCopy
import Kernels.TmlFa4Fwd.Proof.OutputStoreFacts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX Thread

/-- Pending as well as performed global output effects avoid all launch input regions. -/
theorem outputIntentApartInput {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hFrame : OutputIntentFootprint p X)
    {w : AsyncCopy.Ref} {a : Acc} {loc : Loc} {region : Region} (hw : X.Intent w a true)
    (hr : region ∈ p.inputRegions) (hl : region.Contains loc) : ¬ a.Covers loc := by
  intro hCover
  have hApart := hp.separate.2 region hr
  suffices hOut : p.oRegion.Contains loc ∨ p.lseRegion.Contains loc by
    rcases hOut with ho | hLse
    · rcases hApart.1 with h | h
      · exact (Nat.not_lt_of_ge (h.trans hl.2.2.1)) ho.2.2.2
      · exact (Nat.not_lt_of_ge (h.trans ho.2.2.1)) hl.2.2.2
    · rcases hApart.2 with h | h
      · exact (Nat.not_lt_of_ge (h.trans hl.2.2.1)) hLse.2.2.2
      · exact (Nat.not_lt_of_ge (h.trans hLse.2.2.1)) hl.2.2.2
  rcases hFrame w a loc hw hCover hl.1 with ho | ⟨q, hq, head, hh, k, hk, rfl⟩
  · exact .inl ho
  · exact .inr (lseByte_in hq hh hk)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- Every byte touched by a paged copy source is a backed K or V launch byte. -/
theorem pagedCopyCoveredSource (hFrame : OutputFootprint p X) {i : EvId} {spec : AsyncCopy.Spec}
    {loc : Loc} (hCopy : X.Copy i spec) (hCover : spec.src.Covers loc) :
    (∃ region ∈ p.inputRegions, region.Contains loc) ∧ ∃ byte, m loc = some (some byte) := by
  let k := loc.addr - spec.src.loc.addr
  obtain ⟨hSpace, hCta, hLo, hHi⟩ := hCover
  have hk : k < spec.src.size := by dsimp only [k]; omega
  have hLoc : spec.src.loc.at k = loc := by
    obtain ⟨sp, cta, addr⟩ := loc
    simp only [Loc.at, Loc.mk.injEq, hSpace.symm, hCta.symm, true_and]
    exact Nat.add_sub_of_le (show spec.src.loc.addr ≤ addr from hLo)
  obtain ⟨hr, hBack, _⟩ := Thread.Loader.ordinaryCopyBacked hp hX hFrame hCopy k hk
  rw [hLoc] at hr hBack
  refine ⟨?_, hBack⟩
  rcases hr with hK | hV
  · exact ⟨_, by simp [Params.inputRegions], hK⟩
  · exact ⟨_, by simp [Params.inputRegions], hV⟩

private theorem tensorReadInInput {i : EvId} {address x y k : Nat} {s : TensorCopy.Spec} {loc : Loc}
    (hIssue : X.TensorIssue i address s) (hRead : TensorCopy.readLoc s x y k = some loc) :
    ∃ region ∈ p.inputRegions, region.Contains loc := by
  rw [TensorCopy.readLoc_source] at hRead
  rcases hSlot : TensorTransfer.slotAt s.descriptor x y k with _ | slot
  · simp [hSlot] at hRead
  · simp only [hSlot, Option.bind_some] at hRead
    cases hSource : TensorCopy.source s slot with
    | global address =>
      simp only [hSource, Option.some.injEq] at hRead
      obtain ⟨region, hr, hb, _, _⟩ :=
        (actualTensorInputSource hp hX hIssue).2.2.2 _ _ hSource
      exact ⟨region, hr, hRead ▸ hb⟩
    | fill => simp [hSource] at hRead

/-- Only ordinary metadata reads can overlap a pending or performed global output write. -/
theorem globalReadAgainstOutputCases (hFrame : OutputIntentFootprint p X) {e f : AsyncCopy.Ref}
    {a b : Acc} {loc : Loc} (hRead : X.Intent e a false) (hWrite : X.Intent f b true)
    (ha : a.Covers loc) (hb : b.Covers loc) (hGlobal : loc.space = .global) :
    ∃ i kind bytes, e = .thread i ∧ MetadataRead X i kind a bytes ∧ a.size = 4 := by
  have hSpace := ha.1.symm.trans hGlobal
  cases e with
  | thread i =>
    rcases hRead with ⟨_, hr, _⟩ | ⟨_, _, hBad⟩ | ⟨_, _, hRmw⟩
    · obtain ⟨⟨kind, hMeta⟩, hSize⟩ := globalMetadataRead hX hr hSpace
      exact ⟨i, kind, _, rfl, hMeta, hSize⟩
    · cases hBad
    · exact (noActualRmw hX hRmw).elim
  | async i part =>
    obtain ⟨hMode, hFoot⟩ := hRead
    cases part <;> (try exact False.elim hFoot) <;> try (simp [AsyncCopy.Part.writes] at hMode)
    case mmaRead isB index =>
      have hs := (mmaSharedFootprintIssue hX hFoot.2).1
      rw [hs] at hSpace
      cases hSpace
    case readCopy =>
      rcases hFoot with ⟨s, hi, hSrc⟩ | hPrefetch
      · obtain ⟨region, hRegion, hByte⟩ :=
          (pagedCopyCoveredSource hp hX hFrame.performed hi (hSrc.symm ▸ ha)).1
        exact (outputIntentApartInput hp hFrame hWrite hRegion hByte hb).elim
      · exact (noBulkPrefetch hX hPrefetch).elim
    case readStore =>
      obtain ⟨s, _, hi, hSrc, _⟩ := hFoot
      obtain ⟨slot, _, hLoc⟩ := Option.map_eq_some_iff.mp hSrc
      obtain ⟨_, _, _, hShared⟩ := actualTensorOutputSharedRange hp hX hi slot
      rw [← hLoc, hShared] at hSpace
      cases hSpace
    case oldStore =>
      obtain ⟨s, _, hi, hReduce, _, _⟩ := hFoot
      simp [(actualTensorStoreForm hX hi).2.2] at hReduce
    case readLoad =>
      obtain ⟨s, _, hi, hSrc, hSize⟩ := hFoot
      rw [Acc.loc_of_one ha hSize] at hSrc
      obtain ⟨_, hr, hl⟩ := tensorReadInInput hp hX hi hSrc
      exact (outputIntentApartInput hp hFrame hWrite hr hl hb).elim
    case readPrefetch =>
      obtain ⟨_, _, hi, _, _⟩ := hFoot
      exact (noTensorPrefetch hX hi).elim
    case oldElem =>
      obtain ⟨_, _, hi, hReduce, _⟩ := hFoot
      rw [(actualCopyShape hX hi).whole] at hReduce
      cases hReduce

/-- Global writes with an overlapping byte have identical access footprints. -/
theorem globalWriteFootprintsMatch (hFrame : OutputIntentFootprint p X) {e f : AsyncCopy.Ref}
    {a b : Acc} {loc : Loc} (he : X.Intent e a true) (hf : X.Intent f b true) (ha : a.Covers loc)
    (hb : b.Covers loc) (hGlobal : loc.space = .global) :
    a.SameFootprint b := by
  have hCuQ := (outputIntent_iff_cuQProtected hp hX).mp hFrame
  exact outputWrites_sameFootprint hp hX
    (fun _ _ _ hWrite hSpace => lseWriteShape hp hX hWrite hSpace)
    (fun _ _ _ hIssue => OutputWarp.issuedBox hp hX hIssue)
    he hf (ha.1.symm.trans hGlobal) ⟨loc, ha, hb⟩

end PTX.Kernels.TmlFa4Fwd.Safety
