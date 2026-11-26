-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.NcApart

@[expose] public section

/-! # The bytes of a launch-word read are allocated inputs

A `.nc` read of four bytes at row `row` of a length array (or at head `h` of the sink) covers
bytes `Pre` allocates (`paramTopkLen`, `paramExtraTopkLen`, `paramSink`) and places apart from the
two outputs (`topkLenApartO`, `topkLenApartLse` and their extra and sink kin). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

variable {P : Params} {L : Launch} {m : Mem0}

/-- A byte of a four-byte global access at `addr` is `addr + k` for a `k < 4`. -/
theorem word_cover {a : Acc} {addr : Nat} {l : Loc} (hl : a.loc = ⟨.global, 0, addr⟩)
    (hs : a.size = 4) (hc : a.Covers l) : ∃ k < 4, l = ⟨.global, 0, addr + k⟩ := by
  obtain ⟨hsp, hcc, hlo, hhi⟩ := hc
  rw [hl] at hsp hcc hlo
  rw [hs] at hhi
  obtain ⟨sp, c, ad⟩ := l
  simp only at hsp hcc hlo hhi
  subst hsp hcc
  rw [hl] at hhi
  have hlo' : addr ≤ ad := hlo
  have hhi' : ad < addr + 4 := hhi
  exact ⟨ad - addr, by omega, by rw [show addr + (ad - addr) = ad by omega]⟩

/-- **A top-k length read's bytes are allocated.** -/
theorem len_alloc_topk (hp : Pre P L m) {x row : Nat} (hrow : row < P.b)
    (hx : P.topkLenBase = some x) {e : Event} {a : Acc} {bs : List (Option Byte)}
    (hk : e.kind = .nc a bs) (hr : ReadsLaunchWord e (x + 4 * row) bs) (l : Loc)
    (hc : a.Covers l) : NcRead P m l := by
  have hm := hp.paramTopkLen
  rw [hx] at hm
  obtain ⟨-, -, hmem⟩ := hm
  obtain ⟨hrd, -⟩ := hr
  rw [hk] at hrd
  have ha := (Kind.nc.inj hrd).1
  obtain ⟨k, hk4, rfl⟩ := word_cover (congrArg Acc.loc ha) (congrArg Acc.size ha) hc
  obtain ⟨h, -⟩ := hmem row hrow k hk4
  refine ⟨by rw [h]; simp, rfl, ?_⟩
  exact ncApart_of (hp.topkLenApartO x hx) (hp.topkLenApartLse x hx) (by omega) (by omega)

/-- **An extra top-k length read's bytes are allocated.** -/
theorem len_alloc_extra (hp : Pre P L m) {x row : Nat} (hrow : row < P.b)
    (hx : P.extraTopkLenBase = some x) {e : Event} {a : Acc} {bs : List (Option Byte)}
    (hk : e.kind = .nc a bs) (hr : ReadsLaunchWord e (x + 4 * row) bs) (l : Loc)
    (hc : a.Covers l) : NcRead P m l := by
  have hm := hp.paramExtraTopkLen
  rw [hx] at hm
  obtain ⟨-, -, hmem⟩ := hm
  obtain ⟨hrd, -⟩ := hr
  rw [hk] at hrd
  have ha := (Kind.nc.inj hrd).1
  obtain ⟨k, hk4, rfl⟩ := word_cover (congrArg Acc.loc ha) (congrArg Acc.size ha) hc
  obtain ⟨h, -⟩ := hmem row hrow k hk4
  refine ⟨by rw [h]; simp, rfl, ?_⟩
  exact ncApart_of (hp.extraTopkLenApartO x hx) (hp.extraTopkLenApartLse x hx) (by omega) (by omega)

/-- **A sink read's bytes are allocated.** -/
theorem sink_alloc (hp : Pre P L m) {x h : Nat} (hh : h < 64) (hx : P.sinkBase = some x)
    {e : Event} {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .nc a bs)
    (hr : ReadsLaunchWord e (x + 4 * h) bs) (l : Loc) (hc : a.Covers l) : NcRead P m l := by
  have hm := hp.paramSink
  rw [hx] at hm
  obtain ⟨-, -, hmem⟩ := hm
  obtain ⟨hrd, -⟩ := hr
  rw [hk] at hrd
  have ha := (Kind.nc.inj hrd).1
  obtain ⟨k, hk4, rfl⟩ := word_cover (congrArg Acc.loc ha) (congrArg Acc.size ha) hc
  obtain ⟨s, bits, -, -, hb, -⟩ := hmem h hh
  refine ⟨by rw [hb k hk4]; simp, rfl, ?_⟩
  exact ncApart_of (hp.sinkApartO x hx) (hp.sinkApartLse x hx) (by omega) (by omega)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
