-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.NcAllocationTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GlobalFrame
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.OrdinaryReadWindow
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RawSharedWrites
import Lemmas.Protocol.NamedBarSources

public section

/-! # Allocated bytes of ordinary thread memory accesses -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow Wg0 Result

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {i : EvId} {a : Acc} {l : Loc}

private theorem byte_in_input {base width : Nat}
    (hInput : FitsInput a base width) (hCta : a.loc.cta = 0) (hCover : a.Covers l) :
    ∃ j < width, l = ⟨.global, 0, base + j⟩ := by
  obtain ⟨hs, hlo, hhi⟩ := hInput
  obtain ⟨hl, hc, hfirst, hlast⟩ := hCover
  have hAddr : l.addr = base + (l.addr - base) := by omega
  refine ⟨l.addr - base, by omega, ?_⟩
  cases l
  rw [Loc.mk.injEq]
  exact ⟨hl.trans hs, hc.trans hCta, hAddr⟩

private theorem linear_word {off width : Nat} (h : off < 4 * width) :
    ∃ row < width, ∃ k < 4, off = 4 * row + k :=
  ⟨off / 4, by omega, off % 4, by omega, by omega⟩

private theorem index_word {off width : Nat} (h : off < 4 * P.b * P.s_q * width) :
    ∃ e < P.b, ∃ q < P.s_q, ∃ j < width, ∃ k < 4,
      off = 4 * ((e * P.s_q + q) * width + j) + k := by
  have hSpan : 4 * P.b * P.s_q * width = 4 * ((P.b * P.s_q) * width) := by ring
  obtain ⟨row, hRow, k, hk, hOff⟩ := linear_word (hSpan ▸ h)
  have hw : 0 < width := by
    by_contra h
    simp [show width = 0 by omega] at hRow
  have hsq : 0 < P.s_q := by
    by_contra h
    simp [show P.s_q = 0 by omega] at hRow
  let eq := row / width
  have heq : eq < P.b * P.s_q := (Nat.div_lt_iff_lt_mul hw).mpr hRow
  have he := (Nat.div_lt_iff_lt_mul hsq).mpr heq
  have h1 := Nat.div_add_mod row width
  have h2 := Nat.div_add_mod eq P.s_q
  refine ⟨eq / P.s_q, he, eq % P.s_q, Nat.mod_lt _ hsq, row % width, Nat.mod_lt _ hw, k, hk, ?_⟩
  rw [hOff]
  congr 1
  congr 1
  rw [Nat.mul_comm (eq / P.s_q) P.s_q, h2, Nat.mul_comm eq width]
  exact h1.symm

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
include hpre hX hs

/-- Every byte of a non-coherent input read is covered by its launch input array. -/
theorem ordinary_nc_allocated (ht : Frame.Tracked (Machine.code P L) X) {bs : List (Option Byte)}
    (hr : X.NcReads i a bs) (hc : a.Covers l) : mem0 l ≠ none := by
  obtain ⟨hi, hc0⟩ := NcInputTrace.allocation_footprint hpre hX hs ht hr
  have word {base width : Nat} (hInput : FitsInput a base (4 * width)) :
      ∃ row < width, ∃ k < 4, l = ⟨.global, 0, base + 4 * row + k⟩ := by
    obtain ⟨off, ho, hLoc⟩ := byte_in_input hInput hc0 hc
    obtain ⟨row, hRow, k, hk, rfl⟩ := linear_word ho
    exact ⟨row, hRow, k, hk, by simpa only [Nat.add_assoc] using hLoc⟩
  have index {base width : Nat} (hInput : FitsInput a base (4 * P.b * P.s_q * width)) :
      ∃ e < P.b, ∃ q < P.s_q, ∃ j < width, ∃ k < 4,
        l = ⟨.global, 0, base + 4 * ((e * P.s_q + q) * width + j) + k⟩ := by
    obtain ⟨off, ho, hLoc⟩ := byte_in_input hInput hc0 hc
    obtain ⟨e, he, q, hq, j, hj, k, hk, rfl⟩ := index_word ho
    exact ⟨e, he, q, hq, j, hj, k, hk, by simpa only [Nat.add_assoc] using hLoc⟩
  cases hi with
  | mainLength hPtr hInput =>
    obtain ⟨row, hRow, k, hk, rfl⟩ := word hInput
    have h := hpre.paramTopkLen
    rw [hPtr] at h
    rw [(h.2.2 row hRow k hk).1]
    simp
  | extraLength hPtr hInput =>
    obtain ⟨row, hRow, k, hk, rfl⟩ := word hInput
    have h := hpre.paramExtraTopkLen
    rw [hPtr] at h
    rw [(h.2.2 row hRow k hk).1]
    simp
  | sink hPtr hInput =>
    obtain ⟨row, hRow, k, hk, rfl⟩ := word hInput
    have h := hpre.paramSink
    rw [hPtr] at h
    obtain ⟨_, _, _, _, hMem, _⟩ := h.2.2 row hRow
    rw [hMem k hk]
    simp
  | mainIndices hInput =>
    obtain ⟨e, he, q, hq, j, hj, k, hk, rfl⟩ := index hInput
    rw [hpre.idxInput e he q hq j hj k hk]
    simp
  | extraIndices hPos hInput =>
    obtain ⟨e, he, q, hq, j, hj, k, hk, rfl⟩ := index hInput
    have h := hpre.extraIdxInput.resolve_left (by omega)
    rw [h.2 e he q hq j hj k hk]
    simp

omit hpre hX hs in
private theorem allocated_shared_byte (hpre : Pre P L mem0) {g : Nat}
    (hg : g < L.threads) (hSpace : l.space = .shared) (hOwner : l.cta = ctaOf L g)
    (hLo : L.sharedBase ≤ l.addr) (hHi : l.addr < L.sharedBase + sharedBytes) :
    mem0 l ≠ none := by
  let off := l.addr - L.sharedBase
  have hOff : off < sharedBytes := by dsimp [off]; omega
  have hAddr : l.addr = L.sharedBase + off := by dsimp [off]; omega
  have hLoc : l = ⟨.shared, ctaOf L g, P.sharedBase + off⟩ := by
    rw [← hpre.sharedBase]
    cases l
    rw [Loc.mk.injEq]
    exact ⟨hSpace, hOwner, hAddr⟩
  rw [hLoc]
  exact hpre.sharedAllocated _ (NamedBar.cta_lt hg) _ hOff

/-- Every byte of an ordinary read is allocated in the issuing CTA's shared window. -/
theorem ordinary_read_allocated (ht : Frame.Tracked (Machine.code P L) X) {bs : List (Option Byte)}
    (hr : X.Reads i a bs) (hc : a.Covers l) : mem0 l ≠ none := by
  obtain ⟨hSpace, hOwner, hLo, hHi⟩ := OrdinaryReadWindow.read_window hpre hX hs ht hr
  obtain ⟨hsp, hc, hlo, hhi⟩ := hc
  exact allocated_shared_byte hpre (Frame.lt_of_get hX hr.choose_spec) (hsp.trans hSpace)
    (hc.trans hOwner) (by omega) (by omega)

/-- Every byte of an ordinary global write lies in the LSE allocation. -/
theorem ordinary_global_write_allocated (ht : Frame.Tracked (Machine.code P L) X) {bs : List Byte}
    (hw : X.Writes i a bs) (hc : a.Covers l) (hg : l.space = .global) :
    mem0 l ≠ none := by
  have hSpace := hc.1.symm.trans hg
  obtain ⟨_, _, _, hLoc, hSize, _⟩ := GlobalWrites.lse_write hpre hs hX ht hw hSpace
  change a.loc.InRange a.size l at hc
  rw [hLoc, hSize, lseLocOf_eq] at hc
  have hG := Frame.lt_of_get hX hw.choose_spec
  obtain ⟨hLo, hHi⟩ := lseRange (Wg1Mma.eOf_lt_b hpre) (Wg1Mma.queryOf_lt hpre hG)
    (head_lt L i.1) hc
  let off := l.addr - P.lseBase
  have hOff : off < lseBytes P := by dsimp [off]; omega
  have hAddr : l.addr = P.lseBase + off := by dsimp [off]; omega
  have hL : l = ⟨.global, 0, P.lseBase + off⟩ := by
    have hCta : l.cta = 0 := hc.2.1
    cases l
    rw [Loc.mk.injEq]
    exact ⟨hg, hCta, hAddr⟩
  rw [hL]
  exact hpre.lseAllocated _ hOff

/-- Every byte of an ordinary store is allocated in the CTA window or the LSE tensor. -/
theorem ordinary_write_allocated (ht : Frame.Tracked (Machine.code P L) X) {bs : List Byte}
    (hw : X.Writes i a bs) (hc : a.Covers l) : mem0 l ≠ none := by
  rcases RawSharedWrites.ordinary_window hpre hX hs ht hw hc with hg | ⟨hSpace, hLo, hHi⟩
  · exact ordinary_global_write_allocated hpre hX hs ht hw hc hg
  · have hOwner := RoleSharedWrites.shared_cta hpre hs hX ht hw (hc.1.symm.trans hSpace)
    exact allocated_shared_byte hpre (Frame.lt_of_get hX hw.choose_spec) hSpace
      (hc.2.1.trans hOwner) hLo hHi

/-- Every byte touched by a synchronous thread event is allocated, including non-coherent loads. -/
theorem ordinary_access_allocated (ht : Frame.Tracked (Machine.code P L) X)
    (hm : X.MemTouches (.thread i) a) (hc : a.Covers l) : mem0 l ≠ none := by
  rcases hm with ⟨w, hw⟩ | ⟨j, _, hij, hr⟩
  · rcases hw with ⟨_, hr, _⟩ | ⟨_, hw, _⟩ | ⟨_, _, hr⟩
    · exact ordinary_read_allocated hpre hX hs ht hr hc
    · exact ordinary_write_allocated hpre hX hs ht hw hc
    · exact (GlobalWrites.no_rmw hX hr).elim
  · obtain rfl := AsyncCopy.Ref.thread.inj hij
    exact ordinary_nc_allocated hpre hX hs ht hr hc

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
