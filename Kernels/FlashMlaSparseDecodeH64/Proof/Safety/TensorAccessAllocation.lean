-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorLoadSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorSharedBounds
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GlobalFrame
import Lemmas.Protocol.NamedBarSources
import Lemmas.Tensor.TensorCopy

public section

/-! # The byte allocations of pending and performed tensor transfers -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow Wg0 Result

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {i : EvId} {a : Acc} {l : Loc} {x y k : Nat}

private theorem tensor_footprint {p : AsyncCopy.Part}
    (hm : X.MemTouches (.async i p) a) : X.AsyncFootprint i p a := by
  rcases hm with ⟨_, _, h⟩ | ⟨_, _, h, _⟩
  · exact h
  · cases h

private theorem covered_byte (hs : a.size = 1) (hc : a.Covers l) : l = a.loc := by
  obtain ⟨hSpace, hCta, hLo, hHi⟩ := hc
  have hAddr : l.addr = a.loc.addr := by omega
  cases l
  cases hA : a.loc
  simp_all

private theorem shared_allocated (hpre : Pre P L mem0) {g : Nat}
    (hg : g < L.threads) (hSpace : l.space = .shared) (hCta : l.cta = ctaOf L g)
    (hLo : L.sharedBase ≤ l.addr) (hHi : l.addr < L.sharedBase + sharedBytes) :
    mem0 l ≠ none := by
  let off := l.addr - L.sharedBase
  have ho : off < sharedBytes := by dsimp [off]; omega
  have hAddr : l.addr = L.sharedBase + off := by dsimp [off]; omega
  have he : l = ⟨.shared, ctaOf L g, P.sharedBase + off⟩ := by
    rw [← hpre.sharedBase]
    cases l
    rw [Loc.mk.injEq]
    exact ⟨hSpace, hCta, hAddr⟩
  rw [he]
  exact hpre.sharedAllocated _ (NamedBar.cta_lt hg) _ ho

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hX hs ht

/-- A tensor load reserves only allocated bytes of its shared destination window. -/
theorem tensor_load_write_allocated (hm : X.MemTouches (.async i (.write (.load x y k))) a)
    (hc : a.Covers l) :
    mem0 l ≠ none := by
  obtain ⟨_, _, hIssue, hLoc, hSize⟩ := tensor_footprint hm
  obtain rfl := covered_byte hSize hc
  obtain ⟨hSpace, hCta, hWindow⟩ := TensorSharedBounds.write_loc_windows hpre hX hs ht hIssue hLoc
  apply shared_allocated hpre (Frame.lt_of_get hX hIssue.choose_spec) hSpace hCta
  all_goals
    rcases hWindow with ⟨h, _⟩ | ⟨h, _⟩
    · dsimp only [TensorSharedBounds.QueryWindow, sharedBytes] at h ⊢
      omega
    · dsimp only [TensorSharedBounds.RawWindow, sharedBytes] at h ⊢
      omega

private theorem output_spec {addr : Nat} {s : TensorStore.Spec} (hi : X.TensorStoreIssue i addr s) :
    ∃ j : Fin 4, s = outputSpec P L i.1 j ∧ warpOf L i.1 < 2 ∧ i.1 < L.threads := by
  obtain ⟨tag, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, j, hd, hSite⟩ := GlobalWrites.outputTile_site hs hX ht ⟨tag, he⟩
  have hw := Wg0OutputControl.outputWarp hX (hs _ hg).machine he hd hSite
  exact ⟨j, (Wg0OutputTrace.tileSpec hpre hX (hs _ hg).machine
    ⟨tag, he⟩ hd hSite).2, hw, hg⟩

/-- A tensor store reserves only allocated bytes of its CTA's shared output staging window. -/
theorem tensor_store_read_allocated (hm : X.MemTouches (.async i (.read (.store x y k))) a)
    (hc : a.Covers l) :
    mem0 l ≠ none := by
  obtain ⟨s, addr, hi, hl, hSize⟩ := tensor_footprint hm
  obtain rfl := covered_byte hSize hc
  obtain ⟨j, rfl, hw, hg⟩ := output_spec hpre hX hs ht hi
  unfold TensorStore.readLoc at hl
  cases hSlot : TensorTransfer.slotAt (outputSpec P L i.1 j).descriptor x y k with
  | none => simp [hSlot] at hl
  | some slot =>
    obtain ⟨out, rfl⟩ := (tensorOutputSlot_bijective P L i.1 j).2 slot
    rw [hSlot, Option.map_some] at hl
    change some ((outputSpec P L i.1 j).toTensorBox.sharedLoc
      (tensorOutputSlot P L i.1 j out)) = some a.loc at hl
    rw [outputSlot_shared hpre j out hw] at hl
    rw [← Option.some.inj hl]
    apply shared_allocated hpre hg rfl rfl
    · change L.sharedBase ≤ L.sharedBase + _
      omega
    · have hb := out.2.2.isLt
      have hBound := stageOff_lt out.2.1.isLt (outputColumn_lt j hw out.1.isLt)
      simp only [stageBase, stageBytes] at hBound
      simp only [shLoc, sharedBytes]
      omega

private theorem store_destination_allocated {addr : Nat} {s : TensorStore.Spec}
    (hi : X.TensorStoreIssue i addr s) (hl : TensorStore.writeLoc s x y k = some l)
    : mem0 l ≠ none := by
  obtain ⟨j, rfl, hw, hg⟩ := output_spec hpre hX hs ht hi
  unfold TensorStore.writeLoc at hl
  cases hSlot : TensorTransfer.slotAt (outputSpec P L i.1 j).descriptor x y k with
  | none => simp [hSlot] at hl
  | some slot =>
    obtain ⟨out, rfl⟩ := (tensorOutputSlot_bijective P L i.1 j).2 slot
    have he := Wg1Mma.eOf_lt_b hpre (g := i.1)
    have hq := Wg1Mma.queryOf_lt hpre hg
    rw [hSlot, Option.bind_some, outputSlot_destination P L i.1 j out hw hq he] at hl
    obtain rfl := (Option.some.inj hl).symm
    let o := (oLoc P (eOf L i.1) (qOf L i.1) out.2.1.val
      (tmaX j.val (warpOf L i.1) + out.1.val)).at out.2.2.val
    have hc : o.InRange 1 o := ⟨rfl, rfl, Nat.le_refl _, Nat.lt_succ_self _⟩
    obtain ⟨hLo, hHi⟩ := outputRange he hq out.2.1.isLt
      (outputColumn_lt j hw out.1.isLt) out.2.2.isLt hc
    let n := o.addr
    have hn : n = P.outBase + (n - P.outBase) := by change P.outBase ≤ n at hLo; omega
    have hFit : n - P.outBase < tensorBytes P := by change n < _ at hHi; omega
    change mem0 ⟨.global, 0, n⟩ ≠ none
    exact hn.symm ▸ hpre.oAllocated _ hFit

/-- A tensor store reserves only allocated destination bytes of the output tensor. -/
theorem tensor_store_write_allocated (hm : X.MemTouches (.async i (.write (.store x y k))) a)
    (hc : a.Covers l) :
    mem0 l ≠ none := by
  obtain ⟨_, _, hi, hl, hSize⟩ := tensor_footprint hm
  obtain rfl := covered_byte hSize hc
  exact store_destination_allocated hpre hX hs ht hi hl

/-- The destination footprint of any old-value read has the output allocation. -/
theorem tensor_store_old_allocated (hm : X.MemTouches (.async i (.old (.store x y k))) a)
    (hc : a.Covers l) :
    mem0 l ≠ none := by
  obtain ⟨_, _, hi, _, hl, hSize⟩ := tensor_footprint hm
  obtain rfl := covered_byte hSize hc
  exact store_destination_allocated hpre hX hs ht hi hl
end

private theorem query_source_allocated (hpre : Pre P L mem0) {g : Nat}
    (hg : g < L.threads) (tile : Fin 8)
    (hl : TensorCopy.readLoc (MmaDataTrace.queryTmaSpec P L g tile) x y k = some l) :
    mem0 l ≠ none := by
  rw [TensorCopy.readLoc_source] at hl
  cases hSlot : TensorTransfer.slotAt (MmaDataTrace.queryTmaSpec P L g tile).descriptor x y k with
  | none => simp [hSlot] at hl
  | some slot =>
    obtain ⟨hCol, hRow, hByte⟩ := queryTile_shape P L g tile
    let col : Fin 64 := ⟨slot.1.val, hCol ▸ slot.1.isLt⟩
    let row : Fin 64 := ⟨slot.2.1.val, hRow ▸ slot.2.1.isLt⟩
    let byte : Fin 2 := ⟨slot.2.2.val, hByte ▸ slot.2.2.isLt⟩
    have he : queryTileSlot P L g tile col row byte = slot := by
      rcases slot with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩
      rfl
    obtain ⟨addr, hSrc, hMem⟩ := queryTile_initial hpre hg tile col row byte
    rw [hSlot, Option.bind_some, ← he, hSrc] at hl
    rw [← Option.some.inj hl, hMem]
    simp

private theorem query_source_range (hpre : Pre P L mem0) {g : Nat}
    (hg : g < L.threads) (tile : Fin 8)
    (hl : TensorCopy.readLoc (MmaDataTrace.queryTmaSpec P L g tile) x y k = some l) :
    P.qBase ≤ l.addr ∧ l.addr < P.qBase + tensorBytes P := by
  rw [TensorCopy.readLoc_source] at hl
  cases hSlot : TensorTransfer.slotAt (MmaDataTrace.queryTmaSpec P L g tile).descriptor x y k with
  | none => simp [hSlot] at hl
  | some slot =>
    obtain ⟨hCol, hRow, hByte⟩ := queryTile_shape P L g tile
    let col : Fin 64 := ⟨slot.1.val, hCol ▸ slot.1.isLt⟩
    let row : Fin 64 := ⟨slot.2.1.val, hRow ▸ slot.2.1.isLt⟩
    let byte : Fin 2 := ⟨slot.2.2.val, hByte ▸ slot.2.2.isLt⟩
    have hEq : queryTileSlot P L g tile col row byte = slot := by
      rcases slot with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩
      rfl
    let batch := Wg1Mma.batchOf L g
    let query := Wg1Mma.queryOf L g
    let feature := Wg1Mma.qCoord tile + col.val
    let offset := 2 * (((batch * P.s_q + query) * 64 + row.val) * 512 + feature) + byte.val
    have hs : TensorCopy.source (MmaDataTrace.queryTmaSpec P L g tile)
        (queryTileSlot P L g tile col row byte) = .global (P.qBase + offset) := by
      rw [TensorCopy.source, queryTile_global hpre hg tile col row byte]
      simp only [TensorTransfer.Source.global.injEq, offset, feature, batch, query]
      omega
    rw [hSlot, Option.bind_some, ← hEq, hs] at hl
    have hLoc : l.addr = P.qBase + offset := by cases hl; rfl
    have hb : batch < P.b := Wg1Mma.eOf_lt_b hpre
    have hq : query < P.s_q := Wg1Mma.queryOf_lt hpre hg
    have hRowBound := Nat.mul_le_mul_right P.s_q (Nat.succ_le_of_lt hb)
    rw [Nat.succ_mul] at hRowBound
    have hQuery : batch * P.s_q + query < P.b * P.s_q := by omega
    have hh := row.isLt
    have hFeature : feature < 512 := by unfold feature Wg1Mma.qCoord; omega
    have hbty := byte.isLt
    have hn : tensorBytes P = 65536 * (P.b * P.s_q) := by unfold tensorBytes; ring
    rw [hLoc, hn]
    dsimp only [offset]
    omega

section
variable {base blocks stride : Nat} {cls : TensorDescriptor.AllocationClass} {s : TensorCopy.Spec}
    (hDesc : (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
      ⟨1, (encodeKv base blocks stride cls).fourRows⟩)
include hDesc

private theorem gather_source_index (hl : TensorCopy.readLoc s x y k = some l) :
    ∃ row < blocks * (stride / 528), ∃ byte < 528,
      l = ⟨.global, 0, base + row * 528 + byte⟩ := by
  rcases s with ⟨⟨outer, descriptor, origin, dst, rows⟩, _, _, _⟩
  obtain ⟨ho, hd⟩ := Sigma.mk.inj hDesc
  dsimp only at ho hd
  subst outer
  have he := eq_of_heq hd
  subst descriptor
  change TensorTransfer.sourceLoc (encodeKv base blocks stride cls).fourRows origin rows x y k =
    some l at hl
  unfold TensorTransfer.sourceLoc at hl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hl
  obtain ⟨slot, _, addr, hAddr, rfl⟩ := hl
  rw [TensorTransfer.globalAddress, TensorAddress.lookup] at hAddr
  split at hAddr
  · rename_i hb
    obtain rfl := (Option.some.inj hAddr).symm
    let coord := TensorTransfer.coord (encodeKv base blocks stride cls).fourRows origin rows slot
    have hx := (hb.1 (0 : Fin 2)).2
    have hr := (hb.1 (1 : Fin 2)).2
    have hByte := hb.2
    change coord 0 < 132 at hx
    change coord 1 < (↑(blocks * (stride / 528)) : Int) at hr
    change slot.2.2.val < 4 at hByte
    have hCol : (coord 0).toNat < 132 := by omega
    have hNonneg : 0 ≤ coord 1 := (hb.1 (1 : Fin 2)).1
    have hRow : (coord 1).toNat < blocks * (stride / 528) := by omega
    have hOff : 4 * (coord 0).toNat + slot.2.2.val < 528 := by omega
    have hEq :
        TensorAddress.byteAddress (TensorDescriptor.geometry
          (encodeKv base blocks stride cls).fourRows) coord slot.2.2.val =
          base + (coord 1).toNat * 528 + (4 * (coord 0).toNat + slot.2.2.val) := by
      simp [TensorAddress.byteAddress, TensorDescriptor.geometry, encodeKv,
        TensorDescriptor.Descriptor.fourRows, Fin.sum_univ_succ, Fin.cases,
        TensorDescriptor.Format.bytes]
      omega
    rw [hEq]
    exact ⟨_, hRow, _, hOff, rfl⟩
  · cases hAddr

private theorem gather_source_allocated
    (hBack : ∀ row < blocks * (stride / 528), ∀ byte < 528,
      mem0 ⟨.global, 0, base + row * 528 + byte⟩ ≠ none) (hl : TensorCopy.readLoc s x y k = some l)
    : mem0 l ≠ none := by
  obtain ⟨row, hRow, byte, hByte, rfl⟩ := gather_source_index hDesc hl
  exact hBack row hRow byte hByte

private theorem gather_source_range (hl : TensorCopy.readLoc s x y k = some l) :
    base ≤ l.addr ∧ l.addr < base + cacheBytes blocks stride := by
  obtain ⟨row, hRow, byte, hByte, rfl⟩ := gather_source_index hDesc hl
  have hs : stride / 528 * 528 ≤ stride := Nat.div_mul_le_self _ _
  have hr : (row + 1) * 528 ≤ blocks * stride := calc
    (row + 1) * 528 ≤ (blocks * (stride / 528)) * 528 :=
      Nat.mul_le_mul_right _ hRow
    _ = blocks * (stride / 528 * 528) := Nat.mul_assoc ..
    _ ≤ blocks * stride := Nat.mul_le_mul_left blocks hs
  change base ≤ base + row * 528 + byte ∧ base + row * 528 + byte < base + blocks * stride
  omega
end

/-- Every actual global source of a query or KV tensor load is allocated at launch. -/
theorem tensor_load_read_allocated (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hm : X.MemTouches (.async i (.read (.load x y k))) a) (hc : a.Covers l) :
    mem0 l ≠ none := by
  obtain ⟨_, _, hi, hl, hSize⟩ := tensor_footprint hm
  obtain rfl := covered_byte hSize hc
  have hg := Frame.lt_of_get hX hi.choose_spec
  cases TensorLoadSources.load hpre hX hs ht hi with
  | query tile hSpec =>
    rw [hSpec] at hl
    exact query_source_allocated hpre hg tile hl
  | main hDesc =>
    apply gather_source_allocated hDesc ?_ hl
    intro row hRow byte hByte
    rw [hpre.kvInput row hRow byte hByte]
    simp
  | extra _ hDesc =>
    apply gather_source_allocated hDesc ?_ hl
    intro row hRow byte hByte
    rw [hpre.extraKvInput row hRow byte hByte]
    simp

/-- Every query or gather source stays in its logical input byte range. -/
theorem tensor_load_input_range (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.TensorIssue i address spec) (hl : TensorCopy.readLoc spec x y k = some l) :
    (P.qBase ≤ l.addr ∧ l.addr < P.qBase + tensorBytes P) ∨
    (P.kvBase ≤ l.addr ∧ l.addr < P.kvBase + cacheBytes P.numBlocks P.blockStride) ∨
    (P.extra_topk ≠ 0 ∧ P.extraKvBase ≤ l.addr ∧
      l.addr < P.extraKvBase + cacheBytes P.extraNumBlocks P.extraBlockStride) := by
  cases TensorLoadSources.load hpre hX hs ht hi with
  | query tile hSpec =>
    rw [hSpec] at hl
    exact .inl (query_source_range hpre (Frame.lt_of_get hX hi.choose_spec) tile hl)
  | main hDesc => exact .inr (.inl (gather_source_range hDesc hl))
  | extra hExtra hDesc => exact .inr (.inr ⟨hExtra, gather_source_range hDesc hl⟩)

/-- The frozen kernel issues no tensor prefetch with a memory footprint. -/
theorem tensor_prefetch_read_allocated
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hm : X.MemTouches (.async i (.read (.prefetch x y k))) a) :
    False := by
  obtain ⟨_, _, hi, _⟩ := tensor_footprint hm
  exact TensorLoadSources.no_tensor_prefetch hX hi

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
