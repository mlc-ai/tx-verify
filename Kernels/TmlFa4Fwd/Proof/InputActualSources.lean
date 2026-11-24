-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.InputCopies
public import Kernels.TmlFa4Fwd.Proof.LoaderInputDescriptors

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX TensorDescriptor

noncomputable section

private theorem packedCoordinates {geometry : TensorAddress.Geometry 3}
    {coordinate : Fin 3 → Int} {k a : Nat}
    (h : TensorAddress.lookup geometry coordinate k = some a) :
    ∃ col row head : Nat, coordinate = inputCoordinate col row head := by
  unfold TensorAddress.lookup at h
  split at h
  · rename_i hBound
    refine ⟨(coordinate 0).toNat, (coordinate 1).toNat, (coordinate 2).toNat, ?_⟩
    funext i
    fin_cases i
    · exact (Int.toNat_of_nonneg (hBound.1 0).1).symm
    · exact (Int.toNat_of_nonneg (hBound.1 1).1).symm
    · exact (Int.toNat_of_nonneg (hBound.1 2).1).symm
  · cases h

private theorem hasPackedQByte {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {coordinate : Fin 3 → Int} {k a : Nat}
    (h : TensorAddress.lookup (geometry p.qMap) coordinate k = some a) :
    ∃ region ∈ p.inputRegions, region.Contains (globalLoc a) ∧
      ∃ byte, m (globalLoc a) = some (some byte) := by
  obtain ⟨col, row, head, rfl⟩ := packedCoordinates h
  rw [qLookup_eq] at h
  split at h
  · rename_i hBounds
    obtain ⟨⟨hc, hr, hh⟩, hk⟩ := hBounds
    obtain rfl := Option.some.inj h.symm
    have hR := packedBf16Byte (base := p.qBase) hr hh hc hk
    rw [show 2 * (p.totalQ * p.heads * 128) = 256 * p.heads * p.totalQ by ring] at hR
    exact ⟨_, by simp [Params.inputRegions], hR, _, hp.qBytes _ hr _ hh _ hc _ hk⟩
  · cases h

private theorem hasPackedBiasByte {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {coordinate : Fin 3 → Int} {k a : Nat}
    (h : TensorAddress.lookup (geometry p.biasMap) coordinate k = some a) :
    ∃ region ∈ p.inputRegions, region.Contains (globalLoc a) ∧
      ∃ byte, m (globalLoc a) = some (some byte) := by
  obtain ⟨col, row, head, rfl⟩ := packedCoordinates h
  rw [biasLookup_eq] at h
  split at h
  · rename_i hBounds
    obtain ⟨⟨hc, hr, hh⟩, hk⟩ := hBounds
    obtain rfl := Option.some.inj h.symm
    have hR := packedBf16Byte (base := p.biasBase) hr hh hc hk
    rw [show 2 * ((p.totalQ + 128) * p.heads * 1280) =
      2560 * p.heads * (p.totalQ + 128) by ring] at hR
    refine ⟨_, by simp [Params.inputRegions], hR, _, hp.biasBytes _ hr _ hh _ hc _ ?_⟩
    cases p.bias row head col <;> simpa [biasValue, Value.bytes, FloatFmt.bytes] using hk
  · cases h

private theorem actualMapValid {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (site : Loader.InputSite) : TensorDescriptor.Valid (Loader.inputMap p site) := by
  cases h : site.bias
  · simpa [Loader.inputMap, h] using (hp.maps 9 p.qMapAddress ⟨2, p.qMap⟩
      (by simp)).2.2.2.2.1
  · simpa [Loader.inputMap, h] using (hp.maps 11 p.biasMapAddress ⟨2, p.biasMap⟩
      (by simp)).2.2.2.2.1

private theorem actualMapBytes (p : Params) (site : Loader.InputSite) :
    TensorTransfer.bytes (Loader.inputMap p site) = 16384 := by
  cases h : site.bias <;>
    norm_num [Loader.inputMap, h, Params.qMap, Params.biasMap, TensorTransfer.bytes,
      TensorTile.count, TensorTile.rows, TensorTile.rowsOf, TensorTile.step,
      TensorDescriptor.Format.bytes]

private theorem actualMapBacked {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (site : Loader.InputSite) {coordinate : Fin 3 → Int} {k a : Nat}
    (hLookup : TensorAddress.lookup (geometry (Loader.inputMap p site)) coordinate k = some a) :
    ∃ region ∈ p.inputRegions, region.Contains (globalLoc a) ∧
      ∃ byte, m (globalLoc a) = some (some byte) := by
  cases h : site.bias
  · exact hasPackedQByte hp (by simpa [Loader.inputMap, h] using hLookup)
  · exact hasPackedBiasByte hp (by simpa [Loader.inputMap, h] using hLookup)

/-- An actual input load uses a valid map and each backed byte belongs to a launch input.
This holds also for padded rows and for arbitrary signed coordinates at the issue. -/
theorem actualTensorInputSource {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {addr : Nat} {s : TensorCopy.Spec} (hi : X.TensorIssue i addr s) :
    TensorCopy.RoutingOk l (i.1 / l.block) s ∧
      TensorDescriptor.Valid s.descriptor ∧ 0 < TensorTransfer.bytes s.descriptor ∧
      ∀ slot a, TensorCopy.source s slot = .global a →
        ∃ region ∈ p.inputRegions, region.Contains (globalLoc a) ∧
          ∃ byte, m (globalLoc a) = some (some byte) := by
  obtain ⟨j, _, hDesc, _⟩ := Loader.actualInputDescriptor hp hX hi
  have hRoute := actualTensorRoute hX hi
  rcases s with ⟨⟨outer, desc, origin, shared, rows⟩, barrier, cluster, group⟩
  simp only [Sigma.mk.injEq] at hDesc
  obtain ⟨rfl, hD⟩ := hDesc
  have hEq : desc = Loader.inputMap p (Loader.inputSite j) := eq_of_heq hD
  subst desc
  have hBytes := actualMapBytes p (Loader.inputSite j)
  refine ⟨hRoute, actualMapValid hp _, by rw [hBytes]; decide, ?_⟩
  intro slot a hSource
  change (match TensorTransfer.globalAddress _ origin rows slot with
    | some address => TensorTransfer.Source.global address
    | none => TensorTransfer.Source.fill _ _ _) = TensorTransfer.Source.global a at hSource
  split at hSource
  · rename_i address hg
    obtain rfl := TensorTransfer.Source.global.inj hSource
    exact actualMapBacked hp (Loader.inputSite j) hg
  · cases hSource

/-- Each byte of a 128-byte-swizzled subbox lies within the box's shared allocation. -/
theorem tensorSharedBoxOffset {outer : Nat} {d : TensorDescriptor.Descriptor outer}
    {base x y byte : Nat} (hSw : d.swizzle = .b128)
    (hWidth : TensorTile.count d.box 0 * d.format.bytes = 128)
    (hx : x < TensorTile.count d.box 0) (hy : y < TensorTile.rows d.box)
    (hb : byte < d.format.bytes) :
    ∃ k < 128 * TensorTile.rows d.box,
      TensorTile.sharedByte d.box d.format.bytes d.swizzle base x y byte = base + k := by
  rw [hSw]
  let linear := TensorTile.linearByte d.box d.format.bytes .b128 x y byte
  have hPitch : TensorTile.rowBytes d.box d.format.bytes .b128 = 128 := by
    simp [TensorTile.rowBytes, hWidth, TensorTile.swizzleWidth]
  have hRow : x * d.format.bytes + byte < 128 := by
    have hNext := Nat.mul_le_mul_right d.format.bytes (Nat.succ_le_of_lt hx)
    rw [Nat.succ_mul, hWidth] at hNext
    omega
  have hLinear : linear < 128 * TensorTile.rows d.box := by
    dsimp [linear, TensorTile.linearByte]
    rw [hPitch]
    omega
  have hSwizzled := TensorSwizzle.offset_row .b128 base linear
  exact ⟨TensorSwizzle.offset .b128 base linear, by omega, rfl⟩

private theorem inputLayout {p : Params} {site : Loader.InputSite} :
    let d := Loader.inputMap p site
    d.format.bytes = 2 ∧ d.swizzle = .b128 ∧
      TensorTile.count d.box 0 = 64 ∧ TensorTile.rows d.box = 128 := by
  cases h : site.bias <;>
    norm_num [Loader.inputMap, h, Params.qMap, Params.biasMap, TensorTile.count,
      TensorTile.rows, TensorTile.rowsOf, TensorTile.step, TensorDescriptor.Format.bytes]

/-- An actual Q or Bias transfer retires one full subbox of transaction bytes. -/
theorem actualTensorInputTxBytes {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {addr : Nat} {s : TensorCopy.Spec} (hi : X.TensorIssue i addr s) :
    TensorTransfer.bytes s.descriptor = 16384 := by
  obtain ⟨site, _, hDesc, _⟩ := Loader.actualInputDescriptor hp hX hi
  have hEq := congrArg
    (fun d : (n : Nat) × TensorDescriptor.Descriptor n => TensorTransfer.bytes d.2) hDesc
  obtain ⟨hBytes, _, hCols, hRows⟩ := inputLayout (p := p) (site := Loader.inputSite site)
  change TensorTransfer.bytes s.descriptor =
    TensorTransfer.bytes (Loader.inputMap p (Loader.inputSite site)) at hEq
  rw [hEq]
  unfold TensorTransfer.bytes
  rw [hBytes, hCols, hRows]

private theorem inputSharedOffsetBounds :
    ∀ i : Fin 14, 3072 ≤ (Loader.inputSite i).sharedOffset ∧
      (Loader.inputSite i).sharedOffset ≤ 216064 ∧
      ((Loader.inputSite i).sharedOffset + 16384 ≤ 68608 ∨
        166912 ≤ (Loader.inputSite i).sharedOffset) := by
  decide

private theorem inputSlotWithinBox {p : Params} {site : Loader.InputSite}
    {s : TensorCopy.Spec}
    (hDesc : (⟨s.outer,s.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
      ⟨2, Loader.inputMap p site⟩) (slot : TensorTransfer.Slot s.descriptor) :
    ∃ k < 16384, (s.sharedLoc slot).addr = s.sharedBase.addr + k := by
  rcases s with ⟨⟨outer, desc, origin, shared, rows⟩, barrier, cluster, group⟩
  simp only [Sigma.mk.injEq] at hDesc
  obtain ⟨rfl, hD⟩ := hDesc
  let d := Loader.inputMap p site
  have hEq : desc = d := eq_of_heq hD
  subst desc
  obtain ⟨hBytes, hSw, hWidth, hRows⟩ := inputLayout (p := p) (site := site)
  have hPitch : TensorTile.count d.box 0 * d.format.bytes = 128 := by rw [hWidth, hBytes]
  obtain ⟨k, hk, hAddr⟩ := tensorSharedBoxOffset (base := shared.addr) hSw hPitch
    slot.1.isLt slot.2.1.isLt slot.2.2.isLt
  rw [hRows] at hk
  exact ⟨k,hk,hAddr⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- Every write of one Q or Bias transfer lies in its physical 16 KiB subbox. -/
theorem actualTensorInputByteWithinBox {i : EvId} {addr x y byte : Nat} {s : TensorCopy.Spec}
    (hi : X.TensorIssue i addr s) {loc : Loc} (hl : TensorCopy.writeLoc s x y byte = some loc) :
    s.sharedBase.addr ≤ loc.addr ∧ loc.addr < s.sharedBase.addr + 16384 := by
  obtain ⟨site,_,hDesc,_⟩ := Loader.actualInputDescriptor hp hX hi
  obtain ⟨slot,_,rfl⟩ := Option.map_eq_some_iff.mp hl
  obtain ⟨k,hlt,heq⟩ := inputSlotWithinBox (site := Loader.inputSite site) hDesc slot
  omega

/-- Every Q or Bias destination lies in the issuing CTA's data area outside the K/V ring. -/
theorem actualTensorInputSharedFrame {i : EvId} {addr : Nat} {s : TensorCopy.Spec}
    (hi : X.TensorIssue i addr s) (slot : TensorTransfer.Slot s.descriptor) :
    ∃ offset, 3072 ≤ offset ∧ offset < 232448 ∧
      (offset < 68608 ∨ 166912 ≤ offset) ∧
      s.sharedLoc slot = ⟨.shared, i.1 / l.block, l.sharedBase + offset⟩ := by
  obtain ⟨j, _, hDesc, _, hDst, _, _⟩ := Loader.actualInputBox hp hX hi
  let site := Loader.inputSite j
  obtain ⟨k,hk,hAddr⟩ := inputSlotWithinBox (site := site) hDesc slot
  obtain ⟨hLower, hUpper, hSeparate⟩ := inputSharedOffsetBounds j
  change 3072 ≤ site.sharedOffset at hLower
  change site.sharedOffset ≤ 216064 at hUpper
  change site.sharedOffset + 16384 ≤ 68608 ∨ 166912 ≤ site.sharedOffset at hSeparate
  refine ⟨site.sharedOffset + k, by omega, by omega, by omega, ?_⟩
  change s.sharedBase = ⟨.shared, i.1 / l.block, l.sharedBase + site.sharedOffset⟩ at hDst
  have hs : (s.sharedLoc slot).space = s.sharedBase.space := rfl
  have hc : (s.sharedLoc slot).cta = s.sharedBase.cta := rfl
  rw [hDst] at hs hc hAddr
  cases hLoc : s.sharedLoc slot with
  | mk space cta addr =>
    rw [hLoc] at hs hc hAddr
    simp only [Loc.mk.injEq]
    exact ⟨hs,hc,hAddr.trans (Nat.add_assoc _ _ _)⟩

/-- Every Q or Bias destination is inside the data area of the issuing CTA. -/
theorem actualTensorInputSharedRange {i : EvId} {addr : Nat} {s : TensorCopy.Spec}
    (hi : X.TensorIssue i addr s) (slot : TensorTransfer.Slot s.descriptor) :
    ∃ offset, 3072 ≤ offset ∧ offset < 232448 ∧
      s.sharedLoc slot = ⟨.shared, i.1 / l.block, l.sharedBase + offset⟩ := by
  obtain ⟨offset, hLo, hHi, _, hLoc⟩ := actualTensorInputSharedFrame hp hX hi slot
  exact ⟨offset, hLo, hHi, hLoc⟩

/-- An actual tensor input byte cannot overwrite any byte in a K/V ring slot. -/
theorem tensorInputWriteLocOutsideKv {issue : EvId} {address x y byte : Nat} {s : TensorCopy.Spec}
    {loc : Loc} (hIssue : X.TensorIssue issue address s)
    (hLoc : TensorCopy.writeLoc s x y byte = some loc) :
    loc.addr < l.sharedBase + 68608 ∨ l.sharedBase + 166912 ≤ loc.addr := by
  obtain ⟨slot, _, rfl⟩ := Option.map_eq_some_iff.mp hLoc
  obtain ⟨offset, _, _, hSeparate, hDst⟩ := actualTensorInputSharedFrame hp hX hIssue slot
  rw [hDst]
  change l.sharedBase + offset < l.sharedBase + 68608 ∨
    l.sharedBase + 166912 ≤ l.sharedBase + offset
  omega

/-- Q and Bias TMA writes cannot compete with a selected K/V byte. -/
theorem tensorInputWriteDoesNotCoverKv {issue : EvId} {x y byte : Nat} {a : Acc} {data : List Byte}
    {loc : Loc} (hWrite : X.MemWrites (.async issue (.write (.load x y byte))) a data)
    (hLower : l.sharedBase + 68608 ≤ loc.addr) (hUpper : loc.addr < l.sharedBase + 166912) :
    ¬ a.Covers loc := by
  intro hCover
  obtain ⟨_, _, _, _, hIssue, hLoc, _, hSize, _⟩ := hWrite
  have hOutside := tensorInputWriteLocOutsideKv hp hX hIssue hLoc
  rw [Acc.loc_of_one hCover hSize] at hOutside
  omega

/-- The destination subbox of every actual Q or Bias load fits its CTA's shared allocation. -/
theorem actualTensorInputSharedAllocated {i : EvId} {addr : Nat} {s : TensorCopy.Spec}
    (hi : X.TensorIssue i addr s) (slot : TensorTransfer.Slot s.descriptor)
    : m (s.sharedLoc slot) ≠ none := by
  obtain ⟨offset, _, hRange, hLoc⟩ := actualTensorInputSharedRange hp hX hi slot
  obtain ⟨_, he⟩ := hi
  have hG := PTX.Proof.event_thread_lt hX he
  have hBlock : 0 < l.block := by rw [hp.block]; decide
  have hCta := (Nat.div_lt_iff_lt_mul hBlock).2 (show i.1 < l.grid * l.block from hG)
  rw [hLoc]
  exact hp.shared.2.2 _ hCta _ hRange

end
end PTX.Kernels.TmlFa4Fwd
