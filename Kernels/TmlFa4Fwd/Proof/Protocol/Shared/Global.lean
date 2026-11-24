-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.ShFrame
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.MemStore
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Lifetime
import Lemmas.Protocol.RegionOrder
import Kernels.TmlFa4Fwd.Proof.Lib.InputMap
import Kernels.TmlFa4Fwd.Proof.Lib.OutputFrame
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.StoreWarp
import Kernels.TmlFa4Fwd.Proof.Lib.StoreForm
import Kernels.TmlFa4Fwd.Proof.Correction.Export.LseAddr

@[expose] public section

/-! # The accesses outside shared memory

* Every global write is of a byte of the O region or of an LSE word (`global_write`), so no write
  is of an input byte (`noInputWrite`, the read-only input assumption's condition).
* Every read outside shared memory is of a scheduler word or a page-table entry, of the lane's local
  memory, of a Q or bias element through a tensor load (`tload_src`), or a row copy's source
  (`outside_read`). Where a row copy's source lies is the loader's row addresses' (`CpSrc`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- **A row copy reads an element of a K/V row** (the loader's row addresses). -/
def CpSrc (p : Params) (X : Execution) : Prop :=
  ∀ i s l, X.Copy i s → s.src.Covers l → ∃ page < p.pages, ∃ h < p.kvHeads, ∃ r < 16,
    ∃ d < 128, ∃ y < 2, l = (p.kLayout.loc page h r d).at y ∨ l = (p.vLayout.loc page h r d).at y

/-- A byte of an input element of the Q or bias tensor. -/
def InElem (p : Params) (l : Loc) : Prop :=
  (∃ q < p.totalQ, ∃ h < p.heads, ∃ d < 128, ∃ y < 2, l = (p.qLoc q h d).at y) ∨
    ∃ q < p.totalQ + 128, ∃ h < p.heads, ∃ c < 1280, ∃ y < 2, l = (p.biasLoc q h c).at y

private theorem lookup_bounds {d : TensorDescriptor.Descriptor 2} {origin : Fin 3 → Int}
    {slot : TensorTransfer.Slot d} {a : Nat}
    (h : TensorTransfer.globalAddress d origin none slot = some a) : ∃ col row head : Nat,
      TensorAddress.lookup (TensorDescriptor.geometry d) (inputCoordinate col row head)
        slot.2.2.val = some a := by
  unfold TensorTransfer.globalAddress at h
  set coordinate := TensorTransfer.coord d origin none slot
  have hb : TensorAddress.InBounds (TensorDescriptor.geometry d) coordinate := by
    by_contra hn
    rw [TensorAddress.lookup, ite_eq_right fun hh => hn hh.1] at h
    cases h
  have hC : coordinate = inputCoordinate (coordinate 0).toNat (coordinate 1).toNat
      (coordinate 2).toNat := by
    funext axis
    fin_cases axis
    · exact (Int.toNat_of_nonneg (hb 0).1).symm
    · exact (Int.toNat_of_nonneg (hb 1).1).symm
    · exact (Int.toNat_of_nonneg (hb 2).1).symm
  exact ⟨_, _, _, hC ▸ h⟩

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
  (hFw : Follow p L X)
include hp hX hFw

/-- A global write of a thread is a log-sum-exp word. -/
theorem lse_write_shape {i : EvId} {a : Acc} {bs : List Byte} (hw : X.Writes i a bs)
    (hgl : a.loc.space = .global) :
    ∃ row < p.totalQ, ∃ head < p.heads, a.loc = p.lseLoc row head ∧ a.size = 4 := by
  obtain ⟨g, k⟩ := i
  obtain ⟨pc, he⟩ := hw
  have hne : a.loc.space ≠ .shared ∧ a.loc.space ≠ .local := by rw [hgl]; simp
  rcases mem_event hp hX hFw he trivial with ⟨_, _, hk, -⟩ | ⟨_, _, hk, h⟩ | ⟨_, hk, -⟩ |
    ⟨_, _, hk, -⟩ | ⟨_, _, hk, -⟩ | ⟨_, _, _, _, hk, -⟩ <;> cases hk
  rcases h with ⟨-, h⟩ | ⟨h8, h11, ⟨st, h⟩ | -⟩ | ⟨-, h⟩ | ⟨o, h, -⟩
  · obtain ⟨-, n, -, h⟩ := h
    exact (hne.1 (by rw [h])).elim
  · obtain ⟨-, q, -, w, -, h⟩ := h
    exact (hne.1 (by rw [h])).elim
  · obtain ⟨b, hb, hlo, hhi, st, hrow, hloc, hz⟩ := corr_lse hp hX hFw h8 h11 he hgl
    refine ⟨_, ?_, _, (Epilogue.assignedCoordinates_valid hp hlo hhi).2, hloc, hz⟩
    have h1 := hp.qOffset_le_total (b := b + 1) (by omega)
    have h2 := hp.qOffset_mono (show b ≤ b + 1 by omega) (show b + 1 ≤ p.batch by omega)
    unfold Params.qLength at hrow
    omega
  · exact (hne.1 (by rw [h.2])).elim
  · exact (hne.2 (by rw [h])).elim

/-- **The global write frame.** -/
theorem global_write {w : Ref} {a : Acc} {l : Loc} (hw : X.Intent w a true) (hc : a.Covers l)
    (hs : l.space = .global) : p.oRegion.Contains l ∨
      ∃ q < p.totalQ, ∃ h < p.heads, ∃ y < 4, l = (p.lseLoc q h).at y :=
  outputIntentFootprint_of_sites hp hX
    (fun _ _ _ hw hg => lse_write_shape hp hX hFw hw hg)
    (fun _ _ _ hi => issuedBox hp hX (store_warp hp hX hFw hi) hi) w a l hw hc hs

/-- **The footprint of a global write**: an LSE word or an O byte. -/
theorem global_write_shape {w : Ref} {a : Acc} (hw : X.Intent w a true)
    (hs : a.loc.space = .global) :
    (∃ q < p.totalQ, ∃ head < p.heads, a.loc = p.lseLoc q head ∧ a.size = 4) ∨
      (a.size = 1 ∧ p.oRegion.Contains a.loc) :=
  outputIntentShape hp hX (fun _ _ _ hw hg => lse_write_shape hp hX hFw hw hg)
    (fun _ _ _ hi => issuedBox hp hX (store_warp hp hX hFw hi) hi) hw hs

/-- A byte the global writes cover is in the O or the LSE region. -/
theorem global_write_region {w : Ref} {a : Acc} {l : Loc} (hw : X.Intent w a true)
    (hc : a.Covers l) (hs : l.space = .global) : p.oRegion.Contains l ∨ p.lseRegion.Contains l := by
  rcases global_write hp hX hFw hw hc hs with h | ⟨q, hq, head, hh, y, hy, rfl⟩
  · exact .inl h
  · exact .inr (lseByte_in hq hh hy)

/-- **The read-only input assumption's condition**: every global write is an LSE store at its row's
LSE word or a byte of an output tensor store's box of a scheduled work item, so it is in the O or
LSE region, which the launch keeps apart from every input array. -/
theorem Top.noInputWrite : ¬ Assumptions.inputReadOnly.ub L m X :=
  OutputIntentFootprint.noInputWrite hp (outputIntentFootprint_of_sites hp hX
    (fun _ _ _ hw hg => lse_write_shape hp hX hFw hw hg)
    (fun _ _ _ hi => issuedBox hp hX (store_warp hp hX hFw hi) hi))

/-- **A tensor load reads a byte of a Q or bias element.** -/
theorem tload_src {i : EvId} {addr : Nat} {s : TensorCopy.Spec} (hi : X.TensorIssue i addr s)
    {x y z : Nat} {l : Loc} (hl : TensorCopy.readLoc s x y z = some l) : InElem p l := by
  obtain ⟨pc, he⟩ := hi
  obtain ⟨-, j, org, mb, -, rfl⟩ := input_box hp hX hFw he
  unfold inputSpec at hl
  rw [TensorCopy.readLoc_source] at hl
  simp only [Option.bind_eq_some_iff] at hl
  obtain ⟨slot, -, hl⟩ := hl
  split at hl
  swap
  · cases hl
  rename_i address hsrc
  obtain rfl := Option.some.inj hl
  unfold TensorCopy.source at hsrc
  split at hsrc
  swap
  · cases hsrc
  rename_i a' ha
  simp only [TensorTransfer.Source.global.injEq] at hsrc
  subst hsrc
  change TensorTransfer.globalAddress (Loader.inputMap p (Loader.inputSite j)) org none slot =
    some a' at ha
  obtain ⟨col, row, head, h⟩ := lookup_bounds ha
  have hg : ∀ (b : Loc) (n : Nat), b.space = .global → b.cta = 0 → (b.at n).addr = a' →
      (⟨.global, 0, a'⟩ : Loc) = b.at n := by
    rintro ⟨_, _, _⟩ n rfl rfl rfl
    rfl
  cases hb : (Loader.inputSite j).bias with
  | false =>
    have hm : Loader.inputMap p (Loader.inputSite j) = p.qMap := by
      simp only [Loader.inputMap, hb, Bool.false_eq_true, ↓reduceIte]
    generalize slot.2.2.val = y at h
    rw [hm, qLookup_eq] at h
    split_ifs at h with hc
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hc
    exact .inl ⟨row, h2, head, h3, col, h1, y, h4, hg _ _ rfl rfl (Option.some.inj h)⟩
  | true =>
    have hm : Loader.inputMap p (Loader.inputSite j) = p.biasMap := by
      simp only [Loader.inputMap, hb, ↓reduceIte]
    generalize slot.2.2.val = y at h
    rw [hm, biasLookup_eq] at h
    split_ifs at h with hc
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hc
    exact .inr ⟨row, h2, head, h3, col, h1, y, h4, hg _ _ rfl rfl (Option.some.inj h)⟩

/-- **The reads outside shared memory.** -/
theorem outside_read {r : Ref} {a : Acc} (hi : X.Intent r a false) (hs : a.loc.space ≠ .shared) :
    InWord p a ∨ (∃ g k, r = .thread (g, k) ∧ LocalAt L g a) ∨
      (∃ i s, X.Copy i s ∧ s.src = a) ∨ a.size = 1 ∧ InElem p a.loc := by
  rcases r with ⟨g, k⟩ | ⟨⟨g, k⟩, part⟩
  · rcases hi with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨_, -, h⟩ | ⟨o, n, pc, he⟩
    · rcases mem_event hp hX hFw he trivial with ⟨a', bs', hk, h⟩ | ⟨_, _, hk, -⟩ | ⟨_, hk, -⟩ |
        ⟨_, _, hk, -⟩ | ⟨_, _, hk, -⟩ | ⟨_, _, _, _, hk, -⟩ <;> cases hk
      rcases h with h | ⟨-, h⟩ | ⟨-, -, n, st, h⟩ | ⟨-, h⟩ | h
      · exact .inl h
      · exact (hs h.2.1).elim
      · rw [h.2] at hs; exact (hs rfl).elim
      · rw [h.2] at hs; exact (hs rfl).elim
      · exact .inr (.inl ⟨g, k, rfl, h⟩)
    · cases h
    · exact (noActualRmw hX ⟨pc, he⟩).elim
  · obtain ⟨hw, hfp⟩ := hi
    cases part
    case async.readCopy =>
      rcases hfp with ⟨sp, hc, rfl⟩ | ⟨pc, he⟩
      · exact .inr (.inr (.inl ⟨_, _, hc, rfl⟩))
      · exact ((no_prefetch hX he).1 a rfl).elim
    case async.readLoad x y z =>
      obtain ⟨sp, al, hi, hl, hz⟩ := hfp
      exact .inr (.inr (.inr ⟨hz, tload_src hp hX hFw hi hl⟩))
    case async.readStore x y z =>
      obtain ⟨sp, al, hi, hl, hz⟩ := hfp
      obtain ⟨st, bx, h⟩ := storeRead_box hp hX (store_warp hp hX hFw hi) hi
      exact (hs (h x y z _ hl).1).elim
    case async.mmaRead isB idx =>
      exact (hs (Execution.mmaFootprint_shared hfp.2)).elim
    case async.readPrefetch =>
      obtain ⟨_, _, ⟨pc, he⟩, -⟩ := hfp
      exact ((no_prefetch hX he).2.1 _ _ rfl).elim
    case async.oldElem j =>
      obtain ⟨sp, r, hc, hr, -⟩ := hfp
      rw [(copy_row hp hX hFw hc).2.whole] at hr
      cases hr
    case async.oldStore x y z =>
      obtain ⟨sp, al, hi, hr, -⟩ := hfp
      rw [(actualTensorStoreForm hX hi).2.2] at hr
      cases hr
    all_goals first
      | exact hfp.elim
      | simp [Part.writes] at hw

/-- **The writes outside shared memory** are global, or of the lane's local memory. -/
theorem outside_write {r : Ref} {a : Acc} (hi : X.Intent r a true) (hs : a.loc.space ≠ .shared) :
    a.loc.space = .global ∨ ∃ g k, r = .thread (g, k) ∧ LocalAt L g a := by
  rcases r with ⟨g, k⟩ | ⟨⟨g, k⟩, part⟩
  · rcases hi with ⟨_, -, h⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨o, n, pc, he⟩
    · cases h
    · rcases mem_event hp hX hFw he trivial with ⟨_, _, hk, -⟩ | ⟨a', bs', hk, h⟩ | ⟨_, hk, -⟩ |
        ⟨_, _, hk, -⟩ | ⟨_, _, hk, -⟩ | ⟨_, _, _, _, hk, -⟩ <;> cases hk
      rcases h with ⟨-, h⟩ | ⟨-, -, ⟨st, h⟩ | h⟩ | ⟨-, h⟩ | h
      · obtain ⟨-, n, -, h⟩ := h; rw [h] at hs; exact (hs rfl).elim
      · obtain ⟨-, q, -, w, -, h⟩ := h; rw [h] at hs; exact (hs rfl).elim
      · exact .inl h
      · rw [h.2] at hs; exact (hs rfl).elim
      · exact .inr ⟨g, k, rfl, h⟩
    · exact (noActualRmw hX ⟨pc, he⟩).elim
  · obtain ⟨hw, hfp⟩ := hi
    cases part
    case async.writeStore x y z =>
      obtain ⟨sp, al, -, hl, -⟩ := hfp
      exact .inl (tstore_global hl)
    case async.writeCopy =>
      obtain ⟨sp, hc, -, rfl⟩ := hfp
      obtain ⟨i, j, -, hd⟩ := (copy_row hp hX hFw hc).2.dst
      rw [hd] at hs
      exact (hs rfl).elim
    case async.writeElem j =>
      obtain ⟨sp, hc, hj⟩ := hfp
      simp [AsyncCopy.Spec.elems, AsyncCopy.Spec.elemOffsets, (copy_row hp hX hFw hc).2.whole] at hj
    case async.writeLoad x y z =>
      obtain ⟨sp, al, ⟨pc, he⟩, hl, hz⟩ := hfp
      obtain ⟨j, h1, -⟩ := tload_box hp hX hFw he hl
      exact (hs h1).elim
    case async.writeCta =>
      obtain ⟨_, _, hi, -⟩ := hfp
      exact (noClcIssue hX hi).elim
    all_goals first
      | exact hfp.elim
      | simp [Part.writes] at hw

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
