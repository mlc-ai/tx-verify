-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchEqual
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchSample
public import Kernels.InklingRelDecode.Proof.Lib.RoundWords
public import Lemmas.Flow.MinSimple
public import Lemmas.Flow.TypedG
public import Lemmas.Flow.OutKinds
import Kernels.InklingRelDecode.Proof.Protocol.Values.ScratchSlot
import Kernels.InklingRelDecode.Proof.Softmax.Export.Scratch
import Kernels.InklingRelDecode.Proof.Softmax.Export.Mem
import Kernels.InklingRelDecode.Proof.Softmax.Export.BflyStages
public import Kernels.InklingRelDecode.Proof.Softmax.Export.Butterfly

@[expose] public section

/-! # The four bytes of a scratch word come from one store

The four bytes a lane reads at pc 2252 are the bytes of the payload of one scratch store of pc
2250: the stores that supply the bytes are in one warp's slot at one barrier ordinal, so they write
the same bytes (`stores_equal`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Flow PTX.Flow.TyG Shared Softmax.Export Lib

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The bytes of a single piece of four bytes rebuild it. -/
theorem rebuild_simple {v : Value} (hs : Simple v) (h4 : v.bytes = 4) :
    rebuild 3 (v.toBytes.map some) = .ok v := by
  have e : v.toBytes = [(v, 0), (v, 1), (v, 2), (v, 3)] := by
    rcases hs with ⟨w, x, rfl⟩ | ⟨f, x, rfl⟩ | ⟨f, rfl⟩ <;>
      simp_all [Value.toBytes, Value.byteAt, List.range_succ]
  simp [rebuild, h4, e]
  rfl

/-- **A scratch read rebuilds to the minimum of the last stage's words** of a lane of the warp the
reading lane's index modulo four names, in the reader's round, when the words of the butterfly's
stages are data. -/
theorem scratch_min (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (agree : ∀ n, StoreAgree L X n) (equal : WarpStoresEqual L X)
    (hR : ∀ g j, g % L.block < 128 → ∀ p ∈ Softmax.Data.roundWords X g j,
      SK.ni.Has p.1 ∧ SK.ni.Has p.2)
    {g j a bs} (read : X.get (g, j) = some ⟨2252, .rd a bs⟩) :
    ∃ v h j' a' r', rebuild 3 bs = .ok v ∧ Dat32 v ∧ v = Lib.minWord a' r' ∧
      Stage X 3 h j' a' r' ∧ h / L.block = g / L.block ∧ h % L.block / 32 % 4 = g % L.block % 4 ∧
      pollRound 1257 ((X.tr h).take (j' + 1)) = pollRound 1257 ((X.tr g).take j) := by
  obtain ⟨h, u, dst, ys, store, byte, cta, warp, round⟩ := scratch_slot hp hX hf agree equal read
  obtain ⟨j', a', r', rfl, st, hys⟩ := store_back hp hX store
  have lane := data_site hp hX store (by simp) (by dsimp; decide) (by dsimp; decide)
  obtain ⟨da, dr⟩ := stage_dat hp hX hf hR 3 (by omega) h j' a' r' lane st
  obtain ⟨v, hv, hdv, hsv⟩ := minE_simple da dr
  have e : Lib.minWord a' r' = v := by
    unfold Lib.minWord
    rw [hv]
    rfl
  have hst : storedBytes v = v.toBytes := by
    unfold storedBytes
    rw [storeValue_of_bytes (by simpa using hdv.2.1)]
    rfl
  obtain ⟨-, size⟩ := scratch_read hp hX read
  have len := (hX.rf _ _ _ (show X.MemReads (.thread (g, j)) a bs from .inl ⟨_, read⟩)).1
  have hbs : bs = v.toBytes.map some := by
    apply List.ext_getElem?
    intro b
    by_cases hb : b < 4
    · have hl : v.toBytes.length = 4 := by simp [Value.toBytes, hdv.2.1]
      rw [byte b hb, hys, e, hst, List.getElem?_map,
        List.getElem?_eq_getElem (by omega : b < v.toBytes.length)]
      rfl
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none]
      simp [Value.toBytes, hdv.2.1]
      omega
  exact ⟨v, h, j', a', r', by rw [hbs]; exact rebuild_simple hsv hdv.2.1, hdv, e.symm, st, cta,
    warp, round⟩

/-- **A scratch read rebuilds to a datum**, when the words of the butterfly's stages are data. -/
theorem scratch_rebuild (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (agree : ∀ n, StoreAgree L X n) (equal : WarpStoresEqual L X)
    (hR : ∀ g j, g % L.block < 128 → ∀ p ∈ Softmax.Data.roundWords X g j,
      SK.ni.Has p.1 ∧ SK.ni.Has p.2)
    {g j a bs} (read : X.get (g, j) = some ⟨2252, .rd a bs⟩) :
    ∃ v, rebuild 3 bs = .ok v ∧ Dat32 v := by
  obtain ⟨v, -, -, -, -, hv, hd, -⟩ := scratch_min hp hX hf agree equal hR read
  exact ⟨v, hv, hd⟩

/-- **A scratch read returns a datum.** -/
theorem scratch_dat (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (agree : ∀ n, StoreAgree L X n) (equal : WarpStoresEqual L X)
    (hR : ∀ g j, g % L.block < 128 → ∀ p ∈ Softmax.Data.roundWords X g j,
      SK.ni.Has p.1 ∧ SK.ni.Has p.2)
    {g j a bs} (read : X.get (g, j) = some ⟨2252, .rd a bs⟩) : Dat32 (Lib.loadWord bs) := by
  obtain ⟨v, hv, hd⟩ := scratch_rebuild hp hX hf agree equal hR read
  unfold Lib.loadWord
  rw [hv]
  exact hd

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
