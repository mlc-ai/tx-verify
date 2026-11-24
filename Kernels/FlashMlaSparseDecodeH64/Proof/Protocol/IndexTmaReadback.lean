-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexTmaCoordinates
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.StageWriteClasses
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorSharedBounds
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1TmaLeader
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2RawWriteKinds
import Lemmas.Order.OrderWaits

@[expose] public section

/-! # Byte addresses and generation order for the indexed coordinate ring -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexTma

open PTX PTX.Flow PTX.Proof PTX.MbarRing IndexRingThreads

/-- A matching byte of two four-byte coordinate words fixes the ring slot, word and base
address. The producer emits two words at each index lane. -/
theorem coordinate_address_match {base slot readerSlot lane part pos offset : Nat}
    (hl : lane < 32) (hp : part < 2) (hc : pos < 64) (ho : offset < 4)
    (hlo : base + 256 * slot + 8 * lane + 4 * part ≤ base + 256 * readerSlot + 4 * pos + offset)
    (hhi : base + 256 * readerSlot + 4 * pos + offset <
      base + 256 * slot + 8 * lane + 4 * part + 4) :
    slot = readerSlot ∧ lane = pos / 2 ∧ part = pos % 2 := by
  have hslot : slot = readerSlot := by omega
  subst readerSlot
  omega

private theorem arrive_is_not_access {m : Loc} {e : Event} (h : arrivesOn m e = true) :
    e.acc = none := by
  obtain ⟨tag, kind⟩ := e
  cases kind <;> simp [sourceArrive, Event.acc] at h ⊢

/-- Two ordinary coordinate writes of the same lane and slot with different publication
ordinals are ordered through a matching barrier arrival between the writes. -/
theorem prior_coordinate_write {L : Launch} {X : Execution} {g i j : Nat}
    {e f : Event} {m : Loc} {a : Acc} {bytes : List Byte}
    (he : X.get (g, i) = some e) (hf : X.get (g, j) = some f)
    (hkind : e.kind = .wr a bytes)
    (hcount : arrivals m ((X.tr g).take i) < arrivals m ((X.tr g).take j)) :
    baseCausality L X (g, i) (g, j) := by
  obtain ⟨k, release, hkj, hk, hrelease, hOrdinal⟩ :=
    exists_nthEv (X := X) (p := arrivesOn m)
      (n := arrivals m ((X.tr g).take i)) hcount
  have hik : i < k := by
    by_contra hn
    rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt hn) with heq | hlt
    · subst k
      rw [he] at hk
      obtain rfl := Option.some.inj hk
      simp [sourceArrive, hkind] at hrelease
    · have hop := countP_take_succ hk hrelease
      have hle := countP_take_mono (arrivesOn m) (X.tr g) (show k + 1 ≤ i by omega)
      unfold arrivals at hOrdinal
      omega
  have hNoAcc : (X.get (g, k)).bind Event.acc = none := by
    rw [hk, Option.bind_some]
    exact arrive_is_not_access hrelease
  have hBefore : baseCausality L X (g, i) (g, k) :=
    .single (.inl (po_of_not_access rfl hik (PTX.len_of_get hk) hNoAcc))
  exact hBefore.trans
    (.single (.inl (po_of_source_not_access rfl hkj (PTX.len_of_get hf) hNoAcc)))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexTma
