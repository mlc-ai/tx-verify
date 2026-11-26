-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.GlobalCls
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Async
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TensorIn
import Lemmas.Order.Order
import Lemmas.Tensor.TensorCompleteConsistentRead
import Lemmas.Tensor.TensorCopy

@[expose] public section

/-! # The global sources of the tensor loads

A global byte a tensor load reads is a byte of the query or of a cache, which `Pre` initializes
(`load_init`), and no write covers it: the only global writes are the LSE stores and the output
stores' slots (`global_at`), and the load's read of the byte is a global access of the third kind,
so the byte is neither (`load_source`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX TensorCopy

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A byte a tensor load reads is initialized**: the byte of a source slot is a byte of the
query or of a cache. -/
theorem load_init (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {i : EvId} {a : Nat} {s : TensorCopy.Spec} {x y k ad : Nat}
    (hi : X.TensorIssue i a s) (hl : TensorCopy.readLoc s x y k = some ⟨.global, 0, ad⟩) :
    ∃ v, m ⟨.global, 0, ad⟩ = some (some v) := by
  obtain ⟨coord, byte, ad', hlk, hloc⟩ := readLoc_lookup hl
  have had : ad' = ad := by
    have := congrArg Loc.addr hloc
    exact this.symm
  subst had
  rcases tensor_load_map hp hX hFw hi with hq | ⟨d0, hd, hK⟩
  · obtain ⟨e, he, q, hq, hh, hhh, t, ht, y', hy', rfl⟩ := tiled_in (d := s.descriptor) hq hlk
    have := hp.qInput e he q hq hh hhh t ht y' hy'
    simp only [Loc.at] at this
    exact ⟨_, this⟩
  · rw [hd, fourRows_geometry] at hlk
    rcases hK with hK | ⟨-, hK⟩
    · obtain ⟨r, hr, y', hy', rfl⟩ := kv_in (d := d0) hK hlk
      exact ⟨_, hp.kvInput r hr y' hy'⟩
    · obtain ⟨r, hr, y', hy', rfl⟩ := kv_in (d := d0) hK hlk
      exact ⟨_, hp.extraKvInput r hr y' hy'⟩

/-- **A source byte of a tensor load is initialized and never written.** -/
theorem load_source (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : NoUbInner L X) {i : EvId} {a : Nat} {s : TensorCopy.Spec}
    (hi : X.TensorIssue i a s) {slot : TensorTransfer.Slot s.descriptor} {ad : Nat}
    (hs : TensorCopy.source s slot = .global ad) :
    (∃ v, m ⟨.global, 0, ad⟩ = some (some v)) ∧
      ∀ w dst bytes, X.MemWrites w dst bytes → ¬ dst.Covers ⟨.global, 0, ad⟩ := by
  have hl : TensorCopy.readLoc s slot.1.val slot.2.1.val slot.2.2.val =
      some ⟨.global, 0, ad⟩ := by
    rw [TensorCopy.readLoc_source, slotAt_self]
    simp only [Option.bind_some, hs]
  refine ⟨load_init hp hX hFw hi hl, fun w dst bytes hw hc => ?_⟩
  have hrd : X.Intent (.async i (.read (.load slot.1.val slot.2.1.val slot.2.2.val)))
      ({ loc := ⟨.global, 0, ad⟩, size := 1 } : Acc) false :=
    ⟨rfl, s, a, hi, hl, rfl⟩
  have hcv : (({ loc := ⟨.global, 0, ad⟩, size := 1 } : Acc) : Acc).Covers ⟨.global, 0, ad⟩ :=
    ⟨rfl, rfl, Nat.le_refl _, by simp⟩
  have hns : (⟨.global, 0, ad⟩ : Loc).space ≠ .shared := by simp
  have hld := global_at hp hX hFw hnu hrd hcv hns
  have hwr := global_at hp hX hFw hnu hw.intent hc hns
  cases hld with
  | load hO hLs =>
    cases hwr with
    | lse _ _ hLse _ _ => exact hLs hLse
    | store _ _ _ _ _ _ _ _ hOut => exact hO hOut

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
