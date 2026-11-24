-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2PayloadTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.DequantLoadPayload
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmKvValues

@[expose] public section

/-! # The actual dequantizing store writes the logical KV bytes -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow Wg2 MmaDataTrace

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The bytes written by a dequantization chunk have the launch cache's BF16 values, with
the zero row used for an invalid sparse index. -/
theorem dequant_store_payload
    {g i : Nat} {d : D} {e : Event} {row : Fin 4} {step : Fin 8}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (hSite : d.site = .store row step) {u : TState}
    (hf : (Wg2.machine P L g).Fired (some (.inr d)) e (some u))
    (elem : Fin 8) (byte : Fin 2) :
    let feature := logicalElem L g step.val elem.val
    let l : Loc := ⟨.shared, ctaOf L g, TcShared.Swizzle.offset .b128
      (kvLinearByte L d.block (rawRow L g row.val) feature byte.val)⟩
    ∃ a bs, X.MemWrites (.thread (g, i)) a bs ∧
      wbyte a bs l = some
        (.float .bf16 (dequant (gatheredByte P L g d.block (rawRow L g row.val)) feature),
          byte.val) := by
  have hi : i ≤ (X.tr g).length := (PTX.len_of_get he).le
  have hp := cachePayload_at
    (fun _ _ _ _ _ _ _ _ hj hjget hjSite hjKind =>
      scale_load_bytes hpre hX hs hjget hj hjSite hjKind)
    (fun _ _ _ _ _ _ _ _ hj hjget hjSite hjKind =>
      raw_load_bytes hpre hX hs hjget hj hjSite hjKind) hd hi
  simp only [CachePayload, hSite] at hp
  have hbuf := ((Exists.choose_spec hf).1.2 : Wg2.Inv P L g d).bufBlock
  exact dequantized_write_byte hpre hSite hbuf he hf hp.2.1
    (hp.1 _ (scaleIdx_lt step.isLt)) elem byte

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
