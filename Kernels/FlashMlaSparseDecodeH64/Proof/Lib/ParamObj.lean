-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Lemmas.Flow.ParamObject

@[expose] public section

/-! # The launch with the bytes of `param_0` explicit

The kernel reads its scalar parameters with `ld.param` from the by-value object `param_0`
through the pointer register `%rd2`. `p0fields P L` lists the fields it reads with the values `Pre`
gives them (the scale's bit pattern, which `Pre.paramScale` only says exists, is `scaleBits L`,
read from the launch's bytes); under the library's `explicitObject L (param "0")
(scalarsParam, P.param0Base) (p0fields P L)` a segment's evaluation reads each such load as the
little-endian number of those bytes, and `p0_eq` (from `explicitObject_eq`) returns to `L`: a role
states it as a hypothesis, which `seg_sym` uses. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

/-- The scale's bit pattern: the four bytes of `param_0` at offset 28 (`Pre.paramScale` says such a
pattern exists). -/
def scaleBits (L : Launch) : Nat :=
  open Classical in
  if h : ∃ b < 2 ^ 32, ∀ k < 4, L.paramBytes (param "0") (28 + k) = some (leByte b k) then
    Classical.choose h
  else 0

theorem scaleBits_spec {P : Params} {L : Launch} {m : Mem0} (hp : Pre P L m) :
    scaleBits L < 2 ^ 32 ∧
      ∀ k < 4, L.paramBytes (param "0") (28 + k) = some (leByte (scaleBits L) k) := by
  have hex : ∃ b < 2 ^ 32, ∀ k < 4, L.paramBytes (param "0") (28 + k) = some (leByte b k) := by
    obtain ⟨b, hb, hbytes, -⟩ := hp.paramScale
    exact ⟨b, hb, hbytes⟩
  unfold scaleBits
  simp only [hex, dite_true]
  exact Classical.choose_spec hex

/-- The fields of `param_0` the kernel reads: offset, value and byte count. -/
def p0fields (P : Params) (L : Launch) : List (Nat × Nat × Nat) :=
  [(0, P.b, 4), (8, 64, 4), (28, scaleBits L, 4), (36, P.page, 4), (40, P.topk, 4),
    (72, P.indicesBase, 8), (88, P.sinkBase.getD 0, 8),
    (80, P.topkLenBase.getD 0, 8), (96, P.lseBase, 8), (116, P.extraPage, 4),
    (120, P.extra_topk, 4), (136, P.extraIndicesBase, 8), (144, P.extraTopkLenBase.getD 0, 8),
    (164, P.blockStride, 4), (172, P.s_q * P.topk, 4), (176, P.topk, 4),
    (180, P.s_q * 64, 4), (184, 64, 4), (200, P.extraBlockStride, 4),
    (208, P.s_q * P.extra_topk, 4), (212, P.extra_topk, 4)]

/-- Every field of `p0fields` is in the launch's bytes. -/
theorem p0fields_ok {P : Params} {L : Launch} {m : Mem0} (hp : Pre P L m) :
    ∀ f ∈ p0fields P L, ∀ k < f.2.2,
      L.paramBytes (param "0") (f.1 + k) = some (leByteOf f.2.1 k) := by
  intro f hf k hk
  simp only [p0fields, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hp.paramB k hk
  · exact hp.paramHq k hk
  · simpa [leByteOf, leByte] using (scaleBits_spec hp).2 k hk
  · exact hp.paramPage k hk
  · exact hp.paramTopk k hk
  · exact hp.paramIndices k hk
  · have h := hp.paramSink
    cases hb : P.sinkBase with
    | none => rw [hb] at h; simpa [leByteOf, leByte] using h.1 k hk
    | some x => rw [hb] at h; simpa [leByteOf, leByte] using h.1 k hk
  · have h := hp.paramTopkLen
    cases hb : P.topkLenBase with
    | none => rw [hb] at h; simpa [leByteOf, leByte] using h.1 k hk
    | some x => rw [hb] at h; simpa [leByteOf, leByte] using h.1 k hk
  · exact hp.paramLse k hk
  · exact hp.paramExtraPage k hk
  · exact hp.paramExtraTopk k hk
  · exact hp.paramExtraIndices k hk
  · have h := hp.paramExtraTopkLen
    cases hb : P.extraTopkLenBase with
    | none => rw [hb] at h; simpa [leByteOf, leByte] using h.1 k hk
    | some x => rw [hb] at h; simpa [leByteOf, leByte] using h.1 k hk
  · exact hp.paramStrideKvBlock k hk
  · exact hp.paramStrideIndicesB k hk
  · exact hp.paramStrideIndicesSq k hk
  · exact hp.paramStrideLseB k hk
  · exact hp.paramStrideLseSq k hk
  · exact hp.paramStrideExtraKvBlock k hk
  · exact hp.paramStrideExtraIndicesB k hk
  · exact hp.paramStrideExtraIndicesSq k hk

/-- **The explicit launch is the launch.** -/
theorem p0_eq {P : Params} {L : Launch} {m : Mem0} (hp : Pre P L m) :
    explicitObject L (param "0") (scalarsParam, P.param0Base) (p0fields P L) = L :=
  explicitObject_eq hp.param0Object (p0fields_ok hp)

/-- The little-endian number of the `n` bytes of `x` from byte `k`, as the explicit launch's
`ld.param` evaluates it. -/
def leNat (x : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | k, n + 1 => (leByteOf x k).toNat + 256 * leNat x (k + 1) n

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
