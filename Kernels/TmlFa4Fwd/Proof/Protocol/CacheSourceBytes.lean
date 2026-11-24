-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyBacking
import Kernels.TmlFa4Fwd.Proof.Thread.GlobalWrites
import Kernels.TmlFa4Fwd.Proof.GlobalWrites
import Lemmas.Kernel.Memory

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.AsyncCopy

/-- Every performed paged copy contains its live launch bytes followed by zero fill. -/
theorem cacheCopySourceBytes {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {i : EvId} {spec : Spec} {bytes : List Byte}
    (hCopy : X.Copy i spec) (hWrite : (X.async.copies i).writeBytes = some bytes) :
    bytes.length = spec.dst.size ∧
    ∀ k < spec.dst.size,
      (k < spec.src.size →
        ∃ byte, m (spec.src.loc.at k) = some (some byte) ∧ bytes[k]? = some byte) ∧
      (spec.src.size ≤ k → bytes[k]? = some zeroByte) := by
  have hNonempty : nonempty (X.async.copies i) :=
    ⟨.write .copy, by simp [present, hWrite]⟩
  obtain ⟨recorded, hRecord, hEffects⟩ := hX.tma.1 i hNonempty
  obtain rfl := Option.some.inj ((issuedBy_some.mpr hCopy).symm.trans hRecord)
  have hShape := actualCopyShape hX hCopy
  have hSource : sourceBytes spec (X.async.copies i) = some bytes := by
    have h := hEffects.2.2.1 bytes hWrite
    rwa [hShape.whole] at h
  rw [sourceBytes, hShape.noData] at hSource
  obtain ⟨read, hRead, rfl⟩ := Option.map_eq_some_iff.mp hSource
  have hLen := (hEffects.2.1 read hRead).2
  have hMem : X.MemReads (.async i (.read .copy)) spec.src (read.map some) :=
    ⟨spec, read, hCopy, rfl, hRead, rfl⟩
  refine ⟨by
    rw [List.length_append, hLen, List.length_replicate]
    exact Nat.add_sub_of_le hShape.srcSize, ?_⟩
  intro k hk
  constructor
  · intro hLive
    obtain ⟨_, ⟨byte, hByte⟩, hUnwritten⟩ :=
      Thread.Loader.ordinaryCopyBacked hp hX hFrame hCopy k hLive
    have hObserved := hX.launch_byte hMem hLive hUnwritten hByte
    rw [List.getElem?_map] at hObserved
    have hRaw : read[k]? = some byte := by
      cases hAt : read[k]? with
      | none => simp [hAt] at hObserved
      | some b =>
        simp only [hAt, Option.map_some, Option.some.injEq] at hObserved ⊢
        exact hObserved
    exact ⟨byte, hByte, by rwa [List.getElem?_append_left (by simpa [hLen] using hLive)]⟩
  · intro hTail
    rw [List.getElem?_append_right (by simpa [hLen] using hTail), hLen]
    exact List.getElem?_replicate_of_lt (by omega)

end PTX.Kernels.TmlFa4Fwd.Protocol
