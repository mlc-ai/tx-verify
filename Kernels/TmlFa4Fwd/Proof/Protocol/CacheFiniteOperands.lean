-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.CacheSourceBytes
public import Kernels.TmlFa4Fwd.Proof.MmaOperandValues
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyBacking

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.AsyncCopy PTX.TcMma Mma

/-- A performed loader vector contains either a complete BF16 cache element or two zero-fill
bytes at every aligned word. -/
theorem cacheCopyWordWritten {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {i : EvId} {spec : Spec} {bytes : List Byte} (hCopy : X.Copy i spec)
    (hWrite : (X.async.copies i).writeBytes = some bytes) {word : Nat} (hWord : word < 8) :
    (∃ value : ℝ, ∀ b : Fin 2, bytes[2 * word + b.val]? =
      some ((Value.float .bf16 value).byteAt b.val)) ∨
    (∀ b : Fin 2, bytes[2 * word + b.val]? = some zeroByte) := by
  have hWidth := (actualCopyShape hX hCopy).widthEq
  have hSpec := (cacheCopySourceBytes hp hX hFrame hCopy hWrite).2
  rcases Thread.Loader.ordinaryCopySize hp hX hCopy with hZero | hLive
  · exact .inr (fun b => (hSpec (2 * word + b.val) (by have := b.isLt; omega)).2 (by omega))
  obtain ⟨value,hValue⟩ := Thread.Loader.ordinaryCopyWords hp hX hFrame hCopy word (by omega)
  refine .inl ⟨value,fun b => ?_⟩
  have hByte := b.isLt
  obtain ⟨seen,hSeen,hw⟩ := (hSpec (2 * word + b.val) (by omega)).1 (by omega)
  have hv := hValue b.val (by simpa [Value.bytes,FloatFmt.bytes] using hByte)
  rw [show (spec.src.loc.at (2 * word)).at b.val = spec.src.loc.at (2 * word + b.val) by
    cases spec.src.loc
    simp [Loc.at,Nat.add_assoc]] at hv
  exact hw.trans (congrArg some (Option.some.inj (Option.some.inj (hSeen.symm.trans hv))))

/-- Two adjacent operand bytes assigned to the same aligned word of a performed cache
copy form a finite BF16 value whenever the actual writes at both bytes are ordered. -/
theorem cacheOperandElementOfOrderedWord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {issue mma : EvId} {spec : Spec} {bytes : List Byte} (hCopy : X.Copy issue spec)
    (hWrite : (X.async.copies issue).writeBytes = some bytes) {word : Nat} (hWord : word < 8)
    {d row k : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat} {ops : MmaOperands}
    (hMma : X.MmaIssue mma d op acc mask) (hOps : X.async.mmaOperands mma = some ops)
    (hLoc : ∀ b : Fin 2, op.byteLoc .b (qkByteIndex row k b.val) =
      some (spec.dst.loc.at (2 * word + b.val)))
    (hOrder : ∀ b : Fin 2, modelCausality l X (spec.dst.loc.at (2 * word + b.val))
      (.async issue (.write .copy)) (.async mma (.mmaRead true (qkByteIndex row k b.val))))
    (hOther : ∀ (b : Fin 2) other a data, X.MemWrites other a data →
      a.Covers (spec.dst.loc.at (2 * word + b.val)) →
      other = .async issue (.write .copy) ∨
        modelCausality l X (spec.dst.loc.at (2 * word + b.val)) other
          (.async issue (.write .copy)) ∨
        modelCausality l X (spec.dst.loc.at (2 * word + b.val))
          (.async mma (.mmaRead true (qkByteIndex row k b.val))) other) :
    ∃ value, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b row k = .ok value := by
  have hShape := actualCopyShape hX hCopy
  have hActual := (Execution.memWrites_write_copy_of_whole hCopy hShape.whole).mpr ⟨rfl,hWrite⟩
  have hRecorded (b : Fin 2) {value : Byte}
      (hValue : bytes[2 * word + b.val]? = some value) :
      ops.b[qkByteIndex row k b.val]? = some (some value) := by
    have hb := b.isLt
    have hCovered : spec.dst.Covers (spec.dst.loc.at (2 * word + b.val)) := by
      simp only [Acc.Covers, Loc.InRange, Loc.at, hShape.widthEq, true_and]
      exact ⟨by omega,by omega⟩
    have hByte : wbyte spec.dst bytes (spec.dst.loc.at (2 * word + b.val)) = some value := by
      simpa only [wbyte, Loc.at, Nat.add_sub_cancel_left] using hValue
    exact operandByte_observed hX hMma hOps (isB := true) (hLoc b)
      ⟨_,_,_,hActual,hCovered,hByte,hOrder b,hOther b⟩
  rcases cacheCopyWordWritten hp hX hFrame hCopy hWrite hWord with ⟨val,hVal⟩ | hZero
  · exact ⟨val,idealBf16Element_of_bytes (hRecorded 0 (hVal 0)) (hRecorded 1 (hVal 1))⟩
  · exact ⟨0,idealBf16Element_of_zeroBytes (hRecorded 0 (hZero 0)) (hRecorded 1 (hZero 1))⟩

end PTX.Kernels.TmlFa4Fwd.Protocol
