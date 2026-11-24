-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionSource
public import Kernels.TmlFa4Fwd.Proof.CorrectionOutputStores
import Lemmas.Execution.EventFrameSource
import Lemmas.Flow.WriteSpace
import Lemmas.Flow.WriteBytes

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame Epilogue
open PTX.Kernels.TmlFa4Fwd.Correction

noncomputable section

/-- A performed write of a vector element into correction's output staging area. -/
@[no_expose] def StagingWrite (X : Execution) (w : AsyncCopy.Ref)
    (a : Acc) (bs : List Byte) : Prop :=
  ∃ writer : EvId, w = .thread writer ∧
    ∃ (stage : Fin 2) (box : Fin 4) (chunk : Fin 8),
      X.get writer = some ⟨outputStorePc stage box chunk, .wr a bs⟩

/-- The decoded vector store supplies its abstract staging-write observation. -/
theorem StagingWrite.of_event {X : Execution} {writer : EvId} {a : Acc} {bs : List Byte}
    (stage : Fin 2) (subbox : Fin 4) (chunk : Fin 8)
    (he : X.get writer = some ⟨outputStorePc stage subbox chunk, .wr a bs⟩) :
    StagingWrite X (.thread writer) a bs := ⟨writer, rfl, stage, subbox, chunk, he⟩

/-- Recover the decoded store in the Thread layer from its staging-write observation. -/
theorem StagingWrite.decoded {X : Execution} {writer : EvId} {a : Acc} {bs : List Byte}
    (h : StagingWrite X (.thread writer) a bs) :
    ∃ (stage : Fin 2) (subbox : Fin 4) (chunk : Fin 8),
      X.get writer = some ⟨outputStorePc stage subbox chunk, .wr a bs⟩ := by
  obtain ⟨owner, ho, stage, subbox, chunk, he⟩ := h
  obtain rfl := AsyncCopy.Ref.thread.inj ho
  exact ⟨stage, subbox, chunk, he⟩

/-- A performed staging element carries all the bytes of its footprint. -/
theorem StagingWrite.length_eq_size {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {writer : EvId} {a : Acc} {bs : List Byte} (h : StagingWrite X (.thread writer) a bs) :
    bs.length = a.size := by
  obtain ⟨stage, box, chunk, he⟩ := h.decoded
  rcases get_source hX he with ⟨_, hFault⟩ | ⟨_, _, _, _, hCode, hFires⟩
  · cases hFault
  · obtain rfl := Option.some.inj (hCode.symm.trans (outputStoreCode stage box chunk))
    exact fires_write_length hFires rfl rfl

/-- A recorded staging write at a decoded vector site uses exactly one of the four
elements at the resolved address, independently of the source data word. -/
theorem stagingWriteElementOfAddress {p : Params} {l : Launch} {m : Mem0} {g : Nat}
    {t : TState} {o : Option TState} {a : Acc} {bytes : List Byte} (hp : Pre p l m)
    (stage : Fin 2) (subbox : Fin 4) (chunk : Fin 8)
    (hStep : EStep kernel Assumptions.all l g t
      ⟨outputStorePc stage subbox chunk, .wr a bytes⟩ o)
    (hAddress : t.regs (outputStoreAddrReg stage chunk) =
      some (b32 (outputChunkLoc l g stage 0 (rowOf l g) chunk.val).addr)) :
    ∃ elem : Fin 4, a = outputElementAccess l g stage subbox
      (4 * chunk.val + elem.val) (rowOf l g) := by
  let base := (outputChunkLoc l g stage 0 (rowOf l g) chunk.val).addr
  let storage := (⟨.shared, g / l.block, base + 16384 * subbox.val⟩ : Loc)
  have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
  have hXor : chunk.val ^^^ (rowOf l g) % 8 < 8 :=
    Nat.xor_lt_two_pow (n := 3) chunk.isLt (Nat.mod_lt _ (by decide))
  have hLimit := hp.shared.2.1
  have hs := stage.isLt
  have hb := subbox.isLt
  have hBound : base + 16384 * subbox.val < 2 ^ 32 := by
    dsimp [base, outputChunkLoc, sharedSlot, Loc.at]
    omega
  have hAlign : storage.addr % 16 = 0 := by
    have hShared := hp.shared.1
    dsimp [storage, base, outputChunkLoc, sharedSlot, Loc.at]
    omega
  have hPc : t.pc = outputStorePc stage subbox chunk := (estep_source_pc hStep).symm
  obtain ⟨tmpl, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · exact Kind.noConfusion (congrArg Event.kind hFire.1)
  rw [hPc, outputStoreCode] at hc
  obtain rfl := Option.some.inj hc.symm
  change Fires t.pc (storeTmpl l g t .shared 32 (outputStoreAddrReg stage chunk)
    (16384 * subbox.val : Nat) (outputOperands stage subbox chunk)) _ o at hFire
  obtain ⟨u, hTmpl⟩ | ⟨u, hTmpl, _⟩ := fires_write_tmpl hFire
  swap
  · unfold storeTmpl at hTmpl
    split at hTmpl
    · cases hTmpl
    · split at hTmpl
      · cases hTmpl
      · split at hTmpl <;> cases hTmpl
  have hEff : effAddr l g t .shared (outputStoreAddrReg stage chunk)
      (16384 * subbox.val : Nat) = .ok storage := effAddr_b32_off hAddress hBound
  simp only [storeTmpl, hEff, bind, Except.bind, elemAcc, outputOperands,
    List.length_ofFn, Nat.reduceDiv, Nat.reduceMul, hAlign, Nat.reduceEqDiff, ne_eq,
    not_true_eq_false, or_self, ↓reduceIte, pure, Except.pure] at hTmpl
  cases hm : (outputOperands stage subbox chunk)[t.sub]? with
  | none =>
    change (List.ofFn fun j => Opnd.reg (outputStoreValueReg stage subbox chunk j))[t.sub]? =
      none at hm
    simp only [hm] at hTmpl
    cases hTmpl
  | some operand =>
    have hElem : t.sub < 4 := by
      simpa only [outputOperands, List.length_ofFn] using (List.getElem?_eq_some_iff.mp hm).1
    change (List.ofFn fun j => Opnd.reg (outputStoreValueReg stage subbox chunk j))[t.sub]? =
      some operand at hm
    simp only [hm] at hTmpl
    split at hTmpl
    · cases hTmpl
    · obtain ⟨rfl, _, _⟩ := Tmpl.write.inj hTmpl
      refine ⟨⟨t.sub, hElem⟩, ?_⟩
      have hDiv : (4 * chunk.val + t.sub) / 4 = chunk.val := by omega
      have hMod : (4 * chunk.val + t.sub) % 4 = t.sub := by omega
      simp only [outputElementAccess, hDiv, hMod]
      congr 1
      simp only [storage, outputChunkLoc, base, sharedSlot, Loc.at]
      congr 1
      omega

end
end PTX.Kernels.TmlFa4Fwd.Thread.Correction
