-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemRescaleChunkOrder
import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleNumerics
import Kernels.TmlFa4Fwd.Proof.CorrectionTmemLoads
import Lemmas.Flow.SplitJoin

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.TcMma PTX.Flow PTX.Proof
open PTX.Kernels.TmlFa4Fwd.Correction

/-- A finite FP32 coefficient whose word is preserved by the scalar and packed paths. -/
structure RescaleFactorWord (word : Value) (alpha : ℝ) : Prop where
  width : word.bytes = 4
  head : word.byteAt 0 = (word, 0)
  value : valFloat .f32 word = .ok alpha
  unpack : splitValue 64 (joinValue word word) = (word, word)

theorem RescaleFactorWord.ofFloat (alpha : ℝ) : RescaleFactorWord (.float .f32 alpha) alpha :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem RescaleFactorWord.ofBits {b : BitVec 64} {alpha : ℝ} (hb : b.toNat < 2 ^ 32)
    (hValue : valFloat .f32 (.bits 32 b) = .ok alpha) : RescaleFactorWord (.bits 32 b) alpha :=
  ⟨rfl, rfl, hValue, split_join_bits hb⟩

/-- The actual entry of a recorded rescale chunk, with its decoded FP32 row factor. -/
@[no_expose] def RescaleChunkEntry (l : Launch) (X : Execution) (writer : EvId)
    (stage : Fin 2) (chunk : Fin 8) (alpha : ℝ) : Prop :=
  ∃ t ending pos word, writer.2 = pos + 2 ∧
    At t (rescaleLoadPc stage chunk) [] ∧
    t.regs (rescaleAddressReg stage chunk) =
      some (b32 (outputAddress l writer.1 stage (16 * chunk.val))) ∧
    RescaleFactorWord word alpha ∧
    (if chunk.val = 0 then t.regs (statsReg stage .alpha) = some word
      else t.regs (rescaleAlphaPair stage) = some (joinValue word word)) ∧
    Run kernel Assumptions.all l writer.1 t ((X.tr writer.1).drop pos) ending

/-- Package the actual load cursor and decoded coefficient as the entry of the
same correction chunk's store. -/
theorem RescaleChunkEntry.ofLoadState {l : Launch} {X : Execution} {writer : EvId}
    {stage : Fin 2} {chunk : Fin 8} {alpha : ℝ} {t : TState} {ending : Option TState}
    {pos : Nat} {word : Value} (hPos : writer.2 = pos+2)
    (ht : At t (rescaleLoadPc stage chunk) [])
    (hAddr : t.regs (rescaleAddressReg stage chunk) =
      some (b32 (outputAddress l writer.1 stage (16*chunk.val))))
    (hWord : RescaleFactorWord word alpha)
    (hReg : if chunk.val = 0 then t.regs (statsReg stage .alpha) = some word
      else t.regs (rescaleAlphaPair stage) = some (joinValue word word))
    (hRun : Run kernel Assumptions.all l writer.1 t ((X.tr writer.1).drop pos) ending) :
    RescaleChunkEntry l X writer stage chunk alpha :=
  ⟨t,ending,pos,word,hPos,ht,hAddr,hWord,hReg,hRun⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) {writer : EvId}
    {stage : Fin 2} {chunk : Fin 8} {alpha : ℝ} {cell : Cell} {value : Value}
    (h : RescaleChunkEntry l X writer stage chunk alpha) (hw : StoreValue l X writer cell value)
    (hWords : ∀ (load : EvId) (a : Nat) (vals : List Value) (sh : TcShape),
      Relation.TransGen (TcStep l X) load writer → X.TLd load a vals sh →
      ∀ (j : Nat) (c : Cell), LoadCell l X load j c → RescaleLoadCell l X load c stage →
      ∃ x, vals[j]? = some (.float .f32 x))
include hp h hw hWords

/-- An actual rescale store multiplies the same tensor cell read by its
preceding chunk load by the row factor present at chunk entry. -/
theorem RescaleChunkEntry.storeProduct :
    ∃ (load : EvId) (address : Nat) (words : List Value) (j : Nat) (x : ℝ),
      TraceBefore X load writer ∧ load.2+2 = writer.2 ∧
      Relation.TransGen (TcStep l X) load writer ∧ X.TLd load address words .s32x32b ∧
      LoadCell l X load j cell ∧ RescaleLoadCell l X load cell stage ∧
      words[j]? = some (.float .f32 x) ∧ value = .float .f32 (x*alpha) := by
  classical
  obtain ⟨g,writerIndex⟩ := writer
  obtain ⟨t,ending,pos,word,hPos,ht,hAddr,hWord,hAlpha,hr⟩ := h
  change writerIndex = pos + 2 at hPos
  subst writerIndex
  obtain ⟨a,vs,sh,j,⟨_,he⟩,hValue,hCell⟩ := hw
  have hLength := len_of_get he
  obtain ⟨_,vals,_,hLen,_,hRead,_,_⟩ := observeRescaleLoadInPrefix hp stage chunk
    (ht.mono (by exact ⟨hAddr,trivial⟩)) hr (.inr (by omega))
  have hPo : po X (g,pos) (g,pos+2) := po_of_not_access rfl (by omega) hLength (by rw [he]; rfl)
  have hBefore : Relation.TransGen (TcStep l X) (g,pos) (g,pos+2) :=
    .single (.inl (.single (.inl hPo)))
  let address := outputAddress l g stage (16 * chunk.val)
  let tld : X.TLd (g,pos) address vals .s32x32b := ⟨_,hRead⟩
  have hPriorWord (k : Nat) (hk : k < 16) : ∃ x, vals[k]? = some (.float .f32 x) := by
    let c := tcDataCell l g .s32x32b address k
    have hk' : k < vals.length := by omega
    exact hWords _ _ _ _ hBefore tld k c ⟨_,_,_,tld,hk',rfl⟩
      (RescaleLoadCell.ofDecoded chunk hRead hk' rfl)
  let old (k : Nat) : ℝ := if hk : k < 16 then Classical.choose (hPriorWord k hk) else 0
  have hList : vals = List.ofFn (fun i : Fin 16 => fl (old i.val)) := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < 16
    · have hAt := Classical.choose_spec (hPriorWord k hk)
      simpa only [List.getElem?_ofFn, old, dite_eq_left hk, fl] using hAt
    · rw [List.getElem?_eq_none (by omega), List.getElem?_ofFn, dite_eq_right hk]
  have hReadList : ∀ ys, X.get (g,pos) = some ⟨rescaleLoadPc stage chunk,
      .tc (.ld address ys .s32x32b)⟩ → ys = List.ofFn (fun i : Fin 16 => fl (old i.val)) := by
    intro ys hys
    have hEq := TcKind.ld.inj (Kind.tc.inj (Event.mk.inj (Option.some.inj
      (hys.symm.trans hRead))).2)
    exact hEq.2.1.trans hList
  have hLow : valFloat .f32 (splitValue 64 (joinValue word word)).1 = .ok alpha := by
    rw [hWord.unpack]
    exact hWord.value
  have hHigh : valFloat .f32 (splitValue 64 (joinValue word word)).2 = .ok alpha := by
    rw [hWord.unpack]
    exact hWord.value
  obtain ⟨_,_,_,hStore,_,_⟩ := observeRescaledChunkInPrefix hp stage chunk old
    word alpha ht hAddr (by simp) hReadList hWord.width hLow hHigh hAlpha hr (.inr hLength)
  have hEq := TcKind.st.inj (Kind.tc.inj (Event.mk.inj (Option.some.inj
    (he.symm.trans hStore))).2)
  rw [hEq.2.1, List.getElem?_ofFn] at hValue
  split at hValue
  next hJ =>
    have hAddress : a = address := hEq.1
    have hShape : sh = .s32x32b := hEq.2.2
    rw [hAddress,hShape] at hCell
    have hLoaded : j < vals.length := by omega
    have hReadWord : vals[j]? = some (.float .f32 (old j)) := by
      rw [hList,List.getElem?_ofFn,dite_eq_left hJ]
      rfl
    exact ⟨(g,pos),address,vals,j,old j,⟨rfl,by omega,hLength⟩,rfl,hBefore,tld,
      ⟨address,vals,.s32x32b,tld,hLoaded,hCell⟩,
      RescaleLoadCell.ofDecoded chunk hRead hLoaded hCell,
      hReadWord,(Option.some.inj hValue).symm⟩
  next => cases hValue

/-- A recorded store is FP32 when its preceding load reads finite values and
the row factor present at chunk entry is FP32. -/
theorem RescaleChunkEntry.finiteStore :
    ∃ x, value = .float .f32 x := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hValue⟩ := h.storeProduct hp hw hWords
  exact ⟨_,hValue⟩
end

/-- The row factor supplied to each actual rescale load can be decoded as a finite FP32 value. -/
def FiniteRescaleFactors (l : Launch) (X : Execution) : Prop :=
  ∀ (g position : Nat) (stage : Fin 2) (chunk : Fin 8) (address : Nat) (words : List Value),
    X.get (g,position) = some ⟨rescaleLoadPc stage chunk,.tc (.ld address words .s32x32b)⟩ →
    ∃ (t : TState) (ending : Option TState) (word : Value) (alpha : ℝ),
      At t (rescaleLoadPc stage chunk) [] ∧
      t.regs (rescaleAddressReg stage chunk) =
        some (b32 (outputAddress l g stage (16 * chunk.val))) ∧
      RescaleFactorWord word alpha ∧
      (if chunk.val = 0 then t.regs (statsReg stage .alpha) = some word
        else t.regs (rescaleAlphaPair stage) = some (joinValue word word)) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop position) ending

/-- Recover the entry of the actual store's chunk. The numerical premise concerns only
the row factor as recorded by the corresponding load's actual thread state. -/
theorem rescaleChunkEntryOfFactor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFactors : FiniteRescaleFactors l X) {writer : EvId} {stage : Fin 2}
    (hStore : OutputRescaleStore X writer stage) :
    ∃ chunk alpha, RescaleChunkEntry l X writer stage chunk alpha := by
  obtain ⟨⟨g,j⟩,chunk,address,words,hLane,hPosition,hLoad⟩ :=
    previousRescaleChunkLoadDecoded hp hX hStore
  change g = writer.1 at hLane
  subst g
  obtain ⟨t,ending,word,alpha,ht,hAddr,hWord,hAlpha,hRun⟩ :=
    hFactors writer.1 j stage chunk address words hLoad
  exact ⟨chunk,alpha,t,ending,j,word,hPosition.symm,ht,hAddr,hWord,hAlpha,hRun⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Correction
