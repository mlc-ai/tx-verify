-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.DequantOperandWriter
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.DequantCompetingWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.DequantGenerationOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2RawWriteKinds

@[expose] public section

/-! # Reads-from selection for observed key and value bytes -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow AsyncCopy Protocol MmaDataTrace MachineTracking

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Later ordinary writes of this operand byte must be after its read. The
two obligations distinguish the dequantization slot's reuse from its output alias. -/
structure KvOperandRetirement (P : Params) (L : Launch) (X : Execution)
    (reader : EvId) (index : Nat) (block : Nat) (byte : Loc) : Prop where
  dequant : ∀ {g j : Nat} {w : Wg2.D} {r : Fin 4} {s : Fin 8} {a : Acc} {bs : List Byte},
    Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 w)) →
    w.site = .store r s → block < w.block → w.block % 2 = block % 2 →
    ctaOf L g = byte.cta → X.Writes (g, j) a bs → a.Covers byte →
    ByteCausality L X byte (.async reader (.mmaRead true index)) (.thread (g, j))
  stage : ∀ {g j : Nat} {a : Acc} {bs : List Byte},
    EpiloguePvHistory P L X g j → ctaOf L g = byte.cta → X.Writes (g, j) a bs → a.Covers byte →
    ByteCausality L X byte (.async reader (.mmaRead true index)) (.thread (g, j))

/-- Given retirement of this exact operand, every admissible reads-from source is
the write of the current sparse block. The earlier TMA writer, initial value, and
all prior ordinary writes are hidden by the actual current dequantization store. -/
theorem dequant_operand_readback
    {cta issuer i index : Nat} {d : Wg1Mma.D} {e : Event} {value : Option Byte}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : GemmRing.MmaIssuer P L X cta issuer) (hc : ctaOf L issuer = cta)
    (he : X.get (issuer, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X issuer i = some (some (.mma d)))
    (hsite : Wg1MmaGemmTrace.completed .dequant d.site = true)
    (slot : Fin 64) (feature : Fin 512) (b : Fin 2)
    (hread : X.MmaRead (issuer, i) true index (kvOperandLoc L cta d.i slot feature b) value)
    (hr : KvOperandRetirement P L X (issuer, i) index d.i
      (kvOperandLoc L cta d.i slot feature b)) :
    value = some (.float .bf16
      (dequant (Wg2.gatheredByte P L issuer d.i slot.val) feature.val), b.val) := by
  let l := kvOperandLoc L cta d.i slot feature b
  let reader : Ref := .async (issuer, i) (.mmaRead true index)
  let g := GemmRing.producer L cta (dequantLane slot feature)
  obtain ⟨j, w, a, bs, hw, hBlock, ⟨r, s, hSite, hRow, hStep⟩, hwrite, hCov, hvalue, hBefore⟩ :=
    dequant_operand_writer hpre hX hs hmma hc he hd hsite slot feature b hread
  have hcta : ctaOf L g = cta := (dequantCoordinates hpre cta slot feature).1
  let write : Ref := .thread (g, j)
  let acc : Acc := {loc := l, size := 1}
  have hRead : X.MemReads reader acc [value] := ⟨value, hread, rfl, rfl⟩
  have hz : 0 < acc.size := Nat.zero_lt_succ 0
  have hZero : acc.loc.at 0 = l := by simp [acc, Loc.at]
  have hHidden := hX.hidden reader acc [value] 0 write a bs hRead hz (.inl hwrite)
    (by rw [hZero]; exact hCov) (by rw [hZero]; exact hBefore)
  have hRf : X.rf reader 0 = some write := by
    cases hSource : X.rf reader 0 with
    | none => rw [hSource] at hHidden; exact hHidden.elim
    | some source =>
      have hSourceOk := (hX.rf reader acc [value] hRead).2 0 hz
      rw [hSource] at hSourceOk hHidden
      obtain ⟨fp, data, hSrc, hCovered, _⟩ := hSourceOk
      rw [hZero] at hCovered hHidden
      have hFuture : ¬ ByteCausality L X l reader source := by
        intro hOrder
        exact hX.noFuture reader acc [value] 0 source hRead hz hSource
          (by rw [hZero]; exact hOrder)
      rcases Wg2.raw_read_competing_kinds hX hSrc hCovered (show l.space = .shared from rfl) with
        ⟨⟨g', j'⟩, rfl, hw'⟩ | ⟨source, x, y, k, rfl⟩
      · rcases actual_kv_ordinary_writer hpre hX hs hw' hCovered with
          ⟨hThread, q, r', s', hState, hq, hRow', hStep', hPhase⟩ |
            ⟨hCtaStage, hHistory⟩
        · change g' = g at hThread
          subst g'
          rcases lt_trichotomy q.block d.i with hlt | hEq | hgt
          · have hg := Frame.lt_of_get hX hw'.choose_spec
            exact (hHidden (GemmRing.dequant_generation_before hpre hX (hs g hg).machine hState hw
              ⟨r', s', hq⟩ ⟨r, s, hSite⟩ hw' hwrite hCovered hCov
              (hPhase.trans (congrArg (· % 2) hBlock.symm)) (hBlock.symm ▸ hlt))).elim
          · obtain rfl : r' = r := Fin.ext (hRow'.trans hRow.symm)
            obtain rfl : s' = s := Fin.ext (hStep'.trans hStep.symm)
            have hJ := Wg2StoreHistory.store_index_unique hState hw
              (PTX.len_of_get hw'.choose_spec).le (PTX.len_of_get hwrite.choose_spec).le
              hq hSite (hEq.trans hBlock.symm)
            cases hJ
            rfl
          · exact (hFuture (hr.dequant hState hq hgt hPhase hcta hw' hCovered)).elim
        · exact (hFuture (hr.stage hHistory hCtaStage hw' hCovered)).elim
      · exact (hHidden (kv_tensor_writer_earlier hpre hX hs
          hw hSite hwrite hCov hSrc hCovered)).elim
  have hContent := (hX.rf reader acc [value] hRead).2 0 hz
  rw [hRf] at hContent
  obtain ⟨a', bytes', hSource, _, hv⟩ := hContent
  have hW : X.MemWrites write a bs := Or.inl hwrite
  obtain ⟨hFp, rfl⟩ := hW.unique hSource
  rw [hZero] at hv
  have hReadByte : value = wbyte a bs l := by
    simpa only [List.getElem?_cons_zero, Option.some.injEq, wbyte, ← hFp.1] using hv
  have hData : Wg2.gatheredByte P L g d.i slot.val =
      Wg2.gatheredByte P L issuer d.i slot.val := by
    funext off
    exact Wg2.gatheredByte_same_cta (hcta.trans hc.symm)
  rw [hReadByte, ← hData]
  exact hvalue

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
