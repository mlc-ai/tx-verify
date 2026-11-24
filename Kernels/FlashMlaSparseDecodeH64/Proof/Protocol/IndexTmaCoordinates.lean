-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexTma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingAccessOrder
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.IndexCoordinateTrace
public import Lemmas.Flow.AllocTmpl
import Lemmas.Order.OrderWaits

@[expose] public section

/-! # The coordinate word published to the TMA reader -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexTma

open PTX PTX.Flow PTX.Proof PTX.MbarRing
open IndexRingThreads

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The coordinate payload depends on the CTA and the index lane. -/
theorem coord_same_cta {g h b lane pair : Nat} (hc : ctaOf L g = ctaOf L h) :
    Wg1Index.coordValue P L g b lane pair = Wg1Index.coordValue P L h b lane pair := by
  simp only [Wg1Index.coordValue, Wg1Index.rowBits, Wg1Index.validBit, Wg1Index.slotIdx,
    Wg1Index.slotPg, Wg1Index.slotStride, Wg1Index.eOf, Wg1Index.qOf, ctaidY, ctaidX, hc]
  rfl

/-- A visible coordinate word is read back when each competing source has the same bytes
or belongs to an earlier or later generation. Only the actual read sources need classification. -/
theorem rebuild_of_publication {g i : Nat} {a aw : Acc} {bs : List (Option Byte)}
    {w : EvId} {word : Nat}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hr : X.MemReads (.thread (g, i)) a bs) (ha : a.size = 4)
    (hl : a.loc = aw.loc) (hz : aw.size = 4)
    (hw : X.MemWrites (.thread w) aw (b32 word).toBytes)
    (hBefore : baseCausality L X w (g, i))
    (sources : ∀ k < 4, ∀ other fp raw, X.rf (.thread (g, i)) k = some other →
      X.MemWrites other fp raw → fp.Covers (a.loc.at k) →
      (fp.loc = a.loc ∧ raw = (b32 word).toBytes) ∨
        ByteCausality L X (a.loc.at k) other (.thread w) ∨
        ByteCausality L X (a.loc.at k) (.thread (g, i)) other) :
    rebuild 3 bs = .ok (b32 word) := by
  have hRf := hX.rf (.thread (g, i)) a bs hr
  have hlen : bs.length = 4 := hRf.1.trans ha
  have hWordLen : (b32 word).toBytes.length = 4 := rfl
  have hbs : bs = (b32 word).toBytes.map some := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < 4
    · have hka : k < a.size := by simpa only [ha] using hk
      have hCov : aw.Covers (a.loc.at k) := by
        rw [hl]
        refine ⟨rfl, rfl, ?_, ?_⟩
        · change aw.loc.addr ≤ aw.loc.addr + k
          omega
        · change aw.loc.addr + k < aw.loc.addr + aw.size
          omega
      have hVisible : ByteCausality L X (a.loc.at k) (.thread w) (.thread (g, i)) :=
        .direct (.inl hBefore)
      have hHidden := hX.hidden (.thread (g, i)) a bs k (.thread w) aw
        (b32 word).toBytes hr hka hw hCov hVisible
      have hrf := hRf.2 k hka
      cases hsrc : X.rf (.thread (g, i)) k with
      | none => rw [hsrc] at hHidden; exact hHidden.elim
      | some other =>
        rw [hsrc] at hrf hHidden
        obtain ⟨fp, raw, hWrite, hCover, hVal⟩ := hrf
        rcases sources k hk other fp raw hsrc hWrite hCover with ⟨hLoc, rfl⟩ | earlier | later
        · have hByte : k < (b32 word).toBytes.length := by omega
          simpa only [wbyte, Loc.at, hLoc, Nat.add_sub_cancel_left, List.getElem?_map,
            List.getElem?_eq_getElem hByte, Option.map_some] using hVal
        · exact (hHidden earlier).elim
        · exact (hX.noFuture (.thread (g, i)) a bs k other hr hka hsrc later).elim
    · rw [List.getElem?_eq_none (by omega : bs.length ≤ k),
        List.getElem?_eq_none (by rw [List.length_map, hWordLen]; omega)]
  rw [hbs]
  exact rebuild_b32 word

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexTma
