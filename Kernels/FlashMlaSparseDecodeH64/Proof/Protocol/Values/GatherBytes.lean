-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.GatherRows
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.GatherBox
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Gather
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.TensorSrc
import Lemmas.Tensor.TensorReadSources

@[expose] public section

/-! # The bytes a gather writes

A notified gather4 load of the TMA lane (`TmaAt`, a tensor issue) has written every slot
`(x, y, z)` of its box with column `x < 132` (`gather_byte`). With the coordinate words good
(`GatherRowsGood`, `Iface/GatherRows.lean`) the byte is the zero fill `(bits 32 0, z)` (row word
`-1`) or byte `4 x + z` of the physical row of a selected slot (`rowBytes`), the byte `Pre`
gives the cache (`kvInput`, `extraKvInput`; no write covers it, `load_source`). The slot's shared
byte is `576 y + 4 x + z` after the box's base (`gather_writeLoc`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX TensorDescriptor GatherBox

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The byte `k` of row `r` of a cache, as the byte the tensor load copies. -/
def rowByte (P : Params) (extra : Bool) (r k : Nat) : Byte :=
  (.bits 8 (BitVec.ofNat 64 (cacheByte P extra r k)), 0)

/-- The length of an extra row is at most `extra_topk`. -/
theorem extraLen_le (hp : Pre P L m) {e : Nat} (he : e < P.b) :
    P.extraTopkLen e ≤ P.extra_topk := by
  have h := hp.paramExtraTopkLen
  cases hb : P.extraTopkLenBase with
  | none => rw [hb] at h; exact (h.2 e he).le
  | some x =>
    rw [hb] at h
    obtain ⟨-, -, hm⟩ := h
    exact (hm e he 0 (by decide)).2 e he

/-- A selected slot's row is a row of its cache, and the cache's rows are non-empty. -/
theorem slotRow_lt (hp : Pre P L m) {e q : Nat} (he : e < P.b) (hq : q < P.s_q) {extra : Bool}
    {j : Nat} (hv : slotValid P e q extra j) :
    slotRow P e q extra j < cacheRows P extra := by
  have rowOf_lt : ∀ {blocks stride page : Nat} {idx : Int}, 0 < page → page ≤ stride / 528 →
      idx.toNat < blocks * page →
      tokenRow page stride idx < blocks * (stride / 528) := by
    intro blocks stride page idx hp0 hpage hidx
    have hblock : idx.toNat / page < blocks := (Nat.div_lt_iff_lt_mul hp0).2 hidx
    have hlocal := Nat.mod_lt idx.toNat hp0
    unfold tokenRow
    calc
      _ < (idx.toNat / page + 1) * (stride / 528) := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  cases extra
  · have hr := (hp.idxRange e he q hq j hv).2
    have := hp.pageFits
    simp only [slotRow, cacheRows, Bool.false_eq_true, ↓reduceIte]
    exact rowOf_lt hp.pagePos (by omega) hr
  · have hr := (hp.extraIdxRange e he q hq j hv).2
    have hlen : j < P.extraTopkLen e := hv.1
    have hpos : 0 < P.extra_topk := by have := extraLen_le hp he; omega
    obtain ⟨hp0, -, -, hfit⟩ := hp.extraPos hpos
    simp only [slotRow, cacheRows, ↓reduceIte]
    exact rowOf_lt hp0 (by omega) hr

/-- **The bytes of a notified gather, for one cache's map** (`base`, `blocks`, `stride`): slot
`(x, y, z)`, `x < 132`, is written; its byte is the zero fill when the row word is `-1` and the
cache's byte `4 x + z` of row `r` when the row word is a row of the cache. -/
private theorem byte_core (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : NoUbInner L X) {base blocks stride : Nat} {cls : AllocationClass}
    {cb : Nat → Nat → Nat}
    (hin : ∀ r < blocks * (stride / 528), ∀ byte < 528,
      m ⟨.global, 0, base + r * 528 + byte⟩ =
        some (some (Value.bits 8 (BitVec.ofNat 64 (cb r byte)), 0)))
    {g k a : Nat} {o : TensorCopy.Observation}
    (hiss : X.TensorIssue (g, k) a o.spec) (ho : X.tensor (g, k) = some o)
    (hn : o.effects.notified = true)
    (hD : (⟨o.spec.outer, o.spec.descriptor⟩ : Σ n, Descriptor n) =
      ⟨1, (encodeKv base blocks stride cls).fourRows⟩)
    {ys : Fin 4 → Int} (hr : o.spec.rows = some ys) (h0 : o.spec.origin 0 = 0)
    {x y z : Nat} (hx : x < 132) (hy : y < 4) (hz : z < 4)
    (hgood : ys ⟨y, hy⟩ = -1 ∨ ∃ r : Nat, ys ⟨y, hy⟩ = r ∧ r < blocks * (stride / 528)) :
    ∃ byte, TensorCopy.writeByte o x y z = some byte ∧
      (ys ⟨y, hy⟩ = -1 → byte = (.bits 32 0, z)) ∧
      ∀ r : Nat, ys ⟨y, hy⟩ = r → r < blocks * (stride / 528) →
        byte = (.bits 8 (BitVec.ofNat 64 (cb r (4 * x + z))), 0) := by
  obtain ⟨-, hok, -⟩ := hX.tensor _ o ho
  rcases hgood with h | ⟨r, hrr, hlt⟩
  · obtain ⟨slot, hsl, hsrc⟩ := spec_source_fill hD hr (x := x) (by omega) hy hz h
    obtain ⟨c, hc⟩ := hok.complete hn slot
    have hct : c = .filled .zero .u32 z := by
      have := hok.writes slot c hc
      rw [hsrc] at this
      exact this
    refine ⟨(.bits 32 0, z), ?_, fun _ => rfl, fun r hrr _ => ?_⟩
    · simp only [TensorCopy.writeByte, hsl, Option.bind_some, hc, hct]
      rfl
    · rw [h] at hrr
      omega
  · obtain ⟨slot, hsl, hsrc⟩ := spec_source_global hD hr h0 hx hy hz hrr hlt
    obtain ⟨c, hc⟩ := hok.complete hn slot
    obtain ⟨byte, hread, hct⟩ : ∃ byte, o.effects.read slot = some byte ∧ c = .copied byte := by
      have := hok.writes slot c hc
      rw [hsrc] at this
      exact this
    have hl : TensorCopy.readLoc o.spec x y z =
        some ⟨.global, 0, base + r * 528 + 4 * x + z⟩ := by
      rw [TensorCopy.readLoc_source, hsl]
      simp only [Option.bind_some, hsrc]
    have hrb : TensorCopy.readByte o x y z = some byte := by
      simp only [TensorCopy.readByte, hsl, Option.bind_some, hread]
    obtain ⟨-, hnw⟩ := load_source hp hX hFw hnu hiss hsrc
    have hm := hin r hlt (4 * x + z) (by omega)
    have hv := tensor_readByte_of_initial hX ho hiss hl hrb
      (by simpa only [Nat.add_assoc] using hm) hnw
    have hval : byte = (.bits 8 (BitVec.ofNat 64 (cb r (4 * x + z))), 0) := hv
    refine ⟨byte, ?_, fun h => ?_, fun r' hr' _ => ?_⟩
    · simp only [TensorCopy.writeByte, hsl, Option.bind_some, hc, hct]
      rfl
    · rw [h] at hrr
      omega
    · have : r' = r := by omega
      subst this
      exact hval

/-- The bytes of a notified gather through the main (`extra = false`) or extra cache's map. -/
theorem gather_byte_map (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : NoUbInner L X) (extra : Bool)
    (hex : extra = true → P.extra_topk ≠ 0)
    {g k a : Nat} {o : TensorCopy.Observation}
    (hiss : X.TensorIssue (g, k) a o.spec) (ho : X.tensor (g, k) = some o)
    (hn : o.effects.notified = true)
    (hD : (⟨o.spec.outer, o.spec.descriptor⟩ : Σ n, Descriptor n) = gatherMap P extra)
    {ys : Fin 4 → Int} (hr : o.spec.rows = some ys) (h0 : o.spec.origin 0 = 0)
    {x y z : Nat} (hx : x < 132) (hy : y < 4) (hz : z < 4)
    (hgood : ys ⟨y, hy⟩ = -1 ∨ ∃ r : Nat, ys ⟨y, hy⟩ = r ∧ r < cacheRows P extra) :
    ∃ byte, TensorCopy.writeByte o x y z = some byte ∧
      (ys ⟨y, hy⟩ = -1 → byte = (.bits 32 0, z)) ∧
      ∀ r : Nat, ys ⟨y, hy⟩ = r → r < cacheRows P extra →
        byte = rowByte P extra r (4 * x + z) := by
  cases extra
  · exact byte_core hp hX hFw hnu (cb := fun r b => (P.kvByte r b).val) hp.kvInput hiss ho hn hD
      hr h0 hx hy hz hgood
  · have hne := hex rfl
    exact byte_core hp hX hFw hnu (cb := fun r b => (P.extraKvByte r b).val) hp.extraKvInput hiss
      ho hn hD hr h0 hx hy hz hgood

/-- **A gather reads through a cache map**: its descriptor is the four-row form of the main
cache's map, or of the extra cache's when the extra cache is on. -/
theorem gather_enc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc a : Nat} {s : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a s⟩) (hat : MbarRow.TmaAt L g pc) :
    (⟨s.outer, s.descriptor⟩ : Σ n, Descriptor n) = gatherMap P false ∨
      (P.extra_topk ≠ 0 ∧ (⟨s.outer, s.descriptor⟩ : Σ n, Descriptor n) = gatherMap P true) := by
  obtain ⟨d0, hd, hK⟩ := tma_gather_map hp hX hFw he hat rfl
  have hd' : s.descriptor = d0.fourRows := hd
  rcases hK with h | ⟨hne, h⟩
  · have := congrArg (fun y : Σ n, Descriptor n => (⟨y.1, y.2.fourRows⟩ : Σ n, Descriptor n)) h
    simp only at this
    refine .inl ?_
    rw [hd']
    exact this
  · have := congrArg (fun y : Σ n, Descriptor n => (⟨y.1, y.2.fourRows⟩ : Σ n, Descriptor n)) h
    simp only at this
    refine .inr ⟨hne, ?_⟩
    rw [hd']
    exact this

/-- **The fill of a gather is the `.u32` zero.** -/
theorem gather_fill (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc a : Nat} {s : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a s⟩) (hat : MbarRow.TmaAt L g pc) :
    s.descriptor.fill = .zero ∧ s.descriptor.format = .u32 := by
  rcases gather_enc hp hX hFw he hat with h | ⟨-, h⟩
  · exact spec_fill (base := P.kvBase) (blocks := P.numBlocks) (stride := P.blockStride)
      (cls := P.kvClass) h
  · exact spec_fill (base := P.extraKvBase) (blocks := P.extraNumBlocks)
      (stride := P.extraBlockStride) (cls := P.extraKvClass) h

/-- **The bytes of a gather** (`GatherRowsGood`): a notified gather of the TMA lane has written
every slot `(x, y, z)` with `x < 132`; the byte is the zero fill `(bits 32 0, z)` or byte
`4 x + z` of the physical row of a selected slot. -/
theorem gather_byte (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : NoUbInner L X) (hG : GatherRowsGood P L X) {g k pc a : Nat}
    {s : TensorCopy.Spec} {o : TensorCopy.Observation}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a s⟩) (hat : MbarRow.TmaAt L g pc)
    (ho : X.tensor (g, k) = some o) (hn : o.effects.notified = true) {x y z : Nat}
    (hx : x < 132) (hy : y < 4) (hz : z < 4) :
    ∃ byte, TensorCopy.writeByte o x y z = some byte ∧
      (byte = (.bits 32 0, z) ∨ ∃ e < P.b, ∃ q < P.s_q, ∃ extra j, slotValid P e q extra j ∧
        byte = rowByte P extra (slotRow P e q extra j) (4 * x + z)) := by
  have hs : o.spec = s := by
    obtain ⟨⟨addr, pc', hiss⟩, -, -⟩ := hX.tensor _ o ho
    rw [he] at hiss
    obtain ⟨-, hk⟩ := Event.mk.inj (Option.some.inj hiss)
    exact (Kind.tensorIssue.inj hk).2.symm
  obtain ⟨h0, ys, hr, hgood⟩ := hG he hat
  have hmap := gather_enc hp hX hFw he hat
  subst hs
  have hiss : X.TensorIssue (g, k) a o.spec := ⟨pc, he⟩
  rcases hgood ⟨y, hy⟩ with h | ⟨e, he', q, hq, extra, j, hv, hD, hrow⟩
  · obtain ⟨extra, hex, hD⟩ : ∃ extra : Bool, (extra = true → P.extra_topk ≠ 0) ∧
        (⟨o.spec.outer, o.spec.descriptor⟩ : Σ n, Descriptor n) = gatherMap P extra := by
      rcases hmap with h | ⟨hne, h⟩
      · exact ⟨false, (fun h => by cases h), h⟩
      · exact ⟨true, fun _ => hne, h⟩
    obtain ⟨byte, hw, hfill, -⟩ := gather_byte_map hp hX hFw hnu extra hex hiss ho hn hD hr h0 hx hy
      hz
      (.inl h)
    exact ⟨byte, hw, .inl (hfill h)⟩
  · have hex : extra = true → P.extra_topk ≠ 0 := by
      intro hextra
      subst hextra
      have hlen : j < P.extraTopkLen e := hv.1
      have := extraLen_le hp he'
      omega
    have hlt := slotRow_lt hp he' hq hv
    obtain ⟨byte, hw, -, hval⟩ := gather_byte_map hp hX hFw hnu extra hex hiss ho hn hD hr h0 hx hy
      hz
      (.inr ⟨slotRow P e q extra j, hrow, hlt⟩)
    exact ⟨byte, hw, .inr ⟨e, he', q, hq, extra, j, hv, hval _ hrow hlt⟩⟩

/-- **The shared byte of a gather's slot**: `576 y + 4 x + z` after the box's base. -/
theorem gather_writeLoc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc a : Nat} {s : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a s⟩) (hat : MbarRow.TmaAt L g pc) {x y z : Nat}
    (hx : x < 144) (hy : y < 4) (hz : z < 4) :
    TensorCopy.writeLoc s x y z = some (s.sharedBase.at (576 * y + 4 * x + z)) := by
  rcases gather_enc hp hX hFw he hat with h | ⟨-, h⟩
  · exact spec_writeLoc (base := P.kvBase) (blocks := P.numBlocks) (stride := P.blockStride)
      (cls := P.kvClass) h hx hy hz
  · exact spec_writeLoc (base := P.extraKvBase) (blocks := P.extraNumBlocks)
      (stride := P.extraBlockStride) (cls := P.extraKvClass) h hx hy hz

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
