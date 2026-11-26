-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.Ordered
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Raw.Obj
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Dequant
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Lag

@[expose] public section

/-! # Two dequant lanes' chunk stores

Two chunk stores of dequant lanes covering one byte are of one lane (`dqChunk_inj`: the lane's
chunk is a function of its index, the row and the step; the chunks are 16-aligned and below the
tile's size), so they are ordered by that lane's program order (`same_thread`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **The place of a covered byte**: a byte a dequant lane's chunk store covers lies in the
store's chunk, `dequant b`'s chunk `dqChunk i r s` of the lane `i`. -/
theorem dq_cover {h k pcw : Nat} {ac : Acc} {bs : List Byte} {l : Loc}
    (hW : X.get (h, k) = some ⟨pcw, .wr ac bs⟩) (hat : MbarRow.DequantAt L h pcw)
    (hc : ac.Covers l) :
    ∃ (b : Fin 2) (r : Fin 4) (s : Fin 8), l.cta = h / L.block ∧
      L.sharedBase + 65536 * b.val + MemRow.dqChunk (h % 128) r s ≤ l.addr ∧
      l.addr < L.sharedBase + 65536 * b.val + MemRow.dqChunk (h % 128) r s + 16 := by
  obtain ⟨b, r, s, -, hws, -, -⟩ := dequant_wrUse hp hX hFw hW hat
  obtain ⟨hl, hs⟩ := hws
  obtain ⟨-, hcta, hlo, hhi⟩ := hc
  rw [hl] at hcta hlo hhi
  rw [hs] at hhi
  simp only [wsLoc, Region.lo] at hcta hlo hhi
  exact ⟨b, r, s, hcta, by omega, by omega⟩

/-- **Two chunk stores covering one byte are of one lane.** -/
theorem dq_same_lane {h k h' k' pcw pcw' : Nat} {ac ac' : Acc} {bs bs' : List Byte} {l : Loc}
    (hW : X.get (h, k) = some ⟨pcw, .wr ac bs⟩) (hat : MbarRow.DequantAt L h pcw)
    (hW' : X.get (h', k') = some ⟨pcw', .wr ac' bs'⟩) (hat' : MbarRow.DequantAt L h' pcw')
    (hc : ac.Covers l) (hc' : ac'.Covers l) : h = h' := by
  obtain ⟨b, r, s, hcta, hlo, hhi⟩ := dq_cover hp hX hFw hW hat hc
  obtain ⟨b', r', s', hcta', hlo', hhi'⟩ := dq_cover hp hX hFw hW' hat' hc'
  have hi := MemRow.dqChunk_lt (i := h % 128) (Nat.mod_lt _ (by decide)) r.isLt s.isLt
  have hi' := MemRow.dqChunk_lt (i := h' % 128) (Nat.mod_lt _ (by decide)) r'.isLt s'.isLt
  have ha := MemRow.dqChunk_al (i := h % 128) (r := r) (s := s) (Nat.mod_lt _ (by decide))
  have ha' := MemRow.dqChunk_al (i := h' % 128) (r := r') (s := s') (Nat.mod_lt _ (by decide))
  have hb := b.isLt
  have hb' := b'.isLt
  have hbb : b.val = b'.val := by
    have : MemRow.dqChunk (h % 128) r s + 16 ≤ 65536 := hi
    omega
  have hq : MemRow.dqChunk (h % 128) r s = MemRow.dqChunk (h' % 128) r' s' := by omega
  obtain ⟨h1, -, -⟩ := MemRow.dqChunk_inj (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    r.isLt r'.isLt hq
  obtain ⟨a, ha⟩ := deq_lane hp hat
  obtain ⟨a', ha'⟩ := deq_lane hp hat'
  have hb384 := hp.block
  simp only [deqLane, hb384] at ha ha'
  rw [hb384] at hcta hcta'
  have := a.isLt
  have := a'.isLt
  omega

/-- **Two chunk stores of dequant lanes are ordered**: of one lane, by program order. -/
theorem dq_ww {h k h' k' pcw pcw' : Nat} {ac ac' : Acc} {bs bs' : List Byte} {l : Loc}
    (hW : X.get (h, k) = some ⟨pcw, .wr ac bs⟩) (hat : MbarRow.DequantAt L h pcw)
    (hW' : X.get (h', k') = some ⟨pcw', .wr ac' bs'⟩) (hat' : MbarRow.DequantAt L h' pcw')
    (hc : ac.Covers l) (hc' : ac'.Covers l) (hne : (h, k) ≠ (h', k')) :
    ByteCausality L X l (.thread (h, k)) (.thread (h', k')) ∨
      ByteCausality L X l (.thread (h', k')) (.thread (h, k)) := by
  obtain rfl := dq_same_lane hp hX hFw hW hat hW' hat' hc hc'
  exact same_thread (we := true) (wf := true) (Or.inr (Or.inl ⟨bs, ⟨pcw, hW⟩, rfl⟩))
    (Or.inr (Or.inl ⟨bs', ⟨pcw', hW'⟩, rfl⟩)) (fun hk => hne (by rw [hk])) ⟨l, hc, hc'⟩ l

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
