-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.DqValue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Numeric.Dequant
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.DqVisible
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Chunks
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Value
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.WrSite
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaBytePair
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Dq
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Lag
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Observe
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.DqClass
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.DqCover
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.DqWw
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.QueryTile
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.StageEpi
import Lemmas.Flow.NthEv
import Lemmas.Order.ReadLast
import Lemmas.Protocol.UnitHandoff
import Lemmas.Tcgen05.MmaObservedReads
import Lemmas.Tcgen05.MmaOperandObservations
import Lemmas.Tcgen05.TcMmaIdealEval

@[expose] public section

/-! # The B elements an MMA reads from a dequantized tile are numbers

The two bytes `2 m`, `2 m + 1` of a 16-bit B element of an MMA that reads the tile `b0` are
adjacent bytes of one 16-byte chunk (`byteLoc_pair`), written by one chunk store (`dq_b_store`
for each byte; the store of the use is the last one covering either byte), whose bytes are those
of `dequantChunk x b` (`dq_store_value`, valid data), so they are the two bytes of one bf16 number
(`dq_b_elem`). -/

/-! # The B byte of an MMA is the byte of the last chunk store of its use

A byte of the dequantized tile `b0` an MMA reads as B, when the MMA has `u' + 1` polls of
`dequantReady b0`, is the byte of the lane's last chunk store covering it with `u'` earlier
arrivals (`dq_b_store`): the lane is the one that stores the byte (`dq_same_lane`); its stores of
the use are ordered by program order, those of earlier uses are before that store, those of later
uses are after the read (`dq_use_split`), the query load is before it (`q_tload_dq`) and the
staging stores after the read (`mma_stage`). -/

/-! # A chunk store and an MMA read of its use, split by the use

A dequant lane's chunk store `W` with `u` earlier arrivals on `dequantReady b0` and an MMA read of
tile `b0` with `u' + 1` polls of it: for `u ≤ u'` the store is before the read (`dq_before`,
a model path), for `u' < u` the read is before the store (`dq_after`). Both facts of `dq_mma`,
split by the uses (`dq_use_split`); and a chunk store of the use `u'` covering the byte exists
(`dq_use_store`, the body of `dq_visible`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow PTX.AsyncCopy

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X)
include hp hX hFw hR hI hB hN

/-- **A chunk store and an MMA read, ordered by their uses.** -/
theorem dq_use_split {h k g i pcw pc bb idx u u' : Nat} {ac : Acc} {bs : List Byte}
    {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat} {isB : Bool} {l : Loc} {b0 : Fin 2}
    (hW : X.get (h, k) = some ⟨pcw, .wr ac bs⟩) (hat : MbarRow.DequantAt L h pcw)
    (hcov : ac.Covers l) (hx : X.get (g, i) = some ⟨pc, .tc (.mma bb sp acc mask)⟩)
    (hatm : MbarRow.MmaAt L g pc) (hf : X.MmaFootprint (g, i) isB idx l)
    (hlg : MemRow.LocIn L (g / L.block) (.dequant b0) l)
    (hwu : arrivals (mbarLoc L (h / L.block) (.dequantReady b0)) ((X.tr h).take k) = u)
    (hmu : okPolls (mbarLoc L (g / L.block) (.dequantReady b0)) ((X.tr g).take i) = u' + 1) :
    (u ≤ u' → modelCausality L X l (.thread (h, k)) (.async (g, i) (.mmaRead isB idx))) ∧
      (u' < u → ByteCausality L X l (.async (g, i) (.mmaRead isB idx)) (.thread (h, k))) := by
  obtain ⟨bw, r, s', u0, hws, hpol, harr, -⟩ := dequant_wrUse hp hX hFw hW hat
  have hlt := MemRow.dqChunk_lt (i := h % 128) (Nat.mod_lt _ (by decide)) r.isLt s'.isLt
  have hlw : MemRow.LocIn L (h / L.block) (.dequant bw) l :=
    (MemRow.wsAcc_in hws (Nat.le_add_right _ _) (by simp only [Region.size]; omega)).locIn hcov
  obtain ⟨hcc, hb⟩ := locIn_eq hlw hlg
  obtain rfl : bw = b0 := by injection hb
  obtain ⟨a, ha⟩ := deq_lane hp hat
  obtain ⟨hpcm, u1, hpm, hcmm⟩ := mma_dqUse hp hX hFw hx hatm hf hlg
  have hon : MmaOn L g pc := ⟨hatm, hpcm⟩
  have hg : g = mmaLane L X (g / L.block) :=
    laneOn_eq (mmaOne hp hX hFw) hx (fun _ h => by cases h) hon
  have hu0 : u0 = u := by rw [← harr, hwu]
  have hu1 : u1 = u' := by omega
  subst hu0 hu1
  generalize hcd : h / L.block = c at *
  subst ha
  rw [← hcc] at hg
  subst hg
  obtain ⟨hls, hlcm, -, -⟩ := id hlg
  have hmc : mmaLane L X c / L.block = c := hcc.symm
  rw [hmc] at hpm hcmm
  have hlc : l.cta = c := by rw [hlcm, hmc]
  exact ⟨fun hle => dq_before hp hX hFw hR hI hB hN hW harr hx (by omega) hf hls hlc hmc,
    fun hlt' => dq_after hp hX hFw hR hI hB hN hW hpol hx hmc (by omega) hf hls ⟨pcw, hW⟩ hcov⟩

/-- **A chunk store of the MMA's use covers each byte of its tile**: of lane `a` of the CTA, with
`u'` earlier arrivals on `dequantReady b0` when the MMA has `u' + 1` polls of it. -/
theorem dq_use_store {g i pc bb idx u' : Nat} {sp : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {isB : Bool} {l : Loc} {b0 : Fin 2}
    (hx : X.get (g, i) = some ⟨pc, .tc (.mma bb sp acc mask)⟩) (hatm : MbarRow.MmaAt L g pc)
    (hf : X.MmaFootprint (g, i) isB idx l) (hl : MemRow.LocIn L (g / L.block) (.dequant b0) l)
    (hmu : okPolls (mbarLoc L (g / L.block) (.dequantReady b0)) ((X.tr g).take i) = u' + 1) :
    ∃ h k pcw ac bs, X.get (h, k) = some ⟨pcw, .wr ac bs⟩ ∧ MbarRow.DequantAt L h pcw ∧
      ac.Covers l ∧ h / L.block = g / L.block ∧
      arrivals (mbarLoc L (g / L.block) (.dequantReady b0)) ((X.tr h).take k) = u' := by
  obtain ⟨hpcm, u, hpm, -⟩ := mma_dqUse hp hX hFw hx hatm hf hl
  have hon : MmaOn L g pc := ⟨hatm, hpcm⟩
  have hg : g = mmaLane L X (g / L.block) :=
    laneOn_eq (mmaOne hp hX hFw) hx (fun _ h => by cases h) hon
  obtain ⟨hls, hlcm, hlo, hhi⟩ := id hl
  obtain ⟨i0, r0, q0, hi0, hr0, hq0, hc1, hc2⟩ := dqChunk_cover
    (t := l.addr - L.sharedBase - (Region.dequant b0).lo) (by
      simp only [Region.lo, Region.size] at hlo hhi ⊢
      omega)
  have hu : u = u' := by omega
  subst hu
  generalize hcd : g / L.block = c at *
  have hlane : deqLane L c ⟨i0, hi0⟩ % 128 = i0 := by
    simp only [deqLane, hp.block]
    omega
  subst hg
  obtain ⟨jw, pcp, p, acq, sc, hjw, hget, hq⟩ := UnitHandoff.exists_poll
    (m := mbarLoc L c (.dequantReady b0)) (h := mmaLane L X c) (f := i) (c := u) hpm.ge
  have hobs := dequantReady_observes hp hX hFw hR hI hB hN hget
  obtain ⟨ia, pca, sca, hga, hca, -⟩ := hobs.2 ⟨i0, hi0⟩
  obtain ⟨j, hj, pcw, ac, bs, hW, hat, hws, hcnt⟩ := dequant_chunks hp hX hFw
    (deqLane_warp hp c ⟨i0, hi0⟩) hga ⟨r0, hr0⟩ ⟨q0, hq0⟩
  rw [deqLane_cta hp c ⟨i0, hi0⟩, hlane] at hws
  have hcov : ac.Covers l := by
    obtain ⟨hw1, hw2⟩ := hws
    rw [Acc.Covers, hw1, hw2]
    simp only [Loc.InRange, wsLoc, Region.lo, Region.size, MemRow.dqChunk] at hc1 hc2 hlo hhi ⊢
    refine ⟨hls, hlcm, ?_, ?_⟩ <;> omega
  exact ⟨deqLane L c ⟨i0, hi0⟩, j, pcw, ac, bs, hW, hat, hcov, by rw [deqLane_cta hp c ⟨i0, hi0⟩],
    by rw [hcnt, hca, hq]⟩

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow PTX.AsyncCopy

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- Two chunk stores of one lane covering a byte are ordered by program order. -/
private theorem dq_po {h k k' pcw pcw' : Nat} {ac ac' : Acc} {bs bs' : List Byte} {l : Loc}
    (hW : X.get (h, k') = some ⟨pcw', .wr ac' bs'⟩) (hW' : X.get (h, k) = some ⟨pcw, .wr ac bs⟩)
    (hc' : ac'.Covers l) (hc : ac.Covers l) (hlt : k' < k) :
    ByteCausality L X l (.thread (h, k')) (.thread (h, k)) :=
  .direct (.of_base L (.single (.inl (po_of_overlap (we := true) (wf := true)
    (Or.inr (Or.inl ⟨bs', ⟨pcw', hW⟩, rfl⟩)) (Or.inr (Or.inl ⟨bs, ⟨pcw, hW'⟩, rfl⟩)) rfl hlt
    ⟨l, hc', hc⟩))))

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X)
include hp hX hFw hR hI hB hN

/-- **The B byte an MMA reads from a dequantized tile** is the byte of a chunk store of use `u'`:
the store `(h, k)` covers the byte, has `u'` earlier arrivals on `dequantReady b0`, and the byte
the MMA observed is its byte. -/
theorem dq_b_store {g i pc bb idx u' : Nat} {sp : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {l : Loc} {b0 : Fin 2} {ops : MmaOperands}
    (hx : X.get (g, i) = some ⟨pc, .tc (.mma bb sp acc mask)⟩) (hatm : MbarRow.MmaAt L g pc)
    (hops : X.async.mmaOperands (g, i) = some ops) (hl : sp.byteLoc .b idx = some l)
    (hlg : MemRow.LocIn L (g / L.block) (.dequant b0) l)
    (hmu : okPolls (mbarLoc L (g / L.block) (.dequantReady b0)) ((X.tr g).take i) = u' + 1) :
    ∃ h k pcw ac bs, X.get (h, k) = some ⟨pcw, .wr ac bs⟩ ∧ MbarRow.DequantAt L h pcw ∧
      ac.Covers l ∧ h / L.block = g / L.block ∧
      arrivals (mbarLoc L (g / L.block) (.dequantReady b0)) ((X.tr h).take k) = u' ∧
      ops.b[idx]? = some (wbyte ac bs l) ∧
      ∀ k', (∃ pcw' ac' bs', X.get (h, k') = some ⟨pcw', .wr ac' bs'⟩ ∧
        MbarRow.DequantAt L h pcw' ∧ ac'.Covers l ∧
        arrivals (mbarLoc L (g / L.block) (.dequantReady b0)) ((X.tr h).take k') = u') →
        k' ≤ k := by
  classical
  obtain ⟨obs, hread, hobs⟩ := hX.mma_read_exists (isB := true) ⟨pc, hx⟩ hops hl
  have hf : X.MmaFootprint (g, i) true idx l := hread.1
  obtain ⟨h0, k0, pcw0, ac0, bs0, hW0, hat0, hcov0, hc0, hu0⟩ :=
    dq_use_store hp hX hFw hR hI hB hN hx hatm hf hlg hmu
  let Q : Nat → Prop := fun j => ∃ pcw ac bs, X.get (h0, j) = some ⟨pcw, .wr ac bs⟩ ∧
    MbarRow.DequantAt L h0 pcw ∧ ac.Covers l ∧
    arrivals (mbarLoc L (g / L.block) (.dequantReady b0)) ((X.tr h0).take j) = u'
  have hlen : ∀ {j pc' kd}, X.get (h0, j) = some ⟨pc', kd⟩ → j ≤ (X.tr h0).length :=
    fun h => (List.getElem?_eq_some_iff.mp h).1.le
  have hQ0 : Q k0 := ⟨pcw0, ac0, bs0, hW0, hat0, hcov0, hu0⟩
  have hQm := Nat.findGreatest_spec (P := Q) (hlen hW0) hQ0
  obtain ⟨pcw, ac, bs, hW, hat, hcov, hu⟩ := hQm
  have hle : ∀ j, Q j → j ≤ Nat.findGreatest Q (X.tr h0).length := by
    intro j hj
    obtain ⟨_, _, _, hg, -⟩ := id hj
    exact Nat.le_findGreatest (hlen hg) hj
  generalize hkm : Nat.findGreatest Q (X.tr h0).length = km at *
  have hv : ByteCausality L X l (.thread (h0, km)) (.async (g, i) (.mmaRead true idx)) :=
    .direct ((dq_use_split hp hX hFw hR hI hB hN hW hat hcov hx hatm hf hlg
      (by rw [hc0]; exact hu) hmu).1 le_rfl)
  have hrd : X.MemReads (.async (g, i) (.mmaRead true idx)) { loc := l, size := 1 } [obs] :=
    ⟨obs, hread, rfl, rfl⟩
  have hall : ∀ w' dst' bytes, X.MemWrites w' dst' bytes →
      dst'.Covers (({ loc := l, size := 1 } : Acc).loc.at 0) →
      w' = .thread (h0, km) ∨ ByteCausality L X (({ loc := l, size := 1 } : Acc).loc.at 0) w'
        (.thread (h0, km)) ∨ ByteCausality L X (({ loc := l, size := 1 } : Acc).loc.at 0)
        (.async (g, i) (.mmaRead true idx)) w' := by
    intro w' dst' bytes hw' hcw'
    have hcw : dst'.Covers l := by simpa [Loc.at] using hcw'
    by_cases hwe : w' = .thread (h0, km)
    · exact .inl hwe
    right
    simp only [Loc.at, Nat.add_zero]
    cases hcl : dq_classify hp hX hFw hw'.intent hcw hlg with
    | dq hW' hat' hcov' hc' =>
      rename_i h' k' pcw' ac' bs'
      obtain rfl : h' = h0 := dq_same_lane hp hX hFw hW' hat' hW hat hcov' hcov
      obtain ⟨bw, r, s', u'', hws, hpol, harr, -⟩ := dequant_wrUse hp hX hFw hW' hat'
      have hlt := MemRow.dqChunk_lt (i := h' % 128) (Nat.mod_lt _ (by decide)) r.isLt s'.isLt
      have hlw : MemRow.LocIn L (h' / L.block) (.dequant bw) l :=
        (MemRow.wsAcc_in hws (Nat.le_add_right _ _)
          (by simp only [Region.size]; omega)).locIn hcov'
      obtain ⟨-, hb⟩ := locIn_eq hlw hlg
      obtain rfl : b0 = bw := by injection hb.symm
      rw [hc0] at harr
      rcases Nat.lt_trichotomy u'' u' with hlt1 | heq | hgt
      · refine .inl (dq_po hW' hW hcov' hcov ?_)
        by_contra hnl
        have hk : km ≤ k' := by omega
        have := countP_take_mono (arrivesOn (mbarLoc L (g / L.block) (.dequantReady b0)))
          (X.tr h') hk
        simp only [arrivals] at harr hu
        omega
      · have hQ' : Q k' := ⟨pcw', ac', bs', hW', hat', hcov', by rw [← heq]; exact harr⟩
        have hk := hle k' hQ'
        refine .inl (dq_po hW' hW hcov' hcov ?_)
        by_contra hnl
        exact hwe (by rw [show k' = km by omega])
      · exact .inr ((dq_use_split hp hX hFw hR hI hB hN hW' hat' hcov' hx hatm hf hlg
          (by rw [hc0]; exact harr) hmu).2 hgt)
    | stage hS hatS hr hst hcovS hc' =>
      exact .inr (mma_stage hp hX hFw hR hI hB hN hx hatm hf hlg hc' hS hatS hst hcovS)
    | tload hr hT hatT hrl hc' =>
      have hl0 : MemRow.LocIn L (g / L.block) (.dequant 0) l := hr ▸ hlg
      exact .inl (q_tload_dq hp hX hFw hR hI hB hT hatT hw'.intent hcw (by rw [hc']; exact hl0)
        hW hat hcov
        (by rw [hc0, hc']))
  have hrb := read_byte_of_last_write_ordered hX hrd (k := 0) Nat.zero_lt_one
    (show X.MemWrites (.thread (h0, km)) ac bs from .inl ⟨pcw, hW⟩)
    (by simpa [Loc.at] using hcov) (by simpa [Loc.at] using hv) hall
  have hbo : obs = wbyte ac bs l := by simpa [wbyte, Loc.at] using hrb
  exact ⟨h0, km, pcw, ac, bs, hW, hat, hcov, hc0, hu, by rw [← hbo]; simpa using hobs, hle⟩

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow PTX.AsyncCopy
open PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Numeric.Dequant

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A chunk store's access is 16-byte aligned and 16 bytes. -/
private theorem wsAcc_al {c r s h : Nat} {b : Fin 2} {ac : Acc} (hSB : L.sharedBase % 16 = 0)
    (hws : MemRow.WsAcc L c ((Region.dequant b).lo + MemRow.dqChunk (h % 128) r s) 16 ac) :
    ac.loc.addr % 16 = 0 ∧ ac.size = 16 := by
  obtain ⟨hl, hs⟩ := hws
  have := MemRow.dqChunk_al (i := h % 128) (r := r) (s := s) (Nat.mod_lt _ (by decide))
  refine ⟨?_, hs⟩
  rw [hl]
  simp only [wsLoc, Region.lo]
  omega

/-- A byte pair of an even address in a 16-byte chunk covers both bytes or neither. -/
private theorem covers_succ {ac : Acc} (h16 : ac.loc.addr % 16 = 0) (hs : ac.size = 16) {l : Loc}
    (hev : l.addr % 2 = 0) :
    (ac.Covers l → ac.Covers ⟨l.space, l.cta, l.addr + 1⟩) ∧
      (ac.Covers ⟨l.space, l.cta, l.addr + 1⟩ → ac.Covers l) := by
  unfold Acc.Covers Loc.InRange
  rw [hs]
  constructor <;> intro h <;> refine ⟨h.1, h.2.1, ?_, ?_⟩ <;> dsimp only at h ⊢ <;> omega

private theorem flat8 (e : Nat → ℝ) (q : Nat) (hq : q < 8) :
    ((List.range 8).flatMap fun i => (Value.float .bf16 (e i)).toBytes)[2 * q]? =
        some ((Value.float .bf16 (e q)).byteAt 0) ∧
      ((List.range 8).flatMap fun i => (Value.float .bf16 (e i)).toBytes)[2 * q + 1]? =
        some ((Value.float .bf16 (e q)).byteAt 1) := by
  interval_cases q <;> exact ⟨rfl, rfl⟩

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X)
  (hv : ∀ h k, NoUbBefore X h k → DqValid X h k)
include hp hX hFw hR hI hB hN hv

/-- **A B element of an MMA that reads a dequantized tile is a bf16 number** (valid data): the two
bytes `2 m`, `2 m + 1` of the operand are the bytes of the bf16 number
`e4m3Val x * ue8m0Val b` of the chunk store of the use. -/
theorem dq_b_elem {g i pc bb u' : Nat} {sp : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {l : Loc} {b0 : Fin 2} {ops : MmaOperands}
    (hx : X.get (g, i) = some ⟨pc, .tc (.mma bb sp acc mask)⟩) (hatm : MbarRow.MmaAt L g pc)
    (hops : X.async.mmaOperands (g, i) = some ops) {n : Nat}
    (hk : sp.descriptor.kind = .f16 .bf16 .f32)
    (hd : sp.b.start % 2 = 0 ∧ sp.b.leading % 2 = 0 ∧ sp.b.stride % 2 = 0)
    (hl : sp.byteLoc .b (2 * n) = some l)
    (hlg : MemRow.LocIn L (g / L.block) (.dequant b0) l)
    (hmu : okPolls (mbarLoc L (g / L.block) (.dequantReady b0)) ((X.tr g).take i) = u' + 1) :
    ∃ x : ℝ, (ops.b.drop (2 * n)).take 2 = (Value.float .bf16 x).toBytes.map some ∧
      ∃ (h k pcw : Nat) (ac : Acc) (bs : List Byte) (bw : Fin 2) (r : Fin 4) (s : Fin 8) (j : Nat),
        X.get (h, k) = some ⟨pcw, .wr ac bs⟩ ∧ pcw = dqStorePc r s ∧
        h / L.block = g / L.block ∧
        MemRow.WsAcc L (h / L.block) ((Region.dequant bw).lo + MemRow.dqChunk (h % 128) r s) 16 ac ∧
        arrivals (mbarLoc L (g / L.block) (.dequantReady b0)) ((X.tr h).take k) = u' ∧
        ac.Covers l ∧ j < 8 ∧ l.addr = ac.loc.addr + 2 * j ∧
        x = e4m3Val (Numeric.Dequant.byteAt (rawWordOf (lastAt X h k (dqRawPc r s) 1)) j) *
          ue8m0Val (Numeric.Dequant.byteAt (scaleWordOf (lastAt X h k (dqScalePc r) 4))
            (2 * s + if h % 8 < 4 then 0 else 1)) := by
  have hSB : L.sharedBase % 16 = 0 := by
    have := hp.sharedAlignment
    rw [← hp.sharedBase] at this
    omega
  obtain ⟨hl', hev⟩ := MmaFoot.byteLoc_pair (op := .b) hk hd hl
  have hlg' : MemRow.LocIn L (g / L.block) (.dequant b0)
      (⟨l.space, l.cta, l.addr + 1⟩ : Loc) := by
    obtain ⟨h1, h2, h3, h4⟩ := hlg
    refine ⟨h1, h2, ?_, ?_⟩ <;> simp only [Region.lo, Region.size] at h3 h4 ⊢ <;>
      omega
  obtain ⟨h, k, pcw, ac, bs, hW, hat, hcov, hc, hu, hob, hmax⟩ :=
    dq_b_store hp hX hFw hR hI hB hN hx hatm hops hl hlg hmu
  obtain ⟨h', k', pcw', ac', bs', hW', hat', hcov', hc', hu', hob', hmax'⟩ :=
    dq_b_store hp hX hFw hR hI hB hN hx hatm hops hl' hlg' hmu
  obtain ⟨bw, r, s, hpc, hws⟩ := dequant_wrSite hp hX hFw hW hat
  obtain ⟨h16, hs16⟩ := wsAcc_al hSB hws
  have hcov2 : ac.Covers ⟨l.space, l.cta, l.addr + 1⟩ := (covers_succ h16 hs16 hev).1 hcov
  obtain rfl : h = h' := (dq_same_lane hp hX hFw hW' hat' hW hat hcov' hcov2).symm
  obtain ⟨bw', r', s', hpc', hws'⟩ := dequant_wrSite hp hX hFw hW' hat'
  obtain ⟨h16', hs16'⟩ := wsAcc_al hSB hws'
  have hcov1' : ac'.Covers l := (covers_succ h16' hs16' hev).2 hcov'
  have hkk : k = k' := le_antisymm
    (hmax' k ⟨pcw, ac, bs, hW, hat, hcov2, hu⟩) (hmax k' ⟨pcw', ac', bs', hW', hat', hcov1', hu'⟩)
  subst hkk
  rw [hW] at hW'
  obtain ⟨rfl, rfl, rfl⟩ : pcw = pcw' ∧ ac = ac' ∧ bs = bs' := by
    obtain ⟨h1, h2⟩ := Event.mk.inj (Option.some.inj hW')
    obtain ⟨h3, h4⟩ := Kind.wr.inj h2
    exact ⟨h1, h3, h4⟩
  have hval := dq_store_value hp hX hFw ⟨hat.1, hat.2.1⟩ hW r.isLt s.isLt hpc
    (hv h k (noUbBefore_of_get hX hW)) ac bs rfl
  have hbyte := flat8 (fun i => e4m3Val (byteAt (rawWordOf (lastAt X h k (dqRawPc r s) 1)) i) *
    ue8m0Val (byteAt (scaleWordOf (lastAt X h k (dqScalePc r) 4))
      (2 * s + if h % 8 < 4 then 0 else 1))) ((l.addr - ac.loc.addr) / 2) (by
    obtain ⟨-, -, hlo, hhi⟩ := hcov
    omega)
  rw [dequantChunk_toBytes] at hval
  have hcov0 := hcov
  obtain ⟨-, -, hlo, hhi⟩ := hcov
  have hq : 2 * ((l.addr - ac.loc.addr) / 2) = l.addr - ac.loc.addr := by omega
  rw [hq] at hbyte
  have e1 : l.addr + 1 - ac.loc.addr = l.addr - ac.loc.addr + 1 := by omega
  refine ⟨e4m3Val (byteAt (rawWordOf (lastAt X h k (dqRawPc r s) 1))
    ((l.addr - ac.loc.addr) / 2)) * ue8m0Val (byteAt (scaleWordOf (lastAt X h k (dqScalePc r) 4))
      (2 * s + if h % 8 < 4 then 0 else 1)), ?_, h, k, pcw, ac, bs, bw, r, s,
    (l.addr - ac.loc.addr) / 2, hW, hpc, hc, hws, hu, hcov0, by omega, by omega, rfl⟩
  simp only [wbyte, e1, hval, hbyte.1, hbyte.2] at hob hob'
  rw [TcMma.take_two hob hob']
  rfl

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
