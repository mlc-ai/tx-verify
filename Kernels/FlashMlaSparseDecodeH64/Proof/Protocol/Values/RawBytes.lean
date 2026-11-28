-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Raw.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Regions
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.Raw
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.GatherBytes
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Gather
import Lemmas.Order.ReadLast
import Lemmas.Protocol.UnitHandoff
import Lemmas.Tensor.LoadWritten
import Lemmas.Tensor.LoadWrittenZero

@[expose] public section

/-! # The bytes a dequant lane loads from a raw tile

A byte a dequant lane loads from raw tile `b` at use `v` is the byte written by the TMA gather of
that use that covers it (`raw_read_byte`): the lane's poll of `rawReady b` with `v` earlier ones
observes the completion of the sixteen gathers of the use (`rawReady_observes`), the gather `q`
whose 2304 bytes hold the byte is finished at the poll (`raw_finished`), so it wrote the byte
(`memWrites_of_notified_zero`) before the read; every other write of the byte is a gather of
another use, ordered with this one by the ring (`AsyncRing.rw_use`, `AsyncRing.ww_use`; two
gathers of one use at a byte are one, `raw_ww`), so the gather is the last write before the read
(`read_byte_of_last_write_ordered`). The gather writes slot `(x, y, z)` of its box, `x < 132`
(the load's column is below the row's 528 bytes, `dequant_rd`; a raw word's below 512, a scale
element's from 512); the slot's byte is
`gather_byte`'s (`Protocol/Values/GatherBytes.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : RawInputs L X)
include hp hX hFw hR hI hB hN

/-- **A byte a dequant lane loads from a raw tile is the byte its use's gather wrote.** -/
theorem raw_read_byte (hnu : NoUbInner L X) {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) (hat : MbarRow.DequantAt L g pc) {i : Nat}
    (hi : i < a.size) :
    ∃ gi ki pcg al : Nat, ∃ s : TensorCopy.Spec, ∃ o : TensorCopy.Observation,
      ∃ x y z : Nat, ∃ byte : Byte,
      X.get (gi, ki) = some ⟨pcg, .tensorIssue al s⟩ ∧ MbarRow.TmaAt L gi pcg ∧
      X.tensor (gi, ki) = some o ∧ o.effects.notified = true ∧ x < 132 ∧ y < 4 ∧ z < 4 ∧
      (a.size = 8 → 4 * x + z < 512) ∧ (a.size = 4 → 512 ≤ 4 * x + z) ∧
      TensorCopy.writeLoc s x y z = some (a.loc.at i) ∧
      TensorCopy.writeByte o x y z = some byte ∧ bs[i]? = some (some byte) ∧
      ∃ (b : Fin 2) (v q R c0 : Nat), q < 16 ∧ MemRow.SharedIn L (g / L.block) (.raw b) a ∧
        a.loc.addr = L.sharedBase + (Region.raw b).lo + (576 * R + c0) ∧ c0 + a.size ≤ 528 ∧
        (a.size = 8 → c0 + 8 ≤ 512) ∧ (a.size = 4 → 512 ≤ c0) ∧
        okPolls (mbarLoc L (g / L.block) (.rawReady b)) ((X.tr g).take k) = v + 1 ∧
        ((X.tr gi).take ki).countP (issuesTo (mbarLoc L (g / L.block) (.rawReady b))) =
          16 * v + q := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨b, hsh, ⟨R, c0, haddr, hc0, hr8, hr4⟩, v, hv1, hv2⟩ := dequant_rd hp hX hFw he hat
  have hcov : a.Covers (a.loc.at i) := Acc.covers_at hi
  have hLoc := MemRow.SharedIn.locIn hsh hcov
  have ring := raw_ring hp hX hFw hR hI hB hN hnu b
  obtain ⟨hls, hlc, hlo, hhi⟩ := id hLoc
  simp only [Region.lo, Region.size, Loc.at] at hlo hhi haddr
  -- the slot of the byte in its gather
  obtain ⟨q, hqd⟩ : ∃ q, q = (576 * R + c0 + i) / 2304 := ⟨_, rfl⟩
  obtain ⟨y, hyd⟩ : ∃ y, y = (576 * R + c0 + i) % 2304 / 576 := ⟨_, rfl⟩
  obtain ⟨x, hxd⟩ : ∃ x, x = (c0 + i) / 4 := ⟨_, rfl⟩
  obtain ⟨z, hzd⟩ : ∃ z, z = (c0 + i) % 4 := ⟨_, rfl⟩
  have hq16 : q < 16 := by omega
  have hx132 : x < 132 := by omega
  have hy4 : y < 4 := by omega
  have hz4 : z < 4 := by omega
  have hoff : 576 * R + c0 + i = 2304 * q + (576 * y + 4 * x + z) := by omega
  generalize hcd : g / L.block = c at *
  -- the poll of the use and the gathers it observes
  obtain ⟨j', pcj, par, acq, sc, hj', hw', hq⟩ := UnitHandoff.exists_poll (X := X)
    (m := mbarLoc L c (.rawReady b)) (h := g) (f := k) (c := v) (by omega)
  obtain ⟨⟨y0, hdeq⟩, -, hall⟩ := rawReady_observes hp hX hFw hR hI hB hN hw'
  obtain ⟨ig, pcg, alg, spg, hget, hmb, -, hcnt, -⟩ := hall ⟨q, hq16⟩
  rw [hq] at hcnt
  have hgT : tmaThread L X c < L.threads := Frame.lt_of_get hX hget
  have hT : RawTma L X c (tmaThread L X c) := ⟨hgT, rfl⟩
  have hat' : MbarRow.TmaAt L (tmaThread L X c) pcg := by
    rcases rawReady_use hR hgT hget hmb with ⟨n, hk⟩ | ⟨hat', -, -, -⟩ | ⟨-, -, ⟨ok, hk⟩⟩
    · cases hk
    · exact hat'
    · cases hk
  obtain ⟨-, b', q', hq', u', hmb', hsb, -, -, hcnt', hfree⟩ :=
    tma_gatherUse hp hX hFw hget hat' rfl
  have hcT : tmaThread L X c / L.block = c := rawTma_cta hp hT
  simp only [hcT] at hmb' hsb hcnt' hfree
  obtain ⟨-, hfam⟩ := fam_eq (hmb.symm.trans hmb')
  obtain rfl : b = b' := by simpa using hfam
  have h2 : 16 * v + q = 16 * u' + q' := hcnt.symm.trans hcnt'
  obtain ⟨rfl, rfl⟩ : v = u' ∧ q = q' := by omega
  -- the gather finished at the poll wrote the byte
  have hfin := raw_finished hp hX hFw hR hI hB hN (x := x) (y := y) (j' := z) hq16 hT
    ⟨hg, y0, hdeq⟩ hget hmb hcnt hw' hq
  obtain ⟨o, ho, hn⟩ := tensor_notified_of_finished hfin
  have hos : o.spec = spg := by
    obtain ⟨⟨addr, pc', hiss⟩, -, -⟩ := hX.tensor _ o ho
    rw [hget] at hiss
    obtain ⟨-, hk⟩ := Event.mk.inj (Option.some.inj hiss)
    exact (Kind.tensorIssue.inj hk).2.symm
  have hwl : TensorCopy.writeLoc spg x y z = some (a.loc.at i) := by
    rw [gather_writeLoc hp hX hFw hget hat' (by omega) hy4 hz4, hsb]
    congr 1
    simp only [Loc.at, Loc.mk.injEq]
    exact ⟨hls.symm, hlc.symm, by omega⟩
  obtain ⟨hz0, hf32⟩ := gather_fill hp hX hFw hget hat'
  have hwl' : TensorCopy.writeLoc o.spec x y z = some (a.loc.at i) := by rw [hos]; exact hwl
  have hz' : o.spec.descriptor.fill = .zero := by rw [hos]; exact hz0
  have hf' : o.spec.descriptor.format ≠ .f64 := by rw [hos, hf32]; decide
  obtain ⟨byte, hwb⟩ := writeByte_of_notified_zero hX ho hn hwl' hz' hf'
  obtain ⟨⟨addr, hIssue⟩, -, -⟩ := hX.tensor (tmaThread L X c, ig) o ho
  have hw0 : X.MemWrites (.async (tmaThread L X c, ig) (.write (.load x y z)))
      { loc := a.loc.at i, size := 1 } [byte] :=
    ⟨o, addr, byte, ho, hIssue, hwl', hwb, rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- the write is the last one before the read
  have hlr : ∃ c', MemRow.LocIn L c' (.raw b) (a.loc.at i) := ⟨c, hLoc⟩
  have hr : X.Access (g, k) a false := Or.inl ⟨bs, ⟨pc, he⟩, rfl⟩
  have hca : ({ loc := a.loc.at i, size := 1 } : Acc).Covers (a.loc.at i) :=
    Acc.covers_at (k := 0) (show 0 < 1 by decide)
  have hv1' : okPolls (mbarLoc L (a.loc.at i).cta (.rawReady b)) ((X.tr g).take k) = v + 1 := by
    rw [hlc]; exact hv1
  have hu1' : okPolls (mbarLoc L (a.loc.at i).cta (.rawFree b)) ((X.tr (tmaThread L X c)).take ig) =
      v + 1 := by
    rw [hlc]; exact hfree
  have hv : ByteCausality L X (a.loc.at i) (.async (tmaThread L X c, ig) (.write (.load x y z)))
      (.thread (g, k)) :=
    (ring.rw_use hr hw0.intent hcov hca hlr hv1' hu1').1 le_rfl
  have hall : ∀ w' dst' bytes, X.MemWrites w' dst' bytes → dst'.Covers (a.loc.at i) →
      w' = .async (tmaThread L X c, ig) (.write (.load x y z)) ∨
        ByteCausality L X (a.loc.at i) w'
          (.async (tmaThread L X c, ig) (.write (.load x y z))) ∨
        ByteCausality L X (a.loc.at i) (.thread (g, k)) w' := by
    intro w' dst' bytes hw' hc'
    have hint := hw'.intent
    rcases w' with ⟨g', k'⟩ | ⟨⟨g', k'⟩, p'⟩
    · exfalso
      obtain ⟨hfalse, -⟩ := ring.hrd g' k' dst' true _ hint hc' hlr
      cases hfalse
    · obtain ⟨-, ⟨t, rfl⟩, -, -, u', hu', -⟩ := ring.hwr g' k' _ dst' true _ hint hc' hlr
      rcases lt_trichotomy u' v with h | h | h
      · exact .inr (.inl (ring.ww_use hint hw0.intent hc' hca hlr
          (by simpa only [hlc] using hu') hu1' h))
      · subst h
        obtain ⟨rfl, rfl, hpp⟩ := ring.hww g' k' _ (tmaThread L X c) ig _ dst' _ _ hint
          hw0.intent hc' hca hlr (by simpa only [hlc] using hu'.trans hu1'.symm)
        obtain rfl := Part.write.inj hpp
        exact .inl rfl
      · exact .inr (.inr ((ring.rw_use hr hint hcov hc' hlr hv1'
          (by simpa only [hlc] using hu')).2 h))
  have hmr : X.MemReads (.thread (g, k)) a bs := Or.inl ⟨pc, he⟩
  have key := read_byte_of_last_write_ordered hX hmr hi hw0 hca hv hall
  refine ⟨tmaThread L X c, ig, pcg, alg, spg, o, x, y, z, byte, hget, hat', ho, hn, hx132, hy4,
    hz4, fun h8 => by have := hr8 h8; omega, fun h4 => by have := hr4 h4; omega, hwl, hwb, ?_⟩
  refine ⟨?_, b, v, q, R, c0, hq16, hsh, haddr, hc0, hr8, hr4, hv1, ?_⟩
  · simpa only [wbyte, Nat.sub_self, List.getElem?_cons_zero] using key
  · exact hcnt

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
