-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Reads
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.Ring
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Lag
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.PvStore
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Use
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Dq
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Mem
import Lemmas.Protocol.StagingHandoff
import Lemmas.Protocol.UnitHandoff
import Lemmas.Tcgen05.MmaObservedReads

@[expose] public section

/-! # A dequant lane's chunk store and an MMA's read of the tile

A dequant lane's chunk store `W` into tile `b` (use `u` of the slot: `u + 1` polls of `svDone b`,
`u` arrivals on `dequantReady b`, `dequant_wrUse`) and the asynchronous read of a QK or PV MMA of
the CTA's MMA lane of the same tile (use `u'`: `u' + 1` polls of `dequantReady b`, `u'` commits to
`svDone b`, `mma_dqUse`) are ordered:

* `u ≤ u'` (`dq_before`): the lane's proxy fence before its arrival of use `u` on `dequantReady b`
  (`dequant_readyFence`) follows `W`, and the MMA lane's poll of use `u` before the MMA observes
  the arrival (`dequantReady_observes`): `Publish` (`ProxyBefore W A`);
* `u' < u` (`dq_after`): the lane's poll of `svDone b` for use `u - 1` before `W` observes the
  notification of the commit `u - 1`, after the MMA in the MMA lane's program order (it has
  `u' ≤ u - 1` earlier commits), so the MMA is done before `W`
  (`completed_mma_source_before_store`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow PTX.AsyncCopy

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- An arrival on an mbarrier of the rows is a release of CTA scope. -/
private theorem arrive_cta' (hX : Consistent L kernel Assumptions.all m X) (hR : MbarRows P L X)
    {w : EvId} {pc tx n : Nat} {l : Loc} {rel : Bool} {sc : MbarScope}
    (he : X.get w = some ⟨pc, .arrive l tx n rel sc⟩) : sc = .cta := by
  rcases mbar_kind hX hR he rfl with ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, _, hc⟩ | ⟨_, hc, -⟩ |
    ⟨_, _, _, hc, -⟩
  · cases hc
  · cases hc
    rfl
  · cases hc
  · cases hc
  · cases hc

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X)
include hp hX hFw hR hI hB hN

/-- **The write first**: a dequant lane's chunk store of use `u` is ordered before an MMA's read of
use `u' ≥ u`. -/
theorem dq_before {c k i u pcw pc bb idx : Nat} {a : Fin 128} {s : Fin 2} {ac : Acc}
    {bs : List Byte} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat} {isB : Bool}
    {l : Loc} (hW : X.get (deqLane L c a, k) = some ⟨pcw, .wr ac bs⟩)
    (hWa : arrivals (mbarLoc L c (.dequantReady s)) ((X.tr (deqLane L c a)).take k) = u)
    (hx : X.get (mmaLane L X c, i) = some ⟨pc, .tc (.mma bb sp acc mask)⟩)
    (hpol : u + 1 ≤ okPolls (mbarLoc L c (.dequantReady s)) ((X.tr (mmaLane L X c)).take i))
    (hf : X.MmaFootprint (mmaLane L X c, i) isB idx l) (hls : l.space = .shared)
    (hlc : l.cta = c) (hmc : mmaLane L X c / L.block = c) :
    modelCausality L X l (.thread (deqLane L c a, k))
      (.async (mmaLane L X c, i) (.mmaRead isB idx)) := by
  have hh : deqLane L c a < L.threads := Frame.lt_of_get hX hW
  have hg' : mmaLane L X c < L.threads := Frame.lt_of_get hX hx
  have hil : i < (X.tr (mmaLane L X c)).length := (List.getElem?_eq_some_iff.mp hx).1
  obtain ⟨jw, pcp, p, acq, sc, hjw, hget, hq⟩ := UnitHandoff.exists_poll hpol
  obtain ⟨-, hall⟩ := dequantReady_observes hp hX hFw hR hI hB hN hget
  obtain ⟨ia, pca, sca, hga, hca, hobs⟩ := hall a
  rw [hq] at hca
  obtain ⟨rfl, rfl⟩ := mbarWait_cta hX hR hget
  obtain rfl := arrive_cta' hX hR hga
  have hki : k ≤ ia := arrival_index_ge hga (by simp [arrivesOn, sourceArrive]) hca hWa.le
  obtain ⟨jf, hia, hfence⟩ := dequant_readyFence hp hX hFw (deqLane_warp hp c a) hga
  obtain ⟨pcf, hfg⟩ := hfence
  have hkjf : k < jf := by
    have hn1 : k ≠ ia := fun h1 => by
      rw [h1, hga] at hW
      cases hW
    have hn2 : k ≠ jf := fun h1 => by
      rw [h1, hfg] at hW
      cases hW
    omega
  have hflen : jf < (X.tr (deqLane L c a)).length := (List.getElem?_eq_some_iff.mp hfg).1
  have hsc : ScopesMeet L .cta (deqLane L c a) .cta (mmaLane L X c) :=
    ⟨⟨hh, hg', by rw [deqLane_cta hp c a, hmc]⟩, hg', hh,
      by rw [deqLane_cta hp c a, hmc]⟩
  have hpub : Staging.Publish L X (deqLane L c a, k) (deqLane L c a, jf) (deqLane L c a, ia)
      (mmaLane L X c, jw) (mmaLane L X c, i) (mbarLoc L c (.dequantReady s)) :=
    ⟨⟨pcf, hfg⟩, hh, .single (.inl ⟨rfl, hkjf, hflen, fun hs => by
      have h1 := hs.1
      rw [hfg] at h1
      simp [Event.acc] at h1⟩), ⟨.cta, ⟨0, 1, pca, hga⟩, .cta, hobs, hsc⟩, ⟨rfl, by omega⟩,
      ⟨rfl, hjw, hil⟩, ⟨hh, hg', by rw [deqLane_cta hp c a, hmc]⟩⟩
  exact hpub.modelCausality hls (by rw [hlc, deqLane_cta hp c a])
    ⟨{ loc := l, size := 1 }, false, ⟨rfl, rfl, hf⟩, Acc.covers_at (k := 0) (show 0 < 1 by decide)⟩

/-- **The MMA first**: an MMA of the MMA lane with at most `u` earlier commits to `svDone s` has
its completion observed by the poll of a dequant lane with `u + 1` earlier ones, before the lane's
later events. -/
theorem dq_first_obs {c k i u pcw pc bb : Nat} {a : Fin 128} {s : Fin 2} {ac : Acc}
    {bs : List Byte} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hW : X.get (deqLane L c a, k) = some ⟨pcw, .wr ac bs⟩)
    (hx : X.get (mmaLane L X c, i) = some ⟨pc, .tc (.mma bb sp acc mask)⟩)
    (hmc : mmaLane L X c / L.block = c)
    (hcm : ((X.tr (mmaLane L X c)).take i).countP
      (PTX.Flow.commitsTo (mbarLoc L c (.svDone s))) ≤ u)
    (hpol : u + 2 ≤ okPolls (mbarLoc L c (.svDone s)) ((X.tr (deqLane L c a)).take k)) :
    ∃ j < k, ∃ ws, AsyncObserved X (mmaLane L X c, i) .mmaDone (deqLane L c a, j) true ws ∧
      ScopesMeet L .cluster (mmaLane L X c) ws (deqLane L c a) ∧
      baseCausality L X (deqLane L c a, j) (deqLane L c a, k) := by
  have hh : deqLane L c a < L.threads := Frame.lt_of_get hX hW
  have hkl : k < (X.tr (deqLane L c a)).length := (List.getElem?_eq_some_iff.mp hW).1
  obtain ⟨j, pcp, p, acq, sc, hjk, hget, hq⟩ := UnitHandoff.exists_poll (c := u + 1) hpol
  obtain ⟨ic, pcc, sp', rank, hcom, hmb, htg, hcnt, hrank, hobs⟩ :=
    svDone_observes hp hX hFw hR hI hB hN hget hq
  obtain ⟨rfl, rfl⟩ := mbarWait_cta hX hR hget
  have hlt : i < ic := by
    by_contra hle
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hle) with h1 | rfl
    · have e1 := countP_take_succ (p := PTX.Flow.commitsTo (mbarLoc L c (.svDone s))) hcom
        (by simp [PTX.Flow.commitsTo, hmb])
      have e2 := countP_take_mono (PTX.Flow.commitsTo (mbarLoc L c (.svDone s)))
        (X.tr (mmaLane L X c)) (show ic + 1 ≤ i by omega)
      omega
    · rw [hx] at hcom
      cases hcom
  have hg' : mmaLane L X c < L.threads := Frame.lt_of_get hX hx
  have hsc : ScopesMeet L .cluster (mmaLane L X c) .cta (deqLane L c a) :=
    ⟨⟨hg', hh, by rw [hmc, deqLane_cta hp c a]⟩, hh, hg', by rw [hmc, deqLane_cta hp c a]⟩
  exact ⟨j, hjk, .cta, ⟨_, _, ⟨(mmaLane L X c, ic), sp', rank, rfl,
    ⟨rfl, hlt, .inl ⟨bb, sp, acc, mask, pc, hx⟩, sp', pcc, hcom⟩, ⟨pcc, hcom⟩, htg, hrank⟩, hobs⟩,
    hsc, .single (.inl (po_of_source_not_access rfl hjk hkl (by rw [hget]; rfl)))⟩

/-- **The write after**: a dequant lane's chunk store of use `v` is after an MMA's read of use
`u' < v` finished. -/
theorem dq_after {c k i v pcw pc bb idx : Nat} {a : Fin 128} {s : Fin 2} {ac : Acc}
    {bs : List Byte} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat} {isB : Bool}
    {l : Loc} (hW : X.get (deqLane L c a, k) = some ⟨pcw, .wr ac bs⟩)
    (hWp : okPolls (mbarLoc L c (.svDone s)) ((X.tr (deqLane L c a)).take k) = v + 1)
    (hx : X.get (mmaLane L X c, i) = some ⟨pc, .tc (.mma bb sp acc mask)⟩)
    (hmc : mmaLane L X c / L.block = c)
    (hcm : ((X.tr (mmaLane L X c)).take i).countP
      (PTX.Flow.commitsTo (mbarLoc L c (.svDone s))) < v)
    (hf : X.MmaFootprint (mmaLane L X c, i) isB idx l) (hls : l.space = .shared)
    (hwr : X.Writes (deqLane L c a, k) ac bs) (hcov : ac.Covers l) :
    ByteCausality L X l (.async (mmaLane L X c, i) (.mmaRead isB idx))
      (.thread (deqLane L c a, k)) := by
  obtain ⟨j, hjk, ws, hobs, hsc, hbase⟩ := dq_first_obs hp hX hFw hR hI hB hN hW hx hmc
    (s := s) (u := v - 1) (by omega) (by omega)
  exact completed_mma_source_before_store (f := (deqLane L c a, k)) ⟨pc, hx⟩ hf
    (.inr ⟨ws, hobs, hsc⟩) rfl hjk hbase hls hwr hcov

/-- **A dequant lane's chunk store and an MMA's read of the tile are ordered**: of one CTA, the
store of lane `h` and the QK or PV MMA read of the byte `l` of the dequantized tile `b0`. -/
theorem dq_mma {h k g i pcw pc bb idx : Nat} {ac : Acc} {bs : List Byte} {sp : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} {isB : Bool} {l : Loc} {b0 : Fin 2}
    (hW : X.get (h, k) = some ⟨pcw, .wr ac bs⟩) (hat : MbarRow.DequantAt L h pcw)
    (hcov : ac.Covers l) (hx : X.get (g, i) = some ⟨pc, .tc (.mma bb sp acc mask)⟩)
    (hatm : MbarRow.MmaAt L g pc) (hf : X.MmaFootprint (g, i) isB idx l)
    (hlg : MemRow.LocIn L (g / L.block) (.dequant b0) l) :
    ByteCausality L X l (.thread (h, k)) (.async (g, i) (.mmaRead isB idx)) ∨
      ByteCausality L X l (.async (g, i) (.mmaRead isB idx)) (.thread (h, k)) := by
  obtain ⟨bw, r, s', u, hws, hpol, harr, -⟩ := dequant_wrUse hp hX hFw hW hat
  have hlt := MemRow.dqChunk_lt (i := h % 128) (Nat.mod_lt _ (by decide)) r.isLt s'.isLt
  have hlw : MemRow.LocIn L (h / L.block) (.dequant bw) l :=
    (MemRow.wsAcc_in hws (Nat.le_add_right _ _) (by simp only [Region.size]; omega)).locIn hcov
  obtain ⟨hcc, hb⟩ := locIn_eq hlw hlg
  obtain rfl : bw = b0 := by injection hb
  obtain ⟨a, ha⟩ := deq_lane hp hat
  obtain ⟨hpcm, u', hpm, hcmm⟩ := mma_dqUse hp hX hFw hx hatm hf hlg
  have hon : MmaOn L g pc := ⟨hatm, hpcm⟩
  have hg : g = mmaLane L X (g / L.block) :=
    laneOn_eq (mmaOne hp hX hFw) hx (fun _ h => by cases h) hon
  generalize hcd : h / L.block = c at *
  subst ha
  rw [← hcc] at hg
  subst hg
  obtain ⟨hls, hlcm, -, -⟩ := id hlg
  have hmc : mmaLane L X c / L.block = c := hcc.symm
  rw [hmc] at hpm hcmm
  have hlc : l.cta = c := by rw [hlcm, hmc]
  rcases le_or_gt u u' with hle | hlt
  · exact .inl (.direct (dq_before hp hX hFw hR hI hB hN hW harr hx (by omega) hf hls hlc hmc))
  · exact .inr (dq_after hp hX hFw hR hI hB hN hW hpol hx hmc (by omega) hf hls ⟨pcw, hW⟩ hcov)

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
