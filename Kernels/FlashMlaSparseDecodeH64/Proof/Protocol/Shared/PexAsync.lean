-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.PExchange
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.PvStore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Out
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect
import Lemmas.Tcgen05.MmaObservedReads

@[expose] public section

/-! # The P tile's writes and the PV MMA's asynchronous read

A thread write `W` of the P exchange (a peer store or a P store of warpgroup 0's lane `h`, block
`r`, `PexBlk`) and the asynchronous read of operand A by a PV MMA `A` of the MMA lane of the CTA
(block `d`, `mma_pvBlock`): the score ring of slot `r % 2`, use `r / 2` orders them.

* `r ≤ d` (`pex_before`): the lane's proxy fence (the event before its arrival of use `r / 2` on
  `soReady`, `wg0_fenceArr`) follows `W`, the arrival is observed by the MMA lane's poll before `A`
  (`soReady_after`): `ProxyBefore W A`.
* `r > d` (`pex_after`): the lane's poll of `qkDone` for use `r / 2` before `W` observes the
  notification of the commit tracking `A` (`mma_first_obs`), so `A` finished before `W`
  (`completed_mma_source_before_store`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- An arrival on `soReady` by a lane of warpgroup 0 is at pc 1122. -/
theorem soArr_pc (hR : MbarRows P L X) {c g k pc tx n : Nat} {s : Fin 2} {rel : Bool}
    {sc : MbarScope} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .arrive (mbarLoc L c (.soReady s)) tx n rel sc⟩) :
    pc = 1122 := by
  rcases mbar_use hR hg he rfl with ⟨-, ⟨-, j, -, -, hk⟩⟩ | ⟨hat, h⟩ | ⟨hat, h⟩ | ⟨-, h⟩ |
    ⟨-, h⟩ | ⟨hat, h⟩
  · cases hk
  · cases h with
    | lastStore _ hl _ | coordReady _ hl _ | coordFree _ hl _ | qkDone _ hl _ | svDone _ hl _ =>
      exact absurd (fam_eq hl).2 (by simp)
    | soReady hpc _ _ => exact hpc
  all_goals
    exfalso
    cases h <;> first
      | (simp_all [MbarRow.Wait, MbarRow.Commit, MbarRow.Arrive]; done)
      | exact absurd (fam_eq ‹_›).2 (by simp)

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
include hp hX hFw hR hI hB

/-- **The write, a fence of its lane, then the MMA**: a thread write of warpgroup 0's block `r`
is before the arrival that ends the block, whose proxy fence is before the PV MMA of block
`d ≥ r` after its poll. -/
theorem pex_fence {h k g i pc bb d : Nat} {f : Event} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {o c r : Nat} {a : Acc} {bs : List Byte}
    (hW : PexCls P L X h k f true o c) (hr : PexBlk L X h k r)
    (hwr : X.Writes (h, k) a bs) (hx : X.get (g, i) = some ⟨pc, .tc (.mma bb s acc mask)⟩)
    (hg : g = mmaLane L X (h / L.block)) (hc : g / L.block = h / L.block)
    (hd : ∀ j : Fin 2, okPolls (mbarLoc L (g / L.block) (.soReady j)) ((X.tr g).take i) =
      ringUses 2 j (d + 1)) (hrd : r ≤ d) :
    ∃ jf, X.IsProxyFence (h, jf) (.async (some (.shared .cta))) none ∧ k < jf ∧
      jf < (X.tr h).length ∧ baseCausality L X (h, jf) (g, i) := by
  have hh : h < L.threads := Frame.lt_of_get hX hW.get
  have hg' : g < L.threads := Frame.lt_of_get hX hx
  have hil : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp hx).1
  have hpol : r / 2 + 1 ≤ okPolls (mbarLoc L (h / L.block) (.soReady (slot2 r)))
      ((X.tr g).take i) := by
    have h1 := hd (slot2 r)
    rw [hc] at h1
    rw [h1]
    show r / 2 + 1 ≤ ringUses 2 (r % 2) (d + 1)
    unfold ringUses
    omega
  obtain ⟨ia, pca, hga, hq, hbc⟩ := TmRace.soReady_after hp hX hFw hR hI hB hh hW.warp hg hc hil
    hpol
  have harr : arrivals (mbarLoc L (h / L.block) (.soReady (slot2 r))) ((X.tr h).take k) =
      r / 2 := by
    rw [(hr (slot2 r)).2]
    show ringUses 2 (r % 2) r = r / 2
    unfold ringUses
    omega
  have hki : k ≤ ia := by
    rcases hq _ le_rfl k harr with h1 | h1
    · exact h1
    · omega
  obtain rfl : pca = 1122 := soArr_pc hR hh hga
  obtain ⟨jf, hia, hfence⟩ := wg0_fenceArr hp hX hFw hW.warp hga
  obtain ⟨pcw, hwk⟩ := hwr
  obtain ⟨pcf, hfg⟩ := hfence
  have hkjf : k < jf := by
    have hn1 : k ≠ ia := fun h1 => by
      rw [h1] at hwk
      rw [hwk] at hga
      cases hga
    have hn2 : k ≠ jf := fun h1 => by
      rw [h1] at hwk
      rw [hwk] at hfg
      cases hfg
    omega
  exact ⟨jf, ⟨pcf, hfg⟩, hkjf, (List.getElem?_eq_some_iff.mp hfg).1, hbc jf (by omega)⟩

/-- **The write first, in the tcgen05 order**: the write of warpgroup 0's block `r` has a `TcStep`
path to the PV MMA of block `d ≥ r`. -/
theorem pex_tc {h k g i pc bb d : Nat} {f : Event} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {o c r : Nat} {a : Acc} {bs : List Byte}
    (hW : PexCls P L X h k f true o c) (hr : PexBlk L X h k r)
    (hwr : X.Writes (h, k) a bs) (hx : X.get (g, i) = some ⟨pc, .tc (.mma bb s acc mask)⟩)
    (hg : g = mmaLane L X (h / L.block)) (hc : g / L.block = h / L.block)
    (hd : ∀ j : Fin 2, okPolls (mbarLoc L (g / L.block) (.soReady j)) ((X.tr g).take i) =
      ringUses 2 j (d + 1)) (hrd : r ≤ d) :
    Relation.TransGen (TcMma.TcStep L X) (h, k) (g, i) := by
  obtain ⟨jf, ⟨pcf, hfg⟩, hkjf, hflen, hbc⟩ := pex_fence hp hX hFw hR hI hB hW hr hwr hx hg hc
    hd hrd
  refine .head (.inl (.single (.inl (po_of_not_access (e := (h, k)) (f := (h, jf)) rfl hkjf
    hflen ?_)))) (.single (.inl hbc))
  rw [hfg]
  rfl

/-- **The write first**: a thread write of warpgroup 0's block `r` is ordered before the PV MMA's
read of block `d ≥ r`. -/
theorem pex_before {h k g i pc bb idx d : Nat} {f : Event} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {o c r : Nat} {a : Acc} {bs : List Byte} {l : Loc}
    (hW : PexCls P L X h k f true o c) (hr : PexBlk L X h k r)
    (hwr : X.Writes (h, k) a bs) (hx : X.get (g, i) = some ⟨pc, .tc (.mma bb s acc mask)⟩)
    (hg : g = mmaLane L X (h / L.block)) (hc : g / L.block = h / L.block)
    (hd : ∀ j : Fin 2, okPolls (mbarLoc L (g / L.block) (.soReady j)) ((X.tr g).take i) =
      ringUses 2 j (d + 1)) (hrd : r ≤ d) (hls : l.space = .shared) (hlc : l.cta = h / L.block)
    (hf : X.MmaFootprint (g, i) false idx l) :
    modelCausality L X l (.thread (h, k)) (.async (g, i) (.mmaRead false idx)) := by
  have hh : h < L.threads := Frame.lt_of_get hX hW.get
  have hg' : g < L.threads := Frame.lt_of_get hX hx
  obtain ⟨jf, hfence, hkjf, hflen, hbc⟩ := pex_fence hp hX hFw hR hI hB hW hr hwr hx hg hc
    hd hrd
  obtain ⟨pcf, hfg⟩ := hfence
  obtain ⟨pcw, hwk⟩ := hwr
  refine ⟨⟨{ loc := l, size := 1 }, false, ⟨rfl, rfl, hf⟩,
    Acc.covers_at (k := 0) (show 0 < 1 by decide)⟩, .inl ⟨(h, jf), some (.shared .cta), none,
    ⟨pcf, hfg⟩, hh, ⟨hls, hlc⟩, ⟨hh, hg', congrArg L.clusterOfCta hc.symm⟩, ?_,
    hbc⟩⟩
  refine .single (.inl ⟨rfl, hkjf, hflen, fun hs => ?_⟩)
  have h1 := hs.1
  rw [hfg] at h1
  simp [Event.acc] at h1

/-- **The write after**: a thread write of warpgroup 0's block `r` is after the PV MMA's read of
block `d < r` finished. -/
theorem pex_after {h k g i pc bb idx d : Nat} {f : Event} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {o c r : Nat} {a : Acc} {bs : List Byte} {l : Loc}
    (hW : PexCls P L X h k f true o c) (hr : PexBlk L X h k r)
    (hwr : X.Writes (h, k) a bs) (hcov : a.Covers l)
    (hx : X.get (g, i) = some ⟨pc, .tc (.mma bb s acc mask)⟩)
    (hg : g = mmaLane L X (h / L.block)) (hc : g / L.block = h / L.block)
    (hd : ∀ j : Fin 2, ((X.tr g).take i).countP
      (PTX.Flow.commitsTo (mbarLoc L (g / L.block) (.qkDone j))) = ringUses 2 j (d + 1))
    (hrd : d < r) (hls : l.space = .shared) (hf : X.MmaFootprint (g, i) false idx l) :
    ByteCausality L X l (.async (g, i) (.mmaRead false idx)) (.thread (h, k)) := by
  have hh : h < L.threads := Frame.lt_of_get hX hW.get
  have hkl : k < (X.tr h).length := (List.getElem?_eq_some_iff.mp hW.get).1
  have hcm : ((X.tr g).take i).countP
      (PTX.Flow.commitsTo (mbarLoc L (h / L.block) (.qkDone (slot2 r)))) ≤ r / 2 := by
    have h1 := hd (slot2 r)
    rw [hc] at h1
    rw [h1]
    show ringUses 2 (r % 2) (d + 1) ≤ r / 2
    unfold ringUses
    omega
  have hpol : r / 2 + 1 ≤ okPolls (mbarLoc L (h / L.block) (.qkDone (slot2 r)))
      ((X.tr h).take k) := by
    rw [(hr (slot2 r)).1]
    show r / 2 + 1 ≤ ringUses 2 (r % 2) (r + 1)
    unfold ringUses
    omega
  obtain ⟨j, hjk, ws, hobs, hsc, hbase⟩ :=
    TmRace.mma_first_obs hp hX hFw hR hI hB hx hh hW.warp hkl hg hc hcm hpol
  exact completed_mma_source_before_store (f := (h, k)) ⟨pc, hx⟩ hf (.inr ⟨ws, hobs, hsc⟩) rfl
    hjk hbase hls hwr hcov

/-- **A thread write and the PV MMA's read are ordered**: of one CTA's warpgroup 0 and MMA lane,
block `r` of the write and block `d` of the MMA. -/
theorem pex_tm {h k g i pc bb idx : Nat} {f : Event} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {o c : Nat} {a : Acc} {bs : List Byte} {l : Loc}
    (hW : PexCls P L X h k f true o c) (hwr : X.Writes (h, k) a bs) (hcov : a.Covers l)
    (hx : X.get (g, i) = some ⟨pc, .tc (.mma bb s acc mask)⟩) (hbb : bb < 256)
    (hat : MmaAt L g pc) (hlg : MemRow.LocIn L (g / L.block) .pExchange l)
    (hlc : l.cta = h / L.block) (hf : X.MmaFootprint (g, i) false idx l) :
    ByteCausality L X l (.thread (h, k)) (.async (g, i) (.mmaRead false idx)) ∨
      ByteCausality L X l (.async (g, i) (.mmaRead false idx)) (.thread (h, k)) := by
  have hc : g / L.block = h / L.block := hlg.2.1.symm.trans hlc
  have hT := tmem_rows hp hX hFw
  have hon := TmRace.pv_on hT hX hx hbb
  have hg : g = mmaLane L X (h / L.block) := by
    rw [← hc]
    exact laneOn_eq (mmaOne hp hX hFw) hx (fun _ h => by cases h) hon
  obtain ⟨d, hd⟩ := mma_pvBlock hp hX hFw hx hat hbb
  obtain ⟨r, hr, hu, hblk⟩ := hW.use
  by_cases hrd : r ≤ d
  · exact .inl (.direct (pex_before hp hX hFw hR hI hB hW hblk hwr hx hg hc
      (fun j => (hd j).1) hrd hlg.1 hlc hf))
  · exact .inr (pex_after hp hX hFw hR hI hB hW hblk hwr hcov hx hg hc
      (fun j => (hd j).2) (by omega) hlg.1 hf)

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
