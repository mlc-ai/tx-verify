-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.PexAsync
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PStores
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Close.Obj
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Close.Lag
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.PvStore
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Block
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Tmem

@[expose] public section

/-! # A P-tile byte the PV MMA reads has a covering write before the read

The PV MMA of block `d` reads the P tile, the first 8192 bytes of `pExchange`, as A. A byte of the
tile is covered by one P store `(k, el)` of one lane `h` of warpgroup 0 (the places of `ost`:
`4096 (w / 2) + 512 (w % 2) + 16 l + 1024 k + 4 el`, a bijection of the lanes and stores onto the
bytes). The MMA's poll of `soReady (d % 2)` for use `d / 2` observes the lane's arrival of that
use (`soReady_after'`), which follows the lane's 16 stores of its block (`wg0_pStores`, with no
arrival between): the store's block `r` is at most `d`, and the store is before the read
(`pex_before`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The byte of the P tile at offset `o < 8192` is lane `t`'s store `(j, el)`**: its place. -/
private theorem pTile_place {o : Nat} (ho : o < 8192) :
    ∃ t j el y, t < 128 ∧ j < 4 ∧ el < 4 ∧ y < 4 ∧
      o = 4096 * (t / 32 / 2) + 512 * (t / 32 % 2) + 16 * (t % 32) + 1024 * j + 4 * el + y :=
  ⟨32 * (2 * (o / 4096) + o % 1024 / 512) + o % 512 / 16, o % 4096 / 1024, o % 16 / 4, o % 4,
    by omega, by omega, by omega, by omega, by omega⟩

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
include hp hX hFw hR hI hB

/-- **A P-tile byte a PV MMA reads has a covering write before the read**: a P store of a lane of
warpgroup 0 of the CTA. -/
theorem pv_visible {g i pc bb idx : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    {l : Loc} (hx : X.get (g, i) = some ⟨pc, .tc (.mma bb s acc mask)⟩) (hbb : bb < 256)
    (hat : MmaAt L g pc) (hf : X.MmaFootprint (g, i) false idx l)
    (hlg : MemRow.LocIn L (g / L.block) .pExchange l)
    (hl8 : l.addr < L.sharedBase + 204800 + 8192) :
    ∃ w a bs, X.MemWrites w a bs ∧ a.Covers l ∧
      ByteCausality L X l w (.async (g, i) (.mmaRead false idx)) := by
  have hon := TmRace.pv_on (tmem_rows hp hX hFw) hX hx hbb
  have hg : g = mmaLane L X (g / L.block) :=
    laneOn_eq (mmaOne hp hX hFw) hx (fun _ h => by cases h) hon
  obtain ⟨d, hd⟩ := mma_pvBlock hp hX hFw hx hat hbb
  have hg0 : g < L.threads := Frame.lt_of_get hX hx
  have hil : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp hx).1
  obtain ⟨hls, hlcta, hlo, hhi⟩ := id hlg
  simp only [Region.lo] at hlo
  obtain ⟨t, j, el, y, ht, hj, hel, hy, hoeq⟩ := pTile_place (o := l.addr - L.sharedBase - 204800)
    (by omega)
  -- the lane
  have hb384 : L.block = 384 := hp.block
  have hgrid : g / L.block < L.grid := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    exact hg0
  generalize hc : g / L.block = c at *
  let b : Fin 128 := ⟨t, ht⟩
  obtain ⟨hw4, hcb⟩ := wg0Lane_at hp c b
  have hh : wg0Lane L c b < L.threads := by
    have : (c + 1) * L.block ≤ L.grid * L.block := Nat.mul_le_mul_right _ hgrid
    simp only [wg0Lane, Launch.threads]
    nlinarith [b.isLt]
  set h := wg0Lane L c b with hhdef
  have hcc : g / L.block = h / L.block := by rw [hc, hcb]
  -- the arrival of the lane
  have hpol : d / 2 + 1 ≤ okPolls (mbarLoc L (h / L.block) (.soReady (slot2 d)))
      ((X.tr g).take i) := by
    have h1 := (hd (slot2 d)).1
    rw [← hcb] at h1
    rw [h1]
    show d / 2 + 1 ≤ ringUses 2 (d % 2) (d + 1)
    unfold ringUses
    omega
  obtain ⟨ia, pca, hga, hca, -, -⟩ := TmRace.soReady_after' hp hX hFw hR hI hB hh hw4
    (hg.trans (by rw [hcb])) hcc hil hpol
  obtain rfl : pca = 1122 := soArr_pc hR hh hga
  obtain ⟨i0, hi0, a, bs, hget0, hsz, hloc, hcnt⟩ := wg0_pStores hp hX hFw hw4 hga
    ⟨j, hj⟩ ⟨el, hel⟩
  have hwr : X.Writes (h, i0) a bs := ⟨_, hget0⟩
  have ht' : tidOf L h = t := by
    rw [tidOf_eq hp]
    simp only [hhdef, wg0Lane, hb384, b]
    omega
  rw [ht'] at hloc
  have hcov : a.Covers l := by
    unfold Acc.Covers Loc.InRange
    rw [hloc, hsz]
    simp only [wsLoc]
    refine ⟨hls, ?_, ?_, ?_⟩
    · rw [hlcta, hcb]
    · omega
    · omega
  have hacc : X.Access (h, i0) a true := .inr (.inl ⟨bs, hwr, rfl⟩)
  have hlg' : MemRow.LocIn L c .pExchange l := ⟨hls, hlcta, by simpa [Region.lo] using hlo,
    by simp only [Region.lo, Region.size]; omega⟩
  obtain ⟨e, hW, -⟩ := pex_cls hp hX hFw hacc hcov hlg'
  obtain ⟨r, -, -, hblk⟩ := hW.use
  have hrd : r ≤ d := by
    have h1 := (hblk (slot2 d)).2
    rw [hcnt, hca] at h1
    have h2 : d / 2 = ringUses 2 (d % 2) r := h1
    by_contra hlt
    unfold ringUses at h2
    omega
  refine ⟨.thread (h, i0), a, bs, .inl hwr, hcov, .direct ?_⟩
  refine pex_before hp hX hFw hR hI hB hW hblk hwr hx (hg.trans (by rw [hcb])) hcc
    (fun j' => ?_) hrd hls (by rw [hlcta, hcb]) hf
  rw [hc]
  exact (hd j').1

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
