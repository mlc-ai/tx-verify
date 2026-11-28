-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.PexAsync
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.PvVisible
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.PvFoot
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PStores
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Count
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Close.Lag
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.PvStore
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Block
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Async
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.Sync9
import Lemmas.Order.ReadLast
import Lemmas.Tcgen05.MmaOperandObservations

@[expose] public section

/-! # The lane's P store of the block a PV MMA reads

The PV MMA of block `d` reads the P tile after the polls of `soReady` it makes (`mma_pvBlock`).
The lane `h` of warpgroup 0 that stores a byte of the tile (the place of `pTile_place`) has its
arrival on `soReady (d % 2)` for use `d / 2` observed by the MMA's poll; the arrival is the one of
block `d` (`wg0_soArrBlk`), after the lane's 16 P stores of the block (`wg0_pStores`), so the
store covering the byte is block `d`'s, at an even barrier-9 count `2 d + 2`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The byte of the P tile at offset `o < 8192` is lane `t`'s store `(j, el)`**: its place. -/
theorem pTile_at {o : Nat} (ho : o < 8192) :
    ∃ t j el y, t < 128 ∧ j < 4 ∧ el < 4 ∧ y < 4 ∧
      o = 4096 * (t / 32 / 2) + 512 * (t / 32 % 2) + 16 * (t % 32) + 1024 * j + 4 * el + y :=
  ⟨32 * (2 * (o / 4096) + o % 1024 / 512) + o % 512 / 16, o % 4096 / 1024, o % 16 / 4, o % 4,
    by omega, by omega, by omega, by omega, by omega⟩

/-- The arrivals of block `d`'s lane are `d / 2` on the slot of `d`: the block of the arrival. -/
theorem blk_of_arrivals {n d : Nat} (h : ringUses 2 (slot2 n) n = d / 2) (hs : slot2 n = slot2 d) :
    n = d := by
  have h1 : n % 2 = d % 2 := by
    have := congrArg Fin.val hs
    simpa [slot2] using this
  simp only [slot2] at h
  unfold ringUses at h
  omega

/-- Two accesses of one byte at an even barrier-9 count by threads of warpgroup 0 are one lane's. -/
theorem pexUse_lane {t t' o r r' n9 np np' : Nat} (hu : PexUse t true o r n9 np)
    (hu' : PexUse t' true o r' n9 np') (hev : n9 % 2 = 0) (ht : t < 128) (ht' : t' < 128) :
    t = t' := by
  unfold PexUse at hu hu'
  rcases hu with hu | hu | ⟨-, h1, h2, j1, hj1, el1, hel1, h3, h4⟩
  · omega
  · simp at hu
  rcases hu' with hu' | hu' | ⟨-, h1', h2', j2, hj2, el2, hel2, h3', h4'⟩
  · omega
  · simp at hu'
  exact (MemRow.wg0Ost_inj ht ht' hj1 hj2 hel1 hel2 (by omega)).1

/-- The barrier-9 count of an access of the exchange is at most `2 r + 2`. -/
theorem pexUse_le {t o r n9 np : Nat} {w : Bool} (h : PexUse t w o r n9 np) : n9 ≤ 2 * r + 2 := by
  unfold PexUse at h
  omega

/-- A thread is its CTA's and its index in the CTA. -/
theorem thread_eq {g h : Nat} (h1 : g % L.block = h % L.block) (h2 : g / L.block = h / L.block) :
    g = h := by
  rw [← Nat.div_add_mod g L.block, ← Nat.div_add_mod h L.block, h1, h2]

/-- Two writes of one lane covering one byte are ordered by the lane's program order. -/
theorem pv_po {h k k' pcw pcw' : Nat} {ac ac' : Acc} {bs bs' : List Byte} {l : Loc}
    (hW : X.get (h, k') = some ⟨pcw', .wr ac' bs'⟩) (hW' : X.get (h, k) = some ⟨pcw, .wr ac bs⟩)
    (hc' : ac'.Covers l) (hc : ac.Covers l) (hlt : k' < k) :
    ByteCausality L X l (.thread (h, k')) (.thread (h, k)) :=
  .direct (.of_base L (.single (.inl (po_of_overlap (we := true) (wf := true)
    (Or.inr (Or.inl ⟨bs', ⟨pcw', hW⟩, rfl⟩)) (Or.inr (Or.inl ⟨bs, ⟨pcw, hW'⟩, rfl⟩)) rfl hlt
    ⟨l, hc', hc⟩))))

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
include hp hX hFw hR hI hB

/-- **The block-`d` store of the lane that stores a P-tile byte**: the lane `h` of the byte's
place, its P store `(j, el)` of block `d` at index `i0` (at pc `704 + j`, covering the byte, at
the even barrier-9 count `2 d + 2`), where `d` is the PV MMA's block. -/
theorem pv_w0 {g i pc bb idx d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    {l : Loc} (hx : X.get (g, i) = some ⟨pc, .tc (.mma bb s acc mask)⟩) (hbb : bb < 256)
    (hat : MmaAt L g pc) (hl : s.byteLoc .a idx = some l)
    (hd : ∀ j : Fin 2, okPolls (mbarLoc L (g / L.block) (.soReady j)) ((X.tr g).take i) =
      ringUses 2 j (d + 1)) :
    ∃ h i0 j a bs, warp L h < 4 ∧ h / L.block = g / L.block ∧
      X.get (h, i0) = some ⟨704 + j, .wr a bs⟩ ∧ j < 4 ∧ a.Covers l ∧
      ((X.tr h).take i0).countP (Execution.isBarId 9) = 2 * d + 2 := by
  have hg0 : g < L.threads := Frame.lt_of_get hX hx
  obtain ⟨hlg, hl8⟩ := mmaFoot_pvA hp hX hFw hg0 hx hat hbb hl
  have hon := TmRace.pv_on (tmem_rows hp hX hFw) hX hx hbb
  have hg : g = mmaLane L X (g / L.block) :=
    laneOn_eq (mmaOne hp hX hFw) hx (fun _ h => by cases h) hon
  have hil : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp hx).1
  obtain ⟨hls, hlcta, hlo, hhi⟩ := id hlg
  simp only [Region.lo] at hlo
  obtain ⟨t, j, el, y, ht, hj, hel, hy, hoeq⟩ := pTile_at (o := l.addr - L.sharedBase - 204800)
    (by omega)
  have hb384 : L.block = 384 := hp.block
  have hgrid : g / L.block < L.grid := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    exact hg0
  obtain ⟨c, hc⟩ : ∃ c, c = g / L.block := ⟨_, rfl⟩
  rw [← hc] at hlg hlcta hg hgrid hd
  let b : Fin 128 := ⟨t, ht⟩
  obtain ⟨hw4, hcb⟩ := wg0Lane_at hp c b
  have hh : wg0Lane L c b < L.threads := by
    have : (c + 1) * L.block ≤ L.grid * L.block := Nat.mul_le_mul_right _ hgrid
    simp only [wg0Lane, Launch.threads]
    nlinarith [b.isLt]
  set h := wg0Lane L c b with hhdef
  have hcc : g / L.block = h / L.block := by rw [← hc, hcb]
  have hpol : d / 2 + 1 ≤ okPolls (mbarLoc L (h / L.block) (.soReady (slot2 d)))
      ((X.tr g).take i) := by
    have h1 := hd (slot2 d)
    rw [← hcb] at h1
    rw [h1]
    show d / 2 + 1 ≤ ringUses 2 (d % 2) (d + 1)
    unfold ringUses
    omega
  obtain ⟨ia, pca, hga, hca, -, -⟩ := TmRace.soReady_after' hp hX hFw hR hI hB hh hw4
    (hg.trans (by rw [hcb])) hcc hil hpol
  obtain rfl : pca = 1122 := soArr_pc hR hh hga
  have hga' : X.get (c * L.block + t, ia) = some ⟨1122, .arrive (mbarLoc L c (.soReady (slot2 d)))
      0 1 true .cta⟩ := by
    rw [hcb] at hga
    exact hga
  obtain ⟨n, hsn, hcn⟩ := wg0_soArrBlk hp hX hFw (b := t) ht hga'
  have hca' : arrivals (mbarLoc L c (.soReady (slot2 d))) ((X.tr (c * L.block + t)).take ia) =
      d / 2 := by
    rw [hcb] at hca
    exact hca
  have hnd : n = d := by
    refine blk_of_arrivals ?_ hsn.symm
    have := hcn (slot2 d)
    rw [hca'] at this
    rw [← hsn]
    exact this.symm
  rw [hnd] at hcn
  have hcn' : ∀ s' : Fin 2, arrivals (mbarLoc L c (.soReady s')) ((X.tr h).take ia) =
      ringUses 2 s' d := hcn
  obtain ⟨i0, hi0, a, bs, hget0, hsz, hloc, hcnt⟩ := wg0_pStores hp hX hFw hw4 hga
    ⟨j, hj⟩ ⟨el, hel⟩
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
  have hacc : X.Access (h, i0) a true := .inr (.inl ⟨bs, ⟨_, hget0⟩, rfl⟩)
  obtain ⟨e, hW, -⟩ := pex_cls hp hX hFw hacc hcov hlg
  have he : e = ⟨704 + j, .wr a bs⟩ := Option.some.inj (hW.get.symm.trans hget0)
  obtain ⟨r, -, hu, hblk⟩ := hW.use
  have hr : r = d := by
    have e0 := (hblk 0).2
    have e1 := (hblk 1).2
    rw [hcnt, hcb, hcn'] at e0 e1
    simp only [Fin.val_zero, Fin.val_one] at e0 e1
    unfold ringUses at e0 e1
    omega
  have hev : ((X.tr h).take i0).countP (Execution.isBarId 9) % 2 = 0 :=
    (hW.ostPc rfl).2 ⟨j, hj, by rw [he]⟩
  refine ⟨h, i0, j, a, bs, hw4, hcb.trans hc, hget0, hj, hcov, ?_⟩
  unfold PexUse at hu
  rcases hu with hu | hu | hu
  · omega
  · simp at hu
  · omega

variable (hBar : BarRows P L X)
include hBar

/-- **Every write of a P-tile byte is the lane's block-`d` store, before it, or after the read**:
for the lane's store `(h, km)` covering the byte at the barrier-9 count `2 d + 2` that is the last
such store of the lane (`hmax`): the store is before the PV MMA's read (`hv`), and every write
covering the byte is the store, before it, or after the read. -/
theorem pv_order {g i pc bb idx d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    {l : Loc} (hx : X.get (g, i) = some ⟨pc, .tc (.mma bb s acc mask)⟩) (hbb : bb < 256)
    (hat : MmaAt L g pc) (hl : s.byteLoc .a idx = some l)
    (hd : ∀ j : Fin 2, okPolls (mbarLoc L (g / L.block) (.soReady j)) ((X.tr g).take i) =
        ringUses 2 j (d + 1) ∧
      ((X.tr g).take i).countP (PTX.Flow.commitsTo (mbarLoc L (g / L.block) (.qkDone j))) =
        ringUses 2 j (d + 1))
    {h km pcw : Nat} {ac : Acc} {bs : List Byte}
    (hW : X.get (h, km) = some ⟨pcw, .wr ac bs⟩) (hhw : h / L.block = g / L.block)
    (hcov : ac.Covers l) (hcnt : ((X.tr h).take km).countP (Execution.isBarId 9) = 2 * d + 2)
    (hmax : ∀ k', (∃ pcw' ac' bs', X.get (h, k') = some ⟨pcw', .wr ac' bs'⟩ ∧ 704 ≤ pcw' ∧
      pcw' < 708 ∧ ac'.Covers l ∧ ((X.tr h).take k').countP (Execution.isBarId 9) = 2 * d + 2) →
      k' ≤ km) :
    ByteCausality L X l (.thread (h, km)) (.async (g, i) (.mmaRead false idx)) ∧
      ∀ w' dst' bytes, X.MemWrites w' dst' bytes → dst'.Covers l →
        w' = .thread (h, km) ∨ ByteCausality L X l w' (.thread (h, km)) ∨
          ByteCausality L X l (.async (g, i) (.mmaRead false idx)) w' := by
  have hg0 : g < L.threads := Frame.lt_of_get hX hx
  obtain ⟨hlg, hl8⟩ := mmaFoot_pvA hp hX hFw hg0 hx hat hbb hl
  have hf : X.MmaFootprint (g, i) false idx l :=
    Or.inl ⟨bb, s, acc, mask, ⟨pc, hx⟩, by simpa using hl⟩
  have hon := TmRace.pv_on (tmem_rows hp hX hFw) hX hx hbb
  have hg : g = mmaLane L X (g / L.block) :=
    laneOn_eq (mmaOne hp hX hFw) hx (fun _ h => by cases h) hon
  have hhg : g = mmaLane L X (h / L.block) := by rw [hhw]; exact hg
  have hcg : g / L.block = h / L.block := hhw.symm
  have hlc : l.cta = h / L.block := hlg.2.1.trans hcg
  have hh0 : h < L.threads := Frame.lt_of_get hX hW
  have hkl : km < (X.tr h).length := (List.getElem?_eq_some_iff.mp hW).1
  have hacc : X.Access (h, km) ac true := .inr (.inl ⟨bs, ⟨_, hW⟩, rfl⟩)
  obtain ⟨e, hW0, -⟩ := pex_cls hp hX hFw hacc hcov hlg
  obtain ⟨r, -, hu, hblk⟩ := hW0.use
  have hr : r = d := by
    unfold PexUse at hu
    rcases hu with hu | hu | hu <;> omega
  refine ⟨.direct (pex_before hp hX hFw hR hI hB hW0 hblk ⟨_, hW⟩ hx hhg hcg
    (fun j => (hd j).1) (by omega) hlg.1 hlc hf), ?_⟩
  intro w' dst' bytes hw' hcw
  cases w' with
  | async y q =>
    exfalso
    rcases async_region hp hX hFw hw'.intent hcw hlg.1 with ⟨r', hr'⟩ | ⟨-, pc', bb', s', acc',
      mask', idx', -, -, -, hq, -⟩ | ⟨r', hr', -⟩
    · exact absurd (locIn_eq hr' hlg).2 (by simp)
    · have h1 := hw'.intent.1
      rw [hq] at h1
      exact absurd h1 (by simp [AsyncCopy.Part.writes])
    · exact absurd (locIn_eq hr' hlg).2 (by simp)
  | thread x =>
    obtain ⟨g', k'⟩ := x
    have hacc' : X.Access (g', k') dst' true := hw'.intent
    obtain ⟨e', hW', hwg'⟩ := pex_cls hp hX hFw hacc' hcw hlg
    obtain ⟨bs', hwr'⟩ := hwg' rfl
    obtain ⟨r', hr', hu', hblk'⟩ := hW'.use
    have hc' : g / L.block = g' / L.block := hlg.2.1.symm.trans hW'.cta
    have hle := pexUse_le hu'
    by_cases hrd : r' ≤ d
    · by_cases hlt : ((X.tr g').take k').countP (Execution.isBarId 9) < 2 * d + 2
      · refine .inr (.inl (.direct (.of_base L (bar9_order hp hX hFw hBar
          ⟨Frame.lt_of_get hX hW'.get, hh0, hc'.symm.trans hcg⟩ hW'.warp hW'.get hW'.n9 hkl
          (by omega) (by omega)))))
      · have heq : ((X.tr g').take k').countP (Execution.isBarId 9) = 2 * d + 2 := by omega
        obtain ⟨j', hj', hpc'⟩ := (hW'.ostPc rfl).1 (by omega)
        obtain ⟨pcw', hget'⟩ := hwr'
        have he' : e' = ⟨pcw', .wr dst' bs'⟩ := Option.some.inj (hW'.get.symm.trans hget')
        have hl1 : g' % L.block = h % L.block := by
          have hu1 := hu
          have hu2 := hu'
          rw [hcnt] at hu1
          rw [heq] at hu2
          have ht1 := warp_tid hp g'
          have ht2 := warp_tid hp h
          have hw1 := hW'.warp
          have hw2 := hW0.warp
          exact pexUse_lane hu2 hu1 (by omega) (by omega) (by omega)
        obtain rfl : g' = h := thread_eq hl1 (hc'.symm.trans hcg)
        have hpc2 : pcw' = 704 + j' := by rw [he'] at hpc'; exact hpc'
        have hk' := hmax k' ⟨pcw', dst', bs', hget', by omega, by omega, hcw, heq⟩
        rcases Nat.lt_or_eq_of_le hk' with hlt' | heq'
        · exact .inr (.inl (pv_po hget' hW hcw hcov hlt'))
        · rw [heq']
          exact .inl rfl
    · exact .inr (.inr (pex_after hp hX hFw hR hI hB hW' hblk' hwr' hcw hx
        (by rw [← hc']; exact hg) hc' (fun j => (hd j).2) (by omega) hlg.1 hf))

/-- **A PV MMA's A byte is the byte of the last P store of its lane**: the byte at `l` the MMA read
is the byte of the P store `(h, k)` of the lane `h` (pc `704 + j`) of the block `d` the MMA reads,
the last such store of the lane covering `l`. -/
theorem pv_a_core {g i pc bb idx : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    {l : Loc} {ops : AsyncCopy.MmaOperands}
    (hx : X.get (g, i) = some ⟨pc, .tc (.mma bb s acc mask)⟩) (hbb : bb < 256)
    (hat : MmaAt L g pc) (hops : X.async.mmaOperands (g, i) = some ops)
    (hl : s.byteLoc .a idx = some l) :
    ∃ d h k pcw ac bs, (∀ j : Fin 2, okPolls (mbarLoc L (g / L.block) (.soReady j))
        ((X.tr g).take i) = ringUses 2 j (d + 1)) ∧
      warp L h < 4 ∧ h / L.block = g / L.block ∧ X.get (h, k) = some ⟨pcw, .wr ac bs⟩ ∧
      704 ≤ pcw ∧ pcw < 708 ∧ ac.Covers l ∧
      ((X.tr h).take k).countP (Execution.isBarId 9) = 2 * d + 2 ∧
      ops.a[idx]? = some (wbyte ac bs l) ∧
      ∀ k', (∃ pcw' ac' bs', X.get (h, k') = some ⟨pcw', .wr ac' bs'⟩ ∧ 704 ≤ pcw' ∧
        pcw' < 708 ∧ ac'.Covers l ∧ ((X.tr h).take k').countP (Execution.isBarId 9) = 2 * d + 2) →
        k' ≤ k := by
  classical
  obtain ⟨obs, hread, hobs⟩ := hX.mma_read_exists (isB := false) ⟨pc, hx⟩ hops hl
  obtain ⟨d, hd⟩ := mma_pvBlock hp hX hFw hx hat hbb
  obtain ⟨h, i0, j, a, bs, hw4, hhw, hget0, hj, hcov0, hcnt0⟩ :=
    pv_w0 hp hX hFw hR hI hB hx hbb hat hl (fun j => (hd j).1)
  let Q : Nat → Prop := fun k' => ∃ pcw ac bs, X.get (h, k') = some ⟨pcw, .wr ac bs⟩ ∧
    704 ≤ pcw ∧ pcw < 708 ∧ ac.Covers l ∧
    ((X.tr h).take k').countP (Execution.isBarId 9) = 2 * d + 2
  have hlen : ∀ {k' pc' kd}, X.get (h, k') = some ⟨pc', kd⟩ → k' ≤ (X.tr h).length :=
    fun h' => (List.getElem?_eq_some_iff.mp h').1.le
  have hQ0 : Q i0 := ⟨_, a, bs, hget0, by omega, by omega, hcov0, hcnt0⟩
  have hQm := Nat.findGreatest_spec (P := Q) (hlen hget0) hQ0
  obtain ⟨pcw, ac, bsm, hW, hp1, hp2, hcov, hcnt⟩ := hQm
  have hle : ∀ k', Q k' → k' ≤ Nat.findGreatest Q (X.tr h).length := by
    intro k' hk'
    obtain ⟨_, _, _, hg', -⟩ := id hk'
    exact Nat.le_findGreatest (hlen hg') hk'
  generalize hkm : Nat.findGreatest Q (X.tr h).length = km at *
  obtain ⟨hv, hall⟩ := pv_order hp hX hFw hR hI hB hBar hx hbb hat hl hd hW hhw hcov hcnt hle
  have hrd : X.MemReads (.async (g, i) (.mmaRead false idx)) { loc := l, size := 1 } [obs] :=
    ⟨obs, hread, rfl, rfl⟩
  have hrb := read_byte_of_last_write_ordered hX hrd (k := 0) Nat.zero_lt_one
    (show X.MemWrites (.thread (h, km)) ac bsm from .inl ⟨pcw, hW⟩)
    (by simpa [Loc.at] using hcov) (by simpa [Loc.at] using hv)
    (fun w' dst' bytes hw' hc' => by
      have hc2 : dst'.Covers l := by simpa [Loc.at] using hc'
      simpa [Loc.at] using hall w' dst' bytes hw' hc2)
  have hbo : obs = wbyte ac bsm l := by simpa [wbyte, Loc.at] using hrb
  refine ⟨d, h, km, pcw, ac, bsm, fun j => (hd j).1, hw4, hhw, hW, hp1, hp2, hcov, hcnt, ?_, hle⟩
  rw [← hbo]
  simpa using hobs

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
