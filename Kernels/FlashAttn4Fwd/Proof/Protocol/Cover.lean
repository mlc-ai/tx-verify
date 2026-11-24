-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Cover
public import Kernels.FlashAttn4Fwd.Proof.Protocol.ORoute
public import Kernels.FlashAttn4Fwd.Proof.Protocol.OAccReady
public import Kernels.FlashAttn4Fwd.Proof.Protocol.ValuesOperands

@[expose] public section

/-! # The MMAs of a tile cover the cells its loads read

`softCoverLast` proves `ValuesOps.SoftCoverLast` and `corrCoverLast` proves
`ValuesOps.CorrCoverLast`: each cell a softmax load of score tile `u` reads is written by step 7 of
the QK block of tile `u`, and each cell a correction load of credit `q` reads by step 7 of the PV
block of tile `q - 1`. They imply `Floats.SoftCover` and `Floats.CorrCover` (`softCover`,
`corrCover`).

* **The footprint** (`mma_region`): an MMA of the kernel is M = 256, N = 128, `cta_group::2`
  with zero lane masks (`TcMmaThreadFacts.mma_desc`), its CTAs are its issuer's and the next
  (`ValuesOps.mma_ctas`), so it writes every lane of both CTAs of its pair over the 128 columns
  from its accumulator column (`resultCell_pair_all`, `writeCell_zero`); that column is the
  first of the region it writes (`ValuesOps.col0_qk`, `col0_pv`). A load's cell is lane
  `32 (warp % 4) + laneid` of its thread's CTA (`tcDataCell32`), in its stage's scores or
  accumulator (`ScoreFacts.soft_ld`, `OAccFacts.corr_ld`).
* **The issue**: a softmax load of tile `u` follows its poll of tile `u`, which observes the
  commit of tile `u` to the S-full object (`SFullHandoff`); the QK block of tile `u`, through
  step 7, precedes it (`CoverFacts.qk_sfull`). A correction load of credit `q` follows a
  softmax event with more than `q` S-full polls (`OAcc.sync_route`), whose poll of tile `q`
  observes the commit of tile `q`, preceded by the PV block of tile `q - 1`
  (`CoverFacts.pv_sfull`); or it follows its poll of the O-full object of item `I` with
  `q ≤ n (I + 1)`, which observes the commit of item `I`, preceded by the PV block of every tile
  before `n (I + 1)` (`OFullHandoff`, `CoverFacts.pv_ofull`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof TcMma

noncomputable section

namespace Cover

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- **An M = 256 `cta_group::2` MMA has a result cell at every row and column of its shape**
once it has one. -/
theorem resultCell_pair_all {s : OperandSpec} {base row col row' col' : Nat} {c : Cell}
    (hm : s.descriptor.m = 256) (hg : s.descriptor.group = .two)
    (h : resultCell s base row col = some c) (hr : row' < 256) (hc : col' < s.descriptor.n) :
    resultCell s base row' col' = some ⟨rowCta s row', row' % 128, base % 2 ^ 16 + col'⟩ := by
  have hsz : s.descriptor.group.size = 2 := by rw [hg]; rfl
  unfold resultCell at h ⊢
  dsimp only at h ⊢
  rw [hsz, hm] at h ⊢
  split at h
  · rename_i hcnd
    simp only [hcnd.1, hcnd.2.1, hr, hc, hcnd.2.2.2.2, and_self, ↓reduceIte,
      show (128 * 2 = 256) from rfl, show 256 / 2 = 128 from rfl, rowCta]
  · cases h

/-- **An MMA writes its whole region**: an MMA of the kernel writes every lane of both CTAs of
its pair over the 128 columns from its accumulator column. -/
theorem mma_region (hpre : Pre P L mem0) (ht : ScoreFacts L X) (htc : TcFacts L X)
    (htt : TcMmaThreadFacts L X) {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} {row col : Nat} {cell0 : Cell} (hi : X.MmaIssue i d s acc mask)
    (hpos : writeCell s d mask row col = some cell0) {cell : Cell} (hl : cell.lane < 128)
    (hcta : leadCta cell.cta = ctaOf L i.1) (h0 : d % 2 ^ 16 ≤ cell.column)
    (h1 : cell.column < d % 2 ^ 16 + 128) : X.MmaCell i cell := by
  obtain ⟨-, hm, hn, hg, -, -⟩ := TcMmaSources.mma_desc' htt hi
  have hmask := (htt.mma_desc hi).1
  subst hmask
  rw [writeCell_zero hm hg] at hpos
  obtain ⟨hlow, hhigh, -⟩ := ValuesOps.mma_ctas hpre ht htc htt hi
  unfold leadCta at hcta
  have hr : (cell.cta - ctaOf L i.1) * 128 + cell.lane < 256 := by omega
  have hres := resultCell_pair_all hm hg hpos hr
    (show cell.column - d % 2 ^ 16 < s.descriptor.n by omega)
  refine htc.mma_reads hi (hres.trans ?_)
  obtain ⟨cta, lane, column⟩ := cell
  simp only at hl hcta h0 h1 hr
  simp only [Option.some.injEq, Cell.mk.injEq, rowCta, hlow, hhigh]
  split_ifs <;> refine ⟨?_, ?_, ?_⟩ <;> omega

/-- The lane of a load's cell is below 128. -/
theorem cell_lane (L : Launch) (h a j : Nat) : (tcDataCell32 L h a j).lane < 128 := by
  simp only [tcDataCell32, laneBase, laneOf]
  generalize h % L.block = r
  omega

/-- The leader of a load's cell's CTA is that of its thread's. -/
theorem cell_lead (L : Launch) (h a j : Nat) :
    leadCta (tcDataCell32 L h a j).cta = leadCta (ctaOf L h) := rfl

/-- **SoftCoverLast**: step 7 of the QK block of the score tile a softmax load reads writes each
cell it loads. -/
theorem softCoverLast (hpre : Pre P L mem0) (ht : ScoreFacts L X) (htc : TcFacts L X)
    (htt : TcMmaThreadFacts L X) (hcv : CoverFacts L X) (hS : Score.SFullHandoff L X) :
    ValuesOps.SoftCoverLast L X := by
  intro h i a j vals hh hw hld hj
  have hst : warpOf L h / 4 < 2 := by omega
  obtain ⟨hcells, -, hcnt⟩ := ht.soft_ld hh hw hld
  obtain ⟨jp, pc, p, acq, sc, -, hget, hq⟩ := MbarRing.UnitHandoff.exists_poll (X := X) (h := h)
    (f := i) (m := sFullBar L (ctaOf L h) (warpOf L h / 4)) (c := pArr L X h (warpOf L h / 4) i)
    (by unfold sPolls at hcnt; omega)
  obtain ⟨x, s, rank, ws, hcom, hcx, hmbar, hxc, -⟩ := hS hh hw hget
  obtain ⟨k, -, ⟨hk, cell0, hc0, hS0⟩, hkc, h7⟩ := hcv.qk_sfull hcom hst hmbar
  obtain ⟨d, s', acc, mask, row, col, hi, hpos⟩ := hc0
  have hlead : leadCta (ctaOf L x.1) = ctaOf L x.1 := (ht.mma_cells hi).2.2.1
  have hd := ValuesOps.col0_qk ht htt htc hi hpos hS0 hst
  have hcell := hcells j hj
  unfold InS at hcell
  have hu : sCommits L X x.1 (warpOf L h / 4) k = pArr L X h (warpOf L h / 4) i := by
    rw [hkc, hxc]
    exact hq
  refine ⟨(x.1, k), hk, mma_region hpre ht htc htt hi hpos (cell_lane L h a j)
    (by rw [cell_lead, ← hcx, hlead]) (by omega) (by omega),
    by rw [← hcnt]; exact congrArg (· + 1) hu, h7⟩

/-- **CorrCoverLast**: step 7 of the PV block of the tile before a correction load's credit
writes each cell it loads. -/
theorem corrCoverLast (H : Score.RouteCtx P L mem0 K A X) (ht : ScoreFacts L X)
    (ho : OAccFacts L X) (htc : TcFacts L X) (htt : TcMmaThreadFacts L X) (hcv : CoverFacts L X)
    (hS : Score.SFullHandoff L X) (hO : OAcc.OFullHandoff L X) : ValuesOps.CorrCoverLast L X := by
  intro h i a j st vals hh h8 h12 hld hj hOc
  obtain ⟨st1, hst1, hcells1, -, hq1⟩ := ho.corr_ld hh h8 h12 hld
  obtain ⟨st2, -, -, hcells2, hroute⟩ := H.rt.corr_ld hh h8 h12 hld
  have e1 : st1 = st := by
    have := hcells1 j hj
    unfold InO at this hOc
    omega
  have e2 : st2 = st := by
    have := hcells2 j hj
    unfold InO at this hOc
    omega
  rw [e1] at hq1
  rw [e2] at hroute
  have hst : st < 2 := e1 ▸ hst1
  have hlen : i < (X.tr h).length := Score.TLd.lt hld
  -- the commit observed on the load's route and step 7 of a PV block before it
  obtain ⟨y, k, ⟨hmk, cell0, hc0, hO0⟩, hkc, h7, hcy⟩ : ∃ y : EvId, ∃ k, PvAt X y.1 st k ∧
      pPolls L X y.1 st k = pArr L X h st i ∧ pvStep L X y.1 st k = 7 ∧
      leadCta (ctaOf L y.1) = leadCta (ctaOf L h) := by
    rcases hroute with hs | ⟨jf, pc, p, acq, sc, -, hget, hqI⟩
    · obtain ⟨g, e, hg, hgc, hgw, hgs, -, hge, -⟩ := OAcc.sync_route H hh h8 h12 hst hlen hs
      obtain ⟨jp, pc, p, acq, sc, -, hget, hcq⟩ := MbarRing.UnitHandoff.exists_poll (X := X)
        (h := g) (f := e) (m := sFullBar L (ctaOf L g) (warpOf L g / 4))
        (c := pArr L X h st i) (by rw [hgs]; unfold sPolls at hge; omega)
      obtain ⟨y, s, rank, ws, hcom, hcy, hmbar, hyc, -⟩ := hS hg hgw hget
      rw [hgs] at hmbar hyc hcq
      unfold sPolls at hyc
      obtain ⟨k, -, hpv, hkc, h7⟩ := hcv.pv_sfull hcom hst hmbar (by omega)
      exact ⟨y, k, hpv, by omega, h7, by rw [hcy, hgc]⟩
    · obtain ⟨y, s, rank, ws, hcom, hcy, hmbar, hyc, -⟩ := hO hh h8 h12 hst hget
      have hyc' : oFullCommits L X y.1 st y.2 =
          okPolls (oFullBar L (ctaOf L h) st) ((X.tr h).take jf) := hyc
      obtain ⟨k, -, hpv, hkc, h7⟩ := hcv.pv_ofull hcom hst hmbar hq1 (by rw [hyc']; exact hqI)
      exact ⟨y, k, hpv, hkc, h7, hcy⟩
  obtain ⟨d, s, acc, mask, row, col, hi, hpos⟩ := hc0
  have hlead : leadCta (ctaOf L y.1) = ctaOf L y.1 := (ht.mma_cells hi).2.2.1
  obtain ⟨hd, -⟩ := ValuesOps.col0_pv ht htt htc hi hpos hO0
  have hcell := hcells1 j hj
  rw [e1] at hcell
  unfold InO at hcell
  exact ⟨(y.1, k), hmk, mma_region H.pre ht htc htt hi hpos (cell_lane L h a j)
    (by rw [cell_lead, ← hcy, hlead]) (by omega) (by omega), hkc, h7⟩

/-- **SoftCover**: the QK MMAs of the score tile a softmax load reads write each cell it
loads. -/
theorem softCover (hpre : Pre P L mem0) (ht : ScoreFacts L X) (htc : TcFacts L X)
    (htt : TcMmaThreadFacts L X) (hcv : CoverFacts L X) (hS : Score.SFullHandoff L X) :
    Floats.SoftCover L X := fun hh hw hld hj =>
  have ⟨x, hx, hc, hn, _⟩ := softCoverLast hpre ht htc htt hcv hS hh hw hld hj
  ⟨x, hx, hc, hn⟩

/-- **CorrCover**: the PV MMAs of the tile before a correction load's credit write each cell it
loads. -/
theorem corrCover (H : Score.RouteCtx P L mem0 K A X) (ht : ScoreFacts L X) (ho : OAccFacts L X)
    (htc : TcFacts L X) (htt : TcMmaThreadFacts L X) (hcv : CoverFacts L X)
    (hS : Score.SFullHandoff L X) (hO : OAcc.OFullHandoff L X) : Floats.CorrCover L X :=
  fun hh h8 h12 hld hj hOc =>
    have ⟨x, hx, hc, hn, _⟩ := corrCoverLast H ht ho htc htt hcv hS hO hh h8 h12 hld hj hOc
    ⟨x, hx, hc, hn⟩

end Cover

end
end PTX.Kernels.FlashAttn4Fwd.Proof
