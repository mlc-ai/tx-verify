-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.TcMmaSourcesDone
public import Kernels.FlashAttn4Fwd.Proof.Protocol.PReadyPublished
public import Kernels.FlashAttn4Fwd.Proof.Protocol.P2Warp
public import Lemmas.Tcgen05.TcMmaACell

@[expose] public section

/-! # The stores a PV MMA reads its A operand from

A PV MMA of stage `st` and tile `u` (`pPolls = u + 1`) reads its A operand from Tensor Memory, at
cells of the stage's probabilities in its pair (`ScoreFacts.pv_polls`), each in the first 128
lanes (the PV descriptor is not a half datapath, `aCell_lane`). The cell is in the row of one
softmax thread of the stage (`cellThread`), and that thread stored it in tile `u`
(`pvAStore`, the existence part of `Safety.PvAStores`):

* below column `112`: the MMA thread's poll of phase `u` of the P-ready object observes the
  thread's arrival of tile `u` (`PReadyHandoff`), which comes after its stores of tile `u` of
  those columns (`TcMmaThreadFacts.soft_low`);
* from column `112`: the MMA thread's poll of phase `u` of the second P-ready object observes the
  arrival of tile `u` of the thread's warp's elected lane (`P2Handoff`), which comes after that
  lane's `u`-th warp barrier (`P2Facts.p2_arrive`); the barrier's instance holds the thread's
  `u`-th warp barrier (`WarpBar.partner`, `WarpBar.ordinal_eq`), which comes after its stores of
  tile `u` of those columns (`TcMmaThreadFacts.soft_high`).

The store's value is the value it wrote (`StoreValue`), and the store is live until the MMA:
every release of an allocation covering a cell an MMA accesses follows the MMA's completion
(`MmaLive`, the allocation premise; it is the deallocation order `Safety.MmaDoneDealloc` read on
the cell's allocation record). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof TcMma

noncomputable section

namespace TcMmaSources
open Score

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- **MmaLive**: every release of an allocation covering a cell an MMA accesses follows the MMA's
completion. -/
def MmaLive (L : Launch) (X : Execution) : Prop :=
  ∀ {i : EvId} {cell : Cell}, IsMma X i → X.MmaAccess i cell → ∀ cta r, r ∈ X.tmemHistory cta →
    Tmem.Pair.Covers L X r cell.cta i cell.column → ∀ release, Tmem.Pair.ReleaseOf L X r release →
      DoneBefore L X i release

/-- A write is live until an MMA accessing its cell. -/
theorem sourceLive (hlive : MmaLive L X) {i src : EvId} {cell : Cell} (hi : IsMma X i)
    (ha : X.MmaAccess i cell) : SourceLive L X src i cell := by
  intro cta r hr hcov release hrel
  obtain ⟨pci, di, si, acci, maski, hgi⟩ := hi.get
  refine .inl ⟨fun ⟨a, vals, _, pc, h⟩ => ?_, fun ⟨a, vals, _, pc, h⟩ => ?_,
    fun _ => hlive hi ha cta r hr hcov release hrel⟩
  · rw [hgi] at h
    cases h
  · rw [hgi] at h
    cases h

/-- The descriptor of an MMA reading A from Tensor Memory: the PV one. -/
theorem pv_desc (htt : TcMmaThreadFacts L X) {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} (hi : X.MmaIssue i d s acc mask) (ha : s.aTmem.isSome = true) :
    s.descriptor.kind = .f16 .f16 .f32 ∧ s.descriptor.m = 256 ∧ s.descriptor.n = 128 ∧
      s.descriptor.group = .two ∧ s.descriptor.ws = false ∧ halfDatapath s.descriptor = false := by
  have hd := Option.some.inj ((htt.mma_desc hi).2.2 ha)
  rw [← hd]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The descriptor of an MMA reading A from shared memory: the QK one. -/
theorem qk_desc (htt : TcMmaThreadFacts L X) {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} (hi : X.MmaIssue i d s acc mask) (ha : s.aTmem = none) :
    s.descriptor.kind = .f16 .f16 .f32 ∧ s.descriptor.m = 256 ∧ s.descriptor.n = 128 ∧
      s.descriptor.group = .two ∧ s.descriptor.ws = false ∧ halfDatapath s.descriptor = false := by
  have hd := Option.some.inj ((htt.mma_desc hi).2.1 ha)
  rw [← hd]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The softmax thread of stage `st` whose row holds cell `c`. -/
def cellThread (L : Launch) (st : Nat) (c : Cell) : Nat := c.cta * L.block + 128 * st + c.lane

/-- The softmax thread of a cell of the first 128 lanes of a launched CTA: of the stage, of the
cell's CTA and lane. -/
theorem cellThread_spec (hpre : Pre P L mem0) {st : Nat} {c : Cell} (hst : st < 2)
    (hl : c.lane < 128) (hc : c.cta < L.grid) :
    cellThread L st c < L.threads ∧ warpOf L (cellThread L st c) = 4 * st + c.lane / 32 ∧
      ctaOf L (cellThread L st c) = c.cta ∧ tcDataCell32 L (cellThread L st c) 0 c.column = c := by
  have hb := hpre.block
  obtain ⟨cta, lane, col⟩ := c
  dsimp only at hl hc ⊢
  unfold cellThread warpOf ctaOf
  unfold Launch.threads
  simp only [tcDataCell32, laneBase, laneOf, Cell.mk.injEq]
  rw [hb]
  have : (cta + 1) * 512 ≤ L.grid * 512 := Nat.mul_le_mul_right _ hc
  rw [Nat.add_mul] at this
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- A cell of an issuer's pair is in a launched CTA. -/
theorem pair_cta_lt (hpre : Pre P L mem0) {g : Nat} {c : Cell} (hg : g < L.threads)
    (hc : leadCta c.cta = ctaOf L g) : c.cta < L.grid ∧ ctaOf L g ≤ c.cta ∧
      c.cta ≤ ctaOf L g + 1 := by
  have hb := hpre.block
  have hgr := hpre.grid
  unfold leadCta ctaOf at hc
  unfold ctaOf
  unfold Launch.threads at hg
  rw [hb] at hg hc ⊢
  have hlt : g / 512 < L.grid := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    exact hg
  omega

/-- **The store a PV MMA reads an A byte from**: the softmax thread of the cell's row stored the
cell in the MMA's tile. -/
theorem pvAStore (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (ht : ScoreFacts L X)
    (htc : TcFacts L X) (htt : TcMmaThreadFacts L X) (hF : P2Facts L X) (hP : PReadyHandoff L X)
    (hU : P2Handoff L X) {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {index pos : Nat} {cell : Cell} (hi : X.MmaIssue i d s acc mask)
    (ha : aCell s index = some (cell, pos)) :
    ∃ h k a j, ∃ vals : List Value, h < L.threads ∧ warpOf L h < 8 ∧ X.TSt (h, k) a vals .s32x32b ∧
      j < vals.length ∧ cell = tcDataCell32 L h a j ∧
      sPolls L X h (warpOf L h / 4) k = pPolls L X i.1 (warpOf L h / 4) i.2 := by
  obtain ⟨c0, hc0⟩ := htc.mma_cell hi
  obtain ⟨hgx, -, hl, st, hst, hcs | hcs⟩ := ht.mma_cells hi
  · have hnone := htc.qk_smem hst hi hc0 (hcs c0 hc0).1
    simp [aCell, hnone] at ha
  obtain ⟨hO, -⟩ := hcs c0 hc0
  obtain ⟨hP1, -, haT, hA⟩ := ht.pv_polls hi hc0 hO
  obtain ⟨hPc, hcta, hhigh⟩ := hA index cell pos ha
  have hlane := aCell_lane (pv_desc htt hi haT).2.2.2.2.2 ha
  obtain ⟨hgrid, hc1, hc2⟩ := pair_cta_lt hpre hgx hcta
  obtain ⟨hhl, hhw, hhc, hcell⟩ := cellThread_spec hpre hst hlane hgrid
  set h := cellThread L st cell
  have hhw8 : warpOf L h < 8 := by omega
  have hhst : warpOf L h / 4 = st := by omega
  have hlh : leadCta (ctaOf L h) = ctaOf L i.1 := by rw [hhc, hcta]
  have hxm : IsMma X i := ⟨_, _, _, _, hi⟩
  obtain ⟨hin, -⟩ := mma_in ht hxm
  have hP' : InP (warpOf L h / 4) (tcDataCell32 L h 0 cell.column) := by rw [hcell, hhst]; exact hPc
  refine ⟨h, ?_⟩
  rw [hhst]
  obtain ⟨u, hu⟩ : ∃ u, pPolls L X i.1 st i.2 = u + 1 := ⟨pPolls L X i.1 st i.2 - 1, by omega⟩
  rw [hu]
  by_cases hH : InPHigh st cell
  · -- from column `112`: the second P-ready object and the warp barrier
    have hp2 := hhigh hH
    obtain ⟨j, pc, p, acq, sc, -, hwj, hcnt⟩ := MbarRing.UnitHandoff.exists_poll
      (X := X) (m := pReady2Bar L (ctaOf L i.1) st) (h := i.1) (f := i.2)
      (c := u) (by rw [← hu, ← hp2]; exact le_refl _)
    have hab : 4 * (cell.cta - ctaOf L i.1) + cell.lane / 32 < 8 := by omega
    obtain ⟨k, hk, hsy⟩ := hU (ctaOf L i.1) st hl hst i.1 j pc p acq sc _ hin hwj hcnt
      _ ⟨⟨_, hab⟩, rfl⟩
    obtain ⟨hgc, hgw⟩ := p2Prod_spec (X := X) hpre (c := ctaOf L i.1) hst ⟨_, hab⟩
    set g := p2Prod L X (ctaOf L i.1) st ⟨_, hab⟩
    obtain ⟨rs, ⟨tx, cnt, pck, hx⟩, -⟩ := id hsy
    have hg := event_thread_lt hX hx
    obtain ⟨-, -, -, -, -, -, -, harr, hwb, -⟩ := hF.p2_arrive hg hst hx
    simp only at hgc hgw harr hwb
    have hgw8 : warpOf L g < 8 := by omega
    have hs : SameWarp L g h :=
      sameWarp_of hg hhl (by rw [hgc, hhc]; omega) (by rw [hgw, hhw]; omega)
    obtain ⟨x, hxk, ev, hev, hq, hcx⟩ := Flow.exists_nth Execution.isWarpBar (X.tr g)
      (n := u) (k := k) (by change _ < warpBars X g k; omega)
    obtain ⟨pcx, m, inst, rfl⟩ : ∃ pc m inst, ev = ⟨pc, .warpBar m inst⟩ := by
      obtain ⟨pc, kind⟩ := ev
      cases kind <;> simp_all [Execution.isWarpBar]
    have hxw : X.WarpBar (g, x) m inst := ⟨pcx, hev⟩
    have hmg := soft_mask (h := g) (g := h) hF hg hgw8
    have hmh := soft_mask (h := h) (g := g) hF hhl hhw8
    obtain ⟨y, hp⟩ := WarpBar.partner hX hs hxw (hmg _ _ _ hxw)
    have hord := WarpBar.ordinal_eq hX hs hmg hmh hp
    obtain ⟨m', inst', -, hyw⟩ := hp
    have hH' : InPHigh (warpOf L h / 4) (tcDataCell32 L h 0 cell.column) := by
      rw [hcell, hhst]; exact hH
    obtain ⟨k', a', j', vals', -, hst', hj', hceq, hsp⟩ := htt.soft_high hhl hhw8 hyw hP' hH'
    refine ⟨k', a', j', vals', hhl, hhw8, hst', hj', by rw [hceq, hcell], ?_⟩
    rw [← hhst, hsp, ← hord]
    unfold warpBars
    rw [hcx]
  · -- below column `112`: the P-ready object
    obtain ⟨j, pc, p, acq, sc, -, hwj, hcnt⟩ := MbarRing.UnitHandoff.exists_poll
      (X := X) (m := pReadyBar L (ctaOf L i.1) st) (h := i.1) (f := i.2)
      (c := u) (by rw [← hu]; exact le_refl _)
    obtain ⟨e, he, hsy⟩ := hP (ctaOf L i.1) st hl hst i.1 j pc p acq sc _ hin hwj hcnt h
      ⟨hhl, hlh, .inl ⟨hhw8, hhst⟩⟩
    obtain ⟨rs, ⟨tx, cnt, pce, hev⟩, -⟩ := id hsy
    have hev' : X.get (h, e) = some ⟨pce,
        .arrive (pReadyBar L (leadCta (ctaOf L h)) (warpOf L h / 4)) tx cnt true rs⟩ := by
      rw [hlh, hhst]
      exact hev
    have hH' : ¬ InPHigh (warpOf L h / 4) (tcDataCell32 L h 0 cell.column) := by
      rw [hcell, hhst]; exact hH
    obtain ⟨k', a', j', vals', -, hst', hj', hceq, hsp⟩ := htt.soft_low hhl hhw8 hev' hP' hH'
    refine ⟨k', a', j', vals', hhl, hhw8, hst', hj', by rw [hceq, hcell], ?_⟩
    rw [← hhst, hsp, hhst]
    unfold pArr
    rw [hlh, he]

/-- **PvAStores**: each A cell of a PV MMA is written by a softmax store of the MMA's tile, with
the value it stored, live until the MMA. -/
theorem pvAStores (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (ht : ScoreFacts L X)
    (htc : TcFacts L X) (htt : TcMmaThreadFacts L X) (hF : P2Facts L X) (hP : PReadyHandoff L X)
    (hU : P2Handoff L X) (hlive : MmaLive L X) (A' : List Assumption) {i : EvId} {d : Nat}
    {s : OperandSpec} {acc : Bool} {mask : List Nat} {index pos : Nat} {cell : Cell}
    (hi : X.MmaIssue i d s acc mask) (ha : aCell s index = some (cell, pos)) :
    ∃ h k a j, ∃ vals : List Value, ∃ value, h < L.threads ∧ warpOf L h < 8 ∧
      X.TSt (h, k) a vals .s32x32b ∧ j < vals.length ∧ cell = tcDataCell32 L h a j ∧
      sPolls L X h (warpOf L h / 4) k = pPolls L X i.1 (warpOf L h / 4) i.2 ∧
      vals[j]? = some value ∧ Wrote L A' X (h, k) cell value ∧ SourceLive L X (h, k) i cell := by
  obtain ⟨h, k, a, j, vals, hh, hw, hs, hj, hc, hu⟩ := pvAStore hpre hX ht htc htt hF hP hU hi ha
  refine ⟨h, k, a, j, vals, vals[j], hh, hw, hs, hj, hc, hu, List.getElem?_eq_getElem hj,
    .inr (.inl ⟨a, vals, _, j, hs, List.getElem?_eq_getElem hj,
      hc.trans (tcDataCell_s32x32b _ _ _ _).symm⟩),
    sourceLive hlive ⟨_, _, _, _, hi⟩ (.inr (.inr ⟨d, s, acc, mask, index, pos, hi, ha⟩))⟩

end TcMmaSources

end
end PTX.Kernels.FlashAttn4Fwd.Proof
