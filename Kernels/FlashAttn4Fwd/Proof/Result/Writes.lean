-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Result.Geometry
public import Lemmas.TensorStore.StoreWrite
public import Lemmas.Execution.ShapeExecution

@[expose] public section

/-! # The writes of the output

Every write of a global byte is a tensor store's slot write (`WriteFacts.global`), and every
tensor store is a store lane's store of half `hh` of stage `st` of an existing item `j`
(`StoreFacts.spec`), whose slot `(x, y, k)` writes byte `k` of O's element
`(tileRow + y, 64 hh + x)` of the item's batch and head (`slot_write`). So every global write is
inside O (`writes_within_output`), and a global byte outside O has no writer (`frame`).

Each tile is written by the cluster and item the schedule assigns (`tile_store`): element
`(batch, head, row, d)` is in work item `w = (batch · h + head) · blocks + row / 512`, item
`w / G` of cluster `w % G`, stage `row % 512 / 256` of the CTA of rank `row % 256 / 128`; that
CTA's store lane 0 exited, so it issued the stage's store of half `d / 64` (`StoreFacts.issued`).
Every other write of the element's byte is the same slot of a store of the same item, stage
and half by a thread of the same CTA, with the same specification (`output_writers`): the
schedule's split is injective (`ItemCoords`, `element_inj`), so the writer's item, stage, half
and CTA are the tile's. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

namespace Result

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The tiles of the schedule -/

/-- The blocks of 512 query rows cover `sq`. -/
theorem blocks_mul (hpre : Pre P L mem0) : 512 * P.blocks = P.sq := by
  have := hpre.sqDiv512
  unfold Params.blocks
  omega

/-- **An existing item's tile is in range**: its batch, head and rows. -/
theorem tile_lt (hpre : Pre P L mem0) (hco : ItemCoords P L) {g j : Nat}
    (hj : workOf L g j < totOf L) :
    tileBatch L g j < P.b ∧ tileHead L g j < P.h ∧ tileBlock L g j < P.blocks := by
  obtain ⟨htot, -, hc⟩ := hco
  rw [htot] at hj
  have hB : 0 < P.blocks := by
    have := blocks_mul hpre
    have := hpre.sqPos
    omega
  simp only [tileBatch, tileHead, tileBlock, hc _ hj]
  exact TileDecomp.split_lt hB hpre.hPos hj

/-- The rows of a stage of an existing item are rows of O. -/
theorem row_lt (hpre : Pre P L mem0) (hco : ItemCoords P L) {g j st y : Nat}
    (hj : workOf L g j < totOf L) (hst : st < 2) (hy : y < 128) : tileRow L g j st + y < P.sq := by
  have hm := (tile_lt hpre hco hj).2.2
  have hb := blocks_mul hpre
  have hr : rankOf L g < 2 := by rw [rankOf_eq hpre]; exact Nat.mod_lt _ (by decide)
  unfold tileRow
  omega

/-- The four store sites are distinct instructions. -/
theorem tma_pc_inj : ∀ st hh st' hh' : Fin 2,
    Store.Site.pc (.tma st hh) = Store.Site.pc (.tma st' hh') → st = st' ∧ hh = hh' := by
  decide

/-- A store lane's tensor store depends on the lane only through its CTA. -/
theorem oSpec_cta {g g' : Nat} (h : ctaOf L g = ctaOf L g') (j st hh : Nat) :
    oSpec P L g j st hh = oSpec P L g' j st hh := by
  simp only [oSpec, oOrigin, tileRow, tileBlock, tileHead, tileBatch, workOf, clusterOf, rankOf, h]

/-! ### The global writes -/

/-- **A slot write of a tensor store**: the store is a store lane's store of half `hh` of stage
`st` of an existing item `j`, and the write is the one-byte write of byte `k` of O's element
`(tileRow + y, 64 hh + x)` of the item. -/
theorem slot_write (hpre : Pre P L mem0) (hco : ItemCoords P L)
    (hX : Consistent L kernel asms mem0 X) (hs : StoreFacts P L X) {i : EvId} {x y k : Nat}
    {a : Acc} {bs : List Byte} (hm : X.MemWrites (.async i (.write (.store x y k))) a bs) :
    ∃ pc j, ∃ st hh : Fin 2, i.1 < L.threads ∧
      X.get i = some ⟨pc, .tensorStore P.oMap (oSpec P L i.1 j st hh)⟩ ∧ warpOf L i.1 = 13 ∧
      StoreSrc L X i.1 i.2 pc (oSpec P L i.1 j st hh) st ∧ pc = Store.Site.pc (.tma st hh) ∧
      arrivals (freeBar L (ctaOf L i.1) st) ((X.tr i.1).take i.2) = j ∧
      workOf L i.1 j < totOf L ∧ x < 64 ∧ y < 128 ∧ k < 2 ∧ a.size = 1 ∧
      a.loc = (elementLoc P P.oBase P.sq (tileBatch L i.1 j) (tileHead L i.1 j)
        (tileRow L i.1 j st + y) (64 * hh + x)).at k := by
  obtain ⟨o, addr, b, -, ⟨pc, hget⟩, hloc, -, hsz, -⟩ := hm
  have hg := event_thread_lt hX hget
  obtain ⟨st, hh, h13, hsrc, hpc, rfl, hj, hspec⟩ := hs.spec hg hget
  rw [hspec] at hloc hget hsrc
  obtain ⟨hx, hy, hk⟩ := oSpec_slot hloc
  obtain ⟨hb, hhd, -⟩ := tile_lt hpre hco hj
  rw [oSpec_writeLoc hx hy hk hh.isLt (row_lt hpre hco hj st.isLt hy) hhd hb] at hloc
  exact ⟨pc, _, st, hh, hg, hget, h13, hsrc, hpc, rfl, hj, hx, hy, hk, hsz,
    (Option.some.inj hloc).symm⟩

/-- Every global write is a one-byte tensor-store slot write inside O. -/
def WritesWithinOutput (P : Params) (X : Execution) : Prop :=
  ∀ w a bs, X.MemWrites w a bs → a.loc.space = .global →
    a.size = 1 ∧ a.loc.cta = 0 ∧ P.oBase ≤ a.loc.addr ∧
      a.loc.addr < P.oBase + tensorBytes P P.sq ∧ ∃ i x y k, w = .async i (.write (.store x y k))

/-- **Every global write is a tensor-store slot write inside O.** -/
theorem writes_within_output (hpre : Pre P L mem0) (hco : ItemCoords P L)
    (hX : Consistent L kernel asms mem0 X) (hs : StoreFacts P L X) (hw : WriteFacts L X) :
    WritesWithinOutput P X := by
  intro w a bs hm hsp
  obtain ⟨i, x, y, k, rfl⟩ := hw.global w a bs hm hsp
  obtain ⟨pc, j, st, hh, -, -, -, -, -, -, hj, hx, hy, hk, hsz, hloc⟩ :=
    slot_write hpre hco hX hs hm
  obtain ⟨hb, hhd, -⟩ := tile_lt hpre hco hj
  have hin := element_in (d := 64 * hh + x) hb hhd (row_lt hpre hco hj st.isLt hy) (by omega) hk
  rw [← hloc] at hin
  refine ⟨hsz, ?_, hin.1, hin.2, i, x, y, k, rfl⟩
  rw [hloc]
  rfl

/-- **A global byte outside O has no writer.** -/
theorem frame (hw : WritesWithinOutput P X) {l : Loc} (hs : l.space = .global)
    (hout : ¬ (l.cta = 0 ∧ P.oBase ≤ l.addr ∧ l.addr < P.oBase + tensorBytes P P.sq)) :
    ∀ w a bs, X.MemWrites w a bs → ¬ a.Covers l := by
  intro w a bs hm hc
  obtain ⟨hsp, hcta, hlo, hhi⟩ := hc
  obtain ⟨h1, h2, h3, h4, -⟩ := hw w a bs hm (hsp ▸ hs)
  rw [h1] at hhi
  exact hout ⟨hcta.trans h2, by omega, by omega⟩

/-! ### The tiles' stores -/

/-- The work item of a tile. -/
theorem tile_work (hpre : Pre P L mem0) {batch head row : Nat} (hb : batch < P.b)
    (hh : head < P.h) (hr : row < P.sq) :
    (batch * P.h + head) * P.blocks + row / 512 < P.items ∧
      ((batch * P.h + head) * P.blocks + row / 512) / P.blocks / P.h = batch ∧
      ((batch * P.h + head) * P.blocks + row / 512) / P.blocks % P.h = head ∧
      ((batch * P.h + head) * P.blocks + row / 512) % P.blocks = row / 512 := by
  have hb512 := blocks_mul hpre
  have hm : row / 512 < P.blocks := by omega
  obtain ⟨hq1, hq2⟩ := Nat.digits_of_lt (q := batch * P.h + head) hm
  obtain ⟨hh1, hh2⟩ := Nat.digits_of_lt (q := batch) hh
  refine ⟨?_, by rw [hq1, hh1], by rw [hq1, hh2], hq2⟩
  have e1 : batch * P.h + head + 1 ≤ P.b * P.h := by
    calc batch * P.h + head + 1 ≤ batch * P.h + P.h := by omega
      _ = (batch + 1) * P.h := by ring
      _ ≤ P.b * P.h := Nat.mul_le_mul_right _ hb
  calc (batch * P.h + head) * P.blocks + row / 512 < (batch * P.h + head + 1) * P.blocks := by
        have : (batch * P.h + head + 1) * P.blocks = (batch * P.h + head) * P.blocks + P.blocks :=
          by ring
        omega
    _ ≤ P.b * P.h * P.blocks := Nat.mul_le_mul_right _ e1
    _ = P.items := by unfold Params.items; ring

/-- The store lane 0 of the CTA of rank `r` of cluster `cl`. -/
theorem tile_lane (hpre : Pre P L mem0) {cl r : Nat} (hcl : cl < P.clusters) (hr : r < 2) :
    (2 * cl + r) * L.block + 416 < L.threads ∧ ctaOf L ((2 * cl + r) * L.block + 416) = 2 * cl + r ∧
      warpOf L ((2 * cl + r) * L.block + 416) = 13 ∧
      rankOf L ((2 * cl + r) * L.block + 416) = r ∧
      clusterOf L ((2 * cl + r) * L.block + 416) = cl := by
  have hblk := hpre.block
  have hcta : ctaOf L ((2 * cl + r) * L.block + 416) = 2 * cl + r := by
    simp only [ctaOf, hblk]; omega
  refine ⟨?_, hcta, ?_, ?_, ?_⟩
  · simp only [Launch.threads, hblk, hpre.grid]; omega
  · simp only [warpOf, hblk]; omega
  · rw [rankOf_eq hpre, hcta]; omega
  · rw [clusterOf_eq hpre, hcta]; omega
/-- **Each tile is written by the cluster and item the schedule assigns**: element `d` of row
`row` of head `head` of batch `batch` is slot `(x, y)` of the store of half `hh` of stage `st` of
item `j` that store lane `g` issued. -/
theorem tile_store (hpre : Pre P L mem0) (hco : ItemCoords P L)
    (hd : Complete L X) (hs : StoreFacts P L X)
    (hw : WriteFacts L X) {batch head row d : Nat} (hb : batch < P.b) (hh : head < P.h)
    (hr : row < P.sq) (hdd : d < 128) :
    ∃ g kk j, ∃ st hh : Fin 2, ∃ x y, g < L.threads ∧
      X.get (g, kk) = some ⟨Store.Site.pc (.tma st hh),
        .tensorStore P.oMap (oSpec P L g j st hh)⟩ ∧ warpOf L g = 13 ∧
      StoreSrc L X g kk (Store.Site.pc (.tma st hh)) (oSpec P L g j st hh) st ∧
      arrivals (freeBar L (ctaOf L g) st) ((X.tr g).take kk) = j ∧ workOf L g j < totOf L ∧
      x < 64 ∧ y < 128 ∧ tileBatch L g j = batch ∧ tileHead L g j = head ∧
      tileRow L g j st + y = row ∧ 64 * hh + x = d := by
  obtain ⟨htot, hG, hc⟩ := hco
  obtain ⟨hWlt, hWb, hWh, hWm⟩ := tile_work hpre hb hh hr
  generalize (batch * P.h + head) * P.blocks + row / 512 = W at hWlt hWb hWh hWm
  have hclW : W % P.clusters < P.clusters := Nat.mod_lt _ hpre.clustersPos
  obtain ⟨hgt, -, hwarp, hrank, hcl⟩ := tile_lane hpre hclW (r := row % 256 / 128) (by omega)
  generalize (2 * (W % P.clusters) + row % 256 / 128) * L.block + 416 = g at hgt hwarp hrank hcl
  have hwork : workOf L g (W / P.clusters) = W := by
    simp only [workOf, hcl, hG]
    exact Nat.mod_add_div' W P.clusters
  have hj : workOf L g (W / P.clusters) < totOf L := by rw [hwork, htot]; exact hWlt
  -- the lane exited, so it issued the store of the tile
  have hexit : ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩ :=
    (hd.1 g hgt).resolve_left (hw.started g hgt)
  obtain ⟨kk, a, s, hget, harr⟩ := hs.issued hgt hwarp hexit (W / P.clusters) hj
    ⟨row % 512 / 256, by omega⟩ ⟨d / 64, by omega⟩
  obtain ⟨st, hh', -, hsrc, hpc, rfl, -, hspec⟩ := hs.spec hgt hget
  obtain ⟨rfl, rfl⟩ := tma_pc_inj _ _ _ _ hpc.symm
  rw [harr] at hspec
  subst hspec
  have hcW := hc W hWlt
  refine ⟨g, kk, _, _, _, d % 64, row % 128, hgt, hget, hwarp, hsrc, harr, hj,
    Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), ?_, ?_, ?_, ?_⟩
  · simp only [tileBatch, hwork, hcW, hWb]
  · simp only [tileHead, hwork, hcW, hWh]
  · simp only [tileRow, tileBlock, hwork, hcW, hWm, hrank]
    omega
  · simp only
    omega

end Result

end

end PTX.Kernels.FlashAttn4Fwd.Proof
