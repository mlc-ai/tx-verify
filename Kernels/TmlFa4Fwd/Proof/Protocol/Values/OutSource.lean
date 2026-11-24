-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.TileGeom
public import Kernels.TmlFa4Fwd.Proof.Lib.OutputFrame
public import Lemmas.TensorStore.SourceBytes
import Kernels.TmlFa4Fwd.Proof.Correction.Export.FinalStores
import Kernels.TmlFa4Fwd.Proof.Correction.Export.FstPoll
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.MemStore
import Kernels.TmlFa4Fwd.Proof.Lib.GlobalWrites
import Kernels.TmlFa4Fwd.Proof.Protocol.Operands
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Global
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Ordered
import Kernels.TmlFa4Fwd.Proof.Protocol.Staging.KvFinal
import Kernels.TmlFa4Fwd.Proof.Protocol.Staging.QFinal
import Kernels.TmlFa4Fwd.Proof.Protocol.Staging.Read
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.LseStore
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.StoreWarp
import Lemmas.TensorStore.StoreWrite
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The staging sources of the output bytes

A tensor store of the output warp reads, for an output byte, the byte of its staging slot
(`stageLoc`). The correction lane of the byte's row stored it before its ready arrival, which the
store's ready poll observes, and every other write of the byte precedes that store
(`stage_source`). So the output byte is the byte of a final store (`outRoute`), whose value is the
correction warp's (`FinalVals`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow TcMma Tm AsyncCopy

noncomputable section
open Classical

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- Byte `k` of the staging word of column `d` of row `ρ` of stage `st`. -/
def stageLoc (L : Launch) (c st ρ d k : Nat) : Loc :=
  ⟨.shared, c, L.sharedBase + (3072 + 65536 * st + 16384 * (d / 32)) +
    TensorSwizzle.offset .b128 (L.sharedBase + (3072 + 65536 * st + 16384 * (d / 32)))
      (128 * ρ + 4 * (d % 32) + k)⟩

/-- **What the final stores of the correction lanes hold**: a byte of the staging word of a column
of a valid row is that of a final load of the lane, of the credit after the tile's last round, over
the row sum. -/
def FinalVals (p : Params) (L : Launch) (X : Execution) (T : Nat → Option Tile)
    (D : Nat → RowData) : Prop :=
  ∀ h i pc a bs st d k, 8 ≤ Prologue.warpIndex L h → Prologue.warpIndex L h < 12 →
    X.get (h, i) = some ⟨pc, .wr a bs⟩ → st < 2 → d < 128 → k < 4 →
    a.Covers (stageLoc L (h / L.block) st (rowIx L h) d k) → ∀ t, T (h / L.block) = some t →
    t.Valid p st (rowIx L h) →
    ∃ i' ad j x, ∃ vals : List Value, X.TLd (h, i') ad vals .s32x32b ∧ j < vals.length ∧
      (tcDataCell32 L h ad j).column = 256 + 128 * st + d ∧ pArr L X h st i' = t.n ∧
      vals[j]? = some (.float .f32 x) ∧
      wbyte a bs (stageLoc L (h / L.block) st (rowIx L h) d k) = some ((Value.float .f32
        (x * (D (softLane L (h / L.block) st (rowIx L h))).rs⁻¹)).byteAt k)

/-- **The byte a tensor store reads.** -/
theorem store_readLoc {g b head tile x y k : Nat} {st : Fin 2} {bx : Fin 4} (hx : x < 32)
    (hy : y < 128) (hk : k < 4) :
    TensorStore.readLoc (Epilogue.writebackStoreSpec p L g b head tile st bx) x y k =
      some (stageLoc L (g / L.block) st.val y (32 * bx.val + x) k) := by
  have hcx : x < TensorTile.count p.oMap.box 0 := (outputBoxWidthShared p).symm ▸ hx
  have hry : y < TensorTile.rows p.oMap.box := (outputBoxRowsShared p).symm ▸ hy
  have hck : k < p.oMap.format.bytes := hk
  have hslot : TensorTransfer.slotAt p.oMap x y k = some ⟨⟨x, hcx⟩, ⟨y, hry⟩, ⟨k, hck⟩⟩ := by
    unfold TensorTransfer.slotAt
    rw [dite_eq_left hcx, dite_eq_left hry, dite_eq_left hck]
  unfold TensorStore.readLoc
  rw [show TensorTransfer.slotAt (Epilogue.writebackStoreSpec p L g b head tile st
    bx).descriptor x y k = some ⟨⟨x, hcx⟩, ⟨y, hry⟩, ⟨k, hck⟩⟩ from hslot, Option.map_some]
  have hlin : TensorTile.linearByte p.oMap.box p.oMap.format.bytes p.oMap.swizzle x y k =
      y * 128 + x * 4 + k := by
    have hf : p.oMap.format.bytes = 4 := rfl
    have hs : p.oMap.swizzle = .b128 := rfl
    simp only [TensorTile.linearByte, TensorTile.rowBytes, outputBoxWidthShared, hf, hs,
      TensorTile.swizzleWidth]
    norm_num
  have hd : (32 * bx.val + x) / 32 = bx.val := by omega
  have hm : (32 * bx.val + x) % 32 = x := by omega
  simp only [Epilogue.writebackStoreSpec, TensorBox.sharedLoc, TensorTile.sharedByte,
    Epilogue.sharedSlot, hlin, stageLoc, hd, hm]
  have e : y * 128 + x * 4 + k = 128 * y + 4 * x + k := by omega
  rw [e]
  rfl

private theorem stageLoc_row {c st ρ d k : Nat} (hk : k < 4) :
    ∃ u < 128, (stageLoc L c st ρ d k).addr =
      L.sharedBase + 3072 + 65536 * st + 16384 * (d / 32) + 128 * ρ + u := by
  have hr := TensorSwizzle.offset_row .b128
    (L.sharedBase + (3072 + 65536 * st + 16384 * (d / 32))) (128 * ρ + 4 * (d % 32) + k)
  exact ⟨TensorSwizzle.offset .b128 (L.sharedBase + (3072 + 65536 * st + 16384 * (d / 32)))
    (128 * ρ + 4 * (d % 32) + k) % 128, Nat.mod_lt _ (by decide), by simp only [stageLoc]; omega⟩

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- A final store that covers a staging byte is of the lane of its row. -/
private theorem fst_lane {c st ρ d k h i pc : Nat} {a : Acc} {bs : List Byte}
    (hρ : ρ < 128) (hd : d < 128) (hk : k < 4) (hw : 8 ≤ Prologue.warpIndex L h)
    (hw1 : Prologue.warpIndex L h ≤ 11) (he : X.get (h, i) = some ⟨pc, .wr a bs⟩)
    (hc : a.Covers (stageLoc L c st ρ d k)) : h = c * L.block + 256 + ρ := by
  obtain ⟨st', ⟨hz, q, hq, w, hw4, hloc⟩, -⟩ := corr_fst hp hX hFw hw hw1 he (hc.1.symm.trans rfl)
  obtain ⟨u, hu, hadd⟩ := stageLoc_row (L := L) (c := c) (st := st) (ρ := ρ) (d := d) hk
  have hb := hp.block
  have hst' := st'.isLt
  obtain ⟨-, c2, c3, c4⟩ := hc
  rw [hz] at c4
  rw [hloc] at c2 c3 c4
  rw [hadd] at c3 c4
  simp only [stageLoc] at c2
  simp only [Correction.rowN, hb] at c2 c3 c4
  simp only [Prologue.warpIndex, hb] at hw hw1
  rw [hb]
  have hd4 : d / 32 < 4 := by omega
  generalize d / 32 = e at hd4 c3 c4
  omega

/-- **The source of a staging byte a tensor store reads**: a final store of the lane of the byte's
row, the last write of the byte before the read and the lane's last write of it. -/
theorem stage_last {o kt addr b head tile x y k : Nat} {st : Fin 2} {bx : Fin 4}
    (hi : X.TensorStoreIssue (o, kt) addr
      (Epilogue.writebackStoreSpec p L o b head tile st bx)) (hx : x < 32) (hy : y < 128)
    (hk : k < 4) : ∃ h i pc a bs, h = o / L.block * L.block + 256 + y ∧
      X.get (h, i) = some ⟨pc, .wr a bs⟩ ∧
      SourceOrdered L X (.async (o, kt) (.read (.store x y k)))
        (stageLoc L (o / L.block) st.val y (32 * bx.val + x) k) (.thread (h, i)) a bs ∧
      ∀ j pc' a' bs', X.get (h, j) = some ⟨pc', .wr a' bs'⟩ →
        a'.Covers (stageLoc L (o / L.block) st.val y (32 * bx.val + x) k) → j ≤ i := by
  set l := stageLoc L (o / L.block) st.val y (32 * bx.val + x) k with hl
  have hbx := bx.isLt
  have hst := st.isLt
  have hd : 32 * bx.val + x < 128 := by omega
  have hb := hp.block
  have hr : TensorStore.readLoc (Epilogue.writebackStoreSpec p L o b head tile st bx) x y k =
      some l := store_readLoc hx hy hk
  obtain ⟨u, hu, hadd⟩ := stageLoc_row (L := L) (c := o / L.block) (st := st.val) (ρ := y)
    (d := 32 * bx.val + x) hk
  rw [← hl, show (32 * bx.val + x) / 32 = bx.val by omega] at hadd
  obtain ⟨h, hh⟩ : ∃ h, h = o / L.block * L.block + 256 + y := ⟨_, rfl⟩
  have hhc : h / L.block = o / L.block := by rw [hh, hb]; omega
  have hhw : 8 ≤ Prologue.warpIndex L h ∧ Prologue.warpIndex L h ≤ 11 := by
    rw [hh]; simp only [Prologue.warpIndex, hb]; omega
  have hhr : Correction.rowN L h = y := by rw [hh]; simp only [Correction.rowN, hb]; omega
  -- a store of the lane covers the byte
  obtain ⟨st', hbox, hall⟩ := store_after hp hX hFw hi
  obtain ⟨-, -, h1, h2⟩ := hbox x y k l hr
  have hst' : st' = st := Fin.ext (by have := st'.isLt; omega)
  subst hst'
  obtain ⟨⟨ka, pca, tx, c, rel, sc, hka⟩, -⟩ := hall h hhc hhw.1 hhw.2
  obtain ⟨-, js, -, pcj, a0, bs0, -, -, -, hwr, hz0, hal0⟩ :=
    corr_fst_before hp hX hFw hhw.1 hhw.2 hka (q := bx.val) (t := u / 4) hbx (by omega)
  have hcov0 : a0.Covers l := by
    refine ⟨by rw [hal0]; rfl, by rw [hal0, hhc]; rfl, ?_, ?_⟩
    · rw [hal0, hhr]; simp only; omega
    · rw [hal0, hz0, hhr]; simp only; omega
  -- the last one
  let Q : Nat → Prop := fun j => ∃ pc a bs, X.get (h, j) = some ⟨pc, .wr a bs⟩ ∧ a.Covers l
  have hjs : js ≤ (X.tr h).length := (List.getElem?_eq_some_iff.mp hwr).1.le
  have hQ : Q (Nat.findGreatest Q (X.tr h).length) :=
    Nat.findGreatest_spec (P := Q) hjs ⟨pcj, a0, bs0, hwr, hcov0⟩
  obtain ⟨pc, a, bs, he, hcov⟩ := id hQ
  have hsp : l.space = .shared := rfl
  have hlast : ∀ j pc' a' bs', X.get (h, j) = some ⟨pc', .wr a' bs'⟩ → a'.Covers l →
      j ≤ Nat.findGreatest Q (X.tr h).length := fun j pc' a' bs' hj hcj => by
    by_contra hgt
    have hjl := (List.getElem?_eq_some_iff.mp (show (X.tr h)[j]? = _ from hj)).1.le
    exact Nat.findGreatest_is_greatest (not_le.mp hgt) hjl ⟨pc', a', bs', hj, hcj⟩
  refine ⟨h, _, pc, a, bs, hh, he, ⟨.inl ⟨pc, he⟩, hcov,
    .direct (fst_store hp hX hFw hhw.1 hhw.2 he hcov hi hr), fun other fp bs' hw' hc' => ?_⟩, hlast⟩
  have hmid : InMid L l := ⟨hsp, by omega, by omega⟩
  rcases sh_region hp hX hFw hw'.intent hc' hsp with hA | hA | hA | ⟨-, hM⟩
  · obtain ⟨-, b1, b2⟩ := hA
    omega
  · obtain ⟨-, b1, b2⟩ := hA
    omega
  · have hin := hA
    unfold InBias at hin
    omega
  cases hM with
  | fst hw2 hw3 hge hcta =>
    rename_i h' j' pc' bs2
    obtain rfl : h' = h := (fst_lane hp hX hFw hy hd hk hw2 hw3 hge hc').trans hh.symm
    rcases Nat.lt_trichotomy j' (Nat.findGreatest Q (X.tr h').length) with hlt | heq | hgt
    · right; left
      have hil := (List.getElem?_eq_some_iff.mp he).1
      have hac : (X.get (h', j')).bind Event.acc = some fp := by rw [hge]; rfl
      have hac' : (X.get (h', Nat.findGreatest Q (X.tr h').length)).bind Event.acc = some a := by
        rw [he]; rfl
      exact .direct (.of_base L (.single (.inl ⟨rfl, hlt, hil,
        fun hs => hs.not_overlap rfl hlt hac hac' ⟨l, hc', hcov⟩⟩)))
    · left
      rw [heq]
    · exact absurd (hlast _ _ _ _ hge hc') (not_le.mpr hgt)
  | row hcp hcta hlo =>
    exact .inr (.inl (kv_copy_fst hp hX hFw hcp hc' ⟨_, _, hw'.intent, hc'⟩ ⟨_, hw'.intent, hc'⟩
      hhw.1 hhw.2 he hsp hcov (hcta.symm.trans hhc.symm)))
  | tma hce hwl hcta hhi =>
    exact .inr (.inl (q_copy_fst hp hX hFw hce hwl hmid.2.1 hhi hhw.1 hhw.2 he hsp hcov))

/-- **The source of a staging byte a tensor store reads.** -/
theorem stage_source {o kt addr b head tile x y k : Nat} {st : Fin 2} {bx : Fin 4}
    (hi : X.TensorStoreIssue (o, kt) addr
      (Epilogue.writebackStoreSpec p L o b head tile st bx)) (hx : x < 32) (hy : y < 128)
    (hk : k < 4) : ∃ h i pc a bs, h = o / L.block * L.block + 256 + y ∧
      X.get (h, i) = some ⟨pc, .wr a bs⟩ ∧
      SourceOrdered L X (.async (o, kt) (.read (.store x y k)))
        (stageLoc L (o / L.block) st.val y (32 * bx.val + x) k) (.thread (h, i)) a bs := by
  obtain ⟨h, i, pc, a, bs, h1, h2, h3, -⟩ := stage_last hp hX hFw hi hx hy hk
  exact ⟨h, i, pc, a, bs, h1, h2, h3⟩

/-- **The route of the output bytes**, given the values of the final stores. -/
theorem outRoute {D : Nat → RowData} (hV : FinalVals p L X (tileOf p L) D) :
    OutRoute p L X (tileOf p L) D := by
  intro b hb hd hhd row hrow d hdd k hk w a bytes hw hc
  have hg : ((p.oLoc (p.qOffset b + row) hd d).at k).space = .global := rfl
  have hR := outputByte_in (packedRow_lt hp hb hrow) hhd hdd hk
  rcases globalWriteIntentSources hX hw.intent (hc.1.symm.trans hg) with
    ⟨i, pc, bs, rfl, hpc, he⟩ | ⟨i, x, y, z, pc, addr, spec, rfl, -, he, hloc, hz⟩
  · exfalso
    obtain ⟨ih, ij⟩ := i
    obtain ⟨-, -, t, hT, st, -, hv, hal, hs4⟩ := lse_store hp hX hFw he (hc.1.symm.trans hg)
    obtain ⟨-, hok⟩ := tileOk hp hT
    have hq := packedRow_lt hp hok.batch hv
    have hh' := hok.head
    generalize p.qOffset t.batch + t.rowOf st (rowIx L ih) = q at hal hq
    generalize t.head = h' at hal hh'
    have hL : p.lseRegion.Contains ((p.oLoc (p.qOffset b + row) hd d).at k) := by
      obtain ⟨c1, c2, c3, c4⟩ := hc
      rw [hal] at c3 c4
      rw [hs4] at c4
      have h0 := lseByte_in (p := p) hq hh' (k := ((p.oLoc (p.qOffset b + row) hd d).at k).addr -
        (p.lseLoc q h').addr) (by omega)
      have e : (p.lseLoc q h').at (((p.oLoc (p.qOffset b + row) hd d).at k).addr -
          (p.lseLoc q h').addr) = (p.oLoc (p.qOffset b + row) hd d).at k := by
        simp only [Loc.at, Params.lseLoc, Params.oLoc, globalLoc, Loc.mk.injEq, true_and] at c3 ⊢
        omega
      rwa [e] at h0
    obtain ⟨-, -, o1, o2⟩ := hR
    obtain ⟨-, -, l1, l2⟩ := hL
    rcases hp.separate.1 with h | h <;> omega
  obtain ⟨o, addr', byte, ho, hiss, hwl, hwb, -, rfl, -⟩ := hw
  obtain ⟨-, b', hb', st, bx, hlo, hhi, hspec⟩ := Epilogue.store_issue hp hX
      (store_warp hp hX hFw hiss) hiss
  obtain ⟨-, hh'⟩ := Epilogue.assignedCoordinates_valid hp hlo hhi
  have hal : a.loc = (p.oLoc (p.qOffset b + row) hd d).at k := Acc.loc_of_one hc hz
  rw [hspec, writebackWriteLoc hp st bx x y z hb' hh'] at hwl
  split at hwl
  swap
  · cases hwl
  rename_i hin
  obtain ⟨hx, hy, hz4, hr'⟩ := hin
  simp only [Option.some.injEq] at hwl
  rw [hal] at hwl
  have hcol : 32 * bx.val + x < 128 := by have := bx.isLt; omega
  have hq1 := packedRow_lt hp hb hrow
  have hq2 := packedRow_lt hp hb' hr'
  -- the indices
  have haddr : 4 * (((p.qOffset b' + (Epilogue.stageRow
      (Epilogue.assignedCoordinates p b' (i.1 / L.block)).1 st + y)) * p.heads +
        (Epilogue.assignedCoordinates p b' (i.1 / L.block)).2) * 128 + (32 * bx.val + x)) + z =
      4 * (((p.qOffset b + row) * p.heads + hd) * 128 + d) + k := by
    have := congrArg Loc.addr hwl
    simp only [Params.oLoc, globalLoc, Loc.at] at this
    omega
  set R1 := p.qOffset b' + (Epilogue.stageRow
    (Epilogue.assignedCoordinates p b' (i.1 / L.block)).1 st + y) with hR1
  set H1 := (Epilogue.assignedCoordinates p b' (i.1 / L.block)).2 with hH1
  have e1 : z = k ∧ 32 * bx.val + x = d ∧ R1 * p.heads + H1 = (p.qOffset b + row) * p.heads + hd :=
      by
    refine ⟨?_, ?_, ?_⟩ <;> omega
  obtain ⟨rfl, rfl, e3⟩ := e1
  have e4 : R1 = p.qOffset b + row ∧ H1 = hd := by
    have h0 : 0 < p.heads := by omega
    have d1 : (R1 * p.heads + H1) / p.heads = R1 := by
      rw [Nat.mul_comm, Nat.mul_add_div h0, Nat.div_eq_of_lt hh', Nat.add_zero]
    have d2 : ((p.qOffset b + row) * p.heads + hd) / p.heads = p.qOffset b + row := by
      rw [Nat.mul_comm, Nat.mul_add_div h0, Nat.div_eq_of_lt hhd, Nat.add_zero]
    have h1 : R1 = p.qOffset b + row := by rw [← d1, e3, d2]
    exact ⟨h1, by rw [h1] at e3; omega⟩
  have hbb : b' = b := by
    have hr1 : p.qOffset b' ≤ p.qOffset b + row ∧ p.qOffset b + row < p.qOffset (b' + 1) := by
      have : p.qLength b' = p.qOffset (b' + 1) - p.qOffset b' := rfl
      omega
    have hr2 : p.qOffset b + row < p.qOffset (b + 1) := by
      have : p.qLength b = p.qOffset (b + 1) - p.qOffset b := rfl
      omega
    rcases lt_trichotomy b' b with hlt | hlt | hlt
    · have := hp.qOffset_mono (show b' + 1 ≤ b from hlt) (by omega)
      omega
    · exact hlt
    · have := hp.qOffset_mono (show b + 1 ≤ b' from hlt) (by omega)
      omega
  subst hbb
  have hrow' : Epilogue.stageRow (Epilogue.assignedCoordinates p b' (i.1 / L.block)).1 st + y =
      row := by omega
  -- the staging source
  obtain ⟨o', kt⟩ := i
  simp only at *
  have hspec' := hspec
  rw [hspec] at hiss
  obtain ⟨h, i', pc', a', bs', hh, hge, hsrc⟩ := stage_source hp hX hFw hiss hx hy hk
  have hb512 := hp.block
  have hhc : h / L.block = o' / L.block := by rw [hh, hb512]; omega
  have hgl := Frame.lt_of_get hX he
  have hT : tileOf p L (o' / L.block) = some (workTile p (o' / L.block) b') :=
    tileOf_eq (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hgl)) ⟨hb', hlo, hhi⟩
  have hri : rowIx L h = y := by rw [hh]; simp only [rowIx, hb512]; omega
  have hhw : 8 ≤ Prologue.warpIndex L h ∧ Prologue.warpIndex L h < 12 := by
    rw [hh]; simp only [Prologue.warpIndex, hb512]; omega
  obtain ⟨i2, ad, j, v, vals, hld, hj, hcl, hpa, hv, hwby⟩ := hV h i' pc' a' bs' st.val
    (32 * bx.val + x) z hhw.1 hhw.2 hge st.isLt hcol hk
    (by rw [hhc, hri]; exact hsrc.2.1) _ (by rw [hhc]; exact hT)
    (by rw [hri]; exact (congrArg (· < p.qLength b') hrow').mpr hrow)
  have hread := hX.store_read_byte ho (by rw [hspec']; rfl) hwb
    (by rw [hspec']; exact store_readLoc hx hy hz4) hsrc
  rw [hhc, hri] at hwby
  rw [hwby] at hread
  refine ⟨_, st.val, h, i2, ad, j, v, vals, by rw [hhc]; exact hT, rfl, e4.2, st.isLt, hhw.1,
    hhw.2, ?_, hld, hj, hcl, hpa, hv, ?_⟩
  · rw [hri, ← hrow']
    rfl
  · rw [hhc, hri, ← hread, ← hal]
    simp [wbyte]

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
