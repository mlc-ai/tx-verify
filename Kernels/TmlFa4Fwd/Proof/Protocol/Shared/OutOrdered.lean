-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.MemOrdered
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.OutSource
import Kernels.TmlFa4Fwd.Proof.Correction.Export.LseAddr
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.StoreReady
import Kernels.TmlFa4Fwd.Proof.Lib.GlobalWrites
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Global
import Kernels.TmlFa4Fwd.Proof.Protocol.Staging.Read
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.LseStore
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.StoreWarp
import Lemmas.Arith.MixedRadix
import Lemmas.TensorStore.StoreWrite
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The output writes of one byte are ordered, or write the same value

A row of a head is of one tile, and a tile of one CTA (`row_unique`). So two log-sum-exp stores of a
word are of one lane, and two writes of an O byte are of one staging byte, whose source is one final
store (`stage_source`): they write its byte. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.Kernels.TmlFa4Fwd.Proof.Values

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A lane's earlier write of a byte is before its later one. -/
theorem wr_po {g u v pcu pcv : Nat} {au av : Acc} {bu bv : List Byte} {l : Loc}
    (hu : X.get (g, u) = some ⟨pcu, .wr au bu⟩) (hv : X.get (g, v) = some ⟨pcv, .wr av bv⟩)
    (hcu : au.Covers l) (hcv : av.Covers l) (hlt : u < v) :
    ByteCausality L X l (.thread (g, u)) (.thread (g, v)) := by
  have hau : (X.get (g, u)).bind Event.acc = some au := by rw [hu]; rfl
  have hav : (X.get (g, v)).bind Event.acc = some av := by rw [hv]; rfl
  exact .direct (.of_base L (.single (.inl ⟨rfl, hlt, (List.getElem?_eq_some_iff.mp hv).1,
    fun hs => hs.not_overlap rfl hlt hau hav ⟨l, hcu, hcv⟩⟩)))

/-- **A CTA is the only one of its tile.** -/
theorem work_inj (hp : Pre p L m) {c c' b : Nat} (h : Work p c b) (h' : Work p c' b)
    (he : Epilogue.assignedCoordinates p b c = Epilogue.assignedCoordinates p b c') : c = c' := by
  have h0 : 0 < p.heads := by
    have := hp.shape.2.2.1
    unfold Params.heads
    omega
  have key : ∀ {x : Nat}, Work p x b → sectionItem (requestTiles p b) p.heads
      (sectionWidth (requestTiles p b) p.heads)
      (Epilogue.assignedCoordinates p b x).1 (Epilogue.assignedCoordinates p b x).2 =
        x - tilePrefix p b * p.heads := by
    rintro x ⟨-, h1, h2⟩
    rw [tilePrefix_succ, Nat.add_mul] at h2
    exact (sectionItem_coords (sectionWidth_pos h0) (by omega)).2.2
  have k1 := key h
  have k2 := key h'
  rw [he, k2] at k1
  obtain ⟨-, h1, -⟩ := h
  obtain ⟨-, h2, -⟩ := h'
  omega

/-- **A row of a head is of one tile.** -/
theorem row_unique (hp : Pre p L m) {c c' b b' s s' r r' : Nat} (h : Work p c b)
    (h' : Work p c' b') (hs : s < 2) (hs' : s' < 2) (hr : r < 128) (hr' : r' < 128)
    (hv : 256 * (Epilogue.assignedCoordinates p b c).1 + 128 * s + r < p.qLength b)
    (hv' : 256 * (Epilogue.assignedCoordinates p b' c').1 + 128 * s' + r' < p.qLength b')
    (hh : (Epilogue.assignedCoordinates p b c).2 = (Epilogue.assignedCoordinates p b' c').2)
    (hq : p.qOffset b + (256 * (Epilogue.assignedCoordinates p b c).1 + 128 * s + r) =
      p.qOffset b' + (256 * (Epilogue.assignedCoordinates p b' c').1 + 128 * s' + r')) :
    c = c' ∧ s = s' ∧ r = r' := by
  have below : ∀ {x y z : Nat}, x < y → y < p.batch → z < p.qLength x →
      p.qOffset x + z < p.qOffset y := by
    intro x y z hxy hy hz
    have := hp.qOffset_mono (show x + 1 ≤ y from hxy) (by omega)
    have : p.qLength x = p.qOffset (x + 1) - p.qOffset x := rfl
    omega
  obtain rfl : b = b' := by
    rcases lt_trichotomy b b' with hlt | heq | hlt
    · have := below hlt h'.1 hv
      omega
    · exact heq
    · have := below hlt h.1 hv'
      omega
  refine ⟨work_inj hp h h' (Prod.ext (by omega) hh), by omega, by omega⟩

/-- An access of an LSE word covers no O byte. -/
theorem lse_not_o (hp : Pre p L m) {q h : Nat} {a : Acc} {l : Loc}
    (hq : q < p.totalQ) (hh : h < p.heads)
    (hl : a.loc = p.lseLoc q h) (hz : a.size = 4) (hc : a.Covers l)
    (ho : p.oRegion.Contains l) : False := by
  have hmul := Nat.mul_le_mul_right p.lseStride (show h ≤ p.heads - 1 by omega)
  obtain ⟨-, -, c3, c4⟩ := hc
  rw [hl] at c3 c4
  rw [hz] at c4
  simp only [Params.lseLoc, globalLoc] at c3 c4
  refine not_both hp.separate.1 ho ⟨ho.1, ho.2.1, ?_, ?_⟩ <;> simp only [Params.lseRegion] <;>
    omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **A write of an O byte** is a slot of a tensor store of its tile. -/
theorem o_write {w : Ref} {a : Acc} {l : Loc} (hw : X.Intent w a true) (hc : a.Covers l)
    (ho : p.oRegion.Contains l) : ∃ i x y k, w = .async i (.write (.store x y k)) ∧
      a.loc = l ∧ a.size = 1 ∧ ∃ addr b, Work p (i.1 / L.block) b ∧ ∃ (st : Fin 2) (bx : Fin 4),
        X.TensorStoreIssue i addr (Epilogue.writebackStoreSpec p L i.1 b
          (Epilogue.assignedCoordinates p b (i.1 / L.block)).2
          (Epilogue.assignedCoordinates p b (i.1 / L.block)).1 st bx) ∧
        x < 32 ∧ y < 128 ∧ k < 4 ∧
        256 * (Epilogue.assignedCoordinates p b (i.1 / L.block)).1 + 128 * st.val + y <
          p.qLength b ∧
        l = (p.oLoc (p.qOffset b + (256 * (Epilogue.assignedCoordinates p b (i.1 / L.block)).1 +
          128 * st.val + y)) (Epilogue.assignedCoordinates p b (i.1 / L.block)).2
            (32 * bx.val + x)).at k := by
  have hs : a.loc.space = .global := hc.1.symm.trans ho.1
  rcases globalWriteIntentSources hX hw hs with
    ⟨i, pc, bs, rfl, -, he⟩ | ⟨i, x, y, k, pc, addr, spec, rfl, -, he, hloc, hz⟩
  · exfalso
    obtain ⟨ih, ij⟩ := i
    obtain ⟨-, -, t, hT, st, -, hv, hal, hz⟩ := lse_store hp hX hFw he hs
    obtain ⟨-, hok⟩ := tileOk hp hT
    exact lse_not_o hp (packedRow_lt hp hok.batch hv) hok.head hal hz hc ho
  obtain ⟨-, b, hb, st, bx, hlo, hhi, rfl⟩ := Epilogue.store_issue hp hX
      (store_warp hp hX hFw ⟨pc, he⟩) ⟨pc, he⟩
  have hal : a.loc = l := Acc.loc_of_one hc hz
  rw [writebackWriteLoc hp st bx x y k hb (Epilogue.assignedCoordinates_valid hp hlo hhi).2] at hloc
  split at hloc
  swap
  · cases hloc
  rename_i hin
  obtain ⟨hx, hy, hk, hr⟩ := hin
  simp only [Option.some.injEq] at hloc
  exact ⟨i, x, y, k, rfl, hal, hz, addr, b, ⟨hb, hlo, hhi⟩, st, bx, ⟨pc, he⟩, hx, hy, hk, hr,
    hal.symm.trans hloc.symm⟩

/-- **The O bytes are written with one value.** -/
theorem o_same {e f : Ref} {a b : Acc} {l : Loc} (he : X.Intent e a true) (hf : X.Intent f b true)
    (ha : a.Covers l) (hb : b.Covers l) (ho : p.oRegion.Contains l) :
    SameValueWrites X e f a b := by
  obtain ⟨i, x, y, k, rfl, hal, haz, addr, r, hW, st, bx, hi, hx, hy, hk, hv, hl⟩ :=
    o_write hp hX hFw he ha ho
  obtain ⟨i', x', y', k', rfl, hal', haz', addr', r', hW', st', bx', hi', hx', hy', hk', hv',
    hl'⟩ :=
    o_write hp hX hFw hf hb ho
  refine ⟨he, hf, ⟨hal.trans hal'.symm, haz.trans haz'.symm⟩, fun bs bs' hw hw' => ?_⟩
  -- one staging byte
  have hh := (Epilogue.assignedCoordinates_valid hp hW.2.1 hW.2.2).2
  have hh' := (Epilogue.assignedCoordinates_valid hp hW'.2.1 hW'.2.2).2
  have hadd := congrArg Loc.addr (hl.symm.trans hl')
  simp only [Params.oLoc, globalLoc, Loc.at] at hadd
  have hbx := bx.isLt
  have hbx' := bx'.isLt
  obtain ⟨hk1, hd1, hrow⟩ : k = k' ∧ 32 * bx.val + x = 32 * bx'.val + x' ∧
      (p.qOffset r + (256 * (Epilogue.assignedCoordinates p r (i.1 / L.block)).1 + 128 * st.val +
        y)) * p.heads + (Epilogue.assignedCoordinates p r (i.1 / L.block)).2 =
      (p.qOffset r' + (256 * (Epilogue.assignedCoordinates p r' (i'.1 / L.block)).1 +
        128 * st'.val + y')) * p.heads +
          (Epilogue.assignedCoordinates p r' (i'.1 / L.block)).2 := by
    refine ⟨?_, ?_, ?_⟩ <;> omega
  obtain ⟨hq, hhd⟩ := Nat.digits_of_eq hh hh' hrow
  obtain ⟨hcc, hst, hyy⟩ := row_unique hp hW hW' st.isLt st'.isLt hy hy' hv hv' hhd hq
  obtain rfl : st = st' := Fin.ext hst
  obtain rfl : bx = bx' := Fin.ext (by omega)
  obtain rfl : x = x' := by omega
  subst hk1 hyy
  -- its source
  obtain ⟨o, kt⟩ := i
  obtain ⟨o', kt'⟩ := i'
  simp only at hcc
  obtain ⟨h1, j1, pc1, a1, bs1, hh1, hg1, hs1, hl1⟩ := stage_last hp hX hFw hi hx hy hk
  obtain ⟨h2, j2, pc2, a2, bs2, hh2, hg2, hs2, hl2⟩ := stage_last hp hX hFw hi' hx hy hk
  rw [← hcc] at hs2 hh2 hl2
  obtain rfl : h1 = h2 := hh1.trans hh2.symm
  obtain rfl : j1 = j2 :=
    le_antisymm (hl2 _ _ _ _ hg1 hs1.2.1) (hl1 _ _ _ _ hg2 hs2.2.1)
  have hee := hg1.symm.trans hg2
  simp only [Option.some.injEq, Event.mk.injEq, Kind.wr.injEq] at hee
  obtain ⟨-, rfl, rfl⟩ := hee
  -- both bytes are the source's
  have val : ∀ {o₀ kt₀ addr₀ r₀ hd₀ tl₀ : Nat} {c : Acc} {cs : List Byte},
      o₀ / L.block = o / L.block → X.TensorStoreIssue (o₀, kt₀) addr₀
        (Epilogue.writebackStoreSpec p L o₀ r₀ hd₀ tl₀ st bx) →
      SourceOrdered L X (.async (o₀, kt₀) (.read (.store x y k)))
        (stageLoc L (o / L.block) st.val y (32 * bx.val + x) k) (.thread (h1, j1)) a1 bs1 →
      X.MemWrites (.async (o₀, kt₀) (.write (.store x y k))) c cs →
      ∃ v, cs = [v] ∧ some v = wbyte a1 bs1
        (stageLoc L (o / L.block) st.val y (32 * bx.val + x) k) := by
    intro o₀ kt₀ addr₀ r₀ hd₀ tl₀ c cs hc₀ hi₀ hS hm
    obtain ⟨ob, addr1, v, hob, hiss, -, hwb, -, rfl, -⟩ := hm
    obtain ⟨pcx, hx1⟩ := hiss
    obtain ⟨pcy, hy1⟩ := hi₀
    have hsp := hx1.symm.trans hy1
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorStore.injEq] at hsp
    obtain ⟨-, -, hsp⟩ := hsp
    exact ⟨v, rfl, hX.store_read_byte hob (by rw [hsp]; rfl) hwb
      (by rw [hsp, ← hc₀]; exact store_readLoc hx hy hk) hS⟩
  obtain ⟨v, rfl, hv1⟩ := val rfl hi hs1 hw
  obtain ⟨v', rfl, hv2⟩ := val hcc.symm hi' hs2 hw'
  rw [Option.some.inj (hv1.trans hv2.symm)]

/-- **Two log-sum-exp stores of a byte are of one lane.** -/
theorem lse_lane {g g' i i' pc pc' : Nat} {a b : Acc} {bs bs' : List Byte} {l : Loc}
    (he : X.get (g, i) = some ⟨pc, .wr a bs⟩) (hf : X.get (g', i') = some ⟨pc', .wr b bs'⟩)
    (ha : a.Covers l) (hb : b.Covers l) (hg : l.space = .global) : g = g' := by
  have hga : a.loc.space = .global := ha.1.symm.trans hg
  have hgb : b.loc.space = .global := hb.1.symm.trans hg
  obtain ⟨hw, hw1, -⟩ := lse_store hp hX hFw he hga
  obtain ⟨hw', hw1', -⟩ := lse_store hp hX hFw hf hgb
  obtain ⟨r, hr, hlo, hhi, st, hv, hl, hz⟩ := corr_lse hp hX hFw hw (by omega) he hga
  obtain ⟨r', hr', hlo', hhi', st', hv', hl', hz'⟩ := corr_lse hp hX hFw hw' (by omega) hf hgb
  have hq := packedRow_lt hp hr hv
  have hq' := packedRow_lt hp hr' hv'
  have hst : p.totalQ ≤ p.lseStride := hp.lseStride
  obtain ⟨-, -, c3, c4⟩ := ha
  obtain ⟨-, -, d3, d4⟩ := hb
  rw [hl] at c3 c4
  rw [hl'] at d3 d4
  rw [hz] at c4
  rw [hz'] at d4
  simp only [Params.lseLoc, globalLoc] at c3 c4 d3 d4
  obtain ⟨hhd, hqq⟩ := Nat.digits_of_eq (lt_of_lt_of_le hq hst) (lt_of_lt_of_le hq' hst)
    (show (Epilogue.assignedCoordinates p r (g / L.block)).2 * p.lseStride + _ =
      (Epilogue.assignedCoordinates p r' (g' / L.block)).2 * p.lseStride + _ by omega)
  have hm := Nat.mod_lt (g % L.block) (show 0 < 128 by decide)
  have hm' := Nat.mod_lt (g' % L.block) (show 0 < 128 by decide)
  obtain ⟨hc, -, hρ⟩ := row_unique hp ⟨hr, hlo, hhi⟩ ⟨hr', hlo', hhi'⟩ st.isLt st'.isLt hm hm'
    hv hv' hhd hqq
  have hb := hp.block
  simp only [Prologue.warpIndex, hb] at hw hw1 hw' hw1' hc hρ
  omega

/-- **The output writes of one byte are ordered, or write the same value.** -/
theorem out_ordered : OutOrdered p L X := by
  intro e f a b l hcon ha hb hl hE
  have hg : l.space = .global := hl.elim (·.1) (·.1)
  obtain ⟨he, hf, -, -⟩ := out_conflict hp hX hFw hcon ha hb (by rw [hg]; decide)
    (by rw [hg]; decide)
  by_cases ho : p.oRegion.Contains l
  · exact (hE (o_same hp hX hFw he hf ha hb ho)).elim
  have thr : ∀ {w : Ref} {c : Acc}, X.Intent w c true → c.Covers l →
      ∃ i pc bs, w = .thread i ∧ X.get i = some ⟨pc, .wr c bs⟩ := by
    intro w c hw hc
    rcases globalWriteIntentSources hX hw (hc.1.symm.trans hg) with
      ⟨i, pc, bs, rfl, -, h⟩ | ⟨i, x, y, k, pc, addr, spec, rfl, -, h, hloc, hz⟩
    · exact ⟨i, pc, bs, rfl, h⟩
    · exfalso
      rcases global_write_shape hp hX hFw hw (hc.1.symm.trans hg) with
        ⟨q, -, h', -, -, h4⟩ | ⟨-, h4⟩
      · omega
      · rw [Acc.loc_of_one hc hz] at h4
        exact ho h4
  obtain ⟨⟨g, i⟩, pc, bs, rfl, hge⟩ := thr he ha
  obtain ⟨⟨g', i'⟩, pc', bs', rfl, hgf⟩ := thr hf hb
  obtain rfl := lse_lane hp hX hFw hge hgf ha hb hg
  rcases Nat.lt_trichotomy i i' with hlt | rfl | hlt
  · exact .inl (wr_po hge hgf ha hb hlt)
  · exact (hcon.1 rfl).elim
  · exact .inr (wr_po hgf hge hb ha hlt)

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
