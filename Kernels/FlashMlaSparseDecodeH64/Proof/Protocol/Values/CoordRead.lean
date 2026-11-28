-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.TmaCoord
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IdxStore
import Lemmas.Kit.CountAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.Store
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Use
import Lemmas.Order.ReadLast
import Lemmas.Protocol.UnitHandoff

@[expose] public section

/-! # The bytes the TMA lane reads from the coordinate ring

A byte of a coordinate word the TMA lane reads (quad `q`, word `jj`, at use `u` of slot `s`) is
the byte written by the index lane `2 q + jj / 2` for the use: the lane's write of element
`jj % 2` of its block `4 u + s` (`coord_read_byte`). The TMA lane's poll of `coordReady s` with
`u` earlier ones observes the lane's arrival of use `u` (`coordReady_observes`), before which the
lane made `(2 + σ) (4 u + s + 1)` writes (`index_arrCount`), so it made the write whose
prefix count is `(2 + σ) (4 u + s) + jj % 2` (`exists_countP_eq`), the write of that block's
element (`index_wrCount`). The write precedes the read by the ring (`UnitHandoff` with offset 0);
every other write of the byte is one of the same lane, of an earlier use (program order) or of a
later one (the read precedes it by the empty handoff), or the write itself (equal counts), so the
write is the last before the read (`read_byte_of_last_write_ordered`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow PTX.Kit

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : CoordInputs L X)
include hp hX hFw hR hI hB hN

/-- **A byte the TMA lane reads from the coordinate ring is the byte of an index lane's write.** -/
theorem coord_read_byte {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) (hat : MbarRow.TmaAt L g pc) :
    ∃ (s : Fin 4) (u q jj gw kw pcw : Nat) (aw : Acc) (bsw : List Byte), q < 16 ∧ jj < 4 ∧
      MemRow.WsAcc L (g / L.block) (221728 + 256 * s.val + 16 * q + 4 * jj) 4 a ∧
      gw = g / L.block * L.block + 224 + (2 * q + jj / 2) ∧
      X.get (gw, kw) = some ⟨pcw, .wr aw bsw⟩ ∧ MbarRow.IndexAt L gw pcw ∧
      MemRow.WsAcc L (g / L.block) (221728 + 256 * s.val + 8 * (2 * q + jj / 2) +
        4 * (jj % 2)) 4 aw ∧
      okPolls (mbarLoc L (g / L.block) (.coordReady s)) ((X.tr g).take k) = u + 1 ∧
      arrivals (mbarLoc L (g / L.block) (.coordReady s)) ((X.tr gw).take kw) = u ∧
      ((X.tr gw).take kw).countP idxWr =
        (2 + if (L.tidOf gw).x % 4 = 0 then 1 else 0) * (4 * u + s.val) + jj % 2 ∧
      ∀ i, i < a.size → bs[i]? = some (wbyte aw bsw (a.loc.at i)) := by
  obtain ⟨hpc, s, ⟨q, hq, jj, hjj, hl', hsz⟩, u, hv1, hv2⟩ := tma_rdUse hp hX hFw he hat
  have hg := Frame.lt_of_get hX he
  have hblock := hp.block
  -- the index lane and the quad's word
  obtain ⟨lane, hlane⟩ : ∃ lane : Fin 32, lane.val = 2 * q + jj / 2 := ⟨⟨_, by omega⟩, rfl⟩
  -- the poll of the use and the lane's arrival it observes
  obtain ⟨j', pcj, par, acq, sc, hj', hw', hq'⟩ := UnitHandoff.exists_poll (X := X)
    (m := mbarLoc L (g / L.block) (.coordReady s)) (h := g) (f := k) (c := u) (by omega)
  obtain ⟨-, hall⟩ := coordReady_observes hp hX hFw hR hI hB hN hw'
  obtain ⟨ia, pca, sca, hga, hia, -⟩ := hall lane
  have hwarp : warp L (idxLane L (g / L.block) lane) = 7 := by
    simp only [warp, idxLane, tidOf_x_eq hp, hp.block]; omega
  obtain ⟨hcc, hcount⟩ := index_arrCount hp hX hFw hwarp hga
  have hcta : idxLane L (g / L.block) lane / L.block = g / L.block := by
    simp only [idxLane, hblock]; omega
  have htid : (L.tidOf (idxLane L (g / L.block) lane)).x % 32 = lane.val := by
    simp only [idxLane, tidOf_x_eq hp, hblock]; omega
  have htid4 : (L.tidOf (idxLane L (g / L.block) lane)).x % 4 = lane.val % 4 := by
    simp only [idxLane, tidOf_x_eq hp, hblock]; omega
  rw [hia.trans hq'] at hcount
  set gl := idxLane L (g / L.block) lane with hgl
  obtain ⟨σ0, hσ0⟩ : ∃ σ0 : Nat, σ0 = if (L.tidOf gl).x % 4 = 0 then 1 else 0 := ⟨_, rfl⟩
  rw [← hσ0] at hcount
  -- the write of the byte's element
  obtain ⟨kw, ev, hkw, hpw, hcw⟩ := exists_countP_eq idxWr ((X.tr gl).take ia)
    ((2 + σ0) * (4 * u + s.val) + jj % 2) (by
      rw [hcount]
      have : (2 + σ0) * (4 * u + s.val + 1) = (2 + σ0) * (4 * u + s.val) + (2 + σ0) := by ring
      omega)
  have hkia : kw < ia := by
    by_contra hc
    simp [hc] at hkw
  have hget : X.get (gl, kw) = some ev := by
    change (X.tr gl)[kw]? = some ev
    rw [← hkw, List.getElem?_take]; simp [hkia]
  rw [List.take_take, Nat.min_eq_left hkia.le] at hcw
  obtain ⟨pcw, kd⟩ := ev
  obtain ⟨aw, bsw, rfl⟩ : ∃ aw bsw, kd = .wr aw bsw := by
    cases kd <;> first | (simp [idxWr] at hpw; done) | exact ⟨_, _, rfl⟩
  have hpcw : 2332 ≤ pcw ∧ pcw ≤ 2586 := by simpa [idxWr] using hpw
  have hatw : MbarRow.IndexAt L gl pcw := ⟨hwarp, hpcw.1, by omega⟩
  -- the write is the lane's element of the block
  have hσ1 : σ0 ≤ 1 := by rw [hσ0]; split <;> omega
  obtain ⟨s', u', j', hcls, hu', hpl', hcn⟩ := index_wrCount hp hX hFw hget hatw
  rw [hcw, ← hσ0] at hcn
  rw [hcta] at hu' hpl'
  have hj' : j' < 2 + σ0 := by
    rcases hcls with ⟨j'', hj'', hjj'', -⟩ | ⟨hj2, h4, -⟩
    · omega
    · have : σ0 = 1 := by simp only [hσ0, h4, ite_true]
      omega
  have hsu : 4 * u' + s'.val = 4 * u + s.val ∧ j' = jj % 2 := by
    have h1 := s'.isLt
    have h2 := s.isLt
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hσ1 with h0 | h0 <;> rw [h0] at hcn hj' <;> omega
  obtain ⟨hsu1, hjj'⟩ := hsu
  obtain rfl : s = s' := Fin.ext (by have := s'.isLt; have := s.isLt; omega)
  obtain rfl : u = u' := by omega
  -- the write's access and the byte's place
  obtain ⟨hawl, hawz⟩ : MemRow.WsAcc L (g / L.block) (221728 + 256 * s.val +
      8 * (2 * q + jj / 2) + 4 * (jj % 2)) 4 aw := by
    rcases hcls with ⟨j'', hj'', hjj'', hws⟩ | ⟨hj2, -⟩
    · rw [hcta, htid] at hws
      have : j'' = jj % 2 := by omega
      rw [this, hlane] at hws
      exact hws
    · omega
  have hbytes : ∀ i, i < a.size → bs[i]? = some (wbyte aw bsw (a.loc.at i)) := by
    intro i hi
    have hl0 : a.loc.at i = wsLoc L (g / L.block) (221728 + 256 * s.val + 16 * q + 4 * jj + i) := by
      rw [hl']; simp only [Loc.at, wsLoc, Loc.mk.injEq, true_and]; omega
    have hia' : i < 4 := by have := hsz; omega
    have hcovr : a.Covers (a.loc.at i) := Acc.covers_at hi
    have hcovw : aw.Covers (a.loc.at i) := by
      rw [hl0]
      simp only [Acc.Covers, Loc.InRange, wsLoc, hawl, hawz, true_and]
      constructor <;> omega
    have hLoc : MemRow.LocIn L (g / L.block) .tmaCoord (a.loc.at i) := by
      rw [hl0]
      refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp only [wsLoc, Region.lo, Region.size] <;> omega
    have hrd : X.Access (g, k) a false := Or.inl ⟨bs, ⟨pc, he⟩, rfl⟩
    have hwr : X.Access (gl, kw) aw true := Or.inr (Or.inl ⟨bsw, ⟨pcw, hget⟩, rfl⟩)
    have hIdx : IdxOf L (g / L.block) gl := ⟨Frame.lt_of_get hX hget, lane, rfl⟩
    have hCons : ConsOf L X (g / L.block) g := by
      refine ⟨hg, ⟨128, by omega⟩, ?_⟩
      simp only [coordCons, show ¬ (128 < 128) from by omega, ↓reduceIte]
      exact tma_thread_on hN.tmaOne he (fun _ h => by cases h) ⟨hat, hpc⟩
    have hF := coordReady_handoff hp hX hFw hR hI hB hN (g / L.block) s
    have hE := coordFree_handoff hp hX hFw hR hI hB hN (g / L.block) s
    have hv : ByteCausality L X (a.loc.at i) (.thread (gl, kw)) (.thread (g, k)) :=
      .direct (.of_base L (hF.baseCausality_of_counts (q := u) hCons hIdx hu'.le (by omega)
        hrd.lt))
    have hc0 : (a.loc.at i).cta = g / L.block := by rw [hl0]; rfl
    have hsl : coordSlotOf L (a.loc.at i) = s := by
      rw [hl0]; apply Fin.ext
      simp only [coordSlotOf, wsLoc]
      have := s.isLt
      omega
    have hall : ∀ w' dst' bytes, X.MemWrites w' dst' bytes → dst'.Covers (a.loc.at i) →
        w' = .thread (gl, kw) ∨ ByteCausality L X (a.loc.at i) w' (.thread (gl, kw)) ∨
          ByteCausality L X (a.loc.at i) (.thread (g, k)) w' := by
      intro w' dst' bytes hw'' hc'
      have hint := hw''.intent
      rcases w' with ⟨g'', k''⟩ | ⟨⟨g'', k''⟩, p'⟩
      · obtain rfl : g'' = gl := coord_ww hp hX hFw hN hint hwr hc' hcovw hLoc
        rcases coord_cls hp hX hFw hN hint hc' hLoc with
          ⟨-, -, -, ⟨pc2, bs2, hget2, hat2⟩, u2, h1, h2⟩ | ⟨hfalse, -⟩
        swap
        · cases hfalse
        rw [hsl, hc0] at h1 h2
        obtain ⟨s2, u2', j2, hcls2, har2, hpo2, hcn2⟩ := index_wrCount hp hX hFw hget2 hat2
        rw [← hσ0] at hcn2
        rw [hcta] at har2 hpo2
        obtain ⟨hs2, hj2⟩ : s2 = s ∧ j2 = jj % 2 := by
          rcases hcls2 with ⟨j'', hj'', hjj'', hws⟩ | ⟨hj2, -, hws⟩
          · rw [hcta, htid, hlane] at hws
            obtain ⟨hl2, hz2⟩ := hws
            unfold Acc.Covers at hc'
            rw [hl2, hz2, hl0] at hc'
            simp only [Loc.InRange, wsLoc, true_and] at hc'
            have := s2.isLt
            have := s.isLt
            refine ⟨Fin.ext (by omega), by omega⟩
          · rw [hcta] at hws
            obtain ⟨hl2, hz2⟩ := hws
            unfold Acc.Covers at hc'
            rw [hl2, hz2, hl0] at hc'
            simp only [Loc.InRange, wsLoc, true_and] at hc'
            have := s2.isLt
            have := s.isLt
            have := Nat.div_le_self (lane.val) 4
            have := lane.isLt
            omega
        subst hs2
        subst hj2
        rw [har2] at h1
        subst h1
        have hiw : ∀ (pc' : Nat) (x : Acc) (y : List Byte), 2332 ≤ pc' → pc' ≤ 2586 →
            idxWr ⟨pc', .wr x y⟩ = true := by
          intro pc' x y h1 h2
          simp [idxWr]
          omega
        rcases lt_trichotomy u2' u with hlt | heq | hgt
        · -- an earlier use: program order
          have hk : k'' < kw := by
            by_contra hn
            have h3 : (List.take kw (X.tr gl)).countP idxWr ≤
                (List.take k'' (X.tr gl)).countP idxWr :=
              (List.take_isPrefix_take.mpr (Or.inl (not_lt.mp hn))).countP_le
            rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hσ1 with h0 | h0 <;>
              rw [h0] at hcn2 hcw <;> omega
          exact .inr (.inl (.direct (.of_base L (.single (.inl
            (po_of_overlap hint hwr rfl hk ⟨a.loc.at i, hc', hcovw⟩))))))
        · subst heq
          rcases lt_trichotomy k'' kw with hk | hk | hk
          · have := countP_take_lt_at idxWr (l := X.tr gl) (k' := kw) hk hget2
              (hiw _ _ _ hat2.2.1 (by have := hat2.2.2; omega))
            omega
          · rw [hk]; exact .inl rfl
          · have := countP_take_lt_at idxWr (l := X.tr gl) (k' := k'') hk hget
              (hiw _ _ _ hpcw.1 hpcw.2)
            omega
        · exact .inr (.inr (.direct (.of_base L (hE.baseCausality_of_counts (q := u) hIdx hCons
            hv2.le (by omega) hint.lt))))
      · exfalso
        obtain ⟨i', hi'⟩ := region_thread hp hX hFw (fun b => by simp) (by simp) (by simp) hint hc'
          hLoc
        cases hi'
    have hmr : X.MemReads (.thread (g, k)) a bs := Or.inl ⟨pc, he⟩
    have hmw : X.MemWrites (.thread (gl, kw)) aw bsw := Or.inl ⟨pcw, hget⟩
    have key := read_byte_of_last_write_ordered hX hmr hi hmw hcovw hv hall
    exact key
  refine ⟨s, u, q, jj, gl, kw, pcw, aw, bsw, hq, hjj, ⟨hl', hsz⟩, ?_, hget, hatw, ⟨hawl, hawz⟩,
    hv1, hu', ?_, hbytes⟩
  · rw [hgl]; simp only [idxLane, hlane]
  · rw [hcw, hσ0]

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
