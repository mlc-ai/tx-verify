-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.CoordLoad
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Closed
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IdxStore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.TokenValid
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region
import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg0
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.Store
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.ValidByte
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IdxEvent
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.VmBlk
import Lemmas.Order.ReadLast
import Lemmas.Protocol.UnitHandoff

@[expose] public section

/-! # The word a validity read returns is the index lanes' bytes

The four bytes of the validity read at pc 289 of lane `g` in its block `r` are the bytes of four
index lanes' stores (`valid_read_byte`), the bytes of 8-bit words whose bit `c` is the validity of
the slot at position `64 r + 8 o + c` of the main cache (`r` below the main cache's blocks,
`64 (r - M) + 8 o + c` of the extra cache from them on, `index_validByte`), `o = 4 half + jb` the
byte's place. The read's word is the four bytes in little-endian order. -/

/-! # The bytes warpgroup 0 reads from the validity ring

Byte `jb` of the validity read at pc 289 of lane `g` (block `r`, the lane's half `h`) is the byte
`4 h + jb` of slot `r % 4`, the byte written by the index lane `4 (4 h + jb)` of its block `r`
(its store with `3 r + 2` stores before it): the lane's poll of `coordReady` with `r / 4` earlier
ones observes the lane's arrival of the use (`coordReady_observes`), before which the lane made
`3 (r + 1)` stores. The write precedes the read by the ring; every other write of the byte is the
lane's own, of an earlier or later use, or the write itself, so it is the last before the read
(`read_byte_of_last_write_ordered`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow PTX.Kit

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : CoordInputs L X)
include hp hX hFw hR hI hB hN

/-- **A byte the validity read returns is the byte of an index lane's write.** -/
theorem valid_read_byte {g k : Nat} (hal : LaneUbFree X g k) {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨289, .rd a bs⟩) (hat : MbarRow.Wg0At L g 289) {jb : Nat}
    (hjb : jb < 4) :
    ∃ (gl kw pcw : Nat) (aw : Acc) (bsw : List Byte),
      gl = g / L.block * L.block + 224 + 4 * (4 * ((L.tidOf g).x / 32 / 2) + jb) ∧
      X.get (gl, kw) = some ⟨pcw, .wr aw bsw⟩ ∧ MbarRow.IndexAt L gl pcw ∧ aw.size = 1 ∧
      aw.loc = a.loc.at jb ∧
      ((X.tr gl).take kw).countP idxWr = 3 * w0Closed ((X.tr g).take k) + 2 ∧
      bs[jb]? = some (wbyte aw bsw (a.loc.at jb)) := by
  have hat0 := hat
  obtain ⟨s, u, ⟨hl', hsz⟩, hv1, hv2, hcl⟩ := wg0_vmBlk_pre hp hX hFw hal he hat
  have hg := Frame.lt_of_get hX he
  have hblock := hp.block
  obtain ⟨hw4, -⟩ := hat0
  have ht : (L.tidOf g).x < 128 := MemRow.wg0_tid hw4
  have hhalf : (L.tidOf g).x / 32 / 2 < 2 := by omega
  obtain ⟨lane, hlane⟩ : ∃ lane : Fin 32, lane.val = 4 * (4 * ((L.tidOf g).x / 32 / 2) + jb) :=
    ⟨⟨_, by omega⟩, rfl⟩
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
  have htid4 : (L.tidOf (idxLane L (g / L.block) lane)).x % 4 = 0 := by
    simp only [idxLane, tidOf_x_eq hp, hblock]; omega
  rw [hia.trans hq'] at hcount
  simp only [htid4, ↓reduceIte] at hcount
  set gl := idxLane L (g / L.block) lane with hgl
  obtain ⟨kw, pcw, aw, bsw, hkia, hget, hpcw, hcw⟩ :=
    idxWr_event_before (X := X) (gl := gl) (ia := ia) (m := 3 * (4 * u + s.val) + 2)
      (by rw [hcount]; omega)
  have hatw : MbarRow.IndexAt L gl pcw := ⟨hwarp, hpcw.1, by omega⟩
  obtain ⟨s', u', j', hcls, hu', hpl', hcn⟩ := index_wrCount hp hX hFw hget hatw
  rw [hcw] at hcn
  simp only [htid4, ↓reduceIte] at hcn
  rw [hcta] at hu' hpl'
  obtain ⟨hj2, -, hawl, hawz⟩ : j' = 2 ∧ (L.tidOf gl).x % 4 = 0 ∧
      aw.loc = wsLoc L (g / L.block) (221696 + 8 * s'.val + (L.tidOf gl).x % 32 / 4) ∧
      aw.size = 1 := by
    rcases hcls with ⟨j'', hj'', hjj'', -⟩ | ⟨hj2, h4, hws⟩
    · omega
    · rw [hcta] at hws
      exact ⟨hj2, h4, hws⟩
  have hsu : s = s' ∧ u = u' := by
    have h1 := s'.isLt
    have h2 := s.isLt
    refine ⟨Fin.ext (by omega), by omega⟩
  obtain ⟨hs', hu''⟩ := hsu
  subst hs' hu''
  refine ⟨gl, kw, pcw, aw, bsw, ?_, hget, hatw, hawz, ?_, ?_, ?_⟩
  · simp only [hgl, idxLane, hlane]
  · rw [htid] at hawl
    rw [hawl, hl']
    simp only [Loc.at, wsLoc, Loc.mk.injEq, true_and]
    omega
  · rw [hcw, hcl]
  · rw [htid] at hawl
    have hl0 : a.loc.at jb = wsLoc L (g / L.block)
        (221696 + 8 * s.val + 4 * ((L.tidOf g).x / 32 / 2) + jb) := by
      rw [hl']; simp only [Loc.at, wsLoc, Loc.mk.injEq, true_and]; omega
    have hia' : jb < a.size := by omega
    have hcovr : a.Covers (a.loc.at jb) := Acc.covers_at hia'
    have hcovw : aw.Covers (a.loc.at jb) := by
      rw [hl0]
      simp only [Acc.Covers, Loc.InRange, wsLoc, hawl, hawz, true_and]
      constructor <;> omega
    have hLoc : MemRow.LocIn L (g / L.block) .tokenValid (a.loc.at jb) := by
      rw [hl0]
      have := s.isLt
      refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp only [wsLoc, Region.lo, Region.size] <;> omega
    have hrd : X.Access (g, k) a false := Or.inl ⟨bs, ⟨289, he⟩, rfl⟩
    have hwr : X.Access (gl, kw) aw true := Or.inr (Or.inl ⟨bsw, ⟨pcw, hget⟩, rfl⟩)
    have hIdx : IdxOf L (g / L.block) gl := ⟨Frame.lt_of_get hX hget, lane, rfl⟩
    have hc0 : (a.loc.at jb).cta = g / L.block := by rw [hl0]; rfl
    obtain ⟨hCons⟩ : Nonempty (ConsOf L X (g / L.block) g) := by
      rcases valid_cls hp hX hFw hN hrd hcovr hLoc with ⟨h, -⟩ | ⟨-, hCons, -⟩
      · cases h
      · rw [hc0] at hCons
        exact ⟨hCons⟩
    have hF := coordReady_handoff hp hX hFw hR hI hB hN (g / L.block) s
    have hE := coordFree_handoff hp hX hFw hR hI hB hN (g / L.block) s
    have hv : ByteCausality L X (a.loc.at jb) (.thread (gl, kw)) (.thread (g, k)) :=
      .direct (.of_base L (hF.baseCausality_of_counts (q := u) hCons hIdx hu'.le (by omega)
        hrd.lt))
    have hsl : validSlotOf L (a.loc.at jb) = s := by
      rw [hl0]; apply Fin.ext
      simp only [validSlotOf, wsLoc]
      have := s.isLt
      omega
    have hall : ∀ w' dst' bytes, X.MemWrites w' dst' bytes → dst'.Covers (a.loc.at jb) →
        w' = .thread (gl, kw) ∨ ByteCausality L X (a.loc.at jb) w' (.thread (gl, kw)) ∨
          ByteCausality L X (a.loc.at jb) (.thread (g, k)) w' := by
      intro w' dst' bytes hw'' hc'
      have hint := hw''.intent
      rcases w' with ⟨g'', k''⟩ | ⟨⟨g'', k''⟩, p'⟩
      · obtain rfl : g'' = gl := valid_ww hp hX hFw hN hint hwr hc' hcovw hLoc
        rcases valid_cls hp hX hFw hN hint hc' hLoc with
          ⟨-, -, -, ⟨pc2, bs2, hget2, hat2⟩, u2, h1, h2⟩ | ⟨hfalse, -⟩
        swap
        · cases hfalse
        rw [hsl, hc0] at h1 h2
        obtain ⟨s2, u2', j2, hcls2, har2, hpo2, hcn2⟩ := index_wrCount hp hX hFw hget2 hat2
        simp only [htid4, ↓reduceIte] at hcn2
        rw [hcta] at har2 hpo2
        obtain ⟨hs2, hj2⟩ : s2 = s ∧ j2 = 2 := by
          rcases hcls2 with ⟨j'', hj'', hjj'', hws⟩ | ⟨hj2, h4, hws⟩
          · rw [hcta] at hws
            obtain ⟨hl2, hz2⟩ := hws
            unfold Acc.Covers at hc'
            rw [hl2, hz2, hl0] at hc'
            simp only [Loc.InRange, wsLoc, true_and] at hc'
            omega
          · rw [hcta, htid] at hws
            obtain ⟨hl2, hz2⟩ := hws
            unfold Acc.Covers at hc'
            rw [hl2, hz2, hl0] at hc'
            simp only [Loc.InRange, wsLoc, true_and] at hc'
            have := s2.isLt
            have := s.isLt
            exact ⟨Fin.ext (by omega), hj2⟩
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
        · have hk : k'' < kw := by
            by_contra hn
            have h3 : (List.take kw (X.tr gl)).countP idxWr ≤
                (List.take k'' (X.tr gl)).countP idxWr :=
              (List.take_isPrefix_take.mpr (Or.inl (not_lt.mp hn))).countP_le
            omega
          exact .inr (.inl (.direct (.of_base L (.single (.inl
            (po_of_overlap hint hwr rfl hk ⟨a.loc.at jb, hc', hcovw⟩))))))
        · subst heq
          have hkk : k'' = kw := by
            rcases Nat.lt_or_ge k'' kw with hk | hk
            · have := countP_take_lt_at idxWr (l := X.tr gl) (k' := kw) hk hget2
                (hiw _ _ _ hat2.2.1 (by have := hat2.2.2; omega))
              omega
            · rcases Nat.eq_or_lt_of_le hk with hk | hk
              · exact hk.symm
              · have := countP_take_lt_at idxWr (l := X.tr gl) (k' := k'') hk hget
                  (hiw _ _ _ hpcw.1 hpcw.2)
                omega
          exact .inl (by rw [hkk])
        · refine .inr (.inr (.direct (.of_base L ?_)))
          exact hE.baseCausality_of_counts (q := u) hIdx hCons hv2.le (by omega) hint.lt
      · exfalso
        obtain ⟨i', hi'⟩ := region_thread hp hX hFw (fun b => by simp) (by simp) (by simp) hint hc'
          hLoc
        cases hi'
    have hmr : X.MemReads (.thread (g, k)) a bs := Or.inl ⟨289, he⟩
    have hmw : X.MemWrites (.thread (gl, kw)) aw bsw := Or.inl ⟨pcw, hget⟩
    exact read_byte_of_last_write_ordered hX hmr hia' hmw hcovw hv hall
end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The validity of the slot of byte place `o`, bit `c` of block `r`: the main cache's below the
main cache's blocks, the extra cache's from them on. -/
def maskBit (P : Params) (L : Launch) (g r o c : Nat) : Prop :=
  if r < FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g)) then
    slotValid P (ctaidY L g) (ctaidX L g) false (64 * r + 8 * o + c)
  else
    slotValid P (ctaidY L g) (ctaidX L g) true
      (64 * (r - FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g))) + 8 * o + c)

theorem quad_testBit (a b c d : Nat) (j c' : Nat) (hj : j < 4) (hc : c' < 8) :
    (a % 256 + 256 * (b % 256 + 256 * (c % 256 + 256 * (d % 256)))).testBit (8 * j + c') =
      ([a, b, c, d].getD j 0).testBit c' := by
  interval_cases j <;> interval_cases c' <;>
    simp [Nat.testBit, Nat.shiftRight_eq_div_pow] <;> omega

/-- The four bytes of four 8-bit words rebuild to the little-endian 32-bit word. -/
theorem rebuild_quad (z0 z1 z2 z3 : BitVec 64) :
    ∃ x : BitVec 64, (rebuild 3 [some (Value.bits 8 z0, 0), some (Value.bits 8 z1, 0),
      some (Value.bits 8 z2, 0), some (Value.bits 8 z3, 0)]).toOption.getD (.pred false) =
        .bits 32 x ∧ x.toNat = z0.toNat % 256 + 256 * (z1.toNat % 256 + 256 *
          (z2.toNat % 256 + 256 * (z3.toNat % 256))) := by
  refine ⟨BitVec.ofNat 64 (z0.toNat % 256 + 256 * (z1.toNat % 256 + 256 *
          (z2.toNat % 256 + 256 * (z3.toNat % 256)))), ?_, ?_⟩
  · simp [rebuild, rebuild.halves, rebuildBits, littleEndianBits, byteBits, Value.bitPattern,
      Value.bytes, intByte]
    rfl
  · simp only [BitVec.toNat_ofNat]
    omega

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : CoordInputs L X)
include hp hX hFw hR hI hB hN

/-- **A byte of the validity read is the byte of the quad's validity bits.** -/
theorem valid_read_bits {g k : Nat} (hal : LaneUbFree X g k) {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨289, .rd a bs⟩) (hat : MbarRow.Wg0At L g 289) {jb : Nat}
    (hjb : jb < 4) :
    ∃ z : BitVec 64, bs[jb]? = some (Value.bits 8 z, 0) ∧
      ∀ c < 8, (z.toNat.testBit c = true ↔
        maskBit P L g (w0Closed ((X.tr g).take k)) (4 * ((L.tidOf g).x / 32 / 2) + jb) c) := by
  have hat0 := hat
  obtain ⟨hw4, -⟩ := hat0
  have ht : (L.tidOf g).x < 128 := MemRow.wg0_tid hw4
  obtain ⟨gl, kw, pcw, aw, bsw, hgl, hget, hatw, hawz, hawl, hcnt, hbyte⟩ :=
    valid_read_byte hp hX hFw hR hI hB hN hal he hat hjb
  obtain ⟨hpc, r', z, hcn, hm4, hbsw, h74, h63⟩ := index_validByte hp hX hFw hget hatw hawz
  have hr' : r' = w0Closed ((X.tr g).take k) := by omega
  subst hr'
  refine ⟨z, ?_, ?_⟩
  · rw [hbyte, hbsw]
    simp only [wbyte, hawl, Nat.sub_self, Value.toBytes, Value.bytes, Value.byteAt]
    simp
  · intro c hc
    have hcta : ctaOf L gl = ctaOf L g := by
      simp only [ctaOf, hgl, hp.block]
      omega
    have ho : tidOf L gl % 32 / 4 = 4 * ((L.tidOf g).x / 32 / 2) + jb := by
      rw [tidOf_eq hp, hgl, hp.block]
      omega
    have hy : ctaidY L gl = ctaidY L g := by simp only [ctaidY, hcta]
    have hx : ctaidX L gl = ctaidX L g := by simp only [ctaidX, hcta]
    rw [hy, hx, ho] at h74 h63
    rcases hpc with h | h
    · obtain ⟨hlt, hb⟩ := h74 h
      simp only [maskBit, hlt, ↓reduceIte]
      exact hb c hc
    · obtain ⟨hge, hb⟩ := h63 h
      simp only [maskBit, show ¬ _ < _ from not_lt.mpr hge, ↓reduceIte]
      exact hb c hc

/-- **The word a validity read returns**: bit `i` is the validity of the slot at position
`64 r + 32 half + i` of the block's cache. -/
theorem valid_read_word {g k : Nat} (hal : LaneUbFree X g k) {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨289, .rd a bs⟩) (hat : MbarRow.Wg0At L g 289) :
    ∃ x : BitVec 64, (rebuild 3 bs).toOption.getD (.pred false) = .bits 32 x ∧
      x.toNat < 2 ^ 32 ∧ ∀ i < 32, (x.toNat.testBit i = true ↔
        maskBit P L g (w0Closed ((X.tr g).take k)) (4 * ((L.tidOf g).x / 32 / 2) + i / 8)
          (i % 8)) := by
  obtain ⟨s, u, ⟨-, hsz⟩, -⟩ := wg0_vmBlk_pre hp hX hFw hal he hat
  have hlen : bs.length = a.size := (hX.rf (.thread (g, k)) a bs (Or.inl ⟨289, he⟩)).1
  rw [hsz] at hlen
  obtain ⟨z0, h0, b0⟩ := valid_read_bits hp hX hFw hR hI hB hN hal he hat (jb := 0) (by omega)
  obtain ⟨z1, h1, b1⟩ := valid_read_bits hp hX hFw hR hI hB hN hal he hat (jb := 1) (by omega)
  obtain ⟨z2, h2, b2⟩ := valid_read_bits hp hX hFw hR hI hB hN hal he hat (jb := 2) (by omega)
  obtain ⟨z3, h3, b3⟩ := valid_read_bits hp hX hFw hR hI hB hN hal he hat (jb := 3) (by omega)
  rcases bs with _ | ⟨y0, _ | ⟨y1, _ | ⟨y2, _ | ⟨y3, _ | ⟨y4, ys⟩⟩⟩⟩⟩ <;> simp at hlen
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] at h0 h1 h2 h3
  simp at h0 h1 h2 h3
  subst h0 h1 h2 h3
  obtain ⟨x, hx, hxn⟩ := rebuild_quad z0 z1 z2 z3
  refine ⟨x, hx, by omega, fun i hi => ?_⟩
  have hj : i / 8 < 4 := by omega
  have hc : i % 8 < 8 := by omega
  have e := quad_testBit z0.toNat z1.toNat z2.toNat z3.toNat (i / 8) (i % 8) hj hc
  rw [show 8 * (i / 8) + i % 8 = i by omega, ← hxn] at e
  rw [e]
  have hb : ∀ j < 4, ∀ c < 8,
      (([z0.toNat, z1.toNat, z2.toNat, z3.toNat].getD j 0).testBit c = true ↔
      maskBit P L g (w0Closed ((X.tr g).take k)) (4 * ((L.tidOf g).x / 32 / 2) + j) c) := by
    intro j hj c hc
    interval_cases j
    · simpa using b0 c hc
    · simpa using b1 c hc
    · simpa using b2 c hc
    · simpa using b3 c hc
  exact hb (i / 8) hj (i % 8) hc

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
