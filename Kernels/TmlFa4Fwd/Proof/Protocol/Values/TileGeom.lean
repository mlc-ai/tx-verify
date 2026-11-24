-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.QOrigin
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Bytes
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Links
import Kernels.TmlFa4Fwd.Proof.Lib.OutputFrame
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.TileAgree
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Input
import Lemmas.Flow.Arith32Word
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The tiles of the CTAs and the blocks they load

A CTA's tile is the scheduler's (`tileOf`): its request is the one whose work holds the CTA, its
first row and head are the assigned coordinates, and its K/V blocks are those of the used keys and
of the keys up to the tile's last row (`tileOk`). The blocks its copies loaded are the tile's
(`inputsAre`): the Q boxes start at the tile's rows and head (`ld_q_origin`), and the row copies
read the rows of the tile's keys (`KvRows`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow TcMma Tm AsyncCopy
open PTX.Flow.Arith32

noncomputable section
open Classical

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The work of request `b` holds CTA `c`. -/
def Work (p : Params) (c b : Nat) : Prop :=
  b < p.batch ∧ tilePrefix p b * p.heads ≤ c ∧ c < tilePrefix p (b + 1) * p.heads

theorem Work.unique {c b b' : Nat} (h : Work p c b) (h' : Work p c b') : b = b' := by
  obtain ⟨-, h1, h2⟩ := h
  obtain ⟨-, h1', h2'⟩ := h'
  rcases lt_trichotomy b b' with hlt | hlt | hlt
  · have := Nat.mul_le_mul_right p.heads (tilePrefix_mono p (show b + 1 ≤ b' from hlt))
    omega
  · exact hlt
  · have := Nat.mul_le_mul_right p.heads (tilePrefix_mono p (show b' + 1 ≤ b from hlt))
    omega

/-- The tile of CTA `c` in request `b`. -/
def workTile (p : Params) (c b : Nat) : Tile where
  batch := b
  head := (Epilogue.assignedCoordinates p b c).2
  row := 256 * (Epilogue.assignedCoordinates p b c).1
  n := Loader.tileBlocks p b (Epilogue.assignedCoordinates p b c).1

/-- **The tile of a CTA.** -/
def tileOf (p : Params) (L : Launch) (c : Nat) : Option Tile :=
  if h : c < L.grid ∧ ∃ b, Work p c b then some (workTile p c h.2.choose) else none

theorem tileOf_eq {c b : Nat} (hc : c < L.grid) (h : Work p c b) :
    tileOf p L c = some (workTile p c b) := by
  have hh : c < L.grid ∧ ∃ b, Work p c b := ⟨hc, b, h⟩
  unfold tileOf
  rw [dite_eq_left hh, hh.2.choose_spec.unique h]

theorem tileOf_some {c : Nat} {t : Tile} (h : tileOf p L c = some t) :
    c < L.grid ∧ ∃ b, Work p c b ∧ t = workTile p c b := by
  unfold tileOf at h
  split at h
  · rename_i hh
    exact ⟨hh.1, _, hh.2.choose_spec, (Option.some.inj h).symm⟩
  · cases h

/-- **The tile of a CTA is in range**, and its blocks hold its rows' keys. -/
theorem tileOk (hp : Pre p L m) {c : Nat} {t : Tile} (h : tileOf p L c = some t) :
    c < L.grid ∧ TileOk p t := by
  obtain ⟨hc, b, ⟨hb, hlo, hhi⟩, rfl⟩ := tileOf_some h
  obtain ⟨hv1, hv2⟩ := Epilogue.assignedCoordinates_valid hp hlo hhi
  obtain ⟨-, hl, -⟩ := hp.lengths b hb
  refine ⟨hc, hb, hv2, ?_, fun st hst ρ hρ hv => ?_⟩
  · simp only [workTile, Loader.tileBlocks]
    omega
  · simp only [workTile, Tile.Valid, Tile.rowOf] at hv ⊢
    simp only [Loader.tileBlocks, Params.keyCount]
    omega

/-- The tile's number of blocks is the MMA lane's loop rounds and one more. -/
theorem tile_rounds (hp : Pre p L m) {g R : Nat} (hg : g < L.threads) (hR : MmaRounds p L g R) :
    ∃ t, tileOf p L (g / L.block) = some t ∧ t.n = R + 1 := by
  obtain ⟨r, bal, hP, rfl⟩ := hR
  obtain ⟨b, hN⟩ := Loader.tile_num hp hg hP
  have hW : Work p (g / L.block) b := ⟨hN.batch, hN.lo, hN.hi⟩
  have hc : g / L.block < L.grid := by
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  refine ⟨_, tileOf_eq hc hW, ?_⟩
  have hsv : Mma.Bs p L g (mmaRef p L g r bal) =
      Loader.sv (Loader.r28Ref p L g r bal) := by
    rw [tile_agree (p := p) rfl r bal]
    show toSigned 32 (r32 _) = toSigned 32 _
    simp only [toSigned, r32, truncBits, BitVec.toNat_ofNat]
    norm_num [Nat.mod_mod]
    rfl
  obtain ⟨-, hok⟩ := tileOk hp (tileOf_eq hc hW)
  have hk := (hp.lengths b hW.1).2.2
  have hb : (workTile p (g / L.block) b).n = Loader.tileBlocks p b
      (Epilogue.assignedCoordinates p b (g / L.block)).1 := rfl
  have hle : Loader.tileBlocks p b (Epilogue.assignedCoordinates p b (g / L.block)).1 ≤
      (p.kLength b + 127) / 128 := Nat.min_le_left _ _
  have h0 := hok.blocks
  rw [hsv, Loader.r28Ref, hN.r28, hb, show Loader.sv (W (Loader.tileBlocks p b
    (Epilogue.assignedCoordinates p b (g / L.block)).1)) = _ from toSigned_W (by omega)]
  omega

/-- **The row copies read the rows of the tile's keys**: the copy of row `row` of the K packet of
tile round `u` reads, when the row's key is used, the key's row of the cache; the next packet reads
V. -/
def KvRows (p : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ c t, tileOf p L c = some t → ∀ u < t.n, ∀ i < 2, ∀ row < 128, ∀ d < 128,
    t.key u row < p.kLength t.batch → ∀ jc sp, KvCp L X c (2 * u + i) row d jc sp →
      sp.src.size = 16 ∧ sp.src.loc = (if i = 0 then p.kLayout else p.vLayout).loc
        (p.page t.batch (t.key u row / 16)) (t.head / 6) (t.key u row % 16) (8 * (d / 8))

/-- The spec's blocks of a tile. -/
def specInputs (p : Params) (t : Tile) : Inputs where
  q st ρ d := p.q (p.qOffset t.batch + t.rowOf st ρ) t.head d
  k u k d := p.k (p.page t.batch (t.key u k / 16)) (t.head / 6) (t.key u k % 16) d
  v u k d := p.v (p.page t.batch (t.key u k / 16)) (t.head / 6) (t.key u k % 16) d

/-- **The blocks of a CTA**: its copies', the spec's where no copy loaded. -/
def tileInputs (p : Params) (L : Launch) (X : Execution) : Nat → Inputs :=
  blocks p L X fun c => specInputs p ((tileOf p L c).getD ⟨0, 0, 0, 0⟩)

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- An element of a packet that a copy of the row's key wrote. -/
private theorem kv_val (hIn : InputsUnwritten p X) (hK : KvRows p L X) {c : Nat} {t : Tile}
    (hT : tileOf p L c = some t) {u i row d : Nat} (hu : u < t.n) (hi : i < 2) (hrow : row < 128)
    (hd : d < 128) (hk : t.key u row < p.kLength t.batch) :
    kvEl L X c (2 * u + i) row d
      ((if i = 0 then p.k else p.v) (p.page t.batch (t.key u row / 16)) (t.head / 6)
        (t.key u row % 16) d) = (if i = 0 then p.k else p.v) (p.page t.batch (t.key u row / 16))
          (t.head / 6) (t.key u row % 16) d := by
  by_cases h : ∃ x, KvEl L X c (2 * u + i) row d x
  · obtain ⟨x, jc, sp, bs, hC, hbs, -⟩ := h
    obtain ⟨hz, hl⟩ := hK c t hT u hu i hi row hrow d hd hk jc sp hC
    obtain ⟨-, hok⟩ := tileOk hp hT
    obtain ⟨hpg1, hpg⟩ := hp.pageTable t.batch hok.batch
    obtain ⟨hkv, hvv⟩ := hp.kvBytes _ (hpg (t.key u row / 16) (by omega)).1 (t.head / 6)
      (by have := hok.head; unfold Params.heads at this; omega) (t.key u row % 16) (by omega) d hd
    have hll : ∀ lay : CacheLayout, sp.src.loc = lay.loc (p.page t.batch (t.key u row / 16))
        (t.head / 6) (t.key u row % 16) (8 * (d / 8)) →
        sp.src.loc.at (2 * (d % 64) % 16) = lay.loc (p.page t.batch (t.key u row / 16))
          (t.head / 6) (t.key u row % 16) d := by
      intro lay h
      rw [h]
      simp only [CacheLayout.loc, globalLoc, Loc.at, Loc.mk.injEq, true_and]
      omega
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact kvEl_eq hp hX hFw (kv_el_of_src hp hX hFw hIn hC hbs hkv (hll _ hl) hz)
    · exact kvEl_eq hp hX hFw (kv_el_of_src hp hX hFw hIn hC hbs hvv (hll _ hl) hz)
  · unfold kvEl
    rw [dite_eq_right h]

/-- **The loaded blocks are the tile's inputs**, when the row copies read the tile's rows. -/
theorem inputsAre (hIn : InputsUnwritten p X) (hK : KvRows p L X) {c : Nat} {t : Tile}
    (hT : tileOf p L c = some t) : InputsAre p t (tileInputs p L X c) where
  q st hst ρ hρ hv d hd := by
    obtain ⟨hc, b, hW, rfl⟩ := tileOf_some hT
    simp only [tileInputs, blocks, hT, Option.getD_some]
    obtain ⟨st', hst'⟩ : ∃ st' : Fin 2, st' = if st = 0 then 0 else 1 := ⟨_, rfl⟩
    obtain ⟨q', hq'⟩ : ∃ q' : Fin 2, q' = if d < 64 then 0 else 1 := ⟨_, rfl⟩
    rw [← hst', ← hq']
    have es : st'.val = st := by rw [hst']; split <;> simp <;> omega
    have eq : q'.val = d / 64 := by rw [hq']; split <;> simp <;> omega
    by_cases h : ∃ org i, QCp p L X c st' q' org i
    · obtain ⟨org, i, hC⟩ := h
      rw [qEl_eq hp hX hFw hC]
      obtain ⟨pc, al, j, mb, hget, hic, -, hoff, -⟩ := hC
      obtain ⟨hw, -⟩ := input_box hp hX hFw hget
      rw [← hic] at hget
      obtain ⟨b', hb1, hb2, hb3, horg⟩ := ld_q_origin hp hX hFw hw (g := i.1) (k := i.2) hget hoff
      rw [hic] at hb2 hb3 horg
      obtain rfl := hW.unique ⟨hb1, hb2, hb3⟩
      obtain ⟨-, hhd⟩ := Epilogue.assignedCoordinates_valid hp hW.2.1 hW.2.2
      have hq1 := hp.qOffset_le_total (show b + 1 ≤ p.batch by have := hW.1; omega)
      have hql : p.qLength b = p.qOffset (b + 1) - p.qOffset b := rfl
      simp only [workTile, Tile.Valid, Tile.rowOf] at hv ⊢
      have e0 : boxCoord org (d % 64) ρ 0 = ((d : Nat) : Int) := by
        rw [horg]; simp [boxCoord]; omega
      have e1 : boxCoord org (d % 64) ρ 1 = ((p.qOffset b +
          (256 * (Epilogue.assignedCoordinates p b c).1 + 128 * st + ρ) : Nat) : Int) := by
        rw [horg]; simp [boxCoord]; omega
      have e2 : boxCoord org (d % 64) ρ 2 =
          (((Epilogue.assignedCoordinates p b c).2 : Nat) : Int) := by
        rw [horg]; simp [boxCoord]
      have hins : Inside 128 p.totalQ p.heads (boxCoord org (d % 64) ρ) := by
        refine ⟨⟨by rw [e0]; omega, by rw [e0]; omega⟩, ⟨by rw [e1]; omega, by rw [e1]; omega⟩,
          by rw [e2]; omega, by rw [e2]; omega⟩
      unfold inputVal
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ite_eq_left hins, e0, e1, e2]
      simp only [Int.toNat_natCast, Option.getD_some]
    · unfold qEl
      rw [dite_eq_right h]
      rfl
  k u hu k hk hkl d hd := by
    simp only [tileInputs, blocks, hT, Option.getD_some]
    exact kv_val hp hX hFw hIn hK hT hu (i := 0) (by decide) hk hd hkl
  v u hu k hk hkl d hd := by
    simp only [tileInputs, blocks, hT, Option.getD_some]
    exact kv_val hp hX hFw hIn hK hT hu (i := 1) (by decide) hk hd hkl

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
