-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.RescaleTrace
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.TileGeom
import Kernels.TmlFa4Fwd.Proof.Correction.Export.RescaleBallot
import Kernels.TmlFa4Fwd.Proof.Lib.GlobalWrites
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Rounds
import Lemmas.Flow.Arith32Norm
import Lemmas.Flow.Step.RuleStep
import Lemmas.Kernel.FrameEnd
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The rescale rounds of the correction lanes

`ScaleReads`: a correction lane's scale read of round `u` returns the factor of the softmax lane of
its row. With it and the Tensor Memory loads the rescale stores are the loaded elements times the
factor (`corrLink_store`), and a round without a store of a cell has a factor of at least one
(`corrLink_skip`): the lane's ballot was zero, so its predicate, the factor below one, was false.
`corrLink` is both. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow TcMma Tm
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (Site ScaleTo LoadTo ReadsAs)

noncomputable section

/-- **The scale reads of the correction lanes**: the read of stage `st` with `u` P-full arrivals
before it reads as the factor of round `u` of the softmax lane of the row. -/
def ScaleReads (L : Launch) (X : Execution) (D : Nat → RowData) : Prop :=
  ∀ {g i u : Nat} {st : Fin 2} {a : Acc} {bs : List (Option Byte)}, g < L.threads →
    8 ≤ Prologue.warpIndex L g → Prologue.warpIndex L g < 12 →
    X.get (g, i) = some ⟨(Site.rscale st).pc, .rd a bs⟩ → pArr L X g st i = u →
    ReadsAs bs ((D (softLane L (g / L.block) st (rowIx L g))).f u)

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {D : Nat → RowData}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hL : ∀ {e : EvId} {a : Nat} {vals : List Value}, X.TLd e a vals .s32x32b → F32s vals)
  (hS : ScaleReads L X D)
include hp hX hFw hL hS

omit hp hX hFw hL in
private theorem scaleTo {g : Nat} (hg : g < L.threads) (hw : 8 ≤ Prologue.warpIndex L g)
    (hw1 : Prologue.warpIndex L g < 12) (K : Nat) : ScaleTo X g K :=
  fun _ _ _ _ _ he => ⟨_, hS hg hw hw1 he rfl⟩

omit hp hX hFw hS in
private theorem loadTo (g K : Nat) : LoadTo X g K := fun _ _ _ _ hl => hL hl

/-- **A rescale store** is the loaded accumulator of its credit times the row's factor. -/
theorem corrLink_store {g k a j st u : Nat} {vals : List Value} (hst : st < 2)
    (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g < 12)
    (ht : X.TSt (g, k) a vals .s32x32b) (hj : j < vals.length)
    (hO : InO st (tcDataCell32 L g a j)) (hu : pArr L X g st k = u) :
    ∃ k' a' j' x, ∃ vals' : List Value, X.TLd (g, k') a' vals' .s32x32b ∧ j' < vals'.length ∧
      tcDataCell32 L g a' j' = tcDataCell32 L g a j ∧ pArr L X g st k' = u ∧
      vals'[j']? = some (.float .f32 x) ∧
      vals[j]? = some (.float .f32 (x * (D (softLane L (g / L.block) st (rowIx L g))).f u)) := by
  have hg : g < L.threads := by
    obtain ⟨pc, he⟩ := ht
    exact Frame.lt_of_get hX he
  obtain ⟨st', c, i, ad, bs, x, h1, h2, -, hr, hb, hp1, k', a', vals', hl, h3, h4, hp2, hv⟩ :=
    Correction.corr_rescale_store hp hX hFw hw (by omega) ht (scaleTo hS hg hw hw1 k)
      (loadTo hL g k)
  have hc := c.isLt
  have hst' := st'.isLt
  obtain rfl : st = st'.val := by
    unfold InO at hO
    simp only [tcDataCell32] at hO
    omega
  obtain ⟨y, hy, hy'⟩ := hv j (by omega)
  have hx := hS hg hw hw1 hr (hp1.trans hu)
  rw [hb.unique hx] at hy'
  refine ⟨k', a', j, y, vals', hl, by omega, ?_, hp2.trans hu, hy, hy'⟩
  simp only [tcDataCell32, show (2 : Nat) ^ 16 = 65536 by rfl, h3]

/-- **A round without a store of a cell** has a factor of at least one. -/
theorem corrLink_skip (hub : ¬ HasUb X) (hD : Complete L X) {c t st ρ d u : Nat} {tl : Tile}
    (hT : tileOf p L c = some tl) (htl : t = tl.n) (hst : st < 2) (hρ : ρ < 128) (hd : d < 128)
    (h1 : 1 ≤ u) (hut : u < t) (hno : ¬ ∃ y, CorrStored L X st ⟨c, ρ, 256 + 128 * st + d⟩ u y) :
    1 ≤ (D (softLane L c st ρ)).f u := by
  have hB := hp.block
  obtain ⟨hcl, b, hW, -⟩ := tileOf_some hT
  -- the row's lane
  obtain ⟨g, hgd⟩ : ∃ g, g = c * L.block + 256 + ρ := ⟨_, rfl⟩
  have hgc : g / L.block = c := by rw [hgd, hB]; omega
  have hgr : rowIx L g = ρ := by unfold rowIx; rw [hgd, hB]; omega
  have hgt : g < L.threads := by
    have := Nat.mul_le_mul_right 512 (show c + 1 ≤ L.grid by omega)
    unfold Launch.threads
    rw [hgd, hB]
    omega
  have hw : 8 ≤ Prologue.warpIndex L g := by unfold Prologue.warpIndex; rw [hgd, hB]; omega
  have hw1 : Prologue.warpIndex L g < 12 := by unfold Prologue.warpIndex; rw [hgd, hB]; omega
  have exits : ∀ {y : Nat}, y < L.threads → ∃ k pc, X.get (y, k) = some ⟨pc, .exit⟩ := by
    intro y hy
    obtain ⟨k, pc, -, he⟩ := Frame.Complete.exit_last hD hy (by
      rintro ⟨-, request, h⟩
      obtain ⟨i, s, ts, -, hi, -⟩ := hX.clc.canceled_has_issue h
      exact noClcIssue hX hi)
    exact ⟨k, pc, he⟩
  obtain ⟨k, pcx, hx⟩ := exits hgt
  obtain ⟨R, hR, hk⟩ := Correction.corr_exit_ballots hp hX hFw hub hw (by omega) hW.1
    (by rw [hgc]; exact hW.2.2) hx
  obtain ⟨tl', hT', hn⟩ := tile_rounds hp hgt (hR.mma hp hgt)
  rw [hgc, hT] at hT'
  cases hT'
  obtain ⟨st', rfl⟩ : ∃ st' : Fin 2, st'.val = st := ⟨⟨st, hst⟩, rfl⟩
  obtain ⟨q, pc, a, bal, ds, n, hqk, he, hσ, hs, harr⟩ :=
    Correction.corr_ballot_at hp hX hFw hub hw (by omega) st' hk (r := u - 1) (by omega)
  obtain ⟨i, ad, bs, x, -, hr, hb, hp1, ha⟩ := Correction.corr_vote_data hp hX hFw hw (by omega) he
    hσ hs (scaleTo hS hgt hw hw1 q) (loadTo hL g q)
  have hxf := hS hgt hw hw1 hr ((hp1.trans harr).trans (by omega : u - 1 + 1 = u))
  rw [hgc, hgr] at hxf
  rw [← hb.unique hxf]
  by_contra hlt
  have hat : a = true := by
    rw [ha, erealCompare_coe_lt]
    exact decide_eq_true (not_le.mp hlt)
  have hbit := Correction.corr_ballot_bit hp hX hFw hw (by omega)
    (fun y hy => exits hy.1.2.1) (fun i hi => by
      rw [Nat.testBit_two_pow_sub_one]; simpa using hi) he
  rw [hat] at hbit
  have hnz : Arith32.scmpi .eq .b (BitVec.ofNat 64 bal.toNat) 0 = false := by
    have h0 : bal.toNat ≠ 0 := by
      intro h0
      have : bal = 0 := BitVec.eq_of_toNat_eq h0
      rw [this] at hbit
      simp at hbit
    rw [show BitVec.ofNat 64 bal.toNat = Arith32.W bal.toNat from rfl,
      Arith32.scmpi_eq_b_W bal.isLt (by omega) (by omega)]
    simpa using h0
  obtain ⟨k', ad', vals, hts, h2, h3, harr'⟩ := Correction.corr_ballot_store hp hX hFw hub hw
    (by omega) he hσ hs hqk hx hnz ⟨d / 16, by omega⟩
  simp only at h2
  have hcell : tcDataCell32 L g ad' (d % 16) = ⟨c, ρ, 256 + 128 * st'.val + d⟩ := by
    simp only [tcDataCell32, laneBase, laneOf, Cell.mk.injEq]
    refine ⟨hgc, ?_, by omega⟩
    rw [hgd, hB]
    omega
  have hpu : pArr L X g st' k' = u := by omega
  obtain ⟨_, _, _, y, _, _, _, _, _, _, hy⟩ := corrLink_store hp hX hFw hL hS hst hw hw1 hts
    (by omega : d % 16 < vals.length) (by
      rw [hcell]; exact ⟨by simp only; omega, by simp only; omega⟩) hpu
  exact hno ⟨_, g, k', ad', d % 16, vals, hts, by omega, hcell, hpu, hy⟩

/-- **The rescale rounds of the correction lanes.** -/
theorem corrLink (hub : ¬ HasUb X) (hD : Complete L X) : CorrLink p L X (tileOf p L) D where
  store hst h8 h12 ht hj hO hu := corrLink_store hp hX hFw hL hS hst h8 h12 ht hj hO hu
  skip _ hT ht _ hst hρ hd _ h1 hu hno :=
    corrLink_skip hp hX hFw hL hS hub hD hT ht hst hρ hd h1 hu hno

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
