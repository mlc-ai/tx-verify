-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.TileGeom
import Kernels.TmlFa4Fwd.Proof.Correction.Export.LseAddr
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.ShFrame
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The route of the log-sum-exp stores

A global store of a lane is of a correction lane, at its row's word in its CTA's tile (`lse_store`).
Its value is the correction warp's (`LseVals`), so it is the row's log-sum-exp (`lseRoute`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow TcMma Tm

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **What the log-sum-exp stores hold**: the log-sum-exp of the row whose word they write. -/
def LseVals (p : Params) (L : Launch) (X : Execution) (T : Nat → Option Tile)
    (D : Nat → RowData) : Prop :=
  ∀ h i pc a bs, 8 ≤ Prologue.warpIndex L h → Prologue.warpIndex L h < 12 →
    X.get (h, i) = some ⟨pc, .wr a bs⟩ → a.loc.space = .global → ∀ t, T (h / L.block) = some t →
    ∀ st < 2, t.Valid p st (rowIx L h) →
      a.loc = p.lseLoc (p.qOffset t.batch + t.rowOf st (rowIx L h)) t.head →
      bs = (Value.float .f32 ((abiFloat p.scaleLog2Bits *
        (D (softLane L (h / L.block) st (rowIx L h))).rm +
        Real.logb 2 (D (softLane L (h / L.block) st (rowIx L h))).rs) *
          abiFloat 0x3F317218)).toBytes

/-- **A global store of a lane**: of a correction lane, at its row's log-sum-exp word. -/
theorem lse_store (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {h i pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (h, i) = some ⟨pc, .wr a bs⟩) (hg : a.loc.space = .global) :
    8 ≤ Prologue.warpIndex L h ∧ Prologue.warpIndex L h < 12 ∧
      ∃ t, tileOf p L (h / L.block) = some t ∧ ∃ st < 2, t.Valid p st (rowIx L h) ∧
        a.loc = p.lseLoc (p.qOffset t.batch + t.rowOf st (rowIx L h)) t.head ∧ a.size = 4 := by
  have hw : 8 ≤ Prologue.warpIndex L h ∧ Prologue.warpIndex L h ≤ 11 := by
    rcases mem_event hp hX hFw he trivial with ⟨_, _, hk, -⟩ | ⟨a', bs', hk, hA⟩ | ⟨_, hk, -⟩ |
      ⟨_, _, hk, -⟩ | ⟨_, _, hk, -⟩ | ⟨_, _, _, _, hk, -⟩
    · cases hk
    · simp only [Kind.wr.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rcases hA with ⟨-, hS⟩ | ⟨h1, h2, -⟩ | ⟨-, hS⟩ | hS
      · exfalso
        obtain ⟨-, n, -, hl⟩ := hS
        rw [hl] at hg
        cases hg
      · exact ⟨h1, h2⟩
      · exfalso
        have := hS.2
        rw [this] at hg
        cases hg
      · exfalso
        obtain ⟨_, hl, -⟩ := hS
        rw [hl] at hg
        cases hg
    all_goals cases hk
  obtain ⟨b, hb, hlo, hhi, st, hv, hl, hz⟩ := corr_lse hp hX hFw hw.1 hw.2 he hg
  have hgl := Frame.lt_of_get hX he
  refine ⟨hw.1, by omega, _, tileOf_eq (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hgl))
    ⟨hb, hlo, hhi⟩, st.val, st.isLt, ?_, ?_, hz⟩
  · simp only [Tile.Valid, Tile.rowOf, workTile, rowIx]
    exact hv
  · exact hl

/-- **The route of the log-sum-exp stores**, given their values. -/
theorem lseRoute (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {D : Nat → RowData} (hV : LseVals p L X (tileOf p L) D) :
    LseRoute p L X (tileOf p L) D := by
  rintro ⟨h, i⟩ a bytes ⟨pc, he⟩ hg
  obtain ⟨hw, hw1, t, hT, st, hst, hv, hl, hz⟩ := lse_store hp hX hFw he hg
  exact ⟨h / L.block, t, st, rowIx L h, hT, hst, Nat.mod_lt _ (by decide), hv, hl, hz,
    hV h i pc a bytes hw hw1 he hg t hT st hst hv hl⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
