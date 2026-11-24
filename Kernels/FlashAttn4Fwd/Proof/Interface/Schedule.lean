-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Common
public import Lemmas.Arith.FastDivmod

@[expose] public section

/-! # What the thread layer exports for the static schedule

Every role of both CTAs of cluster `c` (`%clusterid.x`) runs the static persistent schedule by
itself: item `i` is the work item `c + i·G` (`workOf`, `G = %nclusterid.x`), started while it is
below the item count (`totOf`, `param_13`); its coordinates are what the code's two `FastDivmod`
sequences compute from the parameter objects `param_11` (query blocks) and `param_12` (heads)
(`coordsOf`: batch, head, query block).

The odd CTA's MMA warp runs no item: it skips the loop and exits. The role facts that place an
item's events (its loads, MMAs, stores) speak of `workOf L g i` and `coordsOf L (workOf L g i)`
for the item index `i` of the role's state. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof

noncomputable section

/-- The number of clusters (`%nclusterid.x`). -/
def clusterCount (L : Launch) : Nat := L.grid / L.clusterSize.val

/-- Item `i` of thread `g`'s cluster: `c + i·G`. -/
def workOf (L : Launch) (g i : Nat) : Nat := clusterOf L g + i * clusterCount L

/-- The coordinates (batch, head, query block) of work item `w` as the code computes them: the
quotient `q` of `w` by the query blocks, then the quotient of `q` by the heads, with the
remainders `x - q·d` (`FastDivmod.quot`, `FastDivmod.rem`, on the parameter objects' words). -/
def coordsOf (L : Launch) (w : Nat) : Nat × Nat × Nat :=
  let q := FastDivmod.quot (divWord L "11" 1) (divShift L "11" 0) (divShift L "11" 1) w
  let b := FastDivmod.quot (divWord L "12" 1) (divShift L "12" 0) (divShift L "12" 1) q
  (b, FastDivmod.rem (divWord L "12" 0) b q, FastDivmod.rem (divWord L "11" 0) q w)

/-! ### Coordinates

The code's coordinates of an item are the exact split of its index into (batch, head, query
block) (`coords_eq`, `coords_lt`). They are proved from the divmod parameter objects
(`divmod_words`) and from the block and head counts (`blocks_lt`, `heads_lt`). The protocol
layer and the thread layer both import this file, so the facts are stated here. -/

namespace Schedule
open PTX.Flow StaticSchedule

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- Four parameter bytes `off + k` holding the little-endian bytes of `x < 2 ^ 32` form `x`. -/
theorem paramNat_eq {name : String} {off x : Nat} (hx : x < 2 ^ 32)
    (h : ∀ k < 4, L.paramBytes name (off + k) = some (leByte x k)) :
    paramNat L name off 4 = x := by
  rw [paramNat_four h, Nat.mod_eq_of_lt hx]

/-- A shift byte of a parameter object. -/
theorem paramNat_byte {name : String} {off s : Nat} (hs : s < 2 ^ 8)
    (h : L.paramBytes name off = some (BitVec.ofNat 8 s)) : paramNat L name off 1 = s := by
  simp only [paramNat, h, Option.getD_some, BitVec.toNat_ofNat, Nat.mul_zero, Nat.add_zero]
  omega

/-- The words and shift bytes of a divmod parameter object. -/
theorem divmod_words {i : String} {p : Divmod} {d : Nat} (hd : d < 2 ^ 32)
    (hb : ∀ k < 10, L.paramBytes (param i) k = some (p.byte k)) (he : p.Exact d) :
    divWord L i 0 = d ∧ divWord L i 1 = p.mul ∧ divShift L i 0 = p.shift1 ∧
      divShift L i 1 = p.shift2 := by
  obtain ⟨hdiv, hm, h1, h2, -⟩ := he
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine paramNat_eq (off := 4 * 0) hd fun k hk => ?_
    rw [hb _ (by omega)]
    simp [Divmod.byte, hk, hdiv]
  · refine paramNat_eq (off := 4 * 1) hm fun k hk => ?_
    rw [hb _ (by omega)]
    simp only [Divmod.byte, show ¬ 4 * 1 + k < 4 by omega, show 4 * 1 + k < 8 by omega,
      ite_true, ite_false, show 4 * 1 + k - 4 = k by omega]
  · refine paramNat_byte h1 ?_
    rw [hb _ (by omega)]
    simp [Divmod.byte]
  · refine paramNat_byte h2 ?_
    rw [hb _ (by omega)]
    simp [Divmod.byte]

theorem blocks_lt (hpre : Pre P L mem0) : P.blocks < 2 ^ 31 := by
  have := hpre.sqRange
  unfold Params.blocks
  omega

theorem heads_lt (hpre : Pre P L mem0) : P.h < 2 ^ 31 := by
  have h1 := hpre.scheduleRange
  have h2 := hpre.clustersPos
  have hb : 0 < P.blocks := by
    unfold Params.blocks
    have := hpre.sqPos
    omega
  have : P.h ≤ P.items := by
    unfold Params.items
    have := hpre.bPos
    calc P.h ≤ P.blocks * P.h := Nat.le_mul_of_pos_left _ hb
      _ ≤ P.blocks * P.h * P.b := Nat.le_mul_of_pos_right _ this
  omega

/-- **The code's coordinates of a work item are the exact split of its index**: batch
`w / B / H`, head `w / B % H`, query block `w % B`, for `B = P.blocks` query blocks and `H = P.h`
heads. -/
theorem coords_eq (hpre : Pre P L mem0) {w : Nat} (hw : w < 2 ^ 32) :
    coordsOf L w = (w / P.blocks / P.h, w / P.blocks % P.h, w % P.blocks) := by
  obtain ⟨b0, b1, b2, b3⟩ := divmod_words (by have := blocks_lt hpre; omega)
    hpre.paramBlockDivmod hpre.blockDivmod
  obtain ⟨h0, h1, h2, h3⟩ := divmod_words (by have := heads_lt hpre; omega)
    hpre.paramHeadDivmod hpre.headDivmod
  have hq : FastDivmod.quot P.blockDivmod.mul P.blockDivmod.shift1 P.blockDivmod.shift2 w =
      w / P.blocks := hpre.blockDivmod.2.2.2.2 w hw
  have hq' : w / P.blocks < 2 ^ 32 := lt_of_le_of_lt (Nat.div_le_self _ _) hw
  have hb : FastDivmod.quot P.headDivmod.mul P.headDivmod.shift1 P.headDivmod.shift2
      (w / P.blocks) = w / P.blocks / P.h := hpre.headDivmod.2.2.2.2 _ hq'
  simp only [coordsOf, b0, b1, b2, b3, h0, h1, h2, h3, hq, hb, FastDivmod.rem_eq_mod hw,
    FastDivmod.rem_eq_mod hq']

/-- The coordinates of an item are in range. -/
theorem coords_lt (hpre : Pre P L mem0) {w : Nat} (hw : w < P.items) :
    w / P.blocks / P.h < P.b ∧ w / P.blocks % P.h < P.h ∧ w % P.blocks < P.blocks := by
  have hb : 0 < P.blocks := by
    unfold Params.blocks
    have := hpre.sqPos
    omega
  have hw' : w < P.blocks * P.h * P.b := hw
  exact TileDecomp.split_lt hb hpre.hPos hw'

end Schedule

end
end PTX.Kernels.FlashAttn4Fwd.Proof
