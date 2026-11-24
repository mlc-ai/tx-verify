-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Operands
public import Lemmas.Order.GuardOrder
import Kernels.TmlFa4Fwd.Proof.Mma.Export.BeforePv
import Kernels.TmlFa4Fwd.Proof.Mma.Export.PvSteps
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.ASource
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.AccSource
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Handoffs
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Issue
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.LoadSource
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Role
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.SourceFacts
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Results
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Score
import Lemmas.Tcgen05.TcMmaACell
import Lemmas.Tcgen05.TcMmaF16Sum
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The output accumulator

For the probabilities `P h u k` that the softmax lanes store (`PStored`), PV step `j` of tile `u`
leaves in the cell of row `row` and column `d` the value before the tile plus the first
`16 (j + 1)` terms `P u k · V(k, d)` of the tile's sum (`PvChain.lean`). The value before the tile
is zero in the first tile, what the correction lane of the row stored of credit `u`, when it stored
(`CorrStored`), and else what the tile before left (`acc`). Here: the A elements are the
probabilities (`pv_a`), and the stored value of a credit is one (`corrStored_unique`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow TcMma Tm

noncomputable section

/-- **The probabilities a softmax lane stores**: the word of column `c` of its row holds columns
`2 c` and `2 c + 1` of the tile. -/
def PStored (L : Launch) (X : Execution) (h : Nat) (P : Nat → Nat → ℝ) : Prop :=
  ∀ {i a j u : Nat} {vals : List Value}, X.TSt (h, i) a vals .s32x32b → (hj : j < vals.length) →
    sPolls L X h (Prologue.warpIndex L h / 4) i = u + 1 →
    Bf16Pair vals[j]
      (P u (2 * ((tcDataCell32 L h a j).column - (128 * (Prologue.warpIndex L h / 4) + 64))))
      (P u (2 * ((tcDataCell32 L h a j).column - (128 * (Prologue.warpIndex L h / 4) + 64)) + 1))

/-- A correction lane stored `y` in a cell of the accumulator with credit `u`. -/
def CorrStored (L : Launch) (X : Execution) (st : Nat) (cell : Cell) (u : Nat) (y : ℝ) : Prop :=
  ∃ g k a j, ∃ vals : List Value, X.TSt (g, k) a vals .s32x32b ∧ j < vals.length ∧
    tcDataCell32 L g a j = cell ∧ pArr L X g st k = u ∧ vals[j]? = some (.float .f32 y)

/-- The softmax lane of row `row` of stage `st` of a CTA. -/
def softLane (L : Launch) (c st row : Nat) : Nat := c * L.block + 128 * st + row

/-- The first `n` terms of the sum of tile `u` at column `d`. -/
def pvSum (P : Nat → Nat → ℝ) (I : Inputs) (u d n : Nat) : ℝ :=
  ∑ k ∈ Finset.range n, P u k * I.v u k d

open Classical in
/-- **The accumulator before tile `u`** in the cell of row `row` and column `d`. -/
def before (L : Launch) (X : Execution) (P : Nat → Nat → ℝ) (I : Inputs) (st : Nat) (cell : Cell)
    (d : Nat) : Nat → ℝ
  | 0 => 0
  | u + 1 =>
    if h : ∃ y, CorrStored L X st cell (u + 1) y then Classical.choose h
    else before L X P I st cell d u + pvSum P I u d 128

/-- **The accumulator after tile `u`**. -/
def acc (L : Launch) (X : Execution) (P : Nat → Nat → ℝ) (I : Inputs) (st : Nat) (cell : Cell)
    (d u : Nat) : ℝ :=
  before L X P I st cell d u + pvSum P I u d 128

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {I : Nat → Inputs}
  {P : Nat → Nat → Nat → ℝ}

theorem before_stored {Q : Nat → Nat → ℝ} {J : Inputs} {st u d : Nat} {cell : Cell} {y : ℝ}
    (h : CorrStored L X st cell (u + 1) y)
    (hu : ∀ y', CorrStored L X st cell (u + 1) y' → y' = y) :
    before L X Q J st cell d (u + 1) = y := by
  have hex : ∃ y, CorrStored L X st cell (u + 1) y := ⟨y, h⟩
  rw [before, dite_eq_left hex]
  exact hu _ (Classical.choose_spec hex)

theorem before_skip {Q : Nat → Nat → ℝ} {J : Inputs} {st u d : Nat} {cell : Cell}
    (h : ¬ ∃ y, CorrStored L X st cell (u + 1) y) :
    before L X Q J st cell d (u + 1) = acc L X Q J st cell d u := by
  rw [before, dite_eq_right h, acc]

/-- The cell of an output position of a PV MMA. -/
theorem pv_pos {g st row col a : Nat} (hst : st < 2) (db : TcShared.Descriptor) (hrow : row < 128)
    (hcol : col < 128) :
    writeCell ⟨pvDsc, db, db, g / L.block, g / L.block, some a, {}⟩ (256 + 128 * st) [0, 0, 0, 0]
      row col = some ⟨g / L.block, row, 256 + 128 * st + col⟩ := by
  have hs : Spec128 ⟨pvDsc, db, db, g / L.block, g / L.block, some a, {}⟩ (g / L.block) :=
    ⟨.inr rfl, rfl, rfl⟩
  exact (writeCell_zero hs (by omega)).trans (resultCell_128 hs (by omega) hrow hcol)

/-- The cell of an element of A of a PV MMA. -/
private theorem pv_aCell {db : TcShared.Descriptor} {c address row k : Nat} {col : TcMma.Collectors}
    (ha : address + 8 ≤ 512) (hrow : row < 128) (hk : k < 16) :
    aCell ⟨pvDsc, db, db, c, c, some address, col⟩ (2 * (row * 16 + k)) =
      some (⟨c, row, address + k / 2⟩, 2 * (k % 2)) := by
  have h1 : 2 * (row * 16 + k) / 32 = row := by omega
  have h2 : 2 * (row * 16 + k) % 32 / 4 = k / 2 := by omega
  have h3 : 2 * (row * 16 + k) % 32 % 4 = 2 * (k % 2) := by omega
  have h4 : address / 2 ^ 16 = 0 := by omega
  have h5 : address % 2 ^ 16 = address := by omega
  have hv := pvDsc_valid
  have hhd : halfDatapath pvDsc = false := by decide
  have hrows : Operand.rows .a pvDsc = 128 := rfl
  unfold aCell
  simp only [Option.bind_some, hv, hhd, hrows, h4, h5]
  simp only [pvDsc, Kind.k, Kind.width, CtaGroup.size]
  simp [h1, h2, h3, hrow, Nat.mod_eq_of_lt hrow, ha]

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

omit hX hFw in
/-- The lane whose word a cell of the probabilities is. -/
theorem softLane_of_cell {h a j st row : Nat} (hw : Prologue.warpIndex L h / 4 = st)
    (hl : (tcDataCell32 L h a j).lane = row) : h = softLane L (h / L.block) st row := by
  have hb := hp.block
  have hd := Nat.div_add_mod h L.block
  simp only [tcDataCell32, laneBase, laneOf] at hl
  unfold softLane
  unfold Prologue.warpIndex at hw
  rw [hb] at hl hw hd ⊢
  omega

/-- **An element of A of a PV MMA** is the softmax lane's probability. -/
theorem pv_a {g k st u : Nat} {j : Fin 8} {d : Nat} {s : OperandSpec} {ac : Bool}
    {mask : List Nat} {ops : AsyncCopy.MmaOperands} {row c : Nat} (hst : st < 2)
    (hP : ∀ h, h < L.threads → Prologue.warpIndex L h < 8 → h / L.block = g / L.block →
      PStored L X h (P h))
    (hq : Pv L X g k st u j) (hi : X.MmaIssue (g, k) d s ac mask)
    (hops : X.async.mmaOperands (g, k) = some ops) (hrow : row < 128) (hc : c < 16) :
    Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row c =
      .ok (P (softLane L (g / L.block) st row) u (16 * j.val + c)) := by
  have ht := scoreFacts hp hX hFw
  have ho := oAccFacts hp hX hFw
  have hT := sourceFacts hp hX hFw
  have hH := handoffs hp hX hFw
  have hj8 := j.isLt
  have hac : aCell s (2 * (row * 16 + c)) =
      some (⟨g / L.block, row, 128 * st + 64 + 8 * j.val + c / 2⟩, 2 * (c % 2)) := by
    obtain ⟨-, -, -, rfl⟩ := hq.spec_eq hi
    exact pv_aCell (by omega) hrow hc
  obtain ⟨hac1, -, -⟩ := aCell_pair hac
  obtain ⟨cellO, st', hst2, hco, hO, h, kk, a, jj, vals, hh, hw, hs', hj, hceq, hu⟩ :=
    pvAStore hp ht hT hH.p hi hac
  -- the stage and the lane
  have hcol := congrArg Cell.column hceq
  have hcta := congrArg Cell.cta hceq
  have hlane := congrArg Cell.lane hceq
  simp only at hcol hcta hlane
  have hstw : Prologue.warpIndex L h / 4 = st := by
    have := (ht.soft_st hh hw hs').1 jj hj
    unfold InP at this
    rw [← hcol] at this
    omega
  have hhc : h / L.block = g / L.block := hcta.symm
  have hlq : h = softLane L (g / L.block) st row := by
    rw [← hhc]
    exact softLane_of_cell hp hstw hlane.symm
  rw [hstw, show pPolls L X (g, k).1 st (g, k).2 = u + 1 from hq.p] at hu
  have hpair := hP h hh hw hhc hs' hj (u := u) (by rw [hstw]; exact hu)
  rw [← hcol, hstw] at hpair
  have hidx : 128 * st + 64 + 8 * j.val + c / 2 - (128 * st + 64) = 8 * j.val + c / 2 := by omega
  rw [hidx] at hpair
  rw [← hlq]
  have hsrc := fun {index pos : Nat} (ha : aCell s index = some (tcDataCell32 L h a jj, pos)) =>
    p_aReadSource hp ht ho hH.p hH.p2 hH.s hi hco hO ha hh hw hs' hj (by
      obtain ⟨h1, h2⟩ := (⟨hst2, hO⟩ : st' < 2 ∧ _)
      rw [hstw, show pPolls L X (g, k).1 st (g, k).2 = u + 1 from hq.p]
      exact hu)
      (sourceLive hT.live ⟨_, _, _, _, hi⟩ (.inr (.inr ⟨_, _, _, _, _, _, hi, ha⟩)))
  rw [hceq] at hac hac1
  have hwr : Wrote L Assumptions.all X (h, kk) (tcDataCell32 L h a jj) vals[jj] :=
    .inr (.inl ⟨a, vals, _, jj, hs', List.getElem?_eq_getElem hj,
      (tcDataCell_s32x32b _ _ _ _).symm⟩)
  obtain ⟨h4, hxy⟩ := hpair
  have hb0 := hX.tcRead.2 _ _ _ _ _ _ _ ⟨_, _, _, _, hi, hac⟩ (hsrc hac) hwr hops (by omega)
  have hb1 := hX.tcRead.2 _ _ _ _ _ _ _ ⟨_, _, _, _, hi, hac1⟩ (hsrc hac1) hwr hops (by omega)
  refine element_of_bytes (.inr rfl) fun z hz => ?_
  rcases (by omega : c % 2 = 0 ∨ c % 2 = 1) with hc2 | hc2
  · rw [show 16 * j.val + c = 2 * (8 * j.val + c / 2) by omega]
    rw [hc2] at hb0 hb1
    rcases (by omega : z = 0 ∨ z = 1) with rfl | rfl
    · rw [Nat.add_zero, hb0, (hxy 0 (by omega)).1]
    · rw [hb1, (hxy 1 (by omega)).1]
  · rw [show 16 * j.val + c = 2 * (8 * j.val + c / 2) + 1 by omega]
    rw [hc2] at hb0 hb1
    rcases (by omega : z = 0 ∨ z = 1) with rfl | rfl
    · rw [Nat.add_zero, hb0, ← (hxy 0 (by omega)).2]
    · rw [hb1, ← (hxy 1 (by omega)).2]

/-- A cell of the accumulator has one value of a credit. -/
theorem corrStored_unique {st u : Nat} {cell : Cell} (hO : InO st cell) {y y' : ℝ}
    (h : CorrStored L X st cell u y) (h' : CorrStored L X st cell u y') : y = y' := by
  have ht := scoreFacts hp hX hFw
  have ho := oAccFacts hp hX hFw
  have hcorr : ∀ {g k a j : Nat} {vals : List Value}, X.TSt (g, k) a vals .s32x32b →
      j < vals.length → tcDataCell32 L g a j = cell →
      g < L.threads ∧ 8 ≤ Prologue.warpIndex L g ∧ Prologue.warpIndex L g < 12 := by
    intro g k a j vals hs hj hceq
    obtain ⟨hgl, hgw⟩ := ht.tc_role (.inr hs)
    refine ⟨hgl, ?_, hgw⟩
    by_contra h8
    have hP' := (ht.soft_st hgl (by omega) hs).1 j hj
    rw [hceq] at hP'
    unfold InP at hP'
    unfold InO at hO
    omega
  obtain ⟨g, k, a, j, vals, hs, hj, hc, hpa, hv⟩ := h
  obtain ⟨g', k', a', j', vals', hs', hj', hc', hpa', hv'⟩ := h'
  obtain ⟨hg, h8, h12⟩ := hcorr hs hj hc
  obtain ⟨hg', h8', h12'⟩ := hcorr hs' hj' hc'
  obtain rfl := corr_cell_thread hp h8 h12 h8' h12' (hc.trans hc'.symm)
  obtain rfl := ho.corr_st_one hg h8 h12 hs hs' hj hj' (hc.trans hc'.symm)
    (by rw [hc]; exact hO) (hpa.trans hpa'.symm)
  obtain ⟨pc, e⟩ := hs
  obtain ⟨pc', e'⟩ := hs'
  rw [e] at e'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at e'
  obtain ⟨-, rfl, rfl, -⟩ := e'
  have : j = j' := by
    have := hc.trans hc'.symm
    simp only [tcDataCell32, Cell.mk.injEq] at this
    omega
  subst this
  rw [hv] at hv'
  simpa using hv'

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
