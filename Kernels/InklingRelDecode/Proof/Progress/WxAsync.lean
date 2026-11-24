-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.MmaFacts
public import Kernels.InklingRelDecode.Proof.Interface.ShapeWords
public import Lemmas.Tcgen05.MmaFinishTmemA
public import Lemmas.Tcgen05.TcMmaSource

@[expose] public section

/-!
# The two MMA shapes: `TcMma.ATmemApart` and `TcMma.LayoutInjective`

Every MMA event of the kernel is the MMA warp's QK MMA or PV MMA (`EvW.QkIssue`, `EvW.PvIssue`,
from `Interface.mma_event_state`). Both instruction descriptors decode to a `kind::f16` MMA of
`M = 64`, `N = 128`, `cta_group::1`, without `.ws` (`qk_desc`, `pv_desc`): the half-datapath
layout, whose result cell of `(row, col)` is lane `row % 16 + 32 (row / 16)` and column
`base + col` (`rc_eq`). The MMA warp's Tensor Memory base is 0 (`Interface.mma_tm`, from the
words the thread reads: `BaseWordRead`, `NumWordRead`).

* `layoutInjective_of`: two outputs of one MMA in one cell are one output (the lane gives the row,
  the column gives the column).
* `aTmemApart_of`: only a PV MMA reads A from Tensor Memory, at columns
  `128 ((i - 1) % 2) + 8 j + [0, 8)`, below 256; the MMAs with its accumulator (`SameAccumulator`:
  the same accumulator column 256) are PV MMAs, whose result columns are `256 + [0, 128)`. A QK
  MMA's accumulator column is 0 or 128.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wx
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof PTX.TcMma
open PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem qk_desc {dsc : Descriptor} (h : TcMma.decode .one false .f16 Mma.qkIdesc = some dsc) :
    dsc.m = 64 ∧ dsc.n = 128 ∧ dsc.ws = false ∧ dsc.group = .one := by
  have e : (TcMma.decode .one false .f16 Mma.qkIdesc).map
      (fun d => (d.m, d.n, d.ws, d.group)) = some (64, 128, false, .one) := by decide
  rw [h] at e
  simpa using e

theorem pv_desc {dsc : Descriptor} (h : TcMma.decode .one false .f16 Mma.pvIdesc = some dsc) :
    dsc.m = 64 ∧ dsc.n = 128 ∧ dsc.ws = false ∧ dsc.group = .one ∧
      dsc.kind.k * dsc.kind.width = 32 := by
  have e : (TcMma.decode .one false .f16 Mma.pvIdesc).map
      (fun d => (d.m, d.n, d.ws, d.group, d.kind.k * d.kind.width)) =
      some (64, 128, false, .one, 32) := by decide
  rw [h] at e
  simpa using e

/-- A write cell is the result cell. -/
theorem wc_rc {s : OperandSpec} {base row col : Nat} {mask : List Nat} {cell : Cell}
    (h : writeCell s base mask row col = some cell) : resultCell s base row col = some cell := by
  unfold writeCell at h
  dsimp only at h
  split at h
  · cases h
  · simp only [bind, Option.bind] at h
    split at h
    · cases h
    · rename_i c hc
      dsimp only at h
      split at h
      · cases h
      · dsimp only at h
        split at h
        · simp only [Option.some.injEq] at h
          rw [hc, h]
        · cases h

/-- **The result cell of a 64 by 128 half-datapath MMA.** -/
theorem rc_eq {s : OperandSpec} {base row col : Nat} {cell : Cell}
    (hm : s.descriptor.m = 64) (hg : s.descriptor.group = .one) (hw : s.descriptor.ws = false)
    (hn : s.descriptor.n = 128) (h : resultCell s base row col = some cell) :
    row < 64 ∧ col < 128 ∧ cell.lane = base / 2 ^ 16 + row % 16 + 32 * (row / 16) ∧
      cell.column = base % 2 ^ 16 + col := by
  unfold resultCell at h
  dsimp only at h
  have hh : halfDatapath s.descriptor = true := by
    simp [halfDatapath, hm, hg, hw]
  have hne : ¬ s.descriptor.m = 128 * s.descriptor.group.size := by
    simp [hm, hg, CtaGroup.size]
  split at h
  · rename_i hc
    obtain ⟨-, -, hrow, hcol, -⟩ := hc
    rw [hm] at hrow
    rw [hn] at hcol
    simp only [hg, CtaGroup.size, hm, Nat.div_one] at h
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨hrow, hcol, ?_, rfl⟩
    simp only [Nat.mod_eq_of_lt hrow]
  · cases h

/-! ### The MMA events -/

/-- **An MMA event is a QK MMA or a PV MMA of the MMA warp**, at a state with base 0. -/
theorem mma_cases (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hb : BaseWordRead L X) (hn : NumWordRead Q L X)
    {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d s acc mask) :
    ∃ (pc : Nat) (dm : Mma.D),
      ((∃ (j : Fin 8) (pc' : Nat), EvW.QkIssue L (i.1 / L.block) 0 dm.i j pc'
          ⟨pc, .tc (.mma d s acc mask)⟩) ∨
        (∃ (j : Fin 8) (pc' : Nat), EvW.PvIssue L (i.1 / L.block) 0 dm.i j pc'
          ⟨pc, .tc (.mma d s acc mask)⟩)) := by
  obtain ⟨pc, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  obtain ⟨dm, P, hσ, hsh⟩ := mma_event_state hpre hX hf.sound hf.tracked hg he
    (.inl ⟨d, s, acc, mask, rfl⟩)
  have htm : dm.tm = 0 :=
    mma_tm hpre hX hf hb hn (m := i) ⟨P, by simpa using hσ⟩
  refine ⟨pc, dm, ?_⟩
  obtain ⟨st, i0, n, tm, pro⟩ := dm
  simp only at htm
  subst htm
  cases st <;> simp only [EvW.MmShape] at hsh <;>
    first
    | (obtain ⟨_, h⟩ := hsh; cases h; done)
    | (obtain ⟨_, _, h⟩ := hsh; cases h; done)
    | (obtain ⟨_, _, h, -⟩ := hsh; cases h; done)
    | (cases hsh; done)
    | (rename_i j; exact .inl ⟨j, _, hsh⟩)
    | (rename_i j; exact .inr ⟨j, _, hsh⟩)

/-- **`TcMma.LayoutInjective`**: an MMA writes each cell from one output. -/
theorem layoutInjective_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hb : BaseWordRead L X) (hn : NumWordRead Q L X) :
    TcMma.LayoutInjective X := by
  intro i d s acc mask hi row col row' col' cell h1 h2
  have hd : s.descriptor.m = 64 ∧ s.descriptor.n = 128 ∧ s.descriptor.ws = false ∧
      s.descriptor.group = .one := by
    obtain ⟨pc, dm, ⟨j, _, da, db, dsc, hdc, -, -, he⟩ | ⟨j, _, db, dsc, hdc, -, he⟩⟩ :=
      mma_cases hpre hX hf hb hn hi
    · simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he
      obtain ⟨-, -, rfl, -⟩ := he
      exact qk_desc hdc
    · simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he
      obtain ⟨-, -, rfl, -⟩ := he
      obtain ⟨a, b, c, e, -⟩ := pv_desc hdc
      exact ⟨a, b, c, e⟩
  obtain ⟨hm, hnn, hw, hg⟩ := hd
  obtain ⟨r1, c1, l1, k1⟩ := rc_eq hm hg hw hnn (wc_rc h1)
  obtain ⟨r2, c2, l2, k2⟩ := rc_eq hm hg hw hnn (wc_rc h2)
  constructor <;> omega

/-- The A cells of an MMA with A in Tensor Memory, for a `kind::f16` MMA of 16 elements: 8 columns
from the address's column. -/
theorem aCell_col {s : OperandSpec} {index : Nat} {cell : Cell} {b a : Nat}
    (hk : s.descriptor.kind.k * s.descriptor.kind.width = 32) (hs : s.aTmem = some a)
    (h : aCell s index = some (cell, b)) : cell.column < a % 2 ^ 16 + 8 := by
  unfold aCell at h
  dsimp only at h
  rw [hs] at h
  simp only [Option.bind_some, hk] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only
    omega
  · cases h

/-- **`TcMma.ATmemApart`**: no MMA reads an A cell in Tensor Memory that an MMA with its
accumulator writes. -/
theorem aTmemApart_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hb : BaseWordRead L X) (hn : NumWordRead Q L X) :
    TcMma.ATmemApart X := by
  intro j d s acc mask hj index cell pos ha w d' s' acc' mask' row col hw hsa hwc
  obtain ⟨pc, dm, ⟨jj, _, da, db, dsc, -, -, -, he⟩ | ⟨jj, _, db, dsc, hdc, -, he⟩⟩ :=
    mma_cases hpre hX hf hb hn hj
  · -- a QK MMA reads A from shared memory
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he
    obtain ⟨-, -, rfl, -⟩ := he
    simp [aCell] at ha
  · simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he
    obtain ⟨-, rfl, rfl, -⟩ := he
    obtain ⟨-, -, -, -, hk⟩ := pv_desc hdc
    have hcol := aCell_col (h := ha) hk rfl
    have hb2 : (dm.i - 1) % 2 < 2 := Nat.mod_lt _ (by omega)
    have hjj := jj.isLt
    have hmod : (0 + 128 * ((dm.i - 1) % 2) + 8 * jj.val) % 2 ^ 16 =
        128 * ((dm.i - 1) % 2) + 8 * jj.val := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [hmod] at hcol
    obtain ⟨hd0, -, -, -, -⟩ := hsa
    obtain ⟨pc', dm', ⟨jj', _, da', db', dsc', hdc', -, -, he'⟩ |
        ⟨jj', _, db', dsc', hdc', -, he'⟩⟩ :=
      mma_cases hpre hX hf hb hn hw
    · simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he'
      obtain ⟨-, rfl, -⟩ := he'
      have : (dm'.i % 2) < 2 := Nat.mod_lt _ (by omega)
      omega
    · simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he'
      obtain ⟨-, rfl, rfl, -⟩ := he'
      obtain ⟨hm, hnn, hws, hg, -⟩ := pv_desc hdc'
      obtain ⟨-, -, -, hc2⟩ := rc_eq hm hg hws hnn (wc_rc hwc)
      rw [hc2] at hcol
      omega

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wx
