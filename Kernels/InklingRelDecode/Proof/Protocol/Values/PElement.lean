-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Iface.PWords
public import Kernels.InklingRelDecode.Proof.Iface.RescaleWords
public import Kernels.InklingRelDecode.Proof.Protocol.Values.PvAStore
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
import Kernels.InklingRelDecode.Proof.Protocol.Values.ACellForm
import Lemmas.Tcgen05.TcMmaACell
import Lemmas.Tcgen05.TcMmaF16Sum

@[expose] public section

/-! # The A elements of a PV MMA are numbers

The source of the A read is a probability store (`Tmem.pv_a_store`), whose word is a pair of bf16
numbers (`Iface.PWords`); the two bytes of an element are the two bytes of one half of the word
(`aCell_pair`, `AReadOk`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma Tmem

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **An A element of a PV MMA, with its probability store**: the element of step `j` at
`(row, kk)` is the half of the word `j2` of the store of the round of the ordinal, which sits at
the cell of the element. -/
theorem p_element_at (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hWrites : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) (W : Iface.PWords X)
    {g k d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat} {j : Fin 8}
    {ops : AsyncCopy.MmaOperands} {row kk : Nat}
    (he : X.get (g, k) = some ⟨Lib.pvIssue j, .tc (.mma d s acc mask)⟩)
    (hops : X.async.mmaOperands (g, k) = some ops) (hrow : row < 64) (hk : kk < 16) :
    ∃ (b : Nat) (src : EvId) (a' : Nat) (vals : List Value) (sh : TcShape) (j2 : Nat) (x y : ℝ),
      pollRound 2510 ((X.tr g).take k) = b ∧
      X.get src = some ⟨1009, .tc (.st a' vals sh)⟩ ∧
      vals[j2]? = some (.pair (.float .bf16 x) (.float .bf16 y)) ∧
      pollRound 1257 ((X.tr src.1).take src.2) = b ∧ src.1 / L.block = g / L.block ∧
      (tcDataCell L src.1 sh a' j2).lane = 32 * (row / 16) + row % 16 ∧
      (tcDataCell L src.1 sh a' j2).column = 128 * ((b - 1) % 2) + 8 * j.val + kk / 2 ∧
      Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row kk =
        .ok (if kk % 2 = 0 then x else y) := by
  obtain ⟨-, lo, hi', bc, qk | pv⟩ := Mma.Export.columns hp hX hf base he
  · obtain ⟨j', hpc, -⟩ := qk
    have ne : ∀ j j' : Fin 8, Lib.pvIssue j ≠ Lib.qkIssue j' := by decide
    exact absurd hpc (ne j j')
  obtain ⟨j', hpcj, -, -, hdesc⟩ := pv
  obtain ⟨b, hb, -, hA⟩ := Mma.Export.pv_acc hp hX hf base he ⟨j, rfl⟩
  have hat := hA j rfl
  have j8 := j.isLt
  have hb' : 2 * (row * 16 + kk) < Operand.bytes .a s.descriptor := by
    rw [hdesc]
    show 2 * (row * 16 + kk) < 2048
    omega
  obtain ⟨-, -, -, -, -, -, -, -, -, hsh⟩ := Mma.Export.issue_shape hp hX hf base he
  obtain ⟨⟨cell, pos⟩, hac⟩ : ∃ c, aCell s (2 * (row * 16 + kk)) = some c := by
    rcases hsh .a _ hb' with ⟨loc, hl⟩ | ⟨-, hc⟩
    · rw [byteLoc_a_tmem (by rw [hat]; rfl)] at hl
      cases hl
    · exact hc
  obtain ⟨hac1, hp2, hp4⟩ := aCell_pair hac
  obtain ⟨-, hlane, hcol, -, hpos'⟩ := a_cell_form hdesc hat (by omega) (lo.trans hi'.symm) hac
  have hr0 : X.MmaACell (g, k) cell := ⟨d, s, acc, mask, _, pos, ⟨_, he⟩, hac⟩
  obtain ⟨src, a', vals, sh, j2, hsrc, hy, hj, hcl, hround, hcta⟩ :=
    pv_a_store hp hX hf hu safe base rows init hG hWrites ht hmd hr0
  obtain ⟨x, y, hv⟩ := W hy vals[j2] (List.getElem_mem hj)
  have hwr : Wrote L Assumptions.all X src cell vals[j2] :=
    .inr (.inl ⟨a', vals, sh, j2, ⟨1009, hy⟩, List.getElem?_eq_getElem hj, hcl⟩)
  have hby : vals[j2].bytes = 4 := by rw [hv]; rfl
  have hb0 := hX.tcRead.2 _ _ _ _ _ _ _ ⟨d, s, acc, mask, ⟨_, he⟩, hac⟩ hsrc hwr hops
    (by omega)
  have hb1 := hX.tcRead.2 _ _ _ _ _ _ _ ⟨d, s, acc, mask, ⟨_, he⟩, hac1⟩ hsrc hwr hops
    (by omega)
  rw [hv] at hb0 hb1
  have e1 : 2 * (row * 16 + kk) / 32 = row := by omega
  have e2 : 2 * (row * 16 + kk) % 32 % 4 = 2 * (kk % 2) := by omega
  have e3 : 2 * (row * 16 + kk) % 32 / 4 = kk / 2 := by omega
  have e4 : 2 * (row * 16 + kk) / 32 / 16 = row / 16 := by omega
  rw [e4, e1] at hlane
  rw [e3] at hcol
  have hpos : pos = 2 * (kk % 2) := by rw [hpos']; omega
  have e00 : (Value.pair (.float .bf16 x) (.float .bf16 y)).byteAt 0 =
      (Value.float .bf16 x).byteAt 0 := rfl
  have e01 : (Value.pair (.float .bf16 x) (.float .bf16 y)).byteAt 1 =
      (Value.float .bf16 x).byteAt 1 := rfl
  have e10 : (Value.pair (.float .bf16 x) (.float .bf16 y)).byteAt 2 =
      (Value.float .bf16 y).byteAt 0 := rfl
  have e11 : (Value.pair (.float .bf16 x) (.float .bf16 y)).byteAt 3 =
      (Value.float .bf16 y).byteAt 1 := rfl
  refine ⟨b, src, a', vals, sh, j2, x, y, hb, hy, by rw [List.getElem?_eq_getElem hj, hv],
    hround.trans hb, hcta, by rw [← hcl]; omega, by rw [← hcl]; omega, ?_⟩
  rcases (by omega : pos = 0 ∨ pos = 2) with rfl | rfl
  · have : kk % 2 = 0 := by omega
    simp only [this, ↓reduceIte]
    refine element_of_bytes (.inr rfl) fun z hz => ?_
    interval_cases z
    · simpa [e00] using hb0
    · simpa [e01] using hb1
  · have : ¬ kk % 2 = 0 := by omega
    simp only [this, ↓reduceIte]
    refine element_of_bytes (.inr rfl) fun z hz => ?_
    interval_cases z
    · simpa [e10] using hb0
    · simpa [e11] using hb1

/-- **The A elements field of `Elements` for the PV MMAs**: every A element of a completed PV MMA
is a number, given that the probability store writes pairs of numbers. -/
theorem p_element (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hWrites : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) (W : Iface.PWords X)
    {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat} {a : Nat}
    {ops : AsyncCopy.MmaOperands} {row kk : Nat} (hi : X.MmaIssue i d s acc mask)
    (hat : s.aTmem = some a) (hops : X.async.mmaOperands i = some ops) (hrow : row < 64)
    (hk : kk < 16) :
    ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row kk = .ok x := by
  obtain ⟨g, k⟩ := i
  obtain ⟨pc, he⟩ := hi
  obtain ⟨_, _, _, _, qk | pv⟩ := Mma.Export.columns hp hX hf base he
  · obtain ⟨j, -, -, none, -⟩ := qk
    rw [none] at hat
    cases hat
  obtain ⟨j, hpcj, -⟩ := pv
  subst hpcj
  obtain ⟨_, _, _, _, _, _, x, y, _, _, _, _, _, _, _, he'⟩ :=
    p_element_at hp hX hf hu safe base rows init hG hWrites ht hmd W he hops hrow hk
  exact ⟨_, he'⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
