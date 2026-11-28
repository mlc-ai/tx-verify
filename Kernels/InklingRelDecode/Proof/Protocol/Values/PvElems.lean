-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.PElement
public import Kernels.InklingRelDecode.Proof.Protocol.Values.PvB
public import Kernels.InklingRelDecode.Proof.Protocol.Values.PvSource
public import Kernels.InklingRelDecode.Proof.Protocol.Values.KvElement
public import Kernels.InklingRelDecode.Proof.Lib.QueryCoord
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaCells
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits

@[expose] public section

/-! # The elements of the PV MMAs

The A element of step `j` at `(row, kk)` of the PV MMA of ordinal `b` is the probability of the key
`16 j + kk` of the round `b - 1` (`pw`, the value the probability stores of that round write: the
hypothesis `PWords`), and the B element at `(row, kk)` is the cache element of the V head column
`row` at the token row `16 (j % 4) + kk` of the slab half `j / 4` of block `b - 1`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma Tmem

/-- The issues of the PV MMAs. -/
def PvIssue (X : Execution) (i : EvId) : Prop :=
  ∃ pc d s acc mask, X.get i = some ⟨pc, .tc (.mma d s acc mask)⟩ ∧ ∃ j : Fin 8, pc = Lib.pvIssue j

/-- The step index of the PV issue at a program counter. -/
def pvStep (pc : Nat) : Nat := [2530, 2533, 2535, 2537, 2539, 2541, 2543, 2545].idxOf pc

theorem pvStep_pvIssue : ∀ j : Fin 8, pvStep (Lib.pvIssue j) = j.val := by decide

/-- The step of the PV issue `i`. -/
def pvStepOf (X : Execution) (i : EvId) : Nat := ((X.get i).map (fun e => pvStep e.pc)).getD 0

/-- The tile row of a Tensor Memory lane of the half datapath. -/
def laneRow (l : Nat) : Nat := 16 * (l / 32) + l % 32

/-- The value `pw cta round row key` of the probability of a key (of the block of a round) in the
row of the tile: what the pair words of the probability stores of that round hold, for the rows
that load (`QRowValid`). -/
def PWords (Q : Params) (L : Launch) (X : Execution) (pw : Nat → Nat → Nat → Nat → ℝ) : Prop :=
  ∀ t k a vals sh jj r, Lib.QRowValid Q L (t / L.block) (laneRow (tcDataCell L t sh a jj).lane) →
    X.get (t, k) = some ⟨1009, .tc (.st a vals sh)⟩ →
    pollRound 1257 ((X.tr t).take k) = r + 1 → jj < vals.length →
    vals[jj]? = some (Value.pair
      (Value.float .bf16 (pw (t / L.block) r (laneRow (tcDataCell L t sh a jj).lane)
        (2 * ((tcDataCell L t sh a jj).column - 128 * (r % 2)))))
      (Value.float .bf16 (pw (t / L.block) r (laneRow (tcDataCell L t sh a jj).lane)
        (2 * ((tcDataCell L t sh a jj).column - 128 * (r % 2)) + 1))))

/-- The A element of the PV issue `i` at row `row`, column `k`. -/
def pvA (L : Launch) (X : Execution) (pw : Nat → Nat → Nat → Nat → ℝ) (i : EvId) (row k : Nat) :
    ℝ :=
  pw (i.1 / L.block) (pollRound 2510 ((X.tr i.1).take i.2) - 1) row (16 * pvStepOf X i + k)

/-- The B element of the PV issue `i` at row `row`, column `k`. -/
noncomputable def pvB (Q : Params) (L : Launch) (X : Execution) (i : EvId) (row k : Nat) : ℝ :=
  kvElem Q L (i.1 / L.block) (pollRound 2510 ((X.tr i.1).take i.2) - 1) 1 (pvStepOf X i / 4)
    (row / 64) (row % 64) (16 * (pvStepOf X i % 4) + k)

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem pv_ne_qk : ∀ j j' : Fin 8, Lib.pvIssue j ≠ Lib.qkIssue j' := by decide +kernel

/-- **The `Ea` hypothesis for the PV MMAs.** -/
theorem pv_a_ideal (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hWrites : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) (W : Iface.PWords X)
    {pw : Nat → Nat → Nat → Nat → ℝ} (P : PWords Q L X pw)
    {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {ops : AsyncCopy.MmaOperands} {row kk : Nat} (hq : PvIssue X i)
    (hi : X.MmaIssue i d s acc mask) (hops : X.async.mmaOperands i = some ops)
    (hrow : row < 64) (hk : kk < 16) (valid : Lib.QRowValid Q L (i.1 / L.block) row) :
    Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row kk = .ok (pvA L X pw i row kk) := by
  obtain ⟨g, k⟩ := i
  obtain ⟨pc, he⟩ := hi
  obtain ⟨pc', d', s', acc', mask', he', j, hj⟩ := hq
  obtain ⟨rfl, -⟩ := Event.mk.inj (Option.some.inj (he.symm.trans he'))
  subst hj
  obtain ⟨b, src, a', vals, sh, j2, x, y, hb, hy, hv, hr, hc, hlane, hcol, hel⟩ :=
    p_element_at hp hX hf hu safe base rows init hG hWrites ht hmd W he hops hrow hk
  obtain ⟨b1, -, pb1, hb1, -⟩ := Mma.Export.pv_block hp hX hf base he ⟨j, rfl⟩
  have hbb : b1 = b := by omega
  subst hbb
  have hP := P src.1 src.2 a' vals sh j2 (b1 - 1) (by
    rw [hlane, hc]
    have e0 : laneRow (32 * (row / 16) + row % 16) = row := by unfold laneRow; omega
    rw [e0]
    exact valid) hy (by omega)
    (List.getElem?_eq_some_iff.mp hv).1
  rw [hv] at hP
  simp only [Option.some.injEq, Value.pair.injEq, Value.float.injEq, true_and] at hP
  obtain ⟨hx, hy'⟩ := hP
  rw [hlane, hcol, hc] at hx hy'
  have e0 : laneRow (32 * (row / 16) + row % 16) = row := by unfold laneRow; omega
  have e1 : 128 * ((b1 - 1) % 2) + 8 * j.val + kk / 2 - 128 * ((b1 - 1) % 2) =
      8 * j.val + kk / 2 := by omega
  rw [e0, e1] at hx hy'
  have st : pvStepOf X (g, k) = j.val := by
    simp [pvStepOf, he, pvStep_pvIssue]
  have key : pvA L X pw (g, k) row kk =
      if kk % 2 = 0 then x else y := by
    unfold pvA
    rw [st]
    simp only []
    rw [pb1]
    by_cases h2 : kk % 2 = 0
    · simp only [h2, ↓reduceIte]
      rw [hx, show 16 * j.val + kk = 2 * (8 * j.val + kk / 2) by omega]
    · simp only [h2, ↓reduceIte]
      rw [hy', show 16 * j.val + kk = 2 * (8 * j.val + kk / 2) + 1 by omega]
  rw [key]
  exact hel

/-- **The `Eb` hypothesis for the PV MMAs.** -/
theorem pv_b_ideal (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (words : RoleBytes L X) (hu : NoUbOutside L X) (nub : ¬ Assumptions.inputReadOnly.ub L m X)
    (form : Iface.KvCopyForm Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {i d s acc mask ops row k} (hq : PvIssue X i) (hi : X.MmaIssue i d s acc mask)
    (hops : X.async.mmaOperands i = some ops) (hrow : row < 128) (hk : k < 16) :
    Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b row k = .ok (pvB Q L X i row k) := by
  obtain ⟨g, k0⟩ := i
  obtain ⟨pc, he⟩ := hi
  obtain ⟨pc', d', s', acc', mask', he', j, hj⟩ := hq
  obtain ⟨rfl, -⟩ := Event.mk.inj (Option.some.inj (he.symm.trans he'))
  subst hj
  obtain ⟨b, -, hb, -⟩ := Mma.Export.pv_block hp hX hf base he ⟨j, rfl⟩
  have := pv_b_elem hp hX hf rows init words hu nub form base he hops rfl hrow hk hb
  have st : pvStepOf X (g, k0) = j.val := by simp [pvStepOf, he, pvStep_pvIssue]
  simp only [pvB, st]
  rw [this]
  simp [hb]

/-- The cells of a PV MMA's accumulator are written by PV MMAs only. -/
theorem pv_closed (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) :
    ∀ i j cell, PvIssue X i → X.MmaReadCell i cell → X.MmaCell j cell →
      WriteBefore L X j i → PvIssue X j := by
  intro i j cell hd hrd hmc _
  have hmc0 := mma_read_write hp hX hf base hrd
  obtain ⟨pc1, d1, s1, acc1, mask1, he1, -, lo, hi1, -, -, kind⟩ :=
    mma_write_cell hp hX hf base hmc0
  obtain ⟨pc', d', s', a', m', he', j', hpc'⟩ := hd
  have hpc : pc' = pc1 := (Event.mk.inj (Option.some.inj (he'.symm.trans he1))).1
  obtain ⟨pc2, d2, s2, acc2, mask2, he2, -, lo2, hi2, -, -, kind2⟩ :=
    mma_write_cell hp hX hf base hmc
  rcases kind with ⟨jq, hq1, hd1, -⟩ | ⟨jp, hpcj, hd1, -⟩
  · exact absurd (hpc'.symm.trans (hpc.trans hq1)) (pv_ne_qk _ _)
  rcases kind2 with ⟨jq2, -, hd2, -⟩ | ⟨jp2, hp2, -⟩
  · omega
  · exact ⟨pc2, d2, s2, acc2, mask2, he2, jp2, hp2⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
