-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.LdsReal
public import Kernels.InklingRelDecode.Proof.Protocol.Values.QkA
import Kernels.InklingRelDecode.Proof.Lib.QkCell
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns

@[expose] public section

/-! # A score load returns the specification's score

The eight steps of a block sum the sixteen products each (`ld_s_real`); the A elements are the
query elements (`qk_a_ideal`) and the B elements the key elements of the block (`qk_b_ideal`), so
the sum is `score` of the row's token and head with the key of the column. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma Tmem Finset

theorem sum_blocks16 (f : ℕ → ℝ) : ∀ n,
    ∑ d ∈ range (16 * n), f d = ∑ i ∈ range n, ∑ kk ∈ range 16, f (16 * i + kk) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, sum_range_add, ih,
      sum_range_succ (fun i => ∑ kk ∈ range 16, f (16 * i + kk)) n]

/-- **The sum of the products of a block's steps is the specification's score.** -/
theorem qk_score_sum (Q : Params) (L : Launch) (c row col r : Nat) :
    ∑ i ∈ range 8, ∑ kk ∈ range 16, Lib.qMat Q L c row (16 * i + kk) *
        kvElem Q L c r 0 (col / 64) (i / 4) (16 * (i % 4) + kk) (col % 64) =
      score Q ((L.ctaidOf c).get .z) (row / 6) ((L.ctaidOf c).get .y * 6 + row % 6)
        (128 * (Q.splits * r + (L.ctaidOf c).get .x) + col) := by
  have hy : ((L.ctaidOf c).get .y * 6 + row % 6) / group = (L.ctaidOf c).get .y := by
    unfold group
    omega
  unfold score
  rw [hy, show headDim = 16 * 8 by rfl, sum_blocks16]
  refine sum_congr rfl fun i hi => sum_congr rfl fun kk hk => ?_
  have hi8 := mem_range.mp hi
  have hk16 := mem_range.mp hk
  congr 1
  unfold kvElem Params.kVal Params.kvRow
  have e1 : (128 * (Q.splits * r + (L.ctaidOf c).get .x) + col) / 64 =
      2 * (Q.splits * r + (L.ctaidOf c).get .x) + col / 64 := by omega
  have e2 : (128 * (Q.splits * r + (L.ctaidOf c).get .x) + col) % 64 = col % 64 := by omega
  have e3 : 64 * (i / 4) + (16 * (i % 4) + kk) = 16 * i + kk := by omega
  rw [e1, e2, Nat.mul_zero, Nat.zero_add, add_assoc, e3]

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A score load returns the score.** The word of the load of round `r` at the TMEM cell of the
element `(row, col)` of the block's result is the specification's score of the row's token and head
with the key `col` of the block `splits r + x`, for a row that loads. -/
theorem ld_s_score (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hws : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) (words : RoleBytes L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) (form : Iface.KvCopyForm Q L X)
    {t k0 ta vals sh j r} (he : X.get (t, k0) = some ⟨1265, .tc (.ld ta vals sh)⟩)
    (hj : j < vals.length) (s1 : pollRound 1257 ((X.tr t).take k0) = r + 1) :
    ∃ row col, row < 64 ∧ col < 128 ∧ (tcDataCell L t sh ta j).cta = t / L.block ∧
      (tcDataCell L t sh ta j).lane = 32 * (row / 16) + row % 16 ∧
      (tcDataCell L t sh ta j).column = 128 * (r % 2) + col ∧
      (Lib.QRowValid Q L (t / L.block) row → vals[j]? = some (.float .f32
        (score Q ((L.ctaidOf (t / L.block)).get .z) (row / 6)
          ((L.ctaidOf (t / L.block)).get .y * 6 + row % 6)
          (128 * (Q.splits * r + (L.ctaidOf (t / L.block)).get .x) + col)))) := by
  obtain ⟨g, ks, row, col, hg, -, rd7, steps, hv⟩ := ld_s_real hp hX hf hu safe base rows init hG
    hws ht hmd words nub form
    (a := qkA Q L X) (b := qkB Q L X)
    (fun hq hi _ ho hr hk => qk_a_ideal hp hX hf words base hq hi ho hr hk)
    (fun hq hi _ ho hr hk => qk_b_ideal hp hX hf rows init words hu nub form base hq hi ho hr hk)
    he hj s1
  obtain ⟨⟨d7, s7, acc7, mask7, e7⟩, r7, d7', s7', acc7', mask7', ⟨pc7, e7'⟩, hw7⟩ := steps 7
  cases Option.some.inj (e7.symm.trans e7')
  obtain ⟨b, hdst, hb, -⟩ := Mma.Export.qk_block hp hX hf base e7 ⟨7, rfl⟩
  obtain ⟨hm, hlo, -, b2, hd⟩ := Mma.Export.columns hp hX hf base e7
  have ne : ∀ j j' : Fin 8, Lib.qkIssue j ≠ Lib.pvIssue j' := by decide
  have hD : s7.descriptor = Lib.qkDesc := by
    rcases hd with ⟨j', -, -, -, hD⟩ | ⟨j', hpc, -⟩
    · exact hD
    · exact absurd hpc (ne 7 j')
  have hbr : b = r := by omega
  obtain ⟨hr, hc, hcell⟩ := Lib.qk_cell hD (hbr ▸ hdst) hm hw7
  refine ⟨row, col, hr, hc, (by rw [hcell]; exact hlo.trans hg), (by rw [hcell]),
    (by rw [hcell]; simp [hdst, hbr]), fun hv' => ?_⟩
  rw [← hg] at hv' ⊢
  have step : ∀ i ∈ range 8, ∀ kk ∈ range 16, qkA Q L X (g, ks i) row kk *
      qkB Q L X (g, ks i) col kk = Lib.qMat Q L (g / L.block) row (16 * i + kk) *
        kvElem Q L (g / L.block) r 0 (col / 64) (i / 4) (16 * (i % 4) + kk) (col % 64) := by
    intro i hi kk _
    obtain ⟨⟨d1, s1, a1, m1, e1⟩, rd, -⟩ := steps ⟨i, mem_range.mp hi⟩
    have st : qkStepOf X (g, ks i) = i := by
      simp [qkStepOf, e1, qkStep_qkIssue]
    simp only [qkA, qkB, st, rd, hv', ↓reduceIte, Nat.add_sub_cancel]
  rw [hv, ← qk_score_sum Q L (g / L.block) row col r]
  congr 2
  exact sum_congr rfl fun i hi => sum_congr rfl (step i hi)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
