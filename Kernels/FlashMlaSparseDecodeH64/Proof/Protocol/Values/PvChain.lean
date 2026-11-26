-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvSource
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.MmaSum

@[expose] public section

/-! # The PV chain of a block: the result of PV MMA `k` is the base plus the products of its slices

PV MMA `k` (D at `128 (k % 2)`) of a block accumulates, at a cell, the result of PV MMA `k - 2` of
the same block (`acc_source_pv`); PV MMA `k % 2` starts from the base, `0` (no accumulation) or
the number its accumulator source's word reads as (a store of the previous block's rescale, or an
MMA result). With the value of one result (`mma_result_sum`), by induction on `k / 2`, `PvChain`:
the result at a cell is the single-precision number `base + Σ_{m ≤ k / 2} Σ_{t < 16} x_m t y_m t`,
the terms the decoded operand elements of PV MMAs `k % 2, k % 2 + 2 … k` of one block. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow MbarRow

noncomputable section

/-- **One term of the chain**: PV MMA `k` at event `(g, j)` has the operand snapshot `ops`, the
cell is its output `(row, col)`, and `a` is the sum of the sixteen products of the decoded
elements of its A row and its B column. -/
def PvTerm (X : Execution) (g j k : Nat) (cell : TcMma.Cell) (a : ℝ) : Prop :=
  ∃ (s : TcMma.OperandSpec) (acc : Bool) (ops : AsyncCopy.MmaOperands) (row col : Nat)
    (x y : Nat → ℝ),
    X.get (g, j) = some ⟨TmemRow.pvPc k, .tc (.mma (128 * (k % 2)) s acc [0, 0, 0, 0])⟩ ∧
    X.async.mmaOperands (g, j) = some ops ∧
    TcMma.writeCell s (128 * (k % 2)) [0, 0, 0, 0] row col = some cell ∧
    (∀ t < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a
      (TcMma.operandRow s.descriptor row col) t = .ok (x t)) ∧
    (∀ t < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b col t = .ok (y t)) ∧
    a = ∑ t ∈ Finset.range 16, x t * y t

/-- **The base of a chain**: PV MMA `p` at event `(g, j)` overwrites (base `0`) or accumulates the
number the word of its accumulator source reads as. -/
def PvBase (L : Launch) (X : Execution) (g j p : Nat) (cell : TcMma.Cell) (base : ℝ) : Prop :=
  ∃ (s : TcMma.OperandSpec) (acc : Bool) (mask : List Nat),
    X.get (g, j) = some ⟨TmemRow.pvPc p, .tc (.mma (128 * (p % 2)) s acc mask)⟩ ∧
    ((acc = false ∧ base = 0) ∨ (acc = true ∧ ∃ src old,
      TcMma.ReadSource L X .acc src (g, j) cell ∧
        (TcMma.Result L Assumptions.all X src cell old ∨ TcMma.StoreValue L X src cell old) ∧
        valFloat .f32 old = .ok base))

/-- **The chain of a result**: the events `j 0 < … < j (k / 2) = i` of the lane (the MMA issues
`24 r + 16 + k % 2 + 2 m` of one block `r`), their terms `a m` and the base. -/
def PvChain (L : Launch) (X : Execution) (g i k : Nat) (cell : TcMma.Cell) (v : Value) : Prop :=
  ∃ (j : Nat → Nat) (a : Nat → ℝ) (base : ℝ), j (k / 2) = i ∧
    PvBase L X g (j 0) (k % 2) cell base ∧
    (∀ m ≤ k / 2, PvTerm X g (j m) (k % 2 + 2 * m) cell (a m)) ∧
    (∀ m < k / 2, j m < j (m + 1)) ∧
    (∃ r, ∀ m ≤ k / 2, mmaIssues ((X.tr g).take (j m)) = 24 * r + 16 + (k % 2 + 2 * m)) ∧
    v = .float .f32 (base + ∑ m ∈ Finset.range (k / 2 + 1), a m)

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem pvPc_inj3 {k k' : Nat} (h : TmemRow.pvPc k = TmemRow.pvPc k') : k = k' := by
  simp only [TmemRow.pvPc] at h
  split_ifs at h <;> omega

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
  (hT : TmemRows P L X) (hO : MmaOne L X) (hPS : PvStoreOrder L X)
  (hG : SyncGuarded L kernel X) (ht : Tmem.One.Tmem1Facts L X 0)
  (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) (b : EvId)
  (hE : ∀ j, (j = b ∨ Relation.TransGen (TcMma.TcStep L X) j b) → MmaElemAt X j)
  (hold : ∀ i src old cell, (i = b ∨ Relation.TransGen (TcMma.TcStep L X) i b) →
      Relation.TransGen (TcMma.TcStep L X) src i →
      ((X.async.mmaDone src = true ∧ TcMma.Result L Assumptions.all X src cell old) ∨
        TcMma.StoreValue L X src cell old) → ∃ r : ℝ, valFloat .f32 old = .ok r)
include hp hX hFw hR hI hB hT hO hPS hG ht hmd hE hold

/-- **The PV chain**: a done PV MMA `k` of the lane at event `(g, i)`, with its result at a cell,
has the chain of the slices `k % 2, k % 2 + 2 … k` of its block. -/
theorem pv_chain {g : Nat} : ∀ n k, k / 2 = n → k < 8 → ∀ {i : Nat} {s : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} {cell : TcMma.Cell} {v : Value},
    X.get (g, i) = some ⟨TmemRow.pvPc k, .tc (.mma (128 * (k % 2)) s acc mask)⟩ →
    (2 ≤ k → acc = true) → X.async.mmaDone (g, i) = true →
    TcMma.Result L Assumptions.all X (g, i) cell v →
    ((g, i) = b ∨ Relation.TransGen (TcMma.TcStep L X) (g, i) b) →
    PvChain L X g i k cell v := by
  intro n
  induction n with
  | zero =>
    intro k hkn hk i s acc mask cell v he hacc hd hr hb
    obtain ⟨d, s', acc', mask', row, col, ops, x, y, prev, hi, hpos, hops, hx, hy, hv, hprev⟩ :=
      mma_result_sum hp hX hT hO hG (hE (g, i) hb)
        (fun src old hdep h => hold (g, i) src old cell hb hdep h) hd hr
    obtain ⟨pc, he'⟩ := id hi
    rw [he] at he'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he'
    obtain ⟨-, rfl, rfl, rfl, rfl⟩ := he'
    obtain ⟨-, -, -, -, hm0, hon, -⟩ := pv_pc hT hX he (by omega)
    subst hm0
    obtain ⟨dd, kk, -, hpc, -, hiss, -, -, -, -, -, -⟩ := mma_pvAt hp hX hFw he hon.1
      (by omega)
    obtain rfl := pvPc_inj3 hpc
    have hkm : k % 2 = k := by omega
    refine ⟨fun _ => i, fun _ => ∑ t ∈ Finset.range 16, x t * y t, prev, rfl,
      ⟨s, acc, [0, 0, 0, 0], by simpa only [hkm, Nat.mod_mod] using he, ?_⟩, fun m hm => ?_,
      fun m h => absurd h (by omega),
      ⟨dd, fun m hm => ?_⟩, ?_⟩
    · rcases hprev with ⟨h1, h2⟩ | ⟨h1, src, old, h2, h3, h4⟩
      · exact .inl ⟨h1, h2⟩
      · exact .inr ⟨h1, src, old, h2, h3, h4⟩
    · obtain rfl : m = 0 := by omega
      exact ⟨s, acc, ops, row, col, x, y,
        by simpa only [hkm, Nat.mod_mod, Nat.mul_zero, Nat.add_zero] using he, hops,
        by simpa only [hkm, Nat.mod_mod, Nat.mul_zero, Nat.add_zero] using hpos, hx, hy, rfl⟩
    · obtain rfl : m = 0 := by omega
      show mmaIssues ((X.tr g).take i) = _
      omega
    · have hk0 : k / 2 = 0 := hkn
      rw [hv, hk0, Finset.sum_range_one, add_comm]
  | succ n ih =>
    intro k hkn hk i s acc mask cell v he hacc hd hr hb
    have hk2 : 2 ≤ k := by omega
    have hacc' := hacc hk2
    subst hacc'
    obtain ⟨d, s', acc', mask', row, col, ops, x, y, prev, hi, hpos, hops, hx, hy, hv, hprev⟩ :=
      mma_result_sum hp hX hT hO hG (hE (g, i) hb)
        (fun src old hdep h => hold (g, i) src old cell hb hdep h) hd hr
    obtain ⟨pc, he'⟩ := id hi
    rw [he] at he'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he'
    obtain ⟨-, rfl, rfl, rfl, rfl⟩ := he'
    obtain ⟨-, -, -, -, hm0, -⟩ := pv_pc hT hX he (by omega)
    subst hm0
    obtain ⟨-, src, old, hsrc, hold', hpv⟩ := hprev.resolve_left (by simp)
    have hrd : X.MmaReadCell (g, i) cell :=
      ⟨_, _, _, row, col, hi, TcMma.writeCell_resultCell hpos⟩
    obtain ⟨j, hji, ⟨s2, a2, m2, hj⟩, hrr, hmc, hsrc'⟩ :=
      acc_source_pv hp hX hFw hR hI hB hT hO hPS hG ht hmd he hk2 hk hrd
    have hsj : src = (g, j) := TcMma.readSource_unique hX hG hsrc hsrc'
    subst hsj
    have hdj := acc_mma_done hp hX hT hO hG hd hrd hsrc' hmc
    have hb' : (g, j) = b ∨ Relation.TransGen (TcMma.TcStep L X) (g, j) b := by
      rcases hb with h | h
      · exact .inr (h ▸ hsrc'.2.2.1.tcStep)
      · exact .inr (hsrc'.2.2.1.tcStep.trans h)
    rcases hold' with hres | ⟨a3, vals, sh, jj, ⟨pcs, hst⟩, -, -⟩
    · obtain ⟨k3, hk3, hpc3, hdc3, hm3, hon3, -⟩ := pv_pc hT hX hj (by omega)
      obtain rfl := pvPc_inj3 hpc3
      subst hm3
      obtain ⟨dj, kj, -, hpcj, -, -, haccj, -⟩ := mma_pvAt hp hX hFw hj hon3.1 (by omega)
      obtain rfl := pvPc_inj3 hpcj
      obtain ⟨jf, af, bf, hjf, hbase, hterms, hmono, ⟨r, hr'⟩, hold2⟩ :=
        ih (k - 2) (by omega) (by omega) (s := s2) (acc := a2) (mask := [0, 0, 0, 0])
          (by rw [show (k - 2) % 2 = k % 2 by omega]; exact hj) (fun h => haccj.mpr (.inl h))
          hdj hres hb'
      obtain ⟨r0, hr0, hr1⟩ := hrr
      have hn2 : (k - 2) / 2 = n := by omega
      have hp2 : (k - 2) % 2 = k % 2 := by omega
      rw [hn2] at hjf hold2
      rw [hp2] at hbase
      have hrj := hr' n (by omega)
      rw [hjf, hp2] at hrj
      have hrr0 : r = r0 := by omega
      subst hrr0
      have hpr : prev = bf + ∑ m ∈ Finset.range (n + 1), af m := by
        rw [hold2] at hpv
        simp [valFloat] at hpv
        exact (Except.ok.inj hpv).symm
      refine ⟨fun m => if m = n + 1 then i else jf m,
        fun m => if m = n + 1 then ∑ t ∈ Finset.range 16, x t * y t else af m, bf,
        by simp [hkn], ?_, fun m hm => ?_, fun m hm => ?_, ⟨r, fun m hm => ?_⟩, ?_⟩
      · have h0 : (0 : Nat) ≠ n + 1 := by omega
        simpa only [h0, ite_false, hp2] using hbase
      · by_cases h : m = n + 1
        · subst h
          simp only [ite_true]
          exact ⟨s, true, ops, row, col, x, y, by
            rw [show k % 2 + 2 * (n + 1) = k by omega]; exact he, hops, by
            rw [show k % 2 + 2 * (n + 1) = k by omega]; exact hpos, hx, hy, rfl⟩
        · simp only [h, ite_false]
          have := hterms m (by omega)
          rw [hp2] at this
          exact this
      · by_cases h : m = n
        · subst h
          simp only [hjf, ite_true, show m ≠ m + 1 by omega, ite_false]
          exact hji
        · simp only [show m ≠ n + 1 by omega, show m + 1 ≠ n + 1 by omega, ite_false]
          exact hmono m (by omega)
      · by_cases h : m = n + 1
        · subst h
          simp only [ite_true]
          rw [show k % 2 + 2 * (n + 1) = k by omega]
          omega
        · simp only [h, ite_false]
          have := hr' m (by omega)
          rw [hp2] at this
          exact this
      · have hs : ∑ m ∈ Finset.range (n + 1), (if m = n + 1 then
            (∑ t ∈ Finset.range 16, x t * y t) else af m) = ∑ m ∈ Finset.range (n + 1), af m :=
          Finset.sum_congr rfl fun m hm => by
            simp only [Finset.mem_range] at hm
            simp [show m ≠ n + 1 by omega]
        have hk3 : k / 2 = n + 1 := hkn
        rw [hk3, hv, hpr, Finset.sum_range_succ _ (n + 1), hs]
        simp only [ite_true]
        ring_nf
    · cases get_tc_inj hj hst

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
