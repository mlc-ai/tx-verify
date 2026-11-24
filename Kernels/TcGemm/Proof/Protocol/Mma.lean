-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Protocol.Tmem
public import Lemmas.Tcgen05.TcMmaResultLayout
public import Lemmas.Tcgen05.TcSharedAddress

@[expose] public section

/-! # `tc_gemm`: the MMA's layout and the Tensor Memory accesses

The MMA (`mmaSpec`, `kind::i8`, M = 128, N = 8, `cta_group::1`) writes row `i`, column `j` of D to
lane `i`, column `base + j` of CTA 0 (`mma_resultCell`, `mma_writeCell`, `mma_writeCell_inv`), and
reads byte `32 i + k` of A at `sA + offA i k` and byte `32 j + k` of B at `sB + offB k j`
(`mmaSpec_a`, `mmaSpec_b`); the commit targets `bar1` only (`commitSpec_target`). The kernel's only
Tensor Memory accesses are this MMA's writes and the threads' loads, inside the recorded
allocation, which is published to them (`mma_access`, `access_allocated`). -/

namespace PTX.Kernels.TcGemm.Proof
open PTX PTX.Proof PTX.Flow Tmem.Pair

noncomputable section

/-- Layout D for the kernel MMA: row `i`, column `j` of D is lane `i`, column `base + j` of
CTA 0. -/
theorem mma_resultCell (S base row col : Nat) :
    TcMma.resultCell (mmaSpec S) base row col =
      if row < 128 ∧ col < 8 ∧ base + 8 ≤ 512 then some ⟨0, row, base + col⟩ else none :=
  TcMma.resultCell_layoutD rfl rfl (show TcMma.Valid mmaDesc by decide)

/-- The kernel MMA writes every cell of its D tile: all lanes are enabled. -/
theorem mma_writeCell {S base row col : Nat} (hr : row < 128) (hc : col < 8)
    (hb : base + 8 ≤ 512) :
    TcMma.writeCell (mmaSpec S) base mmaMask row col = some ⟨0, row, base + col⟩ := by
  have hm : TcMma.OutputMaskValid .one mmaMask := by decide
  unfold TcMma.writeCell
  simp only [mmaSpec, show TcMma.OutputMaskValid mmaDesc.group mmaMask from hm, not_true_eq_false,
    ↓reduceIte, Option.bind_eq_bind]
  rw [show TcMma.resultCell ⟨mmaDesc, descA S, descB S, 0, 0, none, {}⟩ base row col =
    some ⟨0, row, base + col⟩ from by rw [← mmaSpec, mma_resultCell, ite_eq_left ⟨hr, hc, hb⟩]]
  have hrow : row / (mmaDesc.m / mmaDesc.group.size) * 128 + row = row := by
    simp only [mmaDesc, CtaGroup.size, Nat.div_one]
    rw [Nat.div_eq_of_lt hr]; simp
  simp only [Option.bind_some, hrow]
  rcases (show row / 32 = 0 ∨ row / 32 = 1 ∨ row / 32 = 2 ∨ row / 32 = 3 by omega) with
    h | h | h | h <;> simp [h, mmaMask]

/-- Conversely, every cell the kernel MMA writes has that form. -/
theorem mma_writeCell_inv {S base row col : Nat} {cell : TcMma.Cell}
    (h : TcMma.writeCell (mmaSpec S) base mmaMask row col = some cell) :
    cell = ⟨0, row, base + col⟩ ∧ row < 128 ∧ col < 8 ∧ base + 8 ≤ 512 := by
  have hres := TcMma.writeCell_resultCell h
  rw [mma_resultCell] at hres
  split_ifs at hres with hg
  · exact ⟨(Option.some.inj hres).symm, hg⟩

/-- Byte `k = 32 i + c` of `A` is `A[i][c]`, at the K-major canonical offset. -/
theorem mmaSpec_a (S k : Nat) : (mmaSpec S).byteLoc .a k =
    if k < 4096 then some ((sA S).at (offA (k / 32) (k % 32))) else none := by
  have hv : TcMma.Valid mmaDesc := by decide
  unfold TcMma.OperandSpec.byteLoc
  by_cases hk : k < 4096
  · have hr : k / (32 * 1) < 128 := by omega
    simp only [mmaSpec, mmaDesc, TcMma.Kind.width, TcMma.Kind.k, TcMma.Operand.extent,
      TcMma.Operand.major, CtaGroup.size, Nat.div_one, Nat.mod_one, Nat.div_one,
      Bool.false_eq_true, false_and, and_false, ↓reduceIte] at hr ⊢
    simp only
      [show TcMma.Valid ⟨.one, .i8 true true false, 128, 8, false, false, false, false, false⟩ from
      hv,
      not_true_eq_false, and_true, hr, ↓reduceIte, Bool.false_eq_true, descA, Option.isSome_none,
        and_false,
      TcShared.byteAddress1_k_none, Option.bind_eq_bind, Option.bind_some, hk, sA, Loc.at, offA]
    simp only [Option.pure_def, Option.some.injEq, Loc.mk.injEq, true_and]
    omega
  · have hr : ¬ k / (32 * 1) < 128 := by omega
    simp only [mmaSpec, mmaDesc, TcMma.Kind.width, TcMma.Kind.k, TcMma.Operand.extent,
      CtaGroup.size] at hr ⊢
    simp [hr, hk]

/-- Byte `k = 32 j + c` of `B` is `B[c][j]`, column `j` stored as a K-major row. -/
theorem mmaSpec_b (S k : Nat) : (mmaSpec S).byteLoc .b k =
    if k < 256 then some ((sB S).at (offB (k % 32) (k / 32))) else none := by
  have hv : TcMma.Valid mmaDesc := by decide
  unfold TcMma.OperandSpec.byteLoc
  by_cases hk : k < 256
  · have hr : k / (32 * 1) < 8 := by omega
    simp only [mmaSpec, mmaDesc, TcMma.Kind.width, TcMma.Kind.k, TcMma.Operand.extent,
      TcMma.Operand.major, CtaGroup.size, Nat.div_one, Nat.mod_one,
      Bool.false_eq_true, false_and, and_false, reduceCtorEq, ↓reduceIte] at hr ⊢
    simp only
      [show TcMma.Valid ⟨.one, .i8 true true false, 128, 8, false, false, false, false, false⟩ from
      hv,
      not_true_eq_false, and_true, hr, ↓reduceIte, descB,
      TcShared.byteAddress1_k_none, Option.bind_eq_bind, Option.bind_some, hk, sB, Loc.at, offB]
    simp only [Option.pure_def, Option.some.injEq, Loc.mk.injEq, true_and]
    omega
  · have hr : ¬ k / (32 * 1) < 8 := by omega
    simp only [mmaSpec, mmaDesc, TcMma.Kind.width, TcMma.Kind.k, TcMma.Operand.extent,
      CtaGroup.size] at hr ⊢
    simp [hr, hk]

theorem commitSpec_target {S : Nat} {rank : Fin 16} {mb : Loc}
    (h : TcCommit.target (commitSpec S) rank = some mb) : rank = 0 ∧ mb = bar1 S :=
  TcCommit.target_unicast_inv rfl h

theorem commitSpec_target_zero {S : Nat} :
    TcCommit.target (commitSpec S) 0 = some (bar1 S) :=
  TcCommit.target_unicast rfl


variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
  {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}

section
variable (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X)
  (hW : Wit A B D L.sharedBase X P m u)
include hpre hX hW

omit hpre hX hW in
/-- A release attempt of a recorded allocation is a deallocation event. -/
theorem release_event {r : Requests} {d : EvId} (h : ReleaseOf L X r d) :
    ∃ t n pc grp, X.get d = some ⟨pc, .tc (.resource grp none (.dealloc t n))⟩ := by
  rcases h with ⟨n, base, pc, -, ⟨grp, hget⟩, -⟩ | ⟨_, -, _, -, -, n, base, pc, -, ⟨grp, hget⟩, -⟩
  · exact ⟨base, n, pc, grp, hget⟩
  · exact ⟨base, n, pc, grp, hget⟩

omit hpre hX in
/-- The kernel's only MMA is the one at its trace position; it never accumulates. -/
theorem mma_access {e : EvId} {cell : TcMma.Cell} (h : X.MmaAccess e cell) :
    e = (0, hd 0 + 2 + (P 0).n0) ∧ hd 0 + 2 + (P 0).n0 < m 0 ∧
      ∃ col, col < 8 ∧ cell = ⟨0, cell.lane, (P 0).c + col⟩ ∧ cell.lane < 128 ∧
        (P 0).c + 8 ≤ 512 := by
  rcases h with ⟨d, s, accum, mask, row, col, ⟨pc, hm⟩, hw⟩ | ⟨d, s, mask, row, col, ⟨pc, hm⟩, _⟩ |
    ⟨d, s, accum, mask, index, b, ⟨pc, hm⟩, ha⟩
  · obtain ⟨g, j⟩ := e
    obtain ⟨-, hj, rfl, rfl, rfl, rfl, -, rfl⟩ := hW.mma hm
    obtain ⟨rfl, hr, hc, hb⟩ := mma_writeCell_inv hw
    exact ⟨rfl, hj, col, hc, rfl, hr, hb⟩
  · obtain ⟨g, j⟩ := e
    obtain ⟨-, -, -, -, -, -, h, -⟩ := hW.mma hm
    cases h
  · obtain ⟨g, j⟩ := e
    obtain ⟨-, -, -, -, -, rfl, -, -⟩ := hW.mma hm
    simp [TcMma.aCell, mmaSpec] at ha

/-- Once a thread has passed its second barrier, every thread has made its second arrival. -/
theorem bar1_all {g : Nat} (hg : g < 128) (hm : ldIdx g (P g) + 12 < m g) {h : Nat}
    (hh : h < 128) : ldIdx h (P h) + 11 < m h := by
  have := hW.length g hg
  have bg : X.IsBarrier (g, ldIdx g (P g) + 11) 0 none Flow.bar_1 := by
    show X.get _ = _
    rw [hW.get_of_lt hg (by omega), show ldIdx g (P g) + 11 = ldIdx g (P g) + 1 + 10 by omega,
      fullAt_post]
    rfl
  obtain ⟨j, pc, hbj, hord⟩ := member_bar hpre hX hW bg (by omega) hh
  have kg := hW.barK (k := ((X.tr g).take (ldIdx g (P g) + 11)).countP Execution.isBar)
    ⟨⟨0, _, bg⟩, rfl⟩
  have kh := hW.barK (k := ((X.tr h).take j).countP Execution.isBar) ⟨⟨0, _, hbj⟩, rfl⟩
  have := ldIdx_eq (g := g) (P g)
  have := tl_ge (g := g) (P g)
  have := ldIdx_eq (g := h) (P h)
  have := tl_ge (g := h) (P h)
  rcases kg.2.2 with ⟨h1, -⟩ | ⟨-, h1⟩ <;> rcases kh.2.2 with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> omega

/-- Every Tensor Memory access lies inside the recorded allocation, published to it. -/
theorem access_allocated {e : EvId} {cell : TcMma.Cell} (hacc : Access L X e cell) :
    ∃ cta r, r ∈ X.tmemHistory cta ∧ Tmem.Pair.Covers L X r cell.cta e cell.column := by
  have hT := threads_eq hpre
  have hB := hpre.block
  have h0 : hd 0 = 9 := rfl
  have he0 : (allocReq L.sharedBase (P 0).col).own.event L 0 = (0, 0) := by
    simp [Tmem.Pair.WarpRequest.event, allocReq]
  rcases hacc with hm | ⟨jj, ta, vs, sh, ⟨pc, htl⟩, hjj, rfl⟩ | ⟨_, _, _, _, ⟨_, hst⟩, -⟩ |
    ⟨_, _, _, _, ⟨_, hcp⟩, -⟩ | ⟨_, ⟨_, hsh⟩, -⟩ | ⟨_, ⟨_, hsh⟩, -⟩
  · obtain ⟨rfl, hj, col, hc, hcell, -, -⟩ := mma_access hW hm
    have hc0 := c_eq hpre hX hW (g := 0) (by decide) (by omega)
    have := hW.length 0 (by decide)
    rw [hcell]
    refine ⟨0, _, alloc_recorded hpre hX hW (by omega),
      32, (P 0).col, rfl, rfl, by simp only; omega, by simp only; omega, ?_⟩
    rw [he0]
    exact .inl <| po_baseCausality (by omega) (by omega) (by
      rw [hW.get_of_lt (by decide) (by omega), fullAt_head _ (by decide)]
      simp [headE, Event.acc, allocE])
  · obtain ⟨g, j⟩ := e
    obtain rfl := hW.tld_shape htl
    obtain ⟨hg, hj, rfl, rfl, rfl⟩ := hW.tld htl
    have hld := ldIdx_eq (g := g) (P g)
    have htl' := tl_ge (g := g) (P g)
    obtain ⟨h10, -⟩ := rd_val hpre hX hW hg (by omega)
    have hcg := c_eq hpre hX hW hg (by omega)
    have hcol := col_ok hpre hX hW (P := P) (m := m) (by omega)
    have hvl := hW.vals g
    have := hW.length g hg
    refine ⟨0, _, alloc_recorded hpre hX hW (by omega),
      32, (P 0).col, rfl,
      by simp [hB, allocReq, tcDataCell_s32x32b, tcDataCell32]; omega, ?_, ?_, ?_⟩
    · simp only [tcDataCell_s32x32b, tcDataCell32, laneBase, laneOf]; unfold taddr; rw [hcg]
      omega
    · simp only [tcDataCell_s32x32b, tcDataCell32, laneBase, laneOf]; unfold taddr; rw [hcg]
      omega
    · rw [he0]
      exact .inl <| sync0 hpre hX hW (by decide) hg (by decide) (by omega) (by omega) (by omega)
  · exact (hW.no_tst hst).elim
  · obtain ⟨_, _⟩ := e; exact (hW.no_cp hcp).elim
  · obtain ⟨_, _⟩ := e; exact (hW.no_shift hsh).elim
  · obtain ⟨_, _⟩ := e; exact (hW.no_shift hsh).elim

end

end

end PTX.Kernels.TcGemm.Proof
