-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Tmem
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Elect.Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCode

@[expose] public section

/-! # The writers of a Tensor Memory cell, by column class

From the Tensor Memory rows only (`TmemRows`), a write of a cell (`TcMma.TmemWrite`) is one of
(`writer_cases`), in the writer's own CTA:

* a QK MMA (`QkW`: D at 400, A at `256 + 8 k`), the cell in columns `[400, 464)`;
* a PV MMA (`PvW b`: D at `b = 128 (k % 2)`), the cell in columns `[b, b + 128)`;
* copy `k` (`CpW k`), the cell in columns `[256 + 8 k, 264 + 8 k)`;
* a store of warpgroup 0 (`StW`), the cell in columns `[0, 256)` and in the writer's lane
  `x.1 % 384`.

The kernel fires no shift (`no_shift_of_code`). An MMA of the rows writes every cell it may
read: an accumulator read is a write of the same MMA (`acc_write`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

namespace TmRace

/-- A QK MMA of the MMA lane. -/
def QkW (L : Launch) (X : Execution) (x : EvId) (k : Nat) : Prop :=
  ∃ pc s, k < 16 ∧ X.get x = some ⟨pc, .tc (.mma 400 s (k != 0) [0, 0, 0, 0])⟩ ∧
    MmaOn L x.1 pc ∧ TmemRow.MmaOps L x.1 s (some (256 + 8 * k)) TmemRow.qkIdesc

/-- A PV MMA of the MMA lane with D at column `b`. -/
def PvW (L : Launch) (X : Execution) (x : EvId) (b : Nat) : Prop :=
  ∃ pc s acc, X.get x = some ⟨pc, .tc (.mma b s acc [0, 0, 0, 0])⟩ ∧ MmaOn L x.1 pc ∧
    TmemRow.MmaOps L x.1 s none TmemRow.pvIdesc

/-- Copy `k` of the MMA lane. -/
def CpW (L : Launch) (X : Execution) (x : EvId) (k : Nat) : Prop :=
  ∃ pc c, k < 16 ∧ X.get x = some ⟨pc, .tc (.cp c)⟩ ∧ MmaOn L x.1 pc ∧
    c.address = 256 + 8 * k ∧ c.shape = .s128x256b

/-- A `32x32b` store of warpgroup 0. -/
def StW (L : Launch) (X : Execution) (x : EvId) : Prop :=
  ∃ pc a vals, X.get x = some ⟨pc, .tc (.st a vals .s32x32b)⟩ ∧ warp L x.1 < 4

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A `tcgen05` event of a launched lane: warpgroup 0's, the MMA warp's, or a paired
resource operation. -/
theorem tc_role (hR : TmemRows P L X) {g k : Nat} {e : Event} {c : TcKind} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hk : e.kind = .tc c) :
    (Wg0At L g e.pc ∧ TmemRow.Wg0Tc e) ∨ (MmaAt L g e.pc ∧ TmemRow.MmaTc L g e) ∨
      ∃ grp dst act, c = .resource grp dst act := by
  rcases hR.place hg he hk with h | h | h | h | h | h | h
  · obtain ⟨-, ⟨d, hk'⟩ | hk'⟩ := hR.startup hg he h hk <;> rw [hk] at hk' <;> cases hk' <;>
      exact .inr (.inr ⟨_, _, _, rfl⟩)
  · exact .inl ⟨h, hR.wg0 hg he h hk⟩
  · exact (hR.wg1 hg he h hk).elim
  · exact .inr (.inl ⟨h, hR.mma hg he h hk⟩)
  · exact (hR.tma hg he h hk).elim
  · exact (hR.index hg he h hk).elim
  · exact (hR.dequant hg he h hk).elim

/-- The descriptor of either MMA word has group one. -/
theorem ops_group {g : Nat} {s : TcMma.OperandSpec} {aT : Option Nat} {i : Nat}
    (hi : i = TmemRow.qkIdesc ∨ i = TmemRow.pvIdesc) (hs : TmemRow.MmaOps L g s aT i) :
    s.descriptor.group = .one := by
  obtain ⟨-, hd, -⟩ := hs
  rcases hi with rfl | rfl
  · have h := TmemRow.qk_desc
    rw [hd] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, hz, -⟩ := h
    cases hgr : s.descriptor.group <;> simp_all [CtaGroup.size]
  · have h := TmemRow.pv_desc
    rw [hd] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, hz, -⟩ := h
    cases hgr : s.descriptor.group <;> simp_all [CtaGroup.size]

/-- The descriptor of either MMA word has M 64. -/
theorem ops_m64 {g : Nat} {s : TcMma.OperandSpec} {aT : Option Nat} {i : Nat}
    (hi : i = TmemRow.qkIdesc ∨ i = TmemRow.pvIdesc) (hs : TmemRow.MmaOps L g s aT i) :
    s.descriptor.m = 64 := by
  obtain ⟨-, hd, -⟩ := hs
  rcases hi with rfl | rfl
  · have h := TmemRow.qk_desc
    rw [hd] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hm, -⟩ := h
    exact hm
  · have h := TmemRow.pv_desc
    rw [hd] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hm, -⟩ := h
    exact hm

/-- **The CTAs of an MMA of the rows are the issuing CTA.** -/
theorem ops_cta (hp : Pre P L m) {g : Nat} (hg : g < L.threads) {s : TcMma.OperandSpec}
    {aT : Option Nat} {i : Nat} (hi : i = TmemRow.qkIdesc ∨ i = TmemRow.pvIdesc)
    (hs : TmemRow.MmaOps L g s aT i) : s.lowCta = g / L.block ∧ s.highCta = g / L.block := by
  have hgr := ops_group hi hs
  obtain ⟨-, -, ctas, hc, hlo, hhi⟩ := hs
  have hb : 0 < L.block := by rw [hp.block]; decide
  have hlt : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul hb).2 hg
  rw [hgr, ctaGroup_self hp hlt] at hc
  cases hc
  simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hlo hhi
  exact ⟨hlo.symm, hhi.symm⟩

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hR : TmemRows P L X)
include hp hX hR

/-- **The writers of a cell, by column class**, in the writer's CTA. -/
theorem writer_cases {x : EvId} {cell : TcMma.Cell} (hw : TcMma.TmemWrite L X x cell) :
    cell.cta = x.1 / L.block ∧
      ((∃ k, QkW L X x k ∧ 400 ≤ cell.column ∧ cell.column < 464) ∨
        (∃ b, PvW L X x b ∧ b ≤ 128 ∧ b % 128 = 0 ∧ b ≤ cell.column ∧ cell.column < b + 128) ∨
        (∃ k, CpW L X x k ∧ 256 + 8 * k ≤ cell.column ∧ cell.column < 264 + 8 * k) ∨
        (StW L X x ∧ cell.column < 256 ∧ cell.lane = x.1 % 384)) := by
  obtain ⟨g, i⟩ := x
  rcases hw with ⟨d, s, acc, mask, row, col, ⟨pc, he⟩, hc⟩ |
    ⟨a, vals, sh, j, ⟨pc, he⟩, hj, rfl⟩ | ⟨c, cta, index, lane, ⟨pc, he⟩, hcta, -, -, rfl⟩ |
    ⟨sp, ⟨pc, he⟩, -⟩
  · have hg := Frame.lt_of_get hX he
    rcases tc_role hR hg he rfl with ⟨-, hW⟩ | ⟨hat, hM⟩ | ⟨_, _, _, hc'⟩
    · rcases hW with h | h | h | h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨-, _, _, h⟩ <;> cases h
    · rcases hM with h | ⟨_, _, -, -, h, -⟩ | ⟨_, h, -⟩ | ⟨s', k, hk, hpc, h, hops⟩ |
        ⟨s', acc', k, hk, hpc, h, -, hops⟩ <;> cases h
      · obtain ⟨hlo, -⟩ := ops_cta hp hg (.inl rfl) hops
        obtain ⟨hcc, h1, h2⟩ := TmemRow.qk_resultCell hops (TmemRow.writeCell_result hc)
        refine ⟨hcc.trans hlo, .inl ⟨k, ⟨pc, _, hk, he, ⟨hat, ?_⟩, hops⟩, h1, h2⟩⟩
        simp only [TmemRow.qkPc] at hpc
        split at hpc <;> omega
      · obtain ⟨hlo, -⟩ := ops_cta hp hg (.inr rfl) hops
        have hb : 128 * (k % 2) ≤ 128 := by omega
        obtain ⟨hcc, h1, h2⟩ := TmemRow.pv_resultCell hops hb (TmemRow.writeCell_result hc)
        refine ⟨hcc.trans hlo, .inr (.inl ⟨_, ⟨pc, _, _, he, ⟨hat, ?_⟩, hops⟩, hb,
          by omega, h1, h2⟩)⟩
        simp only [TmemRow.pvPc] at hpc
        split at hpc <;> omega
    · cases hc'
  · have hg := Frame.lt_of_get hX he
    rcases tc_role hR hg he rfl with ⟨hat, hW⟩ | ⟨-, hM⟩ | ⟨_, _, _, hc'⟩
    · rcases hW with h | h | h | h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨cc, _, h⟩ | ⟨-, _, _, h⟩ <;> cases h
      obtain ⟨ins, ta, ss, sh', hci, hop, hl⟩ := get_tcSt_len hX he rfl
      have h64 := stLen_of_code hci hop
      obtain ⟨hcc, hln, hcol⟩ := stCell hp hat.1 cc.isLt (j := j)
      refine ⟨hcc, .inr (.inr (.inr ⟨⟨pc, _, _, he, hat.1⟩, ?_, hln⟩))⟩
      have := cc.isLt
      dsimp only
      omega
    · rcases hM with h | ⟨_, _, -, -, h, -⟩ | ⟨_, h, -⟩ | ⟨_, _, -, -, h, -⟩ |
        ⟨_, _, _, -, -, h, -⟩ <;> cases h
    · cases hc'
  · have hg := Frame.lt_of_get hX he
    rcases tc_role hR hg he rfl with ⟨-, hW⟩ | ⟨hat, hM⟩ | ⟨_, _, _, hc'⟩
    · rcases hW with h | h | h | h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨-, _, _, h⟩ <;> cases h
    · rcases hM with h | ⟨s', k, hk, hpc, h, hsh, -, ha, hctas⟩ | ⟨_, h, -⟩ |
        ⟨_, _, -, -, h, -⟩ | ⟨_, _, _, -, -, h, -⟩ <;> cases h
      have hb : 0 < L.block := by rw [hp.block]; decide
      rw [ctaGroup_self hp ((Nat.div_lt_iff_lt_mul hb).2 hg)] at hctas
      have hct : c.ctas = [g / L.block] := (Option.some.inj hctas).symm
      rw [hct, List.mem_singleton] at hcta
      subst hcta
      obtain ⟨h1, h2⟩ := TmemRow.cp_cell (cta := g / L.block) (lane := lane) (index := index) hk
      rw [hsh, ha]
      refine ⟨rfl, .inr (.inr (.inl ⟨k, ⟨pc, _, hk, he, ⟨hat, ?_⟩, ha, hsh⟩, h1, h2⟩))⟩
      simp only [TmemRow.cpPc] at hpc
      split at hpc <;> omega
    · cases hc'
  · exact absurd rfl (no_shift_of_code hX code_noShift he sp)

omit hp in
/-- **An accumulator read is a write of the same MMA**: every MMA of the rows has zero output
masks, group one and M 64. -/
theorem acc_write {r : EvId} {cell : TcMma.Cell} (hr : X.MmaReadCell r cell) :
    TcMma.TmemWrite L X r cell := by
  obtain ⟨d, s, mask, row, col, ⟨pc, he⟩, hc⟩ := hr
  have hg := Frame.lt_of_get hX he
  rcases tc_role hR hg he rfl with ⟨-, hW⟩ | ⟨-, hM⟩ | ⟨_, _, _, hc'⟩
  · rcases hW with h | h | h | h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨-, _, _, h⟩ <;> cases h
  · rcases hM with h | ⟨_, _, -, -, h, -⟩ | ⟨_, h, -⟩ | ⟨_, k, -, -, h, hops⟩ |
      ⟨_, _, k, -, -, h, -, hops⟩
    · cases h
    · cases h
    · cases h
    · simp only [Kind.tc.injEq, TcKind.mma.injEq] at h
      obtain ⟨rfl, rfl, -, rfl⟩ := h
      exact .inl ⟨_, _, _, _, _, _, ⟨pc, he⟩,
        writeCell_zeroMask (ops_group (.inl rfl) hops) (ops_m64 (.inl rfl) hops) hc⟩
    · simp only [Kind.tc.injEq, TcKind.mma.injEq] at h
      obtain ⟨rfl, rfl, -, rfl⟩ := h
      exact .inl ⟨_, _, _, _, _, _, ⟨pc, he⟩,
        writeCell_zeroMask (ops_group (.inr rfl) hops) (ops_m64 (.inr rfl) hops) hc⟩
  · cases hc'

end

end TmRace

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
