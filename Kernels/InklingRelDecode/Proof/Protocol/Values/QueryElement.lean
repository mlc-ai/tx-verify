-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Iface.QueryTile
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.Regs
import Kernels.InklingRelDecode.Proof.Protocol.Shared.QueryOrder
import Kernels.InklingRelDecode.Proof.Mma.Export.Operands
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns
import Kernels.InklingRelDecode.Proof.Lib.ZeroElement
import Lemmas.Tcgen05.MmaBytePair
import Lemmas.Tcgen05.MmaOperandObservations
import Lemmas.Tcgen05.TcMmaF16Sum

@[expose] public section

/-! # The A elements of a QK MMA are numbers

The A byte an MMA reads from the query tile is a byte of a query store covering it (its source is
a write of the byte, `Hidden` gives it one because a covering store precedes the read). The two
bytes of an element lie in one aligned four-byte word, and one store writes each location, so they
are two bytes of one `QueryWord`: half of two bf16 numbers or of the zero word. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Flow Protocol Protocol.Shared

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The A byte an MMA reads is the byte of a query store covering it.** -/
theorem query_byte (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (T : Iface.QueryTile L X) {g k pc dst s acc mask ops idx l}
    (he : X.get (g, k) = some ⟨pc, .tc (.mma dst s acc mask)⟩)
    (hops : X.async.mmaOperands (g, k) = some ops) (hl : s.byteLoc .a idx = some l) :
    ∃ gs ks a bs, ∃ i : Fin 8, X.get (gs, ks) = some ⟨526 + 6 * i.val, .wr a bs⟩ ∧
      a.Covers l ∧ a.size = 4 ∧ a.loc.addr % 4 = 0 ∧ ops.a[idx]? = some (wbyte a bs l) := by
  obtain ⟨obs, hrd, hget⟩ := hX.mma_read_exists (isB := false) ⟨pc, he⟩ hops (by simpa using hl)
  obtain ⟨-, -, tile⟩ := Mma.Export.operands_all hp hX hf he
  obtain ⟨space, cta, lo, hi⟩ := tile .a idx l hl
  have inq : Iface.InQ L l := ⟨space, lo, hi⟩
  have memr : X.MemReads (.async (g, k) (.mmaRead false idx)) { loc := l, size := 1 } [obs] :=
    ⟨obs, hrd, rfl, rfl⟩
  have rintent : X.Intent (.async (g, k) (.mmaRead false idx)) { loc := l, size := 1 } false :=
    ⟨rfl, rfl, .inl ⟨dst, s, acc, mask, ⟨pc, he⟩, by simpa using hl⟩⟩
  have cov : ({ loc := l, size := 1 } : Acc).Covers l := by simp [Acc.Covers, Loc.InRange]
  have hat : l.at 0 = l := by simp [Loc.at]
  obtain ⟨gs, ks, a0, bs0, i0, get0, cov0⟩ := T.covered he inq cta
  have memw : X.MemWrites (.thread (gs, ks)) a0 bs0 := Or.inl ⟨_, get0⟩
  have hh := hX.hidden _ _ _ 0 _ _ _ memr (by simp) memw (by simpa [hat] using cov0)
    (by simpa [hat] using query_write_read hp hX hf memw.intent rintent cov0 cov inq)
  have hrf := (hX.rf _ _ _ memr).2 0 (by simp)
  cases hs : X.rf (.async (g, k) (.mmaRead false idx)) 0 with
  | none => simp [hs] at hh
  | some w =>
    rw [hs] at hrf
    obtain ⟨a', bs', hw, hc, hv⟩ := hrf
    rw [hat] at hc hv
    obtain ⟨g1, k1, bs1, i1, j1, rfl, get1, lane, loc, size⟩ :=
      query_store_facts hp hX hf hw.intent hc inq
    rcases hw with ⟨pc1, get1'⟩ | ⟨old, pc1, get1'⟩
    · rw [get1] at get1'
      obtain ⟨-, hk⟩ := Event.mk.inj (Option.some.inj get1')
      obtain ⟨-, rfl⟩ := Kind.wr.inj hk
      have hobs : obs = wbyte a' bs1 l := by simpa using hv
      have align := hp.sharedAlignment
      have swz := (Lib.qSwz_spec _ lane).2
      refine ⟨g1, k1, a', bs1, i1, get1, hc, size, ?_, hobs ▸ hget⟩
      rw [loc]
      simp only
      omega
    · rw [get1] at get1'
      cases Option.some.inj get1'

/-- **Every A element of a QK MMA is a number.** -/
theorem query_element (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (T : Iface.QueryTile L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {g k pc dst s acc mask ops} (he : X.get (g, k) = some ⟨pc, .tc (.mma dst s acc mask)⟩)
    (hq : s.aTmem = none) (hops : X.async.mmaOperands (g, k) = some ops) {row kk : Nat}
    (hrow : row < 64) (hk : kk < 16) :
    ∃ y, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row kk = .ok y := by
  obtain ⟨-, -, -, -, hEa, hEb, -, -, -, hloc⟩ := Mma.Export.issue_shape hp hX hf base he
  obtain ⟨-, -, -, b, hd⟩ := Mma.Export.columns hp hX hf base he
  have hw : s.descriptor.kind.width = 2 ∧ TcMma.Operand.bytes .a s.descriptor = 2048 := by
    rcases hd with ⟨j, -, -, -, hd⟩ | ⟨j, -, -, hat, -⟩
    · rw [hd]; exact ⟨rfl, rfl⟩
    · rw [hq] at hat; cases hat
  obtain ⟨hw2, hbytes⟩ := hw
  have hl0 : ∃ l0, s.byteLoc .a (2 * (row * 16 + kk)) = some l0 := by
    rcases hloc .a (2 * (row * 16 + kk)) (by omega) with h | ⟨-, h⟩
    · exact h
    · simp [TcMma.aCell, hq] at h
  obtain ⟨l0, hl0⟩ := hl0
  have hl1 : s.byteLoc .a (2 * (row * 16 + kk) + 1) = some ⟨l0.space, l0.cta, l0.addr + 1⟩ := by
    rw [TcMma.OperandSpec.byteLoc_pair s .a _ hw2 hEa hEb, hl0]
    rfl
  have even := TcMma.OperandSpec.byteLoc_even s .a _ hw2 hEa hEb hl0
  obtain ⟨g0, k0, a0, bs0, i0, get0, cov0, sz0, al0, ob0⟩ := query_byte hp hX hf T he hops hl0
  obtain ⟨g1, k1, a1, bs1, i1, get1, cov1, sz1, al1, ob1⟩ := query_byte hp hX hf T he hops hl1
  obtain ⟨sp0, ct0, lo0, hi0⟩ := cov0
  obtain ⟨sp1, ct1, lo1, hi1⟩ := cov1
  simp only at sp0 ct0 lo0 hi0 sp1 ct1 lo1 hi1
  have hloc : a0.loc = a1.loc := by
    have ext : ∀ x y : Loc, x.space = y.space → x.cta = y.cta → x.addr = y.addr → x = y :=
      fun ⟨_, _, _⟩ ⟨_, _, _⟩ h1 h2 h3 => by simp_all
    exact ext _ _ (sp0.symm.trans sp1) (ct0.symm.trans ct1) (by omega)
  obtain ⟨rfl, rfl⟩ := T.once get0 get1 hloc
  rw [get0] at get1
  obtain ⟨-, hk1⟩ := Event.mk.inj (Option.some.inj get1)
  obtain ⟨-, rfl⟩ := Kind.wr.inj hk1
  simp only [wbyte] at ob0 ob1
  have wd := T.word get0
  simp only [sz0] at hi0
  have e1 : l0.addr + 1 - a0.loc.addr = (l0.addr - a0.loc.addr) + 1 := by omega
  rw [← hloc, e1] at ob1
  rcases (by omega : l0.addr - a0.loc.addr = 0 ∨ l0.addr - a0.loc.addr = 2) with h | h <;>
    rw [h] at ob0 ob1 <;> rcases wd with ⟨x, y, hxy⟩ | hz
  · obtain ⟨x0, x1⟩ := hxy 0 (by omega)
    obtain ⟨y0, y1⟩ := hxy 1 (by omega)
    refine ⟨x, TcMma.element_of_bytes (Or.inr rfl) fun z hz => ?_⟩
    interval_cases z
    · simpa [ob0] using x0
    · simpa [ob1] using y0
  · refine ⟨0, Lib.zero_elem (p := 0) (Or.inl rfl) ?_ ?_⟩
    · rw [ob0]; simpa using hz 0 (by omega)
    · rw [ob1]; simpa using hz 1 (by omega)
  · obtain ⟨x0, x1⟩ := hxy 0 (by omega)
    obtain ⟨y0, y1⟩ := hxy 1 (by omega)
    refine ⟨y, TcMma.element_of_bytes (Or.inr rfl) fun z hz => ?_⟩
    interval_cases z
    · simpa [ob0] using x1
    · simpa [ob1] using y1
  · refine ⟨0, Lib.zero_elem (p := 2) (Or.inr rfl) ?_ ?_⟩
    · rw [ob0]; simpa using hz 2 (by omega)
    · rw [ob1]; simpa using hz 3 (by omega)

/-- **The A elements field of `Elements`**: every completed QK MMA's A elements are numbers. -/
theorem elements_q (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (T : Iface.QueryTile L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {i d s acc mask ops row k} (hi : X.MmaIssue i d s acc mask) (hq : s.aTmem = none)
    (hops : X.async.mmaOperands i = some ops) (hrow : row < 64) (hk : k < 16) :
    ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row k = .ok x := by
  obtain ⟨g, k'⟩ := i
  obtain ⟨pc, he⟩ := hi
  exact query_element hp hX hf T base he hq hops hrow hk

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
