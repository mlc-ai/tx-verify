-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Facts
public import Kernels.TmlFa4Fwd.Proof.Lib.TmemCells
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Spec
public import Kernels.TmlFa4Fwd.Assumptions
import Kernels.TmlFa4Fwd.Proof.Correction.Export.Tmem
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Tmem
import Kernels.TmlFa4Fwd.Proof.Protocol.O.Done
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Info
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Role
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Tmem

@[expose] public section

/-! # The Tensor Memory facts, from the role exports -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

theorem Qk.spec {g k st u : Nat} {j : Fin 8} (_h : Qk L X g k st u j) (da db : TcShared.Descriptor)
    :
    Spec128 ⟨qkDsc, da, db, g / L.block, g / L.block, none, {}⟩ (g / L.block) :=
  ⟨.inl rfl, rfl, rfl⟩

/-- The cells a QK MMA writes: its stage's scores, in its CTA. -/
theorem Qk.cells {g k st u : Nat} {j : Fin 8} (h : Qk L X g k st u j) (hst : st < 2) {cell : Cell}
    (hc : X.MmaCell (g, k) cell) : InS st cell ∧ cell.cta = g / L.block := by
  obtain ⟨d, s, acc, mask, row, col, ⟨pc, hi⟩, hw⟩ := hc
  obtain ⟨pc', da, db, he⟩ := h.issue
  rw [he] at hi
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hi
  obtain ⟨-, rfl, rfl, -, rfl⟩ := hi
  rw [writeCell_zero (h.spec da db) (by omega)] at hw
  obtain ⟨h1, h2, rfl⟩ := resultCell_128_iff (h.spec da db) (by omega) hw
  exact ⟨⟨by simp only; omega, by simp only; omega⟩, rfl⟩

/-- The cells a PV MMA writes: its stage's accumulator, in its CTA. -/
theorem Pv.cells {g k st u : Nat} {j : Fin 8} (h : Pv L X g k st u j) (hst : st < 2) {cell : Cell}
    (hc : X.MmaCell (g, k) cell) : InO st cell ∧ cell.cta = g / L.block := by
  obtain ⟨d, s, acc, mask, row, col, ⟨pc, hi⟩, hw⟩ := hc
  obtain ⟨pc', db, he⟩ := h.issue
  rw [he] at hi
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hi
  obtain ⟨-, rfl, rfl, -, rfl⟩ := hi
  have hs : Spec128 ⟨pvDsc, db, db, g / L.block, g / L.block,
      some (128 * st + 64 + 8 * j.val), {}⟩ (g / L.block) := ⟨.inr rfl, rfl, rfl⟩
  rw [writeCell_zero hs (by omega)] at hw
  obtain ⟨h1, h2, rfl⟩ := resultCell_128_iff hs (by omega) hw
  exact ⟨⟨by simp only; omega, by simp only; omega⟩, rfl⟩

theorem inS_inO {st st' : Nat} {cell : Cell} (hst : st < 2) (h : InS st cell) (h' : InO st' cell) :
    False := by
  unfold InS at h
  unfold InO at h'
  omega

theorem inS_st {st st' : Nat} {cell : Cell} (h : InS st cell) (h' : InS st' cell) : st = st' := by
  unfold InS at h h'
  omega

theorem inO_st {st st' : Nat} {cell : Cell} (h : InO st cell) (h' : InO st' cell) : st = st' := by
  unfold InO at h h'
  omega

/-- An MMA as a QK or PV MMA. -/
theorem mma_qkpv (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {i : EvId} (hi : IsMma X i) :
    Prologue.warpIndex L i.1 = 12 ∧ ∃ st u j, st < 2 ∧ (Qk L X i.1 i.2 st u j ∨ Pv L X i.1 i.2 st u
        j) := by
  obtain ⟨g, k⟩ := i
  obtain ⟨d, s, acc, mask, hi⟩ := hi
  have hw := mma_warp hp hX hFw hi
  exact ⟨hw, Mma.mma_at hp hX hw hi⟩

/-- An MMA writing a stage's scores is a QK MMA of the stage. -/
theorem qk_of_cell (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {i : EvId} {cell : Cell} {st : Nat} (hi : IsMma X i)
    (hc : X.MmaCell i cell) (hS : InS st cell) (hst2 : st < 2) :
    ∃ u j, Qk L X i.1 i.2 st u j := by
  obtain ⟨-, st', u, j, hst', h | h⟩ := mma_qkpv hp hX hFw hi
  · obtain rfl := inS_st hS (h.cells hst' (cell := cell) hc).1
    exact ⟨u, j, h⟩
  · exact (inS_inO hst2 hS (h.cells hst' (cell := cell) hc).1).elim

/-- An MMA writing a stage's accumulator is a PV MMA of the stage. -/
theorem pv_of_cell (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {i : EvId} {cell : Cell} {st : Nat} (hi : IsMma X i)
    (hc : X.MmaCell i cell) (hO : InO st cell) :
    st < 2 ∧ ∃ u j, Pv L X i.1 i.2 st u j := by
  obtain ⟨-, st', u, j, hst', h | h⟩ := mma_qkpv hp hX hFw hi
  · exact (inS_inO hst' (h.cells hst' (cell := cell) hc).1 hO).elim
  · obtain rfl := inO_st hO (h.cells hst' (cell := cell) hc).1
    exact ⟨hst', u, j, h⟩

/-- A cell of some stage's scores in a column below 256 has a stage below 2. -/
theorem mma_acc_at (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d s acc mask) : mask = [0, 0, 0, 0] ∧ Spec128 s (i.1 / L.block) ∧
      ∃ st < 2, (∃ u j, Qk L X i.1 i.2 st u j ∧ d = 128 * st ∧ s.descriptor = qkDsc ∧
          s.aTmem = none) ∨
        ∃ u j, Pv L X i.1 i.2 st u j ∧ d = 256 + 128 * st ∧ s.descriptor = pvDsc ∧
          s.aTmem = some (128 * st + 64 + 8 * j.val) := by
  obtain ⟨-, st, u, j, hst, h | h⟩ := mma_qkpv hp hX hFw ⟨_, _, _, _, hi⟩
  · obtain ⟨pc, hi⟩ := hi
    obtain ⟨pc', da, db, he⟩ := h.issue
    rw [show i = (i.1, i.2) from rfl, he] at hi
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hi
    obtain ⟨-, rfl, rfl, -, rfl⟩ := hi
    exact ⟨rfl, ⟨.inl rfl, rfl, rfl⟩, st, hst, .inl ⟨u, j, h, rfl, rfl, rfl⟩⟩
  · obtain ⟨pc, hi⟩ := hi
    obtain ⟨pc', db, he⟩ := h.issue
    rw [show i = (i.1, i.2) from rfl, he] at hi
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hi
    obtain ⟨-, rfl, rfl, -, rfl⟩ := hi
    exact ⟨rfl, ⟨.inr rfl, rfl, rfl⟩, st, hst, .inr ⟨u, j, h, rfl, rfl, rfl⟩⟩

theorem same_acc {i i' : EvId} {d d' : Nat} {s s' : OperandSpec}
    (hs : Spec128 s (i.1 / L.block)) (hs' : Spec128 s' (i'.1 / L.block))
    (hc : i.1 / L.block = i'.1 / L.block) (hd : d = d') : SameAccumulator d s d' s' := by
  have e : ∀ {s : OperandSpec} {c : Nat}, Spec128 s c → s.descriptor.m = 128 ∧
      s.descriptor.n = 128 := by
    intro s c h
    rcases h.dsc with h | h <;> rw [h] <;> exact ⟨rfl, rfl⟩
  exact ⟨hd, (e hs).1.trans (e hs').1.symm, (e hs).2.trans (e hs').2.symm,
    by rw [hs.low, hs'.low, hc], by rw [hs.high, hs'.high, hc]⟩

/-- **The score facts.** -/
theorem scoreFacts (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) : ScoreFacts L X where
  no_cp := fun e c => noCp_of_consistent kernel_noTcCp hX e c
  no_shift := fun e s => no_shift hX
  mma_cells := by
    intro i d s acc mask hi
    obtain ⟨hw, st, u, j, hst, h⟩ := mma_qkpv hp hX hFw ⟨_, _, _, _, hi⟩
    obtain ⟨pc, he⟩ := hi
    refine ⟨Frame.lt_of_get hX (k := i.2) he, hw, st, hst, ?_⟩
    rcases h with h | h
    · exact .inl fun cell hc => h.cells hst hc
    · exact .inr fun cell hc => h.cells hst hc
  tc_one := by
    rintro ⟨g, k⟩ ⟨g', k'⟩ hi hi' hc
    obtain ⟨hw, -⟩ := mma_qkpv hp hX hFw hi
    obtain ⟨d, s, acc, mask, hi⟩ := hi
    rcases hi' with hi' | ⟨s', hi'⟩
    · obtain ⟨hw', -⟩ := mma_qkpv hp hX hFw hi'
      obtain ⟨d', s', acc', mask', hi'⟩ := hi'
      exact Mma.mma_lane hp hX hw hw' hc hi hi'
    · exact Mma.mma_commit_lane hp hX hw (commit_warp hp hX hFw hi') hc hi hi'
  mma_acc := by
    intro i i' d d' st s s' acc acc' mask mask' cell cell' hi hi' hc hc' hcta hst h
    obtain ⟨-, hs, st1, hst1, h1⟩ := mma_acc_at hp hX hFw hi
    obtain ⟨-, hs', st2, hst2, h2⟩ := mma_acc_at hp hX hFw hi'
    have hcc : cell.cta = i.1 / L.block := by
      rcases h1 with ⟨_, _, h, -⟩ | ⟨_, _, h, -⟩ <;> exact (h.cells hst1 (cell := cell) hc).2
    have hcc' : cell'.cta = i'.1 / L.block := by
      rcases h2 with ⟨_, _, h, -⟩ | ⟨_, _, h, -⟩ <;> exact (h.cells hst2 (cell := cell') hc').2
    refine same_acc hs hs' (by rw [← hcc, hcta, hcc']) ?_
    rcases h with ⟨hS, hS'⟩ | ⟨hO, hO'⟩
    · rcases h1 with ⟨_, _, q1, e1, -⟩ | ⟨_, _, q1, -⟩
      swap
      · exact (inS_inO hst hS (q1.cells hst1 (cell := cell) hc).1).elim
      rcases h2 with ⟨_, _, q2, e2, -⟩ | ⟨_, _, q2, -⟩
      swap
      · exact (inS_inO hst hS' (q2.cells hst2 (cell := cell') hc').1).elim
      have a1 := inS_st hS (q1.cells hst1 (cell := cell) hc).1
      have a2 := inS_st hS' (q2.cells hst2 (cell := cell') hc').1
      rw [e1, e2, ← a1, ← a2]
    · rcases h1 with ⟨_, _, q1, -⟩ | ⟨_, _, q1, e1, -⟩
      · exact (inS_inO hst1 (q1.cells hst1 (cell := cell) hc).1 hO).elim
      rcases h2 with ⟨_, _, q2, -⟩ | ⟨_, _, q2, e2, -⟩
      · exact (inS_inO hst2 (q2.cells hst2 (cell := cell') hc').1 hO').elim
      have a1 := inO_st hO (q1.cells hst1 (cell := cell) hc).1
      have a2 := inO_st hO' (q2.cells hst2 (cell := cell') hc').1
      rw [e1, e2, ← a1, ← a2]
  qk_polls := by
    intro i cell st hst hi hc hS
    obtain ⟨u, j, h⟩ := qk_of_cell hp hX hFw hi hc hS hst
    rw [h.com, h.p, h.p2]
    exact ⟨le_rfl, le_rfl⟩
  pv_polls := by
    intro i d s acc mask cell st hi hc hO
    obtain ⟨hst, u, j, h⟩ := pv_of_cell hp hX hFw ⟨_, _, _, _, hi⟩ hc hO
    obtain ⟨-, hs, st1, hst1, h1⟩ := mma_acc_at hp hX hFw hi
    rw [h.com, h.p, h.p2]
    rcases h1 with ⟨_, _, q1, -⟩ | ⟨u1, j1, q1, -, hd, ha⟩
    · exact (inS_inO hst1 (q1.cells hst1 (cell := cell) hc).1 hO).elim
    obtain rfl := inO_st hO (q1.cells hst1 (cell := cell) hc).1
    refine ⟨by omega, le_rfl, by rw [ha]; rfl, fun index c pos hac => ?_⟩
    have hj1 := j1.isLt
    have hcol : c.cta = i.1 / L.block ∧ 128 * st + 64 + 8 * j1.val ≤ c.column ∧
        c.column < 128 * st + 64 + 8 * j1.val + 8 := by
      unfold aCell at hac
      rw [hd, ha, hs.low, hs.high] at hac
      simp only [Option.bind_some] at hac
      split at hac
      · simp only [Option.some.injEq, Prod.mk.injEq] at hac
        obtain ⟨rfl, -⟩ := hac
        have hm : index % (pvDsc.kind.k * pvDsc.kind.width) / 4 < 8 := by
          have : index % (pvDsc.kind.k * pvDsc.kind.width) < 32 :=
            Nat.mod_lt _ (by decide)
          omega
        refine ⟨by simp, ?_, ?_⟩ <;> simp only <;> omega
      · cases hac
    refine ⟨⟨by omega, by omega⟩, hcol.1, fun hhi => ?_⟩
    have hk := q1.p2
    rw [h.p2] at hk
    unfold InPHigh at hhi
    have hp1 := q1.p
    rw [h.p] at hp1
    rw [ite_eq_left (show 5 < j1.val by omega)] at hk
    omega
  pv_qk := by
    rintro ⟨g, k⟩ ⟨g', k'⟩ cell cell' st hst hi hi' hg hc hO hc' hS hle
    simp only at hg hle ⊢
    subst hg
    obtain ⟨-, u, j, h⟩ := pv_of_cell hp hX hFw hi hc hO
    obtain ⟨u', j', h'⟩ := qk_of_cell hp hX hFw hi' hc' hS hst
    simp only at h h'
    have e1 := h.p
    have e2 := h'.com
    exact Mma.pv_qk hst h h' (by omega)
  mma_reads := by
    intro i d s acc mask row col cell hi hr
    obtain ⟨rfl, hs, st1, hst1, h1⟩ := mma_acc_at hp hX hFw hi
    refine ⟨d, s, acc, _, row, col, hi, ?_⟩
    rw [writeCell_zero hs (by rcases h1 with ⟨_, _, -, h, -⟩ | ⟨_, _, -, h, -⟩ <;> omega)]
    exact hr
  mma_cell := by
    intro i d s acc mask hi
    obtain ⟨rfl, hs, st1, hst1, h1⟩ := mma_acc_at hp hX hFw hi
    have hb : d + 128 ≤ 512 := by rcases h1 with ⟨_, _, -, h, -⟩ | ⟨_, _, -, h, -⟩ <;> omega
    refine ⟨⟨i.1 / L.block, 0, d + 0⟩, d, s, acc, _, 0, 0, hi, ?_⟩
    rw [writeCell_zero hs hb]
    exact resultCell_128 hs hb (by decide) (by decide)
  qk_smem := by
    intro i d st s acc mask cell hst hi hc hS
    obtain ⟨-, hs, st1, hst1, h1⟩ := mma_acc_at hp hX hFw hi
    rcases h1 with ⟨_, _, -, -, -, h⟩ | ⟨_, _, q1, -⟩
    · exact h
    · exact (inS_inO hst hS (q1.cells hst1 (cell := cell) hc).1).elim
  tc_role := by
    intro g i a vals sh h
    have hw := ldst_warp hp hX hFw h
    rcases h with ⟨pc, he⟩ | ⟨pc, he⟩ <;> exact ⟨Frame.lt_of_get hX he, hw⟩
  tc_shape := by
    rintro ⟨g, k⟩ a vals sh h
    have hw := ldst_warp hp hX hFw h
    by_cases h8 : Prologue.warpIndex L g < 8
    · rcases h with h | h
      · exact (Softmax.soft_ld hp hX hFw h8 h).1
      · exact (Softmax.soft_st hp hX hFw h8 h).1
    · rcases h with h | h
      · exact (Correction.corr_ld hp hX hFw (by omega) (by omega) h).1
      · exact (Correction.corr_st hp hX hFw (by omega) (by omega) h).1
  soft_ld := by
    intro h i a vals hh hw hl
    obtain ⟨-, hlen, ⟨c, hc⟩, h1, -, hwt⟩ := Softmax.soft_ld hp hX hFw hw hl
    refine ⟨fun j hj => ?_, fun e ev hie he ha => ?_, h1⟩
    · have := c.isLt
      refine ⟨?_, ?_⟩ <;> simp only [tcDataCell32] <;> omega
    · obtain ⟨pc, kd⟩ := ev
      cases kd <;> simp [arrivesOn, sourceArrive] at ha
      subst ha
      exact hwt e pc _ _ _ _ hie he
  soft_st := by
    intro h i a vals hh hw hl
    obtain ⟨-, hlen, q, hc, h1, h2, -⟩ := Softmax.soft_st hp hX hFw hw hl
    have hq := q.isLt
    refine ⟨fun j hj => ?_, ?_, h1, ?_, fun e hne => Softmax.soft_st_wait hp hX hFw hw hl hne⟩
    · refine ⟨?_, ?_⟩ <;> simp only [tcDataCell32] <;> omega
    · by_cases h3 : q.val < 3
      · refine .inl fun j hj hh => ?_
        unfold InPHigh at hh
        simp only [tcDataCell32] at hh
        omega
      · refine .inr fun j hj => ?_
        unfold InPHigh
        simp only [tcDataCell32]
        omega
    · by_cases h3 : q.val < 3
      · rw [ite_eq_left h3] at h2
        exact .inr h2
      · refine .inl fun j hj => ?_
        unfold InPHigh
        simp only [tcDataCell32]
        omega
  soft_p := fun hw he => Softmax.soft_p hp hX hFw hw he
  soft_ld_st := by
    intro h i i' a a' vals vals' hh hw hl hs hq
    obtain ⟨-, -, -, -, h1, -⟩ := Softmax.soft_ld hp hX hFw hw hl
    obtain ⟨-, -, q, -, -, -, h2⟩ := Softmax.soft_st hp hX hFw hw hs
    by_contra hle
    obtain ⟨pc, he⟩ := hs
    have hlt : i' < i := by
      rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hle) with rfl | hlt
      · obtain ⟨pc', he'⟩ := hl
        rw [he] at he'
        cases he'
      · exact hlt
    have h3 : stN X h i' + 1 ≤ stN X h i := by
      unfold stN
      have e1 : ((X.tr h).take (i' + 1)).countP isTcSt = ((X.tr h).take i').countP isTcSt + 1 := by
        rw [List.take_add_one, show (X.tr h)[i']? = _ from he, Option.toList_some,
          List.countP_append]
        rfl
      have e2 : ((X.tr h).take (i' + 1)).countP isTcSt ≤ ((X.tr h).take i).countP isTcSt :=
        (List.take_prefix_take_left (show i' + 1 ≤ i by omega)).sublist.countP_le
      omega
    omega
  soft_st_one := by
    intro h i i' a a' j j' vals vals' hh hw hl hs hj hj' hc hq
    obtain ⟨-, l1, q, c1, -, -, h1⟩ := Softmax.soft_st hp hX hFw hw hl
    obtain ⟨-, l2, q', c2, -, -, h2⟩ := Softmax.soft_st hp hX hFw hw hs
    simp only [tcDataCell32, Cell.mk.injEq, true_and] at hc
    have hqq : q.val = q'.val := by omega
    have hN : stN X h i = stN X h i' := by omega
    obtain ⟨pc, he⟩ := hl
    obtain ⟨pc', he'⟩ := hs
    have key : ∀ {i i' pc : Nat} {k : TcKind}, X.get (h, i) = some ⟨pc, .tc k⟩ →
        isTcSt ⟨pc, .tc k⟩ = true → i < i' → stN X h i + 1 ≤ stN X h i' := by
      intro i i' pc k he hk hlt
      unfold stN
      have e1 : ((X.tr h).take (i + 1)).countP isTcSt = ((X.tr h).take i).countP isTcSt + 1 := by
        rw [List.take_add_one, show (X.tr h)[i]? = _ from he, Option.toList_some,
          List.countP_append]
        simp [hk]
      have e2 : ((X.tr h).take (i + 1)).countP isTcSt ≤ ((X.tr h).take i').countP isTcSt :=
        (List.take_prefix_take_left (show i + 1 ≤ i' by omega)).sublist.countP_le
      omega
    rcases Nat.lt_trichotomy i i' with hlt | h' | hlt
    · have := key he rfl hlt; omega
    · exact h'
    · have := key he' rfl hlt; omega

/-- The correction cells' stage. -/
theorem inO_col {h a j st : Nat} (hO : InO st (tcDataCell32 L h a j)) :
    256 + 128 * st ≤ a % 2 ^ 16 + j ∧ a % 2 ^ 16 + j < 384 + 128 * st := hO

/-- **The output accumulator's facts.** -/
theorem oAccFacts (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) : OAccFacts L X where
  corr_ld := by
    intro h i a vals hh h8 h12 hl
    obtain ⟨-, st, hst, h1, h2, h3⟩ := Correction.corr_ld hp hX hFw h8 (by omega) hl
    refine ⟨st, hst, fun j hj => ?_,
      fun _ ⟨hq,_,he,_,hu⟩ => Correction.corr_ld_wait' hp hX hFw h8 (by omega) hl hq he hu, h3⟩
    refine ⟨?_, ?_⟩ <;> simp only [tcDataCell32] <;> omega
  corr_st := by
    intro h i a vals hh h8 h12 hl
    obtain ⟨-, st, hst, h1, h2, h3⟩ := Correction.corr_st hp hX hFw h8 (by omega) hl
    by_cases hv : vals.length = 0
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hv'⟩ :=
        Correction.corr_st_state hp hX hFw h8 (by omega) hl
      omega
    refine ⟨st, hst, fun j hj => ?_, h3, fun e hne =>
      Correction.corr_st_wait hp hX hFw h8 (by omega) hl hst h1 (by omega) hne⟩
    refine ⟨?_, ?_⟩ <;> simp only [tcDataCell32] <;> omega
  corr_ld_st := by
    intro h i i' a a' j j' st vals vals' hh h8 h12 hl hs hj hj' hc hO hq
    obtain ⟨-, st1, hst1, h1, h2, -⟩ := Correction.corr_ld hp hX hFw h8 (by omega) hl
    obtain ⟨o1, o2⟩ := inO_col hO
    simp only [tcDataCell32, Cell.mk.injEq, true_and] at hc
    obtain rfl : st = st1 := by omega
    exact Correction.corr_ld_st hp hX hFw h8 (by omega) hl hs hst1 h1 (by omega) hj hj' hc hq
  corr_st_one := by
    intro h i i' a a' j j' st vals vals' hh h8 h12 hl hs hj hj' hc hO hq
    obtain ⟨-, st1, hst1, h1, h2, -⟩ := Correction.corr_st hp hX hFw h8 (by omega) hl
    obtain ⟨o1, o2⟩ := inO_col hO
    simp only [tcDataCell32, Cell.mk.injEq, true_and] at hc
    obtain rfl : st = st1 := by omega
    exact Correction.corr_st_one hp hX hFw h8 (by omega) hl hs hst1 h1 (by omega) hj hj' hc hq

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm
