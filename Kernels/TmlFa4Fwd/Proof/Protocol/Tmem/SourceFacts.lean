-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.SourceDef
public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.FactsProof
import Kernels.TmlFa4Fwd.Proof.Correction.Export.Tmem
import Kernels.TmlFa4Fwd.Proof.Correction.Export.TmemRoute
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Before
import Kernels.TmlFa4Fwd.Proof.Mma.Export.BeforePv
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Count
import Kernels.TmlFa4Fwd.Proof.Protocol.O.Dealloc
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Rounds
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Handoffs
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Info
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.LdstDealloc
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Role
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Word
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemStores
import Lemmas.Tcgen05.TcMmaACell
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The facts for the read sources (`sourceFacts`)

An access completes before the releases of its CTA (`tmemLive`, the orders of the access-lifetime
class). A softmax load follows its S-full poll, whose commit follows a QK MMA of the tile
(`Mma.qk_before_commit`). A correction load of credit `q` follows a softmax S-full poll of ordinal
`q`, whose commit follows `q` P-full polls, or the poll of the final O commit, which follows one
P-full poll more than the tile's rounds: before the commit, the P-full poll of ordinal `q - 1` is
followed by the PV block of the tile (`Mma.pv_before`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

theorem tmemLive : TmemLive L X := by
  intro e cell ha cta r hr hcov d hrel
  obtain ⟨hacc, hno_cp, hno_shift⟩ := tmem_info hp hX hFw
  obtain ⟨he, hc, hcol, hk⟩ := hacc ha
  have hto := (tmem1Facts hp hX hFw).toTmem1Ops
  obtain ⟨⟨pc, grp, a, n, hd⟩, hdc⟩ := Tmem1.release_info hX hto hr hrel
  have hown := Tmem1.covers_owner hcov
  obtain ⟨hlc, -⟩ := Tmem.One.record_info hX hto hr
  have hcell : d.1 / L.block = e.1 / L.block := by rw [hdc, ← hlc, ← hown, hc]
  refine ⟨fun ⟨a', vals, sh, hld⟩ => ?_, fun ⟨a', vals, sh, hst⟩ => ?_, fun hasync => ?_⟩
  · exact (ldst_dealloc hp hX hFw hd hcell).1 hld
  · exact (ldst_dealloc hp hX hFw hd hcell).2 hst
  · rcases hasync with hm | ⟨c, hcp⟩ | ⟨s, hsh⟩
    · exact mma_done hp hX hFw hm hd hcell
    · exact (hno_cp _ _ hcp).elim
    · exact (hno_shift _ _ hsh).elim

omit hFw hX in
/-- The cell of a lane's load or store. -/
theorem cell_lane {h a j : Nat} : (tcDataCell32 L h a j).lane < 128 ∧
    (tcDataCell32 L h a j).cta = h / L.block := by
  refine ⟨?_, rfl⟩
  have hb := hp.block
  simp only [tcDataCell32, laneBase, laneOf]
  rw [hb]
  omega

/-- A QK MMA writes the cells of its stage's scores. -/
theorem qk_cell {g k st u : Nat} {j : Fin 8} {cell : Cell} (hst : st < 2)
    (h : Qk L X g k st u j) (hc : cell.cta = g / L.block) (hl : cell.lane < 128)
    (hS : InS st cell) : X.MmaCell (g, k) cell := by
  obtain ⟨pc, da, db, he⟩ := h.issue
  refine (scoreFacts hp hX hFw).mma_reads (row := cell.lane) (col := cell.column - 128 * st)
    ⟨pc, he⟩ ?_
  unfold InS at hS
  rw [resultCell_128 ⟨.inl rfl, rfl, rfl⟩ (by omega) hl (by omega)]
  obtain ⟨c, l, o⟩ := cell
  simp only [Option.some.injEq, Cell.mk.injEq] at hc hS ⊢
  exact ⟨hc.symm, trivial, by omega⟩

/-- A PV MMA writes the cells of its stage's output accumulator. -/
theorem pv_cell {g k st u : Nat} {j : Fin 8} {cell : Cell} (hst : st < 2)
    (h : Pv L X g k st u j) (hc : cell.cta = g / L.block) (hl : cell.lane < 128)
    (hO : InO st cell) : X.MmaCell (g, k) cell := by
  obtain ⟨pc, db, he⟩ := h.issue
  refine (scoreFacts hp hX hFw).mma_reads (row := cell.lane)
    (col := cell.column - (256 + 128 * st)) ⟨pc, he⟩ ?_
  unfold InO at hO
  rw [resultCell_128 ⟨.inr rfl, rfl, rfl⟩ (by omega) hl (by omega)]
  obtain ⟨c, l, o⟩ := cell
  simp only [Option.some.injEq, Cell.mk.injEq] at hc hO ⊢
  exact ⟨hc.symm, trivial, by omega⟩

/-- The lane of an MMA's cell. -/
theorem mma_cell_lane {i : EvId} {cell : Cell} (hc : X.MmaCell i cell) : cell.lane < 128 := by
  obtain ⟨d, s, acc, mask, row, col, hi, hw⟩ := hc
  obtain ⟨rfl, hs, st, hst, h⟩ := mma_acc_at hp hX hFw hi
  have hd : d + 128 ≤ 512 := by
    rcases h with ⟨_, _, -, h, -⟩ | ⟨_, _, -, h, -⟩ <;> omega
  rw [writeCell_zero hs hd] at hw
  obtain ⟨hr, -, rfl⟩ := resultCell_128_iff hs hd hw
  exact hr

theorem soft_cover {h i a j : Nat} {vals : List Value} (hh : h < L.threads)
    (hw : Prologue.warpIndex L h < 8) (hld : X.TLd (h, i) a vals .s32x32b) (hj : j < vals.length) :
    ∃ x, IsMma X x ∧ X.MmaCell x (tcDataCell32 L h a j) ∧
      sCommits L X x.1 (Prologue.warpIndex L h / 4) x.2 + 1 =
        sPolls L X h (Prologue.warpIndex L h / 4) i := by
  have ht := scoreFacts hp hX hFw
  obtain ⟨hS, -, hcnt⟩ := ht.soft_ld hh hw hld
  have hst : Prologue.warpIndex L h / 4 < 2 := by omega
  obtain ⟨j', pc, par, acq, sc, hji, hget, hq⟩ := MbarRing.UnitHandoff.exists_poll (X := X)
    (m := sFull L (h / L.block) (Prologue.warpIndex L h / 4)) (h := h) (f := i)
    (c := sPolls L X h (Prologue.warpIndex L h / 4) i - 1) (by unfold sPolls at hcnt ⊢; omega)
  obtain ⟨⟨y, k⟩, s, rank, ws, hcom, hcy, hb, hcc, -⟩ := sFullHandoff hp hX hFw hh hw hget
  simp only at hcy hb hcc
  have hyw := commit_warp hp hX hFw hcom
  obtain ⟨k', -, hqk, -⟩ := Mma.qk_before_commit hp hX hFw hyw hst hcom hb
  obtain ⟨hl, hcta⟩ := cell_lane hp (L := L) (h := h) (a := a) (j := j)
  refine ⟨(y, k'), ?_, qk_cell hp hX hFw hst hqk (by rw [hcta, hcy]) hl (hS j hj), ?_⟩
  · obtain ⟨_, _, _, he⟩ := hqk.issue
    exact ⟨_, _, _, _, _, he⟩
  · have h1 := hqk.com
    have h2 : sPolls L X h (Prologue.warpIndex L h / 4) j' =
      sPolls L X h (Prologue.warpIndex L h / 4) i - 1 := hq
    simp only
    omega

/-- A PV MMA of a tile before a commit of the CTA. -/
theorem pv_of_commit {h a j y k st q : Nat} {s : TcCommit.Spec} (hst : st < 2)
    (hcom : X.Commit (y, k) s) (hcy : y / L.block = h / L.block)
    (hq1 : 1 ≤ q) (hq : q ≤ pPolls L X y st k) (hO : InO st (tcDataCell32 L h a j)) :
    ∃ x, IsMma X x ∧ X.MmaCell x (tcDataCell32 L h a j) ∧ pPolls L X x.1 st x.2 = q := by
  have hyw := commit_warp hp hX hFw hcom
  obtain ⟨pc, he⟩ := id hcom
  obtain ⟨k', -, hpv⟩ := Mma.pv_before hp hX hFw hyw (v := q - 1) hst he (.inr ⟨_, rfl⟩) (by omega)
  obtain ⟨hl, hcta⟩ := cell_lane hp (L := L) (h := h) (a := a) (j := j)
  refine ⟨(y, k'), ?_, pv_cell hp hX hFw hst hpv (by rw [hcta, hcy]) hl hO, ?_⟩
  · obtain ⟨_, _, he'⟩ := hpv.issue
    exact ⟨_, _, _, _, _, he'⟩
  · have := hpv.p
    simp only
    omega

/-- **The commit a correction load follows**: by it the MMA lane has polled the stage's P-full
barrier as often as the load's credit. -/
theorem corr_commit {h i a j st : Nat} {vals : List Value} (hh : h < L.threads)
    (h8 : 8 ≤ Prologue.warpIndex L h) (h12 : Prologue.warpIndex L h < 12)
    (hld : X.TLd (h, i) a vals .s32x32b) (hj : j < vals.length)
    (hO : InO st (tcDataCell32 L h a j)) :
    st < 2 ∧ 1 ≤ pArr L X h st i ∧ ∃ y k s, X.Commit (y, k) s ∧ y / L.block = h / L.block ∧
      pArr L X h st i ≤ pPolls L X y st k := by
  obtain ⟨st', hst', hcells, -, h1⟩ := (oAccFacts hp hX hFw).corr_ld hh h8 h12 hld
  obtain rfl := inO_st hO (hcells j hj)
  have hst := hst'
  refine ⟨hst, h1, ?_⟩
  rcases oRoute hp hX hFw hh h8 h12 (.inl hld) hcells with
    ⟨g, e, pc, par, acq, sc, hg, hgc, hw, hgs, hget, hq, -⟩ | ⟨j', pc, par, acq, sc, hji, hget, -⟩
  · subst hgs
    obtain ⟨⟨y, k⟩, s, rank, ws, hcom, hcy, hb, hcc, -⟩ := sFullHandoff hp hX hFw hg hw hget
    simp only at hcy hb hcc
    have hyw := commit_warp hp hX hFw hcom
    obtain ⟨-, -, -, -, hpp⟩ := Mma.qk_before_commit hp hX hFw hyw hst hcom hb
    exact ⟨y, k, s, hcom, hcy.trans hgc, by omega⟩
  · obtain ⟨⟨y, k⟩, s, rank, ws, hcom, hcy, hb, -⟩ := oFullHandoff hp hX hFw hh h8 h12 hst hget
    simp only at hcy hb
    have hyw := commit_warp hp hX hFw hcom
    obtain ⟨pcc, he⟩ := id hcom
    have hy := Frame.lt_of_get hX he
    obtain ⟨-, R, hR, jl, pce, mk, inst, ld, hjl, hel, hall⟩ :=
      mma_o_commit hp hX hFw ⟨st, hst⟩ hyw he hb
    have hpoll := hall y ⟨⟨hy, hy, rfl⟩, rfl⟩ _ _ _ _ _ hel rfl
    have hmono : R + 1 ≤ pPolls L X y st k := by
      rw [← hpoll]
      exact countP_take_mono _ _ hjl.le
    refine ⟨y, k, s, hcom, hcy, ?_⟩
    have hj0 := hcells j hj
    unfold InO at hj0
    simp only [tcDataCell32] at hj0
    obtain ⟨-, st2, hst2, e1, e2, -⟩ := Correction.corr_ld hp hX hFw h8 (by omega) hld
    have hc0 := hcells 0 (by omega)
    unfold InO at hc0
    simp only [tcDataCell32] at hc0
    have key : ∃ R', CorrRounds p L h R' ∧ pArr L X h st i ≤ R' + 1 := by
      rcases Correction.corr_route hp hX hFw h8 (by omega) (.inl hld) (st := st) (by omega)
        (by omega) hst with ⟨-, R', hR', hle⟩ | ⟨-, R', hR', hle⟩
      · exact ⟨R', hR', by omega⟩
      · exact ⟨R', hR', by omega⟩
    obtain ⟨R', hR', hle⟩ := key
    have hRR := (MmaRounds.cta hcy hR).unique (hR'.mma hp hh)
    omega

theorem corr_cover {h i a j st : Nat} {vals : List Value} (hh : h < L.threads)
    (h8 : 8 ≤ Prologue.warpIndex L h) (h12 : Prologue.warpIndex L h < 12)
    (hld : X.TLd (h, i) a vals .s32x32b) (hj : j < vals.length)
    (hO : InO st (tcDataCell32 L h a j)) :
    ∃ x, IsMma X x ∧ X.MmaCell x (tcDataCell32 L h a j) ∧
      pPolls L X x.1 st x.2 = pArr L X h st i := by
  obtain ⟨hst, h1, y, k, s, hcom, hcy, hle⟩ := corr_commit hp hX hFw hh h8 h12 hld hj hO
  exact pv_of_commit hp hX hFw hst hcom hcy h1 hle hO

theorem qk_acc {i : EvId} {d : Nat} {s : OperandSpec} {mask : List Nat} {cell : Cell} {st : Nat}
    (hst : st < 2) (hi : X.MmaIssue i d s true mask) (hc : X.MmaCell i cell) (hS : InS st cell) :
    ∃ k < i.2, X.MmaCell (i.1, k) cell ∧ sCommits L X i.1 st k = sCommits L X i.1 st i.2 := by
  obtain ⟨u, j, hq⟩ := qk_of_cell hp hX hFw ⟨_, _, _, _, hi⟩ hc hS hst
  have hw := mma_warp hp hX hFw hi
  have hj : j ≠ 0 := by
    rintro rfl
    obtain ⟨pc, hi⟩ := hi
    obtain ⟨_, _, _, he⟩ := hq.issue
    rw [show i = (i.1, i.2) from rfl, he] at hi
    simp at hi
  obtain ⟨k', hk', j', -, hq'⟩ := Mma.qk_prev hp hX hFw hw hq hj
  have hcells := (mma_s (scoreFacts hp hX hFw) hi hc hS hst cell hc).2
  exact ⟨k', by omega, qk_cell hp hX hFw hst hq' hcells (mma_cell_lane hp hX hFw hc) hS,
    hq'.com.trans hq.com.symm⟩

theorem pv_acc {i : EvId} {d : Nat} {s : OperandSpec} {mask : List Nat} {cell : Cell} {st : Nat}
    (hi : X.MmaIssue i d s true mask) (hc : X.MmaCell i cell) (hO : InO st cell) :
    ∃ k < i.2, X.MmaCell (i.1, k) cell ∧ pPolls L X i.1 st i.2 ≤ pPolls L X i.1 st k + 1 := by
  obtain ⟨hst, u, j, hq⟩ := pv_of_cell hp hX hFw ⟨_, _, _, _, hi⟩ hc hO
  have hw := mma_warp hp hX hFw hi
  have hju : j ≠ 0 ∨ u ≠ 0 := by
    by_contra hn
    push Not at hn
    obtain ⟨rfl, rfl⟩ := hn
    obtain ⟨pc, hi⟩ := hi
    obtain ⟨_, _, he⟩ := hq.issue
    rw [show i = (i.1, i.2) from rfl, he] at hi
    simp at hi
  have hcells := (mma_o (scoreFacts hp hX hFw) hi hc hO cell hc).2
  have hpp := hq.p
  obtain ⟨v, hv, hv2⟩ : ∃ v, v + 1 ≤ pPolls L X i.1 st i.2 ∧
      (pPolls L X i.1 st i.2 ≤ v + 2 ∧ (j ≠ 0 ∨ v ≠ u)) := by
    by_cases hj : j = 0
    · have hu := hju.resolve_left (not_not_intro hj)
      exact ⟨u - 1, by omega, by omega, .inr (by omega)⟩
    · exact ⟨u, by omega, by omega, .inl hj⟩
  obtain ⟨pc, he⟩ := id hi
  obtain ⟨k', hk', hpv⟩ := Mma.pv_before hp hX hFw hw (g := i.1) (K := i.2) hst he
    (.inl ⟨_, _, _, _, rfl⟩) hv
  have hne : k' ≠ i.2 := by
    rintro rfl
    have h1 := hpv.p
    rcases hv2.2 with hj | hj
    · obtain ⟨_, _, e1⟩ := hpv.issue
      obtain ⟨_, _, e2⟩ := hq.issue
      rw [e1] at e2
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq,
        OperandSpec.mk.injEq] at e2
      obtain ⟨-, -, ⟨-, -, -, -, -, h3, -⟩, -⟩ := e2
      have : j.val = 0 := by
        simp only [Fin.isValue, Fin.val_zero] at h3
        omega
      exact hj (Fin.ext this)
    · omega
  refine ⟨k', by omega, pv_cell hp hX hFw hst hpv hcells (mma_cell_lane hp hX hFw hc) hO, ?_⟩
  have h1 := hpv.p
  omega

theorem same_write {i i' : EvId} {d d' : Nat} {s s' : OperandSpec} {acc acc' : Bool}
    {mask mask' : List Nat} {cell : Cell} (hi : X.MmaIssue i d s acc mask)
    (hi' : X.MmaIssue i' d' s' acc' mask') (hg : i.1 = i'.1) (hc : X.MmaCell i cell)
    (hc' : X.MmaCell i' cell) :
    SameAccumulator d s d' s' ∧ ∀ row col,
      writeCell s d mask row col = writeCell s' d' mask' row col := by
  have ht := scoreFacts hp hX hFw
  obtain ⟨rfl, hs, st, hst, h⟩ := mma_acc_at hp hX hFw hi
  obtain ⟨rfl, hs', st', hst', h'⟩ := mma_acc_at hp hX hFw hi'
  have hd : d + 128 ≤ 512 := by rcases h with ⟨_, _, -, h, -⟩ | ⟨_, _, -, h, -⟩ <;> omega
  have hd' : d' + 128 ≤ 512 := by rcases h' with ⟨_, _, -, h, -⟩ | ⟨_, _, -, h, -⟩ <;> omega
  have hacc : SameAccumulator d s d' s' := by
    obtain ⟨-, -, st1, hst1, h1⟩ := ht.mma_cells hi
    rcases h1 with h1 | h1
    · have hS := (h1 cell hc).1
      exact ht.mma_acc hi hi' hc hc' rfl hst1 (.inl ⟨hS, hS⟩)
    · have hO := (h1 cell hc).1
      exact ht.mma_acc hi hi' hc hc' rfl hst1 (.inr ⟨hO, hO⟩)
  refine ⟨hacc, fun row col => ?_⟩
  obtain rfl : d = d' := hacc.1
  rw [writeCell_zero hs hd, writeCell_zero hs' hd']
  have hcta : i.1 / L.block = i'.1 / L.block := by rw [hg]
  rw [← hcta] at hs'
  by_cases hrc : row < 128 ∧ col < 128
  · rw [resultCell_128 hs hd hrc.1 hrc.2, resultCell_128 hs' hd hrc.1 hrc.2]
  · have hnone : ∀ {s : OperandSpec}, Spec128 s (i.1 / L.block) →
        resultCell s d row col = none := by
      intro s hs
      cases hr : resultCell s d row col with
      | none => rfl
      | some c =>
        obtain ⟨a, b, -⟩ := resultCell_128_iff hs hd hr
        exact absurd ⟨a, b⟩ hrc
    rw [hnone hs, hnone hs']

omit hp hX hFw in
/-- A column of a lane's row, as a store's register. -/
theorem store_reg {h a col q st : Nat} (ha : a % 65536 = 128 * st + 64 + 16 * q)
    (h1 : 128 * st + 64 + 16 * q ≤ col) :
    tcDataCell32 L h a (col - (128 * st + 64 + 16 * q)) = tcDataCell32 L h 0 col := by
  simp only [tcDataCell32, Cell.mk.injEq]
  exact ⟨trivial, trivial, by omega⟩

/-- **The facts for the read sources.** -/
theorem sourceFacts : SourceFacts L X where
  live := tmemLive hp hX hFw
  soft_cover := soft_cover hp hX hFw
  corr_cover := corr_cover hp hX hFw
  qk_acc := qk_acc hp hX hFw
  pv_acc := pv_acc hp hX hFw
  same_write := same_write hp hX hFw
  a_lane := by
    intro i d s acc mask index pos c hi ha
    obtain ⟨-, -, st, -, h⟩ := mma_acc_at hp hX hFw hi
    refine aCell_lane ?_ ha
    rcases h with ⟨_, _, -, -, hd, -⟩ | ⟨_, _, -, -, hd, -⟩ <;> rw [hd] <;> rfl
  soft_low := by
    intro h e pc tx cnt col rel sc hw he hP hH
    unfold InP at hP
    unfold InPHigh at hH
    simp only [tcDataCell32] at hP hH
    obtain ⟨k, a, vals, hk, hs, hlen, ha, hcnt⟩ := Softmax.soft_store_low hp hX hFw hw
      ⟨(col - (128 * (Prologue.warpIndex L h / 4) + 64)) / 16, by omega⟩
      (by simp only; omega) he
    simp only at ha
    exact ⟨k, a, col - (128 * (Prologue.warpIndex L h / 4) + 64 + 16 *
      ((col - (128 * (Prologue.warpIndex L h / 4) + 64)) / 16)), vals, hk, hs, by omega,
      store_reg ha (by omega), hcnt⟩
  soft_high := by
    intro h b mask inst col hw hb hP hH
    unfold InP at hP
    unfold InPHigh at hH
    simp only [tcDataCell32] at hP hH
    obtain ⟨k, a, vals, hk, hs, hlen, ha, hcnt⟩ := Softmax.soft_store_high hp hX hFw hw hb
    exact ⟨k, a, col - (128 * (Prologue.warpIndex L h / 4) + 64 + 16 * 3), vals, hk, hs, by omega,
      store_reg (q := 3) (by omega) (by omega), hcnt⟩
  elected := by
    intro h u f hh hw hf hc hp2
    obtain ⟨b, mask, inst, hb, hu, -⟩ := p2_elected hp hX hFw hh hw hf hc hp2
    exact ⟨b, mask, inst, hb, hu⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm
