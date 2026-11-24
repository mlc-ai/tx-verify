-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaDataTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Rescale
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Kernel.Frame
import Lemmas.Flow.Final
import Lemmas.Tcgen05.TcMmaResultLayout
import Lemmas.Tcgen05.TcMmaSource
import Lemmas.Tcgen05.TcDataCell
import Lemmas.Flow.NotTcCp
import Lemmas.Flow.NotTcMma
import Lemmas.Flow.NotTcShift
import Lemmas.Flow.NotTcSt
import Lemmas.Flow.OpPcsFast

import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxQkParity
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxTmemStore
import Lemmas.Flow.NotBulk

@[expose] public section

/-! # Tensor Memory writers of the WG0 score columns -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0ScoreSources

open PTX.Flow Wg1Mma MmaDataTrace MachineTracking

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

private def writerOp (op : Op) : Bool :=
  tcMmaOp op || tcCpOp op || tcStOp op || tcShiftOp op

private def writerSites : List Nat :=
  Flow.mma.toList ++ Flow.tmemCopy.toList ++ [814, 915, 1016, 1117]

set_option maxRecDepth 100000 in
private theorem writer_sites : OpPcsFast kernel.code writerOp writerSites = true := by
  decide +kernel

/-- The Tensor Memory writer instructions of the followed roles. -/
private def WriterSite : Machine.ThreadD → Prop
  | .wg0 d => ∃ j, d.site = .rescaleStore j
  | .mma d => (∃ j, d.site = .qCopy j) ∨ (∃ j, d.site = .qkMma j) ∨ (∃ j, d.site = .pvMma j)
  | _ => False

local macro "absent_writer" : tactic =>
  `(tactic| first
    | decide
    | (rename_i a; revert a; decide)
    | (rename_i a b; revert a b; decide)
    | (rename_i a b c; revert a b c; decide)
    | (rename_i a b c d; revert a b c d; decide))

private theorem writer_site {d : Machine.ThreadD}
    (hp : (Machine.code P L g).pc d ∈ writerSites) : WriterSite d := by
  cases d
  case prologue q =>
    change q.pc ∈ _ at hp
    change False
    cases q <;> revert hp <;> absent_writer
  case wg0 q =>
    change q.site.pc ∈ _ at hp
    change ∃ j, q.site = .rescaleStore j
    generalize h : q.site = s at hp ⊢
    clear h q
    cases s
    case rescaleStore j => exact ⟨j, rfl⟩
    all_goals exfalso; revert hp; absent_writer
  case mma q =>
    change q.site.pc ∈ _ at hp
    change (∃ j, q.site = .qCopy j) ∨ (∃ j, q.site = .qkMma j) ∨ (∃ j, q.site = .pvMma j)
    generalize h : q.site = s at hp ⊢
    clear h q
    cases s
    case qCopy j => exact .inl ⟨j, rfl⟩
    case qkMma j => exact .inr (.inl ⟨j, rfl⟩)
    case pvMma j => exact .inr (.inr ⟨j, rfl⟩)
    all_goals exfalso; revert hp; absent_writer
  case tma q =>
    change q.site.pc ∈ _ at hp
    change False
    generalize h : q.site = s at hp
    clear h q
    cases s <;> revert hp <;> absent_writer
  case index q =>
    change q.site.pc ∈ _ at hp
    change False
    generalize h : q.site = s at hp
    clear h q
    cases s <;> revert hp <;> absent_writer
  case wg2 q =>
    change q.site.pc ∈ _ at hp
    change False
    generalize h : q.site = s at hp
    clear h q
    cases s <;> revert hp <;> absent_writer
  case idle q =>
    change q.pc ∈ _ at hp
    change False
    cases q <;> revert hp <;> absent_writer
  case head =>
    change 1843 ∈ _ at hp
    exact (by decide : 1843 ∉ writerSites) hp
  case done =>
    change 3611 ∈ _ at hp
    exact (by decide : 3611 ∉ writerSites) hp

def WritesTensorMemory : Kind → Prop
  | .tc (.mma ..) | .tc (.cp ..) | .tc (.st ..) | .tc (.shift ..) => True
  | _ => False

private theorem writer_fires_op {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hf : Fires t.pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (hw : WritesTensorMemory e.kind) : writerOp ins.op = true := by
  have hout : (∃ d s a m, e.kind = .tc (.mma d s a m)) ∨
      (∃ s, e.kind = .tc (.cp s)) ∨ (∃ a v s, e.kind = .tc (.st a v s)) ∨
      ∃ s, e.kind = .tc (.shift s) := by
    cases hk : e.kind <;> simp only [hk, WritesTensorMemory] at hw
    case tc k =>
      cases k <;> simp_all
  rcases hout with ⟨d, s, a, m, hk⟩ | ⟨s, hk⟩ | ⟨a, v, s, hk⟩ | ⟨s, hk⟩
  · simp [writerOp, fires_tcMma_op hf hk]
  · simp [writerOp, fires_tcCp_op hf hk]
  · simp [writerOp, fires_tcSt_op hf hk]
  · simp [writerOp, fires_tcShift_op hf hk]

private theorem writer_event {d : Machine.ThreadD} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some d) e o) (hw : WritesTensorMemory e.kind) :
    ∃ t ins u, (Machine.code P L g).AtD d t ∧ WriterSite d ∧
      kernel.code[(Machine.code P L g).pc d]? = some ins ∧ o = some u ∧
      Fires ((Machine.code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e (some u) := by
  cases o with
  | none =>
    obtain ⟨_, _, hf⟩ := hf
    rcases fires_none_ends hf with ⟨_, hk⟩ | hk <;> rw [hk] at hw <;> exact hw.elim
  | some u =>
    obtain ⟨t, ⟨hat, _⟩, hf⟩ := hf
    change (Machine.code P L g).AtD d t at hat
    change Fires t.pc (match kernel.code[(Machine.code P L g).pc d]? with
      | some ins => eventTmpl Assumptions.all L g t ins.op
      | none => .ub .pcOutOfRange) e (some u) at hf
    cases hc : kernel.code[(Machine.code P L g).pc d]? with
    | none => rw [hc] at hf; exact absurd hf.2 (by simp)
    | some ins =>
      rw [hc] at hf
      have hs := writer_site (OpPcsFast.mem writer_sites hc (writer_fires_op hf hw))
      rw [hat.1] at hf
      exact ⟨t, ins, u, hat, hs, rfl, rfl, hf⟩

/-- The exact Tensor Memory write emitted by the real role state. -/
def WriterFields (L : Launch) (g : Nat) (d : Machine.ThreadD) (e : Event) : Prop :=
    (∃ s j, d = .wg0 s ∧ s.site = .rescaleStore j ∧
      e.kind = .tc (.st (64 * j.val) (Wg0.rescaleStoreValues s) .s32x32b)) ∨
    (∃ s j, d = .mma s ∧ s.site = .qCopy j ∧ e.kind = .tc (.cp (queryCopySpec L g j))) ∨
    (∃ s j, d = .mma s ∧ s.site = .qkMma j ∧
      e.kind = .tc (.mma tmemP (qkOperands L g s.i j) (qkAccum j) [0, 0, 0, 0])) ∨
    ∃ s j, d = .mma s ∧ s.site = .pvMma j ∧
      e.kind = .tc (.mma (pvDest j) (pvOperands L g s.i j) (pvAccum s.i j) [0, 0, 0, 0])

/-- Exact payloads of the only writer instructions in a followed thread. -/
theorem writer_fields {d : Machine.ThreadD} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hg : g < L.threads)
    (hf : (Machine.machine P L g).Fired (some d) e o)
    (hw : (∃ dst sp acc mask, e.kind = .tc (.mma dst sp acc mask)) ∨
      (∃ sp, e.kind = .tc (.cp sp)) ∨ (∃ dst words sh, e.kind = .tc (.st dst words sh)) ∨
      ∃ sp, e.kind = .tc (.shift sp)) :
    WriterFields L g d e := by
  have hw' : WritesTensorMemory e.kind := by
    rcases hw with ⟨_, _, _, _, hk⟩ | ⟨_, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, hk⟩ <;> rw [hk] <;> trivial
  obtain ⟨t, ins, u, hat, hs, hc, _, hfire⟩ := writer_event hf hw'
  cases d
  case wg0 d =>
    obtain ⟨j, hj⟩ := hs
    exact .inl ⟨d, j, rfl, hj, (Wg0.fires_rescaleStore hpre hj hat hc hfire).1⟩
  case mma d =>
    change (Wg1Mma.code P L g).AtD d t at hat
    change kernel.code[d.site.pc]? = some ins at hc
    change Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e (some u) at hfire
    rcases hs with ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, hj⟩
    · have hd : d = ⟨.qCopy j, d.i⟩ := by cases d; simp_all
      rw [hd] at hat
      rw [hj] at hc hfire
      exact .inr (.inl ⟨d, j, rfl, hj, (fires_qCopy hpre hg d.i j hat hc hfire).1⟩)
    · have hd : d = ⟨.qkMma j, d.i⟩ := by cases d; simp_all
      rw [hd] at hat
      rw [hj] at hc hfire
      exact .inr (.inr (.inl ⟨d, j, rfl, hj, (fires_qkMma hpre hg d.i j hat hc hfire).1⟩))
    · have hd : d = ⟨.pvMma j, d.i⟩ := by cases d; simp_all
      rw [hd] at hat
      rw [hj] at hc hfire
      exact .inr (.inr (.inr ⟨d, j, rfl, hj, (fires_pvMma hpre hg d.i j hat hc hfire).1⟩))
  all_goals exact hs.elim

/-- A followed FlashMLA thread never issues a tensor-memory shift. -/
theorem no_shift_issue {i : Nat} {s : TcShift.Spec}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hi : X.ShiftIssue (g, i) s) : False := by
  obtain ⟨tag, hg⟩ := hi
  have hlt := Frame.lt_of_get hX hg
  obtain ⟨_, _, _, hf⟩ := RingSourceSites.fired_from_trace hX (hs g hlt).machine ht hg (by simp)
  have hw := writer_fields hpre hlt hf (.inr (.inr (.inr ⟨s, rfl⟩)))
  rcases hw with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
  all_goals cases h

private theorem rescale_column {g : Nat} {d : Wg0.D} (j : Fin 4) {n : Nat}
    (hn : n < (Wg0.rescaleStoreValues d).length) :
    (tcDataCell L g .s32x32b (64 * j.val) n).column < 400 := by
  have hj := j.isLt
  have hbase : 64 * j.val < 2 ^ 16 := by omega
  rw [tcDataCell_s32x32b]
  simp only [tcDataCell32, Nat.mod_eq_of_lt hbase]
  simp only [Wg0.rescaleStoreValues, List.length_map, List.length_range] at hn
  omega

private theorem query_column (k : Fin 16) (cta lane index : Nat) :
    (TcCopy.cell (queryCopySpec L g k).shape (queryCopySpec L g k).address
      cta lane index).column < 400 := by
  have hk := k.isLt
  have hbase : 256 + 8 * k.val < 2 ^ 16 := by omega
  have hmod := Nat.mod_lt index (by decide : 0 < 32)
  change (256 + 8 * k.val) % 2 ^ 16 + index % 32 / 4 < 400
  rw [Nat.mod_eq_of_lt hbase]
  omega

private theorem pv_column (k : Fin 8) (block : Nat) {row col : Nat} {cell : TcMma.Cell}
    (hw : TcMma.writeCell (pvOperands L g block k) (pvDest k) [0, 0, 0, 0]
      row col = some cell) : cell.column < 400 := by
  have hr := TcMma.writeCell_resultCell hw
  have hdim : row < 64 ∧ col < 256 := by
    unfold TcMma.resultCell at hr
    dsimp only at hr
    split at hr
    · rename_i h
      exact ⟨h.2.2.1, h.2.2.2.1⟩
    · cases hr
  rw [pvResultCell L g block k ⟨row, hdim.1⟩ ⟨col, hdim.2⟩] at hr
  cases hr
  change pvDest k + col % 128 < 400
  unfold pvDest tmemO
  have hk := Nat.mod_lt k.val (by decide : 0 < 2)
  have hc := Nat.mod_lt col (by decide : 0 < 128)
  omega

variable {X : Execution}

/-- In a followed writer state, a write in the score columns can only be an actual QK issue.
Rescale writes the O columns, query copies write the Q columns, and PV writes O. -/
theorem score_write {i : Nat} {site : Machine.ThreadD} {cell : TcMma.Cell} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.code P L g).Sound)
    (hsite : Frame.stateAt (Machine.code P L) X g i = some (some site)) (hcol : 400 ≤ cell.column)
    (hw : TcMma.TmemWrite L X (g, i) cell) :
    ∃ d k, site = .mma d ∧ d.site = .qkMma k ∧
      X.MmaIssue (g, i) tmemP (qkOperands L g d.i k) (qkAccum k) [0, 0, 0, 0] := by
  have fields {e : Event} (he : X.get (g, i) = some e)
      (hk : (∃ dst sp acc mask, e.kind = .tc (.mma dst sp acc mask)) ∨
        (∃ sp, e.kind = .tc (.cp sp)) ∨ (∃ dst words sh, e.kind = .tc (.st dst words sh)) ∨
        ∃ sp, e.kind = .tc (.shift sp)) : WriterFields L g site e := by
    have hg := Frame.lt_of_get hX he
    obtain ⟨_, hf⟩ := ((hs.machine.produces (hX.thr g hg)).fired_at he hsite)
    exact writer_fields hpre hg hf hk
  rcases hw with hw | hw | hw | hw
  · obtain ⟨dst, sp, acc, rowMask, row, col, ⟨tag, he⟩, hcell⟩ := hw
    rcases fields he (.inl ⟨dst, sp, acc, rowMask, rfl⟩) with
      ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ | ⟨d, k, hd, hs, hk⟩ | ⟨d, k, _, _, hk⟩
    · cases hk
    · cases hk
    · exact ⟨d, k, hd, hs, ⟨tag, he.trans (congrArg some (congrArg (Event.mk tag) hk))⟩⟩
    · obtain ⟨rfl, rfl, _, rfl⟩ := TcKind.mma.inj (Kind.tc.inj hk)
      exact (Nat.not_lt_of_ge hcol (pv_column k d.i hcell)).elim
  · obtain ⟨dst, ws, shape, n, ⟨_, he⟩, hn, hcell⟩ := hw
    rcases fields he (.inr (.inr (.inl ⟨dst, ws, shape, rfl⟩))) with
      ⟨d, j, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩
    · obtain ⟨rfl, rfl, rfl⟩ := TcKind.st.inj (Kind.tc.inj hk)
      rw [hcell] at hcol
      exact (Nat.not_lt_of_ge hcol (rescale_column j hn)).elim
    · cases hk
    · cases hk
    · cases hk
  · obtain ⟨cp, cta, index, lane, ⟨_, he⟩, _, _, _, hcell⟩ := hw
    rcases fields he (.inr (.inl ⟨cp, rfl⟩)) with
      ⟨_, _, _, _, hk⟩ | ⟨_, j, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩
    · cases hk
    · have hcp := TcKind.cp.inj (Kind.tc.inj hk)
      subst cp
      rw [hcell] at hcol
      exact (Nat.not_lt_of_ge hcol (query_column j cta lane index)).elim
    · cases hk
    · cases hk
  · obtain ⟨s, ⟨_, he⟩, _⟩ := hw
    rcases fields he (.inr (.inr (.inr ⟨s, rfl⟩))) with
      ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ <;>
      cases hk

set_option maxRecDepth 100000 in
private theorem softmax_only_st : kernel.code.zipIdx.all (fun (ins, pc) =>
    !decide (softmaxWriteRegion pc) || !(tcMmaOp ins.op || tcCpOp ins.op || tcShiftOp ins.op)) =
    true := by decide +kernel

private theorem softmax_writer_is_store {ins : Instr} {t : TState} {e : Event}
    {o : Option TState}
    (hRegion : softmaxWriteRegion t.pc) (hc : kernel.code[t.pc]? = some ins)
    (hf : Fires t.pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (hw : WritesTensorMemory e.kind) :
    ∃ dst words shape, e.kind = .tc (.st dst words shape) := by
  have hAudit := List.all_eq_true.mp softmax_only_st (ins, t.pc)
    (List.mem_zipIdx_iff_getElem?.mpr hc)
  simp only [decide_eq_true hRegion, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hAudit
  cases hk : e.kind <;> simp only [hk, WritesTensorMemory] at hw
  case tc k =>
    cases k <;> try contradiction
    case st dst words shape => exact ⟨dst, words, shape, rfl⟩
    case mma => simp [fires_tcMma_op hf hk] at hAudit
    case cp => simp [fires_tcCp_op hf hk] at hAudit
    case shift => simp [fires_tcShift_op hf hk] at hAudit

/-- A dismissed Tensor Memory writer can only store a rescaled output slice. -/
theorem dismissed_writer_store {i : Nat} {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (he : X.get (g, i) = some e)
    (hDismiss : Frame.stateAt (Machine.code P L) X g i = some none) (hw : WritesTensorMemory e.kind)
    :
    ∃ tile : Fin 4, ∃ words,
      e.kind = .tc (.st (64 * tile.val) words .s32x32b) ∧ words.length = 64 := by
  obtain ⟨start, hLe, d, hSite, _, hAnchor⟩ := mask_anchor_after_dismissal hpre hX hs he hDismiss
  have hGet : ((X.tr g).drop start)[i - start]? = some e := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hLe]
    exact he
  have hMem := List.mem_of_getElem? hGet
  have hg := Frame.lt_of_get hX he
  obtain ⟨t, o, _, ht, hRun⟩ :=
    softmax_write_suffix hX hs hg hSite hAnchor (List.ne_nil_of_mem hMem)
  have hRegion := run_in_control_region softmax_write_region_closed
    (show softmaxWriteRegion t.pc by rw [ht]; decide) hRun e hMem
  obtain ⟨dst, words, shape, hk⟩ : ∃ dst words shape, e.kind = .tc (.st dst words shape) := by
    rcases get_source hX he with ⟨f, hf⟩ | ⟨state, ins, next, hp, hc, hf⟩
    · rw [hf] at hw
      exact hw.elim
    · exact softmax_writer_is_store (g := g) (t := state) (ins := ins)
        (by simpa only [hp] using hRegion)
        (by simpa only [hp] using hc) (by simpa only [hp] using hf) hw
  obtain ⟨tile, hp⟩ := actual_tmem_store_site hX he hk
  obtain ⟨rfl, rfl, hLength⟩ := tmem_store_from_mask tile ht hRun hMem hp hk
  exact ⟨tile, words, hk, hLength⟩

/-- A writer outside the output columns cannot have dismissed its numerical tracking. -/
theorem high_writer_followed {i : Nat} {cell : TcMma.Cell} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (hCol : 256 ≤ cell.column)
    (hWrite : TcMma.TmemWrite L X (g, i) cell) :
    Frame.stateAt (Machine.code P L) X g i ≠ some none := by
  intro hDismiss
  have address {e : Event} (he : X.get (g, i) = some e) (hw : WritesTensorMemory e.kind) :=
    dismissed_writer_store hpre hX hs he hDismiss hw
  rcases hWrite with h | h | h | h
  · obtain ⟨_, _, _, _, _, _, ⟨_, he⟩, _⟩ := h
    obtain ⟨_, _, hStore, _⟩ := address he trivial
    cases hStore
  · obtain ⟨dst, words, shape, n, ⟨_, he⟩, hn, hCell⟩ := h
    obtain ⟨tile, ws, hStore, hLength⟩ := address he trivial
    obtain ⟨rfl, rfl, rfl⟩ := TcKind.st.inj (Kind.tc.inj hStore)
    rw [hLength] at hn
    have ht := tile.isLt
    have hbase : 64 * tile.val < 2 ^ 16 := by omega
    rw [hCell, tcDataCell_s32x32b] at hCol
    simp only [tcDataCell32, Nat.mod_eq_of_lt hbase] at hCol
    omega
  · obtain ⟨_, _, _, _, ⟨_, he⟩, _, _, _, _⟩ := h
    obtain ⟨_, _, hStore, _⟩ := address he trivial
    cases hStore
  · obtain ⟨_, ⟨_, he⟩, _⟩ := h
    obtain ⟨_, _, hStore, _⟩ := address he trivial
    cases hStore

/-- Every actual score-column writer is the followed QK issue for its own block. -/
theorem actual_score_write {i : Nat} {cell : TcMma.Cell} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (hCol : 400 ≤ cell.column)
    (hWrite : TcMma.TmemWrite L X (g, i) cell) :
    ∃ d k, Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)) ∧
      d.site = .qkMma k ∧
      X.MmaIssue (g, i) tmemP (qkOperands L g d.i k) (qkAccum k) [0, 0, 0, 0] := by
  have follow {e : Event} (he : X.get (g, i) = some e) (hUb : ∀ f, e.kind ≠ .ub f) :
      g < L.threads ∧ ∃ site, Frame.stateAt (Machine.code P L) X g i = some (some site) := by
    have hg := Frame.lt_of_get hX he
    have hNot : Frame.stateAt (Machine.code P L) X g i ≠ some none :=
      high_writer_followed hpre hX hs (by omega) hWrite
    obtain ⟨d, _, hd, _⟩ :=
      RingSourceSites.fired_at_followed hX (hs g hg).machine hNot he hUb
    exact ⟨hg, d, hd⟩
  have hFollow : g < L.threads ∧
      ∃ site, Frame.stateAt (Machine.code P L) X g i = some (some site) := by
    rcases hWrite with h | h | h | h
    · obtain ⟨_, _, _, _, _, _, ⟨_, he⟩, _⟩ := h
      exact follow he (by simp)
    · obtain ⟨_, _, _, _, ⟨_, he⟩, _, _⟩ := h
      exact follow he (by simp)
    · obtain ⟨_, _, _, _, ⟨_, he⟩, _, _, _, _⟩ := h
      exact follow he (by simp)
    · obtain ⟨_, ⟨_, he⟩, _⟩ := h
      exact follow he (by simp)
  obtain ⟨hg, site, hSite⟩ := hFollow
  obtain ⟨d, k, rfl, hd, hIssue⟩ := score_write hpre hX (hs g hg) hSite hCol hWrite
  exact ⟨d, k, hSite, hd, hIssue⟩

/-- A value-bearing write in the score columns is the result of that actual QK issue. -/
theorem score_writer {i : Nat} {site : Machine.ThreadD} {cell : TcMma.Cell} {value : Value}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.code P L g).Sound)
    (hsite : Frame.stateAt (Machine.code P L) X g i = some (some site)) (hcol : 400 ≤ cell.column)
    (hw : TcMma.Wrote L Assumptions.all X (g, i) cell value) :
    ∃ d k, site = .mma d ∧ d.site = .qkMma k ∧
      X.MmaIssue (g, i) tmemP (qkOperands L g d.i k) (qkAccum k) [0, 0, 0, 0] ∧
      TcMma.Result L Assumptions.all X (g, i) cell value := by
  obtain ⟨d, k, hd, hq, hm⟩ := score_write hpre hX hs hsite hcol hw.tmemWrite
  refine ⟨d, k, hd, hq, hm, ?_⟩
  obtain ⟨_, he⟩ := hm
  rcases hw with hr | hw | hw | hw
  · exact hr
  · obtain ⟨_, _, _, _, ⟨_, he'⟩, _, _⟩ := hw
    cases congrArg Event.kind (Option.some.inj (he.symm.trans he'))
  · obtain ⟨_, _, _, _, _, _, _, ⟨_, he'⟩, _, _, _, _, _, _, _⟩ := hw
    cases congrArg Event.kind (Option.some.inj (he.symm.trans he'))
  · obtain ⟨_, _, ⟨⟨_, ⟨_, he'⟩, _⟩, _, _, _⟩, _⟩ := hw
    cases congrArg Event.kind (Option.some.inj (he.symm.trans he'))

/-- The selected bf16 MMA arithmetic returns an FP32 accumulator. -/
theorem bf16_eval_f32 {desc : TcMma.Descriptor} {acc : Bool} {a b : List (Option Byte)}
    {old : Option Value}
    {row col : Nat} {v : Value}
    (hk : desc.kind = .f16 .bf16 .f32)
    (he : TcMma.eval Assumptions.all desc acc a b old row col = .ok v) :
    ∃ score : ℝ, v = .float .f32 score := by
  have hprofile : Assumptions.idealArith.mmaRule desc acc a b old row col =
      some (Assumption.execIdealMma desc acc a b old row col) := by
    simp [Assumptions.idealArith, Assumption.idealReal, hk]
  simp only [TcMma.eval, hk, Assumptions.all, List.findSome?, hprofile, Option.getD_some] at he
  simp only [Assumption.execIdealMma, hk, pure, Except.pure, bind, Except.bind] at he
  split at he
  · split at he
    · cases he
    · split at he
      · cases he
      · cases he
        exact ⟨_, rfl⟩
  · cases he

private theorem qk_result_f32 {i block : Nat} {k : Fin 16} {cell : TcMma.Cell} {v : Value}
    (hiq : X.MmaIssue (g, i) tmemP (qkOperands L g block k) (qkAccum k) [0, 0, 0, 0])
    (hr : TcMma.Result L Assumptions.all X (g, i) cell v) :
    ∃ score : ℝ, v = .float .f32 score := by
  have descriptor {d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {m : List Nat}
      (he : X.MmaIssue (g, i) d s acc m) : s.descriptor = qkDescriptor := by
    obtain ⟨_, ha⟩ := he
    obtain ⟨_, hb⟩ := hiq
    have hf := congrArg Event.kind (Option.some.inj (ha.symm.trans hb))
    rw [(TcKind.mma.inj (Kind.tc.inj hf)).2.1]
    rfl
  cases hr with
  | overwrite hi _ _ ha => exact bf16_eval_f32 rfl (descriptor hi ▸ ha)
  | accumulate hi _ _ _ _ ha => exact bf16_eval_f32 rfl (descriptor hi ▸ ha)
  | accumulateStored hi _ _ _ _ ha => exact bf16_eval_f32 rfl (descriptor hi ▸ ha)

/-- Any actual value-bearing writer in the score columns with a known role state
leaves a full FP32 QK result. Its numerical value may still require operand attribution. -/
theorem score_writer_f32 {i : Nat} {site : Machine.ThreadD} {cell : TcMma.Cell} {value : Value}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.code P L g).Sound)
    (hsite : Frame.stateAt (Machine.code P L) X g i = some (some site)) (hcol : 400 ≤ cell.column)
    (hw : TcMma.Wrote L Assumptions.all X (g, i) cell value) :
    ∃ score : ℝ, value = .float .f32 score ∧
      TcMma.Result L Assumptions.all X (g, i) cell (.float .f32 score) := by
  obtain ⟨_, _, _, _, hi, hr⟩ := score_writer hpre hX hs hsite hcol hw
  obtain ⟨score, rfl⟩ := qk_result_f32 hi hr
  exact ⟨score, rfl, hr⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0ScoreSources
