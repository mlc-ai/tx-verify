-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreSources
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryTmaSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1MmaLeader
import Lemmas.Tcgen05.TcMmaResultLayout
import Lemmas.Tcgen05.TcDataCell

@[expose] public section

/-! # The actual query copy is the only writer of a QK A cell -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryCellWriters

open PTX PTX.Flow MmaDataTrace Wg1Mma

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private theorem rescale_column_lt {d : Wg0.D} (j : Fin 4) {n : Nat}
    (hn : n < (Wg0.rescaleStoreValues d).length) :
    (tcDataCell L g .s32x32b (64 * j.val) n).column < 256 := by
  have hj := j.isLt
  have hbase : 64 * j.val < 2 ^ 16 := by omega
  rw [tcDataCell_s32x32b]
  change (64 * j.val) % 2 ^ 16 + n < 256
  rw [Nat.mod_eq_of_lt hbase]
  simp only [Wg0.rescaleStoreValues, List.length_map, List.length_range] at hn
  omega

private theorem result_dimensions {s : TcMma.OperandSpec} {base row col : Nat} {cell : TcMma.Cell}
    (h : TcMma.resultCell s base row col = some cell) :
    row < s.descriptor.m ∧ col < s.descriptor.n := by
  unfold TcMma.resultCell at h
  dsimp only at h
  split at h
  · rename_i hguard
    exact ⟨hguard.2.2.1, hguard.2.2.2.1⟩
  · cases h

private theorem pv_column_lt (j : Fin 8) (block : Nat) {row col : Nat} {cell : TcMma.Cell}
    (hw : TcMma.writeCell (pvOperands L g block j) (pvDest j) [0, 0, 0, 0]
      row col = some cell) : cell.column < 256 := by
  have hr := TcMma.writeCell_resultCell hw
  obtain ⟨hrow, hcol⟩ := result_dimensions hr
  change row < 64 at hrow
  change col < 256 at hcol
  rw [pvResultCell L g block j ⟨row, hrow⟩ ⟨col, hcol⟩] at hr
  cases hr
  change pvDest j + col % 128 < 256
  unfold pvDest tmemO
  have hj := Nat.mod_lt j.val (by decide : 0 < 2)
  have hc := Nat.mod_lt col (by decide : 0 < 128)
  omega

private theorem qk_column_ge (j : Fin 16) (block : Nat) {row col : Nat} {cell : TcMma.Cell}
    (hw : TcMma.writeCell (qkOperands L g block j) tmemP [0, 0, 0, 0]
      row col = some cell) : 400 ≤ cell.column := by
  have hr := TcMma.writeCell_resultCell hw
  obtain ⟨hrow, hcol⟩ := result_dimensions hr
  change row < 64 at hrow
  change col < 128 at hcol
  rw [qkResultCell L g block j ⟨row, hrow⟩ ⟨col, hcol⟩] at hr
  cases hr
  change 400 ≤ 400 + col % 64
  omega

/-- A query copy writes its own CTA and the eight columns of its chunk. -/
theorem copy_column {g i : Nat} {chunk : Fin 16} {cell : TcMma.Cell}
    (hw : TcMma.CpCell X (g, i) cell)
    (hi : X.CpIssue (g, i) (queryCopySpec L g chunk)) :
    cell.cta = ctaOf L g ∧ qkACol chunk ≤ cell.column ∧ cell.column < qkACol chunk + 8 := by
  obtain ⟨s, owner, idx, lane, ⟨_, he⟩, hm, _, _, hcell⟩ := hw
  obtain ⟨_, hcp⟩ := hi
  have hs := TcKind.cp.inj (Kind.tc.inj (congrArg Event.kind (Option.some.inj (he.symm.trans hcp))))
  subst s
  have ho : owner = ctaOf L g := by simpa [queryCopySpec] using hm
  subst owner
  rw [hcell]
  have hchunk := chunk.isLt
  have hbase : 256 + 8 * chunk.val < 2 ^ 16 := by omega
  have hiCol := Nat.mod_lt idx (by decide : 0 < 32)
  change ctaOf L g = ctaOf L g ∧
    256 + 8 * chunk.val ≤ (256 + 8 * chunk.val) % 2 ^ 16 + idx % 32 / 4 ∧
    (256 + 8 * chunk.val) % 2 ^ 16 + idx % 32 / 4 < 256 + 8 * chunk.val + 8
  rw [Nat.mod_eq_of_lt hbase]
  exact ⟨rfl, by omega, by omega⟩

/-- Every write in the query operand region belongs to the copy covering that column. -/
theorem copy_writer_of_column {a i : Nat} {cell : TcMma.Cell}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hcol : 256 ≤ cell.column ∧ cell.column < 400)
    (hw : TcMma.TmemWrite L X (a, i) cell) :
    ∃ (q : Wg1Mma.D) (e : Event) (chunk : Fin 16), X.get (a, i) = some e ∧ ctaOf L a = cell.cta ∧
      Frame.stateAt (Machine.code P L) X a i = some (some (.mma q)) ∧
      q.site = .qCopy chunk ∧ qkACol chunk ≤ cell.column ∧
        cell.column < qkACol chunk + 8 := by
  have get_fields {e : Event} (he : X.get (a, i) = some e) (hn : ∀ f, e.kind ≠ .ub f)
      (hk : (∃ dst sp acc mask, e.kind = .tc (.mma dst sp acc mask)) ∨
        (∃ sp, e.kind = .tc (.cp sp)) ∨ (∃ dst words sh, e.kind = .tc (.st dst words sh)) ∨
        ∃ sp, e.kind = .tc (.shift sp)) :
      ∃ d, Frame.stateAt (Machine.code P L) X a i = some (some d) ∧
        Wg0ScoreSources.WriterFields L a d e := by
    have ha := Frame.lt_of_get hX he
    obtain ⟨d, _, hst, hf⟩ := RingSourceSites.fired_at_followed hX (hs a ha).machine
      (Wg0ScoreSources.high_writer_followed hpre hX hs hcol.1 hw) he hn
    exact ⟨d, hst, Wg0ScoreSources.writer_fields hpre ha hf hk⟩
  rcases hw with hw | hw | hw | hw
  · obtain ⟨base, spec, accum, mask, ri, ci, ⟨_, hg⟩, hcell⟩ := hw
    obtain ⟨s, _, hfields⟩ := get_fields hg (by simp) (.inl ⟨_, _, _, _, rfl⟩)
    rcases hfields with ⟨_, _, _, _, hr⟩ | ⟨_, _, _, _, hr⟩ |
      ⟨d, j, _, _, hr⟩ | ⟨d, j, _, _, hr⟩
    · cases hr
    · cases hr
    · obtain ⟨rfl, rfl, _, rfl⟩ := TcKind.mma.inj (Kind.tc.inj hr)
      exact (Nat.not_le_of_lt hcol.2 (qk_column_ge j d.i hcell)).elim
    · obtain ⟨rfl, rfl, _, rfl⟩ := TcKind.mma.inj (Kind.tc.inj hr)
      exact (Nat.not_lt_of_ge hcol.1 (pv_column_lt j d.i hcell)).elim
  · obtain ⟨dest, vals, shape, n, ⟨_, hg⟩, hn, hc⟩ := hw
    obtain ⟨s, _, hfields⟩ := get_fields hg (by simp) (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))
    rcases hfields with ⟨d, j, _, _, hr⟩ | ⟨_, _, _, _, hr⟩ |
      ⟨_, _, _, _, hr⟩ | ⟨_, _, _, _, hr⟩
    · obtain ⟨rfl, rfl, rfl⟩ := TcKind.st.inj (Kind.tc.inj hr)
      change cell = _ at hc
      rw [hc] at hcol
      exact (Nat.not_lt_of_ge hcol.1 (rescale_column_lt j hn)).elim
    · cases hr
    · cases hr
    · cases hr
  · have hcover := hw
    obtain ⟨spec, _, _, _, ⟨tag, hg⟩, _, _, _, _⟩ := hw
    obtain ⟨s, hstate, hfields⟩ := get_fields hg (by simp) (.inr (.inl ⟨_, rfl⟩))
    rcases hfields with ⟨_, _, _, _, hr⟩ | ⟨d, j, rfl, hsite, hr⟩ |
      ⟨_, _, _, _, hr⟩ | ⟨_, _, _, _, hr⟩
    · cases hr
    · have hget := hg.trans (congrArg some (congrArg (Event.mk tag) hr))
      obtain ⟨hcta, hLow, hHigh⟩ := copy_column hcover (⟨tag, hget⟩ : X.CpIssue (a, i) _)
      exact ⟨d, _, j, hg, hcta.symm, hstate, hsite, hLow, hHigh⟩
    · cases hr
    · cases hr
  · obtain ⟨spec, ⟨_, hg⟩, _⟩ := hw
    obtain ⟨_, _, hfields⟩ := get_fields hg (by simp) (.inr (.inr (.inr ⟨spec, rfl⟩)))
    rcases hfields with ⟨_, _, _, _, hr⟩ | ⟨_, _, _, _, hr⟩ |
      ⟨_, _, _, _, hr⟩ | ⟨_, _, _, _, hr⟩ <;> cases hr

/-- Every writer of a query A cell is the matching actual copy, on its elected lane. -/
theorem unique_writer {i : Nat} {q : Wg1Mma.D} {e : Event} {issue : Fin 16}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hq : Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)))
    (hsite : q.site = .qCopy issue) (row : Fin 128) (k : Fin 16)
    {other : EvId}
    (hw : TcMma.TmemWrite L X other ⟨ctaOf L g, row.val, qkACol issue + k.val / 2⟩) :
    other = (g, i) := by
  obtain ⟨h, j⟩ := other
  have hcol : 256 ≤ qkACol issue + k.val / 2 ∧ qkACol issue + k.val / 2 < 400 := by
    have := k.isLt
    have := issue.isLt
    unfold qkACol tmemQ
    omega
  obtain ⟨r, f, chunk, hf, hcta, hr, hrSite, hlo, hhi⟩ :=
    copy_writer_of_column hpre hX hs hcol hw
  have hchunk : chunk = issue := by
    apply Fin.ext
    change 256 + 8 * chunk.val ≤ 256 + 8 * issue.val + k.val / 2 at hlo
    change 256 + 8 * issue.val + k.val / 2 < 256 + 8 * chunk.val + 8 at hhi
    have := k.isLt
    omega
  subst chunk
  obtain ⟨_, hLeader⟩ := Wg1MmaLeader.cta_issuer (cta := ctaOf L g) hpre hX
    (fun a ha => (hs a ha).machine)
  have hg := hLeader g i q rfl hq (by rw [hsite]; simp)
  have hh := hLeader h j r hcta hr (by rw [hrSite]; simp)
  have hsame := hh.trans hg.symm
  rw [hsame] at hf hr ⊢
  have hj := QueryTmaSites.copy_site_unique hf he hr hq hrSite hsite
  rw [hj]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryCellWriters
