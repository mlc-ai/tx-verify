-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Resource
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.InitCtaPublication
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaAccessWindow
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryCellWriters
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TcCollectiveOperands
import Lemmas.Tcgen05.TcMmaAReadUnique
import Lemmas.Tcgen05.TcMmaResultLayout
import Lemmas.Tcgen05.TcDataCell

@[expose] public section

/-! # A role event lies after its CTA's full tensor-memory allocation -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow Tmem.Pair MmaDataTrace Wg1Mma

/-- The publishing prologue gate places the actual 512-column allocation before each role. -/
theorem tmem_allocated_at_role {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {g i col : Nat} {e : Event} {d : Machine.ThreadD} (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hrole : ∀ s, d ≠ .prologue s) (hcol : col < 512) :
    ∃ r ∈ X.tmemHistory (ctaOf L g), Covers L X r (ctaOf L g) (g, i) col := by
  let cta := ctaOf L g
  let leader := cta * L.block
  have hb : 0 < L.block := by rw [hpre.block]; decide
  have hLeader : leader < L.threads :=
    NamedBar.cta_thread_lt (NamedBar.cta_lt (Frame.lt_of_get hX he)) hb
  have hCta : ctaOf L leader = cta := Nat.mul_div_cancel cta hb
  have hSound : ∀ g < L.threads, (Machine.machine P L g).Sound := fun a ha => (hs a ha).machine
  obtain ⟨j, tag, hbar, hjs⟩ :=
    InitCtaPublication.role_gate_member hpre hX hSound ht he hd hrole hLeader hCta
  obtain ⟨r, ev, hr, hHome, hAlloc, hThread, hGet, hEarlier⟩ :=
    alloc_record_at_gate hpre hX hs ht hbar hjs
  refine ⟨r, hr, Covers.own ⟨512, 0, hAlloc, hHome.symm, Nat.zero_le _, ?_, ?_⟩⟩
  · simpa using hcol
  · have hEv : r.own.event L 0 = (leader, (r.own.event L 0).2) := Prod.ext hThread rfl
    rw [hEv] at hGet ⊢
    exact InitCtaPublication.on_prologue_before_role hpre hX hSound ht hGet he
      hEarlier hd hrole hCta

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hX hs ht

private theorem result_access_site {g i dst row col : Nat} {spec : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {cell : TcMma.Cell} (hi : X.MmaIssue (g, i) dst spec acc mask)
    (hc : TcMma.resultCell spec dst row col = some cell) :
    cell.cta = ctaOf L g ∧ cell.column < 512 ∧
      ∃ q, Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)) := by
  rcases (MmaAccessWindow.mma_spec hpre hX hs ht hi).2 with
    ⟨block, issue, _, rfl, _, hst⟩ | ⟨block, issue, _, rfl, _, hst⟩
  all_goals
    exact ⟨(TcMma.resultCell_cta hc).elim id id, (TcMma.resultCell_bounds hc).2, _, hst⟩

private theorem a_access_site {g i : Nat} {cell : TcMma.Cell} (hi : X.MmaACell (g, i) cell) :
    cell.cta = ctaOf L g ∧ cell.column < 512 ∧
      ∃ q, Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)) := by
  obtain ⟨d, s, acc, mask, index, b, hi, hc⟩ := hi
  rcases (MmaAccessWindow.mma_spec hpre hX hs ht hi).2 with
    ⟨block, issue, _, rfl, _, hst⟩ | ⟨block, issue, _, rfl, _, _⟩
  · have hBound := TcMma.aCell_index_lt hc
    norm_num [qkOperands, qkDescriptor, TcMma.Operand.bytes, TcMma.Operand.rows,
      TcMma.Kind.k, TcMma.Kind.width] at hBound
    obtain ⟨row, k, byte, rfl⟩ := MmaAccessWindow.operand_slot (rows := 128) hBound
    have hMatch := (Prod.mk.inj (Option.some.inj
      (hc.symm.trans (qkQueryByte L g block issue row k byte)))).1
    have hCol : qkACol issue + k.val / 2 < 512 := by
      unfold qkACol tmemQ
      have := issue.isLt
      have := k.isLt
      omega
    exact ⟨hMatch ▸ rfl, hMatch ▸ hCol, _, hst⟩
  · simp [TcMma.aCell, pvOperands] at hc

/-- Every represented load, store, MMA cell and query copy is covered by its CTA's allocation. -/
theorem tmem_access_owner_and_allocation {e : EvId} {cell : TcMma.Cell} (ha : Access L X e cell) :
    cell.cta = ctaOf L e.1 ∧
      ∃ cta r, r ∈ X.tmemHistory cta ∧ Covers L X r cell.cta e cell.column := by
  obtain ⟨g, i⟩ := e
  have finish {ev : Event} {d : Machine.ThreadD} (he : X.get (g, i) = some ev)
      (hd : Frame.stateAt (Machine.code P L) X g i = some (some d))
      (hrole : ∀ s, d ≠ .prologue s) (hc : cell.cta = ctaOf L g) (hcol : cell.column < 512) :
      cell.cta = ctaOf L g ∧
        ∃ cta r, r ∈ X.tmemHistory cta ∧ Covers L X r cell.cta (g, i) cell.column := by
    obtain ⟨r, hr, hCover⟩ := tmem_allocated_at_role hpre hX hs ht he hd hrole hcol
    exact ⟨hc, _, r, hr, hc.symm ▸ hCover⟩
  rcases ha with ha | ⟨j, ha⟩ | ha | ha | ⟨s, hi, _⟩ | ⟨s, hi, _⟩
  · rcases ha with ⟨_, _, _, _, _, _, hi, hc⟩ | ⟨_, _, _, _, _, hi, hc⟩ | ha
    · obtain ⟨hCta, hCol, q, hst⟩ :=
        result_access_site hpre hX hs ht hi (TcMma.writeCell_resultCell hc)
      exact finish hi.choose_spec hst (by simp) hCta hCol
    · obtain ⟨hCta, hCol, q, hst⟩ := result_access_site hpre hX hs ht hi hc
      exact finish hi.choose_spec hst (by simp) hCta hCol
    · obtain ⟨hCta, hCol, q, hst⟩ := a_access_site hpre hX hs ht ha
      obtain ⟨_, _, _, _, _, _, hi, _⟩ := ha
      exact finish hi.choose_spec hst (by simp) hCta hCol
  · obtain ⟨address, words, sh, hi, hj, rfl⟩ := ha
    have hg := Frame.lt_of_get hX hi.choose_spec
    obtain ⟨d, hst, rfl, hsite⟩ :=
      TcCollectiveSites.load_fields hpre hX (hs g hg).machine ht hi
    refine finish hi.choose_spec hst (by simp) rfl ?_
    rw [tcDataCell_s32x32b]
    change address % 2 ^ 16 + j < 512
    rcases hsite with ⟨arm, part, _, rfl, hlen⟩ | ⟨tile, _, rfl, hlen⟩
    · rw [hlen] at hj
      unfold Wg0.scoreLoadColumn
      have := part.isLt
      omega
    · rw [hlen] at hj
      have := tile.isLt
      omega
  · obtain ⟨address, words, sh, slot, ⟨tag, he⟩, hn, rfl⟩ := ha
    have hg := Frame.lt_of_get hX he
    obtain ⟨_, _, hst, hf⟩ :=
      RingSourceSites.fired_from_trace hX (hs g hg).machine ht he (by simp)
    have hw := Wg0ScoreSources.writer_fields hpre hg hf (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))
    rcases hw with ⟨q, tile, rfl, _, hk⟩ | ⟨_, _, _, _, hk⟩ |
      ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩
    · obtain ⟨rfl, rfl, rfl⟩ := TcKind.st.inj (Kind.tc.inj hk)
      refine finish he hst (by simp) rfl ?_
      rw [tcDataCell_s32x32b]
      change (64 * tile.val) % 2 ^ 16 + _ < 512
      simp only [Wg0.rescaleStoreValues, List.length_map, List.length_range] at hn
      have := tile.isLt
      omega
    all_goals cases hk
  · have hCopy := ha
    obtain ⟨spec, _, _, _, hi, _, _, _, _⟩ := ha
    obtain ⟨q, k, hst, _, rfl⟩ := MmaAccessWindow.copy_state hpre hX hs ht hi
    obtain ⟨hCta, _, hCol⟩ := QueryCellWriters.copy_column hCopy hi
    refine finish hi.choose_spec hst (by simp) hCta (by unfold qkACol tmemQ at hCol; omega)
  · exact (Wg0ScoreSources.no_shift_issue hpre hX hs ht hi).elim
  · exact (Wg0ScoreSources.no_shift_issue hpre hX hs ht hi).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
