-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryOperandLifetime
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRingObjects
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreReadbackOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QkIssueHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmResults
import Lemmas.Tcgen05.TcMmaResultLayout
import Lemmas.Tcgen05.TcProgramOrder

@[expose] public section

/-! # Adjacent QK instructions read the previous partial sum -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QkAccumulatorSource

open PTX PTX.Flow Wg1Mma MmaDataTrace

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A writer of a score cell is an actual QK issue of the unique issuer for that CTA. -/
theorem issue_of_write {g other i : Nat} {cell : TcMma.Cell}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hissuer : GemmRing.MmaIssuer P L X (ctaOf L g) g)
    (hcta : cell.cta = ctaOf L g) (hcol : 400 ≤ cell.column)
    (hw : TcMma.TmemWrite L X (other, i) cell) :
    other = g ∧ ∃ (block : Nat) (k : Fin 16),
      X.MmaIssue (other, i) tmemP (qkOperands L other block k) (qkAccum k) [0, 0, 0, 0] := by
  obtain ⟨d, k, hstate, hsite, hm⟩ := Wg0ScoreSources.actual_score_write hpre hX hs hcol hw
  obtain ⟨tag, hget⟩ := hm
  have howner : cell.cta = ctaOf L other := by
    rcases hw with ⟨_, s, _, _, _, _, ⟨_, hh⟩, hcell⟩ | ⟨_, _, _, _, ⟨_, hh⟩, _, _⟩ |
      ⟨_, _, _, _, ⟨_, hh⟩, _, _, _, _⟩ | ⟨_, ⟨_, hh⟩, _⟩
    all_goals have hk := congrArg Event.kind (Option.some.inj (hh.symm.trans hget))
    · obtain ⟨_, rfl, _, _⟩ := TcKind.mma.inj (Kind.tc.inj hk)
      exact (TcMma.resultCell_cta (TcMma.writeCell_resultCell hcell)).elim id id
    all_goals cases hk
  exact ⟨hissuer other i d (howner.symm.trans hcta) hstate (by rw [hsite]; simp),
    d.i, k, tag, hget⟩

/-- Each cell of an accumulating QK instruction reads the immediately preceding QK result. -/
theorem previous_of_adjacent {g i block k : Nat} (hk : k + 1 < 16)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hprev : X.MmaIssue (g, i) tmemP (qkOperands L g block ⟨k, by omega⟩)
      (qkAccum ⟨k, by omega⟩) [0, 0, 0, 0])
    (hnext : X.MmaIssue (g, i + 1) tmemP (qkOperands L g block ⟨k + 1, hk⟩)
      (qkAccum ⟨k + 1, hk⟩) [0, 0, 0, 0])
    (hstate : Frame.stateAt (Machine.code P L) X g (i + 1) =
      some (some (.mma ⟨.qkMma ⟨k + 1, hk⟩, block⟩)))
    (head : Fin 64) (col : Fin 128) :
    TcMma.ReadSource L X .acc (g, i) (g, i + 1)
      ⟨ctaOf L g, head.val + 64 * (col.val / 64), tmemP + col.val % 64⟩ := by
  let cell : TcMma.Cell := ⟨ctaOf L g, head.val + 64 * (col.val / 64), tmemP + col.val % 64⟩
  obtain ⟨issuer, his⟩ := GemmRing.exists_issuer (cta := ctaOf L g) hpre hX
    (fun t h => (hs t h).machine)
  have hi := his g (i + 1) _ rfl hstate (by simp)
  subst issuer
  have horder := ScoreReadback.earlier_qk_write hX hprev hnext (Nat.lt_succ_self i)
  have hwrite : X.MmaCell (g, i) cell :=
    ⟨_, _, _, _, head.val, col.val, hprev, Result.qkWriteCell L g block ⟨k, by omega⟩ head col⟩
  have hlive : TcMma.SourceLive L X (g, i) (g, i + 1) cell :=
    QueryOperandLifetime.sourceLive_of_qk hpre hX hs hnext hstate rfl rfl
  refine ⟨fun h => by have hi := congrArg Prod.snd h; omega, .inl hwrite, horder, ?_, hlive⟩
  rintro ⟨other, j⟩ hother
  have hcol : 400 ≤ cell.column := by change 400 ≤ 400 + col.val % 64; omega
  obtain ⟨rfl, b, p, hm⟩ := issue_of_write hpre hX hs his rfl hcol hother
  rcases Nat.lt_trichotomy j i with hlt | rfl | hlt
  · exact .inr (.inl (ScoreReadback.earlier_qk_write hX hm hprev hlt))
  · exact .inl rfl
  · refine .inr (.inr ?_)
    rcases Nat.eq_or_lt_of_le (show i + 1 ≤ j by omega) with rfl | hlt
    · exact .inl rfl
    · obtain hd | hp := TcMma.Before.of_mma_po hnext hm
        (Frame.lt_of_get hX hnext.choose_spec) rfl hlt ⟨rfl, rfl, rfl, rfl, rfl⟩
      · exact .inr (.inl hd)
      · exact .inr (.inr hp)

/-- An actual QK commit identifies all sixteen issues and their accumulator read sources. -/
theorem of_commit {g commit : Nat} {d : Wg1Mma.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, commit) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g commit = some (some (.mma d)))
    (hsite : d.site = .qkCommit) :
    ∃ visit : Fin 16 → Nat,
      (∀ k, visit k + (16 - k.val) = commit ∧
        Frame.stateAt (Machine.code P L) X g (visit k) =
          some (some (.mma ⟨.qkMma k, d.i⟩)) ∧
        X.MmaIssue (g, visit k) tmemP (qkOperands L g d.i k) (qkAccum k) [0, 0, 0, 0]) ∧
      ∀ (i : Nat) (hi : i + 1 < 16) (head : Fin 64) (col : Fin 128),
        TcMma.ReadSource L X .acc (g, visit ⟨i, by omega⟩) (g, visit ⟨i + 1, hi⟩)
          ⟨ctaOf L g, head.val + 64 * (col.val / 64), tmemP + col.val % 64⟩ := by
  choose visit hvisit using fun k => QkIssueHistory.qk_issue_of_commit hpre hX hs he hd hsite k
  refine ⟨visit, hvisit, ?_⟩
  intro i hi head col
  have hprev := hvisit ⟨i, by omega⟩
  have hnext := hvisit ⟨i + 1, hi⟩
  have hadj : visit ⟨i + 1, hi⟩ = visit ⟨i, by omega⟩ + 1 := by
    have hp := hprev.1
    have hn := hnext.1
    change visit ⟨i, by omega⟩ + (16 - i) = commit at hp
    change visit ⟨i + 1, hi⟩ + (16 - (i + 1)) = commit at hn
    omega
  rw [hadj] at hnext ⊢
  exact previous_of_adjacent hi hpre hX hs hprev.2.2 hnext.2.2 hnext.2.1 head col

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QkAccumulatorSource
