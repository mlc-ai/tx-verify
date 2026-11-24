-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.BoundWg0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.BoundWg2
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.BoundIndex
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.BoundMma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.BoundTma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
public import Lemmas.Kernel.Bound

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound
open PTX PTX.Proof PTX.Flow
open Machine (ThreadD)

noncomputable section

/-- Maximum padded block count of a launched batch row. -/
def maxBlocks (P : Params) : Nat := (Finset.range P.b).sup (Result.blocks P)

/-- The maximum initial role budget, plus the shared hand-off events. -/
def threadLimit (P : Params) : Nat := 720 * maxBlocks P + 755

def rank (P : Params) (L : Launch) (g : Nat) : ThreadD → Nat
  | .prologue s => 720 * maxBlocks P + 721 + prologueRank s
  | .head => 720 * maxBlocks P + 721
  | .wg0 d => wg0Rank P L g d
  | .mma d => mmaRank P L g d
  | .tma d => tmaRank P L g d
  | .index d => indexRank P L g d
  | .idle s => idleRank s
  | .wg2 d => wg2Rank P L g d
  | .done => 0

private theorem row_le_limit {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) : Result.blocks P (ctaidY L g) ≤ maxBlocks P := by
  have hb := Wg1Mma.eOf_lt_b (g := g) hpre
  rw [Wg1Mma.eOf, Wg1Mma.batchOf_eq_ctaidY] at hb
  exact Finset.le_sup (f := Result.blocks P) (Finset.mem_range.mpr hb)

private theorem roleStart_rank {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) (w : Fin 3) :
    rank P L g (Machine.roleStart P L g w) ≤ 720 * maxBlocks P + 721 := by
  have hb := row_le_limit (g := g) hpre
  fin_cases w
  · have hi := wg0Rank_init P L g
    unfold Wg0.blocksOf Wg0.eOf at hi
    change wg0Rank P L g (Wg0.init P L g) ≤ _
    omega
  · rfl
  · have hi := wg2Rank_init P L g
    unfold Wg2.eOf at hi
    change wg2Rank P L g (Wg2.init P L g) ≤ _
    omega

private theorem headStart_rank {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : ThreadD}
    (hpre : Pre P L mem0) (hn : Machine.headStart P L g = some d) :
    rank P L g d ≤ 720 * maxBlocks P + 720 := by
  have hb := row_le_limit (g := g) hpre
  unfold Machine.headStart at hn
  split_ifs at hn <;> cases hn
  · have hi := mmaRank_elect P L g
    rw [Wg1Mma.eOf, Wg1Mma.batchOf_eq_ctaidY] at hi
    change mmaRank P L g ⟨.elect, 0⟩ ≤ _
    omega
  · have hi := tmaRank_init P L g
    unfold Wg1Tma.eOf at hi
    change tmaRank P L g (Wg1Tma.init P L g) ≤ _
    omega
  · have hi := indexRank_init P L g
    unfold Wg1Index.eOf at hi
    change indexRank P L g (Wg1Index.init P L g) ≤ _
    omega
  · have hi := idleRank_le (Thread.startSite L g)
    change idleRank (Thread.startSite L g) ≤ _
    omega

private theorem tma_bar_id {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : Wg1Tma.D} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hd : d.site = .barrier)
    (hf : (Machine.machine P L g).Fired (some (.tma d)) e o)
    {id : Nat} {count : Option Nat} {mode : BarMode} (he : e.kind = .bar id count mode) :
    id = 12 := by
  obtain ⟨t, ⟨hat, _⟩, hf⟩ := hf
  change Wg1Tma.AtD P L g d t at hat
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  have hcode : kernel.code[d.site.pc]? = some ⟨none, .barSyncN (.reg 790) (.reg 791) false⟩ := by
    rw [hd]
    exact Flow.code_bar_12
  rw [hcode] at hf
  obtain ⟨h790, h791⟩ := Wg1Tma.barrier_regs P L g hd hat
  change Fires t.pc (eventTmpl Assumptions.all L g t (.barSyncN (.reg 790) (.reg 791) false))
    e o at hf
  rw [Wg1Tma.fires_bar_12 h790 h791 hpre.block] at hf
  exact (Kind.bar.inj (he.symm.trans (congrArg Event.kind hf.1))).1

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
theorem rank_step {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d d' : ThreadD} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hi : (Machine.code P L g).inv d)
    (hf : (Machine.machine P L g).Fired (some d) e o)
    (hn : (Machine.code P L g).next d e = some (some d')) :
    rank P L g d' + (if e.counts then 1 else 0) ≤ rank P L g d := by
  have hcount := eventCount_le e
  change Machine.next P L g d e = some (some d') at hn
  cases d <;> simp only [Machine.next] at hn
  case prologue s =>
    split at hn
    · rename_i s' h
      cases hn
      have hs := prologueRank_step h
      simp only [rank]
      omega
    · cases s with
      | handoff w =>
        dsimp only at hn
        split_ifs at hn <;> cases hn
        have hs := roleStart_rank (g := g) hpre w
        change rank P L g (Machine.roleStart P L g w) + (if e.counts then 1 else 0) ≤
          720 * maxBlocks P + 721 + 1
        omega
      | _ => cases hn
    · cases hn
  case head =>
    split at hn
    · split at hn
      · split at hn
        · rename_i d h
          cases hn
          have hs := headStart_rank (g := g) hpre h
          change rank P L g _ + (if e.counts then 1 else 0) ≤ 720 * maxBlocks P + 721
          omega
        · cases hn
      · cases hn
    · cases hn
  case wg0 d =>
    change Wg0.Inv P L g d at hi
    split at hn
    · rename_i d' h
      cases hn
      exact wg0Rank_step hi h
    · split at hn
      · cases hn
        rename_i hd
        have hs := hi.subLt
        rcases hd with he | he <;>
          simp [he, Wg0.Site.elems] at hs <;>
          simp [rank, wg0Rank, wg0Block, wg0Ordinal, he, hs] <;> omega
      · cases hn
    · cases hn
  case mma d =>
    split at hn
    · rename_i d' h
      cases hn
      exact mmaRank_step h
    · split_ifs at hn <;> cases hn
      rename_i hd
      have hs := idleRank_le (Thread.startSite L g)
      simp only [rank, mmaRank, hd, mmaOrdinal]
      omega
    · split_ifs at hn
      cases hn
      rename_i hd
      simp [rank, mmaRank, hd]
      omega
  case tma d =>
    change Wg1Tma.Inv P L g d at hi
    split at hn
    · rename_i d' h
      cases hn
      exact tmaRank_step hi (fun hd _ _ _ he => tma_bar_id hpre hd hf he) h
    · split_ifs at hn <;> cases hn
      · rename_i hd
        simp [rank, tmaRank, hd]
        omega
      · rename_i hd
        have hs := idleRank_le (Thread.startSite L g)
        simp [rank, tmaRank, hd.1, tmaBlock, tmaOrdinal]
        omega
    · split_ifs at hn
      cases hn
      rename_i hd
      simp [rank, tmaRank, hd]
      omega
  case index d =>
    change Wg1Index.Inv P L g d at hi
    split at hn
    · rename_i d' h
      cases hn
      exact indexRank_step hi h
    · split_ifs at hn <;> cases hn
      rename_i hd
      simp [rank, indexRank, hd]
      omega
    · cases hn
  case idle s =>
    split at hn
    · rename_i s' h
      cases hn
      exact idleRank_step h
    · cases hn
    · split_ifs at hn
      cases hn
      rename_i hd
      simp [rank, idleRank, hd]
      omega
  case wg2 d =>
    change Wg2.Inv P L g d at hi
    split at hn
    · rename_i d' h
      cases hn
      exact wg2Rank_step hi h
    · split_ifs at hn <;> cases hn
      rename_i hd
      simp [rank, wg2Rank, hd]
      omega
    · cases hn
  case done => cases hn

/-- The counted events of an actual tracked thread prefix fit the launch's uniform budget. -/
theorem counted_le {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hsound : ∀ g < L.threads, (Machine.code P L g).Sound)
    (htracked : Frame.Tracked (Machine.code P L) X) (hg : g < L.threads) :
    (X.tr g).countP Event.counts ≤ threadLimit P + 2 := by
  have h := Frame.count_le hsound hX hg htracked (rank P L g) (fun _ => false) 0 fun
      k d d' e he hd hi hn => by
    have hget : X.get (g, k) = some e := he
    obtain ⟨o, hf⟩ := RingEvents.fired_of_trace hX (hsound g hg).machine hget hd
    simpa using rank_step hpre hi hf hn
  simpa [Machine.code, rank, prologueRank, threadLimit, Nat.add_assoc] using h

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound
