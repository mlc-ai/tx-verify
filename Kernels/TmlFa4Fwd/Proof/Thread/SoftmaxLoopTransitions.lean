-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxPlainVisit
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedSoftmaxRetire
import Kernels.TmlFa4Fwd.Proof.Thread.OpeningLoopRegisters
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalSingleVisit
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Numeric Prologue Thread Correction

/-- The registers a lane carries into its terminal statistics (pc 7605). -/
def terminalEntryFacts (l : Launch) (warp : Fin 8) (visit : Nat) (maximum : Option ℝ)
    (sum : ℝ) : List (Nat × Value) :=
  [(7257,fl sum),(7256,scoreValue maximum),(5127,b32 (3+warp.val)),(7258,b32 (visit%2)),
    (1062,b32 warp.val),(2535,b32 l.sharedBase)]

/-- A lane at the entry of its terminal statistics after `visit` visits. -/
structure SoftmaxTerminalAt (p : Params) (l : Launch) (X : Execution) (g : Nat)
    (warp : Fin 8) (visit : Nat) (maximum : Option ℝ) (sum : ℝ) where
  valid : DenominatorValid sum maximum
  cursor : OpeningTripCursor l X g 7605 (terminalEntryFacts l warp visit maximum sum)
  notices : ((X.tr g).take cursor.pos).countP Scores.publishesStats = visit

private theorem phaseBitT (v : Nat) : (decide (v%2 = 1)).toNat = v%2 := by
  rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]

/-- The biased exit enters the plain loop, or the terminal statistics when there are no
plain visits. -/
theorem BiasedLoopAt.exitOfLoop {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g : Nat} {warp : Fin 8} (hw : warp.val = warpIndex l g)
    {visit block floor counter bars elects : Nat} {maximum : Option ℝ} {sum : ℝ}
    (c : BiasedLoopAt p l X g warp 6654 visit block floor counter bars elects maximum sum) :
    (c.split = 0 ∧ Nonempty (SoftmaxTerminalAt p l X g warp visit maximum sum)) ∨
    (c.split ≠ 0 ∧ ∃ head : PlainLoopAt p l X g warp 6661 visit (2^32-c.split) (11*visit) bars
      elects maximum sum, head.cursor.pos = c.cursor.pos) := by
  let phase := decide (visit%2 = 1)
  have hPhase : phase.toNat = visit%2 := phaseBitT visit
  have regs := c.cursor.checkpoint.2.2.2.2
  have hr (r : Nat) {v : Value}
      (h : (r,v) ∈ biasedHeadFacts p l g warp visit block maximum sum floor counter) :
      c.cursor.ready.regs r = some v := holds_mem regs h
  have geo := c.geometry
  have hODR : Holds c.cursor.ready.regs (openingDenominatorRegisters p l g) :=
    ((holds_append ..).mp regs.2.2.2.2).1
  have hAt : At c.cursor.ready 6654
      (loopChoiceFacts c.blocks c.split c.pastTile maximum sum phase phase) := by
    refine c.cursor.checkpoint.mono ⟨geo.2.2.2.1,geo.2.2.2.2.1,?_,?_,geo.1,geo.2.1,geo.2.2.1,
      c.maxWord,hr 7257 (by simp [biasedHeadFacts]),trivial⟩
    · rw [hPhase]; exact hr 7253 (by simp [biasedHeadFacts])
    · rw [hPhase]; exact hr 7258 (by simp [biasedHeadFacts])
  obtain ⟨u,hLocal,hu⟩ := plainLoopEntryLocal hp c.blocks c.split c.pastTile maximum sum phase
    phase c.bounds.1 c.bounds.2 hAt
  have hAbi := openingLoopRegistersLocal (.inr c.cursor.checkpoint.1) hODR hLocal
  have abi (r : Nat) {v : Value} (h : (r,v) ∈ openingDenominatorRegisters p l g) :
      u.regs r = some v := holds_mem hAbi h
  have hwv : (b32 (warpIndex l g)) = b32 warp.val := by rw [hw]
  by_cases hZero : c.split = 0
  · rw [ite_eq_left hZero] at hu
    left
    refine ⟨hZero,⟨⟨c.valid,⟨c.cursor.pos,c.cursor.before,u,c.cursor.ending,c.cursor.positive,
      c.cursor.bounded,c.cursor.released,hu.mono ?_,c.cursor.recorded,c.cursor.remaining,
      c.cursor.localSteps.trans hLocal⟩,c.counts.2.2.2.1⟩⟩⟩
    have f := hu.2.2.2.2
    refine ⟨holds_mem f (by simp [loopChoiceFacts,firstLoopStable]),
      holds_mem f (by simp [loopChoiceFacts,firstLoopStable]),
      abi 5127 (by simp [openingDenominatorRegisters,hw]),?_,
      (abi 1062 (by simp [openingDenominatorRegisters])).trans (congrArg some hwv),
      abi 2535 (by simp [openingDenominatorRegisters]),trivial⟩
    rw [← hPhase]; exact holds_mem f (by simp [loopChoiceFacts])
  · rw [ite_eq_right hZero] at hu
    right
    have f := hu.2.2.2.2
    refine ⟨hZero,⟨c.valid,⟨c.cursor.pos,c.cursor.before,u,c.cursor.ending,c.cursor.positive,
      c.cursor.bounded,c.cursor.released,hu.mono ?_,c.cursor.recorded,c.cursor.remaining,
      c.cursor.localSteps.trans hLocal⟩,c.scores,c.counts⟩,rfl⟩
    refine ⟨(abi 1062 (by simp [openingDenominatorRegisters])).trans (congrArg some hwv),
      abi 2535 (by simp [openingDenominatorRegisters]),?_,
      abi 5127 (by simp [openingDenominatorRegisters,hw]),
      abi 1230 (by simp [openingDenominatorRegisters]),
      holds_mem f (by simp [plainLoopFacts]),holds_mem f (by simp [plainLoopFacts]),
      holds_mem f (by simp [plainLoopFacts]),holds_mem f (by simp [plainLoopFacts]),
      holds_mem f (by simp [plainLoopFacts,loopChoiceFacts,firstLoopStable]),
      holds_mem f (by simp [plainLoopFacts,loopChoiceFacts,firstLoopStable]),?_,trivial⟩
    · rw [← hPhase]; exact holds_mem f (by simp [plainLoopFacts,loopChoiceFacts])
    · rw [← hPhase]; exact holds_mem f (by simp [plainLoopFacts,loopChoiceFacts])

/-- The plain exit is the terminal statistics entry. -/
def PlainLoopAt.terminal {p : Params} {l : Launch} {X : Execution} {g : Nat} {warp : Fin 8}
    {visit counter tc bars elects : Nat} {maximum : Option ℝ} {sum : ℝ}
    (c : PlainLoopAt p l X g warp 7605 visit counter tc bars elects maximum sum) :
    SoftmaxTerminalAt p l X g warp visit maximum sum := by
  have regs := c.cursor.checkpoint.2.2.2.2
  have hr (r : Nat) {v : Value}
      (h : (r,v) ∈ plainHeadFacts p l warp visit counter maximum sum) :
      c.cursor.ready.regs r = some v := holds_mem regs h
  exact ⟨c.valid,⟨c.cursor.pos,c.cursor.before,c.cursor.ready,c.cursor.ending,c.cursor.positive,
    c.cursor.bounded,c.cursor.released,c.cursor.checkpoint.mono
      ⟨hr 7257 (by simp [plainHeadFacts,plainHeadKept]),
        hr 7256 (by simp [plainHeadFacts,plainHeadKept]),
        hr 5127 (by simp [plainHeadFacts,plainHeadKept]),
        hr 7258 (by simp [plainHeadFacts,plainHeadKept]),
        hr 1062 (by simp [plainHeadFacts]),hr 2535 (by simp [plainHeadFacts]),trivial⟩,
    c.cursor.recorded,c.cursor.remaining,c.cursor.localSteps⟩,c.counts.2.2.2.1⟩

/-- With the scheduler cursor of the same lane, the terminal entry after all `trips` visits
is the terminal producer row. -/
theorem SoftmaxTerminalAt.producerRow {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) {g trips : Nat}
    (hg : g < l.threads)
    {warp : Fin 8} (hw : warp.val = warpIndex l g) {maximum : Option ℝ} {sum : ℝ}
    (c : SoftmaxTerminalAt p l X g warp trips maximum sum)
    (source : OpeningTripCursor l X g 3212 (RowDrainRole.softmax.frame p l g)) :
    Nonempty (TerminalProducerRow p l X g warp trips) := by
  have regs := c.cursor.checkpoint.2.2.2.2
  have hGeom := geometryAtTerminalOfRecordedSource hp source c.cursor
  have hFacts : Holds c.cursor.ready.regs
      (terminalRowFrame p l g warp (trips%2) (fl sum) (scoreValue maximum)) := by
    refine (holds_append ..).mpr ⟨⟨regs.1,regs.2.1,regs.2.2.1,trivial⟩,?_⟩
    exact ⟨regs.2.2.2.1,regs.2.2.2.2.1,regs.2.2.2.2.2.1,hGeom⟩
  let cur : OpeningTripCursor l X g 7605
      (terminalRowFrame p l g warp (trips%2) (fl sum) (scoreValue maximum)) :=
    ⟨c.cursor.pos,c.cursor.before,c.cursor.ready,c.cursor.ending,c.cursor.positive,
      c.cursor.bounded,c.cursor.released,c.cursor.checkpoint.mono hFacts,c.cursor.recorded,
      c.cursor.remaining,c.cursor.localSteps⟩
  have bytes : (scoreValue maximum).bytes = 4 := by cases maximum <;> rfl
  obtain ⟨⟨_,hs⟩,⟨_,hm⟩,_⟩ := terminalPublicationCursorOfRow hp hMax hg warp hw rfl bytes cur
  have hw8 : warpIndex l g < 8 := hw ▸ warp.isLt
  refine ⟨⟨sum,maximum,c.valid,cur,?_⟩⟩
  have hOrd := Scores.notificationOrdinal hp hMax.1 (g := g) (j := cur.pos) hw8
  rw [Scores.beforeNotices,Scores.barrierOrdinal] at hOrd
  change ((X.tr g).take (cur.pos+1+1)).countP (Execution.isBarId (3+warpIndex l g)) = trips
  rw [countP_take_succ_false hm rfl,countP_take_succ_false hs rfl,← hOrd]
  exact c.notices

end PTX.Kernels.TmlFa4Fwd.Softmax
