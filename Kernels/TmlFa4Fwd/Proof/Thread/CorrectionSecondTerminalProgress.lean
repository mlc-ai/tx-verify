-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionOutputSignalProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningCorrectionStatistics
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalReadProgress
import Kernels.TmlFa4Fwd.Proof.Progress.SyncGuarded

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue

noncomputable def FirstOutputPublished.baseFrame {p : Params} {l : Launch} {X : Execution}
    {g batch : Nat} (c : FirstOutputPublished p l X g batch) : List (Nat × Value) :=
  firstChunkFrame p l g batch (laneOf l g) c.staging.sum c.staging.maximum

/-- The second terminal rendezvous has been recorded after the first stage publication. -/
structure SecondTerminalWaitReached (p : Params) (l : Launch) (X : Execution)
    (g batch : Nat) where
  first : FirstOutputPublished p l X g batch
  state : TState
  waited : Thread.CorrectionWaits X (g,first.published.cursor.pos) .terminal 1
  ready : At state (statsPc 1 .sum) first.baseFrame
  recorded : Run kernel Assumptions.all l g {}
    ((X.tr g).take (first.published.cursor.pos+1)) (some state)
  remaining : Run kernel Assumptions.all l g state
    ((X.tr g).drop (first.published.cursor.pos+1)) first.published.cursor.ending

theorem FirstOutputPublished.secondWaitOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch : Nat} (hg : g < l.threads) (c : FirstOutputPublished p l X g batch) :
    Nonempty (SecondTerminalWaitReached p l X g batch) := by
  let d := c.published.cursor
  have h := d.checkpoint
  have ha : At d.ready (statsBarrierPc 1 false) c.baseFrame :=
    ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,((holds_append _ _ _).1 h.2.2.2.2).2⟩
  let cur : OpeningTripCursor l X g (statsBarrierPc 1 false) c.baseFrame :=
    ⟨d.pos,d.before,d.ready,d.ending,d.positive,d.bounded,d.released,ha,d.recorded,
      d.remaining,d.localSteps⟩
  have hSelf : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  have hBar : (statsBarrierReg 1,b32 (statsBarrierId l g 1)) ∈ c.baseFrame := by
    simp [FirstOutputPublished.baseFrame,firstChunkFrame,firstTerminalReciprocalFrame,
      correctionBeforeRescale,tileSetupFrame,correctionTileGeometryFacts,statsBarrierReg,hSelf]
  have hCode := statsBarrierCode (1 : Fin 2) false
  have hModel : out kernel Assumptions.all l g cur.ready = out kernel [] l g cur.ready := by
    apply Assumptions.out_all_eq_nil _ _ _ (ha.1.symm ▸ hCode) rfl
    all_goals rw [ha.1]; decide
  obtain ⟨he,hReturned,hRest⟩ := statsSyncOfCursor hMax hg cur
    (statsSyncOut hp 1 ha hCode hModel (holds_mem ha.2.2.2.2 hBar))
  rw [ha.1] at he
  exact ⟨⟨c,next cur.ready,Thread.terminalWaitObservation 1 he,ha.next,hReturned,hRest⟩⟩

/-- Both terminal row statistics are recorded and the second reciprocal setup is next. -/
structure SecondTerminalWordsReady (p : Params) (l : Launch) (X : Execution)
    (g batch : Nat) where
  firstSum : ℝ
  firstMaximum : Option ℝ
  firstValid : Softmax.DenominatorValid firstSum firstMaximum
  sum : ℝ
  maximum : Option ℝ
  valid : Softmax.DenominatorValid sum maximum
  cursor : OpeningTripCursor l X g (statsPc 1 .maximum+1)
    ((statsReg 1 .maximum,Softmax.scoreValue maximum)::(statsReg 1 .sum,fl sum)::
      firstChunkFrame p l g batch (laneOf l g) firstSum firstMaximum)

theorem SecondTerminalWaitReached.readOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    {g batch : Nat} (hg : g < l.threads) (c : SecondTerminalWaitReached p l X g batch)
    (hRelease : c.first.published.cursor.pos+1 = (X.tr g).length →
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
        Y.MemWrites = X.MemWrites ∧ Step.Released l Y g)
    (hMatched : ∀ Y, Maximal l kernel Assumptions.all m Y → Y.tr = X.tr →
      Y.MemWrites = X.MemWrites → c.first.published.cursor.pos+1 < (Y.tr g).length →
      ∃ pub sum max,
        Thread.Correction.TerminalPublishedWords l Y g 1 pub (fl sum) (Softmax.scoreValue max) ∧
        Thread.Correction.TerminalGeneration l Y g 1 (pub-2) c.first.published.cursor.pos ∧
        Softmax.DenominatorValid sum max) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Y.MemWrites = X.MemWrites ∧
      Nonempty (SecondTerminalWordsReady p l Y g batch) := by
  let j := c.first.published.cursor.pos
  let F := c.first.baseFrame
  have hBound : j+1 ≤ (X.tr g).length := by
    obtain ⟨_,he,_⟩ := c.waited
    exact len_of_get he
  have hReady : ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
      Y.MemWrites = X.MemWrites ∧ (j+1 = (Y.tr g).length → Step.Released l Y g) := by
    by_cases hLast : j+1 = (X.tr g).length
    · obtain ⟨Y,hY,hTrace,hWrites,hRel⟩ := hRelease hLast
      exact ⟨Y,hY,hTrace,hWrites,fun _ => hRel⟩
    · exact ⟨X,hMax,rfl,rfl,fun h => (hLast h).elim⟩
  obtain ⟨Y,hY,hTrace,hWrites,hRel⟩ := hReady
  let cur : OpeningTripCursor l Y g (statsPc 1 .sum) F :=
    ⟨j+1,c.state,c.state,c.first.published.cursor.ending,Nat.succ_pos _,
      by rwa [hTrace],hRel,c.ready,
      by simpa only [hTrace] using c.recorded,by simpa only [hTrace] using c.remaining,.refl⟩
  have hProtected : Epilogue.DrainCuQProtected p Y := by
    unfold Epilogue.DrainCuQProtected at hCuQ ⊢
    rwa [hWrites]
  have hGuard := Progress.syncGuarded hp hY.1 hProtected
  have hSelf : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  have hBase : (1627,b32 (l.sharedBase+4*rowOf l g)) ∈ F := by
    simp [F,FirstOutputPublished.baseFrame,firstChunkFrame,firstTerminalReciprocalFrame,
      correctionBeforeRescale,tileSetupFrame,correctionTileGeometryFacts,hSelf]
  have hPass := terminalStatsSumRecorded hp hY hGuard hg 1 cur hBase
  obtain ⟨pub,sum,max,hWords,hGeneration,hValid⟩ := hMatched Y hY hTrace hWrites hPass
  have hWait : Thread.CorrectionWaits Y (g,j) .terminal 1 := by
    obtain ⟨event,he,hAction⟩ := c.waited
    exact ⟨event,by simpa only [Execution.get,hTrace] using he,hAction⟩
  have hFresh : ∀ pair ∈ F, pair.1 ≠ statsReg 1 .sum ∧ pair.1 ≠ statsReg 1 .maximum := by
    have hf : ∀ r ∈ F.map Prod.fst, r ≠ statsReg 1 .sum ∧ r ≠ statsReg 1 .maximum :=
      of_decide_eq_true rfl
    intro pair hm
    exact hf _ (List.mem_map_of_mem hm)
  have hBytes : (Softmax.scoreValue max).bytes = 4 := by cases max <;> rfl
  have hScalar : rebuild 3 ((Softmax.scoreValue max).toBytes.map some) =
      .ok (Softmax.scoreValue max) := by
    apply PTX.Proof.rebuild_scalar (by rw [hBytes]; decide)
    cases max <;> rfl
  obtain ⟨d,_,_,_⟩ := terminalStatsWordsOfMaximal hp hY hGuard hg hWait hWords rfl hBytes
    hGeneration cur rfl hBase hFresh
    (PTX.Proof.rebuild_scalar (by change 0 < 4; decide) rfl) hScalar
  exact ⟨Y,hY,hTrace,hWrites,⟨⟨c.first.staging.sum,c.first.staging.maximum,
    c.first.staging.valid,sum,max,hValid,d⟩⟩⟩

end PTX.Kernels.TmlFa4Fwd.Correction
