-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionLseStatistics
public import Kernels.TmlFa4Fwd.Proof.CorrectionStatsHandoff
public import Kernels.TmlFa4Fwd.Proof.CorrectionLseValues
import Kernels.TmlFa4Fwd.Proof.NamedBarrierParticipants
import Lemmas.Protocol.NamedBarArrive
import Lemmas.Flow.MemTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue AsyncCopy
open PTX.Kernels.TmlFa4Fwd.Correction

noncomputable section

private theorem pairedTerminalCta {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage : Fin 2) : terminalStatsProducer l g stage / l.block = g / l.block := by
  have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
  have hStage := stage.isLt
  unfold terminalStatsProducer
  rw [hp.block]
  omega

private theorem pairedTerminalId (l : Launch) (g : Nat) (stage : Fin 2) :
    3 + (terminalStatsWarp l g stage).val = statsBarrierId l g stage := by
  have hRow : rowOf l g / 32 = warpIndex l g % 4 := by unfold rowOf warpIndex; omega
  dsimp only [terminalStatsWarp, statsBarrierId]
  omega

/-- The selected producer and consumer arrivals occupy the same statistics generation. -/
def TerminalGeneration (l : Launch) (X : Execution) (g : Nat) (stage : Fin 2)
    (producerPos wait : Nat) : Prop :=
  ∃ key,
    CtaBarArrivalK l X (terminalStatsProducer l g stage, producerPos + 2) key ∧
    CtaBarK l X (g, wait) key

/-- Each byte that shares a terminal word is either the selected producer's write, ordered
before it, or ordered after the consumer's read. -/
def TerminalWordOrder (l : Launch) (X : Execution) (g : Nat) (stage : Fin 2)
    (producerPos wait : Nat) : Prop :=
  ∀ (word : Fin 2) k, k < 4 → ∀ w a bytes, X.MemWrites w a bytes →
    let loc := (statsLoc l g stage (finalStatsKind word)).at k
    let writer := Ref.thread (terminalStatsProducer l g stage, producerPos + word.val)
    let reader := Ref.thread (g, wait + 1 + word.val)
    a.Covers loc → w = writer ∨ modelCausality l X loc w writer ∨ modelCausality l X loc reader w

/-- The actual terminal stores and rendezvous identify each word seen by the correction read. -/
theorem terminalStatWordReadOfEvents {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} {stage : Fin 2} {producerPos wait : Nat}
    (hTerminal : CorrectionWaits X (g,wait) .terminal stage)
    {sumValue maxValue : Value} (hSum : sumValue.bytes = 4) (hMax : maxValue.bytes = 4)
    (sStore : X.get (terminalStatsProducer l g stage, producerPos) =
      some ⟨7614, .wr (Softmax.statsAcc l (terminalStatsProducer l g stage)
        (terminalStatsWarp l g stage) 2) sumValue.toBytes⟩)
    (mStore : X.get (terminalStatsProducer l g stage, producerPos + 1) =
      some ⟨7615, .wr (Softmax.statsAcc l (terminalStatsProducer l g stage)
        (terminalStatsWarp l g stage) 3) maxValue.toBytes⟩)
    (hBar : X.get (terminalStatsProducer l g stage, producerPos + 2) =
      some ⟨7616, .bar (3 + (terminalStatsWarp l g stage).val) (some 64) .arrive⟩)
    (hGeneration : TerminalGeneration l X g stage producerPos wait)
    (hOrder : TerminalWordOrder l X g stage producerPos wait) (word : Fin 2)
    {bytes : List (Option Byte)}
    (hRead : X.Reads (g,wait+1+word.val)
      {loc := statsLoc l g stage (finalStatsKind word),size := 4} bytes) :
    bytes =
      (if word = 0 then sumValue else maxValue).toBytes.map some := by
  let producerId := terminalStatsProducer l g stage
  let warp := terminalStatsWarp l g stage
  let id := statsBarrierId l g stage
  obtain ⟨_, ⟨e, hGet, hKind, _, _⟩, _⟩ := correctionWaits hp hX hTerminal
  have hId : 3 + warp.val = id := pairedTerminalId l g stage
  have hCta : SameCta l producerId g :=
    ⟨event_thread_lt hX hBar, event_thread_lt hX (e := (g, wait)) hGet,
      pairedTerminalCta hp g stage⟩
  rw [hId] at hBar
  obtain ⟨key, hAKey, hSKey⟩ := hGeneration
  have hSync : ∃ e, X.get (g, wait) = some e ∧ e.kind = .bar id (some 64) .sync :=
    ⟨e, hGet, hKind⟩
  have hArrival : ∃ e, X.get (producerId, producerPos + 2) = some e ∧
      e.kind = .bar id (some 64) .arrive := ⟨_, hBar, rfl⟩
  have hSources := hId ▸ statsBarrierSources hp hX warp
  have hShape := hId ▸ statsBarrierShape hp warp
  have hA := hSources.arrival_kind_key hX hShape hArrival hAKey
  have hS := hSources.arrival_kind_key hX hShape hSync hSKey.arrival
  have hOrd : ((X.tr producerId).take (producerPos + 2)).countP (Execution.isBarId id) =
      ((X.tr g).take wait).countP (Execution.isBarId id) := by
    change key = id + 16 * ((X.tr producerId).take (producerPos + 2)).countP
      (Execution.isBarId id) at hA
    change key = id + 16 * ((X.tr g).take wait).countP (Execution.isBarId id) at hS
    omega
  let readId : EvId := (g, wait + 1 + word.val)
  let rAcc : Acc := {loc := statsLoc l g stage (finalStatsKind word), size := 4}
  let v := if word = 0 then sumValue else maxValue
  let writerId : EvId := (producerId, producerPos + word.val)
  let wAcc := Softmax.statsAcc l producerId warp (finalStatsWriteSite word)
  have hLen : readId.2 < (X.tr g).length := by
    obtain ⟨_, he⟩  := hRead
    exact (List.getElem?_eq_some_iff.mp he).1
  have hWritten : X.Writes writerId wAcc v.toBytes := by
    fin_cases word
    · exact ⟨_, sStore⟩
    · exact ⟨_, mStore⟩
  have hPrior : baseCausality l X writerId readId := by
    have hw := word.isLt
    apply hSources.arrive_sync_kind_baseCausality hX hShape hCta hArrival hSync hOrd
    · omega
    · omega
    · exact hLen
  have hWidth : v.toBytes.length = 4 := by
    dsimp only [v]
    split <;> simp [Value.toBytes, hSum, hMax]
  have hR : X.MemReads (.thread readId) rAcc bytes  := .inl hRead
  have hW : X.MemWrites (.thread writerId) wAcc v.toBytes := .inl hWritten
  exact read_of_last_write hX hR hW (terminalStatsLocation hp g stage word)
    rfl hWidth (fun _ _ => .inl hPrior) (hOrder word)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {store : EvId} {stage : Fin 2}
    {first wait producerPos batch tile head blocks : Nat} {s producer : TState}
    {producerEnd : Option TState} {sum maximum : List (Option Byte)} {refs : Nat → Option ℝ}
    {sums : Nat → ℝ} {maxValue : ℝ} (hRead : TerminalLseReads l X store stage wait sum maximum)
    (hWindow : LseWindowInputs l X store stage first s sum maximum)
    (hProducer : TerminalSoftmaxStatistics p l store.1 batch tile head stage producer blocks refs
      sums maxValue)
    (hRun : Run kernel Assumptions.all l (terminalStatsProducer l store.1 stage) producer
      ((X.tr (terminalStatsProducer l store.1 stage)).drop producerPos) producerEnd)
    (hMore : producerPos + 2 < (X.tr (terminalStatsProducer l store.1 stage)).length)
    (hGeneration : TerminalGeneration l X store.1 stage producerPos wait)
    (hOrder : TerminalWordOrder l X store.1 stage producerPos wait)
include hp hX hRead hWindow hProducer hRun hMore hGeneration hOrder

end
end PTX.Kernels.TmlFa4Fwd.Thread.Correction
