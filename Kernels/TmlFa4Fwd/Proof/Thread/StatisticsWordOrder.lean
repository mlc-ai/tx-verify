-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingGeometry
public import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsAllocationExclusion
public import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsStoreGeometry
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionLseTerminalStores
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalOccurrence
public import Kernels.TmlFa4Fwd.Proof.CorrectionStatsHandoff
import Lemmas.Order.Order

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Proof PTX.Flow Prologue
open PTX.Kernels.TmlFa4Fwd.Correction

noncomputable section

private theorem sameStatisticsLane {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g writer : Nat} (stage word : Fin 2) (site : Fin 4) (warp : Fin 8)
    (hWarp : warp.val = warpIndex l writer) {k : Nat} (hk : k < 4)
    (hCovers : (Softmax.statsAcc l writer warp site).Covers
      ((statsLoc l g stage (finalStatsKind word)).at k)) :
    writer = terminalStatsProducer l g stage ∧ (site = 3 ↔ word = 1) := by
  obtain ⟨_, hCta, hBeg, hEnd⟩ := hCovers
  change g / l.block = writer / l.block at hCta
  have hLane : 32 * warp.val + laneOf l writer = writer % l.block := by
    rw [hWarp]
    unfold warpIndex laneOf
    omega
  have hW : 32 * warp.val + laneOf l writer < 256 := by
    have h := warp.isLt
    have hl : laneOf l writer < 32 := Nat.mod_lt _ (by decide)
    omega
  rw [hLane] at hW
  have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
  have hStage := stage.isLt
  have hWordOffset : (Softmax.statsStore site).offset = if site = 3 then 1392 else 368 := by
    fin_cases site <;> rfl
  change l.sharedBase + 4 * (32 * warp.val + laneOf l writer) + (Softmax.statsStore site).offset ≤
    l.sharedBase + 4 * rowOf l g + statsOff stage (finalStatsKind word) + k at hBeg
  change l.sharedBase + 4 * rowOf l g + statsOff stage (finalStatsKind word) + k <
    l.sharedBase + 4 * (32 * warp.val + laneOf l writer) +
      (Softmax.statsStore site).offset + 4 at hEnd
  have hTarget : statsOff stage (finalStatsKind word) =
      (if word = 1 then 1392 else 368) + 512 * stage.val := by
    fin_cases word <;> rfl
  rw [hLane, hWordOffset, hTarget] at hBeg hEnd
  have hSplit : writer % l.block = rowOf l g + 128 * stage.val ∧ (site = 3 ↔ word = 1) := by
    by_cases hWord : word = 1 <;> by_cases hSite : site = 3 <;>
      simp [hSite, hWord] at hBeg hEnd ⊢ <;> omega
  refine ⟨?_, hSplit.2⟩
  unfold terminalStatsProducer
  rw [hp.block] at *
  omega

private theorem terminalWordStore {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g publication : Nat} {stage : Fin 2} (word : Fin 2)
    (hFinal : Scores.Publishes X (terminalStatsProducer l g stage, publication) .final) :
    ∃ bytes, X.get (terminalStatsProducer l g stage, publication - 2 + word.val) =
      some ⟨(Softmax.statsStore (finalStatsWriteSite word)).pc,
        .wr {loc := statsLoc l g stage (finalStatsKind word), size := 4} bytes⟩ := by
  obtain ⟨first, hFirst, a, b, sum, max, hSum, hMax⟩ := terminalStoresOfPublicationAtSites hX hFinal
  have hIndex : publication - 2 = first := by omega
  let writer := terminalStatsProducer l g stage
  have hPos : ∃ a bytes, X.get (writer, first + word.val) =
      some ⟨(Softmax.statsStore (finalStatsWriteSite word)).pc, .wr a bytes⟩ := by
    fin_cases word
    · exact ⟨a, sum, hSum⟩
    · exact ⟨b, max, hMax⟩
  obtain ⟨acc, bytes, hActual⟩ := hPos
  obtain ⟨warp, hw, hAcc⟩ :=
    Scores.statisticsStoreFootprint hp hX (finalStatsWriteSite word) hActual
  have hWarp : warp = terminalStatsWarp l g stage :=
    Fin.ext (hw.trans (terminalStatsProducerWarp hp g stage))
  subst warp
  have hFootprint : Softmax.statsAcc l writer (terminalStatsWarp l g stage)
      (finalStatsWriteSite word) = {loc := statsLoc l g stage (finalStatsKind word), size := 4} :=
    congrArg (fun loc : Loc => ({loc := loc, size := 4} : Acc))
      (terminalStatsLocation hp g stage word)
  rw [hIndex]
  exact ⟨bytes, hFootprint ▸ hAcc ▸ hActual⟩


private theorem statsWriteEarlierOrSame {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g publication issuer j : Nat} {stage : Fin 2} (word : Fin 2)
    (hFinal : Scores.Publishes X (terminalStatsProducer l g stage, publication) .final)
    {a : Acc} {bs : List Byte} (site : Fin 4)
    (he : X.get (issuer, j) = some ⟨(Softmax.statsStore site).pc, .wr a bs⟩)
    {k : Nat} (hk : k < 4) (hCover : a.Covers ((statsLoc l g stage (finalStatsKind word)).at k)) :
    (issuer, j) = (terminalStatsProducer l g stage, publication - 2 + word.val) ∨
      baseCausality l X (issuer, j)
        (terminalStatsProducer l g stage, publication - 2 + word.val) := by
  obtain ⟨warp, hw, rfl⟩ := Scores.statisticsStoreFootprint hp hX site he
  obtain ⟨hThread, hFamily⟩ := sameStatisticsLane hp stage word site warp hw hk hCover
  subst issuer
  let writer := terminalStatsProducer l g stage
  let ix := publication - 2 + word.val
  let target : Acc := {loc := statsLoc l g stage (finalStatsKind word), size := 4}
  obtain ⟨bytes, hTarget⟩ := terminalWordStore hp hX word hFinal
  obtain ⟨first, hFirst, _, _, _, _, _, hMax⟩ :=
    terminalStoresOfPublicationAtSites hX hFinal
  have hBefore : j < publication := by
    rcases Nat.lt_trichotomy j publication with hj | rfl | hj
    · exact hj
    · obtain ⟨e, hf, hn⟩ := hFinal
      rw [he] at hf
      obtain rfl := Option.some.inj hf.symm
      simp [Scores.notice] at hn
    · have hb := Scores.afterFinalPublicationPc hX hFinal hj he
      change 7616 < (Softmax.statsStore site).pc at hb
      fin_cases site <;> contradiction
  have hBound : j ≤ ix := by
    fin_cases word
    · by_contra! hl
      have hEq : j = first + 1 := by
        change publication - 2 + 0 < j at hl
        omega
      rw [hEq] at he
      have hs := congrArg Event.pc (Option.some.inj (he.symm.trans hMax))
      have hNow : site = 3 := by
        change (Softmax.statsStore site).pc = 7615 at hs
        fin_cases site <;> first | rfl | contradiction
      exact (by decide : (0 : Fin 2) ≠ 1) (hFamily.mp hNow)
    · change j ≤ publication - 2 + 1
      omega
  rcases Nat.eq_or_lt_of_le hBound with hEq | hLt
  · exact .inl (Prod.ext rfl hEq)
  refine .inr (Relation.TransGen.single (.inl ⟨rfl, hLt,
    (List.getElem?_eq_some_iff.mp hTarget).1, ?_⟩))
  intro hSame
  have hA : (X.get (writer,j)).bind Event.acc = some (Softmax.statsAcc l writer warp site) := by
    rw [he]
    rfl
  have hB : (X.get (writer,ix)).bind Event.acc = some target := by
    change (X.get (writer, publication - 2 + word.val)).bind Event.acc = some target
    rw [hTarget]
    rfl
  exact hSame.not_overlap rfl hLt hA hB ⟨_, hCover, Acc.covers_at hk⟩

/-- Every competing writer of a terminal statistics byte is either the matched write, ordered
before it, or an observed correction staging write. -/
theorem terminalWordOrderOrStaging {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g publication : Nat} {stage : Fin 2}
    (hFinal : Scores.Publishes X (terminalStatsProducer l g stage, publication) .final)
    (word : Fin 2) {k : Nat} (hk : k < 4)
    {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte} (hw : X.MemWrites w a bs)
    (hCovers : a.Covers ((statsLoc l g stage (finalStatsKind word)).at k)) :
    let writer := (terminalStatsProducer l g stage, publication - 2 + word.val)
    w = .thread writer ∨
      modelCausality l X ((statsLoc l g stage (finalStatsKind word)).at k) w (.thread writer) ∨
      StagingWrite X w a bs := by
  obtain ⟨⟨issuer, j⟩, rfl, hWrite⟩ := terminalStatisticsWriterOrdinary hp hX hk hw hCovers
  have hShared : a.loc.space = .shared := hCovers.1.symm
  rcases sharedWriteSite hX hWrite hShared with hAlloc | ⟨site, hStats⟩ | hStage
  · exact (allocatorWriteDoesNotCoverStatistics hp hX hAlloc hCovers).elim
  · rcases statsWriteEarlierOrSame hp hX word hFinal site hStats hk hCovers with h | h
    · exact .inl (congrArg AsyncCopy.Ref.thread h)
    · exact .inr (.inl (.inl h))
  · obtain ⟨stage, subbox, chunk, he⟩ := hStage
    exact .inr (.inr (StagingWrite.of_event stage subbox chunk he))

end
end PTX.Kernels.TmlFa4Fwd.Thread.Correction
