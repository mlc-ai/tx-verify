-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedKeyBank
public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringKeyLaunchValue
import Kernels.TmlFa4Fwd.Proof.Thread.RecurringKeyScoreUse
import Kernels.TmlFa4Fwd.Proof.Protocol.CacheOperandWriterOrder
import Kernels.TmlFa4Fwd.Proof.Protocol.CompetingCacheWrites
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSelectedUseBound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.TcMma PTX.AsyncCopy Thread Thread.Scores Thread.Loader
open Protocol.LoaderReady
open Loader (kvUseStage)
open Mma (qkFragment kvStart sharedDescriptor qkByteIndex qkOperands qkKey recurringKeyBlock)

noncomputable section

/-- Each observed recurring score bank uses the descending key tile of its own commit ordinal. -/
theorem ScoreQkBank.keyUseOfScoreOrdinal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {load : EvId} {cell : Cell} {stage : Fin 2} (bank : ScoreQkBank l X load cell stage)
    (hPositive : 0 < scoreCommitOrdinal l X (load.1/l.block) stage bank.seen.commit) :
    bank.keyUse = 2*scoreCommitOrdinal l X (load.1/l.block) stage bank.seen.commit := by
  have hScore : ScoreCommit l X (bank.seen.commit.1,bank.seen.commit.2)
      (load.1/l.block) stage bank.seen.spec bank.seen.rank := bank.seen.score
  obtain ⟨start,hIndex,hFragments⟩ := hScore.recurringKeyUse hp hX hPositive
  have hStart : start = bank.start := by have := bank.position; omega
  subst start
  obtain ⟨_,_,_,_,_,hRank,_⟩ := hFragments 0
  simpa only [ScoreQkBank.keyUse,Fin.val_zero,Nat.add_zero] using hRank

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : Epilogue.DrainCuQProtected p X)
    (hFrame : OutputFootprint p X) {g pos : Nat} {stage : Fin 2} {round : Round} (quarter : Fin 4)
    (word : Fin 32) {values : List Value}
    (he : X.get (g,pos) = some
      ⟨scorePc round quarter,.tc (.ld (scoreAddress l g stage quarter) values .s32x32b)⟩)
    (bank : ScoreQkBank l X (g,pos)
      (tcDataCell l g .s32x32b (scoreAddress l g stage quarter) word.val) stage)
    (hPositive : 0 < scoreCommitOrdinal l X (g/l.block) stage bank.seen.commit) {batch : Nat}
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ bank.seen.commit.1/l.block)
    (hHi : bank.seen.commit.1/l.block < tilePrefix p (batch+1)*p.heads)
include hp hX hCuQ hFrame quarter word he bank hPositive hb hLo hHi

/-- A recurring score word equals its launch-input dot product once the serving
copies are ordered with every competing cache copy to their operand bytes. -/
theorem ScoreQkBank.recurringWordOfOrderedKeysInPrefix
    (hOrder : ∀ (step : Fin 8) {idx : Nat} {loc : Loc} {pub : EvId}
      {group : PublishedCopyGroup l X pub} {j : Nat} {spec : Spec} {bs : List Byte},
      X.AsyncArrive pub (readyObject l bank.seen.commit.1 (kvUseStage bank.keyUse)) true →
      generation l X pub (kvUseStage bank.keyUse) = bank.keyUse/3 →
      (j,spec) ∈ group.copies →
      (qkOperands l bank.seen.commit.1 bank.block step bank.keyUse).byteLoc .b idx = some loc →
      X.MemWrites (.async (pub.1,j) (.write .copy)) spec.dst bs → spec.dst.Covers loc →
      ∀ other copy, X.Copy other copy → copy.dst.Covers loc →
        other = (pub.1,j) ∨
        modelCausality l X loc (.async other (.write .copy)) (.async (pub.1,j) (.write .copy)) ∨
        modelCausality l X loc
          (.async (bank.seen.commit.1,bank.start+step.val) (.mmaRead true idx))
          (.async other (.write .copy))) :
    let coords := Epilogue.assignedCoordinates p batch (bank.seen.commit.1/l.block)
    let firstQ := p.qOffset batch+256*coords.1+128*stage.val
    let n := scoreCommitOrdinal l X (g/l.block) stage bank.seen.commit
    let firstK := 128*(Mma.trips p batch coords.1-1-n)
    values[word.val]? = some (.float .f32
      (firstScoreDot p l g batch coords.2 firstQ firstK quarter word)) := by
  let coords := Epilogue.assignedCoordinates p batch (bank.seen.commit.1/l.block)
  let n := scoreCommitOrdinal l X (g/l.block) stage bank.seen.commit
  let firstK := 128*(Mma.trips p batch coords.1-1-n)
  have hKeyBytes (step : Fin 8) (k byte : Nat) (hk : k < 16) (hbByte : byte < 2) :
      ∃ loc,
        let col := (firstScoreColumn quarter word).val
        let idx := qkByteIndex col k byte
        (qkOperands l bank.seen.commit.1 bank.block step bank.keyUse).byteLoc .b idx = some loc ∧
        Mma.OperandByteSource l X (bank.seen.commit.1,bank.start+step.val) true idx loc
          (if firstK+col < p.kLength batch then
            (Value.float .bf16 (qkKey p batch coords.2 (firstK+col)
              (16*step.val+k))).byteAt byte
          else zeroByte) := by
    let row := (firstScoreColumn quarter word).val
    let idx := qkByteIndex row k byte
    obtain ⟨d,op,accum,mask,hIssue,_⟩ := bank.fragments step
    have hB := bank.recurringKeyDescriptors hp hX hPositive step hIssue
    have hOp := hIssue.operandsOfKey hp hX hB
    have hBlock := bank.recurringBlock hp hX hPositive step hIssue
    rw [hBlock] at hIssue
    obtain ⟨pub,group,j,spec,bytes,loc,hPub,hPhase,hMember,hValid,hLoc,hWrite,hCover,
        hBefore,hValue⟩ :=
      recurringKeyOperandLaunchByte hp hX hFrame stage hIssue hb hLo hHi
        (firstScoreColumn quarter word).isLt hk hbByte
    have hUse := bank.keyUseAtFragment step.val (by have := step.isLt; omega)
    dsimp only at hUse hPub hPhase hValid hValue
    rw [hUse] at hPub hPhase hValid hValue
    have hN := bank.keyUseOfScoreOrdinal hp hX hPositive
    change bank.keyUse = 2*n at hN
    have hDiv : bank.keyUse/2 = n := by omega
    rw [hDiv] at hValid hValue
    change firstK+row < p.kLength batch at hValid
    have hByte := hLoc
    rw [hOp] at hLoc
    have hMma : X.MmaIssue (bank.seen.commit.1,bank.start+step.val) d op accum mask :=
      ⟨_,hIssue.decoded⟩
    refine ⟨loc,hLoc,⟨.async (pub.1,j) (.write .copy),spec.dst,bytes,hWrite,hCover,?_,hBefore,?_⟩⟩
    · rw [ite_eq_left hValid,qkKey,ite_eq_left hValid]
      exact hValue
    · intro other a data hOther hCovers
      exact Protocol.cacheOperandOrderOfCopyOrder hp hX hMma hByte
        (hOrder step hPub hPhase hMember hLoc hWrite hCover) hOther hCovers
  exact bank.wordOfSelectedQueryInPrefix hp hX hCuQ hFrame quarter word he
    hb hLo hHi (by
      intro step d operands accum mask hIssue
      exact bank.recurringKeyDescriptors hp hX hPositive step hIssue) hKeyBytes

/-- Every observed recurring score word is its launch-input dot product, with all
overlapping cache writers ordered by the actual ready and release observations. -/
theorem ScoreQkBank.recurringWordOfLaunchInputsInPrefix :
    let coords := Epilogue.assignedCoordinates p batch (bank.seen.commit.1/l.block)
    let firstQ := p.qOffset batch+256*coords.1+128*stage.val
    let n := scoreCommitOrdinal l X (g/l.block) stage bank.seen.commit
    let firstK := 128*(Mma.trips p batch coords.1-1-n)
    values[word.val]? = some (.float .f32
      (firstScoreDot p l g batch coords.2 firstQ firstK quarter word)) :=
  bank.recurringWordOfOrderedKeysInPrefix hp hX hCuQ hFrame quarter word he
    hPositive hb hLo hHi (by
    intro step idx loc pub group j spec bytes hPub hPhase hMember hByte _ hCover
    obtain ⟨d,op,accum,mask,hKey,_⟩ := bank.fragments step
    have hB := bank.recurringKeyDescriptors hp hX hPositive step hKey
    have hOp := hKey.operandsOfKey hp hX hB
    have hBlock := bank.recurringBlock hp hX hPositive step hKey
    rw [hBlock] at hKey
    have hUse := bank.keyUseAtFragment step.val (by have := step.isLt; omega)
    exact recurringKeyCopyCompetitors hp hX stage hKey hUse.symm hPub hPhase hMember
      (hOp.symm ▸ hByte) hCover)
end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

/-- The selected recurring QK commit's visit lies inside the launch request.
The bound follows from its matched, actually issued key-cache packet. -/
theorem ScoreQkBank.recurringVisitBound (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g pos batch : Nat} {cell : Cell} {stage : Fin 2}
    (bank : ScoreQkBank l X (g,pos) cell stage)
    (hPositive : 0 < scoreCommitOrdinal l X (g/l.block) stage bank.seen.commit)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    scoreCommitOrdinal l X (g/l.block) stage bank.seen.commit <
      Mma.trips p batch (Epilogue.assignedCoordinates p batch (g/l.block)).1 := by
  have hCta := (scoreCommitActor hp hX bank.seen.score).1
  obtain ⟨d,op,accum,mask,hIssue,_⟩ := bank.fragments 0
  have hBlock := bank.recurringBlock hp hX hPositive 0 hIssue
  rw [hBlock] at hIssue
  obtain ⟨pub,group,j,spec,_,_,hPub,hPhase,hMember,_⟩ :=
    recurringKeyOperandLaunchByte (row := 0) (k := 0) (byte := 0) hp hX hFrame stage
      hIssue hb (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (by decide) (by decide) (by decide)
  have hUse := bank.keyUseAtFragment 0 (by decide)
  have hOrdinal := bank.keyUseOfScoreOrdinal hp hX hPositive
  dsimp only [Fin.val_zero,Nat.add_zero] at hPub hPhase hUse hOrdinal hCta
  rw [hUse] at hPub hPhase
  have hOwner := (publicationCta hp hX hPub).symm.trans hCta
  have hMany : 2 ≤ bank.keyUse := by omega
  have hBound := group.recurringUseBound hp hX hFrame hPub hPhase hMany hMember
    (hOwner.symm ▸ hLo) (hOwner.symm ▸ hHi)
  rw [hOwner,hOrdinal] at hBound
  omega

end
end PTX.Kernels.TmlFa4Fwd.Softmax
