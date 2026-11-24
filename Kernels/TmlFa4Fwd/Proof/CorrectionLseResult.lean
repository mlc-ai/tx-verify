-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionLseValues
public import Kernels.TmlFa4Fwd.Proof.CorrectionLseIssuer
public import Kernels.TmlFa4Fwd.Proof.CorrectionLseWriters

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Epilogue Prologue

noncomputable section

/-- Statistics at the selected trace window, required only for a valid output row. -/
def ObservedValidLseStatisticsAt (p : Params) (l : Launch) (X : Execution) (cta : Nat) : Prop :=
  ∀ {g batch lane pos j pc : Nat} {targetAcc : Acc} {bytes : List Byte}
    {t : TState} {o : Option TState},
    g / l.block = cta → lane < 32 → batch < p.batch → tilePrefix p batch * p.heads ≤ g / l.block →
    g / l.block < tilePrefix p (batch + 1) * p.heads →
    At t 7932 (correctionActiveTileFacts p l g batch lane) →
    Run kernel Assumptions.all l (warpLane l g lane) t ((X.tr (warpLane l g lane)).drop pos) o →
    pos ≤ j → X.get (warpLane l g lane, j) = some ⟨pc, .wr targetAcc bytes⟩ →
    let thread := warpLane l g lane
    let coords := assignedCoordinates p batch (g / l.block)
    ∀ (stage : Fin 2) u consumed es visits, pc = lseGuardPc stage + 1 →
      stageRow coords.1 stage + rowOf l thread < p.qLength batch →
      u.pc = (if stage = 0 then 9061 else 9074) →
      (X.tr thread).drop pos = consumed ++ es →
      TraceReach kernel Assumptions.all l thread t consumed u →
      Walk kernel Assumptions.all l thread u es visits → ⟨pc, .wr targetAcc bytes⟩ ∈ es →
      LseStatisticsAt p batch coords.2 (stageRow coords.1 stage + rowOf l thread) stage u

private theorem correctionWorkOfObservedLse {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g lane j pc : Nat} {a : Acc} {bs : List Byte} (hg : g < l.threads)
    (hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (hl : lane < 32) (hPc : pc = 9073 ∨ pc = 9082)
    (he : X.get (warpLane l g lane, j) = some ⟨pc, .wr a bs⟩) :
    g / l.block < tilePrefix p p.batch * p.heads := by
  by_cases hFirst : g / l.block < tilePrefix p (min p.batch 31) * p.heads
  · exact hFirst.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (Nat.min_le_left ..)))
  have hRoute := correctionFirstRouteOfEvent hp hX hg hWarp.1 hWarp.2 hl
    (by change 7801 < pc; omega) he
  rw [ite_eq_right hFirst] at hRoute
  obtain ⟨ends, fallback, hFallback⟩ := hRoute
  rcases correctionFallbackGroupEvent hp hX hg fallback (Nat.le_of_not_gt hFirst)
      (by change 7859 < pc; omega) hFallback with
    ⟨_, _, done, hDone⟩ | ⟨first, batch, _, _, hb, _, hHigh, _, result, hResult⟩
  · exact (exhaustedCannotWrite hp hPc done hDone).elim
  · exact hHigh.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4 * i)).at k))
include hp hX hUsedK

/-- Every recorded LSE store carries the numerical result of its decoded request and row.
The row information comes from the issuer's actual scheduler and both tail guards. -/
theorem correctionLseEventValueAtCta {i : EvId} {pc : Nat} {a : Acc} {bytes : List Byte}
    (hStats : ObservedValidLseStatisticsAt p l X (i.1 / l.block)) (hPc : pc ∈ lseStoreSites)
    (he : X.get i = some ⟨pc, .wr a bytes⟩) :
    ∃ batch < p.batch, ∃ head < p.heads, ∃ row < p.qLength batch,
      a.loc = p.lseLoc (p.qOffset batch + row) head ∧
      a.size = 4 ∧ bytes = (fl (lse p batch head row)).toBytes := by
  have hg := Step.CtaBar.thread_lt_of_get hX he
  have hWarp := lseStoreWarp hp hX he hPc
  have hl : laneOf l i.1 < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l i.1 (laneOf l i.1) = i.1 :=
    Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hGet : X.get (warpLane l i.1 (laneOf l i.1), i.2) = some ⟨pc, .wr a bytes⟩ := by
    rw [hSelf]
    exact he
  have hSite : pc = 9073 ∨ pc = 9082 := by simpa [lseStoreSites] using hPc
  have hWork := correctionWorkOfObservedLse hp hX hg hWarp hl hSite hGet
  obtain ⟨batch, hb, hLo, hHi, ends, sh, votes, tile, hTile⟩ :=
    correctionActiveTileOfEvent hp hX hg hWarp.1 hWarp.2 hl hWork
      (by change 7884 < pc; omega) hGet
  let lane := laneOf l i.1
  let coords := assignedCoordinates p batch (i.1 / l.block)
  have ht := tile.checkpoint lane hl
  have hRun := (tile.continuation lane hl).after_local_nonempty
    (tile.localSteps lane hl) hTile.nonempty
  obtain ⟨s, es, vs, hs, hw, hEvent, consumed, hTrace, hPath⟩ :=
    correctionLseReadyFromSelected hp hX hb hLo hHi ht
      (hUsedK batch hb)
      hRun hTile.before (by change 9057 < pc; omega) hGet
  have ⟨htile, hHead⟩ := assignedCoordinates_valid hp hLo hHi
  have hNumerics := hStats rfl hl hb hLo hHi ht hRun hTile.before hGet
  obtain ⟨stage, _, hRow, hAddr, hSize, hBytes⟩ :=
    correctionLseValueFromReadyForValidRow hp hb hHead htile hs hSite hw hEvent
      (fun stage u advanced rest tail hStage hr hPc hEq hReach hw he =>
        hNumerics stage u (consumed ++ advanced) rest tail hStage hr hPc
          (by rw [hTrace, List.append_assoc, ← hEq]) (hPath.append hReach) hw he)
  refine ⟨batch, hb, coords.2, hHead, stageRow coords.1 stage + rowOf l (warpLane l i.1 lane),
    hRow, ?_, hSize, hBytes⟩
  simpa only [Nat.add_assoc] using hAddr

omit hp hX hUsedK in
/-- The shape and value of one scalar output write of the correction role. -/
def LseWriteValue (p : Params) (a : Acc) (bytes : List Byte) : Prop :=
  ∃ batch < p.batch, ∃ head < p.heads, ∃ row < p.qLength batch,
    a.loc = p.lseLoc (p.qOffset batch + row) head ∧ a.size = 4 ∧
      bytes = (Value.float .f32 (lse p batch head row)).toBytes

omit hp hX hUsedK in
/-- Value supplied by every scalar output write of the correction role. -/
def LseWriteValues (p : Params) (X : Execution) : Prop :=
  ∀ i a bytes, X.Writes i a bytes → a.loc.space = .global → LseWriteValue p a bytes

/-- The observed final statistics determine the value of each abstract LSE write. -/
theorem lseWriteValueAtCta {i : EvId} {a : Acc} {bytes : List Byte}
    (hStats : ObservedValidLseStatisticsAt p l X (i.1 / l.block)) (hWrite : X.Writes i a bytes)
    (hGlobal : a.loc.space = .global) : LseWriteValue p a bytes := by
  have hIntent : X.Intent (.thread i) a true := (show
    X.MemWrites (.thread i) a bytes from .inl hWrite).intent
  rcases globalWriteIntentSources hX hIntent hGlobal with
    ⟨j, site, result, hRef, hSite, he⟩ | ⟨_, _, _, _, _, _, _, hRef, _⟩
  · have hId := AsyncCopy.Ref.thread.inj hRef
    subst j
    obtain ⟨_, hWrite⟩ := hWrite
    rw [he] at hWrite
    obtain ⟨_, hBytes⟩ := Kind.wr.inj (Event.mk.inj (Option.some.inj hWrite)).2
    subst result
    exact correctionLseEventValueAtCta hp hX hUsedK hStats hSite he
  · cases hRef

end
end PTX.Kernels.TmlFa4Fwd.Correction
