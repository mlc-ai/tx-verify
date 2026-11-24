-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueWritebackDrain
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainRounds

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- Output waits, stores, commits and releases preserve both warp counts, including
unsuccessful output polls. -/
theorem WritebackTrace.noCollectives {p : Params} {l : Launch} {g batch head tile : Nat}
    {start finish : Option WritebackSite} {events : List Event}
    (h : WritebackTrace p l g batch head tile start events finish) :
    events.countP Execution.isShfl = 0 ∧ events.countP isFullWarpVote = 0 := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | @step site e es finish he hTail ih =>
    rw [he]
    cases site <;> simpa [List.countP_cons, writebackKind, Execution.isShfl, isFullWarpVote,
      isWarpVote, voteClass] using ih

private theorem drainPersistent_writeback_disjoint :
    ∀ r ∈ drainPersistent, r ∉ writebackWrites ++ [7872, 7873, 7229, 2401] := by
  decide

/-- A lane that performs one read reaches the same shared collective ordinal as its peers. -/
theorem readBeforeDrainCounts {l : Launch} {X : Execution} {pc : Nat}
    {eligible : Nat → Prop} [DecidablePred eligible]
    {g : Nat} {pos : Nat → Nat} {shuffles votes : Nat}
    (hOrd : WarpOrdinals l X g pos shuffles votes)
    (hRead : ∀ lane < 32, eligible lane →
      ∃ a bs, X.get (warpLane l g lane, pos lane) = some ⟨pc, .rd a bs⟩) :
    WarpOrdinals l X g (fun lane => if eligible lane then pos lane + 1 else pos lane)
      shuffles votes := by
  have same (test : Event → Bool) (n : Nat)
      (hCount : ∀ lane < 32, ((X.tr (warpLane l g lane)).take (pos lane)).countP test = n)
      (hNo : ∀ a bs, test ⟨pc, .rd a bs⟩ = false) :
      ∀ lane < 32, ((X.tr (warpLane l g lane)).take
        (if eligible lane then pos lane + 1 else pos lane)).countP test = n := by
    intro lane hl
    by_cases h : eligible lane
    · obtain ⟨a, bs, he⟩ := hRead lane hl h
      rw [ite_eq_left h, List.take_add_one]
      rw [show (X.tr (warpLane l g lane))[pos lane]? = _ from he]
      simp [hNo, hCount lane hl]
    · rw [ite_eq_right h]
      exact hCount lane hl
  exact ⟨same _ _ hOrd.shfl (fun _ _ => rfl), same _ _ hOrd.vote (fun _ _ => rfl)⟩

/-- The writeback and optional cuQ read bring every lane to the first drain shuffle.
The first down shuffle supplies the adjacent request endpoint and starts the up-scan rounds. -/
theorem drainStartFromWriteback {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g batch head tile : Nat} (hg : g < l.threads)
    (hb : batch < p.batch) (hh : head < p.heads) (htile : 256 * tile < p.qLength batch)
    {pos : Nat → Nat} {state : Nat → TState} {shuffles votes : Nat}
    (hOrd : WarpOrdinals l X g pos shuffles votes)
    (hAt : ∀ lane < 32, At (state lane) 2958 (writebackEntry p l batch head tile))
    (hGate : ∀ lane < 32, (state lane).regs 307 = some (.pred (p.batch < lane)))
    (hIndex : ∀ lane < 32, (state lane).regs 1201 = some (b32 lane))
    (hBase : ∀ lane < 32, (state lane).regs 7506 = some (b64 p.cuQBase))
    (hActive : ∀ lane < 32, (state lane).regs 268 =
      some (.pred (!decide (laneHasRequest lane p.batch))))
    (hRun : ∀ lane < 32, Run kernel Assumptions.all l (warpLane l g lane) (state lane)
      ((X.tr (warpLane l g lane)).drop (pos lane)) none)
    (hProtected : ∀ lane < 32, lane ≤ p.batch → ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * lane)).at k)) :
    ∃ atUp : Nat → Nat, ∃ after : Nat → TState,
      WarpOrdinals l X g atUp (shuffles + 1) votes ∧
      DrainRound p l X g 0 false 0 atUp after ∧
      (∀ lane < 32, ∀ stage : Fin 5, (after lane).regs (drainScanGuardReg false stage) =
        some (.pred (drainScanGuard stage lane))) ∧
      (∀ lane < 32, ∀ r ∈ drainPersistent, (after lane).regs r = (state lane).regs r) ∧
      ∀ lane < 32, ∃ e, X.get (warpLane l g lane, atUp lane - 1) = some e ∧ e.pc = 2990 := by
  let _ : Nonempty Value := ⟨b32 0⟩
  let _ : Nonempty TState := ⟨state 0⟩
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane : ∀ lane < 32, laneOf l (warpLane l g lane) = lane := by
    intro lane hl
    exact (Step.sameWarp_lane hBlock hg hl).2
  have hObserved (lane : Nat) (hl : lane < 32) :
      ∃ (written suffix : List Event) (recv : Value) (ok : Bool) (u : TState),
      (X.tr (warpLane l g lane)).drop (pos lane) = written ++ suffix ∧
      WritebackTrace p l (warpLane l g lane) batch head tile (some (.ready 0)) written none ∧
      let start := pos lane + written.length
      let idx := if lane ≤ p.batch then start + 1 else start
      let word := b32 (drainCuQ p lane)
      (lane ≤ p.batch → ∃ a bs, X.get (warpLane l g lane, start) = some ⟨2989, .rd a bs⟩) ∧
      X.get (warpLane l g lane, idx) = some ⟨2990, .shfl .down word 1 31 recv ok⟩ ∧
        At u 2991 [(7229, word), (2401, recv)] ∧
        (∀ r, r ∉ writebackWrites ++ [7872, 7873, 7229, 2401] → u.regs r = (state lane).regs r) ∧
        Run kernel Assumptions.all l (warpLane l g lane) u
          ((X.tr (warpLane l g lane)).drop (idx + 1)) none := by
    let thread := warpLane l g lane
    have he : laneOf l thread = lane := hLane lane hl
    have hProtect : laneOf l thread ≤ p.batch → ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
        ¬ a.Covers ((globalLoc (p.cuQBase + 4 * laneOf l thread)).at k) := by
      rw [he]
      exact hProtected lane hl
    obtain ⟨written, suffix, hs, hTrace, _, rest⟩ :=
      writebackDrainFirst hp hX thread (pos lane) hb hh htile (hAt lane hl)
        (by simpa only [he] using hGate lane hl) (by simpa only [he] using hIndex lane hl)
        (hBase lane hl) (hRun lane hl) hProtect
    simp only [he] at rest
    obtain ⟨recv, ok, u, heObs, hAt, hFrame, hRun⟩ := rest.2
    exact ⟨written, suffix, recv, ok, u, hs, hTrace,
      fun ha => ⟨_, _, rest.1 ha⟩, heObs, hAt, hFrame, hRun⟩
  choose! written suffix recv ok u hSplit hTrace hRead hEvent hAfter hFrame hRest using hObserved
  have hAfterWriteback := hOrd.advance written (fun lane hl => ⟨suffix lane, hSplit lane hl⟩)
    (fun lane hl => (hTrace lane hl).noCollectives.1)
    (fun lane hl => (hTrace lane hl).noCollectives.2)
  have hBeforeDown := readBeforeDrainCounts (eligible := fun lane => lane ≤ p.batch)
    hAfterWriteback hRead
  let idx := fun lane =>
    if lane ≤ p.batch then pos lane + (written lane).length + 1
      else pos lane + (written lane).length
  let atUp := fun lane => idx lane + 1
  have hRecv := hBeforeDown.shuffle_value hX hBlock hg (fun _ => 2990) .down
    (fun lane => b32 (drainCuQ p lane)) recv (fun _ => 1) (fun _ => 31) ok hEvent
  have hPrep (lane : Nat) (hl : lane < 32) :
      ∃ after, At after (drainScanPc false 0) [(7232, b32 (groupLaneTiles p 0 lane))] ∧
        (∀ stage : Fin 5, after.regs (drainScanGuardReg false stage) =
          some (.pred (drainScanGuard stage lane))) ∧
        Run kernel Assumptions.all l (warpLane l g lane) after
          ((X.tr (warpLane l g lane)).drop (atUp lane)) none ∧
        ∀ r ∈ drainPersistent, after.regs r = (state lane).regs r := by
    have hr := hAfter lane hl
    rw [(hRecv lane hl).1] at hr
    have hFacts : At (u lane) 2991
        [(7229, b32 (drainCuQ p lane)),
         (2401, b32 (drainCuQ p (shflSource .down lane 1 31).1)),
         (268, .pred (!decide (laneHasRequest lane p.batch))), (1201, b32 lane)] :=
      hr.mono ⟨hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        (hFrame lane hl 268 (by decide)).trans (hActive lane hl),
        (hFrame lane hl 1201 (by decide)).trans (hIndex lane hl), trivial⟩
    obtain ⟨_, after, hLocal, hu, hGuards, hSaved⟩ :=
      drainFirstPrepared hp (warpLane l g lane) (u lane) (by rw [hLane lane hl]; exact hl)
        (by simpa only [hLane lane hl] using hFacts)
    rw [hLane lane hl] at hu hGuards
    refine ⟨after, hu, hGuards, (hRest lane hl).after_local (run_rtg hLocal), ?_⟩
    intro r hr
    refine (hSaved r hr).trans (hFrame lane hl r ?_)
    exact drainPersistent_writeback_disjoint r hr
  choose! after hReady hGuards hTail hSave using hPrep
  refine ⟨atUp, after, (hBeforeDown.shuffle (fun _ => 2990) .down
    (fun lane => b32 (drainCuQ p lane)) recv (fun _ => 1) (fun _ => 31) ok hEvent).2,
    ⟨?_, hTail⟩, hGuards, hSave, fun lane hl =>
      ⟨⟨2990, .shfl .down (b32 (drainCuQ p lane)) 1 31 (recv lane) (ok lane)⟩, ?_, rfl⟩⟩
  swap
  · simpa only [atUp, Nat.add_sub_cancel] using hEvent lane hl
  intro lane hl
  have hReg := (hReady lane hl).2.2.2.2.1
  exact (hReady lane hl).mono ⟨hGuards lane hl 0, by
    change (after lane).regs 7232 = some (b32 (prefixWindow (groupLaneTiles p 0) 1 lane))
    rw [prefixWindow_one]; exact hReg, trivial⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
