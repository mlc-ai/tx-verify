-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainLaterPrepare
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainRounds

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

private theorem holds_of_members {R : Nat → Option Value} {facts : List (Nat × Value)}
    (h : ∀ rv ∈ facts, R rv.1 = some rv.2) : Holds R facts := by
  induction facts with
  | nil => trivial
  | cons rv rest ih =>
    cases rv with
    | mk r v => exact ⟨h (r, v) (by simp), ih (fun x hx => h x (by simp [hx]))⟩

/-- An accepted warp enters a later scan on every lane. The optional cuQ reads preserve the
collective ordinals, and the down shuffle advances their common shuffle ordinal by one. -/
theorem drainWarpNext {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g first base stop cta : Nat} (hg : g < l.threads) (hGroup : first + 31 < p.batch)
    {pos : Nat → Nat} {state : Nat → TState} {shuffles votes : Nat}
    (hOrd : WarpOrdinals l X g pos shuffles votes)
    (hAt : ∀ lane < 32, At (state lane) 3032
      (drainLaterEntry p l (warpLane l g lane) first base stop cta))
    (hRun : ∀ lane < 32, Run kernel Assumptions.all l (warpLane l g lane) (state lane)
      ((X.tr (warpLane l g lane)).drop (pos lane)) none)
    (hProtected : ∀ lane < 32, first + 31 + lane ≤ p.batch →
      ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
        ¬ a.Covers ((globalLoc (p.cuQBase + 4 * (first + 31 + lane))).at k)) :
    ∃ atUp : Nat → Nat, ∃ after : Nat → TState,
      WarpOrdinals l X g atUp (shuffles + 1) votes ∧
      DrainRound p l X g (first + 31) true 0 atUp after ∧
      (∀ lane < 32, ∀ stage : Fin 5, (after lane).regs (drainScanGuardReg true stage) =
        some (.pred (drainScanGuard stage lane))) ∧
      (∀ lane < 32, Holds (after lane).regs
        (drainLaterGroup p l (warpLane l g lane) (first + 31) base stop cta)) ∧
      (∀ lane < 32, atUp lane =
        (if first + 31 + lane ≤ p.batch then pos lane + 1 else pos lane) + 1) ∧
      ∀ lane < 32, first + 31 + lane ≤ p.batch → X.get (warpLane l g lane, pos lane) =
        some ⟨3043, .rd {loc := globalLoc (p.cuQBase + 4 * (first + 31 + lane)), size := 4}
          ((b32 (drainCuQ p (first + 31 + lane))).toBytes.map some)⟩ := by
  let _ : Nonempty Value := ⟨b32 0⟩
  let _ : Nonempty TState := ⟨state 0⟩
  let nextGroup := first + 31
  let index := fun lane => nextGroup + lane
  let needsRead := fun lane => index lane ≤ p.batch
  let readAcc := fun lane : Nat =>
    { loc := globalLoc (p.cuQBase + 4 * index lane), size := 4 : Acc }
  let word := fun lane => b32 (drainCuQ p (index lane))
  let idx := fun lane => if needsRead lane then pos lane + 1 else pos lane
  let atUp := fun lane => idx lane + 1
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : laneOf l (warpLane l g lane) = lane :=
    (Step.sameWarp_lane hBlock hg hl).2
  have hIndex (lane : Nat) (hl : lane < 32) : index lane < 2 ^ 31 := by
    have hTotal := hp.shape.2.2.2.2.2
    change p.qOffset p.batch + 256 * p.batch < 2 ^ 30 at hTotal
    dsimp [index, nextGroup]
    omega
  have hOperands (lane : Nat) (hl : lane < 32) :
      (needsRead lane → X.get (warpLane l g lane, pos lane) =
        some ⟨3043, .rd (readAcc lane) ((word lane).toBytes.map some)⟩) ∧
      ∃ recv ok, X.get (warpLane l g lane, idx lane) =
        some ⟨3045, .shfl .down (word lane) 1 31 recv ok⟩ := by
    simpa only [hLane lane hl] using
      drainLaterDownOperands hp hX
        (by rw [hLane lane hl]; exact hIndex lane hl) hGroup (hAt lane hl) (hRun lane hl)
        (by rw [hLane lane hl]; exact hProtected lane hl)
  have hBefore : WarpOrdinals l X g idx shuffles votes := by
    have same (test : Event → Bool) (n : Nat)
        (counts : ∀ lane < 32, ((X.tr (warpLane l g lane)).take (pos lane)).countP test = n)
        (ordinary : ∀ a bs, test ⟨3043, .rd a bs⟩ = false) :
        ∀ lane < 32, ((X.tr (warpLane l g lane)).take (idx lane)).countP test = n := by
      intro lane hl
      by_cases h : needsRead lane
      · have he := (hOperands lane hl).1 h
        dsimp only [idx]
        rw [ite_eq_left h, List.take_add_one]
        rw [show (X.tr (warpLane l g lane))[pos lane]? = _ from he]
        simp [ordinary, counts lane hl]
      · simpa only [idx, ite_eq_right h] using counts lane hl
    exact ⟨same _ _ hOrd.shfl (fun _ _ => rfl), same _ _ hOrd.vote (fun _ _ => rfl)⟩
  choose! recv ok hEvent using fun lane hl => (hOperands lane hl).2
  obtain ⟨hShfl, hAfter⟩ := hBefore.shuffle (fun _ => 3045) .down
    word recv (fun _ => 1) (fun _ => 31) ok hEvent
  have hPeer (lane : Nat) (hl : lane < 32) :
      DrainDownPeer p l X (warpLane l g lane) (idx lane) nextGroup := by
    dsimp only [DrainDownPeer]
    rw [hLane lane hl]
    intro _ _ _
    let source := (shflSource .down lane 1 31).1
    have hSource : source < 32 := Step.shflSource_lt .down hl 1 31
    have hThread : warpLane l g lane - lane + source = warpLane l g source := by
      unfold warpLane
      omega
    change ∃ ordinal j peerRecv peerOk, X.ShflK (warpLane l g lane, idx lane) ordinal ∧
      X.get (warpLane l g lane - lane + source, j) =
        some ⟨3045, .shfl .down (word source) 1 31 peerRecv peerOk⟩ ∧
      X.ShflK (warpLane l g lane - lane + source, j) ordinal ∧
      ¬ ShflExited X (warpLane l g lane - lane + source) ordinal
    rw [hThread]
    exact ⟨shuffles, idx source, recv source, ok source, hShfl lane hl, hEvent source hSource,
      hShfl source hSource,
      ShflK.not_exited hX (Step.sameWarp_lane hBlock hg hSource).1.1.2.1 (hShfl source hSource)⟩
  have hPrep (lane : Nat) (hl : lane < 32) :
      ∃ after, At after (drainScanPc true 0) [(7232, b32 (groupLaneTiles p nextGroup lane))] ∧
        (∀ stage : Fin 5, after.regs (drainScanGuardReg true stage) =
          some (.pred (drainScanGuard stage lane))) ∧
        Run kernel Assumptions.all l (warpLane l g lane) after
          ((X.tr (warpLane l g lane)).drop (atUp lane)) none ∧
        Holds after.regs (drainLaterGroup p l (warpLane l g lane) nextGroup base stop cta) := by
    let thread := warpLane l g lane
    have hL : laneOf l thread = lane := hLane lane hl
    have hSeen := drainLaterReadObserved hp hX (by rw [hL]; exact hIndex lane hl)
      (hAt lane hl) (hRun lane hl) (by rw [hL]; exact hProtected lane hl)
      (fun _ => by rw [hLane lane hl]; exact hPeer lane hl)
    rcases hSeen with ⟨hImpossible, _⟩ | ⟨_, t, _, _, ht, hSuffix⟩
    · omega
    obtain ⟨_, after, hLocal, hTiles, hGuards, hFrame⟩ :=
      drainLaterPrepared hp thread t (by rw [hL]; exact hl) (by rw [hL]; exact hIndex lane hl) ht
    rw [hL] at hTiles hGuards
    have hTail := hSuffix.after_local (run_rtg hLocal)
    rw [hL] at hTail
    refine ⟨after, hTiles, hGuards, hTail, holds_of_members ?_⟩
    intro rv hr
    have hInside : ∀ r ∈ (drainLaterGroup p l thread nextGroup base stop cta).map Prod.fst,
        r ∈ drainPersistent := by
      change ∀ r ∈ [7235, 7236, 1210, 1201, 7147, 7506, 7230, 1072, 7138, 1062],
        r ∈ drainPersistent
      decide
    have hSave := hFrame rv.1 (hInside _ (List.mem_map_of_mem hr))
    have hGroupFacts := ((holds_append _ _ _).mp ht.2.2.2.2).2
    rw [hSave]
    exact holds_mem hGroupFacts hr
  choose! after hReady hGuards hTail hSave using hPrep
  refine ⟨atUp, after, hAfter, ⟨?_, hTail⟩, hGuards, hSave, fun _ _ => rfl,
    fun lane hl => (hOperands lane hl).1⟩
  intro lane hl
  have hTile := (hReady lane hl).2.2.2.2.1
  refine (hReady lane hl).mono ⟨hGuards lane hl 0, ?_, trivial⟩
  change (after lane).regs 7232 = some (b32 (prefixWindow (groupLaneTiles p nextGroup) 1 lane))
  rwa [prefixWindow_one]

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
