-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainPrepare
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The whole warp at one up shuffle, carrying the translated request words in its
actual trace state. -/
structure DrainRound (p : Params) (l : Launch) (X : Execution) (g first : Nat)
    (later : Bool) (stage : Fin 5) (pos : Nat → Nat) (state : Nat → TState) : Prop where
  atWord : ∀ lane < 32, At (state lane) (drainScanPc later stage)
    [(drainScanGuardReg later stage, .pred (drainScanGuard stage lane)),
     (drainScanSrc later stage,
      b32 (prefixWindow (groupLaneTiles p first) (2 ^ stage.val) lane))]
  suffix : ∀ lane < 32, Run kernel Assumptions.all l (warpLane l g lane) (state lane)
    ((X.tr (warpLane l g lane)).drop (pos lane)) none

/-- Use the actual next shuffle of every lane to prove one round of its prefix scan.
The arithmetic continuation leaves all later guards and shared scheduler registers intact. -/
theorem DrainRound.step {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g first : Nat} (hg : g < l.threads) (hf : first ≤ p.batch)
    {later : Bool} {stage : Fin 5} {pos : Nat → Nat} {state : Nat → TState}
    {shuffles votes : Nat} (h : DrainRound p l X g first later stage pos state)
    (hOrd : WarpOrdinals l X g pos shuffles votes) :
    ∃ after : Nat → TState,
      WarpOrdinals l X g (fun lane => pos lane + 1) (shuffles + 1) votes ∧
      ∀ lane < 32, At (after lane) (drainScanPc later stage + 3)
        [(drainScanSum later stage,
          b32 (prefixWindow (groupLaneTiles p first) (2 * 2 ^ stage.val) lane))] ∧
        Run kernel Assumptions.all l (warpLane l g lane) (after lane)
          ((X.tr (warpLane l g lane)).drop (pos lane + 1)) none ∧
        ∀ r, r ∉ [drainScanDst later stage, drainScanDst later stage + 1,
          drainScanSum later stage] → (after lane).regs r = (state lane).regs r := by
  let _ : Nonempty Value := ⟨b32 0⟩
  let _ : Nonempty TState := ⟨state 0⟩
  let pc := drainScanPc later stage
  let width := 2 ^ stage.val
  let input := fun lane => b32 (prefixWindow (groupLaneTiles p first) width lane)
  let resume := fun lane val => next (setReg (state lane) (drainScanDst later stage) val)
  have hLo : 3009 ≤ pc := by cases later <;> simp [pc, drainScanPc]; omega
  have hHi : pc ≤ 3078 := by
    have := stage.isLt
    cases later <;> simp [pc, drainScanPc] <;> omega
  have hModel {s : TState} (hlo : pc ≤ s.pc) (hhi : s.pc ≤ pc + 2) (thread : Nat) :
      out kernel Assumptions.all l thread s = out kernel [] l thread s :=
    epilogue_out_all_eq_nil (.inl ⟨by omega, by omega⟩)
  have hObs : ∀ lane < 32, ∃ recv ok,
      X.get (warpLane l g lane, pos lane) =
        some ⟨pc, .shfl .up (input lane) width 0 recv ok⟩ ∧
      Run kernel Assumptions.all l (warpLane l g lane) (resume lane recv)
        ((X.tr (warpLane l g lane)).drop (pos lane + 1)) none := by
    intro lane hl
    have ht := h.atWord lane hl
    have hv := holds_mem ht.2.2.2.2 (by right; left)
    let thread := warpLane l g lane
    have hOut := drainScanTemplate hp later stage thread (state lane) _ ht.1 ht.2.2.2.1 hv
    rw [← hModel (by rw [ht.1]) (by rw [ht.1]; omega) thread] at hOut
    have hNext : Next kernel Assumptions.all l thread (state lane) (state lane)
        (.shfl .up (input lane) width 0 (fun v _ => resume lane v)) := ⟨.refl, hOut⟩
    obtain ⟨recv, ok, he, _, hRest⟩ :=
      hNext.shuffle_at (h.suffix lane hl) (hOrd.shfl lane hl)
    rw [ht.1] at he
    exact ⟨recv, ok, he, hRest⟩
  choose! recv ok hEvent hSuffix using hObs
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hRecv := hOrd.shuffle_value hX hBlock hg (fun _ => pc) .up input recv
    (fun _ => width) (fun _ => 0) ok hEvent
  have hAfter : ∀ lane < 32, ∃ after, At after (pc + 3)
      [(drainScanSum later stage,
        b32 (prefixWindow (groupLaneTiles p first) (2 * width) lane))] ∧
      Run kernel Assumptions.all l (warpLane l g lane) after
        ((X.tr (warpLane l g lane)).drop (pos lane + 1)) none ∧
      ∀ r, r ∉ [drainScanDst later stage, drainScanDst later stage + 1,
        drainScanSum later stage] → after.regs r = (state lane).regs r := by
    intro lane hl
    have ht := h.atWord lane hl
    let e : Event := ⟨pc, .shfl .up (input lane) width 0 (recv lane) (ok lane)⟩
    have hFire : Fires (state lane).pc
        (.shfl .up (input lane) width 0 (fun v _ => resume lane v)) e
        (some (resume lane (recv lane))) :=
      ⟨recv lane, ok lane, by rw [ht.1], rfl⟩
    obtain ⟨v, hr, hv, hFrame⟩ := drainWarpFold hp later stage (warpLane l g lane) hf hl
      (state lane) (resume lane (recv lane)) e ht hFire
      ⟨ok lane, by rw [ht.1]; dsimp [e]; rw [(hRecv lane hl).1]⟩
      (fun hlo hhi => hModel (by omega) hhi (warpLane l g lane))
    exact ⟨v, hv, (hSuffix lane hl).after_local (run_rtg hr), hFrame⟩
  choose! after hAfter using hAfter
  refine ⟨after, (hOrd.shuffle (fun _ => pc) .up input recv
    (fun _ => width) (fun _ => 0) ok hEvent).2, hAfter⟩

/-- The scan also retains each lane's original contribution for terminal request selection. -/
def drainRoundPersistent : List Nat := 7232 :: drainPersistent

private theorem drainRoundKeeps (later : Bool) (stage : Fin 5) :
    ∀ r ∈ drainRoundPersistent, r ∉ [drainScanDst later stage, drainScanDst later stage + 1,
      drainScanSum later stage] := by
  cases later <;> fin_cases stage <;> decide

private theorem drainRoundKeepsGuard (later : Bool) (stage guard : Fin 5) :
    drainScanGuardReg later guard ∉ [drainScanDst later stage, drainScanDst later stage + 1,
      drainScanSum later stage] := by
  cases later <;> fin_cases stage <;> fin_cases guard <;> decide

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- A scan round before the fifth leaves the next round's exact operand. -/
theorem DrainRound.nextRound {g first : Nat} (hg : g < l.threads) (hf : first ≤ p.batch)
    {later : Bool} {stage : Fin 5} {pos : Nat → Nat} {state : Nat → TState} {shuffles votes : Nat}
    (h : DrainRound p l X g first later stage pos state)
    (hOrd : WarpOrdinals l X g pos shuffles votes)
    (hGuards : ∀ lane < 32, ∀ guard : Fin 5, (state lane).regs (drainScanGuardReg later guard) =
      some (.pred (drainScanGuard guard lane))) (hs : stage.val + 1 < 5) :
    ∃ after : Nat → TState,
      DrainRound p l X g first later ⟨stage.val + 1, hs⟩ (fun lane => pos lane + 1) after ∧
      WarpOrdinals l X g (fun lane => pos lane + 1) (shuffles + 1) votes ∧
      (∀ lane < 32, ∀ guard : Fin 5, (after lane).regs (drainScanGuardReg later guard) =
        some (.pred (drainScanGuard guard lane))) ∧
      ∀ lane < 32, ∀ r ∈ drainRoundPersistent, (after lane).regs r = (state lane).regs r := by
  obtain ⟨after, hNewOrd, hAfter⟩ := h.step hp hX hg hf hOrd
  let follow : Fin 5 := ⟨stage.val + 1, hs⟩
  have hGuard : ∀ lane < 32, ∀ guard : Fin 5, (after lane).regs (drainScanGuardReg later guard) =
      some (.pred (drainScanGuard guard lane)) := by
    intro lane hl guard
    exact ((hAfter lane hl).2.2 _ (drainRoundKeepsGuard later stage guard)).trans
      (hGuards lane hl guard)
  have hPc : drainScanPc later stage + 3 = drainScanPc later follow := by
    simp [drainScanPc, follow]
    omega
  have hReg : drainScanSum later stage = drainScanSrc later follow := by
    cases later <;> fin_cases stage <;> try (exact (by rfl))
    all_goals exact (Nat.lt_irrefl 5 hs).elim
  have hWidth : 2 * 2 ^ stage.val = (2 : Nat) ^ follow.val := by
    simp [follow, pow_succ, Nat.mul_comm]
  refine ⟨after, ⟨?_, fun lane hl => (hAfter lane hl).2.1⟩, hNewOrd, hGuard, ?_⟩
  · intro lane hl
    have ht := (hAfter lane hl).1
    rw [hPc, hReg, hWidth] at ht
    exact ht.mono ⟨hGuard lane hl follow, ht.2.2.2.2.1, trivial⟩
  · intro lane hl r hr
    exact (hAfter lane hl).2.2 r (drainRoundKeeps later stage r hr)

/-- All five up-scan rounds preserve the incoming scheduler state and produce the
inclusive prefix of valid request tiles in each lane. -/
theorem DrainRound.scan {g first : Nat} (hg : g < l.threads) (hf : first ≤ p.batch) {later : Bool}
    {pos : Nat → Nat} {state : Nat → TState} {shuffles votes : Nat}
    (h : DrainRound p l X g first later 0 pos state) (hOrd : WarpOrdinals l X g pos shuffles votes)
    (hGuards : ∀ lane < 32, ∀ guard : Fin 5, (state lane).regs (drainScanGuardReg later guard) =
      some (.pred (drainScanGuard guard lane))) :
    ∃ after : Nat → TState,
      WarpOrdinals l X g (fun lane => pos lane + 5) (shuffles + 5) votes ∧
      ∀ lane < 32, At (after lane) (if later then 3081 else 3024)
        [(7233, b32 (∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i))] ∧
        Run kernel Assumptions.all l (warpLane l g lane) (after lane)
          ((X.tr (warpLane l g lane)).drop (pos lane + 5)) none ∧
        ∀ r ∈ drainRoundPersistent, (after lane).regs r = (state lane).regs r := by
  obtain ⟨_, h1, hOrd1, hG1, hF1⟩ := h.nextRound hp hX hg hf hOrd hGuards (by decide)
  obtain ⟨_, h2, hOrd2, hG2, hF2⟩ := h1.nextRound hp hX hg hf hOrd1 hG1 (by decide)
  obtain ⟨_, h3, hOrd3, hG3, hF3⟩ := h2.nextRound hp hX hg hf hOrd2 hG2 (by decide)
  obtain ⟨_, h4, hOrd4, _, hF4⟩ := h3.nextRound hp hX hg hf hOrd3 hG3 (by decide)
  obtain ⟨after, hOrd5, h5⟩ := h4.step hp hX hg hf (stage := 4) hOrd4
  refine ⟨after, hOrd5, ?_⟩
  intro lane hl
  have hPC : drainScanPc later 4 + 3 = (if later then 3081 else 3024) := by
    cases later <;> rfl
  have hAt := (h5 lane hl).1
  rw [hPC] at hAt
  have hVal : (after lane).regs 7233 =
      some (b32 (∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i)) := by
    have hv := hAt.2.2.2.2.1
    change (after lane).regs 7233 =
      some (b32 (prefixWindow (groupLaneTiles p first) 32 lane)) at hv
    simpa only [prefixWindow_warp _ hl] using hv
  refine ⟨hAt.mono ⟨hVal, trivial⟩, (h5 lane hl).2.1, ?_⟩
  intro r hr
  exact ((h5 lane hl).2.2 r (drainRoundKeeps later 4 r hr)).trans
    ((hF4 lane hl r hr).trans ((hF3 lane hl r hr).trans
      ((hF2 lane hl r hr).trans (hF1 lane hl r hr))))

/-- Each lane obtains the group's total from lane 31's inclusive scan. -/
theorem drainTotalObserved {g first : Nat} (hg : g < l.threads) (later : Bool) {pos : Nat → Nat}
    {state : Nat → TState} {shuffles votes : Nat} (hOrd : WarpOrdinals l X g pos shuffles votes) :
    let pc := if later then 3081 else 3024
    let part := fun lane => ∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i
    (∀ lane < 32, At (state lane) pc [(7233, b32 (part lane))]) →
    (∀ lane < 32, Run kernel Assumptions.all l (warpLane l g lane) (state lane)
      ((X.tr (warpLane l g lane)).drop (pos lane)) none) →
    ∃ after : Nat → TState,
      WarpOrdinals l X g (fun lane => pos lane + 1) (shuffles + 1) votes ∧
      ∀ lane < 32, At (after lane) (pc + 1) [(7234, b32 (part 31)), (7233, b32 (part lane))] ∧
        Run kernel Assumptions.all l (warpLane l g lane) (after lane)
          ((X.tr (warpLane l g lane)).drop (pos lane + 1)) none ∧
        ∀ r, r ≠ 7234 → (after lane).regs r = (state lane).regs r := by
  let pc := if later then 3081 else 3024
  let part := fun lane => ∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i
  change (∀ lane < 32, At (state lane) pc [(7233, b32 (part lane))]) → _
  intro hAt hRun
  have hObs (lane : Nat) : ∃ recv ok, lane < 32 →
      X.get (warpLane l g lane, pos lane) = some ⟨pc, .shfl .idx (b32 (part lane)) 31 31 recv ok⟩ ∧
      Run kernel Assumptions.all l (warpLane l g lane) (next (setReg (state lane) 7234 recv))
        ((X.tr (warpLane l g lane)).drop (pos lane + 1)) none := by
    by_cases hl : lane < 32
    · have ht := hAt lane hl
      have hPC : EpiloguePc (state lane).pc := by
        apply Or.inl
        rw [ht.1]
        cases later <;> decide
      have hTemplate := drainGroupTotalTemplate hp later (warpLane l g lane) (state lane)
        (part lane) ht.1 ht.2.2.2.1 ht.2.2.2.2.1
      have hNext : Next kernel Assumptions.all l (warpLane l g lane) (state lane) (state lane)
          (.shfl .idx (b32 (part lane)) 31 31
            (fun value _ => next (setReg (state lane) 7234 value))) :=
        ⟨.refl, (epilogue_out_all_eq_nil hPC).trans hTemplate⟩
      obtain ⟨recv, ok, he, _, hTail⟩ := hNext.shuffle_at (hRun lane hl) (hOrd.shfl lane hl)
      exact ⟨recv, ok, fun _ => ⟨by simpa only [ht.1] using he, hTail⟩⟩
    · exact ⟨b32 0, false, fun h => (hl h).elim⟩
  choose recv ok observed using hObs
  have hEvent := fun lane hl => (observed lane hl).1
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hReceives := hOrd.shuffle_value hX hBlock hg (fun _ => pc) .idx (fun lane => b32 (part lane))
    recv (fun _ => 31) (fun _ => 31) ok hEvent
  refine ⟨fun lane => next (setReg (state lane) 7234 (recv lane)),
    (hOrd.shuffle (fun _ => pc) .idx (fun lane => b32 (part lane))
      recv (fun _ => 31) (fun _ => 31) ok hEvent).2, ?_⟩
  intro lane hl
  have hv : recv lane = b32 (part 31) := by
    simpa only [shflSource_idx lane (by decide : 31 < 32)] using (hReceives lane hl).1
  have hNew := (hAt lane hl).set (r := 7234) (v := recv lane) (by simp)
  have hTotal : (next (setReg (state lane) 7234 (recv lane))).regs 7234 =
      some (b32 (part 31)) := hNew.2.2.2.2.1.trans (congrArg some hv)
  exact ⟨hNew.mono ⟨hTotal, hNew.2.2.2.2.2⟩, (observed lane hl).2,
    fun r hr => by simp [next, setReg, hr]⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
