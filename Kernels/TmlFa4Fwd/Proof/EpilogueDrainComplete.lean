-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainStart
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainSearch
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainWarpFinish
public import Kernels.TmlFa4Fwd.Proof.Thread.EpilogueLaterDrainCuQRead
import all Kernels.TmlFa4Fwd.Proof.Thread.OutputLaterDrainCuQReadClass

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof

noncomputable section

private theorem lastOfSuffix {events : List Event} {i : Nat} {e : Event}
    (hLast : (events.drop i).getLast? = some e) : events.getLast? = some e := by
  rw [List.getLast?_drop] at hLast
  split at hLast
  · cases hLast
  · exact hLast

private theorem finishDrainPoint {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g cta first shuffles votes : Nat} (hg : g < l.threads) (hc : cta < l.grid)
    (hFirst : first ≤ p.batch) (hLow : tilePrefix p first * p.heads ≤ cta)
    (hHigh : first < p.batch → cta < tilePrefix p (min p.batch (first + 31)) * p.heads)
    (cur : DrainWarpPoint l X g 3086 (drainFinishFacts p first cta) shuffles votes) :
    ∀ lane < 32, (X.tr (warpLane l g lane)).getLast? = some ⟨9205, .exit⟩ := by
  rcases drainWarpFinishGroup hp hX hg hc hFirst hLow hHigh cur.ordinals
    (fun lane hl => ⟨cur.state lane, cur.atState lane hl, cur.suffix lane hl⟩) with
    ⟨_, hExit⟩ | ⟨selected, _, _, _, _, _, hExit⟩
  · intro lane hl
    exact lastOfSuffix (i := cur.pos lane) (by rw [hExit lane hl]; rfl)
  · intro lane hl
    apply lastOfSuffix (i := cur.pos lane)
    rw [hExit lane hl]
    by_cases hz : selected - first = 0 <;> simp [drainTerminalEvents, hz]

/-- A warp-13 output trace for a valid CTA continues from writeback through the bounded
drain search. Every actual lane trace ends at the kernel exit. -/
theorem drainCompleteFromWriteback {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g cta batch head tile : Nat} (hg : g < l.threads) (hc : cta < l.grid)
    (hTotal : cta < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hh : head < p.heads) (htile : 256 * tile < p.qLength batch)
    {pos : Nat → Nat} {state : Nat → TState} {shuffles votes : Nat}
    (hOrd : WarpOrdinals l X g pos shuffles votes)
    (hAt : ∀ lane < 32, At (state lane) 2958 (writebackEntry p l batch head tile))
    (hGate : ∀ lane < 32, (state lane).regs 307 = some (.pred (p.batch < lane)))
    (hIndex : ∀ lane < 32, (state lane).regs 1201 = some (b32 lane))
    (hBase : ∀ lane < 32, (state lane).regs 7506 = some (b64 p.cuQBase))
    (hActive : ∀ lane < 32, (state lane).regs 268 =
      some (.pred (!decide (laneHasRequest lane p.batch))))
    (hScheduler : ∀ lane < 32, Holds (state lane).regs
      [(7138, b32 p.heads), (1072, b32 cta), (1062, b32 13), (7147, b32 p.batch)])
    (hRun : ∀ lane < 32, Run kernel Assumptions.all l (warpLane l g lane) (state lane)
      ((X.tr (warpLane l g lane)).drop (pos lane)) none)
    (hProtected : DrainCuQProtected p X) :
    (∀ lane < 32, (X.tr (warpLane l g lane)).getLast? = some ⟨9205, .exit⟩) ∧
      Thread.OutputLaterDrainCuQWords p l X g := by
  obtain ⟨atUp, after, hFirstOrd, hScan, hGuards, hKeep, hDown⟩ :=
    drainStartFromWriteback hp hX hg hb hh htile hOrd hAt hGate hIndex hBase hActive hRun
      (fun lane _ hLane => hProtected lane hLane)
  have hFrame (lane : Nat) (hl : lane < 32) : Holds (after lane).regs
      [(7138, b32 p.heads), (1072, b32 cta), (1062, b32 13), (1201, b32 lane),
      (7147, b32 p.batch), (7506, b64 p.cuQBase)] := by
    have keep (r : Nat) (hr : r ∈ drainPersistent) {v : Value}
        (h : (state lane).regs r = some v) : (after lane).regs r = some v :=
      (hKeep lane hl r hr).trans h
    have hs := hScheduler lane hl
    exact ⟨keep 7138 (by decide) hs.1, keep 1072 (by decide) hs.2.1,
      keep 1062 (by decide) hs.2.2.1, keep 1201 (by decide) (hIndex lane hl),
      keep 7147 (by decide) hs.2.2.2.1, keep 7506 (by decide) (hBase lane hl), trivial⟩
  have hAdvance (lane : Nat) (hl : lane < 32) {j : Nat} {a : Acc} {bytes : List (Option Byte)}
      (h : Thread.OutputLaterDrainCuQRead X (warpLane l g lane, j) a bytes) : atUp lane ≤ j := by
    obtain ⟨e, he, hPc⟩ := hDown lane hl
    have hOrd := h.afterFirstShuffle hX he hPc
    omega
  have hScanCovered {next : Nat → Nat} {j lane : Nat} (hl : lane < 32)
      (hNext : WarpOrdinals l X g next (shuffles + 1 + 6) votes)
      (hPos : next = fun lane => atUp lane + 6)
      (hLen : next lane ≤ (X.tr (warpLane l g lane)).length)
      {a : Acc} {bytes : List (Option Byte)}
      (h : Thread.OutputLaterDrainCuQRead X (warpLane l g lane, j) a bytes) : next lane ≤ j := by
    by_contra! hBefore
    have hCount : ((X.tr (warpLane l g lane)).take (next lane)).countP Execution.isShfl =
        ((X.tr (warpLane l g lane)).take (atUp lane)).countP Execution.isShfl +
          (next lane - atUp lane) := by
      rw [hNext.shfl lane hl, hFirstOrd.shfl lane hl, hPos]
      simp
    have he : X.get (warpLane l g lane, j) = some ⟨3043, .rd a bytes⟩ := h.get_eq
    have hShfl := getIsShuffleBetween hLen (hAdvance lane hl h) hBefore hCount he
    exact Bool.noConfusion hShfl
  let limit := tilePrefix p (min p.batch 31) * p.heads
  have hGroup := drainFirstGroup hp hX hg hc hFirstOrd hScan hGuards hFrame
  change if cta < limit then _ else _ at hGroup
  by_cases hHit : cta < limit
  · rw [ite_eq_left hHit] at hGroup
    obtain ⟨cur, hPos⟩ := hGroup
    have hLow : tilePrefix p 0 * p.heads ≤ cta := by simp [tilePrefix]
    refine ⟨finishDrainPoint hp hX hg hc (Nat.zero_le p.batch) hLow (fun _ => hHit) cur, ?_⟩
    intro lane hl j a bytes hRead
    have hLen : cur.pos lane ≤ (X.tr (warpLane l g lane)).length := by
      by_contra! hTooFar
      have hr := cur.suffix lane hl
      rw [List.drop_eq_nil_iff.mpr hTooFar.le] at hr
      cases hr
    have hAfter := hScanCovered hl cur.ordinals hPos hLen hRead
    exact (Thread.noLaterCuQAfterSearch (cur.atState lane hl).1 (cur.suffix lane hl)
      hAfter hRead.get_eq).elim
  · rw [ite_eq_right hHit] at hGroup
    obtain ⟨cur, hPos⟩ := hGroup
    obtain ⟨terminal, hCovered⟩ :=
      drainRemainingGroups hp hX hg hc hTotal hProtected (Nat.le_of_not_gt hHit) cur
    refine ⟨finishDrainPoint hp hX hg hc terminal.first_lt.le terminal.low
      (fun _ => terminal.high) terminal.cursor, ?_⟩
    intro lane hl j a bytes hRead
    have hLen : cur.pos lane ≤ (X.tr (warpLane l g lane)).length := by
      by_contra! hTooFar
      have hr := cur.suffix lane hl
      rw [List.drop_eq_nil_iff.mpr hTooFar.le] at hr
      cases hr
    have hAfter := hScanCovered hl cur.ordinals hPos hLen hRead
    by_cases hInSearch : j < terminal.cursor.pos lane
    · exact hCovered lane hl j a bytes hAfter hInSearch hRead
    · exact (Thread.noLaterCuQAfterSearch (terminal.cursor.atState lane hl).1
        (terminal.cursor.suffix lane hl) (Nat.le_of_not_gt hInSearch) hRead.get_eq).elim

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
