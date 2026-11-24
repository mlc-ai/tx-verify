-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueExitLoop
public import Kernels.TmlFa4Fwd.Proof.EpilogueLocalRun
public import Lemmas.Flow.ContinuingEvent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The first scan's two totals and the scheduler inputs that remain available after it. -/
def drainFirstRouteInputs (p : Params) (l : Launch) (g count lanePrefix laneTiles cta : Nat) :
    List (Nat × Value) :=
  [(7234, b32 count), (7138, b32 p.heads), (1072, b32 cta), (7233, b32 lanePrefix),
   (7232, b32 laneTiles), (1062, b32 13), (1201, b32 (laneOf l g)),
   (7147, b32 p.batch), (7506, b64 p.cuQBase)]

/-- The first group's end test either selects that group or initializes the repeated scan.
Both routes retain the exact local path in the full model. -/
theorem drainFirstRouteLocal {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g count lanePrefix laneTiles cta : Nat} {t : TState}
    (hCount : count < 2 ^ 31) (hCTA : cta < 2 ^ 31) (hEnd : count * p.heads < 2 ^ 31)
    (ht : At t 3025 (drainFirstRouteInputs p l g count lanePrefix laneTiles cta)) :
    (cta < count * p.heads ∧ ∃ u,
      At u 3086 [(7235, b32 0), (7147, b32 p.batch), (7234, b32 count), (7138, b32 p.heads),
        (7236, b32 (count * p.heads)), (7233, b32 lanePrefix), (1072, b32 cta),
        (7232, b32 laneTiles), (1062, b32 13)] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      ∀ r ∉ [7236, 316, 7235, 1210, 7230], u.regs r = t.regs r) ∨
    (count * p.heads ≤ cta ∧ ∃ u,
      At u 3032 [(7235, b32 0), (1210, b32 (cta + 1)), (1201, b32 (laneOf l g)),
        (7147, b32 p.batch), (7506, b64 p.cuQBase), (7230, b32 (count * p.heads)),
        (1072, b32 cta), (7138, b32 p.heads), (1062, b32 13)] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      ∀ r ∉ [7236, 316, 7235, 1210, 7230], u.regs r = t.regs r) := by
  let limit := count * p.heads
  have get {r : Nat} {v : Value}
      (hr : (r, v) ∈ drainFirstRouteInputs p l g count lanePrefix laneTiles cta) :
      t.regs r = some v := holds_mem ht.2.2.2.2 hr
  have hArgs : At t 3025 [(7234, b32 count), (7138, b32 p.heads), (1072, b32 cta)] :=
    ht.mono ⟨get (by simp [drainFirstRouteInputs]), get (by simp [drainFirstRouteInputs]),
      get (by simp [drainFirstRouteInputs]), trivial⟩
  obtain ⟨v, hTest, hv⟩ := drainFirstLimit l g hCount hp.heads_signed hCTA hEnd t hArgs
  have hPC := ht.1
  obtain ⟨hTestAll, hTestFrame, _, _⟩ := epilogueLinearRun (F := [7236, 316, 7235])
    (t := t) (n := 3) (by omega) (by omega) (by
      intro pc hlo hhi
      rcases (show pc = 3025 ∨ pc = 3026 by omega) with rfl | rfl
      · exact ⟨_, Flow.code_3025, rfl, fun _ h => h, by simp [writesRegs]⟩
      · exact ⟨_, Flow.code_3026, rfl, fun _ h => h, by simp [writesRegs]⟩) (by
      intro _
      rw [hPC]
      exact ⟨_, Flow.code_3027, by simp [writesRegs]⟩) ht.2.1 ht.2.2.1 hTest
  obtain ⟨w, hBranch, hw⟩ := drainBranchRun 1 l g v (decide (cta < limit)) hv
    hv.2.2.2.2.2.1
  have hvPC := hv.1
  obtain ⟨hBranchAll, hBranchFrame, _, _⟩ := epilogueLinearRun (F := [])
    (t := v) (n := 1) (by omega) (by omega) (by omega) (by
      intro _
      rw [hvPC]
      exact ⟨_, Flow.code_3028, by simp [writesRegs]⟩) hv.2.1 hv.2.2.1 hBranch
  have hFrame (r : Nat) (hr : r ∉ [7236, 316, 7235]) : w.regs r = t.regs r :=
    (hBranchFrame r (by simp)).trans (hTestFrame r hr)
  have hAfter := (run_rtg hTestAll).trans (run_rtg hBranchAll)
  by_cases hC : cta < limit
  · have hwPC : w.pc = 3086 := by simpa [drainBranchSite, hC] using hw.1
    have keep {r : Nat} {v : Value} (hn : r ∉ [7236, 316, 7235])
        (hr : (r, v) ∈ drainFirstRouteInputs p l g count lanePrefix laneTiles cta) :
        w.regs r = some v := (hFrame r hn).trans (get hr)
    refine .inl ⟨hC, w, ⟨hwPC, hw.2.1, hw.2.2.1, hw.2.2.2.1, ?_⟩, hAfter, ?_⟩
    · exact ⟨hw.2.2.2.2.2.2.1, keep (by decide) (by simp [drainFirstRouteInputs]),
        keep (by decide) (by simp [drainFirstRouteInputs]),
        keep (by decide) (by simp [drainFirstRouteInputs]), hw.2.2.2.2.1,
        keep (by decide) (by simp [drainFirstRouteInputs]),
        keep (by decide) (by simp [drainFirstRouteInputs]),
        keep (by decide) (by simp [drainFirstRouteInputs]),
        keep (by decide) (by simp [drainFirstRouteInputs]), trivial⟩
    · intro r hr
      exact hFrame r (fun hm => hr (by simp_all))
  · have hwPC : w.pc = 3029 := by simpa [drainBranchSite, hC] using hw.1
    have hInit : At w 3029 [(1072, b32 cta), (7236, b32 limit)] :=
      ⟨hwPC, hw.2.1, hw.2.2.1, hw.2.2.2.1,
        (hFrame 1072 (by decide)).trans (get (by simp [drainFirstRouteInputs])),
        hw.2.2.2.2.1, trivial⟩
    obtain ⟨u, hEnter, hu⟩ := enterDrainSearch l g (by omega) w hInit
    obtain ⟨hEnterAll, hEnterFrame, _, _⟩ := epilogueLinearRun (F := [1210, 7235, 7230])
      (t := w) (n := 3) (by omega) (by omega) (by
        intro pc hlo hhi
        rcases (show pc = 3029 ∨ pc = 3030 by omega) with rfl | rfl
        · exact ⟨_, Flow.code_3029, rfl, fun _ h => h, by simp [writesRegs]⟩
        · exact ⟨_, Flow.code_3030, rfl, fun _ h => h, by simp [writesRegs]⟩) (by
        intro _
        rw [hwPC]
        exact ⟨_, Flow.code_3031, by simp [writesRegs]⟩) hw.2.1 hw.2.2.1 hEnter
    have frame (r : Nat) (hr : r ∉ [7236, 316, 7235, 1210, 7230]) : u.regs r = t.regs r :=
      (hEnterFrame r (fun hm => hr (by simp_all))).trans (hFrame r (fun hm => hr (by simp_all)))
    have keep {r : Nat} {v : Value} (hn : r ∉ [7236, 316, 7235, 1210, 7230])
        (hr : (r, v) ∈ drainFirstRouteInputs p l g count lanePrefix laneTiles cta) :
        u.regs r = some v := (frame r hn).trans (get hr)
    refine .inr ⟨Nat.le_of_not_gt hC, u, hu.mono ?_, hAfter.trans (run_rtg hEnterAll), frame⟩
    exact ⟨hu.2.2.2.2.2.1, hu.2.2.2.2.1,
      keep (by decide) (by simp [drainFirstRouteInputs]),
      keep (by decide) (by simp [drainFirstRouteInputs]),
      keep (by decide) (by simp [drainFirstRouteInputs]), hu.2.2.2.2.2.2.1,
      keep (by decide) (by simp [drainFirstRouteInputs]),
      keep (by decide) (by simp [drainFirstRouteInputs]),
      keep (by decide) (by simp [drainFirstRouteInputs]), trivial⟩

/-- The first group's end test either selects that group or initializes the repeated scan.
Both routes are local steps in the full model, retaining the incoming event suffix. -/
theorem drainFirstRoute {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g count lanePrefix laneTiles cta : Nat} {t : TState} {events : List Event}
    (hCount : count < 2 ^ 31) (hCTA : cta < 2 ^ 31) (hEnd : count * p.heads < 2 ^ 31)
    (ht : At t 3025 (drainFirstRouteInputs p l g count lanePrefix laneTiles cta))
    (hRun : Run kernel Assumptions.all l g t events none) :
    (cta < count * p.heads ∧ ∃ u,
      At u 3086 [(7235, b32 0), (7147, b32 p.batch), (7234, b32 count), (7138, b32 p.heads),
        (7236, b32 (count * p.heads)), (7233, b32 lanePrefix), (1072, b32 cta),
        (7232, b32 laneTiles), (1062, b32 13)] ∧
      Run kernel Assumptions.all l g u events none ∧
      ∀ r ∉ [7236, 316, 7235, 1210, 7230], u.regs r = t.regs r) ∨
    (count * p.heads ≤ cta ∧ ∃ u,
      At u 3032 [(7235, b32 0), (1210, b32 (cta + 1)), (1201, b32 (laneOf l g)),
        (7147, b32 p.batch), (7506, b64 p.cuQBase), (7230, b32 (count * p.heads)),
        (1072, b32 cta), (7138, b32 p.heads), (1062, b32 13)] ∧
      Run kernel Assumptions.all l g u events none ∧
      ∀ r ∉ [7236, 316, 7235, 1210, 7230], u.regs r = t.regs r) := by
  rcases drainFirstRouteLocal hp hCount hCTA hEnd ht with h | h
  · obtain ⟨hc,u,hu,hr,hFrame⟩ := h
    exact .inl ⟨hc,u,hu,hRun.after_local hr,hFrame⟩
  · obtain ⟨hc,u,hu,hr,hFrame⟩ := h
    exact .inr ⟨hc,u,hu,hRun.after_local hr,hFrame⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
