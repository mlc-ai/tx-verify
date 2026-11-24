-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainGroup
public import Kernels.TmlFa4Fwd.Proof.SchedulerProtection
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainWarpNext
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainFinish

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof

noncomputable section

/-- The recorded later-drain CuQ lookups between two warp cursors have in-range addresses. -/
def DrainCuQInterval (p : Params) (l : Launch) (X : Execution) (g : Nat)
    (start stop : Nat → Nat) : Prop :=
  ∀ lane < 32, ∀ j a bytes, start lane ≤ j → j < stop lane →
    X.get (warpLane l g lane, j) = some ⟨3043, .rd a bytes⟩ →
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase + 4 * index), size := 4}

/-- One pass through a later 31-request group reaches its next work boundary. -/
theorem drainLaterGroupWarp {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g first cta shuffles votes : Nat} (hg : g < l.threads) (hc : cta < l.grid)
    (hMore : first + 31 < p.batch) (hProtected : DrainCuQProtected p X)
    (cur : DrainWarpPoint l X g 3032 (drainNextFacts p l g first cta) shuffles votes) :
    let newFirst := first + 31
    let limit := tilePrefix p (min p.batch (newFirst + 31)) * p.heads
    if cta < limit then
      ∃ next : DrainWarpPoint l X g 3086 (drainFinishFacts p newFirst cta) (shuffles + 7) votes,
        DrainCuQInterval p l X g cur.pos next.pos
    else
      ∃ next : DrainWarpPoint l X g 3032 (drainNextFacts p l g newFirst cta) (shuffles + 7) votes,
        DrainCuQInterval p l X g cur.pos next.pos := by
  let newFirst := first + 31
  let base := tilePrefix p newFirst * p.heads
  let limit := tilePrefix p (min p.batch (newFirst + 31)) * p.heads
  have hBase : tilePrefix p (min p.batch (first + 31)) * p.heads = base := by
    rw [Nat.min_eq_right (Nat.le_of_lt hMore)]
  have hAt := fun lane hl => cur.atState lane hl
  simp only [drainNextFacts, hBase] at hAt
  obtain ⟨pos, state, hOrd, hRound, hGuards, hFrame, hPosition, hRead⟩ :=
    drainWarpNext hp hX hg hMore cur.ordinals hAt cur.suffix (fun lane _ => hProtected _)
  obtain ⟨_, hO5, hS⟩ := hRound.scan hp hX hg (Nat.le_of_lt hMore) hOrd hGuards
  obtain ⟨v, hO6, hV⟩ := drainTotalObserved hp hX hg true hO5
    (fun lane hl => (hS lane hl).1) (fun lane hl => (hS lane hl).2.1)
  let cursor := fun lane => pos lane + 6
  have hCount : tilePrefix p newFirst + drainPrefix p newFirst 31 =
      tilePrefix p (min p.batch (newFirst + 31)) :=
    groupTiles_eq p (Nat.le_of_lt hMore) (show 32 ≤ 32 by decide)
  have hRoute (lane : Nat) (hl : lane < 32) :
      ∃ u, At u (if limit ≤ cta then 3032 else 3086) [(7230, b32 limit), (7236, b32 limit)] ∧
        (∀ r ∉ [7236, 330, 7230], u.regs r = (v lane).regs r) ∧
        Run kernel Assumptions.all l (warpLane l g lane) u
          ((X.tr (warpLane l g lane)).drop (cursor lane)) none := by
    have keep (r : Nat) (hr : r ∈ drainRoundPersistent) (hNe : r ≠ 7234) :
        (v lane).regs r = (state lane).regs r :=
      ((hV lane hl).2.2 r hNe).trans ((hS lane hl).2.2 r hr)
    have hd := (hV lane hl).1
    have raw {r : Nat} {x : Value}
        (hm : (r, x) ∈ drainLaterGroup p l (warpLane l g lane) newFirst base (cta + 1) cta) :
        (state lane).regs r = some x := holds_mem (hFrame lane hl) hm
    have ht : At (v lane) 3082 [(7230, b32 base), (7234, b32 (drainPrefix p newFirst 31)),
        (7138, b32 p.heads), (1072, b32 cta)] := by
      refine hd.mono ⟨(keep 7230 (by decide) (by decide)).trans ?_, hd.2.2.2.2.1,
        (keep 7138 (by decide) (by decide)).trans ?_,
        (keep 1072 (by decide) (by decide)).trans ?_, trivial⟩
      all_goals exact raw (by simp [drainLaterGroup, drainLaterCommon, newFirst])
    exact drainLaterRoute hp hc hCount ht (hV lane hl).2.1
  have saved (lane : Nat) (hl : lane < 32) {u : TState}
      (hKeep : ∀ r ∉ [7236, 330, 7230], u.regs r = (v lane).regs r) (r : Nat)
      (hr : r ∈ drainRoundPersistent) (hNe : r ∉ [7234, 7236, 330, 7230]) :
      u.regs r = (state lane).regs r := by
    exact (hKeep r (fun h => hNe (List.mem_cons_of_mem _ h))).trans
      (((hV lane hl).2.2 r (fun h => hNe (by simp [h]))).trans ((hS lane hl).2.2 r hr))
  have hCovered : DrainCuQInterval p l X g cur.pos cursor := by
    intro lane hl j a bytes hFrom hUntil he
    let thread := warpLane l g lane
    let x := first + 31 + lane
    let start := if x ≤ p.batch then cur.pos lane + 1 else cur.pos lane
    have hPos : pos lane = start + 1 := hPosition lane hl
    have hLen : cursor lane ≤ (X.tr thread).length := by
      obtain ⟨_, _, _, hr⟩ := hRoute lane hl
      by_contra! hBad
      rw [List.drop_eq_nil_of_le hBad.le] at hr
      cases hr
    have hStartCount : ((X.tr thread).take start).countP Execution.isShfl = shuffles := by
      by_cases hLive : x ≤ p.batch
      · have hE := hRead lane hl hLive
        simp only [start, ite_eq_left hLive, List.take_add_one]
        rw [show (X.tr thread)[cur.pos lane]? = _ from hE]
        simpa [Execution.isShfl] using cur.ordinals.shfl lane hl
      · simpa only [start, ite_eq_right hLive] using cur.ordinals.shfl lane hl
    have hEndCount : ((X.tr thread).take (cursor lane)).countP Execution.isShfl =
        ((X.tr thread).take start).countP Execution.isShfl + (cursor lane - start) := by
      rw [hStartCount]
      have h := hO6.shfl lane hl
      change ((X.tr thread).take (cursor lane)).countP Execution.isShfl = shuffles + 7 at h
      rw [h]
      dsimp [cursor]
      omega
    by_cases hj : start ≤ j
    · have hShfl := getIsShuffleBetween hLen hj hUntil hEndCount he
      cases hShfl
    · have hLive : x ≤ p.batch := by
        by_contra hn
        exact hj (by simpa [start, hn] using hFrom)
      have eq : j = cur.pos lane := by simp only [start, ite_eq_left hLive] at hj; omega
      rw [eq] at he
      exact ⟨x, hLive, (Kind.rd.inj (congrArg Event.kind
        (Option.some.inj (he.symm.trans (hRead lane hl hLive))))).1⟩
  change if cta < limit then _ else _
  by_cases hHit : cta < limit
  · rw [ite_eq_left hHit]
    have hNext (lane : Nat) (hl : lane < 32) :
        ∃ u, At u 3086 ((drainFinishFacts p newFirst cta) lane) ∧
          Run kernel Assumptions.all l (warpLane l g lane) u
            ((X.tr (warpLane l g lane)).drop (cursor lane)) none := by
      obtain ⟨u, hu, hKeep, hr⟩ := hRoute lane hl
      rw [ite_eq_right (Nat.not_le_of_gt hHit)] at hu
      refine ⟨u, hu.mono ?_, hr⟩
      have hd := (hV lane hl).1
      have hk {r : Nat} {x : Value} (rr : r ∈ drainRoundPersistent)
          (rn : r ∉ [7234, 7236, 330, 7230])
          (hv : (state lane).regs r = some x) : u.regs r = some x :=
        (saved lane hl hKeep r rr rn).trans hv
      have raw {r : Nat} {x : Value}
          (hm : (r, x) ∈ drainLaterGroup p l (warpLane l g lane) newFirst base (cta + 1) cta) :
          (state lane).regs r = some x := holds_mem (hFrame lane hl) hm
      have tiles : (state lane).regs 7232 = some (b32 (groupLaneTiles p newFirst lane)) := by
        have hState := (hRound.atWord lane hl).2.2.2.2.2.1
        change (state lane).regs 7232 = some (b32 (prefixWindow (groupLaneTiles p newFirst) 1 lane))
          at hState
        simpa only [prefixWindow_one] using hState
      refine ⟨hk (r := 7235) (by decide) (by decide) ?_, hk (r := 7147) (by decide) (by decide) ?_,
        (hKeep 7234 (by decide)).trans hd.2.2.2.2.1, hk (r := 7138) (by decide) (by decide) ?_,
        hu.2.2.2.2.2.1, (hKeep 7233 (by decide)).trans hd.2.2.2.2.2.1,
        hk (r := 1072) (by decide) (by decide) ?_, hk (by decide) (by decide) tiles,
        hk (r := 1062) (by decide) (by decide) ?_, trivial⟩
      all_goals exact raw (by simp [drainLaterGroup, drainLaterCommon, newFirst])
    obtain ⟨next, hNextPos⟩ := DrainWarpPoint.ofLanes hO6 (v 0) hNext
    exact ⟨next, hNextPos.symm ▸ hCovered⟩

  · rw [ite_eq_right hHit]
    have hNext (lane : Nat) (hl : lane < 32) :
        ∃ u, At u 3032 ((drainNextFacts p l g newFirst cta) lane) ∧
          Run kernel Assumptions.all l (warpLane l g lane) u
            ((X.tr (warpLane l g lane)).drop (cursor lane)) none := by
      obtain ⟨u, hu, hKeep, hr⟩ := hRoute lane hl
      rw [ite_eq_left (Nat.le_of_not_gt hHit)] at hu
      refine ⟨u, hu.mono ?_, hr⟩
      unfold drainNextFacts drainLaterEntry drainLaterCommon
      have keep {r : Nat} {x : Value} (hR : r ∈ drainRoundPersistent)
          (hNot : r ∉ [7234, 7236, 330, 7230])
          (hm : (r, x) ∈ drainLaterGroup p l (warpLane l g lane) newFirst base (cta + 1) cta) :
          u.regs r = some x :=
        (saved lane hl hKeep r hR hNot).trans (holds_mem (hFrame lane hl) hm)
      refine ⟨keep (r := 7235) (by decide) (by decide) ?_,
        keep (r := 1210) (by decide) (by decide) ?_,
        keep (r := 1201) (by decide) (by decide) ?_, keep (r := 7147) (by decide) (by decide) ?_,
        keep (r := 7506) (by decide) (by decide) ?_, hu.2.2.2.2.1,
        keep (r := 1072) (by decide) (by decide) ?_, keep (r := 7138) (by decide) (by decide) ?_,
        keep (r := 1062) (by decide) (by decide) ?_, trivial⟩
      all_goals simp [drainLaterGroup, drainLaterCommon, newFirst]
    obtain ⟨next, hNextPos⟩ := DrainWarpPoint.ofLanes hO6 (v 0) hNext
    exact ⟨next, hNextPos.symm ▸ hCovered⟩

/-- The group's half-open work interval contains the CTA's assigned tile. -/
structure DrainTerminal (p : Params) (l : Launch) (X : Execution) (g cta votes : Nat) where
  first : Nat
  shuffles : Nat
  first_lt : first < p.batch
  low : tilePrefix p first * p.heads ≤ cta
  high : cta < tilePrefix p (min p.batch (first + 31)) * p.heads
  cursor : DrainWarpPoint l X g 3086 (drainFinishFacts p first cta) shuffles votes

/-- Each backedge consumes another 31 requests, so the repeated search reaches the
group that contains the assigned CTA. -/
theorem drainRemainingGroups {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g cta votes : Nat} (hg : g < l.threads) (hc : cta < l.grid)
    (hTotal : cta < tilePrefix p p.batch * p.heads) (hProtected : DrainCuQProtected p X)
    {first shuffles : Nat}
    (hExhausted : tilePrefix p (min p.batch (first + 31)) * p.heads ≤ cta)
    (cur : DrainWarpPoint l X g 3032 (drainNextFacts p l g first cta) shuffles votes) :
    ∃ terminal : DrainTerminal p l X g cta votes,
      DrainCuQInterval p l X g cur.pos terminal.cursor.pos := by
  suffices all : ∀ fuel first shuffles, p.batch - first = fuel →
      tilePrefix p (min p.batch (first + 31)) * p.heads ≤ cta →
      ∀ cur : DrainWarpPoint l X g 3032 (drainNextFacts p l g first cta) shuffles votes,
        ∃ terminal : DrainTerminal p l X g cta votes,
          DrainCuQInterval p l X g cur.pos terminal.cursor.pos by
    exact all _ first shuffles rfl hExhausted cur
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro first shuffles hFuel hPast cur
    have hMore : first + 31 < p.batch := by
      by_contra! h
      rw [Nat.min_eq_left h] at hPast
      omega
    have hLow : tilePrefix p (first + 31) * p.heads ≤ cta := by
      simpa only [Nat.min_eq_right (Nat.le_of_lt hMore)] using hPast
    let limit := tilePrefix p (min p.batch (first + 31 + 31)) * p.heads
    have h := drainLaterGroupWarp hp hX hg hc hMore hProtected cur
    change if cta < limit then _ else _ at h
    by_cases hHit : cta < limit
    · rw [ite_eq_left hHit] at h
      obtain ⟨terminal, hCovered⟩ := h
      exact ⟨⟨first + 31, shuffles + 7, hMore, hLow, hHit, terminal⟩, hCovered⟩
    · rw [ite_eq_right hHit] at h
      obtain ⟨next, hCovered⟩ := h
      obtain ⟨terminal, hRest⟩ := ih (p.batch - (first + 31)) (by omega) (first + 31)
        (shuffles + 7) rfl (Nat.le_of_not_gt hHit) next
      refine ⟨terminal, fun lane hl j a bytes hStart hStop he => ?_⟩
      by_cases hEarly : j < next.pos lane
      · exact hCovered lane hl j a bytes hStart hEarly he
      · exact hRest lane hl j a bytes (Nat.le_of_not_gt hEarly) hStop he

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
