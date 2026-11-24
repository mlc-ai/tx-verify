-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.BarrierCursor
public import Kernels.TmlFa4Fwd.Proof.NamedBarrierSites
public import Kernels.TmlFa4Fwd.Proof.SoftmaxNamedBarrierIds
public import Kernels.TmlFa4Fwd.Proof.FirstStatsOrdinal
public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarriers

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow Prologue

noncomputable section

namespace Scores

/-- The four kinds of statistics handoff in the softmax trace. -/
inductive Round where
  | first
  | biased
  | plain
  | final
  deriving DecidableEq

/-- The values at the statistics rendezvous are tracked separately from successful acquires. -/
structure D where
  lastNotice : Option Round := none
  notices : Nat := 0
  barrier : Nat → Nat := fun _ => 0
  acquires : Nat := 0
  credits : Nat := 0
  exited : Bool := false

def initial : D := {}

def noticeRound (site : Nat) : Option Round :=
  match site with
  | 4397 => some .first
  | 5683 => some .biased
  | 6891 => some .plain
  | 7616 => some .final
  | _ => none

def notice (e : Event) : Option Round :=
  match e.kind with
  | .bar _ _ .arrive => noticeRound e.pc
  | _ => none

def acquired (e : Event) : Bool :=
  match e.kind with
  | .wait _ _ true true .cta => (Softmax.scorePollSites.map Prod.fst).contains e.pc
  | _ => false

/-- Successful acquires of the statistics buffer have their own per-lane cursor. -/
def creditAcquired (e : Event) : Bool :=
  match e.kind with
  | .wait _ _ true _ _ => [3420, 4874, 6558, 7463, 7738].contains e.pc
  | _ => false

/-- The publication cursor counts all rounds in their execution order. -/
def publishesStats (e : Event) : Bool := (notice e).isSome

def advance (d : D) (e : Event) : D :=
  let next := match notice e with
    | some round => { d with lastNotice := some round, notices := d.notices + 1 }
    | none =>
      if acquired e then { d with acquires := d.acquires + 1 } else
      match e.kind with
      | .exit => { d with exited := true }
      | _ => d
  { next with
    barrier := advanceBarrierCursor d.barrier e
    credits := d.credits + if creditAcquired e then 1 else 0 }

abbrev machine (l : Launch) (g : Nat) := observationMachine l g initial advance

theorem sound {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) (g : Nat) :
    (machine l g).Sound :=
  observationSound hp g initial advance

/-- The abstract state before an indexed softmax event. -/
def before (X : Execution) (i : EvId) : D :=
  ((X.tr i.1).take i.2).foldl advance initial

/-- The barrier cursor agrees with the consistency model's arrival ordinal. -/
theorem barrierOrdinal (X : Execution) (i : EvId) (id : Nat) :
    (before X i).barrier id = ((X.tr i.1).take i.2).countP (Execution.isBarId id) := by
  simp only [before]
  simpa [initial] using foldBarrierCursor D.barrier advance
    (fun _ _ => rfl) ((X.tr i.1).take i.2) initial id

theorem beforeCredits (X : Execution) (i : EvId) :
    (before X i).credits = ((X.tr i.1).take i.2).countP creditAcquired := by
  simp only [before]
  simpa [initial] using foldEventCount D.credits advance creditAcquired
    (fun _ _ => rfl) ((X.tr i.1).take i.2) initial

theorem beforeNotices (X : Execution) (i : EvId) :
    (before X i).notices = ((X.tr i.1).take i.2).countP publishesStats := by
  have step (d : D) (e : Event) :
      (advance d e).notices = d.notices + if publishesStats e then 1 else 0 := by
    unfold advance publishesStats
    cases h : notice e with
    | some r => rfl
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      split_ifs with hq
      · rfl
      · cases e.kind <;> rfl
  simp only [before]
  simpa [initial] using foldEventCount D.notices advance publishesStats step
    ((X.tr i.1).take i.2) initial

/-- A statistics notification, with the abstract round and count visible to consumers. -/
def Publishes (X : Execution) (i : EvId) (round : Round) : Prop :=
  ∃ e, X.get i = some e ∧ notice e = some round

private theorem noticeSite {e : Event} {round : Round} (h : notice e = some round) :
    e.pc ∈ Softmax.softmaxStatsSites ∧ ∃ id count, e.kind = .bar id count .arrive := by
  have hSource (site : Nat) : (noticeRound site).isSome ↔ site ∈ Softmax.softmaxStatsSites := by
    by_cases h : site = 4397 ∨ site = 5683 ∨ site = 6891 ∨ site = 7616
    · rcases h with rfl | rfl | rfl | rfl <;> decide
    · have hNot : site ≠ 4397 ∧ site ≠ 5683 ∧ site ≠ 6891 ∧ site ≠ 7616 := by tauto
      simp only [noticeRound, hNot.1, hNot.2.1, hNot.2.2.1, hNot.2.2.2,
        Softmax.softmaxStatsSites, List.mem_cons, List.not_mem_nil, or_false, eq_comm]
      all_goals simp_all
  cases hk : e.kind with
  | bar id count mode =>
    cases mode <;> simp only [notice, hk, reduceCtorEq] at h
    exact ⟨(hSource e.pc).mp (by simp [h]), id, count, rfl⟩
  | _ => all_goals simp [notice, hk] at h

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The notification identifies the producer's statistics rendezvous and advances its cursor. -/
theorem publishes {i : EvId} {round : Round} (h : Publishes X i round) :
    ∃ d, Transition (machine l i.1) X i.2
      (.bar (3 + warpIndex l i.1) (some 64) .arrive) (before X i) d ∧
        d.lastNotice = some round ∧ d.notices = (before X i).notices + 1 := by
  obtain ⟨e, he, hNotice⟩ := h
  obtain ⟨hSite, id, count, hKind⟩ := noticeSite hNotice
  have he' : X.get i = some ⟨e.pc, .bar id count .arrive⟩ := by
    have hEq : e = ⟨e.pc, .bar id count .arrive⟩ := by
      cases e
      exact congrArg (Event.mk _) hKind
    rwa [hEq] at he
  have hId := Softmax.actualSoftmaxStatsBarrierId hp hX hSite he'
  have hCount := (actualNamedBarrier hp hX he').2.1
  have hc : count = some 64 := by
    simp only [Softmax.softmaxStatsSites, List.mem_cons, List.not_mem_nil, or_false] at hSite
    rcases hSite with h | h | h | h <;> rwa [h] at hCount
  rw [hId, hc] at hKind
  refine ⟨advance _ e, ⟨e, he, hKind, observationAfter .., rfl⟩, ?_, ?_⟩ <;>
    simp [advance, hNotice]

private theorem publicationMarker {g j : Nat} {e : Event} (he : X.get (g,j) = some e)
    (hw : warpIndex l g < 8) :
    publishesStats e = true ↔ Execution.isBarId (3 + warpIndex l g) e = true := by
  constructor
  · intro hm
    obtain ⟨round, hn⟩ := Option.isSome_iff_exists.mp hm
    obtain ⟨_, ⟨f, hf, hk, _, _⟩, _⟩ := publishes hp hX (i := (g,j)) ⟨e, he, hn⟩
    rw [Option.some.inj (he.symm.trans hf)]
    simp [Execution.isBarId, hk]
  · intro hm
    obtain ⟨pc, count, mode, rfl⟩ := NamedBar.isBarId_form hm
    obtain ⟨hSite, hCount, hMode, _, _⟩ := actualNamedBarrier hp hX he
    have hId : 3 + warpIndex l g < 11 := by omega
    have hC : count = some 64 := by
      have h := actualNamedBarrierCountById hp hX he
      simpa [countOfBarrierId, hId, show 3 + warpIndex l g ≠ 0 by omega,
        show 3 + warpIndex l g ≠ 2 by omega] using h
    have hStats := count64StatsSites hSite (hCount.symm.trans hC)
    have hRole := namedStatsRole hp hX he hStats
    rcases hStats with hS | ⟨stage, hs⟩
    · simp only [Softmax.softmaxStatsSites, List.mem_cons, List.not_mem_nil, or_false] at hS
      rcases hS with rfl | rfl | rfl | rfl <;> subst mode <;> rfl
    · have hPc : 7747 ≤ pc ∧ pc < 9205 := by
        fin_cases stage <;> simp [Correction.correctionStatsSites] at hs <;> omega
      rcases hRole with h | h
      · omega
      · split_ifs at h <;> omega

/-- A softmax lane's statistics cursor is its named rendezvous generation at every prefix. -/
theorem notificationOrdinal {g j : Nat} (hw : warpIndex l g < 8) :
    (before X (g,j)).notices = (before X (g,j)).barrier (3 + warpIndex l g) := by
  rw [beforeNotices, barrierOrdinal]
  apply List.countP_congr
  intro e hm
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
  have hj := (List.getElem?_eq_some_iff.mp hk).1
  simp only [List.length_take] at hj
  rw [List.getElem?_take_of_lt (by omega)] at hk
  exact publicationMarker hp hX (g := g) (j := k) hk hw

/-- A softmax lane's rendezvous on its statistics barrier is a publication. -/
theorem publishesAtStatisticsBarrier {g j : Nat} {count : Option Nat} {mode : BarMode}
    (hw : warpIndex l g < 8) (h : BarrierArrival X (g,j) (3 + warpIndex l g) count mode) :
    ∃ round, Publishes X (g,j) round := by
  obtain ⟨e, he, hk⟩ := h
  have hm := (publicationMarker hp hX he hw).mpr (by simp [Execution.isBarId, hk])
  obtain ⟨round, hRound⟩ := Option.isSome_iff_exists.mp hm
  exact ⟨round, e, he, hRound⟩

/-- The arriving side of every statistics rendezvous is the matching softmax producer. -/
theorem statisticsArrivalPublishes {g j barrier : Nat} {count : Option Nat}
    (hId : 3 ≤ barrier ∧ barrier < 11) (h : BarrierArrival X (g,j) barrier count .arrive) :
    barrier = 3 + warpIndex l g ∧ warpIndex l g < 8 ∧ ∃ round, Publishes X (g,j) round := by
  obtain ⟨⟨pc,kind⟩, he, hk⟩ := h
  change kind = _ at hk
  subst kind
  obtain ⟨hSite, hCount, hMode, _, _⟩ := actualNamedBarrier hp hX he
  have hC : count = some 64 := by
    have hActual := actualNamedBarrierCountById hp hX he
    simpa [countOfBarrierId, hId.2, show barrier ≠ 0 by omega, show barrier ≠ 2 by omega]
      using hActual
  rcases count64StatsSites hSite (hCount.symm.trans hC) with hProd | ⟨stage, hCorr⟩
  · have heq := Softmax.actualSoftmaxStatsBarrierId hp hX hProd he
    have hw : warpIndex l g < 8 := by omega
    refine ⟨heq, hw, publishesAtStatisticsBarrier hp hX (count := count) (mode := .arrive) hw ?_⟩
    rw [← heq]
    exact ⟨_, he, rfl⟩
  · have hSync : namedBarrierMode pc = .sync := by
      fin_cases stage <;> simp [Correction.correctionStatsSites] at hCorr <;>
        rcases hCorr with rfl | rfl | rfl <;> decide
    rw [hSync] at hMode
    cases hMode

/-- The initial softmax notification joins the first generation for its warp. -/
theorem firstOrdinal {i : EvId} {members : Finset Nat} (h : Publishes X i .first)
    (hSources : NamedBar.Sources l X (some 64) members (3 + warpIndex l i.1)) :
    (before X i).barrier (3 + warpIndex l i.1) = 0 := by
  rw [barrierOrdinal]
  obtain ⟨e, he, hNotice⟩ := h
  have hPc : e.pc = 4397 := by
    obtain ⟨hs, _, _, hk⟩ := noticeSite hNotice
    simp only [Softmax.softmaxStatsSites, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with h | h | h | h <;> simp_all [notice, noticeRound]
  obtain ⟨_, ⟨f, hf, hKind, _, _⟩, _⟩ := publishes hp hX (i := i) ⟨e, he, hNotice⟩
  have hEq := Option.some.inj (he.symm.trans hf)
  rw [← hEq] at hKind
  have ee : e = ⟨4397, .bar (3 + warpIndex l i.1) (some 64) .arrive⟩ := by
    obtain ⟨pc, k⟩ := e
    change pc = _ at hPc
    change k = _ at hKind
    rw [hPc, hKind]
  exact firstSoftmaxStatsOrdinal hp hX (he.trans (congrArg some ee)) hSources

end Scores
end
end PTX.Kernels.TmlFa4Fwd.Thread
