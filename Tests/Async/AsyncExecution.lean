-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.AsyncExecution
public import Lemmas.Async.AsyncOrigins
public import Lemmas.Execution.NoTma
public import Lemmas.MBarrier.MBarrierHistory
public import Tests.MBarrier.AsyncMBarrier
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace PTX.Tests.AsyncExecution
open PTX.AsyncCopy
noncomputable section

-- The barrier is reused in phases 0 and 1, for two copies to the same destination.
def src0 : Acc := { loc := ⟨.global, 0, 0⟩, size := 16 }
def src1 : Acc := { loc := ⟨.global, 0, 16⟩, size := 16 }
def dst : Acc := { loc := ⟨.shared, 0, 0⟩, size := 16 }
def mb : Loc := ⟨.shared, 0, 64⟩
def bytes0 : List Byte := List.replicate 16 (.bits 32 5, 0)
def bytes1 : List Byte := List.replicate 16 (.bits 32 9, 0)
def L : Launch := { grid := 1, block := 1, params := fun _ => none }

/-- The bulk copy of `src` to `dst`, completed through the barrier at `mb`. -/
def bulk (src : Acc) : AsyncCopy.Spec := { src := src, dst := dst, completion := .mbarrier mb }

def trace : List Event := [⟨0, .mbInit mb 1⟩, ⟨1, .fenceProxy (.async (some (.shared .cta))) none⟩,
  ⟨2, .arrive mb 16⟩, ⟨3, .copy (bulk src0)⟩, ⟨4, .wait mb 0 true⟩,
  ⟨5, .rd dst (bytes0.map some)⟩, ⟨6, .fenceProxy (.async (some (.shared .cta))) none⟩,
  ⟨7, .arrive mb 16⟩, ⟨8, .copy (bulk src1)⟩, ⟨9, .wait mb 1 true⟩,
  ⟨10, .exit⟩]

def effects : Snapshot where
  copies := fun i =>
    if i = (0, 3) then { readBytes := some bytes0, writeBytes := some bytes0, notified := true }
    else if i = (0, 8) then
      { readBytes := some bytes1, writeBytes := some bytes1, notified := true }
    else {}

def ops : List (Ref × MBarrier.Action) := [
  (.thread (0, 0), .init 1), (.thread (0, 2), .arrive 1 16),
  (.async (0, 3) (.notify .copy), .completeTx 16), (.thread (0, 4), .pollParity 0 true),
  (.thread (0, 7), .arrive 1 16), (.async (0, 8) (.notify .copy), .completeTx 16),
  (.thread (0, 9), .pollParity 1 true)]

def log : List (MBarrier.Record Ref) := match MBarrier.replay none ops with
  | .ok xs => xs
  | .error _ => []

def X : Execution where
  tr := fun g => if g = 0 then trace else []
  rf := fun e _ => if e = .thread (0, 5) then some (.async (0, 3) (.write .copy)) else none
  async := effects
  objects := fun m => if m = mb then log else []

theorem log_checked : MBarrier.CheckedLog log :=
  MBarrier.checkedLog_of_replay (ops := ops) (by rfl) (by decide)

theorem observes_first : AsyncObserved X (0, 3) (.write .copy) (0, 4) true .cta := by
  refine ⟨.async (0, 3) (.notify .copy), mb, .inl ⟨rfl, 16, bulk src0, rfl, rfl, rfl, rfl⟩,
    ⟨⟨4, 0, rfl⟩, ?_⟩⟩
  change MBarrier.UpdateBeforeWait log _ _
  exact ⟨2, 3, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      fun _ _ _ h2 _ => absurd h2 (by omega)⟩

theorem observes_second : AsyncObserved X (0, 8) (.write .copy) (0, 9) true .cta := by
  refine ⟨.async (0, 8) (.notify .copy), mb, .inl ⟨rfl, 16, bulk src1, rfl, rfl, rfl, rfl⟩,
    ⟨⟨9, 1, rfl⟩, ?_⟩⟩
  change MBarrier.UpdateBeforeWait log _ _
  exact ⟨5, 6, _, _, 1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      fun _ _ _ h2 _ => absurd h2 (by omega)⟩

theorem copies_well_formed : WellFormed (issuedBy X) X.async := by
  intro i hi
  by_cases h0 : i = (0, 3)
  · subst i
    refine ⟨bulk src0, rfl, by decide, ?_, ?_, ?_, ?_⟩
    · intro bs h
      simp [X, effects] at h
      subst h
      exact ⟨rfl, by simp [bulk, src0, bytes0]⟩
    · intro bs h
      simp [X, effects, sourceBytes, bulk, bytes0] at h ⊢
      subst h
      rfl
    · intro _
      exact ⟨⟨mb, rfl⟩, bytes0, rfl⟩
    · refine ⟨?_, ?_⟩ <;> intro j bs h <;> simp [X, effects] at h
  · by_cases h1 : i = (0, 8)
    · subst i
      refine ⟨bulk src1, rfl, by decide, ?_, ?_, ?_, ?_⟩
      · intro bs h
        simp [X, effects] at h
        subst h
        exact ⟨rfl, by simp [bulk, src1, bytes1]⟩
      · intro bs h
        simp [X, effects, sourceBytes, bulk, bytes1] at h ⊢
        subst h
        rfl
      · intro _
        exact ⟨⟨mb, rfl⟩, bytes1, rfl⟩
      · refine ⟨?_, ?_⟩ <;> intro j bs h <;> simp [X, effects] at h
    · obtain ⟨p, hp⟩ := hi
      cases p <;> simp [X, effects, present, h0, h1] at hp

theorem log_matches : MatchesObject X X.async mb log := by
  intro r hr
  change r ∈ [_, _, _, _, _, _, _] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨by rfl, ?_⟩
  all_goals intro p ok hp _
  all_goals cases hp
  all_goals rfl

-- Every real operation is covered, including the parity-1 wait.
theorem action_has_record (id : Ref) (a : MBarrier.Action)
    (h : objectAction X X.async mb id = some a) : id ∈ log.map MBarrier.Record.id := by
  cases id with
  | thread e =>
    obtain ⟨g, i⟩ := e
    by_cases hg : g = 0
    · subst g
      by_cases hi : i < 11
      · interval_cases i <;>
          simp [objectAction, X, Execution.get, trace] at h
        all_goals change Ref.thread _ ∈ [_, _, _, _, _, _, _]
        all_goals simp
      · have ht : (trace)[i]? = none := List.getElem?_eq_none (by simpa [trace] using hi)
        simp [objectAction, X, Execution.get, ht] at h
    · simp [objectAction, X, Execution.get, hg] at h
  | async i p =>
    by_cases h0 : i = (0, 3)
    · subst i
      cases p <;> simp [objectAction, issuedBy, X, effects, Execution.get, trace] at h
      change Ref.async _ _ ∈ [_, _, _, _, _, _, _]
      simp
    · by_cases h1 : i = (0, 8)
      · subst i
        cases p <;> simp [objectAction, issuedBy, X, effects, Execution.get, trace] at h
        change Ref.async _ _ ∈ [_, _, _, _, _, _, _]
        simp
      · have hp := objectAction_present h
        cases p <;> simp [Execution.RefPresent, Execution.AsyncPresent, Execution.MmaRead, X,
          effects, h0, h1] at hp


theorem log_covers : CoversObject X X.async mb log := by
  intro id a h
  exact List.mem_map.mp (action_has_record id a h)

theorem get_mem {e : EvId} {ev : Event} (h : X.get e = some ev) : ev ∈ trace := by
  obtain ⟨g, i⟩ := e
  by_cases hg : g = 0
  · subst g
    exact List.mem_of_getElem? h
  · simp [Execution.get, X, hg] at h

theorem no_tc : X.NoTc := by
  intro e pc k he
  have hm := get_mem he
  simp [trace] at hm

theorem other_object_empty (m : Loc) (hm : m ≠ mb) (id : Ref) :
    objectAction X X.async m id = none := by
  have hmb : mb ≠ m := Ne.symm hm
  cases id with
  | thread e =>
    cases he : X.get e with
    | none => simp [objectAction, he]
    | some ev =>
      have hp := get_mem he
      simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [objectAction, he, hmb]
  | async i p =>
    cases he : X.get i with
    | none => cases p <;> simp [objectAction, issuedBy, he]
    | some ev =>
      have hp := get_mem he
      simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals cases p <;> simp only [objectAction, issuedBy, he]
      all_goals simp [X, effects, bulk, hmb]


theorem objects_ok : ObjectsOk X := by
  intro m
  by_cases hm : m = mb
  · subst m
    change MBarrier.CheckedLog log ∧ MatchesObject X X.async mb log ∧ CoversObject X X.async mb log
    exact ⟨log_checked, log_matches, log_covers⟩
  · rw [show X.objects m = [] by simp [X, hm]]
    refine ⟨⟨by simp, none, .nil none⟩, ?_, ?_⟩
    · intro r hr; cases hr
    · intro id a ha
      rw [other_object_empty m hm id] at ha
      cases ha

-- All active async/object constraints admit this two-phase reuse execution. No old
-- phase-0/sole-copy/source-immutability restriction remains in TmaOk.
theorem two_phase_tma_ok : TmaOk X := by
  refine ⟨copies_well_formed, ?_, objects_ok, ?_⟩
  · refine ⟨?_, ?_⟩
    all_goals intro i h
    all_goals simp [X, effects, AsyncCopy.Snapshot.mmaStarted] at h
  · intro i h
    simp [X, effects] at h

-- A later wait on the same object cannot publish a different phase's copy.
theorem first_not_second_phase {acq : Bool} {ws : MbarScope} :
    ¬ AsyncObserved X (0, 3) (.notify .copy) (0, 9) acq ws := by
  rintro ⟨n, m, hn, ⟨-, i, j, r, w, phase, hr, hid, -, hw, hwid, -, -, -, hp, hq, -⟩⟩
  obtain ⟨hnr, hnotify⟩ := hn
  simp only [NotifyOn, Notification] at hnotify
  obtain ⟨bytes, s, hi, -, hm, -⟩ := hnotify
  have hs : s = bulk src0 := by
    simpa [issuedBy, Execution.get, X, trace] using hi.symm
  rw [hs] at hm
  injection hm with hm
  subst hm
  have hid' : r.id = Ref.async (0, 3) (Part.notify Target.copy) := hid.trans hnr
  change log[i]? = some r at hr
  change log[j]? = some w at hw
  have hil : i < 7 := (List.getElem?_eq_some_iff.mp hr).choose
  have hjl : j < 7 := (List.getElem?_eq_some_iff.mp hw).choose
  have hir : (log.map MBarrier.Record.id)[i]? = some (.async (0, 3) (.notify .copy)) := by
    rw [List.getElem?_map, hr]
    simpa using congrArg some hid'
  have hjr : (log.map MBarrier.Record.id)[j]? = some (.thread (0, 9)) := by
    rw [List.getElem?_map, hw]
    simpa using congrArg some hwid
  have hi2 : i = 2 := by
    interval_cases i <;> first | rfl | (change some _ = some _ at hir; cases hir)
  have hj6 : j = 6 := by
    interval_cases j <;> first | rfl | (change some _ = some _ at hjr; cases hjr)
  subst i; subst j
  change some (0 : Nat) = some phase at hp
  change some (1 : Nat) = some phase at hq
  cases hp
  cases hq

theorem baseCausality_4_8 : baseCausality L X (0, 4) (0, 8) :=
  .single (Or.inl ⟨rfl, by decide, by decide⟩)

-- The same destination may be written again, after completion observation.
theorem reuse_ordered (l : Loc) (hl : dst.Covers l) :
    modelCausality L X l (.async (0, 3) (.write .copy)) (.async (0, 8) (.write .copy)) :=
  ⟨.inl (by simp [SameCta, L, Launch.threads]),
    .direct ⟨⟨dst, true, ⟨rfl, bulk src0, ⟨3, rfl⟩, rfl, rfl⟩, hl⟩,
      ⟨dst, true, ⟨rfl, bulk src1, ⟨8, rfl⟩, rfl, rfl⟩, hl⟩,
      Or.inl ⟨(0, 4), ⟨.inr ⟨.cta, observes_first, by simp [ScopesMeet, MbarScopeIncludes, SameCta,
        SameCluster, L, Launch.threads, Launch.clusterOfCta]⟩, baseCausality_4_8⟩⟩⟩⟩

-- The source of the second transfer is its read effect, not hard-coded launch memory.
example : X.MemWrites (.async (0, 8) (.write .copy)) dst bytes1 :=
  ⟨bulk src1, ⟨8, rfl⟩, rfl, rfl, rfl⟩
example : X.MemReads (.async (0, 8) (.read .copy)) src1 (bytes1.map some) :=
  ⟨bulk src1, bytes1, ⟨8, rfl⟩, rfl, rfl, rfl⟩

-- Thread progress is independent of a copy's completion. The async stages contribute
-- their own counted progress, rather than occupying a synthetic pc position.
example : X.get (0, 4) = some ⟨4, .wait mb 0 true⟩ := rfl
example : X.size L = 17 := by decide

-- A real arrival on an uninitialized object remains an execution with a fault.
-- It is not filtered out by the object consistency predicate.
def faultRecord : MBarrier.Record Ref :=
  ⟨.thread (0, 0), .arrive 1 0, ⟨none, none, none⟩, some .invalidObject⟩

def faultX : Execution where
  tr := fun g => if g = 0 then [⟨0, .arrive mb 0⟩] else []
  rf := fun _ _ => none
  objects := fun m => if m = mb then [faultRecord] else []

theorem invalid_arrival_checked : MBarrier.CheckedLog [faultRecord] :=
  ⟨by simp, none, .cons ⟨rfl, rfl⟩ (.nil none)⟩

theorem fault_action_matches : MatchesObject faultX faultX.async mb [faultRecord] := by
  intro r hr
  have : r = faultRecord := List.mem_singleton.mp hr
  subst r
  refine ⟨rfl, ?_⟩
  intro p ok h
  cases h

theorem fault_action_covers : CoversObject faultX faultX.async mb [faultRecord] := by
  intro id a h
  cases id with
  | thread e =>
    obtain ⟨g, i⟩ := e
    by_cases hg : g = 0
    · subst g
      cases i with
      | zero => exact ⟨faultRecord, by simp, rfl⟩
      | succ i => simp [objectAction, Execution.get, faultX] at h
    · simp [objectAction, Execution.get, faultX, hg] at h
  | async e p =>
    obtain ⟨g, i⟩ := e
    by_cases hg : g = 0
    · subst g
      cases i <;> cases p <;> simp [objectAction, issuedBy, Execution.get, faultX] at h
    · cases p <;> simp [objectAction, issuedBy, Execution.get, faultX, hg] at h

example (A : List Assumption) (mem0 : Mem0) : Unsafe L K A mem0 faultX :=
  object_fault_unsafe (m := mb) (r := faultRecord) (by simp [faultX]) (by decide)

-- Thread exit alone is insufficient when an issued copy has not notified completion.
example : ¬ Complete L { X with async := {} } := by
  intro hc
  have hh := hc.copy_notified (i := (0, 3)) (s := bulk src0) ⟨3, rfl⟩ rfl
  cases hh

end
end PTX.Tests.AsyncExecution
