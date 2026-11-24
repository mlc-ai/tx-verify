-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Lemmas.Async.AsyncCopy

/-! Litmus for ERR-OBJECT-LIFETIME: initializing an mbarrier on bytes an asynchronous copy wrote.

Thread 0 issues a bulk copy into a shared buffer whose completion notifies mbarrier `F`, polls
`F` successfully with an acquire wait, and then initializes an mbarrier `M` on the first eight
bytes of the buffer. §9.7.15.16 forbids "non-mbarrier or mbarrier.init operations on an
initialized mbarrier object" only; here the copy's write is complete and observed before `M` is
initialized. The copy's write is ordered before the initialization at every byte of `M`
(`copy_before_init`), so the branch of `TmaUnsafe` for accesses of an mbarrier's bytes does not
hold (`not_init_overlap`); it held for every asynchronous access before ERR-OBJECT-LIFETIME admitted
asynchronous accesses ordered by `modelCausality`. Only the events and `F`'s history are given: the
other object histories and initializations are not part of this check. -/

namespace PTX.Tests.InitAfterCopy
open PTX

noncomputable section

def L1 : Launch := { grid := 1, block := 1, params := fun _ => none }

/-- The global source, the shared buffer, the completion barrier `F` and the barrier `M` laid
over the start of the buffer. -/
def src : Acc := ⟨⟨.global, 0, 0⟩, 16, false, false, .cta, 0, false⟩
def dst : Acc := ⟨⟨.shared, 0, 0⟩, 16, false, false, .cta, 0, false⟩
def F : Loc := ⟨.shared, 0, 64⟩
def M : Loc := ⟨.shared, 0, 0⟩

def st (phase pending : Nat) (obs : Bool) : MBarrier.State := ⟨phase, 1, pending, 0, obs⟩

/-- The bulk copy from `src` to `dst` whose completion notifies `F`. -/
def cp : AsyncCopy.Spec := { src := src, dst := dst, completion := .mbarrier F }

/-- `F`'s history: its initialization with one arrival, the copy's notification of sixteen bytes
in phase 0, the poll observing phase 0. -/
def logF : List (MBarrier.Record AsyncCopy.Ref) := [
  ⟨.thread (0, 0), .init 1, ⟨some (st 0 1 true), none, none⟩, none⟩,
  ⟨.async (0, 1) (.notify .copy), .completeTx 16, ⟨some (st 1 1 false), none, none⟩, none⟩,
  ⟨.thread (0, 2), .pollParity 0 true, ⟨some (st 1 1 true), some true, some 0⟩, none⟩]

def X : Execution where
  tr
    | 0 => [⟨0, .mbInit F 1⟩, ⟨1, .copy cp⟩, ⟨2, .wait F 0 true true .cta⟩,
        ⟨3, .mbInit M 1⟩]
    | _ => []
  rf _ _ := none
  objects m := if m = F then logF else []
  async := { copies := fun i => if i = (0, 1) then { notified := true } else {} }

theorem get_copy : X.get (0, 1) = some ⟨1, .copy cp⟩ := rfl

theorem is_copy : X.Copy (0, 1) cp := ⟨1, rfl⟩

theorem get_cases {e : EvId} {ev : Event} (h : X.get e = some ev) :
    ev = ⟨0, .mbInit F 1⟩ ∨ (e = (0, 1) ∧ ev = ⟨1, .copy cp⟩) ∨
      ev = ⟨2, .wait F 0 true true .cta⟩ ∨ (e = (0, 3) ∧ ev = ⟨3, .mbInit M 1⟩) := by
  obtain ⟨g, k⟩ := e
  rcases g with _ | g
  · rcases k with _ | _ | _ | _ | k <;> simp [Execution.get, X] at h <;> simp [h]
  · simp [Execution.get, X] at h

/-- No event of `X` has kind `k` when `k` is none of its four kinds. -/
theorem no_kind {e : EvId} {pc : Nat} {k : Kind} (h : X.get e = some ⟨pc, k⟩)
    (h1 : k ≠ .mbInit F 1) (h2 : k ≠ .copy cp) (h3 : k ≠ .wait F 0 true true .cta)
    (h4 : k ≠ .mbInit M 1) : False := by
  rcases get_cases h with h | ⟨-, h⟩ | h | ⟨-, h⟩ <;> simp only [Event.mk.injEq] at h
  · exact h1 h.2
  · exact h2 h.2
  · exact h3 h.2
  · exact h4 h.2

/-- `F`'s history records the copy's notification before the poll. -/
theorem notified_before_wait :
    MBarrier.UpdateBeforeWait logF (.async (0, 1) (.notify .copy)) (.thread (0, 2)) := by
  refine ⟨1, 2, ⟨.async (0, 1) (.notify .copy), .completeTx 16, ⟨some (st 1 1 false), none, none⟩,
    none⟩,
    ⟨.thread (0, 2), .pollParity 0 true, ⟨some (st 1 1 true), some true, some 0⟩, none⟩, 0, ?_,
    rfl, rfl, ?_, rfl, rfl, rfl, by decide, ?_, ?_, fun _ _ _ h2 _ => absurd h2 (by omega)⟩
  all_goals simp [logF, MBarrier.phaseAt, MBarrier.stateBefore, MBarrier.observedAt, st]

/-- The poll observes the copy's completion. -/
theorem observed : AsyncCopy.AsyncObserved X (0, 1) (.notify .copy) (0, 2) true .cta :=
  ⟨_, F, ⟨rfl, 16, cp, rfl, rfl, rfl, rfl⟩, ⟨2, 0, rfl⟩, notified_before_wait⟩

/-- The poll observes the copy's write. -/
theorem observed_write : AsyncCopy.AsyncObserved X (0, 1) (.write .copy) (0, 2) true .cta :=
  ⟨_, F, .inl ⟨rfl, 16, cp, rfl, rfl, rfl, rfl⟩, ⟨2, 0, rfl⟩, notified_before_wait⟩

theorem wait_baseCausality_init : baseCausality L1 X (0, 2) (0, 3) :=
  .single (.inl ⟨rfl, by decide, by decide⟩)

/-- **The copy's write is ordered before the initialization at every byte of `M`.** -/
theorem copy_before_init {l : Loc} (hl : dst.Covers l) :
    modelCausality L1 X l (.async (0, 1) (.write .copy)) (.thread (0, 3)) :=
  ⟨⟨dst, true, ⟨rfl, cp, is_copy, rfl, rfl⟩, hl⟩, (0, 2),
    ⟨.inr ⟨.cta, observed_write, by simp [ScopesMeet, MbarScopeIncludes, SameCta, SameCluster, L1,
      Launch.threads, Launch.clusterOfCta]⟩, .inl wait_baseCausality_init⟩⟩

/-- The only copy event of `X` is the bulk copy at `(0, 1)`. -/
theorem copy_cases {j : EvId} {s : AsyncCopy.Spec} (h : X.Copy j s) : j = (0, 1) ∧ s = cp := by
  obtain ⟨pc, he⟩ := h
  rcases get_cases he with h | ⟨rfl, h⟩ | h | ⟨-, h⟩
  any_goals simp only [Event.mk.injEq, reduceCtorEq] at h
  · exact absurd h.2 (by simp)
  · simp only [Kind.copy.injEq] at h
    exact ⟨rfl, h.2⟩
  · exact absurd h.2 (by simp)
  · exact absurd h.2 (by simp)

/-- **No access of an mbarrier's bytes is unordered with its initialization.** -/
theorem not_init_overlap : ¬ ∃ e a w i m c l, X.Intent e a w ∧ X.MbInit i m c ∧ a.Covers l ∧
    Acc.Covers { loc := m, size := 8 } l ∧ ¬ modelCausality L1 X l e (.thread i) := by
  rintro ⟨e, a, w, i, m, c, l, hint, ⟨pci, hi⟩, ha, hm, hv⟩
  have hmi : (m = F ∨ (m = M ∧ i = (0, 3))) := by
    rcases get_cases hi with h | ⟨-, h⟩ | h | ⟨hi', h⟩
    · simp only [Event.mk.injEq, Kind.mbInit.injEq] at h
      exact .inl h.2.1
    · simp at h
    · simp at h
    · simp only [Event.mk.injEq, Kind.mbInit.injEq] at h
      exact .inr ⟨h.2.1, hi'⟩
  rcases e with j | ⟨j, p⟩
  · -- the thread reads, writes and reduces nothing
    rcases hint with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨old, new, ⟨pc, he⟩⟩ <;>
      exact no_kind he (by simp) (by simp) (by simp) (by simp)
  · -- the only async event of the execution is the copy at `(0, 1)`
    cases p <;> simp only [Execution.Intent, AsyncCopy.Part.writes, Execution.AsyncFootprint,
      and_false] at hint
    case readCopy =>
      -- the copy's read is in global memory
      obtain ⟨-, hs | ⟨pc, he⟩⟩ := hint
      · obtain ⟨s, hs, hsrc⟩ := hs
        obtain ⟨rfl, rfl⟩ := copy_cases hs
        subst hsrc
        rcases hmi with rfl | ⟨rfl, -⟩
        · simp [Acc.Covers, Loc.InRange, cp, src, F] at ha hm
          omega
        · simp [Acc.Covers, Loc.InRange, cp, src, M] at ha hm
          rw [ha.1] at hm
          simp at hm
      · exact no_kind he (by simp) (by simp) (by simp) (by simp)
    case writeCopy =>
      obtain ⟨-, s, hs, -, hdst⟩ := hint
      obtain ⟨rfl, rfl⟩ := copy_cases hs
      subst hdst
      rcases hmi with rfl | ⟨rfl, rfl⟩
      · simp [Acc.Covers, Loc.InRange, cp, dst, F] at ha hm
        omega
      · exact hv (copy_before_init ha)
    all_goals
      first
      | (-- the copy writes its destination as a whole, so it has no element stages
         obtain ⟨-, s, hs, hel⟩ := hint
         obtain ⟨rfl, rfl⟩ := copy_cases hs
         simp [cp, AsyncCopy.Spec.elems, AsyncCopy.Spec.elemOffsets] at hel)
      | (-- the copy is not a reduction
         obtain ⟨-, s, r, hs, hw, -⟩ := hint
         obtain ⟨rfl, rfl⟩ := copy_cases hs
         simp [cp] at hw)
      | (obtain ⟨-, s, addr, ⟨pc, he⟩, -, -⟩ := hint
         exact no_kind he (by simp) (by simp) (by simp) (by simp))
      | (obtain ⟨-, -, ⟨d, s, accum, mask, ⟨pc, he⟩, -⟩ |
          ⟨c, kk, cta, ⟨pc, he⟩, _, _, _⟩⟩ := hint <;>
         exact no_kind he (by simp) (by simp) (by simp) (by simp))

end

end PTX.Tests.InitAfterCopy
