-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Core.Source.Decode
public import Lemmas.MBarrier.MBarrierHistory
public import Mathlib.Tactic.IntervalCases
public import Lemmas.Async.AsyncCopy

/-! Litmus for `mbarrier.inval` and mbarrier object lifetimes (OBJ-MBAR-STATE,
OBJ-MBAR-PHASES, OBJ-MBAR-HISTORY, ERR-OBJECT-LIFETIME).

§9.7.15.16.13: "mbarrier.inval invalidates the mbarrier object at the location specified by the
address operand addr"; "An mbarrier object must be invalidated before using its memory location
for any other purpose. Performing any mbarrier operation except mbarrier.init on a memory
location that does not contain a valid mbarrier object , results in undefined behavior." Its
example reuses the location for an ordinary store and then re-initializes it.

* `reuse` (one thread): init, arrive, successful poll, inval, an ordinary store and load of the
  object's eight bytes, re-init, arrive, successful poll, inval. Every access is ordered by
  program order before an initialization or after the invalidation of its lifetime, so the
  lifetime rules accept it (`reuse_not_tmaUnsafe`). The second lifetime's poll observes the
  second arrival only, not the first lifetime's arrival of the same phase number
  (`reuse_second_observes_second`, `reuse_second_not_first`).
* `inside`: an ordinary store between the initialization and the invalidation: `Unsafe`
  (`inside_unsafe`), since the store is neither before the initialization nor after the
  invalidation.
* `stale`: an arrival after the invalidation without re-initialization: its record faults
  (`stale_arrive_faults`) and the execution is `Unsafe` (`stale_unsafe`). -/

namespace PTX.Tests.MBarrierLifetime
open PTX

noncomputable section

def L1 : Launch := { grid := 1, block := 1, params := fun _ => none }
def M : Loc := ⟨.shared, 0, 0⟩
/-- The object's eight bytes, as an ordinary access. -/
def word : Acc := ⟨M, 8, false, false, .cta, 0, false⟩
def bs : List Byte := List.replicate 8 (.bits 8 0, 0)
def mem0 : Mem0 := fun _ => some none

/-! ### Decoding and the thread event -/

private def env : Decode.Env := { classes := [⟨"r".toList, 1, 32⟩], labels := [], params := [] }

example : Decode.op env "mbarrier.inval.shared::cta.b64" [.address [.register "r0"]] =
    .ok (.mbarInval 0 0) := rfl
example : Decode.op env "mbarrier.inval.shared.b64" [.address [.register "r0"]] =
    .ok (.mbarInval 0 0) := rfl
example : Op.isLocal (.mbarInval 0 0) = false := rfl

private def t0 : TState := { regs := fun r => if r = 0 then some (.bits 32 0) else none }
example : tmaTmpl L1 0 t0 (.mbarInval 0 0) = .mbInval M (next t0) := rfl
-- A `.shared::cluster` pointer is not a `.shared::cta` operand, even when it names the
-- executing CTA.
private def t1 : TState := { regs := fun r => if r =
                             0 then some (.ptr 32 false (.shared 0 0) 0) else none }
example : tmaTmpl L1 0 t1 (.mbarInval 0 0) = .ub .noRule := rfl

/-! ### Object transitions -/

example : MBarrier.perform (some ⟨1, 1, 1, 0, true⟩) .inval = .ok ⟨none, none, none⟩ := rfl
example : MBarrier.perform none .inval = .error .invalidObject := rfl
example : MBarrier.perform none (.arrive 1 0) = .error .invalidObject := rfl
-- After invalidation a new initialization starts a new object at phase 0.
example : MBarrier.perform none (.init 2) = .ok ⟨some ⟨0, 2, 2, 0, true⟩, none, none⟩ := rfl

/-! ### `reuse`: invalidation, ordinary reuse and re-initialization -/

def sInit : MBarrier.State := ⟨0, 1, 1, 0, true⟩
def sArr : MBarrier.State := ⟨1, 1, 1, 0, false⟩
def sObs : MBarrier.State := ⟨1, 1, 1, 0, true⟩

/-- The object's history: two lifetimes, events `0–3` and `6–9` of thread 0. -/
def reuseLog : List (MBarrier.Record AsyncCopy.Ref) := [
  ⟨.thread (0, 0), .init 1, ⟨some sInit, none, none⟩, none⟩,
  ⟨.thread (0, 1), .arrive 1 0, ⟨some sArr, none, none⟩, none⟩,
  ⟨.thread (0, 2), .pollParity 0 true, ⟨some sObs, some true, some 0⟩, none⟩,
  ⟨.thread (0, 3), .inval, ⟨none, none, none⟩, none⟩,
  ⟨.thread (0, 6), .init 1, ⟨some sInit, none, none⟩, none⟩,
  ⟨.thread (0, 7), .arrive 1 0, ⟨some sArr, none, none⟩, none⟩,
  ⟨.thread (0, 8), .pollParity 0 true, ⟨some sObs, some true, some 0⟩, none⟩,
  ⟨.thread (0, 9), .inval, ⟨none, none, none⟩, none⟩]

theorem reuse_checked : MBarrier.CheckedLog reuseLog :=
  MBarrier.checkedLog_of_replay (ops := reuseLog.map (fun r => (r.id, r.action))) (by rfl)
    (by decide)

def reuseTrace : List Event := [
  ⟨0, .mbInit M 1⟩, ⟨1, .arrive M 0⟩, ⟨2, .wait M 0 true⟩, ⟨3, .mbInval M⟩,
  ⟨4, .wr word bs⟩, ⟨5, .rd word (bs.map some)⟩,
  ⟨6, .mbInit M 1⟩, ⟨7, .arrive M 0⟩, ⟨8, .wait M 0 true⟩, ⟨9, .mbInval M⟩]

def reuse : Execution where
  tr g := if g = 0 then reuseTrace else []
  rf _ _ := none
  objects m := if m = M then reuseLog else []

/-- The record at position `i` is the one of event `i` (first lifetime) or `i + 2`. -/
theorem reuse_idx {i : Nat} {r : MBarrier.Record AsyncCopy.Ref} (h : reuseLog[i]? = some r) :
    i < 8 ∧ r.id = .thread (0, if i < 4 then i else i + 2) ∧
      (r.action = .inval ↔ i = 3 ∨ i = 7) ∧ (i = 0 ∨ i = 4 → r.action = .init 1) := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [reuseLog] at h <;> subst h <;>
    simp

/-- Two ids are ordered in the history as their events are. -/
theorem reuse_before {a b : Nat} (h : MBarrier.Before reuseLog (.thread (0, a)) (.thread (0, b))) :
    a < b := by
  obtain ⟨i, j, r, s, hi, ha, hj, hb, hij⟩ := h
  obtain ⟨hi8, hri, -⟩ := reuse_idx hi
  obtain ⟨hj8, hsj, -⟩ := reuse_idx hj
  rw [ha] at hri
  rw [hb] at hsj
  simp only [AsyncCopy.Ref.thread.injEq, Prod.mk.injEq, true_and] at hri hsj
  split_ifs at hri hsj <;> omega

theorem reuse_initBefore {a b : Nat}
    (h : MBarrier.InitBefore reuseLog (.thread (0, a)) (.thread (0, b))) :
    a < b ∧ (a = 0 → b ≤ 3) ∧ (a = 6 → 6 < b) := by
  obtain ⟨i, j, r, s, n, hi, ha, hact, -, hj, hb, hij, hl⟩ := h
  obtain ⟨hi8, hri, hinv⟩ := reuse_idx hi
  obtain ⟨hj8, hsj, -⟩ := reuse_idx hj
  rw [ha] at hri
  rw [hb] at hsj
  simp only [AsyncCopy.Ref.thread.injEq, Prod.mk.injEq, true_and] at hri hsj
  have h3 : ¬ (i < 3 ∧ 3 < j) := fun ⟨h1, h2⟩ => hl 3 _ h1 h2 rfl rfl
  split_ifs at hri hsj <;> omega

theorem reuse_get {g k : Nat} {ev : Event} (h : reuse.get (g, k) = some ev) :
    g = 0 ∧ k < 10 ∧ reuseTrace[k]? = some ev := by
  by_cases hg : g = 0
  · subst hg
    have h' : reuseTrace[k]? = some ev := by simpa [Execution.get, reuse] using h
    exact ⟨rfl, by simpa [reuseTrace] using (List.getElem?_eq_some_iff.mp h').1, h'⟩
  · simp [Execution.get, reuse, hg] at h

theorem reuse_po {j k : Nat} (hjk : j < k) (hk : k < 10) :
    baseCausality L1 reuse (0, j) (0, k) := by
  refine .single (.inl ⟨rfl, hjk, by simp [reuse, reuseTrace]; omega, ?_⟩)
  rintro ⟨h1, h2⟩
  have h3 := h2 (k - j) le_rfl
  interval_cases k <;> interval_cases j <;>
    simp [Execution.get, reuse, reuseTrace, Event.acc, word, Acc.shift, M, Loc.at] at h1 h3

theorem reuse_mbInit {i : EvId} {m : Loc} {c : Nat} (h : reuse.MbInit i m c) :
    (i = (0, 0) ∨ i = (0, 6)) ∧ m = M := by
  obtain ⟨g, k⟩ := i
  obtain ⟨pc, h⟩ := h
  obtain ⟨rfl, hk, h⟩ := reuse_get h
  interval_cases k <;> simp [reuseTrace] at h <;> simp_all

theorem reuse_mbInval {v : EvId} {m : Loc} (h : reuse.MbInval v m) :
    (v = (0, 3) ∨ v = (0, 9)) ∧ m = M := by
  obtain ⟨g, k⟩ := v
  obtain ⟨pc, h⟩ := h
  obtain ⟨rfl, hk, h⟩ := reuse_get h
  interval_cases k <;> simp [reuseTrace] at h <;> simp_all

theorem reuse_objects {m : Loc} {r : MBarrier.Record AsyncCopy.Ref} (h : r ∈ reuse.objects m) :
    m = M ∧ r ∈ reuseLog := by
  by_cases hm : m = M
  · subst hm; exact ⟨rfl, by simpa [reuse] using h⟩
  · simp [reuse, hm] at h

/-- No event of `reuse` other than its mbarrier operations and its access of `word`. -/
theorem reuse_kinds {e : EvId} {pc : Nat} {k : Kind} (h : reuse.get e = some ⟨pc, k⟩) :
    k = .mbInit M 1 ∨ k = .arrive M 0 ∨ k = .wait M 0 true ∨ k = .mbInval M ∨
      k = .wr word bs ∨ k = .rd word (bs.map some) := by
  obtain ⟨g, j⟩ := e
  obtain ⟨rfl, hj, h⟩ := reuse_get h
  interval_cases j <;> simp [reuseTrace] at h <;> obtain ⟨-, rfl⟩ := h <;> simp

/-- Every record lies inside its lifetime. -/
theorem reuse_published {m : Loc} {r : MBarrier.Record AsyncCopy.Ref} (hr : r ∈ reuse.objects m) :
    ObjectPublished L1 reuse m r := by
  obtain ⟨rfl, hrl⟩ := reuse_objects hr
  have hobj : reuse.objects M = reuseLog := by simp [reuse]
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hrl
  obtain ⟨hi8, hid, -, hact⟩ := reuse_idx hi
  by_cases hinit : i = 0 ∨ i = 4
  · -- an initialization happens after every earlier invalidation
    have ha := hact hinit
    rcases hinit with rfl | rfl <;> simp only [show (0 : Nat) < 4 by omega,
      show ¬ (4 : Nat) < 4 by omega, ite_true, ite_false] at hid
    · refine .inl ⟨⟨1, ha⟩, fun v hv hb => ?_⟩
      rw [hobj, hid] at hb
      obtain ⟨hv, -⟩ := reuse_mbInval hv
      rcases hv with rfl | rfl <;> have := reuse_before hb <;> omega
    · refine .inl ⟨⟨1, ha⟩, fun v hv hb => ?_⟩
      rw [hobj, hid] at hb
      rw [hid]
      obtain ⟨hv, -⟩ := reuse_mbInval hv
      rcases hv with rfl | rfl
      · exact reuse_po (by omega) (by omega)
      · have := reuse_before hb; omega
  rcases (show i < 4 ∨ 4 < i by omega) with hlt | hlt
  · -- first lifetime: after `(0, 0)`, before its invalidation `(0, 3)`
    have hn : r.id = .thread (0, i) := by simpa [hlt] using hid
    refine .inr ⟨(0, 0), 1, ⟨0, rfl⟩, ⟨0, i, _, r, 1, rfl, rfl, rfl, rfl, hi, rfl, by omega,
      fun k s h1 h2 hk ha => ?_⟩, ?_, fun v hv hib hne => ?_⟩
    · have := (reuse_idx hk).2.2.1.mp ha; omega
    · rw [hn]; exact .inl (reuse_po (by omega) (by omega))
    · obtain ⟨hv, -⟩ := reuse_mbInval hv
      rw [hn] at hne ⊢
      rcases hv with rfl | rfl
      · have : i ≠ 3 := by rintro rfl; exact hne rfl
        exact .inl ⟨_, rfl, reuse_po (by omega) (by omega)⟩
      · exact .inl ⟨_, rfl, reuse_po (by omega) (by omega)⟩
  · -- second lifetime: after `(0, 6)`, before its invalidation `(0, 9)`
    have hn : r.id = .thread (0, i + 2) := by simpa [show ¬ i < 4 by omega] using hid
    refine .inr ⟨(0, 6), 1, ⟨6, rfl⟩, ⟨4, i, _, r, 1, rfl, rfl, rfl, rfl, hi, rfl, by omega,
      fun k s h1 h2 hk ha => ?_⟩, ?_, fun v hv hib hne => ?_⟩
    · have := (reuse_idx hk).2.2.1.mp ha; omega
    · rw [hn]; exact .inl (reuse_po (by omega) (by omega))
    · obtain ⟨hv, -⟩ := reuse_mbInval hv
      rw [hn] at hne ⊢
      rcases hv with rfl | rfl
      · rw [hobj] at hib
        have := (reuse_initBefore hib).2.2 rfl; omega
      · have : i ≠ 7 := by rintro rfl; exact hne rfl
        exact .inl ⟨_, rfl, reuse_po (by omega) (by omega)⟩

/-- The thread accesses only `word`, at events `4` and `5`; no asynchronous access exists. -/
theorem reuse_intent {e : AsyncCopy.Ref} {a : Acc} {w : Bool} (h : reuse.Intent e a w) :
    ∃ k, e = .thread (0, k) ∧ (k = 4 ∨ k = 5) ∧ a = word := by
  cases e with
  | thread e =>
    obtain ⟨g, k⟩ := e
    rcases h with ⟨bs', ⟨pc, h⟩, -⟩ | ⟨bs', ⟨pc, h⟩, -⟩ | ⟨old, new, ⟨pc, h⟩⟩ <;>
      obtain ⟨rfl, hk, h⟩ := reuse_get h <;>
      interval_cases k <;> simp [reuseTrace] at h <;> simp_all
  | async i p =>
    cases p <;> simp only [Execution.Intent, AsyncCopy.Part.writes, Execution.AsyncFootprint,
      and_false] at h
    case readCopy =>
      obtain ⟨-, ⟨s, ⟨pc, he⟩, -⟩ | ⟨pc, he⟩⟩ := h
      · exact absurd (reuse_kinds he) (by simp)
      · exact absurd (reuse_kinds he) (by simp)
    case writeCopy =>
      obtain ⟨-, s, ⟨pc, he⟩, -, -⟩ := h
      exact absurd (reuse_kinds he) (by simp)
    case writeElem =>
      obtain ⟨-, s, ⟨pc, he⟩, -⟩ := h
      exact absurd (reuse_kinds he) (by simp)
    case oldElem =>
      obtain ⟨-, s, r, ⟨pc, he⟩, -, -⟩ := h
      exact absurd (reuse_kinds he) (by simp)
    case oldStore =>
      obtain ⟨-, s, addr, ⟨pc, he⟩, -, -, -⟩ := h
      exact absurd (reuse_kinds he) (by simp)
    case writeCta =>
      obtain ⟨-, s, targets, ⟨pc, he⟩, -, -⟩ := h
      exact absurd (reuse_kinds he) (by simp)
    case mmaRead =>
      obtain ⟨-, -, ⟨d, s, acc, mask, ⟨pc, he⟩, -⟩ |
        ⟨c, kk, cta, ⟨pc, he⟩, -, -, -, -⟩⟩ := h <;>
        exact absurd (reuse_kinds he) (by simp)
    all_goals
      obtain ⟨-, s, addr, ⟨pc, he⟩, -, -⟩ := h
      exact absurd (reuse_kinds he) (by simp)

/-- **Reuse is safe**: ordinary accesses after the invalidation and before the re-initialization,
and the re-initialized object's operations, satisfy every lifetime rule. -/
theorem reuse_not_tmaUnsafe : ¬ TmaUnsafe L1 mem0 reuse := by
  rintro (⟨m, r, hr, hf⟩ | ⟨m, r, hr, hp⟩ |
    ⟨e, a, w, i, m, c, l, he, hi, ha, hl, hv, hnot⟩ | hov | hmu)
  · obtain ⟨-, hr⟩ := reuse_objects hr
    have : ∀ q ∈ reuseLog, q.fault = none := by decide
    rw [this r hr] at hf; cases hf
  · exact hp (reuse_published hr)
  · obtain ⟨k, rfl, hk, rfl⟩ := reuse_intent he
    obtain ⟨hii, rfl⟩ := reuse_mbInit hi
    rcases hii with rfl | rfl
    · -- after the invalidation `(0, 3)` of the first lifetime
      exact hnot ⟨(0, 3), ⟨3, rfl⟩, ⟨0, 3, _, _, 1, rfl, rfl, rfl, rfl, rfl, rfl, by omega,
        fun k s h1 h2 hk ha => by have := (reuse_idx hk).2.2.1.mp ha; omega⟩,
        .inl (reuse_po (by omega) (by omega))⟩
    · -- before the re-initialization `(0, 6)`
      exact hv (.inl (reuse_po (by omega) (by omega)))
  · -- the execution issues no `cp.async`
    obtain ⟨i, j, s, s', -, hi, -, -⟩ := hov
    obtain ⟨pc, h⟩ := hi
    rcases reuse_kinds h with h | h | h | h | h | h <;> cases h
  · -- the execution issues no masked copy
    obtain ⟨i, s, w', l, hc, -, -, -⟩ := hmu
    obtain ⟨pc, h⟩ := hc
    rcases reuse_kinds h with h | h | h | h | h | h <;> cases h

/-- The second lifetime's poll observes its own arrival. -/
theorem reuse_second_observes_second :
    MBarrier.UpdateBeforeWait reuseLog (.thread (0, 7)) (.thread (0, 8)) :=
  ⟨5, 6, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by omega, rfl, rfl,
    fun _ _ _ h2 _ => absurd h2 (by omega)⟩

/-- Phase `0` of the first lifetime is not the phase `0` the second lifetime's poll observes: the
invalidation between them separates the lifetimes. -/
theorem reuse_second_not_first :
    ¬ MBarrier.UpdateBeforeWait reuseLog (.thread (0, 1)) (.thread (0, 8)) := by
  rintro ⟨i, j, r, w, p, hi, hr, -, hj, hw, -, -, hij, -, -, hl⟩
  obtain ⟨-, hri, -⟩ := reuse_idx hi
  obtain ⟨-, hwj, -⟩ := reuse_idx hj
  rw [hr] at hri
  rw [hw] at hwj
  simp only [AsyncCopy.Ref.thread.injEq, Prod.mk.injEq, true_and] at hri hwj
  have hi1 : i = 1 := by split_ifs at hri <;> omega
  have hj6 : j = 6 := by split_ifs at hwj <;> omega
  subst hi1; subst hj6
  exact hl 3 _ (by omega) (by omega) rfl rfl

/-! ### `inside`: an ordinary store while the object is initialized -/

def insideLog : List (MBarrier.Record AsyncCopy.Ref) := [
  ⟨.thread (0, 0), .init 1, ⟨some sInit, none, none⟩, none⟩,
  ⟨.thread (0, 2), .inval, ⟨none, none, none⟩, none⟩]

def inside : Execution where
  tr g := if g = 0 then [⟨0, .mbInit M 1⟩, ⟨1, .wr word bs⟩, ⟨2, .mbInval M⟩] else []
  rf _ _ := none
  objects m := if m = M then insideLog else []

theorem inside_get {g k : Nat} {ev : Event} (h : inside.get (g, k) = some ev) :
    g = 0 ∧ (k = 0 ∧ ev = ⟨0, .mbInit M 1⟩ ∨ k = 1 ∧ ev = ⟨1, .wr word bs⟩ ∨
      k = 2 ∧ ev = ⟨2, .mbInval M⟩) := by
  by_cases hg : g = 0
  · subst hg
    rcases k with _ | _ | _ | k <;> simp [Execution.get, inside] at h <;> simp [h]
  · simp [Execution.get, inside, hg] at h

theorem inside_inval {v : EvId} {m : Loc} (h : inside.MbInval v m) : v = (0, 2) := by
  obtain ⟨g, k⟩ := v
  obtain ⟨pc, h⟩ := h
  by_cases hg : g = 0
  · subst hg
    rcases k with _ | _ | _ | k <;> simp [Execution.get, inside] at h ⊢
  · simp [Execution.get, inside, hg] at h

/-- `inside` has no fence event. -/
theorem inside_noFence {e : EvId} {sem : FenceSem} {sc : MbarScope} :
    ¬ inside.ThreadFence e sem sc := by
  rintro ⟨pc, he⟩
  obtain ⟨-, h⟩ := inside_get he
  rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h

/-- `inside` has no release/acquire pair: its only access is the store of `word`. -/
theorem inside_noSync (e f : EvId) : ¬ synchronizesWith L1 inside e f := by
  rintro ⟨a, b, bs', cs, hw, -, hrel, -, -, -, -, -, -, -⟩
  rcases hw with ⟨pc, he⟩ | ⟨old, pc, he⟩
  · obtain ⟨-, h⟩ := inside_get he
    rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · cases h
    · cases h
      simp [word] at hrel
    · cases h
  · obtain ⟨-, h⟩ := inside_get he
    rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h

/-- `inside` has no fence synchronization. -/
theorem inside_noFenceSync (e f : EvId) : ¬ FenceSync L1 inside e f := by
  rintro (⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ⟨sem, sc, hf | hf⟩, -⟩ |
    ⟨⟨sc, -, hs, -⟩, -⟩)
  · exact inside_noFence hf
  · exact inside_noFence hf
  · exact inside_noFence hs

/-- Causality of `inside` is program order: it has no synchronizing event. -/
theorem inside_baseCausality {e f : EvId} (h : baseCausality L1 inside e f) : e.2 < f.2 := by
  have base : ∀ e f, (po inside e f ∨ CtaBarSync L1 inside e f ∨ MSync L1 inside e f ∨
      ClusterSync L1 inside e f ∨ WarpBarSync L1 inside e f ∨ synchronizesWith L1 inside e f ∨
      FenceSync L1 inside e f) → e.2 < f.2 := by
    intro e f h
    rcases h with ⟨-, h, -⟩ | ⟨-, key, i, j, -, ⟨-, ⟨count, pc, hb⟩, -⟩, -⟩ |
      ⟨x, w, m, rs, as, ⟨tx, count, pc, hx⟩, -⟩ | ⟨-, i, j, ⟨phase, ha, -⟩, -⟩ |
      ⟨i, j, ⟨-, mask, inst, ⟨pc, hw⟩, -⟩, -⟩ | hsync | hfs
    · exact h
    · obtain ⟨-, h⟩ := inside_get hb; rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
    · obtain ⟨-, h⟩ := inside_get hx; rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
    · obtain ⟨k, s, t, c, w, lanes, g, hk, -⟩ := ha
      simp [inside] at hk
    · obtain ⟨-, h⟩ := inside_get hw; rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
    · exact absurd hsync (inside_noSync e f)
    · exact absurd hfs (inside_noFenceSync e f)
  induction h with
  | single h => exact base _ _ h
  | tail _ h ih => exact ih.trans (base _ _ h)

/-- **An access of an initialized object is undefined**: the store is neither before the
initialization nor after the invalidation. -/
theorem inside_tmaUnsafe : TmaUnsafe L1 mem0 inside := by
  have noResult {l : Loc} {e g : EvId} :
      ¬ Tmem.Pair.AllocResultBefore L1 inside l e g := by
    rintro ⟨_, _, _, _, _, _, _, ⟨_, he⟩, _⟩
    obtain ⟨_, h⟩ := inside_get (g := g.1) (k := g.2) he
    rcases h with ⟨_, hf⟩ | ⟨_, hf⟩ | ⟨_, hf⟩ <;> cases hf
  refine .inr (.inr (.inl ⟨.thread (0, 1), word, true, (0, 0), M, 1, M,
    .inr (.inl ⟨bs, ⟨1, rfl⟩, rfl⟩), ⟨0, rfl⟩, ?_, ?_, fun h => ?_, ?_⟩))
  · simp [Acc.Covers, Loc.InRange, word, M]
  · simp [Acc.Covers, Loc.InRange, M]
  · rcases h with h | h
    · have := inside_baseCausality h; simp at this
    · exact noResult h
  · rintro ⟨v, hv, -, h⟩
    rw [inside_inval hv] at h
    rcases h with h | h
    · have := inside_baseCausality h; simp at this
    · exact noResult h

theorem inside_unsafe (K : Kernel) (A : List Assumption) : Unsafe L1 K A mem0 inside :=
  .inr (.inr (.inr (.inr (.inr (.inl inside_tmaUnsafe)))))

/-! ### `stale`: an operation after the invalidation, without re-initialization -/

def staleLog : List (MBarrier.Record AsyncCopy.Ref) := [
  ⟨.thread (0, 0), .init 1, ⟨some sInit, none, none⟩, none⟩,
  ⟨.thread (0, 1), .inval, ⟨none, none, none⟩, none⟩,
  ⟨.thread (0, 2), .arrive 1 0, ⟨none, none, none⟩, some .invalidObject⟩]

/-- The history with the stale arrival's fault is the checked one. -/
theorem stale_checked : MBarrier.CheckedLog staleLog :=
  ⟨by decide, none, .cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.nil _)))⟩

/-- After the invalidation the arrival has no object: any checked record of it faults. -/
theorem stale_arrive_faults (r : MBarrier.Record AsyncCopy.Ref) (hr : MBarrier.RecordOk none r)
    (ha : r.action = .arrive 1 0) : r.fault = some .invalidObject := by
  unfold MBarrier.RecordOk at hr
  rw [ha] at hr
  exact hr.2

example : MBarrier.stateBefore staleLog 2 = none := rfl

def stale : Execution where
  tr g := if g = 0 then [⟨0, .mbInit M 1⟩, ⟨1, .mbInval M⟩, ⟨2, .arrive M 0⟩] else []
  rf _ _ := none
  objects m := if m = M then staleLog else []

theorem stale_unsafe (K : Kernel) (A : List Assumption) : Unsafe L1 K A mem0 stale :=
  .inr (.inr (.inr (.inr (.inr (.inl (.inl ⟨M, ⟨.thread (0, 2), .arrive 1 0, ⟨none, none, none⟩,
    some .invalidObject⟩, by simp [stale, staleLog], rfl⟩))))))

end

end PTX.Tests.MBarrierLifetime
