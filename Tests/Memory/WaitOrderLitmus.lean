-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.WaitOrderEnables
public import Lemmas.Order.WaitOrderWaits
public import Lemmas.Order.WaitOrderObject
public import Lemmas.MBarrier.MBarrierHistory
public import Lemmas.Order.DependencyWitness
import Tests.Memory.WaitOrderLitmusWitness

/-! Litmus tests for the proposed execution-order axioms (MEM-OBJECT-ORDER-CAUSALITY):
`ObservationCausal`, `ObjectCoherent` and the acyclicity of the dependency order
(`DependencyOk`, DEP-ORDER, through its special case `DepStepAcyclic`).

A: two threads arrive on two mbarriers in opposite orders, and each object's history orders
the arrivals the other way. Not excluded by the proposal, forbidden by `WaitAcyclic`. Whether
PTX admits it is not established (§8.10.4 shows ordinary loads and stores, not mbarrier
operations); by the principle that the model must not exclude what PTX may allow, the model
must not exclude it.

C: load buffering through two mbarriers. Each thread's relaxed wait on one barrier succeeds by
observing the other thread's relaxed arrival, which follows that thread's own wait in program
order. Not excluded by the proposal, forbidden by `WaitAcyclic`. Whether PTX admits it is not
established (§8.10.4 shows ordinary loads and stores, not mbarrier operations); by the same
principle the model must not exclude it. C-sync, the same shape with release arrivals and
acquire waits in one CTA, is forbidden by `ObservationCausal`. C satisfies all three
predicates for its code (`lb_dependencyOk`): each thread polls once and arrives whatever
the poll returned, so the poll is no canonical spin and no arrival depends on it. `lb` and
`lbCode` show only the mbarrier operations (the address register is not initialized and the
initializations are not published). The full witness is in
`Tests/Memory/WaitOrderLitmusWitness.lean`:
`Full.lbFull_consistent` proves `Consistent` (every field) for a concrete kernel whose threads
compute their barrier addresses, initialize the barriers with `mbarrier.init`, publish them
through `bar.warp.sync`, poll once (relaxed) and arrive (relaxed), with a concrete launch and
initial memory; both polls succeed (`Full.lbFull_polls_succeed`) and the execution is not
`TmaUnsafe` (`Full.lbFull_not_tmaUnsafe`). C-loop, where each thread spins on its poll before
arriving, has a dependency cycle (`lbLoop_not_depStepAcyclic`). C-double, a loop with two
polls, is no canonical spin and is unsafe instead (ERR-POLL-SHAPE, `dpLoop_pollShapeUnsafe`).

Failed poll: a failed poll is not an update observed by a later successful poll, although
`MBarrier.UpdateBeforeWait` alone relates them.

B' (full/empty ring self-causation) does not follow from `ObservationCausal`: no causal path
reaches the copy's complete-tx or the commit's arrive-on from a thread instruction, since
asynchronous lifetimes are not part of `stageCausality`. It is excluded by the acyclicity of
the dependency order (`full_empty_not_depStepAcyclic`).

CTA barriers: the order of one logical barrier does not relate records of another ID. -/

namespace PTX.Tests.WaitOrderLitmus
open PTX.MBarrier

/-! ## Executions with only mbarrier operations -/

/-- Only mbarrier initializations, arrivals and relaxed waits, with no asynchronous effects
and no other object histories. -/
structure Quiet (X : Execution) : Prop where
  kinds : ∀ e pc k, X.get e = some ⟨pc, k⟩ → (∃ m c, k = .mbInit m c) ∨
    (∃ m tx c r s, k = .arrive m tx c r s) ∨ (∃ m p ok s, k = .wait m p ok false s)
  async : ∀ i p, ¬ X.AsyncPresent i p
  tensor : ∀ i, X.tensor i = none
  clusters : ∀ c, X.clusters c = []
  barriers : ∀ c, X.barriers c = []
  tmem : ∀ k, X.tmemHistory k = []
  pairing : X.tmemPairing = []

/-- Program position, shifted per thread. -/
def rank (off : Nat → Nat) : AsyncCopy.Ref × Bool → Nat
  | (.thread e, b) => 2 * (e.2 + off e.1) + b.toNat
  | (.async _ _, _) => 0

section Quiet
variable {L : Launch} {X : Execution}

theorem Quiet.kind (hq : Quiet X) {e : EvId} {pc : Nat} {k : Kind} (h : X.get e = some ⟨pc, k⟩)
    (h1 : ∀ m c, k ≠ .mbInit m c) (h2 : ∀ m tx c r s, k ≠ .arrive m tx c r s)
    (h3 : ∀ m p ok s, k ≠ .wait m p ok false s) : False := by
  rcases hq.kinds _ _ _ h with ⟨m, c, hk⟩ | ⟨m, tx, c, r, s, hk⟩ | ⟨m, p, ok, s, hk⟩
  · exact h1 _ _ hk
  · exact h2 _ _ _ _ _ hk
  · exact h3 _ _ _ _ hk

theorem Quiet.not_acquire (hq : Quiet X) {w : EvId} {m : Loc} : ¬ X.AcquireWait w m := by
  rintro ⟨pc, parity, scope, h⟩
  exact hq.kind h (by simp) (by simp) (by simp)

/-- No stage edge: there is no asynchronous stage. -/
theorem Quiet.not_stageEdge (hq : Quiet X) (e f : AsyncCopy.Ref) : ¬ StageEdge X e f := by
  intro hs
  have hna := hq.async
  cases e <;> cases f <;> unfold StageEdge at hs <;> split at hs <;> simp_all

/-- Base causality is program order only. -/
theorem Quiet.baseCausality (hq : Quiet X) {e f : EvId}
    (h : baseCausality L X e f) : e.1 = f.1 ∧ e.2 < f.2 := by
  have base : ∀ {e f : EvId}, (po X e f ∨ CtaBarSync L X e f ∨ MSync L X e f ∨
      ClusterSync L X e f ∨ WarpBarSync L X e f ∨ synchronizesWith L X e f ∨
      FenceSync L X e f) → e.1 = f.1 ∧ e.2 < f.2 := by
    intro e f h
    rcases h with h | ⟨-, key, i, j, hi, -⟩ | ⟨x, w, m, rs, as, -, ⟨⟨pc, q, hw⟩, -⟩, -⟩ |
        ⟨-, i, j, ⟨phase, ha, -⟩, -⟩ | ⟨i, j, ⟨-, mask, inst, ⟨pc, hb⟩, -⟩, -⟩ |
        ⟨a, b, bs, cs, hw, -⟩ | h
    · exact ⟨h.1, h.2.1⟩
    · obtain ⟨idx, st, warp, count, lanes, g, hget, -⟩ := hi.2.2
      simp [hq.barriers] at hget
    · exact (hq.kind hw (by simp) (by simp) (by simp)).elim
    · simp [hq.clusters, ClusterBarrier.ArrivalOf] at ha
    · exact (hq.kind hb (by simp) (by simp) (by simp)).elim
    · rcases hw with ⟨pc, hw⟩ | ⟨o, pc, hw⟩ <;>
        exact (hq.kind hw (by simp) (by simp) (by simp)).elim
    · exact absurd h (not_fenceSync_of_noFence (fun e sem s ⟨pc, hf⟩ =>
        hq.kind hf (by simp) (by simp) (by simp)) e f)
  unfold PTX.baseCausality at h
  induction h with
  | single h => exact base h
  | tail _ h ih =>
    have := base h
    exact ⟨ih.1.trans this.1, by omega⟩

/-- Each causal edge stays in one thread and moves forward. -/
theorem Quiet.cause (hq : Quiet X) {a c : AsyncCopy.Ref × Bool} (h : stageCausality L X a c) :
    ∃ e f, a.1 = .thread e ∧ c.1 = .thread f ∧ e.1 = f.1 ∧
      2 * e.2 + a.2.toNat < 2 * f.2 + c.2.toNat := by
  obtain ⟨e, b⟩ := a
  obtain ⟨f, b'⟩ := c
  rcases h with (⟨rfl, rfl, rfl, hp⟩ | ⟨-, -, hs⟩) | ⟨rfl, rfl, i, j, rfl, rfl, h⟩ |
      ⟨-, -, j, -, i, p, w, ws, -, -, ⟨n, m, -, ⟨pc, q, hw⟩, -⟩, -⟩
  · cases e with
    | thread e => exact ⟨e, e, rfl, rfl, rfl, by simp⟩
    | async i p => exact (hq.async i p hp).elim
  · exact (hq.not_stageEdge _ _ hs).elim
  · have := hq.baseCausality h
    exact ⟨i, j, rfl, rfl, this.1, by simp; omega⟩
  · exact (hq.kind hw (by simp) (by simp) (by simp)).elim

theorem Quiet.chain (hq : Quiet X) {a c : AsyncCopy.Ref × Bool}
    (h : Relation.TransGen (stageCausality L X) a c) :
    ∃ e f, a.1 = .thread e ∧ c.1 = .thread f ∧ e.1 = f.1 ∧
      2 * e.2 + a.2.toNat < 2 * f.2 + c.2.toNat := by
  induction h with
  | single h => exact hq.cause h
  | tail _ h ih =>
    obtain ⟨e, g, ha, hb, h1, h2⟩ := ih
    obtain ⟨g', f, hb', hc, h3, h4⟩ := hq.cause h
    rw [hb] at hb'
    cases hb'
    exact ⟨e, f, ha, hc, h1.trans h3, by omega⟩

theorem Quiet.cause_rank (hq : Quiet X) (off : Nat → Nat) {a c : AsyncCopy.Ref × Bool}
    (h : stageCausality L X a c) : rank off a < rank off c := by
  obtain ⟨e, f, ha, hc, he, hlt⟩ := hq.cause h
  obtain ⟨a, b⟩ := a
  obtain ⟨c, b'⟩ := c
  simp only at ha hc hlt
  subst ha hc
  simp only [rank, he]
  omega

/-- No observation synchronizes: every wait is relaxed and no asynchronous stage exists. -/
theorem Quiet.not_syncObserved (hq : Quiet X) {x w : AsyncCopy.Ref} :
    ¬ SyncObserved L X x w := by
  rintro (⟨-, j, m, pc, q, ws, us, g, -, hj, -⟩ | ⟨i, p, j, k, -, -, hp, -⟩)
  · exact hq.kind hj (by simp) (by simp) (by simp)
  · exact hq.async i p hp

/-- The only witnesses are the counter updates a successful poll observed. -/
theorem Quiet.witness (hq : Quiet X) {x : AsyncCopy.Ref} {j : EvId} (h : Witness L X x j) :
    MbarObserved X x (.thread j) := by
  obtain ⟨fills, hn, -, hf⟩ := id h
  unfold Needs at hn
  cases hj : X.get j with
  | none => simp [hj] at hn
  | some ev =>
    obtain ⟨pc, k⟩ := ev
    rw [hj] at hn
    rcases hq.kinds _ _ _ hj with ⟨m, c, rfl⟩ | ⟨m, tx, c, r, s, rfl⟩ | ⟨m, p, ok, s, rfl⟩
    · simp [KindNeeds] at hn
    · simp [KindNeeds] at hn
    · cases ok
      · simp [KindNeeds] at hn
      · exact h.mbarObserved hj

/-- The dependency steps of a quiet execution whose successful polls are no canonical spins:
the issue-to-return step of a thread event, and a witness before the return it fills. -/
theorem Quiet.depStep {K : Kernel} (hq : Quiet X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∀ exit, ¬ K.CanonicalSpin pc exit)
    {a c : AsyncCopy.Ref × Bool} (h : DepStep L K X a c) :
    a.2 = false ∧ c.2 = true ∧ (a.1 = c.1 ∨ ∃ j, c.1 = .thread j ∧ Witness L X a.1 j) := by
  obtain ⟨e, b⟩ := a
  obtain ⟨f, b'⟩ := c
  rcases h with (⟨rfl, rfl, rfl, hp⟩ | ⟨-, -, hs⟩) | ⟨-, -, i, p, -, -, -, hp, -⟩ |
      ⟨rfl, rfl, j, rfl, hw⟩ | ⟨rfl, rfl, w, j, rfl, rfl, -, hm⟩
  · exact ⟨rfl, rfl, .inl rfl⟩
  · exact (hq.not_stageEdge _ _ hs).elim
  · exact (hq.async i p hp).elim
  · exact ⟨rfl, rfl, .inr ⟨j, rfl, hw⟩⟩
  · exfalso
    cases hg : X.get w with
    | none => simp [hg] at hm
    | some ev =>
      obtain ⟨pc, k⟩ := ev
      rw [hg] at hm
      rcases hq.kinds _ _ _ hg with ⟨m, c, rfl⟩ | ⟨m, tx, c, r, s, rfl⟩ | ⟨m, p, ok, s, rfl⟩ <;>
        simp only [Option.map_some, Kind.resume] at hm
      obtain ⟨pc', exit, m', q, acq, sc, hw, hs, -⟩ := hm
      rw [hg] at hw
      cases hw
      exact hspin _ _ _ _ _ _ hg exit hs

/-- In a quiet execution whose successful polls are no canonical spins, every dependency step
goes from an issue to a return, so no dependency path closes a cycle. -/
theorem Quiet.depStepAcyclic {K : Kernel} (hq : Quiet X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∀ exit, ¬ K.CanonicalSpin pc exit) :
    DepStepAcyclic L K X :=
  acyclic_of_rank (fun n => n.2.toNat) fun a c h => by
    obtain ⟨h1, h2, -⟩ := hq.depStep hspin h
    simp [h1, h2]

/-- Every returned event of a quiet execution is ready: only a successful poll returns, and its
needs are the counter updates it observed, which are present. -/
theorem Quiet.ready (hq : Quiet X) (e : EvId) (_ : Returned X e) : Ready L X e := by
  intro n hn
  unfold Needs at hn
  cases hj : X.get e with
  | none => simp [hj] at hn
  | some ev =>
    obtain ⟨pc, k⟩ := ev
    rw [hj] at hn
    rcases hq.kinds _ _ _ hj with ⟨m, c, rfl⟩ | ⟨m, tx, c, r, s, rfl⟩ | ⟨m, p, ok, s, rfl⟩
    · simp [KindNeeds] at hn
    · simp [KindNeeds] at hn
    · cases ok
      · simp [KindNeeds] at hn
      · simp only [KindNeeds, ite_true, pollNeeds, needsIf, List.mem_flatMap] at hn
        obtain ⟨r, -, hn⟩ := hn
        split at hn
        · simp only [List.mem_singleton] at hn
          subst hn
          exact ⟨r.id, ‹MbarObserved _ _ _›.1, rfl⟩
        · simp at hn

/-- Record positions in a history with distinct operation identities follow its order. -/
theorem before_idxOf {log : List (Record AsyncCopy.Ref)} (hnd : (log.map Record.id).Nodup)
    {a c : AsyncCopy.Ref} (h : Before log a c) :
    (log.map Record.id).idxOf a < (log.map Record.id).idxOf c := by
  obtain ⟨i, j, r, s, hr, rfl, hs, rfl, hij⟩ := h
  have hi : (log.map Record.id)[i]? = some r.id := by simp [hr]
  have hj : (log.map Record.id)[j]? = some s.id := by simp [hs]
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
  rw [← hie, ← hje, List.Nodup.idxOf_getElem hnd, List.Nodup.idxOf_getElem hnd]
  exact hij

/-- In a quiet execution whose successful polls are no canonical spins and whose histories
have distinct identities, dependency steps go from an issue to a return and object edges between
returns go forward in the history, so DEP-ORDER holds. -/
theorem Quiet.dependencyOk {K : Kernel} (hq : Quiet X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∀ exit, ¬ K.CanonicalSpin pc exit)
    (hnd : ∀ m, ((X.objects m).map Record.id).Nodup) : DependencyOk L K X := by
  refine ⟨hq.ready, fun o _ => ?_⟩
  let r : AsyncCopy.Ref × Bool → Nat := fun n => match o with
    | .mbar m => if n.2 then 1 + ((X.objects m).map Record.id).idxOf n.1 else 0
    | _ => n.2.toNat
  refine acyclic_of_rank r fun a c h => ?_
  obtain ⟨e, b⟩ := a
  obtain ⟨f, b'⟩ := c
  rcases h with h | h
  · obtain ⟨rfl, rfl, -⟩ := hq.depStep hspin h
    cases o <;> simp [r]
  · cases o with
    | mbar m =>
      obtain ⟨rfl, rfl, hb⟩ := h
      simp only [r, ite_true]
      have := before_idxOf (hnd m) hb
      omega
    | ctaBar c id =>
      obtain ⟨-, -, -, -, -, -, -, -, k, -, r, -, hr, -⟩ := h
      simp [hq.barriers] at hr
    | cluster c =>
      obtain ⟨-, -, -, -, -, -, k, -, r, -, hr, -⟩ := h
      simp [hq.clusters] at hr
    | tmem cta =>
      obtain ⟨-, -, -, -, -, -, k, -, x, -, hx, -⟩ := h
      simp [hq.tmem] at hx

/-- In a quiet execution, observation is causal: no observation synchronizes. -/
theorem Quiet.observationCausal (hq : Quiet X) : ObservationCausal L X :=
  fun _ _ ho => (hq.not_syncObserved ho).elim

/-- Per-object ranks that the mbarrier histories increase give per-object coherence. -/
theorem Quiet.objectCoherent (hq : Quiet X) (off : OrderObject → Nat → Nat)
    (hmbar : ∀ m a c, ObjectOrder L X (.mbar m) a c →
      rank (off (.mbar m)) a < rank (off (.mbar m)) c) :
    ObjectCoherent L X := fun o =>
  acyclic_of_rank (rank (off o)) fun a c h => by
    rcases h with h | h
    · exact hq.cause_rank _ h
    · obtain ⟨e, b⟩ := a
      obtain ⟨f, b'⟩ := c
      cases o with
      | mbar m => exact hmbar m _ _ h.1
      | ctaBar c id =>
        obtain ⟨-, -, -, -, -, -, -, -, k, -, r, -, hr, -⟩ := h
        simp [hq.barriers] at hr
      | cluster c =>
        obtain ⟨-, -, -, -, -, -, k, -, r, -, hr, -⟩ := h
        simp [hq.clusters] at hr
      | tmem cta =>
        obtain ⟨-, -, -, -, -, -, k, -, x, -, hx, -⟩ := h
        simp [hq.tmem] at hx

end Quiet

def A : Loc := ⟨.shared, 0, 0⟩
def B : Loc := ⟨.shared, 0, 8⟩

theorem A_ne_B : A ≠ B := by decide

/-! ## A — opposite-order arrivals on two barriers -/

def s0 : State := ⟨0, 2, 2, 0, true⟩
def s1 : State := ⟨0, 2, 1, 0, true⟩
def s2 : State := ⟨1, 2, 2, 0, false⟩

/-- Thread 0 initializes `A` and `B`; thread 1 arrives on `A` before thread 0 does. -/
def logA : List (Record AsyncCopy.Ref) := [
  ⟨.thread (0, 0), .init 2, ⟨some s0, none, none⟩, none⟩,
  ⟨.thread (1, 1), .arrive 1 0, ⟨some s1, none, none⟩, none⟩,
  ⟨.thread (0, 2), .arrive 1 0, ⟨some s2, none, none⟩, none⟩]

/-- Thread 0 arrives on `B` before thread 1 does. -/
def logB : List (Record AsyncCopy.Ref) := [
  ⟨.thread (0, 1), .init 2, ⟨some s0, none, none⟩, none⟩,
  ⟨.thread (0, 3), .arrive 1 0, ⟨some s1, none, none⟩, none⟩,
  ⟨.thread (1, 0), .arrive 1 0, ⟨some s2, none, none⟩, none⟩]

/-- Both histories are the object transitions of OBJ-MBAR-STATE. -/
theorem logA_checked : CheckedLog logA :=
  checkedLog_of_replay (ops := logA.map (fun r => (r.id, r.action))) (by rfl) (by decide)

theorem logB_checked : CheckedLog logB :=
  checkedLog_of_replay (ops := logB.map (fun r => (r.id, r.action))) (by rfl) (by decide)

/-- Thread 0: init A, init B, arrive A, arrive B. Thread 1: arrive B, arrive A. -/
def opp : Execution where
  tr
    | 0 => [⟨0, .mbInit A 2⟩, ⟨1, .mbInit B 2⟩, ⟨2, .arrive A 0⟩, ⟨3, .arrive B 0⟩]
    | 1 => [⟨3, .arrive B 0⟩, ⟨2, .arrive A 0⟩]
    | _ => []
  rf _ _ := none
  objects m := if m = A then logA else if m = B then logB else []

theorem opp_quiet : Quiet opp where
  kinds i pc k h := by
    obtain ⟨t, n⟩ := i
    rcases t with _ | _ | t <;> rcases n with _ | _ | _ | _ | n <;>
      simp [Execution.get, opp] at h <;> simp [← h.2]
  async i p := by cases p <;> simp [Execution.AsyncPresent, Execution.MmaRead, opp]
  tensor _ := rfl
  clusters _ := rfl
  barriers _ := rfl
  tmem _ := rfl
  pairing := rfl

theorem opp_not_waited (m : Loc) {j : Nat} {w : Record AsyncCopy.Ref}
    (h : (opp.objects m)[j]? = some w) : w.reply.waited = none := by
  have hw := List.mem_of_getElem? h
  simp only [opp] at hw
  split_ifs at hw <;> simp [logA, logB] at hw <;> rcases hw with rfl | rfl | rfl <;> rfl

def offB (t : Nat) : Nat := if t = 1 then 4 else 0

def oppOff : OrderObject → Nat → Nat
  | .mbar m => if m = B then offB else fun _ => 0
  | _ => fun _ => 0

/-- Each history increases the rank chosen for its object. -/
theorem opp_mbar_rank (L : Launch) (m : Loc) {a c : AsyncCopy.Ref × Bool}
    (h : ObjectOrder L opp (.mbar m) a c) :
    rank (oppOff (.mbar m)) a < rank (oppOff (.mbar m)) c := by
  obtain ⟨e, b⟩ := a
  obtain ⟨f, b'⟩ := c
  obtain ⟨rfl, rfl, i, j, r, s, hi, rfl, hj, rfl, hij⟩ := h
  by_cases hA : m = A
  · subst hA
    have hl : opp.objects A = logA := by simp [opp]
    have ho : oppOff (.mbar A) = fun _ => 0 := by simp [oppOff, A_ne_B]
    rw [hl] at hi hj
    rw [ho]
    rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;>
      simp [logA] at hi hj hij <;> subst hi hj <;> simp [rank]
  · by_cases hB : m = B
    · subst hB
      have hl : opp.objects B = logB := by simp [opp, hA]
      have ho : oppOff (.mbar B) = offB := by simp [oppOff]
      rw [hl] at hi hj
      rw [ho]
      rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;>
        simp [logB] at hi hj hij <;> subst hi hj <;> simp [rank, offB]
    · simp [opp, hA, hB] at hi

/-- `opp` satisfies the observation axiom: it has no acquire wait, so no observation
synchronizes. -/
theorem opp_observationCausal (L : Launch) : ObservationCausal L opp :=
  opp_quiet.observationCausal

/-- `opp` satisfies per-object coherence: each object's order alone fits program order. -/
theorem opp_objectCoherent (L : Launch) : ObjectCoherent L opp :=
  opp_quiet.objectCoherent oppOff (opp_mbar_rank L)

/-- `opp` violates `WaitAcyclic`: program order with both histories is cyclic. -/
theorem opp_not_waitAcyclic (L : Launch) : ¬ WaitAcyclic L opp := by
  intro h
  apply h (.thread (0, 2), true)
  have hB1 : (opp.objects B)[1]? = some (logB[1]'(by decide)) := by simp [opp, A_ne_B.symm]
  have hB2 : (opp.objects B)[2]? = some (logB[2]'(by decide)) := by simp [opp, A_ne_B.symm]
  have hA1 : (opp.objects A)[1]? = some (logA[1]'(by decide)) := by simp [opp]
  have hA2 : (opp.objects A)[2]? = some (logA[2]'(by decide)) := by simp [opp]
  -- arrive A (0,2) → arrive B (0,3) → B: (1,0) → arrive A (1,1) → A: (0,2)
  exact (((Waits.po (L := L) (i := (0, 2)) (j := (0, 3)) ⟨rfl, by decide, by decide⟩).tail
    (Waits.node ⟨_, rfl⟩)).tail (Waits.before ⟨1, 2, _, _, hB1, rfl, hB2, rfl, by decide⟩)).trans
    (((Waits.po (i := (1, 0)) (j := (1, 1)) ⟨rfl, by decide, by decide⟩).tail
      (Waits.node ⟨_, rfl⟩)).tail (Waits.before ⟨1, 2, _, _, hA1, rfl, hA2, rfl, by decide⟩))

/-! ## C — load buffering through two mbarriers -/

def t0 : State := ⟨0, 1, 1, 0, true⟩
def t1 : State := ⟨1, 1, 1, 0, false⟩
def t2 : State := ⟨1, 1, 1, 0, true⟩

/-- Thread 2 initializes `A`; thread 0 arrives; thread 1's poll observes phase 0. -/
def lbA : List (Record AsyncCopy.Ref) := [
  ⟨.thread (2, 0), .init 1, ⟨some t0, none, none⟩, none⟩,
  ⟨.thread (0, 1), .arrive 1 0, ⟨some t1, none, none⟩, none⟩,
  ⟨.thread (1, 0), .pollParity 0 true, ⟨some t2, some true, some 0⟩, none⟩]

/-- Thread 2 initializes `B`; thread 1 arrives; thread 0's poll observes phase 0. -/
def lbB : List (Record AsyncCopy.Ref) := [
  ⟨.thread (2, 1), .init 1, ⟨some t0, none, none⟩, none⟩,
  ⟨.thread (1, 1), .arrive 1 0, ⟨some t1, none, none⟩, none⟩,
  ⟨.thread (0, 0), .pollParity 0 true, ⟨some t2, some true, some 0⟩, none⟩]

theorem lbA_checked : CheckedLog lbA :=
  checkedLog_of_replay (ops := lbA.map (fun r => (r.id, r.action))) (by rfl) (by decide)

theorem lbB_checked : CheckedLog lbB :=
  checkedLog_of_replay (ops := lbB.map (fun r => (r.id, r.action))) (by rfl) (by decide)

/-- T0: wait B (succeeds); arrive A. T1: wait A (succeeds); arrive B. T2 initializes both.
`sync = false`: relaxed arrivals and waits; `sync = true`: release arrivals, acquire waits,
all at `.cta` scope. -/
def lb (sync : Bool) : Execution where
  tr
    | 0 => [⟨0, .wait B 0 true sync .cta⟩, ⟨1, .arrive A 0 1 sync .cta⟩]
    | 1 => [⟨2, .wait A 0 true sync .cta⟩, ⟨3, .arrive B 0 1 sync .cta⟩]
    | 2 => [⟨4, .mbInit A 1⟩, ⟨5, .mbInit B 1⟩]
    | _ => []
  rf _ _ := none
  objects m := if m = A then lbA else if m = B then lbB else []

theorem lb_A (sync : Bool) : (lb sync).objects A = lbA := by simp [lb]
theorem lb_B (sync : Bool) : (lb sync).objects B = lbB := by simp [lb, A_ne_B.symm]

theorem lb_quiet : Quiet (lb false) where
  kinds i pc k h := by
    obtain ⟨t, n⟩ := i
    rcases t with _ | _ | _ | t <;> rcases n with _ | _ | n <;>
      simp [Execution.get, lb] at h <;> simp [← h.2]
  async i p := by cases p <;> simp [Execution.AsyncPresent, Execution.MmaRead, lb]
  tensor _ := rfl
  clusters _ := rfl
  barriers _ := rfl
  tmem _ := rfl
  pairing := rfl

/-- The only observations: thread 1 observes thread 0's arrival on `A`, and thread 0
observes thread 1's arrival on `B`. -/
theorem lb_updates (sync : Bool) {m : Loc} {x w : AsyncCopy.Ref}
    (h : UpdateBeforeWait ((lb sync).objects m) x w) :
    (x = .thread (0, 1) ∧ w = .thread (1, 0)) ∨ (x = .thread (1, 1) ∧ w = .thread (0, 0)) := by
  obtain ⟨i, j, r, s, phase, hr, rfl, -, hs, rfl, -, -, hij, hp, -⟩ := h
  by_cases hA : m = A
  · subst hA
    rw [lb_A] at hr hs hp
    rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;>
      simp [lbA, phaseAt, stateBefore] at hr hs hij hp
    subst hr hs
    simp
  · by_cases hB : m = B
    · subst hB
      rw [lb_B] at hr hs hp
      rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;>
        simp [lbB, phaseAt, stateBefore] at hr hs hij hp
      subst hr hs
      simp
    · simp [lb, hA, hB] at hr

def lbOff : OrderObject → Nat → Nat
  | .mbar m => if m = A then (fun t => if t = 1 then 2 else 0)
    else (fun t => if t = 0 then 3 else if t = 1 then 1 else 0)
  | _ => fun _ => 0

theorem lb_mbar_rank (L : Launch) (m : Loc) {a c : AsyncCopy.Ref × Bool}
    (h : ObjectOrder L (lb false) (.mbar m) a c) :
    rank (lbOff (.mbar m)) a < rank (lbOff (.mbar m)) c := by
  obtain ⟨e, b⟩ := a
  obtain ⟨f, b'⟩ := c
  obtain ⟨rfl, rfl, i, j, r, s, hi, rfl, hj, rfl, hij⟩ := h
  by_cases hA : m = A
  · subst hA
    rw [lb_A] at hi hj
    rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;>
      simp [lbA] at hi hj hij <;> subst hi hj <;> simp [rank, lbOff]
  · by_cases hB : m = B
    · subst hB
      rw [lb_B] at hi hj
      rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;>
        simp [lbB] at hi hj hij <;> subst hi hj <;> simp [rank, lbOff, A_ne_B.symm]
    · simp [lb, hA, hB] at hi

/-- C (relaxed, both waits succeed) satisfies the observation axiom: its relaxed observations
do not synchronize (MEM-MBAR-SYNCHRONIZES), and causality stays in one thread. -/
theorem lb_observationCausal (L : Launch) : ObservationCausal L (lb false) :=
  lb_quiet.observationCausal

/-- C satisfies per-object coherence. -/
theorem lb_objectCoherent (L : Launch) : ObjectCoherent L (lb false) :=
  lb_quiet.objectCoherent lbOff (lb_mbar_rank L)

/-- C (in either form) violates `WaitAcyclic`: program order with both histories is
cyclic. -/
theorem lb_not_waitAcyclic (L : Launch) (sync : Bool) : ¬ WaitAcyclic L (lb sync) := by
  intro h
  apply h (.thread (0, 1), true)
  have hA1 : ((lb sync).objects A)[1]? = some (lbA[1]'(by decide)) := by simp [lb_A]
  have hA2 : ((lb sync).objects A)[2]? = some (lbA[2]'(by decide)) := by simp [lb_A]
  have hB1 : ((lb sync).objects B)[1]? = some (lbB[1]'(by decide)) := by simp [lb_B]
  have hB2 : ((lb sync).objects B)[2]? = some (lbB[2]'(by decide)) := by simp [lb_B]
  -- arrive A (0,1) → A: wait (1,0) → arrive B (1,1) → B: wait (0,0) → arrive A (0,1)
  exact (((((Relation.TransGen.single
    (Waits.before (L := L) ⟨1, 2, _, _, hA1, rfl, hA2, rfl, by decide⟩)).trans
    (Waits.trace (i := (1, 0)) (j := (1, 1)) ⟨rfl, by decide, by simp [lb]⟩)).tail
    (Waits.node ⟨_, rfl⟩)).tail
    (Waits.before ⟨1, 2, _, _, hB1, rfl, hB2, rfl, by decide⟩)).trans
    ((Waits.trace (i := (0, 0)) (j := (0, 1)) ⟨rfl, by decide, by simp [lb]⟩).tail
      (Waits.node ⟨_, rfl⟩)))

/-- C-sync: with release arrivals and acquire waits in one CTA, thread 0's wait causally
precedes thread 1's arrival on `B` (program order, then thread 0's release arrival on `A`
synchronizes with thread 1's acquire wait), and that arrival is what the wait observed. -/
theorem lbSync_not_observationCausal (L : Launch) (hcta : SameCta L 0 1) :
    ¬ ObservationCausal L (lb true) := by
  intro h
  have hupdA : UpdateBeforeWait ((lb true).objects A) (.thread (0, 1)) (.thread (1, 0)) := by
    rw [lb_A]; exact ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
        fun _ _ _ h2 _ => absurd h2 (by omega)⟩
  have hupdB : UpdateBeforeWait ((lb true).objects B) (.thread (1, 1)) (.thread (0, 0)) := by
    rw [lb_B]; exact ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
        fun _ _ _ h2 _ => absurd h2 (by omega)⟩
  have hobs : SyncObserved L (lb true) (.thread (1, 1)) (.thread (0, 0)) :=
    .inl ⟨⟨⟨_, rfl⟩, (0, 0), B, true, .cta, rfl, ⟨⟨0, 0, rfl⟩, hupdB⟩, by rw [lb_B]; simp [lbB,
      CounterUpdate]⟩, (0, 0), B, 0, 0, .cta, .cta, 1, rfl, rfl,
      .inl ⟨(1, 1), B, 0, 1, rfl, rfl, ⟨3, rfl⟩⟩,
      ⟨⟨hcta.2.1, hcta.1, hcta.2.2.symm⟩, hcta⟩⟩
  have hsync : MSync L (lb true) (0, 1) (1, 1) :=
    ⟨(0, 1), (1, 0), A, .cta, .cta, ⟨0, 1, 1, rfl⟩, ⟨⟨2, 0, rfl⟩, hupdA⟩,
      ⟨hcta, hcta.2.1, hcta.1, hcta.2.2.symm⟩, rfl, by decide, by simp [lb], rfl, le_rfl⟩
  have hhb : baseCausality L (lb true) (0, 0) (1, 1) :=
    .head (b := (0, 1)) (Or.inl ⟨rfl, by decide, by simp [lb], by simp [lb, SameAccess,
      Execution.get, Event.acc]⟩)
      (.single (Or.inr (Or.inr (Or.inl hsync))))
  exact h _ _ hobs (.single (.inr (.inl ⟨rfl, rfl, (0, 0), (1, 1), rfl, rfl, hhb⟩)))

/-! ### C under the dependency order: a single poll resumes nothing

The code of C: each thread polls once and then arrives whatever the poll returned
(positions as in `lb`: thread 0 at 0 and 1, thread 1 at 2 and 3). -/

def waitIns (off : Int) : Instr := { op := .mbarWait 0 1 off (.imm 0) false .cta }
def arriveIns (off : Int) : Instr :=
  { op := .mbarArrive 1 off (.imm 0) (.imm 1) false false .cta }

def lbCode : Kernel where
  name := "lb"
  params := []
  code := [waitIns 8, arriveIns 0, waitIns 0, arriveIns 8]

/-- In `lbCode`, the poll at 0 or 2 is followed by the arrival, not by a branch: no poll is a
canonical spin (DEP-CANONICAL-SPIN). -/
theorem lbCode_not_canonicalSpin (pc : Nat) (hpc : pc = 0 ∨ pc = 2) (exit : Nat) :
    ¬ lbCode.CanonicalSpin pc exit := by
  rintro ⟨h, -⟩
  have hn : lbCode.spinExit? pc = none := by rcases hpc with rfl | rfl <;> decide
  rw [Kernel.SpinShape, hn] at h
  cases h

/-- The successful polls of C are at 0 and 2. -/
theorem lb_no_spin (w : EvId) (pc : Nat) (m : Loc) (q : Nat) (acq : Bool) (sc : MbarScope)
    (hw : (lb false).get w = some ⟨pc, .wait m q true acq sc⟩) (exit : Nat) :
    ¬ lbCode.CanonicalSpin pc exit := by
  obtain ⟨t, n⟩ := w
  rcases t with _ | _ | _ | t <;> rcases n with _ | _ | n <;>
    simp [Execution.get, lb] at hw
  · exact lbCode_not_canonicalSpin pc (.inl hw.1.symm) exit
  · exact lbCode_not_canonicalSpin pc (.inr hw.1.symm) exit

/-- C has no dependency cycle for its code: its arrivals do not depend on the polls. -/
theorem lb_depStepAcyclic (L : Launch) : DepStepAcyclic L lbCode (lb false) :=
  lb_quiet.depStepAcyclic lb_no_spin

/-- C satisfies DEP-ORDER (EXT-ENABLES-OBJECT) for its code: the union of the dependency order
with one mbarrier's order has no cycle, since program order alone is not a dependency edge
(arrive A before poll A in `A`'s order, then poll A → arrive B is plain program order). -/
theorem lb_dependencyOk (L : Launch) : DependencyOk L lbCode (lb false) :=
  lb_quiet.dependencyOk lb_no_spin (fun m => by
    by_cases hA : m = A
    · subst hA; rw [lb_A]; decide
    · by_cases hB : m = B
      · subst hB; rw [lb_B]; decide
      · simp [lb, hA, hB])

/-! ### C-loop: spinning polls

Each thread spins on its poll and arrives only after it succeeded:
`L: try_wait p, [B]; @p bra D; bra L; D: arrive [A]; ret` (thread 0 at 0–4) and the same
with `A` and `B` exchanged (thread 1 at 5–9). Both polls succeed by observing the other
thread's arrival, as in C. Each poll is a canonical spin (`loop_spin0`, `loop_spin1`), so its
thread's arrival resumes after its return (`Resumes`), and each arrival is the witness of the
other thread's poll: the two observations close a dependency cycle. -/

def loopCode : Kernel where
  name := "lbLoop"
  params := []
  code := [waitIns 8, { guard := some (0, false), op := .bra 3 false }, { op := .bra 0 false },
    arriveIns 0, { op := .ret },
    waitIns 0, { guard := some (0, false), op := .bra 8 false }, { op := .bra 5 false },
    arriveIns 8, { op := .ret }]

/-- C with the positions of `loopCode`; the histories are those of C. -/
def lbLoop : Execution where
  tr
    | 0 => [⟨0, .wait B 0 true false .cta⟩, ⟨3, .arrive A 0 1 false .cta⟩]
    | 1 => [⟨5, .wait A 0 true false .cta⟩, ⟨8, .arrive B 0 1 false .cta⟩]
    | 2 => [⟨4, .mbInit A 1⟩, ⟨9, .mbInit B 1⟩]
    | _ => []
  rf _ _ := none
  objects m := if m = A then lbA else if m = B then lbB else []

/-- The poll at 0 is a canonical spin exiting to 3, the poll at 5 one exiting to 8. -/
theorem loop_spin0 : loopCode.CanonicalSpin 0 3 :=
  ⟨by unfold Kernel.SpinShape; decide, 0, by decide, by unfold Kernel.SpinPred; decide⟩
theorem loop_spin1 : loopCode.CanonicalSpin 5 8 :=
  ⟨by unfold Kernel.SpinShape; decide, 0, by decide, by unfold Kernel.SpinPred; decide⟩

/-- C-loop has a dependency cycle. -/
theorem lbLoop_not_depStepAcyclic (L : Launch) : ¬ DepStepAcyclic L loopCode lbLoop := by
  intro h
  have hA : lbLoop.objects A = lbA := by simp [lbLoop]
  have hB : lbLoop.objects B = lbB := by simp [lbLoop, A_ne_B.symm]
  have obsA : Witness L lbLoop (.thread (0, 1)) (1, 0) :=
    Witness.of_mbarObserved ⟨⟨_, rfl⟩, (1, 0), A, false, .cta, rfl, ⟨⟨5, 0, rfl⟩, by
      rw [hA]; exact ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      by decide, rfl, rfl, fun _ _ h1 h2 _ => absurd h2
        (by omega)⟩⟩, by rw [hA]; simp [lbA, CounterUpdate]⟩
  have obsB : Witness L lbLoop (.thread (1, 1)) (0, 0) :=
    Witness.of_mbarObserved ⟨⟨_, rfl⟩, (0, 0), B, false, .cta, rfl, ⟨⟨0, 0, rfl⟩, by
      rw [hB]; exact ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      by decide, rfl, rfl, fun _ _ h1 h2 _ => absurd h2
        (by omega)⟩⟩, by rw [hB]; simp [lbB, CounterUpdate]⟩
  have g0 : Resumes loopCode lbLoop (0, 0) (0, 1) :=
    ⟨⟨rfl, by decide, by simp [lbLoop]⟩, by
      simp only [Execution.get, lbLoop, List.getElem?_cons_zero, Option.map_some, Kind.resume]
      exact ⟨0, 3, B, 0, false, .cta, rfl, loop_spin0, rfl, by decide, by simp⟩⟩
  have g1 : Resumes loopCode lbLoop (1, 0) (1, 1) :=
    ⟨⟨rfl, by decide, by simp [lbLoop]⟩, by
      simp only [Execution.get, lbLoop, List.getElem?_cons_zero, Option.map_some, Kind.resume]
      exact ⟨5, 8, A, 0, false, .cta, rfl, loop_spin1, rfl, by decide, by simp⟩⟩
  -- poll (0,0) → arrive A (0,1) → poll (1,0) → arrive B (1,1) → poll (0,0)
  exact h (.thread (0, 0), true) (.tail (.tail (.tail (.single (DepStep.of_resumes L g0))
    (DepStep.of_witness L obsA)) (DepStep.of_resumes L g1)) (DepStep.of_witness L obsB))

/-- C-loop violates DEP-ORDER (its dependency steps alone already close a cycle). -/
theorem lbLoop_not_dependencyOk (L : Launch) : ¬ DependencyOk L loopCode lbLoop :=
  fun h => lbLoop_not_depStepAcyclic L (DepStepAcyclic.of_dependency h)

/-! ### C-double: a wait loop with two polls

`L: try_wait p, [B]; @p bra D; try_wait p, [B]; @!p bra L; bra D; D: arrive [A]; ret`
(thread 0 at 0–6) and the same with `A` and `B` exchanged (thread 1 at 7–13). A failed poll
leads to the other poll of the loop, not back to itself. Neither poll is a canonical spin
(DEP-CANONICAL-SPIN), so neither resumes the arrival; instead, an execution that performs such
a poll is unsafe (ERR-POLL-SHAPE, `dpLoop_pollShapeUnsafe`). -/

def dpCode : Kernel where
  name := "doublePoll"
  params := []
  code := [waitIns 8, { guard := some (0, false), op := .bra 5 false }, waitIns 8,
    { guard := some (0, true), op := .bra 0 false }, { op := .bra 5 false }, arriveIns 0,
    { op := .ret },
    waitIns 0, { guard := some (0, false), op := .bra 12 false }, waitIns 0,
    { guard := some (0, true), op := .bra 7 false }, { op := .bra 12 false }, arriveIns 8,
    { op := .ret }]

/-- No poll of the double-poll loop is a canonical spin. -/
theorem dp_not_canonicalSpin (pc : Nat) (hpc : pc = 0 ∨ pc = 2 ∨ pc = 7 ∨ pc = 9)
    (exit : Nat) : ¬ dpCode.CanonicalSpin pc exit := by
  rintro ⟨h, -⟩
  have hn : dpCode.spinExit? pc = none := by
    rcases hpc with rfl | rfl | rfl | rfl <;> decide
  rw [Kernel.SpinShape, hn] at h
  cases h

/-- C with the positions of `dpCode`: both first polls succeed. -/
def dpLoop : Execution where
  tr
    | 0 => [⟨0, .wait B 0 true false .cta⟩, ⟨5, .arrive A 0 1 false .cta⟩]
    | 1 => [⟨7, .wait A 0 true false .cta⟩, ⟨12, .arrive B 0 1 false .cta⟩]
    | 2 => [⟨6, .mbInit A 1⟩, ⟨13, .mbInit B 1⟩]
    | _ => []
  rf _ _ := none
  objects m := if m = A then lbA else if m = B then lbB else []

/-- C-double is unsafe (ERR-POLL-SHAPE): its poll at 0 is no canonical spin, and its result is
read by the branch after it. -/
theorem dpLoop_pollShapeUnsafe : PollShapeUnsafe dpCode dpLoop :=
  ⟨(0, 0), 0, B, 0, true, false, .cta, rfl, fun ⟨exit, h⟩ => dp_not_canonicalSpin 0 (.inl rfl)
    exit h, fun ⟨⟨p, hp, hs⟩, _⟩ => by
      have : p = 0 := by simpa [Kernel.pollReg, dpCode, waitIns] using hp.symm
      subst this
      exact absurd hs (by unfold Kernel.SpinPred; decide)⟩

/-! ### A poll that does not spin on its own object

`0: try_wait p, [r]; 1: mov r, 8; 2: @p bra 4; 3: bra 0; 4: arrive [r]`. After a failed
first poll the thread returns to the same instruction, but the address register now names
another object, so the arrival does not depend on the first poll's result. The poll at 0 is
no canonical spin: the instruction after it is not the branch on its result, so no dependency
edge from it is added (the earlier, wider spin rule, which only asked for a return to the same
`pc`, held here). -/

def swCode : Kernel where
  name := "switch"
  params := []
  code := [waitIns 0, { op := .move ⟨.scalar, .int .b 32, [some 1], [.imm 8]⟩ },
    { guard := some (0, false), op := .bra 4 false },
    { op := .bra 0 false }, arriveIns 0]

/-- The poll at 0 is no canonical spin. -/
theorem swCode_not_canonicalSpin (exit : Nat) : ¬ swCode.CanonicalSpin 0 exit := by
  rintro ⟨h, -⟩
  have hn : swCode.spinExit? 0 = none := by decide
  rw [Kernel.SpinShape, hn] at h
  cases h

/-! ## Failed poll -/

def M : Loc := ⟨.shared, 0, 0⟩

def fpLog : List (Record AsyncCopy.Ref) := [
  ⟨.thread (0, 0), .init 1, ⟨some t0, none, none⟩, none⟩,
  ⟨.thread (0, 1), .pollParity 0 false, ⟨some t0, some false, none⟩, none⟩,
  ⟨.thread (0, 2), .arrive 1 0, ⟨some t1, none, none⟩, none⟩,
  ⟨.thread (0, 3), .pollParity 0 true, ⟨some t2, some true, some 0⟩, none⟩]

theorem fpLog_checked : CheckedLog fpLog :=
  checkedLog_of_replay (ops := fpLog.map (fun r => (r.id, r.action))) (by rfl) (by decide)

/-- init; failed poll; arrive; successful poll (all relaxed). -/
def fp : Execution where
  tr
    | 0 => [⟨0, .mbInit M 1⟩, ⟨1, .wait M 0 false false .cta⟩, ⟨2, .arrive M 0 1 false .cta⟩,
        ⟨3, .wait M 0 true false .cta⟩]
    | _ => []
  rf _ _ := none
  objects m := if m = M then fpLog else []

theorem fp_quiet : Quiet fp where
  kinds i pc k h := by
    obtain ⟨t, n⟩ := i
    rcases t with _ | t <;> rcases n with _ | _ | _ | _ | n <;>
      simp [Execution.get, fp] at h <;> simp [← h.2]
  async i p := by cases p <;> simp [Execution.AsyncPresent, Execution.MmaRead, fp]
  tensor _ := rfl
  clusters _ := rfl
  barriers _ := rfl
  tmem _ := rfl
  pairing := rfl

theorem fp_M : fp.objects M = fpLog := by simp [fp]

/-- The history alone puts the failed poll in the observed phase. -/
theorem fp_failed_updateBeforeWait :
    UpdateBeforeWait (fp.objects M) (.thread (0, 1)) (.thread (0, 3)) := by
  rw [fp_M]; exact ⟨1, 3, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
    fun k s h1 h2 hk => by
      obtain rfl : k = 2 := by omega
      simp [fpLog] at hk; subst hk; simp⟩

/-- A failed poll is not an observed update, so it is no witness of the successful poll. -/
theorem fp_failed_not_witness (L : Launch) : ¬ Witness L fp (.thread (0, 1)) (0, 3) := by
  intro h
  obtain ⟨_, _, m, _, _, _, ⟨_, i, _, r, _, _, hr, _⟩, hu⟩ := fp_quiet.witness h
  have hm : m = M := by
    by_contra hm
    simp [fp, hm] at hr
  subst hm
  rw [fp_M] at hu
  have := hu ⟨.thread (0, 1), .pollParity 0 false, ⟨some t0, some false, none⟩, none⟩
    (by simp [fpLog]) rfl
  simp [CounterUpdate] at this

/-- The arrival is the observed update, a witness of the successful poll. -/
theorem fp_arrive_witness (L : Launch) : Witness L fp (.thread (0, 2)) (0, 3) :=
  Witness.of_mbarObserved ⟨⟨_, rfl⟩, (0, 3), M, false, .cta, rfl, ⟨⟨3, 0, rfl⟩, by
    rw [fp_M]; exact ⟨2, 3, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
    fun _ _ _ h2 _ => absurd h2 (by omega)⟩⟩, by rw [fp_M]; simp [fpLog, CounterUpdate]⟩

/-! ## B' — the full/empty ring

v2 forbade the ring in which the consumer's acquire wait `waitF` on the full barrier observes
a tensor copy's complete-tx, its program-order successor `commit` issues `tcgen05.commit`,
the producer's wait `waitE` on the empty barrier observes that commit's arrive-on, and
`waitE`'s program-order successor issues that same copy. The proof composed
`waitE` → (program order) copy issue → (issue to complete-tx) → (synchronizes-with) `commit`
→ (issue to arrive-on), which `waitE` observed. Both issue edges are asynchronous lifetime
edges, which `stageCausality` no longer contains: §8.9.1.1 says the complete-tx "does not
transitively establish ordering with respect to prior instructions from the issuing thread", and no
quote gives the commit's issue an edge that may be chained. Neither notification is reachable from
`waitE`, so `ObservationCausal` does not forbid the ring. The dependency order (DEP-ORDER) does:
each wait is a canonical spin, so its thread's later issue resumes after its return, each
notification is a witness of the wait that observed it, and each notification's stage exists
only because its instruction was issued; this is not memory ordering and is never chained with
`stageCausality`. -/

/-- Neither notification of B' is causally after the producer's wait. -/
theorem full_empty_notifications_unreached {L : Launch} {X : Execution}
    {copy commit waitE : EvId} {rank : Fin 16} :
    ¬ Relation.TransGen (stageCausality L X) (.thread waitE, true) (.async copy (.notify .load),
        false) ∧
    ¬ Relation.TransGen (stageCausality L X) (.thread waitE, true)
      (.async commit (.tcNotify rank), false) :=
  ⟨stageCausality.not_to_async, stageCausality.not_to_async⟩

/-- B' under the dependency order: the self-satisfying full/empty ring is excluded. The
copy's complete-tx is a witness of the consumer's wait `waitF`, whose return the commit resumes
after; the commit's arrive-on is a witness of the producer's wait `waitE`, whose return the copy
resumes after; the copy's issue precedes its write, whose completion precedes its complete-tx
(DEP-ASYNC-STAGE-ORDER). The returns are as a kernel discharges them (`Resumes` through a
canonical spin). -/
theorem full_empty_not_depStepAcyclic {L : Launch} {K : Kernel} {X : Execution}
    {copy commit waitE waitF : EvId} {x y k : Nat} {rank : Fin 16}
    (hcopy : X.RefPresent (.thread copy)) (hwrite : X.AsyncPresent copy (.write (.load x y k)))
    (hnote : X.AsyncPresent copy (.notify .load))
    (hobsF : Witness L X (.async copy (.notify .load)) waitF)
    (hguardF : Resumes K X waitF commit)
    (hcommit : X.RefPresent (.thread commit)) (hcnote : X.AsyncPresent commit (.tcNotify rank))
    (hobsE : Witness L X (.async commit (.tcNotify rank)) waitE)
    (hguardE : Resumes K X waitE copy) :
    ¬ DepStepAcyclic L K X := fun h =>
  h (.thread waitE, true)
    (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.single (DepStep.of_resumes L hguardE))
      (DepStep.issue (p := .write (.load x y k)) hcopy hwrite (by simp) (by simp) (by simp)
        (by simp))) (DepStep.node hwrite))
      (DepStep.stage (c := (.async copy (.notify .load), false))
        (.inr ⟨rfl, rfl, rfl, rfl, hwrite, hnote⟩)))
      (DepStep.of_witness L hobsF)) (DepStep.of_resumes L hguardF))
      (DepStep.issue (p := .tcNotify rank) hcommit hcnote (by simp) (by simp) (by simp)
        (by simp))) (DepStep.of_witness L hobsE))

/-! ## CTA barriers — one order per logical barrier -/

/-- Thread 0 arrives at barrier 0 then 1; thread 32 at barrier 1 then 0. The CTA's bank
records: (0,0) on 0, (32,0) on 1, (0,1) on 1, (32,1) on 0. -/
def bars : Execution where
  tr
    | 0 => [⟨0, .bar 0⟩, ⟨1, .bar 1⟩]
    | 32 => [⟨0, .bar 1⟩, ⟨1, .bar 0⟩]
    | _ => []
  rf _ _ := none
  barriers
    | 0 => [.arrival 0 0 none [(0, (0, 0))], .arrival 1 1 none [(32, (32, 0))],
        .arrival 1 0 none [(0, (0, 1))], .arrival 0 1 none [(32, (32, 1))]]
    | _ => []

/-- The bank-wide order of `Waits` relates an arrival on barrier 0 to one on barrier 1. -/
theorem bars_bank_orders (L : Launch) :
    Waits L bars (.thread (0, 0), false) (.thread (32, 0), false) :=
  .inr (.inr (.inl ⟨(0, 0), (32, 0), rfl, rfl, ⟨_, rfl⟩, ⟨_, rfl⟩,
    .inl ⟨rfl, rfl, 0, 0, 1, _, _, rfl, rfl, by decide, by simp [CtaBarrier.Record.refs],
      by simp [CtaBarrier.Record.refs]⟩⟩))

/-- No single logical barrier's order relates them. -/
theorem bars_cross_id_unordered (L : Launch) (id : Fin 16) :
    ¬ ObjectOrder L bars (.ctaBar 0 id) (.thread (0, 0), false) (.thread (32, 0), false) := by
  rintro ⟨-, -, i, j, hi, hj, -, -, k, l, r, q, hr, hq, -, hor, hoq, hir, hjq⟩
  cases hi
  cases hj
  rcases k with _ | _ | _ | _ | k <;> simp [bars] at hr
  all_goals (subst hr; simp [CtaBarrier.Record.refs] at hir)
  rcases l with _ | _ | _ | _ | l <;> simp [bars] at hq
  all_goals (subst hq; simp [CtaBarrier.Record.refs] at hjq)
  simp only [CtaBarOn] at hor hoq
  omega

/-- Barrier 1's own order relates its two arrivals. -/
theorem bars_same_id_ordered (L : Launch) :
    ObjectOrder L bars (.ctaBar 0 1) (.thread (32, 0), false) (.thread (0, 1), false) :=
  ⟨rfl, rfl, (32, 0), (0, 1), rfl, rfl, ⟨_, rfl⟩, ⟨_, rfl⟩, 1, 2, _, _, rfl, rfl, by decide,
    rfl, rfl, by simp [CtaBarrier.Record.refs], by simp [CtaBarrier.Record.refs]⟩

end PTX.Tests.WaitOrderLitmus
