-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.WaitOrderWaits
public import Lemmas.Order.WaitOrderObject
public import Lemmas.MBarrier.MBarrierHistory
public import Lemmas.TensorStore.TensorReduce
public import Lemmas.Kernel.SharedLifetime
public import Lemmas.Order.OrderWaits
public import Lemmas.Tcgen05.TcFence

/-! Litmus C (load buffering through two mbarriers) as a full execution of a kernel
(`lbFull_consistent`).

`lbFullCode`, launched as one CTA of two threads (`lbL`), one warp: thread `t` computes the
address of its own barrier (`8 * t`) and of the other one from `%tid.x` and the shared
symbol at offset 0, initializes its own barrier with expected count 1, passes
`bar.warp.sync 3`, polls the other barrier once with a relaxed `try_wait.parity` (parity 0),
arrives on its own barrier with a relaxed `arrive` and returns. Thread 0 owns `A` (offset 0),
thread 1 owns `B` (offset 8).

In `lbFull` both polls succeed, each observing the other thread's arrival
(`lbFull_polls_succeed`). Each initialization is published (OBJ-MBAR-INIT-PUBLICATION,
`InitPublished` through `baseCausality`) to the owner's arrival by program order and to the other
thread's poll by the warp barrier (`WarpBarSync`), so the execution is not `TmaUnsafe`
(`lbFull_not_tmaUnsafe`), and its mbarriers are allocated and initialized and no aligned
instruction diverges (`lbFull_mbar_ok`). The polls are no canonical spins (`not_spin`), so the
dependency order (DEP-ORDER) leaves a thread's poll only through its witness, the other thread's
arrival. The order axioms use `BarQuiet`, the generalization of `Quiet`
(`Tests/Memory/WaitOrderLitmus.lean`) to executions with one warp barrier: base causality crosses
threads only from before the barrier to after it. -/

namespace PTX.Tests.WaitOrderLitmus.Full
open PTX.MBarrier

/-! ## Executions with mbarrier operations and one warp barrier -/

/-- Mbarrier initializations, arrivals, relaxed waits, warp barriers and exits, with no
asynchronous effects and no other object histories; every warp barrier event is the `cut`-th
event of its thread. -/
structure BarQuiet (X : Execution) (cut : Nat) : Prop where
  kinds : ∀ e pc k, X.get e = some ⟨pc, k⟩ → (∃ m c, k = .mbInit m c) ∨
    (∃ m tx c r s, k = .arrive m tx c r s) ∨ (∃ m p ok s, k = .wait m p ok false s) ∨
    (∃ mask inst, k = .warpBar mask inst) ∨ k = .exit
  cut : ∀ e pc mask inst, X.get e = some ⟨pc, .warpBar mask inst⟩ → e.2 = cut
  async : ∀ i p, ¬ X.AsyncPresent i p
  tensor : ∀ i, X.tensor i = none
  clusters : ∀ c, X.clusters c = []
  barriers : ∀ c, X.barriers c = []
  tmem : ∀ k, X.tmemHistory k = []
  pairing : X.tmemPairing = []

section BarQuiet
variable {L : Launch} {X : Execution} {cut : Nat}

theorem BarQuiet.kind (hq : BarQuiet X cut) {e : EvId} {pc : Nat} {k : Kind}
    (h : X.get e = some ⟨pc, k⟩)
    (h1 : ∀ m c, k ≠ .mbInit m c) (h2 : ∀ m tx c r s, k ≠ .arrive m tx c r s)
    (h3 : ∀ m p ok s, k ≠ .wait m p ok false s) (h4 : ∀ mask inst, k ≠ .warpBar mask inst)
    (h5 : k ≠ .exit) : False := by
  rcases hq.kinds _ _ _ h with ⟨m, c, hk⟩ | ⟨m, tx, c, r, s, hk⟩ | ⟨m, p, ok, s, hk⟩ |
    ⟨mask, inst, hk⟩ | hk
  · exact h1 _ _ hk
  · exact h2 _ _ _ _ _ hk
  · exact h3 _ _ _ _ hk
  · exact h4 _ _ hk
  · exact h5 hk

theorem BarQuiet.not_acquire (hq : BarQuiet X cut) {w : EvId} {m : Loc} :
    ¬ X.AcquireWait w m := by
  rintro ⟨pc, parity, scope, h⟩
  exact hq.kind h (by simp) (by simp) (by simp) (by simp) (by simp)

/-- No stage edge: there is no asynchronous stage. -/
theorem BarQuiet.not_stageEdge (hq : BarQuiet X cut) (e f : AsyncCopy.Ref) :
    ¬ StageEdge X e f := by
  intro hs
  have hna := hq.async
  cases e <;> cases f <;> unfold StageEdge at hs <;> split at hs <;> simp_all

/-- Base causality is program order, or crosses the warp barrier. -/
theorem BarQuiet.baseCausality (hq : BarQuiet X cut) {e f : EvId} (h : baseCausality L X e f) :
    e.2 < f.2 ∧ (e.1 = f.1 ∨ (e.2 < cut ∧ cut < f.2)) := by
  have base : ∀ {e f : EvId}, (po X e f ∨ CtaBarSync L X e f ∨ MSync L X e f ∨
      ClusterSync L X e f ∨ WarpBarSync L X e f ∨ synchronizesWith L X e f ∨
      FenceSync L X e f) → e.2 < f.2 ∧ (e.1 = f.1 ∨ (e.2 < cut ∧ cut < f.2)) := by
    intro e f h
    rcases h with h | ⟨-, key, i, j, hi, -⟩ | ⟨x, w, m, rs, as, -, ⟨⟨pc, q, hw⟩, -⟩, -⟩ |
        ⟨-, i, j, ⟨phase, ha, -⟩, -⟩ |
        ⟨i, j, ⟨-, mask, inst, ⟨pc, hi⟩, ⟨pc', hj⟩⟩, h1, h2, -⟩ | ⟨a, b, bs, cs, hw, -⟩ | h
    · exact ⟨h.2.1, .inl h.1⟩
    · obtain ⟨idx, st, warp, count, lanes, g, hget, -⟩ := hi.2.2
      simp [hq.barriers] at hget
    · exact (hq.kind hw (by simp) (by simp) (by simp) (by simp) (by simp)).elim
    · simp [hq.clusters, ClusterBarrier.ArrivalOf] at ha
    · have := hq.cut _ _ _ _ hi
      have := hq.cut _ _ _ _ hj
      simp only at *
      omega
    · rcases hw with ⟨pc, hw⟩ | ⟨o, pc, hw⟩ <;>
        exact (hq.kind hw (by simp) (by simp) (by simp) (by simp) (by simp)).elim
    · exact absurd h (not_fenceSync_of_noFence (fun e sem s ⟨pc, hf⟩ =>
        hq.kind hf (by simp) (by simp) (by simp) (by simp) (by simp)) e f)
  unfold PTX.baseCausality at h
  induction h with
  | single h => exact base h
  | tail _ h ih =>
    have := base h
    refine ⟨by omega, ?_⟩
    rcases ih.2 with h1 | h1 <;> rcases this.2 with h2 | h2
    · exact .inl (h1.trans h2)
    · exact .inr ⟨by omega, h2.2⟩
    · exact .inr ⟨h1.1, by omega⟩
    · exact .inr ⟨h1.1, by omega⟩

/-- Each causal edge is the issue-to-completion step of a thread event or a base causality
edge. -/
theorem BarQuiet.cause (hq : BarQuiet X cut) {a c : AsyncCopy.Ref × Bool}
    (h : stageCausality L X a c) :
    ∃ e f, a.1 = .thread e ∧ c.1 = .thread f ∧
      ((e = f ∧ a.2 = false ∧ c.2 = true) ∨
       (a.2 = true ∧ c.2 = false ∧ e.2 < f.2 ∧ (e.1 = f.1 ∨ (e.2 < cut ∧ cut < f.2)))) := by
  obtain ⟨e, b⟩ := a
  obtain ⟨f, b'⟩ := c
  rcases h with (⟨rfl, rfl, rfl, hp⟩ | ⟨-, -, hs⟩) | ⟨rfl, rfl, i, j, rfl, rfl, h⟩ |
      ⟨-, -, j, -, i, p, w, ws, -, -, ⟨n, m, -, ⟨pc, q, hw⟩, -⟩, -⟩
  · cases e with
    | thread e => exact ⟨e, e, rfl, rfl, .inl ⟨rfl, rfl, rfl⟩⟩
    | async i p => exact (hq.async i p hp).elim
  · exact (hq.not_stageEdge _ _ hs).elim
  · exact ⟨i, j, rfl, rfl, .inr ⟨rfl, rfl, hq.baseCausality h⟩⟩
  · exact (hq.kind hw (by simp) (by simp) (by simp) (by simp) (by simp)).elim

/-- A causal path moves forward, and leaves its thread only from before the warp barrier. -/
theorem BarQuiet.chain (hq : BarQuiet X cut) {a c : AsyncCopy.Ref × Bool}
    (h : Relation.TransGen (stageCausality L X) a c) :
    ∃ e f, a.1 = .thread e ∧ c.1 = .thread f ∧
      2 * e.2 + a.2.toNat < 2 * f.2 + c.2.toNat ∧ (e.1 = f.1 ∨ e.2 < cut) := by
  have one : ∀ {a c : AsyncCopy.Ref × Bool}, stageCausality L X a c → ∃ e f, a.1 = .thread e ∧
      c.1 = .thread f ∧ 2 * e.2 + a.2.toNat < 2 * f.2 + c.2.toNat ∧ (e.1 = f.1 ∨ e.2 < cut) := by
    intro a c h
    obtain ⟨e, f, ha, hc, h⟩ := hq.cause h
    refine ⟨e, f, ha, hc, ?_⟩
    rcases h with ⟨rfl, h1, h2⟩ | ⟨h1, h2, h3, h4⟩
    · simp [h1, h2]
    · refine ⟨by simp [h1, h2]; omega, ?_⟩
      rcases h4 with h4 | h4
      · exact .inl h4
      · exact .inr h4.1
  induction h with
  | single h => exact one h
  | @tail m n _ h ih =>
    obtain ⟨e, g, ha, hb, h1, h2⟩ := ih
    obtain ⟨g', f, hb', hc, h3, h4⟩ := one h
    rw [hb] at hb'
    cases hb'
    have := Bool.toNat_le m.2
    refine ⟨e, f, ha, hc, by omega, ?_⟩
    rcases h2 with h2 | h2
    · rcases h4 with h4 | h4
      · exact .inl (h2.trans h4)
      · exact .inr (by omega)
    · exact .inr h2

/-- The witnesses of a return are the counter updates that a successful poll observed and the
warp barrier events of the instance of a warp barrier event. -/
theorem BarQuiet.witness (hq : BarQuiet X cut) {x : AsyncCopy.Ref} {j : EvId}
    (h : Witness L X x j) :
    MbarObserved X x (.thread j) ∨
      ∃ i, x = .thread i ∧ ∃ mask inst, X.WarpBar i mask inst ∧ X.WarpBar j mask inst := by
  obtain ⟨fills, hn, -, hf⟩ := h
  unfold Needs at hn
  cases hj : X.get j with
  | none => simp [hj] at hn
  | some ev =>
    obtain ⟨pc, k⟩ := ev
    rw [hj] at hn
    rcases hq.kinds _ _ _ hj with ⟨m, c, rfl⟩ | ⟨m, tx, c, r, s, rfl⟩ | ⟨m, p, ok, s, rfl⟩ |
      ⟨mask, inst, rfl⟩ | rfl
    · simp [KindNeeds] at hn
    · simp [KindNeeds] at hn
    · cases ok
      · simp [KindNeeds] at hn
      · simp only [KindNeeds, ite_true, pollNeeds, needsIf, List.mem_flatMap] at hn
        obtain ⟨r, -, hn⟩ := hn
        split at hn
        · simp only [List.mem_singleton, Need.node.injEq] at hn
          subst hn
          subst hf
          exact .inl ‹_›
        · simp at hn
    · simp only [KindNeeds, List.mem_map] at hn
      obtain ⟨l, -, hn⟩ := hn
      simp only [Need.node.injEq] at hn
      subst hn
      obtain ⟨j', rfl, hw⟩ := hf
      exact .inr ⟨_, rfl, mask, inst, hw, ⟨pc, hj⟩⟩
    · simp [KindNeeds] at hn

/-- No observation synchronizes: the polls are relaxed and no asynchronous stage exists. -/
theorem BarQuiet.not_syncObserved (hq : BarQuiet X cut) {x w : AsyncCopy.Ref} :
    ¬ SyncObserved L X x w := by
  rintro (⟨-, j, m, pc, q, ws, us, g, -, hj, -⟩ | ⟨i, p, j, k, -, -, hp, -⟩)
  · exact hq.kind hj (by simp) (by simp) (by simp) (by simp) (by simp)
  · exact hq.async i p hp

/-- Observation is causal: no observation synchronizes. -/
theorem BarQuiet.observationCausal (hq : BarQuiet X cut) : ObservationCausal L X :=
  fun _ _ ho => (hq.not_syncObserved ho).elim

/-- Only an mbarrier has an order: the other object histories are empty. -/
theorem BarQuiet.objectOrder (hq : BarQuiet X cut) {o : OrderObject}
    {a c : AsyncCopy.Ref × Bool} (h : ObjectOrder L X o a c) : ∃ m, o = .mbar m := by
  obtain ⟨e, b⟩ := a
  obtain ⟨f, b'⟩ := c
  cases o with
  | mbar m => exact ⟨m, rfl⟩
  | ctaBar c id =>
    obtain ⟨-, -, -, -, -, -, -, -, k, l, r, q, hr, -⟩ := h
    simp [hq.barriers] at hr
  | cluster c =>
    obtain ⟨-, -, -, -, -, -, k, l, r, q, hr, -⟩ := h
    simp [hq.clusters] at hr
  | tmem cta =>
    obtain ⟨-, -, -, -, -, -, k, l, x, y, hx, -⟩ := h
    simp [hq.tmem] at hx

/-- Per-object ranks that causality and the object's order increase. -/
theorem BarQuiet.objectCoherent (hq : BarQuiet X cut)
    (r : OrderObject → AsyncCopy.Ref × Bool → Nat)
    (hcause : ∀ o (e f : EvId) (b b' : Bool),
      ((e = f ∧ b = false ∧ b' = true) ∨
       (b = true ∧ b' = false ∧ e.2 < f.2 ∧ (e.1 = f.1 ∨ (e.2 < cut ∧ cut < f.2)))) →
      r o (.thread e, b) < r o (.thread f, b'))
    (hmbar : ∀ m a c, ObjectOrder L X (.mbar m) a c → r (.mbar m) a < r (.mbar m) c) :
    ObjectCoherent L X := fun o =>
  acyclic_of_rank (r o) fun a c h => by
    rcases h with h | h
    · obtain ⟨e, f, ha, hc, hh⟩ := hq.cause h
      obtain ⟨a, b⟩ := a
      obtain ⟨c, b'⟩ := c
      simp only at ha hc hh
      subst ha hc
      exact hcause o e f b b' hh
    · cases o with
      | mbar m => exact hmbar m _ _ h.1
      | ctaBar c id => exact absurd (hq.objectOrder (L := L) (o := .ctaBar c id) h) (by simp)
      | cluster c => exact absurd (hq.objectOrder (L := L) (o := .cluster c) h) (by simp)
      | tmem cta => exact absurd (hq.objectOrder (L := L) (o := .tmem cta) h) (by simp)

/-- Each dependency step is the issue-to-completion step of a thread event, a return before a
later event that depends on it, or a witness before the return it fills. -/
theorem BarQuiet.depStep {K : Kernel} (hq : BarQuiet X cut) {a c : AsyncCopy.Ref × Bool}
    (h : DepStep L K X a c) :
    (∃ e, a.1 = .thread e ∧ c.1 = .thread e ∧ a.2 = false ∧ c.2 = true) ∨
    (∃ w j, a.1 = .thread w ∧ c.1 = .thread j ∧ a.2 = true ∧ c.2 = false ∧ Resumes K X w j) ∨
    (∃ j, c.1 = .thread j ∧ a.2 = false ∧ c.2 = true ∧ Witness L X a.1 j) := by
  obtain ⟨e, b⟩ := a
  obtain ⟨f, b'⟩ := c
  rcases h with (⟨rfl, rfl, rfl, hp⟩ | ⟨-, -, hs⟩) | ⟨-, -, i, p, -, -, -, hp, -⟩ |
      ⟨rfl, rfl, j, rfl, hw⟩ | ⟨rfl, rfl, w, j, rfl, rfl, hr⟩
  · cases e with
    | thread e => exact .inl ⟨e, rfl, rfl, rfl, rfl⟩
    | async i p => exact (hq.async i p hp).elim
  · exact (hq.not_stageEdge _ _ hs).elim
  · exact (hq.async i p hp).elim
  · exact .inr (.inr ⟨j, rfl, rfl, rfl, hw⟩)
  · exact .inr (.inl ⟨w, j, rfl, rfl, rfl, rfl, hr⟩)

/-- A rank that the dependency steps and every mbarrier's order increase also increases along
the dependency steps together with the order of any one object. -/
theorem BarQuiet.depWith_rank {K : Kernel} (hq : BarQuiet X cut)
    (r : AsyncCopy.Ref × Bool → Nat)
    (hdep : ∀ a c, DepStep L K X a c → r a < r c)
    (hmbar : ∀ m a c, ObjectOrder L X (.mbar m) a c → r a < r c) (o : OrderObject)
    {a c : AsyncCopy.Ref × Bool} (h : DepStep L K X a c ∨ ObjectOrder L X o a c) : r a < r c := by
  rcases h with h | h
  · exact hdep _ _ h
  · obtain ⟨m, rfl⟩ := hq.objectOrder h
    exact hmbar m _ _ h

/-- A single rank that the dependency steps and every mbarrier's order increase: the acyclic
half of `DependencyOk`. -/
theorem BarQuiet.depAcyclic {K : Kernel} (hq : BarQuiet X cut)
    (r : AsyncCopy.Ref × Bool → Nat)
    (hdep : ∀ a c, DepStep L K X a c → r a < r c)
    (hmbar : ∀ m a c, ObjectOrder L X (.mbar m) a c → r a < r c) :
    ∀ o, o.Enabling → ∀ n,
      ¬ Relation.TransGen (fun a c => DepStep L K X a c ∨ ObjectOrder L X o a c) n n :=
  fun o _ => acyclic_of_rank r fun _ _ h => hq.depWith_rank r hdep hmbar o h

end BarQuiet

/-! ## The kernel, launch, memory and execution -/

def lbFullCode : Kernel where
  name := "lbFull"
  params := []
  sharedBytes := 16
  code := [
    { op := .move ⟨.scalar, .int .u 32, [some 5], [.sreg ⟨.tid, some .x⟩]⟩ },
    { op := .int ⟨.shl, .int .b 32, false, [some 4], [.reg 5, .imm 3]⟩ },
    { op := .int ⟨.add, .int .u 32, false, [some 2], [.reg 4, .sharedSym 0]⟩ },
    { op := .int ⟨.xor, .int .b 32, false, [some 3], [.reg 4, .imm 8]⟩ },
    { op := .int ⟨.add, .int .u 32, false, [some 1], [.reg 3, .sharedSym 0]⟩ },
    { op := .mbarInit 2 0 (.imm 1) },
    { op := .warp { kind := .barWarp, mask := some (.imm 3) } },
    { op := .mbarWait 0 1 0 (.imm 0) false .cta },
    { op := .mbarArrive 2 0 (.imm 0) (.imm 1) false false .cta },
    { op := .ret }]

def lbL : Launch := { grid := 1, block := 2, params := fun _ => none }

def A : Loc := ⟨.shared, 0, 0⟩
def B : Loc := ⟨.shared, 0, 8⟩

def lbMem : Mem0 := fun l =>
  if l.space = .shared ∧ l.cta = 0 ∧ l.addr < 16 then some none else none

def trace (own other : Loc) : List Event :=
  [⟨5, .mbInit own 1⟩, ⟨6, .warpBar 3 0⟩, ⟨7, .wait other 0 true false .cta⟩,
    ⟨8, .arrive own 0 1 false .cta⟩, ⟨9, .exit⟩]

def t0 : State := ⟨0, 1, 1, 0, true⟩
def t1 : State := ⟨1, 1, 1, 0, false⟩
def t2 : State := ⟨1, 1, 1, 0, true⟩

/-- The history of `A` (`own = 0`) or `B` (`own = 1`): its owner initializes it and arrives;
the other thread's poll observes phase 0. -/
def log (own : Nat) : List (Record AsyncCopy.Ref) := [
  ⟨.thread (own, 0), .init 1, ⟨some t0, none, none⟩, none⟩,
  ⟨.thread (own, 3), .arrive 1 0, ⟨some t1, none, none⟩, none⟩,
  ⟨.thread (1 - own, 2), .pollParity 0 true, ⟨some t2, some true, some 0⟩, none⟩]

def lbFull : Execution where
  tr
    | 0 => trace A B
    | 1 => trace B A
    | _ => []
  rf _ _ := none
  objects m := if m = A then log 0 else if m = B then log 1 else []

theorem A_ne_B : A ≠ B := by decide

theorem objects_A : lbFull.objects A = log 0 := by simp [lbFull]
theorem objects_B : lbFull.objects B = log 1 := by simp [lbFull, A_ne_B.symm]

theorem log_checked (own : Nat) (h : own = 0 ∨ own = 1) : CheckedLog (log own) := by
  rcases h with rfl | rfl <;>
  exact checkedLog_of_replay (ops := (log _).map (fun r => (r.id, r.action))) (by rfl)
    (by decide)

/-! ### Traces -/

theorem run_tau {K : Kernel} {As : List Assumption} {L : Launch} {g : Nat} {t t' : TState}
    {e : Event} {l : List Event} {o : Option TState}
    (h : out K As L g t = .tau t') (hr : Run K As L g t' (e :: l) o) :
    Run K As L g t (e :: l) o := by
  cases hr with
  | step hl he hr => exact .step (.head h hl) he hr
  | last hl he => exact .last (.head h hl) he

theorem produces (g : Nat) (hg : g < lbL.threads) :
    Produces lbFullCode [] lbL g (lbFull.tr g) := by
  refine ⟨none, ?_⟩
  rcases g with _ | _ | g
  · exact run_tau rfl (run_tau rfl (run_tau rfl (run_tau rfl (run_tau rfl
      (.step .refl ⟨_, rfl, rfl, rfl⟩ (.step .refl ⟨_, rfl, 0, rfl, rfl⟩
      (.step .refl ⟨_, rfl, true, rfl, rfl⟩ (.step .refl ⟨_, rfl, rfl, rfl⟩
      (.last .refl ⟨_, rfl, rfl, rfl⟩)))))))))
  · exact run_tau rfl (run_tau rfl (run_tau rfl (run_tau rfl (run_tau rfl
      (.step .refl ⟨_, rfl, rfl, rfl⟩ (.step .refl ⟨_, rfl, 0, rfl, rfl⟩
      (.step .refl ⟨_, rfl, true, rfl, rfl⟩ (.step .refl ⟨_, rfl, rfl, rfl⟩
      (.last .refl ⟨_, rfl, rfl, rfl⟩)))))))))
  · simp [lbL, Launch.threads] at hg

/-! ### Events -/

theorem kinds {e : EvId} {pc : Nat} {k : Kind} (h : lbFull.get e = some ⟨pc, k⟩) :
    k = .mbInit A 1 ∨ k = .mbInit B 1 ∨ k = .warpBar 3 0 ∨ k = .wait A 0 true false .cta ∨
    k = .wait B 0 true false .cta ∨ k = .arrive A 0 1 false .cta ∨
    k = .arrive B 0 1 false .cta ∨ k = .exit := by
  obtain ⟨t, n⟩ := e
  rcases t with _ | _ | t <;> rcases n with _ | _ | _ | _ | _ | n <;>
    simp [Execution.get, lbFull, trace] at h <;> simp [← h.2]

/-- All events of `lbFull`. -/
theorem get_iff {e : EvId} {ev : Event} : lbFull.get e = some ev ↔
    (e = (0, 0) ∧ ev = ⟨5, .mbInit A 1⟩) ∨ (e = (0, 1) ∧ ev = ⟨6, .warpBar 3 0⟩) ∨
    (e = (0, 2) ∧ ev = ⟨7, .wait B 0 true false .cta⟩) ∨
    (e = (0, 3) ∧ ev = ⟨8, .arrive A 0 1 false .cta⟩) ∨ (e = (0, 4) ∧ ev = ⟨9, .exit⟩) ∨
    (e = (1, 0) ∧ ev = ⟨5, .mbInit B 1⟩) ∨ (e = (1, 1) ∧ ev = ⟨6, .warpBar 3 0⟩) ∨
    (e = (1, 2) ∧ ev = ⟨7, .wait A 0 true false .cta⟩) ∨
    (e = (1, 3) ∧ ev = ⟨8, .arrive B 0 1 false .cta⟩) ∨ (e = (1, 4) ∧ ev = ⟨9, .exit⟩) := by
  obtain ⟨t, n⟩ := e
  rcases t with _ | _ | t <;> rcases n with _ | _ | _ | _ | _ | n <;>
    simp [Execution.get, lbFull, trace, eq_comm]

theorem quiet : BarQuiet lbFull 1 where
  kinds e pc k h := by
    rcases kinds h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  cut e pc mask inst h := by
    obtain ⟨t, n⟩ := e
    rcases t with _ | _ | t <;> rcases n with _ | _ | _ | _ | _ | n <;>
      simp [Execution.get, lbFull, trace] at h ⊢
  async i p := by cases p <;> simp [Execution.AsyncPresent, Execution.MmaRead, lbFull]
  tensor _ := rfl
  clusters _ := rfl
  barriers _ := rfl
  tmem _ := rfl
  pairing := rfl

/-- An event of a kind outside `kinds` does not exist. -/
macro "kind_absurd " h:ident : tactic =>
  `(tactic| (rcases kinds $h with h | h | h | h | h | h | h | h <;> cases h))

theorem wait_at {e : EvId} {pc : Nat} {m : Loc} {q : Nat} {ok acq : Bool} {sc : MbarScope}
    (h : lbFull.get e = some ⟨pc, .wait m q ok acq sc⟩) : pc = 7 ∧ e.2 = 2 := by
  obtain ⟨t, n⟩ := e
  rcases t with _ | _ | t <;> rcases n with _ | _ | _ | _ | _ | n <;>
    simp [Execution.get, lbFull, trace] at h ⊢ <;> exact h.1.symm

theorem no_memReads (e : AsyncCopy.Ref) (a : Acc) (bs : List (Option Byte)) :
    ¬ lbFull.MemReads e a bs := by
  cases e with
  | thread e => rintro (⟨pc, h⟩ | ⟨new, pc, h⟩) <;> kind_absurd h
  | async i p =>
    cases p <;> simp [Execution.MemReads, Execution.MmaRead, Execution.Copy, lbFull]

theorem no_memWrites (e : AsyncCopy.Ref) (a : Acc) (bs : List Byte) :
    ¬ lbFull.MemWrites e a bs := by
  cases e with
  | thread e => rintro (⟨pc, h⟩ | ⟨old, pc, h⟩) <;> kind_absurd h
  | async i p =>
    cases p <;> simp [Execution.MemWrites, Execution.Copy, lbFull]
    rintro s targets ⟨pc, h⟩
    kind_absurd h

/-! ### Witnesses and the order axioms -/

/-- The witnesses of the returns: each poll's witness is the other thread's arrival, and the
witnesses of a warp barrier event are the two warp barrier events. -/
theorem witness {x : AsyncCopy.Ref} {j : EvId} (h : Witness lbL lbFull x j) :
    (x = .thread (0, 3) ∧ j = (1, 2)) ∨ (x = .thread (1, 3) ∧ j = (0, 2)) ∨
    ∃ i, x = .thread i ∧ i.2 = 1 ∧ j.2 = 1 := by
  rcases quiet.witness h with ⟨-, k, m, acq, ws, hk, ⟨-, hu⟩, -⟩ |
      ⟨i, rfl, mask, inst, ⟨pc, hi⟩, ⟨pc', hj⟩⟩
  · cases hk
    obtain ⟨i, j, r, s, phase, hr, rfl, -, hs, hsid, -, -, hij, hp, -⟩ := hu
    by_cases hA : m = A
    · subst hA
      rw [objects_A] at hr hs hp
      rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;>
        simp [log, phaseAt, stateBefore] at hr hs hij hp
      subst hr hs
      simp only [AsyncCopy.Ref.thread.injEq] at hsid
      subst hsid
      simp
    · by_cases hB : m = B
      · subst hB
        rw [objects_B] at hr hs hp
        rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;>
          simp [log, phaseAt, stateBefore] at hr hs hij hp
        subst hr hs
        simp only [AsyncCopy.Ref.thread.injEq] at hsid
        subst hsid
        simp
      · simp [lbFull, hA, hB] at hr
  · exact .inr (.inr ⟨i, rfl, quiet.cut _ _ _ _ hi, quiet.cut _ _ _ _ hj⟩)

/-- Observation is causal: the relaxed polls synchronize with nothing. -/
theorem observationCausal : ObservationCausal lbL lbFull :=
  quiet.observationCausal

/-- Thread `p`'s events after the warp barrier come first. -/
def crank (p : Nat) : AsyncCopy.Ref × Bool → Nat
  | (.thread e, b) => (if e.2 < 2 then 4 * e.2 + (if e.1 = p then 0 else 2)
      else (if e.1 = p then 8 else 16) + 2 * e.2) + b.toNat
  | (.async _ _, _) => 0

def orank : OrderObject → AsyncCopy.Ref × Bool → Nat
  | .mbar m => if m = B then crank 1 else crank 0
  | _ => crank 0

theorem crank_cause (p : Nat) (e f : EvId) (b b' : Bool)
    (h : (e = f ∧ b = false ∧ b' = true) ∨
      (b = true ∧ b' = false ∧ e.2 < f.2 ∧ (e.1 = f.1 ∨ (e.2 < 1 ∧ 1 < f.2)))) :
    crank p (.thread e, b) < crank p (.thread f, b') := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, h1, h2⟩
  · simp only [crank]; split_ifs <;> simp
  · simp only [crank]; split_ifs <;> simp <;> omega

theorem log_before {own : Nat} {a c : AsyncCopy.Ref} (h : Before (log own) a c) :
    (a = .thread (own, 0) ∧ c = .thread (own, 3)) ∨
    (a = .thread (own, 0) ∧ c = .thread (1 - own, 2)) ∨
    (a = .thread (own, 3) ∧ c = .thread (1 - own, 2)) := by
  obtain ⟨i, j, r, s, hr, rfl, hs, rfl, hij⟩ := h
  rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;>
    simp [log] at hr hs hij <;> subst hr hs <;> simp

theorem mbar_before {m : Loc} {a c : AsyncCopy.Ref} (h : Before (lbFull.objects m) a c) :
    (m = A ∧ Before (log 0) a c) ∨ (m = B ∧ Before (log 1) a c) := by
  by_cases hA : m = A
  · subst hA; rw [objects_A] at h; exact .inl ⟨rfl, h⟩
  · by_cases hB : m = B
    · subst hB; rw [objects_B] at h; exact .inr ⟨rfl, h⟩
    · obtain ⟨i, j, r, s, hr, -⟩ := h
      simp [lbFull, hA, hB] at hr

theorem objectCoherent : ObjectCoherent lbL lbFull := by
  refine quiet.objectCoherent orank ?_ ?_
  · intro o e f b b' h
    cases o <;> simp only [orank] <;> (try split_ifs) <;> exact crank_cause _ e f b b' h
  · intro m a c h
    obtain ⟨e, b⟩ := a
    obtain ⟨f, b'⟩ := c
    obtain ⟨rfl, rfl, h⟩ := h
    rcases mbar_before h with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · rcases log_before h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [orank, crank, A_ne_B]
    · rcases log_before h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [orank, crank]

theorem asyncObject : AsyncObjectOrdered lbL lbFull := by
  intro m i p y h
  rcases mbar_before h with ⟨-, h⟩ | ⟨-, h⟩ <;>
    rcases log_before h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h

/-- The poll at position 7 is followed by the arrival, not by a branch: it is no canonical
spin. -/
theorem not_spin (exit : Nat) : ¬ lbFullCode.CanonicalSpin 7 exit := by
  rintro ⟨h, -⟩
  have hn : lbFullCode.spinExit? 7 = none := by decide
  rw [Kernel.SpinShape, hn] at h
  cases h

/-- Warp barrier first, then the polls after the arrivals they observe. -/
def erank : AsyncCopy.Ref × Bool → Nat
  | (.thread e, b) => if e.2 < 2 then 2 * e.2 + b.toNat
      else 4 + (if b then (if e.2 = 2 then 2 else 1) else 0)
  | (.async _ _, _) => 0

/-- Only the warp barrier events have later events that depend on their return: the polls are
no canonical spins. -/
theorem resumes_from {w j : EvId} (h : Resumes lbFullCode lbFull w j) : w.2 = 1 := by
  obtain ⟨-, hm⟩ := h
  cases hg : lbFull.get w with
  | none => simp [hg] at hm
  | some ev =>
    obtain ⟨pc, k⟩ := ev
    rw [hg] at hm
    rcases kinds hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Option.map_some, Kind.resume] at hm
    · exact quiet.cut _ _ _ _ hg
    · obtain ⟨pc', exit, m, q, acq, sc, hw, hs, -⟩ := hm
      rw [hg] at hw
      cases hw
      exact ((not_spin exit) ((wait_at hg).1 ▸ hs)).elim
    · obtain ⟨pc', exit, m, q, acq, sc, hw, hs, -⟩ := hm
      rw [hg] at hw
      cases hw
      exact ((not_spin exit) ((wait_at hg).1 ▸ hs)).elim

theorem erank_depStep (a c : AsyncCopy.Ref × Bool) (h : DepStep lbL lbFullCode lbFull a c) :
    erank a < erank c := by
  rcases quiet.depStep h with ⟨e, ha, hc, h1, h2⟩ | ⟨w, j, ha, hc, h1, h2, hr⟩ |
      ⟨j, hc, h1, h2, hw⟩
  · obtain ⟨a, b⟩ := a
    obtain ⟨c, b'⟩ := c
    simp only at ha hc h1 h2
    subst ha hc h1 h2
    simp only [erank]; split_ifs <;> simp_all
  · obtain ⟨a, b⟩ := a
    obtain ⟨c, b'⟩ := c
    simp only at ha hc h1 h2
    subst ha hc h1 h2
    have hw := resumes_from hr
    obtain ⟨⟨-, hlt, -⟩, -⟩ := hr
    simp only [erank]; split_ifs <;> simp <;> omega
  · obtain ⟨a, b⟩ := a
    obtain ⟨c, b'⟩ := c
    simp only at hc h1 h2 hw
    subst hc h1 h2
    rcases witness hw with ⟨rfl, hj⟩ | ⟨rfl, hj⟩ | ⟨i, rfl, hi, hj⟩
    · cases hj; simp [erank]
    · cases hj; simp [erank]
    · simp [erank, hi, hj]

theorem erank_mbar (m : Loc) (a c : AsyncCopy.Ref × Bool) (h : ObjectOrder lbL lbFull (.mbar m) a c)
    :
    erank a < erank c := by
  obtain ⟨e, b⟩ := a
  obtain ⟨f, b'⟩ := c
  obtain ⟨rfl, rfl, h⟩ := h
  rcases mbar_before h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
    rcases log_before h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [erank]

theorem lanes {lane : Nat} (hb : Nat.testBit 3 lane = true) : lane = 0 ∨ lane = 1 := by
  rcases lane with _ | _ | lane
  · exact .inl rfl
  · exact .inr rfl
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 3 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) (by omega)))] at hb
    cases hb

/-- Every returned event is ready: each poll's need is the other thread's arrival, and the
need of each lane of a warp barrier event is that lane's warp barrier event. -/
theorem ready (e : EvId) (_ : Returned lbFull e) : Ready lbL lbFull e := by
  intro n hn
  unfold Needs at hn
  cases hj : lbFull.get e with
  | none => simp [hj] at hn
  | some ev =>
    rw [hj] at hn
    rcases get_iff.mp hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals simp only [KindNeeds, ite_true, List.not_mem_nil] at hn
    all_goals first
      | (simp only [pollNeeds, needsIf, List.mem_flatMap] at hn
         obtain ⟨r, -, hn⟩ := hn
         split at hn
         · simp only [List.mem_singleton] at hn
           subst hn
           exact ⟨r.id, ‹MbarObserved _ _ _›.1, rfl⟩
         · simp at hn)
      | (simp only [List.mem_map, List.mem_filter, List.mem_range] at hn
         obtain ⟨l, ⟨-, hb⟩, rfl⟩ := hn
         rcases lanes hb with rfl | rfl <;> refine ⟨_, ?_, 1, rfl, 6, rfl⟩ <;> exact ⟨_, rfl⟩)

/-- DEP-ORDER holds: every returned event is ready, and a single rank orders the dependency
steps and every mbarrier's order. -/
theorem dependency : DependencyOk lbL lbFullCode lbFull :=
  ⟨ready, quiet.depAcyclic erank erank_depStep erank_mbar⟩

/-! ### The remaining fields -/

theorem warpBarOk : WarpBarOk lbL lbFull := by
  refine ⟨?_, ?_⟩
  · rintro ⟨t, n⟩ mask inst ⟨pc, h⟩
    have hn := quiet.cut _ _ _ _ h
    simp only at hn
    subst hn
    rcases kinds h with h' | h' | h' | h' | h' | h' | h' | h' <;> cases h'
    have ht : t < 2 := by
      rcases t with _ | _ | t
      · decide
      · decide
      · simp [Execution.get, lbFull] at h
    refine ⟨by simpa [lbL, Launch.threads] using ht, ?_⟩
    rcases t with _ | _ | t
    · decide
    · decide
    · omega
  · rintro ⟨t, n⟩ ⟨t', n'⟩ mask mask' inst ⟨pc, h⟩ ⟨pc', h'⟩ -
    have hn := quiet.cut _ _ _ _ h
    have hn' := quiet.cut _ _ _ _ h'
    simp only at hn hn'
    subst hn hn'
    rcases kinds h with h | h | h | h | h | h | h | h <;> cases h
    rcases kinds h' with h | h | h | h | h | h | h | h <;> cases h
    simp

/-- Every object operation of an instruction is in that object's history. -/
theorem covers {m : Loc} {id : AsyncCopy.Ref} {action : Action}
    (h : AsyncCopy.objectAction lbFull lbFull.async m id = some action) :
    ∃ r ∈ lbFull.objects m, r.id = id := by
  cases id with
  | thread e =>
    obtain ⟨t, n⟩ := e
    rcases t with _ | _ | t <;> rcases n with _ | _ | _ | _ | _ | n <;>
      simp [AsyncCopy.objectAction, Execution.get, lbFull, trace] at h
    all_goals
      obtain ⟨rfl, -⟩ := h
      simp [lbFull, log, A_ne_B.symm]
  | async i p =>
    cases p <;> simp [AsyncCopy.objectAction, AsyncCopy.issuedBy, lbFull] at h <;>
      split at h <;> cases h

theorem matches_log (own : Nat) (h : own = 0 ∨ own = 1) :
    AsyncCopy.MatchesObject lbFull lbFull.async (if own = 0 then A else B) (log own) := by
  intro r hr
  rcases h with rfl | rfl <;> simp [log] at hr <;> rcases hr with rfl | rfl | rfl <;>
    simp [AsyncCopy.objectAction, Execution.get, lbFull, trace]

theorem tmaOk : TmaOk lbFull := by
  refine ⟨?_, ⟨?_, ?_⟩, fun m => ?_, ?_⟩
  · intro i hi
    obtain ⟨p, hp⟩ := hi
    cases p <;> cases hp
  · intro i hi; cases hi
  · intro i hi; cases hi
  · refine ⟨?_, ?_, fun id action h => covers h⟩
    · by_cases hA : m = A
      · subst hA; rw [objects_A]; exact log_checked 0 (.inl rfl)
      · by_cases hB : m = B
        · subst hB; rw [objects_B]; exact log_checked 1 (.inr rfl)
        · simp only [lbFull, hA, hB, ite_false]
          exact ⟨by simp, none, .nil none⟩
    · by_cases hA : m = A
      · subst hA; rw [objects_A]; exact matches_log 0 (.inl rfl)
      · by_cases hB : m = B
        · subst hB; rw [objects_B]; simpa [A_ne_B.symm] using matches_log 1 (.inr rfl)
        · simp only [lbFull, hA, hB, ite_false]
          intro r hr; cases hr
  · intro i hi; cases hi

theorem lbFull_consistent : Consistent lbL lbFullCode [] lbMem lbFull where
  thr := produces
  outside g hg := by
    rcases g with _ | _ | g
    · simp [lbL, Launch.threads] at hg
    · simp [lbL, Launch.threads] at hg
    · rfl
  rf e a bs h := (no_memReads e a bs h).elim
  ctaBar := ⟨fun _ _ => rfl, fun c _ => ⟨by simp [lbFull], by simp [lbFull], ⟨{}, rfl⟩⟩⟩
  cluster := ⟨by decide, fun _ _ => rfl, fun c _ => ⟨by simp [lbFull], by simp [lbFull], ⟨{}, rfl⟩⟩⟩
  dependency := dependency
  shfl := by
    intro g i n pc m a b c recv ok h
    kind_absurd h
  vote := by
    intro g i n pc mask a ballot h
    kind_absurd h
  warpValue := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g i pc mode mask a r n h
      kind_absurd h
    · intro g i pc op signed mask a r n h
      kind_absurd h
    · intro g i pc all wide mask a r p n h
      kind_absurd h
    · intro g i pc r h
      kind_absurd h
  matrix := by
    intro g i pc op own recv n h
    kind_absurd h
  elect := by
    refine ⟨?_, ?_, ?_⟩
    · intro e pc mask inst leader h
      kind_absurd h
    · intro e f pc pc' mask mask' inst leader leader' h
      kind_absurd h
    · intro e f pc pc' mask inst inst' leader leader' h
      kind_absurd h
  warpBar := warpBarOk
  observation := observationCausal
  object := objectCoherent
  asyncObject := asyncObject
  initFence := by
    rintro m init w y ⟨_, _, _, _, _, _, _, _, _, -, -, -, h, -⟩ -
    kind_absurd h
  noFuture e a bs k w h := (no_memReads e a bs h).elim
  hidden e a bs k w a' bs' h := (no_memReads e a bs h).elim
  tma := tmaOk
  clc := by
    refine ⟨.refl, ?_, ?_, ?_, ?_⟩
    · simp [lbFull, Clc.initial]
    · simp [lbFull]
    · rintro i s targets ⟨pc, h⟩
      kind_absurd h
    · rintro ⟨i, s, targets, pc, h⟩
      kind_absurd h
  tensor i o h := by simp [lbFull] at h
  store i o h := by simp [lbFull] at h
  reduce := TensorStore.ReduceOk.of_none (fun _ _ h => by simp [lbFull] at h)
    (fun _ _ h => by obtain ⟨pc, h⟩ := h; kind_absurd h)
  atomic := by
    have noRmw : ∀ p l n, ¬ lbFull.RmwAt p l n := by
      intro p l n
      cases p with
      | thread e =>
        rintro ⟨a, old, new, ⟨pc, h⟩, -⟩
        kind_absurd h
      | tensor i x y =>
        rintro ⟨fp, ⟨o, red, loc, ho, -⟩, -⟩
        simp [lbFull] at ho
      | copy i j =>
        rintro ⟨s, r, a, ⟨pc, h⟩, -⟩
        kind_absurd h
    refine ⟨fun p q l n k hp => absurd hp (noRmw p l n), ?_⟩
    intro p path
    obtain ⟨q, edge, -⟩ := Relation.TransGen.head'_iff.mp path
    obtain ⟨l, n, hp, -⟩ := edge
    exact noRmw p l n hp
  fenceSc := fenceScOk_of_noSc fun e s ⟨pc, h⟩ => by kind_absurd h
  tmemPair := by
    simp [Tmem.Pair.HistoriesOk, Tmem.Pair.RequestHistory, Tmem.Pair.runRequests, lbFull]
  tmemPairCompletion := by
    intro ws hws
    rcases hws with ⟨_, _, hr, -⟩ | ⟨_, hr, -⟩ <;> simp [lbFull] at hr
  tmemPairResult := by
    intro i pc group dst n h
    kind_absurd h
  tcCommit := by simp [AsyncCopy.CommitOk, lbFull]
  mmaCompletion := by
    intro i j _ hd
    simp [lbFull] at hd
  tcRead := by
    refine ⟨?_, ?_⟩
    · rintro load address vals sh j source cell value ⟨pc, h⟩
      kind_absurd h
    · rintro mma index cell pos source value operands ⟨d, s, accum, mask, ⟨pc, h⟩, -⟩
      kind_absurd h
  asm := by simp

/-- Both relaxed polls succeed, each observing the other thread's relaxed arrival. -/
theorem lbFull_polls_succeed :
    lbFull.get (0, 2) = some ⟨7, .wait B 0 true false .cta⟩ ∧
    lbFull.get (1, 2) = some ⟨7, .wait A 0 true false .cta⟩ ∧
    MbarObserved lbFull (.thread (1, 3)) (.thread (0, 2)) ∧
    MbarObserved lbFull (.thread (0, 3)) (.thread (1, 2)) := by
  refine ⟨rfl, rfl, ⟨⟨_, rfl⟩, (0, 2), B, false, .cta, rfl, ⟨⟨7, 0, rfl⟩, ?_⟩, ?_⟩,
    ⟨⟨_, rfl⟩, (1, 2), A, false, .cta, rfl, ⟨⟨7, 0, rfl⟩, ?_⟩, ?_⟩⟩
  · rw [objects_B]; exact ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      fun _ _ _ h2 _ => absurd h2 (by omega)⟩
  · rw [objects_B]; simp [log, CounterUpdate]
  · rw [objects_A]; exact ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      fun _ _ _ h2 _ => absurd h2 (by omega)⟩
  · rw [objects_A]; simp [log, CounterUpdate]

/-! ### Initialization publication -/

/-- The two warp barrier events belong to one instance. -/
theorem warp_edges :
    WarpBarEdge lbL lbFull (0, 1) (1, 1) ∧ WarpBarEdge lbL lbFull (1, 1) (0, 1) :=
  ⟨⟨⟨⟨by decide, by decide, by decide⟩, by decide⟩, 3, 0, ⟨6, rfl⟩, ⟨6, rfl⟩⟩,
    ⟨⟨⟨by decide, by decide, by decide⟩, by decide⟩, 3, 0, ⟨6, rfl⟩, ⟨6, rfl⟩⟩⟩

/-- The initialization is published to the owner's arrival by program order, and to the other
thread's poll through the warp barrier. -/

theorem published (m : Loc) (r : Record AsyncCopy.Ref) (hr : r ∈ lbFull.objects m) :
    ObjectPublished lbL lbFull m r := by
  have hw := warp_edges
  by_cases hA : m = A
  · subst hA
    rw [objects_A] at hr
    simp [log] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl ⟨⟨1, rfl⟩, fun v ⟨pc, h⟩ => by kind_absurd h⟩
    · refine .inr ⟨(0, 0), 1, ⟨5, rfl⟩, ?_, .inl (.single (.inl ⟨rfl, by decide, by decide⟩)),
        fun v ⟨pc, h⟩ => by kind_absurd h⟩
      rw [objects_A]; exact ⟨0, 1, _, _, 1, rfl, rfl, rfl, rfl, rfl, rfl, by decide,
        fun _ _ _ h2 _ => absurd h2 (by omega)⟩
    · refine .inr ⟨(0, 0), 1, ⟨5, rfl⟩, ?_, .inl (.single (.inr (.inr (.inr (.inr (.inl
        ⟨1, 1, hw.1, by decide, by decide, by decide⟩)))))),
        fun v ⟨pc, h⟩ => by kind_absurd h⟩
      rw [objects_A]; exact ⟨0, 2, _, _, 1, rfl, rfl, rfl, rfl, rfl, rfl, by decide,
        MBarrier.NoInval.sameLifetime (by decide) _ _⟩
  · by_cases hB : m = B
    · subst hB
      rw [objects_B] at hr
      simp [log] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inl ⟨⟨1, rfl⟩, fun v ⟨pc, h⟩ => by kind_absurd h⟩
      · refine .inr ⟨(1, 0), 1, ⟨5, rfl⟩, ?_, .inl (.single (.inl ⟨rfl, by decide, by decide⟩)),
        fun v ⟨pc, h⟩ => by kind_absurd h⟩
        rw [objects_B]; exact ⟨0, 1, _, _, 1, rfl, rfl, rfl, rfl, rfl, rfl, by decide,
        fun _ _ _ h2 _ => absurd h2 (by omega)⟩
      · refine .inr ⟨(1, 0), 1, ⟨5, rfl⟩, ?_, .inl (.single (.inr (.inr (.inr (.inr (.inl
          ⟨1, 1, hw.2, by decide, by decide, by decide⟩)))))),
        fun v ⟨pc, h⟩ => by kind_absurd h⟩
        rw [objects_B]; exact ⟨0, 2, _, _, 1, rfl, rfl, rfl, rfl, rfl, rfl, by decide,
        MBarrier.NoInval.sameLifetime (by decide) _ _⟩
    · simp [lbFull, hA, hB] at hr

theorem lbFull_not_tmaUnsafe : ¬ TmaUnsafe lbL lbMem lbFull := by
  rintro (⟨m, r, hr, hf⟩ | ⟨m, r, hr, hp⟩ | ⟨e, a, w, i, m, c, l, he, -⟩ | ho | hu)
  · have : r ∈ log 0 ∨ r ∈ log 1 := by
      by_cases hA : m = A
      · subst hA; rw [objects_A] at hr; exact .inl hr
      · by_cases hB : m = B
        · subst hB; rw [objects_B] at hr; exact .inr hr
        · simp [lbFull, hA, hB] at hr
    rcases this with hr | hr <;> simp [log] at hr <;> rcases hr with rfl | rfl | rfl <;>
      simp at hf
  · exact hp (published m r hr)
  · cases e with
    | thread e =>
      rcases he with ⟨bs, ⟨pc, h⟩, -⟩ | ⟨bs, ⟨pc, h⟩, -⟩ | ⟨old, new, pc, h⟩ <;> kind_absurd h
    | async j p =>
      cases p <;> simp [Execution.Intent, AsyncCopy.Part.writes, Execution.AsyncFootprint,
        and_false, Execution.MmaFootprint, Execution.Copy, Execution.BulkPrefetch,
        Execution.TensorIssue, Execution.TensorStoreIssue, Execution.TensorPrefetchIssue,
        Execution.ClcIssue, Execution.MmaIssue, Execution.CpIssue, get_iff] at he
  · exact not_cpAsyncOverlap_of_none (fun i s ⟨pc, h⟩ => by kind_absurd h) ho
  · exact not_maskedRangeUnalloc_of_none (fun i s m ⟨pc, h⟩ => by kind_absurd h) hu

/-- Every mbarrier operand is `A` or `B`. -/
theorem uses_mbar {e : EvId} {m : Loc} (hu : lbFull.UsesMbar e m) : m = A ∨ m = B := by
  rcases hu with ⟨tx, count, release, scope, pc, h⟩ | ⟨s, ⟨pc, h⟩, -⟩ | ⟨noinc, pc, h⟩ |
      ⟨s, rank, ⟨pc, h⟩, -⟩ | ⟨pc, q, ok, acquire, scope, h⟩ | ⟨pc, h⟩ |
      ⟨address, s, ⟨pc, h⟩, -⟩ | ⟨s, targets, c, ⟨pc, h⟩, -⟩ | ⟨count, pc, h⟩ <;>
    rcases kinds h with h | h | h | h | h | h | h | h <;> cases h <;> simp

/-- The checks that took over the other parts of the former mbarrier check accept `lbFull`: the
eight bytes of each mbarrier are allocated (ERR-UNALLOCATED-ACCESS), an initialization is
published to every other use of each mbarrier (ERR-MBAR-UNINITIALIZED), and no aligned
instruction diverges or is skipped (ERR-ALIGNED-MISMATCH). -/
theorem lbFull_mbar_ok :
    (¬ ∃ e m l, lbFull.UsesMbar e m ∧ Acc.Covers { loc := m, size := 8 } l ∧ lbMem l = none) ∧
    ¬ MbarUninit lbL lbFull ∧ ¬ AlignedMismatch lbL lbFullCode lbFull := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨e, m, l, hu, hl, hn⟩
    rcases uses_mbar hu with rfl | rfl <;> simp [Acc.Covers, Loc.InRange, A, B] at hl <;>
      simp [lbMem, hl.1, hl.2.1] at hn <;> omega
  · rintro ⟨e, m, hu, hni, hn⟩
    have hw := warp_edges
    rcases hu with ⟨tx, count, release, scope, pc, h⟩ | ⟨s, ⟨pc, h⟩, -⟩ | ⟨noinc, pc, h⟩ |
        ⟨s, rank, ⟨pc, h⟩, -⟩ | ⟨pc, q, ok, acquire, scope, h⟩ | ⟨pc, h⟩ |
        ⟨address, s, ⟨pc, h⟩, -⟩ | ⟨s, targets, c, ⟨pc, h⟩, -⟩ | ⟨count, pc, h⟩ <;>
      rcases get_iff.mp h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ |
        ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> cases h
    all_goals first
      | exact hni _ ⟨_, rfl⟩
      | exact hn ⟨(0, 0), 1, ⟨5, rfl⟩, .inl (.single (.inl ⟨rfl, by decide, by decide⟩))⟩
      | exact hn ⟨(1, 0), 1, ⟨5, rfl⟩, .inl (.single (.inl ⟨rfl, by decide, by decide⟩))⟩
      | exact hn ⟨(1, 0), 1, ⟨5, rfl⟩, .inl (.single (.inr (.inr (.inr (.inr (.inl
          ⟨1, 1, hw.2, by decide, by decide, by decide⟩))))))⟩
      | exact hn ⟨(0, 0), 1, ⟨5, rfl⟩, .inl (.single (.inr (.inr (.inr (.inr (.inl
          ⟨1, 1, hw.1, by decide, by decide, by decide⟩))))))⟩
  · rintro ⟨c, ⟨e, f, pe, pf, ke, kf, -, he, -, hm, -⟩ | ⟨e, f, ⟨pc, k⟩, -, he, hm, -⟩⟩
    · rcases kinds he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases c <;>
        simp [AlignedClass.member, isTcColl, Execution.isBar, isCluster, SetMaxNReg.isRequest,
          isMatrix] at hm
    · rcases kinds he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases c <;>
        simp [AlignedClass.exitMember, AlignedClass.member, Kernel.isAlignedCtaBar, isTcColl,
          isCluster, SetMaxNReg.isRequest, isMatrix] at hm

/-! ### The lifetime order (ERR-SHARED-LIFETIME)

Thread `t` polls the other thread's barrier once, observing the other thread's arrival, then
arrives on its own barrier and exits. The old joint relation `Waits` (now a proof device,
`Lemmas/Order/JointWaits.lean`) chains one barrier's history with program order: it has a path from
each thread's arrival to the other thread's exit (`waits_arrival_exit`), so a lifetime check
stated over it would accept "thread 0's arrival completed before thread 1 exited" and the
converse, and its paths close a cycle (`waits_cycle`). The lifetime order has neither path
(`not_completedBefore`): base causality crosses threads only through the warp barrier, before
both polls, and a dependency path cannot leave a poll that is no canonical spin. -/

/-- Thread `t`'s arrival is recorded before the other thread's poll in its barrier's history. -/
theorem arrival_before_poll (t : Nat) (ht : t = 0 ∨ t = 1) :
    Before (lbFull.objects (if t = 0 then A else B)) (.thread (t, 3)) (.thread (1 - t, 2)) := by
  rcases ht with rfl | rfl
  · show Before (lbFull.objects A) _ _
    rw [objects_A]; exact ⟨1, 2, _, _, rfl, rfl, rfl, rfl, by decide⟩
  · show Before (lbFull.objects B) _ _
    rw [objects_B]; exact ⟨1, 2, _, _, rfl, rfl, rfl, rfl, by decide⟩

/-- The old joint relation orders each thread's arrival before the other thread's exit. -/
theorem waits_arrival_exit (t : Nat) (ht : t = 0 ∨ t = 1) :
    Relation.TransGen (Waits lbL lbFull) (.thread (t, 3), true) (.thread (1 - t, 4), false) := by
  have hlen : (lbFull.tr (1 - t)).length = 5 := by rcases ht with rfl | rfl <;> rfl
  exact .head (Waits.before (arrival_before_poll t ht)) (waits_po (by decide) (by omega))

/-- The two paths close a cycle of the old joint relation. -/
theorem waits_cycle : ¬ WaitAcyclic lbL lbFull := by
  intro h
  have hlen : ∀ t, t = 0 ∨ t = 1 → (lbFull.tr t).length = 5 := by
    rintro t (rfl | rfl) <;> rfl
  have p0 : Relation.TransGen (Waits lbL lbFull) (.thread (0, 3), true) (.thread (1, 3), false) :=
    .head (Waits.before (arrival_before_poll 0 (.inl rfl))) (waits_po (by decide) (by
      rw [hlen 1 (.inr rfl)]; decide))
  have p1 : Relation.TransGen (Waits lbL lbFull) (.thread (1, 3), true) (.thread (0, 3), false) :=
    .head (Waits.before (arrival_before_poll 1 (.inr rfl))) (waits_po (by decide) (by
      rw [hlen 0 (.inl rfl)]; decide))
  have n0 : Waits lbL lbFull (.thread (0, 3), false) (.thread (0, 3), true) :=
    Waits.node ⟨_, rfl⟩
  have n1 : Waits lbL lbFull (.thread (1, 3), false) (.thread (1, 3), true) :=
    Waits.node ⟨_, rfl⟩
  exact h _ (p0.tail n1 |>.trans (p1.tail n0))

/-- A dependency path with one object's order increases `erank`. -/
theorem erank_path {o : OrderObject} {a c : AsyncCopy.Ref × Bool}
    (h : Relation.TransGen (fun x y => DepStep lbL lbFullCode lbFull x y ∨
      ObjectOrder lbL lbFull o x y) a c) : erank a < erank c := by
  induction h with
  | single h => exact quiet.depWith_rank erank erank_depStep erank_mbar o h
  | tail _ h ih => exact ih.trans (quiet.depWith_rank erank erank_depStep erank_mbar o h)

/-- Neither arrival's completion precedes the other thread's exit in the lifetime order. -/
theorem not_completedBefore (t : Nat) (ht : t = 0 ∨ t = 1) :
    ¬ CompletedBefore lbL lbFullCode [] lbFull (.thread (t, 3)) (.thread (1 - t, 4), false) := by
  rintro ((h | ⟨o, -, h⟩) | ⟨i, p, w, o, he, -⟩)
  · obtain ⟨e, f, he, hf, -, hcross⟩ := quiet.chain h
    simp only [AsyncCopy.Ref.thread.injEq] at he hf
    subst he hf
    rcases ht with rfl | rfl <;> simp at hcross
  · have := erank_path (Relation.TransGen.mono
      (fun _ _ h => (lifetimeStep_noAssumedOrder (by simp) (by simp)).mp h) _ _ h)
    rcases ht with rfl | rfl <;> simp [erank] at this
  · cases he

/-! ### The execution ordering of tcgen05 fences has no cycle -/

/-- Each relaxed arrival of Litmus C is observed by the other thread's relaxed poll: the
observation step of an execution ordering (`MbarExec`, EXT-TC-EXEC-ORDER). -/
theorem relays : MbarExec lbL lbFull (0, 3) (1, 2) ∧ MbarExec lbL lbFull (1, 3) (0, 2) := by
  have hs : ∀ g h, g < 2 → h < 2 → ScopesMeet lbL .cta g .cta h := by
    intro g h hg hh
    simp only [ScopesMeet, MbarScopeIncludes, SameCta, lbL, Launch.threads]
    omega
  refine ⟨⟨A, 0, 1, false, .cta, false, .cta, ⟨8, rfl⟩, ⟨⟨7, 0, rfl⟩, ?_⟩, hs _ _ (by decide) (by
    decide)⟩,
    ⟨B, 0, 1, false, .cta, false, .cta, ⟨8, rfl⟩, ⟨⟨7, 0, rfl⟩, ?_⟩, hs _ _ (by decide) (by
      decide)⟩⟩
  · rw [objects_A]; exact ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      fun _ _ _ h2 _ => absurd h2 (by omega)⟩
  · rw [objects_B]; exact ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      fun _ _ _ h2 _ => absurd h2 (by omega)⟩

/-- In the consistent execution of Litmus C, no execution ordering closes a cycle: an
ordering's one observation is never followed back, by base causality, to its start. The relay
`(0, 2) →po→ (0, 3) →obs→ (1, 2) →po→ (1, 3) →obs→ (0, 2)` composes two observations and
is no ordering. The observations are relaxed, so base causality from the poll leaves its thread
only through the warp barrier, which precedes the poll. -/
theorem execOrder_acyclic {s x w : EvId} (hp : po lbFull s x) (h : MbarExec lbL lbFull x w) :
    ¬ baseCausality lbL lbFull w s := by
  intro hb
  obtain ⟨m, tx, count, rel, rs, acq, ws, ⟨pc, hx⟩, ⟨⟨pc', q, hw⟩, -⟩, -⟩ := h
  have hw2 := (wait_at hw).2
  have hx3 : x.2 = 3 := by
    rcases get_iff.mp hx with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ |
      ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> first | rfl | cases h
  have := quiet.baseCausality hb
  have := hp.2.1
  omega

end PTX.Tests.WaitOrderLitmus.Full
