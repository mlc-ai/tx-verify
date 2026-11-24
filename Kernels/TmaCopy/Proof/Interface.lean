-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmaCopy.Proof.Thread.Machine
public import Lemmas.Kernel.Frame
public import Lemmas.Kernel.Goals
public import Lemmas.Flow.SpinsAtLoop

@[expose] public section

/-! # The interface between the thread layer and the layers above

The layers above the thread layer see the threads only through `ThreadFacts`: what each thread
does along its own events, stated with the abstract state its machine (`code`) is in before an
event (`stateAt`). Thread 0 initializes the mbarrier, fences, arrives with an expected
transaction of 16 bytes, issues the bulk copy (`issue`), polls the mbarrier until a poll
succeeds, reads the first word of `buf` and writes it to `B`, then exits; every other thread
only exits (`Along`, the events before each state, and `SiteEvent`, the event at it). Undefined
behaviour follows a read whose bytes are not one 4-byte value (`dead`, and the store's event).
At the state after its last event, a pending thread can perform its site's template (`fire`).
The poll heads a self loop and is the canonical spin (`spin`, a fact of the code).
The thread layer proves `ThreadFacts` (`Thread/Facts.lean`). -/

namespace PTX.Kernels.TmaCopy.Proof

open PTX PTX.Flow

noncomputable section

/-- The abstract state of thread `g` before its `k`-th event: `some none` when the machine no
longer follows the thread, `none` after an event into a dead state. -/
abbrev stateAt (L : Launch) (A B : Nat) (X : Execution) (g k : Nat) : Option (Option Site) :=
  Frame.stateAt (code L A B) X g k

/-- **The kernel's poll is a canonical spin**: it heads a self loop whose branch alone reads its
predicate. -/
theorem spin : ∃ exit, kernel.CanonicalSpin Flow.mbarWait_0 exit :=
  ⟨_, Kernel.canonicalSpin_of_selfLoop Flow.code_mbarWait_0 Flow.code_14 (by decide) (by decide)
    (by decide +kernel) (by unfold Kernel.SpinPred; decide +kernel)⟩

/-! ### The events of the sites -/

def initE (S : Nat) : Event := ⟨Flow.mbarInit_0, .mbInit (mbar S) 1⟩
def fenceE : Event := ⟨Flow.fenceProxy_0, .fenceProxy (.async (some (.shared .cta))) none⟩
def arriveE (S : Nat) : Event := ⟨Flow.mbarArrive_0, .arrive (mbar S) 16⟩
/-- The bulk copy of the 16 bytes at `A` to `buf`, completing through `mbar`. -/
def copySpec (A S : Nat) : AsyncCopy.Spec :=
  bulkSpec { loc := gA A, size := 16 } { loc := buf S, size := 16 } (.mbarrier (mbar S)) .whole none
def bulkE (A S : Nat) : Event := ⟨Flow.bulkCopy_0, .copy (copySpec A S)⟩
def waitE (S : Nat) (ok : Bool) : Event := ⟨Flow.mbarWait_0, .wait (mbar S) 0 ok⟩
def rdE (S : Nat) (bs : List (Option Byte)) : Event :=
  ⟨Flow.load_0, .rd { loc := buf S, size := 4 } bs⟩
def wrE (B : Nat) (v : Value) : Event := ⟨Flow.store_0, .wr { loc := gB B, size := 4 } v.toBytes⟩
def exE : Event := ⟨Flow.exit_0, .exit⟩

/-- Thread 0's first four events: the initialization, the fence, the arrival and the copy. -/
def issue (A S : Nat) : List Event := [initE S, fenceE, arriveE S, bulkE A S]

/-- The event a site performs. -/
def SiteEvent (L : Launch) (A B : Nat) : Site → Event → Prop
  | .init, e => e = initE L.sharedBase
  | .fence, e => e = fenceE
  | .arrive, e => e = arriveE L.sharedBase
  | .bulk, e => e = bulkE A L.sharedBase
  | .wait, e => ∃ ok, e = waitE L.sharedBase ok
  | .load, e => ∃ bs, e = rdE L.sharedBase bs
  | .store v, e => (v.bytes = 4 ∧ e = wrE B v) ∨ (v.bytes ≠ 4 ∧ ∃ f, e = ⟨Flow.store_0, .ub f⟩)
  | .exit, e => e = exE

/-- The events of thread `g` before it is at a site: the run invariant. -/
def Along (L : Launch) (A B g : Nat) : Site → List Event → Prop
  | .init, pre => g = 0 ∧ pre = []
  | .fence, pre => g = 0 ∧ pre = [initE L.sharedBase]
  | .arrive, pre => g = 0 ∧ pre = [initE L.sharedBase, fenceE]
  | .bulk, pre => g = 0 ∧ pre = [initE L.sharedBase, fenceE, arriveE L.sharedBase]
  | .wait, pre => g = 0 ∧ ∃ n, pre = issue A L.sharedBase ++
      List.replicate n (waitE L.sharedBase false)
  | .load, pre => g = 0 ∧ ∃ n, pre = issue A L.sharedBase ++
      List.replicate n (waitE L.sharedBase false) ++ [waitE L.sharedBase true]
  | .store v, pre => g = 0 ∧ ∃ n bs, pre = issue A L.sharedBase ++
      List.replicate n (waitE L.sharedBase false) ++
        [waitE L.sharedBase true, rdE L.sharedBase bs] ∧
      rebuild 3 bs = .ok v ∧ bs.length = 4
  | .exit, pre => (g ≠ 0 ∧ pre = []) ∨ (g = 0 ∧ ∃ n bs v, pre = issue A L.sharedBase ++
      List.replicate n (waitE L.sharedBase false) ++
        [waitE L.sharedBase true, rdE L.sharedBase bs, wrE B v] ∧
      rebuild 3 bs = .ok v ∧ v.bytes = 4)

/-- The template a site's instruction makes. -/
def SiteTmpl (L : Launch) (A B : Nat) : Site → Tmpl → Prop
  | .init, m => ∃ u, m = .mbInit (mbar L.sharedBase) 1 u
  | .fence, m => ∃ u, m = .fenceProxy (.async (some (.shared .cta))) none u
  | .arrive, m => ∃ u, m = .arrive (mbar L.sharedBase) 16 u
  | .bulk, m => ∃ u, m = .copy (copySpec A L.sharedBase) u
  | .wait, m => ∃ k, m = .wait (mbar L.sharedBase) 0 k
  | .load, m => ∃ k, m = .read { loc := buf L.sharedBase, size := 4 } k
  | .store v, m => (v.bytes = 4 ∧ ∃ u, m = .write { loc := gB B, size := 4 } v.toBytes u) ∨
      (v.bytes ≠ 4 ∧ ∃ f, m = .ub f)
  | .exit, m => m = .exit

/-- Per-thread facts of an execution. -/
structure ThreadFacts (L : Launch) (A B : Nat) (X : Execution) : Prop where
  /-- Every launched thread is simulated by its machine. -/
  sound : ∀ g < L.threads, (code L A B g).Sound
  /-- Every launched thread is followed by its machine at each of its events. -/
  tracked : Frame.Tracked (code L A B) X
  /-- An event of a followed thread is its state's event. -/
  event : ∀ {g k : Nat} {e : Event} {s : Site}, g < L.threads → X.get (g, k) = some e →
    stateAt L A B X g k = some (some s) → SiteEvent L A B s e
  /-- Before a followed state, the thread has made the events of `Along`. -/
  along : ∀ {g k : Nat} {s : Site}, g < L.threads → k ≤ (X.tr g).length →
    stateAt L A B X g k = some (some s) → Along L A B g s ((X.tr g).take k)
  /-- An event after the machine stopped is undefined behaviour right after a read whose bytes
  are not one 4-byte value. -/
  dead : ∀ {g k : Nat} {e : Event}, g < L.threads → X.get (g, k) = some e →
    stateAt L A B X g k = none → ∃ pc f bs, e = ⟨pc, .ub f⟩ ∧ 0 < k ∧
      X.get (g, k - 1) = some (rdE L.sharedBase bs) ∧ ∀ v, rebuild 3 bs = .ok v → v.bytes ≠ 4
  /-- A thread whose run has not ended, at the state after its last event, reaches by local
  steps a concrete state whose template is its site's. -/
  fire : ∀ {g : Nat} {s : Site} {t : TState}, g < L.threads →
    stateAt L A B X g (X.tr g).length = some (some s) → Run kernel [] L g {} (X.tr g) (some t) →
    ∃ t1 m, Relation.ReflTransGen (Tau kernel [] L g) t t1 ∧ t1.pc = s.pc ∧
      out kernel [] L g t1 = .ev m ∧ SiteTmpl L A B s m

end

end PTX.Kernels.TmaCopy.Proof
