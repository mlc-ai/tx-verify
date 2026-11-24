-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Thread.Sites
public import Lemmas.Kernel.Frame
public import Lemmas.Kernel.Goals

@[expose] public section

/-! # The interface between the thread layer and the layers above

The layers above the thread layer see the threads only through `ThreadFacts`: what each thread
does along its own events, stated with the abstract state its machine (`code`) is in before an
event (`stateAt`).

Warp 0 allocates the Tensor Memory columns; thread 0 stores their address, initializes `bar0` and
`bar1`, fences, arms `bar0` for 4352 bytes and issues the copies of `A` and `B` (`headE`). Every
thread passes the first barrier and reads the address (`rdE`), keeping its low 16 bits as its
column `c` (`rdCol`). Thread 0 polls `bar0` until a poll succeeds, issues the MMA and commits it
(`midE`). Every thread polls `bar1` until a poll succeeds, fences, loads its row of the result,
waits for the load, stores the eight words, fences, passes the second barrier and fences; warp 0
frees the columns; every thread exits (`lastE`). `Along` gives the events before each state and
`SiteEvent` the event at it. Undefined behaviour follows a read whose bytes give no column
(`dead`), and is the store of a loaded word that a 32-bit store does not accept (`SiteEvent`). At
the state after its last event, a pending thread can perform its site's template (`fire`). The
thread layer proves `ThreadFacts` (`Thread/Facts.lean`). -/

namespace PTX.Kernels.TcGemm.Proof

open PTX PTX.Flow

noncomputable section

/-- The abstract state of thread `g` before its `k`-th event: `some none` when the machine no
longer follows the thread, `none` after an event into a dead state. -/
abbrev stateAt (L : Launch) (A B D : Nat) (X : Execution) (g k : Nat) :
    Option (Option ThreadD) :=
  Frame.stateAt (code L A B D) X g k

/-! ### The events of the sites -/

def allocE (S : Nat) : Event :=
    ⟨Flow.tmemAlloc_0, .tc (.resource .one (some (tslot S)) (.alloc 32))⟩
def tslotE (S col : Nat) : Event :=
  ⟨Flow.tmemAlloc_0, .wr { loc := tslot S, size := 4 } (Value.bits 32 (BitVec.ofNat 64
    col)).toBytes⟩
def init0E (S : Nat) : Event := ⟨Flow.mbarInit_0, .mbInit (bar0 S) 1⟩
def init1E (S : Nat) : Event := ⟨Flow.mbarInit_1, .mbInit (bar1 S) 1⟩
def fenceE : Event := ⟨Flow.fenceProxy_0, .fenceProxy (.async (some (.shared .cta))) none⟩
def arriveE (S : Nat) : Event := ⟨Flow.mbarArrive_0, .arrive (bar0 S) 4352⟩
/-- The bulk copy of the 4096 bytes of `A` to `sA`, completing through `bar0`. -/
def specA (A S : Nat) : AsyncCopy.Spec :=
  bulkSpec { loc := gA A, size := 4096 } { loc := sA S, size := 4096 } (.mbarrier (bar0 S)) .whole
    none
/-- The bulk copy of the 256 bytes of `B` to `sB`, completing through `bar0`. -/
def specB (B S : Nat) : AsyncCopy.Spec :=
  bulkSpec { loc := gB B, size := 256 } { loc := sB S, size := 256 } (.mbarrier (bar0 S)) .whole
    none
def bulkAE (A S : Nat) : Event := ⟨Flow.bulkCopy_0, .copy (specA A S)⟩
def bulkBE (B S : Nat) : Event := ⟨Flow.bulkCopy_1, .copy (specB B S)⟩
def bar0E : Event := ⟨Flow.bar_0, .bar 0⟩
def rdE (S : Nat) (bs : List (Option Byte)) : Event :=
    ⟨Flow.load_0, .rd { loc := tslot S, size := 4 } bs⟩
def wait0E (S : Nat) (ok : Bool) : Event := ⟨Flow.mbarWait_0, .wait (bar0 S) 0 ok⟩
def mmaE (S c : Nat) : Event := ⟨Flow.mma_0, .tc (.mma c (mmaSpec S) false mmaMask)⟩
def commitE (S : Nat) : Event := ⟨Flow.tcCommit_0, .tc (.commit (commitSpec S))⟩
def wait1E (S : Nat) (ok : Bool) : Event := ⟨Flow.mbarWait_1, .wait (bar1 S) 0 ok⟩
def fa1E : Event := ⟨Flow.tcFence_0, .tc .fenceAfter⟩
def ldE (g c : Nat) (vals : List Value) : Event :=
  ⟨Flow.tmemLoad_0, .tc (.ld (taddr g c) vals .s32x32b)⟩
def wldE : Event := ⟨Flow.tmemWait_0, .tc .waitLd⟩
/-- Store `j` of row `g`: word `j` of the load. -/
def stE (D g : Nat) (vals : List Value) (j : Nat) : Event :=
  ⟨(Site.st j).pc, .wr (stAcc D g j) (stBytes (word vals j))⟩
def fbE : Event := ⟨Flow.tcFence_1, .tc .fenceBefore⟩
def bar1E : Event := ⟨Flow.bar_1, .bar 0⟩
def fa2E : Event := ⟨Flow.tcFence_2, .tc .fenceAfter⟩
def deallocE (c : Nat) : Event := ⟨Flow.tmemDealloc_0, .tc (.resource .one none (.dealloc c 32))⟩
def exitE : Event := ⟨Flow.exit_0, .exit⟩

/-! ### The trace of a thread -/

/-- The events before the first barrier: thread 0's allocation and issue, the allocation of the
other lanes of warp 0, nothing for the other warps. -/
def headE (A B S g col : Nat) : List Event :=
  if g = 0 then
    [allocE S, tslotE S col, init0E S, init1E S, fenceE, arriveE S, bulkAE A S, bulkBE B S]
  else if g / 32 = 0 then [allocE S] else []

/-- Thread 0 after the address read: failed polls of `bar0`, the successful one, the MMA and the
commit. -/
def midE (S c n : Nat) : List Event :=
  List.replicate n (wait0E S false) ++ [wait0E S true, mmaE S c, commitE S]

/-- The events up to the polls of `bar1`. -/
def preW1 (A B S g col : Nat) (bs : List (Option Byte)) (c n0 : Nat) : List Event :=
  headE A B S g col ++ [bar0E, rdE S bs] ++ (if g = 0 then midE S c n0 else [])

/-- The stores of the first `j` words of the row. -/
def storesE (D g : Nat) (vals : List Value) (j : Nat) : List Event := (List.range j).map
    (stE D g vals)

/-- From the successful poll of `bar1` to the exit. -/
def lastE (D S g c : Nat) (vals : List Value) : List Event :=
  [wait1E S true, fa1E, ldE g c vals, wldE] ++ storesE D g vals 8 ++ [fbE, bar1E, fa2E] ++
    (if g / 32 = 0 then [deallocE c] else []) ++ [exitE]

/-- The loaded words that are stored are words. -/
def Words (vals : List Value) (j : Nat) : Prop := ∀ i < j, StoreOk (word vals i)

/-- Thread 0 between its address read and its commit, before `midE`'s `k`-th event. -/
def Mid (L : Launch) (A B g : Nat) (d : ThreadD) (k : Nat) (pre : List Event) : Prop :=
  g = 0 ∧ ∃ col bs n, col < 2 ^ 16 ∧ bs.length = 4 ∧ rdCol bs = some d.c ∧
    pre = headE A B L.sharedBase 0 col ++ [bar0E, rdE L.sharedBase bs] ++
      List.replicate n (wait0E L.sharedBase false) ++
        [wait0E L.sharedBase true, mmaE L.sharedBase d.c].take k

/-- A thread past its address read and thread 0's commit, before `lastE`'s `k`-th event. -/
def After (L : Launch) (A B D g : Nat) (d : ThreadD) (k : Nat) (pre : List Event) : Prop :=
  ∃ col bs n0 n, col < 2 ^ 16 ∧ bs.length = 4 ∧ rdCol bs = some d.c ∧
    pre = preW1 A B L.sharedBase g col bs d.c n0 ++ List.replicate n (wait1E L.sharedBase false) ++
      (lastE D L.sharedBase g d.c d.vals).take k

/-- The events of thread `g` before it is at a state: the run invariant. -/
def Along (L : Launch) (A B D g : Nat) (d : ThreadD) (pre : List Event) : Prop :=
  match d.site with
  | .alloc => g / 32 = 0 ∧ pre = []
  | .allocSt => g = 0 ∧ pre = [allocE L.sharedBase]
  | .init0 => g = 0 ∧ ∃ col < 2 ^ 16, pre = (headE A B L.sharedBase 0 col).take 2
  | .init1 => g = 0 ∧ ∃ col < 2 ^ 16, pre = (headE A B L.sharedBase 0 col).take 3
  | .fence => g = 0 ∧ ∃ col < 2 ^ 16, pre = (headE A B L.sharedBase 0 col).take 4
  | .arrive => g = 0 ∧ ∃ col < 2 ^ 16, pre = (headE A B L.sharedBase 0 col).take 5
  | .bulkA => g = 0 ∧ ∃ col < 2 ^ 16, pre = (headE A B L.sharedBase 0 col).take 6
  | .bulkB => g = 0 ∧ ∃ col < 2 ^ 16, pre = (headE A B L.sharedBase 0 col).take 7
  | .bar0 z => z = decide (g = 0) ∧ ∃ col < 2 ^ 16, pre = headE A B L.sharedBase g col
  | .load z => z = decide (g = 0) ∧ ∃ col < 2 ^ 16, pre = headE A B L.sharedBase g col ++ [bar0E]
  | .wait0 => Mid L A B g d 0 pre
  | .mma => Mid L A B g d 1 pre
  | .commit => Mid L A B g d 2 pre
  | .wait1 => After L A B D g d 0 pre
  | .fence1 => After L A B D g d 1 pre
  | .ld => After L A B D g d 2 pre
  | .waitLd => After L A B D g d 3 pre ∧ d.vals.length = 8
  | .st j => After L A B D g d (4 + j) pre ∧ d.vals.length = 8 ∧ j < 8 ∧ Words d.vals j
  | .fenceB => After L A B D g d 12 pre ∧ d.vals.length = 8 ∧ Words d.vals 8
  | .bar1 => After L A B D g d 13 pre ∧ d.vals.length = 8 ∧ Words d.vals 8
  | .fence2 => After L A B D g d 14 pre ∧ d.vals.length = 8 ∧ Words d.vals 8
  | .dealloc => g / 32 = 0 ∧ After L A B D g d 15 pre ∧ d.vals.length = 8 ∧ Words d.vals 8
  | .exit => After L A B D g d (if g / 32 = 0 then 16 else 15) pre ∧ d.vals.length = 8 ∧
      Words d.vals 8

/-- The event a site performs. -/
def SiteEvent (L : Launch) (A B D g : Nat) (d : ThreadD) (e : Event) : Prop :=
  match d.site with
  | .alloc => e = allocE L.sharedBase
  | .allocSt => ∃ col < 2 ^ 16, e = tslotE L.sharedBase col
  | .init0 => e = init0E L.sharedBase
  | .init1 => e = init1E L.sharedBase
  | .fence => e = fenceE
  | .arrive => e = arriveE L.sharedBase
  | .bulkA => e = bulkAE A L.sharedBase
  | .bulkB => e = bulkBE B L.sharedBase
  | .bar0 _ => e = bar0E
  | .load _ => ∃ bs, bs.length = 4 ∧ e = rdE L.sharedBase bs
  | .wait0 => ∃ ok, e = wait0E L.sharedBase ok
  | .mma => e = mmaE L.sharedBase d.c
  | .commit => e = commitE L.sharedBase
  | .wait1 => ∃ ok, e = wait1E L.sharedBase ok
  | .fence1 => e = fa1E
  | .ld => ∃ vals, vals.length = 8 ∧ e = ldE g d.c vals
  | .waitLd => e = wldE
  | .st j => (StoreOk (word d.vals j) ∧ e = stE D g d.vals j) ∨
      (¬ StoreOk (word d.vals j) ∧ ∃ f, e = ⟨(Site.st j).pc, .ub f⟩)
  | .fenceB => e = fbE
  | .bar1 => e = bar1E
  | .fence2 => e = fa2E
  | .dealloc => e = deallocE d.c
  | .exit => e = exitE

/-- The template a site's instruction makes. -/
def SiteTmpl (L : Launch) (A B D g : Nat) (d : ThreadD) (m : Tmpl) : Prop :=
  match d.site with
  | .alloc => ∃ u, m = .tc (.resource .one (some (tslot L.sharedBase)) (.alloc 32)) u
  | .allocSt => ∃ u, m = .tcAllocStore (tslot L.sharedBase) u
  | .init0 => ∃ u, m = .mbInit (bar0 L.sharedBase) 1 u
  | .init1 => ∃ u, m = .mbInit (bar1 L.sharedBase) 1 u
  | .fence => ∃ u, m = .fenceProxy (.async (some (.shared .cta))) none u
  | .arrive => ∃ u, m = .arrive (bar0 L.sharedBase) 4352 u
  | .bulkA => ∃ u, m = .copy (specA A L.sharedBase) u
  | .bulkB => ∃ u, m = .copy (specB B L.sharedBase) u
  | .bar0 _ => ∃ u, m = .bar 0 u
  | .load _ => ∃ k, m = .read { loc := tslot L.sharedBase, size := 4 } k
  | .wait0 => ∃ k, m = .wait (bar0 L.sharedBase) 0 k
  | .mma => ∃ u, m = .tc (.mma d.c (mmaSpec L.sharedBase) false mmaMask) u
  | .commit => ∃ u, m = .tc (.commit (commitSpec L.sharedBase)) u
  | .wait1 => ∃ k, m = .wait (bar1 L.sharedBase) 0 k
  | .fence1 => ∃ u, m = .tc .fenceAfter u
  | .ld => ∃ k, m = .tcLd (taddr g d.c) 8 .s32x32b k
  | .waitLd => ∃ u, m = .tc .waitLd u
  | .st j => (StoreOk (word d.vals j) ∧
        ∃ u, m = .write (stAcc D g j) (stBytes (word d.vals j)) u) ∨
      (¬ StoreOk (word d.vals j) ∧ ∃ f, m = .ub f)
  | .fenceB => ∃ u, m = .tc .fenceBefore u
  | .bar1 => ∃ u, m = .bar 0 u
  | .fence2 => ∃ u, m = .tc .fenceAfter u
  | .dealloc => ∃ u, m = .tc (.resource .one none (.dealloc d.c 32)) u
  | .exit => m = .exit

/-- Per-thread facts of an execution. -/
structure ThreadFacts (L : Launch) (A B D : Nat) (X : Execution) : Prop where
  /-- Every launched thread is simulated by its machine. -/
  sound : ∀ g < L.threads, (code L A B D g).Sound
  /-- Every launched thread is followed by its machine at each of its events. -/
  tracked : Frame.Tracked (code L A B D) X
  /-- An event of a followed thread is its state's event. -/
  event : ∀ {g k : Nat} {e : Event} {d : ThreadD}, g < L.threads → X.get (g, k) = some e →
    stateAt L A B D X g k = some (some d) → SiteEvent L A B D g d e
  /-- Before a followed state, the thread has made the events of `Along`. -/
  along : ∀ {g k : Nat} {d : ThreadD}, g < L.threads → k ≤ (X.tr g).length →
    stateAt L A B D X g k = some (some d) → Along L A B D g d ((X.tr g).take k)
  /-- An event after the machine stopped is undefined behaviour right after a read whose bytes
  give no column. -/
  dead : ∀ {g k : Nat} {e : Event}, g < L.threads → X.get (g, k) = some e →
    stateAt L A B D X g k = none → ∃ pc f bs, e = ⟨pc, .ub f⟩ ∧ 0 < k ∧
      X.get (g, k - 1) = some (rdE L.sharedBase bs) ∧ rdCol bs = none
  /-- A thread whose run has not ended, at the state after its last event, reaches by local
  steps a concrete state whose template is its site's. -/
  fire : ∀ {g : Nat} {d : ThreadD} {t : TState}, g < L.threads →
    stateAt L A B D X g (X.tr g).length = some (some d) → Run kernel [] L g {} (X.tr g) (some t) →
    ∃ t1 m, Relation.ReflTransGen (Tau kernel [] L g) t t1 ∧ t1.pc = d.site.pc ∧
      t1.sub = d.site.sub ∧ out kernel [] L g t1 = .ev m ∧ SiteTmpl L A B D g d m

/-- An event that ends its thread is its last. -/
theorem end_last {L : Launch} {mem0 : Mem0} {X : Execution} (hX : Consistent L kernel [] mem0 X)
    {g i : Nat} {e : Event} (he : X.get (g, i) = some e) (hk : Flow.Ends e) :
    i + 1 = (X.tr g).length := by
  obtain ⟨o, hr⟩ := hX.thr g (Frame.lt_of_get hX he)
  exact Flow.Run.end_last hr he hk

end

end PTX.Kernels.TcGemm.Proof
