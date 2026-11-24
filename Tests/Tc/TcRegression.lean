-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Core.Source.Decode
public meta import Core.Source.Decode
public import Lemmas.Async.AsyncOrder
public import Lemmas.MBarrier.MBarrierHistory
public import Lemmas.Tcgen05.TcCommit

/-!
# Regression tests for the `tcgen05` rules

Three executions a review found accepted by an earlier version of the rules; each is now
rejected.

* `CommitCycle`: a thread waits on an mbarrier whose only arrival is a later
  `tcgen05.commit` of the same thread. The commit is a producer (DEP-ASYNC-STAGE-ORDER), so the wait
  depends on it and the waiting relation has a cycle.
* `CollectiveCycle`: lane 0 waits on an mbarrier before a warp-collective
  `tcgen05.wait::ld`; lane 1 executes that collective, then arrives on the mbarrier. The
  collective completes only after every lane issued it, so the waiting relation has a cycle.
* `GrowingAlloc`: every lane of a warp allocates 32 columns, then 64. The allocator rejects an
  increasing request (ERR-TMEM-RESOURCE; a later allocation with more columns is
  undefined, §9.7.18.7.1).

The acquire path (EXT-TCACQUIRE) is accepted without `tcgen05.fence`, and its limits are
kept:

* `AcquirePath`: MMA, commit, acquire wait, load, `wait::ld`, dealloc in one thread, with no
  tcgen05 fence. The load sees the MMA (`TcMma.DoneBefore`) and both are complete at the dealloc
  (`TcMma.CompletedBefore`).
* `WrongBarrier`: the commit arrives on one mbarrier and the wait is on another; the load
  does not see the MMA.
* `LdNoWait`: a load followed by the dealloc with no `wait::ld`; the load is not complete.
* `LdByCommit`: a load whose only completion evidence is a commit and a successful wait;
  that tracks MMAs, not loads, so the load is not complete.
* `MmaByWaitLd`: an MMA whose only completion evidence is a `wait::ld`; that tracks loads,
  not MMAs, so the MMA is not complete.
* `CommitNoRelease`: a write before a commit is not ordered before the events after a wait
  on that commit's mbarrier: a commit is not a release arrival (MEM-MBAR-SYNCHRONIZES).
* `DecodeWait`: the default `try_wait` and `.acquire.cta` (with or without the time hint)
  are acquires; `.relaxed` (with or without the hint) is decoded as a non-acquire wait, so
  the acquire/relaxed distinction EXT-TCACQUIRE relies on is preserved.
-/

namespace PTX.Tests.TcRegression
open PTX PTX.AsyncCopy

noncomputable section

private def replayLog (ops : List (Ref × MBarrier.Action)) : List (MBarrier.Record Ref) :=
  match MBarrier.replay none ops with
  | .ok xs => xs
  | .error _ => []

namespace CommitCycle

def launch : Launch := { grid := 1, block := 1, params := fun _ => none, sharedBase := 0,
                         clusterSize := 1 }
def bar : Loc := ⟨.shared, 0, 0⟩
def X : Execution where
  tr g := if g = 0 then [⟨1, .mbInit bar 1⟩, ⟨2, .wait bar 0 true⟩,
    ⟨4, .tc (.commit (TcCommit.unicast bar))⟩, ⟨5, .exit⟩] else []
  rf _ _ := none
  tcNotified := fun i => if i = (0, 2) then {0} else ∅
  objects m := if m = bar then replayLog [(.thread (0, 0), .init 1),
    (.async (0, 2) (.tcNotify 0), .arrive 1 0), (.thread (0, 1), .pollParity 0 true)] else []

theorem cycle : ¬ WaitAcyclic launch X := by
  intro h
  apply h (.thread (0, 1), true)
  have e1 := waits_po (L := launch) (X := X) (g := 0) (i := 1) (j := 2) (by decide) (by decide)
  have e2 := waits_self (L := launch) (X := X) (e := (0, 2)) (by decide)
  have e3 : Waits launch X (.thread (0, 2), false) (.async (0, 2) (.tcNotify 0), false) :=
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      ⟨rfl, rfl, ⟨rfl, rfl, ⟨(0, 2), .tcNotify 0, rfl, rfl,
        ⟨⟨4, .tc (.commit (TcCommit.unicast bar))⟩, by simp [Execution.get, X]⟩,
        by simp [Execution.AsyncPresent, X], trivial⟩⟩⟩)))))))))))))
  have e4 : Waits launch X (.async (0, 2) (.tcNotify 0), false) (.async (0, 2) (.tcNotify 0),
    true) :=
    Waits.node (by simp [Execution.RefPresent, Execution.AsyncPresent, X])
  have e5 : Waits launch X (.async (0, 2) (.tcNotify 0), true) (.thread (0, 1), true) :=
    waits_object (m := bar) ⟨1, 2, _, _, rfl, rfl, rfl, rfl, by decide⟩
  exact (((e1).tail e3).tail e4).tail e5

end CommitCycle

namespace CollectiveCycle

def launch : Launch := { grid := 1, block := 32, params := fun _ => none, sharedBase := 0,
                         clusterSize := 1 }
def mbar : Loc := ⟨.shared, 0, 0⟩
def ini : Event := ⟨3, .mbInit mbar 1⟩
def sync : Event := ⟨4, .bar 0⟩
def poll : Event := ⟨6, .wait mbar 0 true⟩
def coll : Event := ⟨8, .tc .waitLd⟩
def arr : Event := ⟨10, .arrive mbar 0⟩
def done : Event := ⟨11, .exit⟩

def X : Execution where
  tr g := if g = 0 then [ini, sync, poll, coll, done]
    else if g = 1 then [sync, coll, arr, done] else if g < 32 then [sync, coll, done] else []
  rf _ _ := none
  objects m := if m = mbar then replayLog [(.thread (0, 0), .init 1),
    (.thread (1, 2), .arrive 1 0), (.thread (0, 2), .pollParity 0 true)] else []

theorem cycle : ¬ WaitAcyclic launch X := by
  intro h
  apply h (.thread (0, 2), true)
  have hw : SameWarp launch 0 1 :=
    ⟨⟨by simp [launch, Launch.threads], by simp [launch, Launch.threads], rfl⟩, rfl⟩
  have k0 : X.TcK (0, 3) 0 := ⟨⟨coll, rfl, rfl⟩, by decide⟩
  have k1 : X.TcK (1, 1) 0 := ⟨⟨coll, rfl, rfl⟩, by decide⟩
  have e1 := waits_po (L := launch) (X := X) (g := 0) (i := 2) (j := 3) (by decide) (by decide)
  have e2 : Waits launch X (.thread (0, 3), false) (.thread (1, 1), true) :=
    .inr (.inr (.inr (.inr (.inl ⟨rfl, rfl, (0, 3), (1, 1), rfl, rfl, hw, 0, k0, k1⟩))))
  have e3 := waits_po (L := launch) (X := X) (g := 1) (i := 1) (j := 2) (by decide) (by decide)
  have e4 := waits_self (L := launch) (X := X) (e := (1, 2)) (by decide)
  have e5 : Waits launch X (.thread (1, 2), true) (.thread (0, 2), true) :=
    waits_object (m := mbar) ⟨1, 2, _, _, rfl, rfl, rfl, rfl, by decide⟩
  exact (((e1.tail e2).trans e3).tail e4).tail e5

end CollectiveCycle

namespace GrowingAlloc

def launch : Launch := { grid := 1, block := 32, params := fun _ => none, sharedBase := 0,
                         clusterSize := 1 }
def dst : Loc := ⟨.shared, 0, 0⟩
def req (pc index : Nat) (a : Tmem.Action) : Tmem.Pair.Requests :=
  ⟨⟨0, 0, fun _ => index, pc, some dst, a.request⟩, .one, a⟩
def X : Execution where
  tr := fun g => if g < 32 then [⟨0, .tc (.resource .one (some dst) (.alloc 32))⟩, ⟨1,
    .tc (.resource .one (some dst) (.alloc 64))⟩,
    ⟨2, .tc (.resource .one none (.dealloc 0 32))⟩, ⟨3, .tc (.resource .one none (.dealloc 32 64))⟩,
      ⟨4, .exit⟩] else []
  rf := fun _ _ => none
  tmemHistory := fun k => if k = 0 then [req 0 0 (.alloc 32 0), req 1 1 (.alloc 64 32)] else []

/-- A growing request is a resource fault of the recorded history. -/
theorem growing_unsafe : Tmem.Pair.ResourceUnsafe launch X :=
  ⟨0, .inl ⟨.increasingRequest, by decide⟩⟩

end GrowingAlloc

/-! ## The acquire path for `tcgen05` -/

/-- A one-thread CTA. -/
def one : Launch := { grid := 1, block := 1, params := fun _ => none, sharedBase := 0,
                      clusterSize := 1 }
@[simp] def bar : Loc := ⟨.shared, 0, 0⟩
@[simp] def bar' : Loc := ⟨.shared, 0, 8⟩
def spec : TcMma.OperandSpec :=
  ⟨⟨.one, .i8 true true false, 128, 8, false, false, false, false, false⟩,
    ⟨64, 0, 0, 0, false, false, .none⟩, ⟨64, 0, 0, 0, false, false, .none⟩, 0, 0, none, {}⟩
@[simp] def mma : Event := ⟨1, .tc (.mma 0 spec false [0, 0, 0, 0])⟩
@[simp] def tld : Event := ⟨2, .tc (.ld 0 [] .s32x32b)⟩
@[simp] def waitLd : Event := ⟨3, .tc .waitLd⟩
@[simp] def dealloc : Event := ⟨4, .tc (.resource .one none (.dealloc 0 32))⟩
@[simp] def commit (m : Loc) : Event := ⟨5, .tc (.commit (TcCommit.unicast m))⟩
@[simp] def poll (m : Loc) : Event := ⟨6, .wait m 0 true⟩
@[simp] def init (m : Loc) : Event := ⟨7, .mbInit m 1⟩

/-- Thread 0 runs `tr`. -/
@[simp] def single (tr : List Event) : Execution where
  tr := fun g => if g = 0 then tr else []
  rf := fun _ _ => none

theorem sameCta : SameCta one 0 0 := ⟨by decide, by decide, rfl⟩

namespace AcquirePath

def X : Execution := { single [init bar, mma, commit bar, poll bar, tld, waitLd, dealloc, ⟨8,
                       .exit⟩] with
  async := { mmaOperands := fun i => if i == (0, 1) then some ⟨[], []⟩ else none, mmaDone :=
             fun i => i == (0, 1) }
  tcNotified := fun i => if i = (0, 2) then {0} else ∅
  objects := fun m => if m = bar then replayLog [(.thread (0, 0), .init 1),
    (.async (0, 2) (.tcNotify 0), .arrive 1 0), (.thread (0, 3), .pollParity 0 true)] else [] }

theorem po' {i j : Nat} (hij : i < j) (hj : j < 8) : baseCausality one X (0, i) (0, j) :=
  .single (.inl (po_of_not_access rfl hij hj (by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;>
    first | omega | decide)))

theorem observed : AsyncCopy.AsyncObserved X (0, 1) .mmaDone (0, 3) true .cta := by
  refine ⟨.async (0, 2) (.tcNotify 0), bar, ⟨(0, 2), TcCommit.unicast bar, 0, rfl,
    ⟨rfl, by decide, .inl ⟨0, spec, false, [0, 0, 0, 0], ⟨1, rfl⟩⟩, _, ⟨5, rfl⟩⟩,
    ⟨5, rfl⟩, TcCommit.target_unicast rfl, by simp [X]⟩, ⟨⟨6, 0, rfl⟩, ?_⟩⟩
  exact ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      fun _ _ _ h2 _ => absurd h2 (by omega)⟩

/-- The commit's cluster-scope arrive and the CTA-scope wait meet in the one thread. -/
theorem scopes : ScopesMeet one .cluster 0 .cta 0 := ⟨⟨by decide, by decide, rfl⟩, sameCta⟩

/-- The load sees the completed MMA without any tcgen05 fence. -/
theorem vis : TcMma.DoneBefore one X (0, 1) (0, 4) :=
  .inl ⟨(0, 3), .cta, observed, scopes, po' (by decide) (by decide)⟩

theorem ldDone : TcMma.CompletedBefore one X (0, 4) (0, 6) :=
  ⟨fun _ => ⟨(0, 5), ⟨3, rfl⟩, rfl, by decide, .inl (po' (by decide) (by decide))⟩,
   fun ⟨_, _, _, _, h⟩ => by simp [X, Execution.get] at h,
   fun hh => by rcases hh with ⟨_, _, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;>
     simp [X, Execution.get] at h⟩

theorem mmaDone : TcMma.CompletedBefore one X (0, 1) (0, 6) :=
  ⟨fun ⟨_, _, _, _, h⟩ => by simp [X, Execution.get] at h,
   fun ⟨_, _, _, _, h⟩ => by simp [X, Execution.get] at h,
   fun _ => .inl ⟨(0, 3), .cta, observed, scopes, po' (by decide) (by decide)⟩⟩

end AcquirePath

namespace WrongBarrier

def X : Execution := { single [init bar, init bar', mma, commit bar,
    ⟨9, .arrive bar' 0⟩, poll bar', tld, ⟨8, .exit⟩] with
  async := { mmaOperands := fun i => if i == (0, 2) then some ⟨[], []⟩ else none, mmaDone :=
             fun i => i == (0, 2) }
  tcNotified := fun i => if i = (0, 3) then {0} else ∅
  objects := fun m => if m = bar then replayLog [(.thread (0, 0), .init 1),
    (.async (0, 3) (.tcNotify 0), .arrive 1 0)] else if m = bar' then replayLog [
    (.thread (0, 1), .init 1), (.thread (0, 4), .arrive 1 0), (.thread (0, 5),
      .pollParity 0 true)] else [] }

theorem not_vis : ¬ TcMma.DoneBefore one X (0, 2) (0, 6) := by
  suffices key : ∀ (w c : EvId) (s : TcCommit.Spec) (rank : Fin 16) (m : Loc), X.Commit c s →
      TcCommit.target s rank = some m → rank ∈ X.tcNotified c →
      MBarrier.UpdateBeforeWait (X.objects m) (.async c (.tcNotify rank)) (.thread w) → False by
    rintro (⟨w, _, ⟨_, m, ⟨c, s, rank, rfl, _, hc, htg, hn⟩, _, hu⟩, _⟩ |
      ⟨w, ⟨_, _, ⟨_, m, ⟨c, s, rank, rfl, _, hc, htg, hn⟩, _, hu⟩, _⟩, _⟩)
    · exact key w c s rank m hc htg hn hu
    · exact key w c s rank m hc htg hn hu
  rintro w c s rank m hc htg hn ⟨i, j, r, wr, phase, _, _, _, hw, _, _, hwait, _⟩
  have hce : c = (0, 3) := by
    by_contra hne
    simp [X, hne] at hn
  subst c
  obtain ⟨pc, hp⟩ := hc
  simp [X, Execution.get] at hp
  obtain ⟨_, rfl⟩ := hp
  obtain ⟨_, rfl⟩ := TcCommit.target_unicast_inv rfl htg
  have hwmem := List.mem_of_getElem? hw
  change wr ∈ [_, _] at hwmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwmem
  rcases hwmem with rfl | rfl <;> cases hwait

end WrongBarrier

/-! The commit's arrive has cluster scope (§9.7.18.12.1); the observing wait must be morally
strong with it (§8.7), so a `.cta` wait in another CTA observes the MMA's completion but
does not order it. -/
namespace PeerScope

/-- Two one-thread CTAs in one cluster. -/
def two : Launch := { grid := 2, block := 1, params := fun _ => none, sharedBase := 0,
                      clusterSize := 2 }
@[simp] def peerBar : Loc := ⟨.shared, 1, 0⟩

def X (ws : MbarScope) : Execution where
  tr g := if g = 0 then [⟨1, .tc (.mma 0 spec false [0, 0, 0, 0])⟩,
      ⟨5, .tc (.commit (TcCommit.unicast peerBar))⟩, ⟨8, .exit⟩]
    else if g = 1 then [⟨7, .mbInit peerBar 1⟩, ⟨6, .wait peerBar 0 true true ws⟩, ⟨8, .exit⟩]
    else []
  rf _ _ := none
  async := { mmaOperands := fun i => if i == (0, 0) then some ⟨[], []⟩ else none,
             mmaDone := fun i => i == (0, 0) }
  tcNotified := fun i => if i = (0, 1) then {0} else ∅
  objects m := if m = peerBar then replayLog [(.thread (1, 0), .init 1),
    (.async (0, 1) (.tcNotify 0), .arrive 1 0), (.thread (1, 1), .pollParity 0 true)] else []

theorem observed (ws : MbarScope) : AsyncCopy.AsyncObserved (X ws) (0, 0) .mmaDone (1, 1) true ws :=
    by
  refine ⟨.async (0, 1) (.tcNotify 0), peerBar, ⟨(0, 1), TcCommit.unicast peerBar, 0, rfl,
    ⟨rfl, by decide, .inl ⟨0, spec, false, [0, 0, 0, 0], ⟨1, rfl⟩⟩, _, ⟨5, rfl⟩⟩,
    ⟨5, rfl⟩, TcCommit.target_unicast rfl, by simp [X]⟩, ⟨⟨6, 0, rfl⟩, ?_⟩⟩
  exact ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
    fun _ _ _ h2 _ => absurd h2 (by omega)⟩

/-- A cluster-scoped wait in the peer CTA orders the MMA before its later instructions. -/
theorem cluster_done : TcMma.DoneBefore two (X .cluster) (0, 0) (1, 2) :=
  .inl ⟨(1, 1), .cluster, observed .cluster, ⟨⟨by decide, by decide, rfl⟩, ⟨by decide, by decide,
    rfl⟩⟩,
    .single (.inl ⟨rfl, by decide, by decide⟩)⟩

/-- The same observation by a CTA-scoped wait orders nothing. -/
theorem cta_not_done : ¬ TcMma.DoneBefore two (X .cta) (0, 0) (1, 2) := by
  suffices key : ∀ w acq ws, AsyncCopy.AsyncObserved (X .cta) (0, 0) .mmaDone w acq ws →
      ¬ ScopesMeet two .cluster 0 ws w.1 by
    rintro (⟨w, ws, ho, hs, -⟩ | ⟨w, ⟨acq, ws, ho, hs⟩, -⟩)
    · exact key w true ws ho hs
    · exact key w acq ws ho hs
  rintro ⟨g, j⟩ acq ws ho ⟨-, hs⟩
  obtain ⟨_, _, _, m, _, _, _, _, ⟨pc, parity, hw⟩, _⟩ := ho.mma
  have hg : g = 1 ∧ ws = .cta := by
    by_cases h0 : g = 0
    · subst g
      have hm := List.mem_of_getElem? hw
      simp [X] at hm
    · by_cases h1 : g = 1
      · subst g
        have hm := List.mem_of_getElem? hw
        simp [X] at hm
        exact ⟨rfl, hm.2.2.2.symm.1⟩
      · simp [X, Execution.get, h0, h1] at hw
  obtain ⟨rfl, rfl⟩ := hg
  exact absurd hs.2.2 (by simp [two])

end PeerScope

namespace LdNoWait

def X : Execution := single [tld, dealloc, ⟨8, .exit⟩]

theorem not_done : ¬ TcMma.CompletedBefore one X (0, 0) (0, 1) := by
  rintro ⟨h, -⟩
  obtain ⟨⟨_, w⟩, ⟨_, hw⟩, rfl, -⟩ := h ⟨_, _, .s32x32b, 2, rfl⟩
  rcases w with _ | _ | _ | w <;> simp [X, Execution.get] at hw

end LdNoWait

namespace LdByCommit

def X : Execution := single [init bar, tld, commit bar, poll bar, dealloc, ⟨8, .exit⟩]

theorem not_done : ¬ TcMma.CompletedBefore one X (0, 1) (0, 4) := by
  rintro ⟨h, -⟩
  obtain ⟨⟨_, w⟩, ⟨_, hw⟩, rfl, -⟩ := h ⟨_, _, .s32x32b, 2, rfl⟩
  rcases w with _ | _ | _ | _ | _ | _ | w <;> simp [X, Execution.get] at hw

end LdByCommit

namespace MmaByWaitLd

def X : Execution := single [mma, waitLd, dealloc, ⟨8, .exit⟩]

theorem not_done : ¬ TcMma.CompletedBefore one X (0, 0) (0, 2) := by
  rintro ⟨-, -, h⟩
  rcases h (.inl ⟨_, _, _, _, 1, rfl⟩) with ⟨w, _, ⟨_, _, ⟨c, _, _, _, _, _, _, hn⟩, _⟩, _⟩ |
      ⟨w, ⟨_, _, ⟨_, _, ⟨c, _, _, _, _, _, _, hn⟩, _⟩, _⟩, _⟩ <;>
    exact Finset.notMem_empty _ hn

end MmaByWaitLd

namespace CommitNoRelease

/-- Two threads of one CTA. -/
def two : Launch := { grid := 1, block := 2, params := fun _ => none, sharedBase := 0,
                      clusterSize := 1 }
def data : Acc := { loc := ⟨.shared, 0, 16⟩, size := 4 }

def X : Execution where
  tr g := if g = 0 then [init bar, ⟨9, .wr data []⟩, commit bar, ⟨8, .exit⟩]
    else if g = 1 then [poll bar, ⟨10, .rd data []⟩, ⟨8, .exit⟩] else []
  rf _ _ := none
  tcNotified := fun i => if i = (0, 2) then {0} else ∅
  objects m := if m = bar then replayLog [(.thread (0, 0), .init 1),
    (.async (0, 2) (.tcNotify 0), .arrive 1 0), (.thread (1, 0), .pollParity 0 true)] else []

theorem not_msync : ¬ MSync two X (0, 1) (1, 1) := by
  rintro ⟨⟨_, x⟩, _, _, _, _, ⟨_, _, _, hx⟩, -, -, -, -, -, rfl, -⟩
  rcases x with _ | _ | _ | _ | x <;> simp [X, Execution.get, init, commit] at hx

end CommitNoRelease

namespace DecodeWait

open Syntax

def env : Decode.Env :=
  { classes := [⟨['%', 'p'], 2, 1⟩, ⟨['%', 'r'], 4, 32⟩], labels := [], params := [] }

def args : List Operand := [.register "%p1", .address [.register "%r1"], .literal "0"]
def hinted : List Operand := args ++ [.literal "1000000"]

#guard (Decode.op env "mbarrier.try_wait.parity.shared::cta.b64" args).toBool
#guard (Decode.op env "mbarrier.try_wait.parity.acquire.cta.shared::cta.b64" args).toBool
#guard (Decode.op env "mbarrier.try_wait.parity.shared::cta.b64" hinted).toBool
#guard (Decode.op env "mbarrier.try_wait.parity.acquire.cta.shared::cta.b64" hinted).toBool
/-- The decoded wait keeps its semantics and scope: `(acquire?, cluster?)`. -/
def waitKind (opcode : String) (as : List Operand) : Option (Bool × Bool) :=
  match Decode.op env opcode as with
  | .ok (.mbarWait _ _ _ _ acquire .cta) => some (acquire, false)
  | .ok (.mbarWait _ _ _ _ acquire .cluster) => some (acquire, true)
  | _ => none

-- A relaxed wait is decoded as non-acquire, so it can never serve EXT-TCACQUIRE.
#guard waitKind "mbarrier.try_wait.parity.relaxed.cta.shared::cta.b64" args = some (false, false)
#guard waitKind "mbarrier.try_wait.parity.acquire.cluster.shared::cta.b64" args = some (true, true)
#guard waitKind "mbarrier.try_wait.parity.relaxed.cta.shared::cta.b64" hinted = some (false, false)
#guard waitKind "mbarrier.try_wait.parity.shared::cta.b64" hinted = some (true, false)

end DecodeWait

end

end PTX.Tests.TcRegression
