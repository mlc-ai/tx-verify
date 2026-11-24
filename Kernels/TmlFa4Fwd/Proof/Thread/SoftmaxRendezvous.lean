-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.AlignedBarrierCases
import Kernels.TmlFa4Fwd.Proof.AllocationBarrierControl
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX Prologue

/-- The four types of CTA rendezvous observed by a softmax lane after startup. -/
inductive SoftmaxRendezvous
  | initialAllocation
  | bias
  | statistics
  | finalAllocation

def SoftmaxRendezvous.id (kind : SoftmaxRendezvous) (l : Launch) (g : Nat) : Nat :=
  match kind with
  | .initialAllocation | .finalAllocation => 2
  | .bias => 11 + warpIndex l g / 4
  | .statistics => 3 + warpIndex l g

def SoftmaxRendezvous.mode : SoftmaxRendezvous → BarMode
  | .initialAllocation | .bias => .sync
  | .statistics | .finalAllocation => .arrive

def SoftmaxRendezvous.count : SoftmaxRendezvous → Option Nat
  | .initialAllocation | .finalAllocation => some 416
  | .bias => some 128
  | .statistics => some 64

/-- The initial allocation rendezvous is the second CTA barrier seen by a lane.
All work and finalization rendezvous follow it. -/
def SoftmaxRendezvous.validOrdinal (kind : SoftmaxRendezvous) (ordinal : Nat) : Prop :=
  match kind with
  | .initialAllocation => ordinal = 1
  | _ => 1 < ordinal

/-- An actual softmax lane arrival, identified by its rendezvous kind. -/
def SoftmaxRendezvous.Observed (kind : SoftmaxRendezvous)
    (l : Launch) (X : Execution) (i : EvId) : Prop :=
  BarrierArrival X i (kind.id l i.1) kind.count kind.mode

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The decoded named barriers of a softmax lane include startup, bias, statistics, and exit. -/
theorem softmaxBarrierStation {g pos site id : Nat} {count : Option Nat} {mode : BarMode}
    (hw : warpIndex l g < 8) (hGet : X.get (g,pos) = some ⟨site, .bar id count mode⟩) :
    site = 173 ∨ (site = 3103 ∨ site = 7741 ∨ site = 3583 ∨ site = 5271 ∨
      site ∈ TmlFa4Fwd.Softmax.softmaxStatsSites) := by
  obtain ⟨hSites, _, _, _, _, _, _⟩ := actualNamedBarrier hp hX hGet
  by_cases hEntry : site = 173
  · exact .inl hEntry
  have hLate : 173 < site := by
    simp only [namedBarrierSites, List.mem_cons, List.not_mem_nil, or_false] at hSites
    omega
  have hNotHint : site ∉ registerHintSites := by
    have audit : namedBarrierSites.all (fun s => !(registerHintSites.contains s)) = true := by
      decide +kernel
    simpa using List.all_eq_true.mp audit site hSites
  have hRole := roleBodyPcOfEvent hp hX hGet hLate hNotHint
  have hRegion : 3103 ≤ site ∧ site ≤ 7742 := by
    change roleBodyPc (warpIndex l g) site at hRole
    change warpIndex l g < 8 at hw
    unfold roleBodyPc at hRole
    rcases hRole with hEq | hRole
    · have noExitSite : 9205 ∉ namedBarrierSites := by decide
      exact (noExitSite (hEq ▸ hSites)).elim
    · split_ifs at hRole <;> omega
  have audit : namedBarrierSites.all (fun s => decide (3103 ≤ s ∧ s ≤ 7742 →
      s = 3103 ∨ s = 7741 ∨ s = 3583 ∨ s = 5271 ∨
        s ∈ TmlFa4Fwd.Softmax.softmaxStatsSites)) = true := by decide +kernel
  exact .inr ((of_decide_eq_true (List.all_eq_true.mp audit site hSites)) hRegion)

theorem BarrierArrival.softmaxRendezvous {i : EvId} {id : Nat} {count : Option Nat} {mode : BarMode}
    (he : BarrierArrival X i id count mode) (hw : warpIndex l i.1 < 8) (hNamed : id ≠ 0) :
    ∃ kind : SoftmaxRendezvous, id = kind.id l i.1 ∧ count = kind.count ∧ mode = kind.mode ∧
      kind.validOrdinal (barrierOrdinal X i) := by
  obtain ⟨g, j⟩ := i
  obtain ⟨⟨site, _⟩, hGet, rfl⟩ := he
  obtain ⟨_, hCount, hMode, _, _, hZero, hTwo⟩ := actualNamedBarrier hp hX hGet
  have hNo : site ≠ 173 := fun h => hNamed (hZero h)
  have hKind := (softmaxBarrierStation hp hX hw hGet).resolve_left hNo
  have hPast (hs : site ∉ Mma.allocationEntrySites) : 1 < barrierOrdinal X (g,j) :=
    afterInitialAllocationOrdinal hp hX hGet hNo hs
  rcases hKind with rfl | rfl | rfl | rfl | hStat
  · have hb : X.IsBarrier (g,j) 2 (some 416) 3103 := by
      rw [show id = 2 from hTwo hCount, show count = some 416 from hCount,
        show mode = .sync from hMode] at hGet
      exact hGet
    exact ⟨.initialAllocation, hTwo hCount, hCount, hMode,
      initialAllocationOrdinal hp hX hb (by decide)⟩
  · exact ⟨.finalAllocation, hTwo hCount, hCount, hMode, hPast (by decide)⟩
  · exact ⟨.bias, (TmlFa4Fwd.Softmax.actualBiasBarrierStage hp hX false hGet).2, hCount, hMode,
      hPast (by decide)⟩
  · exact ⟨.bias, (TmlFa4Fwd.Softmax.actualBiasBarrierStage hp hX true hGet).2, hCount, hMode,
      hPast (by decide)⟩
  · have hNonEntry : site ∉ Mma.allocationEntrySites := by
      have tab : TmlFa4Fwd.Softmax.softmaxStatsSites.all
          (fun s => !Mma.allocationEntrySites.contains s) = true := by decide +kernel
      simpa using List.all_eq_true.mp tab site hStat
    refine ⟨.statistics, TmlFa4Fwd.Softmax.actualSoftmaxStatsBarrierId hp hX hStat hGet,
      ?_, ?_, hPast hNonEntry⟩
    · have audit : TmlFa4Fwd.Softmax.softmaxStatsSites.all
          (fun s => namedBarrierCount s == some 64) = true := by decide +kernel
      exact hCount.trans (eq_of_beq (List.all_eq_true.mp audit site hStat))
    · have audit : TmlFa4Fwd.Softmax.softmaxStatsSites.all
          (fun s => decide (namedBarrierMode s = .arrive)) = true := by decide +kernel
      exact hMode.trans (of_decide_eq_true (List.all_eq_true.mp audit site hStat))

/-- Distinct work rendezvous at the same lane-local ordinal disagree on an aligned
barrier instruction. -/
theorem SoftmaxRendezvous.alignedMismatch {i j : EvId} {kind kind' : SoftmaxRendezvous}
    (hWarp : SameWarp l i.1 j.1) (hSoft : warpIndex l i.1 < 8) (hi : kind.Observed l X i)
    (hj : kind'.Observed l X j) (hOrdinal : barrierOrdinal X i = barrierOrdinal X j)
    (hNe : kind ≠ kind') (hWork : kind ≠ .initialAllocation) (hWork' : kind' ≠ .initialAllocation) :
    AlignedWorkBarrierMismatch l X 8 := by
  have hNamed : kind.id l i.1 ≠ 0 := by
    cases kind <;> simp [SoftmaxRendezvous.id]
  obtain ⟨actual, _, hCount, hMode, hOrdinalActual⟩ :=
    BarrierArrival.softmaxRendezvous hp hX hi hSoft hNamed
  have hActual : kind = actual := by
    cases kind <;> cases actual <;>
      simp_all [SoftmaxRendezvous.count, SoftmaxRendezvous.mode]
  subst actual
  have hPast : 1 < barrierOrdinal X i := by
    cases kind <;> simp_all [SoftmaxRendezvous.validOrdinal]
  have hCounts : kind.count ≠ kind'.count := by
    cases kind <;> cases kind' <;> simp_all [SoftmaxRendezvous.count]
  obtain ⟨⟨site, _⟩, he, rfl⟩ := hi
  obtain ⟨⟨site', _⟩, hf, rfl⟩ := hj
  obtain ⟨hs, hc, _⟩ := actualNamedBarrier hp hX he
  obtain ⟨_, hc', _⟩ := actualNamedBarrier hp hX hf
  have hSites : site ≠ site' := fun h =>
    hCounts (hc.trans ((congrArg namedBarrierCount h).trans hc'.symm))
  have audit : namedBarrierSites.all kernel.alignedAt = true := by decide +kernel
  have hAligned := List.all_eq_true.mp audit site hs
  exact .ofObservations hWarp hSoft he hf hPast hOrdinal (by simp [hAligned]) hSites

end PTX.Kernels.TmlFa4Fwd.Thread
