-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.BarrierOrdinals
public import Kernels.TmlFa4Fwd.Proof.Thread.AllocationBarrierOrder
import Kernels.TmlFa4Fwd.Proof.AllocationBarrierControl
import Kernels.TmlFa4Fwd.Proof.PrologueStartupUnique
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow Prologue Mma

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem sameAllocationEntrySite {g i j site site' : Nat}
    (he : X.IsBarrier (g,i) 2 (some 416) site) (hf : X.IsBarrier (g,j) 2 (some 416) site')
    (hs : site ∈ allocationEntrySites) (hs' : site' ∈ allocationEntrySites) : site = site' := by
  have hRole := Mma.allocationEntryRole hp hX hs he
  have hRole' := Mma.allocationEntryRole hp hX hs' hf
  omega

private theorem noNamedBeforeEntry {g i j site site' id : Nat} {count : Option Nat} {mode : BarMode}
    (hEntry : X.IsBarrier (g,j) 2 (some 416) site) (hs : site ∈ allocationEntrySites) (hi : i < j)
    (he : X.get (g,i) = some ⟨site', .bar id count mode⟩) :
    site' = 173 := by
  by_contra hNoncommon
  by_cases hEntry' : site' ∈ allocationEntrySites
  · have hTwo := (actualNamedBarrier hp hX he).2.2.2.2.2.2
    have hCount := (actualNamedBarrier hp hX he).2.1
    have hSize : namedBarrierCount site' = some 416 := by
      simp only [allocationEntrySites, List.mem_cons, List.not_mem_nil, or_false] at hEntry'
      rcases hEntry' with rfl | rfl | rfl <;> rfl
    obtain rfl := hTwo (hCount.trans hSize)
    have hE := Mma.actualAllocationEntry hp hX hEntry' he
    have hSame := sameAllocationEntrySite hp hX hE hEntry hEntry' hs
    have hPast := afterAllocationArrival hp hX hE hi hEntry
    change site' < site at hPast
    omega
  · obtain ⟨k, hk, s, hs', hK⟩ :=
      Mma.allocationEntryBeforeNamedBarrier hp hX he hNoncommon hEntry'
    have hSame := sameAllocationEntrySite hp hX hK hEntry hs' hs
    have hPast := afterAllocationArrival hp hX hK (hk.trans hi) hEntry
    change s < site at hPast
    omega

/-- The initial allocation rendezvous of each participating role is the second CTA
barrier event in that lane. -/
theorem initialAllocationOrdinal {g j site : Nat} (he : X.IsBarrier (g,j) 2 (some 416) site)
    (hs : site ∈ allocationEntrySites) :
    barrierOrdinal X (g,j) = 1 := by
  have hSite : 173 < site := by
    simp only [allocationEntrySites, List.mem_cons, List.not_mem_nil, or_false] at hs
    omega
  obtain ⟨n, hn, hCommon⟩ := commonBeforeRoleEvent hp hX he hSite
  have hc : X.get (g,n) = some ⟨173, .bar 0 none .sync⟩ := hCommon
  have hZero := (BarrierArrival.ordinalZeroIff hp hX
    (show BarrierArrival X (g,n) 0 none .sync from ⟨_, hc, rfl⟩)).mpr rfl
  have hFirst := countP_take_succ (p := Execution.isBar) hc rfl
  change barrierOrdinal X (g,n) = 0 at hZero
  change ((X.tr g).take n).countP Execution.isBar = 0 at hZero
  rw [hZero, Nat.zero_add] at hFirst
  let events := (X.tr g).take j
  let rest := events.drop (n + 1)
  have hSplit : ((X.tr g).take (n + 1)) ++ rest = events := by
    have hTake : events.take (n + 1) = (X.tr g).take (n + 1) := by
      dsimp only [events]
      rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [← hTake, List.take_append_drop]
  have hTail : rest.countP Execution.isBar = 0 := by
    apply List.countP_eq_zero.mpr
    intro e hm hBar
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
    have hLen := (List.getElem?_eq_some_iff.mp hk).1
    have hBound : n + 1 + k < j := by
      simp only [rest, events, List.length_drop, List.length_take] at hLen
      omega
    dsimp only [rest, events] at hk
    rw [List.getElem?_drop, List.getElem?_take_of_lt hBound] at hk
    obtain ⟨pc, kind⟩ := e
    cases kind <;> try cases hBar
    case bar id count mode =>
      have hGet : X.get (g,n+1+k) = some ⟨pc, .bar id count mode⟩ := hk
      have hs := noNamedBeforeEntry hp hX he hs hBound hGet
      subst pc
      obtain ⟨_, _, hMode, _, hCount, hId, _⟩ := actualNamedBarrier hp hX hGet
      obtain rfl := hId rfl
      obtain rfl := hCount.mpr rfl
      obtain rfl := hMode
      have hn' := commonStartupUnique hX (event_thread_lt hX hc) hc hGet
      omega
  change events.countP Execution.isBar = 1
  rw [← hSplit, List.countP_append, hFirst, hTail]

/-- A role rendezvous after allocation has an ordinal greater than one. -/
theorem afterInitialAllocationOrdinal {g j site id : Nat} {count : Option Nat} {mode : BarMode}
    (he : X.get (g,j) = some ⟨site, .bar id count mode⟩) (hCommon : site ≠ 173)
    (hRole : site ∉ allocationEntrySites) :
    1 < barrierOrdinal X (g,j) := by
  obtain ⟨i, hi, start, hs, hb⟩ :=
    Mma.allocationEntryBeforeNamedBarrier hp hX he hCommon hRole
  have hOrdinal := initialAllocationOrdinal hp hX hb hs
  change ((X.tr g).take i).countP Execution.isBar = 1 at hOrdinal
  have ht := countP_take_succ (p := Execution.isBar)
    (show X.get (g,i) = some ⟨start, .bar 2 (some 416) .sync⟩ from hb) rfl
  have hLe := countP_take_mono Execution.isBar (X.tr g) (show i + 1 ≤ j by omega)
  rw [ht, hOrdinal] at hLe
  exact hLe

end PTX.Kernels.TmlFa4Fwd.Thread
