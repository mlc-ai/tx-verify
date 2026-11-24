-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.RingCommit
public import Kernels.InklingRelDecode.Proof.Protocol.SOSched

@[expose] public section

/-!
# The MMA warp's counts of the S/P/O handshake, along its run

The MMA warp (`Mma.D`, an abstract state of `WComp.code`) takes part in four barriers of the
handshake, once per iteration `i` of its loop (`d.i`; the QK half of iteration `i < n` is block
`i`, the PV half of iteration `i ≥ 1` is block `i - 1`):

* **QK commit to `s_ready (i % 2)`** (`MmShape.qkCommit`), by the elected lane: `Mm.qkDone d`
  counts the QK commits issued at state `d`;
* **poll of `p_ready ((i - 1) % 2)`** (`MmShape.pWait`), by every lane: `Mm.pPolled d` counts the PV
  halves whose poll has succeeded;
* **second PV commit to `o_done`** (`MmShape.pvCommit2`), by the elected lane: `Mm.oDoneC d`;
* **the commit to `o_final`** after the loop (`MmShape.finCommit`), by the elected lane:
  `Mm.finDone d`.

For each the file proves the one-step lemma of the measure (`mm_next_*`: a step of a state that
satisfies `Mma.Inv` changes the measure by one exactly at the site), the classification of the
fired event (`mm_*_count`: it is a poll of / commit to buffer `b` exactly at that site and buffer),
and the count along a run (`mma_*s`): the events of buffer `b` of a run number
`below2 b (measure d) - below2 b (measure d₀)`. The elected-lane statements take the elections of
the run to return the thread's own lane (`LeadRun`), as `RingCommit` does.

The counts are about one run of the machine; that the thread's trace is such a run is the
role-table protocol (obligation 6, `Ring.lean`), the same premises `hin`/`hfresh`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.SO
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Ring (okW LeadRun count_trace)
open PTX.Kernels.InklingRelDecode.Proof.EvW (MmShape mma_shape sReady pReady oDone oFinal)

noncomputable section
set_option maxRecDepth 100000

/-- The PV halves whose `p_ready` poll has succeeded at state `d` (the PV half of iteration
`i ≥ 1` polls once, for block `i - 1`). -/
def Mm.pPolled (d : Mma.D) : Nat :=
  match d.site with
  | .setMaxReg | .ldNum | .bar0 => 0
  | .qkBar | .kvWait | .qkShfl | .qkBar2 | .qkElect | .qk _ | .qkCommit | .qkSkip => d.i - 1
  | .pvBar | .pWait => d.i - 1
  | .pvShfl | .pvBar2 | .pvElect | .pv _ | .pvCommit1 | .pvCommit2 | .pvSkip => d.i
  | .finBar | .finElect | .finCommit | .bar1 | .setMaxRegInc => if d.i = 0 then 0 else d.n

/-- The QK commits to `s_ready` issued at state `d`, when every election returns the thread's
lane: one per completed QK half. -/
def Mm.qkDone (d : Mma.D) : Nat :=
  match d.site with
  | .setMaxReg | .ldNum | .bar0 => 0
  | .qkBar | .kvWait | .qkShfl | .qkBar2 | .qkElect | .qk _ | .qkCommit => d.i
  | .pvBar | .pWait | .pvShfl | .pvBar2 | .pvElect | .pv _ | .pvCommit1 | .pvCommit2
  | .qkSkip | .pvSkip => min (d.i + 1) d.n
  | .finBar | .finElect | .finCommit | .bar1 | .setMaxRegInc => if d.i = 0 then 0 else d.n

/-- The second PV commits, to `o_done`, issued at state `d`, when every election returns the
thread's lane: one per completed PV half. -/
def Mm.oDoneC (d : Mma.D) : Nat :=
  match d.site with
  | .setMaxReg | .ldNum | .bar0 => 0
  | .qkBar | .kvWait | .qkShfl | .qkBar2 | .qkElect | .qk _ | .qkCommit | .qkSkip => d.i - 1
  | .pvBar | .pWait | .pvShfl | .pvBar2 | .pvElect | .pv _ | .pvCommit1 | .pvCommit2 => d.i - 1
  | .pvSkip => d.i
  | .finBar | .finElect | .finCommit | .bar1 | .setMaxRegInc => if d.i = 0 then 0 else d.n

/-- The commits to `o_final` issued at state `d`, when every election returns the thread's
lane. -/
def Mm.finDone (d : Mma.D) : Nat :=
  match d.site with
  | .bar1 | .setMaxRegInc => 1
  | _ => 0

/-- **A step of the MMA warp, for the `p_ready` polls.** -/
theorem mm_next_pPolled {L : Launch} {g : Nat} {d d' : Mma.D} {e : Event} (hi : Mma.Inv d)
    (hne : d.site ≠ .setMaxRegInc) (h : Mma.next L g d e = some (some d')) :
    Mm.pPolled d' = Mm.pPolled d + if d.site = .pWait ∧ okW e = true then 1 else 0 := by
  have hq := hi.qk
  have hp := hi.pv
  have hpre := hi.pre
  obtain ⟨site, i, n, tm, pro⟩ := d
  simp only [Mma.QkSite, Mma.PvSite, Mma.PreSite] at hq hp hpre
  simp only at hne
  cases site
  case setMaxRegInc => exact absurd rfl hne
  all_goals
    simp only [Mma.next] at h
    (repeat' split at h)
    all_goals try (obtain rfl := Option.some.inj (Option.some.inj h))
    all_goals try (cases h)
    all_goals try simp only [Mma.start, Mma.afterQk, Mma.iterNext, Mma.qkNext, Mma.pvNext]
    all_goals (repeat' split)
    all_goals simp_all [Mm.pPolled, okW]

variable {L : Launch} {g : Nat} {d d' : Mma.D} {e : Event} (hi : Mma.Inv d)
    (hne : d.site ≠ .setMaxRegInc)
    (hE : ∀ mask inst ld, e.kind = .elect mask inst ld → ld = laneOf L g)
include hi hne hE

/-- **A step of the MMA warp, for `qkDone`.** -/
theorem mm_next_qkDone (hB : Mma.BcastOk e) (h : Mma.next L g d e = some (some d')) :
    Mm.qkDone d' = Mm.qkDone d + if d.site = .qkCommit then 1 else 0 := by
  have hq := hi.qk
  have hp := hi.pv
  have hpre := hi.pre
  have hk := fun hs => Mma.next_not_skip hB hs h
  clear hB
  obtain ⟨site, i, n, tm, pro⟩ := d
  simp only [Mma.QkSite, Mma.PvSite, Mma.PreSite] at hq hp hpre
  simp only at hne
  cases site
  case setMaxRegInc => exact absurd rfl hne
  all_goals
    simp only [Mma.next] at h
    (repeat' split at h)
    all_goals try (obtain rfl := Option.some.inj (Option.some.inj h))
    all_goals try (cases h)
    all_goals try simp only [Mma.start, Mma.afterQk, Mma.iterNext, Mma.qkNext, Mma.pvNext]
    all_goals (repeat' split)
    all_goals simp_all [Mm.qkDone, Mma.Site.isSkip]
    all_goals omega

/-- **A step of the MMA warp, for `oDoneC`.** -/
theorem mm_next_oDoneC (hB : Mma.BcastOk e) (h : Mma.next L g d e = some (some d')) :
    Mm.oDoneC d' = Mm.oDoneC d + if d.site = .pvCommit2 then 1 else 0 := by
  have hq := hi.qk
  have hp := hi.pv
  have hpre := hi.pre
  have hk := fun hs => Mma.next_not_skip hB hs h
  clear hB
  obtain ⟨site, i, n, tm, pro⟩ := d
  simp only [Mma.QkSite, Mma.PvSite, Mma.PreSite] at hq hp hpre
  simp only at hne
  cases site
  case setMaxRegInc => exact absurd rfl hne
  all_goals
    simp only [Mma.next] at h
    (repeat' split at h)
    all_goals try (obtain rfl := Option.some.inj (Option.some.inj h))
    all_goals try (cases h)
    all_goals try simp only [Mma.start, Mma.afterQk, Mma.iterNext, Mma.qkNext, Mma.pvNext]
    all_goals (repeat' split)
    all_goals simp_all [Mm.oDoneC, Mma.Site.isSkip]

/-- **A step of the MMA warp, for `finDone`.** -/
theorem mm_next_finDone (h : Mma.next L g d e = some (some d')) :
    Mm.finDone d' = Mm.finDone d + if d.site = .finCommit then 1 else 0 := by
  have hq := hi.qk
  have hp := hi.pv
  have hpre := hi.pre
  obtain ⟨site, i, n, tm, pro⟩ := d
  simp only [Mma.QkSite, Mma.PvSite, Mma.PreSite] at hq hp hpre
  simp only at hne
  cases site
  case setMaxRegInc => exact absurd rfl hne
  all_goals
    simp only [Mma.next] at h
    (repeat' split at h)
    all_goals try (obtain rfl := Option.some.inj (Option.some.inj h))
    all_goals try (cases h)
    all_goals try simp only [Mma.start, Mma.afterQk, Mma.iterNext, Mma.qkNext, Mma.pvNext]
    all_goals (repeat' split)
    all_goals simp_all [Mm.finDone]

end
end PTX.Kernels.InklingRelDecode.Proof.SO
