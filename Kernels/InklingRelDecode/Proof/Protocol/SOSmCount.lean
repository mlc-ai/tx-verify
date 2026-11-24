-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SOSites
public import Kernels.InklingRelDecode.Proof.Protocol.SOMmaRun

@[expose] public section

/-!
# The default partition's counts of the S/P/O handshake, along its run

The softmax region of the default partition (`Sm.D`, abstract state of `Sm.code`; warps 0 to 3, all
128 threads) takes part in the handshake once per iteration `i` of its loop (`d.i`, the block it
processes):

* **poll of `s_ready (i % 2)`** (`Sm.Shape.waitS`), every thread: `smPolled d` counts the polls
  that have succeeded;
* **arrival on `p_ready (i % 2)`** (`Sm.Shape.arrive`), thread 0 of the block only (`Sm.Inv.lead`):
  `smArrived d` counts them (for that thread);
* **poll of `o_done`** (site `waitO`, every iteration `i ≥ 1`, before the rescale test): the poll
  is dense, but its count is not a state function of the machine (a failed poll stays at the
  site); the event shape of the site, which `Sm.Shape` leaves as `True`, is `WaitOShape`
  (`SOSmEvents`).

For the first two the file proves the one-step lemma of the measure (`sm_next_*`), the
classification of the fired event at every site (`sm_okPoll_s`, `sm_arrivesOn_p`: a poll of /
an arrival on buffer `b` exactly at that site and buffer), and the count along a run
(`sm_sPolls`, `sm_pArrivals`). The classification at the sites without an event shape uses the
audit of `SOSites` (no other instruction of the program polls or arrives).

A run is an anchored run of the machine `Sm.code asms L g d₀`; that the thread's trace is such a
run is what the composed default-partition thread has to provide (`SO.SmRunAt` in `SOSmExec`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.SO
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Ring (okW count_trace)

noncomputable section
set_option maxRecDepth 100000

/-- The successful `s_ready` polls at state `d`: the iteration `d.i` has polled from the site after
`waitS` on. -/
def smPolled (d : Sm.D) : Nat :=
  match d.site with
  | .setMaxReg | .bar0 | .pre _ | .nxt _ | .waitS => d.i
  | _ => d.i + 1

/-- A step of the softmax region raises `smPolled` exactly at a successful poll at `waitS`. -/
theorem sm_next_polled {L : Launch} {g : Nat} {d d' : Sm.D} {e : Event}
    (h : Sm.next L g d e = some (some d')) :
    smPolled d' = smPolled d + if d.site = .waitS ∧ okW e = true then 1 else 0 := by
  obtain ⟨site, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases site
  all_goals
    simp only [Sm.next, Sm.afterArrive, Sm.afterSetup, Sm.toBar20] at h
    (repeat' split at h)
    all_goals try (obtain rfl := Option.some.inj (Option.some.inj h))
    all_goals try (cases h)
    all_goals simp_all [smPolled, okW, Sm.D.upd, Sm.D.afterSum, Sm.D.afterMax, Sm.D.afterMaxT]

end
end PTX.Kernels.InklingRelDecode.Proof.SO
