-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SOSmEvents
public import Kernels.InklingRelDecode.Proof.Protocol.SOSmRun

@[expose] public section

/-!
# The softmax region's polls of `o_done`, counted along a run

The fixed kernel polls `o_done` in **every** iteration `i ≥ 1`, at the site `waitO` (after the row
sum's shuffle, before the lazy-rescale test): `Sm.next` leaves `shfl6` for `bar20` where `i = 0`
and for `waitO` where `i > 0`. So the polls of a thread alternate like any ring's: its successful
polls of `o_done` are one per iteration from the second, and the poll of iteration `i` is the
thread's `(i - 1)`-th (counting from 0).

* `smOPolled d`: the successful `o_done` polls at state `d`: `i - 1` from the start of the
  iteration up to and at the site `waitO`, `i` from the site after it on.
* `OdoneOk d`: at the site `waitO` the iteration is positive. It holds of every state a step
  leads to and of every state a step starts from that satisfies it (`sm_next_odoneOk`), so of
  every state of a run from a state that satisfies it.
* `sm_oPolls`: along a run from a state with `OdoneOk`, the successful `o_done` polls number
  `smOPolled d - smOPolled d₀`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.SO
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Ring (okW)
open PTX.Kernels.InklingRelDecode.Proof.EvW (oDone)

noncomputable section
set_option maxRecDepth 100000

/-- The successful `o_done` polls at state `d`. -/
def smOPolled (d : Sm.D) : Nat :=
  match d.site with
  | .setMaxReg | .bar0 | .pre _ | .nxt _ | .waitS | .shfl4 | .ldS | .waitLd | .shfl5 | .shfl6
  | .waitO => d.i - 1
  | _ => d.i

/-- At the site `waitO` the iteration is positive (the first iteration skips the poll). -/
def OdoneOk (d : Sm.D) : Prop := d.site = .waitO → 1 ≤ d.i

/-- A step keeps `OdoneOk`, and raises `smOPolled` exactly at a successful poll at `waitO`. -/
theorem sm_next_odone {L : Launch} {g : Nat} {d d' : Sm.D} {e : Event} (hd : OdoneOk d)
    (h : Sm.next L g d e = some (some d')) :
    OdoneOk d' ∧
      smOPolled d' = smOPolled d + if d.site = .waitO ∧ okW e = true then 1 else 0 := by
  obtain ⟨site, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases site
  all_goals
    simp only [Sm.next, Sm.afterArrive, Sm.afterSetup, Sm.toBar20] at h
    (repeat' split at h)
    all_goals try (obtain rfl := Option.some.inj (Option.some.inj h))
    all_goals try (cases h)
    all_goals simp_all [smOPolled, okW, Sm.D.upd, Sm.D.afterSum, OdoneOk]
    all_goals omega

variable {L : Launch} {g : Nat} {d0 : Sm.D}

end
end PTX.Kernels.InklingRelDecode.Proof.SO
