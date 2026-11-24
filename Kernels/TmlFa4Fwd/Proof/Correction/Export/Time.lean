-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Time
public import Kernels.TmlFa4Fwd.Proof.Correction.Machine

@[expose] public section

/-! # The times of the correction warps' states -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Progress
open PTX PTX.Proof PTX.Flow

noncomputable section

/-! ### The correction warps -/

namespace Cr

/-- The scheduler's sites of a correction lane as the output warp's sites (their collectives are
the same events), any other site as a site with no collective. -/
def toE : Correction.Site → Epilogue.Site
  | .word k => .word k
  | .down k => .down k
  | .up k j => .up k j
  | .total k => .total k
  | .vote l => .vote l
  | .pre l => .pre l
  | .tiles l => .tiles l
  | _ => .q0

/-- The second pass's sites and the end after it. -/
def late : Correction.Site → Bool
  | .word k | .down k | .up k _ | .total k => k.late
  | .vote l | .pre l | .tiles l | .wend l | .barEnd l | .exit l => l
  | _ => false

/-- The rescale rounds' sites, with the two syncs and the credit arrival before them. -/
def round : Correction.Site → Bool
  | .nb _ | .free | .rbar _ | .rscale _ | .rvote _ | .rld _ _ | .rldw _ _ | .rst _ _ | .rwait _
  | .rarr _ _ => true
  | _ => false

/-- The final stage's sites, with their offset in their band. -/
def tailOff : Correction.Site → Option Nat
  | .farr0 => some 100
  | .fbar _ => some 102
  | .fsum _ => some 104
  | .fmax _ => some 106
  | .farr _ => some 108
  | .fw _ k => some (110 + 2 * k.val)
  | .fld _ j => some (114 + 8 * j.val)
  | .fwl _ j => some (116 + 8 * j.val)
  | .fst _ j h => some (118 + 8 * j.val + h.val)
  | .fence _ => some 242
  | .fdone _ k => some (244 + 2 * k.val)
  | .lse h => some (250 + 2 * h.val)
  | _ => none

/-- A rescale-round site's offset in its band: the sync, the scale, the ballot, per chunk the
load, its wait and the store, the store wait, the P-full and credit arrivals; the start's credit
arrival after its first sync. -/
def roundOff : Correction.Site → Nat
  | .rscale _ => 2
  | .rvote _ => 4
  | .rld _ c => 6 + 6 * c.val
  | .rldw _ c => 8 + 6 * c.val
  | .rst _ c => 10 + 6 * c.val
  | .rwait _ => 56
  | .rarr _ k => 58 + 2 * k.val
  | .free => 62
  | _ => 0

/-- The stage part of a round or final site, and whether the site is past the part's sync (its
slot is then one less than the syncs so far): a sync (`nb`, `rbar`, `fbar`) and `farr0` are
before it. -/
def part : Correction.Site → Option (Fin 2 × Bool)
  | .nb st | .rbar st | .fbar st => some (st, false)
  | .farr0 => some (0, false)
  | .free => some (0, true)
  | .rscale st | .rvote st | .rld st _ | .rldw st _ | .rst st _ | .rwait st | .rarr st _ =>
    some (st, true)
  | .fsum st | .fmax st | .farr st | .fw st _ | .fld st _ | .fwl st _ | .fst st _ _ | .fence st
  | .fdone st _ => some (st, true)
  | .lse _ => some (1, true)
  | _ => none

/-- The slot of a correction state of stage part `st`: its syncs on the stage's named barrier
with the softmax warp, less one past the part's sync. -/
def slot (p : Params) (st : Fin 2) (past : Bool) (n : Cls → Nat) : Nat :=
  slotOf p (n (.corr (.nb st)) - if past then 1 else 0)

/-- The end: the poll for the output warp's copies, barrier 2, the return. -/
def endOff : Correction.Site → Option (Bool × Nat)
  | .wend l => some (l, 2)
  | .barEnd l => some (l, 4)
  | .exit l => some (l, 6)
  | _ => none

/-- **The time of a correction state** with ghost counts `n`: a rescale round's or the final
stage's site in its stage's band of the slot of its generation; the entry, the first barrier; the
scheduler's passes by the shuffles so far (and the pass's ballot), the end after them. -/
def time (p : Params) (d : Correction.D) (n : Cls → Nat) : Nat :=
  match part d.site with
  | some (st, past) =>
    clk p (slot p st past n) (bandC st.val + (tailOff d.site).getD (roundOff d.site))
  | none =>
    match endOff d.site with
    | some (l, o) => endT p l o
    | none =>
      if d.site = .setmax then scanBase else if d.site = .bar1 then scanBase + 3
      else passTime (if late d.site then endBase p else scanBase)
        (n .shfl + Out.ballots (toE d.site)) (Out.coll (toE d.site))

/-- A round or final site's offset is inside the slot. -/
theorem off_lt (st : Fin 2) (s : Correction.Site) :
    bandC st.val + (tailOff s).getD (roundOff s) < span := by
  have := st.isLt
  cases s <;> simp only [tailOff, roundOff, Option.getD_some, Option.getD_none, span, bandC] <;>
    omega

/-- A site has a stage part exactly when it is a rescale-round or a final-stage site. -/
theorem part_none (s : Correction.Site) :
    part s = none ↔ round s = false ∧ tailOff s = none := by
  cases s <;> simp [part, round, tailOff]

end Cr

end
end PTX.Kernels.TmlFa4Fwd.Proof.Progress
