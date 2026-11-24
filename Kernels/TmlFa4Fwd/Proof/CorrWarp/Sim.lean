-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The correction warps' scheduler steps as the output warp's

The correction warps record their scheduler's scan in an output-warp state (`V.sc`). At every
scheduler site (`Site.sched`) their step is the output warp's step of that state (`succ_scan`),
read back as a correction state (`ofE`), once the CTA index the role reads (`ctaR`) is the
launch's (`ctaR_eq`). The last arrival before the scan is the output warp's first state; the end
of a pass without a tile is the output warp's return and the correction warps' final poll.

`toE d` is the output-warp state of correction state `d`; its site is `epi d.site`: the start
before the scan, the return at the end, and the first stage poll from the request's used-K read
on (the scan state no longer changes there). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (laneW paramW batchOf headsW reqOf loopOf tlOf)

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-- The output warp's site of each correction site. -/
def epi : Site → Epilogue.Site
  | .setmax | .bar1 | .arr _ => .start
  | .word k => .word k
  | .down k => .down k
  | .up k j => .up k j
  | .total k => .total k
  | .vote l => .vote l
  | .pre l => .pre l
  | .tiles l => .tiles l
  | .q0 => .q0
  | .q1 => .q1
  | .wend l | .barEnd l | .exit l => .exit l
  | _ => .ready 0

/-- The correction site of an output-warp site that a scheduler step reaches. -/
def ofS : Epilogue.Site → Site
  | .word k => .word k
  | .down k => .down k
  | .up k j => .up k j
  | .total k => .total k
  | .vote l => .vote l
  | .pre l => .pre l
  | .tiles l => .tiles l
  | .q0 => .q0
  | .q1 => .q1
  | .exit l => .wend l
  | _ => .uk

/-- The output-warp state of a correction state. -/
abbrev toE (d : D) : Epilogue.D := { d.v.sc with site := epi d.site }

/-- The correction state over `d` with the output-warp state `c` (the scan state's own site is
kept; it is not read). -/
abbrev ofE (d : D) (c : Epilogue.D) : D :=
  D.mk' (ofS c.site) { d.v with sc := { c with site := d.v.sc.site } }

/-- The scheduler sites at which the two warps step alike. -/
def _root_.PTX.Kernels.TmlFa4Fwd.Proof.Correction.Site.sched : Site → Bool
  | .arr k => k.val = 1
  | .word _ | .down _ | .up _ _ | .total _ | .vote _ | .pre _ | .tiles _ | .q0 | .q1 => true
  | _ => false

variable {p : Params} {L : Launch} {g : Nat}

theorem scanExit_eq (late : Bool) (d : D) (gx cur : BitVec 64) :
    scanExit p late d gx cur = ofE d (Epilogue.scanExit p late (toE d) gx cur) := by
  unfold scanExit Epilogue.scanExit
  split <;> rfl

theorem loopHead_eq (hc : ctaR p L g = Epilogue.ctaW L g) (late : Bool) (d : D)
    (grp acc : BitVec 64) :
    loopHead p L g late d grp acc = ofE d (Epilogue.loopHead p L g late (toE d) grp acc) := by
  unfold loopHead Epilogue.loopHead
  simp only [hc, D.ite]
  split
  · exact scanExit_eq late d _ _
  · split <;> rfl

theorem afterTotal_eq (hc : ctaR p L g = Epilogue.ctaW L g) (k : Epilogue.Scan) (d : D)
    (x : BitVec 64) :
    afterTotal p L g k d x = ofE d (Epilogue.afterTotal p L g k (toE d) x) := by
  unfold afterTotal Epilogue.afterTotal
  cases k <;> simp only [hc, D.ite] <;> split <;>
    first
    | exact scanExit_eq _ _ _ _
    | exact loopHead_eq hc _ _ _ _

theorem word32_eq (d : D) (w : Value) {f : BitVec 64 → D} {f' : BitVec 64 → Epilogue.D}
    (h : ∀ x, f x = ofE d (f' x)) :
    word32 w f = (Epilogue.word32 w f').map (Option.map (ofE d)) := by
  unfold word32 Epilogue.word32
  split <;> simp_all

theorem coords_eq (hc : ctaR p L g = Epilogue.ctaW L g) (c : Epilogue.D) :
    coords p L g c = Epilogue.coords p L g c := by
  unfold coords Epilogue.coords
  rw [hc]

/-- **At a scheduler site the correction warps step as the output warp** on their scan state. -/
theorem succ_scan (hc : ctaR p L g = Epilogue.ctaW L g) {d : D} {e : Event}
    (hs : d.site.sched = true) :
    succ p L g d e = (Epilogue.succ p L g (toE d) e).map (Option.map (ofE d)) := by
  obtain ⟨s, v, k⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [Site.sched, Bool.false_eq_true, decide_eq_true_eq] at hs
  case arr j =>
    have : j = 1 := Fin.ext hs
    subst this
    simp only [succ, Epilogue.succ, epi, passStart, D.ite, Bool.false_eq_true, ↓reduceIte,
      Option.map_some, Option.map]
    split <;> rfl
  all_goals cases kind <;> simp only [succ, Epilogue.succ, epi, Option.map_none]
  case word.rd a bs =>
    cases rebuild 3 bs with
    | error _ => rfl
    | ok w => exact word32_eq _ w fun _ => rfl
  case down.shfl w _ => exact word32_eq _ w fun _ => rfl
  case up.shfl k j _ _ _ _ w _ => exact word32_eq _ w fun x => by fin_cases j <;> rfl
  case total.shfl w _ => exact word32_eq _ w fun x => afterTotal_eq hc _ _ x
  case vote.vote b => simp only [Option.map_some, D.ite]; split <;> rfl
  case pre.shfl l _ _ _ _ w _ => exact word32_eq _ w fun x => by cases l <;> rfl
  case tiles.shfl l _ _ _ _ w _ =>
    cases w <;> try rfl
    rename_i n x
    by_cases h32 : n = 32
    · subst h32
      cases l
      · simp only [Bool.false_eq_true, ↓reduceIte, afterTiles, Epilogue.afterTiles,
          coords_eq hc, scAt, D.ite]
        repeat' split
        all_goals first | rfl | (simp only [Epilogue.coords] at *; simp_all; done)
      · rfl
    · simp [h32]
  case q0.rd a bs =>
    cases rebuild 3 bs with
    | error _ => rfl
    | ok w => exact word32_eq _ w fun _ => rfl
  case q1.rd a bs =>
    cases rebuild 3 bs with
    | error _ => rfl
    | ok w => exact word32_eq _ w fun _ => rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
