-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Machine
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The softmax warps' scheduler steps as the output warp's

The softmax warps record their scheduler's scan in an output-warp state (`V.sc`), as the
correction warps do (`CorrWarp/Sim.lean`). At every scheduler site (`Site.sched`) their step is
the output warp's step of that state (`succ_scan`), read back as a softmax state (`ofE`), once the
second pass's CTA index (`ctaR`) is the launch's (`ctaR_eq`). The barrier before the scan is the
output warp's first state; the end of a pass is the output warp's return and the softmax warps'
final poll (where a lane without a tile also sets its P parity to 1, `ofE`).

`toE d` is the output-warp state of softmax state `d`; its site is `epi d.site`: the start before
the scan, the return at the end, and the first stage poll from the used-K read on. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (laneW paramW batchOf headsW reqOf loopOf tlOf)

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-- The output warp's site of each softmax site. -/
def epi : Site → Epilogue.Site
  | .setmax | .bar1 => .start
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

/-- The softmax site of an output-warp site that a scheduler step reaches. -/
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

/-- The output-warp state of a softmax state. -/
abbrev toE (d : D) : Epilogue.D := { d.v.sc with site := epi d.site }

/-- The softmax state over `d` with the output-warp state `c` (the scan state's own site is kept;
at the first pass's end the P parity is 1). -/
abbrev ofE (d : D) (c : Epilogue.D) : D :=
  let sc : Epilogue.D := { c with site := d.v.sc.site }
  let pp : BitVec 64 := if c.site = .exit false then i32 1 else d.v.ppar
  D.mk' (ofS c.site) { d.v with sc := sc, ppar := pp }

/-- The scheduler sites at which the two warps step alike. -/
def _root_.PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Site.sched : Site → Bool
  | .bar1 | .word _ | .down _ | .up _ _ | .total _ | .vote _ | .pre _ | .tiles _ | .q0 | .q1 =>
    true
  | _ => false

variable {p : Params} {L : Launch} {g : Nat}

theorem scanExit_eq (late : Bool) (d : D) (gx cur : BitVec 64) :
    scanExit p late d gx cur = ofE d (Epilogue.scanExit p late (toE d) gx cur) := by
  unfold scanExit Epilogue.scanExit D.ite
  cases late <;> split <;> simp [ofS]

theorem loopHead_eq (hc : ctaR p L g = Epilogue.ctaW L g) (late : Bool) (d : D)
    (grp acc : BitVec 64) :
    loopHead p L g late d grp acc = ofE d (Epilogue.loopHead p L g late (toE d) grp acc) := by
  unfold loopHead Epilogue.loopHead
  cases late <;> simp only [ctaOf, hc, D.ite, Bool.false_eq_true, ↓reduceIte] <;> split <;>
    first | exact scanExit_eq _ d _ _ | (split <;> rfl)

theorem afterTotal_eq (hc : ctaR p L g = Epilogue.ctaW L g) (k : Epilogue.Scan) (d : D)
    (x : BitVec 64) :
    afterTotal p L g k d x = ofE d (Epilogue.afterTotal p L g k (toE d) x) := by
  unfold afterTotal Epilogue.afterTotal
  cases k <;> simp only [ctaOf, hc, D.ite, Epilogue.Scan.late, Bool.false_eq_true,
    ↓reduceIte] <;> split <;>
    first
    | exact scanExit_eq _ _ _ _
    | exact loopHead_eq hc _ _ _ _

theorem word32_eq (d : D) (w : Value) {f : BitVec 64 → D} {f' : BitVec 64 → Epilogue.D}
    (h : ∀ x, f x = ofE d (f' x)) :
    word32 w f = (Epilogue.word32 w f').map (Option.map (ofE d)) := by
  unfold word32 Epilogue.word32
  split <;> simp_all

/-- **At a scheduler site the softmax warps step as the output warp** on their scan state. -/
theorem succ_scan (hc : ctaR p L g = Epilogue.ctaW L g) {d : D} {e : Event}
    (hs : d.site.sched = true) :
    succ p L g d e = (Epilogue.succ p L g (toE d) e).map (Option.map (ofE d)) := by
  obtain ⟨s, v, k, acc⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [Site.sched, Bool.false_eq_true] at hs
  case bar1 =>
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
      · simp only [Bool.false_eq_true, ↓reduceIte, afterTiles, Epilogue.afterTiles, scAt, D.ite]
        have e1 : ∀ c : Epilogue.D, (Mma.coords p L g c).n1 = (Epilogue.coords p L g c).n1 :=
          fun _ => rfl
        have e2 : ∀ c : Epilogue.D, (Mma.coords p L g c).d1 = (Epilogue.coords p L g c).d1 :=
          fun _ => rfl
        have e3 : ∀ c : Epilogue.D, (Mma.coords p L g c).n2 = (Epilogue.coords p L g c).n2 :=
          fun _ => rfl
        have e4 : ∀ c : Epilogue.D, (Mma.coords p L g c).d2 = (Epilogue.coords p L g c).d2 :=
          fun _ => rfl
        simp only [e1, e2, e3, e4]
        repeat' split
        all_goals first | rfl | (simp_all [ofS]; done) |
          (simp only [Epilogue.coords, Epilogue.chosen] at *; simp_all [ofS]; done)
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
end PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
