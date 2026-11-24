-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Shape
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader warps' scheduler steps as the output warp's

The loader warps record their scheduler's scan in an output-warp state (`V.sc`). At every
scheduler site but the choice of a tile their step is the output warp's step of that state
(`succ_scan`), read back as a loader state (`ofE`): the arithmetic of the two warps' scans is the
same, on other registers. The end of a pass without a tile is the output warp's return and the
loader's drain (`dw 0`); the loader sets its ring and Q parities there (`drain0`, and the Q parity
0 at the end of the second pass, which it sets before the second pass's ballot too). The choice
of a tile (`tiles false`) differs: the loader records the tile's coordinates in its own field
(`succ_tiles`).

`toE d` is the output-warp state of loader state `d`; its site is `Site.epi`: the start before
the scan, the request's reads, the first stage poll for the sites after the used-K read (the scan
state no longer changes there), and the return at the drain. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (paramW chosen i32)

noncomputable section
set_option linter.unusedTactic false

/-- The scan's sites, whose events are the output warp's. -/
def Site.scan : Site → Bool
  | .word _ | .down _ | .up _ _ | .total _ | .vote _ | .pre _ | .tiles _ => true
  | _ => false

/-- The scheduler sites at which the two warps step alike: the scan's except the choices of a
tile, and the request's two reads. -/
def Site.sched : Site → Bool
  | .word _ | .down _ | .up _ _ | .total _ | .vote _ | .pre _ | .q0 | .q1 => true
  | _ => false

/-- The output warp's site of each loader site. -/
def Site.epi : Site → Epilogue.Site
  | .setmax => .start
  | .word k => .word k
  | .down k => .down k
  | .up k j => .up k j
  | .total k => .total k
  | .vote l => .vote l
  | .pre l => .pre l
  | .tiles l => .tiles l
  | .q0 => .q0
  | .q1 => .q1
  | _ => .ready 0

/-- The loader site of an output-warp site that a scheduler step reaches. -/
def Site.ofE : Epilogue.Site → Site
  | .word k => .word k
  | .down k => .down k
  | .up k j => .up k j
  | .total k => .total k
  | .vote l => .vote l
  | .pre l => .pre l
  | .tiles l => .tiles l
  | .q0 => .q0
  | .q1 => .q1
  | .ready _ => .uk
  | _ => .dw 0

/-- The output-warp state of a loader state. -/
abbrev toE (d : D) : Epilogue.D := { d.v.sc with site := d.site.epi }

/-- The loader's values after a scheduler step to output-warp site `s`: the drain's ring and Q
parities at the end of the first pass, the Q parity 0 from the second pass's ballot on. -/
def vOf (v : V) : Epilogue.Site → V
  | .exit false => drain0 v
  | .exit true | .vote true => { v with qp := i32 0 }
  | _ => v

/-- The loader state over `d` with the output-warp state `c` (the scan state's own site is kept;
it is not read). -/
abbrev ofE (d : D) (c : Epilogue.D) : D :=
  D.mk' (Site.ofE c.site) { vOf d.v c.site with sc := { c with site := d.v.sc.site } }

theorem toE_eq {s : Site} (hs : s.scan = true) : s.epi = s.toE := by
  cases s <;> simp_all [Site.scan, Site.epi, Site.toE]

variable {p : Params} {L : Launch} {g w : Nat}

theorem scanExit_eq (late : Bool) (d : D) (gx cur : BitVec 64) :
    scanExit p late d gx cur = ofE d (Epilogue.scanExit p late (toE d) gx cur) := by
  unfold scanExit Epilogue.scanExit
  cases late <;> simp only [D.ite] <;> split <;> rfl

theorem loopHead_eq (late : Bool) (d : D) (grp acc : BitVec 64) :
    loopHead p L g late d grp acc = ofE d (Epilogue.loopHead p L g late (toE d) grp acc) := by
  unfold loopHead Epilogue.loopHead
  simp only [D.ite]
  split
  · exact scanExit_eq late d _ _
  · split <;> cases late <;> rfl

/-- A loader state with only its scan state changed reads back the same output-warp states. -/
theorem ofE_scAt (d : D) (f : Epilogue.D → Epilogue.D) (hf : (f d.v.sc).site = d.v.sc.site)
    (c : Epilogue.D) : ofE (scAt d d.site f) c = ofE d c := by
  simp only [ofE, D.mk', hf]
  unfold vOf
  split <;> rfl

theorem afterTotal_eq (k : Epilogue.Scan) (d : D) (x : BitVec 64) :
    afterTotal p L g k d x = ofE d (Epilogue.afterTotal p L g k (toE d) x) := by
  unfold afterTotal Epilogue.afterTotal
  cases k <;> simp only [D.ite] <;> split <;>
    first
    | (rw [scanExit_eq, ofE_scAt _ _ rfl]; done)
    | (rw [loopHead_eq, ofE_scAt _ _ rfl]; done)

theorem word32_eq (d : D) (w : Value) {f : BitVec 64 → D} {f' : BitVec 64 → Epilogue.D}
    (h : ∀ x, f x = ofE d (f' x)) :
    word32 w f = (Epilogue.word32 w f').map (Option.map (ofE d)) := by
  unfold word32 Epilogue.word32
  split <;> simp_all

/-- **At a scheduler site the loader steps as the output warp** on its scan state. -/
theorem succ_scan {d : D} {e : Event} (hs : d.site.sched = true) :
    succ p L g w d e = (Epilogue.succ p L g (toE d) e).map (Option.map (ofE d)) := by
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [Site.sched, Bool.false_eq_true] at hs
  all_goals cases kind <;> simp only [succ, Epilogue.succ, Site.epi, Option.map_none]
  case word.rd a bs =>
    cases rebuild 3 bs with
    | error _ => rfl
    | ok w => exact word32_eq _ w fun _ => rfl
  case down.shfl w _ => exact word32_eq _ w fun _ => rfl
  case up.shfl k j _ _ _ _ w _ => exact word32_eq _ w fun x => by fin_cases j <;> rfl
  case total.shfl w _ => exact word32_eq _ w fun x => afterTotal_eq _ _ x
  case vote.vote l _ _ b =>
    simp only [Option.map_some, D.ite]
    split <;> cases l <;> rfl
  case pre.shfl l _ _ _ _ w _ => exact word32_eq _ w fun x => by cases l <;> rfl
  case q0.rd a bs =>
    cases rebuild 3 bs with
    | error _ => rfl
    | ok w => exact word32_eq _ w fun _ => rfl
  case q1.rd a bs =>
    cases rebuild 3 bs with
    | error _ => rfl
    | ok w => exact word32_eq _ w fun _ => rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
