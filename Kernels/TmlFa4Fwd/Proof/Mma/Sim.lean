-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Shape
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The MMA warp's scheduler steps as the output warp's

The MMA warp records its scheduler's scan in an output-warp state (`V.sc`). At every scheduler
site the MMA warp's step is the output warp's step of that state (`succ_scan`), read back as an
MMA state (`ofE`): the arithmetic of the two warps' scans is the same, on other registers. The
end of the scan without a tile is the output warp's return and the MMA warp's permit
relinquishment (`Site.ofE`). The choice of a tile (`tiles false`) differs: the MMA warp computes
the tile's coordinates its own way (`coords`), so only its successor's scan state is the output
warp's (`succ_tiles`).

`toE d` is the output-warp state of MMA state `d`; its site is `Site.epi`, the output warp's site
of each MMA site (the start for the sites before the scan, the return for the end, the request's
reads, and the first stage poll for the pipeline, whose scan state no longer changes). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (laneW ctaW paramW batchOf headsW reqOf loopOf tlOf)

noncomputable section

/-- The output warp's site of each MMA site. -/
def Site.epi : Site → Epilogue.Site
  | .bar1 | .ldAlloc | .bcast => .start
  | .word k => .word k
  | .down k => .down k
  | .up k j => .up k j
  | .total k => .total k
  | .vote l => .vote l
  | .pre l => .pre l
  | .tiles l => .tiles l
  | .q0 => .q0
  | .q1 => .q1
  | .relinq l | .bar2 l | .dealloc l | .exit l => .exit l
  | _ => .ready 0

/-- The MMA site of an output-warp site of the scan, of the request's first read and of the
return. -/
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
  | .ready st => if st = 0 then .uk else .bcast
  | .exit l => .relinq l
  | _ => .bcast

/-- The output-warp state of an MMA state. -/
abbrev toE (d : D) : Epilogue.D := { d.v.sc with site := d.site.epi }

/-- The MMA state over `d` with the output-warp state `c` (the scan state's own site is kept;
it is not read). -/
abbrev ofE (d : D) (c : Epilogue.D) : D :=
  ⟨Site.ofE c.site, { d.v with sc := { c with site := d.v.sc.site } }⟩

/-- The scan's sites, whose events are the output warp's. -/
def Site.scan : Site → Bool
  | .word _ | .down _ | .up _ _ | .total _ | .vote _ | .pre _ | .tiles _ => true
  | _ => false

/-- The scheduler sites at which the two warps step alike: the scan's except the choice of a
tile, and the request's two reads. -/
def Site.sched : Site → Bool
  | .word _ | .down _ | .up _ _ | .total _ | .vote _ | .pre _ | .q0 | .q1 => true
  | .tiles l => l
  | _ => false

theorem toE_eq {s : Site} (hs : s.scan = true) : s.epi = s.toE := by
  cases s <;> simp_all [Site.scan, Site.epi, Site.toE]

variable {p : Params} {L : Launch} {g : Nat}

theorem scanExit_eq (late : Bool) (d : D) (gx cur : BitVec 64) :
    scanExit p late d gx cur = ofE d (Epilogue.scanExit p late (toE d) gx cur) := by
  unfold scanExit Epilogue.scanExit
  split <;> rfl

theorem loopHead_eq (late : Bool) (d : D) (grp acc : BitVec 64) :
    loopHead p L g late d grp acc = ofE d (Epilogue.loopHead p L g late (toE d) grp acc) := by
  unfold loopHead Epilogue.loopHead
  split
  · exact scanExit_eq late d _ _
  · split <;> rfl

theorem afterTotal_eq (k : Epilogue.Scan) (d : D) (x : BitVec 64) :
    afterTotal p L g k d x = ofE d (Epilogue.afterTotal p L g k (toE d) x) := by
  unfold afterTotal Epilogue.afterTotal
  cases k <;> dsimp only <;> split <;>
    first
    | exact scanExit_eq _ _ _ _
    | exact loopHead_eq _ _ _ _

theorem word32_eq (d : D) (w : Value) {f : BitVec 64 → D} {f' : BitVec 64 → Epilogue.D}
    (h : ∀ x, f x = ofE d (f' x)) :
    word32 w f = (Epilogue.word32 w f').map (Option.map (ofE d)) := by
  unfold word32 Epilogue.word32
  split <;> simp_all

/-- **At a scheduler site the MMA warp steps as the output warp** on its scan state. -/
theorem succ_scan {d : D} {e : Event} (hs : d.site.sched = true) :
    succ p L g d e = (Epilogue.succ p L g (toE d) e).map (Option.map (ofE d)) := by
  obtain ⟨s, v⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [Site.sched, Bool.false_eq_true] at hs
  case tiles l =>
    cases l <;> simp only [Bool.false_eq_true] at hs
    cases kind <;> simp only [succ, Epilogue.succ, Site.epi, Option.map_none]
    case shfl _ _ _ _ w _ =>
      cases w <;> split <;> simp_all [Site.ofE]
  all_goals cases kind <;> simp only [succ, Epilogue.succ, Site.epi, Option.map_none]
  case word.rd a bs =>
    cases rebuild 3 bs with
    | error _ => rfl
    | ok w => exact word32_eq _ w fun _ => rfl
  case down.shfl w _ => exact word32_eq _ w fun _ => rfl
  case up.shfl k j _ _ _ _ w _ => exact word32_eq _ w fun x => by fin_cases j <;> rfl
  case total.shfl w _ => exact word32_eq _ w fun x => afterTotal_eq _ _ x
  case vote.vote b => simp only [Option.map_some]; split <;> rfl
  case pre.shfl l _ _ _ _ w _ => exact word32_eq _ w fun x => by cases l <;> rfl
  case q0.rd a bs =>
    cases rebuild 3 bs with
    | error _ => rfl
    | ok w => exact word32_eq _ w fun _ => rfl
  case q1.rd a bs =>
    cases rebuild 3 bs with
    | error _ => rfl
    | ok w => exact word32_eq _ w fun _ => rfl

/-- The output-warp state after the tile count `x` of the first pass. -/
def tilesE (p : Params) (d : D) (x : BitVec 64) : Epilogue.D :=
  let c : Epilogue.D := { d.v.sc with nt := x }
  if scmp .lt .s (Epilogue.chosen c) (paramW p.batch) then { c with site := .q0 }
  else { c with site := .exit false }

/-- **The choice of a tile**: the MMA warp's successor holds the output warp's scan state after
the tile count, at the request's first read or the end of the first pass. -/
theorem succ_tiles {d d' : D} {e : Event} (hs : d.site = .tiles false)
    (hn : succ p L g d e = some (some d')) :
    ∃ x : BitVec 64, (∃ pc r a b c ok, e = ⟨pc, .shfl r a b c (.bits 32 x) ok⟩) ∧
      d' = ofE d (tilesE p d x) := by
  obtain ⟨s, v⟩ := d
  obtain ⟨pc, kind⟩ := e
  simp only at hs
  subst hs
  cases kind <;> simp only [succ, reduceCtorEq] at hn
  case shfl r a b c w ok =>
    cases w
    all_goals try (simp at hn; done)
    case bits n x =>
      by_cases h32 : n = 32
      · subst h32
        refine ⟨x, ⟨pc, r, a, b, c, ok, rfl⟩, ?_⟩
        simp only [afterTiles, ↓reduceIte] at hn
        repeat' split at hn
        all_goals simp only [Option.map_some, Option.map_none, reduceCtorEq,
          Option.some.injEq] at hn
        all_goals subst hn
        all_goals simp_all [tilesE, Site.ofE]
      · simp [h32] at hn

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
