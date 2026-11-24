-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.RankDefs
public import Kernels.Fp16Gemm8192.Proof.Thread.TmemDefs

@[expose] public section

/-! # The warp-synchronous collective sites

Six sites of the kernel are warp-synchronous collectives (`CollSite`): the prologue's shuffle (every
warp), election and warp barrier (warp 0), the role election of warp 11, and the elections of the
MMA warps and of the scheduler warp. Every lane of a warp runs the same sequence of these sites. At
a site a thread performs one of `CollSite.Fires` (a full-mask election or warp barrier, the shuffle
of its warp index from lane 0); the events of other threads that match an instance of the site are
`CollSite.Matches`; the event before the site, which the lanes' release depends on, is
`CollSite.Before`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof

noncomputable section

/-- The warp-synchronous collective sites. -/
inductive CollSite where
  | shfl | elect | warpBar | roleElect | mmaElect | schedElect
  deriving DecidableEq

/-- The collective site a state is at, if any. -/
def ThreadD.coll : ThreadD → Option CollSite
  | .inl p => match p.site with
    | .shfl => some .shfl | .elect => some .elect | .warpBar => some .warpBar
    | .roleElect => some .roleElect | _ => none
  | .inr (.mma m) => match m.site with | .elect => some .mmaElect | _ => none
  | .inr (.sched s) => match s.site with | .elect => some .schedElect | _ => none
  | .inr _ => none

/-- The program position of a site. -/
def CollSite.pc : CollSite → Nat
  | .shfl => Prologue.Site.shfl.pc
  | .elect => Prologue.Site.elect.pc
  | .warpBar => Prologue.Site.warpBar.pc
  | .roleElect => Prologue.Site.roleElect.pc
  | .mmaElect => Mma.Site.elect.pc
  | .schedElect => Scheduler.Site.elect.pc

/-- The full member mask. -/
abbrev fullMask : Nat := 4294967295

/-- The events thread `g` performs at a site: the shuffle of its warp index from lane 0, the
full-mask warp barrier, the full-mask election. -/
def CollSite.Fires (L : Launch) (g : Nat) (s : CollSite) (e : Event) : Prop :=
  match s with
  | .shfl => ∃ recv ok, e = ⟨s.pc, .shfl .idx (b32 (g % L.block / 32)) 0 31 recv ok⟩
  | .warpBar => ∃ inst, e = ⟨s.pc, .warpBar fullMask inst⟩
  | _ => ∃ inst leader, e = ⟨s.pc, .elect fullMask inst leader⟩

/-- The events that belong to an instance of a site: any shuffle, any full-mask warp barrier, a
full-mask election at the site. -/
def CollSite.Matches (s : CollSite) (e : Event) : Prop :=
  match s with
  | .shfl => ∃ pc m a b c recv ok, e = ⟨pc, .shfl m a b c recv ok⟩
  | .warpBar => ∃ pc inst, e = ⟨pc, .warpBar fullMask inst⟩
  | _ => ∃ inst leader, e = ⟨s.pc, .elect fullMask inst leader⟩

/-- The events of thread `g` before a site: none before the shuffle; the shuffle before warp 0's
election; before the warp barrier, warp 0's Tensor Memory allocation, as its last event or
followed by lane 0's write of the column; before the role elections, the register
request. -/
def CollSite.Before (X : Execution) (g : Nat) (s : CollSite) : Prop :=
  match s with
  | .shfl => X.tr g = []
  | .elect => ∃ e, X.tr g = [e] ∧ Execution.isShfl e = true
  | .warpBar => ∃ j pc grp dst act, X.get (g, j) = some ⟨pc, .tc (.resource grp dst act)⟩ ∧
      tmemOps ((X.tr g).take j) = 0 ∧
      (j + 1 = (X.tr g).length ∨ (j + 2 = (X.tr g).length ∧
        ∃ pc' a bs, X.get (g, j + 1) = some ⟨pc', .wr a bs⟩))
  | _ => 0 < (X.tr g).length ∧
      ∃ pc inc n inst, X.get (g, (X.tr g).length - 1) = some ⟨pc, .setMaxReg inc n inst⟩

/-- A state at a collective site is outside the exit stage. -/
theorem ThreadD.coll_exitOff {d : ThreadD} {s : CollSite} (h : d.coll = some s) :
    d.exitOff = none := by
  rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
      ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
  all_goals (cases site <;> simp_all [ThreadD.coll, ThreadD.exitOff, Mma.exitOff,
    Scheduler.exitOff])

/-- The time of a state at a collective site: at least 2 after the shuffle. -/
theorem ThreadD.coll_vtime {d : ThreadD} {s : CollSite} (h : d.coll = some s) (L : Launch)
    (g : Nat) (es : List Event) : s ≠ .shfl → 2 ≤ d.vtime L g es := by
  rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
      ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
  all_goals (cases site <;> simp_all [ThreadD.coll, ThreadD.vtime, Prologue.Site.vtime,
    Mma.vtime, Scheduler.vtime])

end
end PTX.Kernels.Fp16Gemm8192.Proof
