-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Next
public import Kernels.TmlFa4Fwd.Proof.Lib.SchedWords
public import Kernels.TmlFa4Fwd.Proof.Lib.SchedStep
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Sim
public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The softmax warps' scheduler reference values

As the correction warps' `CFits` without the rescale ballots: the softmax warps make no warp
collective outside their scheduler, so their reference values are the output warp's (`Fits`) on
their scan state at the thread's own shuffle and ballot counts, and from the used-K read to the
final named-barrier arrival the used-K word is the chosen request's (`SFits`). A step keeps them
(`sfits_next`): a scheduler step as the output warp's (`succ_scan`, `CorrWarp.efits_step`), the
used-K read by its reference, the region from the used-K read to the final stores without a change
of the scan state or the used-K word (`frameS`), the final arrival into the second pass
(`Epilogue.fits_pass2`), and the steps before the scan and at the end without one. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen Picked)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (ukv)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The region from the used-K read to the final stores, by site. -/
def _root_.PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Site.rgn : Site → Bool
  | .wq | .ws _ | .sld _ _ | .sldw _ | .wb _ | .bld _ _ | .fence _ | .bsync _ | .barr _ | .stat _
  | .narr _ | .pst _ _ | .pwst _ _ | .parr _ | .pws _ | .pel _ | .parr2 _ | .pwend _
  | .fin _ => true
  | _ => false

/-- From the used-K read to the final named-barrier arrival. -/
def _root_.PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Site.hasUk (s : Site) : Bool :=
  s.rgn || s == .finarr

/-- **The reference values at a state of a softmax lane**, with the thread's shuffles `ns` and
full-mask ballots `nv` before it. -/
def SFits (p : Params) (L : Launch) (g : Nat) (d : D) (ns nv : Nat) : Prop :=
  Epilogue.Fits p L g (toE d) ns nv ∧ (d.site.hasUk = true → d.v.ukw = ukv p (chosen d.v.sc))

/-- What the reference says a scheduler event returns: the output warp's reference at a
scheduler site, the launch's used-K length at its read. -/
def SExpect (p : Params) (L : Launch) (g : Nat) (d : D) (ns : Nat) (e : Event) : Prop :=
  match d.site, e.kind with
  | .uk, .rd _ bs => rebuild 3 bs = .ok (.bits 32 (ukv p (chosen d.v.sc)))
  | s, _ => s.sched = true → Epilogue.Expect p L g (toE d) ns e

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ns nv : Nat}

/-! ### Event counts -/

set_option maxHeartbeats 4000000 in
/-- An event is a shuffle at a scan shuffle site and a full-mask ballot at a ballot site. -/
theorem ev_counts {d : D} {e : Event} (hev : Softmax.Ev p L g d e) :
    Epilogue.sh e = (if (epi d.site).shfl then 1 else 0) ∧
      Epilogue.vt e = (if (epi d.site).ballot then 1 else 0) := by
  obtain ⟨pc, kind⟩ := e
  obtain ⟨s, v, k, acc⟩ := d
  cases s
  case down | up | total | pre | tiles =>
    simp only [Softmax.Ev] at hev
    exact Epilogue.ev_counts hev
  case vote =>
    simp only [Softmax.Ev] at hev
    obtain ⟨_, rfl⟩ := hev
    exact ⟨rfl, by simp only [Epilogue.vt, Epilogue.isFullVote_vote]; rfl⟩
  all_goals simp only [Softmax.Ev] at hev
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals subst_vars
  all_goals exact ⟨rfl, rfl⟩

/-! ### Scheduler steps -/

theorem ofS_back {s : Epilogue.Site} (h : Mma.backE s = true) :
    epi (ofS s) = s ∧ (ofS s).hasUk = false ∧ (ofS s).sched = (ofS s).sched := by
  cases s with
  | word k | down k | total k => cases k <;> decide
  | up k j => cases k <;> fin_cases j <;> decide
  | vote l | pre l | tiles l | exit l => cases l <;> decide
  | ready st => (fin_cases st <;> simp_all [Mma.backE]); decide
  | _ => simp_all [Mma.backE] <;> decide

theorem toE_ofE {d : D} {c : Epilogue.D} (h : Mma.backE c.site = true) : toE (ofE d c) = c := by
  simp only [toE, ofE, D.mk', (ofS_back h).1]

theorem sched_out {s : Site} (hs : s.sched = true) : s.hasUk = false := by
  cases s with
  | word k | down k | total k => cases k <;> decide
  | up k j => cases k <;> fin_cases j <;> decide
  | vote l | pre l | tiles l => cases l <;> decide
  | _ => simp_all [Site.sched] <;> decide

/-- **A scheduler step reaches a scheduler site, the used-K read, or the end.** -/
theorem succ_back {d : D} {e : Event} {c : Epilogue.D} (hs : d.site.sched = true)
    (h : Epilogue.succ p L g (toE d) e = some (some c)) : Mma.backE c.site = true := by
  obtain ⟨s, v, k, acc⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [Site.sched, Bool.false_eq_true] at hs
  all_goals cases kind <;> simp only [Epilogue.succ, epi, reduceCtorEq] at h
  all_goals try simp only [Epilogue.word32, Epilogue.afterTotal, Epilogue.loopHead,
    Epilogue.scanExit, Epilogue.afterTiles] at h
  all_goals repeat' split at h
  all_goals try simp only [reduceCtorEq, Option.some.injEq, Option.map_some,
    Option.map_none] at h
  all_goals first
    | (subst h; simp_all [Mma.backE, Epilogue.loopOf, Epilogue.Scan.late]; done)
    | (cases h; done)
    | (simp_all; done)

/-- The scheduler step keeps the reference values. -/
theorem sfits_sched (hc : ctaR p L g = Epilogue.ctaW L g) {d d' : D} {e : Event}
    (hs : d.site.sched = true) (hF : SFits p L g d ns nv) (hE : SExpect p L g d ns e)
    (hev : Softmax.Ev p L g d e) (hn : succ p L g d e = some (some d')) :
    SFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) := by
  obtain ⟨hFE, -⟩ := hF
  rw [succ_scan hc hs] at hn
  rcases hc' : Epilogue.succ p L g (toE d) e with _ | _ | c <;> rw [hc'] at hn <;>
    simp only [Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at hn
  subst hn
  have b1 := succ_back hs hc'
  have hE' : Epilogue.Expect p L g (toE d) ns e := by
    obtain ⟨s, v, k, acc⟩ := d
    obtain ⟨pc, kind⟩ := e
    have hs' := hs
    cases s <;> simp only [Site.sched, Bool.false_eq_true] at hs' <;>
      first | exact hE hs | (cases kind <;> exact hE hs)
  obtain ⟨h1, h2⟩ := ev_counts hev
  have hn' := CorrWarp.efits_step hFE hE' h1 h2 hc'
  refine ⟨?_, fun h => by simp [ofE, D.mk', (ofS_back b1).2.1] at h⟩
  rw [toE_ofE b1]
  exact hn'

/-! ### Steps that keep the scan state -/

/-- A step to a state with the same scan state and used-K word and the same output-warp site
keeps the reference values. -/
theorem sfits_keep {d d' : D} (hsc : d'.v.sc = d.v.sc) (hu : d'.v.ukw = d.v.ukw)
    (hep : epi d'.site = epi d.site) (huk : d'.site.hasUk = true → d.site.hasUk = true)
    (hF : SFits p L g d ns nv) : SFits p L g d' ns nv := by
  obtain ⟨hFE, hU⟩ := hF
  have hE : toE d' = toE d := by simp only [toE, hsc, hep]
  exact ⟨hE ▸ hFE, fun h => by rw [hu, hsc]; exact hU (huk h)⟩

/-- What a step inside the region from the used-K read to the final stores keeps. -/
def KeepS (d d' : D) : Prop := d'.v.sc = d.v.sc ∧ d'.v.ukw = d.v.ukw ∧ d'.site.hasUk = true

theorem keepS_ite {c : Bool} {d a b : D} (ha : KeepS d a) (hb : KeepS d b) :
    KeepS d (D.ite c a b) := by
  cases c <;> assumption

theorem keepS_plainEntry {d : D} {v : V} (hsc : v.sc = d.v.sc) (hu : v.ukw = d.v.ukw) :
    KeepS d (plainEntry p L g v) := by
  unfold plainEntry
  apply keepS_ite <;> exact ⟨hsc, hu, rfl⟩

theorem keepS_afterRound (d : D) (r : Rd) : KeepS d (afterRound p L g d r) := by
  cases r
  · unfold afterRound afterFirst
    apply keepS_ite
    · exact keepS_plainEntry rfl rfl
    · exact ⟨rfl, rfl, rfl⟩
  · unfold afterRound afterBias
    apply keepS_ite
    · exact ⟨rfl, rfl, rfl⟩
    · exact keepS_plainEntry rfl rfl
  · unfold afterRound afterPlain
    apply keepS_ite <;> exact ⟨rfl, rfl, rfl⟩

theorem pstNext_hasUk (r : Rd) (q : Fin 4) : (pstNext r q).hasUk = true := by
  cases r <;> fin_cases q <;> rfl

theorem afterLoads_hasUk (r : Rd) : (afterLoads r).hasUk = true := by
  cases r <;> rfl

set_option hygiene false in
/-- The closing script of one region site's successors. -/
macro "fs_close" : tactic => `(tactic| (
  simp only [succ, Fin.isValue] at hn
  -- the transition names one or two event kinds: split its match, not the kinds
  repeat' split at hn
  all_goals try contradiction
  all_goals try simp only [Option.some.injEq, reduceCtorEq] at hn
  all_goals try subst hn
  all_goals first
    | contradiction
    | exact ⟨rfl, rfl, rfl⟩
    | exact keepS_afterRound _ _
    | exact ⟨rfl, rfl, pstNext_hasUk _ _⟩
    | exact ⟨rfl, rfl, afterLoads_hasUk _⟩
    | (simp only [D.ite]; split <;> exact ⟨rfl, rfl, rfl⟩)
    | (split <;> exact ⟨rfl, rfl, rfl⟩)
    | (cases hn; done)))

set_option maxHeartbeats 8000000 in
/-- **A step inside the region keeps the scan state and the used-K word, and stays in it**
(its last site, the final arrival, excepted). -/
theorem frameS {d d' : D} {e : Event} (hr : d.site.rgn = true)
    (hn : succ p L g d e = some (some d')) : KeepS d d' := by
  obtain ⟨s, v, k, acc⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [Site.rgn, Bool.false_eq_true] at hr
  case ws r => cases r <;> fs_close
  case narr r => cases r <;> fs_close
  case parr r => cases r <;> fs_close
  case pws r => cases r <;> fs_close
  case pel r => cases r <;> fs_close
  case parr2 r => cases r <;> fs_close
  case pwend r =>
    cases kind <;> simp only [succ, reduceCtorEq] at hn
    simp only [Option.some.injEq] at hn
    subst hn
    split
    · exact keepS_afterRound _ _
    · cases r <;> exact ⟨rfl, rfl, rfl⟩
  case sld r c | pst r c | pwst r c => cases r <;> fs_close
  case sldw c => fs_close
  case fin c => fin_cases c <;> fs_close
  case bld b c => cases b <;> fs_close
  case wb b | fence b | bsync b | barr b | stat b => cases b <;> fs_close
  all_goals fs_close

/-! ### Every step -/

theorem epi_hasUk {s : Site} (h : s.hasUk = true) : epi s = .ready 0 := by
  cases s <;> simp_all [Site.hasUk, Site.rgn, epi]

set_option maxHeartbeats 8000000 in
/-- **Every step of a softmax lane keeps the scheduler reference values.** -/
theorem sfits_next (hc : ctaR p L g = Epilogue.ctaW L g) {d d' : D} {e : Event}
    (hF : SFits p L g d ns nv) (hE : SExpect p L g d ns e) (hev : Softmax.Ev p L g d e)
    (hn : succ p L g d e = some (some d')) :
    SFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) := by
  by_cases hs : d.site.sched = true
  · exact sfits_sched hc hs hF hE hev hn
  obtain ⟨h1, h2⟩ := ev_counts hev
  by_cases hr : d.site.rgn = true
  · obtain ⟨hsc, hu, huk⟩ := frameS hr hn
    have hep : epi d.site = .ready 0 := epi_hasUk (by simp [Site.hasUk, hr])
    rw [h1, h2, hep]
    simp only [Epilogue.Site.shfl, Epilogue.Site.ballot, Bool.false_eq_true, ↓reduceIte,
      Nat.add_zero]
    exact sfits_keep hsc hu (by rw [epi_hasUk huk, hep]) (fun _ => by simp [Site.hasUk, hr]) hF
  obtain ⟨s, v, k, acc⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [Site.sched, Site.rgn, Bool.false_eq_true, not_false_eq_true,
    not_true_eq_false] at hs hr
  all_goals simp only [epi, Epilogue.Site.shfl, Epilogue.Site.ballot, Bool.false_eq_true,
    ↓reduceIte] at h1 h2
  all_goals rw [h1, h2]
  case setmax =>
    simp only [succ, Option.some.injEq] at hn
    subst hn
    exact sfits_keep rfl rfl rfl id hF
  case uk =>
    cases kind <;> simp only [succ, reduceCtorEq] at hn
    rename_i a bs
    simp only [SExpect] at hE
    rw [hE] at hn
    simp only [word32, Option.some.injEq] at hn
    subst hn
    exact ⟨hF.1, fun _ => rfl⟩
  case finarr =>
    simp only [succ, Option.some.injEq] at hn
    subst hn
    obtain ⟨hFE, -⟩ := hF
    simp only [Epilogue.Fits, toE, epi] at hFE
    obtain ⟨R, bal, hC, -, -⟩ := hFE
    have hP := Epilogue.fits_pass2 hC
    by_cases hb : scmp .gt .s (Epilogue.laneW L g) (Epilogue.paramW p.batch) = true
    · simp only [hb, ↓reduceIte] at hP
      simp only [passStart, D.ite, hb, ↓reduceIte, ite_true]
      exact ⟨hP, fun h => by simp [Site.hasUk, Site.rgn] at h⟩
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hP
      simp only [passStart, D.ite, hb, Bool.false_eq_true, ↓reduceIte, ite_true]
      exact ⟨hP, fun h => by simp [Site.hasUk, Site.rgn] at h⟩
  case wend l =>
    cases kind <;> simp only [succ, reduceCtorEq, Option.some.injEq] at hn
    split at hn <;> subst hn
    · exact sfits_keep rfl rfl rfl (fun h => by cases l <;> simp [Site.hasUk, Site.rgn] at h) hF
    · exact hF
  case barEnd l =>
    simp only [succ, Option.some.injEq] at hn
    subst hn
    exact sfits_keep rfl rfl rfl (fun h => by cases l <;> simp [Site.hasUk, Site.rgn] at h) hF
  case exit l => simp [succ] at hn

end
end PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
