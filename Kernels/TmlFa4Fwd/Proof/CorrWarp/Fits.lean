-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.SchedWords
public import Kernels.TmlFa4Fwd.Proof.Lib.SchedStep
public import Kernels.TmlFa4Fwd.Proof.Correction.Places
public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Sim
public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Next
import Kernels.TmlFa4Fwd.Proof.Correction.Ref
import Kernels.TmlFa4Fwd.Proof.Correction.RefCases
import Kernels.TmlFa4Fwd.Proof.Correction.RefStep
import Lemmas.Flow.Counter32
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The correction warps' reference values

The correction warps' scheduler is the output warp's on their scan state, so their reference
values are the output warp's (`Epilogue.Fits`) on `toE d`, with the thread's ballot count shifted
by the rescale rounds' ballots (`RvAt`): two per round done and those of the current round before
the state; from the final stage to the LSE stores the ballots of all rounds of the tile (`rvN` of
its block count); in the second pass and at its end those of the tile the first pass picked,
which is the same on every lane of the CTA. From the used-K read to the second pass the recorded
used-K length is the launch word (`ukv`).

`cfits_next`: a step on an event that returns what the reference says (`CExpect`) keeps `CFits`.
At a scheduler site it is the output warp's step (`succ_scan`); the rounds and the final stage
keep the scan state (the correction lane's `succ_cases`), the entry and the end of a round move
the round counter, and the end of the final stage starts the second pass (`Epilogue.fits_pass2`).
-/

namespace PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (laneW paramW chosen Picked)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (ukv neg32)

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-! ### Definitions -/

/-- The second pass's sites and the end after it. -/
def _root_.PTX.Kernels.TmlFa4Fwd.Proof.Correction.Site.late : Site → Bool
  | .word k | .down k | .up k _ | .total k => k.late
  | .vote l | .pre l | .tiles l | .wend l | .barEnd l | .exit l => l
  | _ => false

/-- From the used-K read to the second pass. -/
def _root_.PTX.Kernels.TmlFa4Fwd.Proof.Correction.Site.hasUk (s : Site) : Bool :=
  decide (7960 ≤ s.pc) && decide (s.pc < 9089)

/-- The rescale ballots. -/
def _root_.PTX.Kernels.TmlFa4Fwd.Proof.Correction.Site.isRvote : Site → Bool
  | .rvote _ => true
  | _ => false

/-- The rescale ballots of the current round before a state at site `s`. -/
def sv (s : Site) : Nat := (if 8009 < s.pc then 1 else 0) + (if 8228 < s.pc then 1 else 0)

/-- The rescale ballots of a tile with `B` blocks: two per round, `B - 1` rounds. -/
def rvN (B : Int) : Nat := if B < 2 then 0 else 2 * (B.toNat - 1)

/-- The rounds' values of the tile the first pass picked after its scan ended at round `R` with
ballot `bal`. -/
def refV (p : Params) (L : Launch) (g R : Nat) (bal : BitVec 64) : V :=
  let c := Epilogue.chosenD p (g / L.block) R bal
  { sc := { c with c0 := Epilogue.qv p (chosen c), c1 := Epilogue.qv p (addi (chosen c) 1) },
    ukw := ukv p (chosen c) }

/-- The rescale ballots before a state, `rv`. -/
def RvAt (p : Params) (L : Launch) (g : Nat) (d : D) (rv : Nat) : Prop :=
  if inRound d.site.pc then ∃ r : Nat, (r : Int) + 1 < Bs p L g d.v ∧
      d.v.trip = i32 (r - Bs p L g d.v) ∧ rv = 2 * r + sv d.site
  else if tailR d.site then rv = rvN (Bs p L g d.v)
  else if d.site.late then ∃ R bal, Picked p L g R bal ∧ rv = rvN (Bs p L g (refV p L g R bal))
  else rv = 0

/-- **The reference values at a state of a correction lane**, with the thread's shuffles `ns` and
full-mask ballots `nv` before it. -/
def CFits (p : Params) (L : Launch) (g : Nat) (d : D) (ns nv : Nat) : Prop :=
  ∃ rv, rv ≤ nv ∧ RvAt p L g d rv ∧ Epilogue.Fits p L g (toE d) ns (nv - rv) ∧
    (d.site.hasUk = true → d.v.ukw = ukv p (chosen d.v.sc))

/-- What the reference says a scheduler event returns: the output warp's reference at a
scheduler site, the launch's used-K length at its read. -/
def CExpect (p : Params) (L : Launch) (g : Nat) (d : D) (ns : Nat) (e : Event) : Prop :=
  match d.site, e.kind with
  | .uk, .rd _ bs => rebuild 3 bs = .ok (.bits 32 (ukv p (chosen d.v.sc)))
  | s, _ => s.sched = true → Epilogue.Expect p L g (toE d) ns e

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ns nv : Nat}

/-! ### Event counts -/

/-- An event is a shuffle at a scan shuffle site and a full-mask ballot at a ballot site. -/
theorem ev_counts {d : D} {e : Event} (hev : Ev p L g d e) :
    Epilogue.sh e = (if (epi d.site).shfl then 1 else 0) ∧
      Epilogue.vt e = (if (epi d.site).ballot || d.site.isRvote then 1 else 0) := by
  obtain ⟨pc, kind⟩ := e
  obtain ⟨s, v, k⟩ := d
  cases s <;> simp only [Ev] at hev
  case down | up | total | pre | tiles => exact Epilogue.ev_counts hev
  case vote | rvote =>
    obtain ⟨_, rfl⟩ := hev
    exact ⟨rfl, by simp only [Epilogue.vt, Epilogue.isFullVote_vote]; rfl⟩
  case word | q0 | q1 | uk | rscale | fsum | fmax =>
    rcases hev with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> exact ⟨rfl, rfl⟩
  case setmax => obtain ⟨_, _, _, rfl⟩ := hev; exact ⟨rfl, rfl⟩
  case fw | wend => obtain ⟨_, rfl⟩ := hev; exact ⟨rfl, rfl⟩
  case rld | fld => rcases hev with ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩ <;> exact ⟨rfl, rfl⟩
  case rldw => rcases hev with rfl | ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩ <;> exact ⟨rfl, rfl⟩
  case rst => rcases hev with ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩ <;> exact ⟨rfl, rfl⟩
  case rwait | barEnd => rcases hev with rfl | ⟨_, rfl⟩ <;> exact ⟨rfl, rfl⟩
  case fst | lse => rcases hev with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> exact ⟨rfl, rfl⟩
  case fence => obtain ⟨_, _, rfl⟩ := hev; exact ⟨rfl, rfl⟩
  all_goals subst hev; exact ⟨rfl, rfl⟩

/-! ### Scheduler steps -/

theorem ofS_back {s : Epilogue.Site} (h : Mma.backE s = true) :
    epi (ofS s) = s ∧ (ofS s).late = Mma.lateE s ∧ inRound (ofS s).pc = false ∧
      tailR (ofS s) = false ∧ (ofS s).hasUk = false ∧ (ofS s).isRvote = false := by
  cases s with
  | word k | down k | total k => cases k <;> decide
  | up k j => cases k <;> fin_cases j <;> decide
  | vote l | pre l | tiles l | exit l => cases l <;> decide
  | ready st => (fin_cases st <;> simp_all [Mma.backE]); decide
  | _ => simp_all [Mma.backE] <;> decide

theorem toE_ofE {d : D} {c : Epilogue.D} (h : Mma.backE c.site = true) : toE (ofE d c) = c := by
  simp only [toE, ofE, D.mk', (ofS_back h).1]

theorem sched_out {s : Site} (hs : s.sched = true) :
    inRound s.pc = false ∧ tailR s = false ∧ s.hasUk = false ∧ s.isRvote = false := by
  cases s with
  | arr k => (fin_cases k <;> simp_all [Site.sched]); decide
  | word k | down k | total k => cases k <;> decide
  | up k j => cases k <;> fin_cases j <;> decide
  | vote l | pre l | tiles l => cases l <;> decide
  | _ => simp_all [Site.sched] <;> decide

/-- **A scheduler step reaches a scheduler site, the used-K read, or the end**, in the same
pass. -/
theorem succ_back {d : D} {e : Event} {c : Epilogue.D} (hs : d.site.sched = true)
    (h : Epilogue.succ p L g (toE d) e = some (some c)) :
    Mma.backE c.site = true ∧ Mma.lateE c.site = d.site.late := by
  obtain ⟨s, v, k⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [Site.sched, Bool.false_eq_true] at hs
  all_goals try subst hs
  all_goals cases kind <;> simp only [Epilogue.succ, epi, reduceCtorEq] at h
  all_goals try simp only [Epilogue.word32, Epilogue.afterTotal, Epilogue.loopHead,
    Epilogue.scanExit, Epilogue.afterTiles] at h
  all_goals repeat' split at h
  all_goals try simp only [reduceCtorEq, Option.some.injEq, Option.map_some,
    Option.map_none] at h
  all_goals first
    | (subst h; simp_all [Mma.backE, Mma.lateE, Site.late, Epilogue.loopOf,
        Epilogue.Scan.late]; done)
    | (cases h; done)
    | (simp_all; done)

theorem rvAt_out {d : D} {rv : Nat} (h1 : inRound d.site.pc = false) (h2 : tailR d.site = false) :
    RvAt p L g d rv ↔ (if d.site.late then ∃ R bal, Picked p L g R bal ∧
      rv = rvN (Bs p L g (refV p L g R bal)) else rv = 0) := by
  simp only [RvAt, h1, h2, Bool.false_eq_true, ↓reduceIte]

/-- The scheduler step keeps the reference values. -/
theorem cfits_sched (hc : ctaR p L g = Epilogue.ctaW L g) {d d' : D} {e : Event}
    (hs : d.site.sched = true) (hF : CFits p L g d ns nv) (hE : CExpect p L g d ns e)
    (hev : Ev p L g d e) (hn : succ p L g d e = some (some d')) :
    CFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) := by
  obtain ⟨rv, hle, hrv, hFE, -⟩ := hF
  obtain ⟨o1, o2, -, o4⟩ := sched_out hs
  rw [succ_scan hc hs] at hn
  rcases hc' : Epilogue.succ p L g (toE d) e with _ | _ | c <;> rw [hc'] at hn <;>
    simp only [Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at hn
  subst hn
  obtain ⟨b1, b2⟩ := succ_back hs hc'
  obtain ⟨q1, q2, q3, q4, q5, -⟩ := ofS_back b1
  have hE' : Epilogue.Expect p L g (toE d) ns e := by
    obtain ⟨s, v, k⟩ := d
    obtain ⟨pc, kind⟩ := e
    have hs' := hs
    cases s <;> simp only [Site.sched, Bool.false_eq_true] at hs' <;>
      first | exact hE hs | (cases kind <;> exact hE hs)
  obtain ⟨h1, h2⟩ := ev_counts hev
  rw [o4, Bool.or_false] at h2
  have hn' := efits_step hFE hE' h1 h2 hc'
  refine ⟨rv, by omega, ?_, ?_, fun h => by simp [ofE, D.mk', q5] at h⟩
  · rw [rvAt_out (by simpa [ofE, D.mk'] using q3) (by simpa [ofE, D.mk'] using q4)]
    rw [rvAt_out o1 o2] at hrv
    simp only [ofE, D.mk', q2, b2]
    exact hrv
  · rw [toE_ofE b1, show nv + Epilogue.vt e - rv = nv - rv + Epilogue.vt e by omega]
    exact hn'

/-! ### Steps that keep the scan state -/

/-- A step to a state with the same values and the same output-warp site keeps the reference
values when the ballots before it are those before the step. -/
theorem cfits_keep {d d' : D} (hv : d'.v = d.v) (hep : epi d'.site = epi d.site)
    (hrv : ∀ rv, RvAt p L g d rv → RvAt p L g d' rv)
    (huk : d'.site.hasUk = true → d.site.hasUk = true) (hF : CFits p L g d ns nv) :
    CFits p L g d' ns nv := by
  obtain ⟨rv, hle, hr, hFE, hu⟩ := hF
  have hE : toE d' = toE d := by simp only [toE, hv, hep]
  exact ⟨rv, hle, hrv rv hr, hE ▸ hFE, fun h => hv ▸ hu (huk h)⟩

/-- The sites whose steps keep the values: before the scan, between the used-K read and the
rounds, and the end. -/
def _root_.PTX.Kernels.TmlFa4Fwd.Proof.Correction.Site.quiet : Site → Bool
  | .setmax | .bar1 | .arr 0 | .nb 0 | .free | .wend _ | .barEnd _ => true
  | _ => false

theorem cfits_quiet {d d' : D} {e : Event} (hq : d.site.quiet = true) (hF : CFits p L g d ns nv)
    (hev : Ev p L g d e) (hn : succ p L g d e = some (some d')) :
    CFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) := by
  obtain ⟨h1, h2⟩ := ev_counts hev
  obtain ⟨s, v, k⟩ := d
  have hk : ∀ (s' : Site), epi s' = epi s → s'.late = s.late → inRound s.pc = false →
      tailR s = false → inRound s'.pc = false → tailR s' = false →
      (s'.hasUk = true → s.hasUk = true) → (d' = D.mk' s' v ∨ d' = ⟨s, v, k⟩) →
      CFits p L g d' ns nv := by
    intro s' he hl r1 t1 r2 t2 hu hd
    rcases hd with rfl | rfl
    · refine cfits_keep (d := ⟨s, v, k⟩) rfl he (fun rv h => ?_) hu hF
      rw [rvAt_out (d := D.mk' s' v) r2 t2]; rw [rvAt_out (d := ⟨s, v, k⟩) r1 t1] at h
      simpa only [D.mk', hl] using h
    · exact hF
  cases s <;> simp only [Site.quiet, Bool.false_eq_true] at hq
  all_goals simp only [epi, Epilogue.Site.shfl, Epilogue.Site.ballot, Site.isRvote,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte] at h1 h2
  all_goals rw [h1, h2]
  case arr j =>
    fin_cases j <;> simp at hq
    simp only [succ, Option.some.injEq] at hn
    exact hk (.arr 1) rfl rfl rfl rfl rfl rfl (fun h => h) (.inl hn.symm)
  case wend l =>
    obtain ⟨pc, kind⟩ := e
    cases kind <;> simp only [succ, reduceCtorEq, Option.some.injEq] at hn
    split at hn <;> subst hn
    · exact hk (.barEnd l) rfl rfl (by cases l <;> rfl) (by cases l <;> rfl)
        (by cases l <;> rfl) (by cases l <;> rfl) (by cases l <;> decide) (.inl rfl)
    · exact hk (.wend l) rfl rfl (by cases l <;> rfl) (by cases l <;> rfl)
        (by cases l <;> rfl) (by cases l <;> rfl) (fun h => h) (.inr rfl)
  case barEnd l =>
    simp only [succ, Option.some.injEq] at hn
    exact hk (.exit l) rfl rfl (by cases l <;> rfl) (by cases l <;> rfl)
      (by cases l <;> rfl) (by cases l <;> rfl) (by cases l <;> decide) (.inl hn.symm)
  case setmax =>
    simp only [succ, Option.some.injEq] at hn
    exact hk .bar1 rfl rfl rfl rfl rfl rfl (by decide) (.inl hn.symm)
  case bar1 =>
    simp only [succ, Option.some.injEq] at hn
    exact hk (.arr 0) rfl rfl rfl rfl rfl rfl (by decide) (.inl hn.symm)
  case nb j =>
    fin_cases j <;> simp at hq
    simp only [succ, Option.some.injEq] at hn
    exact hk .free rfl rfl rfl rfl rfl rfl (fun _ => rfl) (.inl hn.symm)
  case free =>
    simp only [succ, Option.some.injEq] at hn
    exact hk (.nb 1) rfl rfl rfl rfl rfl rfl (fun _ => rfl) (.inl hn.symm)

/-- The used-K read records the launch word. -/
theorem cfits_uk {d d' : D} {e : Event} (hs : d.site = .uk) (hF : CFits p L g d ns nv)
    (hE : CExpect p L g d ns e) (hev : Ev p L g d e) (hn : succ p L g d e = some (some d')) :
    CFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) := by
  obtain ⟨h1, h2⟩ := ev_counts hev
  obtain ⟨s, v, k⟩ := d
  simp only at hs
  subst hs
  simp only [epi, Epilogue.Site.shfl, Epilogue.Site.ballot, Site.isRvote, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte] at h1 h2
  rw [h1, h2]
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp only [succ, reduceCtorEq] at hn
  rename_i a bs
  simp only [CExpect] at hE
  rw [hE] at hn
  simp only [word32, Option.some.injEq] at hn
  subst hn
  obtain ⟨rv, hle, hr, hFE, -⟩ := hF
  refine ⟨rv, hle, ?_, hFE, fun _ => rfl⟩
  rw [rvAt_out rfl rfl] at hr ⊢
  exact hr

/-! ### The rounds and the final stage -/

/-- The sites whose successor the explicit lemmas treat: the end of the final stage and the LSE
stores. -/
def _root_.PTX.Kernels.TmlFa4Fwd.Proof.Correction.Site.fin (s : Site) : Bool :=
  s == .fdone 1 1 || s == .lse 0 || s == .lse 1

/-- A move inside the rounds or the final stage: it stays there, at the output warp's first
stage poll, past the used-K read; inside a round it passes the rescale ballot it fires; it
enters the final stage only from it. -/
def RtP (s : Site) : Prop :=
  (inRound s.pc || tailR s) = true → s.special = false → s.fin = false →
    epi s = .ready 0 ∧ s.hasUk = true ∧ ¬ (inRound s.pc = true ∧ tailR s = true) ∧
    ∀ s' ∈ nexts s, (inRound s'.pc || tailR s') = true ∧ epi s' = .ready 0 ∧ s'.hasUk = true ∧
      (inRound s'.pc = true →
        inRound s.pc = true ∧ sv s' = sv s + (if s.isRvote = true then 1 else 0)) ∧
      (tailR s' = true → tailR s = true ∧ s.isRvote = false ∧ inRound s'.pc = false)

instance (s : Site) : Decidable (RtP s) := by unfold RtP; infer_instance

set_option maxRecDepth 100000 in
theorem rt_ok : allSites.all (fun s => decide (RtP s)) = true := by decide +kernel

theorem rtP_of (s : Site) : RtP s :=
  of_decide_eq_true (List.all_eq_true.mp rt_ok s (mem_allSites s))

/-- A step inside the rounds or the final stage keeps the reference values. -/
theorem cfits_rt {d d' : D} {e : Event} (hrt : (inRound d.site.pc || tailR d.site) = true)
    (hsp : d.site.special = false) (hfin : d.site.fin = false) (hF : CFits p L g d ns nv)
    (hev : Ev p L g d e) (hn : succ p L g d e = some (some d')) :
    CFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) := by
  obtain ⟨hep, huk0, hnb, hall⟩ := rtP_of d.site hrt hsp hfin
  obtain ⟨h1, h2⟩ := ev_counts hev
  simp only [hep, Epilogue.Site.shfl, Epilogue.Site.ballot, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte] at h1 h2
  obtain ⟨rv, hle, hr, hFE, hu⟩ := hF
  rcases succ_cases hn with ⟨rfl, m, par, a, sc, hw⟩ | ⟨hf, -, rfl⟩ | hM
  · obtain ⟨pc, kind⟩ := e
    simp only at hw
    subst hw
    exact ⟨rv, hle, hr, hFE, hu⟩
  · have hrv : d.site.isRvote = false := by
      obtain ⟨s, v, k⟩ := d; cases s <;> simp_all [Site.isFst, Site.isRvote]
    rw [h1, h2, hrv]
    exact ⟨rv, hle, hr, hFE, hu⟩
  · obtain ⟨hmem, -, -, -, hT, -⟩ := hM
    obtain ⟨hrt', hep', huk', hin, htl⟩ := hall d'.site hmem
    have hfr := hT hsp (by simpa [Bool.or_eq_true] using hrt')
    obtain ⟨htr, hukw, hsc⟩ := id hfr
    have hB : Bs p L g d'.v = Bs p L g d.v := by simp only [Bs, blocks_frame hfr]
    have hE : toE d' = toE d := by simp only [toE, hsc, hep, hep']
    rw [h1]
    by_cases hi : inRound d'.site.pc = true
    · obtain ⟨hi0, hsv⟩ := hin hi
      simp only [RvAt, hi0, ↓reduceIte] at hr
      obtain ⟨r, hr1, hr2, rfl⟩ := hr
      refine ⟨2 * r + sv d'.site, ?_, ?_, ?_, fun _ => by rw [hukw, hsc]; exact hu huk0⟩
      · rw [hsv, h2]; split <;> omega
      · simp only [RvAt, hi, ↓reduceIte]
        exact ⟨r, by rw [hB]; exact hr1, by rw [htr, hB]; exact hr2, rfl⟩
      · rw [hE, hsv, h2]
        have e1 : nv + (if d.site.isRvote = true then 1 else 0) -
            (2 * r + (sv d.site + if d.site.isRvote = true then 1 else 0)) =
            nv - (2 * r + sv d.site) := by split <;> omega
        rw [e1]; exact hFE
    · have ht' : tailR d'.site = true := by simpa [hi] using hrt'
      obtain ⟨ht0, hnr, -⟩ := htl ht'
      have hi0 : inRound d.site.pc = false := by
        cases h : inRound d.site.pc
        · rfl
        · exact absurd ⟨h, ht0⟩ hnb
      rw [h2, hnr]
      simp only [RvAt, hi0, ht0, Bool.false_eq_true, ↓reduceIte] at hr
      have hi' : inRound d'.site.pc = false := by simpa using hi
      refine ⟨rv, by omega, ?_, by rw [hE]; simpa using hFE,
        fun _ => by rw [hukw, hsc]; exact hu huk0⟩
      simp only [RvAt, hi', ht', Bool.false_eq_true, ↓reduceIte, hB]
      exact hr

/-- **The entry of the rounds**: none when the tile has fewer than two blocks, else round 0. -/
theorem cfits_enter {d d' : D} {e : Event} (hs : d.site = .nb 1) (hF : CFits p L g d ns nv)
    (hev : Ev p L g d e) (hn : succ p L g d e = some (some d')) :
    CFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) := by
  obtain ⟨h1, h2⟩ := ev_counts hev
  obtain ⟨s, v, k⟩ := d
  simp only at hs
  subst hs
  simp only [epi, Epilogue.Site.shfl, Epilogue.Site.ballot, Site.isRvote, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte] at h1 h2
  rw [h1, h2]
  obtain ⟨rv, hle, hr, hFE, hu⟩ := hF
  rw [rvAt_out rfl rfl] at hr
  simp only [Site.late, Bool.false_eq_true, ↓reduceIte] at hr
  subst hr
  have hu' := hu rfl
  simp only [succ, enterRounds, D.ite, Option.some.injEq] at hn
  subst hn
  have hB := toSigned_r32 (blocks p L g v)
  split <;> rename_i hb
  · rw [scmpi_lt2, decide_eq_true_eq] at hb
    refine ⟨0, Nat.zero_le _, ?_, hFE, fun _ => hu'⟩
    simp only [RvAt, D.mk', show inRound (Site.pc .farr0) = false from rfl,
      show tailR Site.farr0 = true from rfl, Bool.false_eq_true, ↓reduceIte, rvN, Bs, hb]
  · rw [scmpi_lt2, decide_eq_true_eq] at hb
    refine ⟨0, Nat.zero_le _, ?_, hFE, fun _ => hu'⟩
    simp only [RvAt, D.mk', show inRound (Site.pc (.rbar 0)) = true from rfl, ↓reduceIte]
    refine ⟨0, ?_, ?_, rfl⟩
    · simp only [Bs, blocks_trip]; push_cast; omega
    · simp only [Bs, blocks_trip, neg32_eq]; exact congrArg i32 (by push_cast; ring)

/-- **The end of a round**: another round, or the final stage after the last. -/
theorem cfits_rend {d d' : D} {e : Event} (hs : d.site = .rarr 1 1) (hF : CFits p L g d ns nv)
    (hev : Ev p L g d e) (hn : succ p L g d e = some (some d')) :
    CFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) := by
  obtain ⟨h1, h2⟩ := ev_counts hev
  obtain ⟨s, v, k⟩ := d
  simp only at hs
  subst hs
  simp only [epi, Epilogue.Site.shfl, Epilogue.Site.ballot, Site.isRvote, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte] at h1 h2
  rw [h1, h2]
  obtain ⟨rv, hle, hr, hFE, hu⟩ := hF
  simp only [RvAt, show inRound (Site.pc (.rarr 1 1)) = true from rfl, ↓reduceIte] at hr
  obtain ⟨r, hr1, hr2, rfl⟩ := hr
  have hu' := hu rfl
  have hsv : sv (.rarr 1 1) = 2 := rfl
  rw [hsv] at hle hFE
  simp only [succ, roundEnd, D.ite, Option.some.injEq] at hn
  subst hn
  have hB := toSigned_r32 (blocks p L g v)
  simp only [Bs] at hr1 hr2 hB
  rw [hr2, i32_addi]
  split <;> rename_i hne
  · have := (ne_m1 (by omega) (by omega)).mp hne
    have e1 : nv + 0 - 2 * (r + 1) = nv - (2 * r + 2) := by omega
    refine ⟨2 * (r + 1), by omega, ?_, by rw [e1]; exact hFE, fun _ => hu'⟩
    simp only [RvAt, D.mk', show inRound (Site.pc (.rbar 0)) = true from rfl, ↓reduceIte]
    refine ⟨r + 1, ?_, ?_, rfl⟩
    · simp only [Bs, blocks_trip]; push_cast; omega
    · simp only [Bs, blocks_trip]; exact congrArg i32 (by push_cast; ring)
  · have : ¬ ((r : Int) - toSigned 32 (r32 (blocks p L g v)) + 1 ≠ -1) := fun h' =>
      hne ((ne_m1 (by omega) (by omega)).mpr h')
    have e1 : nv + 0 - 2 * (r + 1) = nv - (2 * r + 2) := by omega
    refine ⟨2 * (r + 1), by omega, ?_, by rw [e1]; exact hFE, fun _ => hu'⟩
    simp only [RvAt, D.mk', show inRound (Site.pc .farr0) = false from rfl,
      show tailR Site.farr0 = true from rfl, Bool.false_eq_true, ↓reduceIte, Bs, blocks_trip,
      rvN]
    split <;> omega

/-- **The rounds' block count is the picked tile's.** -/
theorem bs_ref {d : D} {R : Nat} {bal : BitVec 64}
    (hC : Epilogue.ChosenVals p L g R bal (toE d) ns nv)
    (h0 : d.v.sc.c0 = Epilogue.qv p (chosen d.v.sc))
    (h1 : d.v.sc.c1 = Epilogue.qv p (addi (chosen d.v.sc) 1))
    (hu : d.v.ukw = ukv p (chosen d.v.sc)) : Bs p L g d.v = Bs p L g (refV p L g R bal) := by
  obtain ⟨-, ht, hgx, hcur, hbal, hpv, hnt, -, -⟩ := hC
  have ht' : d.v.sc.tot = _ := ht
  have hgx' : d.v.sc.gx = _ := hgx
  have hcur' : d.v.sc.cur = _ := hcur
  have hbal' : d.v.sc.bal = _ := hbal
  have hpv' : d.v.sc.pv = _ := hpv
  have hnt' : d.v.sc.nt = _ := hnt
  have hch : chosen d.v.sc = chosen (Epilogue.chosenD p (g / L.block) R bal) := by
    simp only [chosen, Epilogue.chosenD, hbal', hgx']
  simp only [Bs, blocks, rowOff, coords, refV, hu, h0, h1, hch, ht', hcur', hpv', hnt',
    Epilogue.chosenD]

/-- The second pass after the final stage holds the reference values. -/
theorem cfits_pass2 {d : D} (hrt : tailR d.site = true) (hep : epi d.site = .ready 0)
    (huk : d.site.hasUk = true) (hF : CFits p L g d ns nv) :
    CFits p L g (passStart p L g true d) ns nv := by
  obtain ⟨rv, hle, hr, hFE, hu⟩ := hF
  have hi0 : inRound d.site.pc = false := by
    simp only [tailR, inRound, Bool.and_eq_true, decide_eq_true_eq] at hrt ⊢
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
  simp only [RvAt, hi0, hrt, Bool.false_eq_true, ↓reduceIte] at hr
  have hFE' := hFE
  simp only [Epilogue.Fits, toE, hep] at hFE'
  obtain ⟨R, bal, hC, h0, h1⟩ := hFE'
  have hB := bs_ref hC h0 h1 (hu huk)
  have hP := Epilogue.fits_pass2 hC
  have hrv : ∃ R bal, Picked p L g R bal ∧ rv = rvN (Bs p L g (refV p L g R bal)) :=
    ⟨R, bal, hC.1, hr.trans (congrArg rvN hB)⟩
  by_cases hb : scmp .gt .s (Epilogue.laneW L g) (Epilogue.paramW p.batch) = true
  · simp only [hb, ↓reduceIte] at hP
    simp only [passStart, D.ite, hb, ↓reduceIte]
    refine ⟨rv, hle, (rvAt_out rfl rfl).mpr (by
      simp only [scAt, D.mk', Site.late, Epilogue.Scan.late, ↓reduceIte]; exact hrv), hP,
      fun h => absurd h Bool.false_ne_true⟩
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hP
    simp only [passStart, D.ite, hb, ↓reduceIte, Bool.false_eq_true]
    refine ⟨rv, hle, (rvAt_out rfl rfl).mpr (by
      simp only [scAt, D.mk', Site.late, Epilogue.Scan.late, ↓reduceIte]; exact hrv), hP,
      fun h => absurd h Bool.false_ne_true⟩

/-- **The end of the final stage and the LSE stores**: the LSE stores, then the second pass. -/
theorem cfits_fin {d d' : D} {e : Event} (hs : d.site.fin = true) (hF : CFits p L g d ns nv)
    (hev : Ev p L g d e) (hn : succ p L g d e = some (some d')) :
    CFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) := by
  obtain ⟨h1, h2⟩ := ev_counts hev
  obtain ⟨s, v, k⟩ := d
  have hs0 := hs
  simp only [Site.fin, Bool.or_eq_true, beq_iff_eq] at hs0
  have hep : epi s = .ready 0 := by rcases hs0 with (rfl | rfl) | rfl <;> rfl
  have hrt : tailR s = true := by rcases hs0 with (rfl | rfl) | rfl <;> rfl
  have hhu : s.hasUk = true := by rcases hs0 with (rfl | rfl) | rfl <;> rfl
  have hrv : s.isRvote = false := by rcases hs0 with (rfl | rfl) | rfl <;> rfl
  simp only [hep, hrv, Epilogue.Site.shfl, Epilogue.Site.ballot, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte] at h1 h2
  rw [h1, h2]
  have hp : CFits p L g (passStart p L g true ⟨s, v, k⟩) ns nv := cfits_pass2 hrt hep hhu hF
  have hq : ∀ st : Fin 2, CFits p L g (D.mk' (.lse st) v) ns nv := by
    intro st
    refine cfits_keep (d := ⟨s, v, k⟩) rfl (by fin_cases st <;> exact hep.symm) (fun rv h => ?_)
      (fun _ => hhu) hF
    have hi0 : inRound s.pc = false := by rcases hs0 with (rfl | rfl) | rfl <;> rfl
    simp only [RvAt, hi0, hrt, Bool.false_eq_true, ↓reduceIte] at h
    fin_cases st
    · simp only [RvAt, D.mk', show inRound (Site.pc (.lse 0)) = false from rfl,
        show tailR (Site.lse 0) = true from rfl, ↓reduceIte, Bool.false_eq_true]
      exact h
    · simp only [RvAt, D.mk', show inRound (Site.pc (.lse 1)) = false from rfl,
        show tailR (Site.lse 1) = true from rfl, ↓reduceIte, Bool.false_eq_true]
      exact h
  rcases hs0 with (rfl | rfl) | rfl
  · simp only [succ, afterFinal, D.ite] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      split
      · split
        · exact hp
        · exact hq 1
      · exact hq 0
    · cases hn
  · simp only [succ, afterLse, D.ite] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      split
      · exact hp
      · exact hq 1
    · cases hn
  · simp only [succ, afterLse, Option.some.injEq] at hn
    subst hn
    exact hp

/-- **A step on an event that returns what the reference says keeps the reference values**,
with the counts its event adds. -/
theorem cfits_next (hc : ctaR p L g = Epilogue.ctaW L g) {d d' : D} {e : Event}
    (hF : CFits p L g d ns nv) (hE : CExpect p L g d ns e) (hev : Ev p L g d e)
    (hn : succ p L g d e = some (some d')) :
    CFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) := by
  by_cases hs : d.site.sched = true
  · exact cfits_sched hc hs hF hE hev hn
  by_cases hq : d.site.quiet = true
  · exact cfits_quiet hq hF hev hn
  by_cases hu : d.site = .uk
  · exact cfits_uk hu hF hE hev hn
  by_cases he : d.site = .nb 1
  · exact cfits_enter he hF hev hn
  by_cases hr : d.site = .rarr 1 1
  · exact cfits_rend hr hF hev hn
  by_cases hf : d.site.fin = true
  · exact cfits_fin hf hF hev hn
  have hrt : (inRound d.site.pc || tailR d.site) = true ∨ d.site = .exit false ∨
      d.site = .exit true := by
    obtain ⟨s, v, k⟩ := d
    simp only at hs hq hu he hr hf ⊢
    cases s with
    | word k | down k | total k => cases k <;> simp_all [Site.sched]
    | up k j => cases k <;> simp_all [Site.sched]
    | vote l | pre l | tiles l => cases l <;> simp_all [Site.sched]
    | wend l | barEnd l => cases l <;> simp_all [Site.quiet]
    | exit l => cases l <;> simp
    | arr j => fin_cases j <;> simp_all [Site.sched, Site.quiet]
    | nb j => fin_cases j <;> simp_all [Site.quiet]
    | rbar st | rscale st | rvote st | rwait st | fbar st | fsum st | fmax st | farr st
      | fence st | lse st => fin_cases st <;> simp_all [Site.fin] <;> decide
    | rarr st j | fw st j | fdone st j =>
      fin_cases st <;> fin_cases j <;> simp_all [Site.fin] <;> decide
    | rld st c | rldw st c | rst st c => fin_cases st <;> fin_cases c <;> decide
    | fld st j | fwl st j => fin_cases st <;> fin_cases j <;> decide
    | fst st j h => fin_cases st <;> fin_cases j <;> fin_cases h <;> decide
    | _ => simp_all [Site.sched, Site.quiet] <;> decide
  rcases hrt with hrt | hx | hx
  · refine cfits_rt hrt ?_ (by simpa using hf) hF hev hn
    obtain ⟨s, v, k⟩ := d
    simp only at he hr ⊢
    cases s <;> simp only [Site.special] <;> simp_all
  all_goals obtain ⟨s, v, k⟩ := d; simp only at hx; subst hx; simp [succ] at hn

end
end PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
