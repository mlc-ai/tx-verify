-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.Common.FollowView
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Corr
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
import Kernels.TmlFa4Fwd.Proof.Top.JRView
public import Lemmas.Kernel.Safety.StateInvU
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Places

@[expose] public section

/-! # The softmax warps' barrier schedule

A softmax lane meets, in order: barrier 0 (the startup's), barrier 2 (`bar1`), its stage's named
barrier and its named barrier with its correction warp in the first round (`bsync false`,
`narr .first`), the same two per biased round (`bsync true`, `narr .bias`), the named barrier with
the correction warp per plain round (`narr .plain`) and at the end (`finarr`), and the arrival at
barrier 2 (`barEnd true`); without a tile, barrier 0, barrier 2 and the arrival. So the `k`-th
barrier event is `softB` of `k` and the CTA's tile (`tileS`: none, or its biased and plain round
counts). The ordinals are closed forms of `Softmax.RefQ` (`soft_ord`), the round counts of a round
or of the final stores are the tile's (`nB_ref`, `nP_ref` from `SFits`), and at the second pass
the stage barrier's and the named barrier's counts still say the tile's rounds (`SLate`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (Picked chosen)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (ukv)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### The tile of the CTA -/

/-- The softmax values of the tile the first pass picked after its scan ended at round `R` with
ballot `bal`: the scan state and the used-K length. -/
def refVS (p : Params) (L : Launch) (g R : Nat) (bal : BitVec 64) : V :=
  let c := Epilogue.chosenD p (g / L.block) R bal
  { sc := { c with c0 := Epilogue.qv p (chosen c), c1 := Epilogue.qv p (addi (chosen c) 1) },
    ukw := ukv p (chosen c) }

/-- **The rounds' counts are the picked tile's.** -/
theorem nBP_ref {d : D} {ns nv R : Nat} {bal : BitVec 64}
    (hC : Epilogue.ChosenVals p L g R bal (SmWarp.toE d) ns nv)
    (h0 : d.v.sc.c0 = Epilogue.qv p (chosen d.v.sc))
    (h1 : d.v.sc.c1 = Epilogue.qv p (addi (chosen d.v.sc) 1))
    (hu : d.v.ukw = ukv p (chosen d.v.sc)) :
    nB p L g d.v = nB p L g (refVS p L g R bal) ∧ nP p L g d.v = nP p L g (refVS p L g R bal) := by
  obtain ⟨-, ht, hgx, hcur, hbal, hpv, hnt, -, -⟩ := hC
  have ht' : d.v.sc.tot = _ := ht
  have hgx' : d.v.sc.gx = _ := hgx
  have hcur' : d.v.sc.cur = _ := hcur
  have hbal' : d.v.sc.bal = _ := hbal
  have hpv' : d.v.sc.pv = _ := hpv
  have hnt' : d.v.sc.nt = _ := hnt
  have hch : chosen d.v.sc = chosen (Epilogue.chosenD p (g / L.block) R bal) := by
    simp only [chosen, Epilogue.chosenD, hbal', hgx']
  constructor <;>
  simp only [nB, nP, r169, r299, r431, r166, r168, r165, r1808, rowOff, Mma.coords, refVS, hu,
    h0, h1, hch, ht', hcur', hpv', hnt', Epilogue.chosenD]

open Classical in
/-- **The CTA's tile for the softmax warps**: none when the first pass picked no tile, else its
biased and plain round counts. -/
def tileS (p : Params) (L : Launch) (g : Nat) : Option (Nat × Nat) :=
  if h : ∃ R bal, Picked p L g R bal then
    some ((nB p L g (refVS p L g h.choose h.choose_spec.choose)).toNat,
      (nP p L g (refVS p L g h.choose h.choose_spec.choose)).toNat)
  else none

theorem tileS_of {R : Nat} {bal : BitVec 64} (h : Picked p L g R bal) :
    tileS p L g =
      some ((nB p L g (refVS p L g R bal)).toNat, (nP p L g (refVS p L g R bal)).toNat) := by
  have he : ∃ R bal, Picked p L g R bal := ⟨R, bal, h⟩
  simp only [tileS, he, dite_true]
  obtain ⟨rfl, rfl⟩ := he.choose_spec.choose_spec.unique h
  rfl

theorem tileS_none (h : ¬ ∃ R bal, Picked p L g R bal) : tileS p L g = none := by
  simp only [tileS, h, dite_false]

/-- The rounds' counts of the picked tile are the same on two lanes of one warp. -/
theorem nBP_warp {h : Nat} (hc : g / L.block = h / L.block)
    (hw : g % L.block / 32 = h % L.block / 32) {R : Nat} {bal : BitVec 64} :
    nB p L g (refVS p L g R bal) = nB p L h (refVS p L h R bal) ∧
      nP p L g (refVS p L g R bal) = nP p L h (refVS p L h R bal) := by
  constructor <;>
  simp only [nB, nP, r169, r299, r431, r166, r168, r165, r1808, rowOff, Mma.coords, refVS,
    Epilogue.chosenD, Epilogue.ctaW, stg, warpW, hc, hw]

/-- **Two lanes of one warp see one tile.** -/
theorem tileS_warp {h : Nat} (hc : g / L.block = h / L.block)
    (hw : g % L.block / 32 = h % L.block / 32) : tileS p L g = tileS p L h := by
  by_cases he : ∃ R bal, Picked p L g R bal
  · obtain ⟨R, bal, hP⟩ := he
    obtain ⟨e1, e2⟩ := nBP_warp (p := p) hc hw (R := R) (bal := bal)
    rw [tileS_of hP, tileS_of (Epilogue.Picked.cta hc hP), e1, e2]
  · have he' : ¬ ∃ R bal, Picked p L h R bal := fun ⟨R, bal, hP⟩ =>
      he ⟨R, bal, Epilogue.Picked.cta hc.symm hP⟩
    rw [tileS_none he, tileS_none he']

/-! ### The ordinals at the barrier sites -/

/-- The counts of the barrier classes before a softmax site, by `RefQ`'s places: the counts
outside the rounds, per biased round and per plain round. -/
theorem soft_cnt (b : Bool) : ([Site.bar1, .bsync false, .narr .first, .bsync true, .narr .bias,
    .narr .plain, .finarr, .barEnd true, .barEnd false].map fun s =>
      ((ptsOf b .bar2).countP (before s), (ptsOf b .nb).countP (before s),
        (ptsOf b .sb).countP (before s))) =
      [(0, 0, 0), (1, 0, 0), (1, 0, 1), (1, 1, 1), (1, 1, 2), (1, 1, 1), (1, 1, 1), (1, 2, 1),
        (1, 0, 0)] ∧
    ((ptsOf b .bar2).countP inBias, (ptsOf b .bar2).countP inPlain, (ptsOf b .nb).countP inBias,
      (ptsOf b .nb).countP inPlain, (ptsOf b .sb).countP inBias, (ptsOf b .sb).countP inPlain) =
      (0, 0, 1, 1, 1, 0) := by
  cases b <;> decide +kernel

/-- Where the barrier sites are: before the rounds, in a biased round, in a plain round. -/
theorem soft_reg : [Site.bar1, .bsync false, .narr .first, .barEnd false].all preR = true ∧
    [Site.bsync true, .narr .bias].all (fun s => inBias s.pos) = true ∧
    inPlain (Site.narr .plain).pos = true := by
  decide +kernel

/-- The sum of the role's barrier classes. -/
abbrev sbar (c : Softmax.Cnt → Nat) : Nat := c .bar2 + c .nb + c .sb

set_option maxHeartbeats 4000000 in
/-- **The softmax warps' barrier classes at their barrier sites.** -/
theorem soft_ord {d : D} {c : Softmax.Cnt → Nat} {rb rp : Nat} (hQ : RefQ p L g d c rb rp) :
    (d.site = .bar1 → sbar c = 0) ∧ (d.site = .bsync false → sbar c = 1) ∧
    (d.site = .narr .first → sbar c = 2) ∧ (d.site = .bsync true → sbar c = 3 + 2 * rb) ∧
    (d.site = .narr .bias → sbar c = 4 + 2 * rb) ∧
    (d.site = .narr .plain → sbar c = 3 + 2 * rb + rp) ∧
    (d.site = .finarr → sbar c = 3 + 2 * rb + rp ∧ c .sb = 1 + rb ∧ c .nb = 1 + rb + rp) ∧
    (d.site = .barEnd true → sbar c = 4 + 2 * rb + rp ∧ c .sb = 1 + rb ∧ c .nb = 2 + rb + rp) ∧
    (d.site = .barEnd false → sbar c = 1) := by
  have c0 := hQ.cnt .bar2 rfl
  have c1 := hQ.cnt .nb rfl
  have c2 := hQ.cnt .sb rfl
  have hpre := hQ.pre
  have hbias := hQ.bias
  obtain ⟨t1, t2⟩ := soft_cnt (lz L g)
  simp only [List.map, List.cons.injEq, Prod.mk.injEq, and_true] at t1 t2
  obtain ⟨s, v, k, acc⟩ := d
  simp only [passed] at c0 c1 c2
  obtain ⟨r1, r2, r3⟩ := soft_reg
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at r1 r2
  dsimp only at hpre hbias c0 c1 c2
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun h => ?_, fun h => ?_⟩
  all_goals subst h
  all_goals simp only [sbar, c0, c1, c2, t1, t2]
  · obtain ⟨rfl, rfl⟩ := hpre r1.1; omega
  · obtain ⟨rfl, rfl⟩ := hpre r1.2.1; omega
  · obtain ⟨rfl, rfl⟩ := hpre r1.2.2.1; omega
  · obtain ⟨rfl, -⟩ := hbias r2.1; omega
  · obtain ⟨rfl, -⟩ := hbias r2.2; omega
  · omega
  · omega
  · omega
  · obtain ⟨rfl, rfl⟩ := hpre r1.2.2.2; omega

/-! ### The rounds at the second pass -/

/-- The second pass's sites and the end after it. -/
def _root_.PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Site.late : Site → Bool
  | .word k | .down k | .up k _ | .total k => k.late
  | .vote l | .pre l | .tiles l | .wend l | .barEnd l | .exit l => l
  | _ => false

/-- The only site that moves into the second pass is the final arrival. -/
theorem late_entryS (b : Bool) : allSites.all (fun s => (nexts b s).all fun s' =>
    !s'.late || s.late || s == .finarr) = true := by
  cases b <;> decide +kernel

set_option maxHeartbeats 4000000 in
/-- No event of the second pass is at the stage's or the correction warps' named barrier, and the
final arrival only at the latter. -/
theorem late_nosb {d : D} {e : Event} (hw : g % L.block / 32 < 8) (hev : Softmax.Ev p L g d e)
    (hs : d.site.late = true ∨ d.site = .finarr) :
    cls L g (.soft .sb) e = false ∧ (d.site.late = true → cls L g (.soft .nb) e = false) ∧
      (d.site = .finarr → cls L g (.soft .nb) e = true) := by
  obtain ⟨h0, h1⟩ := soft_nb_range (L := L) hw
  have f1 : (Softmax.nbW L g).toNat ≠ 2 := by omega
  obtain ⟨s, v, k, acc⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s
  all_goals simp [Site.late] at hs
  all_goals simp only [Softmax.Ev, Epilogue.Ev, Site.toE] at hev
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals subst_vars
  all_goals simp [cls, Softmax.cls, Softmax.Cnt.pointed, hw, Site.late]
  all_goals (cases hst : stg L g <;> simp only [hst, Bool.false_eq_true, ↓reduceIte] at * <;>
    omega)

/-- **The softmax warps' barrier counts at the second pass**: the picked tile's rounds (after an
undefined-behaviour event, nothing). -/
def SLate (p : Params) (L : Launch) (g : Nat) : (thread p L g).D → Prop
  | (.inr ⟨.softmax, d⟩, n) => n .ub = 0 → d.site.late = true →
      ∃ R bal, Picked p L g R bal ∧
        n (.soft .sb) = 1 + (nB p L g (refVS p L g R bal)).toNat ∧
        n (.soft .nb) = 2 + (nB p L g (refVS p L g R bal)).toNat +
          (nP p L g (refVS p L g R bal)).toNat
  | _ => True

theorem done_toNat {r : Nat} {n : Int} (h : Done r n) : n.toNat = r := by
  rcases h with h | ⟨rfl, h⟩ <;> omega

set_option maxHeartbeats 8000000 in
/-- **Every state of a lane keeps `SLate`.** -/
theorem soft_late (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hg : g < L.threads) :
    ∀ k σ, Frame.NoUbBefore X g k → Frame.stateAt (thread p L) X g k = some (some σ) →
        SLate p L g σ := by
  refine Frame.RoleTable.stateInvU (T := table p L) (S := fun g => g < L.threads)
    (fun g hg => thread_sound hp hg) hX (table_shape_of hp hFw)
    (table_followed hp hX hFw) (P := fun g σ => SLate p L g σ) hg trivial ?_
  rintro ⟨σ1, n⟩ e ⟨σ1', n'⟩ hJ hi hev hB hn hJ'
  obtain ⟨h1, rfl⟩ := Code.counted_next_some (C := glued p L g) hn
  rcases σ1 with s | ⟨i, d⟩
  · simp only [glued, Code.glue, Startup.code] at h1
    cases hsu : Startup.succ L g s e with
    | none => rw [hsu] at h1; simp at h1
    | some o =>
      cases o with
      | none => rw [hsu] at h1; simp at h1
      | some s' =>
        rw [hsu] at h1
        simp only [Option.map_some, Option.some.injEq] at h1
        subst h1
        unfold Code.enter
        split
        · rename_i r _
          cases r <;> first | trivial | (intro _ h; simp [Site.late] at h)
        · trivial
  · simp only [glued, Code.glue] at h1
    cases hr : (frag p L g i).next d e with
    | none => rw [hr] at h1; simp at h1
    | some o =>
      cases o with
      | none => rw [hr] at h1; simp at h1
      | some d1 =>
        rw [hr] at h1
        simp only [Option.map_some, Option.some.injEq] at h1
        subst h1
        cases i with
        | softmax =>
          intro hub hl
          have hub0 : n .ub = 0 := Nat.eq_zero_of_le_zero
            (hub ▸ Nat.le_add_right (n .ub) _)
          have hc : Softmax.Ev p L g d e := hev.1
          have hw : g % L.block / 32 < 8 := hi.2
          have hJs : SmWarp.Ref p L (Prologue.warpIndex L g) g (.inr ⟨.softmax, d⟩, n) := by
            have := hJ
            simp only [table, JR_eq] at this
            split_ifs at this
            · exact this
            · unfold RefAll at this
              split_ifs at this <;> simp_all [Mma.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref]
          obtain ⟨⟨c, ⟨⟨rb, rp, hQ⟩⟩, hL⟩, hF⟩ := hJs.2 hub0
          have hsc := Softmax.Control.succ_places (d := d) hr
          have hB' := hB hub0
          rcases hsc with ⟨hs', -⟩ | hM
          · change d1.site = d.site at hs'
            rw [hs'] at hl
            obtain ⟨R, bal, hP, h2, h3⟩ := hB' hl
            obtain ⟨k1, -, -⟩ := late_nosb hw hc (.inl hl)
            have k2 := (late_nosb hw hc (.inl hl)).2.1 hl
            exact ⟨R, bal, hP, by simp only [Code.bump, k1]; simpa using h2,
              by simp only [Code.bump, k2]; simpa using h3⟩
          · by_cases hdl : d.site.late = true
            · obtain ⟨R, bal, hP, h2, h3⟩ := hB' hdl
              obtain ⟨k1, k2, -⟩ := late_nosb hw hc (.inl hdl)
              exact ⟨R, bal, hP, by simp only [Code.bump, k1]; simpa using h2,
                by simp only [Code.bump, k2 hdl]; simpa using h3⟩
            have hfa : d.site = .finarr := by
              have h := late_entryS (lz L g)
              rw [List.all_eq_true] at h
              have h' := h d.site (mem_allSites _)
              rw [List.all_eq_true] at h'
              have := h' d1.site hM.1
              simp only [hl, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at this
              simp only [Bool.not_eq_true] at hdl
              rcases this with h | h
              · simp [hdl] at h
              · exact h
            obtain ⟨k1, -, k3⟩ := late_nosb hw hc (.inr hfa)
            have hfin := hQ.fin (by change finR d.site = true; rw [hfa]; decide)
            obtain ⟨-, -, -, -, -, -, f7, -, -⟩ := soft_ord hQ
            obtain ⟨-, f2, f3⟩ := f7 hfa
            simp only at f2 f3
            obtain ⟨hFE, hu⟩ := hF
            have hep : SmWarp.epi d.site = .ready 0 := by rw [hfa]; rfl
            have huk : d.site.hasUk = true := by rw [hfa]; rfl
            simp only [Epilogue.Fits, SmWarp.toE, show d.scheduler.site = d.site from rfl,
                hep] at hFE
            obtain ⟨R, bal, hC, h0, h1⟩ := hFE
            obtain ⟨eB, eP⟩ := nBP_ref hC h0 h1 (hu huk)
            have l1 := hL .sb rfl
            have l2 := hL .nb rfl
            refine ⟨R, bal, hC.1, ?_, ?_⟩
            · simp only [Code.bump, k1, Bool.false_eq_true, ↓reduceIte]
              rw [← eB, done_toNat hfin.1]
              omega
            · simp only [Code.bump, k3 hfa, ↓reduceIte]
              rw [← eB, ← eP, done_toNat hfin.1, done_toNat hfin.2]
              omega
        | _ => trivial

/-! ### The schedule -/

/-- **The softmax warps' barrier schedule**: the operands of the `k`-th barrier event of a lane
of the CTA's tile `T` (its biased and plain round counts). -/
def softB (L : Launch) (g : Nat) (T : Option (Nat × Nat)) (k : Nat) :
    Nat × Option Nat × BarMode :=
  if k = 0 then (0, none, .sync) else if k = 1 then (2, some 416, .sync) else
  match T with
  | none => (2, some 416, .arrive)
  | some (B, P) =>
    if k ≤ 3 + 2 * B then
      if k % 2 = 0 then (if stg L g then 12 else 11, some 128, .sync)
      else ((nbW L g).toNat, some 64, .arrive)
    else if k ≤ 4 + 2 * B + P then ((nbW L g).toNat, some 64, .arrive)
    else (2, some 416, .arrive)

theorem softB_sb {B P k : Nat} (h1 : 2 ≤ k) (h2 : k ≤ 3 + 2 * B) (h3 : k % 2 = 0) :
    softB L g (some (B, P)) k = (if stg L g then 12 else 11, some 128, .sync) := by
  have e0 : k ≠ 0 := by omega
  have e1 : k ≠ 1 := by omega
  simp only [softB, e0, e1, h2, h3, ↓reduceIte]

theorem softB_nb {B P k : Nat} (h1 : 2 ≤ k) (h2 : k ≤ 4 + 2 * B + P)
    (h3 : k ≤ 3 + 2 * B → k % 2 = 1) :
    softB L g (some (B, P)) k = ((nbW L g).toNat, some 64, .arrive) := by
  have e0 : k ≠ 0 := by omega
  have e1 : k ≠ 1 := by omega
  by_cases h : k ≤ 3 + 2 * B
  · have e2 : k % 2 ≠ 0 := by have := h3 h; omega
    simp only [softB, e0, e1, h, e2, ↓reduceIte]
  · simp only [softB, e0, e1, h, h2, ↓reduceIte]

theorem softB_end {B P k : Nat} (h2 : 4 + 2 * B + P < k) :
    softB L g (some (B, P)) k = (2, some 416, .arrive) := by
  have e0 : k ≠ 0 := by omega
  have e1 : k ≠ 1 := by omega
  have e2 : ¬ k ≤ 3 + 2 * B := by omega
  have e3 : ¬ k ≤ 4 + 2 * B + P := by omega
  simp only [softB, e0, e1, e2, e3, ↓reduceIte]

set_option maxHeartbeats 8000000 in
/-- **A softmax lane's barrier event has its ordinal's operands in the schedule.** -/
theorem soft_sched {d : D} {n : Cls → Nat} {c : Softmax.Cnt → Nat} {rb rp ns nv : Nat}
    {pc id : Nat} {cnt : Option Nat} {mode : BarMode} (hQ : RefQ p L g d c rb rp)
    (hL : SmWarp.Linked n c) (hF : SmWarp.SFits p L g d ns nv)
    (hev : Softmax.Ev p L g d ⟨pc, .bar id cnt mode⟩)
    (hB : n (.mma .bar) = 1 + n (.soft .bar2) + n (.soft .nb) + n (.soft .sb))
    (hLate : d.site.late = true → ∃ R bal, Picked p L g R bal ∧
        n (.soft .sb) = 1 + (nB p L g (refVS p L g R bal)).toNat ∧
        n (.soft .nb) = 2 + (nB p L g (refVS p L g R bal)).toNat +
          (nP p L g (refVS p L g R bal)).toNat) :
    (id, cnt, mode) = softB L g (tileS p L g) (n (.mma .bar)) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9⟩ := soft_ord hQ
  have l0 := hL .bar2 rfl
  have l1 := hL .nb rfl
  have l2 := hL .sb rfl
  simp only [sbar] at o1 o2 o3 o4 o5 o6 o7 o8 o9
  -- the tile at a site of the rounds' region
  have tile : SmWarp.epi d.site = .ready 0 → d.site.hasUk = true →
      ∃ R bal, Picked p L g R bal ∧ nB p L g d.v = nB p L g (refVS p L g R bal) ∧
        nP p L g d.v = nP p L g (refVS p L g R bal) := by
    intro hep huk
    obtain ⟨hFE, hu⟩ := hF
    simp only [Epilogue.Fits, SmWarp.toE, show d.scheduler.site = d.site from rfl, hep] at hFE
    obtain ⟨R, bal, hC, h0, h1⟩ := hFE
    exact ⟨R, bal, hC.1, nBP_ref hC h0 h1 (hu huk)⟩
  obtain ⟨s, v, k, acc⟩ := d
  cases s
  case bar1 =>
    simp only [Softmax.Ev, Kind.bar.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    have hk : n (.mma .bar) = 1 := by have := o1 rfl; omega
    rw [hk]; rfl
  case bsync l =>
    simp only [Softmax.Ev, Kind.bar.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    obtain ⟨R, bal, hP, eB, -⟩ := tile rfl rfl
    rw [tileS_of hP]
    generalize nB p L g (refVS p L g R bal) = Bi at *
    generalize nP p L g (refVS p L g R bal) = Pi at *
    cases l
    · have hk : n (.mma .bar) = 2 := by have := o2 rfl; omega
      rw [hk, softB_sb (by omega) (by omega) (by omega)]
    · have hb := hQ.bias rfl
      simp only at hb
      rw [eB] at hb
      have hk : n (.mma .bar) = 4 + 2 * rb := by have := o4 rfl; omega
      rw [hk, softB_sb (by omega) (by omega) (by omega)]
  case narr r =>
    simp only [Softmax.Ev, Kind.bar.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    obtain ⟨R, bal, hP, eB, eP⟩ := tile rfl rfl
    rw [tileS_of hP]
    generalize nB p L g (refVS p L g R bal) = Bi at *
    generalize nP p L g (refVS p L g R bal) = Pi at *
    cases r
    · have hk : n (.mma .bar) = 3 := by have := o3 rfl; omega
      rw [hk, softB_nb (by omega) (by omega) (by omega)]
    · have hb := hQ.bias rfl
      simp only at hb
      rw [eB] at hb
      have hk : n (.mma .bar) = 5 + 2 * rb := by have := o5 rfl; omega
      rw [hk, softB_nb (by omega) (by omega) (by omega)]
    · have hb := hQ.plain rfl
      simp only at hb
      rw [eB, eP] at hb
      obtain ⟨-, h2, -, h4⟩ := hb
      have h4' := done_toNat h4
      have hk : n (.mma .bar) = 4 + 2 * rb + rp := by have := o6 rfl; omega
      rw [hk, softB_nb (by omega) (by omega) (by omega)]
  case finarr =>
    simp only [Softmax.Ev, Kind.bar.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    obtain ⟨R, bal, hP, eB, eP⟩ := tile rfl rfl
    rw [tileS_of hP]
    generalize nB p L g (refVS p L g R bal) = Bi at *
    generalize nP p L g (refVS p L g R bal) = Pi at *
    have hf := hQ.fin rfl
    simp only at hf
    rw [eB, eP] at hf
    have f1 := done_toNat hf.1
    have f2 := done_toNat hf.2
    have hk : n (.mma .bar) = 4 + 2 * rb + rp := by have := (o7 rfl).1; omega
    rw [hk, softB_nb (by omega) (by omega) (by omega)]
  case barEnd l =>
    simp only [Softmax.Ev] at hev
    rcases hev with hk | ⟨f, hk⟩
    · simp only [Kind.bar.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      cases l
      · obtain ⟨hFE, -⟩ := hF
        have hFE' : Epilogue.Fits p L g { v.sc with site := .exit false } ns nv := hFE
        have hk : n (.mma .bar) = 2 := by have := o9 rfl; omega
        rw [tileS_none (noPicked_exit hFE' rfl), hk]
        rfl
      · obtain ⟨R, bal, hP, h2, h3⟩ := hLate rfl
        obtain ⟨h5, h6, h7⟩ := o8 rfl
        rw [tileS_of hP]
        generalize nB p L g (refVS p L g R bal) = Bi at *
        generalize nP p L g (refVS p L g R bal) = Pi at *
        have hk : n (.mma .bar) = 5 + 2 * Bi.toNat + Pi.toNat := by omega
        rw [hk, softB_end (by omega)]
    · cases hk
  all_goals simp only [Softmax.Ev, Epilogue.Ev, Site.toE] at hev
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (simp only [reduceCtorEq, Kind.tc.injEq, TcKind.commit.injEq] at *)

end
end PTX.Kernels.TmlFa4Fwd.Proof
