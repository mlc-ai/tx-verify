-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.Correction.Ledger
public import Kernels.TmlFa4Fwd.Proof.Correction.Ref
public import Kernels.TmlFa4Fwd.Proof.Correction.RefDef
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Correction.RefCases
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
import Kernels.TmlFa4Fwd.Proof.Top.JRView
public import Lemmas.Kernel.Safety.StateInvU
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

import Kernels.TmlFa4Fwd.Proof.Correction.Export.Places

@[expose] public section

/-! # The correction warps' barrier schedule

A correction lane meets, in order: the CTA barrier 0 (the startup's), barrier 2 (`bar1`), its two
named barriers with its softmax warp (`nb 0`, `nb 1`), per rescale round the two named barriers
again (`rbar 0`, `rbar 1`), the final stage's two (`fbar 0`, `fbar 1`) and the arrival at
barrier 2 (`barEnd true`); without a tile, barrier 0, barrier 2 and the arrival at barrier 2. So
the `k`-th barrier event is `corrB` of `k` and the CTA's tile (`tileC`: none, or its rescale
rounds `R`, the block count less one). Its ordinal is the barrier count of `bar_count` with the
classes' closed forms of `Correction.RefQ` (`corr_ord`), the rounds of a round or the final stage
are the tile's (`bs_ref`), and at the second pass the named-barrier count still says the tile's
rounds (`CLate`, kept along the trace: it enters from the final stage, where `RefQ` fixes the
rounds, and the second pass meets no named barrier). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp (refV rvN)
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (Picked)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### The ordinals at the barrier sites -/

/-- The sum of the role's barrier classes. -/
abbrev cbar (n : Cnt → Nat) : Nat := n .bar2 + n (.nb 0) + n (.nb 1)

set_option maxHeartbeats 4000000 in
/-- **The correction warps' barrier classes at their barrier sites**, from the counts' closed
forms: before barrier 2 none; at named barrier `k` before the rounds `1 + k`; at a round's or the
final stage's named barrier `st` after `r` rounds `3 + 2 r + st`; at the second pass's arrival
`5 + 2 r`, the named barrier 0's count being `2 + r`; without a tile, one. -/
theorem corr_ord {d : D} {n : Cnt → Nat} {r ℓ : Nat} (hQ : RefQ p L g d n r ℓ) :
    (d.site = .bar1 → cbar n = 0) ∧ (∀ k : Fin 2, d.site = .nb k → cbar n = 1 + k.val) ∧
    (∀ st : Fin 2, d.site = .rbar st → cbar n = 3 + 2 * r + st.val) ∧
    (∀ st : Fin 2, d.site = .fbar st → cbar n = 3 + 2 * r + st.val) ∧
    (d.site = .barEnd true → cbar n = 5 + 2 * r ∧ n (.nb 0) = 2 + r) ∧
    (d.site = .barEnd false → cbar n = 1) := by
  have c0 := hQ.cnt .bar2 (by simp)
  have c1 := hQ.cnt (.nb 0) (by simp)
  have c2 := hQ.cnt (.nb 1) (by simp)
  obtain ⟨s, v, k⟩ := d
  simp only at c0 c1 c2 ⊢
  refine ⟨fun h => ?_, fun kk h => ?_, fun st h => ?_, fun st h => ?_, fun h => ?_, fun h => ?_⟩
  all_goals subst h
  all_goals try fin_cases kk
  all_goals try fin_cases st
  all_goals have hr0 := hQ.pre
  all_goals simp [cbar, c0, c1, c2, passed, ptsOf, bar2Pts, nbPts, before, inRound, Site.pc,
    Site.noTile, preR] at hr0 ⊢
  all_goals omega

/-! ### The tile of the CTA -/

open Classical in
/-- **The CTA's tile for the correction warps**: none when the first pass picked no tile, else
its rescale rounds (the block count less one, none below two). -/
def tileC (p : Params) (L : Launch) (g : Nat) : Option Nat :=
  if h : ∃ R bal, Picked p L g R bal then
    some (rvN (Bs p L g (refV p L g h.choose h.choose_spec.choose)) / 2)
  else none

theorem tileC_of {R : Nat} {bal : BitVec 64} (h : Picked p L g R bal) :
    tileC p L g = some (rvN (Bs p L g (refV p L g R bal)) / 2) := by
  have he : ∃ R bal, Picked p L g R bal := ⟨R, bal, h⟩
  simp only [tileC, he, dite_true]
  obtain ⟨rfl, rfl⟩ := he.choose_spec.choose_spec.unique h
  rfl

theorem tileC_none (h : ¬ ∃ R bal, Picked p L g R bal) : tileC p L g = none := by
  simp only [tileC, h, dite_false]

/-- The rounds' block count of the picked tile is the same on every lane of a warp. -/
theorem bs_warp (hp : Pre p L m) {h : Nat} (hg : g < L.threads) (hh : h < L.threads)
    (hc : g / L.block = h / L.block) {R : Nat} {bal : BitVec 64} :
    Bs p L g (refV p L g R bal) = Bs p L h (refV p L h R bal) := by
  simp only [Bs, blocks, rowOff, coords, refV, Epilogue.chosenD, ctaR_eq hp hg, ctaR_eq hp hh,
    Epilogue.ctaW, hc]

/-- **Two lanes of one CTA see one tile.** -/
theorem tileC_cta (hp : Pre p L m) {h : Nat} (hg : g < L.threads) (hh : h < L.threads)
    (hc : g / L.block = h / L.block) : tileC p L g = tileC p L h := by
  by_cases he : ∃ R bal, Picked p L g R bal
  · obtain ⟨R, bal, hP⟩ := he
    rw [tileC_of hP, tileC_of (Epilogue.Picked.cta hc hP), bs_warp hp hg hh hc]
  · have he' : ¬ ∃ R bal, Picked p L h R bal := fun ⟨R, bal, hP⟩ =>
      he ⟨R, bal, Epilogue.Picked.cta hc.symm hP⟩
    rw [tileC_none he, tileC_none he']

/-! ### The rounds at the second pass -/

/-- The sites that move into the second pass: the last final arrival and the LSE stores. -/
theorem late_entry : allSites.all (fun s => (nexts s).all fun s' =>
    !s'.late || s.late || s == .fdone 1 1 || s == .lse 0 || s == .lse 1) = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- No event of the second pass, of the last final arrival or of an LSE store is at named
barrier 0. -/
theorem nb0_not {d : D} {e : Event} (hev : Correction.Ev p L g d e)
    (hs : d.site.late = true ∨ d.site = .fdone 1 1 ∨ d.site = .lse 0 ∨ d.site = .lse 1) :
    Correction.cls L g (.nb 0) e = false := by
  obtain ⟨h0, h1, h2, h3⟩ := corr_nb_range L g
  have e4 : 2 ≠ (Correction.nb0W L g).toNat := by omega
  obtain ⟨s, v, k⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s
  all_goals simp [Site.late] at hs
  all_goals simp only [Correction.Ev, Epilogue.Ev, Correction.Site.toE] at hev
  all_goals shape_destruct hev
  all_goals subst_vars
  all_goals simp [Correction.cls, nbOf, e4]

/-- **The correction warps' named-barrier count at the second pass**: the picked tile's rounds
plus two (after an undefined-behaviour event, nothing). -/
def CLate (p : Params) (L : Launch) (g : Nat) : (thread p L g).D → Prop
  | (.inr ⟨.correction, d⟩, n) => n .ub = 0 → d.site.late = true →
      ∃ R bal, Picked p L g R bal ∧ 2 ≤ n (.corr (.nb 0)) ∧
        2 * (n (.corr (.nb 0)) - 2) = rvN (Bs p L g (refV p L g R bal))
  | _ => True

set_option maxHeartbeats 8000000 in
/-- **Every state of a lane keeps `CLate`.** -/
theorem corr_late (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hg : g < L.threads) :
    ∀ k σ, Frame.NoUbBefore X g k → Frame.stateAt (thread p L) X g k = some (some σ) →
        CLate p L g σ := by
  refine Frame.RoleTable.stateInvU (T := table p L) (S := fun g => g < L.threads)
    (fun g hg => thread_sound hp hg) hX (table_shape_of hp hFw)
    (table_followed hp hX hFw) (P := fun g σ => CLate p L g σ) hg trivial ?_
  rintro ⟨σ1, n⟩ e ⟨σ1', n'⟩ hJ hi hev hB hn hJ'
  obtain ⟨h1, rfl⟩ := Code.counted_next_some (C := glued p L g) hn
  rcases σ1 with s | ⟨i, d⟩
  · -- from the startup: the role's first state is not in the second pass
    simp only [glued, Code.glue, Startup.code] at h1
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
        | correction =>
          intro hub hl
          have hub0 : n .ub = 0 := Nat.eq_zero_of_le_zero
            (hub ▸ Nat.le_add_right (n .ub) _)
          have hJc : CorrWarp.Ref p L (Prologue.warpIndex L g) g
              (.inr ⟨.correction, d⟩, n) := by
            have := hJ
            simp only [table, JR_eq] at this
            split_ifs at this
            · simp [SmWarp.Ref] at this
            · unfold RefAll at this
              split_ifs at this <;> simp_all [Mma.Ref, Epilogue.Ref, LdWarp.Ref]
          obtain ⟨⟨⟨r, ℓ, hQ⟩, -⟩, hF⟩ := hJc hub0
          have hu : ∀ f, e.kind ≠ .ub f := by
            intro f h
            obtain ⟨pc,kind⟩ := e
            cases h
            simp [Code.bump, cls] at hub
          obtain ⟨a,ev,hc,_,hsc,hsite,_,_,hcls,_⟩ :=
            Control.represents (hJc hub0).1.counts hev.1 hu hr
          have hB' := hB hub0
          -- the named barrier 0's count is kept by an event of these sites
          have keep : (d.site.late = true ∨ d.site = .fdone 1 1 ∨ d.site = .lse 0 ∨
              d.site = .lse 1) → Code.bump (cls L g) n e (.corr (.nb 0)) = n (.corr (.nb 0)) := by
            intro hs
            simp only [Code.bump, cls, ← hcls, nb0_not hc hs]
            rfl
          rw [← hsite] at hl
          rcases succ_cases hsc with ⟨rfl, -, -, -, -, -⟩ | ⟨hf, -, rfl⟩ | hM
          · obtain ⟨R, bal, hP, h2, h3⟩ := hB' hl
            exact ⟨R, bal, hP, by rw [keep (.inl hl)]; exact h2, by rw [keep (.inl hl)]; exact h3⟩
          · obtain ⟨s, v, k⟩ := d
            cases s <;> simp_all [Control.D.scheduler, Site.isFst, Site.late]
          · by_cases hdl : d.site.late = true
            · obtain ⟨R, bal, hP, h2, h3⟩ := hB' hdl
              exact ⟨R, bal, hP, by rw [keep (.inl hdl)]; exact h2,
                by rw [keep (.inl hdl)]; exact h3⟩
            have hent : d.site = .fdone 1 1 ∨ d.site = .lse 0 ∨ d.site = .lse 1 := by
              have h := late_entry
              rw [List.all_eq_true] at h
              have h' := h d.site (mem_allSites _)
              rw [List.all_eq_true] at h'
              have := h' a.site hM.1
              simp only [hl, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at this
              simp only [Bool.not_eq_true] at hdl
              rcases this with ((h | h) | h) | h
              · simp [hdl] at h
              · exact .inl h
              · exact .inr (.inl h)
              · exact .inr (.inr h)
            rw [keep (.inr hent)]
            have c1 := hQ.cnt (.nb 0) (by simp)
            have htail := hQ.tail
            have hcount : n (.corr (.nb 0)) = 2 + r ∧ tailR d.site = true ∧
                CorrWarp.epi d.site = .ready 0 ∧ d.site.hasUk = true := by
              obtain ⟨s, v, k⟩ := d
              simp only [Control.D.scheduler] at c1 hent ⊢
              rcases hent with rfl | rfl | rfl <;>
                refine ⟨?_, by decide, rfl, by decide⟩ <;>
                simp only [CorrWarp.rc] at c1 <;>
                simp [c1, passed, ptsOf, nbPts, before, inRound, Site.pc, Site.noTile]
            obtain ⟨hn0, htr, hep, huk⟩ := hcount
            obtain ⟨rv, -, -, hFE, hu⟩ := hF
            simp only [Epilogue.Fits, CorrWarp.toE, show d.scheduler.site = d.site from rfl,
                hep] at hFE
            obtain ⟨R, bal, hC, h0, h1⟩ := hFE
            have hBs := CorrWarp.bs_ref hC h0 h1 (hu huk)
            refine ⟨R, bal, hC.1, by omega, ?_⟩
            have ht := htail htr
            rw [hBs] at ht
            rw [hn0]
            rcases ht with h | ⟨rfl, h⟩
            · simp only [rvN]; split <;> omega
            · simp only [rvN]; split <;> omega
        | _ => trivial

/-! ### The schedule -/

/-- **The correction warps' barrier schedule**: the operands of the `k`-th barrier event of a
lane of the CTA's tile `T`. -/
def corrB (L : Launch) (g : Nat) (T : Option Nat) (k : Nat) : Nat × Option Nat × BarMode :=
  if k = 0 then (0, none, .sync) else if k = 1 then (2, some 416, .sync) else
  match T with
  | none => (2, some 416, .arrive)
  | some R => if k ≤ 5 + 2 * R then ((nbOf L g (if k % 2 = 0 then 0 else 1)).toNat, some 64, .sync)
      else (2, some 416, .arrive)

/-- The first pass found no tile at the end without one. -/
theorem noPicked_exit {d : Epilogue.D} {ns nv : Nat} (hF : Epilogue.Fits p L g d ns nv)
    (hs : d.site = .exit false) : ¬ ∃ R bal, Picked p L g R bal := by
  rintro ⟨R, bal, hP⟩
  rcases Mma.eband hF (by rw [hs]; simp) with ⟨-, -, hk⟩ | ⟨hp2, -⟩
  · exact (hk R bal hP).2.2 false hs
  · rw [hs] at hp2; simp [Mma.ePass] at hp2

/-- The picked tile's rounds from a nonnegative block count. -/
theorem rvN_half {B : Int} {r : Nat} (h : (r : Int) + 1 = B ∨ (r = 0 ∧ B < 2)) :
    rvN B / 2 = r := by
  simp only [rvN]; split <;> omega

set_option maxHeartbeats 8000000 in
/-- **A correction lane's barrier event has its ordinal's operands in the schedule.** -/
theorem corr_sched {d : D} {n : Cls → Nat} {ns nv : Nat} {pc id : Nat} {cnt : Option Nat}
    {mode : BarMode} (hR : Correction.Ref p L g (d, CorrWarp.rc n))
    (hF : CorrWarp.CFits p L g d ns nv) (hev : Correction.Ev p L g d ⟨pc, .bar id cnt mode⟩)
    (hB : n (.mma .bar) = 1 + n (.corr .bar2) + n (.corr (.nb 0)) + n (.corr (.nb 1)))
    (hLate : d.site.late = true → ∃ R bal, Picked p L g R bal ∧ 2 ≤ n (.corr (.nb 0)) ∧
        2 * (n (.corr (.nb 0)) - 2) = rvN (Bs p L g (refV p L g R bal))) :
    (id, cnt, mode) = corrB L g (tileC p L g) (n (.mma .bar)) := by
  obtain ⟨⟨r, ℓ, hQ⟩, -⟩ := hR
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := corr_ord hQ
  simp only [cbar, CorrWarp.rc] at o1 o2 o3 o4 o5 o6
  -- the tile at a site of the rounds' region
  have tile : CorrWarp.epi d.site = .ready 0 → d.site.hasUk = true →
      ∃ R bal, Picked p L g R bal ∧ Bs p L g d.v = Bs p L g (refV p L g R bal) := by
    intro hep huk
    obtain ⟨rv, -, -, hFE, hu⟩ := hF
    simp only [Epilogue.Fits, CorrWarp.toE, show d.scheduler.site = d.site from rfl, hep] at hFE
    obtain ⟨R, bal, hC, h0, h1⟩ := hFE
    exact ⟨R, bal, hC.1, CorrWarp.bs_ref hC h0 h1 (hu huk)⟩
  obtain ⟨s, v, k⟩ := d
  cases s
  case bar1 =>
    simp only [Correction.Ev, Kind.bar.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    have hk : n (.mma .bar) = 1 := by have := o1 rfl; omega
    rw [hk]; rfl
  case nb kk =>
    simp only [Correction.Ev, Kind.bar.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    obtain ⟨R, bal, hP, -⟩ := tile rfl (by fin_cases kk <;> rfl)
    have hk : n (.mma .bar) = 2 + kk.val := by have := o2 kk rfl; omega
    rw [tileC_of hP, hk]
    have h5 : 2 + kk.val ≤ 5 + 2 * (rvN (Bs p L g (refV p L g R bal)) / 2) := by omega
    have hpar : (2 + kk.val) % 2 = kk.val := by omega
    have hne : 2 + kk.val ≠ 0 ∧ 2 + kk.val ≠ 1 := by omega
    simp only [corrB, hne.1, hne.2, h5, hpar, ite_false, ite_true]
    fin_cases kk <;> simp [nbW, barK, nbOf]
  case rbar st =>
    simp only [Correction.Ev, Kind.bar.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    obtain ⟨R, bal, hP, hBs⟩ := tile rfl (by fin_cases st <;> rfl)
    have hl := hQ.loop (by fin_cases st <;> rfl)
    simp only at hl
    rw [hBs] at hl
    have hk : n (.mma .bar) = 4 + 2 * r + st.val := by have := o3 st rfl; omega
    rw [tileC_of hP, hk]
    have h5 : 4 + 2 * r + st.val ≤ 5 + 2 * (rvN (Bs p L g (refV p L g R bal)) / 2) := by
      simp only [rvN]; split <;> omega
    have hpar : (4 + 2 * r + st.val) % 2 = st.val := by omega
    have hne : 4 + 2 * r + st.val ≠ 0 ∧ 4 + 2 * r + st.val ≠ 1 := by omega
    simp only [corrB, hne.1, hne.2, h5, hpar, ite_false, ite_true]
    fin_cases st <;> simp [nbW, barK, nbOf]
  case fbar st =>
    simp only [Correction.Ev, Kind.bar.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    obtain ⟨R, bal, hP, hBs⟩ := tile rfl (by fin_cases st <;> rfl)
    have ht := hQ.tail (by fin_cases st <;> rfl)
    simp only at ht
    rw [hBs] at ht
    have hk : n (.mma .bar) = 4 + 2 * r + st.val := by have := o4 st rfl; omega
    rw [tileC_of hP, hk, rvN_half ht]
    have h5 : 4 + 2 * r + st.val ≤ 5 + 2 * r := by omega
    have hpar : (4 + 2 * r + st.val) % 2 = st.val := by omega
    have hne : 4 + 2 * r + st.val ≠ 0 ∧ 4 + 2 * r + st.val ≠ 1 := by omega
    simp only [corrB, hne.1, hne.2, h5, hpar, ite_false, ite_true]
    fin_cases st <;> simp [nbW, barK, nbOf]
  case barEnd l =>
    simp only [Correction.Ev] at hev
    rcases hev with hk | ⟨f, hk⟩
    · simp only [Kind.bar.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      cases l
      · obtain ⟨rv, -, -, hFE, -⟩ := hF
        have hk : n (.mma .bar) = 2 := by have := o6 rfl; omega
        rw [tileC_none (noPicked_exit hFE rfl), hk]
        rfl
      · obtain ⟨R, bal, hP, h2, h3⟩ := hLate rfl
        obtain ⟨h5, h6⟩ := o5 rfl
        have hk : n (.mma .bar) = 6 + 2 * r := by omega
        have hR : rvN (Bs p L g (refV p L g R bal)) / 2 = r := by omega
        rw [tileC_of hP, hk, hR]
        have hne : 6 + 2 * r ≠ 0 ∧ 6 + 2 * r ≠ 1 ∧ ¬ (6 + 2 * r ≤ 5 + 2 * r) := by omega
        simp only [corrB, hne.1, hne.2.1, hne.2.2, ite_false]
    · cases hk
  all_goals simp only [Correction.Ev, Epilogue.Ev, Correction.Site.toE] at hev
  all_goals shape_destruct hev
  all_goals (simp only [reduceCtorEq, Kind.tc.injEq, TcKind.commit.injEq] at *)

end
end PTX.Kernels.TmlFa4Fwd.Proof
