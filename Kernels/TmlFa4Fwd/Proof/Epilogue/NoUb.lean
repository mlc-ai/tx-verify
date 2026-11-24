-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Next
import Kernels.TmlFa4Fwd.Proof.Lib.InputRead
import Kernels.TmlFa4Fwd.Proof.Common.NoUb
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Epilogue.Facts
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.Epilogue.StoreSafe
import Lemmas.Kernel.NoUbFollowedSites
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # No event of the output warp is undefined behaviour

`Frame.noUb_of_followed_sites` for the lanes of warp 13 (`noUb`): they are followed with `Ref`
(`good_all`). `safe`: at a startup state the lane is on the fence path (`StartAt`: the three
shuffles, the fence, the barrier), whose shapes have no undefined behaviour; at a role state
`fired_safe` under `Fits`. `live`: the role machine dies only on an event of another kind than its
site's, which the shapes exclude, at the exit, at a read whose bytes do not rebuild, and at the
first pass's tile count when the coordinate divisions have no rule (`next_none`, with those two
as hypotheses; `chosen_divOk` gives the divisions' rules for a CTA with a work item). The
assembly waits for the division at a CTA without a work item (`DECISIONS.md`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

set_option maxHeartbeats 4000000 in
/-- **The first pass's tile count step does not die** on the reference tile count: the scan
ended at a group of the batch (`Fits`), so it picked a request of the batch (`picked_of_pre`),
and the chosen request's coordinate divisions have rules (`chosen_divOk`). -/
theorem tiles_next (hp : Pre p L m) (hg : g < L.threads) {d : D} {ns nv : Nat} {e : Event}
    (hs : d.site = .tiles false) (hF : Fits p L g d ns nv) (hE : Expect p L g d ns e)
    (hev : Ev p L g d e) : (M p L g).next d e ≠ none := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  simp only at hs
  subst hs
  obtain ⟨R, n0, v0, hP, hEV, hns, hnv, hRV, hB, hpv⟩ := hF
  obtain ⟨hEnd, htot, hgx, hcur, hgxB⟩ := hEV
  have hpre : PickedPre p L g R bal := ⟨hEnd, hB, hgxB⟩
  have hPk := picked_of_pre hp hg hpre
  have hpv' := hpv rfl
  simp only at htot hgx hcur hpv'
  subst htot hgx hcur hpv'
  obtain ⟨pc, kind⟩ := e
  simp only [Ev] at hev
  obtain ⟨recv, ok, hk⟩ := hev
  subst hk
  simp only [Expect] at hE
  have hx := hE R n0 v0 hP hEnd
  subst hx
  have hC : ChosenVals p L g R bal
      { site := .tiles false, w := w, dn := dn, tl := tl, u1 := u1, u2 := u2, u4 := u4, u8 := u8,
        u16 := u16, tot := T p false R, grp := grp, acc := acc,
        gx := gxv p (g / L.block) false R, cur := curv p (g / L.block) false R, bal := bal,
        pv := pvv p false R bal, nt := ntv p false R bal, c0 := c0, c1 := c1 }
      (3 + 7 * (R + 1) + selN bal) 1 :=
    ⟨hPk, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨h1, h2⟩ := chosen_divOk hp hg hC
  intro hn
  simp only [M, code, succ, afterTiles] at hn
  simp only [ntv] at h1 h2
  simp only [h1, h2, ↓reduceIte] at hn
  simp at hn

set_option maxHeartbeats 4000000 in
/-- **The role machine dies only at the exit** on an event of its shape that is no undefined
behaviour and returns what the reference says (the reads rebuild; the tile count is the
reference one, `tiles_next`). -/
theorem next_none (hp : Pre p L m) (hg : g < L.threads) {d : D} {ns nv : Nat} {e : Event}
    (hF : Fits p L g d ns nv) (hE : Expect p L g d ns e) (hev : Ev p L g d e)
    (hub : ∀ f, e.kind ≠ .ub f) (hn : (M p L g).next d e = none) : e.kind = .exit := by
  by_cases ht : d.site = .tiles false
  · exact absurd hn (tiles_next hp hg ht hF hE hev)
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s
  case exit l => simpa [Ev] using hev
  case tiles l =>
    cases l
    · exact absurd rfl ht
    · simp only [Ev] at hev
      obtain ⟨_, _, hk⟩ := hev
      subst hk
      simp [M, code, succ] at hn
      repeat' split at hn
      all_goals (exact absurd hn (Option.some_ne_none _))
  case word k =>
    simp only [Ev] at hev
    rcases hev with ⟨bs, hk⟩ | ⟨f, hk⟩
    · subst hk
      obtain ⟨r, n0, v0, hP, hR, hns, -⟩ := hF
      simp only [Expect] at hE
      simp only [M, code, succ, hE r n0 v0 hP hR hns] at hn
      simp [word32] at hn
    · exact absurd hk (hub f)
  case q0 | q1 =>
    all_goals simp only [Ev] at hev
    all_goals rcases hev with ⟨bs, hk⟩ | ⟨f, hk⟩
    all_goals try exact absurd hk (hub f)
    all_goals subst hk
    all_goals simp only [Expect] at hE
    all_goals simp only [M, code, succ, hE] at hn
    all_goals simp [word32] at hn
  all_goals simp only [Ev] at hev
  all_goals shape_destruct hev
  all_goals first
    | (simp [M, code, succ, word32] at hn; done)
    | (simp [M, code, succ, word32] at hn
       repeat' split at hn
       all_goals simp_all)

set_option maxHeartbeats 4000000 in
/-- **No event of a lane of warp 13 is undefined behaviour.** -/
theorem noUb (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {g : Nat}
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 13) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (f : Fault) : e.kind ≠ .ub f := by
  have hReads := cuQReadsFromLaunch hp hX
  have IH : ∀ n, GoodUpTo p L X n := fun _ h j hin _ => good_all hp hX hin.1 hin.2 j
  refine Frame.noUb_of_followed_sites (C := thread p L) (J := Ref p L)
    hX (fun k => good_all hp hX hg hw k) ?_ ?_ he f
  · intro k σ e he hσ hR f
    obtain ⟨σ, n⟩ := σ
    rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
    on_goal 7 => exact hR.elim
    · exact start_safe hp hX he hσ hR.1 f
    · obtain ⟨hF, -, -⟩ := hR
      obtain ⟨-, o, hf⟩ := fired hp hX he hσ
      exact fired_safe hp hg hF hf f
    all_goals exact hR.elim
  · intro k σ e he hσ hR hub hn
    obtain ⟨σ, n⟩ := σ
    rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
    on_goal 7 => exact hR.elim
    · exact start_live hp hX he hσ hR.1 hn
    · obtain ⟨hF, -, -⟩ := hR
      have hev := (fired hp hX he hσ).1
      have hE := expect hp hX hReads hg hw he hσ hF fun _ => IH _
      exact next_none hp hg hF hE hev hub (role_next_none hn)
    all_goals exact hR.elim

end
end PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
