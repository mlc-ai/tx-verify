-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.Softmax.RefDef
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.Softmax.Fragment
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Softmax.RefNext

@[expose] public section

/-! # The fragment's expected values at the scheduler's events

What the softmax fragment expects of an event (`Softmax.ExpectD`) at a scheduler site follows
from the scheduler's reference values (`SFits`) and what the event returns (`SExpect`,
`SmWarp.sexpect`): the launch words rebuild to 32-bit words, the shuffles return 32-bit words, and
at the first pass's tile count the chosen request's coordinate divisions have rules (as the output
warp's `Epilogue.tiles_next`: the scan of the first pass picks a request, `picked_of_pre`, whose
divisions have rules, `chosen_divOk`). What is left of the expected values is at the bias loads
(`.bld`, the bytes of the bias tile in shared memory) and the score loads (`.sld`, the `f32`
payloads in Tensor Memory): `ExpectRest`, whose sources are the other roles' writes. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen Picked)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {w : Nat}

/-- What the fragment expects of an event at the sites whose values come from other roles'
writes: the bias loads and the score loads. -/
def ExpectRest (p : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .bld _ _ | .sld _ _ => ExpectD p L g d e
  | _ => True

set_option maxHeartbeats 4000000 in
/-- **The first pass's tile count has division rules**: on the reference tile count, the chosen
request's coordinate divisions have rules. -/
theorem tiles_divOk (hp : Pre p L m) (hg : g < L.threads) {c : Epilogue.D} {ns nv : Nat}
    (hs : c.site = .tiles false) (hF : Epilogue.Fits p L g c ns nv) {x : BitVec 64}
    (hx : ∀ R n0 v0, Epilogue.PassStart p L g false n0 v0 → Epilogue.End p (g / L.block) false R →
      x = Epilogue.ntv p false R c.bal) :
    Epilogue.divOk (Mma.coords p L g { c with nt := x }).n1
        (Mma.coords p L g { c with nt := x }).d1 = true ∧
      Epilogue.divOk (Mma.coords p L g { c with nt := x }).n2
        (Mma.coords p L g { c with nt := x }).d2 = true := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := c
  simp only at hs
  subst hs
  obtain ⟨R, n0, v0, hP, hEV, hns, hnv, hRV, hB, hpv⟩ := hF
  obtain ⟨hEnd, htot, hgx, hcur, hgxB⟩ := hEV
  have hpre : Epilogue.PickedPre p L g R bal := ⟨hEnd, hB, hgxB⟩
  have hPk := Epilogue.picked_of_pre hp hg hpre
  have hpv' := hpv rfl
  simp only at htot hgx hcur hpv'
  subst htot hgx hcur hpv'
  obtain rfl := hx R n0 v0 hP hEnd
  have hC : Epilogue.ChosenVals p L g R bal
      { site := .tiles false, w := w, dn := dn, tl := tl, u1 := u1, u2 := u2, u4 := u4, u8 := u8,
        u16 := u16, tot := Epilogue.T p false R, grp := grp, acc := acc,
        gx := Epilogue.gxv p (g / L.block) false R, cur := Epilogue.curv p (g / L.block) false R,
        bal := bal, pv := Epilogue.pvv p false R bal, nt := Epilogue.ntv p false R bal, c0 := c0,
        c1 := c1 }
      (3 + 7 * (R + 1) + Epilogue.selN bal) 1 :=
    ⟨hPk, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact Epilogue.chosen_divOk hp hg hC

set_option maxHeartbeats 4000000 in
/-- **At a scheduler site the fragment's expected values hold**, from the reference values and
what the event returns; elsewhere they are `ExpectRest`. -/
theorem expectD_of (hp : Pre p L m) (hg : g < L.threads) {d : D} {ns nv : Nat} {e : Event}
    (hF : SFits p L g d ns nv) (hE : SExpect p L g d ns e) (hR : ExpectRest p L g d e) :
    ExpectD p L g d e := by
  obtain ⟨hFE, -⟩ := hF
  obtain ⟨s, v, kk, acc⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s
  case bld | sld => exact hR
  case uk =>
    simp only [ExpectD]
    intro a bs hk
    subst hk
    exact ⟨_, hE⟩
  case q0 | q1 =>
    simp only [ExpectD]
    intro a bs hk
    subst hk
    exact ⟨_, hE rfl⟩
  case word k =>
    simp only [ExpectD]
    intro a bs hk
    subst hk
    have hE' := hE rfl
    simp only [Epilogue.Expect, epi] at hE'
    simp only [Epilogue.Fits, toE, epi] at hFE
    obtain ⟨r, n0, v0, hP, hS, hns, -⟩ := hFE
    exact ⟨_, hE' r n0 v0 hP hS hns⟩
  case down k =>
    simp only [ExpectD]
    intro md a b c x ok hk
    subst hk
    have hE' := hE rfl
    simp only [Epilogue.Expect, epi] at hE'
    simp only [Epilogue.Fits, toE, epi] at hFE
    obtain ⟨r, n0, v0, hP, hS, hns, -⟩ := hFE
    exact ⟨_, hE' r n0 v0 hP hS hns⟩
  case up k j =>
    simp only [ExpectD]
    intro md a b c x ok hk
    subst hk
    have hE' := hE rfl
    simp only [Epilogue.Expect, epi] at hE'
    simp only [Epilogue.Fits, toE, epi] at hFE
    obtain ⟨r, n0, v0, hP, hS, hns, -⟩ := hFE
    exact ⟨_, hE' r n0 v0 hP hS hns⟩
  case total k =>
    simp only [ExpectD]
    intro md a b c x ok hk
    subst hk
    have hE' := hE rfl
    simp only [Epilogue.Expect, epi] at hE'
    simp only [Epilogue.Fits, toE, epi] at hFE
    obtain ⟨r, n0, v0, hP, hS, hns, -⟩ := hFE
    exact ⟨_, hE' r n0 v0 hP hS hns⟩
  case pre l =>
    simp only [ExpectD]
    intro md a b c x ok hk
    subst hk
    have hE' := hE rfl
    simp only [Epilogue.Expect, epi] at hE'
    simp only [Epilogue.Fits, toE, epi] at hFE
    obtain ⟨R, n0, v0, hP, hEV, hns, -⟩ := hFE
    exact ⟨_, hE' R n0 v0 hP hEV.1 hns⟩
  case tiles l =>
    have hE' := hE rfl
    cases l
    · simp only [ExpectD]
      intro md a b c x ok hk
      subst hk
      simp only [Epilogue.Expect, epi] at hE'
      have hFE' := hFE
      simp only [Epilogue.Fits, toE, epi] at hFE'
      obtain ⟨R, n0, v0, hP, hEV, -⟩ := hFE'
      obtain ⟨y, rfl⟩ : ∃ y, x = .bits 32 y := ⟨_, hE' R n0 v0 hP hEV.1⟩
      refine ⟨y, rfl, ?_⟩
      have := tiles_divOk (c := toE ⟨.tiles false, v, kk, acc⟩) hp hg rfl hFE (x := y)
        fun R n0 v0 hP hEnd => by
          have h := hE' R n0 v0 hP hEnd
          simp only [Value.bits.injEq, true_and] at h
          exact h
      exact this
    · simp only [ExpectD]
      intro md a b c x ok hk
      subst hk
      simp only [Epilogue.Expect, epi] at hE'
      simp only [Epilogue.Fits, toE, epi] at hFE
      obtain ⟨R, n0, v0, hP, hEV, -⟩ := hFE
      exact ⟨_, hE' R n0 v0 hP hEV.1⟩
  all_goals simp only [ExpectD]

end
end PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
