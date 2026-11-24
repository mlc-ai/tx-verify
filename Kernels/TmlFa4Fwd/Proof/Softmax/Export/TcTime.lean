-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TcPts
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.PlaceLag
import Kernels.TmlFa4Fwd.Proof.Lib.RoundsBound
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Rounds
import Kernels.TmlFa4Fwd.Proof.SmWarp.Open
import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Representative
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.BarLag
import Kernels.TmlFa4Fwd.Proof.Softmax.RefCases
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Tc
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The softmax warps' warp-collective `tcgen05` events in the time table

`soft_tcLag`: a lane with no more warp-collective `tcgen05` events than a lane of its warp before
one
is no later than it. `soft_tcAfter`: such an event leads to a later state. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (ptsOf passed before allSites mem_allSites Reg ordK
  val valT sm nexts tw tcPts ex)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h k j : Nat}

private def tcChk (st : Nat) (s : Softmax.Site) : Bool :=
  decide (tw s = 0) || ((val st s).isSome && decide (s.pos ≤ 15232) && s.hasUk && !s.noTile &&
    decide ((if s.delayed then 1 else 0) < tcPts.countP (· = s.pos)) &&
    decide (∀ l, s ≠ .exit l))

private theorem tc_chk : [0, 1].all (fun st => allSites.all (tcChk st)) = true := by
  decide +kernel

private def nextChk (st : Nat) (s s' : Softmax.Site) : Bool :=
  match Progress.Sm.place st s, Progress.Sm.place st s' with
  | some (b1, true, o1), some (b2, true, o2) => decide (b1 + o1 + sm s < b2 + o2)
  | _, _ => false

private theorem next_chk : [0, 1].all (fun st => allSites.all fun s => decide (tw s = 0) ||
    [false, true].all fun b => (nexts b s).all (nextChk st s)) = true := by decide +kernel

private theorem stage_lt : Progress.Sm.stage L g = 0 ∨ Progress.Sm.stage L g = 1 := by
  unfold Progress.Sm.stage; split <;> simp

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hw : Prologue.warpIndex L g < 8)
include hp hX hFw hub hw

omit hp hX hFw hw in
private theorem ub0 {d : Softmax.Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (SmWarp.sinj p L g d n))) : n .ub = 0 := by
  by_contra h
  obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
  cases kind <;> simp [cls] at hk
  exact hub ⟨(g, j), pc, _, hf⟩

/-- **A warp-collective `tcgen05` event of a softmax lane** is at a place of its tile. -/
theorem soft_tc_at (hg : g < L.threads) {e : Event} (he : X.get (g, k) = some e)
    (hcl : isTcColl e = true) {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    ∃ d n B P rb rp a, σ = SmWarp.sinj p L g d n ∧ Softmax.Ev p L g d.scheduler e ∧ 0 < tw
        d.scheduler.site ∧
      SoftTile p L g B P ∧ SoftAt p L g B P d.scheduler n rb rp ∧
      val (Progress.Sm.stage L g) d.scheduler.site = some a ∧ d.scheduler.site.pos ≤ 15232 ∧
      ex d.scheduler < tcPts.countP (· = d.scheduler.site.pos) ∧ (∀ l, d.scheduler.site ≠ .exit l) ∧
      ((X.tr g).take k).countP isTcColl = passed tcPts d.scheduler.site rb rp + ex d.scheduler := by
  have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(g, k), e.pc, f, by
    rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
  rcases SmWarp.open_ev hp hX hFw hw he hne with ⟨s, n', hσ', -, -, hi, hev⟩ |
    ⟨d, n, hσ', h0, -, -, hev⟩
  · exact absurd hcl (start_not_tcColl hi.2 hev)
  rw [hσ] at hσ'
  cases hσ'
  have htw : 0 < tw d.scheduler.site := by
    have := tc_site hev.1 hne
    rw [hcl] at this
    simpa using this
  have hchk := List.all_eq_true.mp (List.all_eq_true.mp tc_chk (Progress.Sm.stage L g) (by
    rcases stage_lt (L := L) (g := g) with h | h <;> simp [h])) d.scheduler.site (mem_allSites _)
  simp only [tcChk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at hchk
  obtain ⟨⟨⟨⟨⟨h2, hpos⟩, huk⟩, -⟩, hex⟩, hx⟩ := hchk.resolve_left (by omega)
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h2
  rcases soft_place hp hX hFw hub hg hw hσ with ⟨-, s, n', h1, -⟩ |
    ⟨d', n', rb, rp, h1, -, h3, hc, hwt, hF, hreg, hno⟩
  · cases h1
  cases h1
  have hpk : ∃ R bal, Epilogue.Picked p L g R bal := by
    have hFE := hF.1
    have hep : SmWarp.epi d.scheduler.site = .ready 0 := by
      revert huk
      cases d.scheduler.site <;> simp [Softmax.Site.hasUk, Softmax.Site.rgn, SmWarp.epi]
    simp only [Epilogue.Fits, SmWarp.toE, hep] at hFE
    obtain ⟨R, bal, hC, -⟩ := hFE
    exact ⟨R, bal, hC.1⟩
  obtain ⟨B, P, hT⟩ := exists_softTile hpk
  obtain ⟨hr, ht⟩ := hreg B P hT
  have hcnt := tc_count hp hX hFw hg hub hσ h0 hc
  have hex1 : ex d.scheduler < tcPts.countP (· = d.scheduler.site.pos) := by
    cases hd : d.scheduler.site.delayed with
    | true =>
      rw [hd] at hex
      have : ex d.scheduler ≤ 1 := by unfold ex Progress.Sm.subOff; split <;> omega
      simp only [ite_true] at hex
      omega
    | false =>
      rw [hd] at hex
      have hx0 : ex d.scheduler = 0 := by
        unfold ex Progress.Sm.subOff
        split <;> first | rfl | (rename_i hs; rw [hs] at hd; cases hd)
      rw [hx0]
      simpa using hex
  exact ⟨d, n, B, P, rb, rp, a, rfl, hev.1, htw, hT, ⟨h3, hc, hwt, hF, hr, ht⟩, ha, hpos, hex1, hx,
    hcnt⟩

/-- **A softmax lane with no more warp-collective `tcgen05` events than a lane of its warp before
one
is no later than it.** -/
theorem soft_tcLag (hg : g < L.threads) (hs : SameWarp L g h) {c : Nat}
    {σ : (thread p L g).D} (hK : X.TcK (g, j) c)
    (hσ : Frame.stateAt (thread p L) X g j = some (some σ))
    (hle : (X.tr h).countP isTcColl ≤ c) :
    Sched.threadTime (Progress.timed p L) X h ≤ Progress.time p L g σ := by
  obtain ⟨⟨e, he, hcl⟩, hcnt⟩ := hK
  obtain ⟨d, n, B, P, rb, rp, a, rfl, hev, htw, hT, hA, ha, hpos, hex, hx, hc⟩ :=
    soft_tc_at hp hX hFw hub hw hg he hcl hσ
  have hh := hs.1.2.1
  have hwi : Prologue.warpIndex L h = Prologue.warpIndex L g := hs.2.symm
  have hwh : Prologue.warpIndex L h < 8 := by omega
  have hst : Progress.Sm.stage L h = Progress.Sm.stage L g := by
    unfold Progress.Sm.stage; rw [hwi]
  have hTh : SoftTile p L h B P := SoftTile.cta hs.1.2.2.symm hw hwh (by rw [hwi]) hT
  have hah : val (Progress.Sm.stage L h) d.scheduler.site = some a := by rw [hst]; exact ha
  have ht : Progress.Sm.time p L g d.scheduler n = valT p (rb + rp) a + ex d.scheduler :=
    (soft_round_time hA ha).2 (hT.bmax hp hg)
  have hne' : ∀ {j e}, X.get (h, j) = some e → ∀ f, e.kind ≠ .ub f := fun {j e} he f hf =>
    hub ⟨(h, j), e.pc, f, by rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
  show _ ≤ Progress.Sm.time p L g d.scheduler n
  rw [ht]
  refine (soft_place_lag hp hX hFw hub hh hwh hTh isTcColl tcPts ex (e0 := ex d.scheduler)
    (fun hσ' _ hA' => tc_count hp hX hFw hh hub hσ' (ub0 hub hσ') hA'.cnt) hA.reg hA.tile hex
    hx ?_ ?_ (fun hσ' he' hev' hd _ => ?_) (fun hA' hK' => ?_) (fun {d' n'} hA' hd hx' => ?_)).2
  · rw [← hc]; exact hle.trans hcnt.ge
  · have := Progress.scanBase_le_primeBase p
    unfold valT Progress.pipeBase; omega
  · rw [tc_site hev' (hne' he'), hd]
    simpa using htw
  · exact lt_of_lt_of_le (soft_time_lt hp hA' hah hA.reg hpos hK') (Nat.le_add_right _ _)
  · have h1 : Progress.Sm.time p L h d' n' ≤ valT p (rb + rp) a + ex d' :=
      (soft_round_time hA' (by rw [hd]; exact hah)).1
    exact ⟨by omega, fun h2 => by omega⟩

/-- **A warp-collective `tcgen05` event of a softmax lane leads to a later state.** -/
theorem soft_tcAfter (hg : g < L.threads) (htr : Frame.Tracked (thread p L) X) {c : Nat}
    {σ : (thread p L g).D} (hK : X.TcK (g, j) c)
    (hσ : Frame.stateAt (thread p L) X g j = some (some σ)) :
    (∃ σ', Frame.stateAt (thread p L) X g (j + 1) = some (some σ') ∧
      Progress.time p L g σ < Progress.time p L g σ') ∨
      Frame.stateAt (thread p L) X g (j + 1) = none := by
  obtain ⟨⟨e, he, hcl⟩, -⟩ := hK
  obtain ⟨d, n, B, P, rb, rp, a, rfl, hev, htw, hT, hA, ha, -, hex, -⟩ :=
    soft_tc_at hp hX hFw hub hw hg he hcl hσ
  have hstep : Frame.stateAt (thread p L) X g (j + 1) =
      ((Softmax.Control.succ p L g d e).map (Option.map fun d' => SmWarp.sinj p L g d'
        (Code.bump (cls L g) n e))) := by
    rw [Frame.stateAt_succ (C := thread p L) (show (X.tr g)[j]? = some e from he), hσ]
    exact SmWarp.next_sinj d n _
  have h80 : Code.bump (cls L g) n e (.soft (.acquire 80)) = n (.soft (.acquire 80)) := by
    obtain ⟨pc, kd⟩ := e
    cases kd <;> first | cases hcl | simp [Code.bump, cls, Softmax.cls]
  rw [hstep]
  cases hs : Softmax.Control.succ p L g d e with
  | none => exact .inr rfl
  | some o =>
    cases o with
    | none =>
      exfalso
      rw [hs] at hstep
      exact htr g (j + 1) hg hstep
    | some d' =>
      left
      refine ⟨_, rfl, ?_⟩
      show Progress.Sm.time p L g d.scheduler n <
        Progress.Sm.time p L g d'.scheduler (Code.bump (cls L g) n e)
      have hsub : Progress.Sm.subOff d.scheduler ≤ sm d.scheduler.site := by
        unfold Progress.Sm.subOff sm
        split <;> simp_all
      by_cases hdl : d.scheduler.site.delayed = true ∧ d.scheduler.k = 0
      · -- the implicit wait of a delayed store
        obtain ⟨h1, h2⟩ := hdl
        obtain ⟨s, v, kk, acc⟩ := d
        change kk = 0 at h2
        subst h2
        rcases delayed_site h1 with h1 | h1 <;>
        · change s = _ at h1
          subst h1
          simp only [Softmax.Control.succ, Softmax.succ, Softmax.Control.D.scheduler, ite_true,
            Option.map_some, Option.some.injEq] at hs
          subst hs
          simp only [Progress.Sm.time, Softmax.Control.D.scheduler, Softmax.Control.erase,
            Progress.Sm.place, Progress.Sm.subOff, h80]
          exact Progress.clk_lt_of_off (Nat.lt_succ_self _)
      · have hM : d'.scheduler.site ∈ nexts (Softmax.lz L g) d.scheduler.site := by
          have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(g, j), e.pc, f, by
            rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
          obtain ⟨n', hRef⟩ : ∃ n', Softmax.Control.Ref p L g (d, n') := by
            rcases SmWarp.open_ev hp hX hFw hw he hne with ⟨s, n', hσ', -⟩ |
              ⟨d', n', hσ', h0, hR, -, -⟩
            · rw [hσ] at hσ'; cases hσ'
            · rw [hσ] at hσ'
              cases hσ'
              obtain ⟨⟨n', hR', -⟩, -⟩ := hR.2 h0
              exact ⟨n', hR'⟩
          obtain ⟨x, ev, hev', hne', hsx, hsite, -, -, -, hor⟩ :=
            Softmax.Control.represents hp hRef hev hne hs
          rw [show d'.scheduler.site = x.site from hsite.symm]
          rcases Softmax.succ_cases hsx with ⟨-, -, -, hno⟩ | hM
          · exfalso
            have hk : ∀ {f}, ev.kind = f → (∀ o, f ≠ .tc o) → False := by
              rintro f hk hf
              rcases hor with rfl | ⟨⟨r, c, hd⟩ | ⟨b, c, hd⟩, -⟩
              · obtain ⟨pc, kd⟩ := ev
                simp only at hk
                subst hk
                cases kd <;> first | cases hcl | exact hf _ rfl
              · obtain ⟨site, v, kk, acc⟩ := d
                change site = _ at hd
                subst hd
                obtain ⟨pc, kd⟩ := ev
                simp only at hk
                subst hk
                simp only [Softmax.Control.D.scheduler, Softmax.Ev, Softmax.tcLdOrUb] at hev'
                cases r <;> shape_destruct hev' <;>
                  first | exact hf _ rfl | exact absurd rfl (hne' _)
              · rw [show d.scheduler.site = _ from hd] at htw
                cases htw
            rcases hno with ⟨_, _, _, _, hk'⟩ | ⟨_, _, hk'⟩ | h
            · exact hk hk' (by simp)
            · exact hk hk' (by simp)
            · exact hdl h
          · exact hM.1
        have h1 := List.all_eq_true.mp (List.all_eq_true.mp next_chk (Progress.Sm.stage L g) (by
          rcases stage_lt (L := L) (g := g) with h | h <;> simp [h])) d.scheduler.site (mem_allSites
              _)
        simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
        have h2 := List.all_eq_true.mp (List.all_eq_true.mp (h1.resolve_left (by omega))
          (Softmax.lz L g) (by cases Softmax.lz L g <;> simp)) d'.scheduler.site hM
        unfold nextChk at h2
        split at h2
        · rename_i b1 o1 b2 o2 e1 e2
          simp only [decide_eq_true_eq] at h2
          simp only [Progress.Sm.time, e1, e2, h80]
          unfold Progress.clk
          omega
        · cases h2

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
