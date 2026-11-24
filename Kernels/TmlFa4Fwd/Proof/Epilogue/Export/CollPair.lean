-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.CollSite
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Common.Migrated
import Kernels.TmlFa4Fwd.Proof.Common.NoUb
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Coll
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Kind
import Kernels.TmlFa4Fwd.Proof.Epilogue.Facts
import Kernels.TmlFa4Fwd.Proof.Epilogue.NoUb
import Kernels.TmlFa4Fwd.Proof.Epilogue.Open
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Kernels.TmlFa4Fwd.Proof.Top.Table
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The collectives of two lanes of the output warp -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Progress (isP cnt)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}
private theorem out_exit_site {g : Nat} {d : Epilogue.D} {pc : Nat}
    (hev : Epilogue.Ev p L g d ⟨pc, .exit⟩) : ∃ l, d.site = .exit l := by
  obtain ⟨s, rest⟩ := d
  cases s <;> simp only [Epilogue.Ev] at hev
  all_goals (try exact ⟨_, rfl⟩)
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals simp_all [Epilogue.isStore]

/-- **An output lane's machine stops only at its exit.** -/
private theorem out_live (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 13) {k : Nat} {σ : (thread p L g).D}
    {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) (hub : ∀ f, e.kind ≠ .ub f)
    (hn : (thread p L g).next σ e = none) : e.kind = .exit := by
  have hR := (Epilogue.good_all hp hX hg hw k).2 _ hσ
  have IH : ∀ n, Epilogue.GoodUpTo p L X n :=
    fun _ h j hin _ => Epilogue.good_all hp hX hin.1 hin.2 j
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
  on_goal 7 => exact hR.elim
  · exact start_live hp hX he hσ hR.1 hn
  · obtain ⟨hF, -, -⟩ := hR
    have hev := (Epilogue.fired hp hX he hσ).1
    have hE := Epilogue.expect hp hX (cuQReadsFromLaunch hp hX) hg hw he hσ hF fun _ => IH _
    exact Epilogue.next_none hp hg hF hE hev hub (role_next_none hn)
  all_goals exact hR.elim

/-- Two states at one site with one ballot have one static part. -/
private theorem outShape_eq {d d' : Epilogue.D} {n n' : Cls → Nat} {h' : Nat} (h : d.site = d'.site)
    (hb : ∀ l, d.site = .pre l ∨ d.site = .tiles l → d.bal = d'.bal) :
    outShape p L g (.inr ⟨.epilogue, d⟩, n) = outShape p L h' (.inr ⟨.epilogue, d'⟩, n') := by
  obtain ⟨site, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  obtain ⟨site', w', dn', tl', v1, v2, v4, v8, v16, tot', grp', acc', gx', cur', bal', pv', nt',
    c0', c1'⟩ := d'
  simp only at h hb
  subst h
  cases site with
  | pre l => rw [show bal = bal' from hb l (.inl rfl)]; rfl
  | tiles l => rw [show bal = bal' from hb l (.inr rfl)]; rfl
  | _ => rfl

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
  (hub : ¬ HasUb X) (hs : SameWarp L g h) (hw : Prologue.warpIndex L g = 13)
include hp hX hub hs hw

omit hub in
/-- A lane exits after more collectives than a lane at one has made. -/
private theorem out_exit_pair {k pc : Nat} {σ : (thread p L g).D} {σ' : (thread p L h).D}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some σ)) (hcg : CollAt p L g σ)
    (hσ' : Frame.stateAt (thread p L) X h k = some (some σ'))
    (he : X.get (h, k) = some ⟨pc, .exit⟩) :
    (X.tr g).countP Sched.isWarpColl < ((X.tr h).take k).countP Sched.isWarpColl := by
  have hg := hs.1.1
  have hh := hs.1.2.1
  have hc : g / L.block = h / L.block := hs.1.2.2
  have hwh : Prologue.warpIndex L h = 13 := by rw [← hw]; exact hs.2.symm
  have hi := (out_collAt hp hX hg hw hσ).mp hcg
  rw [← List.take_length (l := X.tr g), Progress.cnt_eq hp hX hg hw hσ,
    Progress.cnt_eq hp hX hh hwh hσ']
  have hR := (Epilogue.good_all hp hX hg hw _).2 _ hσ
  have hR' := (Epilogue.good_all hp hX hh hwh k).2 _ hσ'
  obtain ⟨σ, n⟩ := σ
  obtain ⟨σ', n'⟩ := σ'
  simp only [cnt, Progress.collCount]
  rcases σ' with s' | ⟨_ | _ | _ | _ | r' | _, d'⟩ <;> try exact hR'.elim
  · exfalso
    obtain ⟨hev, -⟩ := start_fired hp hX he hσ'
    obtain ⟨hS, -⟩ := hR'
    obtain ⟨site, x1, x2, x3⟩ := s'
    cases site <;> simp only [StartAt] at hS
    case sh j => fin_cases j <;> simp [Startup.Ev] at hev
    case fence => simp [Startup.Ev] at hev
    case bar => simp [Startup.Ev] at hev
  · obtain ⟨l, hx⟩ := out_exit_site (Epilogue.fired hp hX he hσ').1
    have hx' : Epilogue.Fits.ExitAt p L h l (n' .shfl) (n' .vote) := by
      have := hR'.1
      simpa only [Epilogue.Fits, hx] using this
    rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
    · obtain ⟨hS, hv, -⟩ := hR
      obtain ⟨site, x1, x2, x3⟩ := s
      cases site <;> simp only [isP, Bool.false_eq_true] at hi
      rename_i j
      simp only [StartAt] at hS
      have := Epilogue.fits_three hR'.1
      have := j.isLt
      omega
    · exact Epilogue.out_lt_exit hR.1 hc hi hx'

/-- **The collectives of two lanes of the output warp.** -/
theorem out_pair : Sched.WarpPair m (Progress.timed p L) X (CollAt p L) (outShape p L) g h := by
  have hg := hs.1.1
  have hh := hs.1.2.1
  have hc : g / L.block = h / L.block := hs.1.2.2
  have hFw := launchFollow hp hX
  have hwh : Prologue.warpIndex L h = 13 := by rw [← hw]; exact hs.2.symm
  refine ⟨fun {k k' σ σ'} hP hP' hn => ?_, fun {σ σ'} hσ hcg hσ' hch hn hrel => ?_,
    fun {k pc σ σ'} hσ hcg hσ' he => ?_, fun {σ} hσ hcg hle hno hnn => ?_,
    fun hph hσ' => ?_⟩
  · -- one position, one static part
    have hi := out_isP hp hX hg hw hP
    have hi' := out_isP hp hX hh hwh hP'
    rw [Progress.cnt_eq hp hX hg hw hP.1, Progress.cnt_eq hp hX hh hwh hP'.1] at hn
    have hR := (Epilogue.good_all hp hX hg hw k).2 _ hP.1
    have hR' := (Epilogue.good_all hp hX hh hwh k').2 _ hP'.1
    obtain ⟨σ, n⟩ := σ
    obtain ⟨σ', n'⟩ := σ'
    simp only [cnt, Progress.collCount] at hn
    rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;>
      rcases σ' with s' | ⟨_ | _ | _ | _ | r' | _, d'⟩ <;>
      try first | exact hR.elim | exact hR'.elim
    · obtain ⟨hS, hv, -⟩ := hR
      obtain ⟨hS', hv', -⟩ := hR'
      obtain ⟨site, x1, x2, x3⟩ := s
      obtain ⟨site', y1, y2, y3⟩ := s'
      cases site <;> simp only [isP, Bool.false_eq_true] at hi
      cases site' <;> simp only [isP, Bool.false_eq_true] at hi'
      rename_i j j'
      simp only [StartAt] at hS hS'
      have : j = j' := Fin.ext (by omega)
      subst this
      exact ⟨rfl, rfl⟩
    · obtain ⟨hS, hv, -⟩ := hR
      obtain ⟨site, x1, x2, x3⟩ := s
      cases site <;> simp only [isP, Bool.false_eq_true] at hi
      rename_i j
      simp only [StartAt] at hS
      have := Epilogue.fits_three hR'.1
      have := j.isLt
      omega
    · obtain ⟨hS, hv, -⟩ := hR'
      obtain ⟨site, x1, x2, x3⟩ := s'
      cases site <;> simp only [isP, Bool.false_eq_true] at hi'
      rename_i j
      simp only [StartAt] at hS
      have := Epilogue.fits_three hR.1
      have := j.isLt
      omega
    · have hsite := Epilogue.out_site_same hR.1 hR'.1 hc hi hi' hn
      exact ⟨show d.site.pc = d'.site.pc by rw [hsite], outShape_eq hsite fun l hd =>
        Epilogue.bal_same hc hR.1 hR'.1 hd hsite.symm⟩
  · -- released
    left
    by_contra hnr
    have hi := (out_collAt hp hX hg hw hσ).mp hcg
    have hi' := (out_collAt hp hX hh hwh hσ').mp hch
    have hlen : 0 < (X.tr h).length := by
      by_contra h0
      exact hnr (Sched.released_nil (List.length_eq_zero_iff.mp
        (show (X.tr h).length = 0 by omega)))
    obtain ⟨e, he⟩ : ∃ e, X.get (h, (X.tr h).length - 1) = some e :=
      ⟨_, List.getElem?_eq_getElem
        (show (X.tr h).length - 1 < (X.tr h).length by omega)⟩
    have hne : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := fun pc f hf => hub ⟨_, pc, f, by rw [he, hf]⟩
    obtain ⟨⟨σ0, n0⟩, hσ0, hR0⟩ := good_state hp hX he hne (Epilogue.good_all hp hX hh hwh _)
    have hun : ¬ Sched.Unblocking e.kind := fun hu => hnr (Sched.released_of_unblocking he hu)
    have hσ1 : Frame.stateAt (thread p L) X h ((X.tr h).length - 1 + 1) = some (some σ') := by
      rw [show (X.tr h).length - 1 + 1 = (X.tr h).length by omega]; exact hσ'
    have hsucc : (thread p L h).next (σ0, n0) e = some (some σ') := by
      have h1 := hσ1
      rw [Frame.stateAt_succ (C := thread p L) (show (X.tr h)[(X.tr h).length - 1]? = some e
        from he), hσ0] at h1
      exact h1
    have hrole : ∃ d' n', σ' = (.inr ⟨.epilogue, d'⟩, n') := by
      have hR' := (Epilogue.good_all hp hX hh hwh _).2 _ hσ'
      obtain ⟨σ', n'⟩ := σ'
      rcases σ' with s' | ⟨_ | _ | _ | _ | r' | _, d'⟩ <;>
        try first | exact hR'.elim | exact ⟨_, _, rfl⟩
      exfalso
      have hle1 : cnt p L h (σ0, n0) ≤ cnt p L h (.inl s', n') := by
        rw [← Progress.cnt_eq hp hX hh hwh hσ0, ← Progress.cnt_eq hp hX hh hwh hσ']
        exact (List.take_sublist_take_left (l := X.tr h) (Nat.sub_le _ _)).countP_le
      obtain ⟨hS', hv', -⟩ := hR'
      obtain ⟨site', y1, y2, y3⟩ := s'
      cases site' <;> simp only [isP, Bool.false_eq_true] at hi'
      rename_i j
      simp only [StartAt] at hS'
      simp only [cnt, Progress.collCount] at hle1
      have hj := j.isLt
      rcases σ0 with s0 | ⟨_ | _ | _ | _ | r0 | _, d0⟩
      on_goal 7 => exact hR0.elim
      · obtain ⟨hev, -⟩ := start_fired hp hX he hσ0
        obtain ⟨hS, hv, -⟩ := hR0
        obtain ⟨site, x1, x2, x3⟩ := s0
        cases site <;> simp only [StartAt] at hS
        case sh j0 =>
          apply hun
          fin_cases j0 <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, hk⟩ := hev <;>
            rw [hk] <;> trivial
        all_goals omega
      · have := Epilogue.fits_three hR0.1
        omega
      all_goals exact hR0.elim
    obtain ⟨d', n', rfl⟩ := hrole
    have hst : d'.site ≠ .start := by
      intro h0
      have : Progress.Out.coll d'.site = true := hi'
      rw [h0] at this; cases this
    obtain ⟨r0, n1, hr0⟩ := epi_prev (show (X.tr h)[(X.tr h).length - 1]? = some e from he)
      hσ1 hst
    rw [hσ0] at hr0
    cases hr0
    rcases r0 with ⟨_ | _ | _ | _ | r | _, d0⟩
    on_goal 6 => exact hR0.elim
    · have hev := (Epilogue.fired hp hX he hσ0).1
      have hreg : d0.site = .start → False := by
        intro h0
        have hev' := hev
        simp only [Epilogue.Ev, h0] at hev'
        obtain ⟨inc, nn, inst, hk⟩ := hev'
        have hgr : ∃ d n, σ = (.inr ⟨.epilogue, d⟩, n) ∧ ¬ IsEntry .epilogue d := by
          have hR := (Epilogue.good_all hp hX hg hw _).2 _ hσ
          have hR' := (Epilogue.good_all hp hX hh hwh _).2 _ hσ'
          have h3 := Epilogue.fits_three hR'.1
          have e1 := Progress.cnt_eq hp hX hg hw hσ
          have e2 := Progress.cnt_eq hp hX hh hwh hσ'
          rw [List.take_length] at e1 e2
          rw [e2, e1] at hn
          obtain ⟨σ, n⟩ := σ
          simp only [cnt, Progress.collCount] at hn
          rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
          on_goal 7 => exact hR.elim
          · exfalso
            obtain ⟨hS, hv, -⟩ := hR
            obtain ⟨site, x1, x2, x3⟩ := s
            cases site <;> simp only [isP, Bool.false_eq_true] at hi
            rename_i j
            simp only [StartAt] at hS
            have := j.isLt
            omega
          · refine ⟨d, n, rfl, fun hE => ?_⟩
            have h0 : d.site = .start := hE
            have : Progress.Out.coll d.site = true := hi
            rw [h0] at this; cases this
          all_goals exact hR.elim
        obtain ⟨d, n, rfl, hE⟩ := hgr
        rcases Sched.thread_cases hX hh (fun pc n hk' => by
            rw [he] at hk'; cases hk'; cases hk) hnr with h | h | h | h | h | h | h
        · obtain ⟨pc, op, hk', -⟩ := h
          rw [he] at hk'; cases hk'; cases hk
        · exact not_regWait hp hX hub hs hσ hE hrel h
        · obtain ⟨pc, grp, dst, act, hk', -⟩ := h
          rw [he] at hk'; cases hk'; cases hk
        · obtain ⟨id, c', pc, -, hk', -⟩ := h
          change X.get _ = _ at hk'
          rw [he] at hk'; cases hk'; cases hk
        · obtain ⟨k, -, ⟨⟨ev, hk', hcl⟩, -⟩, -⟩ := h
          rw [he] at hk'; cases hk'
          obtain ⟨pc, kd⟩ := e
          simp only at hk
          subst hk
          cases hcl
        · obtain ⟨pc, id, c', hk', -⟩ := h
          rw [he] at hk'; cases hk'; cases hk
        · obtain ⟨pc, md, n, hk', -⟩ := h
          rw [he] at hk'; cases hk'; cases hk
      have hdrain : ∀ st, d0.site ≠ .drain st := by
        intro st h0
        have hf : d'.site = .free st := by
          obtain ⟨h1, -⟩ := Code.counted_next_some (C := glued p L h) hsucc
          have h2 : Epilogue.succ p L h d0 e = some (some { d0 with site := .free st }) := by
            obtain ⟨site, rest⟩ := d0
            simp only at h0
            subst h0
            rfl
          simp only [glued, Code.glue] at h1
          change (Epilogue.succ p L h d0 e).map _ = _ at h1
          rw [h2] at h1
          cases h1
          rfl
        have : Progress.Out.coll d'.site = true := hi'
        rw [hf] at this; cases this
      apply hun
      obtain ⟨pc, kd⟩ := e
      cases hs0 : d0.site <;> simp only [Epilogue.Ev, hs0] at hev
      case start => exact (hreg hs0).elim
      case drain st => exact (hdrain st hs0).elim
      case store => cases kd <;> simp_all [Epilogue.isStore, Sched.Unblocking]
      case word | q0 | q1 => rcases hev with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> trivial
      case down | up | total | pre | tiles => obtain ⟨_, _, rfl⟩ := hev; trivial
      case vote | ready => obtain ⟨_, rfl⟩ := hev; trivial
      all_goals (subst hev; trivial)
    all_goals exact hR0.elim
  · exact out_exit_pair hp hX hs hw hσ hcg hσ' he
  · -- lag
    have hi := (out_collAt hp hX hg hw hσ).mp hcg
    have hsch := Progress.out_collSched hp hX
    have htg := (Progress.time_sched hp hX hg hw hσ).1 hi
    have hcg' : cnt p L g σ = (X.tr g).countP Sched.isWarpColl := by
      rw [← Progress.cnt_eq hp hX hg hw hσ, List.take_length]
    rw [htg, hcg']
    show Sched.threadTime (Progress.timed p L) X h < Progress.outSched p (g / L.block) _
    rw [hc]
    rcases Nat.lt_or_ge ((X.tr h).countP Sched.isWarpColl) ((X.tr g).countP Sched.isWarpColl) with
      hlt | hge
    · refine (Sched.threadTime_le_sched hsch hh ⟨hh, hwh⟩).trans_lt ?_
      exact (hsch.mono _ _).trans_le (Sched.sched_le hsch.mono _ hlt)
    · have heq : (X.tr h).countP Sched.isWarpColl = (X.tr g).countP Sched.isWarpColl :=
        le_antisymm hle hge
      rw [← heq]
      cases hσ' : Frame.stateAt (thread p L) X h (X.tr h).length with
      | some o =>
        cases o with
        | none => exact absurd hσ' (Epilogue.good_all hp hX hh hwh _).1
        | some σ' =>
          have hni : isP p L h σ' = false := by
            by_contra hcon
            exact hno ⟨heq, σ', hσ', (out_collAt hp hX hh hwh hσ').mpr (by simpa using hcon)⟩
          have h1 := (Progress.time_sched hp hX hh hwh hσ').2 hni
          have h2 : cnt p L h σ' = (X.tr h).countP Sched.isWarpColl := by
            rw [← Progress.cnt_eq hp hX hh hwh hσ', List.take_length]
          rw [h2] at h1
          exact (Sched.threadTime_of (M := Progress.timed p L) hσ').trans_lt h1
      | none => exact absurd hσ' hnn
  · -- a stopped lane has exited
    exfalso
    obtain ⟨i, d, hi', h1, h2⟩ := Frame.first_stop (C := thread p L)
      (fun x k hx => (goodR' hp hX hx k).1) hh hσ'
    obtain ⟨e, he⟩ : ∃ e, X.get (h, i) = some e := ⟨_, List.getElem?_eq_getElem hi'⟩
    have hk := out_live hp hX hh hwh he h1 (fun f hf => hub ⟨(h, i), e.pc, f, by
      rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩) (by
      rw [Frame.stateAt_succ (C := thread p L) (show (X.tr h)[i]? = some e from he), h1] at h2
      exact h2)
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    subst hk
    have hl := Execution.exit_last hX hh he
    refine hph.2.2 pc ?_
    rw [List.getLast?_eq_getElem?, ← hl, Nat.add_sub_cancel]
    exact he

end
end
end PTX.Kernels.TmlFa4Fwd.Proof.Top
