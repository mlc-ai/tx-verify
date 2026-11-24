-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
public import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Soft
public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Places
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Lib.NoTc
import Kernels.TmlFa4Fwd.Proof.Common.View

import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Representative
import Kernels.TmlFa4Fwd.Proof.SmWarp.Open
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The softmax warps' collective `tcgen05` events in their ledger

A softmax lane's collective `tcgen05` events before a state are its score loads and P stores, with
the waits its barrier counts and its site give (`soft_tc`): six per arrival at the correction
warps' barrier less three per stage barrier, and `tcCorr`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

namespace Softmax

/-- The waits made at a site and sub-step (`z`: sub-step 0) beyond those its barrier counts
give. -/
def tcCorr (s : Site) (z : Bool) : Int :=
  match s with
  | .barr _ | .stat false | .narr .first | .narr .bias => 3
  | .stat true | .narr .plain => 4
  | .sldw c | .sld .plain c => c.val
  | .pst r q => if q = 3 then -1 else if r ≠ .plain ∧ q = 0 ∧ z = true then -3 else -2
  | .pwst _ k => if k = 0 then -2 else -1
  | .parr _ => -1
  | s => if s.late then -6 else 0

/-- What the event of a site adds to `tcCorr`. -/
def tcW (s : Site) (z : Bool) : Int :=
  match s with
  | .narr _ | .finarr => -6
  | .bsync _ => 3
  | .sldw _ | .pwst _ _ => 1
  | .pst r q => if r ≠ .plain ∧ q = 0 ∧ z = true then 1 else 0
  | _ => 0

theorem tcCorr_next : [false, true].all (fun lz => allSites.all fun s => (nexts lz s).all fun s' =>
    decide (tcCorr s' true = tcCorr s false + tcW s false)) = true := by
  decide +kernel

end Softmax

private theorem ind_eq (b : Bool) : (ind b : Int) = if b then 1 else 0 := by
  cases b <;> rfl

set_option maxHeartbeats 8000000 in
/-- **A softmax event's share of the count.** -/
theorem soft_tc_ev (hw : g % L.block / 32 < 8) {d : Softmax.D} {e : Event}
    (hev : Softmax.Ev p L g d e) (hub : ∀ f, e.kind ≠ .ub f)
    (hk : ∀ c, d.site = .sldw c → d.k = 1) :
    (ind (isTcColl e) : Int) = ind (cls L g (.soft .tcld) e) + ind (cls L g (.soft .tcst) e) +
      6 * ind (cls L g (.soft .nb) e) - 3 * ind (cls L g (.soft .sb) e) +
        Softmax.tcW d.site (d.k == 0) := by
  obtain ⟨h0, h1⟩ := soft_nb_range (L := L) hw
  have f1 : (2 : Nat) ≠ (Softmax.nbW L g).toNat := by omega
  have f2 : (Softmax.nbW L g).toNat ≠ 11 := by omega
  have f3 : (Softmax.nbW L g).toNat ≠ 12 := by omega
  have f4 : (2 : Nat) ≠ if stg L g then 12 else 11 := by split <;> omega
  have f5 : (Softmax.nbW L g).toNat ≠ if stg L g then 12 else 11 := by split <;> omega
  have f6 : (if stg L g then 12 else 11) ≠ (Softmax.nbW L g).toNat := fun h => f5 h.symm
  obtain ⟨s, v, k, acc⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s
  case pst r q =>
    simp only [Softmax.Ev] at hev
    by_cases hd : (Site.pst r q).delayed && k.val == 0
    · rw [ite_eq_left hd] at hev
      change kind = _ at hev
      subst hev
      simp only [Bool.and_eq_true, beq_iff_eq] at hd
      obtain ⟨hd, hk0⟩ := hd
      have hk0' : k = 0 := Fin.ext hk0
      subst hk0'
      cases r <;> fin_cases q <;> simp [Site.delayed] at hd <;>
        simp [ind, isTcColl, cls, Softmax.cls, Softmax.tcW]
    · rw [ite_eq_right hd] at hev
      rcases hev with ⟨a, vals, sh, hk'⟩ | ⟨f, hk'⟩
      · change kind = _ at hk'
        subst hk'
        have : Softmax.tcW (.pst r q) (k == 0) = 0 := by
          revert hd
          cases r <;> fin_cases q <;> fin_cases k <;> decide
        simp only [this]
        simp [ind, isTcColl, cls, Softmax.cls, hw, Softmax.Cnt.pointed]
      · exact absurd hk' (hub f)
  case sldw c =>
    have hk1 := hk c rfl
    subst hk1
    simp only [Softmax.Ev, Fin.isValue, Fin.val_one, BEq.rfl, ↓reduceIte] at hev
    rcases hev with hk' | ⟨f, hk'⟩
    · change kind = _ at hk'
      subst hk'
      simp [ind, isTcColl, cls, Softmax.cls, Softmax.tcW]
    · exact absurd hk' (hub f)
  all_goals simp only [Softmax.Ev, Epilogue.Ev, Softmax.Site.toE] at hev
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try subst_vars)
  all_goals first
    | exact absurd rfl (hub _)
    | (simp [ind, isTcColl, cls, Softmax.cls, Softmax.Cnt.pointed, Softmax.tcW, hw, f1, f2, f3, f4,
        f5, f6]; done)
    | (simp_all [ind, isTcColl, cls, Softmax.cls, Softmax.Cnt.pointed, Softmax.tcW]; done)

/-- A poll's site has no place in `tcCorr`. -/
private theorem stay_wait {v : V} {k k' : Fin 4} {acc : List Value} {s : Site} {e : Event} {l : Loc}
    {q : Nat} {ok acq : Bool} {sc : MbarScope} (hev : Softmax.Ev p L g ⟨s, v, k, acc⟩ e)
    (hw : e.kind = .wait l q ok acq sc) : Softmax.tcCorr s (k' == 0) =
      Softmax.tcCorr s (k == 0) + Softmax.tcW s (k == 0) := by
  obtain ⟨pc, kind⟩ := e
  change kind = _ at hw
  subst hw
  cases s <;> try (first | rfl | (simp [Softmax.tcCorr, Softmax.tcW]; done))
  all_goals exfalso
  all_goals simp only [Softmax.Ev, Epilogue.Ev, Softmax.Site.toE] at hev
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (first | contradiction | (simp only [reduceCtorEq] at *; done))

/-- A read's site has no place in `tcCorr`. -/
private theorem stay_rd {v : V} {k k' : Fin 4} {acc : List Value} {s : Site} {e : Event} {a : Acc}
    {bs : List (Option Byte)} (hev : Softmax.Ev p L g ⟨s, v, k, acc⟩ e)
    (hw : e.kind = .rd a bs) : Softmax.tcCorr s (k' == 0) =
      Softmax.tcCorr s (k == 0) + Softmax.tcW s (k == 0) := by
  obtain ⟨pc, kind⟩ := e
  change kind = _ at hw
  subst hw
  cases s <;> try (first | rfl | (simp [Softmax.tcCorr, Softmax.tcW]; done))
  all_goals exfalso
  all_goals simp only [Softmax.Ev, Epilogue.Ev, Softmax.Site.toE] at hev
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (first | contradiction | (simp only [reduceCtorEq] at *; done))

/-- **A softmax step's move of `tcCorr`.** -/
theorem soft_tc_move (hp : Pre p L m) {d d' : Softmax.Control.D} {n : Softmax.Cnt → Nat} {e : Event}
    (hJ : Softmax.Control.Ref p L g (d, n)) (hev : Softmax.Ev p L g d e)
    (hub : ∀ f, e.kind ≠ .ub f) (hn : Softmax.Control.succ p L g d e = some (some d')) :
    Softmax.tcCorr d'.site (d'.k == 0) =
      Softmax.tcCorr d.site (d.k == 0) + Softmax.tcW d.site (d.k == 0) := by
  obtain ⟨⟨rb, rp, hQ⟩⟩ := id hJ
  obtain ⟨a, ev, hev', -, hs, hsite, -, hk, -, hor⟩ :=
    Softmax.Control.represents hp hJ hev hub hn
  rw [← hsite, ← hk]
  rcases Softmax.succ_cases hs with ⟨h1, -, -, hN⟩ | hM
  · -- a step that stays at its site
    obtain ⟨site, v, k, acc⟩ := d
    simp only [Softmax.Control.D.scheduler] at h1 hN hs
    rw [h1]
    rcases hN with ⟨_, _, _, _, hw⟩ | ⟨_, _, hw⟩ | ⟨hd, hk0⟩
    · exact stay_wait hev' hw
    · exact stay_rd hev' hw
    · simp only at hd hk0
      subst hk0
      cases site <;> simp only [Site.delayed, Bool.false_eq_true] at hd
      rename_i r q
      have hk1 : a.k = 1 := by
        cases r <;> fin_cases q <;> first
          | (simp [Site.delayed] at hd; done)
          | (have h := congrArg (fun x : Option (Option Softmax.D) =>
              x.bind fun y => y.map (·.k)) hs
             exact (Option.some.inj h).symm)
      rw [hk1]
      cases r <;> fin_cases q <;> first
        | (simp [Site.delayed] at hd; done)
        | rfl
  · obtain ⟨hm, hka, -, hd, -⟩ := hM
    have ht := List.all_eq_true.mp Softmax.tcCorr_next (lz L g) (by cases lz L g <;> simp)
    have ht1 := List.all_eq_true.mp (List.all_eq_true.mp ht d.site (mem_allSites _)) a.site hm
    have ht2 := of_decide_eq_true ht1
    have e1 : Softmax.tcCorr a.site (a.k == 0) = Softmax.tcCorr a.site true := by
      rw [hka]
      cases a.site <;> rfl
    have e2 : Softmax.tcCorr d.site (d.k == 0) = Softmax.tcCorr d.site false ∧
        Softmax.tcW d.site (d.k == 0) = Softmax.tcW d.site false := by
      have hd' : d.site.delayed = true → d.k ≠ 0 := hd
      revert hd'
      cases d.site
      case stat pl => cases pl <;> exact fun _ => ⟨rfl, rfl⟩
      case narr r => cases r <;> exact fun _ => ⟨rfl, rfl⟩
      case sld r c => cases r <;> exact fun _ => ⟨rfl, rfl⟩
      case pst r q =>
        intro hd'
        cases r <;> fin_cases q <;> first
          | exact ⟨rfl, rfl⟩
          | (have hz : (d.k == 0) = false := by simpa using hd' rfl
             rw [hz]
             exact ⟨rfl, rfl⟩)
      all_goals exact fun _ => ⟨rfl, rfl⟩
    rw [e1, e2.1, e2.2, ht2]

/-- **The collective `tcgen05` events before a state of a softmax lane.** -/
def SoftTc (p : Params) (L : Launch) (g : Nat) : (thread p L g).D → Nat → Prop
  | (.inl _, _), N => N = 0
  | (.inr ⟨.softmax, d⟩, n), N => n .ub = 0 →
      (N : Int) = n (.soft .tcld) + n (.soft .tcst) + 6 * n (.soft .nb) - 3 * n (.soft .sb) +
        Softmax.tcCorr d.site (d.k == 0)
  | _, _ => True

theorem soft_tc (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hg : g < L.threads) :
    ∀ k σ, Frame.NoUbBefore X g k → Frame.stateAt (thread p L) X g k = some (some σ) →
      SoftTc p L g σ (((X.tr g).take k).countP isTcColl) := by
  refine Frame.RoleTable.countInvU (T := table p L) (S := fun g => g < L.threads)
    (fun g hg => thread_sound hp hg) hX (table_shape_of hp hFw)
    (table_followed hp hX hFw) hg isTcColl (P := fun σ N => SoftTc p L g σ N) rfl ?_
  rintro ⟨σ1, n⟩ e ⟨σ1', n'⟩ N hJ hi hev hB hn hJ'
  obtain ⟨h1, rfl⟩ := Code.counted_next_some (C := glued p L g) hn
  rcases σ1 with s | ⟨i, d⟩
  · have hN : N = 0 := hB
    have htc : isTcColl e = false := start_tcFree hev hi.2
    simp only [hN, htc]
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
        cases hx : exit L g s' with
        | none => simp only [Code.enter, hx]; rfl
        | some r =>
          simp only [Code.enter, hx] at hJ' ⊢
          cases r with
          | softmax =>
            intro hub
            obtain ⟨⟨c, ⟨⟨rb, rp, hQ⟩⟩, hLk⟩, -⟩ := (JR.softmax hJ').2.2 hub
            obtain ⟨h1, h2⟩ := hQ.pre rfl
            have z : ∀ c' : Softmax.Cnt, c'.pointed = true → c c' = 0 := by
              intro c' hc'
              have hcc : c c' = passed (ptsOf (lz L g) c') .setmax rb rp := hQ.cnt c' hc'
              obtain ⟨rb0, rp0, hQ0⟩ := refCounts_init p L g
              obtain ⟨h3, h4⟩ := hQ0.pre rfl
              have h0 : 0 = passed (ptsOf (lz L g) c') .setmax rb0 rp0 := hQ0.cnt c' hc'
              rw [hcc, h1, h2]
              rw [h3, h4] at h0
              exact h0.symm
            have z1 := (hLk .tcld rfl).symm.trans (z .tcld rfl)
            have z2 := (hLk .tcst rfl).symm.trans (z .tcst rfl)
            have z3 := (hLk .nb rfl).symm.trans (z .nb rfl)
            have z4 := (hLk .sb rfl).symm.trans (z .sb rfl)
            rw [z1, z2, z3, z4]
            rfl
          | _ => trivial
  · simp only [glued, Code.glue] at h1
    obtain ⟨o, hr, ho⟩ := Option.map_eq_some_iff.mp h1
    obtain ⟨d1, rfl, rfl⟩ := Option.map_eq_some_iff.mp ho
    cases i with
    | softmax =>
      intro hub
      have hub0 : n .ub = 0 := Nat.eq_zero_of_le_zero (hub ▸ Nat.le_add_right (n .ub) _)
      have hue : ∀ f, e.kind ≠ .ub f := by
        intro f h
        obtain ⟨pc, kind⟩ := e
        cases h
        simp [Code.bump, cls] at hub
      obtain ⟨h8, hR⟩ := JR.softmax hJ
      obtain ⟨⟨c, hRc, hLk⟩, -⟩ := hR.2 hub0
      obtain ⟨⟨rb, rp, hQ⟩⟩ := id hRc
      have hc : Softmax.Ev p L g d e := hev.1
      have hB0 := hB hub0
      have he := soft_tc_ev (g := g) (L := L) (p := p) h8 hc hue hQ.wait
      have hm := soft_tc_move hp hRc hc hue hr
      have b : ∀ c', Code.bump (cls L g) n e c' = n c' + ind (cls L g c' e) := fun _ => rfl
      simp only [b]
      rw [hm]
      have hi' : (if isTcColl e = true then 1 else 0 : Nat) = ind (isTcColl e) := rfl
      rw [hi']
      have he' : (ind (isTcColl e) : Int) = ind (cls L g (.soft .tcld) e) +
          ind (cls L g (.soft .tcst) e) + 6 * ind (cls L g (.soft .nb) e) -
          3 * ind (cls L g (.soft .sb) e) + Softmax.tcW d.site (d.k == 0) := he
      generalize ind (isTcColl e) = t0 at *
      generalize ind (cls L g (.soft .tcld) e) = t1 at *
      generalize ind (cls L g (.soft .tcst) e) = t2 at *
      generalize ind (cls L g (.soft .nb) e) = t3 at *
      generalize ind (cls L g (.soft .sb) e) = t4 at *
      push_cast
      linarith
    | _ => trivial

end
end PTX.Kernels.TmlFa4Fwd.Proof
