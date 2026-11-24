-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Counts
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.Common.FollowView
import Kernels.TmlFa4Fwd.Proof.Softmax.MbarSite
import Kernels.TmlFa4Fwd.Proof.Softmax.RefCases
public import Lemmas.Kernel.Safety.StateInvU
import Std.Tactic.BVDecide.Normalize.Prop

import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Places

@[expose] public section

/-! # A softmax lane's second P arrivals

In every round a softmax lane arrives once on P-full (offset 96) and then makes one election, on
which it arrives on the second P barrier (offset 112) or which it loses. So at every state the
second arrivals and the lost elections together are the P-full arrivals, less one between a round's
P-full arrival and its second arrival or lost election (`p2_count`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (nexts lz allSites mem_allSites sig)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- A second P arrival of lane `g`, or an election it loses after the startup. -/
def isP2 (L : Launch) (g : Nat) (e : Event) : Bool :=
  match e.kind with
  | .arrive m _ _ _ _ => decide (m = Softmax.bl L g 112)
  | .elect _ _ ld => decide (174 ≤ e.pc) && decide (laneOf L g ≠ ld)
  | _ => false

/-- A round's sites from its P-full arrival to its second arrival or lost election. -/
def midP2 : Softmax.Site → Nat
  | .pst _ q => if q.val = 3 then 1 else 0
  | .pwst _ c => if c.val = 1 then 1 else 0
  | .pws _ | .pel _ | .parr2 _ => 1
  | _ => 0

/-- How a move from `s` changes `midP2`. -/
def midOk (s s' : Softmax.Site) : Bool :=
  match s with
  | .parr _ => midP2 s' == 1
  | .pel _ => midP2 s' == if s'.isParr2 then 1 else 0
  | .parr2 _ => midP2 s' == 0
  | _ => midP2 s' == midP2 s

private theorem mid_moves : [false, true].all (fun lz =>
    allSites.all fun s => (nexts lz s).all (midOk s)) = true := by decide +kernel

private theorem mid_move {b : Bool} {s s' : Softmax.Site} (h : s' ∈ nexts b s) :
    midOk s s' = true := by
  have h1 := List.all_eq_true.mp mid_moves b (by cases b <;> simp)
  exact List.all_eq_true.mp (List.all_eq_true.mp h1 s (mem_allSites s)) s' h

private theorem pel_pc (r : Softmax.Rd) : 174 ≤ (Softmax.Site.pel r).pc := by
  cases r <;> decide

private theorem start_pc (j : Fin 16) : (Startup.Site.elect j).pc < 174 := by
  revert j; decide

private theorem bl_inj {a b : Nat} : Softmax.bl L g a = Softmax.bl L g b ↔ a = b := by
  simp [Softmax.bl]

/-- **The relation at a thread state.** -/
def P2Inv (p : Params) (L : Launch) (g : Nat) : (thread p L g).D → Nat → Prop
  | (.inl _, nn), n => n = 0 ∧ nn (.soft (.arrive 96)) = 0
  | (.inr ⟨.softmax, d⟩, nn), n =>
      nn .ub = 0 → n + midP2 d.site = nn (.soft (.arrive 96))
  | _, _ => True

/-- A softmax lane's arrivals are on its site's barrier. -/
theorem soft_arr_loc {d : Softmax.D} (hev : Softmax.Ev p L g d e) :
    ∀ m tx c rel sc, e.kind = .arrive m tx c rel sc →
      m = Softmax.bl L g (Softmax.arrOff d.site) := by
  intro m tx c rel sc hk
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  rcases soft_mbar hev (l := m) rfl with ⟨-, hl, -⟩ | ⟨_, _, hk, -⟩
  · exact hl
  · cases hk

/-- The P-full arrivals are the first arrivals' sites'. -/
theorem soft_arr96 {d : Softmax.D} (hw : g % L.block / 32 < 8) (hev : Softmax.Ev p L g d e) :
    cls L g (.soft (.arrive 96)) e = true ↔ ∃ r, d.site = .parr r := by
  have harr := soft_arr_loc hev
  obtain ⟨site, v, kk, acc⟩ := d
  constructor
  · intro h
    obtain ⟨pc, kind⟩ := e
    cases kind <;> simp [cls, Softmax.cls, Softmax.Cnt.pointed] at h
    rw [harr _ _ _ _ _ rfl, bl_inj] at h
    cases site <;> simp_all [Softmax.arrOff]
  · rintro ⟨r, hr⟩
    simp only at hr
    subst hr
    simp only [Softmax.Ev] at hev
    simp [cls, Softmax.cls, Softmax.Cnt.pointed, hw, hev, Softmax.arrOff]

/-- The softmax role's step keeps the relation. -/
private theorem step_soft {d d' : Softmax.D} {nn : Cls → Nat} {n : Nat}
    (hw : g % L.block / 32 < 8) (hev : Softmax.Ev p L g d e) (hub : ∀ f, e.kind ≠ .ub f)
    (hs : Softmax.Control.PlaceStep L g d d' e)
    (hI : n + midP2 d.site = nn (.soft (.arrive 96))) :
    (n + if isP2 L g e then 1 else 0) + midP2 d'.site =
      nn (.soft (.arrive 96)) + if cls L g (.soft (.arrive 96)) e then 1 else 0 := by
  have harr := soft_arr_loc hev
  -- the two classes by the site
  have h96 := soft_arr96 hw hev
  have hP2 : ∀ (hne : ∀ r, d.site ≠ .pel r), isP2 L g e = true ↔ ∃ r, d.site = .parr2 r := by
    intro hne
    constructor
    · intro h
      unfold isP2 at h
      split at h
      · rename_i hk
        have hk' := harr _ _ _ _ _ hk
        simp only [decide_eq_true_eq] at h
        rw [hk', bl_inj] at h
        revert h
        cases d.site <;> simp [Softmax.arrOff]
      · rename_i hk
        obtain ⟨r, hr, -⟩ := soft_elect_site hev hk
        exact absurd hr (hne r)
      · cases h
    · rintro ⟨r, hr⟩
      obtain ⟨site, v, kk, acc⟩ := d
      simp only at hr
      subst hr
      simp only [Softmax.Ev] at hev
      simp [isP2, hev, Softmax.arrOff]
  rcases hs with ⟨hs', hno⟩ | hM
  · -- the state stays at its site: no arrival and no election
    have h1 : isP2 L g e = false ∧ cls L g (.soft (.arrive 96)) e = false := by
      rcases hno with ⟨_, _, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨hd, hk0⟩
      · constructor <;> simp [isP2, cls, Softmax.cls, hk]
      · constructor <;> simp [isP2, cls, Softmax.cls, hk]
      · have hk : e.kind = .tc .waitLd := by
          obtain ⟨site, v, kk, acc⟩ := d
          cases site <;> simp [Softmax.Site.delayed] at hd
          simp only at hk0
          subst hk0
          simp [Softmax.Ev, Softmax.Site.delayed, hd] at hev
          exact hev
        constructor <;> simp [isP2, cls, Softmax.cls, hk]
    rw [h1.1, h1.2, hs']
    simpa using hI
  · have hmid := mid_move hM.1
    by_cases hpel : ∃ r, d.site = .pel r
    · obtain ⟨r, hr⟩ := hpel
      have hl := hM.2 (by rw [hr]; rfl)
      have h0 : cls L g (.soft (.arrive 96)) e = false := by
        rw [Bool.eq_false_iff]
        intro h
        obtain ⟨r', hr'⟩ := h96.mp h
        rw [hr] at hr'
        cases hr'
      obtain ⟨inst, ld, hpc, hk⟩ : ∃ inst ld, e.pc = d.site.pc ∧
          e.kind = .elect (2 ^ 32 - 1) inst ld := by
        obtain ⟨site, v, kk, acc⟩ := d
        simp only at hr
        subst hr
        simp only [Softmax.Ev] at hev
        rcases hev with h | ⟨f, h⟩
        · exact h
        · exact absurd h (hub f)
      have hl' := hl _ _ _ hk
      have hpc' : 174 ≤ e.pc := by rw [hpc, hr]; exact pel_pc r
      rw [hr] at hmid hI
      simp only [midOk, beq_iff_eq] at hmid
      simp only [midP2] at hI
      rw [h0, hmid]
      by_cases hld : laneOf L g = ld
      · have := hl'.mpr hld
        simp [isP2, hk, hld, this]
        omega
      · have : d'.site.isParr2 = false := by
          rw [Bool.eq_false_iff]; exact fun h => hld (hl'.mp h)
        simp [isP2, hk, hld, this, hpc']
        omega
    · have hne : ∀ r, d.site ≠ .pel r := fun r hr => hpel ⟨r, hr⟩
      have hP2' := hP2 hne
      by_cases ha : ∃ r, d.site = .parr r
      · have h1 := h96.mpr ha
        have h2 : isP2 L g e = false := by
          rw [Bool.eq_false_iff]
          intro h
          obtain ⟨r, hr⟩ := ha
          obtain ⟨r', hr'⟩ := hP2'.mp h
          rw [hr] at hr'; cases hr'
        obtain ⟨r, hr⟩ := ha
        rw [hr] at hmid hI
        simp only [midOk, beq_iff_eq] at hmid
        simp only [midP2] at hI
        simp [h1, h2, hmid]
        omega
      · have h1 : cls L g (.soft (.arrive 96)) e = false := by
          rw [Bool.eq_false_iff]; exact fun h => ha (h96.mp h)
        by_cases hb : ∃ r, d.site = .parr2 r
        · have h2 := hP2'.mpr hb
          obtain ⟨r, hr⟩ := hb
          rw [hr] at hmid hI
          simp only [midOk, beq_iff_eq] at hmid
          simp only [midP2] at hI
          simp [h1, h2, hmid]
          omega
        · have h2 : isP2 L g e = false := by
            rw [Bool.eq_false_iff]; exact fun h => hb (hP2'.mp h)
          have hm' : midP2 d'.site = midP2 d.site := by
            revert hmid hne ha hb
            cases d.site <;> simp [midOk]
          simp [h1, h2, hm', hI]

set_option maxHeartbeats 1000000 in
/-- **A softmax lane's second P arrivals and lost elections** at every state. -/
theorem p2_count (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hg : g < L.threads) :
    ∀ k σ, Frame.NoUbBefore X g k → Frame.stateAt (thread p L) X g k = some (some σ) →
      P2Inv p L g σ (((X.tr g).take k).countP (isP2 L g)) := by
  refine Frame.RoleTable.countInvU (T := table p L) (S := fun g => g < L.threads)
    (fun g hg => thread_sound hp hg) hX (table_shape_of hp hFw)
    (table_followed hp hX hFw) hg (isP2 L g) (P := fun σ n => P2Inv p L g σ n) ⟨rfl, rfl⟩ ?_
  rintro ⟨σ1, nn⟩ e ⟨σ1', nn'⟩ n hJ hi hev hB hn hJ'
  obtain ⟨h1, rfl⟩ := Code.counted_next_some (C := glued p L g) hn
  rcases σ1 with s | ⟨i, d⟩
  · -- the startup makes no arrival, and its elections are before pc 174
    obtain ⟨rfl, h0⟩ := hB
    have hEv : Startup.Ev L g s e := hev
    have hq : isP2 L g e = false ∧ cls L g (.soft (.arrive 96)) e = false := by
      obtain ⟨site, x1, x2, x3⟩ := s
      cases site with
      | enter r => exact absurd hi.2 (by simp [exit])
      | sh j =>
        fin_cases j <;> simp only [Startup.Ev] at hEv <;> obtain ⟨_, _, hk⟩ := hEv <;>
          constructor <;> simp [isP2, cls, Softmax.cls, hk]
      | fence => simp only [Startup.Ev] at hEv; constructor <;> simp [isP2, cls, Softmax.cls, hEv]
      | bar => simp only [Startup.Ev] at hEv; constructor <;> simp [isP2, cls, Softmax.cls, hEv]
      | elect j =>
        simp only [Startup.Ev] at hEv
        rcases hEv with ⟨_, _, hpc, hk⟩ | ⟨_, hk⟩
        · have := start_pc j
          constructor
          · simp only [isP2, hk, hpc, Bool.and_eq_false_iff, decide_eq_false_iff_not]
            exact .inl (by omega)
          · simp [cls, Softmax.cls, hk]
        · constructor <;> simp [isP2, cls, Softmax.cls, hk]
      | init q =>
        simp only [Startup.Ev] at hEv
        rcases hEv with ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> constructor <;> simp [isP2, cls, Softmax.cls, hk]
    have hb : Code.bump (cls L g) nn e (.soft (.arrive 96)) = 0 := by
      simp only [Code.bump, hq.2, h0, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    simp only [hq.1, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
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
          cases r <;> first
            | trivial
            | (intro _; simp only [hb]; rfl)
        · exact ⟨rfl, hb⟩
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
          intro hub
          have hub0 : nn .ub = 0 := Nat.eq_zero_of_le_zero
            (hub ▸ Nat.le_add_right (nn .ub) _)
          have hw : g % L.block / 32 < 8 := hi.2
          have hsc := Softmax.Control.succ_places (d := d) hr
          exact step_soft hw hev.1 hev.2 hsc (hB hub0)
        | _ => trivial

/-- **A softmax lane's second P arrivals before an event of its role.** -/
theorem p2_before (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (he : X.get (g, k) = some e)
    {d : Softmax.Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (SmWarp.sinj p L g d n))) :
    ((X.tr g).take k).countP (isP2 L g) + midP2 d.site =
      ((X.tr g).take k).countP (cls L g (.soft (.arrive 96))) := by
  rw [count hσ]
  exact p2_count hp hX hFw (Frame.lt_of_get hX he) k _ (Frame.noUbBefore_of_get hX he) hσ (ub_zero
      hX he hσ)

/-! ### The election before a second arrival -/

/-- An election of the full mask that lane `g` wins. -/
def isWonEl (L : Launch) (g : Nat) (e : Event) : Bool :=
  match e.kind with
  | .elect mk _ ld => decide (mk = 2 ^ 32 - 1) && decide (laneOf L g = ld)
  | _ => false

private theorem parr2_from : [false, true].all (fun lz => allSites.all fun s =>
    (nexts lz s).all fun s' => !s'.isParr2 || (match s with | .pel _ => true | _ => false)) =
      true := by decide +kernel

/-- At a second arrival the lane has won an election. -/
def WonInv (p : Params) (L : Launch) (g : Nat) : (thread p L g).D → Nat → Prop
  | (.inr ⟨.softmax, d⟩, nn), n => nn .ub = 0 → d.site.isParr2 = true → 1 ≤ n
  | _, _ => True

set_option maxHeartbeats 1000000 in
/-- **A lane at its second arrival has won an election.** -/
theorem won_count (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hg : g < L.threads) :
    ∀ k σ, Frame.NoUbBefore X g k → Frame.stateAt (thread p L) X g k = some (some σ) →
      WonInv p L g σ (((X.tr g).take k).countP (isWonEl L g)) := by
  refine Frame.RoleTable.countInvU (T := table p L) (S := fun g => g < L.threads)
    (fun g hg => thread_sound hp hg) hX (table_shape_of hp hFw)
    (table_followed hp hX hFw) hg (isWonEl L g) (P := fun σ n => WonInv p L g σ n) trivial ?_
  rintro ⟨σ1, nn⟩ e ⟨σ1', nn'⟩ n hJ hi hev hB hn hJ'
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
          cases r <;> first
            | trivial
            | (intro _ h; exact absurd h Bool.false_ne_true)
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
          intro hub hp2
          have hub0 : nn .ub = 0 := Nat.eq_zero_of_le_zero
            (hub ▸ Nat.le_add_right (nn .ub) _)
          have hsc := Softmax.Control.succ_places (d := d) hr
          rcases hsc with ⟨hs', -⟩ | hM
          · change d1.site = d.site at hs'
            have := hB hub0 (by rw [← hs']; exact hp2)
            omega
          · have h2 := List.all_eq_true.mp parr2_from (lz L g) (by cases lz L g <;> simp)
            have h3 := List.all_eq_true.mp (List.all_eq_true.mp h2 d.site (mem_allSites _))
              d1.site hM.1
            rw [hp2] at h3
            obtain ⟨site, v, kk, acc⟩ := d
            cases site <;> simp at h3
            rename_i r
            have hEv : Softmax.Ev p L g ⟨.pel r, v.scheduler, kk, acc⟩ e := hev.1
            simp only [Softmax.Ev] at hEv
            rcases hEv with ⟨inst, ld, -, hk⟩ | ⟨f, hk⟩
            · have hl := (hM.2 rfl _ _ _ hk).mp hp2
              simp [isWonEl, hk, hl]
            · exact absurd hk (hev.2 f)
        | _ => trivial

end
end PTX.Kernels.TmlFa4Fwd.Proof
