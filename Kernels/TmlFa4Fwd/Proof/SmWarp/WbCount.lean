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
public import Lemmas.Order.WarpBarOrdinal
import Std.Tactic.BVDecide.Normalize.Prop

import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Places

@[expose] public section

/-! # A softmax lane's warp barriers

In every round a softmax lane arrives once on P-full (offset 96) and then makes one warp barrier, so
at every state its warp barriers are its P-full arrivals, less one between a round's P-full arrival
and its warp barrier (`wb_count`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (nexts lz allSites mem_allSites sig)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- A warp barrier. -/
def isWb (e : Event) : Bool := match e.kind with | .warpBar .. => true | _ => false

/-- A round's sites from its P-full arrival to its warp barrier. -/
def midWb : Softmax.Site → Nat
  | .pst _ q => if q.val = 3 then 1 else 0
  | .pwst _ c => if c.val = 1 then 1 else 0
  | .pws _ => 1
  | _ => 0

/-- How a move from `s` changes `midWb`. -/
def wbOk (s s' : Softmax.Site) : Bool :=
  match s with
  | .parr _ => midWb s' == 1
  | .pws _ => midWb s' == 0
  | _ => midWb s' == midWb s

private theorem wb_moves : [false, true].all (fun lz =>
    allSites.all fun s => (nexts lz s).all (wbOk s)) = true := by decide +kernel

private theorem wb_move {b : Bool} {s s' : Softmax.Site} (h : s' ∈ nexts b s) :
    wbOk s s' = true := by
  have h1 := List.all_eq_true.mp wb_moves b (by cases b <;> simp)
  exact List.all_eq_true.mp (List.all_eq_true.mp h1 s (mem_allSites s)) s' h

/-- A warp barrier is fired at its site, with the full mask. -/
theorem soft_wb_site {d : Softmax.D} (hev : Softmax.Ev p L g d e) {mask inst : Nat}
    (hk : e.kind = .warpBar mask inst) : (∃ r, d.site = .pws r) ∧ mask = 4294967295 := by
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  obtain ⟨s, v, kk, acc⟩ := d
  cases s <;> simp only [Softmax.Ev] at hev
  case pws r =>
    rcases hev with ⟨i, h⟩ | ⟨f, h⟩
    · cases h
      exact ⟨⟨r, rfl⟩, rfl⟩
    · cases h
  case down | up | total | pre | tiles =>
    exfalso
    simp only [Epilogue.Ev, Softmax.Site.toE] at hev
    all_goals (obtain ⟨_, _, h⟩ := hev; cases h)
  all_goals exfalso
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals simp_all [Softmax.rdOrUb, Softmax.tcLdOrUb]

/-- **The relation at a thread state.** -/
def WbInv (p : Params) (L : Launch) (g : Nat) : (thread p L g).D → Nat → Prop
  | (.inl _, nn), n => n = 0 ∧ nn (.soft (.arrive 96)) = 0
  | (.inr ⟨.softmax, d⟩, nn), n =>
      nn .ub = 0 → n + midWb d.site = nn (.soft (.arrive 96))
  | _, _ => True

/-- The softmax role's step keeps the relation. -/
private theorem wb_step {d d' : Softmax.D} {nn : Cls → Nat} {n : Nat}
    (hw : g % L.block / 32 < 8) (hev : Softmax.Ev p L g d e) (hub : ∀ f, e.kind ≠ .ub f)
    (hs : Softmax.Control.PlaceStep L g d d' e)
    (hI : n + midWb d.site = nn (.soft (.arrive 96))) :
    (n + if isWb e then 1 else 0) + midWb d'.site =
      nn (.soft (.arrive 96)) + if cls L g (.soft (.arrive 96)) e then 1 else 0 := by
  have h96 : cls L g (.soft (.arrive 96)) e = true ↔ ∃ r, d.site = .parr r := by
    constructor
    · intro h
      obtain ⟨pc, kind⟩ := e
      cases kind <;> simp [cls, Softmax.cls, Softmax.Cnt.pointed] at h
      rename_i m tx c rel sc
      rcases soft_mbar hev (l := m) rfl with ⟨-, hl, -⟩ | ⟨_, _, hk, -⟩
      swap
      · cases hk
      have h' := h.1
      rw [hl] at h'
      have ho : Softmax.arrOff d.site = 96 := by simpa [Softmax.bl] using h'
      obtain ⟨site, v, kk, acc⟩ := d
      cases site <;> simp [Softmax.arrOff] at ho
      exact ⟨_, rfl⟩
    · rintro ⟨r, hr⟩
      obtain ⟨site, v, kk, acc⟩ := d
      simp only at hr
      subst hr
      simp only [Softmax.Ev] at hev
      simp [cls, Softmax.cls, Softmax.Cnt.pointed, hw, hev, Softmax.arrOff]
  have hwb : isWb e = true ↔ ∃ r, d.site = .pws r := by
    constructor
    · intro h
      obtain ⟨pc, kind⟩ := e
      cases kind <;> simp [isWb] at h
      exact (soft_wb_site hev rfl).1
    · rintro ⟨r, hr⟩
      obtain ⟨site, v, kk, acc⟩ := d
      simp only at hr
      subst hr
      simp only [Softmax.Ev] at hev
      rcases hev with ⟨i, h⟩ | ⟨f, h⟩
      · simp [isWb, h]
      · exact absurd h (hub f)
  rcases hs with ⟨hs', hno⟩ | hM
  · -- the state stays at its site: no arrival and no warp barrier
    have h1 : isWb e = false ∧ cls L g (.soft (.arrive 96)) e = false := by
      rcases hno with ⟨_, _, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨hd, hk0⟩
      · constructor <;> simp [isWb, cls, Softmax.cls, hk]
      · constructor <;> simp [isWb, cls, Softmax.cls, hk]
      · have hk : e.kind = .tc .waitLd := by
          obtain ⟨site, v, kk, acc⟩ := d
          cases site <;> simp [Softmax.Site.delayed] at hd
          simp only at hk0
          subst hk0
          simp [Softmax.Ev, Softmax.Site.delayed, hd] at hev
          exact hev
        constructor <;> simp [isWb, cls, Softmax.cls, hk]
    rw [h1.1, h1.2, hs']
    simpa using hI
  · have hmid := wb_move hM.1
    by_cases ha : ∃ r, d.site = .parr r
    · have h1 := h96.mpr ha
      have h2 : isWb e = false := by
        rw [Bool.eq_false_iff]
        intro h
        obtain ⟨r, hr⟩ := ha
        obtain ⟨r', hr'⟩ := hwb.mp h
        rw [hr] at hr'; cases hr'
      obtain ⟨r, hr⟩ := ha
      rw [hr] at hmid hI
      simp only [wbOk, beq_iff_eq] at hmid
      simp only [midWb] at hI
      simp [h1, h2, hmid]
      omega
    · have h1 : cls L g (.soft (.arrive 96)) e = false := by
        rw [Bool.eq_false_iff]; exact fun h => ha (h96.mp h)
      by_cases hb : ∃ r, d.site = .pws r
      · have h2 := hwb.mpr hb
        obtain ⟨r, hr⟩ := hb
        rw [hr] at hmid hI
        simp only [wbOk, beq_iff_eq] at hmid
        simp only [midWb] at hI
        simp [h1, h2, hmid]
        omega
      · have h2 : isWb e = false := by
          rw [Bool.eq_false_iff]; exact fun h => hb (hwb.mp h)
        have hm' : midWb d'.site = midWb d.site := by
          revert hmid ha hb
          cases d.site <;> simp [wbOk]
        simp [h1, h2, hm', hI]

set_option maxHeartbeats 1000000 in
/-- **A softmax lane's warp barriers** at every state. -/
theorem wb_count (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hg : g < L.threads) :
    ∀ k σ, Frame.NoUbBefore X g k → Frame.stateAt (thread p L) X g k = some (some σ) →
      WbInv p L g σ (((X.tr g).take k).countP (isWb)) := by
  refine Frame.RoleTable.countInvU (T := table p L) (S := fun g => g < L.threads)
    (fun g hg => thread_sound hp hg) hX (table_shape_of hp hFw)
    (table_followed hp hX hFw) hg (isWb) (P := fun σ n => WbInv p L g σ n) ⟨rfl, rfl⟩ ?_
  rintro ⟨σ1, nn⟩ e ⟨σ1', nn'⟩ n hJ hi hev hB hn hJ'
  obtain ⟨h1, rfl⟩ := Code.counted_next_some (C := glued p L g) hn
  rcases σ1 with s | ⟨i, d⟩
  · -- the startup makes no arrival and no warp barrier
    obtain ⟨rfl, h0⟩ := hB
    have hEv : Startup.Ev L g s e := hev
    have hq : isWb e = false ∧ cls L g (.soft (.arrive 96)) e = false := by
      obtain ⟨site, x1, x2, x3⟩ := s
      cases site with
      | enter r => exact absurd hi.2 (by simp [exit])
      | sh j =>
        fin_cases j <;> simp only [Startup.Ev] at hEv <;> obtain ⟨_, _, hk⟩ := hEv <;>
          constructor <;> simp [isWb, cls, Softmax.cls, hk]
      | fence => simp only [Startup.Ev] at hEv; constructor <;> simp [isWb, cls, Softmax.cls, hEv]
      | bar => simp only [Startup.Ev] at hEv; constructor <;> simp [isWb, cls, Softmax.cls, hEv]
      | elect j =>
        simp only [Startup.Ev] at hEv
        rcases hEv with ⟨_, _, hpc, hk⟩ | ⟨_, hk⟩ <;> constructor <;>
          simp [isWb, cls, Softmax.cls, hk]
      | init q =>
        simp only [Startup.Ev] at hEv
        rcases hEv with ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> constructor <;> simp [isWb, cls, Softmax.cls, hk]
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
          exact wb_step hw hev.1 hev.2 hsc (hB hub0)
        | _ => trivial

/-- **A softmax lane's warp barriers before an event of its role.** -/
theorem wb_before (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (he : X.get (g, k) = some e)
    {d : Softmax.Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (SmWarp.sinj p L g d n))) :
    warpBars X g k + midWb d.site = n (.soft (.arrive 96)) := by
  have hw : warpBars X g k = ((X.tr g).take k).countP isWb := by
    refine List.countP_congr fun e _ => ?_
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp [Execution.isWarpBar, isWb]
  rw [hw]
  exact wb_count hp hX hFw (Frame.lt_of_get hX he) k _ (Frame.noUbBefore_of_get hX he) hσ (ub_zero
      hX he hσ)

end
end PTX.Kernels.TmlFa4Fwd.Proof
