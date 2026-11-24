-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Open
public import Kernels.TmlFa4Fwd.Proof.Softmax.Places
import Kernels.TmlFa4Fwd.Proof.Softmax.RefCases
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The steps of a softmax lane, and its `tcgen05` sites -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (nexts lz allSites mem_allSites sig)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The `tcgen05` sites. -/
def Softmax.Site.tcS : Softmax.Site → Bool
  | .sld _ _ | .sldw _ | .pst _ _ | .pwst _ _ => true
  | _ => false

/-- **What a step of a softmax lane does**: it stays, with no `tcgen05` event and no class; it makes
a delayed store's wait; or it moves. -/
def SoftMove (L : Launch) (g : Nat) (d d' : Softmax.Control.D) (e : Event) : Prop :=
  (d'.site = d.site ∧ ((∃ m par a sc, e.kind = .wait m par false a sc) ∨
      ∃ a bs, e.kind = .rd a bs) ∧ (d.site.delayed = true → d'.k = d.k)) ∨
    (d'.site = d.site ∧ d.site.delayed = true ∧ d.k = 0 ∧ d'.k = 1) ∨
    (d'.site ∈ nexts (lz L g) d.site ∧ (d'.site.delayed = true → d'.k = 0) ∧
      (d.site.isPoll = true → ∀ m par a sc, e.kind ≠ .wait m par false a sc) ∧
      (d.site.delayed = true → d.k ≠ 0))

theorem soft_move {d d' : Softmax.Control.D} {e : Event}
    (hn : Softmax.Control.succ p L g d e = some (some d')) : SoftMove L g d d' e := by
  have del : ∀ r, (r = .first ∨ r = .bias) → d.site = .pst r 0 →
      (d'.site = d.site ∧ d.site.delayed = true ∧ d.k = 0 ∧ d'.k = 1) ∨
      (d'.site ∈ nexts (lz L g) d.site ∧ (d'.site.delayed = true → d'.k = 0) ∧
        (d.site.isPoll = true → ∀ m par a sc, e.kind ≠ .wait m par false a sc) ∧
        (d.site.delayed = true → d.k ≠ 0)) := by
    intro r hr hs
    obtain ⟨site, v, k, acc⟩ := d
    simp only at hs
    subst hs
    by_cases hk : k = 0
    · left
      rcases hr with rfl | rfl <;>
        simp only [Softmax.Control.succ, Softmax.Control.D.scheduler, Softmax.succ, hk, ite_true,
          Option.map_some, Option.some.injEq] at hn <;>
        subst hn <;> exact ⟨rfl, rfl, hk, rfl⟩
    · right
      rcases hr with rfl | rfl <;>
        simp only [Softmax.Control.succ, Softmax.Control.D.scheduler, Softmax.succ, hk, ite_false,
          Option.map_some, Option.some.injEq] at hn <;>
        subst hn <;>
        exact ⟨by simp [nexts, Softmax.Control.erase, Softmax.pstNext],
          (fun h => by cases h), (fun h => by cases h), fun _ => hk⟩
  by_cases hd : d.site.delayed = true
  · have : ∃ r, (r = .first ∨ r = .bias) ∧ d.site = .pst r 0 := by
      revert hd
      cases d.site <;> simp [Softmax.Site.delayed]
      rename_i r q
      cases r <;> simp
      all_goals (intro h; revert h; revert q; decide)
    obtain ⟨r, hr, hs⟩ := this
    exact .inr (del r hr hs)
  have hd' : d.site.delayed = false := by simpa using hd
  have direct : (Softmax.succ p L g d.scheduler e).map (Option.map Softmax.Control.erase) =
      some (some d') → SoftMove L g d d' e := fun hn => by
    obtain ⟨x, hx, hm⟩ := Option.map_eq_some_iff.mp hn
    obtain ⟨a, rfl, rfl⟩ := Option.map_eq_some_iff.mp hm
    rcases Softmax.succ_cases hx with ⟨hs, -, -, hc⟩ | ⟨hM, hk, hp, -⟩
    · rcases hc with hc | hc | ⟨hc, -⟩
      · exact .inl ⟨hs, .inl hc, fun h => absurd h hd⟩
      · exact .inl ⟨hs, .inr hc, fun h => absurd h hd⟩
      · exact absurd hc hd
    · refine .inr (.inr ⟨hM, fun h => ?_, hp, fun h => absurd h hd⟩)
      show a.k = 0
      rw [hk]
      revert h
      show a.site.delayed = true → _
      cases a.site <;> simp [Softmax.Site.delayed, Softmax.kIn]
  obtain ⟨site, v, k, acc⟩ := d
  cases site with
  | sld r c =>
    simp only [Softmax.Control.succ] at hn
    split at hn
    · refine .inr (.inr ?_)
      cases r <;> cases hn
      · exact ⟨by by_cases hc : c.val = 3 <;> simp [nexts, hc], fun _ => rfl,
          (fun h => by cases h), fun h => absurd h hd⟩
      · exact ⟨by by_cases hc : c.val = 3 <;> simp [nexts, hc], fun _ => rfl,
          (fun h => by cases h), fun h => absurd h hd⟩
      · exact ⟨by simp [nexts], (fun h => by cases h), (fun h => by cases h),
          fun h => absurd h hd⟩
    · cases hn
  | bld b c =>
    simp only [Softmax.Control.succ] at hn
    split at hn
    · rename_i a bs hk
      split at hn
      · cases hn
        exact .inl ⟨rfl, .inr ⟨a, bs, hk⟩, fun h => absurd h hd⟩
      · cases hn
        exact .inr (.inr ⟨by simp only [nexts]; split <;> simp_all, fun _ => rfl,
          (fun h => by cases h),
          fun h => absurd h hd⟩)
    · cases hn
  | _ => exact direct hn

/-- A softmax event that is a `tcgen05` event is at a `tcgen05` site. -/
theorem soft_isTc {d : Softmax.D} {e : Event} (hev : Softmax.EvS p L g d e) :
    isTcColl e = d.site.tcS := by
  obtain ⟨hev, hub⟩ := hev
  have hub' : ∀ f, e.kind = .ub f → False := fun f h => hub f h
  obtain ⟨s, v, kk, acc⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [Softmax.Ev] at hev
  all_goals (try simp only [Epilogue.Ev, Softmax.Site.toE] at hev)
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals first
    | (subst_vars; rfl)
    | exact (hub' _ rfl).elim
    | exact (hub' _ ‹_›).elim

/-- A softmax event is no paired Tensor Memory operation. -/
theorem soft_no_res {d : Softmax.D} {e : Event} (hev : Softmax.EvS p L g d e) (grp : CtaGroup)
    (dst : _) (act : _) : e.kind ≠ .tc (.resource grp dst act) := by
  obtain ⟨hev, hub⟩ := hev
  obtain ⟨s, v, kk, acc⟩ := d
  obtain ⟨pc, kind⟩ := e
  rintro rfl
  cases s <;> simp only [Softmax.Ev] at hev
  all_goals (try simp only [Epilogue.Ev, Softmax.Site.toE] at hev)
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals first | contradiction | simp_all

end
end PTX.Kernels.TmlFa4Fwd.Proof
