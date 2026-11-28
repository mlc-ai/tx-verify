-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section
variable {Q : Params} {L : Launch} {g : Nat} {m : Mem0} {X : Execution}

private def side : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.prologue _),_⟩,_) => g%L.block<128
  | (.inr ⟨.inl (.dispatch _ x),_⟩,_) => g%L.block≥128 ∧ x=BitVec.ofNat 64 (g%L.block/32)
  | (.inr ⟨.inr _,_⟩,_) => False
  | _ => True

private theorem select_lane : ∀ tid : Fin 256, Startup.entryOf (BitVec.ofNat 64 (tid.val/32)) =
    if tid.val<128 then .dp else .worker := by decide +kernel

private theorem ordinary {s dn : Startup.D} {ev : Event} (site : s.site≠.shfl)
    (step : Startup.succ L g s ev=some (some dn)) : Startup.enterOf dn=none := by
  obtain ⟨site',tm,x,w⟩ := s
  cases site' <;> simp only [Startup.succ] at step
  all_goals repeat' split at step
  all_goals first | contradiction | (cases step; rfl)

private theorem side_step {k s sn ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k)=some ev) (hs : Frame.stateAt (thread Q L) X g k=some (some s))
    (old : side s) (step : (thread Q L g).next s ev=some (some sn)) : side sn := by
  obtain ⟨s,n⟩ := s
  obtain ⟨sn,nn⟩ := sn
  obtain ⟨next,_⟩ := Code.counted_next_some step
  rcases s with s|⟨r,d⟩
  · obtain ⟨dn,move,rfl⟩ := Code.glue_inl_some next
    by_cases sh : s.site=.shfl
    · have active : Startup.enterOf s=none := by simp [Startup.enterOf,sh]
      obtain ⟨kd,tm,x,w⟩ := s
      cases sh
      change Startup.succ L g ⟨.shfl,tm,x,w⟩ ev = some (some dn) at move
      cases ev with | mk pc kind =>
        cases kind <;> simp only [Startup.succ] at move <;> try contradiction
        have shape := start_ev hp hX he hs (by simp)
        obtain ⟨v,b,eq⟩ := shape
        cases eq
        have ord := startup_ordinal hp hX (List.getElem?_eq_some_iff.mp he).1.le active hs
        have recv := startup_recv hp hX he ord
        subst recv
        cases move
        have small : g%L.block<256 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
        have test := select_lane ⟨_,small⟩
        change Startup.entryOf (BitVec.ofNat 64 (g%L.block/32)) = _ at test
        unfold Code.enter Code.gatedExit Startup.enterOf
        dsimp only
        rw [test]
        by_cases low : g%L.block<128
        · simp only [low,↓reduceIte,Option.map_some,sel,side]
        · simpa only [low,↓reduceIte,Option.map_some,sel,side] using
            And.intro (Nat.le_of_not_gt low)
            (rfl : BitVec.ofNat 64 (g%L.block/32) = _)
    · have hx := ordinary sh move
      rw [enter_inl hx]
      trivial
  · obtain ⟨_,_,rfl⟩ := Code.glue_inr_some next
    rcases r with (r|r)
    · cases r <;> exact old
    · exact old

private theorem launch_lane {k s} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hk : k≤(X.tr g).length) (hs : Frame.stateAt (thread Q L) X g k=some (some s)) : side s := by
  induction k generalizing s with
  | zero =>
    rw [Frame.stateAt_zero] at hs
    cases hs
    change side (Q := Q) (L := L) (g := g) (Code.enter _ _ _ (Startup.init L g),_)
    rw [enter_inl enterOf_init]
    trivial
  | succ k ih =>
    have get := List.getElem?_eq_getElem (l := X.tr g) (i := k) (by omega)
    rw [Frame.stateAt_succ get] at hs
    rcases prev : Frame.stateAt (thread Q L) X g k with _|_|s' <;> rw [prev] at hs <;>
      try solve | cases hs
    exact side_step hp hX get prev (ih (by omega) prev) hs

theorem data_warp {k w d n} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hk : k≤(X.tr g).length) (hs : Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.prologue w),d⟩,n))) : g%L.block<128 :=
  launch_lane hp hX hk hs

theorem no_stub {k r d n} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hk : k≤(X.tr g).length) (hs : Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inr r,d⟩,n))) : False := launch_lane hp hX hk hs
theorem worker_warp {k w x d n} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hk : k≤(X.tr g).length) (hs : Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.dispatch w x),d⟩,n))) :
    128≤g%L.block ∧ x=BitVec.ofNat 64 (g%L.block/32) := launch_lane hp hX hk hs

/-- **A worker lane's states are the startup's and the dispatch warp's.** -/
theorem worker_lane {k s} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : 128 ≤ g % L.block) (hk : k ≤ (X.tr g).length)
    (hs : Frame.stateAt (thread Q L) X g k = some (some s)) :
    (∃ d n, s = (.inl d, n)) ∨ ∃ w x d n, s = (.inr ⟨.inl (.dispatch w x), d⟩, n) := by
  have h := launch_lane hp hX hk hs
  obtain ⟨σ, n⟩ := s
  rcases σ with σ | ⟨r, d⟩
  · exact .inl ⟨σ, n, rfl⟩
  · rcases r with (r | r)
    · cases r with
      | prologue w => exact absurd h (by simp only [side]; omega)
      | dispatch w x => exact .inr ⟨w, x, d, n, rfl⟩
    · exact absurd h id

end
end PTX.Kernels.InklingRelDecode.Proof
