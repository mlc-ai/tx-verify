-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.WorkerCall
public import Kernels.InklingRelDecode.Proof.Dispatch.IdleWarp
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof PTX.Frame

noncomputable section

private def idleAt {Q L g} : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.dispatch _ _),.inl s⟩,_) => Dispatch.IdleLow (g%L.block/32) s ∧
    s.site≠.loaderEntry ∧ s.site≠.mmaEntry
  | _ => True

private theorem idle_start {Q L g} (s : Startup.D) (n : Cls → Nat) :
    idleAt (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) := by
  obtain ⟨s,t,x,w⟩ := s
  cases s <;> first | trivial |
    (rename_i r; cases r <;> first | trivial | exact ⟨fun h => by simp at h,nofun,nofun⟩)

private theorem idle_enter {Q L g w x n} (d : Dispatch.D)
    (ok : Dispatch.IdleLow (g%L.block/32) d) :
    @idleAt Q L g (.inr ⟨.inl (.dispatch w x),Code.enter (Dispatch.code L g
      (startRegs Q L g w x) x 0) (workerFrag Q L g w x) workerEntry d⟩,n) := by
  obtain ⟨s,r⟩ := d
  cases s <;> first | trivial | exact ⟨ok,nofun,nofun⟩

private theorem idle_step {Q L m X g k s sn ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X)
    (he : X.get (g,k)=some ev) (hs : stateAt (thread Q L) X g k=some (some s))
    (ok : idleAt s) (hn : (thread Q L g).next s ev=some (some sn)) : idleAt sn := by
  obtain ⟨s,n⟩ := s
  obtain ⟨sn,nn⟩ := sn
  obtain ⟨mv,_⟩ := Code.counted_next_some hn
  rcases s with s|⟨r,s⟩
  · obtain ⟨_,_,rfl⟩ := Code.glue_inl_some mv
    exact idle_start ..
  · obtain ⟨_,step,rfl⟩ := Code.glue_inr_some mv
    rcases r with (r|r)
    · cases r with
      | prologue => trivial
      | dispatch w x =>
        rcases s with d|⟨i,d⟩
        · have ⟨low,_⟩ := worker_warp hp hX (List.getElem?_eq_some_iff.mp he).1.le hs
          change 128≤g%L.block at low
          change (Dispatch.next L g d ev).map _ = _ at step
          obtain ⟨_,move,h⟩ := Option.map_eq_some_iff.mp step
          obtain ⟨dn,rfl,rfl⟩ := Option.map_eq_some_iff.mp h
          apply idle_enter
          have lt := Nat.mod_lt g (show L.block>0 by rw [hp.block]; omega)
          rw [hp.block] at lt
          exact Dispatch.idle_next (by omega) (by rw [hp.block]; omega)
            (fun _ _ read kind => dispatch_bytes hp hX words he hs read kind) ok.1 move
        · change ((workerFrag Q L g w x i).next d ev).map _ = _ at step
          obtain ⟨_,_,h⟩ := Option.map_eq_some_iff.mp step
          obtain ⟨dn,rfl,rfl⟩ := Option.map_eq_some_iff.mp h
          cases i <;> obtain ⟨site,rest⟩ := dn <;> cases site <;>
            first | trivial | exact ⟨fun h => by simp at h,nofun,nofun⟩
    · trivial

/-- **A dispatch state at an idle site is a state of warp 4 or 5.** -/
theorem idle_warp {Q L m X g k w x s n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X)
    (hk : k≤(X.tr g).length) (hs : stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.dispatch w x),.inl s⟩,n))) :
    Dispatch.IdleLow (g%L.block/32) s ∧ s.site≠.loaderEntry ∧ s.site≠.mmaEntry := by
  have reach {j st} (bound : j≤(X.tr g).length)
      (atSt : stateAt (thread Q L) X g j=some (some st)) : idleAt st := by
    induction j generalizing st with
    | zero => rw [stateAt_zero] at atSt; cases atSt; exact idle_start ..
    | succ j ih =>
      have ev := List.getElem?_eq_getElem (l := X.tr g) (i := j) (by omega)
      rw [stateAt_succ ev] at atSt
      rcases prev : stateAt (thread Q L) X g j with _|_|old <;> rw [prev] at atSt <;>
        try solve | cases atSt
      exact idle_step hp hX words ev prev (ih (by omega) prev) atSt
  exact reach hk hs

end
end PTX.Kernels.InklingRelDecode.Proof
