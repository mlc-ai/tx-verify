-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Kernels.InklingRelDecode.Proof.Common.PublicationPrefix
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Lemmas.Flow.GlueStep
public import Kernels.InklingRelDecode.Proof.Common.DispatchRef

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof PTX.Frame

noncomputable section

private def called {Q L g w x} : (workerCode Q L g w x).D → Prop
  | .inl _ => True
  | .inr ⟨.loader r,_⟩ => g%L.block/32=6 ∧ r=0
  | .inr ⟨.mma r,_⟩ => g%L.block/32=7 ∧ r=0

private def entered {Q L g} : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.dispatch _ _),s⟩,_) => called s
  | _ => True

private theorem call_enter {Q L g w x} (d : Dispatch.D) (ok : Dispatch.Called (g%L.block/32) d) :
    called (Code.enter (Dispatch.code L g (startRegs Q L g w x) x 0)
      (workerFrag Q L g w x) workerEntry d) := by
  obtain ⟨s,r⟩ := d
  cases s <;> first | trivial | exact ok.1 rfl | exact ok.2 rfl

private theorem call_back {Q L g w x i} (s : (workerFrag Q L g w x i).D)
    (ok : @called Q L g w x (.inr ⟨i,s⟩)) :
    called (Code.backEnter (Dispatch.code L g (startRegs Q L g w x) x 0)
      (workerFrag Q L g w x) workerEntry (workerBack Q L g w x) i s) := by
  cases i <;> obtain ⟨site,rest⟩ := s <;> cases site <;> trivial

theorem dispatch_bytes {Q L m X g k w x s n ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X)
    (he : X.get (g,k)=some ev) (hs : stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.dispatch w x),.inl s⟩,n)))
    (read : s.site=.read) {a bs} (kind : ev.kind=.rd a bs) :
    bs=[(Proof.b32 (if s.round=0 then 16777730 else 50529027)).toBytes[g%L.block/32-4]?] := by
  have hg := Frame.lt_of_get hX he
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by rw [kind]; simp)
  change ev.pc=s.site.pc at pc
  rw [read] at pc
  have eq : ev=⟨2340,.rd a bs⟩ := by cases ev; congr
  have byte := words (eq ▸ he)
  have phase := publication_prefix hp hX hg (Frame.noUbBefore_of_get hX he) hs
  change _=3*s.round+Dispatch.publicationOffset s.site at phase
  rw [read] at phase
  change _=3*s.round+1 at phase
  simpa only [show ((X.tr g).take k).countP (Execution.isBarId 1)=1 ↔ s.round=0 by omega]
    using byte

theorem dispatch_called {Q L m X g k w x s n ev sn} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X)
    (he : X.get (g,k)=some ev) (hs : stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.dispatch w x),.inl s⟩,n)))
    (move : Dispatch.next L g s ev=some (some sn)) : Dispatch.Called (g%L.block/32) sn := by
  have ⟨low,_⟩ := worker_warp hp hX (List.getElem?_eq_some_iff.mp he).1.le hs
  change 128≤g%L.block at low
  have high : g%L.block<256 := by rw [hp.block]; omega
  exact Dispatch.called_next (by omega) (by omega)
    (fun _ _ read kind => dispatch_bytes hp hX words he hs read kind) move

/-- A dispatch step keeps the round's sites and the busy warps' calls. -/
theorem dispatch_ref {Q L m X g k w x s n ev sn} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X)
    (he : X.get (g,k)=some ev) (hs : stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.dispatch w x),.inl s⟩,n)))
    (al : Dispatch.Allowed s) (bz : Dispatch.Busy (g%L.block/32) s)
    (move : Dispatch.next L g s ev=some (some sn)) :
    Dispatch.Allowed sn ∧ Dispatch.Busy (g%L.block/32) sn := by
  have ⟨low,_⟩ := worker_warp hp hX (List.getElem?_eq_some_iff.mp he).1.le hs
  change 128≤g%L.block at low
  have high : g%L.block<256 := by rw [hp.block]; omega
  have read : ∀ a bs, s.site=.read → ev.kind=.rd a bs →
      bs=[(Proof.b32 (if s.round=0 then 16777730 else 50529027)).toBytes[g%L.block/32-4]?] :=
    fun _ _ read kind => dispatch_bytes hp hX words he hs read kind
  exact ⟨Dispatch.allowed_next (by omega) (by omega) read al move,
    Dispatch.busy_next (by omega) (by omega) read bz move⟩

private theorem step_worker {Q L m X g k w x d n ev dn} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X)
    (he : X.get (g,k)=some ev) (hs : stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.dispatch w x),d⟩,n))) (ok : called d)
    (step : (workerCode Q L g w x).next d ev=some (some dn)) : called dn := by
  rcases d with s|⟨i,s⟩
  · change (Dispatch.next L g s ev).map _ = _ at step
    obtain ⟨_,move,h⟩ := Option.map_eq_some_iff.mp step
    obtain ⟨sn,rfl,rfl⟩ := Option.map_eq_some_iff.mp h
    apply call_enter
    exact dispatch_called hp hX words he hs move
  · change ((workerFrag Q L g w x i).next s ev).map _ = _ at step
    obtain ⟨_,_,h⟩ := Option.map_eq_some_iff.mp step
    obtain ⟨sn,rfl,rfl⟩ := Option.map_eq_some_iff.mp h
    apply call_back
    cases i <;> exact ok

private theorem enter_start {Q L g} (s : Startup.D) (n : Cls → Nat) :
    entered (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) := by
  obtain ⟨s,t,x,w⟩ := s
  cases s <;> first | trivial | (rename_i r; cases r <;> trivial)

private theorem step_call {Q L m X g k s sn ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X)
    (he : X.get (g,k)=some ev) (hs : stateAt (thread Q L) X g k=some (some s))
    (ok : entered s) (hn : (thread Q L g).next s ev=some (some sn)) : entered sn := by
  obtain ⟨s,n⟩ := s
  obtain ⟨sn,nn⟩ := sn
  obtain ⟨move,_⟩ := Code.counted_next_some hn
  rcases s with s|⟨r,s⟩
  · obtain ⟨_,_,rfl⟩ := Code.glue_inl_some move
    exact enter_start ..
  · obtain ⟨_,step,rfl⟩ := Code.glue_inr_some move
    rcases r with (r|r)
    · cases r with
      | prologue => trivial
      | dispatch => exact step_worker hp hX words he hs ok step
    · trivial

theorem worker_called {Q L m X g k w x i s n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X)
    (hk : k≤(X.tr g).length) (hs : stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.dispatch w x),.inr ⟨i,s⟩⟩,n))) :
    match i with
    | .loader r => g%L.block/32=6 ∧ r=0
    | .mma r => g%L.block/32=7 ∧ r=0 := by
  have reach {j st} (bound : j≤(X.tr g).length)
      (atSt : stateAt (thread Q L) X g j=some (some st)) : entered st := by
    induction j generalizing st with
    | zero => rw [stateAt_zero] at atSt; cases atSt; exact enter_start ..
    | succ j ih =>
      have ev := List.getElem?_eq_getElem (l := X.tr g) (i := j) (by omega)
      rw [stateAt_succ ev] at atSt
      rcases prev : stateAt (thread Q L) X g j with _|_|old <;> rw [prev] at atSt <;>
        try solve | cases atSt
      exact step_call hp hX words ev prev (ih (by omega) prev) atSt
  have result := reach hk hs
  cases i <;> exact result

end
end PTX.Kernels.InklingRelDecode.Proof
