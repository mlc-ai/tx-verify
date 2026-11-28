-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.RequestPrefix
public import Lemmas.Kernel.Safety.TableU
import Kernels.InklingRelDecode.Proof.Common.WorkerCall
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame PTX.Proof
noncomputable section

private theorem read_good {i : Fin 4} {r : Nat} {d}
    (h : Dispatch.readTarget [(b32 (if r=0 then 16777730 else 50529027)).toBytes[i.val]?] =
      some d) : DispatchClean ⟨d,r⟩ := by
  have := Dispatch.role_target i (decide (r=0))
  simp only [decide_eq_true_eq] at this
  rw [this] at h
  by_cases r0 : r=0
  · simp only [r0,ite_true] at h
    cases h
    subst r0
    split <;> try split
    all_goals simp [DispatchClean]
  · simp only [r0,ite_false] at h
    cases h
    simp [DispatchClean]
    omega

private theorem dispatch_good {Q L m X g k w x s n ev sn} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X)
    (he : X.get (g,k)=some ev) (hs : stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.dispatch w x),.inl s⟩,n)))
    (ok : DispatchClean s) (move : Dispatch.next L g s ev=some (some sn)) : DispatchClean sn := by
  obtain ⟨site,r⟩ := s
  cases site
  case read =>
    have ⟨low,_⟩ := worker_warp hp hX (List.getElem?_eq_some_iff.mp he).1.le hs
    change 128≤g%L.block at low
    have high : g%L.block<256 := by rw [hp.block]; omega
    simp only [Dispatch.next] at move
    split at move <;> try contradiction
    rename_i a bs kind
    have bytes := dispatch_bytes hp hX words he hs rfl kind
    let i : Fin 4 := ⟨g%L.block/32-4,by omega⟩
    rw [bytes] at move
    obtain ⟨dest,eq,h⟩ := Option.map_eq_some_iff.mp move
    cases h
    exact read_good (i := i) (r := r) eq
  all_goals simp only [Dispatch.next] at move
  all_goals repeat' split at move
  all_goals try contradiction
  all_goals cases move
  all_goals simp [DispatchClean] at ok ⊢
  all_goals omega

private theorem clean_start {Q L g} (s : Startup.D) (n : Cls → Nat) :
    requestClean (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g)
      Startup.Entry.pc) (Code.gatedExit Startup.enterOf (sel L g)) s,n) := by
  obtain ⟨s,t,x,w⟩ := s
  cases s <;> first | trivial |
    (rename_i r; cases r <;> first | trivial | exact ⟨nofun,nofun,nofun,nofun⟩)

private theorem clean_back {Q L g w x i} (s : (workerFrag Q L g w x i).D)
    (ok : @workerClean Q L g w x (.inr ⟨i,s⟩)) :
    workerClean (Q := Q) (L := L) (g := g) (w := w) (x := x)
      (Code.backEnter (Dispatch.code L g (startRegs Q L g w x) x 0) (workerFrag Q L g w x)
        workerEntry (workerBack Q L g w x) i s) := by
  cases i <;> obtain ⟨site,rest⟩ := s <;> cases site <;>
    first | exact ok | exact ⟨nofun,nofun,nofun,nofun⟩

private theorem clean_enter {Q L g w x} (d : Dispatch.D) (ok : DispatchClean d) :
    workerClean (Q := Q) (L := L) (g := g) (w := w) (x := x)
      (Code.enter (Dispatch.code L g (startRegs Q L g w x) x 0) (workerFrag Q L g w x)
        workerEntry d) := by
  obtain ⟨s,r⟩ := d
  cases s <;> first | trivial | exact ok.2.2.1 (by simp)

theorem request_clean_step {Q L m X g k s sn ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X)
    (he : X.get (g,k)=some ev) (hs : stateAt (thread Q L) X g k=some (some s))
    (ok : requestClean s) (hn : (thread Q L g).next s ev=some (some sn)) : requestClean sn := by
  obtain ⟨s,n⟩ := s
  obtain ⟨sn,nn⟩ := sn
  obtain ⟨move,_⟩ := Code.counted_next_some hn
  rcases s with s|⟨r,s⟩
  · obtain ⟨_,_,rfl⟩ := Code.glue_inl_some move
    exact clean_start ..
  · obtain ⟨_,step,rfl⟩ := Code.glue_inr_some move
    rcases r with (r|r)
    · cases r with
      | prologue => trivial
      | dispatch w x =>
        rcases s with s|⟨i,s⟩
        · change (Dispatch.next L g s ev).map _ = _ at step
          obtain ⟨_,mv,h⟩ := Option.map_eq_some_iff.mp step
          obtain ⟨sn,rfl,rfl⟩ := Option.map_eq_some_iff.mp h
          exact clean_enter _ (dispatch_good hp hX words he hs ok mv)
        · change ((workerFrag Q L g w x i).next s ev).map _ = _ at step
          obtain ⟨_,_,h⟩ := Option.map_eq_some_iff.mp step
          obtain ⟨sn,rfl,rfl⟩ := Option.map_eq_some_iff.mp h
          exact clean_back _ (by cases i <;> exact ok)
    · trivial

/-- **The count of register requests before an event is the state's.** -/
theorem request_prefix {Q L m X g k s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X)
    (hk : k≤(X.tr g).length) (nu : NoUbBefore X g k)
    (hs : stateAt (thread Q L) X g k=some (some s)) :
    ((X.tr g).take k).countP SetMaxNReg.isRequest = requests s ∧ requestClean s := by
  induction k generalizing s with
  | zero =>
    rw [stateAt_zero] at hs
    cases hs
    exact ⟨by simpa using (enter_requests ..).symm,clean_start ..⟩
  | succ k ih =>
    have ev := List.getElem?_eq_getElem (l := X.tr g) (i := k) (by omega)
    have clear := nu k (Nat.lt_succ_self k) _ ev
    rw [stateAt_succ ev] at hs
    rcases prev : stateAt (thread Q L) X g k with _|_|old <;> rw [prev] at hs <;>
      try solve | cases hs
    obtain ⟨count,ok⟩ := ih (by omega) (fun j hj => nu j (Nat.lt_succ_of_lt hj)) prev
    refine ⟨?_,request_clean_step hp hX words ev prev ok hs⟩
    obtain ⟨_,ins,_,_,_,hc,fire⟩ := fired_siteU (fun g hg => thread_sound hp hg) hX ev prev clear
    have hit := (Lib.request_fires hc fire).1
    rw [List.take_add_one,ev,List.countP_append,count,request_step ok hs]
    simp [hit]

end
end PTX.Kernels.InklingRelDecode.Proof
