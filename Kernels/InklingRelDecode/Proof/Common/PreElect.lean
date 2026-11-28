-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.ReferenceInduction
public import Kernels.InklingRelDecode.Proof.Common.WorkerCall
public import Kernels.InklingRelDecode.Proof.Common.WorkerBalance
public import Kernels.InklingRelDecode.Proof.Loader.PreElect
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame

def dispatchBefore (s : Dispatch.D) : Prop :=
  s.round=0 ∧ (s.site=.head ∨ s.site=.sync ∨ s.site=.read)

private def preWorker {Q L g w x} : (workerCode Q L g w x).D → Prop
  | .inl s => dispatchBefore s
  | .inr ⟨.loader _,_⟩ => True
  | .inr ⟨.mma _,_⟩ => False

private def beforeVote {Q L g} : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.dispatch _ _),s⟩,n) => n .elect=0 → preWorker s
  | _ => True

private theorem on_start {Q L g} (s : Startup.D) (n : Cls → Nat) :
    beforeVote (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) := by
  obtain ⟨site,t,x,w⟩ := s
  cases site <;> try trivial
  rename_i r
  cases r <;> first | trivial | exact fun _ => ⟨rfl,.inl rfl⟩

private theorem first_dispatch {Q L m X g k w x d n e dn} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X) (warp : g%L.block/32=6)
    (he : X.get (g,k)=some e) (hs : stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.dispatch w x),.inl d⟩,n))) (early : dispatchBefore d)
    (step : Dispatch.next L g d e=some (some dn)) :
    preWorker (Code.enter (Dispatch.code L g (startRegs Q L g w x) x 0)
      (workerFrag Q L g w x) workerEntry dn) := by
  obtain ⟨s,r⟩ := d
  obtain ⟨rfl,h|h|h⟩ := early
  · cases h; cases step; exact ⟨rfl,.inr (.inl rfl)⟩
  · cases h; cases step; exact ⟨rfl,.inr (.inr rfl)⟩
  · cases h
    simp only [Dispatch.next] at step
    split at step <;> try contradiction
    rename_i a bs kind
    have bytes := dispatch_bytes hp hX words he hs rfl kind
    rw [warp] at bytes
    have target : Dispatch.readTarget bs=some .loaderEntry :=
      bytes ▸ Dispatch.role_target (2 : Fin 4) true
    rw [target] at step
    cases step; trivial

theorem loader_before_vote {Q L m X g j w x d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (warp : g%L.block/32=6) (work : Iface.preloadCount Q L (g/L.block)<Lib.blocksOf Q L (g/L.block))
    (bound : j≤(X.tr g).length) (hs : stateAt (thread Q L) X g j =
      some (some (.inr ⟨.inl (.dispatch w x),.inl d⟩,n))) (nu : NoUbBefore X g j)
    (noVote : n .elect=0) : dispatchBefore d := by
  have h : beforeVote (Q := Q) (L := L) (g := g) (.inr ⟨.inl (.dispatch w x),.inl d⟩,n) := by
    apply reference_induction beforeVote _ _ bound hs (prefix_ub_zero hs nu)
    · apply on_start
    · rintro k ⟨s,c⟩ ev ⟨sn,cn⟩ he prev hu ih move
      obtain ⟨sub,count⟩ := Code.counted_next_some move
      change cn=Code.bump cls c ev at count
      subst cn
      rcases s with s|⟨r,s⟩
      · obtain ⟨_,_,rfl⟩ := Code.glue_inl_some sub
        apply on_start
      · obtain ⟨_,step,rfl⟩ := Code.glue_inr_some sub
        rcases r with (r|r)
        · cases r with
          | prologue => trivial
          | dispatch w x =>
            intro clear
            have vote : c .elect=0 := Nat.eq_zero_of_add_eq_zero_right clear
            have old := ih vote
            rcases s with s|⟨i,s⟩
            · change (Dispatch.next L g s ev).map _ = _ at step
              obtain ⟨_,go,h⟩ := Option.map_eq_some_iff.mp step
              obtain ⟨sn,rfl,rfl⟩ := Option.map_eq_some_iff.mp h
              exact first_dispatch hp hX words warp he prev old go
            · cases i with
              | mma => exact False.elim old
              | loader r =>
                change (Loader.next L g s ev).map _ = _ at step
                obtain ⟨_,go,h⟩ := Option.map_eq_some_iff.mp step
                obtain ⟨sn,rfl,rfl⟩ := Option.map_eq_some_iff.mp h
                have hg := lt_of_get hX he
                have clean := noUbBefore_of_get hX he
                obtain ⟨_,ref,ord,_⟩ := (reached_table hf hg clean prev).2
                have bal := loader_balance hp hX hf hg warp clean prev
                rw [vote,Nat.zero_add,ord] at bal
                have active := (Loader.pre_elect_time work (Lib.blocksOf_lt hp hg) ref bal).2
                have stay : sn.site≠.dispatch := fun back => active (Loader.before_dispatch go back)
                simp only [Code.backEnter,workerBack,stay,↓reduceIte]
                trivial
        · trivial
  exact h noVote

end PTX.Kernels.InklingRelDecode.Proof
