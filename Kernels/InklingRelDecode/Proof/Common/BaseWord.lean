-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.StartupEvents
public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
import Lemmas.Flow.GlueStep
import Lemmas.Flow.AllocTmpl

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Proof PTX.Flow PTX.Frame

private theorem startup_word {L X g k d dn ev} (base : Iface.BaseRead L X)
    (he : X.get (g,k)=some ev) (shape : Startup.Ev L g d ev)
    (move : Startup.succ L g d ev=some (some dn)) (old : d.w=b32 0) : dn.w=b32 0 := by
  obtain ⟨s,t,x,w⟩ := d
  cases s
  case ld0 =>
    obtain ⟨a,bs,rfl,loc,size,_⟩ := shape
    have bytes := base he loc size
    simp only [Startup.succ,bytes,rebuild_b32] at move
    cases move
    rfl
  all_goals simp only [Startup.succ] at move
  all_goals repeat' split at move
  all_goals cases move
  all_goals exact old

def recordedZero {Q L g} : (thread Q L g).D → Prop
  | (.inl d,_) => d.w=b32 0
  | (.inr ⟨.inl (.dispatch w _),_⟩,_) => w=b32 0
  | (.inr ⟨.inl (.prologue w),.inl _⟩,_) => w=b32 0
  | (.inr ⟨.inl (.prologue _),.inr ⟨ent,_⟩⟩,_) => ent.base=b32 0
  | _ => True

private theorem word_enter {Q L g} (n : Cls → Nat) (s : Startup.D) (h : s.w=b32 0) :
    recordedZero (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) := by
  obtain ⟨s,t,x,w⟩ := s
  cases s <;> try exact h
  rename_i r
  cases r <;> exact h

theorem recorded_zero {Q L m X g k s}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (base : Iface.BaseRead L X) (hk : k≤(X.tr g).length) (clean : NoUbBefore X g k)
    (hs : stateAt (thread Q L) X g k=some (some s)) : recordedZero s := by
  induction k generalizing s with
  | zero =>
    rw [stateAt_zero] at hs
    cases hs
    apply word_enter
    change (Startup.init L g).w=b32 0
    unfold Startup.init
    split <;> rfl
  | succ j ih =>
    have he := List.getElem?_eq_getElem (l := X.tr g) (i := j) (by omega)
    rw [stateAt_succ he] at hs
    rcases prev : stateAt (thread Q L) X g j with _|_|old <;> rw [prev] at hs <;>
      try solve | cases hs
    have prior := ih (by omega) (noUbBefore_of_get hX he) prev
    obtain ⟨old,n⟩ := old
    obtain ⟨sn,nn⟩ := s
    obtain ⟨move,_⟩ := Code.counted_next_some hs
    rcases old with d|⟨r,d⟩
    · obtain ⟨dn,go,rfl⟩ := Code.glue_inl_some move
      exact word_enter _ _ (startup_word base he (start_ev hp hX he prev (clean j (by omega) _ he))
        go prior)
    · obtain ⟨dn,go,rfl⟩ := Code.glue_inr_some move
      rcases r with (r|r)
      · cases r with
        | dispatch => exact prior
        | prologue w =>
          rcases d with d|⟨e,d⟩
          · obtain ⟨s,_,rfl⟩ := Code.glue_inl_some go
            obtain ⟨site,a,b,c,v⟩ := s
            cases site <;> exact prior
          · obtain ⟨_,_,rfl⟩ := Code.glue_inr_some go
            exact prior
      · trivial

end PTX.Kernels.InklingRelDecode.Proof
