-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.EpiPrev
public import Kernels.InklingRelDecode.Proof.Common.ReferenceInduction
public import Kernels.InklingRelDecode.Proof.Softmax.BarrierCount
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame
noncomputable section

private def fixedTotal (n : Cls → Nat) :=
  n (.atPc 2241)+n (.atPc 2251)+n (.atPc 999)+n (.atPc 1012)

private theorem fixed_bump (n : Cls → Nat) (ev : Event) :
    fixedTotal (Code.bump cls n ev)=fixedTotal n+(Softmax.fixedSync ev.pc).toNat := by
  simp only [fixedTotal,Code.bump,cls,Softmax.fixedSync]
  by_cases a : ev.pc=2241 <;> by_cases b : ev.pc=2251 <;> by_cases c : ev.pc=999 <;>
    by_cases d : ev.pc=1012 <;> simp_all <;> omega

private def onPath {Q L g} : (thread Q L g).D → Prop
  | (.inl _,n) | (.inr ⟨.inl (.prologue _),.inl _⟩,n) => fixedTotal n=0
  | (.inr ⟨.inl (.prologue _),.inr ⟨_,.inl d⟩⟩,n) => fixedTotal n+2=Softmax.fixedCount d
  | _ => True

private theorem enter_start {Q L g} (s : Startup.D) (n : Cls → Nat) (z : fixedTotal n=0) :
    onPath (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) := by
  obtain ⟨s,t,v,w⟩ := s
  cases s <;> try exact z
  rename_i r
  cases r <;> trivial

private theorem enter_pro {Q L g w} (s : Prologue.Control.D) (n : Cls → Nat)
    (z : fixedTotal n=0) :
    onPath (Q := Q) (L := L) (g := g) (.inr ⟨.inl (.prologue w),
      Code.enter (Prologue.Control.checkedCode Q L g w) (fun e => softCode e L g)
        (dataExit Q L g w) s⟩,n) := by
  obtain ⟨s,a,b,c,d,e⟩ := s
  cases s <;> try exact z
  change fixedTotal n+2=2
  omega

private theorem enter_soft {Q L g w ent} (s : Softmax.Control.D) (n : Cls → Nat)
    (z : fixedTotal n+2=Softmax.fixedCount s) :
    onPath (Q := Q) (L := L) (g := g) (.inr ⟨.inl (.prologue w),.inr ⟨ent,
      Code.enter (Softmax.Control.code ent L g) (fun _ : Unit =>
        Epilogue.Control.code (epiEntry ent (g%L.block)) L g) epiExit s⟩⟩,n) := by
  obtain ⟨s,i,v⟩ := s
  cases s <;> trivial

private theorem early_clear {pc : Nat} (lt : pc≤574) : Softmax.fixedSync pc=false := by
  simp only [Softmax.fixedSync,Bool.or_eq_false_iff,beq_eq_false_iff_ne]
  omega

private theorem start_clear (s : Startup.Site) : Softmax.fixedSync s.pc=false := by
  cases s <;> first | decide | (rename_i r; cases r <;> decide)

private theorem bump_early {n ev} (old : fixedTotal n=0) (clear : Softmax.fixedSync ev.pc=false) :
    fixedTotal (Code.bump cls n ev)=0 := by
  rw [fixed_bump,old,clear]
  rfl

theorem soft_fixed_total {Q L m X g k w ent d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (softState w ent d n))) (nu : NoUbBefore X g k) :
    n (.atPc 2241)+n (.atPc 2251)+n (.atPc 999)+n (.atPc 1012)+2=Softmax.fixedCount d := by
  apply reference_induction (Q := Q) (L := L) (P := onPath) (enter_start _ _ rfl) _ hk hs
    (prefix_ub_zero hs nu)
  rintro j ⟨old,n⟩ ev ⟨sn,nn⟩ get prev clean ih move
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX get prev clean
  obtain ⟨step,rfl⟩ := Code.counted_next_some move
  rcases old with s|⟨r,d⟩
  · obtain ⟨_,_,rfl⟩ := Code.glue_inl_some step
    apply enter_start _ _ (bump_early ih _)
    change ev.pc=s.site.pc at pc
    exact pc ▸ start_clear _
  obtain ⟨next,sub,rfl⟩ := Code.glue_inr_some step
  rcases r with r|r
  · cases r with
    | dispatch => trivial
    | prologue w =>
      rcases d with s|⟨ent,s|⟨_,s⟩⟩
      · obtain ⟨_,_,rfl⟩ := Code.glue_inl_some sub
        exact enter_pro _ _ (bump_early ih (early_clear (pc ▸ s.site.pc_range.2)))
      · obtain ⟨_,go,rfl⟩ := Code.glue_inr_some sub
        obtain ⟨dn,localStep,rfl⟩ := Code.glue_inl_some go
        apply enter_soft
        change fixedTotal n+2=Softmax.fixedCount s at ih
        change ev.pc=s.site.pc at pc
        rw [fixed_bump,pc,Softmax.fixed_next localStep,←ih]
        omega
      · obtain ⟨_,go,rfl⟩ := Code.glue_inr_some sub
        obtain ⟨_,_,rfl⟩ := Code.glue_inr_some go
        trivial
  · cases sub

end
end PTX.Kernels.InklingRelDecode.Proof
