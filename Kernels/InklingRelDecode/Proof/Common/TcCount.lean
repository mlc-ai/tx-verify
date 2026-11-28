-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
public import Kernels.InklingRelDecode.Proof.Common.LaunchRounds
public import Kernels.InklingRelDecode.Proof.Common.ReferenceInduction
public import Kernels.InklingRelDecode.Proof.Softmax.TcCount
public import Kernels.InklingRelDecode.Proof.Epilogue.TcCount
public import Kernels.InklingRelDecode.Proof.Softmax.ShuffleCount
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Common.DataStart
import Lemmas.Flow.GlueStep

@[expose] public section

/-! # The counts of the `tcgen05` data positions of a data thread

At every reached state of a thread, the number of events at each position of `Lib.dataPcs` is a
function of the state: in the Softmax loop of the site, the round and the visits of the optional
rendezvous (`Softmax.softCount`), in the epilogue of the launch's loop count and the site
(`Epilogue.epiCount`), and zero elsewhere. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame

/-- The positions the count invariant follows: the optional rendezvous and the data positions. -/
def watchPcs : List Nat := 2326 :: Lib.dataPcs

/-- Outside the Softmax loop and the epilogue no watched position was visited. -/
def Zero (n : Cls → Nat) : Prop := ∀ P ∈ watchPcs, n (.atPc P)=0

/-- The count invariant of a thread state. -/
def TcInv {Q L g} : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.prologue _),.inr ⟨_,.inl d⟩⟩,n) =>
    (∀ P ∈ Lib.dataPcs, n (.atPc P)=Softmax.softCount d.site d.i (n (.atPc 2326)) P) ∧
      (Softmax.visited d.site=true → 1≤n (.atPc 2326))
  | (.inr ⟨.inl (.prologue _),.inr ⟨ent,.inr ⟨_,e⟩⟩⟩,n) =>
    (∀ P ∈ Lib.dataPcs, n (.atPc P)=Softmax.softCount .epilogue ent.limit (n (.atPc 2326)) P+
      Epilogue.epiCount (epiEntry ent (g%L.block)).skip e.site P) ∧
      Epilogue.Live (epiEntry ent (g%L.block)) e.site
  | (_,n) => Zero n

private theorem enter_zero {Q L g n} (s : Startup.D) (z : Zero n) :
    TcInv (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) := by
  obtain ⟨s,t,v,w⟩ := s
  cases s <;> try exact z
  rename_i r
  cases r <;> exact z

private theorem pro_enter {Q L g w n} (s : Prologue.Control.D)
    (z : Zero n) :
    TcInv (Q := Q) (L := L) (g := g) (.inr ⟨.inl (.prologue w),
      Code.enter (Prologue.Control.checkedCode Q L g w) (fun e => softCode e L g)
        (dataExit Q L g w) s⟩,n) := by
  obtain ⟨s,a,b,c,d,e⟩ := s
  cases s <;> try exact z
  have clear : n (.atPc 2326)=0 := z 2326 (by simp [watchPcs])
  refine ⟨fun P hP => ?_,fun h => ?_⟩
  · rw [z P (List.mem_cons_of_mem _ hP),clear]
    simp only [Softmax.softCount]
    split_ifs <;> simp [Softmax.afterLdS,Softmax.afterWaitLd,Softmax.afterTmemSt,
      Softmax.afterTmemWait]
  · cases h

private theorem soft_enter {Q L g w ent n} (s : Softmax.Control.D)
    (z : (∀ P ∈ Lib.dataPcs, n (.atPc P)=Softmax.softCount s.site s.i (n (.atPc 2326)) P) ∧
      (Softmax.visited s.site=true → 1≤n (.atPc 2326)))
    (lim : s.site=.epilogue → s.i=ent.limit) :
    TcInv (Q := Q) (L := L) (g := g) (.inr ⟨.inl (.prologue w),.inr ⟨ent,
      Code.enter (Softmax.Control.code ent L g) (fun _ : Unit =>
        Epilogue.Control.code (epiEntry ent (g%L.block)) L g) epiExit s⟩⟩,n) := by
  obtain ⟨s,i,v⟩ := s
  cases s <;> try exact z
  obtain ⟨cnt,-⟩ := z
  have hi : i=ent.limit := lim rfl
  subst hi
  refine ⟨fun P hP => ?_,?_⟩
  · rw [cnt P hP]
    simp [Epilogue.epiCount]
    split_ifs <;> simp [Epilogue.afterLoad,Epilogue.afterWaitLd]
  · rintro (h|h|h) <;> (change Epilogue.Site.wait=_ at h; cases h)

private theorem bump_pc (n : Cls → Nat) (ev : Event) (P : Nat) :
    Code.bump cls n ev (.atPc P)=n (.atPc P)+(decide (ev.pc=P)).toNat := by
  change n _+(if cls (.atPc P) ev then 1 else 0)=_
  simp only [cls,beq_iff_eq]
  split_ifs <;> simp_all

private theorem bump_other (n : Cls → Nat) (ev : Event) (P : Nat) (h : ev.pc≠P) :
    Code.bump cls n ev (.atPc P)=n (.atPc P) := by
  rw [bump_pc,decide_eq_false h]; rfl

theorem startup_data_pc (s : Startup.Site) {P : Nat} (h : P ∈ watchPcs) : s.pc≠P := by
  simp only [watchPcs,Lib.dataPcs,List.mem_cons,List.not_mem_nil,or_false] at h
  cases s <;> first | (rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide) |
    (rename_i r; cases r <;> rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)

theorem prologue_data_pc (s : Prologue.Site) {P : Nat} (h : P ∈ watchPcs) : s.pc≠P := by
  have := s.pc_range
  simp only [watchPcs,Lib.dataPcs,List.mem_cons,List.not_mem_nil,or_false] at h
  omega

theorem worker_data_pc {Q L g w x s n P}
    (hi : (thread Q L g).inv (.inr ⟨.inl (.dispatch w x),s⟩,n)) (h : P ∈ watchPcs) :
    (thread Q L g).pc (.inr ⟨.inl (.dispatch w x),s⟩,n)≠P := by
  intro eq
  have pl := state_role (Q := Q) (L := L) (g := g) (.inr ⟨.inl (.dispatch w x),s⟩,n)
  rw [eq] at pl
  simp only [watchPcs,Lib.dataPcs,List.mem_cons,List.not_mem_nil,or_false] at h
  by_cases c : 574<P ∧ P<2331
  · obtain ⟨_,_,_,_,h⟩ := pl.softmax c.1 c.2
    cases h
  · obtain ⟨_,_,_,_,h⟩ := pl.epilogue (by omega) (by omega) hi
    cases h

theorem tc_inv {Q L m X g k s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g<L.threads)
    (hk : k≤(X.tr g).length) (hs : stateAt (thread Q L) X g k=some (some s))
    (nu : NoUbBefore X g k) : TcInv s := by
  apply reference_induction (P := TcInv) (enter_zero _ (fun _ _ => rfl)) _ hk hs
    (prefix_ub_zero hs nu)
  rintro j ⟨old,n⟩ ev ⟨sn,nn⟩ get prev clean ih move
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX get prev clean
  have hi := (reached_table hf hg (Frame.noUbBefore_of_get hX get) prev).1
  obtain ⟨step,rfl⟩ := Code.counted_next_some move
  rcases old with s|⟨r,d⟩
  · obtain ⟨_,go,rfl⟩ := Code.glue_inl_some step
    change ev.pc=s.site.pc at pc
    change Zero n at ih
    exact enter_zero _ (fun P hP => by
      rw [bump_other _ _ _ (pc ▸ startup_data_pc s.site hP)]; exact ih P hP)
  obtain ⟨next,sub,rfl⟩ := Code.glue_inr_some step
  rcases r with r|r
  · cases r with
    | dispatch w x =>
      change Zero n at ih
      intro P hP
      rw [bump_other _ _ _ (pc ▸ worker_data_pc hi hP)]
      exact ih P hP
    | prologue w =>
      rcases d with s|⟨ent,s|⟨_,s⟩⟩
      · obtain ⟨dn,go,rfl⟩ := Code.glue_inl_some sub
        change ev.pc=s.site.pc at pc
        change Zero n at ih
        exact pro_enter _ (fun P hP => by
          rw [bump_other _ _ _ (pc ▸ prologue_data_pc s.site hP)]; exact ih P hP)
      · obtain ⟨_,go,rfl⟩ := Code.glue_inr_some sub
        obtain ⟨dn,localStep,rfl⟩ := Code.glue_inl_some go
        change ev.pc=s.site.pc at pc
        obtain ⟨cnt,vis⟩ := ih
        refine soft_enter _ ⟨fun P hP => ?_,fun h => ?_⟩
          (fun h => Softmax.epilogue_limit localStep h)
        · have step := (Softmax.count_next (n (.atPc 2326)) P hP vis localStep).1
          simp only [beq_eq_decide] at step
          rw [bump_pc,bump_pc,pc,cnt P hP]
          exact step.symm
        · have step := (Softmax.count_next (n (.atPc 2326)) 1265 (by simp [Lib.dataPcs]) vis
            localStep).2 h
          rw [bump_pc,pc]
          simpa only [beq_eq_decide] using step
      · obtain ⟨_,go,rfl⟩ := Code.glue_inr_some sub
        obtain ⟨_,localStep,rfl⟩ := Code.glue_inr_some go
        change ev.pc=s.site.pc at pc
        obtain ⟨cnt,live⟩ := ih
        have range := s.site.pc_range
        refine ⟨fun P hP => ?_,(Epilogue.count_next 2607 (.inl rfl) live localStep).2⟩
        have same : Code.bump cls n ev (.atPc 2326)=n (.atPc 2326) :=
          bump_other _ _ _ (by omega)
        change Code.bump cls n ev (.atPc P)=Softmax.softCount .epilogue _
          (Code.bump cls n ev (.atPc 2326)) P+_
        rw [same]
        by_cases e : P=2607 ∨ P=2608
        · have step := (Epilogue.count_next P e live localStep).1
          simp only [beq_eq_decide] at step
          rw [bump_pc,pc,cnt P hP]
          omega
        · have off : s.site.pc≠P := by
            simp only [Lib.dataPcs,List.mem_cons,List.not_mem_nil,or_false] at hP
            omega
          rw [bump_other _ _ _ (pc ▸ off),cnt P hP]
          simp only [Epilogue.epiCount]
          split_ifs <;> first | rfl | (exfalso; omega)
  · cases sub

end PTX.Kernels.InklingRelDecode.Proof
