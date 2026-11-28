-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.DataRef
public import Kernels.InklingRelDecode.Proof.Softmax.BarrierCount
public import Kernels.InklingRelDecode.Proof.Prologue.BarrierCount
public import Kernels.InklingRelDecode.Proof.Lib.BarZero
public import Kernels.InklingRelDecode.Proof.Epilogue.FinalSync
public import Kernels.InklingRelDecode.Proof.Softmax.ShuffleCount
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame

private def ordinalInv {Q L g} (p : Nat) : (thread Q L g).D → Prop
  | (.inl s,n) => LaunchCounts n (Startup.barriers s.site)
  | (.inr ⟨.inl (.prologue _),.inl d⟩,n) =>
    n (.bar 0)=Prologue.preloadPosition p d.site ∧ n (.atPc 2326)=0
  | (.inr ⟨.inl (.prologue _),.inr ⟨_,.inl d⟩⟩,n) =>
    n (.bar 0)+2=3+5*p+Softmax.fixedCount d+n (.atPc 2326)
  | (.inr ⟨.inl (.prologue _),.inr ⟨ent,.inr ⟨_,e⟩⟩⟩,n) =>
    n (.bar 0)+2=3+5*p+Softmax.fixedCount ⟨.epilogue,ent.limit,{}⟩+n (.atPc 2326)+
      Lib.afterFinal e.site.pc
  | _ => True

private theorem start_at {Q L g n p} (s : Startup.D)
    (h : LaunchCounts n (Startup.barriers s.site)) :
    ordinalInv p (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) := by
  obtain ⟨s,t,v,w⟩ := s
  cases s <;> try exact h
  rename_i r
  cases r with
  | dp => exact ⟨h.first,h.visit _ (by decide)⟩
  | worker => trivial

private theorem pro_at {Q L g w n p} (s : Prologue.Control.D)
    (z : n (.bar 0)=Prologue.preloadPosition p s.site) (clear : n (.atPc 2326)=0) :
    ordinalInv (Q := Q) (L := L) (g := g) p (.inr ⟨.inl (.prologue w),
      Code.enter (Prologue.Control.checkedCode Q L g w) (fun e => softCode e L g)
        (dataExit Q L g w) s⟩,n) := by
  obtain ⟨s,a,b,c,d,e⟩ := s
  cases s <;> try exact ⟨z,clear⟩
  change n (.bar 0)+2=3+5*p+2+n (.atPc 2326)
  change n (.bar 0)=3+5*p at z
  omega

private theorem soft_at {Q L g w ent n p} (s : Softmax.Control.D)
    (z : n (.bar 0)+2=3+5*p+Softmax.fixedCount s+n (.atPc 2326))
    (lim : s.site=.epilogue → s.i=ent.limit) :
    ordinalInv (Q := Q) (L := L) (g := g) p (.inr ⟨.inl (.prologue w),.inr ⟨ent,
      Code.enter (Softmax.Control.code ent L g) (fun _ : Unit =>
        Epilogue.Control.code (epiEntry ent (g%L.block)) L g) epiExit s⟩⟩,n) := by
  obtain ⟨s,i,v⟩ := s
  cases s <;> try trivial
  have hi : i=ent.limit := lim rfl
  subst hi
  exact z

private theorem pro_sites (s : Prologue.Site) : Lib.zeroSite s.pc=Prologue.preloadSync s := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem soft_sites (s : Softmax.Site) : (Lib.zeroSite s.pc).toNat=
    (Softmax.fixedSync s.pc).toNat+(s.pc==2326).toNat := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem epi_sites (s : Epilogue.Site) : (Lib.zeroSite s.pc).toNat =
    (Lib.finalSync s.pc).toNat := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem bar_bump {Q L m X g k n ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (get : X.get (g,k)=some ev)
    (nu : ∀ f, ev.kind≠.ub f) :
    Code.bump cls n ev (.bar 0)=n (.bar 0)+(Lib.zeroSite ev.pc).toNat := by
  have kind := Lib.zero_event hX hp.block get nu
  change n _+(if cls (.bar 0) ev then 1 else 0)=_
  rw [cls_bar0,kind]
  cases Lib.zeroSite ev.pc <;> rfl

private theorem ordinal_at {Q L m X g k s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some s)) (nu : NoUbBefore X g k) :
    ordinalInv (Iface.preloadCount Q L (g/L.block)) s := by
  let p := Iface.preloadCount Q L (g/L.block)
  apply reference_induction (P := ordinalInv p) (start_at _ launch_counts_init) _ hk hs
    (prefix_ub_zero hs nu)
  rintro j ⟨old,n⟩ ev ⟨sn,nn⟩ get prev clean ih move
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX get prev clean
  obtain ⟨step,rfl⟩ := Code.counted_next_some move
  rcases old with s|⟨r,d⟩
  · obtain ⟨_,go,rfl⟩ := Code.glue_inl_some step
    exact start_at _ (launch_counts_step ih (start_ev hp hX get prev clean) go)
  obtain ⟨next,sub,rfl⟩ := Code.glue_inr_some step
  rcases r with r|r
  · cases r with
    | dispatch => trivial
    | prologue w =>
      rcases d with s|⟨ent,s|⟨_,s⟩⟩
      · obtain ⟨dn,go,rfl⟩ := Code.glue_inl_some sub
        have hg := Frame.lt_of_get hX get
        have hist := (data_reference hp hX (List.getElem?_eq_some_iff.mp get).1.le prev
          (prefix_ub_zero prev (Frame.noUbBefore_of_get hX get))).1
        change ev.pc=s.site.pc at pc
        obtain ⟨z,clear⟩ := ih
        apply pro_at
        · rw [bar_bump hp hX get clean,pc,pro_sites,z,Prologue.preload_sync_next go _ hist.block]
          intro large
          exact Prologue.preload_count hp hg (hist.known.first (by omega))
            (hist.known.last (by omega)) (hist.known.seq (by omega))
        · have small := s.site.pc_range.2
          simp [Code.bump,cls,clear,show ev.pc≠2326 by omega]
      · obtain ⟨_,go,rfl⟩ := Code.glue_inr_some sub
        obtain ⟨dn,localStep,rfl⟩ := Code.glue_inl_some go
        refine soft_at _ ?_ (fun h => Softmax.epilogue_limit localStep h)
        change ev.pc=s.site.pc at pc
        change n (.bar 0)+2=3+5*p+Softmax.fixedCount s+n (.atPc 2326) at ih
        rw [bar_bump hp hX get clean,pc,soft_sites,Softmax.fixed_next localStep]
        change _=3+5*p+_+(n (.atPc 2326)+(if ev.pc==2326 then 1 else 0))
        rw [pc]
        cases s.site.pc==2326 <;> simp_all only [Bool.false_eq_true,ite_false,Bool.toNat_false,
          ite_true,Bool.toNat_true] <;> omega
      · obtain ⟨_,go,rfl⟩ := Code.glue_inr_some sub
        obtain ⟨_,localStep,rfl⟩ := Code.glue_inr_some go
        change ev.pc=s.site.pc at pc
        change n (.bar 0)+2=_ at ih
        change _=3+5*p+_+(n (.atPc 2326)+(if ev.pc==2326 then 1 else 0))+_
        rw [bar_bump hp hX get clean,pc,epi_sites,Epilogue.final_step localStep]
        have far : (s.site.pc==2326)=false := by
          have := s.site.pc_range.1
          simp only [beq_eq_false_iff_ne]
          omega
        simp only [far,Bool.false_eq_true,ite_false]
        omega
  · cases sub

/-- Actual physical barrier ordinal, including the CTA's launch-dependent
preload and exactly one extra barrier per observed O rescale. -/
theorem data_ordinal {Q L m X g k w ent d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (softState w ent d n))) (nu : NoUbBefore X g k) :
    n (.bar 0)+2=3+5*Iface.preloadCount Q L (g/L.block)+Softmax.fixedCount d+n (.atPc 2326) := by
  exact ordinal_at hp hX hk hs nu

/-- Barrier-zero ordinal of an epilogue state: the loop ran to its limit, and the final
rendezvous is counted once the site is past it. -/
theorem epilogue_ordinal {Q L m X g k w ent e n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (epiState w ent e n))) (nu : NoUbBefore X g k) :
    n (.bar 0)+2=3+5*Iface.preloadCount Q L (g/L.block)+
      Softmax.fixedCount ⟨.epilogue,ent.limit,{}⟩+n (.atPc 2326)+Lib.afterFinal e.site.pc :=
  ordinal_at hp hX hk hs nu

theorem preload_ordinal {Q L m X g k w d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (proState w d n))) (nu : NoUbBefore X g k) :
    n (.bar 0)=Prologue.preloadPosition (Iface.preloadCount Q L (g/L.block)) d.site :=
  (ordinal_at hp hX hk hs nu).1

/-- A preload thread has not met the optional rendezvous. -/
theorem preload_clear {Q L m X g k w d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (proState w d n))) (nu : NoUbBefore X g k) :
    n (.atPc 2326)=0 :=
  (ordinal_at hp hX hk hs nu).2

/-- A startup thread has counted only its own startup rendezvous. -/
theorem startup_counts {Q L m X g k s n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (.inl s,n))) (nu : NoUbBefore X g k) :
    LaunchCounts n (Startup.barriers s.site) :=
  ordinal_at hp hX hk hs nu

end PTX.Kernels.InklingRelDecode.Proof
