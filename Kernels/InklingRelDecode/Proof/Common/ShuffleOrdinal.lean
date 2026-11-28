-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.DataRef
public import Kernels.InklingRelDecode.Proof.Softmax.ShuffleCount
public import Kernels.InklingRelDecode.Proof.Prologue.BarrierCount
public import Kernels.InklingRelDecode.Proof.Lib.ShuffleEvent
public import Kernels.InklingRelDecode.Proof.Lib.BcastWord
public import Kernels.InklingRelDecode.Proof.Softmax.HeldNext
public import Kernels.InklingRelDecode.Proof.Epilogue.HeldNext
import Kernels.InklingRelDecode.Proof.Common.ShuffleShape
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame

private def phase : Startup.Site → Nat
  | .enter _ => 1
  | _ => 0

private def shflInv {Q L g} (X : Execution) (p : Nat) : (thread Q L g).D → Prop
  | (.inl s,n) => n .shfl=phase s.site
  | (.inr ⟨.inl (.prologue _),.inl d⟩,n) => n .shfl=1+Prologue.shflPosition p d.site
  | (.inr ⟨.inl (.prologue _),.inr ⟨_,.inl d⟩⟩,n) =>
    n .shfl=1+p+Softmax.shflCount d ∧ (Softmax.needsPrevious d.site=true → 0 < d.i) ∧
      (Softmax.held d.site=true → Lib.ShflAt X g 1261 (1+p+Lib.shflBase d.i) d.held.base)
  | (.inr ⟨.inl (.prologue _),.inr ⟨ent,.inr ⟨_,e⟩⟩⟩,n) =>
    1+p+Lib.shflBase ent.limit ≤ n .shfl ∧
      ((e.site=.wait ∨ e.site=.shfl) → n .shfl=1+p+Lib.shflBase ent.limit) ∧
      (e.site=.load → Lib.ShflAt X g 2603 (1+p+Lib.shflBase ent.limit) e.received) ∧
      (Epilogue.pastShfl e.site=true → (epiEntry ent (g%L.block)).skip=false →
        2+p+Lib.shflBase ent.limit ≤ n .shfl)
  | _ => True

private theorem start_at {Q L g n p X} (s : Startup.D) (h : n .shfl=phase s.site) :
    shflInv (Q := Q) (L := L) (g := g) X p
      (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) := by
  obtain ⟨s,t,v,w⟩ := s
  cases s <;> try exact h
  rename_i r
  cases r with
  | dp => exact (h.trans rfl).trans (by simp [Prologue.shflPosition]; rfl)
  | worker => trivial

private theorem pro_at {Q L g w n p X} (s : Prologue.Control.D)
    (z : n .shfl=1+Prologue.shflPosition p s.site) :
    shflInv (Q := Q) (L := L) (g := g) X p (.inr ⟨.inl (.prologue w),
      Code.enter (Prologue.Control.checkedCode Q L g w) (fun e => softCode e L g)
        (dataExit Q L g w) s⟩,n) := by
  obtain ⟨s,a,b,c,d,e⟩ := s
  cases s <;> try exact z
  refine ⟨?_,fun h => ?_,fun h => ?_⟩
  · change n .shfl=1+p+0
    exact z
  · cases h
  · cases h

private theorem soft_at {Q L g w ent n p X} (s : Softmax.Control.D)
    (z : n .shfl=1+p+Softmax.shflCount s ∧ (Softmax.needsPrevious s.site=true → 0 < s.i) ∧
      (Softmax.held s.site=true → Lib.ShflAt X g 1261 (1+p+Lib.shflBase s.i) s.held.base))
    (end_ : s.site=.epilogue → s.i=ent.limit) :
    shflInv (Q := Q) (L := L) (g := g) X p (.inr ⟨.inl (.prologue w),.inr ⟨ent,
      Code.enter (Softmax.Control.code ent L g) (fun _ : Unit =>
        Epilogue.Control.code (epiEntry ent (g%L.block)) L g) epiExit s⟩⟩,n) := by
  obtain ⟨s,i,v⟩ := s
  cases s
  case epilogue =>
    obtain ⟨count,_⟩ := z
    have last := end_ rfl
    change i=ent.limit at last
    have total : n .shfl=1+p+Lib.shflBase ent.limit := by
      rw [count,←last]
      simp [Softmax.shflCount,Softmax.shflInRound]
    refine ⟨total.ge,fun _ => total,fun h => ?_,fun h => ?_⟩ <;> cases h
  all_goals exact z

private theorem bump_shfl {m X g k n ev} {L : Launch}
    (hX : Consistent L kernel Assumptions.all m X) (get : X.get (g,k)=some ev)
    (nu : ∀ f, ev.kind≠.ub f) :
    Code.bump cls n ev .shfl=n .shfl+(decide (ev.pc ∈ Lib.shflPcs)).toNat := by
  have kind := Lib.shfl_event hX get nu
  change _+(if Execution.isShfl ev then 1 else 0)=_
  rw [kind]
  cases decide (ev.pc ∈ Lib.shflPcs) <;> rfl

private theorem startup_phase {L g d dn ev} (hn : Startup.succ L g d ev=some (some dn)) :
    phase dn.site=phase d.site+(decide (d.site.pc ∈ Lib.shflPcs)).toNat := by
  obtain ⟨s,t,x,w⟩ := d
  cases s <;> simp only [Startup.succ] at hn
  all_goals repeat' split at hn
  all_goals try contradiction
  all_goals cases hn
  all_goals rfl

private theorem pro_shuffle (s : Prologue.Site) :
    decide (s.pc ∈ Lib.shflPcs)=s.isShuffle := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem soft_shuffle (s : Softmax.Site) :
    decide (s.pc ∈ Lib.shflPcs)=s.isShuffle := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem epi_shuffle (s : Epilogue.Site) :
    decide (s.pc ∈ Lib.shflPcs)=decide (s=.shfl) := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem shfl_at {Q L m X g k s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some s)) (nu : NoUbBefore X g k) :
    shflInv X (Iface.preloadCount Q L (g/L.block)) s := by
  let p := Iface.preloadCount Q L (g/L.block)
  apply reference_induction (P := shflInv X p)
    (start_at _ (by
      change 0=phase (Startup.init L g).site
      unfold Startup.init
      split <;> rfl))
    _ hk hs (prefix_ub_zero hs nu)
  rintro j ⟨old,n⟩ ev ⟨sn,nn⟩ get prev clean ih move
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX get prev clean
  obtain ⟨step,rfl⟩ := Code.counted_next_some move
  rcases old with s|⟨r,d⟩
  · obtain ⟨_,go,rfl⟩ := Code.glue_inl_some step
    apply start_at
    change ev.pc=s.site.pc at pc
    rw [bump_shfl hX get clean,pc,startup_phase go]
    exact congrArg (· + _) ih
  obtain ⟨next,sub,rfl⟩ := Code.glue_inr_some step
  rcases r with r|r
  · cases r with
    | dispatch => trivial
    | prologue w =>
      rcases d with s|⟨ent,s|⟨_,s⟩⟩
      · obtain ⟨dn,go,rfl⟩ := Code.glue_inl_some sub
        have hg := Frame.lt_of_get hX get
        have hist := (data_ref_get hp hX get prev).1
        change ev.pc=s.site.pc at pc
        apply pro_at
        rw [bump_shfl hX get clean,pc,pro_shuffle,
          Prologue.preload_shfl_next go _ hist.block]
        · have z : n .shfl=1+Prologue.shflPosition p s.site := ih
          omega
        · intro large
          exact Prologue.preload_count hp hg (hist.known.first (by omega))
            (hist.known.last (by omega)) (hist.known.seq (by omega))
      · obtain ⟨_,go,rfl⟩ := Code.glue_inr_some sub
        obtain ⟨dn,localStep,rfl⟩ := Code.glue_inl_some go
        obtain ⟨z,before,held⟩ := ih
        change ev.pc=s.site.pc at pc
        refine soft_at _ ⟨?_,Softmax.previous_next before localStep,fun hd => ?_⟩
          (Softmax.epilogue_limit localStep)
        · rw [bump_shfl hX get clean,pc,soft_shuffle,Softmax.shfl_next before localStep]
          omega
        · rcases Softmax.held_next localStep hd with ⟨site,same,m,a,b,c,ok,kind⟩|⟨h,same,base⟩
          · obtain ⟨rfl,rfl,rfl⟩ := bcast_shape hp hX get prev
              (Or.inl (by change s.site.pc=1261; rw [site]; rfl)) kind
            have at1261 : ev=⟨1261,.shfl .idx a 0 31 dn.held.base ok⟩ := by
              obtain ⟨q,kd⟩ := ev
              change q=s.site.pc at pc
              rw [site] at pc
              change q=1261 at pc
              cases pc
              change kd=_ at kind
              cases kind
              rfl
            refine ⟨j,a,ok,at1261 ▸ get,?_⟩
            have count : n .shfl=((X.tr g).take j).countP Execution.isShfl := fcount prev _
            rw [←count,z,same]
            simp [Softmax.shflCount,site,Softmax.shflInRound]
          · rw [same,base]
            exact held h
      · obtain ⟨_,go,rfl⟩ := Code.glue_inr_some sub
        obtain ⟨dn,localStep,rfl⟩ := Code.glue_inr_some go
        obtain ⟨ge,wait,load,past⟩ := ih
        obtain ⟨toLoad,toWait,toPast⟩ := Epilogue.held_next localStep
        have bump := bump_shfl (n := n) hX get clean
        change ev.pc=s.site.pc at pc
        rw [pc,epi_shuffle] at bump
        have count : n .shfl=((X.tr g).take j).countP Execution.isShfl := fcount prev _
        refine ⟨?_,fun h => ?_,fun h => ?_,fun h skip => ?_⟩
        · omega
        · have site := toWait h
          rw [site] at bump
          have := wait (.inl site)
          simp at bump
          omega
        · obtain ⟨site,m,a,b,c,ok,kind⟩ := toLoad h
          obtain ⟨rfl,rfl,rfl⟩ := bcast_shape hp hX get prev
            (Or.inr (by change s.site.pc=2603; rw [site]; rfl)) kind
          have at2603 : ev=⟨2603,.shfl .idx a 0 31 dn.received ok⟩ := by
            obtain ⟨q,kd⟩ := ev
            change q=s.site.pc at pc
            rw [site] at pc
            change q=2603 at pc
            cases pc
            change kd=_ at kind
            cases kind
            rfl
          exact ⟨j,a,ok,at2603 ▸ get,(count.symm.trans (wait (.inr site)))⟩
        · rcases toPast h with old|site|⟨site,sk⟩
          · have := past old skip
            change 2+p+Lib.shflBase ent.limit≤_
            omega
          · have := wait (.inr site)
            rw [site] at bump
            simp at bump
            change 2+p+Lib.shflBase ent.limit≤_
            omega
          · rw [sk] at skip
            cases skip
  · cases sub

/-- The shuffles a Softmax thread has made before a state: one for the startup, one per
preloaded block, and the loop rounds. -/
theorem shfl_ordinal {Q L m X g k w ent d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (softState w ent d n))) (nu : NoUbBefore X g k) :
    n .shfl=1+Iface.preloadCount Q L (g/L.block)+Softmax.shflCount d :=
  (shfl_at hp hX hk hs nu).1

/-- A Softmax site that follows an earlier round has a positive round index. -/
theorem shfl_previous {Q L m X g k w ent d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (softState w ent d n))) (nu : NoUbBefore X g k) :
    Softmax.needsPrevious d.site=true → 0<d.i := by
  obtain ⟨_,before,_⟩ := shfl_at hp hX hk hs nu
  exact before

/-- A Softmax thread at a site that holds the round's broadcast word received it at the
round's first shuffle. -/
theorem shfl_held {Q L m X g k w ent d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (softState w ent d n))) (nu : NoUbBefore X g k) :
    Softmax.held d.site=true → Lib.ShflAt X g 1261
      (1+Iface.preloadCount Q L (g/L.block)+Lib.shflBase d.i) d.held.base := by
  obtain ⟨_,_,held⟩ := shfl_at hp hX hk hs nu
  exact held

/-- An epilogue thread has made every shuffle of the Softmax rounds. -/
theorem shfl_epilogue {Q L m X g k w ent d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (epiState w ent d n))) (nu : NoUbBefore X g k) :
    1+Iface.preloadCount Q L (g/L.block)+Lib.shflBase ent.limit≤n .shfl := by
  obtain ⟨bound,_⟩ := shfl_at hp hX hk hs nu
  exact bound

/-- An epilogue thread at the wait or the shuffle has made exactly the shuffles of the Softmax
rounds; one at the load holds the word its shuffle received; one past the shuffle that does not
skip it has made it. -/
theorem shfl_epi {Q L m X g k w ent d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (epiState w ent d n))) (nu : NoUbBefore X g k) :
    ((d.site=.wait ∨ d.site=.shfl) →
      n .shfl=1+Iface.preloadCount Q L (g/L.block)+Lib.shflBase ent.limit) ∧
    (d.site=.load → Lib.ShflAt X g 2603
      (1+Iface.preloadCount Q L (g/L.block)+Lib.shflBase ent.limit) d.received) ∧
    (Epilogue.pastShfl d.site=true → (epiEntry ent (g%L.block)).skip=false →
      2+Iface.preloadCount Q L (g/L.block)+Lib.shflBase ent.limit ≤ n .shfl) := by
  obtain ⟨_,exact,load,past⟩ := shfl_at hp hX hk hs nu
  exact ⟨exact,load,past⟩

/-- A thread in the startup has made at most one shuffle. -/
theorem shfl_startup {Q L m X g k s n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (.inl s,n))) (nu : NoUbBefore X g k) :
    n .shfl≤1 := by
  have h : n .shfl=phase s.site := shfl_at hp hX hk hs nu
  rw [h]
  obtain ⟨s,t,v,w⟩ := s
  cases s <;> simp [phase]

/-- A thread in the startup has made its shuffle exactly when it is past its site. -/
theorem shfl_startup_exact {Q L m X g k s n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (.inl s,n))) (nu : NoUbBefore X g k) :
    n .shfl=match s.site with | .enter _ => 1 | _ => 0 := by
  have h : n .shfl=phase s.site := shfl_at hp hX hk hs nu
  rw [h]
  cases s.site <;> rfl

/-- A preload thread has made one shuffle for the startup and one per preloaded block it left. -/
theorem shfl_prologue {Q L m X g k w d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (proState w d n))) (nu : NoUbBefore X g k) :
    n .shfl=1+Prologue.shflPosition (Iface.preloadCount Q L (g/L.block)) d.site :=
  shfl_at hp hX hk hs nu


end PTX.Kernels.InklingRelDecode.Proof
