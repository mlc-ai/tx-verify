-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.DataRef
public import Kernels.InklingRelDecode.Proof.Common.ShuffleOrdinal
public import Kernels.InklingRelDecode.Proof.Lib.CollectiveAt
import Lemmas.Flow.NotBulk
import Lemmas.Flow.GlueStep

@[expose] public section

/-! # The elections a data lane has made

A data lane makes twelve elections for the barrier initializations and four for each preloaded
block, all in the prologue; the Softmax and the epilogue make none. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame

private def elInv {Q L g} (p : Nat) : (thread Q L g).D → Prop
  | (.inl _,n) => n .elect=0
  | (.inr ⟨.inl (.prologue _),.inl d⟩,n) => n .elect=Prologue.electPosition p d.site
  | (.inr ⟨.inl (.prologue _),.inr _⟩,n) => n .elect=12+4*p
  | _ => True

private theorem start_at {Q L g n p} (s : Startup.D) (h : n .elect=0) :
    elInv (Q := Q) (L := L) (g := g) p
      (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) := by
  obtain ⟨s,t,v,w⟩ := s
  cases s <;> try exact h
  rename_i r
  cases r with
  | dp => exact h
  | worker => trivial

private theorem pro_at {Q L g w n p} (s : Prologue.Control.D)
    (z : n .elect=Prologue.electPosition p s.site) :
    elInv (Q := Q) (L := L) (g := g) p (.inr ⟨.inl (.prologue w),
      Code.enter (Prologue.Control.checkedCode Q L g w) (fun e => softCode e L g)
        (dataExit Q L g w) s⟩,n) := by
  obtain ⟨s,a,b,c,d,e⟩ := s
  cases s <;> exact z

private theorem bump_elect (n : Cls → Nat) (e : Event) :
    Code.bump cls n e .elect = n .elect + (isElectEv e).toNat := by
  change _ + (if isElectEv e then 1 else 0) = _; cases isElectEv e <;> rfl

private theorem no_elect {L m X i e} (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get i = some e) (nu : ∀ f, e.kind ≠ .ub f) (off : Lib.canElect e.pc = false) :
    isElectEv e = false := by
  obtain ⟨f,bad⟩|⟨t,ins,o,_,code,fire⟩ := get_source hX get
  · exact (nu f bad).elim
  · exact (Lib.collective_at code fire).election off

private theorem startup_off (s : Startup.Site) : Lib.canElect s.pc=false := by
  cases s <;> first | decide +kernel | (rename_i r; cases r <;> decide +kernel)

private theorem soft_off (s : Softmax.Site) : Lib.canElect s.pc=false := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem epi_off (s : Epilogue.Site) : Lib.canElect s.pc=false := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem elect_at {Q L m X g k s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some s)) (nu : NoUbBefore X g k) :
    elInv (Q := Q) (L := L) (g := g) (Iface.preloadCount Q L (g/L.block)) s := by
  let p := Iface.preloadCount Q L (g/L.block)
  apply reference_induction (P := elInv p)
    (start_at _ (by rfl)) _ hk hs (prefix_ub_zero hs nu)
  rintro j ⟨old,n⟩ ev ⟨sn,nn⟩ get prev clean ih move
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX get prev clean
  obtain ⟨step,rfl⟩ := Code.counted_next_some move
  rcases old with s|⟨r,d⟩
  · obtain ⟨_,go,rfl⟩ := Code.glue_inl_some step
    apply start_at
    change ev.pc=s.site.pc at pc
    rw [bump_elect, no_elect hX get clean (pc ▸ startup_off s.site)]
    exact ih
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
        have cap : 180≤s.site.pc → min 3 (Prologue.Control.preload Q.splits
            ((L.ctaidOf (g/L.block)).get .x) s)=p := fun large =>
          Prologue.preload_count hp hg (hist.known.first (by omega))
            (hist.known.last (by omega)) (hist.known.seq (by omega))
        have cnt : Prologue.electPosition p dn.site = Prologue.electPosition p s.site +
            s.site.isElect.toNat := Prologue.elect_next go cap hist.block
        have kind : isElectEv ev = s.site.isElect := by
          by_cases e : s.site.isElect = true
          · obtain ⟨_,_,_,k⟩ := Prologue.elect_kind go e
            rw [e]; simp [isElectEv, k]
          · rw [Bool.not_eq_true] at e
            rw [e]
            exact no_elect hX get clean (pc ▸ Prologue.canElect_off s.site e)
        rw [bump_elect, kind, cnt]
        have z : n .elect=Prologue.electPosition p s.site := ih
        omega
      · obtain ⟨_,go,rfl⟩ := Code.glue_inr_some sub
        obtain ⟨dn,localStep,rfl⟩ := Code.glue_inl_some go
        change ev.pc=s.site.pc at pc
        change Code.bump cls n ev .elect=12+4*p
        rw [bump_elect, no_elect hX get clean (pc ▸ soft_off s.site)]
        exact ih
      · obtain ⟨_,go,rfl⟩ := Code.glue_inr_some sub
        obtain ⟨dn,localStep,rfl⟩ := Code.glue_inr_some go
        change ev.pc=s.site.pc at pc
        change Code.bump cls n ev .elect=12+4*p
        rw [bump_elect, no_elect hX get clean (pc ▸ epi_off s.site)]
        exact ih
  · cases sub

/-- A data lane in the prologue has made the elections before its site. -/
theorem elect_prologue {Q L m X g k w d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (proState w d n))) (nu : NoUbBefore X g k) :
    n .elect=Prologue.electPosition (Iface.preloadCount Q L (g/L.block)) d.site :=
  elect_at hp hX hk hs nu

/-- A lane in the startup has made no election. -/
theorem elect_startup {Q L m X g k s n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (.inl s,n))) (nu : NoUbBefore X g k) :
    n .elect=0 :=
  elect_at hp hX hk hs nu

/-- A lane past the prologue has made all its elections, a lane in the startup none. -/
theorem elect_late {Q L m X g k w ent d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (softState w ent d n))) (nu : NoUbBefore X g k) :
    n .elect=12+4*Iface.preloadCount Q L (g/L.block) :=
  elect_at hp hX hk hs nu

/-- A lane in the epilogue has made all its elections. -/
theorem elect_epi {Q L m X g k w ent d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (epiState w ent d n))) (nu : NoUbBefore X g k) :
    n .elect=12+4*Iface.preloadCount Q L (g/L.block) :=
  elect_at hp hX hk hs nu

end PTX.Kernels.InklingRelDecode.Proof
