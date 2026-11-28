-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Kernels.InklingRelDecode.Proof.Lib.SymbolStore
import Kernels.InklingRelDecode.Proof.Prologue.ShapePublish
import Kernels.InklingRelDecode.Proof.Prologue.PublishTail
import Kernels.InklingRelDecode.Proof.Common.FollowSub
import Kernels.InklingRelDecode.Flow.Code.Part008
import Lemmas.Flow.Final
import Lemmas.Step.ExitLast

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow PTX.Proof Control

private theorem previous {Q L X g w d n k} (hk : k≤(X.tr g).length) (i : Fin 3)
    (live : Frame.stateAt (thread Q L) X g k=some (some (proState w d n)))
    (site : d.site=pubSite i.succ) :
    ∃ u old cnt, u+1=k ∧ Frame.stateAt (thread Q L) X g u=some (some (proState w old cnt)) ∧
      old.site=pubSite i.castSucc := by
  have later : d≠{} := by
    rintro rfl
    fin_cases i <;> contradiction
  obtain ⟨u,old,cnt,ev,eq,hs,_,step⟩ := pro_prev hk later live
  exact ⟨u,old,cnt,eq,hs,pub_predecessor i step site⟩

private theorem before_sync {Q L m X g k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k)=some ⟨573,.bar 1 none .sync⟩) (i : Fin 3) :
    ∃ u w d n, u<k ∧ Frame.stateAt (thread Q L) X g u=some (some (proState w d n)) ∧
      d.site=pubSite i.castSucc := by
  have hk : k<(X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (by simp) ⟨control_tracked hp hX g k (Frame.lt_of_get hX he),fun _ _ => trivial⟩
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
  obtain ⟨w,d,n,rfl⟩ := (pc ▸ state_role s).prologue (by decide : 27<573) (by decide : 573<574)
  have only (s : Site) : 573=s.pc → s=.bar18 := by
    cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
  obtain ⟨u₂,d₂,n₂,h₂,s₂,t₂⟩ := previous hk.le 2 hs (only _ pc)
  obtain ⟨u₁,d₁,n₁,h₁,s₁,t₁⟩ := previous (by omega) 1 s₂ t₂
  obtain ⟨u₀,d₀,n₀,h₀,s₀,t₀⟩ := previous (by omega) 0 s₁ t₁
  fin_cases i
  · exact ⟨_,_,_,_,by omega,s₀,t₀⟩
  · exact ⟨_,_,_,_,by omega,s₁,t₁⟩
  · exact ⟨_,_,_,_,by omega,s₂,t₂⟩

private theorem store_fired {Q L m X g k w d n u} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨573,.bar 1 none .sync⟩)
    (before : u<k) (hs : Frame.stateAt (thread Q L) X g u=some (some (proState w d n))) :
    ∃ ev t ins t', X.get (g,u)=some ev ∧ (code Q L g w).AtD d t ∧
      kernel.code[d.site.pc]?=some ins ∧ Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op)
        ev (some t') := by
  have hk : k<(X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have get := List.getElem?_eq_getElem (l := X.tr g) (i := u) (by omega)
  have clear := Frame.noUbBefore_of_get hX he u before _ get
  obtain ⟨t,ins,o,ht,_,hc,fire⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX get hs clear
  cases o with
  | some t' => exact ⟨_,t,ins,t',get,ht,hc,fire⟩
  | none =>
    rcases fires_none_ends fire with ⟨f,bad⟩|exit
    · exact (clear f bad).elim
    · have eq : (X.tr g)[u] = ⟨((X.tr g)[u]).pc,.exit⟩ := by
        generalize (X.tr g)[u] = e at exit ⊢
        cases e with | mk pc kd => cases exit; rfl
      have length := Execution.exit_last hX (Frame.lt_of_get hX he) (get.trans (congrArg some eq))
      omega

/-- Both substeps have fired before any Prologue lane releases its worker inputs. -/
public theorem published_pair {Q L m X g k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨573,.bar 1 none .sync⟩)
    (j : Fin 2) : ∃ u, u<k ∧ X.get (g,u)=some ⟨571,.wr
      (Lib.wordAcc ⟨.shared,g/L.block,L.sharedBase+212992+4*j.val⟩ j.val)
      (b32 (if j=0 then Iface.preloadCount Q L (g/L.block)
        else Q.numIters ((L.ctaidOf (g/L.block)).get .z)
          ((L.ctaidOf (g/L.block)).get .x))).toBytes⟩ := by
  obtain ⟨u,w,d,n,uk,hs,site⟩ := before_sync hp hX he j.succ
  have st : d.site=.st9 j := by fin_cases j <;> exact site
  obtain ⟨ev,t,ins,t',get,ht,hc,fire⟩ := store_fired hp hX he uk hs
  have pc : d.site.pc=571 := st ▸ rfl
  rw [pc] at hc fire
  have know := pro_known hp hX (List.getElem?_eq_some_iff.mp get).1.le hs
  have eq := pair_store hp (Frame.lt_of_get hX he) j st ht know hc fire
  rw [eq] at get
  refine ⟨u,uk,?_⟩
  fin_cases j <;> exact get

/-- The scalar publication immediately before the pair is present in the
same issuing lane. Its payload is the immediate at PC 570. -/
public theorem published_role {Q L m X g k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨573,.bar 1 none .sync⟩) :
    ∃ u a bs, u<k ∧ X.get (g,u)=some ⟨570,.wr a bs⟩ := by
  obtain ⟨u,w,d,n,uk,hs,site⟩ := before_sync hp hX he 0
  have st : d.site=.st8 := site
  obtain ⟨ev,t,ins,t',get,ht,hc,fire⟩ := store_fired hp hX he uk hs
  have pc : d.site.pc=570 := st ▸ rfl
  rw [pc] at hc fire
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_570)
  have sub : t.sub=0 := by
    have h := ht.2.1
    change t.sub=d.site.sub at h
    rw [st] at h
    exact h
  change Fires 570 (eventTmpl Assumptions.all L g t
    (.mem (Lib.symStore 1 213336 [.imm 16777730]))) ev (some t') at fire
  generalize Assumptions.all = A at fire
  have row := Lib.fires_st_sym (A := A) (L := L) (g := g) (t := t) (pc := 570)
    (e := ev) (u := t') (op := .mem (Lib.symStore 1 213336 [.imm 16777730]))
    (vec := 1) (off := 213336) (srcs := [.imm 16777730]) (o := .imm 16777730) (j := 0)
    (v := b32 16777730) rfl (by decide) sub rfl rfl rfl (Or.inl rfl)
  generalize eventTmpl A L g t (.mem (Lib.symStore 1 213336 [.imm 16777730])) = tpl at row fire
  obtain ⟨v,_,eq⟩ := row (by assumption)
  exact ⟨u,_,_,uk,get.trans (congrArg some eq)⟩

private theorem event_pc {Q L m X g k w d n u} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨573,.bar 1 none .sync⟩)
    (before : u<k) (hs : Frame.stateAt (thread Q L) X g u=some (some (proState w d n))) :
    ∃ ev, X.get (g,u)=some ev ∧ ev.pc=d.site.pc := by
  obtain ⟨ev,t,ins,t',get,ht,hc,fire⟩ := store_fired hp hX he before hs
  exact ⟨ev,get,EventFrame.fires_source_pc fire⟩

/-- The fence before the first publication store of a lane that reaches the releasing barrier:
the four events before it are the fence and the three publication stores. -/
public theorem published_fence {Q L m X g k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨573,.bar 1 none .sync⟩) :
    ∃ u, u+4=k ∧ X.get (g,u)=some ⟨569,.fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      ∀ j, u<j → j<k → ∃ ev, X.get (g,j)=some ev ∧ (ev.pc=570 ∨ ev.pc=571) := by
  have hk : k<(X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (by simp) ⟨control_tracked hp hX g k (Frame.lt_of_get hX he),fun _ _ => trivial⟩
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
  obtain ⟨w,d,n,rfl⟩ := (pc ▸ state_role s).prologue (by decide : 27<573) (by decide : 573<574)
  have only (s : Site) : 573=s.pc → s=.bar18 := by
    cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
  obtain ⟨u₂,d₂,n₂,h₂,s₂,t₂⟩ := previous hk.le 2 hs (only _ pc)
  obtain ⟨u₁,d₁,n₁,h₁,s₁,t₁⟩ := previous (by omega) 1 s₂ t₂
  obtain ⟨u₀,d₀,n₀,h₀,s₀,t₀⟩ := previous (by omega) 0 s₁ t₁
  have later : d₀≠{} := by
    rintro rfl
    exact absurd t₀ (by decide)
  obtain ⟨uf,old,cnt,ev,eq,sf,getf,step⟩ := pro_prev (by omega) later s₀
  have fnc : old.site=.fnc1 := fence_predecessor step t₀
  obtain ⟨evf,t,ins,t',get,ht,hc,fire⟩ := store_fired hp hX he (by omega) sf
  have pcf : d₀.site.pc=570 := by rw [t₀]; rfl
  have eqf : old.site.pc=569 := by rw [fnc]; rfl
  rw [eqf] at hc fire
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_569)
  obtain ⟨shape,_⟩ := fires_fence_proxy fire
  have here : evf=⟨569,.fenceProxy (.async (some (.shared .cta))) none⟩ := shape
  refine ⟨uf,by omega,by rw [get,here],fun j lo hi => ?_⟩
  have pcs : ∀ {u d n}, u<k → Frame.stateAt (thread Q L) X g u=some (some (proState w d n)) →
      ∃ ev, X.get (g,u)=some ev ∧ ev.pc=d.site.pc := fun lt hs => event_pc hp hX he lt hs
  have c0 : j=u₀ ∨ j=u₁ ∨ j=u₂ := by omega
  rcases c0 with rfl|rfl|rfl
  · obtain ⟨ev,gev,pe⟩ := pcs (by omega) s₀
    exact ⟨ev,gev,.inl (by rw [pe,t₀]; rfl)⟩
  · obtain ⟨ev,gev,pe⟩ := pcs (by omega) s₁
    exact ⟨ev,gev,.inr (by rw [pe,t₁]; rfl)⟩
  · obtain ⟨ev,gev,pe⟩ := pcs (by omega) s₂
    exact ⟨ev,gev,.inr (by rw [pe,t₂]; rfl)⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
