-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.RoleWord
import Kernels.InklingRelDecode.Proof.Common.EpiPrev
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Flow.Code.Part044
import Lemmas.Flow.Final
import Lemmas.Step.ExitLast

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
open PTX PTX.Flow PTX.Proof Control

private theorem prev_word {ent L g d ev dn} (step : Control.next ent L g d ev=some (some dn))
    (target : dn.site=.sync1) : d.site=.roleWord := by
  obtain ⟨s,v⟩ := d
  cases s <;> simp only [Control.next,firstStore,storeAt] at step
  all_goals repeat' split at step
  all_goals first | contradiction | (cases step; first | rfl | cases target)

private theorem store_event {A L g t o ev} (x : Nat)
    (imm : readValue L g t 32 (.imm x)=.ok (b32 x))
    (hf : Fires 2848 (eventTmpl A L g t (.mem (Lib.symStore 1 213336 [.imm x]))) ev
      (some o)) (sub : t.sub=0) : ∃ a bs, ev=⟨2848,.wr a bs⟩ := by
  have row := Lib.fires_st_sym (op := .mem (Lib.symStore 1 213336 [.imm x]))
    (A := A) (L := L) (g := g) (t := t) (e := ev) (u := o) (v := b32 x)
    (vec := 1) (off := 213336) (srcs := [.imm x]) (o := .imm x) (j := 0)
    (pc := 2848) rfl (by decide) sub rfl imm rfl (.inl rfl)
  generalize eventTmpl A L g t (.mem (Lib.symStore 1 213336 [.imm x])) = tpl at row hf
  obtain ⟨_,_,eq⟩ := row (by assumption)
  exact ⟨_,_,eq⟩

/-- A lane that reached the release at 2849 actually wrote the second dispatch word. -/
public theorem published_exit {Q L m X g k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k)=some ⟨2849,.bar 1 none .sync⟩) :
    ∃ u, u+1=k ∧ X.get (g,u)=some ⟨2848,.wr
      (Lib.wordAcc ⟨.shared,g/L.block,L.sharedBase+213336⟩) (b32 50529027).toBytes⟩ := by
  have len : k<(X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (by simp) ⟨control_tracked hp hX g k (Frame.lt_of_get hX he),fun _ _ => trivial⟩
  obtain ⟨_,_,_,_,inv,_,fire⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hs
    (by simp)
  have pc := EventFrame.fires_source_pc fire
  obtain ⟨w,ent,d,n,rfl⟩ := (pc ▸ state_role s).epilogue (by decide : 2565≤2849) (by decide) inv
  have only (s : Site) : s.pc=2849 → s=.sync1 := by
    cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
  have place := only d.site pc.symm
  obtain ⟨u,old,cnt,ev,eq,live,get,mv⟩ := epi_prev len.le (by rintro rfl; cases place) hs
  have atWord := prev_word mv place
  have clear := Frame.noUbBefore_of_get hX he u (by omega) _ get
  obtain ⟨t,ins,o,ht,_,hc,hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX get live clear
  change kernel.code[old.site.pc]?=some ins at hc
  change Fires old.site.pc _ _ _ at hf
  have src : old.site.pc=2848 := atWord ▸ rfl
  rw [src] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2848)
  change Fires 2848 (eventTmpl Assumptions.all L g t
    (.mem (Lib.symStore 1 213336 [.imm 50529027]))) ev o at hf
  generalize Assumptions.all = A at hf
  cases o with
  | none =>
    generalize eventTmpl A L g t (.mem (Lib.symStore 1 213336 [.imm 50529027])) = tpl at hf
    rcases fires_none_ends (pc := 2848) (e := ev) (m := tpl) hf with ⟨f,ub⟩|exit
    · exact (clear _ ub).elim
    · cases ev with | mk pc kind =>
        cases exit
        have last := Execution.exit_last hX (Frame.lt_of_get hX he) get
        omega
  | some o =>
    have sub : t.sub=0 := ht.2.1
    have row := store_event (A := A) (L := L) (g := g) (t := t) (ev := ev) (o := o)
      50529027 rfl
    generalize eventTmpl A L g t (.mem (Lib.symStore 1 213336 [.imm 50529027])) = tpl at row hf
    obtain ⟨a,b,rfl⟩ := row hf sub
    obtain ⟨addr,data⟩ := Lib.role_word hp hX get (.inr ⟨rfl,rfl⟩)
    exact ⟨u,eq,addr ▸ data ▸ get⟩

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
