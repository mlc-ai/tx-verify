-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.FollowControl
public import Kernels.InklingRelDecode.Proof.Common.Where
public import Kernels.InklingRelDecode.Proof.Prologue.RefWords

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The first prologue state is entered from startup. Every other step into the
prologue comes from a preceding prologue state. -/
private theorem pro_pred {Q L g w d n e} {s : (thread Q L g).D}
    (hs : (thread Q L g).next s e = some (some (proState w d n))) :
    d = {} ∨ ∃ old cnt, s = proState w old cnt ∧
      Prologue.Control.next Q L g old e = some (some d) := by
  obtain ⟨a,b⟩ := Code.counted_next_some hs
  obtain ⟨s,cnt⟩ := s
  rcases s with start | ⟨r,old⟩
  · change (Startup.succ L g start e).map _ = _ at a
    rcases hn : Startup.succ L g start e with _ | _ | t <;> rw [hn] at a <;> try solve | cases a
    simp only [Option.map_some,Option.some.injEq] at a
    obtain ⟨site,tm,x,word⟩ := t
    cases site <;> try contradiction
    rename_i entry
    cases entry <;> cases a
    exact .inl rfl
  change ((Code.withStubs (frag Q L g) Startup.Entry.pc r).next old e).map _ = _ at a
  rcases hn : (Code.withStubs (frag Q L g) Startup.Entry.pc r).next old e with _ | _ | t <;>
    rw [hn] at a <;> try solve | cases a
  simp only [Option.map_some,Option.some.injEq] at a
  cases a
  rcases old with old | ⟨ent,old⟩
  · change (Prologue.Control.next Q L g old e).map _ = _ at hn
    rcases hv : Prologue.Control.next Q L g old e with _ | _ | dn <;> rw [hv] at hn <;>
      try solve | cases hn
    simp only [Option.map_some,Option.some.injEq] at hn
    unfold Code.enter at hn
    split at hn <;> cases hn
    exact .inr ⟨old,cnt,rfl,hv⟩
  · change ((softCode ent L g).next old e).map _ = _ at hn
    rcases hv : (softCode ent L g).next old e with _ | _ | dn <;> rw [hv] at hn <;> cases hn

/-- A noninitial prologue state has an actual local predecessor in the trace. -/
theorem pro_prev {Q L g X w k d n} (hk : k≤(X.tr g).length) (later : d≠{})
    (hs : Frame.stateAt (thread Q L) X g k = some (some (proState w d n))) :
    ∃ u old cnt ev, u+1=k ∧ Frame.stateAt (thread Q L) X g u=some (some (proState w old cnt)) ∧
      X.get (g,u)=some ev ∧ Prologue.Control.next Q L g old ev=some (some d) := by
  cases k with
  | zero =>
    rw [Frame.stateAt_zero] at hs
    have start := congrArg Prod.fst (Option.some.inj (Option.some.inj hs))
    change Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) (Startup.init L g) = _ at start
    rw [enter_inl enterOf_init] at start
    cases start
  | succ k =>
    have get := List.getElem?_eq_getElem (l := X.tr g) (i := k) (by omega)
    rw [Frame.stateAt_succ get] at hs
    rcases prev : Frame.stateAt (thread Q L) X g k with _|_|s <;> rw [prev] at hs <;>
      try solve | cases hs
    obtain ⟨old,cnt,rfl,step⟩ := (pro_pred hs).resolve_left later
    exact ⟨k,old,cnt,_,rfl,prev,get,step⟩

theorem pro_known_step {Q L m X g k w old cnt dn ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ev)
    (hs' : Frame.stateAt (thread Q L) X g k = some (some (proState w old cnt)))
    (known : Prologue.Known Q ((L.ctaidOf (g/L.block)).get .z) old)
    (hn : Prologue.Control.next Q L g old ev = some (some dn)) :
    Prologue.Known Q ((L.ctaidOf (g/L.block)).get .z) dn := by
  apply Prologue.known_next known hn
  intro j site a bs kind
  have hnub : ∀ f, ev.kind ≠ .ub f := by rw [kind]; simp
  obtain ⟨t,ins,o,ht,_,hc,fire⟩ := Frame.fired_siteU
    (fun g hg => thread_sound hp hg) hX he hs' hnub
  have pc := EventFrame.fires_source_pc fire
  have eq : ev = ⟨old.site.pc,.rd a bs⟩ := by
    change ev.pc = old.site.pc at pc
    rw [←pc,←kind]
  rw [eq] at he fire
  exact Prologue.request_value hp hX (Frame.lt_of_get hX he) j site ht hc he fire

/-- The request words come from the three launch arrays regardless of the
other lanes' progress or the values previously observed in shared memory. -/
theorem pro_known {Q L m X g k w d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k ≤ (X.tr g).length)
    (hs : Frame.stateAt (thread Q L) X g k = some (some (proState w d n))) :
    Prologue.Known Q ((L.ctaidOf (g/L.block)).get .z) d := by
  induction k generalizing d n with
  | zero =>
    rw [Frame.stateAt_zero] at hs
    have start := congrArg Prod.fst (Option.some.inj (Option.some.inj hs))
    change Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) (Startup.init L g) = _ at start
    rw [enter_inl enterOf_init] at start
    cases start
  | succ k ih =>
    have he := List.getElem?_eq_getElem (l := X.tr g) (i := k) (by omega)
    rw [Frame.stateAt_succ he] at hs
    rcases hs' : Frame.stateAt (thread Q L) X g k with _ | _ | s <;> rw [hs'] at hs <;>
      try solve | cases hs
    rcases pro_pred (s := s) hs with rfl | ⟨old,cnt,rfl,hn⟩
    · exact Prologue.known_init ..
    · exact pro_known_step hp hX he hs' (ih (by omega) hs') hn


end
end PTX.Kernels.InklingRelDecode.Proof
