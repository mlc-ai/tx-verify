-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Prologue.Data.Machine
import Kernels.InklingRelDecode.Proof.Common.ValueSound
public import Kernels.InklingRelDecode.Proof.Common.ValueFollow
public import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Lemmas.Kernel.StateMap
import Lemmas.Kernel.FrameU
import Lemmas.Kernel.CountClosed

@[expose] public section

/-! # The value state of the prologue along a trace

The value thread machine `threadD` is the control thread machine with the prologue's value
machine in its slot, and a value state is followed whenever its control state is
(`threadD_stepMap`). `proD_event` is the value state at an event, `proD_induct` an invariant along
the states. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Flow PTX.Proof Control Data

variable {Q : Params} {L : Launch} {g : Nat}

public theorem proD_shape {s : (threadD Q L g).D} {w : Value} {c : Prologue.Control.D}
    {n : Cls → Nat} (h : eraseThread Q L g s = proState w c n) :
    ∃ d : Prologue.Data.D, d.c = c ∧ s = proDState w d n := by
  obtain ⟨a, m⟩ := s
  rcases a with b | ⟨j | r, x⟩
  · cases h
  · cases j with
    | dispatch w' x' => cases h
    | prologue w' =>
      rcases x with d | ⟨en, y⟩
      · cases h
        exact ⟨d, rfl, rfl⟩
      · rcases y with y | ⟨u, y⟩ <;> cases h
  · cases h

/-- **The value state at an event of the prologue**, with its concrete state and the fired
event (as `prologue_event` for the control machine). -/
public theorem proD_event {m : Mem0} {X : Execution} {k : Nat} {ev : Event} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g, k) = some ev)
    (hu : ∀ f, ev.kind ≠ .ub f) (lo : 27 < ev.pc) (hi : ev.pc < 574) :
    ∃ (w : Value) (d : Prologue.Data.D) (n : Cls → Nat) (t : TState) (ins : Instr)
      (u : Option TState),
      Frame.stateAt (threadD Q L) X g k = some (some (proDState w d n)) ∧
      (Prologue.Data.code Q L g w).AtD d t ∧ ev.pc = d.c.site.pc ∧
      kernel.code[d.c.site.pc]? = some ins ∧
      Fires d.c.site.pc (eventTmpl Assumptions.all L g t ins.op) ev u := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨c0, hc0, -⟩ := Frame.good_stateU (J := fun _ _ => True)
    (fun g hg => thread_sound hp hg) hX he (fun _ f h => hu f (congrArg Event.kind h))
    ⟨control_tracked hp hX g k hg, fun _ _ => trivial⟩
  obtain ⟨s, hs, hse⟩ := value_state hc0
  have pc := Frame.event_pcU (fun g h => thread_sound hp h) hX he hc0 hu
  obtain ⟨w, c, n, rfl⟩ := (pc ▸ state_role c0).prologue lo hi
  obtain ⟨d, rfl, rfl⟩ := proD_shape hse
  obtain ⟨t, ins, o, ht, -, hc, fire⟩ :=
    Frame.fired_siteU (fun g h => threadD_sound hp h) hX he hs hu
  exact ⟨w, d, n, t, ins, o, hs, ht, pc, hc, fire⟩

public theorem proD_pred {s : (threadD Q L g).D} {e : Event} {w : Value} {d : Prologue.Data.D}
    {n : Cls → Nat}
    (hs : (threadD Q L g).next s e = some (some (proDState w d n))) :
    d = {} ∨ ∃ old cnt, s = proDState w old cnt ∧
      Prologue.Data.succ Q L g old e = some (some d) := by
  obtain ⟨a, b⟩ := Code.counted_next_some hs
  obtain ⟨s, cnt⟩ := s
  rcases s with start | ⟨r, old⟩
  · change (Startup.succ L g start e).map _ = _ at a
    rcases hn : Startup.succ L g start e with _ | _ | t <;> rw [hn] at a <;> try solve | cases a
    simp only [Option.map_some, Option.some.injEq] at a
    obtain ⟨site, tm, x, word⟩ := t
    cases site <;> try contradiction
    rename_i entry
    cases entry <;> cases a
    exact .inl rfl
  change ((Code.withStubs (fragD Q L g) Startup.Entry.pc r).next old e).map _ = _ at a
  rcases hn : (Code.withStubs (fragD Q L g) Startup.Entry.pc r).next old e with _ | _ | t <;>
    rw [hn] at a <;> try solve | cases a
  simp only [Option.map_some, Option.some.injEq] at a
  cases a
  rcases old with old | ⟨ent, old⟩
  · change (Prologue.Data.succ Q L g old e).map _ = _ at hn
    rcases hv : Prologue.Data.succ Q L g old e with _ | _ | dn <;> rw [hv] at hn <;>
      try solve | cases hn
    simp only [Option.map_some, Option.some.injEq] at hn
    unfold Code.enter at hn
    split at hn <;> cases hn
    exact .inr ⟨old, cnt, rfl, hv⟩
  · change ((softDCode ent L g).next old e).map _ = _ at hn
    rcases hv : (softDCode ent L g).next old e with _ | _ | dn <;> rw [hv] at hn <;> cases hn


/-- **An invariant along the value states of the prologue**: it holds at the initial state, and a
state that has it keeps it over every event that is not undefined behavior. -/
public theorem proD_induct {X : Execution} (I : Nat → Prologue.Data.D → Prop)
    (init : ∀ k, I k {})
    (step : ∀ k e (w : Value) old (cnt : Cls → Nat) d', X.get (g, k) = some e →
      (∀ f, e.kind ≠ .ub f) →
      Frame.stateAt (threadD Q L) X g k = some (some (proDState w old cnt)) → I k old →
      Prologue.Data.succ Q L g old e = some (some d') → I (k + 1) d')
    {k : Nat} {w : Value} {d : Prologue.Data.D} {n : Cls → Nat} (hk : k ≤ (X.tr g).length)
    (hs : Frame.stateAt (threadD Q L) X g k = some (some (proDState w d n)))
    (nub : Frame.NoUbBefore X g k) : I k d := by
  have key := Frame.stateAt_inv (C := threadD Q L) (X := X) (g := g)
    (fun k s => ∀ w d n, s = proDState w d n → Frame.NoUbBefore X g k → I k d)
    (by
      intro w d n e
      have h := congrArg Prod.fst e
      change Code.enter (Startup.code Q L g) (Code.withStubs (fragD Q L g) Startup.Entry.pc)
        (Code.gatedExit Startup.enterOf (sel L g)) (Startup.init L g) = _ at h
      simp [Code.enter, Code.gatedExit, enterOf_init] at h)
    (by
      intro k e s s' he hs IH hn w' d' n' rfl nub'
      rcases proD_pred hn with rfl | ⟨old, cnt, rfl, hv⟩
      · exact init _
      · have he' : X.get (g, k) = some e := he
        exact step k e w' old cnt d' he' (nub' k (by omega) e he') hs
          (IH w' old cnt rfl fun j hj => nub' j (by omega)) hv) k _ hk hs
  exact key w d n rfl nub

end PTX.Kernels.InklingRelDecode.Proof.Prologue
