-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Soft.Ledger
public import Kernels.InklingRelDecode.Proof.Softmax.Soft.Early
import Lemmas.Kernel.CountClosed
public import Lemmas.Kernel.Safety.TableU
import Kernels.InklingRelDecode.Proof.Softmax.InvNext
import Kernels.InklingRelDecode.Proof.Softmax.PollStep
import Kernels.InklingRelDecode.Proof.Common.ValueThread
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Common.ValueFollow
import Kernels.InklingRelDecode.Proof.Common.StartupEvents

/-! # An invariant of the value machine with its control invariant and its round counter

The step of a property of the value machine may use the control machine's invariant of the state
before it and the match of its round counter with the polls of the trace (`Led`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow Control Data

variable {Q : Params} {L : Launch} {g : Nat}

private theorem inv_init {ent : Control.Entry} (ok : ent.Ok) (t : g % L.block < 256) :
    Inv ent (g % L.block) ({} : Data.D).c :=
  ⟨ok, t, Nat.zero_le _, fun _ => rfl, (fun _ h => by cases h), (fun _ h => by cases h),
    (fun h => by cases h), fun _ h => absurd rfl h⟩

/-- The instruction the event of a state fires: the state's thread, instruction and result. -/
@[expose] public def Fired (ent : Control.Entry) (L : Launch) (g : Nat) (y : Data.D)
    (e : Event) : Prop :=
  ∃ (t : TState) (ins : Instr) (o : Option TState), (Data.codeS ent L g).AtD y t ∧
    kernel.code[y.c.site.pc]? = some ins ∧
    Fires y.c.site.pc (eventTmpl Assumptions.all L g t ins.op) e o

/-- **An invariant of the value machine with its control invariant and its poll counter.** -/
public theorem soft_ind {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (J : Control.Entry → Nat → Data.D → Prop)
    (init : ∀ ent k, ent.Ok → pollRound 1257 ((X.tr g).take k) = 0 → J ent k {})
    (step : ∀ k ent old y e, ent.Ok → X.get (g, k) = some e → (∀ f, e.kind ≠ .ub f) →
      Fired ent L g old e → e.pc = old.c.site.pc → succ ent L g old e = some (some y) →
      Led X g k old →
      Inv ent (g % L.block) old.c → J ent k old → J ent (k + 1) y) :
    ∀ k, k ≤ (X.tr g).length → ∀ s, Frame.stateAt (threadD Q L) X g k = some (some s) →
      Frame.NoUbBefore X g k → (Early s → pollRound 1257 ((X.tr g).take k) = 0) ∧
      ∀ w ent y n, s = softDState w ent y n → ent.Ok →
        Led X g k y ∧ Inv ent (g % L.block) y.c ∧ J ent k y := by
  have thr : g % L.block < 256 := hp.block ▸ Nat.mod_lt _ (by rw [hp.block]; decide)
  have key := Frame.stateAt_inv (C := threadD Q L) (X := X) (g := g)
    (fun k s => Frame.NoUbBefore X g k → (Early s → pollRound 1257 ((X.tr g).take k) = 0) ∧
      ∀ w ent y n, s = softDState w ent y n → ent.Ok →
        Led X g k y ∧ Inv ent (g % L.block) y.c ∧ J ent k y)
    (by
      intro nub
      refine ⟨fun _ => by simp [pollRound], fun w ent y n h => ?_⟩
      have h1 := congrArg Prod.fst h
      change Code.enter (Startup.code Q L g) (Code.withStubs (fragD Q L g) Startup.Entry.pc)
        (Code.gatedExit Startup.enterOf (sel L g)) (Startup.init L g) = _ at h1
      simp [Code.enter, Code.gatedExit, enterOf_init] at h1)
    (by
      intro k e s s' he hs IH hn nub'
      have nub0 : Frame.NoUbBefore X g k := fun j hj => nub' j (by omega)
      have he' : X.get (g, k) = some e := he
      have hu : ∀ f, e.kind ≠ .ub f := nub' k (by omega) e he'
      obtain ⟨E1, E2⟩ := IH nub0
      have pc := Frame.event_pcU (fun g h => threadD_sound hp h) hX he' hs hu
      refine ⟨fun hearly => ?_, fun w ent y n hsd ok => ?_⟩
      · have es := early_pred hn hearly
        rw [poll_same he' (pc ▸ (early_pc es).1), E1 es]
      · subst hsd
        rcases softD_pred hn with ⟨rfl, d, cnt, rfl⟩ | ⟨old, cnt, rfl, hv⟩
        · have es : Early (proDState (Q := Q) (L := L) (g := g) w d cnt) := .inr ⟨w, d, rfl⟩
          have p0 : pollRound 1257 ((X.tr g).take (k + 1)) = 0 := by
            rw [poll_same he' (pc ▸ (early_pc es).1), E1 es]
          exact ⟨by simpa [Led, Site.afterS] using p0, inv_init ok thr, init ent _ ok p0⟩
        · change e.pc = old.c.site.pc at pc
          obtain ⟨led, inv, J0⟩ := E2 w ent old cnt rfl ok
          obtain ⟨c', hnc, rfl⟩ := succ_inv hv
          obtain ⟨t, ins, o, ht, -, hc, fire⟩ :=
            Frame.fired_siteU (fun g h => threadD_sound hp h) hX he' hs hu
          exact ⟨led_step he' pc hv led, inv_next inv hnc, step k ent old _ e ok he' hu
            ⟨t, ins, o, ht, hc, fire⟩ pc hv led inv J0⟩)
  exact fun k hk s hs nub => key k s hk hs nub

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
