-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Soft.Step
import Kernels.InklingRelDecode.Proof.Common.ValueThread
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Common.ValueFollow
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Lemmas.Kernel.CountClosed
public import Lemmas.Kernel.Safety.TableU

/-! # An invariant of the softmax value machine along the trace

A property of the value machine's state (and the position) that holds at its first state and is
kept by each step of the machine on an event of the trace (an event that is not undefined
behaviour, at the pc of the state's site) holds at every softmax state the thread reaches. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow Control Data

variable {Q : Params} {L : Launch} {g : Nat}

/-- **An invariant of the softmax value machine along the trace**, which may mention the entry. -/
public theorem soft_induct_ent {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (J : Control.Entry → Nat → Data.D → Prop)
    (init : ∀ ent k, J ent k {})
    (step : ∀ k ent old y e, X.get (g, k) = some e → (∀ f, e.kind ≠ .ub f) →
      e.pc = old.c.site.pc → succ ent L g old e = some (some y) → J ent k old → J ent (k + 1) y) :
    ∀ k, k ≤ (X.tr g).length → ∀ s, Frame.stateAt (threadD Q L) X g k = some (some s) →
      Frame.NoUbBefore X g k → ∀ w ent y n, s = softDState w ent y n → J ent k y := by
  have key := Frame.stateAt_inv (C := threadD Q L) (X := X) (g := g)
    (fun k s => Frame.NoUbBefore X g k → ∀ w ent y n, s = softDState w ent y n → J ent k y)
    (by
      intro nub w ent y n h
      have h1 := congrArg Prod.fst h
      change Code.enter (Startup.code Q L g) (Code.withStubs (fragD Q L g) Startup.Entry.pc)
        (Code.gatedExit Startup.enterOf (sel L g)) (Startup.init L g) = _ at h1
      simp [Code.enter, Code.gatedExit, enterOf_init] at h1)
    (by
      intro k e s s' he hs IH hn nub'
      have nub0 : Frame.NoUbBefore X g k := fun j hj => nub' j (by omega)
      have he' : X.get (g, k) = some e := he
      have hu : ∀ f, e.kind ≠ .ub f := nub' k (by omega) e he'
      have pc := Frame.event_pcU (fun g h => threadD_sound hp h) hX he' hs hu
      intro w ent y n hsd
      subst hsd
      rcases softD_pred hn with ⟨rfl, d, cnt, rfl⟩ | ⟨old, cnt, rfl, hv⟩
      · exact init _ _
      · exact step k ent old y e he' hu pc hv (IH nub0 w ent old cnt rfl))
  exact fun k hk s hs nub => key k s hk hs nub

/-- **An invariant of the softmax value machine along the trace.** -/
public theorem soft_induct {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (J : Nat → Data.D → Prop)
    (init : ∀ k, J k {})
    (step : ∀ k ent old y e, X.get (g, k) = some e → (∀ f, e.kind ≠ .ub f) →
      e.pc = old.c.site.pc → succ ent L g old e = some (some y) → J k old → J (k + 1) y) :
    ∀ k, k ≤ (X.tr g).length → ∀ s, Frame.stateAt (threadD Q L) X g k = some (some s) →
      Frame.NoUbBefore X g k → ∀ w ent y n, s = softDState w ent y n → J k y :=
  soft_induct_ent hp hX (fun _ => J) (fun _ => init) fun k ent => step k ent

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
