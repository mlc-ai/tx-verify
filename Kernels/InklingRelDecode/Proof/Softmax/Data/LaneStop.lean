-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.WinLane
public import Kernels.InklingRelDecode.Flow.Sites.Part000
public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Inp
public import Kernels.InklingRelDecode.Proof.Softmax.Data.NiStep
public import Kernels.InklingRelDecode.Proof.Softmax.Data.CodeS
import Kernels.InklingRelDecode.Proof.Softmax.Soft.Ni
import Kernels.InklingRelDecode.Proof.Softmax.Soft.Induct
import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpTyped
import Kernels.InklingRelDecode.Proof.Common.ValueThread
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Lemmas.Kernel.PostEvent

/-! # The machine state before the last event of a lane

For an event of a softmax data lane (its position inside the softmax region) the value machine's
state before it is typed (`VTyp`, `NiVals`), its facts hold at the state where the event fired, and
that state's event steps to the lane's state after it. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Assumption Control Soft

variable {Q : Params} {L : Launch} {g : Nat}

/-- **The stop before an event**, with the induction of the value machine: the machine state `y`
whose site is the event's, the concrete state `sp` it fired at (with the machine's facts), and every
invariant `J` of the machine along the trace holds at `y`. -/
public theorem lane_stop_core {m : Mem0} {X : Execution} {k : Nat} {e : Event} {t0 : TState}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get (g, k) = some e)
    (hr1 : Run kernel Assumptions.all L g {} ((X.tr g).take (k + 1)) (some t0))
    (lo : 574 < e.pc) (hi : e.pc < 2331) :
    ∃ ent y sp, y.c.site.pc = e.pc ∧ (codeS ent L g).AtD y sp ∧
      EStep kernel Assumptions.all L g sp e (some t0) ∧
      ∀ J : Nat → Data.D → Prop, (∀ k, J k {}) →
        (∀ k ent old y e, X.get (g, k) = some e → (∀ f, e.kind ≠ .ub f) →
          e.pc = old.c.site.pc → succ ent L g old e = some (some y) → J k old → J (k + 1) y) →
        J k y := by
  have hk : (X.tr g)[k]? = some e := get
  have len : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp hk).1.le
  obtain ⟨u, s, -, -, hes⟩ := Run.unsnoc _ e (by
    rw [List.take_add_one, hk, Option.toList_some] at hr1
    exact hr1)
  have clean : ∀ f, e.kind ≠ .ub f := fun f h => by
    obtain ⟨ins1, hc1, -, hf1⟩ := EventFrame.estep_event_source hes
    exact fires_some_not_ub hf1 e.pc f (by cases e; simp_all)
  obtain ⟨w, ent, d, n, hsc, atpc⟩ := at_site hp hX get clean lo hi
  obtain ⟨s0, hs0, hse⟩ := value_state hsc
  obtain ⟨y, hy, rfl⟩ := softD_shape hse
  have nub := Frame.noUbBefore_of_get hX get
  obtain ⟨sp, ins0, hat, -, -, hes'⟩ := Frame.post_event (C := threadD Q L)
    (fun g h => threadD_sound hp h) hX get hr1 hs0
  exact ⟨ent, y, sp, by rw [hy]; exact atpc.symm, hat, hes', fun J init step =>
    soft_induct hp hX J init step k len _ hs0 nub w ent y n rfl⟩

/-- **The stop before an event**: the machine state `y` whose site is the event's, the concrete
state `sp` it fired at (with the machine's facts) and the typing of `y`'s words. -/
public theorem lane_stop {m : Mem0} {X : Execution} {k : Nat} {e : Event} {t0 : TState}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨Flow.tmemLoad_0, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv)
    (lane : g % L.block < 128) (get : X.get (g, k) = some e)
    (hr1 : Run kernel Assumptions.all L g {} ((X.tr g).take (k + 1)) (some t0))
    (lo : 574 < e.pc) (hi : e.pc < 2331) :
    ∃ ent y sp, y.c.site.pc = e.pc ∧ (codeS ent L g).AtD y sp ∧
      EStep kernel Assumptions.all L g sp e (some t0) ∧ VTyp y.v ∧ NiVals y.v := by
  obtain ⟨ent, y, sp, h1, h2, h3, ind⟩ := lane_stop_core hp hX get hr1 lo hi
  exact ⟨ent, y, sp, h1, h2, h3, ind (fun _ y => VTyp y.v ∧ NiVals y.v)
    (fun _ => ⟨⟨fun _ => bw_dflt, fun _ => bw_dflt, fun x hx => by simp at hx⟩, ni_init⟩)
    fun k ent old y e he hu pc hn hv => soft_ni_step hp hX hf hS (h5 lane) he hu pc hn hv⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
