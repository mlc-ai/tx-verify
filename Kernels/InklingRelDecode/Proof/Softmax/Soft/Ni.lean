-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Soft.Typed
public import Kernels.InklingRelDecode.Proof.Softmax.Data.NiStep

/-! # The maxima of the value state are typed along the trace

Given that the score loads return numbers and that the shuffles of pc 1838 send and bring numbers
or `-inf`, the value state is typed and its running maxima are numbers or `-inf` at every softmax
state. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow Control Data

variable {Q : Params} {L : Launch} {g : Nat}

/-- **A step of the value machine keeps the typing and the maxima.** -/
public theorem soft_ni_step {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨Flow.tmemLoad_0, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : ∀ k mode sent b c recv ok, X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ →
      SK.ni.Has sent ∧ SK.ni.Has recv) {k : Nat} {ent : Control.Entry} {old y : Data.D}
    {e : Event} (he : X.get (g, k) = some e) (hu : ∀ f, e.kind ≠ .ub f)
    (pc : e.pc = old.c.site.pc) (hn : succ ent L g old e = some (some y))
    (hv : VTyp old.v ∧ NiVals old.v) : VTyp y.v ∧ NiVals y.v := by
  refine ⟨vtyp_succ hp hX hf hS he pc hn hv.1, ?_⟩
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  refine ni_step hv.2 fun hs mode a b c r ok hk => ?_
  have e1 : e.pc = 1838 := by rw [pc, hs]; rfl
  obtain ⟨pc0, kind⟩ := e
  change pc0 = 1838 at e1
  subst e1
  change kind = _ at hk
  subst hk
  exact h5 k mode a b c r ok he

/-- **The value state is typed and its maxima are numbers or `-inf`** at every softmax state. -/
public theorem soft_ni {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨Flow.tmemLoad_0, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : ∀ k mode sent b c recv ok, X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ →
      SK.ni.Has sent ∧ SK.ni.Has recv) :
    ∀ k, k ≤ (X.tr g).length → ∀ s, Frame.stateAt (threadD Q L) X g k = some (some s) →
      Frame.NoUbBefore X g k → ∀ w ent y n, s = softDState w ent y n →
        VTyp y.v ∧ NiVals y.v := by
  refine soft_induct hp hX (fun _ y => VTyp y.v ∧ NiVals y.v) (fun _ => ⟨⟨fun _ => bw_dflt,
    fun _ => bw_dflt, fun x hx => by simp at hx⟩, ni_init⟩) ?_
  intro k ent old y e he hu pc hn hv
  exact soft_ni_step hp hX hf hS h5 he hu pc hn hv

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
