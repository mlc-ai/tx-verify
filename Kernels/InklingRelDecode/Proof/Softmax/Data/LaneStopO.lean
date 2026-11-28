-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.LaneStop
import Kernels.InklingRelDecode.Proof.Softmax.Soft.Ni
import Kernels.InklingRelDecode.Proof.Softmax.Data.Site

@[expose] public section

/-! # The accumulator words of the value state are numbers

The words the accumulator load of pc 2260 returned (`Vals.ov`) are numbers when the loads of the
lane are: `lane_stop_o` is `lane_stop` with that fact about the machine state `y`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Assumption Control Soft

variable {Q : Params} {L : Launch} {g : Nat}

/-- The accumulator words of the value state are numbers. -/
def OTyp (v : Vals) : Prop := ∀ x ∈ v.ov, SK.fl.Has x

/-- **The step keeps the accumulator words numbers**, given the words of the load of pc 2260. -/
theorem otyp_step {d : D} {ev : Event} {s : Site} (hv : OTyp d.v)
    (ho : d.c.site = .ldO → ∀ a vals sh, ev.kind = .tc (.ld a vals sh) → ∀ x ∈ vals,
      SK.fl.Has x) : OTyp (record L d ev s) := by
  unfold record
  split <;> (try dsimp only) <;> (try split) <;> first | exact hv | exact ho ‹_› _ _ _ ‹_›

/-- **The stop before an event**, with the typing of the value state and of its accumulator
words: the loads of pc 2260 of the lane return numbers (`hO`). -/
public theorem lane_stop_o {m : Mem0} {X : Execution} {k : Nat} {e : Event} {t0 : TState}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨Flow.tmemLoad_0, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv)
    (hO : ∀ k a vals sh, X.get (g, k) = some ⟨2260, .tc (.ld a vals sh)⟩ → ∀ x ∈ vals,
      SK.fl.Has x)
    (lane : g % L.block < 128) (get : X.get (g, k) = some e)
    (hr1 : Run kernel Assumptions.all L g {} ((X.tr g).take (k + 1)) (some t0))
    (lo : 574 < e.pc) (hi : e.pc < 2331) :
    ∃ ent y sp, y.c.site.pc = e.pc ∧ (codeS ent L g).AtD y sp ∧
      EStep kernel Assumptions.all L g sp e (some t0) ∧ NiVals y.v ∧ OTyp y.v := by
  obtain ⟨ent, y, sp, h1, h2, h3, ind⟩ := lane_stop_core hp hX get hr1 lo hi
  obtain ⟨⟨-, ni⟩, ot⟩ := ind (fun _ y => (VTyp y.v ∧ NiVals y.v) ∧ OTyp y.v)
    (fun _ => ⟨⟨⟨fun _ => bw_dflt, fun _ => bw_dflt, fun x hx => by simp at hx⟩, ni_init⟩,
      fun x hx => by simp at hx⟩)
    fun k ent old y e he hu pc hn hv => by
      refine ⟨soft_ni_step hp hX hf hS (h5 lane) he hu pc hn hv.1, ?_⟩
      obtain ⟨c', -, rfl⟩ := succ_inv hn
      refine otyp_step hv.2 fun hs a vals sh hk x hx => ?_
      have e1 : e.pc = 2260 := by rw [pc, hs]; rfl
      obtain ⟨pc0, kind⟩ := e
      change pc0 = 2260 at e1
      subst e1
      change kind = _ at hk
      subst hk
      exact hO k a vals sh he x hx
  exact ⟨ent, y, sp, h1, h2, h3, ni, ot⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
