-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.ShapeFault

@[expose] public section

/-!
# The prologue's `next` never rejects a followed event

`Safety.Protocol.faultFree` asks that no followed event (one with a later event of its thread) be
one the thread machine's `next` rejects with `none`. The prologue (`ProA.next`) rejects an event
with `none` only where the event is not of the kind the site matches on (every value-dependent
case is `some none`: the machine stops following the thread, it does not declare a fault), and
`ProA.stops` (the reason `ProA.Stop` of every `none` at a fired event, `Code.StopsFor`) names the
two places: the election after a broadcast whose received word has no bits (`ProA.PelDead`: the
`and.b32` that reads the word faults) and a base word without an outcome of the add at pc 319. So no
other prologue state has a `none` successor at a fired event (`ProA.next_ne_none_of_fired`), and
`pro_followed_ne_none` is the thread-machine form for a followed event of an execution; the
received words have bits in every execution (`Interface.pshSo_all`).

Not covered (value-dependent `none`, see `ShapeFault` and the gap table): the common start's read
of the Tensor Memory base word, the MMA warp's read of `num_iters`, the epilogue's reciprocal and
64-word load, the softmax region's bias bytes, tile words and sum update, and the bridge's
`NoFault`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

/-- **A fired event at a prologue state has a successor or a `some none`**, never `none`, except
at the election after a broadcast whose received word has no bits (`PelDead`) and where the base
word gives the prologue's add on it no outcome (`addOk`). -/
theorem next_ne_none_of_fired {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}
    (hF : Fired L g d e (some u)) (hok : ¬ PelDead d) (hadd : addOk d.dt.w = true)
    (hdiv : d.site = .bar2 → div182 L g d.dt = true) :
    next L g d e ≠ none := by
  obtain ⟨t, ins, h, hinv, hc, hf⟩ := fired_unpack hF
  exact Code.next_ne_none (stops (L := L) (g := g) d.dt.pro d) h hinv hc hf
    (by rintro (h | h | ⟨h1, h2⟩) <;> simp_all)

end PTX.Kernels.InklingRelDecode.Proof.ProA

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A followed event at a prologue state is not rejected by the thread machine.** -/
theorem pro_followed_ne_none (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k : Nat} {d : ProA.D} {e e' : Event}
    (hg : g < L.threads) (he : (X.tr g)[k]? = some e) (he' : (X.tr g)[k + 1]? = some e')
    (hσ : St Q L X g k = some (some (.d (.pro d)))) (hok : ¬ ProA.PelDead d)
    (hadd : ProA.addOk d.dt.w = true) (hdiv : d.site = .bar2 → ProA.div182 L g d.dt = true) :
    (threadCode L g Q).next (.d (.pro d)) e ≠ none := by
  obtain ⟨u, hF⟩ := fired_of_followed hS hX hg he he' hσ
  have hn := ProA.next_ne_none_of_fired (fired_pro hF) hok hadd hdiv
  rw [next_d]
  change (DComp.proNext L g Q d e).map (Option.map TSt.d) ≠ none
  unfold DComp.proNext
  split
  · split <;> simp
  · intro h
    apply hn
    cases hh : ProA.next L g d e with
    | none => rfl
    | some o => simp [hh] at h

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
