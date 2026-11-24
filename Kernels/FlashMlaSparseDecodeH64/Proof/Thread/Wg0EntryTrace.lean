-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.LaunchReads
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Kernel.Frame

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

open PTX.Flow LaunchReads

noncomputable section

/-- The states before the first QK acquire. Optional input sites retain the pointer choice,
and the extra length site retains whether the main length has already been read. -/
def BeforeFirstQk (P : Params) (d : D) : Prop :=
  d.block = 0 ∧
    match d.site with
    | .sink => P.sinkBase.isSome = true
    | .lenOrig => P.topkLenBase.isSome = true
    | .lenExtra => P.extraTopkLenBase.isSome = true ∧ d.origLenRead = P.topkLenBase.isSome
    | .bulkWait | .lastStore | .wg0Sync | .maskReady | .qkDone => True
    | _ => False

private theorem before_afterLen {P : Params} {L : Launch} {g : Nat} (read : Bool)
    (hr : read = P.topkLenBase.isSome) :
    BeforeFirstQk P { init P L g with site := afterLen P, origLenRead := read } := by
  unfold BeforeFirstQk afterLen
  split <;> simp [init, *]

private theorem before_afterSink {P : Params} {L : Launch} {g : Nat} :
    BeforeFirstQk P { init P L g with site := afterSink P } := by
  by_cases h : P.topkLenBase.isSome = true
  · simp [BeforeFirstQk, afterSink, h, init]
  · have hf : false = P.topkLenBase.isSome := by
      cases hs : P.topkLenBase.isSome <;> simp_all
    simpa [afterSink, h, init] using before_afterLen (P := P) (L := L) (g := g) false hf

/-- The launch puts WG0 at the first before-QK state. -/
theorem beforeFirstQk_init (P : Params) (L : Launch) (g : Nat) :
    BeforeFirstQk P (init P L g) := by
  by_cases h : P.sinkBase.isSome = true
  · simp [BeforeFirstQk, init, firstSite, h]
  · simpa [init, firstSite, h] using before_afterSink (P := P) (L := L) (g := g)

/-- Every actual event before the first QK acquire stays tracked. A successful poll
reaches the first post-acquire fence; a fault can end the role's trace. -/
theorem next_beforeFirstQk {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    {g j : Nat} {d : D} {e : Event} {o : Option TState}
    (he : X.get (g, j) = some e) (hf : (Wg0.code P L g).toMachine.Fired (some d) e o)
    (hb : BeforeFirstQk P d) :
    Wg0.next P L g d e = none ∨
      ∃ d', Wg0.next P L g d e = some (some d') ∧
        (BeforeFirstQk P d' ∨ d'.block = 0 ∧ d'.site = .fenceLoad) := by
  have hblock := hb.1
  have hbatch : eOf L g < P.b := Wg1Mma.eOf_lt_b hpre
  cases hd : d.site <;> simp only [BeforeFirstQk, hd] at hb
  case sink =>
    obtain ⟨ptr, hptr⟩ := Option.isSome_iff_exists.mp hb.2
    obtain ⟨bs, hr⟩ := fired_sink hpre hptr hd hf
    obtain ⟨v, s, hv, hvalue, hfinite⟩ := rebuild_sink hpre hX hptr he hr
    refine .inr ⟨{ init P L g with site := afterSink P }, ?_, .inl before_afterSink⟩
    simp only [Wg0.next, nextSite, hd, hr.1, hv, hvalue, hfinite, Except.toOption,
      ↓reduceIte]
  case lenOrig =>
    obtain ⟨ptr, hptr⟩ := Option.isSome_iff_exists.mp hb.2
    obtain ⟨bs, hr⟩ := fired_main hpre hbatch hptr hd hf
    have hv := rebuild_main hpre hX hbatch hptr he hr
    refine .inr ⟨{ init P L g with site := afterLen P, origLenRead := true }, ?_,
      .inl (before_afterLen true hb.2.symm)⟩
    simp only [Wg0.next, nextSite, hd, hr.1, hv, ↓reduceIte]
  case lenExtra =>
    obtain ⟨ptr, hptr⟩ := Option.isSome_iff_exists.mp hb.2.1
    obtain ⟨bs, hr⟩ := fired_extra hpre hbatch hptr hd hf
    have hv := rebuild_extra hpre hX hbatch hptr he hr
    refine .inr ⟨{ init P L g with site := .bulkWait }, ?_, .inl ⟨rfl, trivial⟩⟩
    simp only [Wg0.next, nextSite, hd, hr.1, hv, hb.2.2, and_self, ↓reduceIte]
  case bulkWait =>
    cases hk : e.kind <;> simp [Wg0.next, nextSite, hd, hk, BeforeFirstQk, hblock]
  case lastStore =>
    cases hk : e.kind <;> simp [Wg0.next, nextSite, hd, hk, BeforeFirstQk, hblock]
  case wg0Sync =>
    cases hk : e.kind <;> simp [Wg0.next, nextSite, hd, hk, BeforeFirstQk, hblock]
  case maskReady =>
    cases hk : e.kind <;> simp [Wg0.next, nextSite, hd, hk, waitStep]
    case wait m parity ok acquire scope =>
      cases ok <;> simp [BeforeFirstQk, hblock, hd]
  case qkDone =>
    cases hk : e.kind <;> simp [Wg0.next, nextSite, hd, hk, waitStep]
    case wait m parity ok acquire scope =>
      cases ok <;> simp [BeforeFirstQk, hblock, hd]
  all_goals exact (hb.2 : False).elim

/-- The composed machine cannot dismiss a WG0 state before its first QK acquire. -/
theorem composed_beforeFirstQk_next {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    {g j : Nat} {d : D} {e : Event} (he : X.get (g, j) = some e)
    (ht : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)))
    (hb : BeforeFirstQk P d) :
    Machine.next P L g (.wg0 d) e = none ∨
      ∃ d', Machine.next P L g (.wg0 d) e = some (some (.wg0 d')) ∧
        (BeforeFirstQk P d' ∨ d'.block = 0 ∧ d'.site = .fenceLoad) := by
  obtain ⟨o, hf⟩ := (Frame.trace hs hX (Frame.lt_of_get hX he)).fired_at he ht
  have hf' : (Wg0.code P L g).toMachine.Fired (some d) e o := hf
  rcases next_beforeFirstQk hpre hX he hf' hb with hd | ⟨d', hd, hb'⟩
  · exact .inl (by simp [Machine.next, hd])
  · exact .inr ⟨d', by simp [Machine.next, hd], hb'⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
