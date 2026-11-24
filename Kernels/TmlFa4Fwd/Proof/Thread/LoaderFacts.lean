-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.Loader
public import Kernels.TmlFa4Fwd.Proof.LoaderReadyCycle
public import Kernels.TmlFa4Fwd.Proof.LoaderRingMbarAddress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof
open PTX.Kernels.TmlFa4Fwd.Loader
open DecodedObservation

noncomputable section

/-- The initialized ready object named by a loader publication. -/
def readyObject (l : Launch) (g : Nat) (slot : Fin 3) : Loc :=
  Prologue.initObject l (g / l.block) (readySlot slot)

/-- A published packet arrives at a ready slot of the issuing CTA. Every observed ordinary
arrival is a publication of one of the six packet forms. -/
theorem readyObservation {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {e : Event} {loc : Loc} {noinc : Bool}
    (he : X.get i = some e) (hk : e.kind = .asyncArrive loc noinc) :
    ∃ pub : Publication, noinc = true ∧ loc = readyObject l i.1 pub.slot ∧
      observe l i.1 e = .publish pub := by
  obtain ⟨pc, kind⟩ := e
  dsimp only at hk
  subst kind
  obtain ⟨⟨site, hPC⟩, rfl, _, _⟩ := actualAsyncArrival hX he
  have hSite : pc ∈ [674, 904, 1137, 1342, 1602, 1735] := by rw [hPC]; fin_cases site <;> decide
  rcases i with ⟨g, index⟩
  obtain ⟨off, hOff, hLoc⟩ := loaderAsyncAddress hp hX he hSite
  have hAddress : ∃ slot : Fin 3, loc = readyObject l g slot := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
    rcases hOff with rfl | rfl | rfl
    · exact ⟨0, hLoc⟩
    · exact ⟨1, hLoc⟩
    · exact ⟨2, hLoc⟩
  have hSlot : (locateSlot l g loc true).isSome := by
    obtain ⟨slot, hs⟩ := hAddress
    apply List.find?_isSome.mpr
    exact ⟨slot, by simp, beq_iff_eq.mpr hs⟩
  obtain ⟨slot, hs⟩ := Option.isSome_iff_exists.mp hSlot
  have hBeq : (loc == readyObject l g slot) = true :=
    List.find?_some (p := fun k : Fin 3 => loc == readyObject l g k) hs
  have hMatch : loc = readyObject l g slot := beq_iff_eq.mp hBeq
  have hPacket : observePacket pc true = some (packetOfSite site) := by
    rw [hPC]
    fin_cases site <;> decide
  exact ⟨⟨packetOfSite site, slot⟩, rfl, hMatch, by simp [observe, hPacket, hs]⟩

/-- An actual no-increment arrival records its packet and slot in the public role history. -/
theorem readyStep {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} {loc : Loc} {noinc : Bool}
    (he : X.get (g, index) = some e) (hk : e.kind = .asyncArrive loc noinc) :
    ∃ pub, noinc = true ∧ loc = readyObject l g pub.slot ∧
      (atPrefix l X g (index + 1)).published = pub :: (atPrefix l X g index).published := by
  obtain ⟨pub, hn, hl, ha⟩ := readyObservation hp hX he hk
  exact ⟨pub, hn, hl, (congrArg D.published (prefixStep he)).trans (advancePublication ha)⟩

private theorem readyObservedTargets {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g, index) = some e) (d : D) :
    ((advance l g d e).published.reverse.map (readyObject l g ∘ Publication.slot)) =
      (d.published.reverse.map (readyObject l g ∘ Publication.slot)) ++ (readyTarget e).toList := by
  rcases e with ⟨pc, kind⟩
  cases kind <;> try (solve | simp [advance, observe, readyTarget])
  case asyncArrive loc noinc =>
    obtain ⟨pub, rfl, hLoc, hPub⟩ := readyObservation hp hX he rfl
    rw [advancePublication hPub]
    simp [readyTarget, hLoc]
  case asyncCommit =>
    cases h : observePacket pc false <;> simp [advance, observe, readyTarget, h]
  case tensorIssue =>
    cases h : observeInput pc with
    | none => simp [advance, observe, readyTarget, h]
    | some plane => cases plane <;> simp [advance, observe, readyTarget, h]
  case wait loc parity ok acq scope =>
    cases ok <;> cases acq <;> cases scope <;>
      try (solve | simp [advance, observe, readyTarget])
    cases h : locateSlot l g loc false <;> simp [advance, observe, readyTarget, h]

/-- The abstract publication history is exactly the sequence of actual ready objects in the
thread prefix. The state retains packet forms as well as the physical slot order. -/
theorem prefixPublications {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (g index : Nat) :
    (atPrefix l X g index).published.reverse.map (readyObject l g ∘ Publication.slot) =
      ((X.tr g).take index).filterMap readyTarget := by
  induction index with
  | zero => rfl
  | succ index ih =>
    cases he : (X.tr g)[index]? with
    | none =>
      have hBound := List.getElem?_eq_none_iff.mp he
      have hSame : (X.tr g).take (index + 1) = (X.tr g).take index := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le hBound]
      simpa only [atPrefix, hSame] using ih
    | some e =>
      have hTake : (X.tr g).take (index + 1) = (X.tr g).take index ++ [e] := by
        rw [List.take_add_one, he]
        rfl
      rw [prefixStep (l := l) he, readyObservedTargets hp hX he, ih,
        hTake, List.filterMap_append]
      cases ht : readyTarget e <;> simp [ht]

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
