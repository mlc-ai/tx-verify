-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueGenerationZero

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Flow PTX.Proof

noncomputable section

private theorem initGroupsCover (i : Fin 34) : ∃ j : Fin 16, i ∈ initGroup j := by
  fin_cases i <;> decide

/-- A role event is causally after the matching common-CTA arrival of the elected initializer.
This identifies the actual initialization that every later operation of that object observes. -/
theorem initPublishedAfterCommon {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} (hg : g < l.threads) {e : Event} (he : X.get (g, index) = some e)
    (hPc : 173 < e.pc) (site : Fin 34) :
    let loc := initObject l (g / l.block) site
    ∃ init, X.MbInit init loc (initSite site).count ∧ InitPublished l X init (g, index) loc := by
  dsimp only
  obtain ⟨j, hj, hUser, hUserKey⟩ := generationZeroBeforeEvent hp hX hg he hPc
  have hPassed : j + 1 < (X.tr g).length := Nat.lt_of_le_of_lt (by omega)
    (List.getElem?_eq_some_iff.mp he).1
  let base := g / l.block * l.block
  have hBase : base < l.threads :=
    by
      simpa [base] using NamedBar.cta_thread_lt (g := 0) (NamedBar.cta_lt hg)
        (by rw [hp.block]; decide)
  have hZero : warpIndex l base = 0 := by simp [warpIndex, base]
  have hBCta : base / l.block = g / l.block := by
    dsimp [base]
    rw [hp.block]
    omega
  obtain ⟨leader, hMember, hLeader⟩ :=
    Step.exists_leader hX (g := base) (electMember_full l base)
  obtain ⟨a, ha, hLane⟩ := warp0LaneWitness hp hBase hZero hMember.1
  have hWarp : warpIndex l a = 0 := ha.2.symm.trans hZero
  have hCta : a / l.block = g / l.block := ha.1.2.2.symm.trans hBCta
  have hA : a < l.threads := ha.1.2.1
  have hReleased := generationZeroReleased hX hUser hPassed
  obtain ⟨before, hBar, hSource⟩ :=
    generationZeroMember hp hX hA (by simpa only [hCta] using hReleased)
  obtain ⟨n, _, _, hInitBar, _, hHistory⟩ :=
    warp0InitializerPrefix hp hX hA hWarp hBar (by decide)
  have hSame := commonStartupUnique hX hA hInitBar hBar
  obtain ⟨round, hRound⟩ := initGroupsCover site
  obtain ⟨slot, hSlot⟩ := List.mem_iff_getElem?.mp hRound
  obtain ⟨start, inst, tag, _, hElect, hInit⟩ := hHistory round round.isLt
  have hTag := hLeader _ _ inst tag ha hElect
  obtain ⟨hInitBefore, hInitGet⟩ := hInit (hLane.trans hTag.symm) slot site hSlot
  refine ⟨(a, start + 1 + slot), ⟨(initSite site).pc, ?_⟩, .inl ?_⟩
  · simpa only [initEvent, initObject, hCta] using hInitGet
  · exact Relation.TransGen.single (.inr (.inl
      ⟨⟨hA, hg, hCta⟩, 0, before, j, hSource.arrival, hUserKey, by omega, hj,
        (List.getElem?_eq_some_iff.mp he).1⟩))

end
end PTX.Kernels.TmlFa4Fwd.Prologue
