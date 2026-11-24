-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityCredits
import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Prologue

/-- A consumer credit comes from softmax or, for the joint packet, from correction. -/
theorem probabilityCreditRole {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {e : EvId} {cta : Nat} (stage packet : Fin 2)
    (hIssue : ProbabilityCredit l X e cta stage packet) :
    e.1 / l.block = cta ∧
      ((warpIndex l e.1 < 8 ∧ warpIndex l e.1 / 4 = stage.val) ∨
       (packet.val = 0 ∧ 8 ≤ warpIndex l e.1 ∧ warpIndex l e.1 < 12)) := by
  obtain ⟨raw, hr⟩ := hIssue
  let off := 96 + 8 * stage.val + 16 * packet.val
  have hoff : off ∈ [96, 104, 112, 120] := by fin_cases stage <;> fin_cases packet <;> decide
  obtain ⟨_, _, hOwner⟩ := actualArriveOffsetIn hp hX hr
  have hCta : e.1 / l.block = cta := (congrArg Loc.cta hOwner).symm
  refine ⟨hCta, ?_⟩
  rcases actualProbabilityArrivalSite hp hX hr hoff rfl with ⟨which, rfl⟩ | hCorr
  · obtain ⟨_, _, _, _, hWarp, hAddr⟩ := Softmax.probabilityArriveFacts hp hX which hr
    have hAddress : l.sharedBase + off = l.sharedBase +
        ((Softmax.probabilityArrivalSite which).offset + 8 * (warpIndex l e.1 / 4)) :=
      congrArg Loc.addr hAddr
    have hOff : (Softmax.probabilityArrivalSite which).offset = 96 ∨
        (Softmax.probabilityArrivalSite which).offset = 112 := by fin_cases which <;> decide
    have hSt := stage.isLt
    have hPk := packet.isLt
    dsimp [off] at hAddress
    exact .inl ⟨hWarp, by omega⟩
  · obtain ⟨_, _, _, _, hLo, hHi⟩ := Correction.correctionProbabilityCredit hp hX hr hCorr
    have hAddr := Correction.correctionArriveAddressExact hp hX hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hCorr ⊢
      tauto)
    have hAddress : l.sharedBase + off = l.sharedBase + Correction.correctionArriveOffset raw :=
      congrArg Loc.addr hAddr
    have hOffsets : ∀ j ∈ [7752, 7754, 8223, 8442, 8759, 9055],
        Correction.correctionArriveOffset j = 96 ∨ Correction.correctionArriveOffset j = 104 :=
      by decide
    have hCs := hOffsets raw hCorr
    have hSt := stage.isLt
    have hPk := packet.isLt
    dsimp [off] at hAddress
    exact .inr ⟨by omega, hLo, hHi⟩

/-- The number of prior credits to this physical packet on the issuing lane. -/
def probabilityOrdinal (l : Launch) (X : Execution) (cta : Nat)
    (stage packet : Fin 2) (e : EvId) : Nat :=
  arrivals (probabilityObject l cta stage packet) ((X.tr e.1).take e.2)

/-- A lane cannot issue two credits of the same local ordinal to a packet. -/
theorem probabilityOrdinalInjective {l : Launch} {X : Execution}
    {a b : EvId} {cta : Nat} {stage packet : Fin 2}
    (ha : ProbabilityCredit l X a cta stage packet) (hb : ProbabilityCredit l X b cta stage packet)
    (hLane : a.1 = b.1)
    (hCount : probabilityOrdinal l X cta stage packet a =
      probabilityOrdinal l X cta stage packet b) : a = b := by
  obtain ⟨g,i⟩ := a
  obtain ⟨g',j⟩ := b
  change g = g' at hLane
  subst g'
  obtain ⟨_, ha⟩ := ha
  obtain ⟨_, hb⟩ := hb
  have hI := nthEv_unique ha (p := arrivesOn (probabilityObject l cta stage packet))
    (by simp [sourceArrive]) hb (by simp [sourceArrive]) hCount
  exact congrArg (fun k => (g,k)) hI

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
