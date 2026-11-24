-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.CorrectionBarrierConflicts
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxRendezvous

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX Thread

/-- A same-warp disagreement between the types of two observed softmax rendezvous. -/
def SoftmaxBarrierMismatch (l : Launch) (X : Execution) : Prop :=
  ∃ (i j : EvId) (kind kind' : SoftmaxRendezvous),
    SameWarp l i.1 j.1 ∧ Prologue.warpIndex l i.1 < 8 ∧
    kind.Observed l X i ∧ kind'.Observed l X j ∧
    barrierOrdinal X i = barrierOrdinal X j ∧ kind ≠ kind' ∧
    kind ≠ .initialAllocation ∧ kind' ≠ .initialAllocation

theorem softmaxBarrierMismatchIsAlignedWork {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hBad : SoftmaxBarrierMismatch l X) : AlignedWorkBarrierMismatch l X 8 := by
  obtain ⟨i, j, kind, kind', hWarp, hSoft, hi, hj, hOrd, hNe, hWork, hWork'⟩ := hBad
  exact SoftmaxRendezvous.alignedMismatch hp hX hWarp hSoft hi hj hOrd hNe hWork hWork'

private theorem classifyBarrierDisagreement {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i j : EvId} {id id' : Nat} {count count' : Option Nat} {mode mode' : BarMode}
    (hw : SameWarp l i.1 j.1) (he : BarrierArrival X i id count mode)
    (hf : BarrierArrival X j id' count' mode')
    (hOrdinal : barrierOrdinal X i = barrierOrdinal X j)
    (hDiff : id ≠ id' ∨ mode ≠ mode') : SoftmaxBarrierMismatch l X := by
  obtain ⟨hn, hn'⟩ := he.nonstartupOfDisagreement hp hX hf hOrdinal hDiff
  by_cases hWarp : 12 ≤ Prologue.warpIndex l i.1
  · have hWarp' : 12 ≤ Prologue.warpIndex l j.1 := by
      unfold Prologue.warpIndex at hWarp ⊢
      rwa [← hw.2]
    obtain ⟨_, hId, _, hMode⟩ := he.allocationForMmaOrDrain hp hX hn hWarp
    obtain ⟨_, hId', _, hMode'⟩ := hf.allocationForMmaOrDrain hp hX hn' hWarp'
    exact (hDiff.elim (fun h => h (hId.trans hId'.symm))
      (fun h => h (hMode.trans hMode'.symm))).elim
  · by_cases hSoftmax : Prologue.warpIndex l i.1 < 8
    · have hSameWarp : Prologue.warpIndex l i.1 = Prologue.warpIndex l j.1 := hw.2
      obtain ⟨kind, hId, hCount, hMode, hK⟩ := he.softmaxRendezvous hp hX hSoftmax hn
      obtain ⟨kind', hId', hCount', hMode', hK'⟩ :=
        hf.softmaxRendezvous hp hX (hSameWarp ▸ hSoftmax) hn'
      have hNe : kind ≠ kind' := by
        rintro rfl
        have hSame : kind.id l i.1 = kind.id l j.1 := by
          cases kind <;> simp [SoftmaxRendezvous.id, hSameWarp]
        exact hDiff.elim (fun h => h (hId.trans (hSame.trans hId'.symm)))
          (fun h => h (hMode.trans hMode'.symm))
      refine ⟨i, j, kind, kind', hw, hSoftmax, ?_, ?_, hOrdinal, ?_, ?_, ?_⟩
      · simpa only [SoftmaxRendezvous.Observed, ← hId, ← hCount, ← hMode] using he
      · simpa only [SoftmaxRendezvous.Observed, ← hId', ← hCount', ← hMode'] using hf
      · exact hNe
      · rintro rfl
        cases kind' <;> simp [SoftmaxRendezvous.validOrdinal, hOrdinal] at hK hK' hNe <;> omega
      · rintro rfl
        cases kind <;> simp [SoftmaxRendezvous.validOrdinal, hOrdinal] at hK hK' hNe <;> omega
    · have hCorrection : 8 ≤ Prologue.warpIndex l i.1 ∧ Prologue.warpIndex l i.1 < 12 := by
        omega
      obtain ⟨hId, hMode⟩ := correctionRendezvousAgree hp hX hw hCorrection
        he hf hn hn' hOrdinal
      exact (hDiff.elim (fun h => h hId) (fun h => h hMode)).elim

/-- Startup, allocation, and correction are uniform. A remaining mismatch must
involve the softmax role's rendezvous. -/
theorem classifyBarMismatch {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hBad : BarMismatch l X) : SoftmaxBarrierMismatch l X := by
  have disagree {id id' : Nat} {i j : EvId} {count count' : Option Nat} {mode mode' : BarMode}
      (he : BarrierArrival X i id count mode) (hf : BarrierArrival X j id' count' mode')
      (hDiff : id ≠ id' ∨ count ≠ count') : id ≠ id' := by
    intro h
    subst id'
    exact (hDiff.resolve_left (not_not_intro rfl)) (barrierCountAgrees hp hX he hf)
  rcases hBad with ⟨g, h, i, j, id, id', cnt, cnt', _, _, hw, he, hf, hK, hDiff⟩ |
    ⟨g, h, i, j, id, id', cnt, cnt', mode', _, _, hw, he, hf, hK, hDiff⟩
  · have hE : BarrierArrival X (g,i) id cnt .sync := ⟨_, he, rfl⟩
    have hF : BarrierArrival X (h,j) id' cnt' .sync := ⟨_, hf, rfl⟩
    exact classifyBarrierDisagreement hp hX hw hE hF hK (.inl (disagree hE hF hDiff))
  · have hE : BarrierArrival X (g,i) id cnt .arrive := ⟨_, he, rfl⟩
    have hF : BarrierArrival X (h,j) id' cnt' mode' := ⟨_, hf, rfl⟩
    apply classifyBarrierDisagreement hp hX hw hE hF hK
    rcases hDiff with hId | hCount | hMode
    · exact .inl hId
    · exact .inl (disagree hE hF (.inr hCount))
    · exact .inr (Ne.symm hMode)

end PTX.Kernels.TmlFa4Fwd.Safety
