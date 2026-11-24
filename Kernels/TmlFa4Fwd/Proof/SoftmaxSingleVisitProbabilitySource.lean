-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitProbabilityCompetition
public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitProbabilityQk
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.Safety.TmemCompletion
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCommitTargets

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.TcMma PTX.Proof Prologue Epilogue

private theorem copyCannotWrite {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {cell : Cell}
    (h : CpCell X i cell ∨ ShiftCell X i cell) : False := by
  rcases h with ⟨copy,_,_,_,⟨pc,he⟩,_⟩ | ⟨shift,⟨pc,he⟩,_⟩
  · obtain ⟨_,_,_,_,_,hIssue⟩ := Thread.tcAsyncIsMma hX (.inr (.inl ⟨copy,pc,he⟩))
    rw [he] at hIssue
    cases hIssue
  · obtain ⟨_,_,_,_,_,hIssue⟩ :=
      Thread.tcAsyncIsMma hX (.inr (.inr ⟨shift,pc,he⟩))
    rw [he] at hIssue
    cases hIssue

/-- The single-visit PV operand takes its packed word from the unique completed
probability store. The QK write precedes that store, and PV completes within
the lifetime of the allocation. -/
theorem singleVisitProbabilityReadSource {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFrame : OutputFootprint p X)
    {warp : Fin 8} {g j batch head row cap past : Nat}
    (hg : g < l.threads) (hw : warp.val = warpIndex l g)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    (hCap : 0 < cap) (hBound : cap < 2^31) (hPast : past+256 < 2^31)
    (hRound : FirstRoundProgress p l X warp g j batch head row 1 cap past)
    {producer commit wait : Nat}
    (hPhase : FirstQkPhase l X (stageOf warp) producer g commit wait)
    {output : EvId} {s : TcCommit.Spec} (hOutput : Thread.SecondOutputCommit X output s)
    (hOutputCta : g/l.block = output.1/l.block)
    (q : Fin 4) {word : Nat} (hWord : word < 16) {vals : List Value}
    (hLen : vals.length = 16)
    (he : X.get (g,j+1+probabilityTraceIndex q) = some ⟨probabilityPc .first q,
      .tc (.st (probabilityAddress l g (stageOf warp) q) vals .s32x32b)⟩)
    {i : EvId} {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hPv : X.MmaIssue i d op acc mask)
    (hBefore : StoreDoneBefore l X (g,j+1+probabilityTraceIndex q) i)
    (hAccess : X.MmaACell i
      (tcDataCell l g .s32x32b (probabilityAddress l g (stageOf warp) q) word)) :
    ReadSource l X .a (g,j+1+probabilityTraceIndex q) i
      (tcDataCell l g .s32x32b (probabilityAddress l g (stageOf warp) q) word) := by
  let source : EvId := (g,j+1+probabilityTraceIndex q)
  have hSeparate : source ≠ i := by
    intro hSame
    obtain ⟨pc,hMma⟩ := hPv
    rw [← hSame,he] at hMma
    cases hMma
  have hCta := hPhase.sameCta.2.2
  have hWritten : StoreCell l X source
      (tcDataCell l g .s32x32b (probabilityAddress l g (stageOf warp) q) word) :=
    ⟨_,_,_,word,⟨_,he⟩,hLen.symm ▸ hWord,rfl⟩
  have hOwned := (Safety.mmaAccessLifetime hp hX (hFrame.metadataProtected hp).1
    (.inr (.inr hAccess))).2
  refine ⟨hSeparate,.inr (.inl hWritten),.inr (.inl hBefore),?_,?_⟩
  · intro other hWriter
    rcases hWriter with hMma | hStore | hCopy
    · refine .inr (.inl (singleVisitMmaWriteBeforeProbabilityStore hp hX hDone hFrame hb
        (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (hCta.symm ▸ hTrip)
        hPhase hOutput (hCta.trans hOutputCta) q hWord he hMma))
    · exact .inl (singleVisitProbabilityStoreUnique hp hX hFrame hg hw hb hLo hHi hTrip
        hCap hBound hPast hRound q hWord hStore)
    · exact (copyCannotWrite hX hCopy).elim
  · intro cta r hMember hCover release hRelease
    exact .inl (hOwned cta r hMember hCover release hRelease)

end PTX.Kernels.TmlFa4Fwd.Softmax
