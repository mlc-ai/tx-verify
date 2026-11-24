-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaPoll
public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Protocol.PollIndex

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof
open Correction (OpeningTripCursor)

/-- A guarded poll cursor consumes its requested generation. The phase
argument is needed only when the actual suffix contains failed polls alone.
If the success is already recorded, its exact ordinal follows from the prefix
count and the failure-only portion of the suffix. -/
theorem pollOrdinalOccursOfMaximal {l : Launch} {m : Mem0} {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (site : Fin 14) {addr phase gen : Nat} (hAddr : addr < 2^32) (hAlign : addr%8 = 0)
    (hPhase : phase < 2) {F : List (Nat × Value)}
    (hFresh : ∀ pair ∈ F, pair.1 ≠ (waitSite site).result)
    (hBase : ((waitSite site).base,b32 addr) ∈ F)
    (hPar : ((waitSite site).phase,b32 phase) ∈ F)
    (cur : OpeningTripCursor l X g (waitSite site).pc F)
    (hOrdinal : okPolls ⟨.shared,g/l.block,addr⟩ ((X.tr g).take cur.pos) = gen)
    (hReady : okPolls ⟨.shared,g/l.block,addr⟩ (X.tr g) = gen →
      let log := X.objects ⟨.shared,g/l.block,addr⟩
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase%2 ≠ phase%2) :
    ∃ j, cur.pos ≤ j ∧
      X.get (g,j) = some ⟨(waitSite site).pc,
        .wait ⟨.shared,g/l.block,addr⟩ phase true true .cta⟩ ∧
      okPolls ⟨.shared,g/l.block,addr⟩ ((X.tr g).take j) = gen := by
  let loc : Loc := ⟨.shared,g/l.block,addr⟩
  let ev (ok : Bool) := Event.mk (waitSite site).pc (.wait loc phase ok true .cta)
  have hMark : okPoll loc (ev false) = false := by simp [ev,okPoll,sourceWaitSuccess]
  have hNo (n : Nat) : okPolls loc (List.replicate n (ev false)) = 0 := by
    simp [okPolls,List.countP_replicate,hMark]
  have hCases :
      (∃ n, (X.tr g).drop cur.pos = List.replicate n (ev false)) ∨
      ∃ n tail, (X.tr g).drop cur.pos = List.replicate n (ev false) ++ ev true :: tail := by
    by_cases hNil : (X.tr g).drop cur.pos = []
    · exact .inl ⟨0,hNil⟩
    obtain ⟨_,hWalk⟩ := walkFromRun (cur.remaining.after_local_nonempty cur.localSteps hNil)
    rcases waitWalk site hAddr hAlign hPhase hFresh hBase hPar cur.checkpoint hWalk with
      hFail | ⟨n,tail,hTrace,_⟩
    · exact .inl hFail
    · exact .inr ⟨n,tail,hTrace⟩
  rcases hCases with ⟨n,hFail⟩ | ⟨n,tail,hTrace⟩
  · have hCount : okPolls loc (X.tr g) = gen := by
      conv_lhs => rw [← List.take_append_drop cur.pos (X.tr g)]
      simp only [okPolls,List.countP_append,hFail]
      have hPrior : ((X.tr g).take cur.pos).countP (okPoll loc) = gen := hOrdinal
      have hFailure : (List.replicate n (ev false)).countP (okPoll loc) = 0 := hNo n
      rw [hPrior,hFailure,Nat.add_zero]
    obtain ⟨ready,_,_,he,_,_,_,_,_⟩ := waitOfMaximalWithTrace hMax hg site hAddr hAlign
      hPhase hFresh hBase hPar (fun _ _ _ => hReady hCount) cur.positive cur.bounded
      cur.released cur.checkpoint cur.recorded cur.remaining cur.localSteps
    have hBefore := MbarRing.Poll.okPoll_get he
    have hAfter := MbarRing.Poll.okPolls_mono loc (X.tr g)
      (show cur.pos+ready+1 ≤ (X.tr g).length from len_of_get he)
    have hBeforeCount := MbarRing.Poll.okPolls_mono loc (X.tr g)
      (show cur.pos ≤ cur.pos+ready by omega)
    change okPolls loc ((X.tr g).take (cur.pos+ready+1)) =
      okPolls loc ((X.tr g).take (cur.pos+ready))+1 at hBefore
    rw [List.take_length,hCount,hBefore] at hAfter
    rw [hOrdinal] at hBeforeCount
    omega
  · have he : ((X.tr g).drop cur.pos)[n]? = some (ev true) := by
      rw [hTrace,List.getElem?_append_right (by simp)]
      simp
    rw [List.getElem?_drop] at he
    refine ⟨cur.pos+n,by omega,he,?_⟩
    have hWindow : ((X.tr g).drop cur.pos).take n = List.replicate n (ev false) := by
      rw [hTrace]
      have hTake : (List.replicate n (ev false) ++ ev true :: tail).take
          (List.replicate n (ev false)).length = List.replicate n (ev false) :=
        List.take_append_length
      simpa only [List.length_replicate] using hTake
    rw [List.take_add,hWindow,okPolls,List.countP_append]
    change okPolls loc ((X.tr g).take cur.pos) + okPolls loc _ = gen
    rw [hOrdinal,hNo,Nat.add_zero]

end PTX.Kernels.TmlFa4Fwd.Mma
