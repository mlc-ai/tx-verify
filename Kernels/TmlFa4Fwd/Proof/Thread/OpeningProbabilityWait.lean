-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstStore
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Lemmas.Step.DrainInOrder
import Lemmas.Step.TcLoad
import Lemmas.Flow.ContinuingEvent
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
import Lemmas.Kernel.ProgressDescent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof

/-- The delayed score-load completion is the first counted event before the opening P stores. -/
def OpeningProbabilityWait (X : Execution) (i : EvId) : Prop :=
  X.get i = some ⟨4826,.tc .waitLd⟩

variable {l : Launch}

private theorem firstDelayedWaitTemplate {g : Nat} {s : TState} (hs : s.pc = 4826)
    (hSub : s.sub = 0) (hFault : s.fault = none) (hBlock : l.block % 32 = 0) :
    out kernel Assumptions.all l g s = .ev (.tc .waitLd {s with sub := 1}) := by
  have hCode := hs.symm ▸ Flow.code_4826
  have hHook : Assumptions.all.any (·.tcStWaitLd s.pc) = true := by
    rw [hs,Assumptions.all_tcStWaitLd]
    decide
  rw [out_event hFault hCode rfl rfl,eventTmpl_tcSt_wait hHook hSub hBlock]

/-- A runnable non-load Tensor Memory collective must already occur in the maximal trace. -/
theorem probabilityCollectiveOfMaximal {m : Mem0} {X : Execution} {g j : Nat} {t v w : TState}
    {o : Option TState} {kind : TcKind} (hg : g < l.threads) (hPos : 0 < j)
    (hBound : j ≤ (X.tr g).length) (hOut : out kernel Assumptions.all l g v = .ev (.tc kind w))
    (hKind : isTcColl ⟨v.pc,.tc kind⟩ = true) (hNoLoad : ∀ a words shape, kind ≠ .ld a words shape)
    (hPast : Run kernel Assumptions.all l g {} ((X.tr g).take j) (some t))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t v)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) o)
    (hRelease : j = (X.tr g).length → ∃ Y, Maximal l kernel Assumptions.all m Y ∧
      Y.tr = X.tr ∧ Step.Released l Y g) :
    X.get (g,j) = some ⟨v.pc,.tc kind⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some w) ∧
      Run kernel Assumptions.all l g w ((X.tr g).drop (j+1)) o := by
  let event := Event.mk v.pc (.tc kind)
  have hStep : EStep kernel Assumptions.all l g v event (some w) := ⟨_,hOut,rfl,rfl⟩
  have hLt : j < (X.tr g).length := by
    by_contra! hShort
    obtain ⟨Y,hY,hTrace,hReady⟩ := hRelease (Nat.le_antisymm hBound hShort)
    have hStarted : Y.tr g ≠ [] := by
      rw [hTrace]
      exact List.ne_nil_of_length_pos (hPos.trans_le hBound)
    have hPrefix : Run kernel Assumptions.all l g {} (Y.tr g) (some t) := by
      rw [hTrace]
      simpa only [List.take_of_length_le hShort] using hPast
    exact hY.not_grows (Step.tccoll_counted_extension hY.1 hg (.inl hStarted) hReady
      hPrefix hLocal hStep hKind (hY.1.tmemPairResult.snoc_not_wr nofun)
      (hY.1.tcRead_snoc_tc hNoLoad)
      (Assumptions.wfStep.quiet hY.1 le_snoc rfl (Execution.noNewRead_snoc rfl)))
  have hNext : Next kernel Assumptions.all l g t v (.tc kind w) := ⟨hLocal,hOut⟩
  obtain ⟨_,_,he,⟨rfl,hAfter⟩,hTail⟩ := hNext.continuing_at_nonempty
    (by rintro _ ⟨_,h⟩; cases h) hRun
    (fun hNil => (Nat.not_le_of_lt hLt) (List.drop_eq_nil_iff.mp hNil))
  have hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some w) := by
    rw [List.take_add_one,show (X.tr g)[j]? = some event from he]
    exact hPast.snoc hLocal hStep
  obtain rfl := Option.some.inj hAfter
  exact ⟨he,hPrefix,hTail⟩

/-- A runnable opening probability wait is recorded even if the maximal trace stops
at the preceding named statistics arrival before its warp record is appended. -/
theorem openingProbabilityWaitOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g j : Nat} {t v : TState} {o : Option TState}
    (hg : g < l.threads) (hPos : 0 < j) (hBound : j ≤ (X.tr g).length)
    {F : List (Nat × Value)} (hAt : At v 4826 F)
    (hPast : Run kernel Assumptions.all l g {} ((X.tr g).take j) (some t))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t v)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) o)
    (hRelease : j = (X.tr g).length → ∃ Y, Maximal l kernel Assumptions.all m Y ∧
      Y.tr = X.tr ∧ Step.Released l Y g) :
    let w := {v with sub := 1}
    OpeningProbabilityWait X (g,j) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some w) ∧
      Run kernel Assumptions.all l g w ((X.tr g).drop (j+1)) o := by
  let w := {v with sub := 1}
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hOut : out kernel Assumptions.all l g v = .ev (.tc .waitLd w) :=
    firstDelayedWaitTemplate hAt.1 hAt.2.1 hAt.2.2.2.1 hBlock
  obtain ⟨he,hPrefix,hTail⟩ := probabilityCollectiveOfMaximal hg hPos hBound hOut
    rfl nofun hPast hLocal hRun hRelease
  refine ⟨?_,hPrefix,hTail⟩
  simpa only [OpeningProbabilityWait,hAt.1] using he

/-- Matching collective occurrences in the whole warp release a lane's last TMEM operation. -/
theorem probabilityCollectiveReleased {X : Execution} {g j site ordinal : Nat} {kind : TcKind}
    (he : X.get (g,j) = some ⟨site,.tc kind⟩)
    (hKind : kind = .waitLd ∨ kind = .waitSt ∨ ∃ a words shape, kind = .st a words shape)
    (hCount : ((X.tr g).take j).countP isTcColl = ordinal)
    (hPeers : ∀ peer ∈ warpLanes l g, ∃ k, X.TcK (peer,k) ordinal) (hLast : j+1 = (X.tr g).length) :
    Step.Released l X g := by
  constructor
  intro pc actual hGet _
  have hIndex : (X.tr g).length-1 = j := by omega
  rw [hIndex,he,Option.some.injEq] at hGet
  cases hGet
  rw [hIndex]
  intro need hNeed
  have hSame : KindNeeds l X (.tc kind) (g,j) = tcNeeds l X (g,j) := by
    rcases hKind with rfl | rfl | ⟨_,_,_,rfl⟩ <;> rfl
  simp only [Needs,he,hSame] at hNeed
  obtain ⟨peer,hPeer,rfl⟩ := List.mem_map.mp hNeed
  obtain ⟨k,hK⟩ := hPeers peer hPeer
  obtain ⟨event,hEvent,_⟩ := hK.1
  exact ⟨.thread (peer,k),⟨event,hEvent⟩,k,rfl,hCount.symm ▸ hK⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
