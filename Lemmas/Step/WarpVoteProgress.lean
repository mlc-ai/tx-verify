-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.WarpVote
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Kernel.ProgressDescent

@[expose] public section

namespace PTX.Step
open PTX PTX.Flow

noncomputable section

/-- If every lane reaches the same ballot boundary and is released, a maximal prefix
contains the ballot at that boundary in each lane. The mask must include the whole warp. -/
theorem ballot_occurs_of_maximal {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hMax : Maximal L K A mem0 X) (hb : L.block % 32 = 0)
    {g pc ordinal mask : Nat} (hg : g < L.threads)
    (index : Nat → Nat) (a : Nat → Bool)
    (hMember : ∀ h, SameWarp L g h → mask.testBit (laneOf L h) = true)
    (hStarted : ∀ h, SameWarp L g h → X.tr h ≠ [] ∨ Launched L X h)
    (hCursor : ∀ h, SameWarp L g h →
      ∃ (t u : TState) (o : Option TState) (dst : BitVec 32 → TState),
        index h ≤ (X.tr h).length ∧
        ((X.tr h).take (index h)).countP (fun e => (voteClass e.kind).any (·.mask == mask)) =
          ordinal ∧
        (index h = (X.tr h).length → Released L X h) ∧ u.pc = pc ∧
        Run K A L h {} ((X.tr h).take (index h)) (some t) ∧
        Run K A L h t ((X.tr h).drop (index h)) o ∧
        Next K A L h t u (.vote mask (a h) dst))
    (hasm : ∀ ev, (∀ h, (ev h).kind.readsMem = false) →
      ∀ a ∈ A, a.wf L mem0 (X.appendLanes (warpThreads L g) ev)) :
    ∃ word, X.get (g,index g) = some ⟨pc,.vote mask (a g) word⟩ ∧
      X.MaskK voteClass (g,index g) mask ordinal := by
  have hWarp (h : Nat) (hw : SameWarp L g h) (hLen : index h < (X.tr h).length) :
      ∃ word, X.get (h,index h) = some ⟨pc,.vote mask (a h) word⟩ ∧
        X.MaskK voteClass (h,index h) mask ordinal := by
    obtain ⟨t,u,o,dst,_,hCount,_,hPc,_,hTail,hn⟩ := hCursor h hw
    rw [List.drop_eq_getElem_cons hLen] at hTail
    obtain ⟨_,⟨word,he,_⟩,_⟩ := hn.continuing_event (by rintro ⟨_,_,h⟩; cases h) hTail
    have hGet : X.get (h,index h) = some ⟨pc,.vote mask (a h) word⟩ := by
      change (X.tr h)[index h]? = _
      rw [List.getElem?_eq_getElem hLen,he,hPc]
    exact ⟨word,hGet,⟨⟨_,_,hGet,rfl,rfl⟩,hCount⟩⟩
  have hgWarp : SameWarp L g g := ⟨⟨hg,hg,rfl⟩,rfl⟩
  obtain ⟨t,u,o,dst,hBound,hCount,hRel,hPc,hPrefix,_,_⟩ := hCursor g hgWarp
  apply hWarp g hgWarp
  by_contra! hLow
  have hLen := Nat.le_antisymm hBound hLow
  have hFull : Run K A L g {} (X.tr g) (some t) := by simpa [hLen] using hPrefix
  have hTotal : maskCount voteClass X g mask = ordinal := by
    simpa [hLen,maskCount] using hCount
  have hAtEnd (h : Nat) (hs : SameWarp L g h) : index h = (X.tr h).length := by
    obtain ⟨_,_,_,_,hBound,_,_,_,_,_,_⟩ := hCursor h hs
    apply Nat.le_antisymm hBound
    by_contra! hLater
    obtain ⟨_,_,hOrd⟩ := hWarp h hs hLater
    rcases vote_lane_of_ready hMax.1 hOrd (sameWarp_symm hs) (hMember g hgWarp) with
      ⟨j,hJ⟩ | ⟨j,site,he⟩
    · exact (Nat.not_lt_of_ge hTotal.le) (MaskK.lt_count hJ)
    · exact hFull.no_exit he
  apply hMax.not_grows
  refine vote_counted_extension hMax.1 hb (pc := pc) a hg hMember hStarted ?_ ?_ hasm
  · intro h hs
    obtain ⟨_,_,_,_,_,_,hReady,_,_,_,_⟩ := hCursor h hs
    exact hReady (hAtEnd h hs)
  · intro h hs word
    obtain ⟨t,u,o,dst,_,_,_,hAt,hRun,_,hn⟩ := hCursor h hs
    have hPrefix : Run K A L h {} (X.tr h) (some t) := by
      simpa [hAtEnd h hs] using hRun
    exact ⟨t,u,_,hPrefix,hn.steps,_,hn.stop,word,by rw [hAt],rfl⟩

end
end PTX.Step
