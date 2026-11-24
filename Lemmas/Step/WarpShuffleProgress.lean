-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.WarpShfl
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Kernel.ProgressDescent

@[expose] public section

namespace PTX.Step
open PTX PTX.Flow

noncomputable section

/-- When every lane has a released local route to its next matching full-warp shuffle,
a maximal prefix already contains that shuffle in each lane. -/
theorem shfl_occurs_of_maximal {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hMax : Maximal L K A mem0 X) (hb : L.block % 32 = 0)
    {g pc ordinal : Nat} (hg : g < L.threads) {mode : ShflMode}
    (index : Nat → Nat) (a : Nat → Value) (b c : Nat → Nat)
    (hStarted : ∀ h, SameWarp L g h → X.tr h ≠ [] ∨ Launched L X h)
    (hCursor : ∀ h, SameWarp L g h →
      ∃ (t u : TState) (o : Option TState) (dst : Value → Bool → TState),
        index h ≤ (X.tr h).length ∧ ((X.tr h).take (index h)).countP Execution.isShfl = ordinal ∧
        (index h = (X.tr h).length → Released L X h) ∧ u.pc = pc ∧
        Run K A L h {} ((X.tr h).take (index h)) (some t) ∧
        Run K A L h t ((X.tr h).drop (index h)) o ∧
        Next K A L h t u (.shfl mode (a h) (b h) (c h) dst))
    (hasm : ∀ ev, (∀ h, (ev h).kind.readsMem = false) →
      ∀ a ∈ A, a.wf L mem0 (X.appendLanes (warpThreads L g) ev)) :
    ∃ recv ok, X.get (g, index g) = some ⟨pc, .shfl mode (a g) (b g) (c g) recv ok⟩ ∧
      X.ShflK (g, index g) ordinal := by
  have hWarp (h : Nat) (hw : SameWarp L g h) (hLen : index h < (X.tr h).length) :
      ∃ recv ok,
        X.get (h,index h) = some ⟨pc, .shfl mode (a h) (b h) (c h) recv ok⟩ ∧
        X.ShflK (h,index h) ordinal := by
    obtain ⟨t, u, o, dst, _, hCount, _, hPc, _, hTail, hn⟩ := hCursor h hw
    rw [List.drop_eq_getElem_cons hLen] at hTail
    obtain ⟨_, ⟨recv, ok, he, _⟩, _⟩ := hn.continuing_event
      (by rintro ⟨_, _, _, h⟩; cases h) hTail
    have hGet : X.get (h,index h) = some ⟨pc, .shfl mode (a h) (b h) (c h) recv ok⟩ := by
      change (X.tr h)[index h]? = _
      rw [List.getElem?_eq_getElem hLen, he, hPc]
    exact ⟨recv, ok, hGet, ⟨⟨_, _, _, _, _, _, _, hGet⟩, hCount⟩⟩
  have hgWarp : SameWarp L g g := ⟨⟨hg, hg, rfl⟩, rfl⟩
  obtain ⟨t, u, o, dst, hBound, hCount, hRel, hPc, hPrefix, _, _⟩ := hCursor g hgWarp
  apply hWarp g hgWarp
  by_contra! hLow
  have hgLen : index g = (X.tr g).length := Nat.le_antisymm hBound hLow
  have hFull : Run K A L g {} (X.tr g) (some t) := by simpa [hgLen] using hPrefix
  have hTotal : (X.tr g).countP Execution.isShfl = ordinal := by simpa [hgLen] using hCount
  have hLength (h : Nat) (hs : SameWarp L g h) : index h = (X.tr h).length := by
    obtain ⟨_, _, _, _, hBound, _, _, _, _, _, _⟩ := hCursor h hs
    apply Nat.le_antisymm hBound
    by_contra! hLater
    obtain ⟨_, _, hh, hOrd⟩ := hWarp h hs hLater
    rcases shfl_lane_of_ready hMax.1 hh hOrd (sameWarp_symm hs) with ⟨j, hJ⟩ | ⟨j, site, he, _⟩
    · exact (Nat.not_lt_of_ge hTotal.le) (Step.ShflK.lt_count hJ)
    · exact hFull.no_exit he
  apply hMax.not_grows
  refine shfl_counted_extension hMax.1 hb (pc := pc) (m := mode) a b c hg hStarted ?_ ?_ hasm
  · intro h hSame
    obtain ⟨_, _, _, _, _, _, hReady, _, _, _, _⟩ := hCursor h hSame
    exact hReady (hLength h hSame)
  · intro h hSame recv ok
    obtain ⟨t, u, o, dst, _, _, _, hAt, hRun, _, hn⟩ := hCursor h hSame
    have hPrefix : Run K A L h {} (X.tr h) (some t) := by
      simpa [hLength h hSame] using hRun
    exact ⟨t, u, _, hPrefix, hn.steps, _, hn.stop, recv, ok, by rw [hAt], rfl⟩

end
end PTX.Step
