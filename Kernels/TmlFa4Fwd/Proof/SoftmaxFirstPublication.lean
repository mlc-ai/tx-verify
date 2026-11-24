-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstStore
public import Kernels.TmlFa4Fwd.Proof.SoftmaxPublishTail

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The exact event for a quarter's first-round packed-probability write. -/
def firstStoreEvent (l : Launch) (g : Nat) (stage : Fin 2) (quarter : Fin 4)
    (values : Nat → ℝ) : Event :=
  ⟨probabilityPc .first quarter, .tc (.st (probabilityAddress l g stage quarter)
    ((List.range 16).map (probabilityWord values)) .s32x32b)⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- Three first-round P stores precede the first P publication; the delayed load wait occurs
only at the first of those stores. -/
theorem firstThreeStoresTrace (hp : Pre p l m) (stage : Fin 2) {g j : Nat} {t : TState}
    (values : Fin 4 → Nat → ℝ) (ht : At t 4818 [])
    (hPacked : ∀ q : Fin 4, ∀ word < 8, t.regs (firstPackedReg q + word) =
      some (probabilityDoubleWord (values q) word))
    (hAddr : ∀ q : Fin 4, t.regs (probabilityReg .first q) =
      some (b32 (probabilityAddress l g stage q)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ u, X.get (g, j) = some ⟨4826, .tc .waitLd⟩ ∧
      X.get (g, j + 1) = some (firstStoreEvent l g stage 0 (values 0)) ∧
      X.get (g, j + 2) = some (firstStoreEvent l g stage 1 (values 1)) ∧
      X.get (g, j + 3) = some (firstStoreEvent l g stage 2 (values 2)) ∧
      At u 4845 [] ∧ (∀ r, r < 3879 ∨ 3927 ≤ r → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + 4)) none := by
  obtain ⟨u, hWait, h0, hU, hFrame, hTail⟩ :=
    firstPackedStoreTrace hp stage (values 0) ht (hPacked 0) (hAddr 0) hRun
  have hPackedAfter (q : Fin 4) (word : Nat) (hWord : word < 8) :
      u.regs (firstPackedReg q + word) = some (probabilityDoubleWord (values q) word) := by
    rw [hFrame _ (.inr (by unfold firstPackedReg; omega))]
    exact hPacked q word hWord
  have hAddr1 := (hFrame (probabilityReg .first 1) (.inl (by decide))).trans (hAddr 1)
  obtain ⟨v, _, h1, hV, hVFrame, hVtail⟩ :=
    packedQuarterStoreTrace hp stage 1 (values 1) hU (hPackedAfter 1) hAddr1 hTail
  have hPackedV (word : Nat) (hWord : word < 8) :
      v.regs (firstPackedReg 2 + word) = some (probabilityDoubleWord (values 2) word) := by
    have hB : firstUnpackBase 1 = 3895 := rfl
    have hP : firstPackedReg 2 = 8170 := rfl
    rw [hVFrame _ (.inr (by rw [hB, hP]; omega))]
    exact hPackedAfter 2 word hWord
  have hAddr2 := (hVFrame (probabilityReg .first 2) (.inl (by decide))).trans
    ((hFrame _ (.inl (by decide))).trans (hAddr 2))
  obtain ⟨w, _, h2, hW, hWFrame, hWtail⟩ :=
    packedQuarterStoreTrace hp stage 2 (values 2) hV hPackedV hAddr2 hVtail
  refine ⟨w, hWait, h0, h1, h2, hW, ?_, hWtail⟩
  intro r hR
  have b1 : firstUnpackBase 1 = 3895 := rfl
  have b2 : firstUnpackBase 2 = 3911 := rfl
  rw [hWFrame r (by rw [b2]; omega), hVFrame r (by rw [b1]; omega), hFrame r (by omega)]

/-- From the first store wait through the first P release, only the arrival count and the
unused barrier-state destination can change. This preserves the tail pack and all ABI facts. -/
theorem firstPHandshakeTrace (hp : Pre p l m) (stage : Fin 2) {g j : Nat} {t : TState}
    (ht : At t 4845 []) (hBase : t.regs 3217 = some (b32 (l.sharedBase + 8 * stage.val)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ u, X.get (g, j) = some ⟨4845, .tc .waitSt⟩ ∧
      X.get (g, j + 1) = some ⟨4847, .arrive (signalLoc l g stage 1) 0 1 true .cta⟩ ∧
      At u 4848 [] ∧ (∀ r, r ≠ 3927 → r ≠ 8186 → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + 2)) none := by
  obtain ⟨hWait, hTail⟩ := probabilityWaitTrace hp .first false ht.1 ht.2.2.2.1 hRun
  let v := next (setReg (next t) 3927 (b32 1))
  have hLocal : run kernel Assumptions.all l g 1 (next t) = some v := by
    apply run_local Flow.code_4846 rfl ht.next
    rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil (by
      rw [ht.next.1]
      decide) rfl]
    rfl
  have hAt : At v 4847 [(3927, b32 1)] := ht.next.set (by simp)
  have hAddr : v.regs 3217 = some (b32 (l.sharedBase + 8 * stage.val)) := by
    simpa [v, next, setReg] using hBase
  obtain ⟨hSignal, hAfter⟩ := signalTrace hp stage 1 hAt.1 hAt.2.2.2.1
    hAddr hAt.2.2.2.2.1 (hTail.after_local (run_rtg hLocal))
  let w := next (mbarStateDest v (some 8186))
  have hW : At w 4848 [] :=
    ⟨congrArg (· + 1) hAt.1, hAt.2.1, hAt.2.2.1, hAt.2.2.2.1, trivial⟩
  refine ⟨w, hWait, hSignal, hW, ?_, hAfter⟩
  intro r hR0 hR1
  simp [w, v, mbarStateDest, setReg, next, Function.update_of_ne hR0, Function.update_of_ne hR1]

/-- The fourth P pack is stored only after the main P slot has been released. -/
theorem firstLastStoreTrace (hp : Pre p l m) (stage : Fin 2) {g j : Nat} {t : TState}
    (values : Nat → ℝ) (ht : At t 4845 [])
    (hSignalBase : t.regs 3217 = some (b32 (l.sharedBase + 8 * stage.val)))
    (hPacked : ∀ word < 8, t.regs (firstPackedReg 3 + word) =
      some (probabilityDoubleWord values word))
    (hAddr : t.regs (probabilityReg .first 3) = some (b32 (probabilityAddress l g stage 3)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ u, X.get (g, j) = some ⟨4845, .tc .waitSt⟩ ∧
      X.get (g, j + 1) = some ⟨4847, .arrive (signalLoc l g stage 1) 0 1 true .cta⟩ ∧
      X.get (g, j + 2) = some (firstStoreEvent l g stage 3 values) ∧
      At u 4857 [] ∧
      (∀ r, r ≠ 3927 → r ≠ 8186 → r < 3928 ∨ 3944 ≤ r → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + 3)) none := by
  obtain ⟨u, hWait, hSignal, hU, hFrame, hTail⟩ := firstPHandshakeTrace hp stage ht hSignalBase hRun
  have hWords (word : Nat) (hWord : word < 8) :
      u.regs (firstPackedReg 3 + word) = some (probabilityDoubleWord values word) := by
    have h0 : firstPackedReg 3 = 8178 := rfl
    rw [hFrame _ (by omega) (by omega)]
    exact hPacked word hWord
  have hAddrU := (hFrame (probabilityReg .first 3) (by decide) (by decide)).trans hAddr
  obtain ⟨v, _, hStore, hV, hVFrame, hRest⟩ :=
    packedQuarterStoreTrace hp stage 3 values hU hWords hAddrU hTail
  exact ⟨v, hWait, hSignal, hStore, hV,
    fun r hR0 hR1 hR2 => (hVFrame r hR2).trans (hFrame r hR0 hR1), hRest⟩

/-- Three first-round P stores precede the first P publication; the delayed load wait occurs
only at the first of those stores. -/
theorem firstThreeStoresInPrefix (hp : Pre p l m) (stage : Fin 2) {g j : Nat} {t : TState}
    {ending : Option TState} (values : Fin 4 → Nat → ℝ) (ht : At t 4818 [])
    (hPacked : ∀ q : Fin 4, ∀ word < 8, t.regs (firstPackedReg q + word) =
      some (probabilityDoubleWord (values q) word))
    (hAddr : ∀ q : Fin 4, t.regs (probabilityReg .first q) =
      some (b32 (probabilityAddress l g stage q)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hBound : j+3 < (X.tr g).length) :
    ∃ u, X.get (g, j) = some ⟨4826, .tc .waitLd⟩ ∧
      X.get (g, j + 1) = some (firstStoreEvent l g stage 0 (values 0)) ∧
      X.get (g, j + 2) = some (firstStoreEvent l g stage 1 (values 1)) ∧
      X.get (g, j + 3) = some (firstStoreEvent l g stage 2 (values 2)) ∧
      At u 4845 [] ∧ (∀ r, r < 3879 ∨ 3927 ≤ r → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + 4)) ending := by
  obtain ⟨u, hWait, h0, hU, hFrame, hTail⟩ :=
    packedQuarterStoreInPrefix hp stage 0 (values 0) ht (hPacked 0) (hAddr 0) hRun (by
      change j+1 < (X.tr g).length
      omega)
  have hPackedAfter (q : Fin 4) (word : Nat) (hWord : word < 8) :
      u.regs (firstPackedReg q + word) = some (probabilityDoubleWord (values q) word) := by
    rw [hFrame _ (.inr (by
      change 3895 ≤ firstPackedReg q+word
      unfold firstPackedReg
      omega))]
    exact hPacked q word hWord
  have hAddr1 := (hFrame (probabilityReg .first 1) (.inl (by decide))).trans (hAddr 1)
  obtain ⟨v, _, h1, hV, hVFrame, hVtail⟩ :=
    packedQuarterStoreInPrefix hp stage 1 (values 1) hU (hPackedAfter 1) hAddr1 hTail (by
      change j+2 < (X.tr g).length
      omega)
  have hPackedV (word : Nat) (hWord : word < 8) :
      v.regs (firstPackedReg 2 + word) = some (probabilityDoubleWord (values 2) word) := by
    have hB : firstUnpackBase 1 = 3895 := rfl
    have hP : firstPackedReg 2 = 8170 := rfl
    rw [hVFrame _ (.inr (by rw [hB, hP]; omega))]
    exact hPackedAfter 2 word hWord
  have hAddr2 := (hVFrame (probabilityReg .first 2) (.inl (by decide))).trans
    ((hFrame _ (.inl (by decide))).trans (hAddr 2))
  obtain ⟨w, _, h2, hW, hWFrame, hWtail⟩ :=
    packedQuarterStoreInPrefix hp stage 2 (values 2) hV hPackedV hAddr2 hVtail hBound
  refine ⟨w, hWait rfl, h0, h1, h2, hW, ?_, hWtail⟩
  intro r hR
  have b1 : firstUnpackBase 1 = 3895 := rfl
  have b2 : firstUnpackBase 2 = 3911 := rfl
  rw [hWFrame r (by rw [b2]; omega), hVFrame r (by rw [b1]; omega),
    hFrame r (by change r < 3879 ∨ 3895 ≤ r; omega)]

/-- From the first store wait through the first P release, only the arrival count and the
unused barrier-state destination can change. This preserves the tail pack and all ABI facts. -/
theorem firstPHandshakeInPrefix (hp : Pre p l m) (stage : Fin 2) {g j : Nat} {t : TState}
    {ending : Option TState} (ht : At t 4845 [])
    (hBase : t.regs 3217 = some (b32 (l.sharedBase + 8 * stage.val)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hBound : j+1 < (X.tr g).length) :
    ∃ u, X.get (g, j) = some ⟨4845, .tc .waitSt⟩ ∧
      X.get (g, j + 1) = some ⟨4847, .arrive (signalLoc l g stage 1) 0 1 true .cta⟩ ∧
      At u 4848 [] ∧ (∀ r, r ≠ 3927 → r ≠ 8186 → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + 2)) ending := by
  obtain ⟨hWait, hTail⟩ := probabilityWaitInPrefix hp .first false ht.1 ht.2.2.2.1 hRun (by omega)
  let v := next (setReg (next t) 3927 (b32 1))
  have hLocal : run kernel Assumptions.all l g 1 (next t) = some v := by
    apply run_local Flow.code_4846 rfl ht.next
    rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil (by
      rw [ht.next.1]
      decide) rfl]
    rfl
  have hAt : At v 4847 [(3927, b32 1)] := ht.next.set (by simp)
  have hAddr : v.regs 3217 = some (b32 (l.sharedBase + 8 * stage.val)) := by
    simpa [v, next, setReg] using hBase
  have hn : (X.tr g).drop (j+1) ≠ [] := by
    intro he
    have hl := congrArg List.length he
    simp only [List.length_drop,List.length_nil] at hl
    omega
  obtain ⟨hSignal, hAfter⟩ := signalTraceInPrefix hp stage 1 hAt.1 hAt.2.2.2.1
    hAddr hAt.2.2.2.2.1 (hTail.after_local_nonempty (run_rtg hLocal) hn) hBound
  let w := next (mbarStateDest v (some 8186))
  have hW : At w 4848 [] :=
    ⟨congrArg (· + 1) hAt.1, hAt.2.1, hAt.2.2.1, hAt.2.2.2.1, trivial⟩
  refine ⟨w, hWait, hSignal, hW, ?_, hAfter⟩
  intro r hR0 hR1
  simp [w, v, mbarStateDest, setReg, next, Function.update_of_ne hR0, Function.update_of_ne hR1]

/-- The fourth P pack is stored only after the main P slot has been released. -/
theorem firstLastStoreInPrefix (hp : Pre p l m) (stage : Fin 2) {g j : Nat} {t : TState}
    {ending : Option TState} (values : Nat → ℝ) (ht : At t 4845 [])
    (hSignalBase : t.regs 3217 = some (b32 (l.sharedBase + 8 * stage.val)))
    (hPacked : ∀ word < 8, t.regs (firstPackedReg 3 + word) =
      some (probabilityDoubleWord values word))
    (hAddr : t.regs (probabilityReg .first 3) = some (b32 (probabilityAddress l g stage 3)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hBound : j+2 < (X.tr g).length) :
    ∃ u, X.get (g, j) = some ⟨4845, .tc .waitSt⟩ ∧
      X.get (g, j + 1) = some ⟨4847, .arrive (signalLoc l g stage 1) 0 1 true .cta⟩ ∧
      X.get (g, j + 2) = some (firstStoreEvent l g stage 3 values) ∧
      At u 4857 [] ∧
      (∀ r, r ≠ 3927 → r ≠ 8186 → r < 3928 ∨ 3944 ≤ r → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + 3)) ending := by
  obtain ⟨u, hWait, hSignal, hU, hFrame, hTail⟩ :=
    firstPHandshakeInPrefix hp stage ht hSignalBase hRun (by omega)
  have hWords (word : Nat) (hWord : word < 8) :
      u.regs (firstPackedReg 3 + word) = some (probabilityDoubleWord values word) := by
    have h0 : firstPackedReg 3 = 8178 := rfl
    rw [hFrame _ (by omega) (by omega)]
    exact hPacked word hWord
  have hAddrU := (hFrame (probabilityReg .first 3) (by decide) (by decide)).trans hAddr
  obtain ⟨v, _, hStore, hV, hVFrame, hRest⟩ :=
    packedQuarterStoreInPrefix hp stage 3 values hU hWords hAddrU hTail hBound
  exact ⟨v, hWait, hSignal, hStore, hV,
    fun r hR0 hR1 hR2 => (hVFrame r hR2).trans (hFrame r hR0 hR1), hRest⟩

/-- The four stores and both P publications, up to the branch join. This prefix contains
the warp-wide events; the elected lane alone appends the tail arrival. -/
def firstPublicationEvents (l : Launch) (g : Nat) (stage : Fin 2) (values : Fin 4 → Nat → ℝ)
    (barInst electInst leader : Nat) : List Event :=
  [⟨4826, .tc .waitLd⟩, firstStoreEvent l g stage 0 (values 0),
    firstStoreEvent l g stage 1 (values 1), firstStoreEvent l g stage 2 (values 2),
    ⟨4845, .tc .waitSt⟩, ⟨4847, .arrive (signalLoc l g stage 1) 0 1 true .cta⟩,
    firstStoreEvent l g stage 3 (values 3), ⟨4857, .tc .waitSt⟩,
    ⟨4858, .warpBar (2 ^ 32 - 1) barInst⟩, ⟨4859, .elect (2 ^ 32 - 1) electInst leader⟩]

/-- The actual first-round P protocol publishes three packed quarters, then stores and
publishes the last quarter, using the corresponding two distinct stage slots. -/
theorem firstPublicationProtocol (hp : Pre p l m) (warp : Fin 8) (frame : Option (Nat → Value))
    {g j : Nat} {t : TState} (values : Fin 4 → Nat → ℝ)
    (ht : At t 4818 (tailCarry l warp .first frame))
    (hPacked : ∀ q : Fin 4, ∀ word < 8, t.regs (firstPackedReg q + word) =
      some (probabilityDoubleWord (values q) word))
    (hAddr : ∀ q : Fin 4, t.regs (probabilityReg .first q) =
      some (b32 (probabilityAddress l g (stageOf warp) q)))
    (hSignalBase : t.regs 3217 = some (b32 (l.sharedBase + 8 * (stageOf warp).val)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ u barInst electInst leader,
      (∀ i : Fin 10, X.get (g, j + i.val) =
        (firstPublicationEvents l g (stageOf warp) values barInst electInst leader)[i.val]?) ∧
      (laneOf l g = leader → X.get (g, j + 10) = some
        ⟨4867, .arrive (signalLoc l g (stageOf warp) 2) 0 1 true .cta⟩) ∧
      At u 4868 (tailCarry l warp .first frame) ∧
      Run kernel Assumptions.all l g u
        ((X.tr g).drop (if laneOf l g = leader then j + 11 else j + 10)) none := by
  obtain ⟨u, hDelayed, h0, h1, h2, hU, hFrame, hTail⟩ := firstThreeStoresTrace
    hp (stageOf warp) values (ht.mono trivial) hPacked hAddr hRun
  have hPack3 (word : Nat) (hWord : word < 8) :
      u.regs (firstPackedReg 3 + word) = some (probabilityDoubleWord (values 3) word) := by
    rw [hFrame _ (.inr (by unfold firstPackedReg; omega))]
    exact hPacked 3 word hWord
  obtain ⟨v, hFirstWait, hRelease, h3, hV, hVFrame, hVtail⟩ := firstLastStoreTrace
    hp (stageOf warp) (values 3) hU ((hFrame 3217 (by decide)).trans hSignalBase) hPack3
      ((hFrame (probabilityReg .first 3) (by decide)).trans (hAddr 3)) hTail
  have hVregs : Holds v.regs (tailCarry l warp .first frame) := by
    have hCarry (r : Nat) (hR : r < 3879 ∨ 3944 ≤ r) (hState : r ≠ 8186) :
        v.regs r = t.regs r := by
      exact (hVFrame r (by omega) hState (by omega)).trans (hFrame r (by omega))
    cases frame with
    | none => exact ⟨(hCarry 1062 (by decide) (by decide)).trans ht.2.2.2.2.1,
        (hCarry 2535 (by decide) (by decide)).trans ht.2.2.2.2.2.1, trivial⟩
    | some values =>
      refine ⟨(hCarry 1062 (by decide) (by decide)).trans ht.2.2.2.2.1,
        (hCarry 2535 (by decide) (by decide)).trans ht.2.2.2.2.2.1, holds_of_pointwise ?_⟩
      intro r hr
      have hRange : r < 3879 ∨ r = 7256 := by
        rcases List.mem_append.mp hr with h | h
        · simp only [firstTransitionRegs, List.mem_cons, List.not_mem_nil, or_false] at h
          omega
        · exact .inl (by have := mem_exponentLive.mp h; omega)
      exact (hCarry r (by omega) (by omega)).trans
        (holds_mem ht.2.2.2.2.2.2 (mem_factsFrom hr))
  obtain ⟨w, barInst, electInst, leader, hLastWait, hBar, hElect, hl, hW, hRest⟩ :=
    tailPublicationCarry hp .first warp frame (hV.mono hVregs) hVtail
  refine ⟨w, barInst, electInst, leader, ?_, ?_, hW, ?_⟩
  · intro i
    fin_cases i
    · exact hDelayed
    · exact h0
    · exact h1
    · exact h2
    · exact hFirstWait
    · exact hRelease
    · exact h3
    · exact hLastWait
    · exact hBar
    · exact hElect
  · exact hl
  · simpa only [Nat.add_assoc] using hRest

def firstAckCarry (frame : Option (Nat → Value)) : List (Nat × Value) :=
  match frame with
  | none => []
  | some values => factsFrom (tailLive .first) values

private def firstAckAfterProb (l : Launch) (offset : Nat) (frame : Option (Nat → Value)) :
    List (Nat × Value) :=
  (3948, b32 (l.sharedBase + (192 + offset))) :: (3949, b32 0) :: firstAckCarry frame

private def firstAckOffset (l : Launch) (offset : Nat) (frame : Option (Nat → Value)) :
    List (Nat × Value) :=
  (3950, b32 offset) :: (2535, b32 l.sharedBase) :: firstAckCarry frame

private theorem firstAckStage (l : Launch) (g : Nat) (warp : Fin 8)
    (frame : Option (Nat → Value)) :
    Seg kernel Assumptions.all l g 3 4868 (tailCarry l warp .first frame) 4871
      (firstAckOffset l (8 * (stageOf warp).val) frame) := by
  cases frame <;> fin_cases warp <;> intro t ht <;>
    simp only [tailCarry, firstAckOffset, firstAckCarry] at ht ⊢ <;>
    seg_fp ht using decide

private theorem firstAckAddress {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g offset : Nat) (hOffset : offset ≤ 8) (frame : Option (Nat → Value)) :
    Seg kernel Assumptions.all l g 3 4871 (firstAckOffset l offset frame) 4874
      (firstAckAfterProb l offset frame) := by
  have hShared := hp.shared.2.1
  have hBase : l.sharedBase < 2 ^ 32 := by omega
  have hOff : offset < 2 ^ 32 := by omega
  have hSum : l.sharedBase + offset < 2 ^ 32 := by omega
  have hTotal : l.sharedBase + offset + 192 < 2 ^ 32 := by omega
  have hAddress :
      Value.bits 32
        (truncBits 32
          (truncBits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 l.sharedBase) +
            truncBits 32 (BitVec.ofNat 64 offset))) + truncBits 32 (BitVec.ofInt 64 192))) =
        b32 (l.sharedBase + (192 + offset)) := by
    rw [show BitVec.ofInt 64 192 = BitVec.ofNat 64 192 by decide,
      truncBits_ofNat hBase (by decide), truncBits_ofNat hOff (by decide),
      truncBits_ofNat (n := 192) (by decide) (by decide), ← BitVec.ofNat_add,
      truncBits_ofNat hSum (by decide), truncBits_ofNat hSum (by decide), ← BitVec.ofNat_add,
      truncBits_ofNat hTotal (by decide), show l.sharedBase + offset + 192 =
        l.sharedBase + (192 + offset) by omega]
    rfl
  cases frame <;> intro t ht <;>
    simp only [firstAckOffset, firstAckAfterProb, firstAckCarry] at ht ⊢ <;>
    seg_fp ht using first | exact hAddress | decide

/-- After rejoining the tail publication, the first round consumes the correction
acknowledgement at phase zero before advancing the actual local trace. -/
theorem firstPublicationAck (hp : Pre p l m) (warp : Fin 8) (frame : Option (Nat → Value))
    {g j : Nat} {t : TState} (ht : At t 4868 (tailCarry l warp .first frame))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ failed u, (X.tr g).drop j =
      List.replicate failed ⟨4874, .wait (waitLoc l g (stageOf warp) 3) 0 false true .cta⟩ ++
        ⟨4874, .wait (waitLoc l g (stageOf warp) 3) 0 true true .cta⟩ ::
          (X.tr g).drop (j + failed + 1) ∧
      At u 4877 (firstAckCarry frame) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + failed + 1)) none := by
  have hStage := (stageOf warp).isLt
  let offset := 8 * (stageOf warp).val
  obtain ⟨u, hLocal, hU⟩ :=
    ((firstAckStage l g warp frame).comp (firstAckAddress hp g offset (by omega) frame)).rtg ht
  have hBase : ((waitSite 3).base, b32 (waitLoc l g (stageOf warp) 3).addr) ∈
      firstAckAfterProb l offset frame := List.Mem.head _
  have hPhase : ((waitSite 3).phase, b32 0) ∈ firstAckAfterProb l offset frame :=
    List.Mem.tail _ (List.Mem.head _)
  have hFresh : ∀ pair ∈ firstAckAfterProb l offset frame, pair.1 ≠ (waitSite 3).result := by
    intro pair hPair
    simp only [firstAckAfterProb, List.mem_cons] at hPair
    rcases hPair with rfl | rfl | hPair
    · change (3948 : Nat) ≠ 9753
      decide
    · decide
    cases frame with
    | none => cases hPair
    | some values =>
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hPair
      simp only [waitSite]
      rcases List.mem_append.mp hr with h | h
      · simp only [firstTransitionRegs, List.mem_cons, List.not_mem_nil, or_false] at h
        omega
      · have := mem_exponentLive.mp h
        omega
  obtain ⟨failed, v, hEvents, hV, hTail⟩ := waitTraceAt hp (stageOf warp) 3 g 0 (by decide)
    hBase hPhase hFresh hU (hRun.after_local hLocal)
  exact ⟨failed, v, hEvents, hV.mono hV.2.2.2.2.2.2, hTail⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
