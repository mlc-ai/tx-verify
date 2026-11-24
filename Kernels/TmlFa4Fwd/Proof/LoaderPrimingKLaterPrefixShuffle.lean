-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKLaterPrefixReady

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

theorem primingKLaterLaneMask {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g batch tile warp lane : Nat} {bases : Nat → Nat}
    (hb : batch < p.batch) (hTile : 128 * tile + 127 < 2 ^ 31) (j : Fin 15)
    (hOrdinary : j.val ≠ 7) {s : TState}
    (hs : At s (primingKPredicatePc (primingKLaterPair j))
      (primingKLaterFrame p l batch tile warp bases j lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (kCopyPc (primingKLaterPair j) - 5)
        (primingKPairPredicate p batch tile warp j lane ::
          primingKLaterFrame p l batch tile warp bases j lane) := by
  let tid := 32 * warp + lane
  let F := primingKLaterFrame p l batch tile warp bases j lane
  have hLen : p.kLength batch < 2 ^ 31 := by have := (hp.lengths batch hb).2.2; omega
  have hRow : kvCopyRow tile tid (0 : Fin 16) < 2 ^ 31 := by
    have := Nat.mod_lt (tid / 8) (by decide : 0 < 8)
    unfold kvCopyRow
    have hz : (0 : Fin 16).val = 0 := rfl
    rw [hz]
    omega
  have hInput : At s (primingKPredicatePc (primingKLaterPair j))
      [(1852, b32 ((p.kLength batch + 2 ^ 32 - kvCopyRow tile tid 0) % 2 ^ 32))] :=
    hs.mono ⟨holds_lookup hs.2.2.2.2 (by fin_cases j <;> rfl), trivial⟩
  obtain ⟨u, hu, hU⟩ := primingKLaterMaskForAll (l := l) (g := g) hLen hRow j s hInput
  obtain ⟨huA, hKeep⟩ := loaderLinear (regs := F.map Prod.fst)
    (by fin_cases j <;> decide) (by fin_cases j <;> decide) hs.1 (by
      fin_cases j <;> (set_option maxRecDepth 100000 in kernel_rfl)) (by
      fin_cases j <;> (set_option maxRecDepth 100000 in kernel_rfl)) hu
  have hFrame := holdsSchedulerFrame hs.2.2.2.2 hKeep (fun _ h => List.mem_map_of_mem h)
  have hPC : primingKPredicatePc (primingKLaterPair j) + 1 =
      kCopyPc (primingKLaterPair j) - 5 := by fin_cases j <;> first | contradiction | decide
  exact ⟨u, run_rtg huA, hU.1.trans hPC, hU.2.1, hU.2.2.1, hU.2.2.2.1,
    hU.2.2.2.2.1, hFrame⟩

structure PrimingKLaterLaneShuffle (p : Params) (l : Launch) (X : Execution)
    (g batch tile warp lane index rank : Nat) (bases : Nat → Nat) (j : Fin 15)
    (ending : Option TState) where
  low : Value
  high : Value
  lowChecked : Bool
  highChecked : Bool
  state : TState
  first :
    let pair := primingKLaterPair j
    X.get (g, index) = some ⟨kCopyPc pair - 5,
      .shfl .idx (b32 (bases lane % 2 ^ 32)) (primingKBroadcastSlot j) 6175 low lowChecked⟩
  second :
    let pair := primingKLaterPair j
    X.get (g, index + 1) = some ⟨kCopyPc pair - 5 + 1,
      .shfl .idx (b32 (bases lane / 2 ^ 32)) (primingKBroadcastSlot j) 6175 high highChecked⟩
  firstOrdinal : X.ShflK (g, index) rank
  secondOrdinal : X.ShflK (g, index + 1) (rank + 1)
  checkpoint :
    At state (kCopyPc (primingKLaterPair j) - 3)
      ((primingKBroadcastReg j, low) :: (primingKBroadcastReg j + 1, high) ::
        primingKPairPredicate p batch tile warp j lane ::
          primingKLaterFrame p l batch tile warp bases j lane)
  continuation : Run kernel Assumptions.all l g state ((X.tr g).drop (index + 2)) ending

theorem primingKLaterLaneShuffles {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch tile warp lane index rank : Nat}
    {bases : Nat → Nat} (j : Fin 15) {s : TState} {ending : Option TState}
    (hs : At s (kCopyPc (primingKLaterPair j) - 5)
      (primingKPairPredicate p batch tile warp j lane ::
        primingKLaterFrame p l batch tile warp bases j lane))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hRank : ((X.tr g).take index).countP Execution.isShfl = rank)
    (hFirst : (X.tr g).drop index ≠ [])
    (hSecond : ∀ e, X.get (g, index) = some e →
      e.pc = kCopyPc (primingKLaterPair j) - 5 → Execution.isShfl e = true →
      (X.tr g).drop (index + 1) ≠ []) :
    Nonempty (PrimingKLaterLaneShuffle p l X g batch tile warp lane index rank bases j ending) := by
  let pair := primingKLaterPair j
  let reg := primingKBroadcastReg j
  let F := primingKPairPredicate p batch tile warp j lane ::
    primingKLaterFrame p l batch tile warp bases j lane
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hBound : primingKBroadcastSlot j < 8 := Nat.mod_lt _ (by decide)
  have huAt : At s (kCopyPc pair - 5) F := hs
  let lowStep := fun v (_ : Bool) => next (setReg s reg v)
  have hLow : Next kernel Assumptions.all l g s s
      (.shfl .idx (b32 (bases lane % 2 ^ 32)) (primingKBroadcastSlot j) 6175 lowStep) := by
    refine ⟨.refl, primingPointerWordTemplate (src := primingKPointerReg j) hBlock hBound
      (by rw [huAt.1]; fin_cases j <;> decide)
      (by rw [huAt.1]; fin_cases j <;> decide) huAt.2.2.2.1 ?_ ?_⟩
    · rw [huAt.1]
      exact primingKLaterShuffleCode j 0
    · exact holds_lookup huAt.2.2.2.2 (by fin_cases j <;> rfl)
  obtain ⟨low, lowOk, hLo, hLoRank, hTail⟩ := hLow.shuffle_at_nonempty hr hFirst hRank
  rw [huAt.1] at hLo
  have hFresh : ∀ r ∈ F, r.1 ≠ reg := by
    fin_cases j <;> simp [F, reg, primingKBroadcastReg, primingKPairPredicate,
      primingKLaterFrame, primingKSourceFrame, primingKPointerReg, primingKLaterPair]
  have hv : At (lowStep low lowOk) (kCopyPc pair - 5 + 1) ((reg, low) :: F) :=
    huAt.set hFresh
  let highStep := fun v (_ : Bool) => next (setReg (lowStep low lowOk) (reg + 1) v)
  have hHigh : Next kernel Assumptions.all l g (lowStep low lowOk) (lowStep low lowOk)
      (.shfl .idx (b32 (bases lane / 2 ^ 32)) (primingKBroadcastSlot j) 6175 highStep) := by
    refine ⟨.refl, primingPointerWordTemplate (src := primingKPointerReg j + 1) hBlock hBound
      (by rw [hv.1]; fin_cases j <;> decide)
      (by rw [hv.1]; fin_cases j <;> decide) hv.2.2.2.1 ?_ ?_⟩
    · rw [hv.1]
      exact primingKLaterShuffleCode j 1
    · exact holds_lookup hv.2.2.2.2 (by fin_cases j <;> rfl)
  have hCount := (Flow.countP_take_succ hLo rfl).trans (congrArg (· + 1) hRank)
  obtain ⟨high, highOk, hHi, hHiRank, hFinal⟩ :=
    hHigh.shuffle_at_nonempty hTail (hSecond _ hLo rfl rfl) hCount
  rw [hv.1] at hHi
  have hFreshHi : ∀ r ∈ (reg, low) :: F, r.1 ≠ reg + 1 := by
    fin_cases j <;> simp [F, reg, primingKBroadcastReg, primingKPairPredicate,
      primingKLaterFrame, primingKSourceFrame, primingKPointerReg, primingKLaterPair]
  have hw := hv.set (v := high) hFreshHi
  have hPc : kCopyPc pair - 5 + 1 + 1 = kCopyPc pair - 3 := by fin_cases j <;> decide
  have hAt : At (highStep high highOk) (kCopyPc pair - 3)
      ((reg, low) :: (reg + 1, high) :: F) :=
    ⟨hw.1.trans hPc, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.2.1,
      hw.2.2.2.2.1, hw.2.2.2.2.2.2⟩
  exact ⟨⟨low, high, lowOk, highOk, _, hLo, hHi, hLoRank, hHiRank, hAt, hFinal⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
