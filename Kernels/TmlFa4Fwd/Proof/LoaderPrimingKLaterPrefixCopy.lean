-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKLaterPrefixOrigins
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

/-- The already issued pair uses the tail mask and its selected launch row's physical page. -/
theorem actualLaterKCopySourceInPrefix {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g src j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hSrc : src < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (i : Fin 15) (upper : Bool) {spec : AsyncCopy.Spec}
    (he : X.get (warpLane l g src, j) =
      some ⟨kCopyPc (primingKLaterPair i) + if upper then 1 else 0, .copy spec⟩) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let coords := assignedCoordinates p batch (g / l.block)
      let head := coords.2 / 6
      let tile := Mma.trips p batch coords.1 - 1
      let tid := 32 * warpIndex l g + src
      let row := kvCopyRow tile tid (primingKLaterPair i)
      head < p.kvHeads ∧ spec.src.size = (if row < p.kLength batch then 16 else 0) ∧
      spec.src.loc = p.kLayout.loc (primingScratchPage p batch row)
        head (row % 16) (kvCopyColumn tid upper) := by
  obtain ⟨batch, hb, hLo, hHi, index, ending, s, hPos, hs, hRun⟩ :=
    primingLaterShuffleSource hp hX hg hw hSrc writes hCTA i upper he
  let coords := assignedCoordinates p batch (g / l.block)
  let head := coords.2 / 6
  let tile := Mma.trips p batch coords.1 - 1
  let warp := warpIndex l g
  let thread := warpLane l g src
  let lane := 32 * warp + src
  let pair := primingKLaterPair i
  let row := kvCopyRow tile lane pair
  let base := primingKRowPointer p batch head row
  let addr := (base + 2 * kvCopyColumn lane false) % 2 ^ 64
  let live := decide (row < p.kLength batch)
  let bytes := kvCopySize (p.kLength batch) tile lane pair
  let facts := kCopyFacts l 0 lane addr bytes pair
  have hHead := (assignedCoordinates_valid hp hLo hHi).2
  have hh : head < p.kvHeads := by unfold head coords; unfold Params.heads at hHead; omega
  have hPage := primingScratchPageBound hp (row := row) hb
  have hRow : primingLaneRow tile (32 * warp + (pointerBroadcastLane src +
      primingKBroadcastSlot i)) + 64 * (pair.val / 8) = row := by
    simpa only [primingKBroadcastSlot, primingKLaterPair, Nat.add_assoc, row, lane, pair] using
      kvCopyRow_of_pointerLane tile warp src pair.val
  change primingLaneRow (Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 - 1)
    (32 * warpIndex l g + (pointerBroadcastLane src + primingKBroadcastSlot i)) +
      64 * ((primingKLaterPair i).val / 8) = row at hRow
  dsimp only [primingKPairBases] at hs
  rw [hRow] at hs
  obtain ⟨hEq, hFit, hAlign⟩ := sourceScratchPayload_live hp 0 hPage
    (Nat.mod_lt row (by decide)) hh
  change sourceScratchPayload _ _ _ _ _ = base at hEq
  rw [hEq] at hFit hAlign
  have hAt : At s (kCopyPc pair - 3)
      [(primingKBroadcastReg i, b32 (base % 2 ^ 32)),
       (primingKBroadcastReg i + 1, b32 (base / 2 ^ 32)),
       (7547, b64 (2 * kvCopyColumn lane false)), (124 + pair.val, .pred live)] :=
    hs.mono ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.1, holds_lookup hs.2.2.2.2 (by fin_cases i <;> rfl),
      hs.2.2.2.2.2.2.1, trivial⟩
  obtain ⟨u, hu, hU⟩ := primingKLaterAddress l thread (tid := lane) hFit i live s hAt
  let dst := kCopyDstReg pair
  have hDst : s.regs dst = some (b32 (kvCopyAddress l.sharedBase 0 lane (pair.val % 2) false)) :=
    holds_lookup hs.2.2.2.2 (by
      dsimp only [dst, pair, lane, warp]
      fin_cases i <;> rfl)
  obtain ⟨huA, hKeep⟩ := loaderLinear (regs := [dst])
    (by fin_cases i <;> decide) (by fin_cases i <;> decide) hAt.1
    (by fin_cases i <;> (set_option maxRecDepth 100000 in kernel_rfl))
    (by fin_cases i <;> (set_option maxRecDepth 100000 in kernel_rfl)) hu
  have huAt : At u (kCopyPc pair) facts := by
    have hSize : bytes = (if live then 16 else 0) := by simp [bytes, live, row, kvCopySize]
    apply hU.mono
    unfold facts kCopyFacts
    rw [← hSize] at hU
    exact ⟨(hKeep dst (by simp)).trans hDst, hU.2.2.2.2⟩
  have hBytes : bytes ≤ 16 := kvCopySize_le ..
  have hAligned : addr % 16 = 0 := by
    unfold addr
    rw [Nat.mod_mod_of_dvd _ (show 16 ∣ (2 : Nat) ^ 64 by decide)]
    have hCol : 2 * kvCopyColumn lane false % 16 = 0 := by
      change 2 * (8 * (lane % 8)) % 16 = 0
      omega
    rw [Nat.add_mod, hAlign, hCol]
  have more {k : Nat} (hk : k ≤ j) : (X.tr thread).drop k ≠ [] := by
    intro hNil
    exact Nat.not_le_of_lt (List.getElem?_eq_some_iff.mp he).1
      ((List.drop_eq_nil_iff.mp hNil).trans hk)
  have huRun := hRun.after_local_nonempty (run_rtg huA) (more hPos)
  obtain ⟨hLow, hTail⟩ := kCopyPrefixObserved hp (by decide : 0 < 3)
    (Nat.mod_lt _ (by decide)) hAligned hBytes pair false huAt huRun (more hPos)
  have hIssued : ∃ k, X.get (thread, k) = some
      ⟨kCopyPc pair + if upper then 1 else 0,
        .copy (kCopySpec l thread 0 lane addr bytes pair upper)⟩ := by
    cases upper
    · exact ⟨_, hLow⟩
    · have hLater : index + 2 + 1 ≤ j := by
        by_contra! h
        have hEq : index + 2 = j := by omega
        rw [hEq] at hLow
        have hBad := congrArg Event.pc (Option.some.inj (he.symm.trans hLow))
        change kCopyPc pair + 1 = kCopyPc pair at hBad
        omega
      obtain ⟨hHigh, _⟩ := kCopyPrefixObserved hp (by decide : 0 < 3)
        (Nat.mod_lt _ (by decide)) hAligned hBytes pair true huAt.next hTail (more hLater)
      exact ⟨_, hHigh⟩
  obtain ⟨other, hOther⟩ := hIssued
  have hWarp : warpIndex l g = warpIndex l thread :=
    (Step.sameWarp_lane (by rw [hp.block]) hg hSrc).1.2
  have hLoader : 14 ≤ warpIndex l thread := hWarp ▸ hw
  have hSite : 550 ≤ kCopyPc pair + (if upper then 1 else 0) ∧
      kCopyPc pair + (if upper then 1 else 0) ≤ 672 := by fin_cases i <;> cases upper <;> decide
  have hIndex := Thread.Loader.uniquePrimingCopy hp hX hLoader (.inl hSite) he hOther
  rw [hIndex] at he
  have hSpec : spec = kCopySpec l thread 0 lane addr bytes pair upper :=
    Kind.copy.inj (congrArg Event.kind (Option.some.inj (he.symm.trans hOther)))
  subst spec
  exact ⟨batch, hb, hLo, hHi, hh, rfl, primingKCopySourceLoc hp hPage hh pair upper⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
