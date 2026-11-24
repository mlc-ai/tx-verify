-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPrefixOrigins
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g src j : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hSrc : src < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
include hp hX hg hw hSrc writes hCTA

/-- The issued V pair uses its actual launch row and the byte mask
computed during K. This holds for either vector in a consistent prefix. -/
theorem actualVCopySourceInPrefix (pair : Fin 16) (upper : Bool) {spec : AsyncCopy.Spec}
    (he : X.get (warpLane l g src, j) = some ⟨vCopyPc pair + if upper then 1 else 0, .copy spec⟩) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let coords := assignedCoordinates p batch (g / l.block)
      let tile := Mma.trips p batch coords.1 - 1
      let head := coords.2 / 6
      let tid := 32 * warpIndex l g + src
      let row := kvCopyRow tile tid pair
      head < p.kvHeads ∧ spec.src.size = (if row < p.kLength batch then 16 else 0) ∧
      spec.src.loc = p.vLayout.loc (primingScratchPage p batch row)
        head (row % 16) (kvCopyColumn tid upper) := by
  obtain ⟨batch, hb, hLo, hHi, index, ending, s, hPos, hs, hRun⟩ :=
    primingVPrefixShuffleSource hp hX hg hw hSrc writes hCTA pair upper he
  let coords := assignedCoordinates p batch (g / l.block)
  let tile := Mma.trips p batch coords.1 - 1
  let head := coords.2 / 6
  let warp := warpIndex l g
  let thread := warpLane l g src
  let tid := 32 * warp + src
  let row := kvCopyRow tile tid pair
  let base := primingVRowPointer p batch head row
  let bytes := kvCopySize (p.kLength batch) tile tid pair
  let addr := (base + 2 * kvCopyColumn tid false) % 2 ^ 64
  have hRow : primingLaneRow tile (32 * warp + vPacketSender pair src) +
      64 * (pair.val / 8) = row := by
    simpa only [vPacketSender, vPacketSelect, Nat.add_assoc, tid, row] using
      kvCopyRow_of_pointerLane tile warp src pair.val
  change primingLaneRow (Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 - 1)
    (32 * warpIndex l g + vPacketSender pair src) + 64 * (pair.val / 8) = row at hRow
  dsimp only [primingVPairBases] at hs
  rw [hRow] at hs
  have hHead := (assignedCoordinates_valid hp hLo hHi).2
  have hh : head < p.kvHeads := by unfold head coords; unfold Params.heads at hHead; omega
  have hPage := primingScratchPageBound hp (row := row) hb
  obtain ⟨hEq, hFit, hAlign⟩ := sourceScratchPayload_live hp 1 hPage
    (Nat.mod_lt row (by decide)) hh
  change sourceScratchPayload _ _ _ _ _ = base at hEq
  rw [hEq] at hFit hAlign
  have hAt : At s (vPacketShufflePc pair + 2) (vPacketAddrInputs pair base tid) := by
    apply hs.mono
    exact ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.1,
      holds_lookup hs.2.2.2.2 (by fin_cases pair <;> rfl), trivial⟩
  obtain ⟨u, hu, hU⟩ := vPacketAddress l thread pair (base := base) (tid := tid) hFit s hAt
  let dst := vCopyDstReg pair
  let count := vCopyByteReg pair
  obtain ⟨huA, hKeep⟩ := loaderLinear (regs := [dst, count])
    (by fin_cases pair <;> decide) (by fin_cases pair <;> decide) hs.1
    (by fin_cases pair <;> (set_option maxRecDepth 100000 in kernel_rfl))
    (by fin_cases pair <;> (set_option maxRecDepth 100000 in kernel_rfl)) hu
  have hDst : s.regs dst = some (b32 (kvCopyAddress l.sharedBase 0 tid (pair.val % 2) false)) :=
    holds_lookup hs.2.2.2.2 (by dsimp only [dst, tid, warp]; fin_cases pair <;> rfl)
  have hCount : s.regs count = some (b32 bytes) :=
    holds_lookup hs.2.2.2.2 (by dsimp only [count, bytes, tid, warp]; fin_cases pair <;> rfl)
  have huAt : At u (vCopyPc pair) (vCopyFacts l tid addr bytes pair) :=
    hU.mono ⟨(hKeep dst (by simp)).trans hDst, hU.2.2.2.2.1,
      (hKeep count (by simp)).trans hCount, trivial⟩
  have hAligned : addr % 16 = 0 := by
    unfold addr
    rw [Nat.mod_mod_of_dvd _ (show 16 ∣ (2 : Nat) ^ 64 by decide)]
    have hCol : 2 * kvCopyColumn tid false % 16 = 0 := by
      change 2 * (8 * (tid % 8)) % 16 = 0
      omega
    rw [Nat.add_mod, hAlign, hCol]
  have hBytes : bytes ≤ 16 := kvCopySize_le ..
  have hActual := hRun.after_local_nonempty (run_rtg huA) (traceAfterObservedEvent he hPos)
  obtain ⟨hLow, hTail⟩ := vCopyPrefixObserved hp (Nat.mod_lt _ (by decide))
    hAligned hBytes pair false huAt hActual (traceAfterObservedEvent he hPos)
  have hIssued : ∃ i, X.get (thread, i) =
      some ⟨vCopyPc pair + if upper then 1 else 0,
        .copy (vCopySpec l thread tid addr bytes pair upper)⟩ := by
    cases upper
    · exact ⟨_, hLow⟩
    · have hLater : index + 2 + 1 ≤ j := by
        by_contra! h
        have hEq : index + 2 = j := by omega
        rw [hEq] at hLow
        have hBad := congrArg Event.pc (Option.some.inj (he.symm.trans hLow))
        change vCopyPc pair + 1 = vCopyPc pair at hBad
        omega
      obtain ⟨hHigh, _⟩ := vCopyPrefixObserved hp (Nat.mod_lt _ (by decide))
        hAligned hBytes pair true huAt.next hTail (traceAfterObservedEvent he hLater)
      exact ⟨_, hHigh⟩
  obtain ⟨other, hOther⟩ := hIssued
  have hWarp : warpIndex l g = warpIndex l thread :=
    (Step.sameWarp_lane (by rw [hp.block]) hg hSrc).1.2
  have hLoader : 14 ≤ warpIndex l thread := hWarp ▸ hw
  have hSite : 810 ≤ vCopyPc pair + (if upper then 1 else 0) ∧
      vCopyPc pair + (if upper then 1 else 0) ≤ 902 :=
    by fin_cases pair <;> cases upper <;> decide
  have hIndex := Thread.Loader.uniquePrimingCopy hp hX hLoader (.inr hSite) he hOther
  rw [hIndex] at he
  have hSpec : spec = vCopySpec l thread tid addr bytes pair upper :=
    Kind.copy.inj (congrArg Event.kind (Option.some.inj (he.symm.trans hOther)))
  subst spec
  exact ⟨batch, hb, hLo, hHi, hh, rfl, primingVSourceLoc hp hPage hh pair upper⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
