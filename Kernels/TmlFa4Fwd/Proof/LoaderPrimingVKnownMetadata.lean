-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVAdmission
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVMetadata
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKFromScratch

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

def primingVPrepareFacts (p : Params) (l : Launch) (batch qhead qtile ktile warp lane : Nat) :
    List (Nat × Value) :=
  primingKPackFrame p l batch (qhead / 6) ktile warp lane ++
    primingVAdmissionCarry p l batch qhead qtile

private theorem primingVPrepareAudit (p : Params) (l : Launch)
    (batch qhead qtile ktile warp lane : Nat) :
    let F := primingVPrepareFacts p l batch qhead qtile ktile warp lane
    PrimingScratchExtra F ∧ PrimingKWaitExtra F := by
  dsimp only
  constructor
  · constructor
    · constructor
      · set_option maxRecDepth 100000 in kernel_rfl
      · simp [primingVPrepareFacts, primingKPackFrame, primingKMaskInputs,
          primingVAdmissionCarry, primingVScratchAbi]
      · set_option maxRecDepth 100000 in kernel_rfl
    · set_option maxRecDepth 100000 in kernel_rfl
    · set_option maxRecDepth 100000 in kernel_rfl
    · set_option maxRecDepth 100000 in kernel_rfl
  · constructor
    · set_option maxRecDepth 100000 in kernel_rfl
    · simp [primingVPrepareFacts, primingKPackFrame, primingKMaskInputs,
        primingVAdmissionCarry, primingVScratchAbi]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- Keep the launcher V arguments while the actual K metadata events run. -/
theorem primingVPreparedLaneInPrefix (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i batch qhead qtile ktile warp lane : Nat} (hb : batch < p.batch)
    (hTile : 128 * ktile + 127 < 2 ^ 31)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) {t : TState} {ending : Option TState}
    (ht : At t 488 (primingKInitialScratchFacts p l batch (qhead / 6) ktile warp lane ++
      primingVAdmissionCarry p l batch qhead qtile))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending) {bound : Nat}
    (hBound : 517 ≤ bound) (hDemand : PrefixDemand X g i bound ending) :
    ∃ n u, let base := primingLaneRow ktile (32 * warp + lane)
      let pre := primingKPrepEvents p l g batch base n
      let stop := i + pre.length
      (X.tr g).drop i = pre ++ (X.tr g).drop stop ∧
      At u 520 (primingVPrepareFacts p l batch qhead qtile ktile warp lane) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop stop) ending ∧
      PrefixDemand X g stop bound ending ∧
      ∀ slot : Fin 2, PrimingMetadataAt p l X g stop batch (base + 64 * slot.val) slot := by
  let F := primingVPrepareFacts p l batch qhead qtile ktile warp lane
  have hs : At t 488 (primingScratchFacts p l batch (primingLaneRow ktile (32 * warp + lane)) 0 ++
      F) := by
    simpa only [primingKInitialScratchFacts, F, primingVPrepareFacts, List.append_assoc] using ht
  exact primingPreparedLaneWithFrameInPrefix hp hX hb hTile writes
    (primingVPrepareAudit p l batch qhead qtile ktile warp lane).1
    (primingVPrepareAudit p l batch qhead qtile ktile warp lane).2 hs hr hBound hDemand

private theorem primingFirstKReadReady {l : Launch} {g : Nat}
    (hStack : l.localBase + 128 ≤ 2 ^ 32) :
    Seg kernel [] l g 5 520 [(7295, b64 (l.localBase + 96))]
      525 [(7536, b64 (l.localBase + 96))] := by
  have hFit : l.localBase + 96 < 2 ^ 64 := by omega
  intro s hs
  seg_fp hs using norm_bits [Nat.mod_eq_of_lt hFit]

/-- The first event of the actual K pointer assembly is the low-slot metadata read. -/
theorem primingVPreparedFirstKReadInPrefix (hp : Pre p l m) {g index : Nat} {s : TState}
    {F : List (Nat × Value)} (hStack : (7295, b64 (l.localBase + 96)) ∈ F) (hs : At s 520 F)
    {ending : Option TState} (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hMore : (X.tr g).drop index ≠ []) :
    ∃ bytes, X.get (g, index) = some ⟨525, .rd (scratchWordAccess l g 0 0) bytes⟩ := by
  obtain ⟨u, hu, hU⟩ := primingFirstKReadReady (g := g) hp.localMemory.2.1 s
    (hs.mono ⟨holds_mem hs.2.2.2.2 hStack, trivial⟩)
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hs.1 (by simp)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  exact scratchWordLoadPresentInPrefix hp 0 0 hU (hr.after_local_nonempty (run_rtg huA) hMore) hMore

end
end PTX.Kernels.TmlFa4Fwd.Loader
