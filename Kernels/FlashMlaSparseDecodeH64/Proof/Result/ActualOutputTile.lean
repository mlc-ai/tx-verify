-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualPvRun
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputSuccessor
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1MmaLeader
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry

@[expose] public section

/-! # The actual output words are the final run's numerator -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow Protocol Wg0
open OutputTmemReadSource

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem output_feature {g : Nat} (hLane : tidOf L g < 128)
    (tile : Fin 4) (reg : Fin 64) :
    256 * (tileHalf tile).val + (resultColumn L g tile reg).val =
      tmaX tile.val (Wg0.half L g) + reg.val := by
  have hr := reg.isLt
  simp only [tileHalf, resultColumn, Nat.mod_eq_of_lt hLane, Wg0.half, warpOf,
    Nat.div_div_eq_div_mul, tmaX]
  fin_cases tile <;> norm_num [planeAdd] <;> omega

/-- The actual output wait holds the ideal-FP32 numerator of each of its 64 output slots. -/
theorem output_wait_value {g i tag : Nat} {d : Wg0.D} {tile : Fin 4} (reg : Fin 64)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hWait : X.get (g, i) = some ⟨tag, .tc .waitLd⟩)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hSite : d.site = .oWait tile) :
    outputReal d.oWords reg.val = (actualRowRun P L X g (head L g)).O d.block
      (tmaX tile.val (Wg0.half L g) + reg.val) := by
  let cta := ctaOf L g
  obtain ⟨leader, hm⟩ := Wg1MmaLeader.cta_issuer (cta := cta) hpre hX
    (fun t ht' => (hs t ht').machine)
  let issuer := cta * L.block + 128 + leader.val
  have hIssuer : GemmRing.MmaIssuer P L X cta issuer := hm
  have hCta : ctaOf L issuer = cta := by
    have hl := leader.isLt
    simp only [issuer, ctaOf, hpre.block]
    omega
  have hg := Frame.lt_of_get hX hWait
  have hRole : wgOf L g = 0 := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
  have hLane : tidOf L g < 128 := by unfold wgOf at hRole; omega
  obtain ⟨src, c, rank, hSrc, _, hTrack, hNotified, _, hWord⟩ :=
    OutputTmemWords.final_word_from_pv hpre hX hs hIssuer hd hSite hWait reg
  have hPV := pv_cell_of_observed_issue (resultRow L g) (tileHalf tile) (resultColumn L g tile reg)
    hpre hX hs ht (hCta ▸ hIssuer) hSrc hTrack hNotified
  have hEq := outputCell_eq_pv hpre hLane hCta tile reg
  rw [← hEq] at hPV
  have hActual := hWord _ hPV
  have hCta' : issuer / L.block = g / L.block := hCta
  have hBatch : Wg1Mma.batchOf L issuer = Wg1Mma.batchOf L g := by
    simp only [Wg1Mma.batchOf, Wg1Mma.ctaOf, hCta']
  have hQuery : Wg1Mma.queryOf L issuer = Wg1Mma.queryOf L g := by
    simp only [Wg1Mma.queryOf, Wg1Mma.ctaOf, hCta']
  have hRow : (resultRow L g).val = head L g := rfl
  have hFeature := output_feature hLane tile reg
  rw [hRow, hFeature] at hActual
  simp only [outputReal, List.getD_eq_getElem?_getD, hActual, Option.getD_some, valFloat_float,
    Except.toOption, actualRowRun, Run.ofReference, hBatch, hQuery, hCta, cta]

/-- The completed epilogue tile load returns a word of the same run as the subsequent wait. -/
theorem output_load_value {g i : Nat} {d : Wg0.D} {tile : Fin 4} {e : Event}
    {words : List Value} (reg : Fin 64)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hComplete : Complete L X)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hSite : d.site = .oLoad tile) (hKind : e.kind = .tc (.ld (64 * tile.val) words .s32x32b)) :
    outputReal words reg.val = (actualRowRun P L X g (head L g)).O d.block
      (tmaX tile.val (Wg0.half L g) + reg.val) := by
  obtain ⟨tag, hw, hState⟩ := output_wait_of_complete_load hpre hX hs ht hComplete he hd hSite hKind
  exact output_wait_value reg hpre hX hs ht hw hState rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
