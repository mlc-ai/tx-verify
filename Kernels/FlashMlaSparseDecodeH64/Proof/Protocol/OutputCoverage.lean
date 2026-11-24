-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputCoverage
public import Lemmas.TensorStore.StoreWrite

@[expose] public section

/-! # Actual output writes of a complete execution -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputCoverage

open PTX Wg0

/-- Every logical output byte belongs to an issued tile and has its performed write in a
complete execution. -/
theorem byteWritten {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hcomplete : Complete L X) (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hg : g < L.threads)
    (h : Fin 64) (column : Fin 512) (byte : Fin 2) :
    let l := (oLoc P (eOf L g) (qOf L g) h.val column.val).at byte.val
    ∃ (issuer : Nat) (i : Nat) (d : D) (j : Fin 4) (address : Nat)
      (sp : TensorStore.Spec) (s : Result.OutputSlot) (out : Byte),
      X.TensorStoreIssue (issuer, i) address sp ∧
      Frame.stateAt (Machine.code P L) X issuer i = some (some (.wg0 d)) ∧
      d.site = .tmaStore j ∧ s.2.1 = h ∧ s.2.2 = byte ∧
      ctaOf L issuer = ctaOf L g ∧ tmaX j.val (warpOf L issuer) + s.1.val = column.val ∧
      TensorStore.writeLoc sp s.1.val s.2.1.val s.2.2.val = some l ∧
      X.MemWrites (.async (issuer, i) (.write (.store s.1.val s.2.1.val s.2.2.val)))
        ⟨l, 1, false, false, .cta, 0, false⟩ [out] := by
  obtain ⟨⟨j, w, x⟩, hcol⟩ := Result.outputColumn_bijective.2 column
  obtain ⟨issuer, i, d, address, sp, hc, hw, hi, hst, hj⟩ :=
    Wg0OutputCoverage.tileOfWarp hpre hX hcomplete hs ht (NamedBar.cta_lt hg) j w
  have hlaunch : issuer < L.threads := by
    obtain ⟨_, he⟩ := hi
    exact Frame.lt_of_get hX he
  have hw' : warpOf L issuer < 2 := by rw [hw]; exact w.isLt
  let s : Result.OutputSlot := (x, h, byte)
  obtain ⟨_, _, hd⟩ := Wg0OutputTrace.tileFootprint hpre hX
    (hs issuer hlaunch) hi hst hj hw' s
  have hx : tmaX j.val (warpOf L issuer) + x.val = column.val := by
    rw [hw]
    exact congrArg Fin.val hcol
  change ctaOf L issuer = ctaOf L g at hc
  have hq : qOf L issuer = qOf L g := by simp only [qOf, ctaidX, hc]
  have he : eOf L issuer = eOf L g := by simp only [eOf, ctaidY, hc]
  have hdest : TensorStore.writeLoc sp s.1.val s.2.1.val s.2.2.val =
      some ((oLoc P (eOf L g) (qOf L g) h.val column.val).at byte.val) := by
    simpa only [s, hq, he, hx] using hd
  obtain ⟨_, b, _, _, hwrite⟩ := hcomplete.store_write hX hi hdest
  exact ⟨issuer, i, d, j, address, sp, s, b, hi, hst, hj, rfl, rfl, hc, hx, hdest, hwrite⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputCoverage
