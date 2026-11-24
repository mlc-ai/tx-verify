-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SxAll
public import Kernels.InklingRelDecode.Proof.Protocol.SxRingUse
public import Kernels.InklingRelDecode.Proof.Interface.SxAll
public import Kernels.InklingRelDecode.Proof.Interface.OutputFrame

@[expose] public section

/-!
# `TensorSources`: the tensor loads' global bytes are fixed

For every consistent execution (so for every maximal one), each tensor copy:

* is routed (`TensorCopy.RoutingOk`): it is a `kvCopySpec` of the issuer's CTA
  (`Proof2.copy_form`), whose destination is in the CTA's shared memory and whose
  barrier is `kv_ready t` of the CTA (`Sx.copy_box`); no cluster address, `cta_group::1`;
* has a valid descriptor (`mapKv_valid` with `Pre`) of a nonempty box (`Lp.kvCopy_bytes`: 8192
  bytes);
* reads only input bytes (`Interface.kvCopy_readLoc_input`), which have their launch content
  (`Interface.reads_mem0`) and which no write covers: every global write is inside an output
  array (`Interface.global_write_in_arrays`) and the inputs are apart from the outputs
  (`Pre.outputsApart`).

Neither `Complete L X` nor maximality is used.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Wz
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A copy from the issuer's CTA to the issuer's CTA, completing on a barrier of the issuer's CTA,
without cluster addressing and of `cta_group::1`, is routed. -/
theorem route_self (hv : L.clusterGridValid) {c : Nat} (hc : c < L.grid) {x y : Nat} :
    TensorRoute L c false .one ⟨.shared, c, x⟩ ⟨.shared, c, y⟩ := by
  have hin : CtaInCluster L c c := ⟨hc, hc, rfl⟩
  refine ⟨hv, rfl, rfl, hin, hin, fun _ => ⟨rfl, rfl⟩, ?_⟩
  rw [sameCtaGroup_iff]
  exact ⟨hin, rfl⟩

/-- **The tensor loads' global bytes are fixed**, in every consistent execution. -/
theorem tensorSources_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (_hn : NumWordRead Q L X) : TensorSources L mem0 X := by
  intro ⟨g, k⟩ addr s ⟨pc, he⟩
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hc : g / L.block < L.grid := ProA.grid_lt hg
  obtain ⟨t, -, isV', slab', hh', -, -, -, hmb, -⟩ := Sx.copy_box hpre hX hf he
  obtain ⟨r, sl, kvh, isV, hh, dst, bar, hr, hs, hkvh, hV, hH, rfl⟩ :=
    Proof2.copy_form hpre hX he
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [EvW.kvCopySpec] at hmb
    show TensorRoute L (g / L.block) false .one _ bar
    rw [hmb]
    exact route_self hpre.launchValid.1 hc
  · exact mapKv_valid hpre.kvAlign hpre.slotStridePos hpre.slotStrideAlign hpre.slotStrideRange
      hpre.rowsPos hpre.rowsRange
  · rw [Lp.kvCopy_bytes]
    decide
  · intro slot a hsrc
    have hloc : TensorCopy.readLoc (EvW.kvCopySpec Q (g / L.block)
        (kvh * Q.headCols + 128 * isV + 64 * hh) (Q.page r sl * Q.pageRows + kvh * Q.headRows)
        dst bar) slot.1.val slot.2.1.val slot.2.2.val = some ⟨.global, 0, a⟩ := by
      rw [TensorCopy.readLoc_source, TensorCopy.slotAt_self]
      simp [hsrc]
    obtain ⟨-, -, hin⟩ := kvCopy_readLoc_input hpre hr hs hkvh hV hH hloc
    obtain ⟨v, hv⟩ := reads_mem0 hpre hin
    refine ⟨v, hv, fun w dst' bytes hw hcov => ?_⟩
    have hsp : dst'.loc.space = .global := hcov.1.symm
    obtain ⟨hno, hnl⟩ := hpre.outputsApart a hin
    rcases global_write_in_arrays hpre hX hf.sound hf.tracked hw hsp hcov with h | h
    · exact hno h
    · exact hnl h

end
end PTX.Kernels.InklingRelDecode.Proof.Wz
