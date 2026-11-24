-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantTileBase
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantOrigin
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ActualSuffix
import Lemmas.Isa.Rule
import Lemmas.Flow.NotClc
import Lemmas.Flow.WriteSpace

@[expose] public section

/-! # Concrete addresses of all dequantized chunks -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private def chunkUpdate (r : Fin 4) (s : Fin 8) : Nat :=
  if s.val = 0 then 2728 + 225 * r.val else Wg2.dequantStart r s + 13

private def chunkRegion (r : Fin 4) (s : Fin 8) (pc : Nat) : Bool :=
  decide (chunkUpdate r s + 1 ≤ pc ∧ pc ≤ (Wg2.Site.store r s).pc)

private def firstChunk (r : Fin 4) (s : Fin 8) : Bool := r == 0 && s == 0

set_option maxRecDepth 100000 in
private theorem chunk_audit {r : Fin 4} {s : Fin 8} (h : firstChunk r s = false) :
    registerRegionChecked (Wg2.storeBaseReg r s) (chunkRegion r s) [chunkUpdate r s] = true := by
  have audit : (List.finRange 4).all (fun a => (List.finRange 8).all (fun b =>
      firstChunk a b ||
        registerRegionChecked (Wg2.storeBaseReg a b) (chunkRegion a b) [chunkUpdate a b])) = true :=
    by decide +kernel
  have hh := List.all_eq_true.mp (List.all_eq_true.mp audit r (by simp)) s (by simp)
  simpa only [h, Bool.false_or] using hh

private theorem chunk_update_code {r : Fin 4} {s : Fin 8} (h : firstChunk r s = false) :
    kernel.code[chunkUpdate r s]? = some ⟨none, .int (Wg2.storeAdd r s)⟩ := by
  by_cases hs : s.val = 0
  · have hEq : s = 0 := Fin.ext hs
    subst s
    fin_cases r
    · cases h
    · exact Flow.code_2953
    · exact Flow.code_3178
    · exact Flow.code_3403
  · simpa only [chunkUpdate, ite_eq_right hs, Wg2.chunkInstruction] using
      (Wg2.chunkCode r s).address hs

private theorem chunk_update_bounds (r : Fin 4) (s : Fin 8)
    (h : firstChunk r s = false) :
    dequantBaseRegion (chunkUpdate r s) = true ∧
      chunkUpdate r s ∉ paramAdds ∧ chunkUpdate r s ∉ prefetchTensorMapSites ∧
      chunkUpdate r s ∉ Assumptions.sharedBitsSites := by
  revert h
  revert r s
  decide +kernel

private theorem chunk_at_store (r : Fin 4) (s : Fin 8) :
    chunkRegion r s (Wg2.Site.store r s).pc = true := by
  revert r s
  decide +kernel

private theorem chunk_fit (r : Fin 4) (s : Fin 8) (b : Fin 2) :
    Wg2.tileBase b.val + Wg2.tileOff L g r.val s.val + 16 ≤ 131072 := by
  have hb := b.isLt
  have h := Wg2.tile_fit (L := L) (g := g) r.isLt s.isLt
  unfold Wg2.dequantBytes at h
  unfold Wg2.tileBase Wg2.dequantBytes
  omega

private theorem chunk_address_add {r : Fin 4} {s : Fin 8} {t u : TState}
    (hpre : Pre P L mem0) (hNotFirst : firstChunk r s = false)
    (hp : t.pc = chunkUpdate r s) (hBefore : DequantTileBase L g t)
    (hTau : Tau kernel Assumptions.all L g t u) :
    ∃ b : Fin 2, u.regs (Wg2.storeBaseReg r s) =
      some (b32 (L.sharedBase + Wg2.tileBase b.val + Wg2.tileOff L g r.val s.val)) := by
  obtain ⟨hRange, hParam, hPrefetch, hSharedBits⟩ := chunk_update_bounds r s hNotFirst
  obtain ⟨b, hb⟩ := hBefore.chunk (hp ▸ hRange)
  let a := L.sharedBase + Wg2.tileBase b.val + Wg2.dstOff L g
  let n := Wg2.tileChunkDelta r s
  have hAddr : a + n = L.sharedBase + Wg2.tileBase b.val + Wg2.tileOff L g r.val s.val := by
    simp [a, n, Wg2.tileChunkDelta, Wg2.tileOff, Wg2.topkBlock, Wg2.numGroups, Nat.add_assoc]
  have hFit := chunk_fit (L := L) (g := g) r s b
  have hShared := sharedBase_lt hpre
  have hLimit : a + n < 2 ^ 32 := by omega
  have hLocal := Thread.asms_localRule_int (L := L) (g := g) (t := t) (i := Wg2.storeAdd r s)
    (hp ▸ hParam) (hp ▸ hPrefetch) (hp ▸ hSharedBits) rfl
  have hExec : execLocalA Assumptions.all L g t (.int (Wg2.storeAdd r s)) =
      .ok (PTX.next (setReg t (Wg2.storeBaseReg r s) (b32 (a + n)))) := by
    rw [execLocalA_noSegment (Proof.asms_segment_free t), execLocalRule_of_none hLocal,
      execLocal_int rfl]
    simp only [Wg2.storeAdd, execInt, DType.width, readValue, readBits, readReg, hb, b32, n, a,
      bind, Except.bind, pure, Except.pure]
    rw [BitVec.ofInt_natCast, Wg2.trunc32_add_word (by omega : n < 2 ^ 32) hLimit]
  have hLocalOut := out_tau (K := kernel) (tau_fault_free hTau)
    (hp ▸ chunk_update_code hNotFirst) rfl rfl hExec
  unfold Tau at hTau
  rw [hLocalOut] at hTau
  obtain rfl := Out.tau.inj hTau
  refine ⟨b, ?_⟩
  change (setReg t (Wg2.storeBaseReg r s) (b32 (a + n))).regs (Wg2.storeBaseReg r s) = _
  simp [setReg, hAddr]

private def ChunkAddresses (L : Launch) (g : Nat) (t : TState) : Prop :=
  DequantTileBase L g t ∧ ∀ r s, firstChunk r s = false → chunkRegion r s t.pc = true →
    ∃ b : Fin 2, t.regs (Wg2.storeBaseReg r s) =
      some (b32 (L.sharedBase + Wg2.tileBase b.val + Wg2.tileOff L g r.val s.val))

private theorem chunk_address_tau {t u : TState}
    (hpre : Pre P L mem0) (hOld : ChunkAddresses L g t)
    (hTau : Tau kernel Assumptions.all L g t u) :
    ChunkAddresses L g u := by
  refine ⟨dequant_tile_base_tau hpre hOld.1 hTau, fun r s hFirst => ?_⟩
  refine register_region_tau (property := fun v => ∃ b : Fin 2,
    v = some (b32 (L.sharedBase + Wg2.tileBase b.val + Wg2.tileOff L g r.val s.val)))
    (chunk_audit hFirst) (hOld.2 r s hFirst) ?_ hTau
  intro hp _
  exact chunk_address_add hpre hFirst (List.mem_singleton.mp hp) hOld.1 hTau

private theorem chunk_address_event {t u : TState} {e : Event}
    (hOld : ChunkAddresses L g t) (he : EStep kernel Assumptions.all L g t e (some u)) :
    ChunkAddresses L g u := by
  refine ⟨dequant_tile_base_event hOld.1 he, fun r s hFirst => ?_⟩
  refine register_region_event (property := fun v => ∃ b : Fin 2,
    v = some (b32 (L.sharedBase + Wg2.tileBase b.val + Wg2.tileOff L g r.val s.val)))
    (chunk_audit hFirst) ?_ (hOld.2 r s hFirst) he
  intro pc hPc ins hc
  obtain rfl := List.mem_singleton.mp hPc
  rw [chunk_update_code hFirst] at hc
  obtain rfl := Option.some.inj hc
  rfl

private theorem chunk_addresses_at_first_scale {d : Wg2.D} {t : TState}
    (hd : d.site = .scale 0 0) (hAt : Wg2.AtD P L g d t) (hi : Wg2.Inv P L g d) :
    ChunkAddresses L g t := by
  have ht := hAt.1
  change t.pc = d.site.pc at ht
  rw [hd] at ht
  have hPc : t.pc = 2695 := ht
  have hDst := hAt.reg (r := 516) (by rw [hd]; decide +kernel)
  have hBase := hAt.reg (r := 2472) (by rw [hd]; decide +kernel)
  refine ⟨⟨by rw [hPc]; decide, fun _ => hDst, ?_, ?_, ?_, fun _ => ?_⟩, ?_⟩
  · rw [hPc]; intro h; cases h
  · rw [hPc]; intro h; cases h
  · rw [hPc]; intro h; cases h
  · exact ⟨⟨d.buf, hi.bufLt⟩, by
      simpa [Wg2.valueOf, Wg2.table, sb, lookupLit, Nat.add_assoc] using hBase⟩
  · intro r s hn hr
    rw [hPc] at hr
    have h : ∀ r s, firstChunk r s = false → chunkRegion r s 2695 = false := by decide +kernel
    rw [h r s hn] at hr
    cases hr

private def tileWrites : List Nat :=
  (List.finRange 4).flatMap (fun r => (List.finRange 8).map (Wg2.Site.store r · |>.pc))

set_option maxRecDepth 100000 in
private theorem dequant_write_sites : kernel.code.zipIdx.all (fun (ins, pc) =>
    !decide (dequantTileRegion pc) || !writeOp ins.op || tileWrites.contains pc) = true := by
  decide +kernel

private theorem chunk_regs_at_store {t : TState} (h : ChunkAddresses L g t)
    (r : Fin 4) (s : Fin 8) (hp : t.pc = (Wg2.Site.store r s).pc) :
    ∃ b : Fin 2, t.regs (Wg2.storeBaseReg r s) =
      some (b32 (L.sharedBase + Wg2.tileBase b.val + Wg2.tileOff L g r.val s.val)) := by
  cases hFirst : firstChunk r s
  · exact h.2 r s hFirst (hp ▸ chunk_at_store r s)
  · have hEq : r = 0 ∧ s = 0 := by simpa [firstChunk, Bool.and_eq_true] using hFirst
    obtain ⟨rfl, rfl⟩ := hEq
    obtain ⟨b, hb⟩ := h.1.chunk (hp ▸ by decide +kernel)
    exact ⟨b, by simpa [Wg2.tileOff, Wg2.storeBaseReg, Wg2.chunkIndex] using hb⟩

private theorem chunk_store_footprint {t : TState} {o : Option TState} {tag : Nat}
    {a : Acc} {bytes : List Byte}
    (hpre : Pre P L mem0) (r : Fin 4) (s : Fin 8) (b : Fin 2)
    (hReg : t.regs (Wg2.storeBaseReg r s) =
      some (b32 (L.sharedBase + Wg2.tileBase b.val + Wg2.tileOff L g r.val s.val)))
    (hf : Fires tag (eventTmpl Assumptions.all L g t (.mem (Wg2.tileStore r s)))
      ⟨tag, .wr a bytes⟩ o) :
    a.loc.addr + a.size ≤ L.sharedBase + 131072 := by
  let addr := L.sharedBase + Wg2.tileBase b.val + Wg2.tileOff L g r.val s.val
  have hFit : addr + 16 ≤ L.sharedBase + 131072 := by
    have h := chunk_fit (L := L) (g := g) r s b
    unfold addr
    omega
  have hBound : addr < 2 ^ 32 := by have := sharedBase_lt hpre; omega
  have hAddr := effAddr_b32 (L := L) (g := g) hReg hBound
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := Wg2.storeBaseReg r s) (w := 32)
    rfl rfl rfl rfl (by simp [Wg2.tileStore])] at hf
  change Fires tag (storeTmpl L g t .shared 128 (Wg2.storeBaseReg r s) 0
    [.reg (Wg2.chunkPackReg r s)]) ⟨tag, .wr a bytes⟩ o at hf
  unfold storeTmpl at hf
  simp only [hAddr, bind, Except.bind, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.reduceDiv] at hf
  have hAlign : addr % (16 * 1) = 0 := by
    simpa [addr, Nat.add_assoc] using Wg2.sharedTile_align hpre g b.val r s
  rw [elemAcc_ok (by decide) hAlign] at hf
  cases hSub : t.sub with
  | zero =>
    rw [hSub] at hf
    simp only [List.getElem?_cons_zero] at hf
    split at hf
    · cases hf.1
    · have hAcc := (Kind.wr.inj (congrArg Event.kind hf.1)).1
      rw [hAcc]
      exact hFit
  | succ n =>
    rw [hSub] at hf
    cases hf.1

/-- Every concrete WG2 write following its first scale load is inside the dequantized tiles.
This includes writes after a later value guard has dismissed the lane. -/
theorem dequant_write_below_coordinates {start i : Nat} {d : Wg2.D} {a : Acc}
    {bytes : List Byte}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hState : Frame.stateAt (Machine.code P L) X g start = some (some (.wg2 d)))
    (hScale : d.site = .scale 0 0) (hBefore : start ≤ i)
    (hw : X.Writes (g, i) a bytes) :
    a.loc.addr + a.size ≤ L.sharedBase + 131072 := by
  obtain ⟨tag, he⟩ := hw
  have hg := Frame.lt_of_get hX he
  have hGet : ((X.tr g).drop start)[i - start]? = some ⟨tag, .wr a bytes⟩ := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hBefore]
    exact he
  have hMem := List.mem_of_getElem? hGet
  obtain ⟨t, o, hGood, hRun⟩ :=
    actual_suffix_from_followed hX hg (hs g hg) hState (List.ne_nil_of_mem hMem)
  have hStart := chunk_addresses_at_first_scale hScale
    (show Wg2.AtD P L g d t from hGood.1) hGood.2
  obtain ⟨u, q, hu, hStep⟩ := actual_event_invariant
    (chunk_address_tau hpre) chunk_address_event hStart hRun hMem
  cases q with
  | none =>
    obtain ⟨_, _, hf⟩ := hStep
    have h := fires_none_ends hf
    simp [Ends] at h
  | some v =>
    obtain ⟨ins, hc, _, hf⟩ := PTX.EventFrame.estep_event_source hStep
    have hTag := PTX.EventFrame.estep_source_pc hStep
    have hk := List.all_eq_true.mp dequant_write_sites (ins, u.pc)
      (List.mem_zipIdx_iff_getElem?.mpr hc)
    have hSite : u.pc ∈ tileWrites := by
      simpa [hu.1.region, fires_write_op hf rfl] using hk
    obtain ⟨r, _, hR⟩ := List.mem_flatMap.mp hSite
    obtain ⟨s, _, hS⟩ := List.mem_map.mp hR
    obtain ⟨b, hb⟩ := chunk_regs_at_store hu r s hS.symm
    rw [← hS, Wg2.tileStore_code] at hc
    obtain rfl := Option.some.inj hc
    rw [← hTag] at hf
    exact chunk_store_footprint hpre r s b hb hf

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
