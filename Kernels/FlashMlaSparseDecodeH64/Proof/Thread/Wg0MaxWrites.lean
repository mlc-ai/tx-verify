-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.StageWriteClasses
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.AllocReadbackSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Exchange
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteInput
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerNumeric
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PStore
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Lse
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2Events
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2RawWriteKinds
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorSharedBounds
import Lemmas.Flow.ArithCore
import Lemmas.Flow.MemTmpl

import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxWriteExtent
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxBarriers
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingTmaCoordinate
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxReturnOrigin
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingControlRegions
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount

public section

/-! # Actual shared writes in the row-maximum window -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0MaxWrites

open PTX PTX.Flow PTX.Proof StageWriteClasses MachineTracking


private theorem ordinary {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {i : EvId} {a : Acc} {bs : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) {q : Machine.ThreadD}
    (hd : Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some q))
    (hw : X.Writes i a bs) (hcover : a.Covers l) (hshared : l.space = .shared)
    (hlo : L.sharedBase + 221184 ≤ l.addr) (hhi : l.addr < L.sharedBase + 221696) :
    ∃ d : Wg0.D,
      Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg0 d)) ∧
      Wg0.Inv P L i.1 d ∧
      (d.site = .rowMax ∨ d.site = .lseStore0) ∧ a.size = 4 ∧
      a.loc = Wg0.shLoc L i.1 (Wg0.rowMaxBase + 4 * (tidOf L i.1 % 128)) := by
  have he := hw.choose_spec
  have hg := Frame.lt_of_get hX he
  have haSpace : a.loc.space = .shared := hcover.1.symm.trans hshared
  have haLow : a.loc.addr ≤ l.addr := hcover.2.2.1
  have haHigh : l.addr < a.loc.addr + a.size := hcover.2.2.2
  have excludeLow {fp : Acc} {bytes : List Byte} (hk : Kind.wr a bs = .wr fp bytes)
      (haddr : fp.loc.addr + fp.size ≤ L.sharedBase + 221184) : False := by
    rw [(Kind.wr.inj hk).1] at haHigh
    omega
  have excludeHigh {fp : Acc} {bytes : List Byte} (hk : Kind.wr a bs = .wr fp bytes)
      (haddr : L.sharedBase + 221696 ≤ fp.loc.addr) : False := by
    rw [(Kind.wr.inj hk).1] at haLow
    omega
  obtain ⟨t, ins, o, hat, hinv, hcode, hf⟩ := Frame.fired_site hs hX he hd
  have hrole := StageWriteClasses.of_write hX hs hw hd
  cases o with
  | none => rcases fires_none_ends hf with ⟨_, h⟩ | h <;> cases h
  | some u =>
    cases q with
    | wg0 d =>
      simp only [writeRole] at hrole
      generalize hsite : d.site = s at hrole
      have hv : Wg0.Inv P L i.1 d := hinv
      cases hrole with
      | stage j k =>
        change kernel.code[d.site.pc]? = some ins at hcode
        rw [hsite] at hcode
        obtain rfl := Option.some.inj (hcode.symm.trans (Wg0.stage_code j k))
        rw [Wg0.event_oStage hpre hg hat hv hsite] at hf
        have hshape := congrArg Event.kind hf.1
        have hsub : t.sub < 4 := by
          rw [(show t.sub = d.sub from hat.2.1)]
          simpa only [hsite, Wg0.Site.elems] using hv.subLt
        have hhalf := Wg0.halfLt hv.warpLt
        have hplane := (by decide : ∀ j : Fin 4, Wg0.planeAdd j.val ≤ 5) j
        have hxor := Wg0.xor_lt_eight k.isLt (Nat.mod_lt (tidOf L i.1 % 64) (by decide))
        exact (excludeLow hshape (by
          simp only [Wg0.shLoc, Wg0.stageWrite, Wg0.stageBase, Wg0.groupOff, Wg0.stageTileBytes]
          omega)).elim
      | exchange j =>
        obtain ⟨fp, hk, hloc, hsize, _⟩ := Wg0.fires_exchangeStore hpre j hsite hat hv hcode hf
        have hxor : ∀ w : Fin 4, w.val ^^^ 2 < 4 := by decide
        have hwarp : warpOf L i.1 ^^^ 2 < 4 := hxor ⟨warpOf L i.1, hv.warpLt⟩
        have hlane := hv.laneLt
        have hj := j.isLt
        exact (excludeLow hk (by
          simp only [Wg0.siteLoc, hsite, Option.some.injEq] at hloc
          rw [← hloc, hsize]
          simp only [Wg0.shLoc, Wg0.exchangeBase, Wg0.exchangeQuad, Wg0.exchangeChunk]
          omega)).elim
      | probability k =>
        obtain ⟨fp, _, _, _, _, hk, hloc, hsize, _⟩ :=
          Wg0.fires_pStore hpre hsite hat hv hcode hf
        have hhalf := Wg0.halfLt hv.warpLt
        have hlane := hv.laneLt
        have hklt := k.isLt
        have hsub : d.sub < 4 := by simpa only [hsite, Wg0.Site.elems] using hv.subLt
        exact (excludeLow hk (by
          simp only [Wg0.siteLoc, hsite, Option.some.injEq] at hloc
          rw [← hloc, hsize]
          simp only [Wg0.shLoc, Wg0.pTileBase, Wg0.pChunkStride]
          omega)).elim
      | rowMax =>
        obtain ⟨fp, hk, hloc, hsize, _⟩ := Wg0.fires_rowMax hpre hsite hat hv hcode hf
        have heq := (Kind.wr.inj hk).1
        exact ⟨d, hd, hv, .inl hsite, (congrArg Acc.size heq).trans hsize,
          (congrArg Acc.loc heq).trans hloc⟩
      | lseStore0 =>
        obtain ⟨fp, hk, hloc, hsize, _⟩ := Wg0.fires_lseStore0 hpre hsite hat hv hcode hf
        have heq := (Kind.wr.inj hk).1
        exact ⟨d, hd, hv, .inr hsite, (congrArg Acc.size heq).trans hsize,
          (congrArg Acc.loc heq).trans hloc⟩
      | lseStore =>
        have hb : Wg0.eOf L i.1 < P.b := Wg1Mma.batchOf_lt hpre hg
        have hq : Wg0.qOf L i.1 < P.s_q := Wg1Mma.queryOf_lt hpre hg
        obtain ⟨fp, hk, hloc, _⟩ := Wg0.fires_lseStore hpre hb hq hsite hat hv hcode hf
        rw [(Kind.wr.inj hk).1, hloc, Wg0.lseLocOf_eq] at haSpace
        cases haSpace
    | wg2 d =>
      simp only [writeRole] at hrole
      obtain ⟨r, s, hsite⟩ := hrole
      have hInv : Wg2.Inv P L i.1 d := hinv
      have hFired :
          (Wg2.machine P L i.1).Fired (some (.inr d)) ⟨hw.choose, .wr a bs⟩ (some u) := by
        refine ⟨t, ⟨hat, hinv⟩, ?_⟩
        change Fires t.pc (match kernel.code[d.site.pc]? with
          | some ins' => eventTmpl Assumptions.all L i.1 t ins'.op
          | none => .ub .pcOutOfRange) _ (some u)
        have hpc : t.pc = d.site.pc := hat.1
        change kernel.code[d.site.pc]? = some ins at hcode
        rw [hpc, hcode]
        exact hf
      obtain ⟨fp, hk, hloc, hsize⟩ := Wg2.fired_store_event hpre hsite hFired
      have hfit := hInv.tileFit r.val r.isLt
      have hs := s.isLt
      have hbuf := hInv.bufLt
      exact (excludeLow hk (by
        rw [hloc, hsize]
        simp only [Wg2.numSteps, Wg2.dequantBytes, Wg2.tileOff, Wg2.topkBlock,
          Wg2.tileBase] at hfit ⊢
        omega)).elim
    | index d =>
      simp only [writeRole] at hrole
      generalize hsite : d.site = s at hrole
      have hv : Wg1Index.Inv P L i.1 d := hinv
      cases hrole with
      | coordinate extra high =>
        cases extra <;> first
          | obtain ⟨fp, hk, hloc, _⟩ :=
              Wg1Index.fires_coord_main hpre hsite hv hat hcode hf
          | obtain ⟨fp, hk, hloc, _⟩ :=
              Wg1Index.fires_coord_extra hpre hsite hv hat hcode hf
        all_goals exact (excludeHigh hk (by rw [hloc]; simp only [Wg1Index.coordOff]; omega)).elim
      | validity extra =>
        cases extra <;> first
          | obtain ⟨fp, hk, hloc, _⟩ :=
              Wg1Index.fires_valid_main hpre hsite hv hat hcode hf
          | obtain ⟨fp, hk, hloc, _⟩ :=
              Wg1Index.fires_valid_extra hpre hsite hv hat hcode hf
        all_goals exact (excludeHigh hk (by rw [hloc]; simp only [Wg1Index.validOff]; omega)).elim
    | prologue d =>
      obtain ⟨w, hthread, hw', halloc⟩ :=
        PrologueAllocation.write_at_allocStore hX hs (w := .thread i) (.inl hw) ⟨d, hd⟩
      obtain rfl := AsyncCopy.Ref.thread.inj hthread
      obtain ⟨hloc, _⟩ := PrologueAllocation.allocStore_footprint hpre hX hs hw' halloc
      rw [hloc] at haLow
      change L.sharedBase + 222752 ≤ l.addr at haLow
      omega
    | head | done | idle _ | mma _ | tma _ => simp [writeRole] at hrole

/-- Only the softmax row maximum or the late row sum can cover the row-maximum window. -/
theorem covered_write {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hw : X.MemWrites w a bs) (hcover : a.Covers l) (hshared : l.space = .shared)
    (hlo : L.sharedBase + 221184 ≤ l.addr) (hhi : l.addr < L.sharedBase + 221696) :
    ∃ (i : EvId) (d : Wg0.D), w = .thread i ∧ X.Writes i a bs ∧
      Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg0 d)) ∧
      Wg0.Inv P L i.1 d ∧
      (d.site = .rowMax ∨ d.site = .lseStore0) ∧ a.size = 4 ∧
      a.loc = Wg0.shLoc L i.1 (Wg0.rowMaxBase + 4 * (tidOf L i.1 % 128)) := by
  rcases Wg2.raw_read_competing_kinds hX hw hcover hshared with
    ⟨i, rfl, hwr⟩ | ⟨i, x, y, b, rfl⟩
  · obtain ⟨role, hState⟩ := Frame.event_state hs hX ht hwr.choose_spec (by simp)
    obtain ⟨d, hd, hi, hsite⟩ := ordinary hpre hX hs hState hwr hcover hshared hlo hhi
    exact ⟨i, d, rfl, hwr, hd, hi, hsite⟩
  · obtain ⟨_, _, hwindow, _⟩ := TensorSharedBounds.written_byte_windows hpre hX hs ht hw hcover
    rcases hwindow with ⟨_, hh⟩ | ⟨_, hh⟩ <;> omega

/-- All writers covering a row word have that lane's four-byte footprint and an odd
warpgroup barrier count, including writes in a dismissed softmax suffix. -/
theorem actual_covered_write {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
    (hw : X.MemWrites w a bs) (hcover : a.Covers l) (hshared : l.space = .shared)
    (hlo : L.sharedBase + 221184 ≤ l.addr) (hhi : l.addr < L.sharedBase + 221696) :
    ∃ g i, w = .thread (g, i) ∧ X.Writes (g, i) a bs ∧ warpOf L g < 4 ∧ a.size = 4 ∧
      a.loc = Wg0.shLoc L g (Wg0.rowMaxBase + 4 * (tidOf L g % 128)) ∧
      ∃ m, ((X.tr g).take i).countP (Execution.isBarId 9) = 2 * m + 1 := by
  rcases Wg2.raw_read_competing_kinds hX hw hcover hshared with
    ⟨⟨g, i⟩, hRef, hwOrd⟩ | ⟨⟨g, i⟩, x, y, b, hRef⟩
  · have he := hwOrd.choose_spec
    have hg := Frame.lt_of_get hX he
    by_cases hDismiss : Frame.stateAt (Machine.code P L) X g i = some none
    · obtain ⟨start, hLe, d, hMask, hZero, hState⟩ :=
        mask_anchor_after_dismissal hpre hX hs he hDismiss
      have hWg : wgOf L g = 0 := RingRoleGeometry.of_trace hX hg (hs g hg).machine hState
      have hWarp : warpOf L g < 4 := by unfold warpOf wgOf at *; omega
      rcases softmax_actual_write_extent hpre hX hs hWg hState hMask hLe hwOrd with
        ⟨hSpace, _⟩ | ⟨_, _, hEnd, _⟩ | ⟨_, _, _, tag, he', hShape⟩
      · have hSpace' := hcover.1.trans hSpace
        rw [hshared] at hSpace'
        cases hSpace'
      · have hAddr := hcover.2.2.2
        omega
      rcases hShape with ⟨j, hTag, hSize, hLoc⟩ | hProb | ⟨hTag, hSize, hLoc⟩
      · have hAddr := hcover.2.2.2
        have hXor := Nat.xor_lt_two_pow (n := 2) hWarp (by decide : 2 < 2 ^ 2)
        have hLane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
        have hj := j.isLt
        rw [hSize, hLoc] at hAddr
        simp only [Wg0.shLoc, Wg0.exchangeBase, Wg0.exchangeQuad, Wg0.exchangeChunk] at hAddr
        omega
      · obtain ⟨_, _, hEnd⟩ := hProb
        have hAddr := hcover.2.2.2
        omega
      · exact ⟨g, i, hRef, hwOrd, hWarp, hSize, hLoc,
          actual_row_write_barrier_counts hpre hX hs he' hLe ⟨d, hMask, hZero, hState⟩ hTag⟩
    obtain ⟨role, _, hState, _⟩ :=
      RingSourceSites.fired_at_followed hX (hs g hg).machine hDismiss he (by simp)
    obtain ⟨d, hd, hInv, hSite, hSize, hLoc⟩ :=
      ordinary (i := (g, i)) hpre hX hs hState hwOrd hcover hshared hlo hhi
    refine ⟨g, i, hRef, hwOrd, hInv.warpLt, hSize, hLoc, ?_⟩
    rcases hSite with hSite | hSite
    · exact ⟨d.block, Wg0BarrierCount.rowMaxCount hpre hX (hs g hg).machine he hd (.inl hSite)⟩
    · have hCount := Wg0BarrierCount.maxReadCount hpre hX (hs g hg).machine he hd (.inr hSite)
      rw [ite_eq_left hSite] at hCount
      exact ⟨d.block + 1, by omega⟩
  · have hTensor := hRef ▸ hw
    have hExtract := hTensor
    obtain ⟨_, _, _, _, hi, _, _, _, _⟩ := hExtract
    have hFollow := actual_tensor_issue_followed hpre hX hs hi.choose_spec rfl
    obtain ⟨_, _, hwindow, _⟩ :=
      TensorSharedBounds.written_byte_windows_at_followed hpre hX hs hTensor hcover hFollow
    rcases hwindow with ⟨_, hh⟩ | ⟨_, hh⟩ <;> omega

private def afterSumBarrier (pc : Nat) : Prop :=
  (1157 ≤ pc ∧ pc < 1842) ∨ 3611 ≤ pc

private instance (pc : Nat) : Decidable (afterSumBarrier pc) := by
  unfold afterSumBarrier
  infer_instance

set_option maxRecDepth 100000 in
private theorem after_sum_barrier_closed : controlRegionClosed afterSumBarrier = true := by
  decide +kernel

/-- After the half sum is published, this lane makes no further write to the row array. -/
theorem no_row_write_after_sum_bar {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g j i tag : Nat} {d : Wg0.D} {a : Acc} {bytes : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
    (hBar : X.IsBarrier (g, j) 9 (some 128) tag)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)))
    (hSite : d.site = .lseBar2) (hAfter : j < i)
    (hw : X.Writes (g, i) a bytes) (hc : a.Covers l) (hShared : l.space = .shared)
    (hLo : L.sharedBase + 221184 ≤ l.addr) (hHi : l.addr < L.sharedBase + 221696) : False := by
  have hLen : j < (X.tr g).length := PTX.len_of_get hBar
  have hg := Frame.lt_of_get hX hBar
  obtain ⟨start, hStart, q, hMask, _, hMaskState⟩ :=
    first_mask_of_followed_sum_bar hLen.le hd hSite
  have hWg : wgOf L g = 0 := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
  have hWarp : warpOf L g < 4 := by unfold warpOf wgOf at *; omega
  rcases softmax_actual_write_extent hpre hX hs hWg hMaskState hMask
    (hStart.trans hAfter.le) hw with ⟨hSpace, _⟩ | ⟨_, _, hEnd, _⟩ | ⟨_, _, _, k, he, hShape⟩
  · have h := hc.1.trans hSpace
    rw [hShared] at h
    cases h
  · have h := hc.2.2.2
    omega
  rcases hShape with ⟨r, _, hSize, hLoc⟩ | ⟨_, _, _, hEnd⟩ | ⟨hTag, _, _⟩
  · have hAddr := hc.2.2.2
    have hXor := Nat.xor_lt_two_pow (n := 2) hWarp (by decide : 2 < 2 ^ 2)
    have hLane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
    have hr := r.isLt
    rw [hLoc, hSize] at hAddr
    simp only [Wg0.shLoc, Wg0.exchangeBase, Wg0.exchangeQuad, Wg0.exchangeChunk] at hAddr
    omega
  · have h := hc.2.2.2
    omega
  · have hRest : ((X.tr g).drop (j + 1))[i - (j + 1)]? = some ⟨k, .wr a bytes⟩ := by
      rw [List.getElem?_drop, Nat.add_sub_of_le hAfter]
      exact he
    have hMem := List.mem_of_getElem? hRest
    have hSplit : (X.tr g).drop j = ⟨tag, .bar 9 (some 128) .sync⟩ :: (X.tr g).drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hLen, (List.getElem?_eq_some_iff.mp hBar).2]
    obtain ⟨t, o, _, hRun⟩ := actual_suffix_from_followed hX hg (hs g hg) hd
      (by rw [hSplit]; simp)
    have hTagBar := Frame.event_pc hs hX hBar hd
    change tag = d.site.pc at hTagBar
    rw [hSite] at hTagBar
    change tag = 1156 at hTagBar
    rw [hSplit] at hRun
    generalize hTrace :
      ⟨tag, .bar 9 (some 128) .sync⟩ :: (X.tr g).drop (j + 1) = es at hRun
    cases hRun with
    | nil => cases hTrace
    | last _ _ =>
      have hTail := (List.cons.inj hTrace).2
      rw [hTail] at hMem
      cases hMem
    | step hLocal hStep hTail =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj hTrace
      have hp := bar_tag_return hStep rfl
      have hSource := PTX.EventFrame.estep_source_pc hStep
      change tag = _ at hSource
      have hAfterPc := run_in_control_region after_sum_barrier_closed
        (show afterSumBarrier _ by rw [hp, ← hSource, hTagBar]; decide) hTail _ hMem
      change afterSumBarrier k at hAfterPc
      rcases hTag with hk | hk <;> rw [hk] at hAfterPc <;> exact (by decide : ¬ _) hAfterPc

/-- An actual row-maximum read addresses the word of the lane in the other half. -/
theorem read_geometry {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {d : Wg0.D} {a : Acc} {bs : List (Option Byte)}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (hr : X.Reads (g, i) a bs)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .maxRead) :
    a.loc = Wg0.shLoc L g (Wg0.rowMaxBase + 4 * (tidOf L g % 128 ^^^ 64)) ∧ a.size = 4 ∧
      Wg0.Inv P L g d := by
  obtain ⟨t, ins, o, hat, hinv, hcode, hf⟩ := Frame.fired_site hs hX hr.choose_spec hd
  cases o with
  | none => rcases fires_none_ends hf with ⟨_, h⟩ | h <;> cases h
  | some u =>
    obtain ⟨fp, _, hk, hloc, hz, _, _⟩ := Wg0.fires_maxRead hpre hsite hat hinv hcode hf
    have hfp := (Kind.rd.inj hk).1
    exact ⟨(congrArg Acc.loc hfp).trans hloc, (congrArg Acc.size hfp).trans hz, hinv⟩

private theorem datum_byteAt_zero (v : FVal) :
    (v.toValue .f32).byteAt 0 = (v.toValue .f32, 0) := by
  cases v with
  | zero s => cases s <;> rfl
  | nan bits => cases bits <;> rfl
  | fin _ | inf _ => rfl

private theorem core_f32_scalar {f : FloatInstr} (hf : f.ty = ty1 .f32) {vs : List Value}
    {v : Value} (h : coreFloat f vs = .ok v) : v.byteAt 0 = (v, 0) := by
  simp only [coreFloat, hf, ty1, show List.range 1 = [0] from rfl, List.mapM_cons,
    List.mapM_nil, bind, Except.bind, pure, Except.pure] at h
  generalize (List.mapM (m := Exec) _ vs : Exec (List FVal)) = m at h
  rcases m with e | xs
  · cases h
  dsimp only at h
  generalize f.lane xs = o at h
  rcases o with _ | (_ | out) <;> simp [throw, throwThe, MonadExceptOf.throw] at h
  subst h
  exact datum_byteAt_zero _

private theorem scalar_mul {a b v : Value} (h : mulE true a b = .ok v) :
    v.bytes = 4 ∧ v.byteAt 0 = (v, 0) := by
  refine ⟨mulE_four true a b v h, ?_⟩
  unfold mulE at h
  split at h
  · rename_i r hr
    subst h
    unfold idealMul at hr
    obtain ⟨x, _, hx⟩ := bindRead_ok hr
    obtain ⟨y, _, hy⟩ := bindRead_ok hx
    obtain ⟨z, rfl⟩ := map_pure_ok hy
    unfold Assumption.erealValue
    split
    · exact datum_byteAt_zero _
    split
    · exact datum_byteAt_zero _
    · rfl
  · exact core_f32_scalar rfl h

/-- The stored maximum is a scalar f32 word, so rebuilding its four actual bytes recovers it. -/
theorem rowLocalMax_scalar (L : Launch) (d : Wg0.D) :
    (Wg0.rowLocalMax L d).bytes = 4 ∧
      rebuild 3 ((Wg0.rowLocalMax L d).toBytes.map some) = .ok (Wg0.rowLocalMax L d) := by
  have hword : (Wg0.rowLocalMax L d).bytes = 4 ∧
      (Wg0.rowLocalMax L d).byteAt 0 = (Wg0.rowLocalMax L d, 0) := by
    unfold Wg0.rowLocalMax Wg0.peerRowMax
    cases h0 : Wg0.peerHalfMax d.scoreSums 0 with
    | error _ => exact ⟨rfl, rfl⟩
    | ok lo =>
      simp only [bind, Except.bind]
      cases h1 : Wg0.peerHalfMax d.scoreSums 8 with
      | error _ => exact ⟨rfl, rfl⟩
      | ok hi =>
        simp only
        cases hm : Wg0.peerMaxE lo hi with
        | error _ => exact ⟨rfl, rfl⟩
        | ok m =>
          simp only
          cases hv : mulE true m (b32 (Wg0.paramWord L 28 4)) with
          | error _ => exact ⟨rfl, rfl⟩
          | ok v => exact scalar_mul hv
  exact ⟨hword.1, rebuild_scalar (by rw [hword.1]; decide) hword.2⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0MaxWrites
