-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.AsyncSharedConflictsLoads
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaRecords
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.DequantAfterPv
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.DequantGenerationOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmReuseSingle
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.StageAfterPv
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.DequantCompetingWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.DequantOperandWriter
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.PvProbabilityConflicts
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaAccessWindow
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryTmaHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryTmaSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1MmaLeader
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2StoreHistory
import Lemmas.Order.OrderNotAccess
import Lemmas.Tcgen05.TcMmaACell
import Lemmas.Tcgen05.MmaObservedReads
import Lemmas.Tensor.TensorSwizzle
import Lemmas.TensorStore.StoreWrite

public section

/-! # Shared byte geometry of pending Tensor Core operand reads -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.AsyncSharedConflicts

open PTX PTX.Flow PTX.AsyncCopy MmaDataTrace Protocol Result Wg1Mma

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem qk_feature_lt (k : Fin 16) (r : Fin 128) (s : Fin 16) :
    qkFeature k r s < 512 := by
  have := k.isLt
  have := r.isLt
  have := s.isLt
  unfold qkFeature
  omega

private theorem operand_copy_geometry {g i index ct n : Nat} {s : TcCopy.Spec} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.CpIssue (g, i) s) (hc : s.ctas[n]? = some ct)
    (hn : index / s.shape.sourceBytes = n)
    (hl : TcCopy.byteLoc s.shape s.src ct (index % s.shape.sourceBytes) = some l) :
    ∃ (d : Wg1Mma.D) (k : Fin 16) (row : Fin 128) (feature : Fin 16) (b : Fin 2),
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)) ∧ d.site = .qCopy k ∧
      index = 2 * (row.val * 16 + feature.val) + b.val ∧
      l = kvOperandLoc L (ctaOf L g) 0 ⟨row.val % 64, Nat.mod_lt _ (by decide)⟩
        ⟨qkFeature k row feature, qk_feature_lt k row feature⟩ b := by
  obtain ⟨d, k, hd, hsite, rfl⟩ := MmaAccessWindow.copy_state hpre hX hs ht hi
  change [ctaOf L g][n]? = some ct at hc
  have hz : n = 0 := by simpa using (List.getElem?_eq_some_iff.mp hc).1
  rw [hz] at hc hn
  change (some (ctaOf L g) : Option Nat) = some ct at hc
  obtain rfl : ct = ctaOf L g := (Option.some.inj hc).symm
  change index / 4096 = 0 at hn
  have hIndex : index < 4096 := by omega
  change TcCopy.byteLoc (queryCopySpec L g k).shape (queryCopySpec L g k).src
    (ctaOf L g) (index % 4096) = some l at hl
  rw [Nat.mod_eq_of_lt hIndex] at hl
  obtain ⟨row, feature, b, rfl⟩ := MmaAccessWindow.operand_slot (rows := 128) hIndex
  rw [queryCopyByteLoc L g k row feature b] at hl
  exact ⟨d, k, row, feature, b, hd, hsite, rfl, (Option.some.inj hl).symm⟩

/-- A shared operand is a KV byte or a packed PV probability byte. -/
theorem operand_mma_geometry {g i index dest : Nat} {isB acc : Bool}
    {mask : List Nat} {s : TcMma.OperandSpec} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.MmaIssue (g, i) dest s acc mask)
    (hl : s.byteLoc (if isB then .b else .a) index = some l) :
    ∃ d : Wg1Mma.D, Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)) ∧
      ((∃ k, d.site = .qkMma k) ∨ ∃ k, d.site = .pvMma k) ∧
      ((isB = true ∧ ∃ (slot : Fin 64) (feature : Fin 512) (b : Fin 2),
          l = kvOperandLoc L (ctaOf L g) d.i slot feature b) ∨
        (isB = false ∧ L.sharedBase + 204800 ≤ l.addr)) := by
  rcases (MmaAccessWindow.mma_spec hpre hX hs ht hi).2 with
    ⟨block, k, _, rfl, _, hState⟩ | ⟨block, k, _, rfl, _, hState⟩
  · refine ⟨⟨.qkMma k, block⟩, hState, .inl ⟨k, rfl⟩, ?_⟩
    cases isB
    · change (qkOperands L g block k).byteLoc .a index = some l at hl
      rw [TcMma.byteLoc_a_tmem (s := qkOperands L g block k) rfl index] at hl
      cases hl
    · change (qkOperands L g block k).byteLoc .b index = some l at hl
      apply Or.inl
      refine ⟨rfl, ?_⟩
      have hN := TcMma.OperandSpec.byteLoc_index_lt (s := qkOperands L g block k) (op := .b) hl
      norm_num [qkOperands, qkDescriptor, TcMma.Operand.rows, TcMma.Operand.extent,
        TcMma.Kind.k, TcMma.Kind.width] at hN
      obtain ⟨col, f, b, rfl⟩ := MmaAccessWindow.operand_slot (rows := 128) hN
      rw [qkKeyByte L g block k col f b] at hl
      exact ⟨⟨col.val % 64, Nat.mod_lt _ (by decide)⟩, ⟨qkFeature k col f, qk_feature_lt k col f⟩,
        b, (Option.some.inj hl).symm⟩
  · refine ⟨⟨.pvMma k, block⟩, hState, .inr ⟨k, rfl⟩, ?_⟩
    have hSite (f : Fin 16) : pvSlot k f < 64 := by
      have := k.isLt
      have := f.isLt
      unfold pvSlot
      omega
    cases isB
    · change (pvOperands L g block k).byteLoc .a index = some l at hl
      apply Or.inr
      refine ⟨rfl, ?_⟩
      have hN := TcMma.OperandSpec.byteLoc_index_lt (s := pvOperands L g block k) (op := .a) hl
      norm_num [pvOperands, pvDescriptor, TcMma.Operand.rows, TcMma.Operand.extent,
        TcMma.Kind.k, TcMma.Kind.width] at hN
      obtain ⟨row, f, b, rfl⟩ := MmaAccessWindow.operand_slot (rows := 128) hN
      rw [pvProbabilityByte L g block k row f b] at hl
      obtain rfl := (Option.some.inj hl).symm
      simp only [pLinearByte]
      omega
    · change (pvOperands L g block k).byteLoc .b index = some l at hl
      apply Or.inl
      refine ⟨rfl, ?_⟩
      have hN := TcMma.OperandSpec.byteLoc_index_lt (s := pvOperands L g block k) (op := .b) hl
      norm_num [pvOperands, pvDescriptor, TcMma.Operand.rows, TcMma.Operand.extent,
        TcMma.Kind.k, TcMma.Kind.width] at hN
      obtain ⟨col, f, b, rfl⟩ := MmaAccessWindow.operand_slot (rows := 256) hN
      have hFeature : pvFeature k col < 512 := by
        have := col.isLt
        have := Nat.mod_lt k.val (by decide : 0 < 2)
        unfold pvFeature
        omega
      rw [pvValueByte L g block k col f b] at hl
      exact ⟨⟨pvSlot k f, hSite f⟩, ⟨pvFeature k col, hFeature⟩, b, (Option.some.inj hl).symm⟩

private theorem operand_location {i : EvId} {isB : Bool} {index : Nat} {a : Acc} {l : Loc}
    (h : X.Intent (.async i (.mmaRead isB index)) a false) (hc : a.Covers l) :
    X.MmaFootprint i isB index l := by
  obtain ⟨_, hSize, hFoot⟩ := h
  rwa [Acc.loc_of_one hc hSize] at hFoot

/-- Tensor Core operands do not read a byte of the raw gather ring. -/
theorem operand_outside_raw {i : EvId} {isB : Bool} {index : Nat} {a : Acc} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (h : X.Intent (.async i (.mmaRead isB index)) a false) (hc : a.Covers l) :
    ¬ TensorSharedBounds.RawWindow L l := by
  intro hRaw
  obtain ⟨g, i⟩ := i
  rcases operand_location h hc with ⟨_, _, _, _, hi, hl⟩ | ⟨_, _, _, hi, _, hc, hn, hl⟩
  · obtain ⟨d, _, _, ⟨_, slot, feature, b, rfl⟩ | ⟨_, hLo⟩⟩ :=
      operand_mma_geometry hpre hX hs ht hi hl
    · have hHi := (kv_operand_region hpre (ctaOf L g) d.i slot feature b).2
      have hLo := hRaw.1
      have hSlot := Nat.mod_lt d.i (by decide : 0 < 2)
      omega
    · exact Nat.not_lt_of_ge hLo hRaw.2
  · obtain ⟨_, k, row, feature, b, _, _, _, rfl⟩ :=
      operand_copy_geometry hpre hX hs ht hi hc hn hl
    have hHi := (kv_operand_region hpre (ctaOf L g) 0
      ⟨row.val % 64, Nat.mod_lt _ (by decide)⟩
      ⟨qkFeature k row feature, qk_feature_lt k row feature⟩ b).2
    have hLo := hRaw.1
    omega

private theorem operand_follows_query_wait {g i index : Nat} {isB : Bool} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hf : X.MmaFootprint (g, i) isB index l) :
    ∃ w < i, ∃ (tag : Nat) (d : Wg1Mma.D),
      X.get (g, w) = some ⟨tag, .wait (QueryTmaRecords.object L (ctaOf L g)) 0 true true .cta⟩ ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)) ∧ d.site ≠ .elect := by
  rcases hf with ⟨_, _, _, _, hi, hl⟩ | ⟨_, _, _, hi, _, _, _, _⟩
  · obtain ⟨d, hd, hSite, _⟩ := operand_mma_geometry hpre hX hs ht hi hl
    have hg := Frame.lt_of_get hX hi.choose_spec
    have hMarked : Wg1Mma.LoopSite d.site := by
      rcases hSite with ⟨_, ht⟩ | ⟨_, ht⟩ <;> rw [ht] <;> trivial
    have hElected : d.site ≠ .elect := by
      rcases hSite with ⟨_, ht⟩ | ⟨_, ht⟩ <;> simp [ht]
    obtain ⟨w, hw, _, tag, _, _, hWait⟩ :=
      QueryTmaHistory.wait_before_loop hpre hX (hs g hg).machine hi.choose_spec hd hMarked
    exact ⟨w, hw, tag, d, hWait, hd, hElected⟩
  · obtain ⟨d, kop, hd, hOp, _⟩ := MmaAccessWindow.copy_state hpre hX hs ht hi
    have hg := Frame.lt_of_get hX hi.choose_spec
    obtain ⟨w, hw, _, tag, _, _, hWait⟩ :=
      QueryTmaHistory.wait_before_copy hpre hX (hs g hg).machine hi.choose_spec hd hOp
    exact ⟨w, hw, tag, d, hWait, hd, by simp [hOp]⟩

/-- An overlapping tensor load is a query tile. Its notification is acquired by the
same issuer before issuing either the query copy or a subsequent MMA. -/
theorem load_write_operand_ordered {i j : EvId} {x y b index : Nat} {isB : Bool}
    {a f : Acc} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.Intent (.async i (.write (.load x y b))) a true) (ha : a.Covers l)
    (hj : X.Intent (.async j (.mmaRead isB index)) f false) (hf : f.Covers l) :
    ByteCausality L X l (.async i (.write (.load x y b))) (.async j (.mmaRead isB index)) := by
  have hInt := hi
  obtain ⟨_, spec, address, hIssue, hLoc, hSize⟩ := hInt
  rw [Acc.loc_of_one ha hSize] at hLoc
  obtain ⟨_, hCta, ⟨_, hMbar⟩ | ⟨hRaw, _⟩⟩ :=
    TensorSharedBounds.write_loc_windows hpre hX hs ht hIssue hLoc
  · obtain ⟨g, i⟩ := i
    obtain ⟨g', j⟩ := j
    have hFun n hn := (hs n hn).machine
    have hiEv := hIssue.choose_spec
    have hg := Frame.lt_of_get hX hiEv
    obtain ⟨_, q, tile, hQ, hTile, hSpec⟩ :=
      QueryTmaRecords.issue_source hpre hX hFun ht hiEv rfl hMbar
    obtain ⟨_, hFire⟩ := (hFun g hg |>.produces (hX.thr g hg)).fired_at hiEv hQ
    have hAddr := (QueryTmaSites.fired_load hpre hg hTile hFire rfl).1
    rw [hAddr, hSpec] at hIssue
    have hFoot := operand_location hj hf
    obtain ⟨hg', _, hCta', _⟩ := MmaAccessWindow.footprint hpre hX hs ht hFoot
    obtain ⟨w, hw, tag, d, hWait, hState, hBody⟩ :=
      operand_follows_query_wait hpre hX hs ht hFoot
    obtain ⟨_, hLeader⟩ := Wg1MmaLeader.cta_issuer (cta := l.cta) hpre hX hFun
    have hLane : g' = g := (hLeader g' j d hCta'.symm hState hBody).trans
      (hLeader g i q hCta.symm hQ (by simp [hTile])).symm
    subst g'
    have hObs := QueryTmaWait.tile_observed hpre hX hFun ht hIssue hWait
    have hScope : ScopesMeet L .cluster g .cta g := ⟨⟨hg, hg, rfl⟩, hg, hg, rfl⟩
    have hFinish : AsyncFinished L X (g, i) (.write (.load x y b)) (g, w) :=
      .inr ⟨.cta, hObs, hScope⟩
    have hLen : j < (X.tr g).length := by
      rcases hFoot with ⟨_, _, _, _, hi, _⟩ | ⟨_, _, _, hi, _⟩
      · exact PTX.len_of_get hi.choose_spec
      · exact PTX.len_of_get hi.choose_spec
    have hb : baseCausality L X (g, w) (g, j) := .single (.inl
      (po_of_source_not_access rfl hw hLen (by rw [hWait]; rfl)))
    exact .direct ⟨.inl ⟨hg, hg, rfl⟩,
      .direct ⟨⟨a, true, hi, ha⟩, ⟨f, false, hj, hf⟩, .inl ⟨(g, w), hFinish, hb⟩⟩⟩
  · exact (operand_outside_raw hpre hX hs ht hj hf hRaw).elim

private theorem same_copy_byte {g h i j index index' : Nat} {l : Loc} {cp cp' : TcCopy.Spec}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.CpIssue (g, i) cp)
    (hj : X.CpIssue (h, j) cp')
    (hf : X.MmaFootprint (g, i) false index l)
    (hf' : X.MmaFootprint (h, j) false index' l) :
    g = h ∧ i = j ∧ index = index' := by
  have extract {g i index : Nat} {cp : TcCopy.Spec} (hCp : X.CpIssue (g, i) cp)
      (hFoot : X.MmaFootprint (g, i) false index l) :
      ∃ (d : Wg1Mma.D) (k : Fin 16) (row : Fin 128) (f : Fin 16) (b : Fin 2),
        Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)) ∧ d.site = .qCopy k ∧
        index = 2 * (row.val * 16 + f.val) + b.val ∧
        l = ⟨.shared, ctaOf L g, TensorSwizzle.offset .b128 0
          (kvLinearByte L 0 (row.val % 64) (qkFeature k row f) b.val)⟩ := by
    rcases hFoot with ⟨_, _, _, _, hm, _⟩ | ⟨_, _, _, hi, _, hc, hn, hl⟩
    · have hBad := congrArg Event.kind (Option.some.inj (hCp.choose_spec.symm.trans hm.choose_spec))
      cases hBad
    · exact operand_copy_geometry hpre hX hs ht hi hc hn hl
  obtain ⟨d, k, row, f, b, hd, hSite, hN, hLoc⟩ := extract hi hf
  obtain ⟨d', k', row', f', b', hd', hSite', hN', hLoc'⟩ := extract hj hf'
  have hCta := congrArg Loc.cta (hLoc.symm.trans hLoc')
  obtain ⟨_, hIssuer⟩ := Wg1MmaLeader.cta_issuer (cta := ctaOf L g) hpre hX
    (fun g hg => (hs g hg).machine)
  have hThread := (hIssuer g i d rfl hd (by simp [hSite])).trans
    (hIssuer h j d' hCta.symm hd' (by simp [hSite'])).symm
  subst h
  have hAddr := TensorSwizzle.offset_injective .b128 0 (congrArg Loc.addr (hLoc.symm.trans hLoc'))
  simp only [kvLinearByte, qkFeature, Wg1Mma.kvBase] at hAddr
  have hR := row.isLt
  have hR' := row'.isLt
  have hF := f.isLt
  have hF' := f'.isLt
  have hB := b.isLt
  have hB' := b'.isLt
  have hK := k.isLt
  have hK' := k'.isLt
  have hKsame : k = k' := Fin.ext (by omega)
  subst k'
  exact ⟨rfl, QueryTmaSites.copy_site_unique hi.choose_spec hj.choose_spec hd hd' hSite hSite',
    by omega⟩

private theorem copy_thread_write_ordered {g i w j index n cta : Nat} {spec : TcCopy.Spec}
    {a : Acc} {l : Loc} {bs : List Byte}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.CpIssue (g, i) spec) (hc : spec.ctas[n]? = some cta)
    (hn : index / spec.shape.sourceBytes = n)
    (hl : TcCopy.byteLoc spec.shape spec.src cta (index % spec.shape.sourceBytes) = some l)
    (hw : X.Writes (w, j) a bs) (ha : a.Covers l) :
    ByteCausality L X l (.async (g, i) (.mmaRead false index)) (.thread (w, j)) := by
  have hFoot : X.MmaFootprint (g, i) false index l := .inr ⟨spec, n, cta, hi, rfl, hc, hn, hl⟩
  obtain ⟨_, k, row, feat, b, _, _, _, rfl⟩ := operand_copy_geometry hpre hX hs ht hi hc hn hl
  let l := kvOperandLoc L (ctaOf L g) 0
    ⟨row.val % 64, Nat.mod_lt _ (by decide)⟩ ⟨qkFeature k row feat, qk_feature_lt k row feat⟩ b
  obtain ⟨hLo, hHi⟩ := kv_operand_region hpre (ctaOf L g) 0
    ⟨row.val % 64, Nat.mod_lt _ (by decide)⟩ ⟨qkFeature k row feat, qk_feature_lt k row feat⟩ b
  change L.sharedBase ≤ l.addr at hLo
  change l.addr < L.sharedBase + 65536 at hHi
  rcases (RawSharedWrites.tile_writer_role hpre hX hs ht hw ha rfl
      (show l.addr < L.sharedBase + 131072 by omega)).2 with
    ⟨q, r, s, hState, hStore⟩ | ⟨hAbove, _⟩
  · obtain ⟨⟨producer, op⟩, wait, n, _, _, _, _, hObs⟩ := GemmRing.query_copy_before_store_byte
      hpre hX (fun g hg => (hs g hg).machine) hState hStore hw ha hLo hHi
    obtain ⟨cp, hCp⟩ := hObs.1
    obtain ⟨rfl, rfl, rfl⟩ := same_copy_byte hpre hX hs ht hi hCp hFoot hObs.2.1
    exact hObs.ordered
  · change L.sharedBase + 65536 ≤ l.addr at hAbove
    omega

private theorem kv_thread_write_ordered {g i w j index dest : Nat} {op : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} {d : Wg1Mma.D} {a : Acc} {bs : List Byte}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.MmaIssue (g, i) dest op acc mask)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hSite : (∃ k, d.site = .qkMma k) ∨ ∃ k, d.site = .pvMma k)
    (slot : Fin 64) (feature : Fin 512) (b : Fin 2)
    (hFoot : X.MmaFootprint (g, i) true index (kvOperandLoc L (ctaOf L g) d.i slot feature b))
    (hw : X.Writes (w, j) a bs) (ha : a.Covers (kvOperandLoc L (ctaOf L g) d.i slot feature b)) :
    let l := kvOperandLoc L (ctaOf L g) d.i slot feature b
    ByteCausality L X l (.thread (w, j)) (.async (g, i) (.mmaRead true index)) ∨
      ByteCausality L X l (.async (g, i) (.mmaRead true index)) (.thread (w, j)) := by
  dsimp only
  let cta := ctaOf L g
  let l := kvOperandLoc L cta d.i slot feature b
  have hFun n hn := (hs n hn).machine
  have hRead : AsyncCovers X (g, i) (.mmaRead true index) l :=
    ⟨{ loc := l, size := 1 }, false, ⟨rfl, rfl, hFoot⟩,
      Acc.covers_at (k := 0) (show 0 < 1 by decide)⟩
  have hOp : X.TcAsync (g, i) := .inl ⟨_, _, _, _, hi⟩
  have hReady : Wg1MmaGemmTrace.completed .dequant d.site = true := by
    rcases hSite with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> rfl
  have hNotElect : d.site ≠ .elect := by
    rcases hSite with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  rcases kv_ordinary_writer hpre hX hs ht hw ha with
    ⟨hThread, q, r, s, hState, hStore, hRow, hStep, hSlot⟩ | ⟨_, hCta, q, t, k, hState, hStage⟩
  · let lane := dequantLane slot feature
    change w = GemmRing.producer L cta lane at hThread
    subst w
    obtain ⟨issuer, hIssuer⟩ := GemmRing.exists_issuer (cta := cta) hpre hX hFun
    by_cases hLate : d.i < q.block
    · obtain ⟨_, wait, hLt, hFinish, hBase⟩ := DequantAfterPv.earlier_operand_completed
        (isB := true) (index := index) hpre hX hFun hIssuer rfl hOp hd hSite hLate hSlot.symm
        hw.choose_spec hState ⟨r, s, hStore⟩
      exact .inr (completed_mma_source_before_store hi hFoot hFinish rfl hLt hBase rfl hw ha)
    · have hG := hIssuer g i d rfl hd hNotElect
      subst issuer
      obtain ⟨p, curr, fp, data, hCurr, hBlock, ⟨r', s', hCurrent, hRow', hStep'⟩, hWrite,
        hCover, _, hPrior⟩ :=
        dequant_operand_source hpre hX hs hIssuer rfl hi.choose_spec hd hReady slot feature b
      rcases Nat.lt_or_eq_of_le (Nat.le_of_not_gt hLate) with hEarly | hEqual
      · have hg := Frame.lt_of_get hX hw.choose_spec
        have hBase := GemmRing.dequant_generation_base hpre hX (hFun _ hg) hState hCurr
          ⟨r, s, hStore⟩ ⟨r', s', hCurrent⟩ hw hWrite ha hCover
          (hSlot.trans (congrArg (· % 2) hBlock.symm)) (hBlock.symm ▸ hEarly)
        obtain ⟨f, sp, scope, hFence, hLt, hCover', hReach, hl, hr⟩ := hPrior
        exact .inl (.direct ⟨hRead, .inl ⟨f, sp, scope, hFence, hLt, hCover', hReach,
          hBase.trans hl, hr⟩⟩)
      · obtain rfl : r' = r := Fin.ext (hRow'.trans hRow.symm)
        obtain rfl : s' = s := Fin.ext (hStep'.trans hStep.symm)
        have hEq := Wg2StoreHistory.store_index_unique hState hCurr
          (PTX.len_of_get hw.choose_spec).le (PTX.len_of_get hWrite.choose_spec).le
          hStore hCurrent (hEqual.trans hBlock.symm)
        change j = p at hEq
        rw [hEq]
        exact .inl (.direct ⟨hRead, .inl hPrior⟩)
  · obtain ⟨issuer, hIssuer⟩ := GemmRing.exists_issuer (cta := ctaOf L w) hpre hX hFun
    obtain ⟨_, wait, hLt, hFinish, hBase⟩ := StageAfterPv.operand_completed
      (isB := true) (index := index) hpre hX hs ht hIssuer hCta.symm hOp hd hSite
      hw.choose_spec hState hStage
    exact .inr (completed_mma_source_before_store hi hFoot hFinish rfl hLt hBase rfl hw ha)

/-- Every ordinary write covering a pending Tensor Core read is ordered at that byte. -/
theorem operand_thread_write_ordered {i j : EvId} {isB : Bool} {index : Nat} {a f : Acc} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.Intent (.async i (.mmaRead isB index)) a false) (ha : a.Covers l)
    (hj : X.Intent (.thread j) f true) (hf : f.Covers l) :
    ByteCausality L X l (.thread j) (.async i (.mmaRead isB index)) ∨
      ByteCausality L X l (.async i (.mmaRead isB index)) (.thread j) := by
  have hFoot := operand_location hi ha
  have hNoRmw : ∀ tag access old bytes, X.get j ≠ some ⟨tag, .rmw access old bytes⟩ :=
    fun tag _ _ _ he => GlobalWrites.no_rmw hX ⟨tag, he⟩
  rcases (Execution.access_iff_of_not_rmw hNoRmw).mp hj with ⟨_, _, hFalse⟩ | ⟨bs, hw, _⟩
  · cases hFalse
  obtain ⟨g, i⟩ := i
  obtain ⟨w, j⟩ := j
  rcases hFoot with ⟨_, _, _, _, hIssue, hl⟩ | ⟨_, _, _, hIssue, rfl, hc, hn, hl⟩
  · obtain ⟨d, hd, hSite, ⟨rfl, slot, feature, b, rfl⟩ | ⟨rfl, hLo⟩⟩ :=
      operand_mma_geometry hpre hX hs ht hIssue hl
    · exact kv_thread_write_ordered hpre hX hs ht hIssue hd hSite slot feature b
        (operand_location hi ha) hw hf
    · exact PvProbabilityConflicts.ordinary_write_ordered hpre hX hs ht hi hj hLo ha hf
  · exact .inr (copy_thread_write_ordered hpre hX hs ht hIssue hc hn hl hw hf)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.AsyncSharedConflicts
