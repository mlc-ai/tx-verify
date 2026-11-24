-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.AsyncSharedConflictsLoads
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputReadOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputStageReuse
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.StageWriteClasses
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0StageUnique
import Lemmas.TensorStore.StoreWrite

public section

/-! # Shared bytes read by output tensor stores -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.AsyncSharedConflicts

open PTX PTX.Flow PTX.AsyncCopy Protocol Wg0 Result

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem output_source_fields {g i x y b : Nat} {a : Acc} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (ha : X.Intent (.async (g, i) (.read (.store x y b))) a false) (hCover : a.Covers l) :
    ∃ (address : Nat) (spec : TensorStore.Spec) (d : D) (tile : Fin 4) (s : OutputSlot),
      X.TensorStoreIssue (g, i) address spec ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)) ∧ d.site = .tmaStore tile ∧
      warpOf L g < 2 ∧ s.1.val = x ∧ s.2.1.val = y ∧ s.2.2.val = b ∧
      l = shLoc L g (stageOff s.2.1.val (tmaX tile.val (warpOf L g) + s.1.val) + s.2.2.val) := by
  obtain ⟨_, spec, address, hIssue, hLoc, hSize⟩ := ha
  have he := hIssue.choose_spec
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, tile, hd, hSite⟩ := GlobalWrites.outputTile_site hs hX ht hIssue
  have hw := Wg0OutputControl.outputWarp hX (hs g hg).machine he hd hSite
  obtain ⟨rfl, rfl⟩ := Wg0OutputTrace.tileSpec hpre hX (hs g hg).machine hIssue hd hSite
  rw [Acc.loc_of_one hCover hSize] at hLoc
  unfold TensorStore.readLoc at hLoc
  cases hSlot : TensorTransfer.slotAt (outputSpec P L g tile).descriptor x y b with
  | none => simp [hSlot] at hLoc
  | some slot =>
    obtain ⟨s, rfl⟩ := (tensorOutputSlot_bijective P L g tile).2 slot
    have hCoords : s.1.val = x ∧ s.2.1.val = y ∧ s.2.2.val = b := by
      have h := hSlot
      unfold TensorTransfer.slotAt at h
      repeat' split at h
      all_goals try contradiction
      obtain heq := (Option.some.inj h).symm
      exact ⟨congrArg (fun t => t.1.val) heq, congrArg (fun t => t.2.1.val) heq,
        congrArg (fun t => t.2.2.val) heq⟩
    rw [hSlot, Option.map_some, outputSlot_shared hpre tile s hw] at hLoc
    exact ⟨_, _, d, tile, s, hIssue, hd, hSite, hw, hCoords.1, hCoords.2.1, hCoords.2.2,
      (Option.some.inj hLoc).symm⟩


private theorem stage_byte_bounds {g : Nat} (tile : Fin 4) (s : OutputSlot)
    (hw : warpOf L g < 2) :
    let l := shLoc L g (stageOff s.2.1.val (tmaX tile.val (warpOf L g) + s.1.val) + s.2.2.val)
    l.space = .shared ∧ L.sharedBase + 65536 ≤ l.addr ∧ l.addr < L.sharedBase + 131072 := by
  dsimp only
  let col := tmaX tile.val (warpOf L g) + s.1.val
  have hBound := stageOff_lt s.2.1.isLt (Result.outputColumn_lt tile hw s.1.isLt)
  change stageOff s.2.1.val col < stageBase + stageBytes at hBound
  have hEven : stageOff s.2.1.val col % 2 = 0 := by
    unfold stageOff stageRel stageBase stageTileBytes
    omega
  have hb := s.2.2.isLt
  have hlo : 65536 ≤ stageOff s.2.1.val col := by simp [stageOff, stageBase]
  change Space.shared = .shared ∧
    L.sharedBase + 65536 ≤ L.sharedBase + (stageOff s.2.1.val col + s.2.2.val) ∧
    L.sharedBase + (stageOff s.2.1.val col + s.2.2.val) < L.sharedBase + 131072
  unfold stageBase stageBytes at hBound
  exact ⟨rfl, by omega, by omega⟩

/-- The pending source read of any actual output issue stays in its CTA's output staging tile. -/
theorem output_read_window {i : EvId} {x y b : Nat} {a : Acc} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (ha : X.Intent (.async i (.read (.store x y b))) a false) (hCover : a.Covers l) :
    l.space = .shared ∧ l.cta = ctaOf L i.1 ∧
      L.sharedBase + 65536 ≤ l.addr ∧ l.addr < L.sharedBase + 131072 := by
  obtain ⟨g, i⟩ := i
  obtain ⟨_, _, _, tile, s, _, _, _, hw, _, _, _, rfl⟩ :=
    output_source_fields hpre hX hs ht ha hCover
  obtain ⟨hShared, hLo, hHi⟩ := stage_byte_bounds tile s hw
  exact ⟨hShared, rfl, hLo, hHi⟩

/-- A pending load destination cannot overlap a pending output read. -/
theorem load_write_output_read_disjoint {i j : EvId} {x y b x' y' b' : Nat}
    {a f : Acc} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.Intent (.async i (.write (.load x y b))) a true) (ha : a.Covers l)
    (hj : X.Intent (.async j (.read (.store x' y' b'))) f false) (hf : f.Covers l) : False := by
  obtain ⟨_, _, hLo, hHi⟩ := output_read_window hpre hX hs ht hj hf
  rcases (load_write_window hpre hX hs ht hi ha).2.2 with ⟨_, hQ⟩ | ⟨hRaw, _⟩ <;> omega

/-- The staging writer of an actual output byte precedes the pending output read of that byte. -/
theorem output_read_after_stage_write {i : EvId} {g j x y b : Nat} {a f : Acc}
    {l : Loc} {bytes : List Byte} {d : D} {tile : Fin 4} {k : Fin 8}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.Intent (.async i (.read (.store x y b))) a false) (ha : a.Covers l)
    (hw : X.Writes (g, j) f bytes) (hf : f.Covers l)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)))
    (hSite : d.site = .oStage tile k) :
    ByteCausality L X l (.thread (g, j)) (.async i (.read (.store x y b))) := by
  obtain ⟨g', i⟩ := i
  obtain ⟨_, _, out, tile', slot, hIssue, hOut, hStore, _, rfl, rfl, rfl, rfl⟩ :=
    output_source_fields hpre hX hs ht hi ha
  have hSound q hq := (hs q hq).machine
  obtain ⟨w, n, _, _, k', _, _, hState, hStage, _, _, hWrite, _, hCover, hOrder⟩ :=
    OutputReadOrder.of_prefix_issue hpre hX hSound ht hIssue hOut hStore slot
  have hWriter := Wg0StageUnique.sameByte hpre hX hSound ht hw.choose_spec hWrite.choose_spec
    rfl rfl hd hState hSite hStage hf hCover
  rw [hWriter]
  exact .direct hOrder

/-- Every ordinary write covering an actual output read byte precedes that pending read. -/
theorem output_read_after_thread_write {i j : EvId} {x y b : Nat} {a f : Acc} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.Intent (.async i (.read (.store x y b))) a false) (ha : a.Covers l)
    (hj : X.Intent (.thread j) f true) (hf : f.Covers l) :
    ByteCausality L X l (.thread j) (.async i (.read (.store x y b))) := by
  have hNoRmw : ∀ tag access old bytes, X.get j ≠ some ⟨tag, .rmw access old bytes⟩ :=
    fun tag _ _ _ he => GlobalWrites.no_rmw hX ⟨tag, he⟩
  rcases (Execution.access_iff_of_not_rmw hNoRmw).mp hj with ⟨_, _, hFalse⟩ | ⟨bs, hw, _⟩
  · cases hFalse
  obtain ⟨hShared, hCta, hLo, hHi⟩ := output_read_window hpre hX hs ht hi ha
  rcases StageWriteClasses.from_covered_write hpre hX hs ht hw hf hShared hLo hHi with
    ⟨d, tile, k, hd, hSite⟩ | ⟨dq, r, s, u, hd, hSite, hBuf, _, hFire⟩
  · exact output_read_after_stage_write hpre hX hs ht hi ha hw hf hd hSite
  obtain ⟨g, j⟩ := j
  obtain ⟨g', i⟩ := i
  obtain ⟨address, sp, out, tile, slot, hIssue, hOut, hStore, _, _, _, _, _⟩ :=
    output_source_fields hpre hX hs ht hi ha
  let cta := ctaOf L g'
  have hg := Frame.lt_of_get hX hw.choose_spec
  have hg' := Frame.lt_of_get hX hIssue.choose_spec
  have hG : ctaOf L g = cta :=
    (RoleSharedWrites.shared_cta hpre hs hX ht hw (hf.1.symm.trans hShared)).symm.trans
      (hf.2.1.symm.trans hCta)
  have hD : wgOf L g = 2 := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
  have hO : wgOf L g' = 0 := RingRoleGeometry.of_trace hX hg' (hs g' hg').machine hOut
  obtain ⟨lane, hProducer⟩ := RawRing.consumer_of_wg2 hpre hG hD
  obtain ⟨softmaxLane, hSoftmax⟩ := GemmRing.softmax_thread hpre (cta := cta) rfl hO
  have he := hw.choose_spec
  generalize hTag : hw.choose = tag at he hFire
  clear hTag
  rw [hProducer] at hw he hd hFire ⊢
  rw [hSoftmax] at hi hIssue hOut ⊢
  obtain ⟨pos, rfl⟩ := OutputStageReuse.dequantStoreByte_of_cover hpre hSite hFire he hw hf
  exact OutputStageReuse.dequant_store_before_epilogue hpre hX hs ht he hd hSite hBuf hFire
    hOut (.inr ⟨tile, hStore⟩) hIssue.choose_spec rfl pos ⟨a, .inl ⟨false, hi⟩, ha⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.AsyncSharedConflicts
