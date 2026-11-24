-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingConsumerControl
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorSharedBounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MachineTracking
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry

@[expose] public section

/-! # Actual tensor writes that cannot cover a coordinate slot -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Proof PTX.Flow PTX.AsyncCopy
open TensorSharedBounds

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem tensor_load_written_byte {i : EvId} {x y b : Nat} {a : Acc} {bs : List Byte}
    {l : Loc} (hw : X.MemWrites (.async i (.write (.load x y b))) a bs)
    (hCover : a.Covers l) :
    ∃ tag addr s, X.get i = some ⟨tag, .tensorIssue addr s⟩ ∧
      TensorCopy.writeLoc s x y b = some l := by
  obtain ⟨o, address, _, _, ⟨tag, he⟩, hl, _, hSize, _⟩ := hw
  have hLoc : l = a.loc := by
    obtain ⟨hSpace, hCta, hLo, hHi⟩ := hCover
    have hAddr : l.addr = a.loc.addr := by omega
    cases l
    cases hA : a.loc
    simp_all
  exact ⟨tag, address, o.spec, he, hLoc ▸ hl⟩

/-- An actual tensor write from the MMA warp is confined to shared query storage.
That warp remains followed independently of the consumer read guards. -/
theorem query_tensor_write_window {g i x y b : Nat} {a : Acc} {bs : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hWarp : warpOf L g = 4)
    (hw : X.MemWrites (.async (g, i) (.write (.load x y b))) a bs) (hCover : a.Covers l) :
    QueryWindow L l := by
  obtain ⟨tag, addr, s, he, hLoc⟩ := tensor_load_written_byte hw hCover
  have hg := Frame.lt_of_get hX he
  have hFollow := tracked_nonconsumer_warp hpre hX (fun g hg => (hs g hg).machine) (.inl hWarp) i
  obtain ⟨z, hz⟩ : ∃ z, Frame.stateAt (Machine.code P L) X g i = some (some z) := by
    rcases Frame.fired hs hX he with ⟨state, _, hd, _⟩ | ⟨_, _, _, hEq⟩
    · cases state with
      | none => exact (hFollow hd).elim
      | some state => exact ⟨state, hd⟩
    · cases hEq
  obtain ⟨_, hf⟩ := RingEvents.fired_of_trace hX (hs g hg).machine he hz
  have hSite := RingTensorEvents.issue_site hf rfl
  have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hz
  cases z with
  | mma d =>
    obtain ⟨tile, hSite⟩ := hSite
    obtain ⟨t, ins, o, hat, _, hc, hf⟩ := Frame.fired_site hs hX he hz
    obtain ⟨site, block⟩ := d
    change site = _ at hSite
    subst site
    cases o with
    | none =>
      rcases fires_none_ends hf with ⟨_, h⟩ | h <;> cases h
    | some u =>
      have h := (MmaDataTrace.fires_qLoad hpre hg block tile hat hc hf).1
      have hSpec := (Kind.tensorIssue.inj h).2
      rw [hSpec] at hLoc
      exact (query_write_loc tile hLoc).2.2
  | tma d =>
    change warpOf L g = 5 at hRole
    omega
  | head | done | prologue _ | wg0 _ | wg2 _ | idle _ | index _ => exact hSite.elim

/-- A covering byte from the gather issuer remains within the raw buffers. -/
theorem gather_tensor_write_window {g i x y b : Nat} {a : Acc} {bs : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hWarp : warpOf L g = 5)
    (hw : X.MemWrites (.async (g, i) (.write (.load x y b))) a bs) (hCover : a.Covers l) :
    RawWindow L l := by
  obtain ⟨tag, addr, s, he, hLoc⟩ := tensor_load_written_byte hw hCover
  let issue : Event := ⟨tag, .tensorIssue addr s⟩
  have hGet : X.get (g, i) = some issue := he
  have hg := Frame.lt_of_get hX hGet
  rcases Frame.fired hs hX hGet with ⟨state, o, hd, hFire⟩ | ⟨_, _, _, hUb⟩
  · cases state with
    | some state =>
      have hSite := RingTensorEvents.issue_site hFire rfl
      have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
      cases state with
      | tma d =>
        obtain ⟨_, hSite⟩ := hSite
        exact (followed_gather_write_loc hpre hX hs hGet rfl hd hSite hLoc).2.2.1
      | mma d => change warpOf L g = 4 at hRole; omega
      | head | done | prologue _ | wg0 _ | wg2 _ | idle _ | index _ => exact hSite.elim
    | none =>
      obtain ⟨j, hj, d, first, hFirst, hd, hn⟩ := prior_dismissal (PTX.len_of_get hGet).le hd
      have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
      cases dismissal_is_consumer hpre hX hs hFirst hd hn with
      | wg0 d => change wgOf L g = 0 at hRole; unfold wgOf warpOf at *; omega
      | wg2 d => change wgOf L g = 2 at hRole; unfold wgOf warpOf at *; omega
  · have hKind := congrArg Event.kind hUb
    change Kind.tensorIssue addr s = Kind.ub _ at hKind
    cases hKind

/-- Only the MMA and gather warps can issue a load into shared memory, across the
whole concrete trace of any role. -/
theorem actual_tensor_issue_warp {g i addr : Nat} {e : Event} {s : TensorCopy.Spec}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, i) = some e) (hk : e.kind = .tensorIssue addr s) :
    warpOf L g = 4 ∨ warpOf L g = 5 := by
  have hg := Frame.lt_of_get hX he
  rcases Frame.fired hs hX he with ⟨state, _, hState, hFire⟩ | ⟨_, _, _, hFault⟩
  · cases state with
    | some state =>
      have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hState
      have hSite := RingTensorEvents.issue_site hFire hk
      cases state with
      | mma d => exact .inl hRole
      | tma d => exact .inr hRole
      | head | done | prologue _ | wg0 _ | wg2 _ | idle _ | index _ => exact hSite.elim
    | none =>
      obtain ⟨j, hj, d, first, hFirst, hd, hn⟩ := prior_dismissal (PTX.len_of_get he).le hState
      have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
      cases dismissal_is_consumer hpre hX hs hFirst hd hn with
      | wg0 d =>
        exact (no_tensor_after_softmax_or_dequant hX hs hFirst he hj hd (.inl ⟨d, rfl⟩) hk).elim
      | wg2 d =>
        exact (no_tensor_after_softmax_or_dequant hX hs hFirst he hj hd (.inr ⟨d, rfl⟩) hk).elim
  · rw [hFault] at hk
    cases hk

/-- Tensor loads write only below the end of the raw buffers. -/
theorem no_tensor_write_above_raw_buffers {g i x y b : Nat} {a : Acc}
    {bs : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hw : X.MemWrites (.async (g, i) (.write (.load x y b))) a bs)
    (hCover : a.Covers l) (hLow : L.sharedBase + 204800 ≤ l.addr) : False := by
  obtain ⟨tag, addr, s, he, _⟩ := tensor_load_written_byte hw hCover
  rcases actual_tensor_issue_warp hpre hX hs he rfl with hQuery | hGather
  · have h := (query_tensor_write_window hpre hX hs hQuery hw hCover).2
    omega
  · have h := (gather_tensor_write_window hpre hX hs hGather hw hCover).2
    omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
