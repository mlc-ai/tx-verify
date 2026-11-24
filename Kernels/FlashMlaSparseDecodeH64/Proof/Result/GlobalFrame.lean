-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GlobalWrites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputControl
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxLseExtent
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxOutputMap
import Lemmas.Tensor.TensorCompleteConsistentRead
import Lemmas.TensorStore.StoreWrite

public section

/-! # The global memory outside the outputs is unchanged -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
open PTX PTX.Flow Wg0

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem rowInRange {e q : Nat} (he : e < P.b) (hq : q < P.s_q) :
    e * P.s_q + q < P.b * P.s_q := by
  have h := Nat.mul_le_mul_right P.s_q (Nat.succ_le_of_lt he)
  rw [Nat.succ_mul] at h
  omega

/-- Bytes of a logical LSE element lie inside the LSE allocation. -/
theorem lseRange {e q h : Nat} (he : e < P.b) (hq : q < P.s_q) (hh : h < 64)
    {l : Loc} (hl : (lseLoc P e q h).InRange 4 l) :
    P.lseBase ≤ l.addr ∧ l.addr < P.lseBase + lseBytes P := by
  have hr := rowInRange he hq
  have htotal : lseBytes P = 256 * (P.b * P.s_q) := by unfold lseBytes; ring
  rw [htotal]
  obtain ⟨_, _, hlo, hhi⟩ := hl
  simp only [lseLoc] at hlo hhi
  omega

/-- Bytes of a logical output element lie inside the output allocation. -/
theorem outputRange {e q h d k : Nat} (he : e < P.b) (hq : q < P.s_q)
    (hh : h < 64) (hd : d < 512) (hk : k < 2) {l : Loc}
    (hl : ((oLoc P e q h d).at k).InRange 1 l) :
    P.outBase ≤ l.addr ∧ l.addr < P.outBase + tensorBytes P := by
  have hr := rowInRange he hq
  have htotal : tensorBytes P = 65536 * (P.b * P.s_q) := by unfold tensorBytes; ring
  rw [htotal]
  obtain ⟨_, _, hlo, hhi⟩ := hl
  simp only [oLoc, Loc.at] at hlo hhi
  omega

/-- An issued asynchronous store reserves a logical output byte for its issuing CTA. -/
theorem output_destination (hpre : Pre P L mem0) (hs : GlobalWrites.SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (ht : Frame.Tracked (Machine.code P L) X)
    {i : EvId} {addr x y k : Nat} {s : TensorStore.Spec} {loc : Loc}
    (hi : X.TensorStoreIssue i addr s) (hloc : TensorStore.writeLoc s x y k = some loc) :
    ∃ d : D, ∃ j : Fin 4,
      Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg0 d)) ∧
      d.site = .tmaStore j ∧ warpOf L i.1 < 2 ∧ x < 64 ∧ y < 64 ∧ k < 2 ∧
      loc = (oLoc P (eOf L i.1) (qOf L i.1) y (tmaX j.val (warpOf L i.1) + x)).at k := by
  have he := hi
  obtain ⟨_, he⟩ := he
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, j, hd, hj⟩ := GlobalWrites.outputTile_site hs hX ht hi
  have hw := Wg0OutputControl.outputWarp hX (hs _ hg).machine he hd hj
  obtain ⟨_, hspec⟩ := Wg0OutputTrace.tileSpec hpre hX (hs _ hg).machine hi hd hj
  rw [hspec, TensorStore.writeLoc] at hloc
  cases hh : TensorTransfer.slotAt (outputSpec P L i.1 j).descriptor x y k with
  | none => simp [hh] at hloc
  | some slot =>
    have hcoords := TensorCopy.slotAt_coordinates hh
    obtain ⟨hx, hy, hk⟩ := outputShape P L i.1 j
    have hx' : slot.1.val < 64 := hx ▸ slot.1.isLt
    have hy' : slot.2.1.val < 64 := hy ▸ slot.2.1.isLt
    have hk' : slot.2.2.val < 2 := hk ▸ slot.2.2.isLt
    let out : OutputSlot := (⟨slot.1.val, hx'⟩, ⟨slot.2.1.val, hy'⟩, ⟨slot.2.2.val, hk'⟩)
    have hslot : tensorOutputSlot P L i.1 j out = slot := by
      rcases slot with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩
      rfl
    rw [hh, Option.bind_some, ← hslot, outputSlot_destination P L i.1 j out hw
      (Wg1Mma.queryOf_lt hpre hg) (Wg1Mma.eOf_lt_b hpre)] at hloc
    obtain ⟨hcx, hcy, hck⟩ := hcoords
    exact ⟨d, j, hd, hj, hw, hcx ▸ hx', hcy ▸ hy', hck ▸ hk',
      by simpa only [out, hcx, hcy, hck] using (Option.some.inj hloc).symm⟩

/-- A performed asynchronous store writes the byte reserved by its issue. -/
theorem output_writer (hpre : Pre P L mem0) (hs : GlobalWrites.SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (ht : Frame.Tracked (Machine.code P L) X)
    {i : EvId} {x y k : Nat} {a : Acc} {bs : List Byte}
    (hm : X.MemWrites (.async i (.write (.store x y k))) a bs) :
    ∃ d : D, ∃ j : Fin 4,
      Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg0 d)) ∧
      d.site = .tmaStore j ∧ warpOf L i.1 < 2 ∧ x < 64 ∧ y < 64 ∧ k < 2 ∧ a.size = 1 ∧
      a.loc = (oLoc P (eOf L i.1) (qOf L i.1) y (tmaX j.val (warpOf L i.1) + x)).at k := by
  obtain ⟨_, _, _, _, hi, hloc, _, hsize, _⟩ := hm
  obtain ⟨d, j, hd, hj, hw, hx, hy, hk, hAddr⟩ := output_destination hpre hs hX ht hi hloc
  exact ⟨d, j, hd, hj, hw, hx, hy, hk, hsize, hAddr⟩

/-- The destination of a performed tensor load uses the shared address space. -/
theorem tensorLoad_shared
    (hX : Consistent L kernel Assumptions.all mem0 X) {i : EvId}
    {x y k : Nat} {a : Acc} {bs : List Byte}
    (hm : X.MemWrites (.async i (.write (.load x y k))) a bs) : a.loc.space = .shared := by
  obtain ⟨o, _, _, ho, _, hw, _⟩ := hm
  have hroute : TensorCopy.RoutingOk L (i.1 / L.block) o.spec := (hX.tensor _ _ ho).2.2.1
  have hsh : o.spec.sharedBase.space = .shared := hroute.2.1
  unfold TensorCopy.writeLoc at hw
  cases hk : TensorTransfer.slotAt o.spec.descriptor x y k with
  | none => simp [hk] at hw
  | some slot =>
    rw [hk, Option.map_some] at hw
    rw [← Option.some.inj hw]
    exact hsh

private theorem output_lookup_extent {coord : Fin 4 → Int} {k addr : Nat}
    (h : TensorAddress.lookup (TensorDescriptor.geometry
      (mapO P.outBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.oClass)) coord k =
        some addr) :
    P.outBase ≤ addr ∧ addr < P.outBase + tensorBytes P := by
  unfold TensorAddress.lookup at h
  split at h
  next hb =>
    obtain rfl := Option.some.inj h.symm
    obtain ⟨hColNonneg, hCol⟩ := hb.1 (0 : Fin 4)
    obtain ⟨hHeadNonneg, hHead⟩ := hb.1 (1 : Fin 4)
    obtain ⟨hQueryNonneg, hQuery⟩ := hb.1 (2 : Fin 4)
    obtain ⟨hBatchNonneg, hBatch⟩ := hb.1 (3 : Fin 4)
    change coord 0 < 512 at hCol
    change coord 1 < 64 at hHead
    change coord 2 < (P.s_q : Int) at hQuery
    change coord 3 < (P.b : Int) at hBatch
    have hCol' : (coord 0).toNat < 512 := by omega
    have hHead' : (coord 1).toNat < 64 := by omega
    have hQuery' : (coord 2).toNat < P.s_q := by omega
    have hBatch' : (coord 3).toNat < P.b := by omega
    have hk : k < 2 := hb.2
    have hRow := rowInRange hBatch' hQuery'
    have hAddress : TensorAddress.byteAddress (TensorDescriptor.geometry
        (mapO P.outBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.oClass)) coord k =
        P.outBase + 65536 * ((coord 3).toNat * P.s_q + (coord 2).toNat) +
          1024 * (coord 1).toNat + 2 * (coord 0).toNat + k := by
      simp [TensorAddress.byteAddress, TensorDescriptor.geometry, mapO, encodeTiled,
        Fin.sum_univ_succ, Fin.cases, TensorDescriptor.Format.bytes]
      ring
    rw [hAddress, show tensorBytes P = 65536 * (P.b * P.s_q) by unfold tensorBytes; ring]
    omega
  next => contradiction

private theorem output_descriptor_extent {s : TensorStore.Spec} {x y k : Nat} {l : Loc}
    (hDesc : (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
      ⟨3, mapO P.outBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.oClass⟩)
    (hLoc : TensorStore.writeLoc s x y k = some l) :
    P.outBase ≤ l.addr ∧ l.addr < P.outBase + tensorBytes P := by
  obtain ⟨⟨outer, descriptor, origin, sharedBase, rows⟩, reduce⟩ := s
  have hRank : outer = 3 := congrArg Sigma.fst hDesc
  subst outer
  have hd := eq_of_heq (Sigma.mk.inj hDesc).2
  change descriptor = mapO P.outBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.oClass at hd
  subst descriptor
  let d := mapO P.outBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.oClass
  let spec : TensorStore.Spec := ⟨⟨3, d, origin, sharedBase, rows⟩, reduce⟩
  change (TensorTransfer.slotAt d x y k).bind (TensorStore.destination spec) = some l at hLoc
  cases hSlot : TensorTransfer.slotAt d x y k with
  | none => simp [hSlot] at hLoc
  | some slot =>
    rw [hSlot, Option.bind_some] at hLoc
    let coord := TensorTransfer.coord d origin rows slot
    change (TensorAddress.lookup (TensorDescriptor.geometry d) coord slot.2.2.val).map
      (fun addr => ⟨.global, 0, addr⟩) = some l at hLoc
    cases hAddr : TensorAddress.lookup (TensorDescriptor.geometry d) coord slot.2.2.val with
    | none => simp [hAddr] at hLoc
    | some addr =>
      rw [hAddr, Option.map_some] at hLoc
      obtain rfl := Option.some.inj hLoc.symm
      exact output_lookup_extent hAddr

/-- Every actual global write stays inside O or LSE, regardless of numerical tracking. -/
theorem actual_global_write_range (hpre : Pre P L mem0) (hs : GlobalWrites.SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte} {l : Loc}
    (hm : X.MemWrites w a bs) (hc : a.Covers l) (hg : l.space = .global) :
    (P.outBase ≤ l.addr ∧ l.addr < P.outBase + tensorBytes P) ∨
      (P.lseBase ≤ l.addr ∧ l.addr < P.lseBase + lseBytes P) := by
  have hsp : a.loc.space = .global := hc.1.symm.trans hg
  cases w with
  | thread i =>
    rcases hm with he | ⟨_, hr⟩
    · obtain ⟨hlo, hhi⟩ := MachineTracking.actual_lse_extent hpre hX hs he hsp
      exact .inr ⟨hlo.trans hc.2.2.1, hc.2.2.2.trans_le hhi⟩
    · exact (GlobalWrites.no_rmw hX hr).elim
  | async i part =>
    cases part <;> try contradiction
    case writeCopy =>
      obtain ⟨_, hs', _⟩ := hm
      exact (GlobalWrites.no_copy hX hs').elim
    case writeElem =>
      obtain ⟨_, hs', _⟩ := hm
      exact (GlobalWrites.no_copy hX hs').elim
    case writeCta =>
      obtain ⟨_, _, hs', _⟩ := hm
      exact (GlobalWrites.no_clc hX hs').elim
    case writeLoad => exact (Space.noConfusion ((tensorLoad_shared hX hm).symm.trans hsp))
    case writeStore =>
      obtain ⟨o, _, _, _, hi, hLoc, _, hSize, _⟩ := hm
      obtain ⟨tag, hIssue⟩ := hi
      rw [Acc.loc_of_one hc hSize] at hLoc
      exact .inl (output_descriptor_extent
        (MachineTracking.actual_output_descriptor hpre hX hs hIssue rfl) hLoc)

/-- Every written global byte is inside either O or LSE. -/
theorem global_write_range (hpre : Pre P L mem0) (hs : GlobalWrites.SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (_ht : Frame.Tracked (Machine.code P L) X)
    {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte} {l : Loc}
    (hm : X.MemWrites w a bs) (hc : a.Covers l) (hg : l.space = .global) :
    (P.outBase ≤ l.addr ∧ l.addr < P.outBase + tensorBytes P) ∨
      (P.lseBase ≤ l.addr ∧ l.addr < P.lseBase + lseBytes P) :=
  actual_global_write_range hpre hs hX hm hc hg

/-- The final memory agrees with launch memory outside the two output tensors. -/
theorem global_frame (hpre : Pre P L mem0) (hs : GlobalWrites.SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (ht : Frame.Tracked (Machine.code P L) X)
    {m : FinalMem} (hm : IsFinal L mem0 X m) {l : Loc} (hg : l.space = .global)
    (ho : ¬ (P.outBase ≤ l.addr ∧ l.addr < P.outBase + tensorBytes P))
    (hl : ¬ (P.lseBase ≤ l.addr ∧ l.addr < P.lseBase + lseBytes P)) : m l = mem0 l := by
  obtain ⟨_, _, hfinal⟩ := hm
  apply (hfinal l).2.1
  intro w a bs hw hc
  exact (global_write_range hpre hs hX ht hw hc hg).elim ho hl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
