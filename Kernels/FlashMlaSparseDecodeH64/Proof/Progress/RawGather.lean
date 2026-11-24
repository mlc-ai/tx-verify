-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressTensor
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmRawInput
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RawGatherTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Geometry.Maps

public section

/-! # Sources for pending gather4 transfers -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
open PTX PTX.Flow Result

/-- Any in-bounds source of a raw gather is a byte of the corresponding cache row. -/
private theorem gather_source {base blocks stride : Nat} {cls : TensorDescriptor.AllocationClass}
    {dst : Loc} {oy : Int} {rows : Fin 4 → Int}
    (s : TensorTransfer.Slot (RawGather.box base blocks stride cls dst oy rows).descriptor)
    {address : Nat}
    (ha : (RawGather.box base blocks stride cls dst oy rows).globalAddress s = some address) :
    ∃ row : Fin 4, ∃ x : Fin 144, ∃ b : Fin 4, ∃ r : Nat,
      rows row = r ∧ r < blocks * (stride / 528) ∧ x.val < 132 ∧
        address = base + r * 528 + 4 * x.val + b.val := by
  have hx : TensorTile.count (encodeKv base blocks stride cls).fourRows.box 0 = 144 := by
    simp [encodeKv, TensorDescriptor.Descriptor.fourRows, TensorTile.count, TensorTile.step]
  have hy : TensorTile.rows (encodeKv base blocks stride cls).fourRows.box = 4 := by
    simp [encodeKv, TensorDescriptor.Descriptor.fourRows, TensorTile.rows, TensorTile.rowsOf,
      TensorTile.count, TensorTile.step]
  obtain ⟨x, row, b⟩ := s
  let x' : Fin 144 := ⟨x.val, hx ▸ x.isLt⟩
  let row' : Fin 4 := ⟨row.val, hy ▸ row.isLt⟩
  let b' : Fin 4 := ⟨b.val, b.isLt⟩
  change (RawGather.box base blocks stride cls dst oy rows).globalAddress
    (RawGather.slot base blocks stride cls row' x' b') = some address at ha
  have hcoord :
      let t := RawGather.box base blocks stride cls dst oy rows
      TensorTransfer.coord t.descriptor t.origin t.rows
        (RawGather.slot base blocks stride cls row' x' b') =
          ![(x'.val : Int), rows row'] := by
    funext i
    have hmod : row'.val % 4 = row'.val := Nat.mod_eq_of_lt row'.isLt
    fin_cases i <;> simp [RawGather.box, TensorTransfer.coord, RawGather.slot, hmod]
  have hin :
      TensorAddress.InBounds (TensorDescriptor.geometry (encodeKv base blocks stride cls).fourRows)
        ![(x'.val : Int), rows row'] := by
    unfold TensorBox.globalAddress TensorTransfer.globalAddress at ha
    rw [hcoord] at ha
    unfold TensorAddress.lookup at ha
    split at ha
    · exact (by assumption :
        TensorAddress.InBounds (TensorDescriptor.geometry
          (encodeKv base blocks stride cls).fourRows) ![(x'.val : Int), rows row'] ∧ _).1
    · cases ha
  have hrow := hin (1 : Fin 2)
  have hcol := hin (0 : Fin 2)
  simp only [TensorDescriptor.geometry, TensorDescriptor.Descriptor.fourRows, encodeKv,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hrow hcol
  have hrows : rows row' = ((rows row').toNat : Int) := by omega
  have hrlt : (rows row').toNat < blocks * (stride / 528) := by omega
  have hxlt : x'.val < 132 := by omega
  have hactual := RawGather.globalAddress (base := base) (cls := cls)
    dst oy rows row' x' b' hrows hrlt hxlt
  exact ⟨row', x', b', (rows row').toNat, hrows, hrlt, hxlt,
    Option.some.inj (ha.symm.trans hactual)⟩

private theorem valid_fourRows {outer : Nat} {d : TensorDescriptor.Descriptor outer}
    (h : TensorDescriptor.Valid d) : TensorDescriptor.Valid d.fourRows := by
  obtain ⟨hrank, hbase, hextent, hstride, hsize, htrav, hbytes, hsw, hfill, hfirst⟩ := h
  refine ⟨hrank, hbase, hextent, hstride, ?_, ?_, hbytes, hsw, hfill, hfirst⟩
  · intro axis
    change 0 < (if axis.val = 1 then 4 else d.box.size axis) ∧
      (if axis.val = 1 then 4 else d.box.size axis) ≤ 256
    split <;> first | decide | exact hsize axis
  · intro axis
    change 0 < (if axis.val = 1 then 1 else d.box.traversal axis) ∧
      (if axis.val = 1 then 1 else d.box.traversal axis) ≤ 8
    split <;> first | decide | exact htrav axis

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem tensor_input_of_box {i : EvId} {s : TensorCopy.Spec} {base blocks stride : Nat}
    {cls : TensorDescriptor.AllocationClass} {dst : Loc} {oy : Int} {rows : Fin 4 → Int}
    (hpre : Pre P L mem0) (hs : GlobalWrites.SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (_ht : Frame.Tracked (Machine.code P L) X)
    (hb : s.toTensorBox = RawGather.box base blocks stride cls dst oy rows)
    (hroute : TensorCopy.RoutingOk L (i.1 / L.block) s)
    (hvalid : TensorDescriptor.Valid (encodeKv base blocks stride cls))
    (hsize : 0 < TensorTransfer.bytes s.descriptor)
    (hO : base + cacheBytes blocks stride ≤ P.outBase ∨ P.outBase + tensorBytes P ≤ base)
    (hLse : base + cacheBytes blocks stride ≤ P.lseBase ∨ P.lseBase + lseBytes P ≤ base)
    (hmem : ∀ r < blocks * (stride / 528), ∀ k < 528,
      ∃ value, mem0 ⟨.global, 0, base + r * 528 + k⟩ = some (some value)) :
    TensorInput L mem0 X i s := by
  rcases s with ⟨box, _, _, _⟩
  dsimp only at hb
  subst box
  refine ⟨hroute, valid_fourRows hvalid, hsize, ?_⟩
  intro slot address ha
  unfold TensorCopy.source at ha
  split at ha
  · rename_i address' haddr
    obtain rfl := TensorTransfer.Source.global.inj ha
    obtain ⟨row, x, b, r, _, hr, hx, rfl⟩ := gather_source slot haddr
    obtain ⟨value, hval⟩ := hmem r hr (4 * x.val + b.val) (by have := b.isLt; omega)
    exact ⟨value, by simpa only [Nat.add_assoc] using hval,
      RawGather.cacheByte_noWrite hpre hs hX x b hr hx hO hLse⟩
  · cases ha

/-- A pending main-cache gather with its identified actual box can advance its transfer. -/
theorem main_gather_extension {i : EvId} {addr : Nat} {s : TensorCopy.Spec} {dst : Loc} {oy : Int}
    {rows : Fin 4 → Int} (hpre : Pre P L mem0) (hs : GlobalWrites.SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.TensorIssue i addr s)
    (hb : s.toTensorBox = RawGather.box P.kvBase P.numBlocks P.blockStride P.kvClass dst oy rows)
    (hroute : TensorCopy.RoutingOk L (i.1 / L.block) s)
    (hsize : 0 < TensorTransfer.bytes s.descriptor)
    (hn : (X.tensor i).any (fun old => old.effects.notified) = false) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  pending_tensor_extension hX hi (tensor_input_of_box hpre hs hX ht hb hroute
    (Geometry.mapKv_valid_of_pre hpre) hsize hpre.kvApartO hpre.kvApartLse
    (fun r hr k hk => ⟨_, hpre.kvInput r hr k hk⟩)) hn

/-- A pending extra-cache gather with its identified actual box can advance its transfer. -/
theorem extra_gather_extension {i : EvId} {addr : Nat} {s : TensorCopy.Spec} {dst : Loc} {oy : Int}
    {rows : Fin 4 → Int} (hpre : Pre P L mem0) (hs : GlobalWrites.SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.TensorIssue i addr s) (hextra : P.extra_topk ≠ 0)
    (hb : s.toTensorBox =
      RawGather.box P.extraKvBase P.extraNumBlocks P.extraBlockStride P.extraKvClass dst oy rows)
    (hroute : TensorCopy.RoutingOk L (i.1 / L.block) s)
    (hsize : 0 < TensorTransfer.bytes s.descriptor)
    (hn : (X.tensor i).any (fun old => old.effects.notified) = false) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  pending_tensor_extension hX hi (tensor_input_of_box hpre hs hX ht hb hroute
    (Geometry.mapExtraKv_valid_of_pre hpre hextra) hsize
    (hpre.extraKvApartO.resolve_left hextra) (hpre.extraKvApartLse.resolve_left hextra)
    (fun r hr k hk => ⟨_, hpre.extraKvInput r hr k hk⟩)) hn

/-- A gather at its actual TMA role site can advance while its notification is pending. -/
theorem raw_gather_extension {g j addr : Nat} {s : TensorCopy.Spec} {d : Wg1Tma.D} {k : Fin 16}
    (hpre : Pre P L mem0) (hs : GlobalWrites.SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.TensorIssue (g, j) addr s)
    (hst : Frame.stateAt (Machine.code P L) X g j = some (some (.tma d))) (hd : d.site = .issue k)
    (hn : (X.tensor (g, j)).any (fun old => old.effects.notified) = false) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨hroute, hsize, rows, hx, hr, hmain | ⟨hextra, hex⟩⟩ :=
    RawGatherTrace.gather_operands hpre hs hX hst hd hi.choose_spec rfl
  · obtain ⟨y, hbox⟩ := RawGather.canonicalBox hmain hx hr
    exact main_gather_extension hpre hs hX ht hi hbox hroute (by omega) hn
  · obtain ⟨y, hbox⟩ := RawGather.canonicalBox hex hx hr
    exact extra_gather_extension hpre hs hX ht hi hextra hbox hroute (by omega) hn

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
