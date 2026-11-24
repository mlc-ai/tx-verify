-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Progress.Assembly
public import Kernels.FlashAttn4Fwd.Proof.Safety.Tensor
public import Kernels.FlashAttn4Fwd.Proof.Protocol.SmemElementsLoad
public import Kernels.FlashAttn4Fwd.Proof.ResultFacts
public import Kernels.FlashAttn4Fwd.Proof.Protocol.InitFirst
public import Lemmas.TensorStore.TensorStoreCompleteConsistentWriteBytes
public import Kernels.FlashAttn4Fwd.Proof.Protocol.QRingSlotSources
public import Kernels.FlashAttn4Fwd.Proof.Protocol.ValuesOperands
public import Kernels.FlashAttn4Fwd.Proof.Protocol.SmemElementsMma
public import Lemmas.Tensor.LoadWritten

@[expose] public section

/-! # The sources of the asynchronous operations

This file sits at the top of the proof tree, outside the layer order (as `ProgressFacts.lean`
does): it supplies the progress layer's asynchronous obligations (`Progress.AsyncSources`) with
the protocols' facts, from the thread layer's exports (`AsyncInputs`).

* **Tensor loads** (`tensorSources`). A load is a ring copy (`Safety.load_source`): slot
  `(x, y)`, byte `z` of its box reads byte `z` of an element of Q, K or V
  (`SmemElements.copy_readLoc`), which holds its launch content (`SmemElements.input_byte`) and
  lies outside O (`SmemElements.input_outside`). Every global write is a tensor store's write
  inside O (`Result.writes_within_output`), so no write covers the byte (`Result.frame`). The
  load is routed through a valid map (`ProgressAsyncFacts.copy_route`) and copies a ring
  barrier's bytes (`RingFacts.issue`).
* **Tensor stores** (`storeSources`). A store reads a staging byte of its item; the byte's row
  thread wrote it last in the item, and the write is visible to the store's read
  (`Output.item_source`, through the staging handoff `Output.outputHandoff`). Every write has a
  defined byte at each byte it covers: a thread's carries as many bytes as its footprint
  (`ProgressAsyncFacts.write_length`), an asynchronous write too
  (`Consistent.async_write_bytes`). The store is valid (`ProgressAsyncFacts.store_valid`) and
  plain (`StoreSrc`).
* **MMAs** (`mmaSources`). An MMA's shared operand byte lies in a Q or KV ring region
  (`ProgressAsyncFacts.mma_reads`); it was written by the copy of the read's use, a write visible
  to the read, and every other write of the byte is ordered around them
  (`Rings.read_source`). That copy is notified (`tensor_notified_of_modelCausality`), so it wrote
  the byte (`writeByte_of_notified`). One thread of a pair issues its MMAs (`ScoreFacts.tc_one`),
  with the QK or PV descriptor. A PV MMA reads A from the probabilities, below column 256, and every
  MMA of its accumulator writes the output accumulator, from column 256 (`aTmemApart`). An MMA
  writes output `(row, col)` at lane `row % 128` of the low or high CTA of its pair, column `col`
  past its address, so its layout is injective (`layoutInjective`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The bounds of a slot of a ring copy's box: 64 columns, `copyBytes / 128` rows, two bytes. -/
theorem copy_slot {g : Nat} {b : FBar} (hb : b.isFull) (cnt : Nat)
    (slot : TensorTransfer.Slot (copySpec P L g b cnt).descriptor) :
    slot.1.val < 64 ∧ slot.2.1.val < b.copyBytes / 128 ∧ slot.2.2.val < 2 := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩ := slot
  cases b with
  | qFull st =>
    simp [copySpec, copyMap, FlashAttn4Fwd.mapQ, FlashAttn4Fwd.encodeTiled, TensorTile.count,
      TensorTile.step, TensorTile.rows, TensorTile.rowsOf,
      TensorDescriptor.Format.bytes] at hx hy hz
    simp [FBar.copyBytes]
    omega
  | kvFull s =>
    by_cases hs : s.val % 2 = 0
    · simp [copySpec, copyMap, hs, FlashAttn4Fwd.mapK, FlashAttn4Fwd.encodeTiled,
        TensorTile.count, TensorTile.step, TensorTile.rows, TensorTile.rowsOf,
        TensorDescriptor.Format.bytes] at hx hy hz
      simp [FBar.copyBytes, hs]
      omega
    · simp [copySpec, copyMap, hs, FlashAttn4Fwd.mapV, FlashAttn4Fwd.encodeTiled,
        TensorTile.count, TensorTile.step, TensorTile.rows, TensorTile.rowsOf,
        TensorDescriptor.Format.bytes] at hx hy hz
      simp [FBar.copyBytes, hs]
      omega
  | _ => cases hb

/-- **The tensor loads' sources are fixed.** Each load is routed, through a valid map, of a
nonempty box, and each global byte it reads is an input byte with its launch content that no
write covers. -/
theorem tensorSources (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hi : AsyncInputs P L X) : TensorSources L mem0 X := by
  intro ⟨g, k⟩ addr s ⟨pc, he⟩
  have hg := Frame.lt_of_get hX he
  obtain ⟨hroute, hvalid⟩ := hi.progress.copy_route he
  obtain ⟨b, hfull, hm, hsp⟩ := Safety.load_source hX hi.rings hi.ringCopies hi.async he
  have hring : b.ring := by cases b <;> simp_all [FBar.isFull, FBar.ring]
  have hbytes := (hi.rings.issue hg he hm hring).2.2.2.2.1
  have hw := hi.async.copy_started hg he hm hfull
  refine ⟨hroute, hvalid, ?_, ?_⟩
  · rw [hbytes]
    cases b <;> simp only [FBar.isFull, Bool.false_eq_true] at hfull <;> simp [FBar.copyBytes]
    split_ifs <;> decide
  intro slot a hsrc
  set cnt := ((X.tr g).take k).countP (issuesTo (b.loc L (pairBase L g)))
  subst hsp
  obtain ⟨hx, hy, hz⟩ := copy_slot hfull cnt slot
  have hloc : TensorCopy.readLoc (copySpec P L g b cnt) slot.1.val slot.2.1.val slot.2.2.val =
      some ⟨.global, 0, a⟩ := by
    rw [TensorCopy.readLoc_source, TensorCopy.slotAt_self]
    simp [hsrc]
  obtain ⟨hbt, hhd, hr, hd, hl⟩ := SmemElements.copy_readLoc hpre hfull cnt hw hx hy hz
  rw [hloc] at hl
  rw [Option.some.inj hl]
  refine ⟨_, SmemElements.input_byte hpre hfull hbt hhd hr hd hz, ?_⟩
  exact Result.frame (Result.writes_within_output hpre (itemCoords hpre) hX hi.store hi.writes)
    rfl (SmemElements.input_outside hpre hfull hbt hhd hr hd hz)

/-- A write's byte at a byte it covers is defined, when the write carries as many bytes as its
footprint. -/
theorem wbyte_of_length {a : Acc} {bs : List Byte} {l : Loc} (hc : a.Covers l)
    (hlen : bs.length = a.size) : ∃ v, wbyte a bs l = some v := by
  obtain ⟨-, -, h1, h2⟩ := hc
  exact ⟨_, List.getElem?_eq_getElem (by omega)⟩

/-- **Every write has a defined byte at each byte it covers**: a thread's write carries as many
bytes as its footprint (FA4 makes no atomic), and so does an asynchronous write (FA4 issues no
linear copy). -/
theorem write_defined (hX : Consistent L kernel asms mem0 X) (hp : ProgressAsyncFacts L X)
    (htm : TmemFacts L X) {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte} {l : Loc}
    (hw : X.MemWrites w a bs) (hc : a.Covers l) : ∃ v, wbyte a bs l = some v := by
  cases w with
  | thread e =>
    rcases hw with ⟨pc, he⟩ | ⟨old, pc, he⟩
    · exact wbyte_of_length hc (hp.write_length he)
    · exact (htm.no_rmw he).elim
  | async i q =>
    refine wbyte_of_length hc (hX.async_write_bytes hw fun s hs => ?_)
    unfold AsyncCopy.issuedBy at hs
    split at hs
    · rename_i he
      exact (htm.no_bulk he).elim
    · cases hs

/-- **The tensor stores' staging bytes have visible sources.** Each store is valid and plain, and
each staging byte it reads was written last in its item by the byte's row thread, a write
visible to the store's read; every write has a defined byte. -/
theorem storeSources (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hi : AsyncInputs P L X) : Progress.StoreSources L X := by
  intro ⟨g, k⟩ addr s ⟨pc, he⟩
  have hg := Frame.lt_of_get hX he
  obtain ⟨h13, st, hst, hsrc⟩ := hi.output.store_tma hg he
  refine ⟨hi.progress.store_valid he, hsrc.1, fun slot loc _ => ⟨?_, ?_⟩⟩
  · have hl : TensorStore.readLoc s slot.1.val slot.2.1.val slot.2.2.val =
        some (s.sharedLoc slot) := by
      simp [TensorStore.readLoc, TensorCopy.slotAt_self]
    have hr : Output.rd L X (ctaOf L g) st (arrivals (freeBar L (ctaOf L g) st)
        ((X.tr g).take k)) (g, k) (slot.1.val, slot.2.1.val, slot.2.2.val) :=
      ⟨⟨hg, rfl, h13⟩, ⟨pc, addr, s, he, hsrc⟩, rfl⟩
    have hH := Output.outputHandoff hpre hX hi.output hi.tmem
      (InitFirst.outputInit hpre hX hi.cluster hi.tmem hi.init hi.output)
      (fun w _ _ _ _ _ hw => hi.rings.spins (Frame.lt_of_get hX hw) hw)
    obtain ⟨n, dst, bs, -, -, hso⟩ := Output.item_source hpre hX hi.output hH
      (stagingAsync hX hi.rings hi.output hi.tmem hi.progress.mma_reads) hst
      (hsrc.2.1 _ _ _ _ hl) hr
    obtain ⟨hw, hc, hv, -⟩ := hso (g, k) _ _ _ pc addr s hr he hl
    exact ⟨_, dst, bs, hw, hc, hv⟩
  · intro w a bs hw hc _
    exact write_defined hX hi.progress hi.tmem hw hc

/-! ### MMAs -/

/-- **The MMAs' output layouts are injective**: output `(row, col)` is at lane `row % 128` of
the pair's low CTA (`row < 128`) or high CTA, column `col` past the accumulator address. -/
theorem layoutInjective (hpre : Pre P L mem0) (hi : AsyncInputs P L X) :
    TcMma.LayoutInjective X := by
  intro i d s acc mask hmi row col row' col' cell h1 h2
  obtain ⟨-, hm, -, hg, -⟩ := TcMmaSources.mma_desc' hi.tcmma hmi
  obtain ⟨hlo, hhi, -⟩ := ValuesOps.mma_ctas hpre hi.score hi.tc hi.tcmma hmi
  obtain ⟨hr1, hc1, he1, -⟩ := TcMma.resultCell_pair hm hg (TcMma.writeCell_resultCell h1)
  obtain ⟨hr2, hc2, he2, -⟩ := TcMma.resultCell_pair hm hg (TcMma.writeCell_resultCell h2)
  rw [he1] at he2
  simp only [TcMma.rowCta, hlo, hhi, TcMma.Cell.mk.injEq] at he2
  obtain ⟨hcta, hlane, hcol⟩ := he2
  have hrow : row = row' := by split_ifs at hcta <;> omega
  exact ⟨hrow, by omega⟩

/-- **A PV MMA's cells**: an MMA reading A from Tensor Memory writes the output accumulator of a
stage, from its accumulator address on, which is at column 256 or later; it reads A from the
stage's probabilities. -/
theorem pv_cells (hi : AsyncInputs P L X) {j : EvId} {d : Nat} {s : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} (hj : X.MmaIssue j d s acc mask) (ha : s.aTmem.isSome = true) :
    256 ≤ d % 2 ^ 16 ∧
      ∃ st < 2, ∀ index c pos, TcMma.aCell s index = some (c, pos) → InP st c := by
  obtain ⟨-, hm, -, hg, -⟩ := TcMmaSources.mma_desc' hi.tcmma hj
  obtain ⟨c0, hc0⟩ := hi.tc.mma_cell hj
  obtain ⟨-, -, -, st, hst, hS | hO⟩ := hi.score.mma_cells hj
  · have := hi.tc.qk_smem hst hj hc0 (hS c0 hc0).1
    simp [this] at ha
  have hpv := (hi.score.pv_polls hj hc0 (hO c0 hc0).1).2.2.2
  refine ⟨?_, st, hst, fun index c pos h => (hpv index c pos h).1⟩
  obtain ⟨d', s', acc', mask', row, col, hj', hw⟩ := hc0
  obtain ⟨rfl, rfl, -, -⟩ := TcMma.mmaIssue_params hj hj'
  obtain ⟨-, -, -, hall⟩ := TcMma.resultCell_pair hm hg (TcMma.writeCell_resultCell hw)
  have hn : 0 < s.descriptor.n := by rw [(TcMmaSources.mma_desc' hi.tcmma hj).2.2.1]; decide
  have h0 := (hO _ (hi.tc.mma_reads hj (hall 0 hn))).1
  simp only [InO] at h0
  omega

/-- **No MMA reads a Tensor Memory A cell its accumulator's MMAs write**: a PV MMA reads the
probabilities, below column 256, and an MMA with its accumulator writes from its accumulator
address on, at column 256 or later. -/
theorem aTmemApart (hi : AsyncInputs P L X) : TcMma.ATmemApart X := by
  intro j d s acc mask hj index cell pos hac w d' s' acc' mask' row col hw hsame hwc
  have ha : s.aTmem.isSome = true := by
    unfold TcMma.aCell at hac
    cases h : s.aTmem <;> simp_all
  obtain ⟨hbase, st, hst, hP⟩ := pv_cells hi hj ha
  have hp := hP index cell pos hac
  obtain ⟨-, hm, -, hg, -⟩ := TcMmaSources.mma_desc' hi.tcmma hw
  obtain ⟨-, -, he, -⟩ := TcMma.resultCell_pair hm hg (TcMma.writeCell_resultCell hwc)
  obtain ⟨rfl, -⟩ := hsame
  rw [he] at hp
  simp only [InP] at hp
  omega

/-- **The MMAs' shared operand bytes have ordered sources.** One thread of a pair issues its
MMAs, each with the valid QK or PV descriptor; a shared operand byte lies in a ring region, and
the copy of the read's use wrote it (the copy is notified, since its write is visible to the
read), with every other write of the byte ordered around them. -/
theorem operandSourcesT (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hi : AsyncInputs P L X) : OperandSourcesT L X := by
  refine ⟨fun {i j} ⟨d, s, acc, mask, hmi⟩ ⟨d', s', acc', mask', hmj⟩ hsw => ?_,
    fun i d sp acc mask hmi => ⟨?_, ?_⟩⟩
  · refine hi.score.tc_one ⟨d, s, acc, mask, hmi⟩ (.inl ⟨d', s', acc', mask', hmj⟩) ?_
    have := hsw.1.2.2
    simp only [leadCta, ctaOf, this]
  · cases ha : sp.aTmem with
    | none =>
      rw [SmemElements.qkDesc_eq ((hi.tcmma.mma_desc hmi).2.1 ha)]
      exact SmemElements.qkDesc_valid
    | some _ =>
      rw [SmemElements.pvDesc_eq ((hi.tcmma.mma_desc hmi).2.2 (by simp [ha]))]
      exact SmemElements.pvDesc_valid
  intro isB k loc hfp
  obtain ⟨gm, km⟩ := i
  have hcov : AsyncCovers X (gm, km) (.mmaRead isB k) loc :=
    ⟨{ loc := loc, size := 1 }, false, ⟨rfl, rfl, hfp⟩, ⟨rfl, rfl, le_rfl, Nat.lt_succ_self _⟩⟩
  have hsh : loc.space = .shared := by
    rcases hfp with ⟨_, _, _, _, _, hbl⟩ | ⟨c, -, -, hcp, -⟩
    · exact TcMma.OperandSpec.byteLoc_shared hbl
    · exact (hi.score.no_cp _ c hcp).elim
  obtain ⟨c, b, hb, hl⟩ := hi.progress.mma_reads _ isB k loc hcov hsh
  have hinit := InitFirst.ringInit hpre hX hi.cluster hi.tmem hi.init hi.rings
  obtain ⟨gl, kl, pc, al, x, y, z, hget, hcta, -, hwl, hvis, hord⟩ :=
    Rings.read_source hpre hX hi.rings hi.tmem hinit hi.ringCopies hb hl hcov
  set cnt := ((X.tr gl).take kl).countP (issuesTo (b.loc L (2 * (c / 2))))
  obtain ⟨o, ho, hnot⟩ := tensor_notified_of_modelCausality hvis
  obtain ⟨⟨addr', pc', he'⟩, -⟩ := hX.tensor (gl, kl) o ho
  have hspec : o.spec = copySpec P L gl b cnt := by
    rw [hget] at he'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at he'
    exact he'.2.2.symm
  obtain ⟨slot, hs, -⟩ := Option.map_eq_some_iff.mp hwl
  obtain ⟨rfl, rfl, rfl⟩ := TensorCopy.slotAt_coordinates hs
  obtain ⟨hx, hy, hz⟩ := copy_slot hb cnt slot
  have hgl := Frame.lt_of_get hX hget
  have hm : (copySpec P L gl b cnt).mbar = b.loc L (2 * (c / 2)) := by
    simp only [copySpec, pairBase, hcta]
  have hw := hi.async.copy_started hgl hget hm hb
  obtain ⟨-, -, -, -, hrl⟩ := SmemElements.copy_readLoc hpre hb cnt hw hx hy hz
  obtain ⟨v, hv⟩ := writeByte_of_notified hX ho hnot (by rw [hspec]; exact hrl)
  refine ⟨⟨loc, .async (gl, kl) (.write (.load slot.1.val slot.2.1.val slot.2.2.val)),
    { loc := loc, size := 1 }, [v], ⟨o, addr', v, ho, ⟨pc', he'⟩, by rw [hspec]; exact hwl, hv,
      rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, le_rfl, Nat.lt_succ_self _⟩⟩, rfl, hord⟩

/-- **The sources of the asynchronous operations** of every maximal execution, from the thread
layer's exports (`Progress.Remaining.async`). -/
theorem asyncSources (hpre : Pre P L mem0) (hR : Progress.Remaining L mem0) :
    Progress.AsyncSources L mem0 where
  tensor X hmax := tensorSources hpre hmax.1 (hR.async P X hpre hmax.1)
  store X hmax := storeSources hpre hmax.1 (hR.async P X hpre hmax.1)
  mma X hmax := ⟨operandSourcesT hpre hmax.1 (hR.async P X hpre hmax.1),
    aTmemApart (hR.async P X hpre hmax.1), layoutInjective hpre (hR.async P X hpre hmax.1)⟩

end

end PTX.Kernels.FlashAttn4Fwd.Proof
