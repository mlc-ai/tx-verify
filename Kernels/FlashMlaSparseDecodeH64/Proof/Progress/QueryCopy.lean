-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Interface.Assumptions
public import Lemmas.Tcgen05.MmaSources
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmQuery
public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.QueryCopyInputs
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreSources
import Lemmas.Kernel.Frame
import Lemmas.Tcgen05.TcReadFinishCp

public section

/-! # Tensor Memory copies in the query prefix -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
open PTX AsyncCopy MmaSources MmaDataTrace Wg1Mma Result

private theorem cp_not_mma {X : Execution} {i : EvId} {c : TcCopy.Spec}
    (hi : X.CpIssue i c) {d : Nat} {s : TcMma.OperandSpec} {a : Bool} {ms : List Nat}
    (hm : X.MmaIssue i d s a ms) : False := by
  obtain ⟨_, h⟩ := hi
  obtain ⟨_, h'⟩ := hm
  rw [h] at h'
  cases h'

private theorem copy_footprint_bound {X : Execution} {i : EvId} {c : TcCopy.Spec}
    (hi : X.CpIssue i c) {isB : Bool} {k : Nat} {l : Loc}
    (h : X.MmaFootprint i isB k l) :
    isB = false ∧ k < c.ctas.length * c.shape.sourceBytes := by
  rcases h with ⟨_, _, _, _, hm, _⟩ | ⟨c', n, cta, hc, hb, hcta, hdiv, _⟩
  · exact (cp_not_mma hi hm).elim
  · have he := Kind.tc.inj (congrArg Event.kind
      (Option.some.inj (hi.choose_spec.symm.trans hc.choose_spec)))
    obtain rfl := TcKind.cp.inj he
    refine ⟨hb, ?_⟩
    have hlt := (List.getElem?_eq_some_iff.mp hcta).1
    have hp : 0 < c.shape.sourceBytes := by
      cases c.shape <;> simp [TcCpShape.sourceBytes, TcCpShape.rows, TcCpShape.rowBytes]
    apply (Nat.div_lt_iff_lt_mul hp).mp
    exact hdiv ▸ hlt

private theorem query_copy_extension_with_read_frame {L : Launch} {mem0 : Mem0} {X : Execution}
    {i : EvId} {c : TcCopy.Spec}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hi : X.CpIssue i c)
    (hn : X.async.mmaOperands i = none) (hd : X.async.mmaDone i = false)
    (hguarded : SyncGuarded L kernel X)
    (hread : ∀ (v : MmaOperands) (ra rb : Nat → Option Ref),
      TcMma.ReadOk L Assumptions.all (X.finishMma i v ra rb))
    (source : Fin (c.ctas.length * c.shape.sourceBytes) → ByteSource X)
    (hfoot : ∀ k, X.MmaFootprint i false k.val (source k).loc)
    (horder : ∀ k w a bs, X.MemWrites w a bs → a.Covers (source k).loc →
      w = (source k).ref ∨ modelCausality L X (source k).loc w (source k).ref ∨
        modelCausality L X (source k).loc (.async i (.mmaRead false k.val)) w) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  let n := c.ctas.length * c.shape.sourceBytes
  let bytes : (isB : Bool) → Fin (if isB then 0 else n) → ByteSource X
    | false => source
    | true => Fin.elim0
  have hfoot' (isB : Bool) (k : Fin (if isB then 0 else n)) :
      X.MmaFootprint i isB k.val (bytes isB k).loc := by
    cases isB
    · exact hfoot k
    · exact Fin.elim0 k
  have hbound {isB k l} (hf : X.MmaFootprint i isB k l) :
      k < if isB then 0 else n := by
    obtain ⟨rfl, hlt⟩ := copy_footprint_bound hi hf
    exact hlt
  let v := newOperands bytes
  let ra := newSource bytes false
  let rb := newSource bytes true
  have hle : X.le (X.finishMma i v ra rb) := le_finishMma_unstarted hn
  have hready : TcMma.CompletionReady L X i := by
    intro j hj
    obtain ⟨_, _, _, ⟨_, _, _, _, _, _, _, _, _, hm, _⟩, _⟩ :=
      TcMma.completionPrecedes_iff.mp hj
    exact (cp_not_mma hi hm).elim
  have hov : Hidden L (X.finishMma i v ra rb) := by
    apply newOperands_hidden hX hguarded bytes hle hd hfoot' (fun _ _ _ => hbound)
    intro isB k w a bs hw hc
    cases isB
    · exact horder k w a bs hw hc
    · exact Fin.elim0 k
  have hlength := (newOperands_lengths bytes).1
  have hempty : v.b = [] := List.length_eq_zero_iff.mp (newOperands_lengths bytes).2
  refine ⟨_, consistent_finishCp hX hi hd hready hlength hempty
    (newOperands_rf hX bytes hle hfoot') (finishMma_noFuture hX hle hd) hov
    (hread v ra rb) (Interface.all_wf_effects hX hle rfl rfl rfl), hle, ?_⟩
  exact finishMma_size (Frame.lt_of_get hX hi.choose_spec) (len_of_get hi.choose_spec) hd

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem notified_tile_source {g : Nat} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hX : Consistent L kernel Assumptions.all mem0 X) {event : EvId} {tile : Fin 8}
    {o : TensorCopy.Observation} (ho : X.tensor event = some o)
    (hi : X.TensorIssue event (P.param1Base + qMapOff) o.spec)
    (hs : o.spec = queryTmaSpec P L g tile) (hn : o.effects.notified = true) (x h : Fin 64)
    (b : Fin 2) :
    ∃ source : ByteSource X, source.ref = .async event (.write (.load x.val h.val b.val)) ∧
      source.loc = (queryTmaSpec P L g tile).toTensorBox.sharedLoc
        (queryTileSlot P L g tile x h b) := by
  let s := queryTileSlot P L g tile x h b
  have hslot :
      TensorTransfer.slotAt (queryTmaSpec P L g tile).descriptor x.val h.val b.val = some s := by
    unfold TensorTransfer.slotAt
    simp [(queryTile_shape P L g tile).1, (queryTile_shape P L g tile).2.1,
      (queryTile_shape P L g tile).2.2, x.isLt, h.isLt, b.isLt, s, queryTileSlot]
  obtain ⟨address, hsrc, _⟩ := queryTile_initial hpre hg tile x h b
  obtain ⟨slot, hs', hsrc'⟩ : ∃ slot,
      TensorTransfer.slotAt o.spec.descriptor x.val h.val b.val = some slot ∧
        TensorCopy.source o.spec slot = .global address := by
    rw [hs]
    exact ⟨s, hslot, hsrc⟩
  have hok := (hX.tensor _ _ ho).2.1
  obtain ⟨content, hcontent⟩ := hok.complete hn slot
  have hc := hok.writes slot content hcontent
  rw [hsrc'] at hc
  obtain ⟨value, _, rfl⟩ := hc
  let l := (queryTmaSpec P L g tile).toTensorBox.sharedLoc s
  have hl : TensorCopy.writeLoc o.spec x.val h.val b.val = some l := by
    rw [hs, TensorCopy.writeLoc, hslot]
    rfl
  have hval : TensorCopy.writeByte o x.val h.val b.val = some value := by
    simp [TensorCopy.writeByte, hs', hcontent, TensorCopy.Content.byte]
  have hwrite : X.MemWrites (.async event (.write (.load x.val h.val b.val)))
      { loc := l, size := 1 } [value] :=
    ⟨_, _, _, ho, hi, hl, hval, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hcover : ({ loc := l, size := 1 } : Acc).Covers l :=
    ⟨rfl, rfl, Nat.le_refl _, Nat.lt_succ_self _⟩
  exact ⟨⟨l, _, _, _, hwrite, hcover⟩, rfl, rfl⟩

private theorem query_copy_from_tiles_with_read_frame {g : Nat} {i : EvId} {issue : Fin 16}
    (hpre : Pre P L mem0) (hg : g < L.threads) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hi : X.CpIssue i (queryCopySpec L g issue)) (hn : X.async.mmaOperands i = none)
    (hd : X.async.mmaDone i = false) (hguarded : SyncGuarded L kernel X)
    (hread : ∀ (v : MmaOperands) (ra rb : Nat → Option Ref),
      TcMma.ReadOk L Assumptions.all (X.finishMma i v ra rb)) (tma : Fin 8 → EvId)
    (obs : Fin 8 → TensorCopy.Observation) (hobs : ∀ t, X.tensor (tma t) = some (obs t))
    (hspec : ∀ t, (obs t).spec = queryTmaSpec P L g t)
    (hissue : ∀ t, X.TensorIssue (tma t) (P.param1Base + qMapOff) (obs t).spec)
    (hdone : ∀ t, (obs t).effects.notified = true)
    (hunique : ∀ (tile : Fin 8) (x h : Fin 64) (b : Fin 2) (source : ByteSource X),
      source.ref = .async (tma tile) (.write (.load x.val h.val b.val)) →
      source.loc = (queryTmaSpec P L g tile).toTensorBox.sharedLoc
        (queryTileSlot P L g tile x h b) →
      ∀ w a bs, X.MemWrites w a bs → a.Covers source.loc → w = source.ref) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  classical
  let c := queryCopySpec L g issue
  let nBytes := c.ctas.length * c.shape.sourceBytes
  have hwidth : (queryCopySpec L g issue).shape.sourceBytes = 4096 := by
    norm_num [queryCopySpec, TcCpShape.sourceBytes, TcCpShape.rows, TcCpShape.rowBytes]
  have hBytes : nBytes = 4096 := by
    simp [nBytes, c, hwidth, show (queryCopySpec L g issue).ctas.length = 1 from rfl]
  have bytes : ∀ n : Fin nBytes, ∃ source : ByteSource X,
      X.MmaFootprint i false n.val source.loc ∧
        ∀ w a bs, X.MemWrites w a bs → a.Covers source.loc → w = source.ref := by
    intro n
    have hlt : n.val < 4096 := hBytes ▸ n.isLt
    let row : Fin 128 := ⟨n.val / 32, by omega⟩
    let k : Fin 16 := ⟨n.val % 32 / 2, by omega⟩
    let b : Fin 2 := ⟨n.val % 2, by omega⟩
    have hn' : 2 * (row.val * 16 + k.val) + b.val = n.val := by
      dsimp [row, k, b]
      omega
    obtain ⟨tile, x, h, _, _, hbyte⟩ := queryCopy_tmaSlot hpre g issue row k b
    obtain ⟨source, hr, hl⟩ :=
      notified_tile_source hpre hg hX (hobs tile) (hissue tile) (hspec tile) (hdone tile) x h b
    refine ⟨source, .inr ⟨queryCopySpec L g issue, 0, ctaOf L g, hi, rfl, rfl, ?_, ?_⟩, ?_⟩
    · rw [hwidth]
      exact Nat.div_eq_of_lt hlt
    · rw [hl]
      have hmod : n.val % (queryCopySpec L g issue).shape.sourceBytes = n.val := by
        rw [hwidth]
        exact Nat.mod_eq_of_lt hlt
      rw [hmod, ← hn']
      exact hbyte
    · exact hunique tile x h b source hr hl
  let source : Fin nBytes → ByteSource X := fun n => (bytes n).choose
  exact query_copy_extension_with_read_frame hX hi hn hd hguarded hread source
    (fun n => (bytes n).choose_spec.1)
    (fun n w a bs hw hc => .inl ((bytes n).choose_spec.2 w a bs hw hc))

/-- An actual query copy whose operands have not been captured can finish from the notified
TMA tiles, including when other CTAs already have Tensor Memory readers. -/
theorem query_copy_pending_extension {g i : Nat} {chunk : Fin 16} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.CpIssue (g, i) (queryCopySpec L g chunk)) (hn : X.async.mmaOperands (g, i) = none)
    (hd : X.async.mmaDone (g, i) = false) (hguarded : SyncGuarded L kernel X) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  classical
  have hg := Frame.lt_of_get hX hi.choose_spec
  let tileInfo := query_copy_tiles_observed hpre hX hs ht hi
  let index (tile : Fin 8) := (tileInfo tile).choose
  let obs (tile : Fin 8) := (tileInfo tile).choose_spec.choose
  have facts (tile : Fin 8) : X.tensor (g, index tile) = some (obs tile) ∧
      (obs tile).spec = queryTmaSpec P L g tile ∧
      X.TensorIssue (g, index tile) (P.param1Base + qMapOff) (obs tile).spec ∧
      (obs tile).effects.notified = true := (tileInfo tile).choose_spec.choose_spec
  have hRead (v : MmaOperands) (ra rb : Nat → Option Ref) :
      TcMma.ReadOk L Assumptions.all (X.finishMma (g, i) v ra rb) := by
    apply TcMma.ReadOk.finishCp hX.tcRead hi
    · intro e s he
      exact Wg0ScoreSources.no_shift_issue hpre hX hs ht he
    · intro e addr vals shape hLoad l
      exact Protocol.QueryCopy.no_load_source_of_incomplete hi hX.tcCommit hd hLoad l
    · intro e dst sp accum mask hMma l
      exact Protocol.QueryCopy.no_a_source_of_incomplete hpre hX hs ht hi hd l
  apply query_copy_from_tiles_with_read_frame hpre hg hX hi hn hd hguarded hRead
    (fun tile => (g, index tile)) obs
    (fun tile => (facts tile).1) (fun tile => (facts tile).2.1)
    (fun tile => (facts tile).2.2.1) (fun tile => (facts tile).2.2.2)
  intro tile x h b source hRef _ w a bs hw hCover
  have hTile := (facts tile).2.2.1
  rw [(facts tile).2.1] at hTile
  have hWrite := source.write
  rw [hRef] at hWrite
  exact (query_copy_tile_unique hpre hX hs ht hi hd tile hTile hWrite source.cover hw hCover).trans
    hRef.symm

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
