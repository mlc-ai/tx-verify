-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvProbabilityOldWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvProbabilityLaterWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaAccessWindow
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ProbabilityUnique
public import Lemmas.Tcgen05.MmaSources
import Lemmas.Tcgen05.MmaObservedReads
import Lemmas.Tcgen05.TcMmaACell
import Lemmas.Order.Order
import Lemmas.Tensor.TensorSwizzle
import Lemmas.TensorStore.StoreWrite

@[expose] public section

/-! # Ordering writes of the shared probability tile against pending PV operand reads -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.PvProbabilityConflicts

open PTX PTX.Flow AsyncCopy MmaSources MmaDataTrace Protocol.PvProbabilitySource

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem later_store {g i s t index : Nat} {d : Wg1Mma.D} {q : Wg0.D}
    {issue : Fin 8} {a : Acc} {bytes : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.MmaIssue (g, i) (Wg1Mma.pvDest issue) (pvOperands L g d.i issue)
      (pvAccum d.i issue) [0, 0, 0, 0])
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .pvMma issue) (hFoot : X.MmaFootprint (g, i) false index l)
    (hw : X.Writes (s, t) a bytes) (hCover : a.Covers l) (hSh : l.space = .shared)
    (hq : Frame.stateAt (Machine.code P L) X s t = some (some (.wg0 q)))
    (hqSite : (∃ k : Fin 8, q.site = .exchStore k) ∨ ∃ k : Fin 4, q.site = .pStore k)
    (hBlock : d.i < q.block) (hCta : ctaOf L g = ctaOf L s) :
    ByteCausality L X l (.async (g, i) (.mmaRead false index)) (.thread (s, t)) := by
  obtain ⟨_, wait, hlt, hFinish⟩ :=
    prior_pv_read_finished (index := index) hpre hX hs ht hi hd hsite hBlock
      hw.choose_spec hq hqSite hCta
  have hGet : ∃ wt m parity scope, X.get (s, wait) = some ⟨wt, .wait m parity true true scope⟩ := by
    rcases hFinish with ⟨kind, hp, _⟩ | ⟨scope, ⟨_, m, _, htObs⟩, _⟩
    · cases kind with
      | cpAsync => cases hp
      | bulk mode => cases mode <;> cases hp
    · obtain ⟨wt, parity, hGet⟩ := htObs.1
      exact ⟨wt, m, parity, scope, hGet⟩
  obtain ⟨wt, m, parity, scope, hGet⟩ := hGet
  have hPo : po X (s, wait) (s, t) := po_of_source_not_access rfl hlt
    (PTX.len_of_get hw.choose_spec) (by rw [hGet]; rfl)
  exact completed_mma_source_before_store hi hFoot hFinish rfl hlt (.single (.inl hPo))
    hSh hw hCover

/-- The selected probability store has the exact footprint byte. Every other cover is
an earlier store or follows the corresponding PV read. -/
theorem operand_source {g i : Nat} {d : Wg1Mma.D} {issue : Fin 8}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.MmaIssue (g, i) (Wg1Mma.pvDest issue) (pvOperands L g d.i issue)
      (pvAccum d.i issue) [0, 0, 0, 0])
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .pvMma issue) (row : Fin 128) (k : Fin 16) (b : Fin 2)
    :
    let l : Loc := ⟨.shared, ctaOf L g, pLinearByte L (row.val % 64) (pvSlot issue k) b.val⟩
    let reader : Ref := .async (g, i) (.mmaRead false (2 * (row.val * 16 + k.val) + b.val))
    ∃ src : ByteSource X, src.loc = l ∧
      (∃ e, src.ref = .thread e ∧ ProxyBefore L X e (g, i) l) ∧
      ∀ other a bytes, X.MemWrites other a bytes → a.Covers l →
        (∃ e f, other = .thread e ∧ src.ref = .thread f ∧ baseCausality L X e f) ∨
        other = src.ref ∨ ByteCausality L X l reader other := by
  let slot : Fin 64 := ⟨pvSlot issue k, by unfold pvSlot; omega⟩
  let h := Result.probabilityLane L (ctaOf L g) row slot
  let site : Fin 4 := ⟨slot.val % 32 / 8, by omega⟩
  let l : Loc := ⟨.shared, ctaOf L g, pLinearByte L (row.val % 64) slot.val b.val⟩
  let index := 2 * (row.val * 16 + k.val) + b.val
  obtain ⟨j, w, e, _, fp, raw, he, hState, hBlock, hSite, hSub,
    hFired, hSelected, _, hFoot, hProxy⟩ :=
    selected_byte_before_pv hpre hX hs ht hi hd hsite row k b
  have hCta : ctaOf L h = ctaOf L g := (Result.probabilityLane_coords hpre (ctaOf L g) row slot).1
  obtain ⟨hSelectedWrite, hCover⟩ :=
    selected_write_covers hpre he hSite hFired row slot b rfl rfl hSub hSelected
  refine ⟨⟨l, .thread (h, j), fp, raw, hSelected, hCover⟩, rfl, ⟨_, rfl, hProxy⟩, ?_⟩
  intro other a bytes hw hc
  rcases competing_base_or_later hpre hX hs ht he hCta hState hSite row slot b hw hc with
    ⟨src, rfl, hBase⟩ | ⟨⟨s, t⟩, q, rfl, hWrite, hq, _, hCta', hClass⟩
  · exact .inl ⟨_, _, rfl, rfl, hBase⟩
  · have hQ := Frame.lt_of_get hX hWrite.choose_spec
    rcases hClass with ⟨grp, hGrp, hb⟩ | ⟨qsite, hqSite, hb⟩
    · exact .inr (.inr (later_store hpre hX hs ht hi hd hsite hFoot hWrite hc rfl hq
        (.inl ⟨grp, hGrp⟩) (hBlock ▸ hb) hCta'.symm))
    rcases lt_or_eq_of_le hb with hlater | hSame
    · exact .inr (.inr (later_store hpre hX hs ht hi hd hsite hFoot hWrite hc rfl hq
        (.inr ⟨qsite, hqSite⟩) (hBlock ▸ hlater) hCta'.symm))
    obtain ⟨hLane, hK, hQSub⟩ :=
      probability_store_coordinates hpre hX (hs s hQ).machine hWrite hq hqSite row slot b hc
    change s = h at hLane
    subst s
    have hSiteEq : qsite = site := Fin.ext hK
    subst qsite
    have hJ := Wg0ProbabilityUnique.write_unique hpre hX (hs h hQ).machine ht hSelectedWrite
      hWrite hState hq hSite hqSite hSame (hSub.trans hQSub.symm)
    subst t
    exact .inr (.inl rfl)

/-- Every covering write is ordered against this exact PV A operand byte. The read footprint is
present from the issue onward. -/
theorem ordered_byte {g i : Nat} {d : Wg1Mma.D} {issue : Fin 8}
    {other : Ref} {a : Acc} {bytes : List Byte}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.MmaIssue (g, i) (Wg1Mma.pvDest issue) (pvOperands L g d.i issue)
      (pvAccum d.i issue) [0, 0, 0, 0])
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .pvMma issue) (row : Fin 128) (k : Fin 16) (b : Fin 2)
    (hw : X.MemWrites other a bytes)
    (hc : a.Covers ⟨.shared, ctaOf L g, pLinearByte L (row.val % 64) (pvSlot issue k) b.val⟩) :
    let l : Loc := ⟨.shared, ctaOf L g, pLinearByte L (row.val % 64) (pvSlot issue k) b.val⟩
    let reader : Ref := .async (g, i) (.mmaRead false (2 * (row.val * 16 + k.val) + b.val))
    ByteCausality L X l other reader ∨ ByteCausality L X l reader other := by
  obtain ⟨src, _, ⟨w, hSrc, hProxy⟩, hOrder⟩ :=
    operand_source hpre hX hs ht hi hd hsite row k b
  let l : Loc := ⟨.shared, ctaOf L g, pLinearByte L (row.val % 64) (pvSlot issue k) b.val⟩
  let index := 2 * (row.val * 16 + k.val) + b.val
  have hFoot : X.MmaFootprint (g, i) false index l :=
    .inl ⟨_, _, _, _, hi, pvProbabilityByte L g d.i issue row k b⟩
  have hAsync : AsyncCovers X (g, i) (.mmaRead false index) l :=
    ⟨{loc := l, size := 1}, false, ⟨rfl, rfl, hFoot⟩,
      Acc.covers_at (k := 0) (show 0 < 1 by decide)⟩
  rcases hOrder other a bytes hw hc with ⟨e, f, rfl, hF, hBase⟩ | hEq | hLate
  · have hId : f = w := AsyncCopy.Ref.thread.inj (hF.symm.trans hSrc)
    subst f
    obtain ⟨fence, sp, scope, hf, hLt, hCover, hReach, hFirst, hSecond⟩ := hProxy
    exact .inl (.direct ⟨hAsync, .inl ⟨fence, sp, scope, hf, hLt, hCover, hReach,
      hBase.trans hFirst, hSecond⟩⟩)
  · rw [hEq, hSrc]
    exact .inl (.direct ⟨hAsync, .inl hProxy⟩)
  · exact .inr hLate

/-- A footprint specified by the issued PV A operand is ordered against any covering write. -/
theorem ordered_of_operand_location {g i index : Nat} {d : Wg1Mma.D} {issue : Fin 8}
    {other : Ref} {a : Acc} {bytes : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.MmaIssue (g, i) (Wg1Mma.pvDest issue) (pvOperands L g d.i issue)
      (pvAccum d.i issue) [0, 0, 0, 0])
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .pvMma issue)
    (hLoc : (pvOperands L g d.i issue).byteLoc .a index = some l)
    (hw : X.MemWrites other a bytes) (hc : a.Covers l) :
    ByteCausality L X l other (.async (g, i) (.mmaRead false index)) ∨
      ByteCausality L X l (.async (g, i) (.mmaRead false index)) other := by
  have hn := TcMma.OperandSpec.byteLoc_index_lt (s := pvOperands L g d.i issue) (op := .a) hLoc
  norm_num [pvOperands, Wg1Mma.pvDescriptor, TcMma.Operand.rows, TcMma.Operand.extent,
    TcMma.Kind.k, TcMma.Kind.width] at hn
  obtain ⟨row, k, b, rfl⟩ := MmaAccessWindow.operand_slot (rows := 128) hn
  rw [pvProbabilityByte L g d.i issue row k b] at hLoc
  obtain rfl := Option.some.inj hLoc
  exact ordered_byte hpre hX hs ht hi hd hsite row k b hw hc

private theorem query_copy_before_probability_window {g index n cta : Nat} {l : Loc}
    (issue : Fin 16)
    (hc : (queryCopySpec L g issue).ctas[n]? = some cta)
    (hn : index / (queryCopySpec L g issue).shape.sourceBytes = n)
    (hl : TcCopy.byteLoc (queryCopySpec L g issue).shape (queryCopySpec L g issue).src
      cta (index % (queryCopySpec L g issue).shape.sourceBytes) = some l) :
    l.addr < L.sharedBase + 204800 := by
  change [ctaOf L g][n]? = some cta at hc
  have hn0 : n = 0 := by
    have hh := (List.getElem?_eq_some_iff.mp hc).1
    simp only [List.length_cons, List.length_nil, Nat.zero_add] at hh
    omega
  rw [hn0] at hc hn
  change some (ctaOf L g) = some cta at hc
  obtain rfl := (Option.some.inj hc).symm
  change index / 4096 = 0 at hn
  have hIndex : index < 4096 := by omega
  change TcCopy.byteLoc (queryCopySpec L g issue).shape (queryCopySpec L g issue).src
    (ctaOf L g) (index % 4096) = some l at hl
  rw [Nat.mod_eq_of_lt hIndex] at hl
  obtain ⟨row, k, b, rfl⟩ :=
    MmaAccessWindow.operand_slot (rows := 128) (show index < 128 * 32 from hIndex)
  rw [queryCopyByteLoc L g issue row k b] at hl
  obtain rfl := Option.some.inj hl
  let addr := kvLinearByte L 0 (row.val % 64) (qkFeature issue row k) b.val
  have hb := b.isLt
  have hFeat : qkFeature issue row k < 512 := by
    have hi := issue.isLt
    have hr := row.isLt
    have hk := k.isLt
    simp only [qkFeature]
    omega
  have hLin : addr < L.sharedBase + 65536 := by
    simp only [addr, kvLinearByte, Wg1Mma.kvBase]
    omega
  have hRow := TensorSwizzle.offset_row .b128 0 addr
  change TensorSwizzle.offset .b128 0 addr < L.sharedBase + 204800
  omega

/-- Any Tensor Core A-read footprint covering a probability byte comes from PV. Its order against
every covering write follows even if the operand read has not yet been recorded. -/
theorem footprint_ordered {g i index : Nat} {other : Ref} {a : Acc} {bytes : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hFoot : X.MmaFootprint (g, i) false index l)
    (hLo : L.sharedBase + 204800 ≤ l.addr) (hw : X.MemWrites other a bytes) (hc : a.Covers l) :
    ByteCausality L X l other (.async (g, i) (.mmaRead false index)) ∨
      ByteCausality L X l (.async (g, i) (.mmaRead false index)) other := by
  rcases hFoot with ⟨dest, spec, accum, mask, hIssue, hLoc⟩ |
    ⟨c, n, cta, hCopy, _, hCta, hDiv, hLoc⟩
  · obtain ⟨rfl, ⟨block, k, rfl, rfl, rfl, _⟩ | ⟨block, k, rfl, rfl, rfl, hPV⟩⟩ :=
      MmaAccessWindow.mma_spec hpre hX hs ht hIssue
    · have hNone := TcMma.byteLoc_a_tmem (s := qkOperands L g block k) rfl index
      change (qkOperands L g block k).byteLoc .a index = some l at hLoc
      rw [hNone] at hLoc
      cases hLoc
    · exact ordered_of_operand_location hpre hX hs ht hIssue hPV rfl hLoc hw hc
  · obtain ⟨k, rfl⟩ := MmaAccessWindow.copy_spec hpre hX hs ht hCopy
    exact (Nat.not_lt_of_ge hLo (query_copy_before_probability_window k hCta hDiv hLoc)).elim

/-- The pending operand read and an overlapping ordinary write are ordered at their shared byte. -/
theorem ordinary_write_ordered {i w : EvId} {index : Nat} {a b : Acc} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hr : X.Intent (.async i (.mmaRead false index)) a false)
    (hw : X.Intent (.thread w) b true) (hLo : L.sharedBase + 204800 ≤ l.addr)
    (ha : a.Covers l) (hb : b.Covers l) :
    ByteCausality L X l (.thread w) (.async i (.mmaRead false index)) ∨
      ByteCausality L X l (.async i (.mmaRead false index)) (.thread w) := by
  have hFoot : X.MmaFootprint i false index l := Acc.loc_of_one ha hr.2.1 ▸ hr.2.2
  have hNoRmw : ∀ tag access old bytes, X.get w ≠ some ⟨tag, .rmw access old bytes⟩ :=
    fun tag _ _ _ he => GlobalWrites.no_rmw hX ⟨tag, he⟩
  rcases (Execution.access_iff_of_not_rmw hNoRmw).mp hw with ⟨_, _, h⟩ | ⟨bs, hWrite, _⟩
  · cases h
  · obtain ⟨g, j⟩ := i
    exact footprint_ordered (other := .thread w) hpre hX hs ht hFoot hLo (.inl hWrite) hb

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.PvProbabilityConflicts
