-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.TcMmaSourcesAcc
public import Kernels.FlashAttn4Fwd.Proof.Safety.TcMmaInstr
public import Kernels.FlashAttn4Fwd.Proof.Protocol.FloatsSources
public import Lemmas.Tcgen05.TcFence

@[expose] public section

/-! # The values of the MMAs' results

Every MMA is a `kind::f16` MMA with an `.f32` accumulator, M = 256 and N = 128 (`qk_desc`,
`pv_desc`), evaluated by the kernel's assumption `fa4-fwd-ideal-arith` (the first of `asms`). A
completed MMA read its operands (`DEP-ASYNC-ORIGIN`), so its ideal arithmetic gives a
single-precision float at every result cell (`TcMma.eval_ok`) when its operand elements are FP16
values and its old value, when it accumulates, is a single-precision float:

* **shared operands** (`SmemElements`, a premise): the elements of B, and of A when A is in
  shared memory, are FP16 values: the bytes the input rings' tensor loads copied from the FP16
  inputs `Q`, `K`, `V` (`Rings.read_source`);
* **Tensor Memory A** (`pv_elements`): the two bytes of an element of a PV MMA's A operand are two
  adjacent bytes of one word (`aCell_pair`), read from the softmax store of the MMA's tile
  (`pvAStore`, `Score.p_aReadSource`, Core `AReadOk`), whose word is a pair of FP16 values
  (`TcMmaThreadFacts.soft_f16`) once the softmax thread's earlier loads returned single-precision
  floats;
* **old values** (`accSource`): the accumulator source is an earlier MMA of the thread writing the
  cell, pipelined before it with the same footprint (`sameAcc`), so completed (Core
  `CompletionClosed`) with a value by induction along the thread (`results`), or a correction
  store, whose words are single-precision floats (`TcMmaThreadFacts.corr_f32`) once the
  correction's earlier loads and statistics reads were finite.

The loads these facts need are of the MMAs' own results, so one induction covers them: a softmax
or correction load that precedes the MMA in the tcgen05 orders reads an MMA of the same thread
that is earlier (`hearly`: the orders have no cycle, `tcStep_acyclic`), whose result the
induction already gives (`softLoad_f32`, `corrLoad_f32`; the statistics word's store follows the
softmax loads, `ValueCtx.stats`).

Exports: `mmaValues` (`Safety.MmaValues`), `accSources` (`Safety.AccSources`), `pvAStoresAt`
(`Safety.PvAStores`), `softLoads_f32` and `corrStore_f32`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof TcMma

noncomputable section

namespace TcMmaSources
open Score

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **SmemElements**: every element a completed MMA read from shared memory is an FP16 value:
each row of B, and each row of A when A is in shared memory. -/
def SmemElements (X : Execution) : Prop :=
  ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {ops : AsyncCopy.MmaOperands} {row k : Nat}, X.MmaIssue i d s acc mask →
    X.async.mmaDone i = true → X.async.mmaOperands i = some ops → k < 16 →
    (row < s.descriptor.n →
      ∃ y, Assumption.idealMmaElement (.f16 .f16 .f32) .b ops.b row k = .ok y) ∧
    (s.aTmem = none → row < s.descriptor.m →
      ∃ x, Assumption.idealMmaElement (.f16 .f16 .f32) .a ops.a row k = .ok x)

/-- Two MMAs writing a common cell have the same accumulator and write the same cells. -/
theorem sameAcc (ht : ScoreFacts L X) (htc : TcFacts L X) (htt : TcMmaThreadFacts L X)
    {x y : EvId} {d d' : Nat} {s s' : OperandSpec} {acc acc' : Bool} {mask mask' : List Nat}
    {cell : Cell} (hx : X.MmaIssue x d s acc mask) (hy : X.MmaIssue y d' s' acc' mask')
    (hcx : X.MmaCell x cell) (hcy : X.MmaCell y cell) :
    SameAccumulator d s d' s' ∧
      ∀ row col, writeCell s d mask row col = writeCell s' d' mask' row col := by
  obtain ⟨-, -, -, st, hst, h | h⟩ := ht.mma_cells hx
  · have hS := (h cell hcx).1
    have hacc := ht.mma_acc hx hy hcx hcy rfl (.inl ⟨hS, hS⟩)
    have hdx := (htt.mma_desc hx).2.1 (htc.qk_smem hst hx hcx hS)
    have hdy := (htt.mma_desc hy).2.1 (htc.qk_smem hst hy hcy hS)
    have hdesc : s.descriptor = s'.descriptor := Option.some.inj (hdx.symm.trans hdy)
    refine ⟨hacc, fun row col => ?_⟩
    rw [writeCell_congr hdesc hacc.2.2.2.1 hacc.2.2.2.2, hacc.1, (htt.mma_desc hx).1,
      (htt.mma_desc hy).1]
  · have hO := (h cell hcx).1
    have hacc := ht.mma_acc hx hy hcx hcy rfl (.inr ⟨hO, hO⟩)
    have hdx := (htt.mma_desc hx).2.2 (ht.pv_polls hx hcx hO).2.2.1
    have hdy := (htt.mma_desc hy).2.2 (ht.pv_polls hy hcy hO).2.2.1
    have hdesc : s.descriptor = s'.descriptor := Option.some.inj (hdx.symm.trans hdy)
    refine ⟨hacc, fun row col => ?_⟩
    rw [writeCell_congr hdesc hacc.2.2.2.1 hacc.2.2.2.2, hacc.1, (htt.mma_desc hx).1,
      (htt.mma_desc hy).1]

/-- An earlier MMA of a completed MMA's thread writing one of its cells has completed. -/
theorem src_done (hX : Consistent L kernel asms mem0 X) (ht : ScoreFacts L X)
    (htc : TcFacts L X) (htt : TcMmaThreadFacts L X) {i : EvId} {d : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} {cell : Cell} {k : Nat} (hi : X.MmaIssue i d s acc mask)
    (hc : X.MmaCell i cell) (hk : k < i.2) (hcs : X.MmaCell (i.1, k) cell)
    (hd : X.async.mmaDone i = true) : X.async.mmaDone (i.1, k) = true := by
  obtain ⟨dK, sK, aK, mK, rowK, colK, hiK, hposK⟩ := id hcs
  obtain ⟨hacc, hw⟩ := sameAcc ht htc htt hiK hi hcs hc
  exact hX.mmaCompletion (i.1, k) i ⟨rfl, hk, mma_pipe ht hiK hi rfl hk hacc,
    _, _, _, _, _, _, _, _, hiK, hi, hw, rowK, colK, cell, hposK⟩ hd

/-- A completed MMA recorded its operands. -/
theorem operands_of_done (hX : Consistent L kernel asms mem0 X) {i : EvId}
    (hd : X.async.mmaDone i = true) : ∃ ops, X.async.mmaOperands i = some ops := by
  have hst := hX.tma.2.1.2 i hd
  cases h : X.async.mmaOperands i with
  | none => simp [AsyncCopy.Snapshot.mmaStarted, h] at hst
  | some ops => exact ⟨ops, rfl⟩

/-- The descriptor of every MMA. -/
theorem mma_desc' (htt : TcMmaThreadFacts L X) {i : EvId} {d : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} (hi : X.MmaIssue i d s acc mask) :
    s.descriptor.kind = .f16 .f16 .f32 ∧ s.descriptor.m = 256 ∧ s.descriptor.n = 128 ∧
      s.descriptor.group = .two ∧ s.descriptor.ws = false ∧ halfDatapath s.descriptor = false := by
  cases ha : s.aTmem with
  | none => exact qk_desc htt hi ha
  | some _ => exact pv_desc htt hi (by simp [ha])

/-- **PvAStores** in the form of the safety premise. -/
theorem pvAStoresAt (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : ScoreFacts L X) (htc : TcFacts L X) (htt : TcMmaThreadFacts L X) (hF : P2Facts L X)
    (hP : PReadyHandoff L X) (hU : P2Handoff L X) (hlive : MmaLive L X) :
    ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat} {index pos : Nat}
      {cell : Cell}, X.MmaIssue i d s acc mask → X.async.mmaDone i = true →
      aCell s index = some (cell, pos) →
        ∃ h k a j vals value, h < L.threads ∧ warpOf L h < 8 ∧ X.TSt (h, k) a vals .s32x32b ∧
          j < vals.length ∧ cell = tcDataCell32 L h a j ∧
          sPolls L X h (warpOf L h / 4) k = pPolls L X i.1 (warpOf L h / 4) i.2 ∧
          Wrote L asms X (h, k) cell value ∧ SourceLive L X (h, k) i cell := by
  intro i d s acc mask index pos cell hi _ ha
  obtain ⟨h, k, a, j, vals, value, hh, hw, hs, hj, hc, hu, -, hwr, hl⟩ :=
    pvAStores hpre hX ht htc htt hF hP hU hlive asms hi ha
  exact ⟨h, k, a, j, vals, value, hh, hw, hs, hj, hc, hu, hwr, hl⟩

/-- **The A elements of a completed PV MMA are FP16 values**: each is read from a softmax store's
packed pair of FP16 values. -/
theorem pv_elements (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : ScoreFacts L X) (ho : OAccFacts L X) (htc : TcFacts L X) (htt : TcMmaThreadFacts L X)
    (hF : P2Facts L X) (hP : PReadyHandoff L X) (hU : P2Handoff L X) (h2 : P2Gate L X)
    (hS : SFullHandoff L X) (hlive : MmaLive L X) {i : EvId} {d : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} {ops : AsyncCopy.MmaOperands} (hi : X.MmaIssue i d s acc mask)
    (haT : s.aTmem.isSome = true) (hops : X.async.mmaOperands i = some ops) {row k : Nat}
    (hrow : row < 256) (hk : k < 16)
    (hsl : ∀ {h0 k0 : Nat}, h0 < L.threads → warpOf L h0 < 8 →
      leadCta (ctaOf L h0) = leadCta (ctaOf L i.1) →
      Relation.TransGen (TcStep L X) (h0, k0) i →
      ∀ pc a' (vals' : List Value),
        X.get (h0, k0) = some ⟨pc, .tc (.ld a' vals' .s32x32b)⟩ → F32s vals') :
    ∃ x, Assumption.idealMmaElement (.f16 .f16 .f32) .a ops.a row k = .ok x := by
  obtain ⟨hkd, hm, -, -, hws, -⟩ := pv_desc htt hi haT
  -- the A cell of the element's first byte
  have hbytes : 2 * (row * 16 + k) < Operand.bytes .a s.descriptor := by
    simp only [Operand.bytes, Operand.rows, Operand.extent, hkd, hm, hws, Kind.k, Kind.width]
    simp
    omega
  obtain ⟨⟨cell, p⟩, hac⟩ : ∃ c, aCell s (2 * (row * 16 + k)) = some c := by
    rcases (htc.mma_shape hi).2.2.2.2.2.2.2.2.2 .a _ hbytes with ⟨loc, hl⟩ | ⟨-, hc⟩
    · rw [byteLoc_a_tmem haT] at hl
      cases hl
    · exact hc
  obtain ⟨hac1, hp2, hp4⟩ := aCell_pair hac
  -- the output accumulator cell the MMA writes
  obtain ⟨c0, hc0⟩ := htc.mma_cell hi
  obtain ⟨-, -, -, st, hst, hcs | hcs⟩ := ht.mma_cells hi
  · have hnone := htc.qk_smem hst hi hc0 (hcs c0 hc0).1
    simp [hnone] at haT
  have hO := (hcs c0 hc0).1
  -- the softmax store of the cell
  obtain ⟨h, kk, a, j, vals, value, hh, hw, hs, hj, hceq, hu, hval, hwr, hl⟩ :=
    pvAStores hpre hX ht htc htt hF hP hU hlive asms hi hac
  have hvm : value ∈ vals := List.mem_of_getElem? hval
  subst hceq
  have hsrc := fun {index pos : Nat} (ha : aCell s index = some (tcDataCell32 L h a j, pos)) =>
    p_aReadSource hpre ht ho hP h2 hS hi hc0 hO ha hh hw hs hj hu hl
  -- the softmax thread's loads before its store precede the MMA, in its CTA pair
  obtain ⟨-, hcta, -⟩ := (ht.pv_polls hi hc0 hO).2.2.2 _ _ _ hac
  have hlead : leadCta (ctaOf L h) = leadCta (ctaOf L i.1) :=
    (leadCta_idem _).symm.trans (by rw [← cell_cta L h a j, hcta])
  have hkl : kk < (X.tr h).length := TSt.lt hs
  obtain ⟨x, y, rfl⟩ := htt.soft_f16 hh hw hs (fun k0 hk0 pc a' vals' hld =>
    hsl hh hw hlead (.head (.inl (.single (.inl (po_of_source_not_access (e := (h, k0))
      (f := (h, kk)) rfl hk0 hkl (by rw [hld]; rfl))))) (hsrc hac).2.2.1.tcStep) pc a' vals' hld)
    value hvm
  have hb0 := hX.tcRead.2 _ _ _ _ _ _ _ ⟨_, _, _, _, hi, hac⟩ (hsrc hac) hwr hops
    (by simp [Value.bytes, FloatFmt.bytes]; omega)
  have hb1 := hX.tcRead.2 _ _ _ _ _ _ _ ⟨_, _, _, _, hi, hac1⟩ (hsrc hac1) hwr hops
    (by simp [Value.bytes, FloatFmt.bytes]; omega)
  have hl2 := take_two hb0 hb1
  rcases (by omega : p = 0 ∨ p = 2) with rfl | rfl
  · exact ⟨x, idealMmaElement_of_bytes (by
      rw [hl2]
      simp [Value.toBytes, Value.byteAt, Value.bytes, FloatFmt.bytes, List.range_succ])⟩
  · exact ⟨y, idealMmaElement_of_bytes (by
      rw [hl2]
      simp [Value.toBytes, Value.byteAt, Value.bytes, FloatFmt.bytes, List.range_succ])⟩

/-- The context of the value induction. -/
structure ValueCtx (P : Params) (L : Launch) (mem0 : Mem0) (X : Execution) : Prop where
  pre : Pre P L mem0
  cons : Consistent L kernel asms mem0 X
  score : ScoreFacts L X
  oacc : OAccFacts L X
  tc : TcFacts L X
  thread : TcMmaThreadFacts L X
  p2 : P2Facts L X
  sFull : SFullHandoff L X
  pReady : PReadyHandoff L X
  p2Handoff : P2Handoff L X
  p2Gate : P2Gate L X
  oReady : OAcc.OReady L X
  live : MmaLive L X
  smem : SmemElements X
  floats : FloatFacts L X
  corrCover : Floats.CorrCover L X
  tmemLive : Floats.TmemLive L X
  /-- Synchronization is guarded, so the tcgen05 orders have no cycle. -/
  guard : SyncGuarded L kernel X
  softCover : Floats.SoftCover L X
  /-- A correction thread's statistics read returns a finite single-precision word, once the
  loads of the row's softmax thread before its store, which happens before the read, returned
  single-precision floats (`Floats.stats_floats`). -/
  stats : ∀ {h j pc : Nat} {a : Acc} {bs : List (Option Byte)}, h < L.threads →
    8 ≤ warpOf L h → warpOf L h < 12 → X.get (h, j) = some ⟨pc, .rd a bs⟩ →
    (∀ {g i : Nat}, g < L.threads → warpOf L g < 8 → ctaOf L g = ctaOf L h →
      i < (X.tr g).length → baseCausality L X (g, i) (h, j) → ∀ k < i, ∀ pc a' (vals' : List Value),
        X.get (g, k) = some ⟨pc, .tc (.ld a' vals' .s32x32b)⟩ → F32s vals') →
    ∃ x, F32Read bs x

/-- The ideal arithmetic of a completed MMA succeeds at each of its cells, on an `.f32` old
value when it accumulates. -/
theorem eval_cell (H : ValueCtx P L mem0 X) {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} {row col : Nat} {cell : Cell} {ops : AsyncCopy.MmaOperands}
    (hi : X.MmaIssue i d s acc mask) (hpos : writeCell s d mask row col = some cell)
    (hd : X.async.mmaDone i = true) (hops : X.async.mmaOperands i = some ops) {old : Option Value}
    (hold : acc = true → ∃ r, old = some (.float .f32 r))
    (hsl : ∀ {h0 k0 : Nat}, h0 < L.threads → warpOf L h0 < 8 →
      leadCta (ctaOf L h0) = leadCta (ctaOf L i.1) →
      Relation.TransGen (TcStep L X) (h0, k0) i →
      ∀ pc a' (vals' : List Value),
        X.get (h0, k0) = some ⟨pc, .tc (.ld a' vals' .s32x32b)⟩ → F32s vals') :
    ∃ r, eval asms s.descriptor acc ops.a ops.b old row col = .ok (.float .f32 r) := by
  obtain ⟨hkd, hm, hn, -, hws, -⟩ := mma_desc' H.thread hi
  obtain ⟨hv, hla, hlb⟩ := H.cons.mma_observation_shape hi hops
  obtain ⟨hrow, hcol⟩ := resultCell_rowcol (writeCell_resultCell hpos)
  have hA : ∀ k, k < 16 →
      ∃ x, Assumption.idealMmaElement (.f16 .f16 .f32) .a ops.a row k = .ok x := by
    intro k hk
    cases haT : s.aTmem with
    | none => exact (H.smem hi hd hops hk).2 haT hrow
    | some _ =>
      exact pv_elements H.pre H.cons H.score H.oacc H.tc H.thread H.p2 H.pReady H.p2Handoff
        H.p2Gate H.sFull H.live hi (by simp [haT]) hops (by omega) hk hsl
  refine eval_ok rfl hkd (by rw [hkd]; simp) hv hws ?_ ?_ hrow hcol hA
    (fun k hk => (H.smem hi hd hops hk).1 hcol) hold
  · rw [hla]
    simp [Operand.bytes, Operand.rows, Operand.extent, hws]
  · rw [hlb]
    simp [Operand.bytes, Operand.rows, Operand.extent]

/-- **A correction load returns single-precision floats** once the MMAs writing its cells that
completed before it have values: its source is such an MMA (`Floats.corr_source`), whose result
is a single-precision float (`Floats.wrote_f32`), and the load returns it (Core `LoadReadOk`). -/
theorem corrLoad_f32 (H : ValueCtx P L mem0 X) {h i : Nat} (hh : h < L.threads)
    (h8 : 8 ≤ warpOf L h) (h12 : warpOf L h < 12)
    (hv : ∀ {a j : Nat} {x d s acc mask}, X.MmaIssue x d s acc mask →
      X.MmaCell x (tcDataCell32 L h a j) → DoneBefore L X x (h, i) → CompletedValues L asms X x)
    {pc a : Nat} {vals : List Value} (hld : X.get (h, i) = some ⟨pc, .tc (.ld a vals .s32x32b)⟩) :
    F32s vals := by
  intro v hv'
  obtain ⟨jj, hjj, rfl⟩ := List.getElem_of_mem hv'
  obtain ⟨src, value, hrs, hwr, hsrcm⟩ := Floats.corr_source H.pre H.cons H.score H.oacc
    H.pReady H.oReady H.corrCover hv H.tmemLive hh h8 h12 ⟨pc, hld⟩ hjj
  obtain ⟨word, hword, hcw⟩ :=
    H.cons.tcRead.1 _ a vals _ jj src _ value ⟨pc, hld⟩ (loadCell32 ⟨pc, hld⟩ hjj) hrs hwr
  obtain ⟨r, rfl⟩ := Floats.wrote_f32 H.score H.floats hwr hsrcm
  rw [List.getElem?_eq_getElem hjj, Option.some.injEq] at hword
  rw [hword]
  rcases hcw with ⟨-, rfl⟩ | ⟨hb, -⟩
  · exact ⟨r, rfl⟩
  · simp [Value.bytes, FloatFmt.bytes] at hb

/-- **A softmax load returns single-precision floats** once the MMAs writing its cells that
completed before it have values: its source is such an MMA (`Floats.soft_source`), whose result
is a single-precision float (`Floats.wrote_f32`), and the load returns it (Core `LoadReadOk`). -/
theorem softLoad_f32 (H : ValueCtx P L mem0 X) {h i : Nat} (hh : h < L.threads)
    (hw : warpOf L h < 8)
    (hv : ∀ {a j : Nat} {x d s acc mask}, X.MmaIssue x d s acc mask →
      X.MmaCell x (tcDataCell32 L h a j) → DoneBefore L X x (h, i) → CompletedValues L asms X x)
    {pc a : Nat} {vals : List Value} (hld : X.get (h, i) = some ⟨pc, .tc (.ld a vals .s32x32b)⟩) :
    F32s vals := by
  intro v hv'
  obtain ⟨jj, hjj, rfl⟩ := List.getElem_of_mem hv'
  obtain ⟨src, value, hrs, hwr, hsrcm⟩ := Floats.soft_source H.pre H.cons H.score H.oacc
    H.pReady H.p2Gate H.sFull H.softCover hv H.tmemLive hh hw ⟨pc, hld⟩ hjj
  obtain ⟨word, hword, hcw⟩ :=
    H.cons.tcRead.1 _ a vals _ jj src _ value ⟨pc, hld⟩ (loadCell32 ⟨pc, hld⟩ hjj) hrs hwr
  obtain ⟨r, rfl⟩ := Floats.wrote_f32 H.score H.floats hwr hsrcm
  rw [List.getElem?_eq_getElem hjj, Option.some.injEq] at hword
  rw [hword]
  rcases hcw with ⟨-, rfl⟩ | ⟨hb, -⟩
  · exact ⟨r, rfl⟩
  · simp [Value.bytes, FloatFmt.bytes] at hb

/-- **Every cell of a completed MMA has a single-precision value**, by induction along the
issuing thread. -/
theorem results (H : ValueCtx P L mem0 X) :
    ∀ k g d s acc mask row col cell, X.MmaIssue (g, k) d s acc mask →
      writeCell s d mask row col = some cell → X.async.mmaDone (g, k) = true →
      ∃ r, Result L asms X (g, k) cell (.float .f32 r) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro g d s acc mask row col cell hi hpos hd
  -- an MMA of the CTA pair before `(g, k)` in the tcgen05 orders is earlier on thread `g`, since
  -- those orders have no cycle
  have hearly : ∀ {x : EvId} {dx sx ax mx}, X.MmaIssue x dx sx ax mx →
      leadCta (ctaOf L x.1) = leadCta (ctaOf L g) → Relation.TransGen (TcStep L X) x (g, k) →
      x.1 = g ∧ x.2 < k := by
    intro x dx sx ax mx hx hl hpath
    have hxg : x.1 = g := H.score.tc_one ⟨_, _, _, _, hx⟩ (.inl ⟨_, _, _, _, hi⟩) hl
    refine ⟨hxg, ?_⟩
    by_contra hge
    obtain ⟨pcx, hxget⟩ := hx
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hge) with hlt | heq
    · exact tcStep_acyclic H.cons H.guard _ (hpath.tail (.inl (.single (.inl
        (po_of_not_access (e := (g, k)) (f := x) hxg.symm hlt (len_of_get hxget)
          (by rw [hxget]; rfl))))))
    · have hx' : x = (g, k) := Prod.ext hxg heq.symm
      subst hx'
      exact tcStep_acyclic H.cons H.guard _ hpath
  -- so a softmax load of the CTA pair before `(g, k)` returns single-precision floats
  have hsoftld : ∀ {h0 k0 : Nat}, h0 < L.threads → warpOf L h0 < 8 →
      leadCta (ctaOf L h0) = leadCta (ctaOf L g) →
      Relation.TransGen (TcStep L X) (h0, k0) (g, k) → ∀ pc a' (vals' : List Value),
        X.get (h0, k0) = some ⟨pc, .tc (.ld a' vals' .s32x32b)⟩ → F32s vals' := by
    intro h0 k0 hh0 hw0 hl0 hp0 pc a' vals' hld
    refine softLoad_f32 H hh0 hw0 ?_ hld
    intro a0 j0 x dx sx ax mx hx hxc hdb hdx c0 ⟨d0, s0, a1, m0, r0, c0', hx0, hp0'⟩
    obtain ⟨hxg, hxk⟩ := hearly hx (by
      rw [Floats.mma_lead H.score ⟨_, _, _, _, hx⟩ hxc, cell_cta, leadCta_idem, hl0])
      (hdb.tcStep.trans hp0)
    obtain ⟨xg, xk⟩ := x
    simp only at hxg hxk
    subst hxg
    obtain ⟨r, hr⟩ := ih xk hxk xg d0 s0 a1 m0 r0 c0' c0 hx0 hp0' hdx
    exact ⟨_, hr⟩
  obtain ⟨ops, hops⟩ := operands_of_done H.cons hd
  cases acc
  · obtain ⟨r, hr⟩ := eval_cell H hi hpos hd hops (old := none) (fun h => by cases h) hsoftld
    exact ⟨r, .overwrite hi hpos hops hr⟩
  · have hc : X.MmaCell (g, k) cell := ⟨_, _, _, _, _, _, hi, hpos⟩
    obtain ⟨src, hsrc, ⟨hs1, hs2, hcs⟩ | ⟨hgl, h8, h12, a, vals, sh, j, hst, hj, hceq⟩⟩ :=
      accSource H.pre H.score H.oacc H.thread H.sFull H.pReady H.p2Gate H.oReady H.live hi hc
    · obtain ⟨g', k'⟩ := src
      simp only at hs1 hs2
      subst hs1
      have hds := src_done H.cons H.score H.tc H.thread hi hc hs2 hcs hd
      obtain ⟨d', s', a', m', row', col', hi', hpos'⟩ := hcs
      obtain ⟨r', hr'⟩ := ih k' hs2 g' d' s' a' m' row' col' cell hi' hpos' hds
      obtain ⟨r, hr⟩ := eval_cell H hi hpos hd hops (old := some (.float .f32 r'))
        (fun _ => ⟨r', rfl⟩) hsoftld
      exact ⟨r, .accumulate hi hpos hops hr' hsrc hr⟩
    · obtain ⟨g', k'⟩ := src
      simp only at hgl h8 h12 hst hceq
      obtain rfl := H.score.tc_shape (.inr hst)
      have hwb : WriteBefore L X (g', k') (g, k) := hsrc.2.2.1
      have hk'l : k' < (X.tr g').length := TSt.lt hst
      obtain ⟨pcs, hsget⟩ := hst
      -- a correction load before the store reads an MMA of thread `g` before `k`
      have hlds : ∀ k0 < k', ∀ pc a' (vals' : List Value),
          X.get (g', k0) = some ⟨pc, .tc (.ld a' vals' .s32x32b)⟩ → F32s vals' := by
        intro k0 hk0 pc a' vals' hld
        refine corrLoad_f32 H hgl h8 h12 ?_ hld
        intro a0 j0 x dx sx ax mx hx hxc hdb hdx c0 ⟨d0, s0, a1, m0, r0, c0', hx0, hp0⟩
        -- `x` is an MMA of thread `g`: both write cells of `g'`'s CTA
        have hxg : x.1 = g := by
          refine H.score.tc_one ⟨_, _, _, _, hx⟩ (.inl ⟨_, _, _, _, hi⟩) ?_
          rw [Floats.mma_lead H.score ⟨_, _, _, _, hx⟩ hxc,
            Floats.mma_lead H.score ⟨_, _, _, _, hi⟩ hc, hceq]
          rfl
        -- and it precedes `k`, since the tcgen05 orders have no cycle
        have hxk : x.2 < k := by
          by_contra hge
          have hpath : Relation.TransGen (TcStep L X) x (g, k) :=
            (hdb.tcStep.tail (.inl (.single (.inl (po_of_not_access (e := (g', k0))
              (f := (g', k')) rfl hk0 hk'l (by rw [hsget]; rfl)))))).trans hwb.tcStep
          obtain ⟨pcx, hxget⟩ := hx
          rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hge) with hlt | heq
          · refine tcStep_acyclic H.cons H.guard _ (hpath.tail (.inl (.single (.inl
              (po_of_not_access (e := (g, k)) (f := x) hxg.symm hlt (len_of_get hxget)
                (by rw [hxget]; rfl))))))
          · have hx' : x = (g, k) := Prod.ext hxg heq.symm
            subst hx'
            exact tcStep_acyclic H.cons H.guard _ hpath
        obtain ⟨xg, xk⟩ := x
        simp only at hxg hxk
        subst hxg
        obtain ⟨r, hr⟩ := ih xk hxk xg d0 s0 a1 m0 r0 c0' c0 hx0 hp0 hdx
        exact ⟨_, hr⟩
      -- a statistics read before the store reads a softmax store of `g'`'s CTA whose earlier
      -- loads precede `(g, k)`
      have hrds : ∀ k0 < k', ∀ pc (ac : Acc) (bs' : List (Option Byte)),
          X.get (g', k0) = some ⟨pc, .rd ac bs'⟩ → ∃ x, F32Read bs' x := by
        intro k0 hk0 pc ac bs' he
        refine H.stats hgl h8 h12 he fun {gs is} hgs hws hcg hisl hb k1 hk1 pc' a' v' hld => ?_
        refine hsoftld hgs hws ?_ ?_ pc' a' v' hld
        · rw [hcg, Floats.mma_lead H.score ⟨_, _, _, _, hi⟩ hc, hceq, tcDataCell_s32x32b,
            cell_cta, leadCta_idem]
        · have p1 : Relation.TransGen (TcStep L X) (gs, k1) (gs, is) :=
            .single (.inl (.single (.inl (po_of_source_not_access (e := (gs, k1))
              (f := (gs, is)) rfl hk1 hisl (by rw [hld]; rfl)))))
          have p3 : TcStep L X (g', k0) (g', k') :=
            .inl (.single (.inl (po_of_not_access (e := (g', k0)) (f := (g', k')) rfl hk0 hk'l
              (by rw [hsget]; rfl))))
          exact ((p1.tail (.inl hb)).tail p3).trans hwb.tcStep
      have hst : X.TSt (g', k') a vals .s32x32b := ⟨pcs, hsget⟩
      obtain ⟨r', hr'⟩ := H.thread.corr_f32 hgl h8 h12 hst hlds hrds vals[j]
        (List.getElem_mem hj)
      obtain ⟨r, hr⟩ := eval_cell H hi hpos hd hops (old := some (.float .f32 r'))
        (fun _ => ⟨r', rfl⟩) hsoftld
      exact ⟨r, .accumulateStored hi hpos hops
        (old := .float .f32 r') ⟨a, vals, _, j, hst,
          by rw [← hr']; exact List.getElem?_eq_getElem hj, hceq⟩ hsrc hr⟩

/-- **MmaValues**: every completed MMA's cells have values. -/
theorem mmaValues (H : ValueCtx P L mem0 X) :
    ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat},
      X.MmaIssue i d s acc mask → CompletedValues L asms X i := by
  intro i _ _ _ _ _ hd cell ⟨d, s, acc, mask, row, col, hi, hpos⟩
  obtain ⟨r, h⟩ := results H i.2 i.1 d s acc mask row col cell hi hpos hd
  exact ⟨_, h⟩

/-- **Every correction store writes single-precision floats** (`TcMmaThreadFacts.corr_f32`): the
correction's earlier loads return single-precision floats (`corrLoad_f32` with `mmaValues`) and
its earlier statistics reads are finite. -/
theorem corrStore_f32 (H : ValueCtx P L mem0 X) {h i a : Nat} {vals : List Value}
    (hh : h < L.threads) (h8 : 8 ≤ warpOf L h) (h12 : warpOf L h < 12)
    (hst : X.TSt (h, i) a vals .s32x32b) : F32s vals :=
  H.thread.corr_f32 hh h8 h12 hst
    (fun _ _ _ _ _ hld => corrLoad_f32 H hh h8 h12 (fun hx _ _ => mmaValues H hx) hld)
    (fun _ _ _ _ _ he => H.stats hh h8 h12 he fun hg hw _ _ _ _ _ _ _ _ hld =>
      softLoad_f32 H hg hw (fun hx _ _ => mmaValues H hx) hld)

/-- **Every softmax load returns single-precision floats** (`softLoad_f32` with `mmaValues`). -/
theorem softLoads_f32 (H : ValueCtx P L mem0 X) {h k pc a : Nat} {vals : List Value}
    (hh : h < L.threads) (hw : warpOf L h < 8)
    (hld : X.get (h, k) = some ⟨pc, .tc (.ld a vals .s32x32b)⟩) : F32s vals :=
  softLoad_f32 H hh hw (fun hx _ _ => mmaValues H hx) hld

/-- **AccSources**: every completed accumulating MMA's old values have sources with values. -/
theorem accSources (H : ValueCtx P L mem0 X) : Safety.AccSources L X := by
  intro i _ _ _ _ _ hd cell ⟨d, s, mask, row, col, hi, hrc⟩
  have hc := H.tc.mma_reads hi hrc
  obtain ⟨src, hsrc, ⟨hs1, hs2, hcs⟩ | ⟨-, -, -, a, vals, sh, j, hst, hj, hceq⟩⟩ :=
    accSource H.pre H.score H.oacc H.thread H.sFull H.pReady H.p2Gate H.oReady H.live hi hc
  · obtain ⟨g', k'⟩ := src
    simp only at hs1 hs2
    subst hs1
    have hds := src_done H.cons H.score H.tc H.thread hi hc hs2 hcs hd
    obtain ⟨d', s', a', m', row', col', hi', hpos'⟩ := hcs
    obtain ⟨r', hr'⟩ := results H k' i.1 d' s' a' m' row' col' cell hi' hpos' hds
    exact ⟨_, _, hsrc, .inl hr'⟩
  · exact ⟨_, vals[j], hsrc, .inr (.inl ⟨a, vals, sh, j, hst, List.getElem?_eq_getElem hj, hceq⟩)⟩

end TcMmaSources

end
end PTX.Kernels.FlashAttn4Fwd.Proof
