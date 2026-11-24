-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.MmaSteps
public import Kernels.FlashAttn4Fwd.Proof.Protocol.TcMmaSourcesValues
public import Kernels.FlashAttn4Fwd.Proof.Protocol.FloatsSources
public import Kernels.FlashAttn4Fwd.Proof.Protocol.Values
public import Lemmas.Tcgen05.TcMmaIdealSum
public import Lemmas.Tcgen05.TcMmaPairLayout

@[expose] public section

/-! # The operand values of the MMAs

The value chains of the scores (`ValuesScore`) and of the accumulator (`ValuesPv`) evaluate each
completed MMA by the kernel's assumption `fa4-fwd-ideal-arith` on its operand elements. They need
three premises beside the context of the MMA values (`TcMmaSources.ValueCtx`) and the thread
facts of the K steps (`MmaStepFacts`):

* **SmemInputs** (the shared operands): element `(row, kk)` of A of QK step `j` of stage `st` and
  score tile `u` (its thread's commits to the stage's S-full object, `sCommits`) is the FP16 value
  `Q` of query row `tileRow + row` of item `u / n` at head-dimension index `16 j + kk`; element
  `(col, kk)` of its B is `K` of key `visitKey (u % n) col` at `16 j + kk`; element `(col, kk)` of
  B of PV step `j` of tile `u` (`pPolls = u + 1`) is `V` of key `visitKey (u % n) (16 j + kk)` at
  head-dimension index `col`. It strengthens `TcMmaSources.SmemElements` (the elements are FP16
  values). `SmemElements.qk_a_element`, `qk_b_element` and `pv_b_element` give each element as
  the input element at the coordinates of the ring copy of the MMA's read use
  (`Rings.readUse`) and of its descriptor step; what remains for this premise is that the
  descriptor step is the K step (`qkStep`, `pvStep`), that the read use is the use of the
  tile's Q stage or KV visit, and that the copy's coordinates are the tile's.
* **SoftCoverLast**, **CorrCoverLast** (strengthening `Floats.SoftCover`, `Floats.CorrCover`): the
  MMAs of the tile a Tensor Memory load reads include step 7 of the tile's block, writing the
  loaded cell.
* **TmemLive** (`Floats.TmemLive`): the accesses are allocated and complete before the releases.

The lemmas here are the parts both chains share: counting K steps (`count_succ`, `count_zero`,
`count_lt`), the MMAs of one region writing the same cells (`region_cell`), the cells of an MMA
(`mma_geom`, `col0_qk`, `col0_pv`, `mma_ctas`, `cell_row`), the ideal evaluation of a completed
MMA (`eval_mma`) and the tile coordinates shared by the threads of a pair (`pair_tile`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof TcMma

noncomputable section

namespace ValuesOps

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **SmemInputs**: the shared operand elements of every completed MMA are the FP16 inputs of its
tile and K step. -/
structure SmemInputs (P : Params) (L : Launch) (X : Execution) : Prop where
  /-- Element `(row, kk)` of A of a QK MMA of stage `st` is `Q` of its tile's row `row`. -/
  qkA : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {ops : AsyncCopy.MmaOperands} {cell : Cell} {st row kk : Nat}, st < 2 →
    X.MmaIssue i d s acc mask →
    X.async.mmaDone i = true → X.async.mmaOperands i = some ops → X.MmaCell i cell →
    InS st cell → row < 256 → kk < 16 →
      Assumption.idealMmaElement (.f16 .f16 .f32) .a ops.a row kk = .ok
        (P.q (tileBatch L i.1 (sCommits L X i.1 st i.2 / kvBlocks P))
          (tileHead L i.1 (sCommits L X i.1 st i.2 / kvBlocks P))
          (tileRow L i.1 (sCommits L X i.1 st i.2 / kvBlocks P) st + row)
          (16 * qkStep L X i.1 st i.2 + kk))
  /-- Element `(col, kk)` of B of a QK MMA of stage `st` is `K` of its visit's key `col`. -/
  qkB : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {ops : AsyncCopy.MmaOperands} {cell : Cell} {st col kk : Nat}, st < 2 →
    X.MmaIssue i d s acc mask →
    X.async.mmaDone i = true → X.async.mmaOperands i = some ops → X.MmaCell i cell →
    InS st cell → col < 128 → kk < 16 →
      Assumption.idealMmaElement (.f16 .f16 .f32) .b ops.b col kk = .ok
        (P.k (tileBatch L i.1 (sCommits L X i.1 st i.2 / kvBlocks P))
          (tileHead L i.1 (sCommits L X i.1 st i.2 / kvBlocks P))
          (visitKey P (sCommits L X i.1 st i.2 % kvBlocks P) col)
          (16 * qkStep L X i.1 st i.2 + kk))
  /-- Element `(col, kk)` of B of a PV MMA of stage `st` is `V` of its visit's key `16 j + kk`
  at head-dimension index `col`. -/
  pvB : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {ops : AsyncCopy.MmaOperands} {cell : Cell} {st col kk : Nat}, st < 2 →
    X.MmaIssue i d s acc mask →
    X.async.mmaDone i = true → X.async.mmaOperands i = some ops → X.MmaCell i cell →
    InO st cell → col < 128 → kk < 16 →
      Assumption.idealMmaElement (.f16 .f16 .f32) .b ops.b col kk = .ok
        (P.v (tileBatch L i.1 ((pPolls L X i.1 st i.2 - 1) / kvBlocks P))
          (tileHead L i.1 ((pPolls L X i.1 st i.2 - 1) / kvBlocks P))
          (visitKey P ((pPolls L X i.1 st i.2 - 1) % kvBlocks P)
            (16 * pvStep L X i.1 st i.2 + kk)) col)

/-- **SoftCoverLast**: step 7 of the QK block of the score tile a softmax load reads writes each
cell it loads. -/
def SoftCoverLast (L : Launch) (X : Execution) : Prop :=
  ∀ {h i a j : Nat} {vals : List Value}, h < L.threads → warpOf L h < 8 →
    X.TLd (h, i) a vals .s32x32b → j < vals.length →
    ∃ x, IsMma X x ∧ X.MmaCell x (tcDataCell32 L h a j) ∧
      sCommits L X x.1 (warpOf L h / 4) x.2 + 1 = sPolls L X h (warpOf L h / 4) i ∧
      qkStep L X x.1 (warpOf L h / 4) x.2 = 7

/-- **CorrCoverLast**: step 7 of the PV block of the tile before a correction load's credit
writes each cell it loads. -/
def CorrCoverLast (L : Launch) (X : Execution) : Prop :=
  ∀ {h i a j st : Nat} {vals : List Value}, h < L.threads → 8 ≤ warpOf L h →
    warpOf L h < 12 → X.TLd (h, i) a vals .s32x32b → j < vals.length →
    InO st (tcDataCell32 L h a j) →
    ∃ x, IsMma X x ∧ X.MmaCell x (tcDataCell32 L h a j) ∧
      pPolls L X x.1 st x.2 = pArr L X h st i ∧ pvStep L X x.1 st x.2 = 7

/-- The context of the value chains. -/
structure Ctx (P : Params) (L : Launch) (mem0 : Mem0) (X : Execution) : Prop where
  base : TcMmaSources.ValueCtx P L mem0 X
  steps : MmaStepFacts P L X
  inputs : SmemInputs P L X
  softCover : SoftCoverLast L X
  corrCover : CorrCoverLast L X

/-! ## Counting K steps -/

section Count
open Classical

/-- The next counted index after `K` has one more counted index before it. -/
theorem count_succ {A : Nat → Prop} {f : Nat → Nat} {K k : Nat} (hK : K < k) (hA : A K)
    (hf : f K = f k) (hno : ∀ k', K < k' → k' < k → ¬ A k') :
    ((Finset.range k).filter fun k' => A k' ∧ f k' = f k).card =
      ((Finset.range K).filter fun k' => A k' ∧ f k' = f K).card + 1 := by
  have he : ((Finset.range k).filter fun k' => A k' ∧ f k' = f k) =
      insert K ((Finset.range K).filter fun k' => A k' ∧ f k' = f K) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hAx, hfx⟩
      rcases Nat.lt_trichotomy x K with h | h | h
      · exact .inr ⟨h, hAx, hfx.trans hf.symm⟩
      · exact .inl h
      · exact absurd hAx (hno x h hx)
    · rintro (rfl | ⟨hx, hAx, hfx⟩)
      · exact ⟨hK, hA, hf⟩
      · exact ⟨by omega, hAx, hfx.trans hf⟩
  rw [he, Finset.card_insert_of_notMem (by simp)]

/-- No counted index before `k` has `k`'s value: the count is zero. -/
theorem count_zero {A : Nat → Prop} {f : Nat → Nat} {k : Nat}
    (h : ∀ k', k' < k → A k' → f k' ≠ f k) :
    ((Finset.range k).filter fun k' => A k' ∧ f k' = f k).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx ⟨hA, hf⟩
  exact h x (Finset.mem_range.mp hx) hA hf

/-- A later counted index with the same value has a greater count. -/
theorem count_lt {A : Nat → Prop} {f : Nat → Nat} {x y : Nat} (hxy : x < y) (hA : A x)
    (hf : f x = f y) :
    ((Finset.range x).filter fun k' => A k' ∧ f k' = f x).card <
      ((Finset.range y).filter fun k' => A k' ∧ f k' = f y).card := by
  have hsub : insert x ((Finset.range x).filter fun k' => A k' ∧ f k' = f x) ⊆
      ((Finset.range y).filter fun k' => A k' ∧ f k' = f y) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range] at hz ⊢
    rcases hz with rfl | ⟨hz, hAz, hfz⟩
    · exact ⟨hxy, hA, hf⟩
    · exact ⟨by omega, hAz, hfz.trans hf⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp)] at this
  omega

/-- A later QK MMA of the same tile has a greater step. -/
theorem qkStep_lt {g st x y : Nat} (hxy : x < y) (hA : QkAt X g st x)
    (hf : sCommits L X g st x = sCommits L X g st y) : qkStep L X g st x < qkStep L X g st y := by
  unfold qkStep
  exact count_lt hxy hA hf

/-- A later PV MMA of the same tile has a greater step. -/
theorem pvStep_lt {g st x y : Nat} (hxy : x < y) (hA : PvAt X g st x)
    (hf : pPolls L X g st x = pPolls L X g st y) : pvStep L X g st x < pvStep L X g st y := by
  unfold pvStep
  exact count_lt hxy hA hf

end Count

/-! ## The cells of an MMA -/

/-- An MMA does not negate its operands. -/
theorem mma_neg (htt : TcMmaThreadFacts L X) {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} (hi : X.MmaIssue i d s acc mask) :
    s.descriptor.negateA = false ∧ s.descriptor.negateB = false := by
  cases ha : s.aTmem with
  | none =>
    have hd := Option.some.inj ((htt.mma_desc hi).2.1 ha)
    rw [← hd]
    exact ⟨rfl, rfl⟩
  | some _ =>
    have hd := Option.some.inj ((htt.mma_desc hi).2.2 (by simp [ha]))
    rw [← hd]
    exact ⟨rfl, rfl⟩

/-- The two CTAs of an MMA are its issuer's (a leader CTA) and the next. -/
theorem mma_ctas (hpre : Pre P L mem0) (ht : ScoreFacts L X) (htc : TcFacts L X)
    (htt : TcMmaThreadFacts L X) {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} (hi : X.MmaIssue i d s acc mask) :
    s.lowCta = ctaOf L i.1 ∧ s.highCta = ctaOf L i.1 + 1 ∧ ctaOf L i.1 % 2 = 0 := by
  obtain ⟨-, -, -, hml, -⟩ := htc.mma_shape hi
  obtain ⟨-, -, hl, -⟩ := ht.mma_cells hi
  obtain ⟨-, -, -, hg, -⟩ := TcMmaSources.mma_desc' htt hi
  have hc := hpre.cluster
  have he : ctaOf L i.1 % 2 = 0 := by
    unfold leadCta at hl
    omega
  have h1d := hpre.oneDimLaunch.1
  obtain ⟨ctas, hctas, hhd, hlast⟩ := hml
  rw [hg, Launch.ctaGroup_two] at hctas
  have hct : i.1 / L.block = ctaOf L i.1 := rfl
  simp only [Launch.peerCta, Launch.oneDim_clusterOfCta h1d, Launch.oneDim_rankOfCta h1d,
    Launch.oneDim_clusterStart h1d, Launch.oneDim_clusterSizeOf h1d, hc, hct] at hctas
  split_ifs at hctas <;> simp only [Option.bind_none, Option.bind_some, reduceCtorEq,
    Option.some.injEq] at hctas
  subst hctas
  simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton,
    Option.some.injEq] at hhd hlast
  refine ⟨?_, ?_, he⟩ <;> omega

/-- **The cells of an MMA**: output `(row, col)` is lane `row % 128` of the issuer's CTA
(`row < 128`) or the next, at column `d % 2^16 + col`; the MMA writes every column of the row. -/
theorem mma_geom (htt : TcMmaThreadFacts L X) (htc : TcFacts L X) {i : EvId} {d : Nat}
    {s : OperandSpec} {acc : Bool} {mask : List Nat} {row col : Nat} {cell : Cell}
    (hi : X.MmaIssue i d s acc mask) (hpos : writeCell s d mask row col = some cell) :
    row < 256 ∧ col < 128 ∧ cell = ⟨TcMma.rowCta s row, row % 128, d % 2 ^ 16 + col⟩ ∧
      ∀ col', col' < 128 → X.MmaCell i ⟨TcMma.rowCta s row, row % 128, d % 2 ^ 16 + col'⟩ := by
  obtain ⟨hkd, hm, hn, hg, -, -⟩ := TcMmaSources.mma_desc' htt hi
  have hmask := (htt.mma_desc hi).1
  subst hmask
  rw [writeCell_zero hm hg] at hpos
  obtain ⟨hrow, hcol, hc, hall⟩ := resultCell_pair hm hg hpos
  rw [hn] at hcol hall
  refine ⟨hrow, hcol, hc, fun col' hcol' => ?_⟩
  exact htc.mma_reads hi (hall col' hcol')

/-- A QK MMA of stage `st` writes from column `128 st`. -/
theorem col0_qk (ht : ScoreFacts L X) (htt : TcMmaThreadFacts L X) (htc : TcFacts L X)
    {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat} {row col st : Nat}
    {cell : Cell} (hi : X.MmaIssue i d s acc mask) (hpos : writeCell s d mask row col = some cell)
    (hS : InS st cell) (hst : st < 2) : d % 2 ^ 16 = 128 * st := by
  obtain ⟨-, -, -, hall⟩ := mma_geom htt htc hi hpos
  have hc : X.MmaCell i cell := ⟨_, _, _, _, _, _, hi, hpos⟩
  obtain ⟨-, -, -, st', hst', h | h⟩ := ht.mma_cells hi
  · have h0 := (h _ (hall 0 (by omega))).1
    have h1 := (h _ (hall 127 (by omega))).1
    have h2 := (h _ hc).1
    unfold InS at h0 h1 h2 hS
    dsimp only at h0 h1
    omega
  · have h2 := (h _ hc).1
    unfold InO at h2
    unfold InS at hS
    omega

/-- A PV MMA of stage `st` writes from column `256 + 128 st`. -/
theorem col0_pv (ht : ScoreFacts L X) (htt : TcMmaThreadFacts L X) (htc : TcFacts L X)
    {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat} {row col st : Nat}
    {cell : Cell} (hi : X.MmaIssue i d s acc mask) (hpos : writeCell s d mask row col = some cell)
    (hO : InO st cell) : d % 2 ^ 16 = 256 + 128 * st ∧ st < 2 := by
  obtain ⟨-, -, -, hall⟩ := mma_geom htt htc hi hpos
  have hc : X.MmaCell i cell := ⟨_, _, _, _, _, _, hi, hpos⟩
  obtain ⟨-, -, -, st', hst', h | h⟩ := ht.mma_cells hi
  · have h2 := (h _ hc).1
    unfold InS at h2
    unfold InO at hO
    omega
  · have h0 := (h _ (hall 0 (by omega))).1
    have h1 := (h _ (hall 127 (by omega))).1
    have h2 := (h _ hc).1
    unfold InO at h0 h1 h2 hO
    dsimp only at h0 h1
    constructor <;> omega

/-- The thread whose register cell is output row `row` of an MMA: lane `row % 128` of CTA rank
`row / 128` of the issuer's pair. -/
theorem cell_row (hpre : Pre P L mem0) {c0 h a p row : Nat} {s : OperandSpec} {col : Nat}
    (hlow : s.lowCta = c0) (hhigh : s.highCta = c0 + 1) (he : c0 % 2 = 0) (hrow : row < 256)
    (hc : tcDataCell32 L h a p = ⟨TcMma.rowCta s row, row % 128, col⟩) :
    row = 128 * rankOf L h + rowOf L h ∧ leadCta (ctaOf L h) = c0 := by
  have hb := hpre.block
  have hcl := hpre.cluster
  simp only [tcDataCell32, laneBase, laneOf, TcMma.rowCta, hlow, hhigh, Cell.mk.injEq] at hc
  obtain ⟨h1, h2, -⟩ := hc
  unfold rankOf rowOf
  rw [Launch.oneDim_rankOfCta hpre.oneDimLaunch.1]
  unfold leadCta ctaOf
  rw [hb, hcl] at *
  split_ifs at h1 with hr <;> constructor <;> omega

/-- The threads of a pair share the tile coordinates of an item; the leader's rank is 0. -/
theorem pair_tile (hpre : Pre P L mem0) {g h : Nat} (hl : leadCta (ctaOf L h) = ctaOf L g)
    (j st : Nat) :
    tileBatch L g j = tileBatch L h j ∧ tileHead L g j = tileHead L h j ∧
      tileRow L g j st + 128 * rankOf L h = tileRow L h j st := by
  have hcl := hpre.cluster
  have hcg : clusterOf L g = clusterOf L h := by
    unfold clusterOf
    rw [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1,
      Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, ← hl, hcl]
    unfold leadCta
    omega
  have hrg : rankOf L g = 0 := by
    unfold rankOf
    rw [Launch.oneDim_rankOfCta hpre.oneDimLaunch.1, ← hl, hcl]
    unfold leadCta
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [tileBatch, workOf, hcg]
  · simp only [tileHead, workOf, hcg]
  · simp only [tileRow, tileBlock, workOf, hcg, hrg]
    ring

/-- The MMAs of one region write the same cells. -/
theorem region_cell (ht : ScoreFacts L X) (htc : TcFacts L X) (htt : TcMmaThreadFacts L X)
    {x y : EvId} {d d' : Nat} {s s' : OperandSpec} {acc acc' : Bool} {mask mask' : List Nat}
    {c c' : Cell} {st : Nat} (hst : st < 2) (hx : X.MmaIssue x d s acc mask)
    (hy : X.MmaIssue y d' s' acc' mask') (hcx : X.MmaCell x c) (hcy : X.MmaCell y c')
    (hthr : x.1 = y.1) (hr : (InS st c ∧ InS st c') ∨ (InO st c ∧ InO st c')) :
    ∀ row col, writeCell s d mask row col = writeCell s' d' mask' row col := by
  have hlead : ∀ {z : EvId} {dz : Nat} {sz : OperandSpec} {az : Bool} {mz : List Nat}
      {cz : Cell}, X.MmaIssue z dz sz az mz → X.MmaCell z cz → leadCta cz.cta = ctaOf L z.1 := by
    intro z dz sz az mz cz hz hcz
    obtain ⟨-, -, -, sz, -, h | h⟩ := ht.mma_cells hz
    · exact (h cz hcz).2
    · exact (h cz hcz).2
  have hacc := ht.mma_acc hx hy hcx hcy (by rw [hlead hx hcx, hlead hy hcy, hthr]) hr
  have hdesc : s.descriptor = s'.descriptor := by
    rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hdx := (htt.mma_desc hx).2.1 (htc.qk_smem hst hx hcx h1)
      have hdy := (htt.mma_desc hy).2.1 (htc.qk_smem hst hy hcy h2)
      exact Option.some.inj (hdx.symm.trans hdy)
    · have hdx := (htt.mma_desc hx).2.2 (ht.pv_polls hx hcx h1).2.2.1
      have hdy := (htt.mma_desc hy).2.2 (ht.pv_polls hy hcy h2).2.2.1
      exact Option.some.inj (hdx.symm.trans hdy)
  intro row col
  rw [writeCell_congr hdesc hacc.2.2.2.1 hacc.2.2.2.2, hacc.1, (htt.mma_desc hx).1,
    (htt.mma_desc hy).1]

/-! ## The ideal evaluation -/

/-- **A completed MMA's ideal value** at `(row, col)`: the sum of the products of its operand
elements plus its old value. -/
theorem eval_mma (H : TcMmaSources.ValueCtx P L mem0 X) {i : EvId} {d : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} {ops : AsyncCopy.MmaOperands} {row col : Nat} {cell : Cell}
    (hi : X.MmaIssue i d s acc mask) (hops : X.async.mmaOperands i = some ops)
    (hpos : writeCell s d mask row col = some cell) {x y : Nat → ℝ}
    (ha : ∀ k, k < 16 → Assumption.idealMmaElement (.f16 .f16 .f32) .a ops.a row k = .ok (x k))
    (hb : ∀ k, k < 16 → Assumption.idealMmaElement (.f16 .f16 .f32) .b ops.b col k = .ok (y k))
    {old : Option Value} {prev : ℝ}
    (hprev : Assumption.idealMmaAccumulator .f32 acc old = .ok prev) :
    eval asms s.descriptor acc ops.a ops.b old row col =
      .ok (.float .f32 (∑ k ∈ Finset.range 16, x k * y k + prev)) := by
  obtain ⟨hkd, hm, hn, -, hws, -⟩ := TcMmaSources.mma_desc' H.thread hi
  obtain ⟨hna, hnb⟩ := mma_neg H.thread hi
  obtain ⟨hv, hla, hlb⟩ := H.cons.mma_observation_shape hi hops
  obtain ⟨hrow, hcol⟩ := resultCell_rowcol (writeCell_resultCell hpos)
  refine eval_sum rfl hkd (by rw [hkd]; simp) hv hws hna hnb ?_ ?_ hrow hcol ha hb hprev
  · rw [hla]
    simp [Operand.bytes, Operand.rows, Operand.extent, hws]
  · rw [hlb]
    simp [Operand.bytes, Operand.rows, Operand.extent]

end ValuesOps

end
end PTX.Kernels.FlashAttn4Fwd.Proof
