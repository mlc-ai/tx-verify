-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.Results
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns
import Kernels.InklingRelDecode.Proof.Protocol.Values.LdsWord
import Lemmas.Tcgen05.TcMmaF16Sum

@[expose] public section

/-! # The real an MMA result is

The value form of `results`: when every operand element and every stored word the MMAs of `Dom`
read is a known real (`ElementVals`), each derived result is the `.float .f32` of the real that
`ResReal` builds along the derivation: the sum of the sixteen products of the issue, plus the
accumulator's real (zero for an overwrite). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma PTX.Kernels.InklingRelDecode.Proof Tmem

/-- **The reals of the operand elements and of the stored accumulator words**: `a i row k` and
`b i col k` are the elements of the issue `i` (the A element of a QK or PV MMA, the B element),
`sv src cell` the real of the word the store `src` left in `cell`. The A element is known only for
the rows `Ok i row` of the issue. -/
structure ElementVals (Dom : EvId → Prop) (L : Launch) (X : Execution)
    (a b : EvId → Nat → Nat → ℝ) (sv : EvId → Cell → ℝ) (Ok : EvId → Nat → Prop) : Prop where
  b : ∀ {i d s acc mask ops row k}, Dom i → X.MmaIssue i d s acc mask →
    X.async.mmaDone i = true → X.async.mmaOperands i = some ops → row < 128 → k < 16 →
    Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b row k = .ok (b i row k)
  a : ∀ {i d s acc mask ops row k}, Dom i → Ok i row → X.MmaIssue i d s acc mask →
    X.async.mmaDone i = true → X.async.mmaOperands i = some ops → row < 64 → k < 16 →
    Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row k = .ok (a i row k)
  store : ∀ {i src cell old}, Dom i → X.MmaReadCell i cell → ReadSource L X .acc src i cell →
    StoreValue L X src cell old → valFloat .f32 old = .ok (sv src cell)

/-- The real of a result cell: the products of the issue, plus the accumulator's real. -/
inductive ResReal (L : Launch) (X : Execution) (a b : EvId → Nat → Nat → ℝ)
    (sv : EvId → Cell → ℝ) : EvId → Cell → ℝ → Prop where
  | overwrite {i d s mask row col cell} (issue : X.MmaIssue i d s false mask)
      (position : writeCell s d mask row col = some cell) :
      ResReal L X a b sv i cell (∑ k ∈ Finset.range 16, a i row k * b i col k)
  | accumulate {i d s mask row col cell source r} (issue : X.MmaIssue i d s true mask)
      (position : writeCell s d mask row col = some cell)
      (previous : ResReal L X a b sv source cell r)
      (provenance : ReadSource L X .acc source i cell) :
      ResReal L X a b sv i cell (∑ k ∈ Finset.range 16, a i row k * b i col k + r)
  | stored {i d s mask row col cell source} (issue : X.MmaIssue i d s true mask)
      (position : writeCell s d mask row col = some cell) (written : StoreCell L X source cell)
      (provenance : ReadSource L X .acc source i cell) :
      ResReal L X a b sv i cell (∑ k ∈ Finset.range 16, a i row k * b i col k + sv source cell)

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A store's value in a cell is a write of the cell. -/
theorem store_cell {st : EvId} {cell : Cell} {v : Value} (h : StoreValue L X st cell v) :
    StoreCell L X st cell :=
  let ⟨a, vals, sh, j, hT, hj, hc⟩ := h
  ⟨a, vals, sh, j, hT, (List.getElem?_eq_some_iff.mp hj).1, hc⟩

/-- **The sum of products** an MMA's cell holds, from the reals of its operand elements. -/
theorem eval_real (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {g k d s acc mask row col cell} (hi : X.MmaIssue (g, k) d s acc mask)
    (hpos : writeCell s d mask row col = some cell) {ops : AsyncCopy.MmaOperands}
    (hops : X.async.mmaOperands (g, k) = some ops) {x y : Nat → ℝ}
    (hx : row < 64 → ∀ k', k' < 16 →
      Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row k' = .ok (x k'))
    (hy : col < 128 → ∀ k', k' < 16 →
      Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b col k' = .ok (y k'))
    {old : Option Value} {prev : ℝ}
    (hprev : Assumption.idealMmaAccumulator .f32 acc old = .ok prev) :
    eval Assumptions.all s.descriptor acc ops.a ops.b old row col =
      .ok (.float .f32 (∑ k' ∈ Finset.range 16, x k' * y k' + prev)) := by
  obtain ⟨pc, he⟩ := id hi
  obtain ⟨hv, hla, hlb⟩ := hX.mma_observation_shape hi hops
  obtain ⟨hrow, hcol⟩ := resultCell_rowcol (writeCell_resultCell hpos)
  obtain ⟨-, -, -, bc, hcols⟩ := Mma.Export.columns hp hX hf base he
  have shape : s.descriptor.kind = .f16 .bf16 .f32 ∧ s.descriptor.ws = false ∧
      s.descriptor.negateA = false ∧ s.descriptor.negateB = false ∧ s.descriptor.m = 64 ∧
      s.descriptor.n = 128 := by
    rcases hcols with ⟨-, -, -, -, hd⟩ | ⟨-, -, -, -, hd⟩ <;> rw [hd] <;>
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨hkind, hws', hna, hnb, hm64, hn128⟩ := shape
  exact eval_sum16 (name := _) (sc := _) rfl hkind
    (by rw [hkind]; exact List.mem_singleton.mpr rfl) hv hws' hna hnb
    (by rw [hla]; simp [Operand.bytes, Operand.rows, Operand.extent, hws'])
    (by rw [hlb]; simp [Operand.bytes, Operand.rows, Operand.extent]) hrow hcol
    (hx (hm64 ▸ hrow)) (hy (hn128 ▸ hcol)) hprev

/-- **Every derived result is the `.float .f32` of its `ResReal`.** -/
theorem result_real (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (hG : SyncGuarded L kernel X) {Dom : EvId → Prop} {a b : EvId → Nat → Nat → ℝ}
    {sv : EvId → Cell → ℝ} {Ok : EvId → Nat → Prop} (E : ElementVals Dom L X a b sv Ok)
    {CellOk : Cell → Prop}
    (link : ∀ {i d s acc mask row col cell}, Dom i → X.MmaIssue i d s acc mask →
      writeCell s d mask row col = some cell → CellOk cell → Ok i row)
    (closed : ∀ i j cell, Dom i → X.MmaReadCell i cell → X.MmaCell j cell →
      WriteBefore L X j i → Dom j)
    {i : EvId} {cell : Cell} {v : Value} (h : Result L Assumptions.all X i cell v) :
    Dom i → X.async.mmaDone i = true → CellOk cell →
      ∃ r : ℝ, v = .float .f32 r ∧ ResReal L X a b sv i cell r := by
  induction h with
  | overwrite issue position reads arithmetic =>
    rename_i i0 d0 s0 mask0 row0 col0 cell0 ops0 value0
    intro hdom hd hok
    obtain ⟨g0, k0⟩ := i0
    have ev := eval_real hp hX hf base issue position reads
      (x := a (g0, k0) row0) (y := b (g0, k0) col0)
      (fun hr k' hk => E.a hdom (link hdom issue position hok) issue hd reads hr hk)
      (fun hc k' hk => E.b hdom issue hd reads hc hk) (old := none) (prev := 0) rfl
    exact ⟨_, by simpa using Except.ok.inj (arithmetic.symm.trans ev), .overwrite issue position⟩
  | accumulate issue position reads previous provenance arithmetic ih =>
    rename_i i0 d0 s0 mask0 row0 col0 cell0 ops0 value0 source0 old0
    intro hdom hd hok
    obtain ⟨g0, k0⟩ := i0
    have hrd : X.MmaReadCell (g0, k0) cell0 := ⟨d0, s0, mask0, row0, col0, issue,
      writeCell_resultCell position⟩
    have hm := result_cell previous
    have hds := Tmem.acc_mma_done hp hX hf base hG hd hrd provenance hm
    obtain ⟨-, -, hswb, -⟩ := id provenance
    obtain ⟨r1, hr1, rr⟩ := ih (closed _ _ _ hdom hrd hm hswb) hds hok
    subst hr1
    have ev := eval_real hp hX hf base issue position reads
      (x := a (g0, k0) row0) (y := b (g0, k0) col0)
      (fun hr k' hk => E.a hdom (link hdom issue position hok) issue hd reads hr hk)
      (fun hc k' hk => E.b hdom issue hd reads hc hk) (old := some (.float .f32 r1))
      (prev := r1) rfl
    exact ⟨_, Except.ok.inj (arithmetic.symm.trans ev), .accumulate issue position rr provenance⟩
  | accumulateStored issue position reads previous provenance arithmetic =>
    rename_i i0 d0 s0 mask0 row0 col0 cell0 ops0 value0 source0 old0
    intro hdom hd hok
    obtain ⟨g0, k0⟩ := i0
    have hrd : X.MmaReadCell (g0, k0) cell0 := ⟨d0, s0, mask0, row0, col0, issue,
      writeCell_resultCell position⟩
    have h1 := E.store hdom hrd provenance previous
    have ev := eval_real hp hX hf base issue position reads
      (x := a (g0, k0) row0) (y := b (g0, k0) col0)
      (fun hr k' hk => E.a hdom (link hdom issue position hok) issue hd reads hr hk)
      (fun hc k' hk => E.b hdom issue hd reads hc hk) (old := some old0)
      (prev := sv source0 cell0) (by simpa [Assumption.idealMmaAccumulator] using h1)
    exact ⟨_, Except.ok.inj (arithmetic.symm.trans ev), .stored issue position
      (store_cell previous) provenance⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
