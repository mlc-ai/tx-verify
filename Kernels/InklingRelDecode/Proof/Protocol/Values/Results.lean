-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AccSource
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteOrder
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Lemmas.Tcgen05.TcFence
import Lemmas.Tcgen05.TcMmaF16Sum

@[expose] public section

/-! # The values of the MMAs' results

A completed MMA read its operands, so its ideal arithmetic gives a single-precision number at every
cell it writes when its operand elements and its old value are numbers (`eval_mma`). The old value
is an earlier MMA's result of the lane, completed before it, or the word of a rescale store; so one
induction along the lane gives every result (`results`). Only the typing is proved, never the
values: the operand elements and the stored words are the facts `Elements`, and they do not depend
on the loads (a lane that read a non-number at a floating instruction is dead, and a dead lane
stores nothing). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma PTX.Kernels.InklingRelDecode.Proof Tmem

/-- **The numbers the MMAs read**: the elements of every completed MMA's operands, and the words of
the stores that an accumulating MMA reads. -/
structure Elements (Dom : EvId → Prop) (L : Launch) (X : Execution) : Prop where
  /-- The B elements (the K and V tiles). -/
  b : ∀ {i d s acc mask ops row k}, Dom i → X.MmaIssue i d s acc mask →
    X.async.mmaDone i = true →
    X.async.mmaOperands i = some ops → row < 128 → k < 16 →
    ∃ y, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b row k = .ok y
  /-- The A elements of a QK MMA (the query tile). -/
  q : ∀ {i d s acc mask ops row k}, Dom i → X.MmaIssue i d s acc mask → s.aTmem = none →
    X.async.mmaDone i = true → X.async.mmaOperands i = some ops → row < 64 → k < 16 →
    ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row k = .ok x
  /-- The A elements of a PV MMA (the probabilities). -/
  p : ∀ {i d s acc mask ops row k a}, Dom i → X.MmaIssue i d s acc mask → s.aTmem = some a →
    X.async.mmaDone i = true → X.async.mmaOperands i = some ops → row < 64 → k < 16 →
    ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row k = .ok x
  /-- The word of a store that is the source of an accumulating MMA's read (not any store of the
  cell: a QK step reads cells that an earlier round's probability store wrote too). -/
  store : ∀ {i src cell old}, Dom i → X.MmaReadCell i cell → ReadSource L X .acc src i cell →
    StoreValue L X src cell old → ∃ r : ℝ, valFloat .f32 old = .ok r

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A completed MMA recorded its operands. -/
theorem operands_of_done (hX : Consistent L kernel Assumptions.all m X) {i : EvId}
    (hd : X.async.mmaDone i = true) : ∃ ops, X.async.mmaOperands i = some ops := by
  obtain ⟨-, ⟨-, hstarted⟩, -, -⟩ := hX.tma
  have hst := hstarted i hd
  cases h : X.async.mmaOperands i with
  | none => simp [AsyncCopy.Snapshot.mmaStarted, h] at hst
  | some ops => exact ⟨ops, rfl⟩

/-- **The ideal value of a QK or PV MMA**, from its operand elements and its old value. -/
theorem eval_cell (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {Dom : EvId → Prop} (E : Elements Dom L X) {g k d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat}
    {row col : Nat} {cell : Cell} (hdom : Dom (g, k))
    (hi : X.MmaIssue (g, k) d s acc mask)
    (hpos : writeCell s d mask row col = some cell) (hd : X.async.mmaDone (g, k) = true)
    {ops : AsyncCopy.MmaOperands} (hops : X.async.mmaOperands (g, k) = some ops)
    {old : Option Value} {prev : ℝ}
    (hprev : Assumption.idealMmaAccumulator .f32 acc old = .ok prev) :
    ∃ r : ℝ, eval Assumptions.all s.descriptor acc ops.a ops.b old row col =
      .ok (.float .f32 r) := by
  obtain ⟨pc, he⟩ := id hi
  obtain ⟨hv, hla, hlb⟩ := hX.mma_observation_shape hi hops
  obtain ⟨hrow, hcol⟩ := resultCell_rowcol (writeCell_resultCell hpos)
  obtain ⟨hk, hA⟩ : (s.descriptor.kind = .f16 .bf16 .f32 ∧ s.descriptor.ws = false ∧
      s.descriptor.negateA = false ∧ s.descriptor.negateB = false ∧ s.descriptor.m = 64 ∧
      s.descriptor.n = 128) ∧ ∀ r k, r < 64 → k < 16 →
      ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a r k = .ok x := by
    obtain ⟨-, -, -, b, ⟨j, -, -, hat, hdesc⟩ | ⟨j, -, -, hat, hdesc⟩⟩ :=
      Mma.Export.columns hp hX hf base he
    · exact ⟨by rw [hdesc]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
        fun r k hr hk => E.q hdom hi hat hd hops hr hk⟩
    · exact ⟨by rw [hdesc]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
        fun r k hr hk => E.p hdom hi hat hd hops hr hk⟩
  obtain ⟨hkind, hws', hna, hnb, hm64, hn128⟩ := hk
  have hr64 : row < 64 := hm64 ▸ hrow
  have hc128 : col < 128 := hn128 ▸ hcol
  have hxs : ∀ k, k < 16 → ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row k =
      .ok x := fun k hk' => hA row k hr64 hk'
  have hys : ∀ k, k < 16 → ∃ y, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b col k =
      .ok y := fun k hk' => E.b hdom hi hd hops hc128 hk'
  choose! x hx using hxs
  choose! y hy using hys
  exact ⟨_, eval_sum16 (name := _) (sc := _) rfl hkind
    (by rw [hkind]; exact List.mem_singleton.mpr rfl) hv hws' hna hnb
    (by rw [hla]; simp [Operand.bytes, Operand.rows, Operand.extent, hws'])
    (by rw [hlb]; simp [Operand.bytes, Operand.rows, Operand.extent]) hrow hcol hx hy hprev⟩

/-- **Every cell of a completed MMA has a single-precision value.** -/
theorem results (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hws : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) {Dom : EvId → Prop} (E : Elements Dom L X)
    (closed : ∀ i j cell, Dom i → X.MmaReadCell i cell → X.MmaCell j cell →
      WriteBefore L X j i → Dom j) :
    ∀ k g d s acc mask row col cell, Dom (g, k) → X.MmaIssue (g, k) d s acc mask →
      writeCell s d mask row col = some cell → X.async.mmaDone (g, k) = true →
      ∃ r : ℝ, Result L Assumptions.all X (g, k) cell (.float .f32 r) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro g d s acc mask row col cell hdom hi hpos hd
  obtain ⟨ops, hops⟩ := operands_of_done hX hd
  obtain ⟨pc, he⟩ := id hi
  cases acc
  · obtain ⟨r, hr⟩ := eval_cell hp hX hf base E hdom hi hpos hd hops (old := none) (prev := 0) rfl
    exact ⟨r, .overwrite hi hpos hops hr⟩
  have hrd : X.MmaReadCell (g, k) cell := ⟨d, s, mask, row, col, hi, writeCell_resultCell hpos⟩
  have hc : X.MmaCell (g, k) cell := ⟨d, s, true, mask, row, col, hi, hpos⟩
  have hcell : ∀ {i : EvId} {d' s' a' m'}, X.MmaIssue i d' s' a' m' → X.MmaCell i cell →
      WriteBefore L X i (g, k) → i.1 = g ∧ i.2 < k := by
    intro i d' s' a' m' hi' hmc hwb
    obtain ⟨pc', he'⟩ := id hi'
    have cta := (Tmem.mma_cells hp hX hf base (.inl hmc)).1.symm.trans
      (Tmem.mma_cells hp hX hf base (.inl hc)).1
    have hg := Tmem.mma_thread hp hX hf he' he cta
    exact ⟨hg, tcStep_same_thread (tcStep_acyclic hX hG) hwb.tcStep hg (by rw [he]; rfl)⟩
  have cand : ∃ w, TmemWrite L X w cell ∧ WriteBefore L X w (g, k) := by
    by_cases hfirst : ∃ d s mask, X.get (g, k) = some ⟨Lib.pvIssue 0, .tc (.mma d s true mask)⟩
    · obtain ⟨d', s', mask', e⟩ := hfirst
      exact Tmem.acc_first hp hX hf hu base hrd e
    · exact Tmem.acc_prev hp hX hf hu base hrd fun d s mask e => hfirst ⟨d, s, mask, e⟩
  have hcv : ∀ i d' s' a' m', X.MmaIssue i d' s' a' m' → X.MmaCell i cell →
      WriteBefore L X i (g, k) → CompletedValues L Assumptions.all X i := by
    intro i d' s' a' m' hi' hmc hwb hdi c' ⟨d2, s2, a2, m2, r2, c2, hi2, hp2⟩
    have hDi := closed _ _ _ hdom hrd hmc hwb
    obtain ⟨hg, hlt⟩ := hcell hi' hmc hwb
    obtain ⟨gi, ki⟩ := i
    obtain ⟨r, hr⟩ := ih ki hlt gi d2 s2 a2 m2 r2 c2 c' hDi hi2 hp2 hdi
    exact ⟨_, hr⟩
  obtain ⟨src, -, hsrc, -⟩ := Tmem.acc_source hp hX hf safe base rows init hG hws ht hmd hcv
    hd hrd cand
  obtain ⟨-, hsw, hswb, -⟩ := id hsrc
  rcases tmemWrite_of_no_copy (Lib.no_cp hX) (Tmem.no_shift hX) hsw with hm | hs
  · obtain ⟨d', s', a', m', r', c', hi', hp'⟩ := id hm
    obtain ⟨hg, hlt⟩ := hcell hi' hm hswb
    have hds := Tmem.acc_mma_done hp hX hf base hG hd hrd hsrc hm
    obtain ⟨gs, ks⟩ := src
    simp only at hg hlt
    subst hg
    obtain ⟨r1, hr1⟩ := ih ks hlt gs d' s' a' m' r' c' cell
      (closed _ _ _ hdom hrd hm hswb) hi' hp' hds
    obtain ⟨r, hr⟩ := eval_cell hp hX hf base E hdom hi hpos hd hops (old := some (.float .f32 r1))
      (prev := r1) rfl
    exact ⟨r, .accumulate hi hpos hops hr1 hsrc hr⟩
  · obtain ⟨old, hv⟩ := Tmem.store_value hs
    obtain ⟨r1, h1⟩ := E.store hdom hrd hsrc hv
    obtain ⟨r, hr⟩ := eval_cell hp hX hf base E hdom hi hpos hd hops (old := some old)
      (prev := r1) (by simpa [Assumption.idealMmaAccumulator] using h1)
    exact ⟨r, .accumulateStored hi hpos hops hv hsrc hr⟩

/-- **Every derived value of a completed MMA's cell is a single-precision number.** -/
theorem result_float (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (hG : SyncGuarded L kernel X) {Dom : EvId → Prop} (E : Elements Dom L X)
    (closed : ∀ i j cell, Dom i → X.MmaReadCell i cell → X.MmaCell j cell →
      WriteBefore L X j i → Dom j)
    {i : EvId} {cell : Cell} {v : Value} (h : Result L Assumptions.all X i cell v) :
    Dom i → X.async.mmaDone i = true → ∃ r : ℝ, v = .float .f32 r := by
  induction h with
  | overwrite issue position reads arithmetic =>
    intro hdom hd
    obtain ⟨r, hr⟩ := eval_cell hp hX hf base E hdom issue position hd reads (old := none)
      (prev := 0) rfl
    exact ⟨r, Except.ok.inj (arithmetic.symm.trans hr)⟩
  | accumulate issue position reads previous provenance arithmetic ih =>
    intro hdom hd
    rename_i i0 d0 s0 mask0 row0 col0 cell0 ops0 value0 source0 old0
    have hrd : X.MmaReadCell i0 cell0 := ⟨d0, s0, mask0, row0, col0, issue,
      writeCell_resultCell position⟩
    obtain ⟨d1, s1, a1, m1, r1, c1, hi1, hp1⟩ : ∃ d s acc mask row col,
        X.MmaIssue source0 d s acc mask ∧ writeCell s d mask row col = some cell0 := by
      cases previous with
      | overwrite issue' position' => exact ⟨_, _, _, _, _, _, issue', position'⟩
      | accumulate issue' position' => exact ⟨_, _, _, _, _, _, issue', position'⟩
      | accumulateStored issue' position' => exact ⟨_, _, _, _, _, _, issue', position'⟩
    have hm : X.MmaCell source0 cell0 := ⟨d1, s1, a1, m1, r1, c1, hi1, hp1⟩
    have hds := Tmem.acc_mma_done hp hX hf base hG hd hrd provenance hm
    obtain ⟨-, -, hswb, -⟩ := id provenance
    obtain ⟨r2, hr2⟩ := ih (closed _ _ _ hdom hrd hm hswb) hds
    subst hr2
    obtain ⟨r, hr⟩ := eval_cell hp hX hf base E hdom issue position hd reads
      (old := some (.float .f32 r2)) (prev := r2) rfl
    exact ⟨r, Except.ok.inj (arithmetic.symm.trans hr)⟩
  | accumulateStored issue position reads previous provenance arithmetic =>
    intro hdom hd
    rename_i i0 d0 s0 mask0 row0 col0 cell0 ops0 value0 source0 old0
    have hrd : X.MmaReadCell i0 cell0 := ⟨d0, s0, mask0, row0, col0, issue,
      writeCell_resultCell position⟩
    obtain ⟨r1, h1⟩ := E.store hdom hrd provenance previous
    obtain ⟨r, hr⟩ := eval_cell hp hX hf base E hdom issue position hd reads (old := some old0)
      (prev := r1) (by simpa [Assumption.idealMmaAccumulator] using h1)
    exact ⟨r, Except.ok.inj (arithmetic.symm.trans hr)⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
