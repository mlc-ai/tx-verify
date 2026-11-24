-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.MmaScore

@[expose] public section

/-!
# The O accumulator: the PV MMAs' values (part (c))

The PV MMAs of iteration `i ≥ 1` work on block `b = i - 1`: eight MMAs `j = 0 … 7`, each adds the
16 products `P(r, 16 j + kk) · V(16 j + kk, n)` to the cell `(r, n)` of `O` (`oCell`: lane
`r % 16 + 32 (r / 16)`, column `tm + 256 + n`). Step 0 of block 0 overwrites; every other step
accumulates (`accumulate = decide (j ≠ 0 ∨ i ≠ 1)`).

* The B elements are the V tile (`pv_b_element`, part (a)).
* The A elements are the probabilities `pElem g r b k` the softmax threads stored in Tensor Memory
  (`PTile`: *premise*: the A read from Tensor Memory is `AReadOk` of the P stores, ordered by
  `bar.sync` and the `p_ready` handoff, `SOHandoff.p_store_before_read`; the words are
  `Sm.Shape`'s `pw`, two bf16 each).
* The accumulator source of step `j + 1` is step `j`. The source of step 0 of block `b ≥ 1` is
  either the last MMA of block `b - 1` (the softmax skipped the rescale: lazy, `alpha = 1`) or the
  default partition's `tcgen05.st` of `alpha ⊙ O` (`OAcc.base`: *premise*, the `Sm` rescale sites'
  load → multiply → store chain, `AccumulateStored.Result.of_rescale`, and the order that puts
  the PV MMA of block `b - 1` before the load and the store before the PV MMA of block `b`
  (`o_done`, whose phase is the open row of `SO.lean`, finding 1)).

`pv_result` is then the exact content of the O cell after step `j` of block `b`:
`oBase b + Σ_{kk < 16 (j + 1)} P(b, kk) · V(b, kk, n)` with `oBase 0 = 0` and
`oBase (b + 1) = alpha (b + 1) · oFull b`, `oFull b = oBase b + Σ_{kk < 128} P · V`: the
`alpha`-rescaled running sum of the online softmax (`Softmax.step`'s `o`, `MmaRun.lean`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX PTX.Flow PTX.Proof PTX.TcMma
open PTX.Kernels.InklingRelDecode.Proof.Interface (St TSt ThreadFacts)
open PTX.Kernels.InklingRelDecode.Proof.Ring.Foot (qkDesc pvDesc pvDesc_valid)

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The cells -/

/-- The Tensor Memory cell of row `r` and column `n` of the output accumulator `O` of CTA `cta`. -/
def oCell (cta tm r n : Nat) : Cell := ⟨cta, r % 16 + 32 * (r / 16), tm + 256 + n⟩

theorem pvDesc_facts : LaneAligned pvDesc 0 ∧ resultColumns pvDesc = 128 ∧
    halfDatapath pvDesc = true ∧ pvDesc.m = 64 ∧ pvDesc.n = 128 ∧ pvDesc.group = .one :=
  ⟨by decide, by decide, by decide, rfl, rfl, rfl⟩

/-- **The cells a PV MMA writes**: element `(r, n)` of the `64 × 128` result of an MMA with
accumulator column `tm + 256` is the cell `oCell`. -/
theorem pv_writeCell {sp : OperandSpec} (hD : sp.descriptor = pvDesc) {cta tm : Nat}
    (hlow : sp.lowCta = cta) (hT : tm + 384 ≤ 512) {r n : Nat} (hr : r < 64) (hn : n < 128) :
    writeCell sp (tm + 256) [0, 0, 0, 0] r n = some (oCell cta tm r n) := by
  obtain ⟨hla, hrc, hhd, hm, hn', hg⟩ := pvDesc_facts
  have e1 : (tm + 256) / 2 ^ 16 = 0 := by omega
  have e2 : (tm + 256) % 2 ^ 16 = tm + 256 := by omega
  have hcond : Valid pvDesc ∧ LaneAligned pvDesc ((tm + 256) / 2 ^ 16) ∧ r < pvDesc.m ∧
      n < pvDesc.n ∧ (tm + 256) % 2 ^ 16 + resultColumns pvDesc ≤ 512 := by
    rw [e1, e2, hrc, hm, hn']
    exact ⟨pvDesc_valid, hla, hr, hn, by omega⟩
  have hmask : OutputMaskValid CtaGroup.one [0, 0, 0, 0] := by decide
  have hk : ∀ k < 4, [0, 0, 0, 0][k]? = some 0 := by decide
  unfold writeCell resultCell
  simp only [hD, hmask, hcond, not_true_eq_false, ↓reduceIte, hm, hg, hhd, CtaGroup.size, e1, e2,
    hla, hrc, Nat.div_one]
  have hk2 := hk ((r % 16 + 32 * (r / 16)) / 32) (by omega)
  have h128 : tm ≤ 128 := by omega
  simp [hr, hlow, Nat.mod_eq_of_lt hr, Nat.div_eq_of_lt hr, h128, hk2, oCell]

theorem pvDesc_bytes :
    ((if pvDesc.ws = true ∧ pvDesc.m < 128 then 128 else pvDesc.m) * pvDesc.kind.k *
      pvDesc.kind.width = Operand.bytes .a pvDesc) ∧
    pvDesc.n * pvDesc.kind.k * pvDesc.kind.width = Operand.bytes .b pvDesc := by
  decide

/-- **A PV MMA evaluates to the sum of its 16 products plus its old accumulator.** -/
theorem pv_eval (hX : Consistent L kernel Assumptions.all mem0 X) {m : EvId} {pc dst : Nat}
    {sp : OperandSpec} {acc : Bool} {mask : List Nat}
    (he : X.get m = some ⟨pc, .tc (.mma dst sp acc mask)⟩) (hD : sp.descriptor = pvDesc)
    {ops : AsyncCopy.MmaOperands} (hops : X.async.mmaOperands m = some ops) {r n : Nat}
    (hr : r < 64) (hn : n < 128) {x y : Nat → ℝ}
    (ha : ∀ k < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a r k = .ok (x k))
    (hb : ∀ k < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b n k = .ok (y k))
    {old : Option Value} {prev : ℝ}
    (hprev : Assumption.idealMmaAccumulator .f32 acc old = .ok prev) :
    TcMma.eval Assumptions.all sp.descriptor acc ops.a ops.b old r n =
      .ok (.float .f32 (∑ k ∈ Finset.range 16, x k * y k + prev)) := by
  obtain ⟨-, hla, hlb⟩ := hX.mma_observation_shape ⟨pc, he⟩ hops
  rw [hD] at hla hlb ⊢
  rw [pvDesc_bytes.1] at hla
  rw [pvDesc_bytes.2] at hlb
  obtain ⟨-, -, -, hm, hn', -⟩ := pvDesc_facts
  exact eval_all rfl pvDesc_valid rfl rfl rfl hla hlb (by omega) (by omega) ha hb hprev

/-! ### The premises -/

/-- **The probabilities in Tensor Memory.** The A element `(r, kk)` of PV MMA `j` of iteration
`i` is the bf16 probability `pElem g r (i - 1) (16 j + kk)` of key `16 j + kk` of block `i - 1`
that the softmax stored for the tile row `r` of thread `g`'s CTA. -/
structure PTile (Q : Params) (L : Launch) (X : Execution)
    (pElem : Nat → Nat → Nat → Nat → ℝ) : Prop where
  elem : ∀ {g k : Nat} {d : Mma.D} {P : Loader.Pro} {j : Fin 8} {ops : AsyncCopy.MmaOperands}
    {r kk : Nat}, St Q L X g k = some (some (.w (.mma d P))) → d.site = .pv j →
    X.async.mmaOperands (g, k) = some ops → QRowValid Q L g r → kk < 16 →
    Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a r kk =
      .ok (pElem g r (d.i - 1) (16 * j.val + kk))

/-- **The accumulator sources of the PV MMAs**, for the rescale factors `alpha g b r` (the factor
by which the softmax scales row `r` of thread `g`'s CTA before block `b ≥ 1`).
* `next`: step `j + 1` accumulates onto step `j` of the same iteration (as `QkChain.prev`).
* `base`: for a valid row (`QRowValid`: a padding row, or a token at or beyond `q_len`, has
  no `Spec` value to agree with: the softmax's `alpha` of such a row is computed from the
  unconstrained `Q` and `Rel` while the machine's comes from garbage score words), step 0 of an
  iteration `i ≥ 2` accumulates onto the last PV MMA of iteration `i - 1`
  (its state is at step 7 of iteration `i - 1`, after one MMA event stream of the role), through
  either no store (the lazy skip: the MMA is the accumulator read source and `alpha = 1`) or a
  `tcgen05.st` of the default partition whose stored word is `alpha` times the value that MMA
  left (the rescale: `StoreValue` of the float of `alpha · v`) and which is the read source. -/
structure OAcc (Q : Params) (L : Launch) (X : Execution) (alpha : Nat → Nat → Nat → ℝ) : Prop
    where
  next : ∀ {g k j : Nat} {d : Mma.D} {P : Loader.Pro} (hj : j + 1 < 8),
    St Q L X g k = some (some (.w (.mma d P))) → d.site = .pv ⟨j + 1, hj⟩ →
    ∃ k', k' < k ∧ St Q L X g k' =
        some (some (.w (.mma { d with site := .pv ⟨j, by omega⟩ } P))) ∧
      (∃ pc dst sp acc mask, X.get (g, k') = some ⟨pc, .tc (.mma dst sp acc mask)⟩) ∧
      ∀ cell, X.MmaCell (g, k) cell → TcMma.ReadSource L X .acc (g, k') (g, k) cell
  base : ∀ {g k : Nat} {d : Mma.D} {P : Loader.Pro},
    St Q L X g k = some (some (.w (.mma d P))) → d.site = .pv 0 → 2 ≤ d.i → ∀ {r n : Nat},
    QRowValid Q L g r → n < 128 →
    ∃ (k' : Nat) (d' : Mma.D), k' < k ∧ St Q L X g k' = some (some (.w (.mma d' P))) ∧
      d'.site = .pv 7 ∧ d'.i + 1 = d.i ∧ d'.tm = d.tm ∧
      (∃ pc dst sp acc mask, X.get (g, k') = some ⟨pc, .tc (.mma dst sp acc mask)⟩) ∧
      ((TcMma.ReadSource L X .acc (g, k') (g, k) (oCell (g / L.block) d.tm r n) ∧
          alpha g (d.i - 1) r = 1) ∨
        ∃ st, TcMma.ReadSource L X .acc st (g, k) (oCell (g / L.block) d.tm r n) ∧
          ∀ v, Result L Assumptions.all X (g, k') (oCell (g / L.block) d.tm r n)
              (.float .f32 v) →
            StoreValue L X st (oCell (g / L.block) d.tm r n)
              (.float .f32 (alpha g (d.i - 1) r * v)))

/-! ### The running sum -/

/-- The V value of key `kk` of block `b` of thread `g`'s CTA at head-dimension column `n`. -/
def vElem (Q : Params) (L : Launch) (g b kk n : Nat) : ℝ :=
  Q.vVal (reqOf L g) (kvhOf L g) (128 * blkOf Q L g b + kk) n

/-- The first `m` terms of the PV sum of block `b`: `Σ_{kk < m} P(b, kk) · V(b, kk, n)`. -/
def pvPrefix (pElem : Nat → Nat → Nat → Nat → ℝ) (Q : Params) (L : Launch) (g r b n m : Nat) :
    ℝ :=
  ∑ kk ∈ Finset.range m, pElem g r b kk * vElem Q L g b kk n

/-- The accumulator after block `b`: the rescaled accumulator after block `b - 1` plus the block's
128 products. -/
def oFull (pElem : Nat → Nat → Nat → Nat → ℝ) (alpha : Nat → Nat → Nat → ℝ) (Q : Params)
    (L : Launch) (g r n : Nat) : Nat → ℝ
  | 0 => pvPrefix pElem Q L g r 0 n 128
  | b + 1 =>
    alpha g (b + 1) r * oFull pElem alpha Q L g r n b +
      pvPrefix pElem Q L g r (b + 1) n 128

/-- The accumulator before block `b`'s products: zero for block 0, else the rescaled accumulator
after block `b - 1`. -/
def oBase (pElem : Nat → Nat → Nat → Nat → ℝ) (alpha : Nat → Nat → Nat → ℝ) (Q : Params)
    (L : Launch) (g r n : Nat) : Nat → ℝ
  | 0 => 0
  | b + 1 => alpha g (b + 1) r * oFull pElem alpha Q L g r n b

theorem oFull_eq (pElem : Nat → Nat → Nat → Nat → ℝ) (alpha : Nat → Nat → Nat → ℝ) (Q : Params)
    (L : Launch) (g r n b : Nat) :
    oFull pElem alpha Q L g r n b =
      oBase pElem alpha Q L g r n b + pvPrefix pElem Q L g r b n 128 := by
  cases b with
  | zero => simp [oFull, oBase]
  | succ b => simp [oFull, oBase]

/-- The next 16 products add to the prefix. -/
theorem pvPrefix_step (pElem : Nat → Nat → Nat → Nat → ℝ) (Q : Params) (L : Launch)
    (g r b n j : Nat) :
    pvPrefix pElem Q L g r b n (16 * (j + 1)) =
      ∑ k ∈ Finset.range 16, pElem g r b (16 * j + k) * vElem Q L g b (16 * j + k) n +
        pvPrefix pElem Q L g r b n (16 * j) := by
  unfold pvPrefix
  rw [show 16 * (j + 1) = 16 * j + 16 by ring, Finset.sum_range_add, add_comm]

/-! ### The chain of the PV MMAs -/

section Chain

variable {pElem : Nat → Nat → Nat → Nat → ℝ} {alpha : Nat → Nat → Nat → ℝ}

/-- **The claim for step `j` of block `b`**: every PV MMA event of iteration `b + 1` at step `j`
leaves in the cell `(r, n)` of a valid row the f32 float of `oBase b + Σ_{kk < 16 (j + 1)}
P(b, kk) · V(b, kk, n)`. -/
def PvValue (pElem : Nat → Nat → Nat → Nat → ℝ) (alpha : Nat → Nat → Nat → ℝ) (Q : Params)
    (L : Launch) (X : Execution) (b j : Nat) : Prop :=
  ∀ {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat} {d : Mma.D}
    {P : Loader.Pro} {r n : Nat} (hj : j < 8), g < L.threads →
    X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩ →
    St Q L X g k = some (some (.w (.mma d P))) → d.site = .pv ⟨j, hj⟩ → d.i = b + 1 →
    QRowValid Q L g r → n < 128 →
    Result L Assumptions.all X (g, k) (oCell (g / L.block) d.tm r n)
      (.float .f32 (oBase pElem alpha Q L g r n b + pvPrefix pElem Q L g r b n (16 * (j + 1))))

variable (hpre : Pre Q L mem0) (hf : ThreadFacts Q L mem0 X)
  (hX : Consistent L kernel Assumptions.all mem0 X) (hcomp : Complete L X)
  (hc : KvCopies Q L X) (ho : KvOrder Q L X) (hw : MmaWords Q L X) (hP : PTile Q L X pElem)
include hpre hf hX hcomp hc ho hw hP

omit hcomp in
/-- The arithmetic of step `j` of block `b = d.i - 1` on an old accumulator `prev`: the MMA's value
is `Σ_{kk < 16} P · V + prev`. -/
theorem pv_arith {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat}
    {d : Mma.D} {P : Loader.Pro} {j : Fin 8} {r n : Nat} {ops : AsyncCopy.MmaOperands}
    (hg : g < L.threads) (he : X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) (hs : d.site = .pv j)
    (hops : X.async.mmaOperands (g, k) = some ops) (hr : QRowValid Q L g r) (hn : n < 128)
    (hD : sp.descriptor = pvDesc) {old : Option Value} {prev : ℝ}
    (hprev : Assumption.idealMmaAccumulator .f32 acc old = .ok prev) :
    TcMma.eval Assumptions.all sp.descriptor acc ops.a ops.b old r n =
      .ok (.float .f32 (∑ kk ∈ Finset.range 16, pElem g r (d.i - 1) (16 * j.val + kk) *
        vElem Q L g (d.i - 1) (16 * j.val + kk) n + prev)) := by
  have hr64 : r < 64 := by have := hr.1; omega
  exact pv_eval hX he hD hops hr64 hn
    (fun kk hk => hP.elem hσ hs hops hr hk)
    (fun kk hk => by
      simpa [vElem] using pv_b_element hpre hf hX hc ho hw hg he hσ hs hops hn hk) hprev

/-- **Step 0 of block 0 overwrites**: the accumulate flag is off. -/
theorem pv_first : PvValue pElem alpha Q L X 0 0 := by
  intro g k pc dst sp acc mask d P r n hj hg he hσ hs hdi hr hn
  obtain ⟨hqo, hdst, hacc, hmask, hI⟩ := pv_event hpre hX hf hg he hσ hs
  obtain ⟨ops, hops⟩ := mma_operands hX hcomp he
  have hT : d.tm = 0 := hw.tm (m := (g, k)) ⟨P, hσ⟩
  have hr64 : r < 64 := by have := hr.1; omega
  have hpos : writeCell sp dst mask r n = some (oCell (g / L.block) d.tm r n) := by
    rw [hdst, hmask]
    exact pv_writeCell hqo.desc hqo.low (by omega) hr64 hn
  have hacc' : acc = false := by simp [hacc, hdi]
  subst hacc'
  refine .overwrite ⟨pc, he⟩ hpos hops ?_
  have h := pv_arith hpre hf hX hc ho hw hP hg he hσ hs hops hr hn hqo.desc
    (old := none) (prev := 0) rfl
  rw [h]
  have hb : d.i - 1 = 0 := by omega
  simp [hb, oBase, pvPrefix, vElem]

/-- **Step `j + 1` accumulates onto step `j`.** -/
theorem pv_next (hO : OAcc Q L X alpha) {b j : Nat} (hprev : PvValue pElem alpha Q L X b j) :
    j + 1 < 8 → PvValue pElem alpha Q L X b (j + 1) := by
  intro _ g k pc dst sp acc mask d P r n hj hg he hσ hs hdi hr hn
  obtain ⟨hqo, hdst, hacc, hmask, hI⟩ := pv_event hpre hX hf hg he hσ hs
  obtain ⟨ops, hops⟩ := mma_operands hX hcomp he
  have hT : d.tm = 0 := hw.tm (m := (g, k)) ⟨P, hσ⟩
  have hr64 : r < 64 := by have := hr.1; omega
  have hpos : writeCell sp dst mask r n = some (oCell (g / L.block) d.tm r n) := by
    rw [hdst, hmask]
    exact pv_writeCell hqo.desc hqo.low (by omega) hr64 hn
  have hacc' : acc = true := by simp [hacc]
  subst hacc'
  obtain ⟨k', hk', hσ', ⟨pc', dst', sp', acc', mask', he'⟩, hrs⟩ :=
    hO.next (j := j) hj hσ hs
  have hih := hprev (by omega) hg he' hσ' rfl hdi hr hn
  have hmc : X.MmaCell (g, k) (oCell (g / L.block) d.tm r n) :=
    ⟨_, _, _, _, _, _, ⟨pc, he⟩, hpos⟩
  refine .accumulate ⟨pc, he⟩ hpos hops hih (hrs _ hmc) ?_
  have h := pv_arith hpre hf hX hc ho hw hP hg he hσ hs hops hr hn hqo.desc
    (old := some (.float .f32 (oBase pElem alpha Q L g r n b +
      pvPrefix pElem Q L g r b n (16 * (j + 1)))))
    (prev := oBase pElem alpha Q L g r n b + pvPrefix pElem Q L g r b n (16 * (j + 1)))
    (idealMmaAccumulator_f32 _)
  have hb : d.i - 1 = b := by omega
  rw [h, hb, pvPrefix_step pElem Q L g r b n (j + 1)]
  congr 2
  ring

/-- **Step 0 of block `b + 1` accumulates onto the last MMA of block `b`**, through the lazy skip
(`alpha = 1`) or the rescale store. -/
theorem pv_base (hO : OAcc Q L X alpha) {b : Nat} (hprev : PvValue pElem alpha Q L X b 7) :
    PvValue pElem alpha Q L X (b + 1) 0 := by
  intro g k pc dst sp acc mask d P r n hj hg he hσ hs hdi hr hn
  obtain ⟨hqo, hdst, hacc, hmask, hI⟩ := pv_event hpre hX hf hg he hσ hs
  obtain ⟨ops, hops⟩ := mma_operands hX hcomp he
  have hT : d.tm = 0 := hw.tm (m := (g, k)) ⟨P, hσ⟩
  have hr64 : r < 64 := by have := hr.1; omega
  have hpos : writeCell sp dst mask r n = some (oCell (g / L.block) d.tm r n) := by
    rw [hdst, hmask]
    exact pv_writeCell hqo.desc hqo.low (by omega) hr64 hn
  have hacc' : acc = true := by simp [hacc]; omega
  subst hacc'
  obtain ⟨k', d', hk', hσ', hs', hdi', htm', ⟨pc', dst', sp', acc', mask', he'⟩, hsrc⟩ :=
    hO.base hσ hs (by omega) hr hn
  have hih := hprev (by omega) hg he' hσ' (d := d') (by simpa using hs') (by omega) hr hn
  have hmc : X.MmaCell (g, k) (oCell (g / L.block) d.tm r n) :=
    ⟨_, _, _, _, _, _, ⟨pc, he⟩, hpos⟩
  have hb : d.i - 1 = b + 1 := by omega
  rw [htm'] at hih
  have hfull : oBase pElem alpha Q L g r n b + pvPrefix pElem Q L g r b n (16 * (7 + 1)) =
      oFull pElem alpha Q L g r n b := by
    rw [oFull_eq]
  rw [hfull] at hih
  rcases hsrc with ⟨hrs, hal⟩ | ⟨st, hrs, hstore⟩
  · refine .accumulate ⟨pc, he⟩ hpos hops hih hrs ?_
    have h := pv_arith hpre hf hX hc ho hw hP hg he hσ hs hops hr hn hqo.desc
      (old := some (.float .f32 (oFull pElem alpha Q L g r n b)))
      (prev := oFull pElem alpha Q L g r n b) (idealMmaAccumulator_f32 _)
    rw [h, hb]
    have hal' : alpha g (b + 1) r = 1 := by simpa [hb] using hal
    simp only [oBase, hal', one_mul]
    rw [pvPrefix_step pElem Q L g r (b + 1) n 0]
    simp only [mul_zero, pvPrefix, Finset.range_zero, Finset.sum_empty, add_zero, zero_add]
    ring_nf
  · have hs' := hstore _ hih
    refine .accumulateStored ⟨pc, he⟩ hpos hops hs' hrs ?_
    have h := pv_arith hpre hf hX hc ho hw hP hg he hσ hs hops hr hn hqo.desc
      (old := some (.float .f32 (alpha g (d.i - 1) r * oFull pElem alpha Q L g r n b)))
      (prev := alpha g (d.i - 1) r * oFull pElem alpha Q L g r n b) (idealMmaAccumulator_f32 _)
    rw [h, hb]
    simp only [oBase]
    rw [pvPrefix_step pElem Q L g r (b + 1) n 0]
    simp only [mul_zero, pvPrefix, Finset.range_zero, Finset.sum_empty, add_zero, zero_add]
    ring_nf

/-- **The value of every PV MMA.** For every block `b` and step `j`, every PV MMA event of
iteration `b + 1` at step `j` leaves in the cell `(r, n)` of a valid row the f32 float of
`oBase b + Σ_{kk < 16 (j + 1)} P(b, kk) · V(b, kk, n)`. -/
theorem pv_result (hO : OAcc Q L X alpha) :
    ∀ b j, j < 8 → PvValue pElem alpha Q L X b j := by
  intro b
  induction b with
  | zero =>
    intro j
    induction j with
    | zero => intro _; exact pv_first hpre hf hX hcomp hc ho hw hP
    | succ j ih => intro hj; exact pv_next hpre hf hX hcomp hc ho hw hP hO (ih (by omega)) hj
  | succ b ihb =>
    intro j
    induction j with
    | zero => intro _; exact pv_base hpre hf hX hcomp hc ho hw hP hO (ihb 7 (by omega))
    | succ j ih => intro hj; exact pv_next hpre hf hX hcomp hc ho hw hP hO (ih (by omega)) hj

/-- **The O accumulator after block `b`.** The last PV MMA of block `b` (step 7 of iteration
`b + 1`) leaves in the cell `(r, n)` of a valid row the f32 float of `oFull b`: the `alpha`-rescaled
running sum `alpha_b · oFull (b - 1) + Σ_{kk < 128} P(b, kk) · V(b, kk, n)`. -/
theorem pv_final (hO : OAcc Q L X alpha) {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool}
    {mask : List Nat} {d : Mma.D} {P : Loader.Pro} {r n b : Nat} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) (hs : d.site = .pv 7) (hdi : d.i = b + 1)
    (hr : QRowValid Q L g r) (hn : n < 128) :
    Result L Assumptions.all X (g, k) (oCell (g / L.block) d.tm r n)
      (.float .f32 (oFull pElem alpha Q L g r n b)) := by
  have h := pv_result hpre hf hX hcomp hc ho hw hP hO b 7 (by omega) (by omega) hg he hσ hs hdi hr
    hn
  rw [oFull_eq]
  exact h

/-- **The O tile's content after `o_final` or `o_done`.** A `tcgen05.ld` whose register `j` is the
cell `(r, n)` of `O`, with the last PV MMA of block `b` as its read source, returns the f32 word
of `oFull b`. -/
theorem o_load (hO : OAcc Q L X alpha) {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool}
    {mask : List Nat} {d : Mma.D} {P : Loader.Pro} {r n b : Nat} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) (hs : d.site = .pv 7) (hdi : d.i = b + 1)
    (hr : QRowValid Q L g r) (hn : n < 128) {ld : EvId} {a : Nat} {vals : List Value}
    {sh : TcShape} {j : Nat} (hld : X.TLd ld a vals sh)
    (hcell : LoadCell L X ld j (oCell (g / L.block) d.tm r n))
    (hrs : ReadSource L X .ld (g, k) ld (oCell (g / L.block) d.tm r n)) :
    vals[j]? = some (.float .f32 (oFull pElem alpha Q L g r n b)) :=
  LoadReadOk.f32 hX.tcRead.1 hld hcell hrs
    (.inl (pv_final hpre hf hX hcomp hc ho hw hP hO hg he hσ hs hdi hr hn))

end Chain

end
end PTX.Kernels.InklingRelDecode.Proof.Result.Mma
