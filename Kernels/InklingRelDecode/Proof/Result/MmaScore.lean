-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.MmaOperand
public import Lemmas.Tcgen05.TcMmaRead

@[expose] public section

/-!
# The S tile: the QK MMAs' values (part (b))

The QK MMAs of iteration `i` write the score buffer `i % 2`: the result cell of tile row `r < 64`
and column `c < 128` is `sCell cta tm i r c` (Layout F of the `64 × 128` MMA of one CTA: row `r`
is lane `r % 16 + 32 (r / 16)`, column `tm + 128 (i % 2) + c`; `qk_writeCell`).

* `qk_eval`: the kernel's assumption evaluates a QK MMA at `(r, c)` to the f32 float
  `Σ_{kk < 16} x kk · y kk` plus the old accumulator, `x` the A elements (the Q tile) and `y` the
  B elements (the K tile) the MMA read (`MmaBf16.eval_all`).
* `qk_result`: the MMA of step `j` leaves in the cell the exact real
  `scorePrefix .. (16 (j + 1)) = Σ_{d < 16 (j + 1)} q(r, d) · K(c, d)`: step 0 does not accumulate
  and overwrites (`Result.overwrite`), step `j + 1` accumulates onto step `j` of the iteration
  (`Result.accumulate` with `QkChain.prev`), and each step adds the 16 products of its operand
  elements (`qk_a_element`, `qk_b_element`).
* `qk_score`: step 7 leaves `Σ_{d < 128} q · K`, which is `Spec.score` of the cell's token, head
  and key: row `r` is token `r / 6` and head `6 kvh + r % 6` (rows `60 … 63` are padding, so
  only valid rows are stated), column `c` is key `128 (split + i · num_splits) + c`
  (`qk_score_spec`).
* `score_load`: a `tcgen05.ld` whose register reads that cell with the last QK MMA as its read
  source returns the f32 word `score` (`LoadReadOk.f32`): the S tile's content after `s_ready`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX PTX.Flow PTX.Proof PTX.TcMma
open PTX.Kernels.InklingRelDecode.Proof.Interface (St TSt ThreadFacts)
open PTX.Kernels.InklingRelDecode.Proof.Ring.Foot (qkDesc pvDesc qkDesc_valid)

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The cells -/

/-- The Tensor Memory cell of row `r` and column `c` of the score buffer of block `i` of CTA
`cta` (accumulator base column `tm`). -/
def sCell (cta tm i r c : Nat) : Cell :=
  ⟨cta, r % 16 + 32 * (r / 16), tm + 128 * (i % 2) + c⟩

theorem qkDesc_facts : LaneAligned qkDesc 0 ∧ resultColumns qkDesc = 128 ∧
    halfDatapath qkDesc = true ∧ qkDesc.m = 64 ∧ qkDesc.n = 128 ∧ qkDesc.group = .one :=
  ⟨by decide, by decide, by decide, rfl, rfl, rfl⟩

/-- **The cells a QK MMA writes**: element `(r, c)` of the `64 × 128` result of an MMA with
accumulator column `tm + 128 (i % 2)` is the cell `sCell`. -/
theorem qk_writeCell {sp : OperandSpec} (hD : sp.descriptor = qkDesc) {cta tm i : Nat}
    (hlow : sp.lowCta = cta) (hT : tm + 384 ≤ 512) {r c : Nat} (hr : r < 64) (hc : c < 128) :
    writeCell sp (tm + 128 * (i % 2)) [0, 0, 0, 0] r c = some (sCell cta tm i r c) := by
  obtain ⟨hla, hrc, hhd, hm, hn, hg⟩ := qkDesc_facts
  have hb : i % 2 < 2 := Nat.mod_lt _ (by omega)
  have e1 : (tm + 128 * (i % 2)) / 2 ^ 16 = 0 := by omega
  have e2 : (tm + 128 * (i % 2)) % 2 ^ 16 = tm + 128 * (i % 2) := by omega
  have hcond : Valid qkDesc ∧ LaneAligned qkDesc ((tm + 128 * (i % 2)) / 2 ^ 16) ∧
      r < qkDesc.m ∧ c < qkDesc.n ∧
      (tm + 128 * (i % 2)) % 2 ^ 16 + resultColumns qkDesc ≤ 512 := by
    rw [e1, e2, hrc, hm, hn]
    exact ⟨qkDesc_valid, hla, hr, hc, by omega⟩
  have hmask : OutputMaskValid CtaGroup.one [0, 0, 0, 0] := by decide
  have hk : ∀ k < 4, [0, 0, 0, 0][k]? = some 0 := by decide
  unfold writeCell resultCell
  simp only [hD, hmask, hcond, not_true_eq_false, ↓reduceIte, hm, hg, hhd, CtaGroup.size, e1, e2,
    hla, hrc, Nat.div_one]
  have h384 : tm + 128 * (i % 2) ≤ 384 := by omega
  have hk2 := hk ((r % 16 + 32 * (r / 16)) / 32) (by omega)
  simp [hr, hlow, Nat.mod_eq_of_lt hr, Nat.div_eq_of_lt hr, h384, hk2, sCell]

/-! ### The evaluation of a QK MMA -/

theorem qkDesc_bytes :
    ((if qkDesc.ws = true ∧ qkDesc.m < 128 then 128 else qkDesc.m) * qkDesc.kind.k *
      qkDesc.kind.width = Operand.bytes .a qkDesc) ∧
    qkDesc.n * qkDesc.kind.k * qkDesc.kind.width = Operand.bytes .b qkDesc := by
  decide

/-- **A QK MMA evaluates to the sum of its 16 products plus its old accumulator.** -/
theorem qk_eval (hX : Consistent L kernel Assumptions.all mem0 X) {m : EvId} {pc dst : Nat}
    {sp : OperandSpec} {acc : Bool} {mask : List Nat}
    (he : X.get m = some ⟨pc, .tc (.mma dst sp acc mask)⟩) (hD : sp.descriptor = qkDesc)
    {ops : AsyncCopy.MmaOperands} (hops : X.async.mmaOperands m = some ops) {r c : Nat}
    (hr : r < 64) (hc : c < 128) {x y : Nat → ℝ}
    (ha : ∀ k < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a r k = .ok (x k))
    (hb : ∀ k < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b c k = .ok (y k))
    {old : Option Value} {prev : ℝ}
    (hprev : Assumption.idealMmaAccumulator .f32 acc old = .ok prev) :
    TcMma.eval Assumptions.all sp.descriptor acc ops.a ops.b old r c =
      .ok (.float .f32 (∑ k ∈ Finset.range 16, x k * y k + prev)) := by
  obtain ⟨-, hla, hlb⟩ := hX.mma_observation_shape ⟨pc, he⟩ hops
  rw [hD] at hla hlb ⊢
  rw [qkDesc_bytes.1] at hla
  rw [qkDesc_bytes.2] at hlb
  obtain ⟨-, -, -, hm, hn, -⟩ := qkDesc_facts
  exact eval_all rfl qkDesc_valid rfl rfl rfl hla hlb (by omega) (by omega) ha hb hprev

/-! ### The prefix sums of the scores -/

/-- The K value of key `c` of block `i` of thread `g`'s CTA at head-dimension index `d`. -/
def kElem (Q : Params) (L : Launch) (g i c d : Nat) : ℝ :=
  Q.kVal (reqOf L g) (kvhOf L g) (128 * blkOf Q L g i + c) d

/-- The first `n` products of the score of tile row `r` and key `c` of block `i`:
`Σ_{d < n} q(r, d) · K(c, d)`. -/
def scorePrefix (Q : Params) (L : Launch) (g i r c n : Nat) : ℝ :=
  ∑ d ∈ Finset.range n, qElem Q L g r d * kElem Q L g i c d

/-- The next 16 products add to the prefix. -/
theorem scorePrefix_step (Q : Params) (L : Launch) (g i r c j : Nat) :
    scorePrefix Q L g i r c (16 * (j + 1)) =
      ∑ k ∈ Finset.range 16, qElem Q L g r (16 * j + k) * kElem Q L g i c (16 * j + k) +
        scorePrefix Q L g i r c (16 * j) := by
  unfold scorePrefix
  rw [show 16 * (j + 1) = 16 * j + 16 by ring, Finset.sum_range_add, add_comm]

/-! ### The chain of the eight QK MMAs -/

/-- **The value a QK MMA leaves in a cell** of a valid row: after step `j` of iteration `d.i` the
cell `(r, c)` of the score buffer holds the exact real `Σ_{d < 16 (j + 1)} q(r, d) · K(c, d)`
as an f32 float (`TcMma.Result`: the derivation of the value, from the operands the MMA read). -/
theorem qk_result (hpre : Pre Q L mem0) (hf : ThreadFacts Q L mem0 X)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hcomp : Complete L X)
    (hc : KvCopies Q L X) (ho : KvOrder Q L X) (hw : MmaWords Q L X) (hq : QTile Q L X)
    (hch : QkChain Q L X) :
    ∀ (j : Nat) (hj : j < 8) {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool}
      {mask : List Nat} {d : Mma.D} {P : Loader.Pro} {r c : Nat}, g < L.threads →
      X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩ →
      St Q L X g k = some (some (.w (.mma d P))) → d.site = .qk ⟨j, hj⟩ → QRowValid Q L g r →
      c < 128 →
      Result L Assumptions.all X (g, k) (sCell (g / L.block) d.tm d.i r c)
        (.float .f32 (scorePrefix Q L g d.i r c (16 * (j + 1)))) := by
  intro j
  induction j with
  | zero =>
    intro hj g k pc dst sp acc mask d P r c hg he hσ hs hr hcc
    obtain ⟨hqo, hdst, hacc, hmask, hI⟩ := qk_event hpre hX hf hg he hσ hs
    obtain ⟨ops, hops⟩ := mma_operands hX hcomp he
    have hT : d.tm = 0 := hw.tm (m := (g, k)) ⟨P, hσ⟩
    have hr64 : r < 64 := by have := hr.1; omega
    have hpos : writeCell sp dst mask r c = some (sCell (g / L.block) d.tm d.i r c) := by
      rw [hdst, hmask]
      exact qk_writeCell hqo.desc hqo.low (by omega) hr64 hcc
    have hacc' : acc = false := by simpa using hacc
    subst hacc'
    refine .overwrite ⟨pc, he⟩ hpos hops ?_
    have h := qk_eval hX he hqo.desc hops hr64 hcc
      (x := fun kk => qElem Q L g r (16 * 0 + kk)) (y := fun kk => kElem Q L g d.i c (16 * 0 + kk))
      (fun kk hk => by simpa using qk_a_element hpre hf hX hq hg he hσ hs hops hr hk)
      (fun kk hk => by simpa [kElem] using qk_b_element hpre hf hX hc ho hw hg he hσ hs hops hcc hk)
      (old := none) (prev := 0) rfl
    rw [h]
    simp [scorePrefix]
  | succ j ih =>
    intro hj g k pc dst sp acc mask d P r c hg he hσ hs hr hcc
    obtain ⟨hqo, hdst, hacc, hmask, hI⟩ := qk_event hpre hX hf hg he hσ hs
    obtain ⟨ops, hops⟩ := mma_operands hX hcomp he
    have hT : d.tm = 0 := hw.tm (m := (g, k)) ⟨P, hσ⟩
    have hr64 : r < 64 := by have := hr.1; omega
    have hpos : writeCell sp dst mask r c = some (sCell (g / L.block) d.tm d.i r c) := by
      rw [hdst, hmask]
      exact qk_writeCell hqo.desc hqo.low (by omega) hr64 hcc
    have hacc' : acc = true := by simpa using hacc
    subst hacc'
    obtain ⟨k', hk', hσ', ⟨pc', dst', sp', acc', mask', he'⟩, hrs⟩ :=
      hch.prev (j := j) (by omega) hσ hs
    have hih := ih (by omega) hg he' hσ' rfl hr hcc
    have hmc : X.MmaCell (g, k) (sCell (g / L.block) d.tm d.i r c) :=
      ⟨_, _, _, _, _, _, ⟨pc, he⟩, hpos⟩
    refine .accumulate ⟨pc, he⟩ hpos hops hih (hrs _ hmc) ?_
    have h := qk_eval hX he hqo.desc hops hr64 hcc
      (x := fun kk => qElem Q L g r (16 * (j + 1) + kk))
      (y := fun kk => kElem Q L g d.i c (16 * (j + 1) + kk))
      (fun kk hk => by simpa using qk_a_element hpre hf hX hq hg he hσ hs hops hr hk)
      (fun kk hk => by simpa [kElem] using qk_b_element hpre hf hX hc ho hw hg he hσ hs hops hcc hk)
      (old := some (.float .f32 (scorePrefix Q L g d.i r c (16 * (j + 1)))))
      (prev := scorePrefix Q L g d.i r c (16 * (j + 1)))
      (idealMmaAccumulator_f32 _)
    rw [h, scorePrefix_step Q L g d.i r c (j + 1)]

/-! ### The score and the S tile after `s_ready` -/

/-- **The 128 products of the full score are `Spec.score`.** Row `r` is token `r / 6` and head
`6 kvh + r % 6` of the thread's request and KV head, column `c` is the key `128 (split + i ·
num_splits) + c`. -/
theorem scorePrefix_score (Q : Params) (L : Launch) (g i r c : Nat) :
    scorePrefix Q L g i r c 128 =
      score Q (reqOf L g) (r / 6) (group * kvhOf L g + r % 6) (128 * blkOf Q L g i + c) := by
  unfold scorePrefix score kElem qElem
  have hh : (group * kvhOf L g + r % 6) / group = kvhOf L g := by
    unfold group
    omega
  rw [hh]
  rfl

variable (hpre : Pre Q L mem0) (hf : ThreadFacts Q L mem0 X)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hcomp : Complete L X) (hc : KvCopies Q L X)
    (ho : KvOrder Q L X) (hw : MmaWords Q L X) (hq : QTile Q L X) (hch : QkChain Q L X)
    {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat} {d : Mma.D}
    {P : Loader.Pro} {r c : Nat} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩)
    (hσ : St Q L X g k = some (some (.w (.mma d P))))
include hpre hf hX hcomp hc ho hw hq hch hg he hσ

/-- **The last QK MMA leaves the score.** After step 7 of iteration `i` the cell `(r, c)` of
score buffer `i % 2` holds the f32 float whose real is `Spec.score` of the row's token and head
and the column's key: `Σ_{d < 128} q(r, d) · K(c, d)`. -/
theorem qk_score (hs : d.site = .qk 7) (hr : QRowValid Q L g r) (hcc : c < 128) :
    Result L Assumptions.all X (g, k) (sCell (g / L.block) d.tm d.i r c)
      (.float .f32 (score Q (reqOf L g) (r / 6) (group * kvhOf L g + r % 6)
        (128 * blkOf Q L g d.i + c))) := by
  have h := qk_result hpre hf hX hcomp hc ho hw hq hch 7 (by omega) hg he hσ hs hr hcc
  rw [show 16 * (7 + 1) = 128 by norm_num, scorePrefix_score] at h
  exact h

/-- **The S tile's content after `s_ready`.** A `tcgen05.ld` whose register `j` is the cell
`(r, c)` of the score buffer, with the last QK MMA of the block as its read source, returns the f32
word of the score: the load's register holds the float of `Spec.score`. -/
theorem score_load (hs : d.site = .qk 7) (hr : QRowValid Q L g r) (hcc : c < 128) {ld : EvId}
    {a : Nat} {vals : List Value} {sh : TcShape} {j : Nat} (hld : X.TLd ld a vals sh)
    (hcell : LoadCell L X ld j (sCell (g / L.block) d.tm d.i r c))
    (hrs : ReadSource L X .ld (g, k) ld (sCell (g / L.block) d.tm d.i r c)) :
    vals[j]? = some (.float .f32 (score Q (reqOf L g) (r / 6) (group * kvhOf L g + r % 6)
      (128 * blkOf Q L g d.i + c))) :=
  LoadReadOk.f32 hX.tcRead.1 hld hcell hrs
    (.inl (qk_score hpre hf hX hcomp hc ho hw hq hch hg he hσ hs hr hcc))

end
end PTX.Kernels.InklingRelDecode.Proof.Result.Mma
