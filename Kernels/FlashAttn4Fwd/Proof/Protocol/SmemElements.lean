-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.QRingSlotSources
public import Kernels.FlashAttn4Fwd.Proof.Protocol.SmemElementsLoad
public import Kernels.FlashAttn4Fwd.Proof.Protocol.OutputRegion
public import Kernels.FlashAttn4Fwd.Proof.Protocol.TcMmaSourcesValues
public import Kernels.FlashAttn4Fwd.Proof.Interface.Async
public import Lemmas.Tcgen05.MmaBytePair
public import Lemmas.Tcgen05.MmaReadSources
public import Lemmas.Tensor.LoadWritten

@[expose] public section

/-! # The shared operand elements of the MMAs: which input element each one is

An MMA reads its shared operands (B, and A when A is in shared memory) from the Q and KV rings
(`MmaReadsRings`, the region layer's premise). Each byte it reads there is the byte the copy of
the read's use wrote (`Rings.read_source`): copy `cnt` of the CTA's loader on the slot, at
element `(x, y)`, byte `z` of its box. That copy's write is visible to the read, so the copy was
notified and wrote the byte (`tensor_notified_of_modelCausality`, `writeByte_of_notified`); it
copied byte `z` of the input element `(copyBatch, copyHead, copyRow + y, copyCol + x)` of Q, K or V
(`copy_readLoc`), which no write reaches (`InputsUnwritten`, the result layer's
`writes_within_output` and `frame`: every global write is a store into O, `input_outside`), so the
byte is its launch byte, byte `z` of the element's FP16 value (`input_byte`). The read returns it
(`mma_read_of_tensor_write`; `ring_byte`).

The two bytes of an operand element are adjacent, the first at an even address
(`OperandSpec.byteLoc_pair`, `OperandSpec.byteLoc_even`), so they are bytes 0 and 1 of one slot
of one box (`Rings.box_eq`, `TensorCopy.box_offset_inj`), loaded by copies of one use, box and
CTA, which have one origin (`copy_congr`): **the element is the FP16 value of that input
element** (`smem_element`). So every element a completed MMA reads from shared memory is an
FP16 value (`smemElements`, the premise `TcMmaSources.SmemElements`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof TcMma

noncomputable section

namespace SmemElements

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **No write reaches a global byte outside O**: the inputs Q, K, V are only read (the result
layer's `frame` of `writes_within_output`). -/
def InputsUnwritten (P : Params) (X : Execution) : Prop :=
  ∀ l : Loc, l.space = .global →
    ¬ (l.cta = 0 ∧ P.oBase ≤ l.addr ∧ l.addr < P.oBase + tensorBytes P P.sq) →
      ∀ w a bs, X.MemWrites w a bs → ¬ a.Covers l

/-- **The byte an MMA reads from a ring slot.** An MMA read of a byte `l` of full barrier `b`'s
region in CTA `cta` returns byte `z` of the FP16 value of the input element
`(copyBatch, copyHead, copyRow + y, copyCol + x)` of copy `cnt` of `cta`'s loader on the slot, a
copy of the read's use that writes its slot `(x, y)`, byte `z` at `l`. -/
theorem ring_byte (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : RingFacts L X) (htm : TmemFacts L X) (hinit : Rings.RingInit L X)
    (hcp : RingCopies P L X) (ha : AsyncFacts P L X) (hun : InputsUnwritten P X) {b : FBar}
    (hb : b.isFull) {cta : Nat} {i : EvId} {isB : Bool} {idx : Nat} {l : Loc}
    {observed : Option Byte} (hl : InRegion L cta b l) (hrd : X.MmaRead i isB idx l observed) :
    ∃ g k cnt pc al x y z,
      cnt = ((X.tr g).take k).countP (issuesTo (b.loc L (2 * (cta / 2)))) ∧
      X.get (g, k) = some ⟨pc, .tensorIssue al (copySpec P L g b cnt)⟩ ∧ ctaOf L g = cta ∧
      cnt / b.copies = Rings.readUse L X (cta / 2) b i ∧
      x < 64 ∧ y < b.copyBytes / 128 ∧ z < 2 ∧
      l = ⟨.shared, cta, Rings.boxBase L b (cnt % b.copies) + TensorSwizzle.offset .b128
        (Rings.boxBase L b (cnt % b.copies)) (128 * y + 2 * x + z)⟩ ∧
      TensorCopy.writeLoc (copySpec P L g b cnt) x y z = some l ∧
      copyBatch P L g b cnt < P.b ∧ copyHead P L g b cnt < P.h ∧
      copyRow P L g b cnt + y < inputRows P b ∧ copyCol L g b cnt + x < 128 ∧
      observed = some ((Value.float .f16 (inputValue P b (copyBatch P L g b cnt)
        (copyHead P L g b cnt) (copyRow P L g b cnt + y) (copyCol L g b cnt + x))).byteAt z) := by
  obtain ⟨gm, km⟩ := i
  have hr : AsyncCovers X (gm, km) (.mmaRead isB idx) l :=
    ⟨{ loc := l, size := 1 }, false, ⟨rfl, rfl, hrd.1⟩, ⟨rfl, rfl, le_refl _, Nat.lt_succ_self _⟩⟩
  obtain ⟨g, k, pc, al, x, y, z, hget, hcta, huse, hwl, hvis, hord⟩ :=
    Rings.read_source hpre hX ht htm hinit hcp hb hl hr
  set cnt := ((X.tr g).take k).countP (issuesTo (b.loc L (2 * (cta / 2)))) with hcnt
  obtain ⟨hx, hy, hz, hleq⟩ := Rings.copy_box hb hwl
  rw [hcta] at hleq
  obtain ⟨o, hobs, hnot⟩ := tensor_notified_of_modelCausality hvis
  obtain ⟨addr, hTI⟩ := (hX.tensor _ o hobs).1
  have hspec : o.spec = copySpec P L g b cnt := by
    obtain ⟨pc', he'⟩ := hTI
    rw [hget] at he'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at he'
    exact he'.2.2.symm
  have hgl : g < L.threads := Frame.lt_of_get hX hget
  have hpb : pairBase L g = 2 * (cta / 2) := by simp only [pairBase, hcta]
  have hw := ha.copy_started (c := 2 * (cta / 2)) hgl hget
    (by simp only [copySpec, hpb]) hb
  obtain ⟨hbt, hhd, hrow, hcol, hrl⟩ := copy_readLoc hpre hb cnt hw hx hy hz
  rw [← hspec] at hrl
  obtain ⟨v, hwb⟩ := writeByte_of_notified hX hobs hnot hrl
  have hv := tensor_writeByte_of_initial hX hobs hTI hrl hwb
    (input_byte hpre hb hbt hhd hrow hcol hz)
    (hun _ rfl (input_outside hpre hb hbt hhd hrow hcol hz))
  have hwl' : TensorCopy.writeLoc o.spec x y z = some l := by rw [hspec]; exact hwl
  have hobsv := mma_read_of_tensor_write hX hrd hobs hTI hwl' hwb hvis hord
  rw [hv] at hobsv
  exact ⟨g, k, cnt, pc, al, x, y, z, rfl, hget, hcta, huse, hx, hy, hz, hleq, hwl, hbt, hhd, hrow,
    hcol, hobsv⟩

/-- A boundary of a ring region is even. -/
theorem region_end_even (hpre : Pre P L mem0) {b : FBar} (hb : b.isFull) :
    (L.sharedBase + b.regionOff + b.regionSize) % 2 = 0 ∧
      ∀ j, Rings.boxBase L b j % 2 = 0 := by
  have := hpre.sharedAlignment
  cases b with
  | qFull st =>
    refine ⟨?_, fun j => ?_⟩ <;>
      simp only [Rings.boxBase, FBar.regionOff, FBar.regionSize, FBar.copyBytes] <;> omega
  | kvFull s =>
    refine ⟨?_, fun j => ?_⟩ <;>
      simp only [Rings.boxBase, FBar.regionOff, FBar.regionSize, FBar.copyBytes] <;>
      (try split_ifs) <;> omega
  | _ => cases hb

/-- **Which input element an MMA's shared operand element is.** The two bytes `2 m` and
`2 m + 1` of a shared operand of an MMA, the first at a byte `l` of full barrier `b`'s region in
CTA `cta`, are the bytes of the FP16 value of the input element
`(copyBatch, copyHead, copyRow + y, copyCol + x)` of copy `cnt` of `cta`'s loader on the slot, a
copy of the read's use whose slot `(x, y)` is at `l`. -/
theorem smem_element (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : RingFacts L X) (htm : TmemFacts L X) (hinit : Rings.RingInit L X)
    (hcp : RingCopies P L X) (ha : AsyncFacts P L X) (hun : InputsUnwritten P X)
    (htc : TcFacts L X) (htt : TcMmaThreadFacts L X) {i : EvId} {d : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} {ops : AsyncCopy.MmaOperands} (hi : X.MmaIssue i d s acc mask)
    (hops : X.async.mmaOperands i = some ops) (isB : Bool) {m : Nat} {l : Loc}
    (hbl : s.byteLoc (if isB then .b else .a) (2 * m) = some l) {b : FBar} (hb : b.isFull)
    {cta : Nat} (hl : InRegion L cta b l) :
    ∃ g k cnt pc al x y,
      cnt = ((X.tr g).take k).countP (issuesTo (b.loc L (2 * (cta / 2)))) ∧
      X.get (g, k) = some ⟨pc, .tensorIssue al (copySpec P L g b cnt)⟩ ∧ ctaOf L g = cta ∧
      cnt / b.copies = Rings.readUse L X (cta / 2) b i ∧ x < 64 ∧ y < b.copyBytes / 128 ∧
      TensorCopy.writeLoc (copySpec P L g b cnt) x y 0 = some l ∧
      copyBatch P L g b cnt < P.b ∧ copyHead P L g b cnt < P.h ∧
      copyRow P L g b cnt + y < inputRows P b ∧ copyCol L g b cnt + x < 128 ∧
      ∀ z, z < 2 → (if isB then ops.b else ops.a)[2 * m + z]? =
        some (some ((Value.float .f16 (inputValue P b (copyBatch P L g b cnt)
          (copyHead P L g b cnt) (copyRow P L g b cnt + y) (copyCol L g b cnt + x))).byteAt
            z)) := by
  obtain ⟨hkd, -, -, -, -, -⟩ := TcMmaSources.mma_desc' htt hi
  have hw2 : s.descriptor.kind.width = 2 := by rw [hkd]; rfl
  obtain ⟨-, -, -, -, hea, heb, -⟩ := htc.mma_shape hi
  have hbl1 : s.byteLoc (if isB then .b else .a) (2 * m + 1) = some (nextLoc l) := by
    rw [OperandSpec.byteLoc_pair s _ m hw2 hea heb, hbl]
    rfl
  have hev : l.addr % 2 = 0 := OperandSpec.byteLoc_even s _ m hw2 hea heb hbl
  obtain ⟨hend, hbe⟩ := region_end_even hpre hb
  have hl1 : InRegion L cta b (nextLoc l) := by
    obtain ⟨h1, h2, h3, h4⟩ := hl
    exact ⟨h1, h2, by simp only [nextLoc]; omega, by simp only [nextLoc]; omega⟩
  obtain ⟨o0, hrd0, hg0⟩ := hX.mma_read_exists hi hops hbl
  obtain ⟨o1, hrd1, hg1⟩ := hX.mma_read_exists hi hops hbl1
  obtain ⟨g, k, cnt, pc, al, x, y, z, hcnt, hget, hcta, huse, hx, hy, hz, hleq, hwl, hbt, hhd, hrow,
    hcol, hv0⟩ := ring_byte hpre hX ht htm hinit hcp ha hun hb hl hrd0
  obtain ⟨g', k', cnt', pc', al', x', y', z', -, -, hcta', huse', hx', hy', hz', hleq', -, -, -, -,
    -, hv1⟩ := ring_byte hpre hX ht htm hinit hcp ha hun hb hl1 hrd1
  have hpos := Rings.copies_pos hb
  have hj : cnt % b.copies < b.copies := Nat.mod_lt _ hpos
  have hj' : cnt' % b.copies < b.copies := Nat.mod_lt _ hpos
  -- the byte offsets of the two bytes in their boxes
  set j := cnt % b.copies with hjdef
  set j' := cnt' % b.copies with hj'def
  have ha0 : l.addr = Rings.boxBase L b j + TensorSwizzle.offset .b128 (Rings.boxBase L b j)
      (128 * y + 2 * x + z) := by rw [hleq]
  have ha1 : l.addr + 1 = Rings.boxBase L b j' + TensorSwizzle.offset .b128
      (Rings.boxBase L b j') (128 * y' + 2 * x' + z') := by
    have := congrArg Loc.addr hleq'
    simpa only [nextLoc] using this
  have hp0 := TensorSwizzle.offset_byte .b128 (Rings.boxBase L b j) (128 * y + 2 * x + z)
  have hp1 := TensorSwizzle.offset_byte .b128 (Rings.boxBase L b j') (128 * y' + 2 * x' + z')
  have hb0 := hbe j
  have hb1 := hbe j'
  obtain rfl : z = 0 := by omega
  obtain rfl : z' = 1 := by omega
  have hsucc := TensorSwizzle.offset_succ .b128 (Rings.boxBase L b j) (128 * y + 2 * x + 0)
    (by omega)
  have hsum : Rings.boxBase L b j' + TensorSwizzle.offset .b128 (Rings.boxBase L b j')
      (128 * y' + 2 * x' + 1) = Rings.boxBase L b j + TensorSwizzle.offset .b128
      (Rings.boxBase L b j) (128 * y + 2 * x + 1) := by
    rw [← ha1, ha0, show 128 * y + 2 * x + 1 = 128 * y + 2 * x + 0 + 1 by omega, hsucc]
    omega
  obtain ⟨hjj, hoff⟩ := Rings.box_eq hb hj' hj (Rings.box_offset_lt' hb _ hx' hy' (by omega))
    (Rings.box_offset_lt' hb _ hx hy (by omega)) hsum
  rw [hjj] at hoff
  obtain ⟨rfl, rfl, -⟩ := TensorCopy.box_offset_inj (base := Rings.boxBase L b j) hx' (by omega)
    hx (by omega) hoff
  -- the two copies load one box
  obtain ⟨e1, e2, e3, e4⟩ := copy_congr (P := P) (b := b) (cnt := cnt') (cnt' := cnt)
    (hcta'.trans hcta.symm) (huse'.trans huse.symm) hjj
  refine ⟨g, k, cnt, pc, al, x', y', hcnt, hget, hcta, huse, hx, hy, hwl, hbt, hhd, hrow, hcol,
    fun zz hzz => ?_⟩
  rcases (by omega : zz = 0 ∨ zz = 1) with rfl | rfl
  · rw [Nat.add_zero, hg0, hv0]
  · rw [hg1, hv1, e1, e2, e3, e4]

/-- **SmemElements**: every element a completed MMA reads from shared memory is an FP16 value. -/
theorem smemElements (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : RingFacts L X) (htm : TmemFacts L X) (hinit : Rings.RingInit L X)
    (hcp : RingCopies P L X) (ha : AsyncFacts P L X) (hun : InputsUnwritten P X)
    (htc : TcFacts L X) (htt : TcMmaThreadFacts L X) (hmr : MmaReadsRings L X) :
    TcMmaSources.SmemElements X := by
  intro i d s acc mask ops row k hi _ hops hk
  obtain ⟨hkd, hm, hn, -, hws, -⟩ := TcMmaSources.mma_desc' htt hi
  have elem : ∀ isB : Bool, row < (if isB then s.descriptor.n else s.descriptor.m) →
      (isB = false → s.aTmem = none) →
      ∃ x, Assumption.idealMmaElement (.f16 .f16 .f32)
        (if isB then .b else .a) (if isB then ops.b else ops.a) row k =
        .ok x := by
    intro isB hrow haT
    have hbytes : 2 * (row * 16 + k) <
        Operand.bytes (if isB then .b else .a) s.descriptor := by
      cases isB <;> simp only [Bool.false_eq_true, ↓reduceIte] at hrow <;>
        simp [Operand.bytes, Operand.rows, Operand.extent, hkd, hm, hn, hws, Kind.k,
          Kind.width] <;> omega
    obtain ⟨l, hbl⟩ : ∃ l, s.byteLoc (if isB then .b else .a) (2 * (row * 16 + k)) = some l := by
      rcases (htc.mma_shape hi).2.2.2.2.2.2.2.2.2 _ _ hbytes with h | ⟨hop, c, hc⟩
      · exact h
      · cases isB
        · simp [aCell, haT rfl] at hc
        · simp at hop
    have hcov : AsyncCovers X i (.mmaRead isB (2 * (row * 16 + k))) l :=
      ⟨{ loc := l, size := 1 }, false, ⟨rfl, rfl, .inl ⟨d, s, acc, mask, hi, hbl⟩⟩,
        ⟨rfl, rfl, le_refl _, Nat.lt_succ_self _⟩⟩
    obtain ⟨cta, b, hb, hreg⟩ := hmr i isB _ l hcov (OperandSpec.byteLoc_shared hbl)
    obtain ⟨g, -, cnt, -, -, x, y, -, -, -, -, -, -, -, -, -, -, -, hz⟩ :=
      smem_element hpre hX ht htm hinit hcp ha hun htc htt hi hops isB hbl hb hreg
    refine ⟨inputValue P b (copyBatch P L g b cnt) (copyHead P L g b cnt)
      (copyRow P L g b cnt + y) (copyCol L g b cnt + x), idealMmaElement_of_bytes ?_⟩
    have h0 := hz 0 (by decide)
    rw [Nat.add_zero] at h0
    rw [take_two h0 (hz 1 (by decide))]
    simp [Value.toBytes, Value.bytes, FloatFmt.bytes, List.range_succ]
  refine ⟨fun hrow => ?_, fun haT hrow => ?_⟩
  · simpa using elem true (by simpa using hrow) (fun h => by cases h)
  · simpa using elem false (by simpa using hrow) (fun _ => haT)

end SmemElements

end
end PTX.Kernels.FlashAttn4Fwd.Proof
