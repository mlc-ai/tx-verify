-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tma
public import Core.Tc.TcDataAddress
public import Core.Tmem.TmemObject

@[expose] public section

/-!
# Thread semantics: `tcgen05` instructions

The events these instructions perform. What an allocation, an MMA or a load returns is
decided by the execution rules (OBJ-TMEM-ALLOC-RESULT, DEP-TC-MMA-VALUE, DEP-TC-LOAD-VALUE).
-/

namespace PTX

noncomputable section

/-! ## THREAD-TC — tcgen05 instructions
Statement: Each tcgen05 instruction produces one event of its thread after decoding its operands,
  and a form whose operands do not decode to a supported shape, descriptor or address has no rule.
  An MMA issue reads its descriptors and masks but no operand bytes, a load sets its destination
  registers at its own event to values that the execution rules decide, a store reads its 32-bit
  source registers at issue, and an allocation names only its request, after which lane 0 of the
  warp writes the allocated address, whose column the execution rules decide, to shared memory.
  `tcgen05.alloc` takes a 4-byte aligned shared address and a power of two from 32 to 512 columns.
  It is one request event per lane, which carries no column. Lane 0 then writes the address (lane 0,
  the column returned) to `dst` with a weak 32-bit generic-proxy store (§9.7.18.7.1: "The store
  operation in tcgen05.alloc is treated as a weak memory operation"; the text does not say which
  lane stores, the model says lane 0, EXT-TCALLOC-STORER). The thread state does not depend on the
  column. The stored column (the low 16 bits of the address) is open and is the allocator's result
  (OBJ-TMEM-ALLOC-RESULT). `tcgen05.dealloc` takes the same column counts. `tcgen05.mma` reads its
  destination address, both shared descriptors, the instruction descriptor, `4 * group size`
  output-lane mask words and the `enable-input-d` operand. It decodes the descriptors
  (THREAD-TC-SHARED-DESCRIPTOR, THREAD-TC-MMA-DESCRIPTOR) and resolves the group's CTAs from the
  launch (THREAD-TC-MMA-OPERANDS). A form it cannot decode has no rule, and shape, mask, address and
  lifetime coverage of a decoded issue are safety checks (ERR-TC-MMA). The `[a-tmem]` form
  reads A's Tensor Memory address, so the spec's `a` field is then unused. It is otherwise the same
  rule, except that a set Transpose A bit has no rule there (§9.7.18.10.6 gives the bit its M-major
  meaning for A in shared memory only, and nothing for A in Tensor Memory). With `.ws` and A in
  Tensor Memory it reads one A row per D lane when M < 128 (EXT-TCFIG). `tcgen05.mma.ws`
  (cta_group::1) has no lane-mask operand and is the same rule with an all-zero mask of four words
  (the decoder supplies it), so every lane is written. The issue records the collector usage of A
  and B in its operands (`TcMma.Collectors`). Which reuses are safe is ERR-TC-COLLECTOR-REUSE. A
  `.ws` zero-column mask descriptor is read at issue, and only one that generates the all-zero mask
  with no column shift (Table 54: "Value 0 indicates generated mask will have all 0s") has a rule
  (`zeroColumnMaskNone`). The issue is then that of the form without the operand. The mask that
  other values generate is described by Table 54 and its examples, whose start counts and spans the
  model does not decode, so they have no rule. The lane-mask operand of `tcgen05.mma` may be
  omitted: the ISA's own examples issue the instruction without it (§9.7.18.12.1:
  "tcgen05.mma.cta_group::2.kind::tf32 [taddr0], adesc, bdesc, idesc, p;"; §9.7.18.8.5:
  "tcgen05.mma.cta_group::1.kind::f16 [taddr0], a-desc, b-desc, idesc, p;"), and only a 1 bit of a
  supplied mask keeps a lane from being written (§9.7.18.10.10.1: "If a bit in the mask is 1, then
  the corresponding lane in the Tensor Memory for the resultant matrix D will not be updated.").
  Without it the decoder supplies `4 * group size` zero words, as for `.ws`, so every lane is
  written. `enable-input-d` is a predicate register, whose value must be a predicate, or an integer
  constant, false exactly when zero (§4.5.3: "In PTX, integer constants may be used as predicates.
  For predicate-type data initializers and instruction operands, integer constants are interpreted
  as in C, i.e., zero values are False and non-zero values are True ."). The same reading serves
  `.ws`. The A address of the `[a-tmem]` form may carry a constant offset, `[a-tmem+imm]` (the
  frozen FlashAttention-4 PTX uses `[tmem_a + 0x8]` to `[tmem_a + 0x38]`). A Tensor Memory address
  has no byte unit. It is a lane index (bits 31 to 16) and a column index (bits 15 to 0)
  (§9.7.18.1.1), so the address is the register with `imm` added to its column index, `r % 2^16 +
  imm` in lane field `r / 2^16` (`tmemOffset`). An offset that would leave the column field (below 0
  or at `2^16` and above), and so carry into or borrow from the lane index, faults (stricter: the
  text gives no meaning to such a sum). The destination `[d-tmem]` takes a register only.
  `tcgen05.ld.<shape>.x<num>` of `n` registers (`n` is `.num` repetitions of the shape, Table 59,
  `TcShape.countOk`) takes its lane field as a lane of the issuing warp's chunk, absolute or
  relative, and a `.16x32bx2` half-split offset that stays in the column field. Each register's
  physical TMEM cell is selected by the shape's fragment, the warp's position within its warpgroup
  and the thread lane (THREAD-TC-DATA-ADDRESS, EXT-TMEM-LANE-FIELD). The event
  records the shape. It sets its destination registers at its own event, so a later instruction of
  the thread reads the loaded values whether or not a `tcgen05.wait::ld` comes between them.
  §9.7.18.6.4.5 gives this true register dependency: "For tcgen05.ld , an intra-thread ordering
  through true register dependency will be respected regardless of the presence or absence of other
  forms of synchronization." The same section says that it orders no memory access: "This form of
  register dependency does not imply any other form of ordering. For example, a register dependency
  does not imply that a dependee instruction’s memory accesses will be performed before a dependent
  instruction’s memory accesses. To enforce such memory orderings and avoiding anti-dependency
  hazards around tcgen05.ld , tcgen05.wait::ld must be used." The load's Tensor Memory read is
  therefore ordered before a later write of the cell only by the rules on Tensor Memory accesses:
  its thread's `tcgen05.wait::ld` followed by a tcgen05 order, or a later `tcgen05.st` of the same
  warp (`TcMma.ReadBefore .ld`, DEP-TC-READ-SOURCE, with DEP-TC-FENCE and EXT-TCACQUIRE). A write of
  a loaded cell that is not so ordered after the load leaves the register without a stable source
  and the execution unsafe (ERR-TMEM-READ-SOURCE), and a release needs the load completed by its
  `wait::ld` (`TcMma.CompletedBefore`, DEP-TC-COMPLETION). `tcgen05.st.<shape>.x<num>` has the
  same count, address and cell rules (Table 61) and reads its `n` source registers at issue (its
  Tensor Memory write is asynchronous). It moves data (§9.7.18.8: "The threads of the CTA can
  perform the loads and stores to the Tensor Memory of the CTA and move data between registers and
  Tensor Memory."; §9.7.18.8.4: "Instruction tcgen05.st asynchronously stores data from the source
  register r into the Tensor Memory"), so it reads each source as `st.shared` does (`storeTmpl`,
  THREAD-ACCESS): the register's value unchanged (`readValue`), a literal as its 32-bit pattern. A
  value that is not 4 bytes wide is a `typeMismatch` fault. The stored word is that value, so a
  packed pair of f16 payloads or an f32 payload reaches Tensor Memory without re-encoding. Fences
  and `tcgen05.wait::{ld,st}` are events. `tcgen05.cp` (single thread) reads its Tensor Memory
  address (lane field 0, the shape's columns in range) and decodes its shared descriptor. It copies
  into the issuer's CTA, or with `.cta_group::2` into both CTAs of the issuer's pair, which must be
  in the launch (THREAD-TC-CP-CELLS). `tcgen05.shift` (single thread) reads its Tensor Memory
  address (lane field 0, 8 columns in range) and shifts in the issuer's CTA, or with `.cta_group::2`
  in both CTAs of the pair (THREAD-TC-SHIFT-CELLS). An address out of range or a pair outside the
  launch is `badValue`.

Defs: mmaEnable, tmemOffset, zeroColumnMaskNone, zeroColumnMaskOk, mmaSmemTmpl, mmaTmemTmpl,
  TcMmaInstr.collectors, mmaTmpl, tcTmpl, TcMmaInstr.rule_dense, tcTmpl_tcMma_smem,
  tcTmpl_tcMma_tmem

Source:
- §9.7.18.7.1 (tcgen05.alloc, tcgen05.dealloc)
- §9.7.18.10.10.1 (tcgen05.mma)
- §9.7.18.4 (descriptors)
- §9.7.18.5.1 (CTA pairs)
- §9.7.18.8.1 (access restrictions)
- §9.7.18.8.3 (tcgen05.ld)
- §9.7.18.8.4 (tcgen05.st)
- §9.7.18.8.5 (tcgen05.wait)
- §9.7.18.6.4.5 (register dependencies)
- §9.7.18.9.2 (tcgen05.cp)
- §9.7.18.9.3 (tcgen05.shift)
- §9.7.18.11.1 (tcgen05.fence)
- §9.7.18.12.1 (tcgen05.commit)
- §4.5.3 (predicate constants)
- §9.7.18.1.1: "Tensor Memory addresses are 32-bit wide and specify two components."
- EXT-TCALLOC-STORER

Direction: reading

Applies: tcgen05.alloc, tcgen05.dealloc, tcgen05.relinquish_alloc_permit, the tcgen05.mma{.ws} forms
  that `TcMmaInstr.rule` names (kind::{i8,f16,tf32,f8f6f4}, dense) with shared A and B or with A in
  Tensor Memory (`[a-tmem]`, `[a-tmem+imm]`), with or without the lane-mask operand, with any
  collector usage and, for `.ws`, an optional zero-column mask, `enable-input-d` a predicate or a
  constant, tcgen05.fence, tcgen05.ld and tcgen05.st of every shape (`.32x32b`, `.16x64b`,
  `.16x128b`, `.16x256b`, `.16x32bx2`), with `.pack::16b` / `.unpack::16b` for the single-access
  shapes (THREAD-TC-PACK16), tcgen05.wait::ld, tcgen05.wait::st, tcgen05.cp of the shapes of
  PROG-ISA-TC-CP, tcgen05.shift

Premises: Operands read and decode to the supported forms below.

Effect: Event production and local faults. A warp is 32 consecutive threads (the CTA size must be a
  multiple of 32).

### EXT-TCALLOC-STORER — lane 0 stores the allocated address with a generic-proxy weak store

Statement: Of the threads of a warp that execute `tcgen05.alloc`, only lane 0 stores the returned
  Tensor Memory address to the shared `dst`, with one weak 32-bit generic-proxy store after its own
  allocation event. The store is an ordinary thread write. Reads of it are ordered only by the
  existing rules (MEM-MODEL-CAUSALITY `modelCausality`, MEM-READ-AXIOMS `Hidden`, the
  conflicting-access checks ERR-DATA-RACE and ERR-MIXED-SIZE).

Source:
- §9.7.18.7.1: "The store operation in tcgen05.alloc is treated as a weak memory operation in the
    Memory Consistency Model"
- §8.6: "Unless otherwise specified, memory operations as defined in Operation types use generic
    method of memory access, i.e. a generic proxy ."
- §9.7.18.6.5 (only the shared-memory accesses of `tcgen05.mma` and `tcgen05.cp` are performed in
    the async proxy)

Why it is not spec text: The text says that the instruction has a store and that it is weak. It does
  not say which thread of the warp performs it (one lane, every lane, or the executing thread of
  each lane). It names no proxy for this store. The model chooses lane 0, so that the store is one
  event ordered after that lane's allocation by program order. It chooses the generic proxy, the
  §8.6 default for an operation whose proxy is not otherwise specified.

Direction: reading

Effect: If the hardware store is performed by another lane, by every lane or through another proxy,
  a read of the address that the model orders after the store through lane 0's program order, or
  through synchronization that starts at lane 0, may not be ordered after it on hardware, and the
  value read is then not determined. The model does not report that. A program in which every lane
  reads the address only after the whole allocating warp has synchronized does not depend on which
  lane writes. Disclosed by every kernel whose statement names `Op.tcAlloc`: FlashAttn4Fwd,
  FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, TcGemm.

Review: This reading is not stricter as a whole. Reporting another lane's unsynchronized read of the
  address as a race only rejects programs. Fixing the writer (lane 0) and the proxy (generic)
  decides which reads are ordered after the store. The §9.7.18.6.1 same-address ordering of this
  store with non-`tcgen05` instructions ("The Tensor Memory allocation related instructions that
  access shared memory maintain same-address ordering with respect to non- tcgen05 instructions.")
  is realized only through lane 0's own program order. Another lane reads the address back only
  after synchronization, for example §9.7.15.2 `bar.warp.sync` ("threads within warp that wish to
  communicate via memory can store to memory, execute bar.warp.sync , and then safely read values
  stored by other threads in warp"), `bar.sync` or `barrier.cluster`. In the ISA's §9.7.18.7.1
  Example 1 and Example 2, which read the address with `ld.shared` right after the allocation with
  no synchronization, the read of a lane other than 0 is reported as a Race (ERR-DATA-RACE).
-/

/-- The `enable-input-d` operand: a predicate register's value, or an integer constant read as a
predicate (§4.5.3, nonzero is true). -/
def mmaEnable (t : TState) : Opnd → Exec Bool
  | .reg r => do
    let .pred accumulate ← readReg t r | throw .badValue
    pure accumulate
  | .imm v => pure (v ≠ 0)
  | _ => throw .badValue

/-- The Tensor Memory address `[a + off]`: the offset is added to the column field and must
leave it in range, so that the lane field is that of `a`. -/
def tmemOffset (a : Nat) (off : Int) : Exec Nat :=
  let column := (a % 2 ^ 16 : Int) + off
  if 0 ≤ column ∧ column < 2 ^ 16 then pure (a / 2 ^ 16 * 2 ^ 16 + column.toNat)
  else throw .badValue

/-- The zero-column mask descriptor of `.ws` (Table 54) generates the all-zero mask and shifts no
column: its Non-Zero Mask bit (39), its column shift (bits 56 to 61) and the reserved bits (36 to
38, and 62 and 63, which the table does not list) are 0. -/
def zeroColumnMaskNone (x : Nat) : Bool :=
  x / 2 ^ 39 % 2 == 0 && x / 2 ^ 36 % 8 == 0 && x / 2 ^ 56 == 0

/-- The zero-column mask operand, when present, generates the all-zero mask; otherwise no rule. -/
def zeroColumnMaskOk (L : Launch) (g : Nat) (t : TState) : Option Opnd → Exec Unit
  | none => pure ()
  | some z => do
    unless zeroColumnMaskNone (← readBits L g t 64 z).toNat do throw .noRule

/-- An MMA issue with A in shared memory: the descriptors, the masks, `enable-input-d` and the
collector usage `c`. `.ws` writes every lane (no lane mask). -/
def mmaSmemTmpl (L : Launch) (g : Nat) (t : TState) (group : CtaGroup) (ws : Bool)
    (kind : MmaKind) (dst : Nat) (ad bd id : Opnd) (mask : List Opnd) (en : Opnd)
    (zcm : Option Opnd) (c : TcMma.Collectors) : Tmpl := ofExec do
  unless g < L.threads do throw .badValue
  let d ← readBits L g t 32 (.reg dst)
  let a ← readBits L g t 64 ad
  let b ← readBits L g t 64 bd
  let i ← readBits L g t 32 id
  let masks ← mask.mapM (readBits L g t 32)
  unless mask.length = 4 * group.size do throw .badValue
  let accumulate ← mmaEnable t en
  zeroColumnMaskOk L g t zcm
  let some da := TcShared.decode a.toNat | throw .noRule
  let some db := TcShared.decode b.toNat | throw .noRule
  let some descriptor := TcMma.decode group ws kind i.toNat | throw .noRule
  let some spec := TcMma.makeOperands L (g / L.block) descriptor da db | throw .badValue
  pure (.tc (.mma d.toNat { spec with collector := c } accumulate (masks.map BitVec.toNat))
    (next t))

/-- An MMA issue with A in Tensor Memory at `[ta + aoff]`; a set Transpose A bit has no rule. -/
def mmaTmemTmpl (L : Launch) (g : Nat) (t : TState) (group : CtaGroup) (ws : Bool)
    (kind : MmaKind) (dst ta : Nat) (aoff : Int) (bd id : Opnd) (mask : List Opnd) (en : Opnd)
    (zcm : Option Opnd) (c : TcMma.Collectors) : Tmpl := ofExec do
  unless g < L.threads do throw .badValue
  let d ← readBits L g t 32 (.reg dst)
  let a ← tmemOffset (← readBits L g t 32 (.reg ta)).toNat aoff
  let b ← readBits L g t 64 bd
  let i ← readBits L g t 32 id
  let masks ← mask.mapM (readBits L g t 32)
  unless mask.length = 4 * group.size do throw .badValue
  let accumulate ← mmaEnable t en
  zeroColumnMaskOk L g t zcm
  let some db := TcShared.decode b.toNat | throw .noRule
  let some descriptor := TcMma.decode group ws kind i.toNat | throw .noRule
  if descriptor.transposeA then throw .noRule
  let some spec := TcMma.makeOperands L (g / L.block) descriptor db db | throw .badValue
  pure (.tc (.mma d.toNat { spec with aTmem := some a, collector := c }
    accumulate (masks.map BitVec.toNat)) (next t))

/-- The collector usage of an instruction. -/
def TcMmaInstr.collectors (m : TcMmaInstr) : TcMma.Collectors :=
  ⟨m.collectorA, m.collectorB, m.bBuffer⟩

/-- The issue of a `tcgen05.mma` with a rule (`TcMmaInstr.rule`); `ub noRule` otherwise. -/
def mmaTmpl (L : Launch) (g : Nat) (t : TState) (m : TcMmaInstr) : Tmpl :=
  match m.rule, m.a with
  | some .threadTc, .smem ad =>
    mmaSmemTmpl L g t m.group m.ws m.kind m.d ad m.bdesc m.idesc m.mask m.enableD
      m.zeroColumnMask m.collectors
  | some .threadTc, .tmem ta aoff =>
    mmaTmemTmpl L g t m.group m.ws m.kind m.d ta aoff m.bdesc m.idesc m.mask m.enableD
      m.zeroColumnMask m.collectors
  | _, _ => .ub .noRule

/-! ## THREAD-TC-LD-RED — the reduction value of tcgen05.ld.red
Statement: A `tcgen05.ld.red` sets its loaded registers as `tcgen05.ld` does and writes to `redval`
  the minimum or maximum of the values its thread loaded, as unsigned or signed 32-bit integers, or
  as FP32 numbers (their absolute values with `.abs`). The reduction runs over the registers of one
  thread, that is over the columns its lane loaded. The integer forms compare the 32-bit patterns as
  unsigned or two's-complement numbers. The `.f32` forms compare the FP32 numbers (THREAD-NUM). A
  loaded value that is not a 32-bit number, an FP32 NaN or infinity, and an FP32 extreme taken by
  values of different bits have no rule, and the thread's next event is `ub`.

Defs: TcLdRed.reduceInt, TcLdRed.reduceF32, TcLdRed.reduce, ldResult, tcTmpl_tcLd_none

Source:
- §9.7.18.8.3: "The qualifier .red specifies that the reduction operation specified by .redOp is
    performed on the data that is loaded across columns in each lane."
- §9.7.18.8.3: "The result of the reduction operation is written into the corresponding thread’s
    32-bit destination register operand redVal ."
- §9.7.18.8.3: "If .abs qualifier is specified, the absolute values of the loaded data are
    considered for the reduction operation."
- §9.7.18.8.3: "If .NaN qualifier is specified, the result of the reduction operation is canonical
    NaN if either of the inputs to the reduction operation is NaN."

Direction: stricter

Why it is not spec text: The text does not say what a minimum or maximum of NaN is without `.NaN`.
  With `.NaN` the result is a NaN, which the model does not represent, so a NaN input has no rule in
  either case, as has an infinity (THREAD-NUM). The text does not order `-0` and `+0`, so when the
  extreme is taken by values of different bits (two zeros of opposite sign) there is no rule. With
  `.abs` the result is the absolute value, whose bits are determined.

Applies: tcgen05.ld.red of `.32x32b` and `.16x32bx2` with `.min` or `.max` and `.u32`, `.s32` or
  `.f32`

Premises: Every loaded value of the thread is a 4-byte value; for `.f32` each is a finite FP32
  number, and without `.abs` the values that take the extreme have one bit pattern.

Effect: Local completion of the load's continuation (THREAD-TC): `redval` is set at the load's own
  event, with the loaded registers; a failed premise records the fault `noRule` for the thread's
  next event. A register dependency on `redval` orders like one on a loaded register
  (§9.7.18.6.4.5).
-/

/-- The unsigned or signed minimum or maximum of 4-byte values. -/
def TcLdRed.reduceInt (signed isMax : Bool) (vals : List Value) : Exec Value := do
  let xs ← vals.mapM fun v => match v.bitPattern with
    | some n =>
      if v.bytes = 4 then pure (if signed then (BitVec.ofNat 32 n).toInt else (n : Int))
      else throw .typeMismatch
    | none => throw .typeMismatch
  match xs with
  | [] => throw .noRule
  | x :: rest =>
    let m := rest.foldl (fun acc y => if isMax then max acc y else min acc y) x
    pure (.bits 32 (BitVec.ofNat 64 (m % 2 ^ 32).toNat))

/-- The FP32 minimum or maximum, of the absolute values with `abs`: the absolute value as a
number, or the loaded value that takes the extreme when all such values have one bit pattern. -/
def TcLdRed.reduceF32 (isMax abs : Bool) (vals : List Value) : Exec Value := do
  let xs ← vals.mapM fun v => do
    let x ← valFloat .f32 v
    pure (v, if abs then |x| else x)
  match xs with
  | [] => throw .noRule
  | (_, x0) :: rest =>
    let m := rest.foldl (fun acc p => if isMax then max acc p.2 else min acc p.2) x0
    if abs then pure (.float .f32 m) else
      match xs.filter (fun p => decide (p.2 = m)) with
      | (v, _) :: others =>
        if others.all (fun p => p.1.bitPattern == v.bitPattern) then pure v else throw .noRule
      | [] => throw .noRule

/-- The value `redval` receives. -/
def TcLdRed.reduce (r : TcLdRed) (vals : List Value) : Exec Value :=
  match r.ty with
  | .u32 => TcLdRed.reduceInt false r.isMax vals
  | .s32 => TcLdRed.reduceInt true r.isMax vals
  | .f32 => TcLdRed.reduceF32 r.isMax r.abs vals

/-- The thread state after a load into `ds` returned `vals`: with a reduction, `redval` too, or
the fault of a reduction without a rule. -/
def ldResult (t : TState) (ds : List Nat) : Option TcLdRed → List Value → TState
  | none, vals => setRegs t ds vals
  | some r, vals =>
    match r.reduce vals with
    | .ok v => setReg (setRegs t ds vals) r.dst v
    | .error f => { setRegs t ds vals with fault := some f }

/-! ## THREAD-TC-PACK16 — tcgen05.ld .pack::16b and tcgen05.st .unpack::16b
Statement: With `.pack::16b` a `tcgen05.ld` reads two adjacent columns for each register of the
  shape and sets the register to the low 16 bits of the first column's word followed by those of the
  second; with `.unpack::16b` a `tcgen05.st` writes the low and the high 16 bits of each source
  register as the low 16 bits of two adjacent columns and leaves the high 16 bits of those words
  without a known value. The access shape is `TcShape.packed16 s`. Its slot `2 j + h` (h = 0, 1) is
  the lane of register `j` of `s` and the column `c + 2 x + h`, where `c` is the address's column
  and `x` the column of register `j` of `s` from its base, so that the columns of `s` are spread
  over twice as many physical columns. A packed load's event returns one word per slot, and the
  thread sets register `j` to the pair of the low two bytes of slots `2 j` and `2 j + 1`
  (`TcPack16.pack`); the words are related to their sources by DEP-TC-LOAD-VALUE, so only their low
  two bytes matter. An unpacking store's event records, for slot `2 j + h`, the two bytes of
  register `j` at byte `2 h` (`TcPack16.unpack`), a 2-byte value, which DEP-TC-LOAD-VALUE
  (`WordContains`) reads as fixing the low two bytes of the word only.

Defs: TcPack16.half, TcPack16.pack, TcPack16.unpack, tcTmpl_tcSt_plain

Source:
- §9.7.18.8.2: "Packing: two 16-bit chunks can be packed into a single 32-bit chunk in the register
    in tcgen05.ld"
- §9.7.18.8.2: "Unpacking: a single 32-bit chunk in the register can be unpacked into two 16-bit
    chunks in tcgen05.st"
- §9.7.18.8.3: "The optional qualifier .pack::16b can be used to pack two 16-bit elements from
    adjacent columns into a single 32-bit element during the load"
- §9.7.18.8.4: "The optional qualifier .unpack::16b can be used to unpack a 32-bit element in the
    register into two 16-bit elements and store them in adjacent columns"
- EXT-TMEM-LANE-FIELD

Direction: reading

Why it is not spec text: The text does not say whether `immHalfSplitoff` counts packed or physical
  columns. `.16x32bx2` with packing therefore decodes to `Op.unmodeled`.

Applies: tcgen05.ld `.pack::16b` and tcgen05.st `.unpack::16b` of `.32x32b`, `.16x64b`, `.16x128b`
  and `.16x256b`

Premises: The premises of THREAD-TC for the shape without packing.

Effect: Event production: the load event records two words per register, at the cells of
  `TcShape.packed16` (THREAD-TC-DATA-ADDRESS); the store event records two 16-bit values per
  register.
-/

/-- The low two bytes of a word, or the value itself when it is two bytes wide. -/
def TcPack16.half (v : Value) : Value := if v.bytes = 2 then v else .slice v 0 2

/-- The registers of a packed load from the words of its slots: register `j` is the low two
bytes of slot `2 j` followed by those of slot `2 j + 1`. -/
def TcPack16.pack : List Value → List Value
  | lo :: hi :: rest => .pair (TcPack16.half lo) (TcPack16.half hi) :: TcPack16.pack rest
  | _ => []

/-- The slot values of an unpacking store: bytes 0 and 1 of register `j` for slot `2 j`, bytes 2
and 3 for slot `2 j + 1`. -/
def TcPack16.unpack (vals : List Value) : List Value :=
  vals.flatMap fun v => [.slice v 0 2, .slice v 2 2]

/-- The event of a `tcgen05` instruction. -/
def tcTmpl (L : Launch) (g : Nat) (t : TState) : Op → Tmpl
  | .tcAlloc group base off nc => ofExec do
    unless L.block % 32 = 0 do throw .noRule
    let dst ← effAddr L g t .shared base off
    let n ← readBits L g t 32 nc
    unless dst.addr % 4 = 0 do throw .misaligned
    unless Tmem.validColumns n.toNat do throw .badValue
    if t.sub = 0 then
      pure (.tc (.resource group (some dst) (.alloc n.toNat))
        (if laneOf L g = 0 then { t with sub := 1 } else next t))
    else pure (.tcAllocStore dst { t with pc := t.pc + 1, sub := 0 })
  | .tcDealloc group ta nc => ofExec do
    unless L.block % 32 = 0 do throw .noRule
    let a ← readBits L g t 32 ta
    let n ← readBits L g t 32 nc
    unless Tmem.validColumns n.toNat do throw .badValue
    pure (.tc (.resource group none (.dealloc a.toNat n.toNat)) (next t))
  | .tcRelinquish group => ofExec do
    unless L.block % 32 = 0 do throw .noRule
    pure (.tc (.resource group none .relinquish) (next t))
  | .tcMma m => mmaTmpl L g t m
  | .tcFenceBefore => .tc .fenceBefore (next t)
  | .tcFenceAfter => .tc .fenceAfter (next t)
  | .tcLd ds ta (.packed16 s) red => ofExec do
    unless L.block % 32 = 0 do throw .noRule
    unless s.countOk ds.length do throw .noRule
    let a ← readBits L g t 32 (.reg ta)
    unless tcDataAddressOk L g (.packed16 s) a.toNat do throw .noRule
    pure (.tcLd a.toNat (2 * ds.length) (.packed16 s) fun vals =>
      ldResult (next t) ds red (TcPack16.pack vals))
  | .tcLd ds ta shape red => ofExec do
    unless L.block % 32 = 0 do throw .noRule
    unless shape.countOk ds.length do throw .noRule
    let a ← readBits L g t 32 (.reg ta)
    unless tcDataAddressOk L g shape a.toNat do throw .noRule
    pure (.tcLd a.toNat ds.length shape fun vals => ldResult (next t) ds red vals)
  | .tcWaitLd => ofExec do
    unless L.block % 32 = 0 do throw .noRule
    pure (.tc .waitLd (next t))
  | .tcSt ta ss (.packed16 s) => ofExec do
    unless L.block % 32 = 0 do throw .noRule
    unless s.countOk ss.length do throw .noRule
    let a ← readBits L g t 32 (.reg ta)
    unless tcDataAddressOk L g (.packed16 s) a.toNat do throw .noRule
    let vals ← ss.mapM (readValue L g t 32)
    unless vals.all (·.bytes = 4) do throw .typeMismatch
    pure (.tc (.st a.toNat (TcPack16.unpack vals) (.packed16 s)) (next t))
  | .tcSt ta ss shape => ofExec do
    unless L.block % 32 = 0 do throw .noRule
    unless shape.countOk ss.length do throw .noRule
    let a ← readBits L g t 32 (.reg ta)
    unless tcDataAddressOk L g shape a.toNat do throw .noRule
    let vals ← ss.mapM (readValue L g t 32)
    unless vals.all (·.bytes = 4) do throw .typeMismatch
    pure (.tc (.st a.toNat vals shape) (next t))
  | .tcWaitSt => ofExec do
    unless L.block % 32 = 0 do throw .noRule
    pure (.tc .waitSt (next t))
  | .tcCp group shape ta sd fmt => ofExec do
    unless g < L.threads do throw .badValue
    let a ← readBits L g t 32 (.reg ta)
    unless TcCopy.AddressOk shape a.toNat do throw .badValue
    let s ← readBits L g t 64 sd
    let some src := TcShared.decode s.toNat | throw .noRule
    let some ctas := L.ctaGroup (g / L.block) group | throw .badValue
    pure (.tc (.cp { address := a.toNat, src, shape, ctas, fmt }) (next t))
  | .tcShift group ta => ofExec do
    unless g < L.threads do throw .badValue
    let a ← readBits L g t 32 (.reg ta)
    unless TcShift.AddressOk a.toNat do throw .badValue
    let some ctas := L.ctaGroup (g / L.block) group | throw .badValue
    pure (.tc (.shift ⟨a.toNat, ctas⟩) (next t))
  | _ => .ub .noRule

/-- A `tcgen05.ld` without reduction and without `.pack::16b` sets its registers to the loaded
values (the form before `tcgen05.ld.red` and `.pack::16b` were represented). -/
theorem tcTmpl_tcLd_none {L : Launch} {g : Nat} {t : TState} {ds : List Nat} {ta : Nat}
    {shape : TcShape} (h : ∀ s, shape ≠ .packed16 s) :
    tcTmpl L g t (.tcLd ds ta shape none) = ofExec (do
      unless L.block % 32 = 0 do throw .noRule
      unless shape.countOk ds.length do throw .noRule
      let a ← readBits L g t 32 (.reg ta)
      unless tcDataAddressOk L g shape a.toNat do throw .noRule
      pure (.tcLd a.toNat ds.length shape fun vals => setRegs (next t) ds vals)) := by
  cases shape with
  | packed16 s => exact absurd rfl (h s)
  | _ => rfl

/-- A `tcgen05.st` without `.unpack::16b` stores its 32-bit source values (the form before
`.unpack::16b` was represented). -/
theorem tcTmpl_tcSt_plain {L : Launch} {g : Nat} {t : TState} {ta : Nat} {ss : List Opnd}
    {shape : TcShape} (h : ∀ s, shape ≠ .packed16 s) :
    tcTmpl L g t (.tcSt ta ss shape) = ofExec (do
      unless L.block % 32 = 0 do throw .noRule
      unless shape.countOk ss.length do throw .noRule
      let a ← readBits L g t 32 (.reg ta)
      unless tcDataAddressOk L g shape a.toNat do throw .noRule
      let vals ← ss.mapM (readValue L g t 32)
      unless vals.all (·.bytes = 4) do throw .typeMismatch
      pure (.tc (.st a.toNat vals shape) (next t))) := by
  cases shape with
  | packed16 s => exact absurd rfl (h s)
  | _ => rfl

/-- The dense forms of `kind::i8`, `kind::f16` and `kind::tf32` have THREAD-TC. -/
theorem TcMmaInstr.rule_dense {group : CtaGroup} {ws : Bool} {kind : MmaKind} {d : Nat}
    {a : TcMmaA} {bd id : Opnd} {mask : List Opnd} {en : Opnd}
    (hk : kind = .i8 ∨ kind = .f16 ∨ kind = .tf32) :
    (TcMmaInstr.dense group ws kind d a bd id mask en).rule = some .threadTc := by
  rcases hk with rfl | rfl | rfl <;> rfl

/-- The former `Op.tcMma group ws kind d adesc bdesc idesc mask enableD` (A in shared memory)
issues as `mmaSmemTmpl` without zero-column mask and with the default collector usage. -/
theorem tcTmpl_tcMma_smem {L : Launch} {g : Nat} {t : TState} {group : CtaGroup} {ws : Bool}
    {kind : MmaKind} {d : Nat} {ad bd id : Opnd} {mask : List Opnd} {en : Opnd}
    (hk : kind = .i8 ∨ kind = .f16 ∨ kind = .tf32) :
    tcTmpl L g t (.tcMma (.dense group ws kind d (.smem ad) bd id mask en)) =
      mmaSmemTmpl L g t group ws kind d ad bd id mask en none {} := by
  simp only [tcTmpl, mmaTmpl, TcMmaInstr.rule_dense hk]; rfl

/-- The former `Op.tcMmaTs group ws kind d a aOff bdesc idesc mask enableD` (A in Tensor Memory)
issues as `mmaTmemTmpl` without zero-column mask and with the default collector usage. -/
theorem tcTmpl_tcMma_tmem {L : Launch} {g : Nat} {t : TState} {group : CtaGroup} {ws : Bool}
    {kind : MmaKind} {d ta : Nat} {aoff : Int} {bd id : Opnd} {mask : List Opnd} {en : Opnd}
    (hk : kind = .i8 ∨ kind = .f16 ∨ kind = .tf32) :
    tcTmpl L g t (.tcMma (.dense group ws kind d (.tmem ta aoff) bd id mask en)) =
      mmaTmemTmpl L g t group ws kind d ta aoff bd id mask en none {} := by
  simp only [tcTmpl, mmaTmpl, TcMmaInstr.rule_dense hk]; rfl

end

end PTX
