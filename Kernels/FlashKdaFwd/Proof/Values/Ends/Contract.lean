-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Values.Ends.Defs
public import Kernels.FlashKdaFwd.Proof.Protocol.ReadBack
public import Kernels.FlashKdaFwd.Proof.Protocol.ResultGlue

@[expose] public section

/-!
# What the values at the ends of the tile loop take from the other layers

`Proof/Values/Ends/` proves what the data are in the four stretches of the kernel around the
tile loop: the conversion loop, the carry loads, the final stores and the element stores of a
partial last tile. The value of a register is followed on the generated thread machine
(`Proof/Thread/`: a state `d` has a site `d.site`, control words `d.w` and data slots `d.x`;
`stateAt (code L) X g k` is the state of thread `g` before position `k` of its trace). This
file states, as one structure per stretch, exactly what that needs from the reference layer of
the stretch's phase (`Proof/Ref/<Phase>`): **where the thread is** and **the address of each
memory event in closed form**. It also states the hypotheses that come from elsewhere.

Words. `g % L.block` is the index `tid` of thread `g` in its thread block and `g / L.block` the
block; a *compute thread* has `tid < 128`. "Window offset `o`" is the byte `L.sharedBase + o`
of the block's shared memory. `bar0Before X (g, k)` is the number of `bar.sync 0` events of
thread `g` before position `k`: three in the conversion loop, five at the carry loads, six in
the tile loops, seven at the final stores. `swzAddr`, the element index, `carryConst`,
`laneOff`, `carrySite` are in `Defs.lean`.

## The four contracts

* `ConvRef` (Conversion phase, instructions 388 to 621, all threads): a conversion load reads
  the four bytes of an element `el` of the FP32 buffer, and the write that follows it is the
  2-byte write of the same element of `state_acc`; a write with three `bar.sync 0` before it is
  the event after a conversion load.
* `CarryRef` (CarryLoad phase, 622 to 1402, compute threads): the `j`-th carry load reads the
  four bytes at the swizzled address of the thread's base pointer plus the `j`-th constant; a
  thread at the `j`-th of these sites was at the first one `j` positions earlier.
* `FinalRef` (Epilogue phase, 3113 to 3835, compute threads): a write with seven `bar.sync 0`
  before it is at one of the 128 final store sites; the `j`-th of them writes four bytes at
  the address of the `j`-th carry; a thread at the `j`-th site was at the first one `j`
  positions earlier.
* `StoreRef` (Store phase, the store path 2945 to 3112 of the store leader): a write to global
  memory is the `(4 + i)`-th event after a state at the vector load 3020; at that state, the
  next twelve events are the four 4-byte reads of one 16-byte chunk of a live row of the
  output stage and the eight 2-byte stores of its eight outputs to `Params.outLoc`.

A fifth structure, `StoreCtl`, is the control half of the three families of stores of data
registers ("if the source converts to the store's width, the event is the write of its
bytes"), which the statements "the event is not undefined behaviour" need (`NoUb.lean`).

All four were tested on the simulator `Gen/simulate.py` (all 192 threads; sequences of 0, 5,
7, 16, 21, 37, 40 tokens; one to three heads; shared bases with bit 7 clear and set): the
addresses, the pairing of each load with its store, that the events of a group are consecutive,
and the numbers of `bar.sync 0`.

Every field speaks about a state the machine follows and an event that exists; none says that
an event is not undefined behaviour because of a data value, which is this layer's part (for
the stores, a field speaks about an event that *is* a write).

## The hypotheses from elsewhere

* `InitContent` (startup phase, with the tensor-load library): what the sixteen loads of the
  initial state write at each byte of the FP32 buffer, in the exact shape of the hypothesis
  `hic` of `UnionFacts.early_read`, with the content `initBuf`. `earlyRead` turns it and the
  protocol layer's contracts into `EarlyRead`: what a read of the buffer returns before the
  tile loop.
* `LeaderReads` (protocol layer and the value induction of the tile loop): what the store
  leader reads from the output buffers, with the protocol layer's content function
  `Protocol.outStage`. It is the premise of the field `elem` of `Protocol.OutContent`
  (`Proof/Protocol/ResultGlue.lean`) for every position; `StorePath.lean: out_elem` takes that
  premise itself, the statements of `NoUb.lean` take `LeaderReads`.
* `FinalCarries` (value induction of the tile loop): at the first final store, the carry
  registers of a compute thread hold the state after the last token.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values.Ends
open PTX PTX.Flow PTX.Frame
open PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Protocol (bar0Before Bar loadLeader storeLeader UnionFacts
  LifeFacts LoadFacts StoreFacts StateFacts InitFacts BarFacts NoEvents Owners blockOf stageOf
  outByte outStage)

noncomputable section

/-! ## A. The conversion loop -/

/-- **From the reference layer of the Conversion phase.** The loop has ten `ld.b32` sites
(`load 21` to `load 30`); the `j`-th is followed by `cvt.rn.bf16.f32` and the `j`-th
`st.shared.b16` (`store 0` to `store 9`). -/
structure ConvRef (L : Launch) (X : Execution) : Prop where
  /-- **A conversion load and the store that follows it.** At the `j`-th load site the thread
  reads, with three `bar.sync 0` before it, the four bytes of the FP32 buffer at the swizzled
  address of an element `el`; and if its next event is a write, that write is the two bytes of
  element `el` of `state_acc`. -/
  load : ∀ g k d e, ∀ j : Fin 10, stateAt (code L) X g k = some (some d) →
    d.site = .load ⟨21 + j.val, by omega⟩ → X.get (g, k) = some e →
    ∃ el < 16384, ∃ a bs, e = ⟨d.site.pc, .rd a bs⟩ ∧ a.size = 4 ∧
      a.loc = ⟨.shared, g / L.block, swzAddr (L.sharedBase + 32768 + 4 * el)⟩ ∧
      bar0Before X (g, k) = 3 ∧
      ∀ pc' a' bs', X.get (g, k + 1) = some ⟨pc', .wr a' bs'⟩ →
        a'.size = 2 ∧ a'.loc = ⟨.shared, g / L.block, L.sharedBase + 2 * el⟩
  /-- **Where a conversion store is.** A write event with three `bar.sync 0` before it is the
  event after a state at a conversion load. -/
  store : ∀ g k pc a bs, X.get (g, k) = some ⟨pc, .wr a bs⟩ → bar0Before X (g, k) = 3 →
    ∃ k0 d, ∃ j : Fin 10, k = k0 + 1 ∧ stateAt (code L) X g k0 = some (some d) ∧
      d.site = .load ⟨21 + j.val, by omega⟩

/-! ## B. The carry loads -/

/-- **From the reference layer of the CarryLoad phase.** The 128 loads are the sites
`carrySite 0` to `carrySite 127` (`load 31` to `load 158`); `carrySite 128` is the proxy fence
after them. -/
structure CarryRef (L : Launch) (X : Execution) : Prop where
  /-- **The `j`-th carry load**: a read, with at most five `bar.sync 0` before it, of the four
  bytes at the swizzled address of the thread's base pointer (`shared_mem + 4 * laneOff tid`)
  plus the constant of the instruction. -/
  load : ∀ g k d e, ∀ j : Fin 128, g % L.block < 128 → stateAt (code L) X g k = some (some d) →
    d.site = carrySite j.val → X.get (g, k) = some e →
    ∃ a bs, e = ⟨d.site.pc, .rd a bs⟩ ∧ a.size = 4 ∧
      a.loc = ⟨.shared, g / L.block,
        swzAddr (L.sharedBase + 4 * laneOff (g % L.block) + carryConst j.val)⟩ ∧
      bar0Before X (g, k) ≤ 5
  /-- **The carry loads are consecutive events.** A compute thread at the `j`-th of these
  sites (or, for `j = 128`, at the fence after them) before position `k` was at the first load
  before position `k - j`. -/
  first : ∀ g k d j, g % L.block < 128 → j ≤ 128 → k ≤ (X.tr g).length →
    stateAt (code L) X g k = some (some d) → d.site = carrySite j →
    j ≤ k ∧ ∃ d0, stateAt (code L) X g (k - j) = some (some d0) ∧ d0.site = carrySite 0

/-! ## C. The final stores -/

/-- The site of the `j`-th final store (`store 18` to `store 145`). -/
def finalSite (j : Fin 128) : Site := .store ⟨18 + j.val, by omega⟩

/-- **From the reference layer of the Epilogue phase.** -/
structure FinalRef (L : Launch) (X : Execution) : Prop where
  /-- **Where a final store is.** A write event with seven `bar.sync 0` before it is an event
  of a compute thread at one of the 128 final store sites. -/
  site : ∀ g k pc a bs, X.get (g, k) = some ⟨pc, .wr a bs⟩ → bar0Before X (g, k) = 7 →
    g % L.block < 128 ∧
      ∃ d, ∃ j : Fin 128, stateAt (code L) X g k = some (some d) ∧ d.site = finalSite j
  /-- **The `j`-th final store**: when its event is a write, it writes the four bytes at the
  address of the `j`-th carry. -/
  store : ∀ g k d pc a bs, ∀ j : Fin 128, g % L.block < 128 →
    stateAt (code L) X g k = some (some d) → d.site = finalSite j →
    X.get (g, k) = some ⟨pc, .wr a bs⟩ →
    a.size = 4 ∧ a.loc = ⟨.shared, g / L.block,
      swzAddr (L.sharedBase + 4 * laneOff (g % L.block) + carryConst j.val)⟩
  /-- **The final stores are consecutive events.** A thread at the `j`-th final store before
  position `k` was at the first one before position `k - j`. -/
  first : ∀ g k d, ∀ j : Fin 128, k ≤ (X.tr g).length →
    stateAt (code L) X g k = some (some d) → d.site = finalSite j →
    j.val ≤ k ∧ ∃ d0, stateAt (code L) X g (k - j.val) = some (some d0) ∧ d0.site = finalSite 0

/-! ## D. The element stores of a partial tile -/

/-- The "full" mbarrier of the output stage of tile `t` in the thread block of `g`: the
compute threads arrive on it after their writes of the stage, the store leader polls it. -/
abbrev storeFullBar (L : Launch) (g t : ℕ) : Loc :=
  (Bar.storeFull ⟨t % 2, Nat.mod_lt _ (by decide)⟩).loc L (g / L.block)

/-- **From the reference layer of the Store phase**, for the path of a partial last tile: per
live row, sixteen times the vector load `ld.shared.v4.b32` at instruction 3020 (the site
`load 177`: four read events of four bytes) and eight `st.global.b16` (`store 10` to
`store 17`). -/
structure StoreRef (P : Params) (L : Launch) (X : Execution) : Prop where
  /-- **Where an element store is.** A write to global memory by a thread is the
  `(4 + i)`-th event after a state at the vector load. -/
  elem : ∀ g k pc a bs, X.get (g, k) = some ⟨pc, .wr a bs⟩ → a.loc.space = .global →
    ∃ k0 d0, ∃ i : Fin 8, k = k0 + 4 + i.val ∧ stateAt (code L) X g k0 = some (some d0) ∧
      d0.site = .load 177
  /-- **One chunk of a live row.** At the vector load, the thread is the store leader of its
  block and there are a tile `t`, a row `row` of it that is a token of the sequence, and a
  chunk `c` of eight value channels such that: the next four events, where they are reads, are
  the four 4-byte elements of the 16 bytes at offset `16 row + 256 c` of the output stage of
  the tile, each after `t / 2 + 1` successful polls of the stage's "full" mbarrier; and the
  eight events after them, where they are writes, are the 2-byte stores of the outputs of the
  channels `8 c` to `8 c + 7` of the token. -/
  chunk : ∀ g k d, stateAt (code L) X g k = some (some d) → d.site = .load 177 →
    g = storeLeader L (g / L.block) ∧
    ∃ t row c, row < 16 ∧ c < 16 ∧ 16 * t + row < P.length (seqOf P L g) ∧
      (∀ m < 4, ∀ pc a bs, X.get (g, k + m) = some ⟨pc, .rd a bs⟩ → a.size = 4 ∧
        a.loc = ⟨.shared, g / L.block,
          L.sharedBase + (86912 + 4096 * (t % 2) + (16 * row + 256 * c + 4 * m))⟩ ∧
        okPolls (storeFullBar L g t) ((X.tr g).take (k + m)) = t / 2 + 1) ∧
      ∀ i : Fin 8, ∀ pc a bs, X.get (g, k + 4 + i.val) = some ⟨pc, .wr a bs⟩ → a.size = 2 ∧
        ∃ v : Fin 128, v.val = 8 * c + i.val ∧
          a.loc = P.outLoc (seqOf P L g) (headOf P L g) (16 * t + row) v

/-! ## The control half of the stores -/

/-- The register that the `j`-th conversion store writes to memory. -/
def convReg (j : ℕ) : ℕ := (Gen.convTable.getD j (0, 0)).2

/-- The register that the `i`-th element store of a partial tile writes to memory. -/
def elemReg (i : ℕ) : ℕ := Gen.elemTable.getD i 0

/-- **From the three phases with stores of data registers: the control half of the stores.**
A store event is a write of the stored form of its source register, or undefined behaviour;
the undefined behaviour comes from the address (no address, misaligned) or from the value (it
does not convert to the store's width). Each field says, for a followed state at a store site
with an event: *if the source converts, the event is the write of its bytes* (the phase proves
that the address is one and is aligned; `Lemmas/Flow/Step/ShapeClasses.lean: shape_stM`). For
the conversion stores and the element stores it also says where the state comes from (the
state form of `ConvRef.store` and `StoreRef.elem`: these locate write events only, and the
event here may be the undefined behaviour to exclude). With the value half of this layer (the
source holds a payload of the store's width), the event is a write: `NoUb.lean`. -/
structure StoreCtl (L : Launch) (X : Execution) : Prop where
  /-- A conversion store: its state follows a state at the conversion load of its pair; if
  the source converts to 16 bits, the event is the write of its bytes. -/
  conv : ∀ g k d e, ∀ j : Fin 10, stateAt (code L) X g k = some (some d) →
    d.site = .store ⟨j.val, by omega⟩ → X.get (g, k) = some e →
    (∃ k0 d0, k = k0 + 1 ∧ stateAt (code L) X g k0 = some (some d0) ∧
      d0.site = .load ⟨21 + j.val, by omega⟩) ∧
    ∀ v', storeValue 16 (d.x (convReg j.val)) = .ok v' → ∃ a, e = ⟨d.site.pc, .wr a v'.toBytes⟩
  /-- A final store: if the source converts to 32 bits, the event is the write of its bytes. -/
  final : ∀ g k d e, ∀ j : Fin 128, g % L.block < 128 →
    stateAt (code L) X g k = some (some d) → d.site = finalSite j → X.get (g, k) = some e →
    ∀ v', storeValue 32 (d.x (carryReg j.val)) = .ok v' → ∃ a, e = ⟨d.site.pc, .wr a v'.toBytes⟩
  /-- An element store of a partial tile: its state is `4 + i` positions after a state at the
  vector load; if the source converts to 16 bits, the event is the write of its bytes. -/
  elem : ∀ g k d e, ∀ i : Fin 8, stateAt (code L) X g k = some (some d) →
    d.site = .store ⟨10 + i.val, by omega⟩ → X.get (g, k) = some e →
    (∃ k0 d0, k = k0 + 4 + i.val ∧ stateAt (code L) X g k0 = some (some d0) ∧
      d0.site = .load 177) ∧
    ∀ v', storeValue 16 (d.x (elemReg i.val)) = .ok v' → ∃ a, e = ⟨d.site.pc, .wr a v'.toBytes⟩

/-! ## The hypotheses from the other layers -/

/-- **From the startup phase: the content of the sixteen loads of the initial state** of
block `c`, in the shape of the hypothesis `hic` of `UnionFacts.early_read`: every byte of the
FP32 buffer has a slot of one of the sixteen loads (the load with `q` earlier ones on the state
barrier) whose record, once the load has notified its barrier, holds the byte
`initBuf P L c o'`, which is defined. -/
def InitContent (P : Params) (L : Launch) (X : Execution) (c : ℕ) : Prop :=
  ∀ o', o' < 65536 → ∃ q < 16, ∃ x y z,
    ∀ i pci al sp, X.get (loadLeader L c, i) = some ⟨pci, .tensorIssue al sp⟩ →
      sp.mbar = Bar.state.loc L c →
      ((X.tr (loadLeader L c)).take i).countP (issuesTo (Bar.state.loc L c)) = q →
      TensorCopy.writeLoc sp x y z = some ⟨.shared, c, L.sharedBase + (32768 + o')⟩ ∧
        ∀ rec, X.tensor (loadLeader L c, i) = some rec → rec.effects.notified = true →
          TensorCopy.writeByte rec x y z = initBuf P L c o' ∧ (initBuf P L c o').isSome

/-- **What a read of the FP32 buffer returns before the tile loop**: a read, with at most five
`bar.sync 0` before it, of bytes at the offset `o` of the buffer returns the content `initBuf`
of the buffer. This is the conclusion of `UnionFacts.early_read` for the content `initBuf`
(`earlyRead`). -/
def EarlyRead (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ g k pc a bs o, X.get (g, k) = some ⟨pc, .rd a bs⟩ → bar0Before X (g, k) ≤ 5 →
    a.loc = ⟨.shared, g / L.block, L.sharedBase + (32768 + o)⟩ → o + a.size ≤ 65536 →
    bs = (List.range a.size).map fun i => initBuf P L (g / L.block) (o + i)

/-- **`EarlyRead` from the protocol layer and the startup phase**: the read-back theorem
`UnionFacts.early_read`, with the contracts of the protocol layer and `InitContent` for every
block. -/
theorem earlyRead {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {T : ℕ → ℕ}
    {O : Owners} (U : UnionFacts L X T O) (hF : LifeFacts L X T) (hLd : LoadFacts L X)
    (hSt : StoreFacts L X) (hS : StateFacts L X) (hI : InitFacts L X) (hB : BarFacts L X T)
    (hN : NoEvents kernel X) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hb : L.block = 192) (hg : SyncGuarded L kernel X) (hic : ∀ c, InitContent P L X c) :
    EarlyRead P L X :=
  fun _ _ _ _ _ o hrd hbar hloc hsz =>
    U.early_read hF hLd hSt hS hI hB hN hX hb hg hrd hbar o _ hloc hsz (hic _)

/-- **From the protocol layer and the value induction of the tile loop: what the store leader
reads from the output buffers.** A read event of the store leader of the block of sequence `s`
and head `h`, at the offset `off` of the output buffer of tile `b`, in rows that are tokens of
the sequence, after `b / 2 + 1` successful polls of the buffer's "full" mbarrier (it has polled
for tile `b` and has not released the buffer), returns the specified content
`Protocol.outStage` of the buffer: the bytes of the bfloat16 payloads of the outputs. This is
the premise of the field `elem` of `Protocol.OutContent` for every position; the assembly gets
it from the read-back `UnionFacts.leader_read` and `OutContent.stage`. -/
def LeaderReads (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {s h : ℕ}, s < P.sequences → h < P.heads →
    ∀ (j pcr : ℕ) (ar : Acc) (br : List (Option Byte)) (b off : ℕ),
      X.get (storeLeader L (blockOf P s h), j) = some ⟨pcr, .rd ar br⟩ →
      ar.loc = outByte L (blockOf P s h) (stageOf b).val off → off + ar.size ≤ 4096 →
      okPolls ((Bar.storeFull (stageOf b)).loc L (blockOf P s h))
        ((X.tr (storeLeader L (blockOf P s h))).take j) = b / 2 + 1 →
      (∀ n < ar.size, 16 * b + (off + n) % 256 / 16 < P.length s) →
        br = (List.range ar.size).map fun n => outStage P s h b (off + n)

/-- **From the value induction of the tile loop: the carries after the last tile.** At the
first final store, the 128 carry registers of a compute thread hold the binary32 payloads of
its entries of the state after the last token of the sequence (the initial state for an empty
sequence). -/
def FinalCarries (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ g k d, g % L.block < 128 → stateAt (code L) X g k = some (some d) → d.site = finalSite 0 →
    CarriesHold (finalState P (g / L.block)) (g % L.block) d.x

end

end PTX.Kernels.FlashKdaFwd.Proof.Values.Ends
