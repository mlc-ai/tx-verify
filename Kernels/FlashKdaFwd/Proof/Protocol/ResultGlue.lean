-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Protocol.ReadBackOut
public import Kernels.FlashKdaFwd.Proof.Protocol.Export
public import Kernels.FlashKdaFwd.Proof.Top.Result
public import Lemmas.Kernel.FrameEnd
public import Lemmas.TensorStore.StoreWrite

@[expose] public section

/-! # The result facts, from facts about single threads

`Proof/Top/Result.lean` derives the postcondition from four facts about one consistent
execution (`ResultFacts`): every output byte and every final-state byte has a performed write
in a complete execution (`outputWritten`, `stateWritten`), and a performed write of such a byte
writes the byte of the specified number (`outputValue`, `stateValue`). This file proves the
four fields, in their exact types, from

1. the contracts of the protocol layer (`Facts`, `UnionFacts`, `StoreCover`), consistency and
   `SyncGuarded L kernel X` (the read-back theorems of `ReadBackOut.lean` need it);
2. `StoresIssued P L X`: what the events that write global memory are, and that the store
   leader has issued them all when it exits. The reference layer owes it;
3. `OutContent P L X O`: what the compute threads wrote into the buffers that the store leader
   copies out. The value layer owes it.

Words: a *block* is a thread block (a "CTA", 192 threads); `blockOf P s h` is the block that
works on sequence `s` and head `h`; its *store leader* is its thread 160 (`storeLeader`), its
*compute threads* are its threads 0 to 127. A *tile* is 16 consecutive tokens of a sequence;
token `t` is row `t % 16` of tile `t / 16`. Tile `b` uses *output buffer* `b % 2` of the block's
shared memory (`stageOf b`; 4096 bytes at offset `86912 + 4096 * (b % 2)`), for the `b / 2`-th
time. `outOff row v k` is the offset in an output buffer of byte `k` of the bfloat16 element of
row `row` and value channel `v`; `outStage P s h b off` is the byte that the specification puts
at offset `off` of the buffer in tile `b`.

## How an output byte leaves the block

* **Full tile.** A tensor store of the store leader copies the byte from the output buffer
  (`StoresIssued.tile` says which byte and in which tile). The store writes what it read
  (`UnionFacts.tile_store_write`), which is the last write of the byte by the compute thread
  that owns it, in that tile; `OutContent.stage` says that this write carries the specified
  byte.
* **Partial last tile.** The store leader reads the live rows of the buffer with ordinary loads
  and writes them with `st.global.b16` (a thread write event; `StoresIssued.elem` says it is the
  leader's). The value passes through the leader's registers: `OutContent.elem` is the
  statement about the leader's write event *given what its read events returned*, and
  `UnionFacts.leader_read` with `OutContent.stage` supplies what they returned.
* **Final state.** A tensor store of the store leader with eight `bar.sync 0` before it
  (`StoresIssued.final`) copies the byte from the FP32 state buffer; it writes the owner's last
  write of the epilogue (`UnionFacts.final_store_write`), which `OutContent.final` says carries
  the specified byte.

For the two "written" fields: in a complete execution the store leader has exited
(`Complete.exit_last`), so it has issued a store event for every byte (`StoresIssued.outIssued`,
`stateIssued`), and an issued tensor store has performed all its writes
(`Complete.store_write`).

## What the value layer has to prove (`OutContent`)

All three fields are about thread events only.

* `stage`: for a byte of a live row of tile `b` (offset `off` of the output buffer, row
  `off % 256 / 16`, with `16 * b + row < P.length s`): the last write event of the owning
  compute thread that covers the byte and has `b / 2` arrivals on `storeFull (b % 2)` before it
  (`OutLast`) has the byte `outStage P s h b off` there.
* `elem`: for a write event of the store leader that covers an output byte of token `t`: *if*
  every earlier read event of the leader that reads bytes of live rows of an output buffer,
  after `b / 2 + 1` successful polls of `storeFull (b % 2)`, returned `outStage P s h b` at
  those bytes, *then* the write event has the specified byte at the output byte. This is the
  data flow through the leader's registers: `ld.shared.v4.b32` (four read events), then eight
  `st.global.b16`.
* `final`: for a tensor store of the store leader whose slot `(x, y, z)` writes byte `b` of
  the final-state entry `(v, k)` and reads the shared byte `l`: the last write event of the
  owning compute thread that covers `l` and has seven `bar.sync 0` before it (`FinalLast`) has
  the byte of the binary32 payload of the final state there. It is stated through the store's
  own slot, so it does not name the swizzled layout of the FP32 state buffer.

## Simulator checks

The fields of `StoresIssued` and the event structure behind `OutContent.elem` were tested on
the control-flow simulator (`Gen/simulate.py`). The
simulator carries no data values and no byte layout inside a tensor store's box, so the three
content statements themselves, and the slot-by-slot form of `tile`, are not testable there. -/

namespace PTX.Kernels.FlashKdaFwd.Protocol
open PTX PTX.Flow PTX.Frame AsyncCopy MBarrier Recurrence

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {O : Owners}

/-! ## Names -/

/-- The block that works on sequence `s` and head `h` (`Spec.gridPlace`: block `c` has
sequence `c % N` and head `c / N`). -/
def blockOf (P : Params) (s h : Nat) : Nat := h * P.sequences + s

/-- The store stage (output buffer) that tile `b` uses. It is the tile's use `b / 2` of that
stage. -/
def stageOf (b : Nat) : Fin 2 := ⟨b % 2, Nat.mod_lt _ (by decide)⟩

/-- The offset, in an output buffer, of byte `k` of the bfloat16 element of row `row` (a token
of the tile) and value channel `v`: the buffer is 16 blocks of 8 channels, each block 16 rows of
16 bytes. -/
def outOff (row : Nat) (v : Fin 128) (k : Nat) : Nat :=
  256 * (v.val / 8) + 16 * row + 2 * (v.val % 8) + k

/-- **The specified content of byte `off` of the output buffer in tile `b`** of sequence `s`
and head `h`: the byte `off % 2` of the bfloat16 payload of the output of token
`16 * b + off % 256 / 16`, value channel `8 * (off / 256) + off % 16 / 2`. -/
noncomputable def outStage (P : Params) (s h b off : Nat) : Option Byte :=
  some ((Value.float .bf16 (P.output s h (16 * b + off % 256 / 16)
    ⟨(8 * (off / 256) + off % 16 / 2) % 128, Nat.mod_lt _ (by decide)⟩)).byteAt (off % 2))

theorem outOff_lt {row k : Nat} (v : Fin 128) (hrow : row < 16) (hk : k < 2) :
    outOff row v k < 4096 := by
  unfold outOff
  have := v.isLt
  omega

/-- The row of `outOff row v k`. -/
theorem outOff_row {row k : Nat} (v : Fin 128) (hrow : row < 16) (hk : k < 2) :
    outOff row v k % 256 / 16 = row := by
  unfold outOff
  have := v.isLt
  omega

/-- The specified content at the offset of an element's byte is that byte of the element. -/
theorem outStage_outOff (P : Params) (s h b : Nat) {row k : Nat} (v : Fin 128)
    (hrow : row < 16) (hk : k < 2) :
    outStage P s h b (outOff row v k) =
      some ((Value.float .bf16 (P.output s h (16 * b + row) v)).byteAt k) := by
  have h1 := outOff_row v hrow hk
  have h2 : (8 * (outOff row v k / 256) + outOff row v k % 16 / 2) % 128 = v.val := by
    unfold outOff
    have := v.isLt
    omega
  have h3 : outOff row v k % 2 = k := by
    unfold outOff
    omega
  simp only [outStage, h1, h2, h3]

theorem blockOf_lt (hP : Pre P L mem0) {s h : Nat} (hs : s < P.sequences) (hh : h < P.heads) :
    blockOf P s h < L.grid := by
  rw [hP.grid]
  unfold blockOf
  have : (h + 1) * P.sequences ≤ P.heads * P.sequences := Nat.mul_le_mul_right _ hh
  rw [Nat.mul_comm P.sequences]
  rw [Nat.add_mul] at this
  omega

/-! ## For the reference layer: blocks and result locations are told apart by their numbers

The fields `tile`, `elem`, `final` of `StoresIssued` start from "this event writes the byte
`(P.outLoc s h t v).at k`". The reference layer knows an event's footprint in closed form, in
terms of the sequence `c % N` and the head `c / N` of the event's block `c`; the lemmas here
turn an equality of such locations into equalities of the indices. -/

theorem blockOf_mod {s h : Nat} (hs : s < P.sequences) : blockOf P s h % P.sequences = s := by
  unfold blockOf
  rw [Nat.add_comm, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt hs

theorem blockOf_div {s h : Nat} (hs : s < P.sequences) : blockOf P s h / P.sequences = h := by
  unfold blockOf
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hs, Nat.zero_add]

/-- A block is the block of its sequence and its head. -/
theorem blockOf_eq (c : Nat) : blockOf P (c % P.sequences) (c / P.sequences) = c := by
  unfold blockOf
  rw [Nat.mul_comm]
  exact Nat.div_add_mod c P.sequences

/-- `a * n + r` determines `a` and `r < n`. -/
theorem mul_add_inj {n a a' r r' : Nat} (hr : r < n) (hr' : r' < n)
    (h : a * n + r = a' * n + r') : a = a' ∧ r = r' := by
  have h1 : (r + a * n) % n = (r' + a' * n) % n := by rw [Nat.add_comm r, Nat.add_comm r', h]
  rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr,
    Nat.mod_eq_of_lt hr'] at h1
  subst h1
  exact ⟨Nat.eq_of_mul_eq_mul_right (m := n) (by omega) (by omega), rfl⟩

/-- A token of a sequence of the batch is one global token: `firstToken s + t` determines the
sequence `s` and the token `t < length s`. -/
theorem token_inj {length : Nat → Nat} {s s' t t' : Nat} (ht : t < length s)
    (ht' : t' < length s') (h : firstToken length s + t = firstToken length s' + t') :
    s = s' ∧ t = t' := by
  rcases Nat.lt_trichotomy s s' with hlt | rfl | hgt
  · have := Proof.Top.firstToken_add_lt hlt ht
    omega
  · exact ⟨rfl, by omega⟩
  · have := Proof.Top.firstToken_add_lt hgt ht'
    omega

/-- **An output byte determines its sequence, head, token, value channel and byte.** -/
theorem outLoc_at_inj {s s' h h' t t' k k' : Nat} {v v' : Fin 128} (hh : h < P.heads)
    (hh' : h' < P.heads) (ht : t < P.length s) (ht' : t' < P.length s') (hk : k < 2)
    (hk' : k' < 2) (heq : (P.outLoc s h t v).at k = (P.outLoc s' h' t' v').at k') :
    s = s' ∧ h = h' ∧ t = t' ∧ v = v' ∧ k = k' := by
  simp only [Params.outLoc, Loc.at, Loc.mk.injEq, true_and] at heq
  have hv := v.isLt
  have hv' := v'.isLt
  obtain ⟨h1, h2⟩ := mul_add_inj (n := P.heads) hh hh'
    (show (firstToken P.length s + t) * P.heads + h =
      (firstToken P.length s' + t') * P.heads + h' by omega)
  obtain ⟨rfl, rfl⟩ := token_inj ht ht' h1
  exact ⟨rfl, h2, rfl, Fin.ext (by omega), by omega⟩

/-- **A final-state byte determines its sequence, head, entry and byte.** -/
theorem stateLoc_at_inj {s s' h h' b b' : Nat} {v v' k k' : Fin 128} (hh : h < P.heads)
    (hh' : h' < P.heads) (hb : b < 4) (hb' : b' < 4)
    (heq : (P.stateLoc s h v k).at b = (P.stateLoc s' h' v' k').at b') :
    s = s' ∧ h = h' ∧ v = v' ∧ k = k' ∧ b = b' := by
  simp only [Params.stateLoc, Loc.at, Loc.mk.injEq, true_and] at heq
  have hv := v.isLt
  have hv' := v'.isLt
  have hk := k.isLt
  have hk' := k'.isLt
  obtain ⟨h1, h2⟩ := mul_add_inj (n := P.heads) hh hh'
    (show s * P.heads + h = s' * P.heads + h' by omega)
  exact ⟨h1, h2, Fin.ext (by omega), Fin.ext (by omega), by omega⟩

/-! ## The two contracts -/

/-- **The events that write global memory** (proved in `Proof/Ref/Assembly/Buffers.lean`). The
first four
fields say what an event is that writes a byte of the result: they are about one thread's
event and counts over the events of that thread before it. The last two say that the store
leader of a block has issued an event for every byte of its result when it exits. -/
structure StoresIssued (P : Params) (L : Launch) (X : Execution) : Prop where
  /-- A tensor store whose slot `(x, y, z)` writes byte `k` of the output of token `t` and
  value channel `v` of `(s, h)` is a store of the store leader of the block of `(s, h)`, issued
  in the tile loop (six `bar.sync 0` before it) after `t / 16 / 2 + 1` successful polls of the
  mbarrier `storeFull` of the stage of tile `t / 16`, and the slot reads the byte at offset
  `outOff (t % 16) v k` of that stage's output buffer. -/
  tile : ∀ {g i pc al x y z s h t k : Nat} {sp : TensorStore.Spec} {v : Fin 128},
    s < P.sequences → h < P.heads → t < P.length s → k < 2 →
    X.get (g, i) = some ⟨pc, .tensorStore al sp⟩ →
    TensorStore.writeLoc sp x y z = some ((P.outLoc s h t v).at k) →
      g = storeLeader L (blockOf P s h) ∧ bar0Before X (g, i) = 6 ∧
      okPolls ((Bar.storeFull (stageOf (t / 16))).loc L (blockOf P s h)) ((X.tr g).take i) =
        t / 16 / 2 + 1 ∧
      TensorStore.readLoc sp x y z =
        some (outByte L (blockOf P s h) (stageOf (t / 16)).val (outOff (t % 16) v k))
  /-- A write event of a thread that covers a byte of the output of a token of `(s, h)` is an
  event of the store leader of the block of `(s, h)` (a `st.global.b16` of the partial last
  tile). -/
  elem : ∀ {g i pc s h t k : Nat} {a : Acc} {bs : List Byte} {v : Fin 128},
    s < P.sequences → h < P.heads → t < P.length s → k < 2 →
    X.get (g, i) = some ⟨pc, .wr a bs⟩ → a.Covers ((P.outLoc s h t v).at k) →
      g = storeLeader L (blockOf P s h)
  /-- A tensor store whose slot writes a byte of the final state of `(s, h)` is a store of the
  store leader of the block of `(s, h)` with eight `bar.sync 0` before it. -/
  final : ∀ {g i pc al x y z s h b : Nat} {sp : TensorStore.Spec} {v k : Fin 128},
    s < P.sequences → h < P.heads → b < 4 →
    X.get (g, i) = some ⟨pc, .tensorStore al sp⟩ →
    TensorStore.writeLoc sp x y z = some ((P.stateLoc s h v k).at b) →
      g = storeLeader L (blockOf P s h) ∧ bar0Before X (g, i) = 8
  /-- No write event of a thread covers a byte of the final state. -/
  finalAsync : ∀ {g i pc s h b : Nat} {a : Acc} {bs : List Byte} {v k : Fin 128},
    s < P.sequences → h < P.heads → b < 4 →
    X.get (g, i) = some ⟨pc, .wr a bs⟩ → ¬ a.Covers ((P.stateLoc s h v k).at b)
  /-- When the store leader of the block of `(s, h)` has exited, it has an event for every byte
  of the output of every token of the sequence: a tensor store with a slot that writes the byte
  (a full tile) or a write event that covers it (the partial last tile). -/
  outIssued : ∀ {s h e pce : Nat}, s < P.sequences → h < P.heads →
    X.get (storeLeader L (blockOf P s h), e) = some ⟨pce, .exit⟩ →
    ∀ t < P.length s, ∀ v : Fin 128, ∀ k < 2,
      (∃ i pc al sp x y z,
        X.get (storeLeader L (blockOf P s h), i) = some ⟨pc, .tensorStore al sp⟩ ∧
        TensorStore.writeLoc sp x y z = some ((P.outLoc s h t v).at k)) ∨
      (∃ i pc a bs, X.get (storeLeader L (blockOf P s h), i) = some ⟨pc, .wr a bs⟩ ∧
        a.Covers ((P.outLoc s h t v).at k))
  /-- When the store leader of the block of `(s, h)` has exited, it has issued a tensor store
  with a slot that writes each byte of the final state of `(s, h)`. -/
  stateIssued : ∀ {s h e pce : Nat}, s < P.sequences → h < P.heads →
    X.get (storeLeader L (blockOf P s h), e) = some ⟨pce, .exit⟩ →
    ∀ v k : Fin 128, ∀ b < 4, ∃ i pc al sp x y z,
      X.get (storeLeader L (blockOf P s h), i) = some ⟨pc, .tensorStore al sp⟩ ∧
      TensorStore.writeLoc sp x y z = some ((P.stateLoc s h v k).at b)

/-- **The content of the writes that the store leader copies out** (proved in
`Proof/Ref/Assembly/Values.lean`; see the module comment). Every field is about write and read
events of threads. -/
structure OutContent (P : Params) (L : Launch) (X : Execution) (O : Owners) : Prop where
  /-- The owning compute thread's last write of a byte of a live row of the output buffer in
  tile `b` carries the specified byte. -/
  stage : ∀ {s h : Nat}, s < P.sequences → h < P.heads → ∀ b off : Nat, off < 4096 →
    16 * b + off % 256 / 16 < P.length s →
    ∀ (ga : Fin 128) (iw : Nat) (aw : Acc) (bw : List Byte),
      O.out (outByte L (blockOf P s h) (stageOf b).val off) = ga.val →
      OutLast L X (blockOf P s h) (stageOf b) ga (b / 2)
        (outByte L (blockOf P s h) (stageOf b).val off) iw aw bw →
        wbyte aw bw (outByte L (blockOf P s h) (stageOf b).val off) = outStage P s h b off
  /-- A write event of the store leader that covers an output byte carries the specified byte
  there, given that its earlier reads of live rows of the output buffers returned the specified
  content of their tiles. -/
  elem : ∀ {s h t k i pc : Nat} {a : Acc} {bs : List Byte} {v : Fin 128},
    s < P.sequences → h < P.heads → t < P.length s → k < 2 →
    X.get (storeLeader L (blockOf P s h), i) = some ⟨pc, .wr a bs⟩ →
    a.Covers ((P.outLoc s h t v).at k) →
    (∀ j < i, ∀ (pcr : Nat) (ar : Acc) (br : List (Option Byte)) (b off : Nat),
      X.get (storeLeader L (blockOf P s h), j) = some ⟨pcr, .rd ar br⟩ →
      ar.loc = outByte L (blockOf P s h) (stageOf b).val off → off + ar.size ≤ 4096 →
      okPolls ((Bar.storeFull (stageOf b)).loc L (blockOf P s h))
        ((X.tr (storeLeader L (blockOf P s h))).take j) = b / 2 + 1 →
      (∀ n < ar.size, 16 * b + (off + n) % 256 / 16 < P.length s) →
        br = (List.range ar.size).map fun n => outStage P s h b (off + n)) →
      wbyte a bs ((P.outLoc s h t v).at k) =
        some ((Value.float .bf16 (P.output s h t v)).byteAt k)
  /-- The owning compute thread's last write in the epilogue of the shared byte that a
  final-state store copies to byte `b` of entry `(v, k)` carries the byte of the final state. -/
  final : ∀ {s h b i pc al x y z : Nat} {sp : TensorStore.Spec} {l : Loc} {v k : Fin 128},
    s < P.sequences → h < P.heads → b < 4 →
    X.get (storeLeader L (blockOf P s h), i) = some ⟨pc, .tensorStore al sp⟩ →
    TensorStore.writeLoc sp x y z = some ((P.stateLoc s h v k).at b) →
    TensorStore.readLoc sp x y z = some l →
    ∀ (ga : Fin 128) (iw : Nat) (aw : Acc) (bw : List Byte), O.final l = ga.val →
      FinalLast L X (blockOf P s h) ga l iw aw bw →
        wbyte aw bw l = some ((Value.float .f32 (P.state s h v (P.length s) k)).byteAt b)

/-! ## The writers of global memory -/

/-- **A performed write that covers a byte of global memory is a write event of a thread or a
write stage of a tensor store**: a tensor load writes shared memory, and the kernel has no
atomic, no linear copy and no cluster-launch-control request. -/
theorem global_write_cases {A : List Assumption} (hX : Consistent L kernel A mem0 X) {w : Ref}
    {a : Acc} {bs : List Byte} {gl : Loc} (hw : X.MemWrites w a bs) (hc : a.Covers gl)
    (hgl : gl.space = .global) :
    (∃ g i pc, w = .thread (g, i) ∧ X.get (g, i) = some ⟨pc, .wr a bs⟩) ∨
    (∃ g i x y z, w = .async (g, i) (.write (.store x y z))) := by
  rcases w with ⟨g, k⟩ | ⟨⟨g, i⟩, part⟩
  · rcases hw with ⟨pc, he⟩ | ⟨old, pc, he⟩
    · exact .inl ⟨g, k, pc, rfl, he⟩
    · exact (no_rmw hX he).elim
  · cases part
    case async.writeStore x y z => exact .inr ⟨g, i, x, y, z, rfl⟩
    case async.writeLoad x y z =>
      obtain ⟨o, addr, b, -, hiss, hwl, -⟩ := hw
      have hsp := load_space hX hiss
      obtain ⟨slot, -, hloc⟩ := Option.map_eq_some_iff.mp hwl
      have : a.loc.space = .shared := by
        rw [← hloc]
        exact hsp
      rw [← hc.1, hgl] at this
      cases this
    case async.writeCopy =>
      obtain ⟨s, hcp, -⟩ := hw
      exact ((noEvents hX).copy _ _ hcp).elim
    case async.writeElem j =>
      obtain ⟨s, hcp, -⟩ := hw
      exact ((noEvents hX).copy _ _ hcp).elim
    case async.writeCta c =>
      obtain ⟨_, _, hi, -⟩ := hw
      exact ((noEvents hX).clc _ _ _ hi).elim
    all_goals exact hw.elim

/-- **In a complete execution the store leader of every block has exited.** -/
theorem leader_exits (hP : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hd : Complete L X) {c : Nat} (hc : c < L.grid) :
    ∃ e pce, X.get (storeLeader L c, e) = some ⟨pce, .exit⟩ := by
  obtain ⟨k, pc, -, he⟩ := Frame.Complete.exit_last hd (storeLeader_lt hP.block hc) (by
    rintro ⟨-, request, h⟩
    obtain ⟨i, s, ts, -, hi, -⟩ := hX.clc.canceled_has_issue h
    exact Proof.Top.noClcIssue hX hi)
  exact ⟨k, pc, he⟩

/-! ## The four fields of `ResultFacts` -/

section fields
variable (hP : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (S : StoresIssued P L X)
include hP hX S

/-- **`ResultFacts.outputWritten`.** -/
theorem outputWritten : Complete L X → ∀ s < P.sequences, ∀ h < P.heads, ∀ t < P.length s,
    ∀ v : Fin 128, ∀ k < 2, ∃ w a bs, X.MemWrites w a bs ∧
      a.Covers ((P.outLoc s h t v).at k) := by
  intro hd s hs h hh t ht v k hk
  obtain ⟨e, pce, he⟩ := leader_exits hP hX hd (blockOf_lt hP hs hh)
  rcases S.outIssued hs hh he t ht v k hk with ⟨i, pc, al, sp, x, y, z, hiss, hwl⟩ |
    ⟨i, pc, a, bs, hget, hcov⟩
  · obtain ⟨o, b, -, -, hw⟩ := hd.store_write hX ⟨pc, hiss⟩ hwl
    exact ⟨_, _, _, hw, rfl, rfl, Nat.le_refl _, Nat.lt_succ_self _⟩
  · exact ⟨.thread (_, i), a, bs, .inl ⟨pc, hget⟩, hcov⟩

/-- **`ResultFacts.stateWritten`.** -/
theorem stateWritten : Complete L X → ∀ s < P.sequences, ∀ h < P.heads, ∀ v k : Fin 128,
    ∀ b < 4, ∃ w a bs, X.MemWrites w a bs ∧ a.Covers ((P.stateLoc s h v k).at b) := by
  intro hd s hs h hh v k b hb
  obtain ⟨e, pce, he⟩ := leader_exits hP hX hd (blockOf_lt hP hs hh)
  obtain ⟨i, pc, al, sp, x, y, z, hiss, hwl⟩ := S.stateIssued hs hh he v k b hb
  obtain ⟨o, b', -, -, hw⟩ := hd.store_write hX ⟨pc, hiss⟩ hwl
  exact ⟨_, _, _, hw, rfl, rfl, Nat.le_refl _, Nat.lt_succ_self _⟩

variable (F : Facts P L X) (U : UnionFacts L X (ctaTiles P) O) (C : StoreCover L X O)
  (V : OutContent P L X O)
include F U C V

/-- **`ResultFacts.outputValue`.** A performed write of an output byte is the write stage of a
tensor store of a full tile, which wrote the owner's last write of the source byte in the tile,
or a write event of the store leader in the partial last tile, whose reads returned the content
of the tile. -/
theorem outputValue (hg : SyncGuarded L kernel X) : ∀ s < P.sequences, ∀ h < P.heads,
    ∀ t < P.length s, ∀ v : Fin 128, ∀ k < 2, ∀ w a bs, X.MemWrites w a bs →
      a.Covers ((P.outLoc s h t v).at k) →
      wbyte a bs ((P.outLoc s h t v).at k) =
        some ((Value.float .bf16 (P.output s h t v)).byteAt k) := by
  intro s hs h hh t ht v k hk w a bs hw hcov
  have hb := hP.block
  have hN := noEvents hX
  have hc := blockOf_lt hP hs hh
  have hrmw : ∀ e pc a o n, X.get e ≠ some ⟨pc, .rmw a o n⟩ := fun _ _ _ _ _ => no_rmw hX
  rcases global_write_cases hX hw hcov rfl with ⟨g, i, pc, rfl, hget⟩ | ⟨g, i, x, y, z, rfl⟩
  · -- the partial last tile: a write event of the store leader
    obtain rfl := S.elem hs hh ht hk hget hcov
    refine V.elem hs hh ht hk hget hcov fun j _ pcr ar br b off hrd hloc hsz hpolls hlive => ?_
    exact U.leader_read C F.life F.load F.store F.state F.init F.bars hN hX hb hg hrmw hc hrd
      (stageOf b) (b / 2) off (outStage P s h b) hpolls hloc hsz fun n hn ga iw aw bw =>
        V.stage hs hh b (off + n) (by omega) (hlive n hn) ga iw aw bw
  · -- a full tile: the write stage of a tensor store
    obtain ⟨rec, addr, b, hrec, ⟨pc, hiss'⟩, hwl, -, hsz, -⟩ := id hw
    have hloc : a.loc = (P.outLoc s h t v).at k := covers_one hsz hcov
    obtain ⟨rfl, hbar, hpolls, hrl⟩ := S.tile hs hh ht hk hiss' (hloc ▸ hwl)
    have hred := (Proof.Top.tensorStore_form hX ⟨pc, hiss'⟩).2.2
    have hrow : t % 16 < 16 := Nat.mod_lt _ (by decide)
    have hoff := outOff_lt v hrow hk
    obtain ⟨hval, -⟩ := U.tile_store_write C F.life F.load F.store F.state F.init F.bars hN hX
      hb hg hrmw hc hiss' hred hbar (stageOf (t / 16)) (t / 16 / 2) (outOff (t % 16) v k) hoff
      hrl hpolls (outStage P s h (t / 16) (outOff (t % 16) v k))
      (V.stage hs hh (t / 16) _ hoff (by rw [outOff_row v hrow hk]; omega)) hw hcov
    rw [hval, outStage_outOff P s h (t / 16) v hrow hk, Nat.div_add_mod]

omit V in
/-- **`ResultFacts.stateValue`**, from the content of the epilogue writes (the field `final`
of `OutContent`). A performed write of a final-state byte is the write stage of a tensor store
of the store leader with eight `bar.sync 0` before it, which wrote the owner's last write of
the source byte in the epilogue. -/
theorem stateValue
    (hfinal : ∀ {s h b i pc al x y z : Nat} {sp : TensorStore.Spec} {l : Loc} {v k : Fin 128},
      s < P.sequences → h < P.heads → b < 4 →
      X.get (storeLeader L (blockOf P s h), i) = some ⟨pc, .tensorStore al sp⟩ →
      TensorStore.writeLoc sp x y z = some ((P.stateLoc s h v k).at b) →
      TensorStore.readLoc sp x y z = some l →
      ∀ (ga : Fin 128) (iw : Nat) (aw : Acc) (bw : List Byte), O.final l = ga.val →
        FinalLast L X (blockOf P s h) ga l iw aw bw →
          wbyte aw bw l = some ((Value.float .f32 (P.state s h v (P.length s) k)).byteAt b)) :
    ∀ s < P.sequences, ∀ h < P.heads, ∀ v k : Fin 128, ∀ b < 4, ∀ w a bs,
      X.MemWrites w a bs → a.Covers ((P.stateLoc s h v k).at b) →
      wbyte a bs ((P.stateLoc s h v k).at b) =
        some ((Value.float .f32 (P.state s h v (P.length s) k)).byteAt b) := by
  intro s hs h hh v k b hb4 w a bs hw hcov
  have hb := hP.block
  have hN := noEvents hX
  have hc := blockOf_lt hP hs hh
  have hrmw : ∀ e pc a o n, X.get e ≠ some ⟨pc, .rmw a o n⟩ := fun _ _ _ _ _ => no_rmw hX
  rcases global_write_cases hX hw hcov rfl with ⟨g, i, pc, rfl, hget⟩ | ⟨g, i, x, y, z, rfl⟩
  · exact (S.finalAsync hs hh hb4 hget hcov).elim
  · obtain ⟨rec, addr, b', hrec, ⟨pc, hiss'⟩, hwl, -, hsz, -⟩ := id hw
    have hloc : a.loc = (P.stateLoc s h v k).at b := covers_one hsz hcov
    obtain ⟨rfl, hbar⟩ := S.final hs hh hb4 hiss' (hloc ▸ hwl)
    have hred := (Proof.Top.tensorStore_form hX ⟨pc, hiss'⟩).2.2
    -- the slot has a shared source byte
    obtain ⟨slot, hslot, -⟩ := Option.bind_eq_some_iff.mp hwl
    have hrl : TensorStore.readLoc rec.spec x y z = some (rec.spec.sharedLoc slot) := by
      simp only [TensorStore.readLoc, hslot, Option.map_some]
    obtain ⟨hval, -⟩ := U.final_store_write C F.life F.load F.store F.state F.init F.bars hN hX
      hb hrmw hc hiss' hred hbar hrl
      (some ((Value.float .f32 (P.state s h v (P.length s) k)).byteAt b))
      (hfinal hs hh hb4 hiss' (hloc ▸ hwl) hrl) hw hcov
    exact hval

/-- **The result facts of one consistent execution**, from the protocol contracts, the events
that write global memory (`StoresIssued`) and the content of the compute threads' writes
(`OutContent`). -/
theorem resultFacts (hg : SyncGuarded L kernel X) : Proof.Top.ResultFacts P L mem0 X where
  outputWritten := outputWritten hP hX S
  outputValue := outputValue hP hX S F U C V hg
  stateWritten := stateWritten hP hX S
  stateValue := stateValue hP hX S F U C V.final

end fields

end PTX.Kernels.FlashKdaFwd.Protocol
