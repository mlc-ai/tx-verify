-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Top.Wire
public import Kernels.FlashKdaFwd.Proof.Thread.Entry
public import Lemmas.Kernel.Frame

@[expose] public section

/-!
# The data half of "no undefined behaviour": what the value layers owe

A thread makes an undefined-behaviour event (`⟨pc, .ub f⟩`) when its instruction faults, and
its machine stops following it (`Frame.stateAt … = none`: a *dead* state) when an instruction
between two events faults; the next event of a thread in a dead state is undefined behaviour.
The reference layer (`Proof/Ref`) proves that no fault comes from the control side (addresses,
barrier operands, tensor maps). What is left is a short list of sites at which the outcome
depends on a data value: the bytes a load returns, the value a store writes, the operands of a
matrix instruction. `DataHalf` states, per family of such sites, exactly the fact that the
reference layer's control half of that phase is missing. `Direct.lean` proves from it, by
induction along each thread's trace, that every event of a thread is fired from a followed
state and is not undefined behaviour.

Words: a *followed state* of thread `g` at position `k` is the state `s` of its machine before
its `k`-th event (`Frame.stateAt (code L) X g k = some (some s)`); `s.site` is the event
instruction the machine is at. "The successor is followed" means that the machine has a state
before the thread's next position, `k + 1`.

**The site families** (the machine's sites, `Proof/Thread/Sites.lean`):

| family | sites | owed |
|---|---|---|
| conversion load | `.load (21 + j)`, `j < 10` | the successor is followed |
| conversion store | `.store j`, `j < 10` | the event is not undefined behaviour |
| carry load | `.load (31 + j)`, `j < 128` | the bytes read have a 32-bit value |
| matrix event | `MatrixSite` | the event is not undefined behaviour |
| tile data path | `TileSite` | the successor is followed |
| element read | `ElemReadSite` | the successor is followed |
| element store | `.store (10 + i)`, `i < 8` | the event is not undefined behaviour |
| final store | `.store (18 + j)`, `j < 128` | the event is not undefined behaviour |

At every other site of the kernel, and for the other half at these sites, the reference layer
needs nothing: a load event is a read whatever the data (a load faults on its address only);
after a store event that is not undefined behaviour the successor is a state; after a carry
load whose bytes have a value the successor is a state (the pointer arithmetic that follows is
control).

Each field is stated for one event at one followed state, so it also holds for executions in
which the thread stops in the middle of a family (a prefix of a run): the induction needs the
successor of the event at `k` whenever the thread has an event at `k + 1`.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread

noncomputable section

/-- **The sites of the warp matrix events** of the tile loop of a compute thread: the second
event of an `ldmatrix` (after its row read), an `mma.sync`, a `movmatrix`, the first event of
an `stmatrix` (before its row write). The event fired there is a matrix event or undefined
behaviour. -/
def MatrixSite : Site → Prop
  | .matrixLoadMx _ _ | .warpMma _ | .matrixMove _ | .matrixStore _ => True
  | _ => False

/-- **The sites of the data path of the tile loop** of a compute thread: every event site
between the two polls and the named barrier of a tile. These are the matrix sites, the row
read of an `ldmatrix`, the row write of an `stmatrix`, and the eighteen scalar loads (two gate
logits, sixteen decay factors: the machine's load sites 159 to 176). -/
def TileSite : Site → Prop
  | .matrixLoad _ | .matrixLoadMx _ _ | .warpMma _ | .matrixMove _ | .matrixStore _
  | .matrixStoreWr _ _ => True
  | .load j => 159 ≤ j.val ∧ j.val ≤ 176
  | _ => False

/-- **The four element reads of the store leader's vector load** (instruction 3020, in the
store of a partial last tile): the machine's load site 177 and its three continuation sites,
which carry the values already read. -/
def ElemReadSite : Site → Prop
  | .load j => j.val = 177
  | .loadEl1 _ _ | .loadEl2 _ _ _ | .loadEl3 _ _ _ _ => True
  | _ => False

/-- **The data half of "no undefined-behaviour event"**, per family of sites at which the
outcome of an event depends on a data value, together with the operands of the warp-level
multiply-accumulate. Every field but the last is about one event `e` of a launched thread `g`
at a followed state `s` at a site of the family. -/
structure DataHalf (P : Params) (L : Launch) (mem0 : Mem0) (X : Execution) : Prop where
  /-- **Conversion load** (`ld.b32` of the FP32 state buffer, instructions 400 to 598): the
  successor is followed, that is, the bytes read rebuild to a value that `cvt.rn.bf16.f32`
  narrows without a fault. -/
  convLoad : ∀ g k s e (j : Fin 10), g < L.threads →
    Frame.stateAt (code L) X g k = some (some s) → s.site = .load ⟨21 + j.val, by omega⟩ →
    X.get (g, k) = some e → ∃ s', Frame.stateAt (code L) X g (k + 1) = some (some s')
  /-- **Conversion store** (`st.shared.b16` into `state_acc`): the event is not undefined
  behaviour, that is, the narrowed value converts to 16 bits. -/
  convStore : ∀ g k s e (j : Fin 10), g < L.threads →
    Frame.stateAt (code L) X g k = some (some s) → s.site = .store ⟨j.val, by omega⟩ →
    X.get (g, k) = some e → ∀ pc f, e ≠ ⟨pc, .ub f⟩
  /-- **Carry load** (the 128 `ld.b32` of a compute thread, instructions 765 to 1400): when
  the event is a read, its bytes rebuild to a 32-bit value. (The event is a read whatever the
  data, and the successor then is a state: both are the reference layer's.) -/
  carryLoad : ∀ g k s (j : Fin 128) pc a bs, g < L.threads → g % L.block < 128 →
    Frame.stateAt (code L) X g k = some (some s) → s.site = .load ⟨31 + j.val, by omega⟩ →
    X.get (g, k) = some ⟨pc, .rd a bs⟩ → ∃ v, ldVal .same 32 bs = .ok v
  /-- **Matrix event** of a compute thread: the event is not undefined behaviour, that is,
  the registers the lane contributes hold values of the kinds the instruction takes. -/
  matrixEv : ∀ g k s e, g < L.threads → g % L.block < 128 →
    Frame.stateAt (code L) X g k = some (some s) → MatrixSite s.site →
    X.get (g, k) = some e → ∀ pc f, e ≠ ⟨pc, .ub f⟩
  /-- **Data path of the tile loop** of a compute thread: the successor is followed, that is,
  the bytes a load returns decode, and the floating-point instructions up to the next event
  do not fault. -/
  tileNext : ∀ g k s e, g < L.threads → g % L.block < 128 →
    Frame.stateAt (code L) X g k = some (some s) → TileSite s.site →
    X.get (g, k) = some e → ∃ s', Frame.stateAt (code L) X g (k + 1) = some (some s')
  /-- **Element read** of the store leader's vector load: the successor is followed, that is,
  the four bytes rebuild to a 32-bit word, and after the fourth read the four words unpack
  into pairs of 16-bit halves. -/
  elemRead : ∀ g k s e, g < L.threads →
    Frame.stateAt (code L) X g k = some (some s) → ElemReadSite s.site →
    X.get (g, k) = some e → ∃ s', Frame.stateAt (code L) X g (k + 1) = some (some s')
  /-- **Element store** (`st.global.b16` of an output of a partial last tile, instructions
  3025 to 3032): the event is not undefined behaviour. -/
  elemStore : ∀ g k s e (i : Fin 8), g < L.threads →
    Frame.stateAt (code L) X g k = some (some s) → s.site = .store ⟨10 + i.val, by omega⟩ →
    X.get (g, k) = some e → ∀ pc f, e ≠ ⟨pc, .ub f⟩
  /-- **Final store** (the 128 `st.b32` of a compute thread into the FP32 state buffer,
  instructions 3132 to 3767): the event is not undefined behaviour, that is, the carry
  register holds a value that a 32-bit store can write. -/
  finalStore : ∀ g k s e (j : Fin 128), g < L.threads → g % L.block < 128 →
    Frame.stateAt (code L) X g k = some (some s) → s.site = .store ⟨18 + j.val, by omega⟩ →
    X.get (g, k) = some e → ∀ pc f, e ≠ ⟨pc, .ub f⟩
  /-- **`DirectFacts.mmaOperands`**, verbatim: in every instance of a warp-level
  multiply-accumulate the instruction is the bf16 `m16n8k16` form and the registers the lanes
  contribute hold real matrices. -/
  mmaOperands : ∀ w n pc s parts, laneOf L w = 0 →
    WarpMatrix.WarpInstance X w n pc (.mma s) parts →
    s = WarpMatrix.mma16 ∧ ∃ ra rb rc a b c, WarpMatrix.Operands ra rb rc a b c ∧
      ∀ l < 32, parts l = WarpMatrix.mmaParts ra rb rc l

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
