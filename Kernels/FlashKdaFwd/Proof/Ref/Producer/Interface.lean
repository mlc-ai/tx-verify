-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Inv
public import Kernels.FlashKdaFwd.Proof.Protocol.Layout
public import Lemmas.Flow.Polls
public import Lemmas.Flow.NotTensor

@[expose] public section

/-! # The Producer phase of the reference layer: entry, exit and ledger (statements)

The Producer phase is the stretch of the program from instruction 1403 to 2105: the tile loop
of the *load leader*. Only the threads of the load warp (thread index 128 to 159 in the block)
enter it, and only its lane 0 (thread 128, the load leader) makes events there. Its boundary
with the other phases:

* **entry**: the state at the site `bar_5` (instruction 1402, a `bar.sync 0` that every thread
  executes), *before* the barrier's event (`Entry`, `ledEntry`). The phases before it (startup,
  conversion, carry load) prove it; the registers are the ones live at `bar_5` for a thread of
  the load warp, in the closed forms of the
  startup phase's exit (`Startup.Exit`): `entry_of_startup` derives the entry condition from
  those facts.
* **exit**: the state at the site `bar_7` (instruction 3113, the first `bar.sync 0` of the
  epilogue), before its event (`Exit`, `ledExit`), for every thread of the load warp. The 31
  lanes other than lane 0 go there directly from `bar_5`.

**The ledger** (`Led`) counts the events a thread has made, by class. Five classes are the
startup phase's (`bar.sync 0`, `mbarrier.init`, arrivals, tensor load issues, successful polls,
on any mbarrier). Nine more count per mbarrier of the load pipeline, because the contracts of
the protocol layer (`Proof/Protocol/LoadRing.lean`) are stated per mbarrier: for each input stage
`s < 3`, the successful polls of its "empty" mbarrier `Bar.loadEmpty s`, the arrivals on its
"full" mbarrier `Bar.loadFull s`, and the tensor loads that complete on `Bar.loadFull s`.
`ledOf L c es` is the ledger of the events `es` of a thread of block `c`.

`ledAt a b n` is the ledger of the load leader when it has polled successfully for `a` tiles,
arrived for `b` tiles and issued `n` tile loads (tile `t` uses stage `t % 3`; the 70 loads of a
tile are issued in order, so `n = 70 * tile + position`). Every ledger of the phase is of this
form.

Abbreviations: `T` is the number of tiles of the sequence of the thread's block (`tilesOf`),
`W n` the 64-bit word of the number `n`. A register is named by its id in the generated thread
machine; the comments give its name in the PTX. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (Bar)

noncomputable section

/-- The number of tiles of the sequence that the block of thread `g` works on. -/
abbrev tilesOf (P : Params) (g : Nat) : Nat := tiles (P.length (seqOf P g))

/-! ### The entry -/

/-- **The entry condition of the Producer phase**, for a thread of the load warp: the state is
at `bar_5` (instruction 1402) and holds the thread index (`%r1`), the four role flags that are
live there (`%p85`, `%p86`, `%p87` are false in the load warp; `%p88` says "this lane is not the
elected one", and the elected lane is lane 0), the results of the scan of the offsets array
(`%r8`: the sequence's number of tokens, `%r9`: its number of tiles, `%r1793`: its first tile,
`%rd2`: its first token) and the flag of the election at instruction 312 (`%r180`: 1 in
lane 0). -/
structure Entry (P : Params) (g : Nat) (d : D) : Prop where
  site : d.site = .bar 5
  tid : d.w 307 = W (tid g)
  p85 : d.p 85 = false
  p86 : d.p 86 = false
  p87 : d.p 87 = false
  p88 : d.p 88 = decide (lane g ≠ 0)
  scan : Startup.Scan P g d
  elected : d.w 486 = W (if lane g = 0 then 1 else 0)

/-- The entry condition follows from the facts of the startup phase's exit (`Startup.Exit`)
about the registers that are live at `bar_5`, for a thread of the load warp. -/
theorem entry_of_startup {P : Params} {g : Nat} {d : D} (hw : warp g = 4)
    (hsite : d.site = .bar 5) (htid : d.w 307 = W (tid g)) (hf : Startup.Flags g d.p)
    (hs : Startup.Scan P g d) (he : d.w 486 = W (if lane g = 0 then 1 else 0)) :
    Entry P g d := by
  have h := (warp_eq4_iff g).mp hw
  simp only [Startup.Flags, Startup.flagsOf, Startup.roleFlags, show ¬ tid g < 128 by omega,
    h.2, ↓reduceIte, Prod.mk.injEq] at hf
  exact ⟨hsite, htid, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2, hs, he⟩

/-! ### The exit -/

/-- **The exit condition of the Producer phase**, for a thread of the load warp: the state is
at `bar_7` (instruction 3113) and holds the election flag (`%r180`), the thread index
(`%r1736`, read again at instruction 3111) and the flag "the thread index is above 127"
(`%p77`): the registers live at `bar_7` for a thread of the load warp. -/
structure Exit (P : Params) (g : Nat) (d : D) : Prop where
  site : d.site = .bar 7
  elected : d.w 486 = W (if lane g = 0 then 1 else 0)
  tid : d.w 2042 = W (tid g)
  p77 : d.p 77 = true

/-! ### The ledger -/

/-- Counts of events by class. -/
structure Led where
  /-- `bar.sync 0` events. -/
  bars : Nat
  /-- `mbarrier.init` events. -/
  inits : Nat
  /-- Arrivals, on any mbarrier. -/
  arrs : Nat
  /-- Tensor load issues, on any completion mbarrier. -/
  issues : Nat
  /-- Successful polls, of any mbarrier. -/
  polls : Nat
  /-- Successful polls of the "empty" mbarrier of input stage 0, 1, 2. -/
  e0 : Nat
  e1 : Nat
  e2 : Nat
  /-- Arrivals on the "full" mbarrier of input stage 0, 1, 2. -/
  a0 : Nat
  a1 : Nat
  a2 : Nat
  /-- Tensor loads that complete on the "full" mbarrier of input stage 0, 1, 2. -/
  i0 : Nat
  i1 : Nat
  i2 : Nat
  deriving DecidableEq

instance : Add Led := ⟨fun a b =>
  ⟨a.bars + b.bars, a.inits + b.inits, a.arrs + b.arrs, a.issues + b.issues, a.polls + b.polls,
    a.e0 + b.e0, a.e1 + b.e1, a.e2 + b.e2, a.a0 + b.a0, a.a1 + b.a1, a.a2 + b.a2,
    a.i0 + b.i0, a.i1 + b.i1, a.i2 + b.i2⟩⟩

theorem Led.add_def (a b : Led) : a + b =
    ⟨a.bars + b.bars, a.inits + b.inits, a.arrs + b.arrs, a.issues + b.issues, a.polls + b.polls,
      a.e0 + b.e0, a.e1 + b.e1, a.e2 + b.e2, a.a0 + b.a0, a.a1 + b.a1, a.a2 + b.a2,
      a.i0 + b.i0, a.i1 + b.i1, a.i2 + b.i2⟩ := rfl

/-- The "empty" mbarrier of input stage `s` of block `c`: the load leader polls it. -/
abbrev emptyLoc (L : Launch) (c : Nat) (s : Fin 3) : Loc := (Bar.loadEmpty s).loc L c

/-- The "full" mbarrier of input stage `s` of block `c`: the load leader arrives on it and its
tile loads complete on it. -/
abbrev fullLoc (L : Launch) (c : Nat) (s : Fin 3) : Loc := (Bar.loadFull s).loc L c

/-- The ledger of the events `es` of a thread of block `c`. -/
def ledOf (L : Launch) (c : Nat) (es : List Event) : Led :=
  ⟨es.countP (Execution.isBarId 0), es.countP Startup.isInit, es.countP Startup.isArr,
    es.countP Startup.isIssue, es.countP Startup.isOkPoll,
    okPolls (emptyLoc L c 0) es, okPolls (emptyLoc L c 1) es, okPolls (emptyLoc L c 2) es,
    arrivals (fullLoc L c 0) es, arrivals (fullLoc L c 1) es, arrivals (fullLoc L c 2) es,
    es.countP (issuesTo (fullLoc L c 0)), es.countP (issuesTo (fullLoc L c 1)),
    es.countP (issuesTo (fullLoc L c 2))⟩

/-- The ledger of one event of a thread of block `c`. -/
def ledEv (L : Launch) (c : Nat) (e : Event) : Led :=
  ⟨if Execution.isBarId 0 e then 1 else 0, if Startup.isInit e then 1 else 0,
    if Startup.isArr e then 1 else 0, if Startup.isIssue e then 1 else 0,
    if Startup.isOkPoll e then 1 else 0,
    if okPoll (emptyLoc L c 0) e then 1 else 0, if okPoll (emptyLoc L c 1) e then 1 else 0,
    if okPoll (emptyLoc L c 2) e then 1 else 0,
    if arrivesOn (fullLoc L c 0) e then 1 else 0, if arrivesOn (fullLoc L c 1) e then 1 else 0,
    if arrivesOn (fullLoc L c 2) e then 1 else 0,
    if issuesTo (fullLoc L c 0) e then 1 else 0, if issuesTo (fullLoc L c 1) e then 1 else 0,
    if issuesTo (fullLoc L c 2) e then 1 else 0⟩

/-- **The ledger at the entry**: five `bar.sync 0`; for thread 128 the initialization of the
state mbarrier, the arrival on it and the 16 loads of the initial state; one successful poll
(of the state mbarrier); nothing on the mbarriers of the load pipeline. -/
def ledEntry (g : Nat) : Led :=
  ⟨5, if tid g = 128 then 1 else 0, if tid g = 128 then 1 else 0, if tid g = 128 then 16 else 0,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The loads on the "full" mbarrier of stage `s` among the first `n` tile loads of the load
leader: 70 for each complete tile of the stage, and the loads of the current tile when it is on
the stage. -/
def issuedOn (n s : Nat) : Nat :=
  70 * ((n / 70 + 2 - s) / 3) + if n / 70 % 3 = s then n % 70 else 0

/-- **The ledger of the load leader** when it has polled successfully for `a` tiles, arrived
for `b` tiles and issued `n` tile loads: six `bar.sync 0`, the startup's initialization, arrival,
16 loads and poll, and per stage `s` the tiles `t < a` (`t < b`) with `t % 3 = s`. -/
def ledAt (a b n : Nat) : Led :=
  ⟨6, 1, 1 + b, 16 + n, 1 + a, (a + 2) / 3, (a + 1) / 3, a / 3, (b + 2) / 3, (b + 1) / 3, b / 3,
    issuedOn n 0, issuedOn n 1, issuedOn n 2⟩

/-- **The ledger at the exit**: the load leader has polled for its `T` tiles and three times
more (the tail), arrived for `T` tiles and issued `70 T` loads; another lane of the load warp
has only made its sixth `bar.sync 0`. -/
def ledExit (P : Params) (g : Nat) : Led :=
  if tid g = 128 then ledAt (tilesOf P g + 3) (tilesOf P g) (70 * tilesOf P g)
  else ⟨6, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
