# Threads: state, local steps and events

How one thread runs: its local state, the registers and local instructions, the events it emits for every other instruction, and the events and executions that collect them. Concepts come first, then the rules.

Generated from the Lean comments of `Core/` by `Tools/coredoc.py`. Every entry links to the Lean source it was generated from. [All chapters](README.md).

## Contents

- [Concepts](#concepts)
  - [Thread state and events](#thread-state-and-events)
    - [`EvId`](#c-evid)
    - [`TState`](#c-tstate)
    - [`Kind`](#c-kind)
    - [`Event`](#c-event)
    - [`Tmpl`](#c-tmpl)
    - [`Execution`](#c-execution)
    - [`Execution.get`](#c-execution-get)
    - [`SameCta`](#c-samecta)
    - [`SameWarp`](#c-samewarp)
    - [`SameWarpgroup`](#c-samewarpgroup)
    - [`laneOf`](#c-laneof)
  - [Running a thread](#running-a-thread)
    - [`out`](#c-out)
    - [`Tau`](#c-tau)
    - [`EStep`](#c-estep)
    - [`Run`](#c-run)
    - [`Produces`](#c-produces)
    - [`execLocal`](#c-execlocal)
    - [`execLocalRule`](#c-execlocalrule)
    - [`execLocalA`](#c-execlocala)
    - [`guardHolds`](#c-guardholds)
  - [Registers and numeric values](#registers-and-numeric-values)
    - [`readReg`](#c-readreg)
    - [`setReg`](#c-setreg)
    - [`next`](#c-next)
    - [`sregValue`](#c-sregvalue)
    - [`readBits`](#c-readbits)
    - [`readValue`](#c-readvalue)
    - [`Value.bitPattern`](#c-value-bitpattern)
    - [`readFloat`](#c-readfloat)
    - [`classify`](#c-classify)
    - [`FVal.toValue`](#c-fval-tovalue)
    - [`execFloat`](#c-execfloat)
    - [`FloatInstr.lane`](#c-floatinstr-lane)
    - [`Layout.round`](#c-layout-round)
    - [`execInt`](#c-execint)
    - [`execMove`](#c-execmove)
    - [`execCvt`](#c-execcvt)
  - [Addresses, loads and stores](#addresses-loads-and-stores)
    - [`effAddr`](#c-effaddr)
    - [`rebuild`](#c-rebuild)
    - [`loadTmpl`](#c-loadtmpl)
    - [`storeTmpl`](#c-storetmpl)
    - [`execCvta`](#c-execcvta)
    - [`readSharedAddress`](#c-readsharedaddress)
    - [`execSharedAddress`](#c-execsharedaddress)
    - [`tensorMapAddress`](#c-tensormapaddress)
  - [Register adjustment](#register-adjustment)
    - [`SetMaxNReg.tmpl`](#c-setmaxnreg-tmpl)
    - [`SetMaxNReg.Request`](#c-setmaxnreg-request)
    - [`SetMaxNReg.SameRequest`](#c-setmaxnreg-samerequest)
    - [`SetMaxNReg.Unsafe`](#c-setmaxnreg-unsafe)
- [Rules](#rules)
  - [Thread state and events](#thread-state-and-events)
    - [a thread's local state](#thread-state) (`THREAD-STATE`)
    - [instruction instance identities](#thread-instance-id) (`THREAD-INSTANCE-ID`)
    - [events](#thread-event) (`THREAD-EVENT`)
    - [event templates](#thread-template) (`THREAD-TEMPLATE`)
    - [executions](#mem-execution) (`MEM-EXECUTION`)
    - [reading an execution](#mem-execution-queries) (`MEM-EXECUTION-QUERIES`)
    - [CTAs, warps and lanes](#prog-cta-warp) (`PROG-CTA-WARP`)
      - [warps](#ext-warp) (`EXT-WARP`)
  - [How a thread runs](#how-a-thread-runs)
    - [the traces of one thread](#thread-run) (`THREAD-RUN`)
    - [which rule a local instruction uses](#thread-local) (`THREAD-LOCAL`)
    - [branches and predication](#thread-branch) (`THREAD-BRANCH`)
  - [Registers and numeric values](#registers-and-numeric-values)
    - [bit patterns](#thread-bits) (`THREAD-BITS`)
      - [bits of an unrepresentable payload](#ext-float-bits) (`EXT-FLOAT-BITS`)
    - [registers and operands](#thread-reg) (`THREAD-REG`)
    - [special register values](#thread-sreg) (`THREAD-SREG`)
    - [integer instructions](#thread-int) (`THREAD-INT`)
    - [numeric operand interpretation](#thread-num) (`THREAD-NUM`)
    - [floating instructions](#thread-float) (`THREAD-FLOAT`)
    - [IEEE 754 operations and the instructions defined by their text](#thread-float-ieee) (`THREAD-FLOAT-IEEE`)
      - [the IEEE 754 rules of the instructions with rounding modifiers](#ext-ieee754) (`EXT-IEEE754`)
    - [the tables of the approximate instructions](#thread-float-approx) (`THREAD-FLOAT-APPROX`)
    - [rounding an exact number to a layout](#thread-float-round) (`THREAD-FLOAT-ROUND`)
    - [data movement](#thread-move) (`THREAD-MOVE`)
    - [conversions](#thread-cvt) (`THREAD-CVT`)
      - [values of the ue8m0 format](#ext-ue8m0) (`EXT-UE8M0`)
      - [values of the e2m1, e2m3, e3m2 and ue5m3 formats](#ext-narrow-float) (`EXT-NARROW-FLOAT`)
  - [Addresses and pointers](#addresses-and-pointers)
    - [generic address windows: cvta and isspacep](#thread-cvta) (`THREAD-CVTA`)
      - [generic and global addresses](#ext-cvta) (`EXT-CVTA`)
    - [descriptor addresses from kernel parameters](#thread-tensor-map-address) (`THREAD-TENSOR-MAP-ADDRESS`)
    - [tensormap prefetches](#thread-tensormap-prefetch) (`THREAD-TENSORMAP-PREFETCH`)
    - [arithmetic on symbolic addresses](#thread-pointer-offset) (`THREAD-POINTER-OFFSET`)
    - [shared addresses and peer mapping](#thread-shared-pointer) (`THREAD-SHARED-POINTER`)
  - [Loads and stores](#loads-and-stores)
    - [effective addresses](#thread-addr) (`THREAD-ADDR`)
      - [an address sum wraps at the address width](#ext-addr-wrap) (`EXT-ADDR-WRAP`)
    - [footprints of loads and stores](#thread-access) (`THREAD-ACCESS`)
      - [which address and register an element has](#ext-vector-elem) (`EXT-VECTOR-ELEM`)
    - [the value of read bytes](#thread-bytes) (`THREAD-BYTES`)
    - [atomic read-modify-write instructions](#thread-atomic) (`THREAD-ATOMIC`)
    - [the values of atomic operations](#thread-atomic-op) (`THREAD-ATOMIC-OP`)
    - [cache prefetch and eviction priority](#thread-prefetch) (`THREAD-PREFETCH`)
    - [cache eviction policies](#thread-cache-policy) (`THREAD-CACHE-POLICY`)
    - [sleeping, performance monitor events and grid dependency control](#thread-no-effect) (`THREAD-NO-EFFECT`)
      - [grid dependency control in a launch of one grid](#ext-griddep-single) (`EXT-GRIDDEP-SINGLE`)
    - [thread fences and proxy fences](#thread-fence) (`THREAD-FENCE`)
  - [Register adjustment](#register-adjustment)
    - [register adjustment requests](#thread-setmaxnreg) (`THREAD-SETMAXNREG`)
      - [PTX registers keep their values across setmaxnreg](#ext-setmaxnreg-virtual) (`EXT-SETMAXNREG-VIRTUAL`)
      - [every setmaxnreg request takes effect and returns](#ext-setmaxnreg-effective) (`EXT-SETMAXNREG-EFFECTIVE`)
    - [warp rendezvous of a register adjustment](#dep-setmaxnreg-rendezvous) (`DEP-SETMAXNREG-RENDEZVOUS`)
    - [register adjustment legality](#err-setmaxnreg) (`ERR-SETMAXNREG`)

## Concepts

The definitions a reader needs to follow the rules. Each text is the Lean doc comment, and each entry links to its Lean source.

### Thread state and events

The state of one thread and the events it produces.

<a id="c-evid"></a>
#### `EvId`

*abbrev*

The identity of an instruction instance: the thread's index in the grid and the position of the
instruction's event in that thread's trace.

[Lean source: `Core/Data/AsyncTypes.lean` L23-L25](../../Core/Data/AsyncTypes.lean#L23-L25)

<a id="c-tstate"></a>
#### `TState`

*structure*

The local state of one thread (THREAD-STATE): source position, registers, the progress of the
current vector access, and a pending fault.

- `pc`
- `regs`
- `cf`: The carry flag `CC.CF` of the condition code register; `none` until an instruction writes it.
- `sub`: Elements of the current vector access already performed.
- `acc`: Values returned so far by the elements of the current vector load.
- `fault`: Undefined behaviour found after the last event: the next event is `ub`.

[Lean source: `Core/Data/Types.lean` L51-L64](../../Core/Data/Types.lean#L51-L64)

<a id="c-kind"></a>
#### `Kind`

*inductive*

The kind of an event: the effect of the instruction that performed it, together with the
values it returned. The mbarrier kinds are `mbInit`, `mbInval`, `arrive`, `wait` and
`fenceMbarInit`.

- `setMaxReg`: A register adjustment request (`setmaxnreg`). `inst` is an uninterpreted label; matching uses the per-thread request ordinal, source PC and payload.
- `warpBar`
- `elect`: Completed election; instance labels pair this dynamic collective across lanes.
- `rd`: A generic-proxy read of `a`; its qualifiers are in `a`, with one result per byte.
- `nc`: An `ld.global.nc` read: outside the memory consistency model (§8.1).
- `wr`: A generic-proxy write of `a`, retaining its memory qualifiers.
- `bar`: Arrival at CTA barrier `id`; `none` denotes the omitted thread count. `mode` is `.sync` for `bar.sync` and `.arrive` for `bar.arrive`.
- `shfl`: A completed `shfl.sync`: own operand `a`, lane operands `b`, `c`, the value received and the in-range predicate.
- `vote`: A completed `vote.sync.ballot.b32` with member mask `mask`: own predicate `a` and the ballot received.
- `exit`
- `ub`

[Lean source: `Core/Data/Types.lean` L200-L295](../../Core/Data/Types.lean#L200-L295)

<a id="c-event"></a>
#### `Event`

*structure*

One event of a thread trace: the source position of its instruction and its kind.

- `pc`: Source position of the instruction that performed it.
- `kind`

[Lean source: `Core/Data/Types.lean` L297-L301](../../Core/Data/Types.lean#L297-L301)

<a id="c-tmpl"></a>
#### `Tmpl`

*inductive*

An event of a thread with the value it returns left open, together with the thread's state
after it (THREAD-TEMPLATE).

- `setMaxReg`
- `warpBar`
- `elect`
- `read`
- `readNC`
- `write`
- `bar`
- `shfl`
- `vote`
- `exit`
- `ub`

[Lean source: `Core/Data/Types.lean` L396-L450](../../Core/Data/Types.lean#L396-L450)

<a id="c-execution"></a>
#### `Execution`

*structure*

One candidate execution of a kernel (MEM-EXECUTION): the thread traces, reads-from, the
asynchronous effects, and the histories of the synchronization objects.

- `tr`: The finite event trace of each thread, indexed by the thread's id in the grid.
- `rf`: For read `e` and byte `k` of its footprint: the write it read from, or `none` for the initial write `W0`.

[Lean source: `Core/Data/Types.lean` L326-L365](../../Core/Data/Types.lean#L326-L365)

<a id="c-execution-get"></a>
#### `Execution.get`

*def*

The event at position `e` of the execution: thread `e.1`, trace index `e.2`.

[Lean source: `Core/Data/Events.lean` L66-L67](../../Core/Data/Events.lean#L66-L67)

<a id="c-samecta"></a>
#### `SameCta`

*def*

Threads `g` and `h` of the launch belong to the same CTA.

[Lean source: `Core/Data/Events.lean` L556-L557](../../Core/Data/Events.lean#L556-L557)

<a id="c-samewarp"></a>
#### `SameWarp`

*def*

Warps are 32 consecutive threads of a CTA (WARP reading: CUDA C++ Programming Guide,
SIMT Architecture).

[Lean source: `Core/Data/Events.lean` L559-L561](../../Core/Data/Events.lean#L559-L561)

<a id="c-samewarpgroup"></a>
#### `SameWarpgroup`

*def*

A warpgroup is four contiguous warps whose first warp-rank is a multiple of 4 (§9.7.17.1).

[Lean source: `Core/Data/Events.lean` L563-L564](../../Core/Data/Events.lean#L563-L564)

<a id="c-laneof"></a>
#### `laneOf`

*def*

The lane of thread `g` within its warp.

[Lean source: `Core/Data/Events.lean` L566-L567](../../Core/Data/Events.lean#L566-L567)

### Running a thread

How a thread's instructions become local steps and events.

<a id="c-out"></a>
#### `out`

*def*

The outcome of the instruction at the thread's source position: a local step, or the template
of the event it performs (a fault, a pc outside the code and a failing local rule give an
undefined-behaviour event).

[Lean source: `Core/Thread/Run.lean` L301-L319](../../Core/Thread/Run.lean#L301-L319)

<a id="c-tau"></a>
#### `Tau`

*def*

A local step: the thread moves from `t` to `t'` without performing an event.

[Lean source: `Core/Thread/Run.lean` L382-L383](../../Core/Thread/Run.lean#L382-L383)

<a id="c-estep"></a>
#### `EStep`

*def*

The thread in state `t` performs event `e` and is then in state `o`.

[Lean source: `Core/Thread/Run.lean` L385-L387](../../Core/Thread/Run.lean#L385-L387)

<a id="c-run"></a>
#### `Run`

*inductive*

From `t`, the thread can perform exactly the events `l` and is then in state `o`.

- `nil`
- `step`
- `last`

[Lean source: `Core/Thread/Run.lean` L389-L396](../../Core/Thread/Run.lean#L389-L396)

<a id="c-produces"></a>
#### `Produces`

*def*

Thread `g` can produce the trace `l` from its initial state.

[Lean source: `Core/Thread/Run.lean` L398-L399](../../Core/Thread/Run.lean#L398-L399)

<a id="c-execlocal"></a>
#### `execLocal`

*def*

A thread-local instruction: the new local state only. Memory and other threads are
not inputs. The rule is the one `Op.rule` names; an instruction whose rule is none or names an
event rule has no local rule.

[Lean source: `Core/Thread/Local.lean` L2948-L2963](../../Core/Thread/Local.lean#L2948-L2963)

<a id="c-execlocalrule"></a>
#### `execLocalRule`

*def*

A local rule: the rule of the first kernel assumption that selects the instruction at this
state, otherwise the core's rule.

[Lean source: `Core/Thread/Local.lean` L2971-L2977](../../Core/Thread/Local.lean#L2971-L2977)

<a id="c-execlocala"></a>
#### `execLocalA`

*def*

The local step: a segment an assumption selects at this state, otherwise the local rule.

[Lean source: `Core/Thread/Local.lean` L2985-L2990](../../Core/Thread/Local.lean#L2985-L2990)

<a id="c-guardholds"></a>
#### `guardHolds`

*def*

Whether the guard of an instruction holds: true without a guard, otherwise the predicate,
negated when requested.

[Lean source: `Core/Thread/Local.lean` L2822-L2829](../../Core/Thread/Local.lean#L2822-L2829)

### Registers and numeric values

Reading and writing registers and interpreting their contents.

<a id="c-readreg"></a>
#### `readReg`

*def*

The value of register `r`, or the `uninitialized` fault when it was never written.

[Lean source: `Core/Thread/Local.lean` L147-L151](../../Core/Thread/Local.lean#L147-L151)

<a id="c-setreg"></a>
#### `setReg`

*def*

Write `v` to register `r`.

[Lean source: `Core/Thread/Local.lean` L153-L155](../../Core/Thread/Local.lean#L153-L155)

<a id="c-next"></a>
#### `next`

*def*

Advance the source position by one.

[Lean source: `Core/Thread/Local.lean` L157-L158](../../Core/Thread/Local.lean#L157-L158)

<a id="c-sregvalue"></a>
#### `sregValue`

*def*

The value of a special register for thread `g` of the launch (THREAD-SREG), or `none` for a
register that changes while the thread runs or has no rule.

[Lean source: `Core/Thread/Local.lean` L263-L285](../../Core/Thread/Local.lean#L263-L285)

<a id="c-readbits"></a>
#### `readBits`

*def*

REG: integer read of the low `w` bits of a thread-private register or operand. A register's
bits are its value's `bitPattern` (an integer's bits, `x`, directly).

[Lean source: `Core/Thread/Local.lean` L344-L360](../../Core/Thread/Local.lean#L344-L360)

<a id="c-readvalue"></a>
#### `readValue`

*def*

Value read for data movement: registers unchanged; literals, including `0f` constants,
are their `w`-bit patterns. A `.pred` special register (`%is_explicit_cluster`) is a predicate.

[Lean source: `Core/Thread/Local.lean` L362-L377](../../Core/Thread/Local.lean#L362-L377)

<a id="c-value-bitpattern"></a>
#### `Value.bitPattern`

*def*

The bits of a data value, `8 * v.bytes` wide: an integer's bits, a payload's encoding,
a pair's halves (low half first), a slice's bytes. Opaque values and predicates have none.

[Lean source: `Core/Thread/Local.lean` L98-L110](../../Core/Thread/Local.lean#L98-L110)

<a id="c-readfloat"></a>
#### `readFloat`

*def*

Read operand `o` as a number of format `fmt`.

[Lean source: `Core/Thread/Local.lean` L1274-L1278](../../Core/Thread/Local.lean#L1274-L1278)

<a id="c-classify"></a>
#### `classify`

*def*

The floating datum a value denotes as format `fmt`: an opaque NaN of `fmt` is NaN with
unknown bits, and every other value is read through its bit pattern, which must have the format's
width (THREAD-FLOAT-FORMAT). This is the only reading of floating data from its bits.

[Lean source: `Core/Thread/Local.lean` L1214-L1226](../../Core/Thread/Local.lean#L1214-L1226)

<a id="c-fval-tovalue"></a>
#### `FVal.toValue`

*def*

The register value of a floating result of format `fmt`: the payload of a finite number or of
`+0`, the opaque NaN for a NaN without a known pattern, and otherwise the bits of the datum
(`-0`, an infinity, a NaN with a known pattern).

[Lean source: `Core/Thread/Local.lean` L1308-L1317](../../Core/Thread/Local.lean#L1308-L1317)

<a id="c-execfloat"></a>
#### `execFloat`

*def*

A floating instruction (THREAD-FLOAT): each source is read at its type's width and each lane
of it classified in its format (`classify`); THREAD-FLOAT's lane rule gives each lane's result;
`setp` and `set` combine the comparison with `BoolOp` and `c` (`boolCombine`), `setp` writes `p`
and `q`, `set` its encoded result (`setResult`), and every other operation writes the lanes'
results in the destination format (`FVal.toValue`, a pair low lane first). A `set` with an integer
source type compares as THREAD-INT does.

[Lean source: `Core/Thread/Local.lean` L2867-L2911](../../Core/Thread/Local.lean#L2867-L2911)

<a id="c-floatinstr-lane"></a>
#### `FloatInstr.lane`

*def*

THREAD-FLOAT for one lane. `xs` are the lane's floating sources in operand order, each
classified in its own format (`srcTys`, or `ty` when `srcTys = []`), before any `.ftz` flush;
predicate sources (the `c` of a BoolOp) are not in `xs`. `none` is no rule.

[Lean source: `Core/Thread/Float.lean` L65-L77](../../Core/Thread/Float.lean#L65-L77)

<a id="c-layout-round"></a>
#### `Layout.round`

*def*

The `L` datum of the exact number `x` rounded by `m` with the overflow policy `ov`; `zneg`
is the sign of an exact zero. `none` where the manual leaves the result open.

[Lean source: `Core/Float/Round.lean` L137-L183](../../Core/Float/Round.lean#L137-L183)

<a id="c-execint"></a>
#### `execInt`

*def*

Integer arithmetic, logic, shifts and comparisons. The scalar `add` and `sub` arms also move
symbolic pointers (THREAD-POINTER-OFFSET); every other one-destination form is
`intResult`.

[Lean source: `Core/Thread/Local.lean` L1016-L1152](../../Core/Thread/Local.lean#L1016-L1152)

<a id="c-execmove"></a>
#### `execMove`

*def*

Data movement: parameters, moves, packing, `selp` and `slct`.

[Lean source: `Core/Thread/Local.lean` L1961-L2049](../../Core/Thread/Local.lean#L1961-L2049)

<a id="c-execcvt"></a>
#### `execCvt`

*def*

A conversion (THREAD-CVT). The first case of an integer source is the general one,
`cvtIntBits false dk dw .u sw x` with the destination's own width, written out as `truncBits`.

[Lean source: `Core/Thread/Local.lean` L2685-L2774](../../Core/Thread/Local.lean#L2685-L2774)

### Addresses, loads and stores

Effective addresses and the events of loads and stores.

<a id="c-effaddr"></a>
#### `effAddr`

*def*

Effective address of a global or shared access (THREAD-ADDR).

[Lean source: `Core/Thread/Access.lean` L120-L128](../../Core/Thread/Access.lean#L120-L128)

<a id="c-rebuild"></a>
#### `rebuild`

*def*

The value of read bytes (BYTES).

[Lean source: `Core/Thread/Access.lean` L254-L272](../../Core/Thread/Access.lean#L254-L272)

<a id="c-loadtmpl"></a>
#### `loadTmpl`

*def*

Element `t.sub` of a load into `ds`.

[Lean source: `Core/Thread/Access.lean` L445-L453](../../Core/Thread/Access.lean#L445-L453)

<a id="c-storetmpl"></a>
#### `storeTmpl`

*def*

Element `t.sub` of a store of `srcs`.

[Lean source: `Core/Thread/Access.lean` L474-L485](../../Core/Thread/Access.lean#L474-L485)

<a id="c-execcvta"></a>
#### `execCvta`

*def*

`cvta` between a state space and the generic address space, window by window, and `isspacep`
(THREAD-CVTA).

[Lean source: `Core/Thread/Local.lean` L1556-L1599](../../Core/Thread/Local.lean#L1556-L1599)

<a id="c-readsharedaddress"></a>
#### `readSharedAddress`

*def*

Read a shared address operand of width `w` as a location in a CTA, checking that the thread
may use it.

[Lean source: `Core/Thread/Local.lean` L1381-L1400](../../Core/Thread/Local.lean#L1381-L1400)

<a id="c-execsharedaddress"></a>
#### `execSharedAddress`

*def*

The shared address instructions `mapa` and `getctarank`.

[Lean source: `Core/Thread/Local.lean` L1402-L1415](../../Core/Thread/Local.lean#L1402-L1415)

<a id="c-tensormapaddress"></a>
#### `tensorMapAddress`

*def*

The address of the tensor map named by operand `map`: a numeric address, or the generic base
of a by-value parameter object that holds a full descriptor.

[Lean source: `Core/Thread/Local.lean` L418-L428](../../Core/Thread/Local.lean#L418-L428)

### Register adjustment

The `setmaxnreg` request, its matching and its legality.

<a id="c-setmaxnreg-tmpl"></a>
#### `SetMaxNReg.tmpl`

*def*

The event of a `setmaxnreg` of count `n`: a request event that leaves the registers
unchanged, or `badValue` for an illegal count.

[Lean source: `Core/Thread/SetMaxNReg.lean` L106-L109](../../Core/Thread/SetMaxNReg.lean#L106-L109)

<a id="c-setmaxnreg-request"></a>
#### `SetMaxNReg.Request`

*def*

Event `e` is a `setmaxnreg` request with direction `inc`, count `n` and instance label
`inst`, at source position `pc`.

[Lean source: `Core/Thread/SetMaxNReg.lean` L111-L114](../../Core/Thread/SetMaxNReg.lean#L111-L114)

<a id="c-setmaxnreg-samerequest"></a>
#### `SetMaxNReg.SameRequest`

*def*

`e` and `f` are the same request of one warp: same warp, same ordinal, same source
position, direction and count.

[Lean source: `Core/Thread/SetMaxNReg.lean` L151-L155](../../Core/Thread/SetMaxNReg.lean#L151-L155)

<a id="c-setmaxnreg-unsafe"></a>
#### `SetMaxNReg.Unsafe`

*def*

The execution contains a `setmaxnreg` request that is unsafe (ERR-SETMAXNREG).

[Lean source: `Core/Thread/SetMaxNReg.lean` L204-L214](../../Core/Thread/SetMaxNReg.lean#L204-L214)

## Rules

Each rule is a contract block of the Lean source. Its statement says what the rule means for programs. The source quotes the PTX ISA 9.5 text the rule rests on, and the direction says how the rule relates to that text. Interpretations (EXT) are readings of the PTX text that the model adopts beyond what the text states. The fields that reviewers check against the Lean bodies are collected under Details for reviewers.

### Thread state and events

What a thread's state, its events and an execution contain.

<a id="thread-state"></a>
#### a thread's local state (`THREAD-STATE`)

*Rule* · [Lean comment: `Core/Data/Types.lean` L28-L48](../../Core/Data/Types.lean#L28-L48)

A thread's local state is its position in the source, its registers, the carry flag of its condition code register, the progress of the current vector access, and the undefined behaviour found since its last event, if any. It says nothing about whether memory operations have completed.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`TState`](../../Core/Data/Types.lean#L51-L64) ([concept](#c-tstate))

<details>
<summary>Details for reviewers</summary>

- §8.9.1 (program order is defined on the source)
- §9.7.2: "Instructions add.cc , addc , sub.cc , subc , mad.cc and madc reference an implicitly
    specified condition code register ( CC ) having a single carry flag bit ( CC.CF ) holding
    carry-in/carry-out or borrow-in/borrow-out."

**Effect:** The state holds a source position, the registers (by id, PROG-INSTR-FORMS), the carry flag `CC.CF` (`none` until an instruction writes it, THREAD-INT), and the progress of the current vector access. The position says where the thread is in its source and nothing about whether earlier memory operations have completed or later ones have. `fault` records undefined behaviour found by local steps: the thread's next event is `ub`.

</details>

<a id="thread-instance-id"></a>
#### instruction instance identities (`THREAD-INSTANCE-ID`)

*Rule* · [Lean comment: `Core/Data/AsyncTypes.lean` L11-L21](../../Core/Data/AsyncTypes.lean#L11-L21)

An executed instruction is named by its thread and its position in that thread's trace. The effects of an asynchronous operation have their own `Ref` identities and occupy no trace position.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`EvId`](../../Core/Data/AsyncTypes.lean#L23-L25) ([concept](#c-evid))

<details>
<summary>Details for reviewers</summary>

- §8.9.1 (program order)

</details>

<a id="thread-event"></a>
#### events (`THREAD-EVENT`)

*Rule* · [Lean comment: `Core/Data/Types.lean` L131-L181](../../Core/Data/Types.lean#L131-L181)

An event is one operation of one thread: a generic-proxy read or write of a footprint, an atomic read-modify-write of a footprint, a non-coherent global read, a barrier arrival, a completed shuffle, vote, reduction, match or election, an `activemask` query, a read of special registers whose values change while the thread runs, a register adjustment request, an mbarrier, bulk-copy, tensor or cluster launch control operation, the thread's exit, or undefined behaviour. A read records the raw bytes that it returned, and the thread rebuilds the value from them.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`TensorPrefetch.Spec`](../../Core/Data/Types.lean#L184-L192), [`BarMode`](../../Core/Data/Types.lean#L194-L198), [`Kind`](../../Core/Data/Types.lean#L200-L295) ([concept](#c-kind)), [`Event`](../../Core/Data/Types.lean#L297-L301) ([concept](#c-event))

<details>
<summary>Details for reviewers</summary>

- §8.2 (memory operations)
- §8.4 (operation types: `ld` / `st` without qualifiers are weak)
- §8.6 (generic proxy)
- §9.7.15.5 (atom)
- §9.7.15.6 (red)
- §9.7.15.1 (bar.sync, bar.arrive)
- §9.7.15.3 (barrier.cluster)
- §9.7.15.10 (vote.sync)
- §9.7.15.11 (match.sync)
- §9.7.15.12 (activemask)
- §9.7.15.13 (redux.sync)
- §9.7.15.16 (mbarrier)
- §9.7.10.28.3 (cp.async and its groups)
- §9.7.10.28.4.1 (cp.async.bulk)
- §9.7.10.28.4.3 (cp.async.bulk.prefetch)
- §9.7.15.16.18 (cp.async.mbarrier.arrive)
- §9.7.10.28.5.5 (cp.async.bulk.prefetch.tensor)
- §9.7.16.5.14 to §9.7.16.6.3 (mma, ldmatrix, stmatrix, movmatrix, mma.sp)
- §10.4
- §10.8
- §10.23
- §10.24
- §10.28 (special registers that change)

**Effect:** An event is one operation of one thread: a generic-proxy read or write of a footprint, an atomic read-modify-write of a footprint (`atom`, `red`), which is one event that both reads and writes (THREAD-ATOMIC), an `ld.global.nc` read, a CTA barrier arrival (`bar.sync`, or `bar.arrive`: `BarMode`), a completed warp shuffle, vote, reduction or match, an `activemask` query, a completed warp-level matrix instruction with the bytes the lane contributes and receives (DEP-WARP-MATRIX), a read of the special registers that change while the thread runs, with the value read from each (THREAD-SREG), the thread's exit, undefined behaviour, an mbarrier or copy operation (DEP-ASYNC-ORIGIN), or a `cp.async` group commit, group wait or mbarrier arrive (THREAD-CP-ASYNC), or a thread fence or proxy fence (THREAD-FENCE). A read records the raw byte contents it returned, so any read can be recorded and a race cannot hide; the value is rebuilt by the thread (THREAD-BYTES). A tensor prefetch records the elements it selects (`TensorPrefetch.Spec`): the transfer descriptor, origin and four-row coordinates of a tensor load, without a shared destination or mbarrier. Its memory read is an asynchronous stage keyed by this event (MEM-FOOTPRINT).

</details>

<a id="thread-template"></a>
#### event templates (`THREAD-TEMPLATE`)

*Rule* · [Lean comment: `Core/Data/Types.lean` L372-L393](../../Core/Data/Types.lean#L372-L393)

A template is the event that an instruction performs with its returned values still open: a read is a function of the bytes it returns, a shuffle of the value it receives, and a `try_wait` of whether it succeeded. The thread rules instantiate a template with any returned value, and the execution rules decide which values are possible.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`Tmpl`](../../Core/Data/Types.lean#L396-L450) ([concept](#c-tmpl))

<details>
<summary>Details for reviewers</summary>

- none (a device of the definition)

**Effect:** A template is the event an instruction performs, with what it returns still open: a read is a function of the bytes it returns, an atomic read-modify-write a function of the bytes it reads, which gives the bytes it writes and the thread's next state, a shuffle a function of the value it receives, a `try_wait` a function of whether it succeeded, a read of changing special registers a function of the values read; bulk-copy effects live independently in `Execution.async`. Also open are the address `tcgen05.alloc` stores, the results of `tcgen05.mma` and `tcgen05.ld` (THREAD-TC-EVENT) and the bytes a warp-level matrix instruction receives (DEP-WARP-MATRIX). The thread rules (THREAD-RUN) instantiate a template with any returned values; the execution rules decide which values are possible.

</details>

<a id="mem-execution"></a>
#### executions (`MEM-EXECUTION`)

*Rule* · [Lean comment: `Core/Data/Types.lean` L303-L323](../../Core/Data/Types.lean#L303-L323)

An execution has one finite trace of events per thread, and for every byte of every read the write that it read from, or the initial write. It also records the asynchronous effects, the histories of the synchronization objects and the Fence-SC order of its `fence.sc` events. There is no global memory, global order or global time.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`Execution`](../../Core/Data/Types.lean#L326-L365) ([concept](#c-execution)), [`Execution.initialByte`](../../Core/Data/Types.lean#L367-L370)

<details>
<summary>Details for reviewers</summary>

- §8 (an execution is a set of operations with relations between them)
- §8.2.6 (W0)

**Effect:** An execution has one finite trace of events per thread, and reads-from: for every byte of every read, the write event it read from, or `none` for `W0`. An event is named by its thread and its index in that thread's trace. There is no global memory, no global order and no global time. Finite traces are enough: `terminates` bounds them, and `progress` speaks about executions that cannot grow. `initial` chooses the values of allocated launch bytes not specified in `Mem0`; known bytes override it. These choices are universally quantified with the execution and are initial contents, not a current shared memory state.

</details>

<a id="mem-execution-queries"></a>
#### reading an execution (`MEM-EXECUTION-QUERIES`)

*Rule* · [Lean comment: `Core/Data/Events.lean` L25-L56](../../Core/Data/Events.lean#L25-L56)

The event at a position of an execution is found by thread and trace index. The remaining queries are projections that say which kind of event it is, such as a read, a write, a barrier arrival, an mbarrier operation or a `tcgen05` instruction, and what it names. They add no constraint.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`wbyte`](../../Core/Data/Events.lean#L59-L60), [`Execution.get`](../../Core/Data/Events.lean#L66-L67) ([concept](#c-execution-get)), [`Execution.Reads`](../../Core/Data/Events.lean#L78-L80), [`Execution.NcReads`](../../Core/Data/Events.lean#L82-L84), [`Execution.Writes`](../../Core/Data/Events.lean#L86-L87), [`Execution.Rmw`](../../Core/Data/Events.lean#L89-L92), [`Execution.Access`](../../Core/Data/Events.lean#L94-L98), [`Execution.access_iff_of_not_rmw`](../../Core/Data/Events.lean#L100-L109), [`Execution.IsBarrier`](../../Core/Data/Events.lean#L111-L113), [`Execution.IsBarArrival`](../../Core/Data/Events.lean#L115-L117), [`Execution.isBar`](../../Core/Data/Events.lean#L119-L122), [`Execution.isShfl`](../../Core/Data/Events.lean#L124-L126), [`Execution.MbInit`](../../Core/Data/Events.lean#L128-L129), [`Execution.MbInval`](../../Core/Data/Events.lean#L131-L132), [`Execution.Arrive`](../../Core/Data/Events.lean#L134-L136), [`Execution.Copy`](../../Core/Data/Events.lean#L138-L139), [`Execution.BulkPrefetch`](../../Core/Data/Events.lean#L150-L151), [`Execution.Copy.unique`](../../Core/Data/Events.lean#L141-L148), [`Execution.AsyncArrive`](../../Core/Data/Events.lean#L153-L156), [`Execution.IsProxyFence`](../../Core/Data/Events.lean#L158-L160), [`Execution.ThreadFence`](../../Core/Data/Events.lean#L162-L164), [`Execution.AcquireWait`](../../Core/Data/Events.lean#L166-L169), [`Execution.UsesMbar`](../../Core/Data/Events.lean#L239-L250), [`Execution.UsesMbar.of_init`](../../Core/Data/Events.lean#L252-L255), [`Execution.UsesMbar.of_inval`](../../Core/Data/Events.lean#L257-L261), [`Execution.UsesMbar.of_tensor`](../../Core/Data/Events.lean#L263-L266), [`Execution.UsesMbar.of_clc`](../../Core/Data/Events.lean#L268-L272), [`Execution.UsesMbar.of_old`](../../Core/Data/Events.lean#L274-L288), [`Execution.MmaIssue`](../../Core/Data/Events.lean#L175-L179) ([concept](tcgen05.md#c-execution-mmaissue)), [`Execution.MmaCell`](../../Core/Data/Events.lean#L181-L185) ([concept](tcgen05.md#c-execution-mmacell)), [`Execution.MmaReadCell`](../../Core/Data/Events.lean#L187-L191) ([concept](tcgen05.md#c-execution-mmareadcell)), [`Execution.MmaACell`](../../Core/Data/Events.lean#L193-L195), [`Execution.MmaAccess`](../../Core/Data/Events.lean#L197-L199), [`Execution.Commit`](../../Core/Data/Events.lean#L171-L173) ([concept](tcgen05.md#c-execution-commit)), [`Execution.FenceBefore`](../../Core/Data/Events.lean#L201-L202) ([concept](tcgen05.md#c-execution-fencebefore)), [`Execution.FenceAfter`](../../Core/Data/Events.lean#L204-L205), [`Execution.TLd`](../../Core/Data/Events.lean#L207-L210) ([concept](tcgen05.md#c-execution-tld)), [`Execution.WaitLd`](../../Core/Data/Events.lean#L212-L213), [`Execution.TSt`](../../Core/Data/Events.lean#L215-L218) ([concept](tcgen05.md#c-execution-tst)), [`Execution.CpIssue`](../../Core/Data/Events.lean#L220-L223) ([concept](tcgen05.md#c-execution-cpissue)), [`Execution.ShiftIssue`](../../Core/Data/Events.lean#L225-L228), [`Execution.TcAsync`](../../Core/Data/Events.lean#L230-L234) ([concept](tcgen05.md#c-execution-tcasync)), [`Execution.ClcIssue`](../../Core/Data/Events.lean#L236-L237), [`Execution.TensorIssue`](../../Core/Data/Events.lean#L69-L70), [`Execution.TensorStoreIssue`](../../Core/Data/Events.lean#L72-L73), [`Execution.TensorPrefetchIssue`](../../Core/Data/Events.lean#L75-L76)

<details>
<summary>Details for reviewers</summary>

- none (projections)

**Effect:** These queries say which event is at a position and what it reads or writes. `Access` collects the reads and writes that are memory operations of the consistency model (§8.1), an atomic read-modify-write (`Rmw`) as both; `nc` reads are separate (`NcReads`). `wbyte a bs l` is the byte a write of `bs` to `a` stores at `l`. A linear copy's write is an independent effect keyed by its issuing instruction (MEM-FOOTPRINT); mbarrier events are named by what they do to the object at `m`; `tcgen05` events by their instruction. `UsesMbar` lists every event that names an mbarrier operand, the initialization included.

</details>

<a id="prog-cta-warp"></a>
#### CTAs, warps and lanes (`PROG-CTA-WARP`)

*Rule* · [Lean comment: `Core/Data/Events.lean` L512-L527](../../Core/Data/Events.lean#L512-L527)

Two threads are in the same CTA when their CTA indices agree. A warp is 32 consecutive threads of a CTA, and a warpgroup is four consecutive warps of a CTA whose first warp rank is a multiple of 4.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`SameCta`](../../Core/Data/Events.lean#L556-L557) ([concept](#c-samecta)), [`SameWarp`](../../Core/Data/Events.lean#L559-L561) ([concept](#c-samewarp)), [`SameWarpgroup`](../../Core/Data/Events.lean#L563-L564) ([concept](#c-samewarpgroup)), [`laneOf`](../../Core/Data/Events.lean#L566-L567) ([concept](#c-laneof))

<details>
<summary>Details for reviewers</summary>

- §10.1–§10.7 (thread and CTA ids)
- §2.2.1 (threads within a warp are sequentially numbered; a warp typically has 32 threads)
- §9.7.17.1 (warp-rank is the linear thread index divided by 32)
- §9.7.17.1: "A warpgroup is a set of four contiguous warps such that the warp-rank of the first
    warp is a multiple of 4."
- EXT-WARP

</details>

<a id="ext-warp"></a>
##### warps (`EXT-WARP`)

*Interpretation (EXT)* · [Lean comment: `Core/Data/Events.lean` L529-L553](../../Core/Data/Events.lean#L529-L553)

The model takes a warp to be 32 consecutive threads of a CTA by linear thread index `%tid.x + %tid.y * %ntid.x + %tid.z * %ntid.x * %ntid.y`, the index §9.7.17.1 divides by 32 to obtain the warp rank (PROG-LAUNCH: thread `g` has linear thread index `g % block`). The PTX ISA numbers the threads of a warp sequentially and says a warp typically has 32 threads.

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Evidence:** PTX ISA §2.2.1 ("Threads within a warp are sequentially numbered. The warp size is a machine-dependent constant. Typically, a warp has 32 threads"), §4.5.1 (WARP_SZ is 32 for all target architectures to date), §9.7.17.1 ("warp-rank of a warp is defined as: (%tid.x + %tid.y * %ntid.x + %tid.z * %ntid.x * %ntid.y) / 32"). The static partition into consecutive groups is a reading of these sentences; the CUDA C++ Programming Guide (SIMT architecture) agrees.

**Effect:** If it does not hold, the lanes the model groups into one warp collective (`shfl.sync`, `bar.warp.sync`, `elect.sync`, `tcgen05` warp instructions, `setmaxnreg`), the source lanes of shuffles, the uniformity checks, the warp counts of barriers and the values of `%laneid` and the lane masks (THREAD-SREG) refer to the wrong threads, and the values and synchronization the model derives from them are not the hardware's. Disclosed by every kernel whose statement names `Op.warp`, `Op.setMaxReg`, `Op.barSync`, `Op.barSyncN`, `Op.barArrive`, `Op.bra (uni := true)`, `Op.tcAlloc`, `Op.tcDealloc`, `Op.tcRelinquish`, `Op.tcLd`, `Op.tcSt`, `Op.tcWaitLd`, `Op.tcWaitSt`, `SRegName.laneid`, `SRegName.lanemaskEq`, `SRegName.lanemaskLe`, `SRegName.lanemaskLt`, `SRegName.lanemaskGe` or `SRegName.lanemaskGt`: BlockSum, FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, TcGemm.

</details>

### How a thread runs

How a thread executes its instructions and emits events.

<a id="thread-run"></a>
#### the traces of one thread (`THREAD-RUN`)

*Rule* · [Lean comment: `Core/Thread/Run.lean` L35-L88](../../Core/Thread/Run.lean#L35-L88)

A thread starts at the first instruction with no registers set and executes the instruction at its source position. A false guard skips the instruction and a local instruction updates the thread's registers. Any other instruction performs an event whose returned values stay open. A pending fault, a source position outside the code or a failing local rule performs an event of undefined behaviour, and so does `trap`, which no assumption replaces, while `ret` and `exit` end the thread. The thread can perform exactly the finite event sequences that this construction yields, with no global scheduling order.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`skip`](../../Core/Thread/Run.lean#L91-L92), [`widenMbarScope`](../../Core/Thread/Run.lean#L94-L103), [`Tmpl.thenWaitLd`](../../Core/Thread/Run.lean#L105-L108), [`tcLdTmpl`](../../Core/Thread/Run.lean#L110-L116), [`tcStTmpl`](../../Core/Thread/Run.lean#L118-L126), [`warpTmpl`](../../Core/Thread/Run.lean#L128-L146), [`localSregTmpl`](../../Core/Thread/Run.lean#L148-L153), [`eventTmpl`](../../Core/Thread/Run.lean#L155-L187), [`RuleId.tmpl`](../../Core/Thread/Run.lean#L189-L217), [`eventTmpl_rule`](../../Core/Thread/Run.lean#L223-L266), [`eventTmpl_tcLd_noWait`](../../Core/Thread/Run.lean#L268-L273), [`eventTmpl_tcSt_noWait`](../../Core/Thread/Run.lean#L275-L280), [`eventTmpl_tcSt_wait`](../../Core/Thread/Run.lean#L282-L287), [`eventTmpl_tcSt_afterWait`](../../Core/Thread/Run.lean#L289-L294), [`Out`](../../Core/Thread/Run.lean#L296-L299), [`out`](../../Core/Thread/Run.lean#L301-L319) ([concept](#c-out)), [`Fires`](../../Core/Thread/Run.lean#L321-L377), [`Tau`](../../Core/Thread/Run.lean#L382-L383) ([concept](#c-tau)), [`EStep`](../../Core/Thread/Run.lean#L385-L387) ([concept](#c-estep)), [`Run`](../../Core/Thread/Run.lean#L389-L396) ([concept](#c-run)), [`Produces`](../../Core/Thread/Run.lean#L398-L399) ([concept](#c-produces))

<details>
<summary>Details for reviewers</summary>

- §8.9.1 (program order)
- §9.3 (predicated execution)
- §9.7.14.6 (ret): "A return instruction executed in a top-level entry routine will terminate thread
    execution."
- §9.7.14.7 (exit): "Ends execution of a thread."
- §9.7.21.4 (trap): "Abort execution and generate an interrupt to the host CPU."

**Applies:** Local instruction and event traces

**Premises:** Instruction guards, local rules and event templates apply from the initial thread state.

**Effect:** Thread trace constraint in Consistent.thr; no global scheduling order. `ret` and `exit` end the thread (`.exit`); the decoder accepts only `.entry` kernels and no `call`, so every `ret` is in the top-level entry routine. `trap` is a `ub` event with its own reason `trap`: it aborts the kernel, so no execution that reaches it is accepted (stricter), and no kernel assumption can replace it because assumptions replace only `noRule` of a local instruction (THREAD-LOCAL). An `Op.unmodeled` event instruction and an event instruction whose family rule is none are a `ub` event with `noRule` (`eventTmpl`, `memTmpl`, `warpTmpl`). A read of special registers that change while the thread runs (`Tmpl.sreg`, THREAD-SREG) is instantiated with any value below each register's bound; the instruction's local rule then runs with these values, and its fault becomes the thread's pending fault. An atomic read-modify-write (`Tmpl.rmw`) is instantiated with any bytes read: its event records them and the bytes written, and when the operation has no result for them the event writes nothing and the thread's next event is `ub` with the operation's fault (THREAD-ATOMIC). `out t` is the outcome of the instruction at `t.pc`: a local step (`tau`), or the event it performs, as a template. A false guard skips the instruction; a pending fault, a `pc` outside the code, or a failing local rule is a `ub` event. `Run t l o` says that from `t` the thread can perform exactly the events `l`, with any returned values recorded in them, and is then in state `o` (`none`: it exited or performed `ub`). `Run` is inductive with no fuel, so a thread that loops locally forever performs no further event. A `pc` outside the code is a `ub` event although the ISA states no behaviour for it (stricter), and `widenMbarScope` is the identity unless a kernel assumption selects ASM-MBAR-SCOPE for the instruction's site (trust). A `tcgen05.ld` at a site a kernel assumption selects with `tcLdWait` (ASM-INTERFACE) is followed, at the same `pc`, by the event of a `tcgen05.wait::ld` (`tcLdTmpl`), as if that instruction came next (trust); at every other site `tcLdTmpl` is THREAD-TC's rule (`eventTmpl_tcLd_noWait`). A `tcgen05.st` selected by `tcStWaitLd` (ASM-INTERFACE) issues an implicit load wait at sub-step zero, then its original store at the same pc with sub-step reset on completion. A kernel assumption may also take a straight-line segment as one local step (THREAD-LOCAL).

</details>

<a id="thread-local"></a>
#### which rule a local instruction uses (`THREAD-LOCAL`)

*Rule* · [Lean comment: `Core/Thread/Local.lean` L2913-L2945](../../Core/Thread/Local.lean#L2913-L2945)

A local instruction is executed by the rule that `Op.rule` names (PROG-INSTR-RULE): integer and floating operations, moves, conversions, address windows, shared addresses, cache prefetches, cache policies, `nanosleep` and `pmevent`, the tensormap prefetch or branches, and every other instruction has none. A kernel assumption that selects an instruction supplies its rule in place of the core's, and may replace a stretch of straight-line code by one local step.

Source:

- 

Direction: `equal` (the entry claims to follow its cited text)

Lean definitions: [`execLocal`](../../Core/Thread/Local.lean#L2948-L2963) ([concept](#c-execlocal)), [`execLocal_cvta`](../../Core/Thread/Local.lean#L2965-L2969), [`execLocalRule`](../../Core/Thread/Local.lean#L2971-L2977) ([concept](#c-execlocalrule)), [`execLocalRule_of_none`](../../Core/Thread/Local.lean#L2979-L2983), [`execLocalA`](../../Core/Thread/Local.lean#L2985-L2990) ([concept](#c-execlocala)), [`execLocalA_noSegment`](../../Core/Thread/Local.lean#L2992-L2998)

<details>
<summary>Details for reviewers</summary>

- none (dispatch)

**Applies:** Local instruction dispatch, including optional assumptions

**Premises:** The instruction is local; any selected assumption supplies its local rule or segment.

**Effect:** Local rule assembly. When several assumption rules apply, the first one is used. A segment that an assumption selects at the thread's state replaces both the built-in rule and the assumption rules. `execLocal` sends each local instruction to the rule `Op.rule` names, and an instruction whose rule is none (a decode-only form, `Op.unmodeled`, `brx.idx.uni`) has `noRule`. In `execLocalRule` the kernel assumptions are consulted first: the first whose `localRule` selects the instruction at this state gives the outcome, and with none selecting it the outcome is the core's (`execLocalRule_of_none`). The assumptions that set `localRule` (ASM-IDEAL, ASM-APPROX) select only the floating forms they name and decline the operands they do not read, so every other instruction keeps the core's rule. `execLocalA` first asks the assumptions for a segment (`segmentRule`, ASM-INTERFACE): the first that selects one at this state gives the outcome of the whole straight-line code from the thread's `pc` as one local step, which may continue at any `pc`. With no segment selected the rule is `execLocalRule` (`execLocalA_noSegment`); without a kernel assumption that selects segments nothing changes.

</details>

<a id="thread-branch"></a>
#### branches and predication (`THREAD-BRANCH`)

*Rule* · [Lean comment: `Core/Thread/Local.lean` L2776-L2808](../../Core/Thread/Local.lean#L2776-L2808)

A branch sets the source position to its target. `brx.idx` takes the target at the position of its index in its `.branchtargets` list, and an index outside the list is undefined. A guarded instruction runs when its guard predicate, or its negation, holds and is skipped otherwise, and a guard that is not a predicate is undefined.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`execBranch`](../../Core/Thread/Local.lean#L2811-L2820), [`guardHolds`](../../Core/Thread/Local.lean#L2822-L2829) ([concept](#c-guardholds))

<details>
<summary>Details for reviewers</summary>

- §9.7.14.3 (bra): "if (p) { pc = tgt; }"
- §9.7.14.4 (brx.idx): "The index operand is a .u32 register."
- §9.7.14.4 (brx.idx): "It is accessed as a zero-based sequence using index ."
- §9.7.14.4 (brx.idx): "Behavior is undefined if the value of index is greater than or equal to the
    length of tlist ."
- §9.7.14.4 (brx.idx): "brx.idx.uni guarantees that the branch is non-divergent, i.e. all active
    threads in a warp that are currently executing this instruction have identical values for the
    guard predicate and the index argument."
- §9.3 (predicated execution)

**Applies:** Branches, predicates and instruction guards

**Premises:** A branch has a target; the index of `brx.idx` is below the length of its list; a present guard register contains a predicate.

**Effect:** Local control flow; an index outside the list is the `badValue` fault. A branch sets `pc` to its target. A guarded instruction runs when its predicate (or its negation) holds and is skipped otherwise; a guard that is not a predicate is undefined. The `.uni` qualifier does not change what one thread does; disagreement between the lanes of a warp is ERR-NONUNIFORM-GUARD. `brx.idx` reads its index as a 32-bit unsigned integer, and the decoder resolves the `.branchtargets` list to source positions (PROG-DECODE). `brx.idx.uni` has the rule of `brx.idx`; its guarantee covers the guard and the index, and ERR-NONUNIFORM-GUARD compares both between the lanes of a warp.

</details>

### Registers and numeric values

Bit patterns, registers, integer and floating operands, and data movement.

<a id="thread-bits"></a>
#### bit patterns (`THREAD-BITS`)

*Rule* · [Lean comment: `Core/Thread/Local.lean` L23-L62](../../Core/Thread/Local.lean#L23-L62)

Every data value has a bit pattern: an integer's bits, a floating payload's encoding in its format, the halves of a packed pair concatenated with the low half first, or the bytes of a slice. Pointers, predicates and cancellation responses have none. A floating payload is kept as the number it denotes, and each finite pattern of a floating format decodes to an exact value, while NaN and infinities have none.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`truncBits`](../../Core/Thread/Local.lean#L91-L91), [`toSigned`](../../Core/Thread/Local.lean#L93-L96), [`Value.bitPattern`](../../Core/Thread/Local.lean#L98-L110) ([concept](#c-value-bitpattern))

<details>
<summary>Details for reviewers</summary>

- §5.2.1: "The bit-size type is compatible with any fundamental type having the same size. In
    principle, all variables (aside from predicates) could be declared using only bit-size types"
- §5.2.3: "the .f16 type indicates 5 bits reserved for exponent and 10 bits reserved for mantissa"
- §5.2.3: "bf16 data format: This data format is a 16-bit floating point format with 8 bits for
    exponent and 7 bits for mantissa. A register variable containing bf16 data must be declared with
    .b16 type."
- §5.2.3: "The e4m3 encoding does not support infinity and NaN values are limited to 0x7f and 0xff"
- §5.2.3: "e5m2 data format: This data format is an 8-bit floating point format with 5 bits for
    exponent and 2 bits for mantissa"
- §4.5.2: "To specify IEEE 754 double-precision floating point values, the constant begins with 0d
    or 0D followed by 16 hex digits."
- §9.7.10.4: "pack two 16-bit elements into .b32 d = a.x | (a.y << 16)"
- §9.7.3: "Instructions that support rounding modifiers are IEEE-754 compliant."
- EXT-FLOAT-BITS

**Applies:** The bits of every data value: integer patterns, floating payloads, packed pairs and byte slices

**Premises:** A width and bit pattern, a format and bit pattern, or a value, as specified by the helper.

**Effect:** Local evaluation. The entry also defines truncation to a width and the signed interpretation of a bit pattern. A register holds a bit pattern; a floating payload is kept as the number it denotes so that arithmetic profiles can compute with it, and `Value.bitPattern` gives its bits. For a number representable in its format this is its IEEE encoding, exactly as PTX stores it (zero is `+0`). `0f` constants are kept as their 32-bit pattern (THREAD-REG), so `-0`, NaN and infinity encodings are never lost. The format layouts and their decoders are THREAD-FLOAT-FORMAT, and the bits of a payload, `FloatFmt.encode`, are the rounding of THREAD-FLOAT-ROUND.

</details>

<a id="ext-float-bits"></a>
##### bits of an unrepresentable payload (`EXT-FLOAT-BITS`)

*Interpretation (EXT)* · [Lean comment: `Core/Thread/Local.lean` L64-L88](../../Core/Thread/Local.lean#L64-L88)

A floating payload whose number is not representable in its format is read as bits by rounding the number to nearest, ties to even, as `cvt.rn` to that format would. The formats `f64`, `f32`, `f16` and `bf16` overflow to infinity, `e4m3` and `e5m2` saturate to the largest finite value, and zero is `+0`. `FloatFmt.encode` is this rounding: `Layout.round` of THREAD-FLOAT-ROUND with `.rn`, the overflow policy `FloatFmt.overflow` and a positive zero.

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Evidence:** PTX ISA §9.7.10.24 (cvt: ".rn rounding to nearest, with ties to even").

**Effect:** The bits stored for such a payload are fixed by this rounding; if the program's code rounds differently, the stored bits differ from the ones proven. Disclosed by every kernel whose statement names `Assumption.idealReal` or `Value.float`: BlockSum, FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, RowSum.

</details>

<a id="thread-reg"></a>
#### registers and operands (`THREAD-REG`)

*Rule* · [Lean comment: `Core/Thread/Local.lean` L112-L144](../../Core/Thread/Local.lean#L112-L144)

Registers are private to a thread, and an instruction that completes advances the source position by one. Reading a register that was never written is undefined, where PTX gives an unspecified value. An integer operand is the low bits of a register's bit pattern, an immediate, a special register (THREAD-SREG), the address of a shared symbol or a `0f` constant read as its 32-bit pattern. A write changes only the selected register of the thread.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`readReg`](../../Core/Thread/Local.lean#L147-L151) ([concept](#c-readreg)), [`setReg`](../../Core/Thread/Local.lean#L153-L155) ([concept](#c-setreg)), [`next`](../../Core/Thread/Local.lean#L157-L158) ([concept](#c-next)), [`readBits`](../../Core/Thread/Local.lean#L344-L360) ([concept](#c-readbits)), [`readValue`](../../Core/Thread/Local.lean#L362-L377) ([concept](#c-readvalue)), [`readValue_sreg`](../../Core/Thread/Local.lean#L379-L384)

<details>
<summary>Details for reviewers</summary>

- §5.1.1 (register state space)
- §5.1.2 (special registers)
- §4.5.2: "To specify IEEE 754 single-precision floating point values, the constant begins with 0f
    or 0F followed by 8 hex digits."
- §9.7.9.1: "Compute the bit-wise and operation for the bits in a and b"
- §9.7.9.1: "The size of the operands must match, but not necessarily the type"
- §9.7.9.1, example: "and.b32 sign,fpvalue,0x80000000;"

**Applies:** Thread-local operands and registers

**Premises:** The requested register exists and its value has a bit pattern.

**Effect:** Local evaluation and fault production. An invalid register operand is a fault. Registers are thread private. Reading a register that was never written is undefined (`uninitialized`), where PTX would give an unspecified value (Direction: stricter). An integer operand is the low `w` bits of a register's bit pattern (THREAD-BITS), whatever the value's type: an integer, a floating payload or a packed pair. It can also be an immediate, a special register, a shared symbol address (THREAD-ADDR) or a `0f` constant, read as its exact 32-bit pattern. Data movement reads a `0f` constant as that pattern (`.bits 32`); floating instructions decode it (THREAD-NUM). Symbolic pointers have no integer reading (THREAD-SHARED-POINTER). An instruction that completes advances `pc` by one (`next`).

</details>

<a id="thread-sreg"></a>
#### special register values (`THREAD-SREG`)

*Rule* · [Lean comment: `Core/Thread/Local.lean` L160-L260](../../Core/Thread/Local.lean#L160-L260)

`%tid`, `%ntid`, `%ctaid`, `%nctaid`, the cluster registers and `%is_explicit_cluster` have the values of the thread's position in the launch and of the launch's shape. `%laneid` and the lane masks follow from the thread's lane (EXT-WARP). A register that the driver or the machine fixes before launch has an unconstrained value that stays the same for the thread. A read of a register whose value changes while the thread runs is an event whose value stays open, within the register's width and the range the manual states. The performance counters have no rule.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`sregValue`](../../Core/Thread/Local.lean#L263-L285) ([concept](#c-sregvalue)), [`sregValue_isSome`](../../Core/Thread/Local.lean#L287-L292), [`sregValue_initial`](../../Core/Thread/Local.lean#L294-L298), [`sregValue_oneDim`](../../Core/Thread/Local.lean#L300-L333), [`SReg.readBound`](../../Core/Thread/Local.lean#L335-L342), [`substVarying`](../../Core/Thread/Local.lean#L3001-L3007), [`Op.withSregValues`](../../Core/Thread/Local.lean#L3009-L3016), [`sregTmpl`](../../Core/Thread/Local.lean#L3018-L3025)

<details>
<summary>Details for reviewers</summary>

- §10.1: "%tid component values range from 0 through %ntid-1 in each CTA dimension."
- §10.1: "%tid.y == %tid.z == 0 in 1D CTAs."
- §10.2: "%ntid.y == %ntid.z == 1 in 1D CTAs."
- §10.3: "A predefined, read-only special register that returns the thread’s lane within the warp."
- §10.4: "Note that %warpid returns the location of a thread at the moment when read, but its value
    may change during execution"
- §10.5: "returns the maximum number of warp identifiers"
- §10.6
- §10.7
- §10.8: "%smid returns the location of a thread at the moment when read, but its value may change
    during execution"
- §10.8: "The SM identifier ranges from 0 to %nsmid-1 ."
- §10.9: "returns the maximum number of SM identifiers"
- §10.10: "initialized with the per-grid temporal grid identifier"
- §10.11: "initialized with the predicate value of whether the cluster launch is explicitly
    specified by user"
- §10.12–§10.17: "It is guaranteed that: 0 <= %cluster_ctarank < %cluster_nctarank"
- §10.18: "initialized with a 32-bit mask with a bit set in the position equal to the thread’s lane
    number in the warp"
- §10.19–§10.22
- §10.23: "Special register %clock and %clock_hi are unsigned 32-bit read-only cycle counters that
    wrap silently."
- §10.24: "Special register %clock64 is an unsigned 64-bit read-only cycle counter that wraps
    silently."
- §10.25: "Their behavior is currently undefined."
- §10.26
- §10.27: "These registers are initialized by the driver prior to kernel launch and can contain
    cta-wide or grid-wide values."
- §10.28: "When JIT-compiled to other targets, the value of these registers is unspecified."
- §10.29–§10.33
- §10.34 and §10.35: "Usage of this special register is valid only inside entry functions that also
    specify directive .minperctamemory ."
- §10.36: "For the lifetime of a cluster, all threads within that cluster always read the same
    value."
- §10.37
- EXT-WARP
- EXT-CLUSTER-RANK
- EXT-PREFERRED-CLUSTER

**Applies:** Every special register operand that the decoder accepts (PROG-ISA-SREG)

**Premises:** The register has a kind (`SReg.kind`). A register that changes while the thread runs is a source of an integer, move or conversion instruction.

**Effect:** Local evaluation for the fixed registers; an event with an open value for the registers that change; `noRule` for the others. `SReg.kind` (PROG-ISA-SREG) names how each register gets its value. `sregValue` gives the value of every register whose kind is not `varying` (`sregValue_isSome`). - Launch registers. Thread `g` is thread `g % block` of CTA `g / block` (PROG-LAUNCH). `%tid` is `Launch.tidOf`, the coordinates of the linear thread index in the CTA shape; `%ntid` and `%nctaid` are the launch's shapes; `%ctaid`, `%clusterid`, `%nclusterid`, `%cluster_nctaid` and `%cluster_ctaid` are those of the CTA's own cluster (PROG-CLUSTER, EXT-CLUSTER-RANK), which has the regular or the preferred shape (EXT-PREFERRED-CLUSTER); `%cluster_ctarank` is the CTA's rank and `%cluster_nctarank` the size of its cluster. `%is_explicit_cluster` is `Launch.explicitCluster`, and it is read as a `.pred` source (PROG-OPERAND). In a one-dimensional launch (`Launch.OneDim`) every launch register has the value of the one-dimensional model (`sregValue_oneDim`): the `.x` components and the ranks of EXT-CLUSTER-RANK, `.y` and `.z` components 0 and extents 1. - Lane registers. `%laneid` is the lane `laneOf` of the thread in its warp (EXT-WARP), and `%lanemask_eq`, `%lanemask_le`, `%lanemask_lt`, `%lanemask_ge` and `%lanemask_gt` are the 32-bit masks of the lane positions equal to, at most, below, at least and above it. - Initial registers. `%nwarpid`, `%nsmid`, `%gridid`, `%envreg<32>`, the reserved shared memory registers, `%total_smem_size`, `%aggr_smem_size`, `%dynamic_smem_size`, `%current_graph_exec`, `%locality_domain_id`, `%locality_domain_supplemental_sm`, `%perctamemoryoffset` and `%perctamemorysize` are set before the thread starts and do not change. Their value is `Launch.sregInit` of the thread and the register (`sregValue_initial`), which no premise of the model constrains, so a proof that quantifies over the launch holds for every value the machine may give. The two `%perctamemory` registers decode only in a kernel with a `.minperctamemory` directive (PROG-DECODE); the bounds §10.35 gives for `%perctamemorysize` are not used. - Registers that change. `%warpid`, `%smid`, `%clock`, `%clock_hi`, `%clock64` and the `%globaltimer` registers change while the thread runs, so two reads may differ. An integer, move or conversion instruction that reads one of them performs one event (`Tmpl.sreg`, `sregTmpl`) that records every such register it reads and a value for each. The value is any number below `SReg.readBound`: `2 ^ width`, and for `%smid` also the thread's `%nsmid`, since "The SM identifier ranges from 0 to %nsmid-1". A launch whose `%nsmid` is 0, which no hardware launch has, bounds a `%smid` read by its width only, so the read always has a value. The manual states no other relation: the sentence that `%clock64` is identical to `%clock` and `%clock_hi` in its halves relates registers at one moment, and two reads are two moments, so it constrains no pair of reads; a cycle counter wraps, so no order between two reads is stated. The instruction then executes with each such operand replaced by the value read (`Op.withSregValues`), and a fault of that execution is a pending fault of the thread. No proof can depend on a value read, because every value is possible. A changing register read by an instruction of another family has no rule. - Registers without a rule. The performance counters `%pm0`–`%pm7` and `%pm0_64`–`%pm7_64` have undefined behaviour. Reading one is `noRule`, which a kernel assumption may replace with a rule of its own (THREAD-LOCAL).

</details>

<a id="thread-int"></a>
#### integer instructions (`THREAD-INT`)

*Rule* · [Lean comment: `Core/Thread/Local.lean` L541-L693](../../Core/Thread/Local.lean#L541-L693)

An integer instruction computes exactly the result of its Semantics section on the low bits of its operands, read as two's complement for the signed types, and the result wraps at the destination width unless `.sat` clamps it. A result the manual leaves unspecified (division or remainder by zero, a quotient or remainder whose rounding the manual leaves open, a `mul24` operand that is not a 24-bit value) has no rule, and `fns` with a base above 31 is undefined. The extended-precision instructions add the carry flag `CC.CF` where their Semantics sections read it and write the carry-out or borrow-out to it under `.cc`; reading the flag before an instruction has written it has no rule.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`execInt`](../../Core/Thread/Local.lean#L1016-L1152) ([concept](#c-execint)), [`compare`](../../Core/Thread/Local.lean#L696-L703), [`readPred`](../../Core/Thread/Local.lean#L705-L720), [`readPred_reg`](../../Core/Thread/Local.lean#L722-L727), [`setDst`](../../Core/Thread/Local.lean#L729-L732), [`BoolOp.eval`](../../Core/Thread/Local.lean#L734-L738), [`boolCombine`](../../Core/Thread/Local.lean#L740-L747), [`intOf`](../../Core/Thread/Local.lean#L749-L752), [`intBits`](../../Core/Thread/Local.lean#L754-L755), [`intSat`](../../Core/Thread/Local.lean#L757-L761), [`intLane`](../../Core/Thread/Local.lean#L763-L764), [`intOfLanes`](../../Core/Thread/Local.lean#L766-L768), [`bitsFrom`](../../Core/Thread/Local.lean#L770-L772), [`highBit`](../../Core/Thread/Local.lean#L774-L775), [`intDiv`](../../Core/Thread/Local.lean#L777-L785), [`intRem`](../../Core/Thread/Local.lean#L787-L794), [`int24`](../../Core/Thread/Local.lean#L796-L801), [`bfindBits`](../../Core/Thread/Local.lean#L803-L809), [`fnsBits`](../../Core/Thread/Local.lean#L811-L818), [`bfeBits`](../../Core/Thread/Local.lean#L820-L824), [`bfiBits`](../../Core/Thread/Local.lean#L826-L828), [`szextBits`](../../Core/Thread/Local.lean#L830-L838), [`bmskBits`](../../Core/Thread/Local.lean#L840-L851), [`lop3Bits`](../../Core/Thread/Local.lean#L853-L857), [`shfBits`](../../Core/Thread/Local.lean#L859-L864), [`prmtTable`](../../Core/Thread/Local.lean#L866-L880), [`prmtBits`](../../Core/Thread/Local.lean#L882-L893), [`clmulBits`](../../Core/Thread/Local.lean#L895-L898), [`dotBits`](../../Core/Thread/Local.lean#L900-L905), [`carryIn`](../../Core/Thread/Local.lean#L907-L913), [`setCarry`](../../Core/Thread/Local.lean#L915-L916), [`intResult`](../../Core/Thread/Local.lean#L918-L1014)

<details>
<summary>Details for reviewers</summary>

- §9.7.1.1 (add): "Saturation modifier: .sat limits result to MININT..MAXINT (no overflow) for the
    size and signedness of the operation."
- §9.7.1.1 (add): "Half-word operands are then added in parallel to produce .u16x2 , .s16x2 result
    in destination."
- §9.7.1.2 (sub): "d = a - b;"
- §9.7.1.3 (mul): "d = t<2n-1..n>; // for .hi variant"
- §9.7.1.3 (mul): "If .wide is specified, then d is twice as wide as a and b to receive the full
    result of the multiplication."
- §9.7.1.4 (mad): "d = t<2n-1..n> + c; // for .hi variant"
- §9.7.1.4 (mad): "If .wide is specified, then d and c are twice as wide as a and b to receive the
    result of the multiplication."
- §9.7.1.4 (mad): "Saturation modifier: .sat limits result to MININT..MAXINT (no overflow) for the
    size of the operation. Applies only to .s32 type in .hi mode."
- §9.7.1.6 (mul24): "Compute the product of two 24-bit integer values held in 32-bit source
    registers"
- §9.7.1.6 (mul24): "d = t<47..16>; // for .hi variant"
- §9.7.1.7 (mad24): "d = t<47..16> + c; // for .hi variant"
- §9.7.1.7 (mad24): "Saturation modifier: .sat limits result of 32-bit signed addition to
    MININT..MAXINT (no overflow)."
- §9.7.1.8 (sad): "d = c + ((a<b) ? b-a : a-b);"
- §9.7.1.9 (div): "Division by zero yields an unspecified, machine-specific value."
- §9.7.1.10 (rem): "The behavior for negative numbers is machine-dependent and depends on whether
    divide rounds toward zero or negative infinity."
- §9.7.1.11 (abs): "d = |a|;"
- §9.7.1.12 (neg): "d = -a;"
- §9.7.1.13 (min): "d = (a < b) ? a : b; // Integer (signed and unsigned)"
- §9.7.1.13 (min): "Saturation modifier: min.relu.{s8x4, s16x2, s32} clamps the result to 0 if
    negative."
- §9.7.1.14 (max): "d = (a > b) ? a : b; // Integer (signed and unsigned)"
- §9.7.1.15 (popc): "Count the number of one bits in a and place the resulting population count in
    32-bit destination register d ."
- §9.7.1.16 (clz): "Count the number of leading zeros in a starting with the most-significant bit"
- §9.7.1.17 (bfind): "For signed integers, bfind returns the bit position of the most significant 0
    for negative inputs and the most significant 1 for non-negative inputs."
- §9.7.1.17 (bfind): "bfind returns 0xffffffff if no non-sign bit is found."
- §9.7.1.18 (fns): "Operand base must be <= 31, otherwise behavior is undefined."
- §9.7.1.19 (brev): "d[i] = a[msb-i];"
- §9.7.1.20 (bfe): "d[i] = (i<len && pos+i<=msb) ? a[pos+i] : sbit;"
- §9.7.1.21 (bfi): "f[pos+i] = a[i];"
- §9.7.1.22 (szext): "d = (a & ~mask) | (sign_bit ? mask : 0);"
- §9.7.1.23 (bmsk): "d = mask0 & ~mask1;"
- §9.7.9.1–§9.7.9.4 (and, or, xor, not): "Allowed types include predicate registers."
- §9.7.9.1–§9.7.9.4 (not): "Invert the bits in a ."
- §9.7.9.5 (cnot): "d = (a==0) ? 1 : 0;"
- §9.7.9.6 (lop3): "ta = 0xF0; tb = 0xCC; tc = 0xAA; immLut = F(ta, tb, tc);"
- §9.7.9.6 (lop3): "p = (d != 0) BoolOp q;"
- §9.7.9.7 (shf): "Operand b holds bits 63:32 and operand a holds bits 31:0 of the 64-bit source
    value."
- §9.7.9.7 (shf): "For shf.l , the most-significant 32-bits of the result are written into d ; for
    shf.r , the least-significant 32-bits of the result are written into d ."
- §9.7.9.7 (shf): "u32 n = (.mode == .clamp) ? min(c, 32) : c & 0x1f;"
- §9.7.9.8 (shl): "Shift amounts greater than the register width N are clamped to N ."
- §9.7.9.9 (shr): "Signed shifts fill with the sign bit, unsigned and untyped shifts fill with 0 ."
- §9.3.2: "Predicate values may be computed and manipulated using the following instructions: and ,
    or , xor , not , and mov ."
- §9.7.10.7 (prmt): "The 3 lsbs of the selection value specify which of the 8 source bytes should be
    moved into the target position."
- §9.7.10.7 (prmt): "msb=0 means copy the literal value; msb=1 means replicate the sign."
- §9.7.1.5 (clmad): "tmp[127:0] = 0; // 128-bit result of carryless multiplication. for (i = 0; i <
    64; i++) { if ((a & (1 << i)) != 0) { tmp ^= b << i; } }"
- §9.7.1.5 (clmad): "if (.mode == .lo) { d = tmp[63..0]; } else { d = tmp[127..64]; } d ^= c; //
    carryless accumulation."
- §9.7.1.24 (dp4a): "Operand c has type .u32 if both .atype and .btype are .u32 else operand c has
    type .s32 ."
- §9.7.1.24 (dp4a): "Va = extractAndSignOrZeroExt_4(a, .atype); Vb = extractAndSignOrZeroExt_4(b,
    .btype); for (i = 0; i < 4; ++i) { d += Va[i] * Vb[i]; }"
- §9.7.1.25 (dp2a): "Va = extractAndSignOrZeroExt_2(a, .atype);"
- §9.7.1.25 (dp2a): "b_select = (.mode == .lo) ? 0 : 2; for (i = 0; i < 2; ++i) { d += Va[i] *
    Vb[b_select + i]; }"
- §9.7.2: "No other instructions access the condition code, and there is no support for setting,
    clearing, or testing the condition code."
- §9.7.2 (add.cc): "d = a + b; carry-out written to CC.CF"
- §9.7.2 (addc): "d = a + b + CC.CF; if .cc specified, carry-out written to CC.CF"
- §9.7.2 (sub.cc): "d = a - b; borrow-out written to CC.CF"
- §9.7.2 (subc): "d = a - (b + CC.CF); if .cc specified, borrow-out written to CC.CF"
- §9.7.2: "Behavior is the same for unsigned and signed integers."
- §9.7.2 (mad.cc): "t = a * b; d = t<63..32> + c; // for .hi variant d = t<31..0> + c; // for .lo
    variant carry-out from addition is written to CC.CF"
- §9.7.2 (madc): "d = t<63..32> + c + CC.CF; // for .hi variant d = t<31..0> + c + CC.CF; // for .lo
    variant if .cc specified, carry-out from addition is written to CC.CF"
- §9.7.7.1 (set): "If this result is True , 1.0f is written for floating-point destination types,
    and 0xffffffff is written for integer destination types. Otherwise, 0x00000000 is written."
- §9.7.7.1 (set): "If the result is True, 0xffff is written to the destination register at a
    bit-position corresponding to input half word values."
- §9.7.7.2 (setp): "t = (a CmpOp b) ? 1 : 0; p = BoolOp(t, c); q = BoolOp(!t, c);"
- §9.7.7.2 (setp): "The sink symbol ‘_’ may be used in place of any one of the destination
    operands."
- §9.3.1.1 (integer comparisons)
- §4.5.3: "For predicate-type data initializers and instruction operands, integer constants are
    interpreted as in C, i.e., zero values are False and non-zero values are True ."

**Applies:** The integer instructions whose rule is THREAD-INT (`IntInstr.rule`, PROG-ISA-INT)

**Premises:** Operands satisfy the register rules and the instruction's width restrictions; a `.pred` operand is a register holding a predicate.

**Effect:** Local evaluation; an unspecified result is `noRule`, and an `fns` base above 31 is `badValue`. Integers are exact bit vectors, and every result is truncated to its destination width (wraparound), as `neg` and `abs` of the most negative value are. A packed type such as `.u16x2` computes each lane of its own width and kind (`intLane`, `intOfLanes`), lane 0 lowest. `.sat` clamps the exact result to the range of the lane type (`intSat`); `.relu` clamps a negative `min` or `max` to 0. `mul.hi` keeps the upper half of the double-width product, `mul.wide` all of it; `mad` adds `c` to that half (of the width of `d` for `.wide`). `mul24` and `mad24` take `t<47..16>` or `t<31..0>` of the exact product. Shifts by the width or more give `0`, or for `shr.s` the sign bit in every position (the amount is clamped to the width). The bit instructions `popc`, `clz`, `bfind`, `fns`, `brev`, `bfe`, `bfi`, `szext`, `bmsk`, `lop3`, `shf` and `prmt` transcribe the loops and tables of their Semantics sections; `shf` shifts the 64-bit value `b:a` as its Description states, which gives `b` for `shf.l` by 0 and `a` by 32. A logic instruction of width 1 is the `.pred` type: it reads predicate registers and integer constants (zero is false, non-zero true; `readPred`) and writes a predicate; any other source value is a type error. `setp` writes `BoolOp(t, c)` to `p` and `BoolOp(!t, c)` to `q`, and `set` writes all ones (or `1.0f`, the bits `0x3F800000`, for an `.f32` destination) per true lane. The manual gives no result for division or remainder by zero, for a quotient that does not fit the type (the most negative value divided by -1), or for a signed quotient or remainder whose value depends on the rounding of the division: `intDiv` has no rule when the quotient is negative and inexact (where rounding toward zero and toward negative infinity differ), and `intRem` has none when an operand of a signed remainder is negative. A `mul24` or `mad24` operand that is not a 24-bit value of its type has no 24-bit product, and has no rule. Each of these is `noRule`, so a kernel assumption may supply the machine's value; without one the execution is undefined (Direction: stricter). A `setp` whose `p` and `q` are the same register has no rule (`IntInstr.rule`), since the manual does not say which value the register keeps. `clmad` transcribes its Semantics loop (`clmulBits`). `dp4a` and `dp2a` extend the bytes or half-words of their operands by `.atype` and `.btype` and add the products to `c` read as `.u32` or `.s32` (`dotBits`); the sum wraps at 32 bits. The extended-precision instructions keep the carry flag `CC.CF` in the thread state (THREAD-STATE). The carry-in is `CC.CF` for `addc`, `subc` and `madc` and 0 for the others (`carryIn`). The carry-out of an addition of `n`-bit values is 1 exactly when the unsigned sum of the bit patterns and the carry-in is at least `2^n`, which is the same for signed and unsigned types; the borrow-out of `a - (b + CC.CF)` is 1 exactly when the unsigned `a` is below `b + CC.CF`. `mad.cc` and `madc` take the half `t<2n-1..n>` or `t<n-1..0>` of the product read by the type, as `mad.hi` does, and add `c` as unsigned bit patterns. The flag is written only under `.cc` (`setCarry`). The manual gives the flag no initial value, so an instruction that reads `CC.CF` before any instruction of the thread has written it has no rule (`noRule`). Calls are not modeled, so the sentence that the flag is not preserved across calls does not apply.

</details>

<a id="thread-num"></a>
#### numeric operand interpretation (`THREAD-NUM`)

*Rule* · [Lean comment: `Core/Thread/Local.lean` L1154-L1211](../../Core/Thread/Local.lean#L1154-L1211)

A floating operand is read as a datum of the instruction's format: an opaque NaN of the format is NaN, and every other value, a payload included, is read through its bit pattern as a pattern of that format. A `0f` constant is its 32-bit pattern. The real-number reader of the assumptions takes a payload of the format as its number and rejects NaN and infinity, and a value of another width or without a bit pattern is a type error.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`classify`](../../Core/Thread/Local.lean#L1214-L1226) ([concept](#c-classify)), [`FVal.finite`](../../Core/Thread/Local.lean#L1228-L1233), [`bitsAsFloat`](../../Core/Thread/Local.lean#L1235-L1236), [`bitsAsFloat_eq`](../../Core/Thread/Local.lean#L1238-L1266), [`valFloat`](../../Core/Thread/Local.lean#L1268-L1272), [`readFloat`](../../Core/Thread/Local.lean#L1274-L1278) ([concept](#c-readfloat)), [`classify_bits`](../../Core/Thread/Local.lean#L1280-L1287), [`classify_float_repr`](../../Core/Thread/Local.lean#L1289-L1293), [`valFloat_float`](../../Core/Thread/Local.lean#L1295-L1297), [`valFloat_of_classify`](../../Core/Thread/Local.lean#L1299-L1306), [`FVal.toValue`](../../Core/Thread/Local.lean#L1308-L1317) ([concept](#c-fval-tovalue)), [`floatLane`](../../Core/Thread/Local.lean#L2831-L2836), [`unitValue`](../../Core/Thread/Local.lean#L2838-L2840), [`setResult`](../../Core/Thread/Local.lean#L2842-L2865), [`execFloat`](../../Core/Thread/Local.lean#L2867-L2911) ([concept](#c-execfloat))

<details>
<summary>Details for reviewers</summary>

- §5.2.1: "The bit-size type is compatible with any fundamental type having the same size."
- §6.1: "Operands having type different from but compatible with the instruction type are silently
    cast to the instruction type."
- §9.7.3 (add.f32x2): "fA[0] = a[0:31]; fA[1] = a[32:63];"
- §9.7.3: "Single-precision instructions return an unspecified NaN"
- §9.7.7.2: "p = BoolOp(t, c); q = BoolOp(!t, c);"
- §9.7.8.2: "p = BoolOp(t[0], c); q = BoolOp(t[1], c);"
- §9.7.7.1: "1.0f is written for floating-point destination types, and 0xffffffff is written for
    integer destination types. Otherwise, 0x00000000 is written."
- §9.7.8.1: "1.0 in target precision floating point format is written for destination type .f16 ,
    .bf16 ."
- §9.7.8.1: "} else if (dtype == .f16 || stype == .bf16) { t = (a CmpOp b) ? 1 : 0; d = BoolOp(t,
    c) ? 1.0 : 0.0; }"
- §9.7.8.1: "if (dtype == .f16x2 || stype == .bf16x2) { for (i = 0; i < 2; i++) { d[i] =
    BoolOp(t[i], c) ? 1.0 : 0.0; } }"

**Applies:** Floating operands of every format, and every floating instruction

**Premises:** The operand is an opaque NaN of the instruction's format, or a value with a bit pattern of the format's width.

**Effect:** Operand decoding and result encoding. `classify` is the only reading of floating data from bits (THREAD-FLOAT-FORMAT); THREAD-FLOAT and THREAD-CVT read their operands with it, so a payload `.float fmt x` whose number is not representable in `fmt` is read as the number its bits give (EXT-FLOAT-BITS), and a payload whose number is representable as that number (`classify_float_repr`). `valFloat`, the reader of the ideal assumptions (ASM-IDEAL) and of MMA and reduction elements, differs from it on a payload of the instruction's format only, which it reads as its number (`valFloat_float`); it reads every other value through `classify` and has no real for NaN and infinity (`badValue`, stricter than the ISA, which defines arithmetic on them). `bitsAsFloat_eq` states its reading of a value other than an opaque NaN as the finite decoder `FloatFmt.decode` of the value's bits. A value of another width or without a bit pattern is a type error. A result is written by `FVal.toValue`: a finite number or `+0` as the payload of the destination format, `-0`, an infinity and a NaN with a known pattern as its bits, and a NaN whose pattern the manual leaves unspecified as the opaque `Value.nan` (THREAD-VALUE). `execFloat` runs a floating instruction (THREAD-FLOAT): it reads each source at its type's width, classifies each lane in its format (`floatLane`), takes each lane's result from `FloatInstr.lane`, combines a comparison with `BoolOp` and `c` (`boolCombine`; `q` of a scalar `setp` is `BoolOp(!t, c)`, and `p`, `q` of a packed `setp` are the two lanes), and writes the results; `set` writes `1.0`/`0.0` in a floating destination and all ones/zero in an integer one (`setResult`), and a `set` with an integer source type compares as THREAD-INT does. Where the Semantics of §9.7.8.1 and its Description give different values (the Semantics tests "} else if (dtype == .f16 || stype == .bf16) {" and "if (dtype == .f16x2 || stype == .bf16x2) {"), there is no rule: a `.bf16` destination with another source type, and an integer destination with a `.bf16` or `.bf16x2` source.

</details>

<a id="thread-float"></a>
#### floating instructions (`THREAD-FLOAT`)

*Rule* · [Lean comment: `Core/Thread/Float.lean` L18-L55](../../Core/Thread/Float.lean#L18-L55)

A floating instruction reads each source as a datum of its format and computes each lane of its result from the data of that lane: the IEEE operations and the instructions defined by their text by THREAD-FLOAT-IEEE, and the approximate instructions by THREAD-FLOAT-APPROX. A result the manual leaves open has no rule.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`FOut`](../../Core/Thread/Float.lean#L58-L63), [`FloatInstr.lane`](../../Core/Thread/Float.lean#L65-L77) ([concept](#c-floatinstr-lane))

<details>
<summary>Details for reviewers</summary>

- §9.7.3.3: "fA[0] = a[0:31]; fA[1] = a[32:63]; fB[0] = b[0:31]; fB[1] = b[32:63]; for (i = 0; i <
    2; i++) { d[i] = fA[i] + fB[i]; }"
- §9.7.4.1: "fA[0] = a[0:15]; fA[1] = a[16:31]; fB[0] = b[0:15]; fB[1] = b[16:31];"
- §9.7.3: "Single-precision instructions return an unspecified NaN"
- §9.7.4: "Half-precision instructions return an unspecified NaN ."

**Applies:** Every floating instruction whose rule is THREAD-FLOAT (`FloatInstr.rule`, PROG-ISA-FLOAT)

**Premises:** The operands satisfy the register rules (THREAD-REG); each floating source is read by `classify` as a datum of its format (THREAD-NUM).

**Effect:** Local evaluation. Each floating source is read with `classify` in its format, which is the source's entry of `srcTys` for a mixed-precision form and the instruction's type otherwise; an opaque NaN reads as the NaN with an unknown pattern. A packed source of an `x2` type has two elements, its halves, the low half first; lane `i` takes element `i` of every packed source, and the result of lane `i` is element `i` of the destination. `FloatInstr.lane` gives the result of one lane from the lane's floating sources in operand order (`FOut`): the Boolean of `testp` and of the comparison of `setp` and `set`, and the datum in the destination format for every other operation; `setp` and `set` combine it with their `BoolOp` and predicate operand, and `set` encodes it, in `execFloat`, which runs the lanes. A `set` with an integer source type compares integers and has no floating lane. The result is written by `FVal.toValue`: a payload for a number and `+0`, the opaque NaN value for a NaN with an unknown pattern, and the bit pattern for `-0`, an infinity and a NaN with a known pattern; a packed result is the pair of its elements, the low element first. A form whose rule is not THREAD-FLOAT has no lane. The rule is stricter than the manual where a result is open: a NaN with unknown bits stays opaque, and every case THREAD-FLOAT-IEEE and THREAD-FLOAT-APPROX leave without a rule is rejected.

</details>

<a id="thread-float-ieee"></a>
#### IEEE 754 operations and the instructions defined by their text (`THREAD-FLOAT-IEEE`)

*Rule* · [Lean comment: `Core/Float/Ieee.lean` L22-L138](../../Core/Float/Ieee.lean#L22-L138)

An instruction with a rounding modifier computes the exact result of its operands in the extended reals and rounds it to the destination format by IEEE 754, with the IEEE 754 rules for NaN, invalid operations and the sign of an exact zero (EXT-IEEE754); a NaN result has unspecified bits. `neg`, `abs`, `copysign`, `min`, `max`, `testp`, `setp` and `set` follow the text and the Semantics pseudocode of their sections.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`FVal.isNaN`](../../Core/Float/Ieee.lean#L162-L165), [`FVal.isNeg`](../../Core/Float/Ieee.lean#L167-L171), [`FVal.toRat`](../../Core/Float/Ieee.lean#L173-L176), [`FVal.signBit`](../../Core/Float/Ieee.lean#L178-L183), [`FVal.withSign`](../../Core/Float/Ieee.lean#L185-L193), [`FVal.negate`](../../Core/Float/Ieee.lean#L195-L200), [`FVal.absV`](../../Core/Float/Ieee.lean#L202-L207), [`FVal.subnormalIn`](../../Core/Float/Ieee.lean#L209-L212), [`FVal.add`](../../Core/Float/Ieee.lean#L214-L225), [`FVal.mul`](../../Core/Float/Ieee.lean#L227-L235), [`FVal.div`](../../Core/Float/Ieee.lean#L237-L249), [`Layout.roundFtz`](../../Core/Float/Ieee.lean#L252-L262), [`Layout.roundVal`](../../Core/Float/Ieee.lean#L264-L268), [`Layout.sqrt`](../../Core/Float/Ieee.lean#L271-L276), [`FVal.sat`](../../Core/Float/Ieee.lean#L278-L285), [`FVal.relu`](../../Core/Float/Ieee.lean#L287-L293), [`FVal.lt`](../../Core/Float/Ieee.lean#L295-L303), [`FVal.minMax`](../../Core/Float/Ieee.lean#L305-L313), [`minMaxOp`](../../Core/Float/Ieee.lean#L315-L331), [`FVal.copysign`](../../Core/Float/Ieee.lean#L333-L338), [`Cmp.evalF`](../../Core/Float/Ieee.lean#L340-L349), [`FCmp.eval`](../../Core/Float/Ieee.lean#L351-L357), [`TestProp.eval`](../../Core/Float/Ieee.lean#L359-L373), [`FloatInstr.srcFmt`](../../Core/Float/Ieee.lean#L375-L378), [`FloatInstr.flushIn`](../../Core/Float/Ieee.lean#L380-L382), [`FloatInstr.arith`](../../Core/Float/Ieee.lean#L384-L407), [`FloatInstr.ieee`](../../Core/Float/Ieee.lean#L409-L422), [`FloatInstr.compare`](../../Core/Float/Ieee.lean#L424-L430)

<details>
<summary>Details for reviewers</summary>

- §9.7.3: "Instructions that support rounding modifiers are IEEE-754 compliant."
- §9.7.3: "Single-precision instructions return an unspecified NaN"
- §9.7.4: "Half-precision instructions return an unspecified NaN ."
- §9.7.3: "NaN payloads are supported for double-precision instructions (except for
    rcp.approx.ftz.f64 and rsqrt.approx.ftz.f64 , which maps input NaN s to a canonical NaN )."
- §9.7.3: "The optional .ftz modifier on single-precision instructions provides backward
    compatibility with sm_1x targets by flushing subnormal inputs and results to sign-preserving
    zero regardless of the target architecture"
- §9.7.3: "If no rounding modifier is specified, default is .rn and instructions may be folded
    into a multiply-add."
- §9.7.3.3: "In particular, mul / add sequences with no rounding modifiers may be optimized to use
    fused-multiply-add instructions on the target device"
- §9.7.3.6: "fma.f32 computes the product of a and b to infinite precision and then adds c to this
    product, again in infinite precision"
- §9.7.3.7: "mad.{f32,f64} is the same as fma.{f32,f64}"
- §9.7.3.8: "Divide with IEEE 754 compliant rounding:"
- §9.7.3.13: "Reciprocal with IEEE 754 compliant rounding:"
- §9.7.3.15: "Square root with IEEE 754 compliant rounding:"
- §9.7.3.3: "Saturation modifier: add.sat.f32 clamps the result to [0.0, 1.0]."
- §9.7.3.3: "NaN results are flushed to +0.0f ."
- §9.7.4.4: "fma.relu.{f16, f16x2, bf16, bf16x2} clamps the result to 0 if negative"
- §9.7.4.4: "NaN result is converted to canonical NaN"
- §9.7.4.4: "Out Of Bounds modifier: fma.oob.{f16, f16x2, bf16, bf16x2} clamps the result to 0 if
    either of the operands is OOB NaN (defined under Tensors ) value"
- §9.7.5: "Before executing the specified operation, operands with different precision needs to
    be converted such that all the instruction operands can be represented with a consistent
    floating-point precision"
- §9.7.5.1: "d[0:15] = convert(a[0:31] + c[0:31]); // Apply rz for output"
- §9.7.5.4: "d[0:15] = convert(a[0:31] * c[0:31]); // Apply rz for output"
- §9.7.3.10: "Negate the sign of a and store the result in d ."
- §9.7.3.10: "NaN inputs yield an unspecified NaN"
- §9.7.3.9: "Take the absolute value of a and store the result in d ."
- §9.7.3.9: "For abs.f32 , NaN input yields unspecified NaN"
- §9.7.3.9: "For abs.f64 , NaN input is passed through unchanged"
- §9.7.3.2: "Copy sign bit of a into value of b , and return the result as d ."
- §9.7.3.1: "testp.finite True if the input is not infinite or NaN testp.infinite True if the input
    is positive or negative infinity testp.number True if the input is not NaN testp.notanumber
    True if the input is NaN testp.normal True if the input is a normal number (not NaN , not
    infinity) testp.subnormal True if the input is a subnormal number (not NaN , not infinity) As
    a special case, positive and negative zero are considered normal numbers."
- §9.7.3.11: "def min_num (z, x, y) { if (isNaN(x) && isNaN(y)) z = NaN; else if (isNaN(x)) z = y;
    else if (isNaN(y)) z = x; else // note: -0.0 < +0.0 here z = (x < y) ? x : y; return z; }"
- §9.7.3.11: "def min_nan (z, x, y) { if (isNaN(x) || isNaN(y)) z = NaN; else // note: -0.0 < +0.0
    here z = (x < y) ? x : y; return z; }"
- §9.7.3.11: "if (.xorsign && !isPresent(c)) { xorsign = getSignBit(a) ^ getSignBit(b); } if (.abs)
    { a = |a|; b = |b|; if (isPresent(c)) { c = |c|; } } d = two_inputs_min(d, a, b) if
    (isPresent(c)) { d = two_inputs_min(d, d, c) } if (.xorsign && !isPresent(c) && !isNaN(d)) {
    setSignBit(d, xorsign); }"
- §9.7.3.11: "If the result of min is NaN then the .xorsign and .abs modifiers will be ignored"
- §9.7.3.11: "If values of both inputs are 0.0, then +0.0 > -0.0."
- §9.7.3.12: "if (.xorsign && !isPresent(c) !isNaN(d)) { setSignBit(d, xorsign); }"
- §9.7.4.8: "if (.xorsign && !isNaN(fA[i])) { setSignBit(d[i], xorsign); }"
- §9.7.4.8: "If the result of max is NaN then the .xorsign and .abs modifiers will be ignored."
- §9.3.1.2: "If either operand is NaN , the result is False ."
- §9.3.1.2: "If both operands are numeric values (not NaN ), then the comparison has the same result
    as its ordered counterpart. If either operand is NaN , then the result of the comparison is
    True ."
- §9.3.1.2: "num returns True if both operands are numeric values (not NaN ), and nan returns True
    if either operand is NaN ."
- §9.7.7.2: "setp.ftz.dtype.f32 flushes subnormal inputs to sign-preserving zero."
- §9.7.7.2: "Modifier .ftz applies only to .f32 comparisons."
- EXT-IEEE754

**Applies:** The floating instructions whose rule is THREAD-FLOAT and whose mode is not `.approx`

**Premises:** The sources are read as data of their formats (THREAD-FLOAT).

**Effect:** Local evaluation. `FloatInstr.arith` computes `add`, `sub`, `mul`, `fma`, `mad` (the rule of `fma`), `div`, `rcp` (`1 / a`) and `sqrt` exactly and rounds by the written modifier with IEEE 754 overflow (`Layout.round`, THREAD-FLOAT-ROUND). A NaN operand, `∞ − ∞`, `0 × ∞`, `0 / 0`, `∞ / ∞` and the square root of a negative number give a NaN whose bits are unknown; the manual names no payload for these results, `.f64` included. An exact zero sum is `-0` when both operands are `-0`, `+0` when both are `+0`, and otherwise `+0` except under `.rm`, which gives `-0` (IEEE 754 §6.3); a zero product or quotient has the XOR of the operand signs. An `add`, `sub` or `mul` without a written rounding modifier has no rule, since the code optimizer may fuse it with a neighbouring instruction and the result then depends on another instruction. `.ftz` flushes every subnormal input and result to the zero of its sign; the manual does not say whether a result is tested before or after rounding, so an exact result below the smallest normal magnitude that rounds to a normal number has no rule (`Layout.roundFtz`). `.relu` makes a negative result `+0` and a NaN result an opaque NaN; `.sat` makes a NaN result `+0` and clamps to `[0.0, 1.0]`; both are applied after the flush, and under both a `-0` result has no rule, since the manual does not say whether the clamp keeps the sign of zero. `.oob` has no rule with a NaN operand, since the manual gives no encoding of the OOB-NaN, and no effect otherwise. A mixed-precision form computes on its operands in their own formats, which converts each of them exactly to `.f32`, and rounds once to the destination format; for the `.rz` forms to `.bf16x2` and `.f16x2` this equals the rounding to `.f32` followed by the rounding to the destination, since rounding toward zero twice through a finer grid equals rounding once. The forms to `.f16x2` carry `.ftz` without a subnormal sentence, so they have a rule only when no input is subnormal in its format and the result is not subnormal, where flushing and not flushing agree. `neg` flips and `abs` clears the sign of a datum after the `.ftz` flush; a NaN input gives an opaque NaN, except that `abs.f64` passes it through. `copysign` gives `b` with the sign bit of `a`; an opaque NaN `a` gives no rule unless `b` is an opaque NaN too. `min` and `max` follow the Semantics pseudocode, with `-0` below `+0`; a NaN result is opaque; `.xorsign` uses the sign bit of a NaN operand when its pattern is known and has no rule when it is unknown. The `.f32` `max` pseudocode lacks an operator in `!isPresent(c) !isNaN(d)`, which is read as `&&` as in `min`. The `.f16x2` and `.bf16x2` `max` pseudocode applies `.xorsign` when `fA[i]` is not NaN, while the description ignores `.xorsign` only for a NaN result, so a lane whose `fA[i]` is NaN and whose result is not NaN has no rule under `.xorsign`. A comparison compares the numbers of its operands in the extended reals, both zeros denoting `0`, with Tables 23 to 25 for NaN; `lo`, `ls`, `hi` and `hs` have no floating rule. `testp` classifies its operand, an opaque NaN being `notanumber` and both zeros normal.

</details>

<a id="ext-ieee754"></a>
##### the IEEE 754 rules of the instructions with rounding modifiers (`EXT-IEEE754`)

*Interpretation (EXT)* · [Lean comment: `Core/Float/Ieee.lean` L140-L159](../../Core/Float/Ieee.lean#L140-L159)

An instruction with a rounding modifier computes the exact result of its operands and rounds it as IEEE 754 specifies: the rounding-direction attributes, the arithmetic of infinity and NaN, the sign of an exact zero result, invalid operations and overflow per rounding direction. The sentences of the manual that override IEEE 754 (`.ftz`, `.sat`, `.relu`, `.satfinite`, the unspecified NaN) take precedence.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The manual states "Instructions that support rounding modifiers are IEEE-754 compliant." and, for `fma`, "fma.f32 computes the product of a and b to infinite precision and then adds c to this product, again in infinite precision", without restating the IEEE 754 rules it imports. The model takes them from IEEE 754-2008 and IEEE 754-2019, which agree on every rule used here (§4.3 rounding-direction attributes, §6.1 and §6.2 infinity and NaN arithmetic, §6.3 the sign bit, §7.2 invalid operation, §7.4 overflow).

**Effect:** The special values, the zero signs and the rounded results of THREAD-FLOAT-IEEE, THREAD-FLOAT-ROUND and THREAD-CVT follow these rules; if the hardware deviates from IEEE 754 in a case the manual does not mention, the proven results differ from the hardware's. Disclosed by every kernel whose statement names `Op.float` or `Op.cvt`: BlockSum, FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, RowSum.

</details>

<a id="thread-float-approx"></a>
#### the tables of the approximate instructions (`THREAD-FLOAT-APPROX`)

*Rule* · [Lean comment: `Core/Float/Approx.lean` L19-L83](../../Core/Float/Approx.lean#L19-L83)

An approximate instruction gives the result its table lists for the class of its operand after the `.ftz` flush, and has no rule for every input the table does not list.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`ACls`](../../Core/Float/Approx.lean#L86-L89), [`ACls.of`](../../Core/Float/Approx.lean#L91-L98), [`ARes`](../../Core/Float/Approx.lean#L100-L106), [`ARes.val`](../../Core/Float/Approx.lean#L108-L113), [`ATable`](../../Core/Float/Approx.lean#L115-L116), [`rcpTable`](../../Core/Float/Approx.lean#L118-L121), [`rcpF64Table`](../../Core/Float/Approx.lean#L123-L126), [`sqrtTable`](../../Core/Float/Approx.lean#L128-L131), [`rsqrtTable`](../../Core/Float/Approx.lean#L133-L136), [`rsqrtF64Table`](../../Core/Float/Approx.lean#L138-L141), [`sinTable`](../../Core/Float/Approx.lean#L143-L146), [`cosTable`](../../Core/Float/Approx.lean#L148-L151), [`lg2Table`](../../Core/Float/Approx.lean#L153-L156), [`ex2Table`](../../Core/Float/Approx.lean#L158-L161), [`tanhTable`](../../Core/Float/Approx.lean#L163-L166), [`ex2Bf16Table`](../../Core/Float/Approx.lean#L168-L171), [`ex2F16Table`](../../Core/Float/Approx.lean#L173-L176), [`upperLayout`](../../Core/Float/Approx.lean#L178-L179), [`upperWord`](../../Core/Float/Approx.lean#L181-L188), [`approxF64`](../../Core/Float/Approx.lean#L190-L198), [`divApprox`](../../Core/Float/Approx.lean#L200-L211), [`FloatInstr.approxTable?`](../../Core/Float/Approx.lean#L213-L227), [`FloatInstr.approx`](../../Core/Float/Approx.lean#L229-L239)

<details>
<summary>Details for reviewers</summary>

- §9.7.3.13: "Input Result -Inf -0.0 -0.0 -Inf +0.0 +Inf +Inf +0.0 NaN NaN"
- §9.7.3.14: "extract the most-significant 32 bits of .f64 operand a in 1.11.20 IEEE floating-point
    format (i.e., ignore the least-significant 32 bits of a )"
- §9.7.3.14: "tmp = a[63:32]; // upper word of a, 1.11.20 format d[63:32] = 1.0 / tmp; d[31:0] =
    0x00000000;"
- §9.7.3.14: "Input a[63:32] Result d[63:32] -Inf -0.0 -subnormal -Inf -0.0 -Inf +0.0 +Inf
    +subnormal +Inf +Inf +0.0 NaN NaN Input NaN s map to a canonical NaN with encoding
    0x7fffffff00000000"
- §9.7.3.14: "Subnormal inputs and results are flushed to sign-preserving zero."
- §9.7.3.15: "Input Result -Inf NaN -normal NaN -0.0 -0.0 +0.0 +0.0 +Inf +Inf NaN NaN"
- §9.7.3.16: "Input Result -Inf NaN -normal NaN -0.0 -Inf +0.0 +Inf +Inf +0.0 NaN NaN"
- §9.7.3.17: "tmp = a[63:32]; // upper word of a, 1.11.20 format d[63:32] = 1.0 / sqrt(tmp);
    d[31:0] = 0x00000000;"
- §9.7.3.17: "Input Result -Inf NaN -subnormal -Inf -0.0 -Inf +0.0 +Inf +subnormal +Inf +Inf +0.0
    NaN NaN Input NaN s map to a canonical NaN with encoding 0x7fffffff00000000"
- §9.7.3.18: "Input Result -Inf NaN -0.0 -0.0 +0.0 +0.0 +Inf NaN NaN NaN"
- §9.7.3.19: "Input Result -Inf NaN -0.0 +1.0 +0.0 +1.0 +Inf NaN NaN NaN"
- §9.7.3.20: "Input Result -Inf NaN -normal NaN -0.0 -Inf +0.0 -Inf +Inf +Inf NaN NaN"
- §9.7.3.21: "Input Result -Inf +0.0 -0.0 +1.0 +0.0 +1.0 +Inf +Inf NaN NaN"
- §9.7.3.22: "Input Result -Inf -1.0 -0.0 -0.0 +0.0 +0.0 +Inf 1.0 NaN NaN"
- §9.7.4.10: "Results of ex2.approx.ftz.bf16 for various corner-case inputs are as follows: Input
    Result -Inf +0.0 -subnormal +1.0 -0.0 +1.0 +0.0 +1.0 +subnormal +1.0 +Inf +Inf NaN NaN"
- §9.7.4.10: "Results of ex2.approx.f16 for various corner-case inputs are as follows: Input Result
    -Inf +0.0 -0.0 +1.0 +0.0 +1.0 +Inf +Inf NaN NaN"
- §9.7.3.8: "For 2 126 < |b| < 2 128 , if a is infinity, div.approx.f32 returns NaN , otherwise it
    returns a sign-preserving zero."
- §9.7.3.8: "div.full.f32 implements a relatively fast, full-range approximation that scales
    operands to achieve better accuracy, but is not fully IEEE 754 compliant and does not support
    rounding modifiers"
- §9.7.3: "Single-precision instructions return an unspecified NaN"

**Applies:** The floating instructions whose rule is THREAD-FLOAT and whose mode is `.approx`

**Premises:** The sources are read as data of their formats (THREAD-FLOAT).

**Effect:** Local evaluation. The tables are data (`ATable`), one per instruction and format, with the rows of the manual; a row gives a zero, an infinity, `±1.0` or NaN, and a NaN result is an opaque NaN. `.ftz` flushes a subnormal input to the zero of its sign before the lookup; no listed result is subnormal. A row the table does not list has no rule; this includes every finite nonzero input of `sin`, `cos`, `ex2` and `tanh`, every positive one of `rcp`, `sqrt`, `rsqrt` and `lg2`, and a subnormal input without `.ftz` where the table has no subnormal row. `rcp.approx.ftz.f64` and `rsqrt.approx.ftz.f64` look up the upper word `a[63:32]` in the 1.11.20 layout: for a number it is the rounding toward zero of the number to that layout, for a zero or an infinity the same datum, and for a NaN with a known pattern the datum of its upper 32 bits. A NaN whose upper word is a NaN gives the NaN `0x7fffffff00000000`; a NaN whose upper word is an infinity (a payload in the low word only) has no rule, since its row and the NaN sentence give different results; an opaque NaN has no rule, since its upper word is unknown. The NaN that `rsqrt.approx.ftz.f64` gives for `-Inf` is an opaque NaN, since the stated encoding is for NaN inputs. `rsqrt.approx.f64` uses the `.f32` table with an opaque NaN. `div.approx.f32` with `2^126 < |b| < 2^128` gives an opaque NaN for an infinite `a`, and for a finite `a` and a positive `b` the zero with the sign of `a`; for a negative `b` the sign-preserving zero can have the sign of `a` or of the quotient, so it has no rule, and so has a NaN `a`. Every other `div.approx` input has no rule. `div.full` has no rule (`FloatInstr.rule`); its text gives only an error bound.

</details>

<a id="thread-float-round"></a>
#### rounding an exact number to a layout (`THREAD-FLOAT-ROUND`)

*Rule* · [Lean comment: `Core/Float/Round.lean` L20-L81](../../Core/Float/Round.lean#L20-L81)

An exact real number is rounded to a layout by one of the rounding modes `.rn`, `.rz`, `.rm`, `.rp` and `.rs`, with IEEE 754 overflow or `.satfinite` saturation. Where the manual leaves the result open, the rounding has no result.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`RoundMode`](../../Core/Float/Round.lean#L84-L89), [`Overflow`](../../Core/Float/Round.lean#L91-L94), [`FloatRound.mode`](../../Core/Float/Round.lean#L96-L101), [`RoundMode.away`](../../Core/Float/Round.lean#L104-L120), [`RoundMode.applies`](../../Core/Float/Round.lean#L122-L129), [`Layout.fixedVal`](../../Core/Float/Round.lean#L131-L134), [`Layout.round`](../../Core/Float/Round.lean#L137-L183) ([concept](#c-layout-round)), [`FloatFmt.overflow`](../../Core/Float/Round.lean#L450-L454), [`FloatFmt.maxField`](../../Core/Float/Round.lean#L456-L461), [`FloatFmt.encode`](../../Core/Float/Round.lean#L463-L466), [`Layout.findGreatest_mag`](../../Core/Float/Round.lean#L188-L198), [`Layout.maxNorm_binary`](../../Core/Float/Round.lean#L200-L202), [`Layout.mag_le_maxNorm`](../../Core/Float/Round.lean#L204-L208), [`Layout.round_zero`](../../Core/Float/Round.lean#L210-L214), [`Layout.round_exact`](../../Core/Float/Round.lean#L216-L240), [`Layout.round_between`](../../Core/Float/Round.lean#L242-L270), [`Layout.round_satfinite`](../../Core/Float/Round.lean#L272-L285), [`Layout.round_inf_none`](../../Core/Float/Round.lean#L287-L299), [`Layout.round_inf_ieee`](../../Core/Float/Round.lean#L301-L324), [`Layout.round_unsigned_below`](../../Core/Float/Round.lean#L326-L337), [`RoundMode.away_rz`](../../Core/Float/Round.lean#L340-L341), [`RoundMode.away_rm`](../../Core/Float/Round.lean#L343-L344), [`RoundMode.away_rp`](../../Core/Float/Round.lean#L346-L347), [`RoundMode.away_rn_lt`](../../Core/Float/Round.lean#L349-L352), [`RoundMode.away_rn_gt`](../../Core/Float/Round.lean#L354-L357), [`RoundMode.away_rn_tie`](../../Core/Float/Round.lean#L359-L362), [`RoundMode.away_rs`](../../Core/Float/Round.lean#L364-L372), [`Layout.maxNorm_fixed`](../../Core/Float/Round.lean#L374-L375), [`Layout.maxNorm_fixed_nonneg`](../../Core/Float/Round.lean#L377-L382), [`Layout.round_fixed_rs`](../../Core/Float/Round.lean#L384-L386), [`Layout.round_fixed_zero`](../../Core/Float/Round.lean#L388-L391), [`Layout.round_fixed_over`](../../Core/Float/Round.lean#L393-L405), [`Layout.round_fixed_under`](../../Core/Float/Round.lean#L407-L417), [`Layout.round_fixed_exact`](../../Core/Float/Round.lean#L419-L427), [`Layout.round_fixed_between`](../../Core/Float/Round.lean#L429-L447), [`FloatFmt.layout_facts`](../../Core/Float/Round.lean#L468-L477), [`FloatFmt.encode_fieldVal`](../../Core/Float/Round.lean#L479-L487), [`FloatFmt.encode_eq`](../../Core/Float/Round.lean#L490-L679), [`FloatFmt.decode_number`](../../Core/Float/Round.lean#L681-L711), [`FloatFmt.decode_encode_of_decode`](../../Core/Float/Round.lean#L713-L755), [`FloatFmt.decode_encode`](../../Core/Float/Round.lean#L757-L761)

<details>
<summary>Details for reviewers</summary>

- §6.5.2: ".rn rounds to nearest even .rna rounds to nearest, ties away from zero .rz rounds
    toward zero .rm rounds toward negative infinity .rp rounds toward positive infinity .rs rounds
    either toward zero or away from zero based on the carry out of the integer addition of random
    bits and the discarded bits of mantissa"
- §9.7.3.3: "Rounding modifiers: .rn mantissa LSB rounds to nearest even .rz mantissa LSB rounds
    toward zero .rm mantissa LSB rounds toward negative infinity .rp mantissa LSB rounds toward
    positive infinity"
- §9.7.10.24: "Operation’s result is rounded in the direction toward zero or away from zero based
    on the carry out of the integer addition of the supplied random bits ( rbits ) to the truncated
    off (discarded) bits of mantissa from the input."
- §9.7.10.24: "If the absolute value of input (ignoring sign) is greater than MAX_NORM of the
    specified destination format, then the result is sign-preserved MAX_NORM of the destination
    format and a positive MAX_NORM in .ue8m0x2 and .ue5m3x2 for which the destination sign is not
    supported."
- §5.2.4: "Positive max representation = 01.111111 = 127 * 2^(-6) = 1.984375 Negative max
    representation = 10.000000 = -128 * 2^(-6) = -2.0"
- §9.7.3: "Instructions that support rounding modifiers are IEEE-754 compliant."

**Applies:** The rounding of an exact result or an exact source value to a destination layout

**Effect:** Local evaluation. A value of the layout is its own result. Otherwise `lo` and `hi` are the neighbouring finite values of the layout in the code order: `.rz` takes the one nearer to zero, `.rm` the lower, `.rp` the higher, and `.rn` the nearer one, at the midpoint the one with the even code (the even mantissa of a binary layout, the even integer of a fixed-point layout). A binary layout with a zero-width mantissa has no result at a midpoint. Underflow is gradual, and a nonzero number that rounds to the zero field gives the zero of its sign; an exact zero gives the zero with the sign `zneg` the caller supplies, and the one zero of a fixed-point layout. Overflow with `Overflow.satfinite`: a magnitude above MAX_NORM gives the MAX_NORM of the sign of the number (positive for an unsigned layout). Overflow with `Overflow.inf` follows IEEE 754 for a layout with infinities: `.rn` gives the infinity from the midpoint between MAX_NORM and `2^(emax+1)` on, `.rz` gives MAX_NORM, `.rm` gives the infinity for a negative number only and `.rp` for a positive number only; a layout without infinity has no result. An unsigned layout has no result below its smallest positive value, which includes zero, negative numbers and the `.ue8m0` pattern `0`. For a fixed-point layout, a number below the negative of MAX_NORM has no result, since the sign-preserved MAX_NORM can be read as `-MAX_NORM` or as the negative maximum (for `.s2f6`, `-1.984375` or `-2.0`). `.rs k r` adds the `k`-bit random number `r` to the `D` discarded units: it applies to an `.f32` value that is zero or at least the smallest normal magnitude of a binary layout and lies `D` units of `2^-k` result ulps above the neighbour `t` nearer to zero, and gives the neighbour away from zero when `D + r ≥ 2^k` and `t` otherwise; overflow is decided on the input, and `.rs` has no result for a subnormal result, for `r ≥ 2^k`, for a fixed-point layout or with `Overflow.inf` above MAX_NORM.

</details>

<a id="thread-move"></a>
#### data movement (`THREAD-MOVE`)

*Rule* · [Lean comment: `Core/Thread/Local.lean` L1806-L1872](../../Core/Thread/Local.lean#L1806-L1872)

`mov`, `selp` and `slct` copy a value unchanged, and packing and unpacking keep the elements with the lowest first. `ld.param` reads a scalar kernel parameter, or the bytes that the host passed in a by-value parameter object named directly or by a register, little-endian and sign- or zero-extended into the destination register, and a byte the launch does not supply is a fault.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`execMove`](../../Core/Thread/Local.lean#L1961-L2049) ([concept](#c-execmove)), [`joinValue`](../../Core/Thread/Local.lean#L1875-L1883), [`splitValue`](../../Core/Thread/Local.lean#L1885-L1893), [`f32NonNeg`](../../Core/Thread/Local.lean#L1895-L1899), [`paramObjectBits`](../../Core/Thread/Local.lean#L1901-L1907), [`MemExt.extendBits`](../../Core/Thread/Local.lean#L1909-L1915), [`MemExt.extendBits_same`](../../Core/Thread/Local.lean#L1917-L1918), [`signExtendRegs`](../../Core/Thread/Local.lean#L1920-L1925), [`paramObjectOf`](../../Core/Thread/Local.lean#L1927-L1938), [`paramElem`](../../Core/Thread/Local.lean#L1940-L1945), [`paramElem_of_ne`](../../Core/Thread/Local.lean#L1947-L1950), [`loadParamObject`](../../Core/Thread/Local.lean#L1952-L1959)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.3 (mov): "Write register d with the value of a"
- §9.7.10.4 (mov pack/unpack): "pack four 16-bit elements into .b64 d = a.x | (a.y << 16) | (a.z <<
    32) | (a.w << 48)"
- §9.7.10.4 (mov pack/unpack): "unpack 32-bit elements from .b128 { d.x, d.y, d.z, d.w } = {
    a[0..31], a[32..63], a[64..95], a[96..127] }"
- §9.7.10.4 (mov pack/unpack): "the sink symbol '_' may be used for one or more elements"
- §9.7.7.3 (selp)
- §9.7.7.4 (slct): "If c >= 0, a is stored in d , otherwise b is stored in d ."
- §9.7.7.4 (slct): "The selected input is copied to the output without modification."
- §9.7.7.4 (slct): "For .f32 comparisons, negative zero equals zero."
- §9.7.7.4 (slct): "If operand c is NaN , the comparison is ordered and operand b is selected."
- §9.7.7.4 (slct): "slct.ftz.dtype.f32 flushes subnormal values of operand c to sign-preserving
    zero, and operand a is selected."
- §5.1.6.1 (kernel parameters): "These parameters are addressable, read-only variables declared in
    the .param state space. Values passed from the host to the kernel are accessed through these
    parameter variables using ld.param instructions."
- §9.7.10.8 (ld): "d = *(&a+immOff) // variable-plus-offset"
- §9.7.10.8 (ld): "A destination register wider than the specified type may be used. The value
    loaded is sign-extended to the destination register width for signed integers, and is
    zero-extended to the destination register width for unsigned and bit-size types."
- §9.7.10.8 (ld): "For ld.param::entry instruction, operand a must be a kernel parameter address,
    otherwise behavior is undefined."
- EXT-ENDIAN (byte order of a multi-byte element)
- EXT-VECTOR-ELEM (element `j` of a vector)

**Applies:** The instructions whose rule is THREAD-MOVE: `mov` and its pack and unpack forms (`MoveInstr.rule`), `selp` and `slct` (`IntInstr.rule`) and `ld.param` (`MemAccess.rule`)

**Premises:** Operands satisfy the relevant type checks.

**Effect:** Local evaluation. `ld.param` of a scalar parameter reads the launch parameter. `ld.param` of a by-value parameter object reads the bytes the host passed (`Launch.paramBytes`): element `j` of an access of `n`-byte elements at byte `offset` is bytes `offset + j n` to `offset + (j + 1) n - 1` (EXT-VECTOR-ELEM), assembled little-endian (EXT-ENDIAN), and is put into register `j`, sign-extended for a `.s` type and zero-extended otherwise when the register is wider (`MemExt.extendBits`); a byte the launch does not supply faults (`badParam`). A `.b128` element is two 64-bit halves, low half first, the value a 16-byte load from memory gives (`paramElem`, THREAD-BYTES). A register address `[r+off]` must hold the parameter-space address of a by-value parameter object (a `.ptr` to it in its state-space representation at offset 0), and the access must lie inside the object and be aligned to its size (`paramObjectOf`); any other value is not a kernel parameter address, which the text makes undefined (`badParam`). A scalar parameter through a register has no rule, since the launch gives its bits and not its width. `mov` copies a value unchanged, so its bit pattern (THREAD-BITS) is unchanged. A scalar `.pred` move writes its source read as a predicate (`readPred`). A scalar `mov.b64` of a declared local symbol writes its numeric state-space address (EXT-LOCAL-CONST-LAYOUT). Packing and unpacking keep the halves, low half first, and four elements are two halves of two halves; a sink `_` destination of an unpack is not written. `slct` copies `a` when `c ≥ 0` and `b` otherwise; an `.f32` `c` is read through its bit pattern, so `-0` selects `a` and a NaN or a negative subnormal selects `b`; with `.ftz` every subnormal `c` is flushed to a zero and selects `a`. Two integer halves of at most 32 bits pack into one integer of twice the width (§9.7.10.4: the halves are concatenated). Packed floats and opaque payloads keep their components; the bit pattern of such a pair is the same concatenation, so later integer instructions read it. Unpacking a payload gives byte slices of it, whose bit patterns are the corresponding bits.

</details>

<a id="thread-cvt"></a>
#### conversions (`THREAD-CVT`)

*Rule* · [Lean comment: `Core/Thread/Local.lean` L2051-L2300](../../Core/Thread/Local.lean#L2051-L2300)

A conversion with a rule gives the result the manual defines: an integer conversion chops, sign-extends or zero-extends by its source type and clamps, `cvt.pack` clamps both sources and packs them, a floating source is read as a floating datum, and a floating conversion rounds the exact number, scaled by its scale factor, into the destination format and then applies `.ftz`, `.sat`, `.relu` and `.pzo`, with `.satfinite` saturating and NaN and infinity handled as the manual states. A result the manual leaves open, among them an overflow to `.f16`, a `-0` under `.sat` or `.relu`, and a NaN whose encoding is unstated in a format without a payload format, has no rule, and so has an infinite input converted from another type to `.f16` or `.bf16` without `.satfinite` or `.sat`: §6.5.1 speaks of numbers beyond the range and names no `.bf16` value (its "~131,000" for `.f16` is no datum of that format), while IEEE 754, with which §9.7.3 makes `cvt` compliant, would keep the infinity; the model declines that reading, which makes the rule stricter than the text.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`execCvt`](../../Core/Thread/Local.lean#L2685-L2774) ([concept](#c-execcvt)), [`cvtIntBits`](../../Core/Thread/Local.lean#L2353-L2357), [`cvtPackBits`](../../Core/Thread/Local.lean#L2359-L2366), [`lowBitsValue`](../../Core/Thread/Local.lean#L2368-L2372), [`lowValue`](../../Core/Thread/Local.lean#L2374-L2378), [`readCvtFloat`](../../Core/Thread/Local.lean#L2380-L2390), [`readCvtFloat_false`](../../Core/Thread/Local.lean#L2392-L2395), [`readCvtFloat_reg`](../../Core/Thread/Local.lean#L2397-L2401), [`cvtFloatDst`](../../Core/Thread/Local.lean#L2403-L2408), [`cvtFloatDst_same`](../../Core/Thread/Local.lean#L2410-L2410), [`CvtRnd.roundInt`](../../Core/Thread/Local.lean#L2412-L2423), [`CvtRnd.mode?`](../../Core/Thread/Local.lean#L2425-L2432), [`cvtIntOf`](../../Core/Thread/Local.lean#L2434-L2442), [`cvtIntOf_fin`](../../Core/Thread/Local.lean#L2444-L2446), [`reluFVal`](../../Core/Thread/Local.lean#L2448-L2456), [`pzoFVal`](../../Core/Thread/Local.lean#L2458-L2461), [`cvtFinish`](../../Core/Thread/Local.lean#L2463-L2471), [`satMaxNorm`](../../Core/Thread/Local.lean#L2473-L2479), [`cvtRound`](../../Core/Thread/Local.lean#L2482-L2500), [`cvtSpecial`](../../Core/Thread/Local.lean#L2502-L2535), [`cvtNum`](../../Core/Thread/Local.lean#L2537-L2543), [`widenElem`](../../Core/Thread/Local.lean#L2545-L2553), [`widenElem_fin`](../../Core/Thread/Local.lean#L2555-L2558), [`roundIntElem`](../../Core/Thread/Local.lean#L2560-L2569), [`cvtElem`](../../Core/Thread/Local.lean#L2571-L2586), [`cvtElem_fmt`](../../Core/Thread/Local.lean#L2588-L2591), [`cvtElem_ue8m0`](../../Core/Thread/Local.lean#L2593-L2601), [`packedElems`](../../Core/Thread/Local.lean#L2603-L2618), [`ue8m0Scale`](../../Core/Thread/Local.lean#L2620-L2625), [`ue8m0Scale_eq`](../../Core/Thread/Local.lean#L2627-L2635), [`cvtScales`](../../Core/Thread/Local.lean#L2637-L2650), [`scaledFlush`](../../Core/Thread/Local.lean#L2652-L2659), [`rsModes`](../../Core/Thread/Local.lean#L2661-L2670), [`cvtPack`](../../Core/Thread/Local.lean#L2672-L2683)

<details>
<summary>Details for reviewers</summary>

- §6.5.1: "the u16 is zero-extended to s32 ."
- §6.5.1: "sext = sign-extend; zext = zero-extend; chop = keep only low bits that fit;"
- §6.5.1: "If the destination register is wider than the destination format, the result is extended
    to the destination register width after chopping."
- §6.5.1: "Conversions to floating-point that are beyond the range of floating-point numbers are
    represented with the maximum floating-point value (IEEE 754 Inf for f32 and f64 , and ~131,000
    for f16 )."
- §9.4.1 (Table 28): "The data are sign-extended to the destination register width for signed
    integer instruction types, and are zero-extended to the destination register width otherwise."
- §9.7.10.24: "For integer destination types, .sat limits the result to MININT..MAXINT for the size
    of the operation."
- §9.7.10.24: "For float-to-integer conversions, the result is clamped to the destination range by
    default; i.e, .sat is redundant."
- §9.7.10.24: ".rni round to nearest integer, choosing even integer if source is equidistant between
    two integers"
- §9.7.10.24: ".rzi round to nearest integer in the direction of zero .rmi round to nearest integer
    in direction of negative infinity .rpi round to nearest integer in direction of positive
    infinity"
- §9.7.10.24: "A floating-point value may be rounded to an integral value using the integer rounding
    modifiers (see Integer Notes)."
- §9.7.10.24: "The result is an integral value, stored in floating-point format."
- §9.7.10.24: "Floating-point rounding is required for float-to-float conversions that result in
    loss of precision, and for integer-to-float conversions."
- §9.7.10.24: ".rn rounding to nearest, with ties to even .rna rounding to nearest, with ties away
    from zero .rz rounding toward zero .rm rounding toward negative infinity .rp rounding toward
    positive infinity"
- §9.7.10.24: "Operation’s result is rounded in the direction toward zero or away from zero based on
    the carry out of the integer addition of the supplied random bits ( rbits ) to the truncated off
    (discarded) bits of mantissa from the input."
- §9.7.10.24: "When converting to .f16x2 , two 16-bit values are provided from rbits where 13 LSBs
    from upper 16-bits are used as random bits for operand a with 3 MSBs are 0 and 13 LSBs from
    lower 16-bits are used as random bits for operand b with 3 MSBs are 0."
- §9.7.10.24: "When converting to .bf16x2 , two 16-bit values are provided from rbits where upper
    16-bits are used as random bits for operand a and lower 16-bits are used as random bits for
    operand b ."
- §9.7.10.24: "Modifier .ftz may be specified to flush single-precision subnormal inputs and results
    to sign-preserving zero."
- §9.7.10.24: "Modifier .ftz can only be specified when either .dtype or .atype is .f32 and applies
    only to single precision ( .f32 ) inputs and results."
- §9.7.10.24: "For cvt.ftz.dtype.f32 float-to-integer conversions and cvt.ftz.f32.f32 float-to-float
    conversions with integer rounding, subnormal inputs are flushed to sign-preserving zero."
- §9.7.10.24: "For floating-point destination types, .sat limits the result to the range [0.0, 1.0].
    NaN results are flushed to positive zero. Applies to .f16 , .f32 , and .f64 types."
- §9.7.10.24: ".relu clamps the result to 0 if negative. NaN results are converted to canonical NaN
    ."
- §9.7.10.24: "if the input value is NaN , then the result is NaN in the specified destination
    format."
- §9.7.10.24: "For .e2m1x2 , .e2m3x2 , .e3m2x2 , .e2m1x4 , .e2m3x4 , .e3m2x4 , .s2f6x2 destination
    formats NaN results are converted to positive MAX_NORM ."
- §9.7.10.24: "If the absolute value of input (ignoring sign) is greater than MAX_NORM of the
    specified destination format, then the result is sign-preserved MAX_NORM of the destination
    format and a positive MAX_NORM in .ue8m0x2 and .ue5m3x2 for which the destination sign is not
    supported."
- §9.7.10.24: "When this qualifier is specified, it enforces the generation of positive zeros only
    in the output. In other words, if the result of the conversion produces -0.0 , it will be forced
    to +0.0 ."
- §9.7.10.24: "In float-to-integer conversions, depending upon conversion types, NaN input results
    in following value: Zero if source is not .f64 and destination is not .s64 , .u64 . Otherwise 1
    << (BitWidth(dst) - 1) corresponding to the value of ( MAXINT >> 1) + 1 for unsigned type or
    MININT for signed type."
- §9.7.10.24: "For cvt.f32.bf16 , NaN input yields unspecified NaN ."
- §9.7.10.24: "The lower n bits corresponding to the instruction-type width are used in the
    conversion."
- §9.7.10.24: "The result of conversion is sign-extended to the destination register width for
    signed integers, and is zero-extended to the destination register width for unsigned, bit-size,
    and floating-point types."
- §9.7.10.24: "two inputs a and b of .f32 type are converted into .f16 or .bf16 type and the
    converted values are packed in the destination register d , such that the value converted from
    input a is stored in the upper half of d and the value converted from input b is stored in the
    lower half of d"
- §9.7.10.24: "d[31:16] = convert(a); d[15:0] = convert(b);"
- §9.7.10.24: "d[15:8] = convert(a / scale-factor[7:0]); // scale-factor if present d[7:0] =
    convert(b / scale-factor[7:0]); // scale-factor if present } else { d[15:8] = convert(a[31:16] /
    scale-factor[7:0]); // scale-factor if present d[7:0] = convert(a[15:0] / scale-factor[7:0]);"
- §9.7.10.24: "d[15:8] = convert(a / scale-factor[15:8]); d[7:0] = convert(b /
    scale-factor[7:0]);"
- §9.7.10.24: "d[7:4] = convert(a / scale-factor[7:0]); // scale-factor if present d[3:0] =
    convert(b / scale-factor[7:0]);"
- §9.7.10.24: "d[15:14] = 0; d[13:8] = convert(a / scale-factor[7:0]); // scale-factor if present
    d[7:6] = 0; d[5:0] = convert(b / scale-factor[7:0]);"
- §9.7.10.24: "d[31:16] = convert(a[15:8]) * scale-factor[15:8]; // scale-factor if present for
    .bf16x2 dest type d[15:0] = convert(a[7:0]) * scale-factor[7:0];"
- §9.7.10.24: "Each 8-bit input value in operand a is converted to .f16 / .bf16 type."
- §9.7.10.24: "the value converted from the upper 8 bits of a is stored in the upper 16 bits of d
    and the value converted from the lower 8 bits of a is stored in the lower 16 bits of d"
- §9.7.10.24: "When converting from .e2m1x2 to .f16x2 / .bf16x2 , source operand a has .b8 type.
    Each 4-bit input value in operand a is converted to .f16 / .bf16 type."
- §9.7.10.24: "the value converted from the upper 4 bits of a is stored in the upper 16 bits of d
    and the value converted from the lower 4 bits of a is stored in the lower 16 bits of d"
- §9.7.10.24: "When converting from .e2m3x2 / .e3m2x2 to .f16x2 / .bf16x2 , source operand a has
    .b16 type. Each 8-bit input value with 2 MSB bits 0 in operand a is converted to .f16 / .bf16
    type."
- §9.7.10.24: "When converting from .s2f6x2 to .bf16x2 , source operand a has .b16 type."
- §9.7.10.24: "Operand scale-factor stores two packed scaling factors of type .ue8m0 ."
- §9.7.10.24: "For down conversion, inputs are divided by scale-factor and then conversion is
    performed."
- §9.7.10.24: "Inputs are converted to destination type and then multiplied by scale-factor ."
- §9.7.10.24: "If not specified explicitly, value of scale-factor will be assumed to be 0x7f7f ,
    that is, assumed as value 1 for both input scale factors."
- §9.7.10.24: "has type .b8 when used with qualifier .scaled::n1::ue8m0 qualifier. Default value of
    scale-factor is 0x7f in this case if not specified explicitly."
- §9.7.10.24: "When qualifier .scaled::n1::ue8m0 is specified, subnormal values for inputs a and b
    are flushed to zero before conversion."
- §9.7.10.25: "The inputs a and b are converted to values of type specified by .convertType with
    saturation and the results after conversion are packed into lower bits of d ."
- §9.7.10.25: "If operand c is specified then remaining bits of d are copied from lower bits of c ."
- §9.7.10.25: "td = tb ; for (i = size; i <= 2 * size - 1; i++) { td[i] = ta[i - size]; }"
- §9.7.10.25: ".sat modifier limits the converted values to MIN(convertType) .. MAX(convertedType)
    (no overflow) if the corresponding inputs are not in the range of datatype specified as
    .convertType ."
- §5.2.4: "s2f6 value = s8 value * 2^(-6)"
- §9.7.3: "Instructions that support rounding modifiers are IEEE-754 compliant."
- THREAD-FLOAT-ROUND
- EXT-UE8M0
- EXT-NARROW-FLOAT

**Applies:** The conversions whose rule is THREAD-CVT (`CvtInstr.rule`, PROG-ISA-CVT)

**Premises:** The operands satisfy the register rules (THREAD-REG) and their values have bit patterns of their formats' widths or are opaque NaN values of their formats (THREAD-NUM); the destination register has the width the decoding recorded.

**Effect:** Local evaluation; a result the manual leaves open is `noRule`. An integer conversion reads the low bits of its source as a value of the source type, clamps it to the destination type under `.sat`, and keeps the low bits of the destination width (`cvtIntBits`), which is chopping, sign extension of a signed source and zero extension of an unsigned one (Table 15). The result fills a wider destination register by the extension the decoding recorded (`MemExt.extendBits`, Table 28). An unsigned conversion of a symbolic pointer (THREAD-VALUE) at its own width keeps the pointer, since the source and destination types are the same. An unsigned conversion of a state-space pointer from 32 to 64 bits keeps it too, since zero extension keeps the address, and so does one of a `.shared::cluster` pointer from 64 to 32 bits, whose address lies below `2 ^ 32` (THREAD-SHARED-POINTER). Any other conversion of a symbolic pointer has no rule. `cvt.pack` clamps `a` and `b` to the convert type and puts `b` in the low and `a` in the next `size` bits, with the low bits of `c` above them (`cvtPackBits`). The Semantics pseudocode clamps `a` from below and then overwrites that value with the clamp from above, which drops the lower clamp; the model follows the Description and the `.sat` text, which clamp both ways. A floating source is read by `classify` (THREAD-NUM) as a floating datum: a zero with its sign, a finite number, an infinity or NaN (`readCvtFloat`). A source of `cvt d, a` in a register wider than its format is read through its low bits (`lowValue`): the low half of a pair whose low half has the format's width, and otherwise the low bits of the register's bit pattern. A `.bf16` source is read at its exact width. A floating result is written by `FVal.toValue`: a payload for a number and for `+0`, the bit pattern of `-0` and of an infinity, and the opaque NaN of the format for a NaN result, whose encoding the manual leaves unspecified. In a wider destination register the result is in the low part with zero bits above it (`cvtFloatDst`), which is the zero extension of its bit pattern. A floating-to-integer conversion rounds the number by `.rni` (ties to even), `.rzi`, `.rmi` or `.rpi` (`CvtRnd.roundInt`) and clamps it to the destination range; an infinity clamps to the end of its sign; NaN gives `1 << (w - 1)` for an `.f64` source or a 64-bit destination and zero otherwise (`cvtIntOf`). `.ftz` first flushes an `.f32` subnormal to zero. A rounding to an integral value at the same format rounds the number by the integer rounding modifier; a zero produced by rounding a negative number is `-0`, as IEEE 754 roundToIntegral gives, and an infinity and a zero are unchanged (`roundIntElem`). A widening (`.f16`, `.bf16` to `.f32`; `.f16`, `.bf16`, `.f32` to `.f64`; the same format without a rounding modifier) keeps the datum (`widenElem`), except that its special values follow the rule of a rounded conversion below (`cvtSpecial`). NaN gives the opaque NaN in both. A conversion with a floating rounding modifier (`.rn`, `.rz`, `.rm`, `.rp`, `.rs`) multiplies the number by its scale factor, when there is one, and rounds the exact product into the layout of the destination type (`cvtNum`, `cvtRound`, THREAD-FLOAT-ROUND): the narrowings between `.f64`, `.f32`, `.f16` and `.bf16`, the integer-to-floating conversions, and the conversions of two `.f32` sources or of the elements of an `.f16x2` or `.bf16x2` source to a packed type. Under `.satfinite` a number above MAX_NORM in magnitude gives the MAX_NORM of its sign (positive for `.ue8m0` and `.ue5m3`), and so does an infinity (`satMaxNorm`); for `.s2f6` a negative input above MAX_NORM in magnitude has no rule, since its sign-preserved MAX_NORM can be read as `-1.984375` or as `-2.0`. Without `.satfinite` an overflow follows IEEE 754, which agrees with §6.5.1 for `.f32` and `.f64`. For `.f16` §6.5.1 gives "~131,000", which is no `.f16` value, and for `.bf16` it names no value, so without `.satfinite` and `.sat` an `.f16` result of a number above MAX_NORM in magnitude has no rule, and so has a `.bf16` result that IEEE 754 makes an infinity; a finite `.bf16` result of MAX_NORM is the IEEE 754 result and is kept. Under `.sat` the clamp decides an overflowing result. An infinite input converted from another type to `.f16` or `.bf16` without `.satfinite` and `.sat` has no rule: §6.5.1 speaks of numbers beyond the range and names no `.bf16` value (its "~131,000" for `.f16` is no datum of that format), while IEEE 754, with which §9.7.3 makes `cvt` compliant, would keep the infinity; the model declines that reading, which makes the rule stricter than the text. An identity conversion (`cvt.f16.f16`, `cvt.bf16.bf16`) without `.satfinite` and `.sat`, whose source type or source element type is the destination type, is no conversion into a smaller range and keeps the infinity. For another destination an infinite input is the infinity of the destination when it has one, and has no rule otherwise. A zero keeps its sign; the one zero of `.s2f6` is `+0`. The unsigned `.ue8m0` and `.ue5m3` have no rule for a zero, a negative number in range, or a result below their smallest value, which for `.ue8m0` is the pattern `0` without a value (EXT-UE8M0). NaN under `.sat` gives `+0`; under `.satfinite` it gives the positive MAX_NORM for `.e2m1`, `.e2m3`, `.e3m2` and `.s2f6` and the NaN pattern `0xff` for `.ue8m0` and `.ue5m3`, which have no rule for NaN without `.satfinite`; every other NaN result, the canonical NaN of `.relu` included, is the opaque NaN of the destination. After rounding (`cvtFinish`), `.ftz` flushes a subnormal `.f32` result to the zero of its sign; an exact number below the smallest normal magnitude that rounds up to it has no rule, since the manual does not say whether a result is flushed before or after rounding. Then `.sat` clamps to `[0.0, 1.0]`, or `.relu` clamps a negative result to `+0`, reading its "0" as `+0`; whether they keep the sign of a `-0` the manual does not say, so a `-0` there has no rule, unless `.pzo` makes the result `+0` under both readings. Last, `.pzo` turns `-0` into `+0`. `.rs` takes its random bits from `rbits`, the upper half for `a` and the lower half for `b`: for `.f16x2` the 13 low bits of the half, and a half whose three high bits are not zero has no rule; for `.bf16x2` the whole half (`rsModes`). Its result is determined for normal results only (THREAD-FLOAT-ROUND), and an overflow without `.satfinite` has no rule. A scale factor is a `.ue8m0` number (EXT-UE8M0, `ue8m0Scale`); the patterns `0` and `0xff` have no rule. `.scaled::n1::ue8m0` gives one byte that divides both inputs, and `.scaled::n2::ue8m0` two, the upper byte for `a` or the upper element and the lower byte for `b` or the lower element; it divides the inputs of `.s2f6x2` and multiplies the elements of a widening to `.bf16x2`, whose product is then rounded once. Without the operand the factor is 1 (`cvtScales`). Which of the two a conversion has follows from its types, as the syntax gives one of them to each. With `.scaled::n1::ue8m0` a subnormal input is flushed to zero first; the manual does not give the sign of that zero, so a negative subnormal input has no rule unless `.pzo` makes the result `+0` under both readings (`scaledFlush`). The results are packed as the Semantics gives: from two `.f32` sources, `a`'s result is the upper element and `b`'s the lower; from a packed source, the result of the upper element is the upper element. An element of `.f16`, `.bf16`, `.e4m3` or `.e5m2` is written by `FVal.toValue` and the result is the pair of the two, low element first; the other formats have no payload format, and the result is the `.b8` (`.e2m1x2`) or `.b16` value of the two patterns (`Layout.encode`), each 6-bit pattern with two zero bits above it (`cvtPack`). A result without a pattern (an opaque NaN of such a format) has no rule. The elements of a packed source are its two halves (`packedElems`). An `.e2m1x2` source is a `.b8` value whose low and high four bits are its elements; the 8-bit packed sources are `.b16` values of two bytes, and `.f16x2` and `.bf16x2` are 32-bit values of two halves. The elements of the payload formats are read by `classify`, and the others through the layouts of THREAD-FLOAT-FORMAT (`cvtElem`): `.ue8m0` by EXT-UE8M0, `.e2m1`, `.e2m3`, `.e3m2` and `.ue5m3` by EXT-NARROW-FLOAT, and `.s2f6` as the `.s8` value of the byte times `2^-6`. An `.e2m3` or `.e3m2` byte whose two most significant bits are not zero is an input the text does not convert, and has no rule. An element of `.e2m1`, `.e2m3`, `.e3m2`, `.ue5m3` or `.s2f6` is a number of at most seven significant bits, all at or above `2^-17`, so `.f16` and `.bf16` represent it exactly when it is at most MAX_NORM of the destination. A `.ue5m3` element with the exponent field 31 is at least `2^16`; its conversion to `.f16` overflows, where §6.5.1 gives no `.f16` value, and has no rule (`widenElem`). An unscaled widening of a number never exceeds MAX_NORM of a `.bf16` destination, so `.satfinite` does not change its numbers. An infinite `.e5m2` element is an infinite input as above: under `.satfinite` it gives the MAX_NORM of its sign, and without it it has no rule for both destinations. A NaN element gives the opaque NaN. The model has no rule for `.tf32` destinations, whose layout is implementation defined, for `.s2f6x2` from `.bf16x2`, whose Description and Semantics select different bits of `a`, and for `.rs` to the four-element formats (PROG-ISA-CVT).

</details>

<a id="ext-ue8m0"></a>
##### values of the ue8m0 format (`EXT-UE8M0`)

*Interpretation (EXT)* · [Lean comment: `Core/Thread/Local.lean` L2302-L2319](../../Core/Thread/Local.lean#L2302-L2319)

A `.ue8m0` pattern `e` between 1 and 254 denotes `2^(e-127)`, the pattern `0xff` is NaN, and the pattern `0` has no rule.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The manual describes `.ue8m0` as "This data format is an 8-bit unsigned floating-point format with 8 bits for exponent and 0 bits for mantissa." and "The ue8m0 encoding does not support infinity. NaN value is limited to 0xff .", and it gives one value: "If not specified explicitly, value of scale-factor will be assumed to be 0x7f7f , that is, assumed as value 1 for both input scale factors." (§5.2.3, §9.7.10.24). It does not state the bias of the exponent or the value of the pattern `0`. The model reads a pattern as a power of two with the exponent bias that makes `0x7f` the value 1, and leaves the pattern `0` without a rule, since an IEEE-style format would make it a zero and the bias reading would make it `2^-127`.

**Effect:** A conversion of `.ue8m0x2` elements (`cvt.rn.bf16x2.ue8m0x2`), a conversion to `.ue8m0x2` and the scale factors of `.scaled::n1::ue8m0` and `.scaled::n2::ue8m0` use these values; if the hardware uses another bias, the proven values differ from the hardware's. Disclosed by every kernel whose statement names `FType.ue8m0`: FlashMlaSparseDecodeH64.

</details>

<a id="ext-narrow-float"></a>
##### values of the e2m1, e2m3, e3m2 and ue5m3 formats (`EXT-NARROW-FLOAT`)

*Interpretation (EXT)* · [Lean comment: `Core/Thread/Local.lean` L2321-L2350](../../Core/Thread/Local.lean#L2321-L2350)

A pattern of `.e2m1`, `.e2m3`, `.e3m2` or `.ue5m3` denotes the number of the IEEE 754 layout with the format's exponent and mantissa widths: exponent bias `2^(e-1) - 1`, a subnormal number when the exponent field is zero, a normal number for every other exponent field, and the sign bit above the fields for the three signed formats. The `.ue5m3` pattern `0xff` is NaN.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The manual gives the widths and the special values of these formats: "e2m1 data format: This data format is a 4-bit floating point format with 2 bits for exponent and 1 bit for mantissa. The e2m1 encoding does not support infinity and NaN ."; "e2m3 data format: This data format is a 6-bit floating point format with 2 bits for exponent and 3 bits for mantissa. The e2m3 encoding does not support infinity and NaN ."; "e3m2 data format: This data format is a 6-bit floating point format with 3 bits for exponent and 2 bits for mantissa. The e3m2 encoding does not support infinity and NaN ."; "ue5m3 data format: This data format is a 8-bit unsigned floating-point format with 5 bits for exponent and 3 bits for mantissa. The ue5m3 encoding does not support infinity. NaN value is limited to 0xff ." (§5.2.3). It does not state the exponent bias, how a zero exponent field is read, or where the sign bit is. The model reads them as the IEEE 754 binary formats do (§9.7.3: "Instructions that support rounding modifiers are IEEE-754 compliant."), as THREAD-BITS reads `.e4m3` and `.e5m2`: bias `2^(e-1) - 1`, subnormal numbers at the zero exponent field, the sign bit as the most significant bit of the element, and, since there is no infinity, a finite number at the largest exponent field except the `.ue5m3` NaN. A pattern with the sign bit set and a zero magnitude is `-0`. With this reading the largest `.e2m1` value is 6, the largest `.e2m3` value 7.5, the largest `.e3m2` value 28 and the largest finite `.ue5m3` value 114688.

**Effect:** The conversions from and to these formats (`cvt.rn.f16x2.e2m1x2`, `cvt.rn.bf16x2.e3m2x2`, `cvt.rn.f16x2.ue5m3x2`, `cvt.rn.satfinite.e2m1x2.f32` and the others of THREAD-CVT) use these values; if the hardware uses another bias or another subnormal reading, the proven values differ from the hardware's. Disclosed by every kernel whose statement names `FType.e2m1`, `FType.e2m3`, `FType.e3m2` or `FType.ue5m3`: none.

</details>

### Addresses and pointers

The generic address windows and `cvta`, pointers to kernel parameters, tensor maps and shared memory, and pointer offsets.

<a id="thread-cvta"></a>
#### generic address windows: cvta and isspacep (`THREAD-CVTA`)

*Rule* · [Lean comment: `Core/Thread/Local.lean` L1417-L1496](../../Core/Thread/Local.lean#L1417-L1496)

`cvta` converts a const, parameter, global, local or shared address to a generic address and back, and `isspacep` says whether a generic address lies in the window of a state space. A generic address in the shared, parameter, local or constant window is a symbolic pointer that remembers the memory it maps to, and a global address is its own generic address. Converting a generic address that lies outside the window of the target space is a fault.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`inWindow`](../../Core/Thread/Local.lean#L1525-L1554), [`execCvta`](../../Core/Thread/Local.lean#L1556-L1599) ([concept](#c-execcvta)), [`execCvta_global`](../../Core/Thread/Local.lean#L1601-L1606), [`execCvta_param`](../../Core/Thread/Local.lean#L1608-L1616), [`execCvta_shared`](../../Core/Thread/Local.lean#L1618-L1628)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.23 (cvta): "Convert a const , Kernel Function Parameters ( .param ), global , local , or
    shared address to a generic address, or vice-versa."
- §9.7.10.23 (cvta): "When converting a generic address into a const , Kernel Function Parameters (
    .param ), global , local , or shared address, the resulting address is undefined in cases where
    the generic address does not fall within the address window of the specified state space."
- §6.4.1.1: "A generic address maps to global memory unless it falls within the window for const ,
    local , or shared memory."
- §6.4.1.1: "Within each window, a generic address maps to an address in the underlying state space
    by subtracting the window base from the generic address."
- §5.1.5: "The local state space ( .local ) is private memory for each thread to keep its own data."
- §5.1.6.1 (addressable kernel parameters)
- §9.7.10.22 (isspacep): "Write predicate register p with 1 if generic address a falls within the
    specified state space window and with 0 otherwise."
- §9.7.10.22 (isspacep): "isspacep.global returns 1 for Kernel Function Parameters as .param window
    is contained within the .global window."
- §9.7.10.22 (isspacep): "ispacep.shared::cluster will return 1 for every shared memory address that
    is accessible to the threads in the cluster, whereas ispacep.shared::cta will return 1 only if
    the address is of a variable declared in the executing CTA."
- EXT-CVTA (the global window)

**Applies:** `cvta{.to}.global.u64`, `cvta{.to}` of the parameter, shared, local and constant spaces of 32 or 64 bits, and `isspacep` (`AddrInstr.rule`); through THREAD-ADDR the generic accesses at the pointers these give, and through THREAD-POINTER-OFFSET their offsets

**Premises:** The source of a conversion to a generic address is an address of the state space: a number for the global, local and constant spaces, a parameter pointer of the instruction width for the parameter space, and a shared address that THREAD-SHARED-POINTER accepts for the shared spaces. The source of a conversion from a generic address is a generic pointer of the instruction width into the window of the target space, for local memory one of the thread itself, or a number for the global space. The operand of `isspacep` is a register.

**Effect:** Local register update. A generic pointer is a `.ptr` value with `generic = true`, and a state-space pointer one with `generic = false` (THREAD-VALUE). The window bases are not modeled: subtracting a base gives back the state-space address (§6.4.1.1), so a conversion changes only the representation and keeps the memory and the offset that the pointer names. Global space: `cvta.global` and `cvta.to.global` are the identity on 64-bit numbers (EXT-CVTA). Parameter space: `cvta.param` turns the parameter-space pointer of a kernel parameter object into its generic pointer, and `cvta.to.param` turns the generic pointer back. The conversion keeps the identity of the parameter object and loads none of its contents; any other source is a fault (`badValue`). Shared spaces: `cvta.shared{::cta}` and `cvta.shared::cluster` read their source by THREAD-SHARED-POINTER and give a generic shared pointer of the thread's CTA to the same location. `cvta.to.shared::cluster` gives the `.shared::cluster` pointer of the location, and `cvta.to.shared{::cta}` the number of its `.shared::cta` address, which must lie in the thread's CTA. The generic and state-space representations stay distinct. Local and constant spaces: `cvta.local` of the local address `x` of thread `g` is the generic pointer to byte `x` of the local memory of `g`, and `cvta.const` of the constant address `x` is the generic pointer to byte `x` of the constant memory. `cvta.to.local` of a generic local pointer of the thread itself is its offset, and `cvta.to.const` of a generic constant pointer is its offset. The text makes the result undefined for a generic address outside the window, so every other source value is a fault (`badValue`); a generic number is a global address (EXT-CVTA), so it is outside both windows. A generic local pointer of another thread has no rule: local memory is private to each thread and the text does not say which bytes another thread reaches through that address. `isspacep` (`inWindow`) answers for a generic shared pointer of the thread's CTA (in the `.shared::cluster` window; in the `.shared::cta` window when it targets the thread's CTA; outside the global and parameter windows, since a shared window address does not map to global memory and the parameter window lies in the global window) and for a generic parameter pointer (in the parameter and global windows, outside the shared, local and constant ones). It also answers for a generic local pointer of the thread (in the local window) and a generic constant pointer (in the constant window). The const, local and shared windows do not overlap: §6.4.1.1 maps a generic address to global memory unless it falls within one of them and maps an address within a window to an address of that window's state space, so a generic address that names a location of one of these spaces lies in no other of the three windows. A generic shared, local or constant pointer is therefore outside the other two of these windows, and `isspacep` answers 0 for them (§9.7.10.22: "with 0 otherwise"). A generic number may lie in any window, and a generic local pointer of another thread names local memory that the querying thread cannot address, so those queries have no rule (stricter).

</details>

<a id="ext-cvta"></a>
##### generic and global addresses (`EXT-CVTA`)

*Interpretation (EXT)* · [Lean comment: `Core/Thread/Local.lean` L1498-L1522](../../Core/Thread/Local.lean#L1498-L1522)

The model takes the generic address of a global allocation to be its global address. Then `cvta.to.global` is the identity, and a generic pointer that the host passes can be used directly as a global address. The PTX ISA says that such a generic address maps to global memory and does not say that its value equals the global address. The generic address of a global allocation is its global address: `cvta.to.global` is the identity on it, and a kernel may use a generic pointer that the host passes (a device pointer) directly as a global address, in `ld.global`/`st.global` and as the global base of a tensor map. The generic address lies outside the const, local and shared windows (the model checks neither). A 64-bit number used as a generic load or store address is therefore a global address (THREAD-ADDR); a number in one of the windows names no allocated global byte of `mem0`, so the access is an access to unallocated memory in the model.

<details>
<summary>Details for reviewers</summary>

**Evidence:** PTX ISA §6.4.1.1 ("A generic address maps to global memory unless it falls within the window for const , local , or shared memory"; within a window the window base is subtracted); §9.7.10.23 (cvta) defines the instruction. Whether an address of a kernel's global allocation avoids the windows is a property of the launch, not checked.

**Effect:** §6.4.1.1 states that such a generic address maps to global memory, not that its value equals the global address; if the values differ, every global access through a host pointer reaches another location than the model's. Disclosed by every kernel whose statement names `AddrInstr.cvta`, `Space.global`, `Op.mem`, `Op.cpTensor`, `Op.cpTensorStore` or `Op.prefetchTensor`: AddOne, BlockSum, CopyDynamic, CopyLdg, FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, RowSum, TcGemm, TmaCopy.

</details>

<a id="thread-tensor-map-address"></a>
#### descriptor addresses from kernel parameters (`THREAD-TENSOR-MAP-ADDRESS`)

*Rule* · [Lean comment: `Core/Thread/Local.lean` L386-L416](../../Core/Thread/Local.lean#L386-L416)

The tensor map operand of a tensor instruction is either a numeric address or the symbolic generic address of a by-value parameter object that holds a full 128-byte descriptor. The address must be 64-byte aligned and name a descriptor that the host published, that is valid and that has the instruction's rank. In four-row mode the map must be 2D with box dimension 1 equal to 1. Otherwise the instruction faults.

Source:

- 

Direction: `scope` (the supported fragment or launch scope is restricted)

Lean definitions: [`tensorMapAddress`](../../Core/Thread/Local.lean#L418-L428) ([concept](#c-tensormapaddress)), [`TensorMode.transfer`](../../Core/Thread/Local.lean#L430-L434), [`TensorMode.rowCoordinates`](../../Core/Thread/Local.lean#L436-L439), [`tensorMap`](../../Core/Thread/Local.lean#L441-L452)

<details>
<summary>Details for reviewers</summary>

- §5.1.6.1
- §9.7.10.23
- §9.7.10.28.5.3
- CUDA Driver API CUtensorMap (128-byte object)
- EXT-TMA-GEOMETRY (64-byte alignment)

**Applies:** Numeric generic descriptor addresses and symbolic generic base addresses of by-value parameter objects; the tensor map operand of every tensor load, store, reduction and prefetch

**Premises:** A symbolic address has 64-bit generic representation and offset 0; its actual launch binding has the matching name, contains the full 128-byte descriptor, respects the declaration alignment and fits the address width.

**Effect:** Address resolution using immutable launch metadata. Parameter offsets and device-side descriptor mutation are outside this rule. The resolved address is the object's generic base, which stays distinct from the object's contents. `tensorMap` applies the map checks for tensor loads, stores and prefetches, and `TensorMode.transfer` and `TensorMode.rowCoordinates` give the transfer descriptor and the row coordinates of a mode.

</details>

<a id="thread-tensormap-prefetch"></a>
#### tensormap prefetches (`THREAD-TENSORMAP-PREFETCH`)

*Rule* · [Lean comment: `Core/Thread/Local.lean` L454-L474](../../Core/Thread/Local.lean#L454-L474)

`prefetch.tensormap` takes a symbolic pointer to an allocated, aligned parameter object. It changes no register, reads no program value, writes no memory and publishes no descriptor, and it only advances the source position.

Source:

- 

Direction: `scope` (the supported fragment or launch scope is restricted)

Lean definitions: [`execTensorMapPrefetch`](../../Core/Thread/Local.lean#L476-L485)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.16 (prefetch.tensormap, generic addressing when unqualified)

**Applies:** prefetch.tensormap of generic or explicit .param base addresses of immutable kernel parameter objects

**Premises:** The source is a symbolic parameter pointer with matching width/space and offset 0; its launch binding names an allocated, nonempty, aligned parameter object in range.

**Effect:** Local evaluation under the model's abstraction of caches. Constant-space addresses and device-updated descriptor caches need separate representation/rules. A tensor-data prefetch is an event (THREAD-TENSOR-PREFETCH).

</details>

<a id="thread-pointer-offset"></a>
#### arithmetic on symbolic addresses (`THREAD-POINTER-OFFSET`)

*Rule* · [Lean comment: `Core/Thread/Local.lean` L487-L514](../../Core/Thread/Local.lean#L487-L514)

Adding or subtracting an integer from a symbolic shared pointer, or from a generic local or constant pointer, changes its byte offset and keeps its representation, its target and the thread or CTA it belongs to. The new offset must stay within `[0, 2 ^ 32)` without wrapping, otherwise the instruction has no rule.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`offsetPointer`](../../Core/Thread/Local.lean#L517-L528), [`offsetPointer_shared`](../../Core/Thread/Local.lean#L530-L539)

<details>
<summary>Details for reviewers</summary>

- §6.4.1.1 (generic address windows)
- §9.7.1.1 (add)
- §9.7.1.2 (sub)

**Applies:** Addition/subtraction of an integer displacement to a symbolic shared pointer or to a generic local or constant pointer (THREAD-CVTA)

**Premises:** The instruction width matches the pointer, and the resulting logical offset is representable without wrapping. A consumed pointer must still refer to allocated shared memory of its recorded target CTA.

**Effect:** Local pointer arithmetic. Arbitrary bit inspection, pointer-pair arithmetic and out-of-window targets are not modeled as new addresses in another CTA. The base of a generic window cancels in the offset calculation. A generic local or constant pointer moves inside its window in the same way as a shared pointer; an offset at or above `2 ^ 32` has no rule. A shared pointer whose offset is at or above `2 ^ 32` before the move has no rule either, and a parameter pointer has no offset arithmetic.

</details>

<a id="thread-shared-pointer"></a>
#### shared addresses and peer mapping (`THREAD-SHARED-POINTER`)

*Rule* · [Lean comment: `Core/Thread/Local.lean` L1319-L1378](../../Core/Thread/Local.lean#L1319-L1378)

A `.shared::cta` address is a number that names a byte of the executing CTA. A generic or `.shared::cluster` address is a symbolic pointer that records its target CTA, its offset and the CTA of the thread that produced it, and only a thread of that CTA can use it. `mapa` changes only the target CTA to a CTA of the same cluster, and `getctarank` gives the cluster rank of the CTA an address names.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`readSharedAddress`](../../Core/Thread/Local.lean#L1381-L1400) ([concept](#c-readsharedaddress)), [`execSharedAddress`](../../Core/Thread/Local.lean#L1402-L1415) ([concept](#c-execsharedaddress))

<details>
<summary>Details for reviewers</summary>

- §5.1.7: "Additional sub-qualifiers ::cta or ::cluster can be specified on instructions with
    .shared state space to indicate whether the address belongs to the shared memory window of the
    executing CTA or of any CTA in the cluster respectively. The addresses in the .shared::cta
    window also fall within the .shared::cluster window."
- §5.1.7: "Variables declared in .shared state space refer to the memory addresses in the current
    CTA."
- §6.4.2: "Arrays of all types can be declared, and the identifier becomes an address constant in
    the space where the array is declared."
- §9.7.10.26 (mapa): "Destination register d will hold an address in CTA b corresponding to operand
    a"
- §9.7.10.27 (getctarank): "Write the destination register d with the rank of the CTA which contains
    the address specified in operand a ."
- §2.2.2 (cluster)
- §9.7.15.16.12
- §9.7.15.16.13
- §9.7.15.16.16
- §9.7.15.16.19
- §9.7.18.7.1: "If the address specified by addr does not fall within the address window of
    .shared::cta state space then the behavior is undefined."
- §9.7.18.7.1 (for `tcgen05.alloc` the same sentence with `dst`)

**Applies:** Shared addresses produced from local offsets, by THREAD-CVTA and by mapa, and read by cvta, mapa, getctarank and the shared-memory instructions; 32-bit or 64-bit address registers

**Premises:** Pointer representation matches the instruction; a symbolic pointer is read only by a thread of the CTA that produced it; a `.shared::cta` operand is not a `.shared::cluster` address, a generic operand converted to `.shared::cta` targets its own CTA, a cluster-qualified one uses a peer in the same cluster, and mapa's target rank is valid.

**Effect:** Register values keep their target and producer through moves, memory round trips and address conversion. Arbitrary bit inspection and manually encoded peer pointers are outside this representation. `getctarank` reads its operand as a `.shared::cluster` address (a cluster pointer or a number of the thread's own window) or, without `.shared::cluster`, as a generic shared pointer, and writes the rank of its target CTA. A `.shared::cta` window address means the same in every CTA: the executing CTA's byte (§5.1.7, §6.4.2: one address constant names each CTA's own copy of a shared variable), which is how a raw integer is read. The text does not say what a generic shared address or a `.shared::cluster` address (e.g. a mapa result) denotes when used by a thread of a CTA other than the one that produced it, so such a use has no rule (`noRule`); a value's meaning thus never depends on whether it is tagged as a pointer. The text gives the inclusion of the `.shared::cta` window in the `.shared::cluster` window only (§5.1.7), not the converse: a `.shared::cluster` address (a result of `mapa.shared::cluster` or `cvta.to.shared::cluster`) at a `.shared{::cta}` operand faults (`noRule`) even when it names the executing CTA. For `mbarrier.init`, `mbarrier.inval`, `mbarrier.arrive`, `mbarrier.test_wait`/`try_wait` and `tcgen05.alloc` the quoted sentence makes such a use undefined; for the other `.shared{::cta}` instructions the text gives it no meaning. Peer addresses are represented symbolically, not with an invented encoding of CTA-rank bits. This layer does not assert peer lifetime or allocation: actual accesses require separate checks.

</details>

### Loads and stores

The address, footprint and value of loads and stores.

<a id="thread-addr"></a>
#### effective addresses (`THREAD-ADDR`)

*Rule* · [Lean comment: `Core/Thread/Access.lean` L20-L79](../../Core/Thread/Access.lean#L20-L79)

The effective address of a load or store is its base plus the offset. A global address lies in CTA 0, a shared window address in the issuing thread's CTA or, through a symbolic pointer, in a CTA of its cluster, a local address in the issuing thread's own local memory and a constant address in the constant memory. A generic address is a symbolic shared pointer, resolved in the shared window, a generic local pointer of the issuing thread or a generic constant pointer, resolved in their windows, or a number, which is a global address. An invalid base register, a generic number of 32 bits, a generic parameter pointer, a generic local pointer of another thread and a generic address that leaves its window have no rule, and a store at a generic constant pointer is a fault.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`sharedEffAddr`](../../Core/Thread/Access.lean#L107-L118), [`effAddr`](../../Core/Thread/Access.lean#L120-L128) ([concept](#c-effaddr)), [`wrapAddr`](../../Core/Thread/Access.lean#L130-L132), [`absLoc`](../../Core/Thread/Access.lean#L134-L136), [`accessLoc`](../../Core/Thread/Access.lean#L138-L191)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.8 (ld): "If no state space is given, perform the load using Generic Addressing ."
- §9.7.10.11 (st)
- §6.4.1.1: "A generic address maps to global memory unless it falls within the window for const ,
    local , or shared memory."
- §6.4.1.1: "Within each window, a generic address maps to an address in the underlying state space
    by subtracting the window base from the generic address."
- §5.1.4 (global)
- §5.1.5: "The local state space ( .local ) is private memory for each thread to keep its own data."
- §5.1.3: "The constant ( .const ) state space is a read-only memory initialized by the host."
- §9.7.10.11: "Stores to const memory are illegal."
- §5.1.7 (shared): "Variables declared in .shared state space refer to the memory addresses in the
    current CTA."
- choice: shared layout
- EXT-ADDR-WRAP
- EXT-CVTA
- EXT-LAUNCH (local memories and constant memory at launch)
- EXT-LOCAL-CONST-LAYOUT

**Applies:** Global, shared, local, constant and generic effective addresses of loads and stores

**Premises:** The base register supplies an address of the space: a 64-bit global number, a shared number below `2 ^ 32` or a symbolic shared pointer, a local or constant number of the register's width, or a generic symbolic shared pointer, generic local or constant pointer or 64-bit number.

**Effect:** Local address evaluation. THREAD-SHARED-POINTER resolves a symbolic shared pointer, which only a thread of its producing CTA can use. A global address is a 64-bit register plus offset. A `.shared` address is a 32-bit address in the issuing thread's CTA; `.shared` variables live at `sharedBase + offset` (the decoder's layout, EXT-SHARED); `.local` and `.const` variables live at `localBase + offset` and `constBase + offset` (EXT-LOCAL-CONST-LAYOUT). `accessLoc` locates every access that `memTmpl` does not locate directly (`MemAccess.locSpace?`): a `.shared::cluster` address is a cluster pointer (THREAD-SHARED-POINTER) or a number of the thread's own `.shared::cta` window, which the `.shared::cluster` window contains (§5.1.7). A `.local` address is location `⟨.local, g, x⟩` of thread `g`: each thread has its own local memory, and no other thread can name it (EXT-LAUNCH). A `.const` address is location `⟨.const, 0, x⟩`; no instruction with a rule writes the constant space (§9.7.10.11: "Stores to const memory are illegal."), so a constant read returns the launch memory. A generic symbolic shared pointer resolves in the shared window of its target CTA and must stay in `[0, 2 ^ 32)` after the offset. A generic local pointer (THREAD-CVTA) resolves in the local memory of the issuing thread when that thread owns it, and a generic constant pointer in the constant memory, both required to stay in `[0, 2 ^ 32)` after the offset; a generic local pointer of another thread has no rule, since local memory is private to each thread (§5.1.5), and a store at a generic constant pointer is a fault (`badValue`). A generic number is a global address (EXT-CVTA), and a generic parameter pointer has no rule as an access address. A 32-bit generic number has no rule.

</details>

<a id="ext-addr-wrap"></a>
##### an address sum wraps at the address width (`EXT-ADDR-WRAP`)

*Interpretation (EXT)* · [Lean comment: `Core/Thread/Access.lean` L81-L104](../../Core/Thread/Access.lean#L81-L104)

The effective address of `[reg+immOff]` is the register's address plus the offset, modulo `2^64` for a global address, `2^32` for a shared address and `2^w` for a local or constant address in a `w`-bit register (`effAddr`, `sharedEffAddr`, `wrapAddr`). An absolute address `[immAddr+immOff]` does not wrap: a negative sum has no rule (`absLoc`). The PTX ISA calls the address a sum and does not say what happens when the sum leaves the address range.

Source:

- - §6.4.1: "[reg+immOff] a sum of register reg containing a byte address plus a constant integer byte offset (signed, 32-bit)."

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** the text calls the address a sum and says nothing about a sum that leaves the address range.

**Effect:** If it does not hold, an access whose sum leaves the address range is performed elsewhere on hardware or faults, and the model neither reports it nor accesses the same bytes. A kernel whose address sums never leave the range does not depend on it. Disclosed by every kernel whose statement names `Op.mem`, `Op.mbarInit`, `Op.mbarInval`, `Op.mbarArrive`, `Op.mbarWait`, `Op.cpBulk`, `Op.cpTensor`, `Op.cpTensorStore`, `Op.tcAlloc`, `Op.tcCommit` or `Op.clcTryCancel`: AddOne, BlockSum, CopyDynamic, CopyLdg, FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, RowSum, TcGemm, TmaCopy.

</details>

<a id="thread-access"></a>
#### footprints of loads and stores (`THREAD-ACCESS`)

*Rule* · [Lean comment: `Core/Thread/Access.lean` L280-L400](../../Core/Thread/Access.lean#L280-L400)

A load or store performs one read or write event per element at the location its address names, carrying the access's memory semantics and scope; `.volatile` accesses are `.relaxed` at `.sys`, and `.mmio` accesses keep their `.relaxed`, `.acquire` or `.release` at `.sys`. A scalar access must be aligned to its size and a vector access to its whole size, otherwise the behaviour is undefined. A narrow load is sign- or zero-extended into a wider destination register, a store writes the bytes of its source value or the low bits of a wider source register, and a source that is too narrow is a fault. `st.bulk` writes zero bytes to a region of the thread's `.shared::cta` window whose address is aligned to the region's size, the access size of §6.4.1. Cache hints have no effect, and `ld.global.nc` has a rule only under a kernel assumption that allows its site.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`elemAcc`](../../Core/Thread/Access.lean#L426-L430), [`setRegs`](../../Core/Thread/Access.lean#L432-L435), [`afterLoad`](../../Core/Thread/Access.lean#L437-L443), [`loadTmpl`](../../Core/Thread/Access.lean#L445-L453) ([concept](#c-loadtmpl)), [`afterStore`](../../Core/Thread/Access.lean#L455-L458), [`storeTmpl`](../../Core/Thread/Access.lean#L474-L485) ([concept](#c-storetmpl)), [`acquireLoadTmpl`](../../Core/Thread/Access.lean#L487-L492), [`releaseStoreTmpl`](../../Core/Thread/Access.lean#L494-L499), [`MemAccess.strongLocOk`](../../Core/Thread/Access.lean#L501-L509), [`MemAccess.strongLocOk_of_not_mmio`](../../Core/Thread/Access.lean#L511-L518), [`MemAccess.semAcc`](../../Core/Thread/Access.lean#L520-L530), [`MemAccess.semAcc_mmio_relaxed`](../../Core/Thread/Access.lean#L532-L536), [`accessAcc`](../../Core/Thread/Access.lean#L538-L548), [`accessAcc_of_weak`](../../Core/Thread/Access.lean#L550-L559), [`extendLoaded`](../../Core/Thread/Access.lean#L561-L568), [`afterAccessLoad`](../../Core/Thread/Access.lean#L570-L578), [`bulkInitTmpl`](../../Core/Thread/Access.lean#L580-L598), [`accessTmpl`](../../Core/Thread/Access.lean#L600-L623), [`memTmpl`](../../Core/Thread/Access.lean#L916-L932), [`memTmpl_direct_weakLoad`](../../Core/Thread/Access.lean#L934-L940), [`memTmpl_direct_weakStore`](../../Core/Thread/Access.lean#L942-L948), [`storeValue`](../../Core/Thread/Access.lean#L460-L468), [`storeValue_of_bytes`](../../Core/Thread/Access.lean#L470-L472)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.8 (ld): "A destination register wider than the specified type may be used. The value
    loaded is sign-extended to the destination register width for signed integers, and is
    zero-extended to the destination register width for unsigned and bit-size types."
- §9.7.10.8 (ld): "The .level::prefetch_size qualifier is a hint to fetch additional data of the
    specified size into the respective cache level."
- §9.7.10.8 (ld): "If the generic address does not fall within the address window of the global
    memory, then the prefetching behavior is undefined."
- §9.7.10.8 (ld): "The qualifiers .unified and .level::cache_hint are only supported for .global
    state space and for generic addressing where the address points to the .global state space."
- §9.7.10.8 (ld): "The .v8 ( .vec ) qualifier is supported if: .type is .b32 or .s32 or .u32 or .f32
    AND State space is .global or with generic addressing where address points to .global state
    space"
- §9.7.10.1: "Cache operators on load or store instructions are treated as performance hints only.
    The use of a cache operator on an ld or st instruction does not change the memory consistency
    behavior of the program."
- §9.7.10.1: "When ld.cs is applied to a Local window address, it performs the ld.lu operation."
- §9.7.10.1: "The compiler/programmer may use ld.lu when restoring spilled registers and popping
    function stack frames to avoid needless write-backs of lines that will not be used again."
- §9.7.10.2: "Cache eviction priority on load or store instructions is treated as a performance
    hint. It is supported for .global state space and generic addresses where the address points to
    .global state space."
- §9.7.10.9 (ld.global.nc)
- §9.7.10.11 (st): "A source register wider than the specified type may be used. The lower n bits
    corresponding to the instruction-type width are stored to memory."
- §9.7.10.14 (st.bulk): "size must be a multiple of 8. If the value is not a multiple of 8, then the
    behavior is undefined."
- §9.7.10.14 (st.bulk): "The maximum value of size operand can be 16777216."
- §9.7.10.14 (st.bulk): "If the address specified by a does not fall within the address window of
    .shared state space then the behavior is undefined."
- §6.4.1 (st.bulk alignment): "The access size of a memory instruction is the total number of bytes
    accessed in memory."
- §6.4.1 (st.bulk alignment): "The address must be naturally aligned to a multiple of the access
    size. If an address is not properly aligned, the resulting behavior is undefined."
- §8.2.4: "Memory operations with a vector data type are modeled as a set of equivalent memory
    operations with a scalar data type, executed in an unspecified order on the elements in the
    vector."
- §5.4.5 (alignment)
- §8.4.2: "The semantics of volatile operations are equivalent to a relaxed memory operation with
    system-scope but with the following extra implementation-specific constraints:"
- §8.4.1: "For formal specification of semantics of mmio operation from Memory Consistency Model
    perspective, it is equivalent to the semantics of a strong operation."
- §8.4.1: "As an exception, in some implementations, the surrounding locations may also be loaded."
- §8.2 (Table 20): "acquire operation A memory operation with .acquire or .acq_rel qualifier."
- §8.2 (Table 20): "release operation A memory operation with .release or .acq_rel qualifier."
- §9.7.10.8: ".relaxed and .acquire : May be used with .global , .shared spaces, or with generic
    addressing where the address points to .global or .shared space."
- §9.7.10.8: ".volatile : May be used with .global , .shared , .local spaces, or with generic
    addressing where the address points to .global , .shared , or .local space."
- §9.7.10.8: ".mmio : May be used only with .global space or with generic addressing where the
    address points to .global space."
- §9.7.10.8: "Only .sys thread scope is valid for ld.mmio operation."
- EXT-VECTOR-ELEM

**Applies:** The loads, stores and `st.bulk` whose rule is THREAD-ACCESS (`MemAccess.rule`, PROG-ISA-MEM); every other memory access is `noRule` (`memTmpl`)

**Premises:** Address, alignment, widths and operands pass the checks below; nc requires an assumption that enables its site.

**Effect:** Event production and local faults. A scalar access is aligned to its size, a vector access to its whole size; otherwise it is undefined. A vector access is a set of scalar memory operations, one event per element; the trace lists them in element order, and MEM-PROGRAM-ORDER orders no two elements of one access (§8.2.4: the element operations are "executed in an unspecified order"). Which bytes and which register each element has is EXT-VECTOR-ELEM. A store writes the bytes of its source value; a wider source register (decoded for the `.b`, `.u` and `.s` types) gives the low bits of its bit pattern (`storeValue`); a wider source without a bit pattern (a pointer) is a `typeMismatch` fault (stricter). A narrower source is a `typeMismatch` fault (Table 27 makes it invalid). A `st.bulk` of `size` bytes accesses `size` bytes, so its address must be a multiple of `size` (§6.4.1; §9.7.10.14 states no alignment of its own); otherwise it is `misaligned`. A `st.bulk` of size 0 accesses no byte and has no alignment condition. `ld.global.nc` is outside the memory model (§8.1) and has no core rule; it is a read only under a kernel assumption that allows it. A strong access (`strongOk`, PROG-ISA-MEM) has the same events with its semantics in the footprint (`semAcc`): `.relaxed`, `.acquire` or `.release` at the instruction's scope, and `.volatile` as `.relaxed` at `.sys`. An `.mmio` access (`MemAccess.mmio`) is a strong operation (§8.4.1) with its own `.sem` at `.sys`: an `ld.mmio.acquire.sys` is an acquire load and an `st.mmio.release.sys` a release store, so they form release and acquire patterns (MEM-RELEASE-ACQUIRE) like the same accesses without `.mmio`. The extra implementation-specific constraints of `.volatile` (instruction counts preserved, no reordering among volatile instructions) and the properties of `.mmio` (never combined, never cached) only restrict the hardware, so leaving them out admits more executions. An `.mmio` load may also load surrounding locations; those loads return nothing to the thread and write nothing, and the model's memory has no I/O device whose state they could change. A strong access at a location the text does not allow for its semantics (for example a generic address of a local location for `.relaxed`) has no rule (`strongLocOk`). `memTmpl` performs a weak scalar or vector access, a scalar acquire load and a scalar release store directly when it is a global access through a 64-bit register or a `.shared::cta` access through a 32-bit register without extension or cache hints (`MemAccess.locSpace?`); every other access is located by `accessLoc` (THREAD-ADDR) and performed by `accessTmpl`, with the same events. A loaded value is extended into its register (`extendLoaded`, `MemExt.extendBits`); a value without a bit pattern cannot be extended (`typeMismatch`). The cache operators, eviction priorities, the prefetch size and the cache policy are recorded in `CacheHints` and change nothing. The manual supports the eviction priorities, the prefetch size and the cache policy only for global addresses and states undefined prefetching for a generic address outside the global window, so such an access at another location has no rule; `.v8` and `.v4` of 64-bit elements likewise need a global location. `ld.lu`, and `ld.cs` on a local address, may drop the line without writing it back, which the text describes for spilled registers; a local load with either has no rule (stricter). `st.bulk` is one weak write of `size` zero bytes at a location of the thread's own `.shared::cta` window; a size that is not a multiple of 8 or above `16777216` is undefined, and so is an address outside that window, which includes every generic number (EXT-CVTA) and a pointer of another CTA.

</details>

<a id="ext-vector-elem"></a>
##### which address and register an element has (`EXT-VECTOR-ELEM`)

*Interpretation (EXT)* · [Lean comment: `Core/Thread/Access.lean` L402-L423](../../Core/Thread/Access.lean#L402-L423)

Element `j` of a vector load, store, `atom` or `red` of `n`-byte elements at `base` is the scalar access to bytes `base + j n` to `base + (j + 1) n - 1`, and it uses register `j` of each vector operand. The PTX ISA names the elements and gives neither their addresses nor their registers.

Source:

- - §8.2.4: "Memory operations with a vector data type are modeled as a set of equivalent memory operations with a scalar data type, executed in an unspecified order on the elements in the vector" - §5.4.2 and §5.4.5 (a vector access is aligned to its whole size)

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** §8.2.4 names the elements and says nothing about their addresses or registers; it does not state that the elements lie at consecutive addresses in register order. This is the ascending-address, register-order layout of a vector in memory. The order in which the elements execute is not part of this reading: §8.2.4 leaves it unspecified and the model keeps it unspecified (MEM-PROGRAM-ORDER).

**Effect:** The layout is one the toolchain is assumed to follow. Disclosed by every kernel whose statement names `MemAccess.mk (vec ≠ 1)`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, TcGemm.

</details>

<a id="thread-bytes"></a>
#### the value of read bytes (`THREAD-BYTES`)

*Rule* · [Lean comment: `Core/Thread/Access.lean` L193-L222](../../Core/Thread/Access.lean#L193-L222)

A load rebuilds a value from the bytes it read. The bits of the value are the bits of the bytes, little-endian, and the bytes of one whole stored value give that value back. An absent byte is an `uninitialized` fault, and bytes that have no bit pattern and are not one whole stored value have no rule.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`byteBits`](../../Core/Thread/Access.lean#L225-L229), [`intByte`](../../Core/Thread/Access.lean#L231-L234), [`littleEndianBits`](../../Core/Thread/Access.lean#L236-L243), [`rebuildBits`](../../Core/Thread/Access.lean#L245-L252), [`rebuild`](../../Core/Thread/Access.lean#L254-L272) ([concept](#c-rebuild)), [`rebuild.halves`](../../Core/Thread/Access.lean#L263-L272), [`memFloat`](../../Core/Thread/Access.lean#L274-L278)

<details>
<summary>Details for reviewers</summary>

- §8.2 (memory is bytes)
- §5.2.5 (packed data types)
- §5.2.1: "The bit-size type is compatible with any fundamental type having the same size."
- EXT-ENDIAN

**Applies:** Reconstructing loaded scalar or packed values

**Premises:** The bytes are present and each is a byte of a value with a bit pattern, or they are the bytes of one whole stored value.

**Effect:** Local consumption of read bytes. A byte's bits are byte `k` of the stored value's bit pattern (THREAD-BITS), independently of which store supplied it and of its type. The bytes of one whole stored value give that value back, so a floating payload keeps its number. Integer bytes of 1, 2, 4 or 8 bytes give the corresponding bit vector; a 16-byte load uses two 64-bit halves. Other bytes are split into halves, which keeps whole floating payloads (a packed pair); a piece that cannot be split further is the bit vector of its bytes. Partial reads of opaque payloads (pointers, CLC responses), which have no bit pattern, are model coverage gaps (Direction: stricter). `memFloat` is the number a load of a `fmt` element followed by a `fmt` instruction reads from memory: the rebuilt value read as a `fmt` operand (THREAD-NUM).

</details>

<a id="thread-atomic"></a>
#### atomic read-modify-write instructions (`THREAD-ATOMIC`)

*Rule* · [Lean comment: `Core/Thread/Access.lean` L625-L736](../../Core/Thread/Access.lean#L625-L736)

An `atom` or `red` with a rule performs one atomic read-modify-write event per scalar element, each vector element and each half of a packed type being its own: it reads the element's old bytes and writes the value of its operation on them, at the location its address names in the global or shared space, the global space for a vector. `atom` writes the old values to its destination registers unless the destination is the sink `_`, and `red` has no destination. The access is strong, with the memory semantics and scope of the instruction, `.relaxed` and `.gpu` when they are absent.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`MemAccess.atomElems`](../../Core/Thread/Access.lean#L739-L744), [`atomAcc`](../../Core/Thread/Access.lean#L746-L754), [`MemAccess.elemSrcs`](../../Core/Thread/Access.lean#L756-L760), [`MemAccess.elemSrcs_of_vec_one`](../../Core/Thread/Access.lean#L762-L771), [`pairUp`](../../Core/Thread/Access.lean#L773-L776), [`afterAtom`](../../Core/Thread/Access.lean#L778-L799), [`afterAtom_of_length_le_one`](../../Core/Thread/Access.lean#L801-L839), [`atomTmpl`](../../Core/Thread/Access.lean#L841-L871), [`atomTmpl_of_vec_one`](../../Core/Thread/Access.lean#L873-L914), [`memTmpl_atomic`](../../Core/Thread/Access.lean#L950-L953)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.5 (atom): "Atomically loads the original value at location a into destination register d ,
    performs a reduction operation with operand b and the value in location a , and stores the
    result of the specified operation at location a , overwriting the original value."
- §9.7.15.5 (atom): "atom with scalar type may be used only with .global and .shared spaces and with
    generic addressing, where the address points to .global or .shared space."
- §9.7.15.5 (atom): "atom with vector type may be used only with .global space and with generic
    addressing where the address points to .global space."
- §9.7.15.5 (atom): "For atom with vector type, operands d and b are brace-enclosed vector
    expressions, size of which is equal to the size of vector qualifier."
- §9.7.15.5 (atom): "If the .sem qualifier is absent, .relaxed is assumed by default."
- §9.7.15.5 (atom): "If the .scope qualifier is absent, .gpu scope is assumed by default."
- §9.7.15.5 (atom): "atom instruction on packed type or vector type, accesses adjacent scalar
    elements in memory. In such cases, the atomicity is guaranteed separately for each of the
    individual scalar elements; the entire atom is not guaranteed to be atomic as a single access."
- §9.7.15.5 (atom): "Simple reductions may be specified by using the bit bucket destination operand
    _ ."
- §9.7.15.5 (atom): "The qualifier .level::cache_hint is only supported for .global state space and
    for generic addressing where the address points to the .global state space."
- §9.7.15.5 (atom): "It is treated as a performance hint only, and does not change the memory
    consistency behavior of the program."
- §9.7.15.5 (atom), Table 41 rows: ".u32 .add , .inc , .dec , .min , .max Not supported Not
    supported .s32 .add , .min , .max Not supported Not supported .u64 .add , .min , .max Not
    supported Not supported .s64 .min , .max Not supported Not supported .f32 Not supported
    .add{.noftz} Not supported .f64 Not supported .add (noftz by default) Not supported .f16 Not
    supported .add (requires .noftz ) Not supported"
- §9.7.15.5 (atom), Table 41 rows: ".b16 Not supported Not supported .cas .b32 Not supported Not
    supported .and , .or , .xor , .exch , .cas .b64 Not supported Not supported .and , .or , .xor ,
    .exch , .cas .b128 Not supported Not supported .exch , .cas"
- §9.7.15.5 (atom): "atom{.sem}{.scope}{.global}.add{.noftz}{.level::cache_hint}.vec_32_bit.f32 d,
    [a], b{, cache_policy};"
- §9.7.15.5 (atom): ".half_word_type = { .f16, .bf16 }; .packed_type = { .f16x2, .bf16x2 };
    .vec_16_bit = { .v2, .v4, .v8 } .vec_32_bit = { .v2, .v4 };"
- §9.7.15.5 (atom), vector table: "Vector qualifier Types .f16 / bf16 .f16x2 / bf16x2 .f32 .v2 .add
    , .min , .max (all require .noftz ) .add , .min , .max (all require .noftz ) .add .v4 .add ,
    .min , .max (all require .noftz ) .add , .min , .max (all require .noftz ) .add .v8 .add , .min
    , .max (all require .noftz ) Not supported Not Supported"
- §9.7.15.6 (red): "Performs a reduction operation with operand b and the value in location a , and
    stores the result of the specified operation at location a , overwriting the original value."
- §9.7.15.6 (red): ".sem = { .relaxed, .release }"
- §9.7.15.6 (red): "red with scalar type may be used only with .global and .shared spaces and with
    generic addressing, where the address points to .global or .shared space."
- §9.7.15.6 (red): "red with vector type may be used only with .global space and with generic
    addressing where the address points to .global space."
- §9.7.15.6 (red): "For red with vector type, operand b is brace-enclosed vector expressions, size
    of which is equal to the size of vector qualifier."
- §9.7.15.6 (red): "red instruction on packed type or vector type, accesses adjacent scalar elements
    in memory. In such case, the atomicity is guaranteed separately for each of the individual
    scalar elements; the entire red is not guaranteed to be atomic as a single access."
- §8.2 (Table 20): "read operation All variants of ld instruction and atom instruction (but not red
    instruction)."
- §5.4.5: "Note that all PTX instructions that access memory require that the address be aligned to
    a multiple of the access size. The access size of a memory instruction is the total number of
    bytes accessed in memory."
- §6.4.1: "The address must be naturally aligned to a multiple of the access size. If an address is
    not properly aligned, the resulting behavior is undefined."
- THREAD-ADDR
- THREAD-ATOMIC-OP
- THREAD-BYTES
- EXT-VECTOR-ELEM

**Applies:** The scalar and vector `atom` and `red` forms whose rule is THREAD-ATOMIC (`MemAccess.atomicOk`, PROG-ISA-MEM)

**Premises:** The operation and type are a combination of Table 41 (`atom`) or Table 42 (`red`), or for a vector form of the vector table; the address names a global or shared location, a global one for a vector form, aligned to the access size; each source has the size of the type.

**Effect:** Event production (`.rmw`) and local faults; the event's read and write enter the memory model as one operation (MEM-FOOTPRINT, ERR-DATA-RACE, MEM-ATOMICITY, MEM-RELEASE-ACQUIRE). A scalar element is the whole value for a scalar type and each half for `.f16x2` and `.bf16x2`, and a vector form (`.v2`, `.v4`, `.v8`) has the scalar elements of each of its vector elements in turn. The manual guarantees atomicity only for each scalar element of a packed or vector type, so each scalar element is its own atomic operation, and the scalar elements of one instruction are unordered among themselves as the elements of a vector access are (MEM-PROGRAM-ORDER). Scalar element `j` of `m`-byte scalar elements lies at bytes `base + j m` to `base + (j + 1) m - 1`: vector element `e` at `base + e s` for `s`-byte vector elements (EXT-VECTOR-ELEM), and half `h` of a packed value at its bytes `2 h` and `2 h + 1` (EXT-ENDIAN, THREAD-BYTES). Vector element `e` takes register `e` of each vector operand (`elemSrcs`, EXT-VECTOR-ELEM). The address is located as a load's (`accessLoc`, THREAD-ADDR); a location outside the global and shared spaces has no rule, and so have a vector form and a cache hint at a location outside the global space (a generic address of a shared location included). An access is aligned to its whole size (a scalar's size, both halves of a packed value, all elements of a vector), otherwise it is `misaligned`. The event's footprint carries the semantics: every `atom` and `red` is strong (`relaxed`, `acquire`, `release`), its scope is the instruction's, `.gpu` when absent, and only an `atom` has an acquiring read, because Table 20 does not count `red` as a read operation. The bytes written are the value of THREAD-ATOMIC-OP on the rebuilt old value and the operands; when that has no value (`noRule`, `typeMismatch`) the event writes nothing and the thread's next event is `ub`. The old values, rebuilt from the bytes read (THREAD-BYTES), are written to the destination registers after the last scalar element, register `e` receiving vector element `e`, one packed value for a packed type (`afterAtom`, `pairUp`). A `cas` compares bit patterns. The `min` and `max` of the half-precision vector forms are floating operations and take their value from an assumption as every floating operation does (THREAD-ATOMIC-OP). The following forms have no rule: the combinations that Table 41, Table 42 and the vector table do not list, `atom` and `red` of a local or constant location, a vector form at a shared location, an `atom` whose destination vector mixes registers and the sink `_`, `red` with `.acquire` or `.acq_rel`, and `.f64` floating forms under the ideal-real assumption, which gives no `.f64` value.

</details>

<a id="thread-atomic-op"></a>
#### the values of atomic operations (`THREAD-ATOMIC-OP`)

*Rule* · [Lean comment: `Core/Memory/AtomicOp.lean` L18-L62](../../Core/Memory/AtomicOp.lean#L18-L62)

An integer or bit operation of `atom`, `red` or a tensor reduction computes the result of the Semantics section of `atom` exactly at the element width, from the bit patterns of the old value in memory and of the operands, comparing as two's complement numbers for the signed types. A floating operation takes its value from a kernel assumption, and without one the operation has no rule.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`AtomOp.apply`](../../Core/Memory/AtomicOp.lean#L65-L83), [`Value.ofWidth`](../../Core/Memory/AtomicOp.lean#L85-L89), [`rmwValue`](../../Core/Memory/AtomicOp.lean#L91-L120)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.5 (atom): "atomic { d = *a; *a = (operation == cas) ? operation(*a, b, c) : operation(*a,
    b); }"
- §9.7.15.5 (atom): "inc(r, s) = (r >= s) ? 0 : r+1; dec(r, s) = (r==0 || r > s) ? s : r-1; exch(r,
    s) = s; cas(r,s,t) = (r == s) ? t : r;"
- §9.7.15.5 (atom): "The .inc and .dec operations return a result in the range [0..b] ."
- §9.7.15.5 (atom): "The .add operation rounds to nearest even."
- §9.7.15.5 (atom): "The .min and .max operations implement the exact same floating-point
    instructions as the non-atomic min and max instructions, but perform them atomically."
- §9.7.15.6 (red): "*a = operation(*a, b);"
- §9.7.1.13 (min): "d = (a < b) ? a : b; // Integer (signed and unsigned)"
- §9.7.1.14 (max): "d = (a > b) ? a : b; // Integer (signed and unsigned)"
- §9.7.9.1: "Compute the bit-wise and operation for the bits in a and b"
- THREAD-INT (an integer result wraps at its width)
- THREAD-BITS (bit patterns)
- ASM-INTERFACE (`rmwRule`)

**Applies:** The write half of every `atom` and `red` element with a rule (THREAD-ATOMIC) and every tensor reduction element (DEP-REDUCTION-VALUES)

**Premises:** The element type is an integer, bit or floating type; for an integer or bit type the old value and each operand has a bit pattern of the element's size.

**Effect:** Local value of the bytes an atomic read-modify-write writes; `noRule` and `typeMismatch` are faults (ERR-FAULT-REASON). The integer and bit operations work on the bit patterns of the old value `r` and the operand `s` taken modulo `2 ^ w` for the element width `w` (`AtomOp.apply`): `add` wraps at the width as the integer `add` does (THREAD-INT), `min` and `max` compare as two's complement numbers for the `.s` types and as unsigned numbers otherwise, `and`, `or` and `xor` are bitwise, `inc`, `dec` and `exch` are the quoted formulas, and `cas` compares `r` with the compare operand and writes the swap operand when they are equal. A result of at most 64 bits is a bit vector; a 128-bit result is two 64-bit halves, low half first (`Value.ofWidth`, THREAD-BYTES). A floating operation (`add`, `min` and `max` of a floating element) has no Core rule: the first assumption whose `rmwRule` gives a value supplies it, and without one the operation is `noRule`, as for every floating instruction.

</details>

<a id="thread-prefetch"></a>
#### cache prefetch and eviction priority (`THREAD-PREFETCH`)

*Rule* · [Lean comment: `Core/Thread/Local.lean` L1630-L1656](../../Core/Thread/Local.lean#L1630-L1656)

`prefetch` and `prefetchu` without `.valid_addr` and `applypriority.global` change neither registers nor memory, so the thread only moves to the next instruction. `applypriority` at an address that is not aligned to 128 bytes is undefined.

Source:

- 

Direction: `equal` (the entry claims to follow its cited text)

Lean definitions: [`addrValue`](../../Core/Thread/Local.lean#L1659-L1665), [`execPrefetch`](../../Core/Thread/Local.lean#L1667-L1673)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.16: "The prefetch instruction brings the cache line containing the specified address in
    global or local memory state space into the specified cache level."
- §9.7.10.16: "A prefetch to a shared memory location performs no operation."
- §9.7.10.17: "The applypriority instruction applies the cache eviction priority specified by the
    .level::eviction_priority qualifier to the address range [a..a+size) in the specified cache
    level."
- §9.7.10.17: "a must be aligned to 128 bytes."

**Applies:** The instructions whose rule is THREAD-PREFETCH (`AddrInstr.rule`)

**Premises:** An `applypriority` address is a 64-bit integer or an absolute address.

**Effect:** Local step to the next instruction. The manual states undefined behaviour for `prefetch.valid_addr` when the location is not valid for the access and for a generic `prefetch.valid_addr` or `applypriority` whose address is outside the global window; these forms need a check of the memory at launch and have no rule. A prefetch states no undefined behaviour for any other address, so it does not read its address register.

</details>

<a id="thread-cache-policy"></a>
#### cache eviction policies (`THREAD-CACHE-POLICY`)

*Rule* · [Lean comment: `Core/Thread/Local.lean` L1675-L1714](../../Core/Thread/Local.lean#L1675-L1714)

`createpolicy` writes an opaque cache eviction policy to its destination register. A range-based policy needs a global address and a primary size at most the total size, and a fraction-based policy a fraction in `(0.0, 1.0]`; any other operand is undefined. A policy has no bit pattern, so an instruction that reads it as an integer has no rule.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`execPolicy`](../../Core/Thread/Local.lean#L1780-L1795)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.21: "The createpolicy instruction creates a cache eviction policy for the specified cache
    level in an opaque 64-bit register specified by the destination operand cache_policy ."
- §9.7.10.21: "The value of primary-size must be less than or equal to the value of total-size ."
- §9.7.10.21: "If the specified address does not fall within the address window of .global state
    space then the behavior is undefined."
- §9.7.10.21: "The valid range of values for the operand fraction is (0.0,.., 1.0] ."
- §9.7.10.21: "If the operand fraction is not specified, it defaults to 1.0."
- §9.7.10.21: "The source operand access-property is a 64-bit opaque register."
- §9.7.10.8: "cache_policy is a hint to the cache subsystem and may not always be respected. It is
    treated as a performance hint only, and does not change the memory consistency behavior of the
    program."

**Applies:** `createpolicy` (`MiscInstr.rule`, PROG-ISA-MISC)

**Premises:** The operands are defined values of their types; the address of a range is a global address in a register or an absolute address.

**Effect:** Local register update; a primary size above the total size or a fraction outside `(0.0, 1.0]` is `badValue`. The policy is the value `Value.policy` (THREAD-VALUE), which records nothing: the manual describes its effect only as a performance hint, so no rule reads what it contains, and the instructions with `.level::cache_hint` accept it as their `cache_policy` operand. The address of a range-based policy is read as an integer (`addrValue`): a generic number is a global address (EXT-CVTA), and a shared, local, constant or parameter pointer has no integer reading and has no rule. The model rejects a generic parameter pointer although the `.param` window lies in the `.global` window, which is one reason the direction is stricter. `total-size` is a 32-bit operand, so it is always within the maximum of 4GB. A fraction is read as an `.f32` number (THREAD-NUM). The access property of `createpolicy.cvt` comes from the CUDA API, and the model requires only that it is a defined 64-bit value.

</details>

<a id="thread-no-effect"></a>
#### sleeping, performance monitor events and grid dependency control (`THREAD-NO-EFFECT`)

*Rule* · [Lean comment: `Core/Thread/Local.lean` L1717-L1745](../../Core/Thread/Local.lean#L1717-L1745)

`nanosleep`, `pmevent` and `griddepcontrol` change no state of the model and continue with the next instruction; `nanosleep` reads its delay operand. `griddepcontrol` has no effect because the launch has no prerequisite or dependent grid (EXT-GRIDDEP-SINGLE).

Source:

- 

Direction: `equal` (the entry claims to follow its cited text)

Lean definitions: [`execMisc`](../../Core/Thread/Local.lean#L1797-L1804)

<details>
<summary>Details for reviewers</summary>

- §9.7.21.2: "Suspends the thread for a sleep duration approximately close to the delay t ,
    specified in nanoseconds."
- §9.7.21.2: "The sleep duration is approximated, but guaranteed to be in the interval [0, 2*t] ."
- §9.7.21.3: "Triggers one or more of a fixed number of performance monitor events, with event index
    or mask specified by immediate operand a ."
- §9.7.21.3: "The relationship between events and counters is programmed via API calls from the
    host."
- §9.7.15.14 (griddepcontrol, as quoted in EXT-GRIDDEP-SINGLE)
- EXT-GRIDDEP-SINGLE

**Applies:** `nanosleep`, `pmevent` and `griddepcontrol` (`MiscInstr.rule`, PROG-ISA-MISC)

**Premises:** The delay operand of `nanosleep` is a defined 32-bit value.

**Effect:** Local step to the next instruction. The model has no time, so a delay of `nanosleep` is a step of the thread that changes nothing; the other threads may take any number of steps meanwhile, as they may at every step. The performance counters that `pmevent` increments are read only through the `%pm` special registers, which have no rule (THREAD-SREG), so no instruction with a rule observes them.

</details>

<a id="ext-griddep-single"></a>
##### grid dependency control in a launch of one grid (`EXT-GRIDDEP-SINGLE`)

*Interpretation (EXT)* · [Lean comment: `Core/Thread/Local.lean` L1747-L1777](../../Core/Thread/Local.lean#L1747-L1777)

The model takes the kernel to run as a single grid with no prerequisite grid and no dependent grid. Then `griddepcontrol.wait` returns at once and `griddepcontrol.launch_dependents` has no effect on the kernel's execution: both are local steps to the next instruction (`execMisc`).

Source:

- - §9.7.15.14: ".launch_dependents modifier signals that specific dependents the runtime system designated to react to this instruction can be scheduled as soon as all other CTAs in the grid issue the same instruction or have completed." - §9.7.15.14: ".wait modifier causes the executing thread to wait until all prerequisite grids in flight have completed and all the memory operations from the prerequisite grids are performed and made visible to the current grid." - §9.7.15.14: "If the prerequisite grid is using griddepcontrol.launch_dependents , then the dependent grid must use griddepcontrol.wait to ensure correct functional execution."

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** the instruction's behaviour depends on the grids the runtime designates as prerequisites and dependents, which are outside the PTX program. The text determines the result only once the launch is known: with no prerequisite grid in flight there is nothing to wait for, and with no designated dependent nothing is scheduled. That the launch has neither is the obligation of EXT-LAUNCH (no PDL-dependent launch, no conflicting outside access), not a fact the model checks.

**Effect:** A kernel launched as a dependent grid, or whose dependents run concurrently through programmatic dependent launch, is outside the theorem: its `griddepcontrol.wait` may block and order memory operations of other grids, and the dependents may access memory concurrently. Disclosed by every kernel whose statement names `MiscInstr.gridDep`: FlashMlaSparseDecodeH64, InklingRelDecode.

</details>

<a id="thread-fence"></a>
#### thread fences and proxy fences (`THREAD-FENCE`)

*Rule* · [Lean comment: `Core/Thread/Fence.lean` L19-L85](../../Core/Thread/Fence.lean#L19-L85)

Each thread fence performs one event that records its semantics and scope, and each proxy fence performs one event that records its proxy kind and its scope (none for a form without a scope). The `.sem` of a proxy fence creates no synchronization; the scope of an async proxy fence bounds the threads its order reaches (MEM-MODEL-CAUSALITY). `fence.proxy.tensormap::generic.acquire` whose address does not lie in the global state space is undefined behaviour.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`fenceTmpl`](../../Core/Thread/Fence.lean#L88-L98), [`fenceTmpl_asyncCta`](../../Core/Thread/Fence.lean#L100-L103), [`fenceTmpl_proxy_order`](../../Core/Thread/Fence.lean#L105-L110)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.4: "The fence instruction establishes an ordering between memory accesses requested by
    this thread ( ld , st , atom and red instructions) as described in the Memory Consistency
    Model ."
- §9.7.15.4: "Generic Addressing is used unconditionally, and the address specified by the operand
    addr must fall within the .global state space. Otherwise, the behavior is undefined."
- §9.7.15.4: "Bi-directional proxy fences do not directly synchronize with other fences in the sense
    that fences with .release or .acquire semantics do."
- §9.7.15.4: "Instead, bi-directional proxy fences take effect within a single thread and therefore
    do not have a .scope qualifier."
- §9.7.15.4 (syntax): "// Proxy fence (bi-directional): fence.proxy.proxykind;
    fence.proxy.proxykind{.sem}.scope;"
- §9.7.15.4: "A .release proxy fence can form a release sequence that synchronizes with an acquire
    sequence that contains a .acquire proxy fence."
- §9.7.15.4: "Value .alias of the .proxykind qualifier refers to memory accesses performed using
    virtually aliased addresses to the same memory location."
- §8.4 (Table 20): "memory fence operation A membar , fence.sc or fence.acq_rel instruction."
- §8.4 (Table 20): "proxy fence operation A fence.proxy or a membar.proxy instruction."
- §8.6: "Operations using methods of access distinct from the generic method include: textures and
    surface accesses, accesses to the same location via the same proxy using distinct virtual memory
    addresses, async-proxy and tensormap-proxy accesses by .async.bulk operations, fabric-proxy
    accesses by fabric operations, readonly-proxy accesses by ld.proxy::readonly operations."
- EXT-LAUNCH (no aliases)

**Applies:** Every `Op.fence` (PROG-ISA-FENCE), `fence.proxy.proxykind{.sem}.scope` included

**Premises:** The tensormap acquire fence's generic address names a global location.

**Effect:** Event production (`.fence`, `.fenceProxy`) and one local fault. A thread fence (`fence.sc`, `fence.acq_rel`, `fence.acquire`, `fence.release`, `membar`) is the event `.fence sem scope`; its synchronization is MEM-RELEASE-ACQUIRE (release and acquire patterns) and MEM-FENCE-SC (`fence.sc`). A proxy fence is the event `.fenceProxy k scope`: `scope` is the scope of `fence.proxy.proxykind{.sem}.scope` and of the tensormap and fabric proxy fences, and `none` for `fence.proxy.proxykind`, which has no scope. The syntax lists both forms as bi-directional proxy fences although the text says that bi-directional proxy fences have no scope; the event keeps the scope so that MEM-MODEL-CAUSALITY can bound the fence's reach by it. An async proxy fence orders generic and async-proxy accesses at the bytes of its state space for the threads it reaches (MEM-MODEL-CAUSALITY, `ProxyFenceReach`). The other proxy fences create no order in the model, which is stricter than the text wherever they would: the alias proxy fence orders accesses through distinct virtual addresses of one location, and the model's launches have no aliases (EXT-LAUNCH); the tensormap proxy fences order generic accesses with tensormap-proxy reads, and the model's tensormap-proxy reads read only the launch's tensor maps; the fabric proxy fences order generic accesses with fabric operations, which have no rule. The `.sem` of a proxy fence (`fence.proxy.proxykind{.sem}.scope`, the tensormap and the fabric proxy fences) gives no synchronization (stricter). The text lets a `.release` proxy fence form a release sequence that synchronizes with an acquire sequence containing a `.acquire` proxy fence, but it does not say whether such a sequence also synchronizes with a release or acquire pattern without a proxy fence, nor what `.sc` adds to a proxy fence (Table 20 names `fence.sc` and `fence.acq_rel` as memory fence operations and `fence.proxy` as a proxy fence operation). Leaving the synchronization of the `.sem` out removes no execution: a kernel that needs it is rejected, for example by a race report. The scope is not left out: leaving it out would let a fence of a narrower scope order the accesses of threads outside that scope, which removes the executions in which those accesses do not see the ordered access. The address of `fence.proxy.tensormap::generic.acquire` is located as a load's generic address (THREAD-ADDR): a generic number is a global address (EXT-CVTA), a shared, local or constant pointer is undefined (`badValue`), and an address `accessLoc` cannot locate has no rule.

</details>

### Register adjustment

The `setmaxnreg` request, how the lanes of a warp match, and when it is unsafe.

<a id="thread-setmaxnreg"></a>
#### register adjustment requests (`THREAD-SETMAXNREG`)

*Rule* · [Lean comment: `Core/Thread/SetMaxNReg.lean` L11-L34](../../Core/Thread/SetMaxNReg.lean#L11-L34)

A `setmaxnreg` instruction is one event that carries its direction and its count, and it changes no register of the thread. The count must be between 24 and 256 and a multiple of 8, otherwise the instruction faults. The lanes of one warp are matched by the ordinal of the request, its source instruction and its payload.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`SetMaxNReg.validCount`](../../Core/Thread/SetMaxNReg.lean#L103-L104), [`SetMaxNReg.tmpl`](../../Core/Thread/SetMaxNReg.lean#L106-L109) ([concept](#c-setmaxnreg-tmpl)), [`SetMaxNReg.Request`](../../Core/Thread/SetMaxNReg.lean#L111-L114) ([concept](#c-setmaxnreg-request)), [`SetMaxNReg.isRequest`](../../Core/Thread/SetMaxNReg.lean#L116-L120), [`SetMaxNReg.ordinal`](../../Core/Thread/SetMaxNReg.lean#L122-L123), [`SetMaxNReg.SameGroup`](../../Core/Thread/SetMaxNReg.lean#L125-L127)

<details>
<summary>Details for reviewers</summary>

- §9.7.21.5: "The value of imm-reg-count must be in the range 24 to 256 (both inclusive) and must be
    a multiple of 8."
- EXT-SETMAXNREG-VIRTUAL
- EXT-SETMAXNREG-EFFECTIVE

**Applies:** setmaxnreg.inc/dec.sync.aligned.u32

**Premises:** Immediate count is between 24 and 256, inclusive, and a multiple of eight.

**Effect:** Event production. Its return is constrained by DEP-SETMAXNREG-RENDEZVOUS and its legality by ERR-SETMAXNREG. The local instance labels of the lanes may differ or repeat and impose no legality constraint.

</details>

<a id="ext-setmaxnreg-virtual"></a>
##### PTX registers keep their values across setmaxnreg (`EXT-SETMAXNREG-VIRTUAL`)

*Interpretation (EXT)* · [Lean comment: `Core/Thread/SetMaxNReg.lean` L36-L62](../../Core/Thread/SetMaxNReg.lean#L36-L62)

The model takes every PTX register to keep the value last written to it across `setmaxnreg.inc` and `setmaxnreg.dec`, and the request changes no register of the thread (`SetMaxNReg.tmpl` is `next t`). The PTX ISA says that the new physical registers after `.inc` have undefined contents and does not say how PTX registers map onto physical ones.

Source:

- - §9.7.21.5: "setmaxnreg provides a hint to the system to update the maximum number of per-thread registers owned by the executing warp" - §9.7.21.5: "After the instruction setmaxnreg.inc obtains new registers from the CTA pool, the initial contents of the new registers are undefined. The new registers must be initialized before they are used."

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** §9.7.21.5 speaks of the physical registers a warp owns and leaves the new ones' contents undefined; it does not say how the program's PTX registers map onto them. That `ptxas` keeps every PTX register's value across the adjustment (reading the undefined new registers never stands for reading a PTX register the program wrote) is the toolchain's allocation, not stated.

**Effect:** If it does not hold, a PTX register read after `setmaxnreg.inc` may return the undefined contents of a newly obtained physical register. The values the model gives the thread after the request, with every result that depends on them, are then not those of the hardware. Disclosed by every kernel whose statement names `Op.setMaxReg`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode.

</details>

<a id="ext-setmaxnreg-effective"></a>
##### every setmaxnreg request takes effect and returns (`EXT-SETMAXNREG-EFFECTIVE`)

*Interpretation (EXT)* · [Lean comment: `Core/Thread/SetMaxNReg.lean` L64-L101](../../Core/Thread/SetMaxNReg.lean#L64-L101)

The model assumes that the kernel was launched with a valid per-thread register configuration. Then every `setmaxnreg` request takes effect: the count the warp owns after it is the requested count, which is the count later requests of the warp are compared with (`SetMaxNReg.prior` is the previous request, ERR-SETMAXNREG). Every `setmaxnreg.inc` returns as soon as every lane of its warp has executed it (DEP-SETMAXNREG-RENDEZVOUS), whatever registers the CTA's pool holds. Register counts and the register pool are not represented, and the direction requirement of a warp's first request is not compared with the per-thread register count the kernel was launched with.

Source:

- - §9.7.21.5: "The setmaxnreg.inc instruction blocks the execution until enough registers are available in the CTA’s register pool." - §9.7.21.5: "The setmaxnreg instruction requires that the kernel has been launched with a valid value of maximum number of per-thread registers specified via the appropriate compilation via the appropriate compile-time option or the appropriate performance tuning directive. Otherwise, the setmaxnreg instruction may have no effect." - §9.7.21.5: "When qualifier .inc is specified, the maximum number of per-thread registers owned by the warp prior to the execution of setmaxnreg instruction should be less than or equal to the imm-reg-count . Otherwise, the behavior is undefined."

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** the text lets `setmaxnreg.inc` block until the pool can supply the registers, lets a request have no effect when the launch configuration is not valid, and states its direction requirements on the count the warp owns, which for a warp's first request is the count of the launch; the model represents none of these.

**Effect:** The reading is not stricter than the text. It depends on the launch configuration, which the model does not check. If it does not hold, an `inc` that the registers of the launch cannot satisfy blocks the warp forever on hardware, and the model's `progress` and `terminates` conclusions do not reflect that. A request may have no effect, so the count the model uses as the base of the next direction comparison (the previous request) differs from the count the hardware holds, and a later request in the wrong direction, which is undefined, may not be reported. A warp's first request in the wrong direction from the launch's per-thread count is undefined, and the model does not report it. Disclosed by every kernel whose statement names `Op.setMaxReg`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode.

</details>

<a id="dep-setmaxnreg-rendezvous"></a>
#### warp rendezvous of a register adjustment (`DEP-SETMAXNREG-RENDEZVOUS`)

*Rule* · [Lean comment: `Core/Thread/SetMaxNReg.lean` L129-L149](../../Core/Thread/SetMaxNReg.lean#L129-L149)

A `setmaxnreg` request returns only after every one of the 32 lanes of its warp has made the same request, with the same ordinal, source instruction and payload.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`SetMaxNReg.SameRequest`](../../Core/Thread/SetMaxNReg.lean#L151-L155) ([concept](#c-setmaxnreg-samerequest))

<details>
<summary>Details for reviewers</summary>

- §9.7.21.5: "The mandatory .sync qualifier indicates that setmaxnreg instruction causes the
    executing thread to wait until all threads in the warp execute the same setmaxnreg instruction
    before resuming execution."
- EXT-SETMAXNREG-EFFECTIVE

**Applies:** setmaxnreg events

**Premises:** The request is followed by another event of its thread: it returned.

**Effect:** `SameRequest` gives the needs of a request in `KindNeeds` (DEP-ORDER): the matching request of every lane of the warp is a witness of its return. No other condition delays the return (EXT-SETMAXNREG-EFFECTIVE): the wait for the CTA's register pool is not a need.

</details>

<a id="err-setmaxnreg"></a>
#### register adjustment legality (`ERR-SETMAXNREG`)

*Rule* · [Lean comment: `Core/Thread/SetMaxNReg.lean` L157-L197](../../Core/Thread/SetMaxNReg.lean#L157-L197)

A `setmaxnreg` request is unsafe when its direction disagrees with the count of the thread's previous request, when its warpgroup is not entirely inside the CTA, or when requests of one warpgroup with the same ordinal differ in direction or count. It is also unsafe when a thread of the previous request of the warpgroup is not ordered before it.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`SetMaxNReg.prior`](../../Core/Thread/SetMaxNReg.lean#L199-L202), [`SetMaxNReg.Unsafe`](../../Core/Thread/SetMaxNReg.lean#L204-L214) ([concept](#c-setmaxnreg-unsafe)), [`SetMaxNReg.UnsafeAt`](../../Core/Thread/SetMaxNReg.lean#L216-L230), [`SetMaxNReg.UnsafeAt.unsafe`](../../Core/Thread/SetMaxNReg.lean#L232-L239), [`SetMaxNReg.unsafeAt_noExempt`](../../Core/Thread/SetMaxNReg.lean#L241-L252)

<details>
<summary>Details for reviewers</summary>

- §9.7.21.5: "When qualifier .dec is specified, the maximum number of per-thread registers owned by
    the warp prior to the execution of setmaxnreg instruction should be greater than or equal to the
    imm-reg-count . Otherwise, the behavior is undefined."
- §9.7.21.5: "When qualifier .inc is specified, the maximum number of per-thread registers owned by
    the warp prior to the execution of setmaxnreg instruction should be less than or equal to the
    imm-reg-count . Otherwise, the behavior is undefined."
- §9.7.21.5: "The same setmaxnreg instruction must be executed by all warps in a warpgroup ."
- §9.7.21.5: "After executing a setmaxnreg instruction, all warps in the warpgroup must synchronize
    explicitly before executing subsequent setmaxnreg instructions."
- §9.7.21.5: "The mandatory .sync qualifier indicates that setmaxnreg instruction causes the
    executing thread to wait until all threads in the warp execute the same setmaxnreg instruction
    before resuming execution."
- EXT-SETMAXNREG-EFFECTIVE
- EXT-BAR-PARTICIPANTS

**Applies:** setmaxnreg events

**Premises:** A thread's request has an ordinal (DEP-SETMAXNREG-RENDEZVOUS); its previous request, if any, gives the count the warp owns, as if it took effect (EXT-SETMAXNREG-EFFECTIVE).

**Effect:** Contributes to Unsafe. A warpgroup thread that has not exited and not yet reached the request remains a progress obligation, not an assumed arrival. The first request of a thread is not compared with the launch's register count (EXT-SETMAXNREG-EFFECTIVE). Between warps only the direction and count are compared, which is the reading EXT-BAR-PARTICIPANTS. The source instructions of the lanes of one warp and a thread of the warpgroup that exits before the request are ERR-ALIGNED-MISMATCH. The order between the previous request of the warpgroup and a later request is base causality order (`baseCausality`, MEM-BASE-CAUSALITY). A request at a site that an assumption selects with `regSyncExempt` (ASM-SETMAXNREG-SYNC) is not subject to the last clause (`UnsafeAt`).

</details>
