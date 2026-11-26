# Instructions: families, rules and tables

How a decoded instruction gets its meaning. The qualifier vocabulary and the operands come first, then the instruction families: each family has a representation, a decoding from a recognized instruction and a rule function that names the contract entry giving the instruction its semantics. The tables at the end list every entry of the instruction table with the modifier values that have semantics and those that only decode.

Generated from the Lean comments of `Core/` and `Assumption/` by `Tools/coredoc.py`. Every entry links to the Lean source it was generated from. [All chapters](README.md).

## Contents

- [Concepts](#concepts)
  - [Types and qualifiers](#types-and-qualifiers)
    - [`DType`](#c-dtype)
    - [`StateSpace`](#c-statespace)
    - [`Sem`](#c-sem)
    - [`Cmp`](#c-cmp)
  - [Family representations](#family-representations)
    - [`RuleId`](#c-ruleid)
    - [`IntInstr`](#c-intinstr)
    - [`FloatInstr`](#c-floatinstr)
    - [`MoveInstr`](#c-moveinstr)
    - [`CvtInstr`](#c-cvtinstr)
    - [`MemAccess`](#c-memaccess)
    - [`AddrInstr`](#c-addrinstr)
    - [`WarpKind`](#c-warpkind)
    - [`WarpInstr`](#c-warpinstr)
- [Rules](#rules)
  - [Types and operands](#types-and-operands)
    - [data types and shared qualifiers](#prog-isa-types) (`PROG-ISA-TYPES`)
    - [operands and their resolution](#prog-operand) (`PROG-OPERAND`)
    - [special registers](#prog-isa-sreg) (`PROG-ISA-SREG`)
  - [Instruction families](#instruction-families)
    - [the contract ID of the rule of an instruction](#prog-rule-id) (`PROG-RULE-ID`)
    - [the rule of every instruction](#prog-instr-rule) (`PROG-INSTR-RULE`)
    - [integer and bit instructions](#prog-isa-int) (`PROG-ISA-INT`)
    - [floating-point instructions](#prog-isa-float) (`PROG-ISA-FLOAT`)
    - [register moves](#prog-isa-move) (`PROG-ISA-MOVE`)
    - [conversions](#prog-isa-cvt) (`PROG-ISA-CVT`)
    - [cache policies, sleep and performance monitor events](#prog-isa-misc) (`PROG-ISA-MISC`)
    - [memory accesses and address instructions](#prog-isa-mem) (`PROG-ISA-MEM`)
    - [thread fences and proxy fences](#prog-isa-fence) (`PROG-ISA-FENCE`)
    - [warp collectives](#prog-isa-warp) (`PROG-ISA-WARP`)
    - [warp-level matrix instructions](#prog-isa-matrix) (`PROG-ISA-MATRIX`)
    - [synchronization, copy and tcgen05 forms](#prog-isa-sync-forms) (`PROG-ISA-SYNC-FORMS`)
    - [the decoded forms of linear copies](#prog-isa-copy) (`PROG-ISA-COPY`)
- [Instruction tables](#instruction-tables)
  - [Integer and bit instructions](#integer-and-bit-instructions)
  - [Register moves](#register-moves)
  - [Conversions](#conversions)
  - [Memory access and addresses](#memory-access-and-addresses)
  - [Warp collectives](#warp-collectives)
  - [Control flow](#control-flow)
  - [Floating-point arithmetic](#floating-point-arithmetic)
  - [Barriers](#barriers)
  - [Memory fences](#memory-fences)
  - [Mbarrier objects](#mbarrier-objects)
  - [Asynchronous copies](#asynchronous-copies)
  - [Tcgen05](#tcgen05)
  - [Cluster launch control](#cluster-launch-control)
  - [Other instructions](#other-instructions)
  - [Warp-level matrix instructions](#warp-level-matrix-instructions)
  - [Without a representation](#without-a-representation)
  - [Special registers](#special-registers)
  - [Not decoded](#not-decoded)

## Concepts

The definitions a reader needs to follow the rules. Each text is the Lean doc comment, and each entry links to its Lean source.

### Types and qualifiers

The qualifier vocabulary that the instruction families share.

<a id="c-dtype"></a>
#### `DType`

*inductive*

A data type of an instruction.

- `pred`
- `int`
- `float`
- `packed`

[Lean source: `Core/Isa/Types.lean` L102-L108](../../Core/Isa/Types.lean#L102-L108)

<a id="c-statespace"></a>
#### `StateSpace`

*inductive*

The state-space qualifier of a memory instruction (§5.1): `param` is the kernel parameter
space (`.param::entry`) and `paramFunc` the device function parameter space (`.param::func`).

- `global`
- `shared`
- `param`
- `paramFunc`
- `const`

[Lean source: `Core/Isa/Types.lean` L134-L143](../../Core/Isa/Types.lean#L134-L143)

<a id="c-sem"></a>
#### `Sem`

*inductive*

The memory semantics of an access (§8.4): `.weak` (also when absent on `ld`/`st`),
`.relaxed`, `.acquire`, `.release`, `.acq_rel` or `.volatile`. The `.mmio` qualifier is a separate
flag of the access (`MemAccess.mmio`) and keeps the access's `.sem`.

- `weak`
- `relaxed`
- `acquire`
- `release`
- `acqRel`
- `volatile`

[Lean source: `Core/Isa/Types.lean` L145-L150](../../Core/Isa/Types.lean#L145-L150)

<a id="c-cmp"></a>
#### `Cmp`

*inductive*

A comparison operator (§9.3.1.1, Table 23): the signed or untyped ones and the unsigned ones
`lo`, `ls`, `hi`, `hs`.

- `eq`
- `ne`
- `lt`
- `le`
- `gt`
- `ge`
- `lo`
- `ls`
- `hi`
- `hs`

[Lean source: `Core/Isa/Types.lean` L75-L79](../../Core/Isa/Types.lean#L75-L79)

### Family representations

One representation for each family of instructions, and the function that names the rule of an instruction.

<a id="c-ruleid"></a>
#### `RuleId`

*inductive*

A contract entry that gives instructions their semantics.

- `threadInt`
- `threadMove`
- `threadCvt`
- `threadFloat`
- `threadCvta`
- `threadSharedPointer`
- `threadAccess`
- `threadAtomic`
- `threadPrefetch`
- `threadCachePolicy`
- `threadNoEffect`
- `threadShfl`
- `threadVote`
- `threadElect`
- `threadWarpBar`
- `threadRedux`
- `threadMatch`
- `threadActivemask`
- `threadBranch`
- `threadTensorMapPrefetch`
- `threadBar`
- `clusterBarrier`
- `threadSetMaxNReg`
- `threadTensorIssue`
- `threadTensorPrefetch`
- `threadTensorStore`
- `threadClc`
- `threadTma`
- `threadCpAsync`
- `threadAsyncStore`
- `threadTcCommit`
- `threadTc`
- `threadRun`
- `threadSreg`
- `threadMatrix`
- `threadMma`
- `threadFence`

[Lean source: `Core/Isa/Rule.lean` L35-L74](../../Core/Isa/Rule.lean#L35-L74)

<a id="c-intinstr"></a>
#### `IntInstr`

*structure*

An integer instruction: the operation, the data type (`.type`, or the source type of `set`
and `slct`), `.sat`, the destinations (`none` for the sink `_`) and the sources in operand
order.

- `op`
- `ty`
- `sat`
- `dsts`
- `srcs`

[Lean source: `Core/Isa/Int.lean` L126-L135](../../Core/Isa/Int.lean#L126-L135)

<a id="c-floatinstr"></a>
#### `FloatInstr`

*structure*

A floating instruction: the operation, its type (`.type`, the destination type of a mixed
form or of `set`, or the source type of `setp` and of a `set` with a floating source), the source
types of a mixed form in operand order (`[]` when every source has type `ty`), the integer source
type of a `set` with an integer `.stype`, the rounding modifier as written, the mode, the
qualifiers, the destinations (`none` for the sink `_`) and the sources in operand order.

- `op`
- `ty`
- `srcTys`
- `cmpTy`
- `rnd`
- `mode`
- `ftz`
- `sat`
- `relu`
- `oob`
- `nanMod`
- `xorsign`
- `absMod`
- `dsts`
- `srcs`

[Lean source: `Core/Isa/Float.lean` L111-L132](../../Core/Isa/Float.lean#L111-L132)

<a id="c-moveinstr"></a>
#### `MoveInstr`

*structure*

A register move: its form, the type of the whole value, destinations (`none` for `_`) and
sources (the elements of a pack, low first).

- `kind`
- `ty`
- `dsts`
- `srcs`

[Lean source: `Core/Isa/Move.lean` L51-L58](../../Core/Isa/Move.lean#L51-L58)

<a id="c-cvtinstr"></a>
#### `CvtInstr`

*structure*

A conversion: destination and source types, rounding, qualifiers, the destination register,
how the result fills a destination register wider than its type, and the sources in operand
order.

- `dst`
- `src`
- `rnd`
- `ftz`
- `sat`
- `relu`
- `satfinite`
- `pzo`
- `scaled`
- `pack`
- `d`
- `ext`
- `srcs`

[Lean source: `Core/Isa/Cvt.lean` L113-L130](../../Core/Isa/Cvt.lean#L113-L130)

<a id="c-memaccess"></a>
#### `MemAccess`

*structure*

A memory access.

- `kind`
- `space`
- `sem`
- `scope`
- `elem`
- `vec`
- `ext`
- `nc`
- `noftz`
- `hints`
- `addr`
- `dsts`
- `srcs`
- `mmio`: The `.mmio` qualifier of `ld.mmio` and `st.mmio`; the access keeps its `.sem`.

[Lean source: `Core/Isa/Mem.lean` L180-L197](../../Core/Isa/Mem.lean#L180-L197)

<a id="c-addrinstr"></a>
#### `AddrInstr`

*inductive*

An address conversion or query.

- `cvta`: `cvta{.to}.space.size d, a`; `toSpace` for `.to`.
- `mapa`: `mapa{.space}.size d, a, b`; `generic` without `.shared::cluster`.
- `isspacep`: `isspacep.space p, a`.
- `getctarank`: `getctarank{.space}.size d, a`; `generic` without `.shared::cluster`.
- `prefetch`: `prefetch{.space}.level [a]` and `prefetch.global.L2::evict_* [a]` (`space` none for a generic address), `prefetch{.global}.L1::32B.valid_addr [a]` (`validAddr`) and `prefetchu.L1 [a]` (`uniform`).
- `applypriority`: `applypriority{.global}.L2::evict_normal [a], 128`; `global` for `.global`.

[Lean source: `Core/Isa/Mem.lean` L213-L229](../../Core/Isa/Mem.lean#L213-L229)

<a id="c-warpkind"></a>
#### `WarpKind`

*inductive*

The kind of a warp collective.

- `shfl`
- `vote`: `neg` for a complemented predicate source `!a`.
- `match_`
- `redux`
- `activemask`
- `elect`
- `barWarp`

[Lean source: `Core/Isa/Warp.lean` L69-L79](../../Core/Isa/Warp.lean#L69-L79)

<a id="c-warpinstr"></a>
#### `WarpInstr`

*structure*

A warp collective: kind, data type (none for `elect.sync` and `bar.warp.sync`), destinations
(`none` for `_`), sources and member mask (none for `activemask`).

- `kind`
- `ty`
- `dsts`
- `srcs`
- `mask`

[Lean source: `Core/Isa/Warp.lean` L81-L89](../../Core/Isa/Warp.lean#L81-L89)

## Rules

Each rule is a contract block of the Lean source. Its statement says what the rule means for programs. The source quotes the PTX ISA 9.5 text the rule rests on, and the direction says how the rule relates to that text.

### Types and operands



<a id="prog-isa-types"></a>
#### data types and shared qualifiers (`PROG-ISA-TYPES`)

*Rule* · [Lean comment: `Core/Isa/Types.lean` L16-L44](../../Core/Isa/Types.lean#L16-L44)

An instruction's data type is a predicate, an integer type of a kind and a width, a floating-point type, or a packed type of several elements. State spaces, memory semantics, comparison operators and scopes are the qualifiers the manual lists for them, and `FloatFmt` is the set of floating formats whose payloads the model represents as numbers.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`FloatFmt`](../../Core/Isa/Types.lean#L47-L50) ([concept](program.md#c-floatfmt)), [`FloatFmt.bytes`](../../Core/Isa/Types.lean#L52-L56), [`FloatRound`](../../Core/Isa/Types.lean#L58-L62), [`Space`](../../Core/Isa/Types.lean#L64-L68) ([concept](program.md#c-space)), [`IType`](../../Core/Isa/Types.lean#L70-L73), [`Cmp`](../../Core/Isa/Types.lean#L75-L79) ([concept](#c-cmp)), [`MbarScope`](../../Core/Isa/Types.lean#L81-L85) ([concept](memory.md#c-mbarscope)), [`FType`](../../Core/Isa/Types.lean#L87-L90), [`FType.fmt?`](../../Core/Isa/Types.lean#L92-L100), [`DType`](../../Core/Isa/Types.lean#L102-L108) ([concept](#c-dtype)), [`DType.width`](../../Core/Isa/Types.lean#L110-L122), [`DType.kind?`](../../Core/Isa/Types.lean#L124-L127), [`SharedWindow`](../../Core/Isa/Types.lean#L129-L132), [`StateSpace`](../../Core/Isa/Types.lean#L134-L143) ([concept](#c-statespace)), [`Sem`](../../Core/Isa/Types.lean#L145-L150) ([concept](#c-sem)), [`BoolOp`](../../Core/Isa/Types.lean#L152-L155)

<details>
<summary>Details for reviewers</summary>

- §5.2.1: "Fundamental Type Specifiers"
- §5.2.5 (packed data types)
- §9.3.1.1 (Table 23, integer comparison operators): "eq, ne, lt, le, gt, ge"
- §9.3.1.1 (Table 23, integer comparison operators): "lo, ls, hi, hs"
- §5.1 (state spaces)
- §8.4 (memory operation qualifiers)
- §9.7.7.2 (setp `.BoolOp`)

**Applies:** The qualifier values of every decoded instruction

**Premises:** The value is one the instruction's syntax lists.

**Effect:** Representation only; the rules of each family read these values. `DType.int k w` is `.b<w>`, `.u<w>` or `.s<w>`; `DType.packed e n` is the packed type of `n` elements of type `e` (`.f16x2` is `packed (float f16) 2`). `FType` lists every floating type name of an instruction; `FType.fmt?` gives the payload format of the model (THREAD-BITS), which exists for `.f16`, `.bf16`, `.f32`, `.f64`, `.e4m3` and `.e5m2` only.

</details>

<a id="prog-operand"></a>
#### operands and their resolution (`PROG-OPERAND`)

*Rule* · [Lean comment: `Core/Source/Operand.lean` L18-L51](../../Core/Source/Operand.lean#L18-L51)

An operand is a register, an integer or binary32 literal, a special register, the address of a `.shared` variable or the address of a kernel parameter. A register operand must be declared with the width the instruction expects, a literal is read with its §4.5.1 type, and a special register has the width of its declared type. A `.pred` source is a predicate register, the `.pred` special register `%is_explicit_cluster`, or an integer constant (§4.5.3: "zero values are False and non-zero values are True"). A `%perctamemory` register is an operand only in a kernel with a `.minperctamemory` directive.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: every definition of [`Core/Source/Operand.lean`](../../Core/Source/Operand.lean).

<details>
<summary>Details for reviewers</summary>

- §4.5.1 (integer constants: hexadecimal, octal, binary, decimal): "Integer constants are 64-bits in
    size and are either signed or unsigned, i.e., every integer constant has type .s64 or .u64"
- §4.5.1 (integer constants: hexadecimal, octal, binary, decimal): "Integer literals may be followed
    immediately by the letter U to indicate that the literal is unsigned."
- §4.5.5: "Unary plus and minus preserve the type of the input operand."
- §4.5.2 (0f binary32 constants)
- §9.4 Table 26 (an `.sX`/`.uX` operand of an `.fX` instruction type is): "invalid"
- §6.4.3: "when specified as destination operand, all elements in vector expression must be unique,
    otherwise behavior is undefined"
- §9.3: "predicate registers can be declared as .reg .pred p, q, r;"
- §10.11: ".sreg .pred %is_explicit_cluster;"
- §11.5.10: "Only entry functions specifying this directive are allowed to use special registers
    %perctamemoryoffset or %perctamemorysize ."
- §6.4.1: "[var+immOff] a sum of address of addressable variable var containing a byte address plus
    a constant integer byte offset (signed, 32-bit)."
- §4.5.3: "For predicate-type data initializers and instruction operands, integer constants are
    interpreted as in C, i.e., zero values are False and non-zero values are True ."

**Effect:** The literal rules, register numbering and rejections are those PROG-DECODE states; this file holds the functions that apply them to one operand.

</details>

<a id="prog-isa-sreg"></a>
#### special registers (`PROG-ISA-SREG`)

*Rule* · [Lean comment: `Core/Isa/SReg.lean` L17-L44](../../Core/Isa/SReg.lean#L17-L44)

A special register operand is one of the predefined registers of §10, with its component `.x`, `.y` or `.z` for the vector registers, and it has the width of its declared type. Any other name is an ordinary register name.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`Dim`](../../Core/Isa/SReg.lean#L47-L50), [`SRegName`](../../Core/Isa/SReg.lean#L52-L62), [`SReg`](../../Core/Isa/SReg.lean#L64-L68) ([concept](program.md#c-sreg)), [`SReg.width`](../../Core/Isa/SReg.lean#L70-L75), [`SReg.table`](../../Core/Isa/SReg.lean#L77-L296), [`SReg.bytesEq`](../../Core/Isa/SReg.lean#L298-L302), [`SReg.lookup`](../../Core/Isa/SReg.lean#L304-L307), [`SReg.ofName?`](../../Core/Isa/SReg.lean#L309-L313), [`SRegKind`](../../Core/Isa/SReg.lean#L315-L320), [`SReg.kind`](../../Core/Isa/SReg.lean#L322-L342), [`SReg.varying`](../../Core/Isa/SReg.lean#L344-L346), [`SReg.perCtaMemory`](../../Core/Isa/SReg.lean#L348-L353), [`SReg.rule`](../../Core/Isa/SReg.lean#L355-L360)

<details>
<summary>Details for reviewers</summary>

- §10 (Special Registers): "Syntax (predefined) .sreg .v4 .u32 %tid; // thread id vector .sreg .u32
    %tid.x, %tid.y, %tid.z; // thread id components"
- §10 (Special Registers): ".sreg .pred %is_explicit_cluster;"
- §10 (Special Registers): ".sreg .u64 %clock64;"
- §10 (Special Registers): ".sreg .u64 %globaltimer;"
- §10 (Special Registers): ".sreg .u64 %gridid;"
- §10 (Special Registers): ".sreg .u64 %current_graph_exec;"
- §10 (Special Registers): ".sreg .u64 %perctamemoryoffset;"
- §10 (Special Registers): ".sreg .b32 %envreg<32>;"

**Applies:** Every special register operand of a decoded instruction

**Premises:** The name is spelled as in §10.

**Effect:** Representation; `SReg.kind` says how THREAD-SREG gives a register its value, and `SReg.rule` names THREAD-SREG exactly for the registers that have a kind. A `%perctamemory` register decodes only in a kernel with a `.minperctamemory` directive (PROG-DECODE).

</details>

### Instruction families



<a id="prog-rule-id"></a>
#### the contract ID of the rule of an instruction (`PROG-RULE-ID`)

*Rule* · [Lean comment: `Core/Isa/Rule.lean` L14-L32](../../Core/Isa/Rule.lean#L14-L32)

Each instruction family has a function that names the contract entry whose rule gives an instruction its semantics, or none when the model has no rule for it, and `Op.rule` (PROG-INSTR-RULE) extends it to every instruction. The semantic functions are defined through it or proved equal to its case split, so an instruction without a named rule has no semantics.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`RuleId`](../../Core/Isa/Rule.lean#L35-L74) ([concept](#c-ruleid)), [`RuleId.id`](../../Core/Isa/Rule.lean#L76-L114)

<details>
<summary>Details for reviewers</summary>

- none (dispatch)

**Applies:** Every decoded instruction

**Effect:** Selects the rule that `execLocal` (THREAD-LOCAL) or `eventTmpl` (THREAD-RUN) applies; no rule selected means `noRule`.

</details>

<a id="prog-instr-rule"></a>
#### the rule of every instruction (`PROG-INSTR-RULE`)

*Rule* · [Lean comment: `Core/Source/Instr.lean` L406-L434](../../Core/Source/Instr.lean#L406-L434)

An instruction of a family has the rule that the family's `rule` function names (PROG-RULE-ID). `bra` and `brx.idx` have THREAD-BRANCH, a tensormap prefetch THREAD-TENSORMAP-PREFETCH, a CTA barrier THREAD-BAR, a cluster barrier OBJ-CLUSTER-BARRIER-SYNC, `setmaxnreg` THREAD-SETMAXNREG, a tensor load THREAD-TENSOR-ISSUE, a tensor-data or linear prefetch THREAD-TENSOR-PREFETCH, a tensor store or reduction and the bulk-group commit and wait THREAD-TENSOR-STORE, the cluster launch control instructions THREAD-CLC-QUERY, the mbarrier instructions, the mbarrier-initialization fence, `cp.async.bulk` and `cp.reduce.async.bulk` THREAD-TMA, `st.async` and `red.async` THREAD-ASYNC-STORE, the thread and proxy fences THREAD-FENCE, `cp.async`, its group commit and wait and `cp.async.mbarrier.arrive` THREAD-CP-ASYNC, `tcgen05.commit` THREAD-TC-COMMIT, `tcgen05.mma` the rule `TcMmaInstr.rule` names (PROG-ISA-TC-MMA), every other `tcgen05` instruction THREAD-TC, and `ret`, `exit` and `trap` THREAD-RUN. `Op.unmodeled` has no rule.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`Op.rule`](../../Core/Source/Instr.lean#L437-L469)

<details>
<summary>Details for reviewers</summary>

- none (dispatch)

**Applies:** Every decoded instruction

**Effect:** `execLocal` dispatches through it (THREAD-LOCAL), and `eventTmpl` equals the template of the rule it names, or `ub noRule` without one (`eventTmpl_rule`, THREAD-RUN). The instruction tables of the documentation take each instruction's status from it.

</details>

<a id="prog-isa-int"></a>
#### integer and bit instructions (`PROG-ISA-INT`)

*Rule* · [Lean comment: `Core/Isa/Int.lean` L18-L78](../../Core/Isa/Int.lean#L18-L78)

An integer instruction is its operation with the operation's own qualifiers, its data type, its saturation qualifier, its destination registers and its source operands. Every entry of the `int` family decodes to it; operands are resolved at the widths of their table types.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`MulMode`](../../Core/Isa/Int.lean#L81-L84), [`PrmtMode`](../../Core/Isa/Int.lean#L86-L89), [`IntOp`](../../Core/Isa/Int.lean#L91-L124), [`IntInstr`](../../Core/Isa/Int.lean#L126-L135) ([concept](#c-intinstr)), [`Decode.IntInstr.cmp?`](../../Core/Isa/Int.lean#L139-L145), [`Decode.IntInstr.boolOp?`](../../Core/Isa/Int.lean#L147-L153), [`Decode.ikind`](../../Core/Isa/Int.lean#L155-L159), [`Decode.IntInstr.ofRaw`](../../Core/Isa/Int.lean#L161-L238), [`DType.intLanes?`](../../Core/Isa/Int.lean#L242-L247), [`Cmp.intOk`](../../Core/Isa/Int.lean#L249-L253), [`IntInstr.rule`](../../Core/Isa/Int.lean#L255-L314)

<details>
<summary>Details for reviewers</summary>

- §9.7.1: "add{.sat}.type2 d, a, b;"
- §9.7.1: "mul.mode.type d, a, b;"
- §9.7.1: ".mode = { .hi, .lo, .wide };"
- §9.7.1: "mad.mode.type d, a, b, c;"
- §9.7.1: "min{.relu}.type2 d, a, b;"
- §9.7.7.2: "setp.CmpOp{.ftz}.type p[|q], a, b;"
- §9.7.7.2: "setp.CmpOp.BoolOp{.ftz}.type p[|q], a, b, {!}c;"
- §9.7.7.3: "selp.type d, a, b, c;"
- §9.7.9: "and.type d, a, b;"
- §9.7.9: "shl.type d, a, b;"
- §9.7.9: "shr.type d, a, b;"
- §9.7.9: "lop3.b32 d, a, b, c, immLut;"
- §9.7.9: "shf.l.mode.b32 d, a, b, c;"
- §9.7.1.5: "clmad.mode.u64 d, a, b, c;"
- §9.7.1.24: "dp4a.atype.btype d, a, b, c;"
- §9.7.1.25: "dp2a.mode.atype.btype d, a, b, c;"
- §9.7.2: "add.cc.type d, a, b;"
- §9.7.2: "addc{.cc}.type d, a, b;"
- §9.7.2: "sub.cc.type d, a, b;"
- §9.7.2: "subc{.cc}.type d, a, b;"
- §9.7.2: "mad{.hi,.lo}.cc.type d, a, b, c;"
- §9.7.2: "madc{.hi,.lo}{.cc}.type d, a, b, c;"
- §9.7.2: ".type = { .u32, .s32, .u64, .s64 };"
- §9.7.9.6: "immLut is an integer constant that can take values from 0 to 255"
- §9.7.10.7: "prmt.b32{.mode} d, a, b, c;"
- §9.7.7.1: "The signed and unsigned comparison operators are eq , ne , lt , le , gt , ge . For
    unsigned values, the comparison operators lo , ls , hi , and hs for lower, lower-or-same,
    higher, and higher-or-same may be used instead of lt , le , gt , ge , respectively. The untyped,
    bit-size comparisons are eq and ne ."

**Applies:** Every instruction of the `int` family

**Premises:** The instruction is recognized by `Grammar.parse`; its registers are declared at the widths of the operand types.

**Effect:** Representation; `IntInstr.rule` selects THREAD-INT for the integer forms of the manual's syntax, THREAD-MOVE for `selp` and `slct`, and no rule for combinations outside the syntax. The model does not decode a negated predicate source `!c`, an `immLut` outside 0 to 255 is rejected, and so is a `setp` whose `p` and `q` are both the sink (§9.7.7.2: "The sink symbol ‘_’ may be used in place of any one of the destination operands."). `slct.ftz` keeps `.ftz` in `IntOp.slct`. `IntInstr.rule` checks each operation's types, qualifiers and destinations against its syntax: `.sat` only where the manual allows it, `.relu` only on the signed types it lists, comparison operators by `Cmp.intOk`, one destination except the `p|q` pair of `setp` (two distinct registers, or one register and the sink) and the `d|p` pair of `lop3.BoolOp`. The extended-precision instructions of §9.7.2 are their own entries of the grammar (`Tools/isa/extra.py`), since the TIRx table has none of them. They decode to `IntOp.addCarry`, `IntOp.subCarry` and `IntOp.madCarry`, which record whether the instruction reads the carry flag (`addc`, `subc`, `madc`) and whether it writes it (`.cc`). The grammar requires the `.hi` or `.lo` mode of `mad.cc` and `madc`, because their Semantics sections define only these two variants, so a form without a mode is not recognized.

</details>

<a id="prog-isa-float"></a>
#### floating-point instructions (`PROG-ISA-FLOAT`)

*Rule* · [Lean comment: `Core/Isa/Float.lean` L18-L67](../../Core/Isa/Float.lean#L18-L67)

A floating instruction is its operation, its type, the source types of a mixed-precision form, its rounding modifier as written, whether it is approximate, its `.ftz`, `.sat`, `.relu`, `.oob`, `.NaN`, `.xorsign` and `.abs` qualifiers, its destinations and its sources. Every entry of the `float` family decodes to it; operands are resolved at the widths of their table types.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`TestProp`](../../Core/Isa/Float.lean#L70-L73), [`FCmp`](../../Core/Isa/Float.lean#L75-L82), [`FOp`](../../Core/Isa/Float.lean#L84-L92), [`FTy`](../../Core/Isa/Float.lean#L94-L98), [`FTy.ofDType?`](../../Core/Isa/Float.lean#L100-L104), [`FMode`](../../Core/Isa/Float.lean#L106-L109), [`FloatInstr`](../../Core/Isa/Float.lean#L111-L132) ([concept](#c-floatinstr)), [`Decode.FloatInstr.cmp?`](../../Core/Isa/Float.lean#L136-L144), [`Decode.FloatInstr.fty`](../../Core/Isa/Float.lean#L146-L150), [`Decode.FloatInstr.ofRaw`](../../Core/Isa/Float.lean#L152-L232), [`FloatInstr.rule`](../../Core/Isa/Float.lean#L236-L245)

<details>
<summary>Details for reviewers</summary>

- §9.7.3.3: "add{.rnd}{.ftz}{.sat}.f32 d, a, b; add{.rnd}{.ftz}.f32x2 d, a, b; add{.rnd}.f64 d, a,
    b;"
- §9.7.3.6: "fma.rnd{.ftz}{.sat}.f32 d, a, b, c; fma.rnd{.ftz}.f32x2 d, a, b, c; fma.rnd.f64 d, a,
    b, c;"
- §9.7.3.8: "div.approx{.ftz}.f32 d, a, b; // fast, approximate divide div.full{.ftz}.f32 d, a, b;
    // full-range approximate divide div.rnd{.ftz}.f32 d, a, b; // IEEE 754 compliant rounding"
- §9.7.3.11: "min{.ftz}{.NaN}{.xorsign.abs}.f32 d, a, b; min{.ftz}{.NaN}{.abs}.f32 d, a, b, c;
    min.f64 d, a, b;"
- §9.7.3.1: "testp.op.type p, a; // result is .pred .op = { .finite, .infinite, .number,
    .notanumber, .normal, .subnormal };"
- §9.7.7.1: "set.CmpOp{.ftz}.dtype.stype d, a, b; set.CmpOp.BoolOp{.ftz}.dtype.stype d, a, b,
    {!}c;"
- §9.7.4.4: "fma.rnd{.ftz}{.sat}.f16 d, a, b, c; fma.rnd{.ftz}{.sat}.f16x2 d, a, b, c;
    fma.rnd{.ftz}.relu.f16 d, a, b, c;"
- §9.7.5.1: "add{.rnd}{.sat}.cdtype.atype d, a, c; add{.rnd}.dtype2.atype2.ctype2 d, a, c;
    add.rz.ftz.dtype3.atype3.ctype2 d, a, c; add.rz.dtype4.atype3.ctype2 d, a, c;"
- §9.7.5.3: "fma{.rnd}{.sat}.cdtype.abtype d, a, b, c; fma{.rnd}.dtype.atype.btype.ctype d, a, b,
    c;"
- §9.7.5.4: "mul.ftz.rz.dtype1.atype1.ctype1 d, a, c; mul.rz.dtype2.atype1.ctype1 d, a, c;
    mul.dtype3.atype2.ctype2 d, a, c; mul.dtype4.atype3.ctype3 d, a, c;"
- §9.7.3: "mad.f32 and fma.f32 are the same."

**Applies:** Every instruction of the `float` family

**Premises:** The instruction is recognized by `Grammar.parse`; its registers are declared at the widths of the operand types.

**Effect:** Representation; `FloatInstr.rule` selects THREAD-FLOAT for every form except `div.full`, the mixed `fma` with a packed half `.atype` and the `mul` forms that mix `.f16x2` and `.bf16x2`, which have no rule. The rounding modifier is kept as written (`none` when omitted), since an omitted modifier lets the code optimizer contract `mul` and `add` (THREAD-FLOAT). `mad` is its own operation with the rule of `fma`. A mixed-precision form records the types of its sources in operand order (`srcTys`); every other form has `srcTys = []`. A `set` with an integer source type records it (`cmpTy`) and takes the destination format as its type. The model does not decode a negated predicate source `!c`, a comparison operator `lo`, `ls`, `hi` or `hs` with a floating source type, or `.relu` on a floating `min` or `max`, which the manual does not define; each fails decoding. A `0d` constant or a decimal floating literal does not decode either (`Opnd` holds `0f` constants only).

</details>

<a id="prog-isa-move"></a>
#### register moves (`PROG-ISA-MOVE`)

*Rule* · [Lean comment: `Core/Isa/Move.lean` L17-L43](../../Core/Isa/Move.lean#L17-L43)

A move is a scalar `mov`, a packing `mov` that joins source elements into one register, or an unpacking `mov` that splits one register into destination elements, with its data type, destinations and sources. Every entry of the `move` family decodes to it.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`MoveKind`](../../Core/Isa/Move.lean#L46-L49), [`MoveInstr`](../../Core/Isa/Move.lean#L51-L58) ([concept](#c-moveinstr)), [`Decode.MoveInstr.ofRaw`](../../Core/Isa/Move.lean#L62-L77), [`MoveInstr.rule`](../../Core/Isa/Move.lean#L81-L99)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.3: "mov.type d, a;"
- §9.7.10.3: ".type = { .pred, .b16, .b32, .b64, .u16, .u32, .u64, .s16, .s32, .s64, .f32, .f64 };"
- §9.7.10.4: "mov.type d, a; .type = { .b16, .b32, .b64, .b128 };"
- §9.7.10.4: "pack two 16-bit elements into .b32 d = a.x | (a.y << 16)"
- §9.7.10.4: "When destination operand d is a vector register, the sink symbol '_' may be used for
    one or more elements provided that at least one element is a scalar register."

**Applies:** Every instruction of the `move` family

**Premises:** The instruction is recognized by `Grammar.parse`; its registers are declared at the widths of the operand types.

**Effect:** Representation; `MoveInstr.rule` selects THREAD-MOVE for the scalar moves of every type of the syntax, and for the packing and unpacking of two or four elements, and no rule otherwise. The type of a pack or unpack is the type of the whole register (`.b32` for `{.b16, .b16}`). A destination of an unpack may be the sink `_`, and an unpack whose destinations are all sinks is rejected; the named destinations are distinct (§6.4.3).

</details>

<a id="prog-isa-cvt"></a>
#### conversions (`PROG-ISA-CVT`)

*Rule* · [Lean comment: `Core/Isa/Cvt.lean` L18-L100](../../Core/Isa/Cvt.lean#L18-L100)

A conversion is its destination and source types, its rounding modifier, its `.ftz`, `.sat`, `.relu`, `.satfinite` and `.pzo` qualifiers, whether it is scaled or a `cvt.pack`, its destination register with the extension that fills a wider one, and its sources. Every entry of the `cvt` family decodes to it, and an operand of `cvt d, a` may be a register wider than its type, except for a `.bf16` operand.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`CvtRnd`](../../Core/Isa/Cvt.lean#L103-L106), [`CvtRnd.isInt`](../../Core/Isa/Cvt.lean#L108-L111), [`CvtInstr`](../../Core/Isa/Cvt.lean#L113-L130) ([concept](#c-cvtinstr)), [`Decode.CvtInstr.rnd?`](../../Core/Isa/Cvt.lean#L135-L142), [`Decode.CvtInstr.intSrc`](../../Core/Isa/Cvt.lean#L144-L155), [`Decode.CvtInstr.intDst`](../../Core/Isa/Cvt.lean#L157-L165), [`Decode.CvtInstr.floatSrcOf`](../../Core/Isa/Cvt.lean#L167-L178), [`Decode.CvtInstr.floatDstOf`](../../Core/Isa/Cvt.lean#L180-L190), [`Decode.CvtInstr.srcOf`](../../Core/Isa/Cvt.lean#L192-L197), [`Decode.CvtInstr.ofRaw`](../../Core/Isa/Cvt.lean#L199-L217), [`CvtInstr.plain`](../../Core/Isa/Cvt.lean#L221-L223), [`CvtInstr.widens`](../../Core/Isa/Cvt.lean#L238-L241), [`CvtInstr.narrows`](../../Core/Isa/Cvt.lean#L243-L247), [`CvtInstr.exact`](../../Core/Isa/Cvt.lean#L249-L288), [`CvtInstr.rule`](../../Core/Isa/Cvt.lean#L290-L293), [`CvtInstr.widenF16?`](../../Core/Isa/Cvt.lean#L225-L229), [`CvtInstr.packF16?`](../../Core/Isa/Cvt.lean#L231-L236)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.24: "cvt{.irnd}{.ftz}{.sat}.dtype.atype d, a;"
- §9.7.10.24: "cvt.frnd2{.relu}{.satfinite}{.pzo}.f16x2.f32 d, a, b;"
- §9.7.10.24: "A source register wider than the specified type may be used, except when the source
    operand has .bf16 or .bf16x2 format."
- §9.7.10.24: "The lower n bits corresponding to the instruction-type width are used in the
    conversion."
- §9.7.10.24: "A destination register wider than the specified type may be used, except when the
    destination operand has .bf16 , .bf16x2 or .tf32 format."
- §9.7.10.24: "The result of conversion is sign-extended to the destination register width for
    signed integers, and is zero-extended to the destination register width for unsigned, bit-size,
    and floating-point types."
- §9.7.10.25: "cvt.pack.sat.convertType.abType d, a, b;"
- §9.7.10.24: "cvt.rs{.relu}{.satfinite}.f16x2.f32 d, a, b, rbits;"
- §9.7.10.24: "cvt.rs{.relu}.satfinite.f8x4type.f32 d, {a, b, e, f}, rbits;"
- §9.7.10.24: "cvt.frnd2.satfinite{.relu}{.pzo}{.scaled::n1::ue8m0}.f8x2type.f32 d, a, b{,
    scale-factor};"
- §9.7.10.24: "cvt.rn{.relu}{.satfinite}{.scaled::n2::ue8m0}.bf16x2.f8x2type d, a{, scale-factor};"
- §9.7.10.24: "When converting from .bf16x2 , each input packed in operand a is converted to .s2f6
    value"
- §9.7.10.24: "d[15:8] = convert(a[15:8] / scale-factor[15:8]); d[7:0] = convert(a[7:0] /
    scale-factor[7:0]);"
- §5.2.3: "The internal layout of tf32 format is implementation defined."
- §9.4.1 (Table 27): "Integer source registers may be used with any appropriately-sized bit-size or
    integer instruction type."
- §9.4.1 (Table 27): "Bit-size source registers may be used with any appropriately-sized instruction
    type. The data are truncated (“chopped”) to the instruction-type size and interpreted according
    to the instruction type."
- §9.4.1 (Table 28): "Destination register size must be of equal or greater size than the
    instruction-type size."
- §9.4.1 (Table 28): "Bit-size destination registers may be used with any appropriately-sized
    instruction type."

**Applies:** Every instruction of the `cvt` family

**Premises:** The instruction is recognized by `Grammar.parse`; its registers are declared at the widths of the operand types, or wider for an operand of `cvt d, a` whose type is not `.bf16`.

**Effect:** Representation; `CvtInstr.rule` selects THREAD-CVT for the conversions that `CvtInstr.exact` lists and no rule otherwise. An integer source of `cvt d, a` may be a register or special register wider than the source type (`Decode.CvtInstr.intSrc`), whose low bits the conversion reads. An integer destination may be a register wider than the destination type, of at most 64 bits (`Decode.CvtInstr.intDst`); the conversion then records the extension `MemExt.sign` for a signed type and `MemExt.zero` otherwise, the representation `ld` uses for the same rule (PROG-ISA-MEM). A floating source of type `.f16`, `.f32` or `.f64` may be a wider register (`Decode.CvtInstr.floatSrcOf`), whose low bits the conversion reads, and a floating destination of these types may be a register wider than the type, of at most 64 bits, which the result fills zero-extended (`MemExt.zero`, `Decode.CvtInstr.floatDstOf`). A `.bf16` operand and every operand of the packed forms keep the exact width of their type. A register declaration records only a width, so the decoding accepts a wider register of any type; Table 27 and Table 28 accept only a bit-size register wider than a floating instruction type. A destination register wider than 64 bits is rejected (stricter: the tables also allow a `.b128` register). `CvtInstr.exact` lists the conversions THREAD-CVT gives a rule: every integer-to-integer conversion and `cvt.pack`; a floating-to-integer conversion with an integer rounding modifier; between `.f16`, `.bf16`, `.f32` and `.f64`, a widening without a rounding modifier (`CvtInstr.widens`), a rounding to an integral value at the same format, and a narrowing with `.rn`, `.rz`, `.rm` or `.rp` (`CvtInstr.narrows`); an integer-to-floating conversion with one of these four; two `.f32` sources to `.f16x2` or `.bf16x2` with one of these four or with `.rs`, and to `.e4m3x2`, `.e5m2x2`, `.e2m1x2`, `.e2m3x2`, `.e3m2x2`, `.ue8m0x2`, `.ue5m3x2` or `.s2f6x2` with an optional scale factor; an `.f16x2` or `.bf16x2` source to these types except `.s2f6x2`; and the widening of these types to `.f16x2` and `.bf16x2`, with a scale factor only to `.bf16x2`. The grammar requires a rounding modifier for a conversion that narrows and rejects a floating rounding modifier on one that widens. The others have no rule: a conversion to `.tf32`, whose internal layout is implementation defined; `.s2f6x2` from `.bf16x2`, whose Description converts the two `.bf16` inputs of `a` while its Semantics converts `a[15:8]` and `a[7:0]`; and `.rs` to the four-element types, whose random bit layouts the manual gives only as figures. `cvt.f32.f16` without qualifiers and `cvt.rn.f16x2.f32` have rules like the other conversions; ASM-IDEAL selects them by `CvtInstr.widenF16?` and `CvtInstr.packF16?`.

</details>

<a id="prog-isa-misc"></a>
#### cache policies, sleep and performance monitor events (`PROG-ISA-MISC`)

*Rule* · [Lean comment: `Core/Isa/Misc.lean` L19-L53](../../Core/Isa/Misc.lean#L19-L53)

A `createpolicy` is its destination register and the operands of its kind: the address and the two sizes of a range-based policy with whether `.global` is written, the optional fraction of a fraction-based policy, or the access property that `createpolicy.cvt` converts. `nanosleep` is its delay operand, `pmevent` its immediate with whether `.mask` is written, and `griddepcontrol` its action.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`PolicyKind`](../../Core/Isa/Misc.lean#L56-L65), [`MiscInstr`](../../Core/Isa/Misc.lean#L67-L74), [`Decode.MiscInstr.ofRaw`](../../Core/Isa/Misc.lean#L78-L104), [`MiscInstr.rule`](../../Core/Isa/Misc.lean#L108-L112)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.21: "cache_policy, [a], primary-size, total-size;"
- §9.7.10.21: "cache_policy{, fraction};"
- §9.7.10.21: "createpolicy.cvt.L2.b64 cache_policy, access-property;"
- §9.7.10.21: "If no state space is specified then Generic Addressing is used."
- §9.7.21.2: "nanosleep.u32 t;"
- §9.7.21.2: "t may be a register or an immediate value."
- §9.7.21.3: "pmevent (without modifier .mask ) triggers a single performance monitor event indexed
    by immediate operand a , in the range 0..15 ."
- §9.7.21.3: "Each bit in the 16-bit immediate operand a controls an event."
- §9.7.15.14: "griddepcontrol.action; .action = { .launch_dependents, .wait }"

**Applies:** `createpolicy`, `nanosleep`, `pmevent` and `griddepcontrol`

**Premises:** The instruction is recognized by `Grammar.parse`; its registers are declared at the widths of the operand types.

**Effect:** Representation; `MiscInstr.rule` selects THREAD-CACHE-POLICY for `createpolicy` and THREAD-NO-EFFECT for `nanosleep`, `pmevent` and `griddepcontrol`. The eviction priorities of `createpolicy` are not recorded, since no rule reads them (THREAD-CACHE-POLICY). A `pmevent` immediate outside 0 to 15, or a `pmevent.mask` immediate outside 16 bits, is rejected. `nanosleep` and `pmevent` are entries of the grammar's own (`Tools/isa/extra.py`), since the TIRx table has neither. The range form `createpolicy.range.fabric` is not in the table and is not recognized.

</details>

<a id="prog-isa-mem"></a>
#### memory accesses and address instructions (`PROG-ISA-MEM`)

*Rule* · [Lean comment: `Core/Isa/Mem.lean` L18-L124](../../Core/Isa/Mem.lean#L18-L124)

A memory access is its kind (load, store, atomic read-modify-write, reduction, `ldu`, read-only proxy load, `discard` or `st.bulk`), its state space (none for a generic address), memory semantics, whether it is `.mmio`, scope, element type, vector length, the extension of a narrow element into a wider destination register, `.nc`, cache hints, address, destination registers and sources. An address instruction is a `cvta`, `mapa`, `isspacep`, `getctarank`, `prefetch`, `prefetchu` or `applypriority` with its state space, width and operands. Every entry of the `mem` family decodes to one of these, except the tensormap prefetch.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`AtomOp`](../../Core/Isa/Mem.lean#L127-L130), [`MemKind`](../../Core/Isa/Mem.lean#L132-L144), [`MemExt`](../../Core/Isa/Mem.lean#L146-L151), [`CacheHints`](../../Core/Isa/Mem.lean#L153-L160), [`AddrBase`](../../Core/Isa/Mem.lean#L162-L172), [`Addr`](../../Core/Isa/Mem.lean#L174-L178), [`MemAccess`](../../Core/Isa/Mem.lean#L180-L197) ([concept](#c-memaccess)), [`MemAccess.regs`](../../Core/Isa/Mem.lean#L199-L200), [`MemAccess.locSpace?`](../../Core/Isa/Mem.lean#L202-L211), [`Decode.MemAccess.ofRaw`](../../Core/Isa/Mem.lean#L350-L426), [`Decode.MemAccess.space?`](../../Core/Isa/Mem.lean#L234-L243), [`Decode.MemAccess.scope?`](../../Core/Isa/Mem.lean#L245-L252), [`Decode.MemAccess.atomOp?`](../../Core/Isa/Mem.lean#L254-L260), [`Decode.MemAccess.addrOf`](../../Core/Isa/Mem.lean#L262-L292), [`Decode.MemAccess.loadDsts`](../../Core/Isa/Mem.lean#L294-L310), [`Decode.MemAccess.storeSrcs`](../../Core/Isa/Mem.lean#L312-L327), [`Decode.MemAccess.paramChecks`](../../Core/Isa/Mem.lean#L329-L348), [`memTypeOk`](../../Core/Isa/Mem.lean#L475-L481), [`vectorShapeOk`](../../Core/Isa/Mem.lean#L483-L486), [`MemExt.ok`](../../Core/Isa/Mem.lean#L488-L495), [`CacheHints.globalOnly`](../../Core/Isa/Mem.lean#L497-L500), [`MemAccess.baseOk`](../../Core/Isa/Mem.lean#L502-L515), [`MemAccess.weakOk`](../../Core/Isa/Mem.lean#L517-L543), [`MemAccess.strongSemOk`](../../Core/Isa/Mem.lean#L545-L569), [`MemAccess.strongOk`](../../Core/Isa/Mem.lean#L571-L576), [`MemAccess.bulkOk`](../../Core/Isa/Mem.lean#L578-L588), [`MemKind.atomOp?`](../../Core/Isa/Mem.lean#L590-L593), [`MemAccess.atomicOk`](../../Core/Isa/Mem.lean#L595-L645), [`MemAccess.atomicOk_of_vec_one`](../../Core/Isa/Mem.lean#L647-L695), [`MemAccess.rule`](../../Core/Isa/Mem.lean#L697-L717), [`AddrInstr`](../../Core/Isa/Mem.lean#L213-L229) ([concept](#c-addrinstr)), [`Decode.AddrInstr.ofRaw`](../../Core/Isa/Mem.lean#L434-L471), [`Decode.AddrInstr.width?`](../../Core/Isa/Mem.lean#L428-L432), [`AddrInstr.rule`](../../Core/Isa/Mem.lean#L719-L729)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.8: "ld{.weak}{.ss}{.cop}{.level::cache_hint}{.level::prefetch_size}{.vec}.type d,
    [a]{.unified}{, cache_policy};"
- §9.7.10.8: ".ss = { .const, .global, .local, .param{::entry, ::func}, .shared{::cta, ::cluster}
    };"
- §9.7.10.8: "A destination register wider than the specified type may be used. The value loaded is
    sign-extended to the destination register width for signed integers, and is zero-extended to the
    destination register width for unsigned and bit-size types."
- §9.7.10.8: "For ld.param::entry instruction, operand a must be a kernel parameter address,
    otherwise behavior is undefined. For ld.param::func instruction, operand a must be a device
    function parameter address, otherwise behavior is undefined."
- §9.7.10.8: "ld.mmio.sem.sys{.global}.type d, [a];"
- §9.7.10.8: ".sem = { .acquire, .relaxed };"
- §9.7.10.11 (st): "st.mmio.sem.sys{.global}.type [a], b;"
- §9.7.10.11 (st): ".sem = { .release, .relaxed };"
- §8.4.1: "For formal specification of semantics of mmio operation from Memory Consistency Model
    perspective, it is equivalent to the semantics of a strong operation."
- §9.7.10.10 (ldu): "where the address is guaranteed to be the same across all threads in the warp."
- §9.7.10.14 (st.bulk)
- §9.7.10.16 (prefetch): "The .valid_addr qualifier requires at-least 1B-wide memory location
    referred to by address a to be valid for this access. Otherwise, the behavior is undefined."
- §9.7.10.17 (applypriority): "If the specified address does not fall within the address window of
    .global state space then the behavior is undefined."
- §9.7.10.20 (discard): "Semantically, this behaves like a weak write of an unstable indeterminate
    value : reads of memory locations with unstable indeterminate values may return different bit
    patterns each time until the memory is overwritten."
- §9.7.15.5 (atom): "If the .sem qualifier is absent, .relaxed is assumed by default."
- §9.7.15.5 (atom): ".vec_16_bit = { .v2, .v4, .v8 } .vec_32_bit = { .v2, .v4 };"
- §9.7.15.5 (atom): "For atom with vector type, operands d and b are brace-enclosed vector
    expressions, size of which is equal to the size of vector qualifier."
- §9.7.15.6 (red)
- §9.7.10.23 (cvta): "When converting a generic address into a const , Kernel Function Parameters (
    .param ), global , local , or shared address, the resulting address is undefined in cases where
    the generic address does not fall within the address window of the specified state space."
- §9.7.10.26 (mapa)
- §9.7.10.22 (isspacep)
- §9.7.10.27 (getctarank)
- §9.7.10.11 (st): "A source register wider than the specified type may be used."
- §5.1.7 (`.shared` is `.shared::cta`)
- §6.4.3: "when specified as destination operand, all elements in vector expression must be unique,
    otherwise behavior is undefined"
- §5.1.6.4: "ld.param.s32 %y, [buffer+8];"

**Applies:** Every instruction of the `mem` family other than the tensormap prefetch

**Premises:** The instruction is recognized by `Grammar.parse`; its registers are declared at the widths of the operand types, except a wider value register of an integer store; a by-value parameter access lies inside the object and is aligned for every placement its declaration allows.

**Effect:** Representation; `MemAccess.rule` selects THREAD-ACCESS and THREAD-MOVE and `AddrInstr.rule` selects THREAD-CVTA, THREAD-SHARED-POINTER and THREAD-PREFETCH for the forms listed below, and no rule otherwise. `.shared` and `.shared::cta` are the same window (`.shared .cta`); `.param` and `.param::entry` are the kernel parameter space, `.param::func` the device function parameter space. An absent `.sem` is `.weak` for `ld` and `st` and `.relaxed` for `atom` and `red`. A load's destination registers have one width, the element width or a wider one (`MemExt`: zero-extended for `.b` and `.u` types, sign-extended for `.s` types; a floating element needs its own width). The value register of a `.b`, `.u` or `.s` store may be wider than the type (`storeSrcs`). Rejected at decoding: a destination vector naming a register twice or containing the sink `_`; a `ld.param` of a by-value parameter object that leaves the object or whose size does not divide the offset and the declared alignment; a `ld.param` of a scalar parameter at a nonzero offset, of a vector, at another width than the parameter's or wider than 64 bits. The rules are as follows. THREAD-ACCESS (`weakOk`) covers weak `ld` of the global, shared (`::cta`, `::cluster`), local and constant spaces and of a generic address, weak `st` of the global, shared and local spaces and of a generic address, of an element type `.b`, `.u`, `.s` of 8 to 128 bits or `.f32`, `.f64`, extended into a register of at most 64 bits; scalar, `.v2` and `.v4` of elements of at most 64 bits, `.v4` of 64-bit elements and `.v8` of 32-bit elements of a global or generic address; `ld.global.nc` scalar or vector; the eviction priorities, prefetch size and cache policy on a global or generic address; no `.lu` or `.cs` on a local load. Also (`strongOk`) the strong loads and stores of the same shapes: `.relaxed` and `.acquire` loads and `.relaxed` and `.release` stores at every scope of a global or shared space or a generic address, `.volatile` accesses of a global, shared or local space or a generic address, and scalar `.mmio` accesses at `.sys` of the global space or a generic address, `.relaxed` and `.acquire` loads and `.relaxed` and `.release` stores, which keep their `.sem` (§8.4.1: an mmio operation is a strong operation in the memory model); and (`bulkOk`) `st.bulk` of a `.shared::cta` or generic address with initial value 0. THREAD-MOVE: `ld.param` of the kernel parameter space through a parameter name or a register, extended as above. THREAD-ATOMIC (`atomicOk`): scalar `atom` and `red` of the operation and type combinations of Table 41 and Table 42 (`.b16` `cas`, `.b128` `exch` and `cas`, the floating `add` forms and the packed `.f16x2` and `.bf16x2` `add` included), of a global, shared or generic address, and vector `atom` and `red` of the vector table of §9.7.15.5 and §9.7.15.6 (`add`, `min` and `max` of `.v2`, `.v4` and `.v8` of `.f16` and `.bf16` and of `.v2` and `.v4` of `.f16x2` and `.bf16x2`, all with `.noftz`, and `add` of `.v2` and `.v4` of `.f32`), of a global or generic address, with every `.sem` the syntax allows and every `.scope`, and `atom` with `_` or with one destination register per vector element. Without a rule: `ldu` (its address must be uniform across the warp), the read-only proxy load, `discard` (an unstable indeterminate value), `.param::func` accesses (device function parameters are not modeled; an entry function's kernel parameter at a `.param::func` operand is undefined), `st.param`.

</details>

<a id="prog-isa-fence"></a>
#### thread fences and proxy fences (`PROG-ISA-FENCE`)

*Rule* · [Lean comment: `Core/Isa/Fence.lean` L10-L50](../../Core/Isa/Fence.lean#L10-L50)

A thread fence is its memory semantics and scope; `membar` is the thread fence `fence.sc` at the scope its level names. A proxy fence is its proxy kind (the alias proxy, the async proxy restricted to a state space or to all of them, the tensormap proxy, or a fabric direction) with its memory semantics and scope when it has a scope. The tensormap acquire fence keeps its address operand.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`FenceSem`](../../Core/Isa/Fence.lean#L53-L56), [`FenceSem.releases`](../../Core/Isa/Fence.lean#L58-L61), [`FenceSem.acquires`](../../Core/Isa/Fence.lean#L63-L66), [`FabricDir`](../../Core/Isa/Fence.lean#L68-L71), [`ProxyFence`](../../Core/Isa/Fence.lean#L73-L80), [`FenceInstr`](../../Core/Isa/Fence.lean#L82-L89), [`FenceInstr.rule`](../../Core/Isa/Fence.lean#L91-L92), [`Decode.FenceInstr.ofRaw`](../../Core/Isa/Fence.lean#L97-L138)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.4: "fence{.sem}.scope;"
- §9.7.15.4: ".sem = { .sc, .acq_rel, .acquire, .release };"
- §9.7.15.4: "If the optional .sem qualifier is absent, .acq_rel is assumed by default."
- §9.7.15.4: "On sm_70 and higher membar is a synonym for fence.sc 1 , and the membar levels cta ,
    gl and sys are synonymous with the fence scopes cta , gpu and sys respectively."
- §9.7.15.4: "fence.proxy.proxykind; fence.proxy.proxykind{.sem}.scope;"
- §9.7.15.4: ".scope = { .cta, .cluster, .gpu, .sys };"
- §9.7.15.4: ".proxykind = { .alias, .async, .async.global, .async.shared::{cta, cluster} };"
- §9.7.15.4: "If no state space is specified, then the memory ordering applies on all state spaces."
- §9.7.15.4: ".to_proxykind::from_proxykind = {.tensormap::generic};"
- §9.7.15.4: ".to_proxykind::from_proxykind_fabric = {.generic::fabric, .fabric::generic,
    .fabric::fabric };"
- §9.7.15.4: ".sem_fabric = { .acquire, .release };"

**Applies:** Every `fence` entry of the instruction table other than `fence.mbarrier_init`, `fence.proxy.proxykind{.sem}.scope` and `membar.{cta,gl,sys}`

**Premises:** The instruction is recognized by `Grammar.parse`.

**Effect:** Representation; `FenceInstr.rule` selects THREAD-FENCE for every form. `fence.mbarrier_init.release.cluster` keeps its own constructor `Op.fenceMbarInit` (OBJ-MBAR-INIT-PUBLICATION). `fence.proxy.proxykind{.sem}.scope`, which the instruction table leaves out, is an entry of its own (`fence_proxy_sem`, PROG-ISA-ENTRY); an absent `.sem` is `.acq_rel`, as for every fence. A proxy fence without a scope (`fence.proxy.proxykind`) has no semantics and scope; the tensormap fences have theirs, the fabric fences their `.sem_fabric` at `.sys`. The `.sync_restrict` fences (including the uni-directional `fence.proxy.async::generic` ones), `fence.alias.sync_restrict::read.release.sys` and `membar.proxy` are not entries of the instruction table or of the added entries and are not decoded.

</details>

<a id="prog-isa-warp"></a>
#### warp collectives (`PROG-ISA-WARP`)

*Rule* · [Lean comment: `Core/Isa/Warp.lean` L18-L51](../../Core/Isa/Warp.lean#L18-L51)

A warp collective is its kind with the kind's qualifiers, its data type, its destinations, its sources and its member mask. Every entry of the `warp` family decodes to it. The predicate source of `vote.sync` may be negated; no other source may.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`ShflMode`](../../Core/Isa/Warp.lean#L54-L57), [`VoteMode`](../../Core/Isa/Warp.lean#L59-L62), [`ReduxOp`](../../Core/Isa/Warp.lean#L64-L67), [`WarpKind`](../../Core/Isa/Warp.lean#L69-L79) ([concept](#c-warpkind)), [`WarpInstr`](../../Core/Isa/Warp.lean#L81-L89) ([concept](#c-warpinstr)), [`Decode.WarpInstr.ofRaw`](../../Core/Isa/Warp.lean#L94-L128), [`ReduxOp.intForm`](../../Core/Isa/Warp.lean#L132-L138), [`WarpInstr.rule`](../../Core/Isa/Warp.lean#L140-L165)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.6: "shfl.sync.mode.b32 d[|p], a, b, c, membermask;"
- §9.7.10.6: ".mode = { .up, .down, .bfly, .idx };"
- §9.7.15.10: "vote.sync.mode.pred d, {!}a, membermask;"
- §9.7.15.10: "vote.sync.ballot.b32 d, {!}a, membermask;"
- §9.7.15.11: "match.any.sync.type d, a, membermask; match.all.sync.type d[|p], a, membermask; .type
    = { .b32, .b64 };"
- §9.7.15.11: "The sink symbol ‘_’ may be used in place of any one of the destination operands."
- §9.7.15.12: "activemask.b32 d;"
- §9.7.15.13: "redux.sync.op.type dst, src, membermask; .op = {.add, .min, .max} .type = {.u32,
    .s32} redux.sync.op.b32 dst, src, membermask; .op = {.and, .or, .xor}"
- §9.7.15.15: "elect.sync d|p, membermask;"
- §9.7.15.2: "bar.warp.sync membermask;"

**Applies:** Every instruction of the `warp` family

**Premises:** The instruction is recognized by `Grammar.parse`; its registers are declared at the widths of the operand types.

**Effect:** Representation; `WarpInstr.rule` selects THREAD-SHFL for `shfl.sync`, THREAD-VOTE for `vote.sync`, THREAD-REDUX for the integer forms of `redux.sync` (`ReduxOp.intForm`), THREAD-MATCH for `match.sync`, THREAD-ACTIVEMASK for `activemask`, THREAD-ELECT for `elect.sync` and THREAD-WARP-BAR for `bar.warp.sync`. The `.f32` forms of `redux.sync` have no rule.

</details>

<a id="prog-isa-matrix"></a>
#### warp-level matrix instructions (`PROG-ISA-MATRIX`)

*Rule* · [Lean comment: `Core/Isa/Matrix.lean` L16-L68](../../Core/Isa/Matrix.lean#L16-L68)

A warp-level matrix instruction is its operation with the operation's qualifiers, its state space and address for `ldmatrix` and `stmatrix`, its destination registers and its source registers. Every `ldmatrix`, `stmatrix`, `movmatrix`, `mma` and `mma.sp` entry of the `matrix` family decodes to it. `spcompress` and `spdecompress` have no representation.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`MatrixShape`](../../Core/Isa/Matrix.lean#L71-L74), [`MatrixFmt`](../../Core/Isa/Matrix.lean#L76-L83), [`MatrixMove`](../../Core/Isa/Matrix.lean#L85-L93), [`MatrixMove.rows`](../../Core/Isa/Matrix.lean#L95-L99), [`MatrixMove.regsPerMatrix`](../../Core/Isa/Matrix.lean#L101-L105), [`MatrixMove.supported`](../../Core/Isa/Matrix.lean#L107-L115), [`MmaTypes`](../../Core/Isa/Matrix.lean#L117-L125), [`MmaBitOp`](../../Core/Isa/Matrix.lean#L127-L130), [`MmaSpec`](../../Core/Isa/Matrix.lean#L132-L145), [`MmaSpec.quad`](../../Core/Isa/Matrix.lean#L147-L149), [`MmaSpec.kc`](../../Core/Isa/Matrix.lean#L151-L152), [`MmaSpec.regBits`](../../Core/Isa/Matrix.lean#L154-L156), [`MmaSpec.elems`](../../Core/Isa/Matrix.lean#L158-L162), [`MmaSpec.regs`](../../Core/Isa/Matrix.lean#L164-L169), [`MmaSpec.supported`](../../Core/Isa/Matrix.lean#L171-L213), [`MatrixOp`](../../Core/Isa/Matrix.lean#L215-L221), [`MatrixInstr`](../../Core/Isa/Matrix.lean#L223-L232), [`Decode.MatrixInstr.mmaShape?`](../../Core/Isa/Matrix.lean#L237-L250), [`Decode.MatrixInstr.moveShape?`](../../Core/Isa/Matrix.lean#L252-L258), [`Decode.MatrixInstr.num?`](../../Core/Isa/Matrix.lean#L260-L265), [`Decode.MatrixInstr.srcsOf`](../../Core/Isa/Matrix.lean#L267-L271), [`Decode.MatrixInstr.dstsOf`](../../Core/Isa/Matrix.lean#L273-L278), [`Decode.MatrixInstr.ofRaw`](../../Core/Isa/Matrix.lean#L280-L333), [`MatrixInstr.rule`](../../Core/Isa/Matrix.lean#L337-L359)

<details>
<summary>Details for reviewers</summary>

- §9.7.16.5.15: "ldmatrix.sync.aligned.shape.num{.trans}{.ss}.type r, [p];
    ldmatrix.sync.aligned.m8n16.num{.ss}.dst_fmt.src_fmt r, [p];
    ldmatrix.sync.aligned.m16n16.num.trans{.ss}.dst_fmt.src_fmt r, [p];
    ldmatrix.sync.aligned.m8n16.num{.ss}.dtype.ctype r, [p];"
- §9.7.16.5.15: "When .shape is .m16n16 , only .x1 and .x2 are valid values for .num ."
- §9.7.16.5.15: "However, for 16x16 matrices, .trans is mandatory."
- §9.7.16.5.16: "stmatrix.sync.aligned.shape.num{.trans}{.ss}.type [p], r;"
- §9.7.16.5.16: ".m16n8 shape is valid only for .b8 type."
- §9.7.16.5.16: "However, for 16x8 matrices, .trans is mandatory."
- §9.7.16.5.17: "movmatrix.sync.aligned.shape.trans.type d, a;"
- §9.7.16.5.14: "mma.sync.aligned.m8n8k4.alayout.blayout.dtype.f16.f16.ctype d, a, b, c;"
- §9.7.16.5.14: "Single bit: mma.sync.aligned.shape.row.col.s32.b1.b1.s32.bitOp.popc d, a, b, c;"
- §9.7.16.6.3: "mma.spvariant.sync.aligned.m16n8k16.row.col.dtype.f16.f16.ctype d, a, b, c, e, f;"
- §9.7.16.6.3: "Operand e is a 32-bit integer and operand f is a 32-bit integer constant with values
    in the range 0..3."

**Applies:** Every instruction of the `matrix` family

**Premises:** The instruction is recognized by `Grammar.parse`; its registers are declared at the widths of the operand types.

**Effect:** Representation; `MatrixInstr.rule` selects THREAD-MATRIX for the `ldmatrix`, `stmatrix` and `movmatrix` forms the manual's syntax lines give and THREAD-MMA-SYNC for `mma` and `mma.sp`. A matrix move (`MatrixMove`) records whether it stores, its shape, the number of matrices, `.trans` and the element format: `.b16`, `.b8`, the expanded `.b8x16` with its packed source format, or `.s8.s4`. An MMA (`MmaSpec`) records its shape, the layouts of A and B, the element types of A, B, C and D with the rounding modifier of `.f64`, `.satfinite`, the single-bit operation and, for `mma.sp`, whether the metadata is ordered and the sparsity selector `f`. The destination and source registers are listed in operand order: an MMA's sources are A, B and C followed by the metadata `e`. `MatrixInstr.rule` gives a rule only to the forms of the manual's syntax lines, which are narrower than the table: `ldmatrix` of `.b16` at `.m8n8`, of `.b8` at `.m16n16` with `.trans`, of `.b8x16` at `.m8n16` without `.trans` and at `.m16n16` with `.trans`; `stmatrix` of `.b16` at `.m8n8` and of `.b8` at `.m16n8` with `.trans`; `movmatrix`; and every `mma` and `mma.sp` shape and type of the table (`MmaSpec.supported`), each with the register counts of its fragments (`MmaSpec.regs`). `ldmatrix.m8n16.s8.s4` has no rule: the text gives neither the number of bytes of a source row nor the order of the 4-bit elements in it.

</details>

<a id="prog-isa-sync-forms"></a>
#### synchronization, copy and tcgen05 forms (`PROG-ISA-SYNC-FORMS`)

*Rule* · [Lean comment: `Core/Source/DecodeOps.lean` L19-L74](../../Core/Source/DecodeOps.lean#L19-L74)

A recognized instruction of the `barrier`, `mbarrier`, `fence`, `async`, `tc`, `clc` and `misc` families decodes to its own constructor of `Op` when its qualifiers form one of the forms listed below, and to `Op.unmodeled` otherwise. The operands of a listed form are resolved at the widths of their types, and an operand that cannot be resolved is an error.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: every definition of [`Core/Source/DecodeOps.lean`](../../Core/Source/DecodeOps.lean).

<details>
<summary>Details for reviewers</summary>

- §9.7.15.1 (bar, barrier)
- §9.7.15.3 (barrier.cluster)
- §9.7.15.4 (fence)
- §9.7.15.16 (mbarrier)
- §9.7.10.16 (prefetch)
- §9.7.10.28 (cp.async, cp.async.bulk, cp.async.bulk.prefetch, cp.async.bulk.tensor,
    cp.reduce.async.bulk.tensor, cp.async.bulk.prefetch.tensor, commit_group, wait_group)
- §9.7.15.16.18 (cp.async.mbarrier.arrive)
- §9.7.15.18 and §9.7.15.19 (clusterlaunchcontrol)
- §9.7.21.5 (setmaxnreg)
- §9.7.18 (tcgen05)

**Effect:** The listed forms are as follows: - `bar.sync` and `bar.arrive` without `.cta` (aligned), `barrier.sync{.aligned}` and `barrier.arrive{.aligned}` without `.cta`, and every `barrier.cluster.arrive` and `barrier.cluster.wait` form. - `mbarrier.init` and `mbarrier.inval` with `.shared` or `.shared::cta` written and no layout; `mbarrier.arrive{.expect_tx}{.sem.scope}.space.b64` with `.space` written and `.sem` and `.scope` both written or both omitted, where a destination register `state` requires a CTA address; `mbarrier.try_wait.parity{.sem.scope}.space.b64` likewise, without `.phase_type`. - `fence.mbarrier_init.release.cluster`, and every other `fence` and `membar` entry (PROG-ISA-FENCE). - `cp.async.bulk` in each direction of the table, `.weak` or `.relaxed`, with `.ignore_oob`, `.multicast::cluster{::16b, ::32b}`, `.L2::cache_hint` and `.cp_mask`, and with `.mbarrier::report::disabled` as the only report mechanism; `cp.reduce.async.bulk` in both directions with its operation, type and optional `.relaxed.scope`; `cp.async.{ca,cg}` with every operand form; `cp.async.commit_group`, `cp.async.wait_group` with a non-negative integer constant, `cp.async.wait_all`; `cp.async.mbarrier.arrive{.noinc}` with `.shared` or `.shared::cta` written or a generic address; `st.async` and `red.async` in every form without `.mmio`; `cp.async.bulk.prefetch.L2.global` with `.L2::cache_hint` or `.L2::evict_last`; the tensor loads to `.shared::cta` and `.shared::cluster` (`.multicast::cluster` and its `::16b` form take a 16-bit mask, `::32b` a 32-bit mask), with `.mbarrier::report::disabled` as the only report mechanism, the tensor stores, the tensor reductions and the tensor prefetch (also with `.L2::evict_last`), each with `.tile` or the default mode, or the four-row mode on a `.2d` map; `cp.async.bulk.commit_group`; `cp.async.bulk.wait_group{.read, .sync_restrict::proxy::async}` with a non-negative integer constant; `prefetch{.param}.tensormap` of `[a]`. - `clusterlaunchcontrol.try_cancel` with `.shared::cta` written, `query_cancel.is_canceled` and `query_cancel.get_first_ctaid::{x,y,z}`. - `setmaxnreg.{inc,dec}.sync.aligned.u32` with a count from 24 to 256 that is a multiple of 8. `createpolicy`, `nanosleep` and `pmevent` decode to `Op.misc` (PROG-ISA-MISC). - `tcgen05.alloc` with `.shared::cta` written, `dealloc`, `relinquish_alloc_permit`, both fences, `wait::ld`, `wait::st`, `commit` with `.shared::cluster` written (multicast with a 16-bit mask only), `ld` and `st` without packing, `ld.red` (PROG-ISA-TC-LD-RED), and `cp` without decompression in the shapes of PROG-ISA-TC-CP. Every `tcgen05.mma` entry decodes to `Op.tcMma` (PROG-ISA-TC-MMA).

</details>

<a id="prog-isa-copy"></a>
#### the decoded forms of linear copies (`PROG-ISA-COPY`)

*Rule* · [Lean comment: `Core/Async/CopyForm.lean` L18-L43](../../Core/Async/CopyForm.lean#L18-L43)

A `cp.async.bulk` or `cp.reduce.async.bulk` instruction decodes to its direction, its addresses, its size, the mbarrier of its mbarrier completion (none for `.bulk_group`), its multicast mask, its `.ignore_oob` operands, its cache policy, its `.cp_mask` byte mask, and for a reduction its operation, type and scope. A `cp.async` decodes to its addresses, its `cp-size` and its source operand form. An `st.async` or `red.async` decodes to its operation, type, state space, address, value operands, and its mbarrier or release scope.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`BulkDir`](../../Core/Async/CopyForm.lean#L46-L50), [`BulkCopy`](../../Core/Async/CopyForm.lean#L52-L76), [`AsyncStore`](../../Core/Async/CopyForm.lean#L78-L91), [`CpAsyncSource`](../../Core/Async/CopyForm.lean#L93-L99)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28.4.1 (cp.async.bulk syntax and completion mechanisms)
- §9.7.10.28.4.2 (cp.reduce.async.bulk syntax)
- §9.7.10.28.3.1 (cp.async syntax)
- §9.7.10.12 (st.async syntax)
- §9.7.15.7 (red.async syntax)

**Applies:** The `cp.async.bulk`, `cp.reduce.async.bulk`, `cp.async`, `st.async` and `red.async` forms PROG-ISA-SYNC-FORMS lists

**Effect:** The operands of `Op.cpBulk`, `Op.cpAsync` and `Op.asyncStore`; the rules are THREAD-TMA, THREAD-CP-ASYNC and THREAD-ASYNC-STORE.

</details>

## Instruction tables

There is one row for each entry of the instruction table (PROG-ISA-ENTRY). The instruction column gives the mnemonic and its modifier slots in syntax order, with optional slots in braces. The modifier column lists, for each slot, the values that occur in at least one combination with Core semantics, and separately the values that occur only in combinations that decode without semantics. A value with semantics has them only in the combinations the coverage file records. The coverage is computed by `Tests/Source/IsaCoverage.lean`, which decodes one instruction with sample operands for every legal modifier combination and applies the rule function of the family, and it is stored in [isa-coverage.json](isa-coverage.json) as cubes of combinations with equal status. A local instruction that decodes without semantics has no rule unless an assumption gives it one. An event instruction that decodes without semantics is rejected when a thread executes it. The register operands of the samples have the width of the operand's type; the rules of the contract entries decide the cases that depend on operand values.

### Integer and bit instructions

Decoded to `IntInstr` (PROG-ISA-INT). `IntInstr.rule` names THREAD-INT, or THREAD-MOVE for `selp` and `slct`. The extended-precision instructions of §9.7.2 are grammar entries of their own, since the instruction table has none of them.

Entries: 54 with Core semantics, 0 decode only, 0 rejected.

| Instruction | Modifiers | Operands | Kind | Status | Rule | Manual |
|---|---|---|---|---|---|---|
| `abs.type` | **With semantics:** type: `s16`, `s32`, `s64` | `d, a` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.11 |
| `add.cc.type` | **With semantics:** cc: `cc`; type: `s32`, `s64`, `u32`, `u64` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.2.1 |
| `add{.sat}.type` | **With semantics:** sat: (omitted), `sat`; type: `s16`, `s16x2`, `s32`, `s64`, `u16`, `u16x2`, `u32`, `u64` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.1 |
| `addc{.cc}.type` | **With semantics:** cc: (omitted), `cc`; type: `s32`, `s64`, `u32`, `u64` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.2.2 |
| `and.type` | **With semantics:** type: `b16`, `b32`, `b64`, `pred` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.9.1 |
| `bfe.type` | **With semantics:** type: `s32`, `s64`, `u32`, `u64` | `d, a, b, c` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.20 |
| `bfi.type` | **With semantics:** type: `b32`, `b64` | `f, a, b, c, d` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.21 |
| `bfind{.shiftamt}.type` | **With semantics:** shiftamt: (omitted), `shiftamt`; type: `s32`, `s64`, `u32`, `u64` | `d, a` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.17 |
| `bmsk.mode.type` | **With semantics:** mode: `clamp`, `wrap`; type: `b32` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.23 |
| `brev.type` | **With semantics:** type: `b32`, `b64` | `d, a` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.19 |
| `clmad.mode.type` | **With semantics:** mode: `hi`, `lo`; type: `u64` | `d, a, b, c` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.5 |
| `clz.type` | **With semantics:** type: `b32`, `b64` | `d, a` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.16 |
| `cnot.type` | **With semantics:** type: `b16`, `b32`, `b64` | `d, a` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.9.5 |
| `div.type` | **With semantics:** type: `s16`, `s32`, `s64`, `u16`, `u32`, `u64` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.9 |
| `dp2a.mode.atype.btype` | **With semantics:** mode: `hi`, `lo`; atype: `s32`, `u32`; btype: `s32`, `u32` | `d, a, b, c` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.25 |
| `dp4a.atype.btype` | **With semantics:** atype: `s32`, `u32`; btype: `s32`, `u32` | `d, a, b, c` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.24 |
| `fns.type` | **With semantics:** type: `b32` | `d, mask, base, offset` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.18 |
| `lop3.type` | **With semantics:** type: `b32` | `d, a, b, c, immLut` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.9.6 |
| `lop3.boolop.type` | **With semantics:** boolop: `and`, `or`; type: `b32` | `d\|p, a, b, c, immLut, q` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.9.6 |
| `lop3.boolop.type` | **With semantics:** boolop: `and`, `or`; type: `b32` | `_\|p, a, b, c, immLut, q` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.9.6 |
| `mad.mode.cc.type` | **With semantics:** mode: `hi`, `lo`; cc: `cc`; type: `s32`, `s64`, `u32`, `u64` | `d, a, b, c` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.2.5 |
| `mad.mode{.sat}.type` | **With semantics:** mode: `hi`, `lo`; sat: (omitted), `sat`; type: `s16`, `s32`, `s64`, `u16`, `u32`, `u64` | `d, a, b, c` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.4 |
| `mad.mode.type` | **With semantics:** mode: `wide`; type: `s16`, `s32`, `u16`, `u32` | `d, a, b, c` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.4 |
| `mad24.mode{.sat}.type` | **With semantics:** mode: `hi`, `lo`; sat: (omitted), `sat`; type: `s32`, `u32` | `d, a, b, c` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.7 |
| `madc.mode{.cc}.type` | **With semantics:** mode: `hi`, `lo`; cc: (omitted), `cc`; type: `s32`, `s64`, `u32`, `u64` | `d, a, b, c` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.2.6 |
| `max{.ftz}{.nan}{.xorsign}{.abs}{.relu}.type` | **With semantics:** ftz: (omitted); nan: (omitted); xorsign: (omitted); abs: (omitted); relu: (omitted), `relu`; type: `s16`, `s16x2`, `s32`, `s64`, `u16`, `u16x2`, `u32`, `u64` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.14 |
| `min{.ftz}{.nan}{.xorsign}{.abs}{.relu}.type` | **With semantics:** ftz: (omitted); nan: (omitted); xorsign: (omitted); abs: (omitted); relu: (omitted), `relu`; type: `s16`, `s16x2`, `s32`, `s64`, `u16`, `u16x2`, `u32`, `u64` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.13 |
| `mul.mode.type` | **With semantics:** mode: `hi`, `lo`; type: `s16`, `s32`, `s64`, `u16`, `u32`, `u64` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.3 |
| `mul.mode.type` | **With semantics:** mode: `wide`; type: `s16`, `s32`, `u16`, `u32` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.3 |
| `mul24.mode.type` | **With semantics:** mode: `hi`, `lo`; type: `s32`, `u32` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.6 |
| `neg.type` | **With semantics:** type: `s16`, `s32`, `s64` | `d, a` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.12 |
| `not.type` | **With semantics:** type: `b16`, `b32`, `b64`, `pred` | `d, a` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.9.4 |
| `or.type` | **With semantics:** type: `b16`, `b32`, `b64`, `pred` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.9.2 |
| `popc.type` | **With semantics:** type: `b32`, `b64` | `d, a` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.15 |
| `prmt.type{.mode}` | **With semantics:** type: `b32`; mode: (omitted), `b4e`, `ecl`, `ecr`, `f4e`, `rc16`, `rc8` | `d, a, b, c` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.10.7 |
| `rem.type` | **With semantics:** type: `s16`, `s32`, `s64`, `u16`, `u32`, `u64` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.10 |
| `sad.type` | **With semantics:** type: `s16`, `s32`, `s64`, `u16`, `u32`, `u64` | `d, a, b, c` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.8 |
| `selp.type` | **With semantics:** type: `b16`, `b32`, `b64`, `f32`, `f64`, `s16`, `s32`, `s64`, `u16`, `u32`, `u64` | `d, a, b, c` | local | Core semantics | [THREAD-MOVE](threads.md#thread-move) | §9.7.7.3 |
| `set.cmp.boolop{.ftz}.dtype.stype` | **With semantics:** cmp: `eq`, `ge`, `gt`, `hi`, `hs`, `le`, `lo`, `ls`, `lt`, `ne`; boolop: `and`, `or`, `xor`; ftz: (omitted); dtype: `f32`, `s32`, `u32`; stype: `b16`, `b32`, `b64`, `s16`, `s32`, `s64`, `u16`, `u32`, `u64` | `d, a, b, c` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.7.1 |
| `set.cmp{.ftz}.dtype.stype` | **With semantics:** cmp: `eq`, `ge`, `gt`, `hi`, `hs`, `le`, `lo`, `ls`, `lt`, `ne`; ftz: (omitted); dtype: `f32`, `s32`, `u32`; stype: `b16`, `b32`, `b64`, `s16`, `s32`, `s64`, `u16`, `u32`, `u64` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.7.1 |
| `set.cmp.type` | **With semantics:** cmp: `eq`, `ge`, `gt`, `hi`, `hs`, `le`, `lo`, `ls`, `lt`, `ne`; type: `s16x2`, `s8x4`, `u16x2`, `u8x4` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.7.1 |
| `setp.cmp.boolop{.ftz}.type` | **With semantics:** cmp: `eq`, `ge`, `gt`, `hi`, `hs`, `le`, `lo`, `ls`, `lt`, `ne`; boolop: `and`, `or`, `xor`; ftz: (omitted); type: `b16`, `b32`, `b64`, `s16`, `s32`, `s64`, `u16`, `u32`, `u64` | `p, a, b, c` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.7.2 |
| `setp.cmp.boolop{.ftz}.type` | **With semantics:** cmp: `eq`, `ge`, `gt`, `hi`, `hs`, `le`, `lo`, `ls`, `lt`, `ne`; boolop: `and`, `or`, `xor`; ftz: (omitted); type: `b16`, `b32`, `b64`, `s16`, `s32`, `s64`, `u16`, `u32`, `u64` | `p\|q, a, b, c` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.7.2 |
| `setp.cmp{.ftz}.type` | **With semantics:** cmp: `eq`, `ge`, `gt`, `hi`, `hs`, `le`, `lo`, `ls`, `lt`, `ne`; ftz: (omitted); type: `b16`, `b32`, `b64`, `s16`, `s32`, `s64`, `u16`, `u32`, `u64` | `p, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.7.2 |
| `setp.cmp{.ftz}.type` | **With semantics:** cmp: `eq`, `ge`, `gt`, `hi`, `hs`, `le`, `lo`, `ls`, `lt`, `ne`; ftz: (omitted); type: `b16`, `b32`, `b64`, `s16`, `s32`, `s64`, `u16`, `u32`, `u64` | `p\|q, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.7.2 |
| `shf.dir.mode.type` | **With semantics:** dir: `l`, `r`; mode: `clamp`, `wrap`; type: `b32` | `d, a, b, c` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.9.7 |
| `shl.type` | **With semantics:** type: `b16`, `b32`, `b64` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.9.8 |
| `shr.type` | **With semantics:** type: `b16`, `b32`, `b64`, `s16`, `s32`, `s64`, `u16`, `u32`, `u64` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.9.9 |
| `slct{.ftz}.dtype.ctype` | **With semantics:** ftz: (omitted), `ftz`; dtype: `b16`, `b32`, `b64`, `f32`, `f64`, `s16`, `s32`, `s64`, `u16`, `u32`, `u64`; ctype: `f32`, `s32` | `d, a, b, c` | local | Core semantics | [THREAD-MOVE](threads.md#thread-move) | §9.7.7.4 |
| `sub.cc.type` | **With semantics:** cc: `cc`; type: `s32`, `s64`, `u32`, `u64` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.2.3 |
| `sub{.sat}.type` | **With semantics:** sat: (omitted), `sat`; type: `s16`, `s32`, `s64`, `u16`, `u32`, `u64` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.2 |
| `subc{.cc}.type` | **With semantics:** cc: (omitted), `cc`; type: `s32`, `s64`, `u32`, `u64` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.2.4 |
| `szext.mode.type` | **With semantics:** mode: `clamp`, `wrap`; type: `s32`, `u32` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.1.22 |
| `xor.type` | **With semantics:** type: `b16`, `b32`, `b64`, `pred` | `d, a, b` | local | Core semantics | [THREAD-INT](threads.md#thread-int) | §9.7.9.3 |

### Register moves

Decoded to `MoveInstr` (PROG-ISA-MOVE). `MoveInstr.rule` names THREAD-MOVE.

Entries: 11 with Core semantics, 0 decode only, 0 rejected.

| Instruction | Modifiers | Operands | Kind | Status | Rule | Manual |
|---|---|---|---|---|---|---|
| `mov.type` | **With semantics:** type: `b16`, `b32`, `b64`, `f32`, `f64`, `pred`, `s16`, `s32`, `s64`, `u16`, `u32`, `u64` | `d, a` | local | Core semantics | [THREAD-MOVE](threads.md#thread-move) | §9.7.10.3 |
| `mov.type` | **With semantics:** type: `b32` | `d, {a...}` | local | Core semantics | [THREAD-MOVE](threads.md#thread-move) | §9.7.10.4 |
| `mov.type` | **With semantics:** type: `b64` | `d, {a...}` | local | Core semantics | [THREAD-MOVE](threads.md#thread-move) | §9.7.10.4 |
| `mov.type` | **With semantics:** type: `b64` | `d, {a...}` | local | Core semantics | [THREAD-MOVE](threads.md#thread-move) | §9.7.10.4 |
| `mov.type` | **With semantics:** type: `b128` | `d, {a...}` | local | Core semantics | [THREAD-MOVE](threads.md#thread-move) | §9.7.10.4 |
| `mov.type` | **With semantics:** type: `b128` | `d, {a...}` | local | Core semantics | [THREAD-MOVE](threads.md#thread-move) | §9.7.10.4 |
| `mov.type` | **With semantics:** type: `b32` | `{d...}, a` | local | Core semantics | [THREAD-MOVE](threads.md#thread-move) | §9.7.10.4 |
| `mov.type` | **With semantics:** type: `b64` | `{d...}, a` | local | Core semantics | [THREAD-MOVE](threads.md#thread-move) | §9.7.10.4 |
| `mov.type` | **With semantics:** type: `b64` | `{d...}, a` | local | Core semantics | [THREAD-MOVE](threads.md#thread-move) | §9.7.10.4 |
| `mov.type` | **With semantics:** type: `b128` | `{d...}, a` | local | Core semantics | [THREAD-MOVE](threads.md#thread-move) | §9.7.10.4 |
| `mov.type` | **With semantics:** type: `b128` | `{d...}, a` | local | Core semantics | [THREAD-MOVE](threads.md#thread-move) | §9.7.10.4 |

### Conversions

Decoded to `CvtInstr` (PROG-ISA-CVT). `CvtInstr.rule` names THREAD-CVT for the conversions the model gives exactly (`CvtInstr.exact`).

Entries: 34 with Core semantics, 6 decode only, 0 rejected.

| Instruction | Modifiers | Operands | Kind | Status | Rule | Manual |
|---|---|---|---|---|---|---|
| `cvt{.rnd}{.relu}{.satfinite}{.ftz}{.sat}.dtype.atype` | **With semantics:** rnd: (omitted), `rm`, `rmi`, `rn`, `rni`, `rp`, `rpi`, `rz`, `rzi`; relu: (omitted), `relu`; satfinite: (omitted), `satfinite`; ftz: (omitted), `ftz`; sat: (omitted), `sat`; dtype: `bf16`, `f16`, `f32`, `f64`, `s16`, `s32`, `s64`, `s8`, `u16`, `u32`, `u64`, `u8`; atype: `bf16`, `f16`, `f32`, `f64`, `s16`, `s32`, `s64`, `s8`, `u16`, `u32`, `u64`, `u8` | `d, a` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd.satfinite{.relu}{.pzo}{.scaled}.dtype.atype` | **With semantics:** rnd: `rn`, `rz`; satfinite: `satfinite`; relu: (omitted), `relu`; pzo: (omitted), `pzo`; scaled: (omitted), `scaled::n1::ue8m0`; dtype: `e2m1x2`, `e2m3x2`, `e3m2x2`, `e4m3x2`, `e5m2x2`; atype: `f32` | `d, a, b, {scale_factor}` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd.satfinite{.relu}{.pzo}{.scaled}.dtype.atype` | **With semantics:** rnd: `rn`, `rz`; satfinite: `satfinite`; relu: (omitted), `relu`; pzo: (omitted), `pzo`; scaled: (omitted), `scaled::n1::ue8m0`; dtype: `e2m1x2`, `e2m3x2`, `e3m2x2`, `e4m3x2`, `e5m2x2`; atype: `bf16x2`, `f16x2` | `d, a, {scale_factor}` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd{.relu}{.satfinite}.dtype.atype` | **With semantics:** rnd: `rn`, `rz`; relu: (omitted), `relu`; satfinite: (omitted), `satfinite`; dtype: `bf16x2`; atype: `f32` | `d, a, b` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd{.relu}{.satfinite}{.scaled}.dtype.atype` | **With semantics:** rnd: `rn`; relu: (omitted), `relu`; satfinite: (omitted), `satfinite`; scaled: (omitted), `scaled::n2::ue8m0`; dtype: `bf16x2`; atype: `e2m1x2` | `d, a, {scale_factor}` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd{.relu}{.satfinite}{.scaled}.dtype.atype` | **With semantics:** rnd: `rn`; relu: (omitted), `relu`; satfinite: (omitted), `satfinite`; scaled: (omitted), `scaled::n2::ue8m0`; dtype: `bf16x2`; atype: `e2m3x2`, `e3m2x2` | `d, a, {scale_factor}` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd{.relu}{.satfinite}{.scaled}.dtype.atype` | **With semantics:** rnd: `rn`; relu: (omitted), `relu`; satfinite: (omitted), `satfinite`; scaled: (omitted), `scaled::n2::ue8m0`; dtype: `bf16x2`; atype: `e4m3x2`, `e5m2x2` | `d, a, {scale_factor}` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd{.satfinite}{.relu}{.scaled}.dtype.atype` | **With semantics:** rnd: `rn`; satfinite: (omitted), `satfinite`; relu: (omitted), `relu`; scaled: (omitted), `scaled::n2::ue8m0`; dtype: `bf16x2`; atype: `s2f6x2` | `d, a, {scale_factor}` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd{.satfinite}{.scaled}.dtype.atype` | **With semantics:** rnd: `rn`; satfinite: (omitted), `satfinite`; scaled: (omitted), `scaled::n2::ue8m0`; dtype: `bf16x2`; atype: `ue5m3x2` | `d, a, {scale_factor}` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd.dtype.atype` | **With semantics:** rnd: `rn`; dtype: `bf16x2`; atype: `ue8m0x2` | `d, a` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd{.relu}{.satfinite}.dtype.atype` | **With semantics:** rnd: `rn`, `rz`; relu: (omitted), `relu`; satfinite: (omitted), `satfinite`; dtype: `f16x2`; atype: `f32` | `d, a, b` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd{.relu}.dtype.atype` | **With semantics:** rnd: `rn`; relu: (omitted), `relu`; dtype: `f16x2`; atype: `e2m1x2` | `d, a` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd{.relu}.dtype.atype` | **With semantics:** rnd: `rn`; relu: (omitted), `relu`; dtype: `f16x2`; atype: `e2m3x2`, `e3m2x2` | `d, a` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd{.relu}.dtype.atype` | **With semantics:** rnd: `rn`; relu: (omitted), `relu`; dtype: `f16x2`; atype: `e4m3x2`, `e5m2x2` | `d, a` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd.dtype.atype` | **With semantics:** rnd: `rn`; dtype: `f16x2`; atype: `ue5m3x2` | `d, a` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd.satfinite{.relu}.dtype.atype` | **With semantics:** rnd: `rn`; satfinite: `satfinite`; relu: (omitted), `relu`; dtype: `e2m1x2`; atype: `f32` | `d, a, b` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd.satfinite{.relu}.dtype.atype` | **With semantics:** rnd: `rn`; satfinite: `satfinite`; relu: (omitted), `relu`; dtype: `e2m1x2`; atype: `bf16x2`, `f16x2` | `d, a` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd.satfinite{.relu}.dtype.atype` | **With semantics:** rnd: `rn`; satfinite: `satfinite`; relu: (omitted), `relu`; dtype: `e2m3x2`, `e3m2x2`; atype: `f32` | `d, a, b` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd.satfinite{.relu}.dtype.atype` | **With semantics:** rnd: `rn`; satfinite: `satfinite`; relu: (omitted), `relu`; dtype: `e2m3x2`, `e3m2x2`; atype: `bf16x2`, `f16x2` | `d, a` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd.satfinite{.relu}.dtype.atype` | **With semantics:** rnd: `rn`; satfinite: `satfinite`; relu: (omitted), `relu`; dtype: `e4m3x2`, `e5m2x2`; atype: `f32` | `d, a, b` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd.satfinite{.relu}.dtype.atype` | **With semantics:** rnd: `rn`; satfinite: `satfinite`; relu: (omitted), `relu`; dtype: `e4m3x2`, `e5m2x2`; atype: `bf16x2`, `f16x2` | `d, a` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd{.relu}{.satfinite}.pzo.dtype.atype` | **With semantics:** rnd: `rn`, `rz`; relu: (omitted), `relu`; satfinite: (omitted), `satfinite`; pzo: `pzo`; dtype: `bf16x2`, `f16x2`; atype: `f32` | `d, a, b` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd{.relu}{.satfinite}.pzo.dtype.atype` | **With semantics:** rnd: `rn`, `rz`; relu: (omitted), `relu`; satfinite: (omitted), `satfinite`; pzo: `pzo`; dtype: `bf16`, `f16`; atype: `f32` | `d, a` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd{.satfinite}{.relu}.pzo.dtype.atype` | **Decode only:** rnd: `rn`, `rz`; satfinite: (omitted), `satfinite`; relu: (omitted), `relu`; pzo: `pzo`; dtype: `tf32`; atype: `f32` | `d, a` | local | Decode only: an `Assumption.localRule` may give it a meaning | none | §9.7.10.24 |
| `cvt.rnd{.relu}{.satfinite}.dtype.atype` | **With semantics:** rnd: `rs`; relu: (omitted), `relu`; satfinite: (omitted), `satfinite`; dtype: `bf16x2`; atype: `f32` | `d, a, b, rbits` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd{.relu}{.satfinite}.dtype.atype` | **With semantics:** rnd: `rs`; relu: (omitted), `relu`; satfinite: (omitted), `satfinite`; dtype: `f16x2`; atype: `f32` | `d, a, b, rbits` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd{.relu}.satfinite.dtype.atype` | **Decode only:** rnd: `rs`; relu: (omitted), `relu`; satfinite: `satfinite`; dtype: `e2m1x4`; atype: `f32` | `d, {abef...}, rbits` | local | Decode only: an `Assumption.localRule` may give it a meaning | none | §9.7.10.24 |
| `cvt.rnd{.relu}.satfinite.dtype.atype` | **Decode only:** rnd: `rs`; relu: (omitted), `relu`; satfinite: `satfinite`; dtype: `e2m3x4`, `e3m2x4`; atype: `f32` | `d, {abef...}, rbits` | local | Decode only: an `Assumption.localRule` may give it a meaning | none | §9.7.10.24 |
| `cvt.rnd{.relu}.satfinite.dtype.atype` | **Decode only:** rnd: `rs`; relu: (omitted), `relu`; satfinite: `satfinite`; dtype: `e4m3x4`, `e5m2x4`; atype: `f32` | `d, {abef...}, rbits` | local | Decode only: an `Assumption.localRule` may give it a meaning | none | §9.7.10.24 |
| `cvt.rnd.satfinite{.relu}{.scaled}.dtype.atype` | **Decode only:** rnd: `rn`; satfinite: `satfinite`; relu: (omitted), `relu`; scaled: (omitted), `scaled::n2::ue8m0`; dtype: `s2f6x2`; atype: `bf16x2` | `d, a, {scale_factor}` | local | Decode only: an `Assumption.localRule` may give it a meaning | none | §9.7.10.24 |
| `cvt.rnd.satfinite{.relu}{.scaled}.dtype.atype` | **With semantics:** rnd: `rn`; satfinite: `satfinite`; relu: (omitted), `relu`; scaled: (omitted), `scaled::n2::ue8m0`; dtype: `s2f6x2`; atype: `f32` | `d, a, b, {scale_factor}` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd{.satfinite}{.relu}.dtype.atype` | **Decode only:** rnd: `rn`, `rna`, `rz`; satfinite: (omitted), `satfinite`; relu: (omitted), `relu`; dtype: `tf32`; atype: `f32` | `d, a` | local | Decode only: an `Assumption.localRule` may give it a meaning | none | §9.7.10.24 |
| `cvt.rnd{.satfinite}.dtype.atype` | **With semantics:** rnd: `rn`, `rp`, `rz`; satfinite: (omitted), `satfinite`; dtype: `ue5m3x2`; atype: `f32` | `d, a, b` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd{.satfinite}.scaled.dtype.atype` | **With semantics:** rnd: `rn`, `rz`; satfinite: (omitted), `satfinite`; scaled: `scaled::n1::ue8m0`; dtype: `ue5m3x2`; atype: `f32` | `d, a, b, scale_factor` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd{.satfinite}.dtype.atype` | **With semantics:** rnd: `rn`, `rp`, `rz`; satfinite: (omitted), `satfinite`; dtype: `ue5m3x2`; atype: `bf16x2`, `f16x2` | `d, a` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd{.satfinite}.scaled.dtype.atype` | **With semantics:** rnd: `rn`, `rz`; satfinite: (omitted), `satfinite`; scaled: `scaled::n1::ue8m0`; dtype: `ue5m3x2`; atype: `bf16x2`, `f16x2` | `d, a, scale_factor` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd{.satfinite}.dtype.atype` | **With semantics:** rnd: `rp`, `rz`; satfinite: (omitted), `satfinite`; dtype: `ue8m0x2`; atype: `bf16x2` | `d, a` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.rnd{.satfinite}.dtype.atype` | **With semantics:** rnd: `rp`, `rz`; satfinite: (omitted), `satfinite`; dtype: `ue8m0x2`; atype: `f32` | `d, a, b` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.24 |
| `cvt.pack.sat.convert.abtype` | **With semantics:** sat: `sat`; convert: `s16`, `u16`; abtype: `s32` | `d, a, b` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.25 |
| `cvt.pack.sat.convert.abtype.ctype` | **With semantics:** sat: `sat`; convert: `s2`, `s4`, `s8`, `u2`, `u4`, `u8`; abtype: `s32`; ctype: `b32` | `d, a, b, c` | local | Core semantics | [THREAD-CVT](threads.md#thread-cvt) | §9.7.10.25 |

### Memory access and addresses

Decoded to `MemAccess` or `AddrInstr` (PROG-ISA-MEM). `MemAccess.rule` and `AddrInstr.rule` name THREAD-ACCESS, THREAD-MOVE, THREAD-CVTA, THREAD-SHARED-POINTER or THREAD-PREFETCH.

Entries: 41 with Core semantics, 5 decode only, 0 rejected.

| Instruction | Modifiers | Operands | Kind | Status | Rule | Manual |
|---|---|---|---|---|---|---|
| `applypriority{.space}.level` | **With semantics:** space: `global`; level: `L2::evict_normal`<br>**Decode only:** space: (omitted) | `[addr], 128` | event | Core semantics (1 of 2)<br>Decode only (1 of 2): execution is rejected | [THREAD-PREFETCH](threads.md#thread-prefetch) | §9.7.10.17 |
| `atom{.sem}{.scope}{.space}.op{.cache}.type` | **With semantics:** sem: (omitted), `acq_rel`, `acquire`, `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`, `shared`, `shared::cluster`, `shared::cta`; op: `add`, `and`, `dec`, `inc`, `max`, `min`, `or`, `xor`; cache: (omitted), `L2::cache_hint`; type: `b32`, `b64`, `f32`, `f64`, `s32`, `s64`, `u32`, `u64` | `d, [addr], value, {cache_policy}` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.5 |
| `atom{.sem}{.scope}{.space}.op{.cache}.type` | **With semantics:** sem: (omitted), `acq_rel`, `acquire`, `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`, `shared`, `shared::cluster`, `shared::cta`; op: `add`, `and`, `dec`, `inc`, `max`, `min`, `or`, `xor`; cache: (omitted), `L2::cache_hint`; type: `b32`, `b64`, `f32`, `f64`, `s32`, `s64`, `u32`, `u64` | `_, [addr], value, {cache_policy}` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.5 |
| `atom{.sem}{.scope}{.space}.op.type` | **With semantics:** sem: (omitted), `acq_rel`, `acquire`, `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`, `shared`, `shared::cluster`, `shared::cta`; op: `cas`; type: `b128`, `b16`, `b32`, `b64` | `d, [addr], compare, value` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.5 |
| `atom{.sem}{.scope}{.space}.op.type` | **With semantics:** sem: (omitted), `acq_rel`, `acquire`, `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`, `shared`, `shared::cluster`, `shared::cta`; op: `cas`; type: `b128`, `b16`, `b32`, `b64` | `_, [addr], compare, value` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.5 |
| `atom{.sem}{.scope}{.space}.op{.cache}.type` | **With semantics:** sem: (omitted), `acq_rel`, `acquire`, `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`, `shared`, `shared::cluster`, `shared::cta`; op: `exch`; cache: (omitted), `L2::cache_hint`; type: `b128`, `b32`, `b64` | `d, [addr], value, {cache_policy}` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.5 |
| `atom{.sem}{.scope}{.space}.op{.cache}.type` | **With semantics:** sem: (omitted), `acq_rel`, `acquire`, `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`, `shared`, `shared::cluster`, `shared::cta`; op: `exch`; cache: (omitted), `L2::cache_hint`; type: `b128`, `b32`, `b64` | `_, [addr], value, {cache_policy}` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.5 |
| `atom{.sem}{.scope}{.space}.op.noftz{.cache}.type` | **With semantics:** sem: (omitted), `acq_rel`, `acquire`, `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`, `shared`, `shared::cluster`, `shared::cta`; op: `add`; noftz: `noftz`; cache: (omitted), `L2::cache_hint`; type: `f32` | `d, [addr], value, {cache_policy}` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.5 |
| `atom{.sem}{.scope}{.space}.op.noftz{.cache}.type` | **With semantics:** sem: (omitted), `acq_rel`, `acquire`, `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`, `shared`, `shared::cluster`, `shared::cta`; op: `add`; noftz: `noftz`; cache: (omitted), `L2::cache_hint`; type: `f32` | `_, [addr], value, {cache_policy}` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.5 |
| `atom{.sem}{.scope}{.space}.op.noftz{.cache}.type` | **With semantics:** sem: (omitted), `acq_rel`, `acquire`, `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`, `shared`, `shared::cluster`, `shared::cta`; op: `add`; noftz: `noftz`; cache: (omitted), `L2::cache_hint`; type: `bf16`, `bf16x2`, `f16`, `f16x2` | `d, [addr], value, {cache_policy}` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.5 |
| `atom{.sem}{.scope}{.space}.op.noftz{.cache}.type` | **With semantics:** sem: (omitted), `acq_rel`, `acquire`, `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`, `shared`, `shared::cluster`, `shared::cta`; op: `add`; noftz: `noftz`; cache: (omitted), `L2::cache_hint`; type: `f16`, `f16x2` | `_, [addr], value, {cache_policy}` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.5 |
| `atom{.sem}{.scope}{.space}.op{.cache}.vec.type` | **With semantics:** sem: (omitted), `acq_rel`, `acquire`, `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`; op: `add`; cache: (omitted), `L2::cache_hint`; vec: `v2`, `v4`; type: `f32` | `{d...}, [addr], {value...}, {cache_policy}` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.5 |
| `atom{.sem}{.scope}{.space}.op{.cache}.vec.type` | **With semantics:** sem: (omitted), `acq_rel`, `acquire`, `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`; op: `add`; cache: (omitted), `L2::cache_hint`; vec: `v2`, `v4`; type: `f32` | `_, [addr], {value...}, {cache_policy}` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.5 |
| `atom{.sem}{.scope}{.space}.op.noftz{.cache}.vec.type` | **With semantics:** sem: (omitted), `acq_rel`, `acquire`, `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`; op: `add`; noftz: `noftz`; cache: (omitted), `L2::cache_hint`; vec: `v2`, `v4`; type: `f32` | `{d...}, [addr], {value...}, {cache_policy}` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.5 |
| `atom{.sem}{.scope}{.space}.op.noftz{.cache}.vec.type` | **With semantics:** sem: (omitted), `acq_rel`, `acquire`, `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`; op: `add`; noftz: `noftz`; cache: (omitted), `L2::cache_hint`; vec: `v2`, `v4`; type: `f32` | `_, [addr], {value...}, {cache_policy}` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.5 |
| `atom{.sem}{.scope}{.space}.op.noftz{.cache}.vec.type` | **With semantics:** sem: (omitted), `acq_rel`, `acquire`, `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`; op: `add`, `max`, `min`; noftz: `noftz`; cache: (omitted), `L2::cache_hint`; vec: `v2`, `v4`, `v8`; type: `bf16`, `bf16x2`, `f16`, `f16x2` | `{d...}, [addr], {value...}, {cache_policy}` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.5 |
| `atom{.sem}{.scope}{.space}.op.noftz{.cache}.vec.type` | **With semantics:** sem: (omitted), `acq_rel`, `acquire`, `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`; op: `add`, `max`, `min`; noftz: `noftz`; cache: (omitted), `L2::cache_hint`; vec: `v2`, `v4`, `v8`; type: `f16`, `f16x2` | `_, [addr], {value...}, {cache_policy}` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.5 |
| `cvta.dir.space.type` | **With semantics:** dir: `to`; space: `const`, `global`, `local`, `param`, `param::entry`, `shared`, `shared::cluster`, `shared::cta`; type: `u32`, `u64` | `d, ptr` | local | Core semantics (15 of 16)<br>Decode only (1 of 16): an `Assumption.localRule` may give it a meaning | [THREAD-CVTA](threads.md#thread-cvta) | §9.7.10.23 |
| `cvta.space.type` | **With semantics:** space: `const`, `global`, `local`, `param`, `param::entry`, `shared`, `shared::cluster`, `shared::cta`; type: `u32`, `u64` | `d, a` | local | Core semantics (15 of 16)<br>Decode only (1 of 16): an `Assumption.localRule` may give it a meaning | [THREAD-CVTA](threads.md#thread-cvta) | §9.7.10.23 |
| `discard{.space}.level` | **Decode only:** space: (omitted), `global`; level: `L2` | `[addr], 128` | event | Decode only: execution is rejected | none | §9.7.10.20 |
| `getctarank.space.type` | **With semantics:** space: `shared::cluster`; type: `u32`, `u64` | `d, a` | local | Core semantics | [THREAD-SHARED-POINTER](threads.md#thread-shared-pointer) | §9.7.10.27 |
| `getctarank.type` | **With semantics:** type: `u32`, `u64` | `d, a` | local | Core semantics | [THREAD-SHARED-POINTER](threads.md#thread-shared-pointer) | §9.7.10.27 |
| `isspacep.space` | **With semantics:** space: `const`, `global`, `local`, `param`, `param::entry`, `shared`, `shared::cluster`, `shared::cta` | `p, a` | local | Core semantics | [THREAD-CVTA](threads.md#thread-cvta) | §9.7.10.22 |
| `ld{.mmio}{.sem}{.scope}{.space}{.cop}{.nc}{.l1ev}{.cache}{.prefetch}.type` | **With semantics:** mmio: (omitted), `mmio`; sem: (omitted), `acquire`, `relaxed`, `volatile`, `weak`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `const`, `global`, `local`, `shared`, `shared::cluster`, `shared::cta`; cop: (omitted), `ca`, `cg`, `cs`, `cv`, `lu`; nc: (omitted), `nc`; l1ev: (omitted), `L1::evict_first`, `L1::evict_last`, `L1::evict_normal`, `L1::evict_unchanged`, `L1::no_allocate`; cache: (omitted), `L2::cache_hint`; prefetch: (omitted), `L2::128B`, `L2::256B`, `L2::64B`; type: `b128`, `b16`, `b32`, `b64`, `b8`, `f32`, `f64`, `s16`, `s32`, `s64`, `s8`, `u16`, `u32`, `u64`, `u8` | `d, [addr], {cache_policy}` | event | Core semantics (19320 of 19395)<br>Decode only (75 of 19395): execution is rejected | [THREAD-ACCESS](threads.md#thread-access) | §9.7.10.8 |
| `ld{.weak}.space.type` | **With semantics:** weak: (omitted), `weak`; space: `param`, `param::entry`; type: `b16`, `b32`, `b64`, `b8`, `f32`, `f64`, `s16`, `s32`, `s64`, `s8`, `u16`, `u32`, `u64`, `u8`<br>**Decode only:** space: `param::func`; type: `b128` | `d, [a]` | event | Core semantics (56 of 90)<br>Decode only (30 of 90): execution is rejected<br>Rejected at decoding (4 of 90): ld.param: parameters wider than 64 bits | [THREAD-MOVE](threads.md#thread-move) | §9.7.10.8 |
| `ld{.weak}.space.vec.type` | **With semantics:** weak: (omitted), `weak`; space: `param`, `param::entry`; vec: `v2`, `v4`; type: `b16`, `b32`, `b64`, `b8`, `f32`, `f64`, `s16`, `s32`, `s64`, `s8`, `u16`, `u32`, `u64`, `u8`<br>**Decode only:** space: `param::func` | `{d...}, [a]` | event | Core semantics (96 of 144)<br>Decode only (48 of 144): execution is rejected | [THREAD-MOVE](threads.md#thread-move) | §9.7.10.8 |
| `ld{.space}.type.proxy` | **Decode only:** space: (omitted), `global`; type: `b16`, `b32`, `b64`, `b8`, `f32`, `f64`, `s16`, `s32`, `s64`, `s8`, `u16`, `u32`, `u64`, `u8`; proxy: `proxy::readonly` | `d, [addr]` | event | Decode only: execution is rejected | none | §9.7.10.8 |
| `ld{.sem}{.scope}{.space}{.cop}{.nc}{.l1ev}{.cache}{.prefetch}.vec.type` | **With semantics:** sem: (omitted), `acquire`, `relaxed`, `volatile`, `weak`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `const`, `global`, `local`, `shared`, `shared::cluster`, `shared::cta`; cop: (omitted), `ca`, `cg`, `cs`, `cv`, `lu`; nc: (omitted), `nc`; l1ev: (omitted), `L1::evict_first`, `L1::evict_last`, `L1::evict_normal`, `L1::evict_unchanged`, `L1::no_allocate`; cache: (omitted), `L2::cache_hint`; prefetch: (omitted), `L2::128B`, `L2::256B`, `L2::64B`; vec: `v2`, `v4`; type: `b16`, `b32`, `b64`, `b8`, `f32`, `f64`, `s16`, `s32`, `s64`, `s8`, `u16`, `u32`, `u64`, `u8` | `{d...}, [addr], {cache_policy}` | event | Core semantics (30816 of 30936)<br>Decode only (120 of 30936): execution is rejected | [THREAD-ACCESS](threads.md#thread-access) | §9.7.10.8 |
| `ld{.sem}{.scope}{.space}{.cop}{.nc}{.l1ev}{.l2ev}{.cache}{.prefetch}.vec.type` | **With semantics:** sem: (omitted), `acquire`, `relaxed`, `volatile`, `weak`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`; cop: (omitted), `ca`, `cg`, `cs`, `cv`, `lu`; nc: (omitted), `nc`; l1ev: (omitted), `L1::evict_first`, `L1::evict_last`, `L1::evict_normal`, `L1::evict_unchanged`, `L1::no_allocate`; l2ev: (omitted), `L2::evict_first`, `L2::evict_last`, `L2::evict_normal`; cache: (omitted), `L2::cache_hint`; prefetch: (omitted), `L2::128B`, `L2::256B`, `L2::64B`; vec: `v4`, `v8`; type: `b32`, `b64`, `f32`, `f64`, `s32`, `s64`, `u32`, `u64` | `{d...}, [addr], {cache_policy}` | event | Core semantics | [THREAD-ACCESS](threads.md#thread-access) | §9.7.10.8 |
| `ldu{.space}.type` | **Decode only:** space: (omitted), `global`; type: `b128`, `b16`, `b32`, `b64`, `b8`, `f32`, `f64`, `s16`, `s32`, `s64`, `s8`, `u16`, `u32`, `u64`, `u8` | `d, [addr]` | event | Decode only: execution is rejected | none | §9.7.10.10 |
| `ldu{.space}.vec.type` | **Decode only:** space: (omitted), `global`; vec: `v2`, `v4`; type: `b16`, `b32`, `b64`, `b8`, `f32`, `f64`, `s16`, `s32`, `s64`, `s8`, `u16`, `u32`, `u64`, `u8` | `{d...}, [addr]` | event | Decode only: execution is rejected | none | §9.7.10.10 |
| `mapa.space.type` | **With semantics:** space: `shared::cluster`; type: `u32`, `u64` | `d, a, b` | local | Core semantics | [THREAD-SHARED-POINTER](threads.md#thread-shared-pointer) | §9.7.10.26 |
| `mapa.type` | **With semantics:** type: `u32`, `u64` | `d, a, b` | local | Core semantics | [THREAD-SHARED-POINTER](threads.md#thread-shared-pointer) | §9.7.10.26 |
| `prefetch{.space}{.level}{.evict}` | **With semantics:** space: (omitted), `global`, `local`; level: (omitted), `L1`, `L2`; evict: (omitted), `L2::evict_last`, `L2::evict_normal` | `[addr]` | event | Core semantics | [THREAD-PREFETCH](threads.md#thread-prefetch) | §9.7.10.16 |
| `prefetch{.space}.level.valid_addr` | **Decode only:** space: (omitted), `global`; level: `L1::32B`; valid_addr: `valid_addr` | `[addr]` | event | Decode only: execution is rejected | none | §9.7.10.16 |
| `prefetchu.level` | **With semantics:** level: `L1` | `[addr]` | event | Core semantics | [THREAD-PREFETCH](threads.md#thread-prefetch) | §9.7.10.16 |
| `red{.sem}{.scope}{.space}.op{.cache}.type` | **With semantics:** sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`, `shared`, `shared::cluster`, `shared::cta`; op: `add`, `and`, `dec`, `inc`, `max`, `min`, `or`, `xor`; cache: (omitted), `L2::cache_hint`; type: `b32`, `b64`, `f32`, `f64`, `s32`, `s64`, `u32`, `u64` | `[addr], value, {cache_policy}` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.6 |
| `red{.sem}{.scope}{.space}.op.noftz{.cache}.type` | **With semantics:** sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`, `shared`, `shared::cluster`, `shared::cta`; op: `add`; noftz: `noftz`; cache: (omitted), `L2::cache_hint`; type: `f32` | `[addr], value, {cache_policy}` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.6 |
| `red{.sem}{.scope}{.space}.op.noftz{.cache}.type` | **With semantics:** sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`, `shared`, `shared::cluster`, `shared::cta`; op: `add`; noftz: `noftz`; cache: (omitted), `L2::cache_hint`; type: `bf16`, `bf16x2`, `f16`, `f16x2` | `[addr], value, {cache_policy}` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.6 |
| `red{.sem}{.scope}{.space}.op{.cache}.vec.type` | **With semantics:** sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`; op: `add`; cache: (omitted), `L2::cache_hint`; vec: `v2`, `v4`; type: `f32` | `[addr], {value...}, {cache_policy}` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.6 |
| `red{.sem}{.scope}{.space}.op.noftz{.cache}.vec.type` | **With semantics:** sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`; op: `add`; noftz: `noftz`; cache: (omitted), `L2::cache_hint`; vec: `v2`, `v4`; type: `f32` | `[addr], {value...}, {cache_policy}` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.6 |
| `red{.sem}{.scope}{.space}.op.noftz{.cache}.vec.type` | **With semantics:** sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`; op: `add`, `max`, `min`; noftz: `noftz`; cache: (omitted), `L2::cache_hint`; vec: `v2`, `v4`, `v8`; type: `bf16`, `bf16x2`, `f16`, `f16x2` | `[addr], {value...}, {cache_policy}` | event | Core semantics | [THREAD-ATOMIC](threads.md#thread-atomic) | §9.7.15.6 |
| `st{.mmio}{.sem}{.scope}{.space}{.cop}{.l1ev}{.cache}.type` | **With semantics:** mmio: (omitted), `mmio`; sem: (omitted), `relaxed`, `release`, `volatile`, `weak`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`, `local`, `shared`, `shared::cluster`, `shared::cta`; cop: (omitted), `cg`, `cs`, `wb`, `wt`; l1ev: (omitted), `L1::evict_first`, `L1::evict_last`, `L1::evict_normal`, `L1::evict_unchanged`, `L1::no_allocate`; cache: (omitted), `L2::cache_hint`; type: `b128`, `b16`, `b32`, `b64`, `b8`, `f32`, `f64`, `s16`, `s32`, `s64`, `s8`, `u16`, `u32`, `u64`, `u8` | `[addr], value, {cache_policy}` | event | Core semantics | [THREAD-ACCESS](threads.md#thread-access) | §9.7.10.11 |
| `st{.sem}{.scope}{.space}{.cop}{.l1ev}{.cache}.vec.type` | **With semantics:** sem: (omitted), `relaxed`, `release`, `volatile`, `weak`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`, `local`, `shared`, `shared::cluster`, `shared::cta`; cop: (omitted), `cg`, `cs`, `wb`, `wt`; l1ev: (omitted), `L1::evict_first`, `L1::evict_last`, `L1::evict_normal`, `L1::evict_unchanged`, `L1::no_allocate`; cache: (omitted), `L2::cache_hint`; vec: `v2`, `v4`; type: `b16`, `b32`, `b64`, `b8`, `f32`, `f64`, `s16`, `s32`, `s64`, `s8`, `u16`, `u32`, `u64`, `u8` | `[addr], {value...}, {cache_policy}` | event | Core semantics | [THREAD-ACCESS](threads.md#thread-access) | §9.7.10.11 |
| `st{.sem}{.scope}{.space}{.cop}{.l1ev}{.l2ev}{.cache}.vec.type` | **With semantics:** sem: (omitted), `relaxed`, `release`, `volatile`, `weak`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`; cop: (omitted), `cg`, `cs`, `wb`, `wt`; l1ev: (omitted), `L1::evict_first`, `L1::evict_last`, `L1::evict_normal`, `L1::evict_unchanged`, `L1::no_allocate`; l2ev: (omitted), `L2::evict_first`, `L2::evict_last`, `L2::evict_normal`; cache: (omitted), `L2::cache_hint`; vec: `v4`, `v8`; type: `b32`, `b64`, `f32`, `f64`, `s32`, `s64`, `u32`, `u64` | `[addr], {value...}, {cache_policy}` | event | Core semantics | [THREAD-ACCESS](threads.md#thread-access) | §9.7.10.11 |
| `st.bulk{.weak}{.space}` | **With semantics:** weak: (omitted), `weak`; space: (omitted), `shared::cta` | `[addr], size, 0` | event | Core semantics | [THREAD-ACCESS](threads.md#thread-access) | §9.7.10.14 |

### Warp collectives

Decoded to `WarpInstr` (PROG-ISA-WARP). `WarpInstr.rule` names THREAD-SHFL, THREAD-VOTE, THREAD-REDUX, THREAD-MATCH, THREAD-ACTIVEMASK, THREAD-ELECT or THREAD-WARP-BAR.

Entries: 12 with Core semantics, 1 decode only, 0 rejected.

| Instruction | Modifiers | Operands | Kind | Status | Rule | Manual |
|---|---|---|---|---|---|---|
| `activemask.type` | **With semantics:** type: `b32` | `d` | local | Core semantics | [THREAD-ACTIVEMASK](barriers.md#thread-activemask) | §9.7.15.12 |
| `bar.warp.action` | **With semantics:** warp: `warp`; action: `sync` | `membermask` | event | Core semantics | [THREAD-WARP-BAR](barriers.md#thread-warp-bar) | §9.7.15.2 |
| `elect.sync` | none | `d\|p, membermask` | local | Core semantics | [THREAD-ELECT](barriers.md#thread-elect) | §9.7.15.15 |
| `match.mode.sync.type` | **With semantics:** mode: `all`; sync: `sync`; type: `b32`, `b64` | `d, a, membermask` | local | Core semantics | [THREAD-MATCH](barriers.md#thread-match) | §9.7.15.11 |
| `match.mode.sync.type` | **With semantics:** mode: `all`; sync: `sync`; type: `b32`, `b64` | `d\|p, a, membermask` | local | Core semantics | [THREAD-MATCH](barriers.md#thread-match) | §9.7.15.11 |
| `match.mode.sync.type` | **With semantics:** mode: `any`; sync: `sync`; type: `b32`, `b64` | `d, a, membermask` | local | Core semantics | [THREAD-MATCH](barriers.md#thread-match) | §9.7.15.11 |
| `redux.sync.op.type` | **With semantics:** op: `add`, `max`, `min`; type: `s32`, `u32` | `d, a, membermask` | local | Core semantics | [THREAD-REDUX](barriers.md#thread-redux) | §9.7.15.13 |
| `redux.sync.op.type` | **With semantics:** op: `and`, `or`, `xor`; type: `b32` | `d, a, membermask` | local | Core semantics | [THREAD-REDUX](barriers.md#thread-redux) | §9.7.15.13 |
| `redux.sync.op{.abs}{.nan}.type` | **Decode only:** op: `max`, `min`; abs: (omitted), `abs`; nan: (omitted), `NaN`; type: `f32` | `d, a, membermask` | local | Decode only: an `Assumption.localRule` may give it a meaning | none | §9.7.15.13 |
| `shfl.sync.mode.type` | **With semantics:** mode: `bfly`, `down`, `idx`, `up`; type: `b32` | `d, a, b, c, membermask` | local | Core semantics | [THREAD-SHFL](barriers.md#thread-shfl) | §9.7.10.6 |
| `shfl.sync.mode.type` | **With semantics:** mode: `bfly`, `down`, `idx`, `up`; type: `b32` | `d\|p, a, b, c, membermask` | local | Core semantics | [THREAD-SHFL](barriers.md#thread-shfl) | §9.7.10.6 |
| `vote.sync.mode.type` | **With semantics:** mode: `all`, `any`, `uni`; type: `pred` | `d, a, membermask` | local | Core semantics | [THREAD-VOTE](barriers.md#thread-vote) | §9.7.15.10 |
| `vote.sync.mode.type` | **With semantics:** mode: `ballot`; type: `b32` | `d, a, membermask` | local | Core semantics | [THREAD-VOTE](barriers.md#thread-vote) | §9.7.15.10 |

### Control flow

Decoded to their own constructors of `Op`. `Op.rule` (PROG-INSTR-RULE) names THREAD-BRANCH for `bra` and for `brx.idx` without `.uni`, THREAD-RUN for `ret`, `exit` and `trap`, and no rule for `brx.idx.uni`.

Entries: 6 with Core semantics, 0 decode only, 0 rejected.

| Instruction | Modifiers | Operands | Kind | Status | Rule | Manual |
|---|---|---|---|---|---|---|
| `bra{.uni}` | **With semantics:** uni: (omitted), `uni` | `tgt` | control | Core semantics | [THREAD-BRANCH](threads.md#thread-branch) | §9.7.14.3 |
| `brkpt` | none | none | control | Core semantics | [THREAD-RUN](threads.md#thread-run) | §9.7.21.1 |
| `brx.idx{.uni}` | **With semantics:** uni: (omitted), `uni` | `index, tlist` | control | Core semantics | [THREAD-BRANCH](threads.md#thread-branch) | §9.7.14.4 |
| `exit` | none | none | control | Core semantics | [THREAD-RUN](threads.md#thread-run) | §9.7.14.7 |
| `ret{.uni}` | **With semantics:** uni: (omitted) | none | control | Core semantics (1 of 2)<br>Rejected at decoding (1 of 2): ret.uni is not decoded | [THREAD-RUN](threads.md#thread-run) | §9.7.14.6 |
| `trap` | none | none | control | Core semantics | [THREAD-RUN](threads.md#thread-run) | §9.7.21.4 |

### Floating-point arithmetic

The listed forms decode to their own constructors of `Op` (PROG-ISA-SYNC-FORMS). The Core has no rule for them; a kernel assumption gives them one (ASM-IDEAL).

Entries: 50 with Core semantics, 3 decode only, 0 rejected.

| Instruction | Modifiers | Operands | Kind | Status | Rule | Manual |
|---|---|---|---|---|---|---|
| `abs{.ftz}.type` | **With semantics:** ftz: (omitted), `ftz`; type: `f32`, `f64` | `d, a` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.9 |
| `abs{.ftz}.type` | **With semantics:** ftz: (omitted), `ftz`; type: `bf16`, `bf16x2`, `f16`, `f16x2` | `d, a` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.4.6 |
| `add{.rnd}{.ftz}{.sat}.type{.srctype}` | **With semantics:** rnd: (omitted), `rm`, `rn`, `rp`, `rz`; ftz: (omitted), `ftz`; sat: (omitted), `sat`; type: `f32`, `f32x2`, `f64`; srctype: (omitted), `bf16`, `f16` | `d, a, b` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.3 |
| `add{.rnd}{.ftz}{.sat}.type` | **With semantics:** rnd: (omitted), `rn`; ftz: (omitted), `ftz`; sat: (omitted), `sat`; type: `bf16`, `bf16x2`, `f16`, `f16x2` | `d, a, b` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.4.1 |
| `add.rnd.dtype.atype.ctype` | **With semantics:** rnd: `rz`; dtype: `bf16x2`; atype: `f32x2`; ctype: `f32x2` | `d, a, c` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.5.1 |
| `add.rnd.ftz.dtype.atype.ctype` | **With semantics:** rnd: `rz`; ftz: `ftz`; dtype: `f16x2`; atype: `f32x2`; ctype: `f32x2` | `d, a, c` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.5.1 |
| `add{.rnd}.dtype.atype.ctype` | **With semantics:** rnd: (omitted), `rm`, `rn`, `rp`, `rz`; dtype: `f32x2`; atype: `bf16x2`, `f16x2`; ctype: `f32x2` | `d, a, c` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.5.1 |
| `copysign.type` | **With semantics:** type: `f32`, `f64` | `d, a, b` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.2 |
| `cos.mode{.ftz}.type` | **With semantics:** mode: `approx`; ftz: (omitted), `ftz`; type: `f32` | `d, value` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.19 |
| `div.mode{.ftz}.type` | **With semantics:** mode: `approx`, `rm`, `rn`, `rp`, `rz`; ftz: (omitted), `ftz`; type: `f32`, `f64`<br>**Decode only:** mode: `full` | `d, a, b` | local | Core semantics (14 of 16)<br>Decode only (2 of 16): an `Assumption.localRule` may give it a meaning | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.8 |
| `ex2.mode{.ftz}.type` | **With semantics:** mode: `approx`; ftz: (omitted), `ftz`; type: `f32` | `d, value` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.21 |
| `ex2.mode{.ftz}.type` | **With semantics:** mode: `approx`; ftz: (omitted), `ftz`; type: `bf16`, `bf16x2`, `f16`, `f16x2` | `d, value` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.4.10 |
| `fma.rnd{.ftz}{.sat}.type{.srctype}` | **With semantics:** rnd: `rm`, `rn`, `rp`, `rz`; ftz: (omitted), `ftz`; sat: (omitted), `sat`; type: `f32`, `f32x2`, `f64`; srctype: (omitted), `bf16`, `f16` | `d, a, b, c` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.6 |
| `fma.rnd{.ftz}{.sat}{.oob}{.relu}.type` | **With semantics:** rnd: `rn`; ftz: (omitted), `ftz`; sat: (omitted), `sat`; oob: (omitted), `oob`; relu: (omitted), `relu`; type: `bf16`, `bf16x2`, `f16`, `f16x2` | `d, a, b, c` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.4.4 |
| `fma.rnd.dtype.atype.btype.ctype` | **Decode only:** rnd: `rm`, `rn`, `rp`, `rz`; dtype: `f32x2`; atype: `bf16x2`, `f16x2`; btype: `f32x2`; ctype: `f32x2` | `d, a, b, c` | local | Decode only: an `Assumption.localRule` may give it a meaning | none | §9.7.5.3 |
| `lg2.mode{.ftz}.type` | **With semantics:** mode: `approx`; ftz: (omitted), `ftz`; type: `f32` | `d, value` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.20 |
| `mad.rnd{.ftz}{.sat}.type` | **With semantics:** rnd: `rm`, `rn`, `rp`, `rz`; ftz: (omitted), `ftz`; sat: (omitted), `sat`; type: `f32`, `f64` | `d, a, b, c` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.7 |
| `max{.ftz}{.nan}{.abs}.type` | **With semantics:** ftz: (omitted), `ftz`; nan: (omitted), `NaN`; abs: (omitted), `abs`; type: `f32` | `d, a, b, c` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.12 |
| `max{.ftz}{.nan}{.xorsign}{.abs}{.relu}.type` | **With semantics:** ftz: (omitted), `ftz`; nan: (omitted), `NaN`; xorsign: (omitted), `xorsign`; abs: (omitted), `abs`; relu: (omitted); type: `bf16`, `bf16x2`, `f16`, `f16x2`, `f32`, `f64` | `d, a, b` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.12 |
| `min{.ftz}{.nan}{.abs}.type` | **With semantics:** ftz: (omitted), `ftz`; nan: (omitted), `NaN`; abs: (omitted), `abs`; type: `f32` | `d, a, b, c` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.11 |
| `min{.ftz}{.nan}{.xorsign}{.abs}{.relu}.type` | **With semantics:** ftz: (omitted), `ftz`; nan: (omitted), `NaN`; xorsign: (omitted), `xorsign`; abs: (omitted), `abs`; relu: (omitted); type: `bf16`, `bf16x2`, `f16`, `f16x2`, `f32`, `f64` | `d, a, b` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.11 |
| `mul{.rnd}{.ftz}{.sat}.type` | **With semantics:** rnd: (omitted), `rm`, `rn`, `rp`, `rz`; ftz: (omitted), `ftz`; sat: (omitted), `sat`; type: `f32`, `f32x2`, `f64` | `d, a, b` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.5 |
| `mul{.rnd}{.ftz}{.sat}.type` | **With semantics:** rnd: (omitted), `rn`; ftz: (omitted), `ftz`; sat: (omitted), `sat`; type: `bf16`, `bf16x2`, `f16`, `f16x2` | `d, a, b` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.4.3 |
| `mul.dtype.atype.ctype` | **Decode only:** dtype: `bf16x2`; atype: `bf16x2`; ctype: `f16x2` | `d, a, c` | local | Decode only: an `Assumption.localRule` may give it a meaning | none | §9.7.5.4 |
| `mul.rnd.dtype.atype.ctype` | **With semantics:** rnd: `rz`; dtype: `bf16x2`; atype: `f32x2`; ctype: `f32x2` | `d, a, c` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.5.4 |
| `mul.ftz.rnd.dtype.atype.ctype` | **With semantics:** ftz: `ftz`; rnd: `rz`; dtype: `f16x2`; atype: `f32x2`; ctype: `f32x2` | `d, a, c` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.5.4 |
| `mul.dtype.atype.ctype` | **Decode only:** dtype: `f16x2`; atype: `f16x2`; ctype: `bf16x2` | `d, a, c` | local | Decode only: an `Assumption.localRule` may give it a meaning | none | §9.7.5.4 |
| `neg{.ftz}.type` | **With semantics:** ftz: (omitted), `ftz`; type: `f32`, `f64` | `d, a` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.10 |
| `neg{.ftz}.type` | **With semantics:** ftz: (omitted), `ftz`; type: `bf16`, `bf16x2`, `f16`, `f16x2` | `d, a` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.4.5 |
| `rcp.mode{.ftz}.type` | **With semantics:** mode: `approx`, `rm`, `rn`, `rp`, `rz`; ftz: (omitted), `ftz`; type: `f32`, `f64` | `d, value` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.13 |
| `rsqrt.mode{.ftz}.type` | **With semantics:** mode: `approx`; ftz: (omitted), `ftz`; type: `f32`, `f64` | `d, value` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.16 |
| `set.cmp.boolop{.ftz}.dtype.stype` | **With semantics:** cmp: `eq`, `equ`, `ge`, `geu`, `gt`, `gtu`, `le`, `leu`, `lt`, `ltu`, `nan`, `ne`, `neu`, `num`; boolop: `and`, `or`, `xor`; ftz: (omitted), `ftz`; dtype: `f32`, `s32`, `u32`; stype: `f32`, `f64` | `d, a, b, c` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.7.1 |
| `set.cmp{.ftz}.dtype.stype` | **With semantics:** cmp: `eq`, `equ`, `ge`, `geu`, `gt`, `gtu`, `le`, `leu`, `lt`, `ltu`, `nan`, `ne`, `neu`, `num`; ftz: (omitted), `ftz`; dtype: `f32`, `s32`, `u32`; stype: `f32`, `f64` | `d, a, b` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.7.1 |
| `set.cmp{.ftz}.dtype.stype` | **With semantics:** cmp: `eq`, `equ`, `ge`, `geu`, `gt`, `gtu`, `le`, `leu`, `lt`, `ltu`, `nan`, `ne`, `neu`, `num`; ftz: (omitted), `ftz`; dtype: `bf16`, `bf16x2`, `f16`, `f16x2`, `s16`, `s32`, `u16`, `u32`; stype: `b16`, `b32`, `b64`, `bf16`, `bf16x2`, `f16`, `f16x2`, `f32`, `f64`, `s16`, `s32`, `s64`, `u16`, `u32`, `u64` | `d, a, b` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.8.1 |
| `set.cmp.boolop{.ftz}.dtype.stype` | **With semantics:** cmp: `eq`, `equ`, `ge`, `geu`, `gt`, `gtu`, `le`, `leu`, `lt`, `ltu`, `nan`, `ne`, `neu`, `num`; boolop: `and`, `or`, `xor`; ftz: (omitted), `ftz`; dtype: `bf16`, `bf16x2`, `f16`, `f16x2`, `s16`, `s32`, `u16`, `u32`; stype: `b16`, `b32`, `b64`, `bf16`, `bf16x2`, `f16`, `f16x2`, `f32`, `f64`, `s16`, `s32`, `s64`, `u16`, `u32`, `u64` | `d, a, b, c` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.8.1 |
| `setp.cmp.boolop{.ftz}.type` | **With semantics:** cmp: `eq`, `equ`, `ge`, `geu`, `gt`, `gtu`, `le`, `leu`, `lt`, `ltu`, `nan`, `ne`, `neu`, `num`; boolop: `and`, `or`, `xor`; ftz: (omitted), `ftz`; type: `f32`, `f64` | `p, a, b, c` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.7.2 |
| `setp.cmp.boolop{.ftz}.type` | **With semantics:** cmp: `eq`, `equ`, `ge`, `geu`, `gt`, `gtu`, `le`, `leu`, `lt`, `ltu`, `nan`, `ne`, `neu`, `num`; boolop: `and`, `or`, `xor`; ftz: (omitted), `ftz`; type: `f32`, `f64` | `p\|q, a, b, c` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.7.2 |
| `setp.cmp{.ftz}.type` | **With semantics:** cmp: `eq`, `equ`, `ge`, `geu`, `gt`, `gtu`, `le`, `leu`, `lt`, `ltu`, `nan`, `ne`, `neu`, `num`; ftz: (omitted), `ftz`; type: `f32`, `f64` | `p, a, b` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.7.2 |
| `setp.cmp{.ftz}.type` | **With semantics:** cmp: `eq`, `equ`, `ge`, `geu`, `gt`, `gtu`, `le`, `leu`, `lt`, `ltu`, `nan`, `ne`, `neu`, `num`; ftz: (omitted), `ftz`; type: `bf16`, `f16` | `p, a, b` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.8.2 |
| `setp.cmp.boolop{.ftz}.type` | **With semantics:** cmp: `eq`, `equ`, `ge`, `geu`, `gt`, `gtu`, `le`, `leu`, `lt`, `ltu`, `nan`, `ne`, `neu`, `num`; boolop: `and`, `or`, `xor`; ftz: (omitted), `ftz`; type: `bf16`, `f16` | `p, a, b, c` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.8.2 |
| `setp.cmp.boolop{.ftz}.type` | **With semantics:** cmp: `eq`, `equ`, `ge`, `geu`, `gt`, `gtu`, `le`, `leu`, `lt`, `ltu`, `nan`, `ne`, `neu`, `num`; boolop: `and`, `or`, `xor`; ftz: (omitted), `ftz`; type: `bf16x2`, `f16x2` | `p\|q, a, b, c` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.8.2 |
| `setp.cmp{.ftz}.type` | **With semantics:** cmp: `eq`, `equ`, `ge`, `geu`, `gt`, `gtu`, `le`, `leu`, `lt`, `ltu`, `nan`, `ne`, `neu`, `num`; ftz: (omitted), `ftz`; type: `bf16x2`, `f16x2` | `p\|q, a, b` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.8.2 |
| `setp.cmp{.ftz}.type` | **With semantics:** cmp: `eq`, `equ`, `ge`, `geu`, `gt`, `gtu`, `le`, `leu`, `lt`, `ltu`, `nan`, `ne`, `neu`, `num`; ftz: (omitted), `ftz`; type: `f32`, `f64` | `p\|q, a, b` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.7.2 |
| `sin.mode{.ftz}.type` | **With semantics:** mode: `approx`; ftz: (omitted), `ftz`; type: `f32` | `d, value` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.18 |
| `sqrt.mode{.ftz}.type` | **With semantics:** mode: `approx`, `rm`, `rn`, `rp`, `rz`; ftz: (omitted), `ftz`; type: `f32`, `f64` | `d, value` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.15 |
| `sub{.rnd}{.ftz}{.sat}.type{.srctype}` | **With semantics:** rnd: (omitted), `rm`, `rn`, `rp`, `rz`; ftz: (omitted), `ftz`; sat: (omitted), `sat`; type: `f32`, `f32x2`, `f64`; srctype: (omitted), `bf16`, `f16` | `d, a, b` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.4 |
| `sub{.rnd}{.ftz}{.sat}.type` | **With semantics:** rnd: (omitted), `rn`; ftz: (omitted), `ftz`; sat: (omitted), `sat`; type: `bf16`, `bf16x2`, `f16`, `f16x2` | `d, a, b` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.4.2 |
| `sub.rnd.dtype.atype.ctype` | **With semantics:** rnd: `rz`; dtype: `bf16x2`; atype: `f32x2`; ctype: `f32x2` | `d, a, c` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.5.2 |
| `sub.rnd.ftz.dtype.atype.ctype` | **With semantics:** rnd: `rz`; ftz: `ftz`; dtype: `f16x2`; atype: `f32x2`; ctype: `f32x2` | `d, a, c` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.5.2 |
| `sub{.rnd}.dtype.atype.ctype` | **With semantics:** rnd: (omitted), `rm`, `rn`, `rp`, `rz`; dtype: `f32x2`; atype: `bf16x2`, `f16x2`; ctype: `f32x2` | `d, a, c` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.5.2 |
| `tanh.mode.type` | **With semantics:** mode: `approx`; type: `f32` | `d, value` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.22 |
| `tanh.mode.type` | **With semantics:** mode: `approx`; type: `bf16`, `bf16x2`, `f16`, `f16x2` | `d, value` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.4.9 |
| `testp.op.type` | **With semantics:** op: `finite`, `infinite`, `normal`, `notanumber`, `number`, `subnormal`; type: `f32`, `f64` | `p, a` | local | Core semantics | [THREAD-FLOAT](threads.md#thread-float) | §9.7.3.1 |

### Barriers

The forms listed in PROG-ISA-SYNC-FORMS decode to their own constructors of `Op`; `Op.rule` (PROG-INSTR-RULE) names the rule of each.

Entries: 8 with Core semantics, 8 decode only, 0 rejected.

| Instruction | Modifiers | Operands | Kind | Status | Rule | Manual |
|---|---|---|---|---|---|---|
| `bar{.cta}.action` | **With semantics:** cta: (omitted); action: `arrive`<br>**Decode only:** cta: `cta` | `a, b` | event | Core semantics (1 of 2)<br>Decode only (1 of 2): execution is rejected | [THREAD-BAR](barriers.md#thread-bar) | §9.7.15.1 |
| `bar{.cta}.action.op.type` | **Decode only:** cta: (omitted), `cta`; action: `red`; op: `popc`; type: `u32` | `d, a, c` | event | Decode only: execution is rejected | none | §9.7.15.1 |
| `bar{.cta}.action.op.type` | **Decode only:** cta: (omitted), `cta`; action: `red`; op: `popc`; type: `u32` | `d, a, b, c` | event | Decode only: execution is rejected | none | §9.7.15.1 |
| `bar{.cta}.action.op.type` | **Decode only:** cta: (omitted), `cta`; action: `red`; op: `and`, `or`; type: `pred` | `d, a, c` | event | Decode only: execution is rejected | none | §9.7.15.1 |
| `bar{.cta}.action.op.type` | **Decode only:** cta: (omitted), `cta`; action: `red`; op: `and`, `or`; type: `pred` | `d, a, b, c` | event | Decode only: execution is rejected | none | §9.7.15.1 |
| `bar{.cta}.action` | **With semantics:** cta: (omitted); action: `sync`<br>**Decode only:** cta: `cta` | `a` | event | Core semantics (1 of 2)<br>Decode only (1 of 2): execution is rejected | [THREAD-BAR](barriers.md#thread-bar) | §9.7.15.1 |
| `bar{.cta}.action` | **With semantics:** cta: (omitted); action: `sync`<br>**Decode only:** cta: `cta` | `a, b` | event | Core semantics (1 of 2)<br>Decode only (1 of 2): execution is rejected | [THREAD-BAR](barriers.md#thread-bar) | §9.7.15.1 |
| `barrier{.cta}.action{.aligned}` | **With semantics:** cta: (omitted); action: `arrive`; aligned: (omitted), `aligned`<br>**Decode only:** cta: `cta` | `a, b` | event | Core semantics (2 of 4)<br>Decode only (2 of 4): execution is rejected | [THREAD-BAR](barriers.md#thread-bar) | §9.7.15.1 |
| `barrier.cluster.action{.sem}{.aligned}` | **With semantics:** cluster: `cluster`; action: `arrive`; sem: (omitted), `relaxed`, `release`; aligned: (omitted), `aligned` | none | event | Core semantics | [OBJ-CLUSTER-BARRIER-SYNC](barriers.md#obj-cluster-barrier-sync) | §9.7.15.3 |
| `barrier.cluster.action{.sem}{.aligned}` | **With semantics:** cluster: `cluster`; action: `wait`; sem: (omitted), `acquire`; aligned: (omitted), `aligned` | none | event | Core semantics | [OBJ-CLUSTER-BARRIER-SYNC](barriers.md#obj-cluster-barrier-sync) | §9.7.15.3 |
| `barrier{.cta}.action.op{.aligned}.type` | **Decode only:** cta: (omitted), `cta`; action: `red`; op: `popc`; aligned: (omitted), `aligned`; type: `u32` | `d, a, c` | event | Decode only: execution is rejected | none | §9.7.15.1 |
| `barrier{.cta}.action.op{.aligned}.type` | **Decode only:** cta: (omitted), `cta`; action: `red`; op: `popc`; aligned: (omitted), `aligned`; type: `u32` | `d, a, b, c` | event | Decode only: execution is rejected | none | §9.7.15.1 |
| `barrier{.cta}.action.op{.aligned}.type` | **Decode only:** cta: (omitted), `cta`; action: `red`; op: `and`, `or`; aligned: (omitted), `aligned`; type: `pred` | `d, a, c` | event | Decode only: execution is rejected | none | §9.7.15.1 |
| `barrier{.cta}.action.op{.aligned}.type` | **Decode only:** cta: (omitted), `cta`; action: `red`; op: `and`, `or`; aligned: (omitted), `aligned`; type: `pred` | `d, a, b, c` | event | Decode only: execution is rejected | none | §9.7.15.1 |
| `barrier{.cta}.action{.aligned}` | **With semantics:** cta: (omitted); action: `sync`; aligned: (omitted), `aligned`<br>**Decode only:** cta: `cta` | `a` | event | Core semantics (2 of 4)<br>Decode only (2 of 4): execution is rejected | [THREAD-BAR](barriers.md#thread-bar) | §9.7.15.1 |
| `barrier{.cta}.action{.aligned}` | **With semantics:** cta: (omitted); action: `sync`; aligned: (omitted), `aligned`<br>**Decode only:** cta: `cta` | `a, b` | event | Core semantics (2 of 4)<br>Decode only (2 of 4): execution is rejected | [THREAD-BAR](barriers.md#thread-bar) | §9.7.15.1 |

### Memory fences

`fence.mbarrier_init` decodes to `Op.fenceMbarInit` (PROG-ISA-SYNC-FORMS, THREAD-TMA); every other `fence` and `membar` form decodes to `Op.fence` (PROG-ISA-FENCE) with THREAD-FENCE.

Entries: 8 with Core semantics, 0 decode only, 0 rejected.

| Instruction | Modifiers | Operands | Kind | Status | Rule | Manual |
|---|---|---|---|---|---|---|
| `fence{.sem}.scope` | **With semantics:** sem: (omitted), `acq_rel`, `acquire`, `release`, `sc`; scope: `cluster`, `cta`, `gpu`, `sys` | none | event | Core semantics | [THREAD-FENCE](threads.md#thread-fence) | §9.7.15.4 |
| `fence.op_restrict.sem.scope` | **With semantics:** op_restrict: `mbarrier_init`; sem: `release`; scope: `cluster` | none | event | Core semantics | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.15.4 |
| `fence.proxy.proxykind{.space}` | **With semantics:** proxy: `proxy`; proxykind: `alias`, `async`; space: (omitted), `global`, `shared::cluster`, `shared::cta` | none | event | Core semantics | [THREAD-FENCE](threads.md#thread-fence) | §9.7.15.4 |
| `fence.proxy.direction.proxykind.sem.scope` | **With semantics:** proxy: `proxy`; direction: `fabric::fabric`, `fabric::generic`, `generic::fabric`; proxykind: `alias`; sem: `acquire`, `release`; scope: `sys` | none | event | Core semantics | [THREAD-FENCE](threads.md#thread-fence) | §9.7.15.4 |
| `fence.proxy.proxykind{.space}{.sem}.scope` | **With semantics:** proxy: `proxy`; proxykind: `alias`, `async`; space: (omitted), `global`, `shared::cluster`, `shared::cta`; sem: (omitted), `acq_rel`, `acquire`, `release`, `sc`; scope: `cluster`, `cta`, `gpu`, `sys` | none | event | Core semantics | [THREAD-FENCE](threads.md#thread-fence) | §9.7.15.4 |
| `fence.proxy.proxykind.sem.scope` | **With semantics:** proxy: `proxy`; proxykind: `tensormap::generic`; sem: `acquire`; scope: `cluster`, `cta`, `gpu`, `sys` | `[addr], 128` | event | Core semantics | [THREAD-FENCE](threads.md#thread-fence) | §9.7.15.4 |
| `fence.proxy.proxykind.sem.scope` | **With semantics:** proxy: `proxy`; proxykind: `tensormap::generic`; sem: `release`; scope: `cluster`, `cta`, `gpu`, `sys` | none | event | Core semantics | [THREAD-FENCE](threads.md#thread-fence) | §9.7.15.4 |
| `membar.level` | **With semantics:** level: `cta`, `gl`, `sys` | none | event | Core semantics | [THREAD-FENCE](threads.md#thread-fence) | §9.7.15.4 |

### Mbarrier objects

The forms listed in PROG-ISA-SYNC-FORMS decode to their own constructors of `Op`; `Op.rule` (PROG-INSTR-RULE) names the rule of each.

Entries: 10 with Core semantics, 38 decode only, 0 rejected.

| Instruction | Modifiers | Operands | Kind | Status | Rule | Manual |
|---|---|---|---|---|---|---|
| `mbarrier.action{.sem}{.scope}{.space}.type` | **With semantics:** action: `arrive`; sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`; space: `shared`, `shared::cluster`, `shared::cta`; type: `b64`<br>**Decode only:** space: (omitted) | `_, [addr], count` | event | Core semantics (15 of 20)<br>Decode only (5 of 20): execution is rejected | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.15.16.16 |
| `mbarrier.action{.sem}{.scope}{.space}.type` | **With semantics:** action: `arrive`; sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`; space: `shared`, `shared::cta`; type: `b64`<br>**Decode only:** space: (omitted) | `state, [addr], count` | event | Core semantics (10 of 15)<br>Decode only (5 of 15): execution is rejected | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.15.16.16 |
| `mbarrier.action{.sem}{.scope}{.space}.type` | **Decode only:** action: `arrive_drop`; sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cluster`, `shared::cta`; type: `b64` | `_, [addr], count` | event | Decode only: execution is rejected | none | §9.7.15.16.17 |
| `mbarrier.action{.sem}{.scope}{.space}.type` | **Decode only:** action: `arrive_drop`; sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `state, [addr], count` | event | Decode only: execution is rejected | none | §9.7.15.16.17 |
| `mbarrier.action.expect_tx{.sem}{.scope}{.space}.type` | **Decode only:** action: `arrive_drop`; expect_tx: `expect_tx`; sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cluster`, `shared::cta`; type: `b64` | `_, [addr], tx_count` | event | Decode only: execution is rejected | none | §9.7.15.16.17 |
| `mbarrier.action.expect_tx{.sem}{.scope}.space.multicast.type` | **Decode only:** action: `arrive_drop`; expect_tx: `expect_tx`; sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`; space: `shared::cluster`; multicast: `multicast::cluster::32b`; type: `b64` | `_, [addr], tx_count, cta_mask` | event | Decode only: execution is rejected | none | §9.7.15.16.17 |
| `mbarrier.action.expect_tx{.sem}{.scope}{.space}.type` | **Decode only:** action: `arrive_drop`; expect_tx: `expect_tx`; sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `state, [addr], count` | event | Decode only: execution is rejected | none | §9.7.15.16.17 |
| `mbarrier.action{.sem}{.scope}.space.multicast.type` | **Decode only:** action: `arrive_drop`; sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`; space: `shared::cluster`; multicast: `multicast::cluster::32b`; type: `b64` | `_, [addr], count, cta_mask` | event | Decode only: execution is rejected | none | §9.7.15.16.17 |
| `mbarrier.action{.sem}{.scope}.space.multicast.type` | **Decode only:** action: `arrive_drop`; sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`; space: `shared::cluster`; multicast: `multicast::cluster::32b`; type: `b64` | `_, [addr], cta_mask` | event | Decode only: execution is rejected | none | §9.7.15.16.17 |
| `mbarrier.action.nocomplete{.sem}{.scope}{.space}.type` | **Decode only:** action: `arrive_drop`; nocomplete: `noComplete`; sem: (omitted), `release`; scope: (omitted), `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `state, [addr], count` | event | Decode only: execution is rejected | none | §9.7.15.16.17 |
| `mbarrier.action.nocomplete{.sem}{.scope}{.space}.type` | **Decode only:** action: `arrive_drop`; nocomplete: `noComplete`; sem: (omitted), `release`; scope: (omitted), `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `_, [addr], count` | event | Decode only: execution is rejected | none | §9.7.15.16.17 |
| `mbarrier.action{.sem}{.scope}{.space}.type` | **Decode only:** action: `arrive_drop`; sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cluster`, `shared::cta`; type: `b64` | `_, [addr]` | event | Decode only: execution is rejected | none | §9.7.15.16.17 |
| `mbarrier.action{.sem}{.scope}{.space}.type` | **Decode only:** action: `arrive_drop`; sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `state, [addr]` | event | Decode only: execution is rejected | none | §9.7.15.16.17 |
| `mbarrier.action.expect_tx{.sem}{.scope}{.space}.type` | **With semantics:** action: `arrive`; expect_tx: `expect_tx`; sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`; space: `shared`, `shared::cluster`, `shared::cta`; type: `b64`<br>**Decode only:** space: (omitted) | `_, [addr], tx_count` | event | Core semantics (15 of 20)<br>Decode only (5 of 20): execution is rejected | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.15.16.16 |
| `mbarrier.action.expect_tx{.sem}{.scope}.space.multicast.type` | **Decode only:** action: `arrive`; expect_tx: `expect_tx`; sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`; space: `shared::cluster`; multicast: `multicast::cluster::32b`; type: `b64` | `_, [addr], tx_count, cta_mask` | event | Decode only: execution is rejected | none | §9.7.15.16.16 |
| `mbarrier.action.expect_tx{.sem}{.scope}{.space}.type` | **With semantics:** action: `arrive`; expect_tx: `expect_tx`; sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`; space: `shared`, `shared::cta`; type: `b64`<br>**Decode only:** space: (omitted) | `state, [addr], count` | event | Core semantics (10 of 15)<br>Decode only (5 of 15): execution is rejected | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.15.16.16 |
| `mbarrier.action{.sem}{.scope}.space.multicast.type` | **Decode only:** action: `arrive`; sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`; space: `shared::cluster`; multicast: `multicast::cluster::32b`; type: `b64` | `_, [addr], count, cta_mask` | event | Decode only: execution is rejected | none | §9.7.15.16.16 |
| `mbarrier.action{.sem}{.scope}.space.multicast.type` | **Decode only:** action: `arrive`; sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`; space: `shared::cluster`; multicast: `multicast::cluster::32b`; type: `b64` | `_, [addr], cta_mask` | event | Decode only: execution is rejected | none | §9.7.15.16.16 |
| `mbarrier.action.nocomplete{.sem}{.scope}{.space}.type` | **Decode only:** action: `arrive`; nocomplete: `noComplete`; sem: (omitted), `release`; scope: (omitted), `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `state, [addr], count` | event | Decode only: execution is rejected | none | §9.7.15.16.16 |
| `mbarrier.action.nocomplete{.sem}{.scope}{.space}.type` | **Decode only:** action: `arrive`; nocomplete: `noComplete`; sem: (omitted), `release`; scope: (omitted), `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `_, [addr], count` | event | Decode only: execution is rejected | none | §9.7.15.16.16 |
| `mbarrier.action{.sem}{.scope}{.space}.type` | **With semantics:** action: `arrive`; sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`; space: `shared`, `shared::cluster`, `shared::cta`; type: `b64`<br>**Decode only:** space: (omitted) | `_, [addr]` | event | Core semantics (15 of 20)<br>Decode only (5 of 20): execution is rejected | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.15.16.16 |
| `mbarrier.action{.sem}{.scope}{.space}.type` | **With semantics:** action: `arrive`; sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`; space: `shared`, `shared::cta`; type: `b64`<br>**Decode only:** space: (omitted) | `state, [addr]` | event | Core semantics (10 of 15)<br>Decode only (5 of 15): execution is rejected | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.15.16.16 |
| `mbarrier.action.layout{.space}.type` | **Decode only:** action: `check_layout`; layout: `layout::v0`, `layout::v1`; space: (omitted), `shared::cta`; type: `b64` | `matches, [addr]` | event | Decode only: execution is rejected | none | §9.7.15.16.21 |
| `mbarrier.action{.sem}{.scope}{.space}.type` | **Decode only:** action: `complete_tx`; sem: (omitted), `relaxed`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cluster`, `shared::cta`; type: `b64` | `[addr], tx_count` | event | Decode only: execution is rejected | none | §9.7.15.16.15 |
| `mbarrier.action{.sem}{.scope}.space.multicast.type` | **Decode only:** action: `complete_tx`; sem: (omitted), `relaxed`; scope: (omitted), `cluster`, `cta`; space: `shared::cluster`; multicast: `multicast::cluster::32b`; type: `b64` | `[addr], tx_count, cta_mask` | event | Decode only: execution is rejected | none | §9.7.15.16.15 |
| `mbarrier.action{.sem}{.scope}{.space}.type` | **Decode only:** action: `expect_tx`; sem: (omitted), `relaxed`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cluster`, `shared::cta`; type: `b64` | `[addr], tx_count` | event | Decode only: execution is rejected | none | §9.7.15.16.14 |
| `mbarrier.action{.sem}{.scope}.space.multicast.type` | **Decode only:** action: `expect_tx`; sem: (omitted), `relaxed`; scope: (omitted), `cluster`, `cta`; space: `shared::cluster`; multicast: `multicast::cluster::32b`; type: `b64` | `[addr], tx_count, cta_mask` | event | Decode only: execution is rejected | none | §9.7.15.16.14 |
| `mbarrier.action{.layout}{.space}.type` | **With semantics:** action: `init`; layout: (omitted); space: `shared`, `shared::cta`; type: `b64`<br>**Decode only:** layout: `layout::v0`, `layout::v1`; space: (omitted) | `[addr], count` | event | Core semantics (2 of 9)<br>Decode only (7 of 9): execution is rejected | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.15.16.12 |
| `mbarrier.action{.space}.type` | **With semantics:** action: `inval`; space: `shared`, `shared::cta`; type: `b64`<br>**Decode only:** space: (omitted) | `[addr]` | event | Core semantics (2 of 3)<br>Decode only (1 of 3): execution is rejected | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.15.16.13 |
| `mbarrier.action{.layout}.type` | **Decode only:** action: `pending_count`; layout: (omitted), `layout::v0`; type: `b64` | `count, state` | local | Decode only: an `Assumption.localRule` may give it a meaning | none | §9.7.15.16.20 |
| `mbarrier.action{.phase_type}{.sem}{.scope}{.space}.type` | **Decode only:** action: `test_wait`; phase_type: (omitted), `phase_type::primary`; sem: (omitted), `acquire`, `relaxed`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `wait_complete, [addr], state` | event | Decode only: execution is rejected | none | §9.7.15.16.19 |
| `mbarrier.action.parity{.phase_type}{.sem}{.scope}{.space}.type` | **Decode only:** action: `test_wait`; parity: `parity`; phase_type: (omitted), `phase_type::conditional`, `phase_type::primary`; sem: (omitted), `acquire`, `relaxed`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `wait_complete, [addr], phase` | event | Decode only: execution is rejected | none | §9.7.15.16.19 |
| `mbarrier.action.parity.phase_type{.sem}{.scope}{.space}.type` | **Decode only:** action: `test_wait`; parity: `parity`; phase_type: `phase_type::primary`; sem: (omitted), `acquire`, `relaxed`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `wait_complete\|report_predicate, [addr], phase` | event | Decode only: execution is rejected | none | §9.7.15.16.19 |
| `mbarrier.action.parity.phase_type{.sem}{.scope}{.space}.type` | **Decode only:** action: `test_wait`; parity: `parity`; phase_type: `phase_type::primary`; sem: (omitted), `acquire`, `relaxed`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `wait_complete\|report_predicate, report_value, [addr], phase` | event | Decode only: execution is rejected | none | §9.7.15.16.19 |
| `mbarrier.action.phase_type{.sem}{.scope}{.space}.type` | **Decode only:** action: `test_wait`; phase_type: `phase_type::primary`; sem: (omitted), `acquire`, `relaxed`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `wait_complete\|report_predicate, [addr], phase` | event | Decode only: execution is rejected | none | §9.7.15.16.19 |
| `mbarrier.action.phase_type{.sem}{.scope}{.space}.type` | **Decode only:** action: `test_wait`; phase_type: `phase_type::primary`; sem: (omitted), `acquire`, `relaxed`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `wait_complete\|report_predicate, report_value, [addr], phase` | event | Decode only: execution is rejected | none | §9.7.15.16.19 |
| `mbarrier.action{.phase_type}{.sem}{.scope}{.space}.type` | **Decode only:** action: `try_wait`; phase_type: (omitted), `phase_type::primary`; sem: (omitted), `acquire`, `relaxed`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `wait_complete, [addr], state` | event | Decode only: execution is rejected | none | §9.7.15.16.19 |
| `mbarrier.action{.phase_type}{.sem}{.scope}{.space}.type` | **Decode only:** action: `try_wait`; phase_type: (omitted), `phase_type::primary`; sem: (omitted), `acquire`, `relaxed`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `wait_complete, [addr], state, time_hint` | event | Decode only: execution is rejected | none | §9.7.15.16.19 |
| `mbarrier.action.parity{.phase_type}{.sem}{.scope}{.space}.type` | **With semantics:** action: `try_wait`; parity: `parity`; phase_type: (omitted); sem: (omitted), `acquire`, `relaxed`; scope: (omitted), `cluster`, `cta`; space: `shared`, `shared::cta`; type: `b64`<br>**Decode only:** phase_type: `phase_type::conditional`, `phase_type::primary`; space: (omitted) | `wait_complete, [addr], phase, time_hint` | event | Core semantics (10 of 45)<br>Decode only (35 of 45): execution is rejected | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.15.16.19 |
| `mbarrier.action.parity{.phase_type}{.sem}{.scope}{.space}.type` | **With semantics:** action: `try_wait`; parity: `parity`; phase_type: (omitted); sem: (omitted), `acquire`, `relaxed`; scope: (omitted), `cluster`, `cta`; space: `shared`, `shared::cta`; type: `b64`<br>**Decode only:** phase_type: `phase_type::conditional`, `phase_type::primary`; space: (omitted) | `wait_complete, [addr], phase` | event | Core semantics (10 of 45)<br>Decode only (35 of 45): execution is rejected | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.15.16.19 |
| `mbarrier.action.parity.phase_type{.sem}{.scope}{.space}.type` | **Decode only:** action: `try_wait`; parity: `parity`; phase_type: `phase_type::primary`; sem: (omitted), `acquire`, `relaxed`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `wait_complete\|report_predicate, [addr], phase` | event | Decode only: execution is rejected | none | §9.7.15.16.19 |
| `mbarrier.action.parity.phase_type{.sem}{.scope}{.space}.type` | **Decode only:** action: `try_wait`; parity: `parity`; phase_type: `phase_type::primary`; sem: (omitted), `acquire`, `relaxed`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `wait_complete\|report_predicate, [addr], phase, time_hint` | event | Decode only: execution is rejected | none | §9.7.15.16.19 |
| `mbarrier.action.parity.phase_type{.sem}{.scope}{.space}.type` | **Decode only:** action: `try_wait`; parity: `parity`; phase_type: `phase_type::primary`; sem: (omitted), `acquire`, `relaxed`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `wait_complete\|report_predicate, report_value, [addr], phase` | event | Decode only: execution is rejected | none | §9.7.15.16.19 |
| `mbarrier.action.parity.phase_type{.sem}{.scope}{.space}.type` | **Decode only:** action: `try_wait`; parity: `parity`; phase_type: `phase_type::primary`; sem: (omitted), `acquire`, `relaxed`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `wait_complete\|report_predicate, report_value, [addr], phase, time_hint` | event | Decode only: execution is rejected | none | §9.7.15.16.19 |
| `mbarrier.action.phase_type{.sem}{.scope}{.space}.type` | **Decode only:** action: `try_wait`; phase_type: `phase_type::primary`; sem: (omitted), `acquire`, `relaxed`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `wait_complete\|report_predicate, [addr], phase` | event | Decode only: execution is rejected | none | §9.7.15.16.19 |
| `mbarrier.action.phase_type{.sem}{.scope}{.space}.type` | **Decode only:** action: `try_wait`; phase_type: `phase_type::primary`; sem: (omitted), `acquire`, `relaxed`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `wait_complete\|report_predicate, [addr], phase, time_hint` | event | Decode only: execution is rejected | none | §9.7.15.16.19 |
| `mbarrier.action.phase_type{.sem}{.scope}{.space}.type` | **Decode only:** action: `try_wait`; phase_type: `phase_type::primary`; sem: (omitted), `acquire`, `relaxed`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `wait_complete\|report_predicate, report_value, [addr], phase` | event | Decode only: execution is rejected | none | §9.7.15.16.19 |
| `mbarrier.action.phase_type{.sem}{.scope}{.space}.type` | **Decode only:** action: `try_wait`; phase_type: `phase_type::primary`; sem: (omitted), `acquire`, `relaxed`; scope: (omitted), `cluster`, `cta`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `wait_complete\|report_predicate, report_value, [addr], phase, time_hint` | event | Decode only: execution is rejected | none | §9.7.15.16.19 |

### Asynchronous copies

The forms listed in PROG-ISA-SYNC-FORMS decode to their own constructors of `Op`; `Op.rule` (PROG-INSTR-RULE) names the rule of each.

Entries: 41 with Core semantics, 47 decode only, 0 rejected.

| Instruction | Modifiers | Operands | Kind | Status | Rule | Manual |
|---|---|---|---|---|---|---|
| `applypriority.api.kind{.src}.completion.priority` | **Decode only:** api: `async`; kind: `bulk`; src: (omitted), `global`; completion: `bulk_group`; priority: `L2::evict_normal` | `[addr], size` | event | Decode only: execution is rejected | none | §9.7.10.18 |
| `applypriority.api.kind.unit.dim{.src}.completion{.load_mode}.priority` | **Decode only:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `1d`, `2d`, `3d`, `4d`, `5d`; src: (omitted), `global`; completion: `bulk_group`; load_mode: (omitted), `tile`, `tile::gather4`; priority: `L2::evict_normal` | `[tmap, {coords...}]` | event | Decode only: execution is rejected | none | §9.7.10.19 |
| `applypriority.api.kind.unit.dim{.src}.completion.load_mode.priority` | **Decode only:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `3d`, `4d`, `5d`; src: (omitted), `global`; completion: `bulk_group`; load_mode: `im2col`, `im2col::w`, `im2col::w::128`; priority: `L2::evict_normal` | `[tmap, {coords...}], {im2col_info...}` | event | Decode only: execution is rejected | none | §9.7.10.19 |
| `applypriority.api.kind.unit.dim{.src}.completion{.load_mode}.priority.override_address` | **Decode only:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `1d`, `2d`, `3d`, `4d`, `5d`; src: (omitted), `global`; completion: `bulk_group`; load_mode: (omitted), `tile`, `tile::gather4`; priority: `L2::evict_normal`; override_address: `override::global_address` | `[tmap, global_address, {coords...}]` | event | Decode only: execution is rejected | none | §9.7.10.19 |
| `applypriority.api.kind.unit.dim{.src}.completion.load_mode.priority.override_address` | **Decode only:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `3d`, `4d`, `5d`; src: (omitted), `global`; completion: `bulk_group`; load_mode: `im2col`, `im2col::w`, `im2col::w::128`; priority: `L2::evict_normal`; override_address: `override::global_address` | `[tmap, global_address, {coords...}], {im2col_info...}` | event | Decode only: execution is rejected | none | §9.7.10.19 |
| `applypriority.api.kind.unit.dim{.src}.completion{.load_mode}.priority.override_address.override_attribute` | **Decode only:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `1d`; src: (omitted), `global`; completion: `bulk_group`; load_mode: (omitted), `tile`; priority: `L2::evict_normal`; override_address: `override::global_address`; override_attribute: `override::global_dim` | `[tmap, global_address, {tensor_size...}, {coords...}]` | event | Decode only: execution is rejected | none | §9.7.10.19 |
| `applypriority.api.kind.unit.dim{.src}.completion{.load_mode}.priority.override_address.override_attribute` | **Decode only:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `2d`, `3d`, `4d`, `5d`; src: (omitted), `global`; completion: `bulk_group`; load_mode: (omitted), `tile`; priority: `L2::evict_normal`; override_address: `override::global_address`; override_attribute: `override::global_dim_stride` | `[tmap, global_address, {tensor_size...}, {lower_stride...}, upper_stride, {coords...}]` | event | Decode only: execution is rejected | none | §9.7.10.19 |
| `cp.api.kind.action` | **With semantics:** api: `async`; kind: `bulk`; action: `commit_group` | none | local | Core semantics | [THREAD-TENSOR-STORE](async.md#thread-tensor-store) | §9.7.10.28.6.1 |
| `cp.api.kind{.sem}{.scope}.dst.src.completion{.multicast}{.cache}{.type}` | **With semantics:** api: `async`; kind: `bulk`; sem: (omitted), `relaxed`, `weak`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; dst: `shared::cluster`; src: `global`; completion: `mbarrier::complete_tx::bytes`; multicast: (omitted), `multicast::cluster`; cache: (omitted), `L2::cache_hint`; type: (omitted), `b128` | `[dst_mem], [src_mem], size, [mbar], {cta_mask}, {cache_policy}` | event | Core semantics | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.10.28.4.1 |
| `cp.api.kind{.sem}{.scope}.dst.src.completion.multicast{.cache}{.type}` | **With semantics:** api: `async`; kind: `bulk`; sem: (omitted), `relaxed`, `weak`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; dst: `shared::cluster`; src: `global`; completion: `mbarrier::complete_tx::bytes`; multicast: `multicast::cluster::16b`; cache: (omitted), `L2::cache_hint`; type: (omitted), `b128` | `[dst_mem], [src_mem], size, [mbar], cta_mask, {cache_policy}` | event | Core semantics | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.10.28.4.1 |
| `cp.api.kind{.sem}{.scope}.dst.src.completion.multicast{.cache}{.type}` | **With semantics:** api: `async`; kind: `bulk`; sem: (omitted), `relaxed`, `weak`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; dst: `shared::cluster`; src: `global`; completion: `mbarrier::complete_tx::bytes`; multicast: `multicast::cluster::32b`; cache: (omitted), `L2::cache_hint`; type: (omitted), `b128` | `[dst_mem], [src_mem], size, [mbar], cta_mask, {cache_policy}` | event | Core semantics | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.10.28.4.1 |
| `cp.api.kind{.sem}{.scope}.dst.src.completion.report{.multicast}{.cache}{.type}` | **With semantics:** api: `async`; kind: `bulk`; sem: (omitted), `relaxed`, `weak`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; dst: `shared::cluster`; src: `global`; completion: `mbarrier::complete_tx::bytes`; report: `mbarrier::report::disabled`; multicast: (omitted), `multicast::cluster`, `multicast::cluster::16b`, `multicast::cluster::32b`; cache: (omitted), `L2::cache_hint`; type: (omitted), `b128`<br>**Decode only:** report: `mbarrier::report::validity::per_16bytes::8`, `mbarrier::report::validity::per_16bytes::80`, `mbarrier::report::validity::per_16bytes::8000`, `mbarrier::report::validity::per_16bytes::80000000`, `mbarrier::report::validity::per_element::ff` | `[dst_mem], [src_mem], size, [mbar], {cta_mask}, {cache_policy}` | event | Core semantics (48 of 288)<br>Decode only (240 of 288): execution is rejected | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.10.28.4.1 |
| `cp.api.kind{.sem}{.scope}.dst.src.completion{.cache}{.ignore_oob}{.type}` | **With semantics:** api: `async`; kind: `bulk`; sem: (omitted), `relaxed`, `weak`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; dst: `shared::cta`; src: `global`; completion: `mbarrier::complete_tx::bytes`; cache: (omitted), `L2::cache_hint`; ignore_oob: (omitted), `ignore_oob`; type: (omitted), `b128` | `[dst_mem], [src_mem], size, {ignore_bytes_left}, {ignore_bytes_right}, [mbar], {cache_policy}` | event | Core semantics | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.10.28.4.1 |
| `cp.api.kind{.sem}{.scope}.dst.src.completion.report{.cache}{.ignore_oob}{.type}` | **With semantics:** api: `async`; kind: `bulk`; sem: (omitted), `relaxed`, `weak`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; dst: `shared::cta`; src: `global`; completion: `mbarrier::complete_tx::bytes`; report: `mbarrier::report::disabled`; cache: (omitted), `L2::cache_hint`; ignore_oob: (omitted), `ignore_oob`; type: (omitted), `b128`<br>**Decode only:** report: `mbarrier::report::validity::per_16bytes::8`, `mbarrier::report::validity::per_16bytes::80`, `mbarrier::report::validity::per_16bytes::8000`, `mbarrier::report::validity::per_16bytes::80000000`, `mbarrier::report::validity::per_element::ff` | `[dst_mem], [src_mem], size, {ignore_bytes_left}, {ignore_bytes_right}, [mbar], {cache_policy}` | event | Core semantics (24 of 84)<br>Decode only (60 of 84): execution is rejected | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.10.28.4.1 |
| `cp.api.kind.op.level.src{.cache}` | **With semantics:** api: `async`; kind: `bulk`; op: `prefetch`; level: `L2`; src: `global`; cache: (omitted), `L2::cache_hint` | `[src_mem], size, {cache_policy}` | event | Core semantics | [THREAD-TENSOR-PREFETCH](async.md#thread-tensor-prefetch) | §9.7.10.28.4.3 |
| `cp.api.kind.op.level.src.priority` | **With semantics:** api: `async`; kind: `bulk`; op: `prefetch`; level: `L2`; src: `global`; priority: `L2::evict_last` | `[src_mem], size` | event | Core semantics | [THREAD-TENSOR-PREFETCH](async.md#thread-tensor-prefetch) | §9.7.10.28.4.3 |
| `cp.api.kind{.sem}{.scope}.dst.src.completion{.type}` | **With semantics:** api: `async`; kind: `bulk`; sem: (omitted), `relaxed`, `weak`; scope: (omitted), `cluster`, `cta`; dst: `shared::cluster`; src: `shared::cta`; completion: `mbarrier::complete_tx::bytes`; type: (omitted), `b128` | `[dst_mem], [src_mem], size, [mbar]` | event | Core semantics | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.10.28.4.1 |
| `cp.api.kind{.sem}{.scope}.dst.src.completion{.cache}{.cp_mask}{.type}` | **With semantics:** api: `async`; kind: `bulk`; sem: (omitted), `relaxed`, `weak`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; dst: `global`; src: `shared::cta`; completion: `bulk_group`; cache: (omitted), `L2::cache_hint`; cp_mask: (omitted), `cp_mask`; type: (omitted), `b128` | `[dst_mem], [src_mem], size, {cache_policy}, {byte_mask}` | event | Core semantics | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.10.28.4.1 |
| `cp.api.kind.unit.dim.dst.src{.load_mode}.completion{.multicast}{.cta_group}{.cache}` | **With semantics:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `1d`, `2d`, `3d`, `4d`, `5d`; dst: `shared::cluster`; src: `global`; load_mode: (omitted), `tile`, `tile::gather4`; completion: `mbarrier::complete_tx::bytes`; multicast: (omitted), `multicast::cluster`; cta_group: (omitted), `cta_group::1`, `cta_group::2`; cache: (omitted), `L2::cache_hint` | `[dst_mem], [tmap, {coords...}], [mbar], {cta_mask}, {cache_policy}` | event | Core semantics | [THREAD-TENSOR-ISSUE](async.md#thread-tensor-issue) | §9.7.10.28.5.3 |
| `cp.api.kind.unit.dim.dst.src.load_mode.completion{.report}{.multicast}{.cta_group}{.cache}` | **Decode only:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `3d`, `4d`, `5d`; dst: `shared::cluster`; src: `global`; load_mode: `im2col`, `im2col::w`, `im2col::w::128`; completion: `mbarrier::complete_tx::bytes`; report: (omitted), `mbarrier::report::disabled`, `mbarrier::report::validity::per_16bytes::8`, `mbarrier::report::validity::per_16bytes::80`, `mbarrier::report::validity::per_16bytes::8000`, `mbarrier::report::validity::per_16bytes::80000000`, `mbarrier::report::validity::per_element::ff`; multicast: (omitted), `multicast::cluster`, `multicast::cluster::16b`, `multicast::cluster::32b`; cta_group: (omitted), `cta_group::1`, `cta_group::2`; cache: (omitted), `L2::cache_hint` | `[dst_mem], [tmap, {coords...}], [mbar], {im2col_info...}, {cta_mask}, {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.3 |
| `cp.api.kind.unit.dim.dst.src{.load_mode}.completion.multicast{.cta_group}{.cache}` | **With semantics:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `1d`, `2d`, `3d`, `4d`, `5d`; dst: `shared::cluster`; src: `global`; load_mode: (omitted), `tile`, `tile::gather4`; completion: `mbarrier::complete_tx::bytes`; multicast: `multicast::cluster::16b`; cta_group: (omitted), `cta_group::1`, `cta_group::2`; cache: (omitted), `L2::cache_hint` | `[dst_mem], [tmap, {coords...}], [mbar], cta_mask, {cache_policy}` | event | Core semantics | [THREAD-TENSOR-ISSUE](async.md#thread-tensor-issue) | §9.7.10.28.5.3 |
| `cp.api.kind.unit.dim.dst.src{.load_mode}.completion.multicast{.cta_group}{.cache}` | **With semantics:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `1d`, `2d`, `3d`, `4d`, `5d`; dst: `shared::cluster`; src: `global`; load_mode: (omitted), `tile`, `tile::gather4`; completion: `mbarrier::complete_tx::bytes`; multicast: `multicast::cluster::32b`; cta_group: (omitted), `cta_group::1`, `cta_group::2`; cache: (omitted), `L2::cache_hint` | `[dst_mem], [tmap, {coords...}], [mbar], cta_mask, {cache_policy}` | event | Core semantics | [THREAD-TENSOR-ISSUE](async.md#thread-tensor-issue) | §9.7.10.28.5.3 |
| `cp.api.kind.unit.dim.dst.src{.load_mode}.completion{.report}{.multicast}{.cta_group}{.cache}.override_address` | **Decode only:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `1d`, `2d`, `3d`, `4d`, `5d`; dst: `shared::cluster`; src: `global`; load_mode: (omitted), `tile`, `tile::gather4`; completion: `mbarrier::complete_tx::bytes`; report: (omitted), `mbarrier::report::disabled`, `mbarrier::report::validity::per_16bytes::8`, `mbarrier::report::validity::per_16bytes::80`, `mbarrier::report::validity::per_16bytes::8000`, `mbarrier::report::validity::per_16bytes::80000000`, `mbarrier::report::validity::per_element::ff`; multicast: (omitted), `multicast::cluster`, `multicast::cluster::16b`, `multicast::cluster::32b`; cta_group: (omitted), `cta_group::1`, `cta_group::2`; cache: (omitted), `L2::cache_hint`; override_address: `override::global_address` | `[dst_mem], [tmap, global_address, {coords...}], [mbar], {cta_mask}, {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.3 |
| `cp.api.kind.unit.dim.dst.src.load_mode.completion{.report}{.multicast}{.cta_group}{.cache}.override_address` | **Decode only:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `3d`, `4d`, `5d`; dst: `shared::cluster`; src: `global`; load_mode: `im2col`, `im2col::w`, `im2col::w::128`; completion: `mbarrier::complete_tx::bytes`; report: (omitted), `mbarrier::report::disabled`, `mbarrier::report::validity::per_16bytes::8`, `mbarrier::report::validity::per_16bytes::80`, `mbarrier::report::validity::per_16bytes::8000`, `mbarrier::report::validity::per_16bytes::80000000`, `mbarrier::report::validity::per_element::ff`; multicast: (omitted), `multicast::cluster`, `multicast::cluster::16b`, `multicast::cluster::32b`; cta_group: (omitted), `cta_group::1`, `cta_group::2`; cache: (omitted), `L2::cache_hint`; override_address: `override::global_address` | `[dst_mem], [tmap, global_address, {coords...}], [mbar], {im2col_info...}, {cta_mask}, {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.3 |
| `cp.api.kind.unit.dim.dst.src{.load_mode}.completion{.report}{.multicast}{.cta_group}{.cache}.override_address.override_attribute` | **Decode only:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `1d`; dst: `shared::cluster`; src: `global`; load_mode: (omitted), `tile`; completion: `mbarrier::complete_tx::bytes`; report: (omitted), `mbarrier::report::disabled`, `mbarrier::report::validity::per_16bytes::8`, `mbarrier::report::validity::per_16bytes::80`, `mbarrier::report::validity::per_16bytes::8000`, `mbarrier::report::validity::per_16bytes::80000000`, `mbarrier::report::validity::per_element::ff`; multicast: (omitted), `multicast::cluster::32b`; cta_group: (omitted), `cta_group::1`, `cta_group::2`; cache: (omitted), `L2::cache_hint`; override_address: `override::global_address`; override_attribute: `override::global_dim` | `[dst_mem], [tmap, global_address, {tensor_size...}, {coords...}], [mbar], {cta_mask}, {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.3 |
| `cp.api.kind.unit.dim.dst.src{.load_mode}.completion{.report}{.multicast}{.cta_group}{.cache}.override_address.override_attribute` | **Decode only:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `2d`, `3d`, `4d`, `5d`; dst: `shared::cluster`; src: `global`; load_mode: (omitted), `tile`; completion: `mbarrier::complete_tx::bytes`; report: (omitted), `mbarrier::report::disabled`, `mbarrier::report::validity::per_16bytes::8`, `mbarrier::report::validity::per_16bytes::80`, `mbarrier::report::validity::per_16bytes::8000`, `mbarrier::report::validity::per_16bytes::80000000`, `mbarrier::report::validity::per_element::ff`; multicast: (omitted), `multicast::cluster::32b`; cta_group: (omitted), `cta_group::1`, `cta_group::2`; cache: (omitted), `L2::cache_hint`; override_address: `override::global_address`; override_attribute: `override::global_dim_stride` | `[dst_mem], [tmap, global_address, {tensor_size...}, {lower_stride...}, upper_stride, {coords...}], [mbar], {cta_mask}, {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.3 |
| `cp.api.kind.unit.dim.dst.src{.load_mode}.completion.report{.multicast}{.cta_group}{.cache}` | **With semantics:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `1d`, `2d`, `3d`, `4d`, `5d`; dst: `shared::cluster`; src: `global`; load_mode: (omitted), `tile`, `tile::gather4`; completion: `mbarrier::complete_tx::bytes`; report: `mbarrier::report::disabled`; multicast: (omitted), `multicast::cluster`, `multicast::cluster::16b`, `multicast::cluster::32b`; cta_group: (omitted), `cta_group::1`, `cta_group::2`; cache: (omitted), `L2::cache_hint`<br>**Decode only:** report: `mbarrier::report::validity::per_16bytes::8`, `mbarrier::report::validity::per_16bytes::80`, `mbarrier::report::validity::per_16bytes::8000`, `mbarrier::report::validity::per_16bytes::80000000`, `mbarrier::report::validity::per_element::ff` | `[dst_mem], [tmap, {coords...}], [mbar], {cta_mask}, {cache_policy}` | event | Core semantics (264 of 1584)<br>Decode only (1320 of 1584): execution is rejected | [THREAD-TENSOR-ISSUE](async.md#thread-tensor-issue) | §9.7.10.28.5.3 |
| `cp.api.kind.unit.dim.dst.src{.load_mode}.completion{.cta_group}{.cache}` | **With semantics:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `1d`, `2d`, `3d`, `4d`, `5d`; dst: `shared::cta`; src: `global`; load_mode: (omitted), `tile`, `tile::gather4`; completion: `mbarrier::complete_tx::bytes`; cta_group: (omitted), `cta_group::1`, `cta_group::2`; cache: (omitted), `L2::cache_hint` | `[dst_mem], [tmap, {coords...}], [mbar], {cache_policy}` | event | Core semantics | [THREAD-TENSOR-ISSUE](async.md#thread-tensor-issue) | §9.7.10.28.5.3 |
| `cp.api.kind.unit.dim.dst.src.load_mode.completion{.report}{.cta_group}{.cache}` | **Decode only:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `3d`, `4d`, `5d`; dst: `shared::cta`; src: `global`; load_mode: `im2col`, `im2col::w`, `im2col::w::128`; completion: `mbarrier::complete_tx::bytes`; report: (omitted), `mbarrier::report::disabled`, `mbarrier::report::validity::per_16bytes::8`, `mbarrier::report::validity::per_16bytes::80`, `mbarrier::report::validity::per_16bytes::8000`, `mbarrier::report::validity::per_16bytes::80000000`, `mbarrier::report::validity::per_element::ff`; cta_group: (omitted), `cta_group::1`, `cta_group::2`; cache: (omitted), `L2::cache_hint` | `[dst_mem], [tmap, {coords...}], [mbar], {im2col_info...}, {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.3 |
| `cp.api.kind.unit.dim.dst.src{.load_mode}.completion{.report}{.cta_group}{.cache}.override_address` | **Decode only:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `1d`, `2d`, `3d`, `4d`, `5d`; dst: `shared::cta`; src: `global`; load_mode: (omitted), `tile`, `tile::gather4`; completion: `mbarrier::complete_tx::bytes`; report: (omitted), `mbarrier::report::disabled`, `mbarrier::report::validity::per_16bytes::8`, `mbarrier::report::validity::per_16bytes::80`, `mbarrier::report::validity::per_16bytes::8000`, `mbarrier::report::validity::per_16bytes::80000000`, `mbarrier::report::validity::per_element::ff`; cta_group: (omitted), `cta_group::1`, `cta_group::2`; cache: (omitted), `L2::cache_hint`; override_address: `override::global_address` | `[dst_mem], [tmap, global_address, {coords...}], [mbar], {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.3 |
| `cp.api.kind.unit.dim.dst.src.load_mode.completion{.report}{.cta_group}{.cache}.override_address` | **Decode only:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `3d`, `4d`, `5d`; dst: `shared::cta`; src: `global`; load_mode: `im2col`, `im2col::w`, `im2col::w::128`; completion: `mbarrier::complete_tx::bytes`; report: (omitted), `mbarrier::report::disabled`, `mbarrier::report::validity::per_16bytes::8`, `mbarrier::report::validity::per_16bytes::80`, `mbarrier::report::validity::per_16bytes::8000`, `mbarrier::report::validity::per_16bytes::80000000`, `mbarrier::report::validity::per_element::ff`; cta_group: (omitted), `cta_group::1`, `cta_group::2`; cache: (omitted), `L2::cache_hint`; override_address: `override::global_address` | `[dst_mem], [tmap, global_address, {coords...}], [mbar], {im2col_info...}, {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.3 |
| `cp.api.kind.unit.dim.dst.src{.load_mode}.completion{.report}{.cta_group}{.cache}.override_address.override_attribute` | **Decode only:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `1d`; dst: `shared::cta`; src: `global`; load_mode: (omitted), `tile`; completion: `mbarrier::complete_tx::bytes`; report: (omitted), `mbarrier::report::disabled`, `mbarrier::report::validity::per_16bytes::8`, `mbarrier::report::validity::per_16bytes::80`, `mbarrier::report::validity::per_16bytes::8000`, `mbarrier::report::validity::per_16bytes::80000000`, `mbarrier::report::validity::per_element::ff`; cta_group: (omitted), `cta_group::1`, `cta_group::2`; cache: (omitted), `L2::cache_hint`; override_address: `override::global_address`; override_attribute: `override::global_dim` | `[dst_mem], [tmap, global_address, {tensor_size...}, {coords...}], [mbar], {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.3 |
| `cp.api.kind.unit.dim.dst.src{.load_mode}.completion{.report}{.cta_group}{.cache}.override_address.override_attribute` | **Decode only:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `2d`, `3d`, `4d`, `5d`; dst: `shared::cta`; src: `global`; load_mode: (omitted), `tile`; completion: `mbarrier::complete_tx::bytes`; report: (omitted), `mbarrier::report::disabled`, `mbarrier::report::validity::per_16bytes::8`, `mbarrier::report::validity::per_16bytes::80`, `mbarrier::report::validity::per_16bytes::8000`, `mbarrier::report::validity::per_16bytes::80000000`, `mbarrier::report::validity::per_element::ff`; cta_group: (omitted), `cta_group::1`, `cta_group::2`; cache: (omitted), `L2::cache_hint`; override_address: `override::global_address`; override_attribute: `override::global_dim_stride` | `[dst_mem], [tmap, global_address, {tensor_size...}, {lower_stride...}, upper_stride, {coords...}], [mbar], {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.3 |
| `cp.api.kind.unit.dim.dst.src{.load_mode}.completion.report{.cta_group}{.cache}` | **With semantics:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `1d`, `2d`, `3d`, `4d`, `5d`; dst: `shared::cta`; src: `global`; load_mode: (omitted), `tile`, `tile::gather4`; completion: `mbarrier::complete_tx::bytes`; report: `mbarrier::report::disabled`; cta_group: (omitted), `cta_group::1`, `cta_group::2`; cache: (omitted), `L2::cache_hint`<br>**Decode only:** report: `mbarrier::report::validity::per_16bytes::8`, `mbarrier::report::validity::per_16bytes::80`, `mbarrier::report::validity::per_16bytes::8000`, `mbarrier::report::validity::per_16bytes::80000000`, `mbarrier::report::validity::per_element::ff` | `[dst_mem], [tmap, {coords...}], [mbar], {cache_policy}` | event | Core semantics (66 of 396)<br>Decode only (330 of 396): execution is rejected | [THREAD-TENSOR-ISSUE](async.md#thread-tensor-issue) | §9.7.10.28.5.3 |
| `cp.api.kind.action.unit.dim.level.src{.load_mode}{.cache}` | **With semantics:** api: `async`; kind: `bulk`; action: `prefetch`; unit: `tensor`; dim: `1d`, `2d`, `3d`, `4d`, `5d`; level: `L2`; src: `global`; load_mode: (omitted), `tile`, `tile::gather4`; cache: (omitted), `L2::cache_hint` | `[tmap, {coords...}], {cache_policy}` | event | Core semantics | [THREAD-TENSOR-PREFETCH](async.md#thread-tensor-prefetch) | §9.7.10.28.5.5 |
| `cp.api.kind.action.unit.dim.level.src{.load_mode}.priority` | **With semantics:** api: `async`; kind: `bulk`; action: `prefetch`; unit: `tensor`; dim: `1d`, `2d`, `3d`, `4d`, `5d`; level: `L2`; src: `global`; load_mode: (omitted), `tile`, `tile::gather4`; priority: `L2::evict_last` | `[tmap, {coords...}]` | event | Core semantics | [THREAD-TENSOR-PREFETCH](async.md#thread-tensor-prefetch) | §9.7.10.28.5.5 |
| `cp.api.kind.action.unit.dim.level.src.load_mode{.cache}` | **Decode only:** api: `async`; kind: `bulk`; action: `prefetch`; unit: `tensor`; dim: `3d`, `4d`, `5d`; level: `L2`; src: `global`; load_mode: `im2col`, `im2col::w`, `im2col::w::128`; cache: (omitted), `L2::cache_hint` | `[tmap, {coords...}], {im2col_info...}, {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.5 |
| `cp.api.kind.action.unit.dim.level.src.load_mode.priority` | **Decode only:** api: `async`; kind: `bulk`; action: `prefetch`; unit: `tensor`; dim: `3d`, `4d`, `5d`; level: `L2`; src: `global`; load_mode: `im2col`, `im2col::w`, `im2col::w::128`; priority: `L2::evict_last` | `[tmap, {coords...}], {im2col_info...}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.5 |
| `cp.api.kind.action.unit.dim.level.src{.load_mode}{.cache}.override_address` | **Decode only:** api: `async`; kind: `bulk`; action: `prefetch`; unit: `tensor`; dim: `1d`, `2d`, `3d`, `4d`, `5d`; level: `L2`; src: `global`; load_mode: (omitted), `tile`, `tile::gather4`; cache: (omitted), `L2::cache_hint`; override_address: `override::global_address` | `[tmap, global_address, {coords...}], {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.5 |
| `cp.api.kind.action.unit.dim.level.src{.load_mode}.priority.override_address` | **Decode only:** api: `async`; kind: `bulk`; action: `prefetch`; unit: `tensor`; dim: `1d`, `2d`, `3d`, `4d`, `5d`; level: `L2`; src: `global`; load_mode: (omitted), `tile`, `tile::gather4`; priority: `L2::evict_last`; override_address: `override::global_address` | `[tmap, global_address, {coords...}]` | event | Decode only: execution is rejected | none | §9.7.10.28.5.5 |
| `cp.api.kind.action.unit.dim.level.src.load_mode{.cache}.override_address` | **Decode only:** api: `async`; kind: `bulk`; action: `prefetch`; unit: `tensor`; dim: `3d`, `4d`, `5d`; level: `L2`; src: `global`; load_mode: `im2col`, `im2col::w`, `im2col::w::128`; cache: (omitted), `L2::cache_hint`; override_address: `override::global_address` | `[tmap, global_address, {coords...}], {im2col_info...}, {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.5 |
| `cp.api.kind.action.unit.dim.level.src.load_mode.priority.override_address` | **Decode only:** api: `async`; kind: `bulk`; action: `prefetch`; unit: `tensor`; dim: `3d`, `4d`, `5d`; level: `L2`; src: `global`; load_mode: `im2col`, `im2col::w`, `im2col::w::128`; priority: `L2::evict_last`; override_address: `override::global_address` | `[tmap, global_address, {coords...}], {im2col_info...}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.5 |
| `cp.api.kind.action.unit.dim.level.src{.load_mode}{.cache}.override_address.override_attribute` | **Decode only:** api: `async`; kind: `bulk`; action: `prefetch`; unit: `tensor`; dim: `1d`; level: `L2`; src: `global`; load_mode: (omitted), `tile`; cache: (omitted), `L2::cache_hint`; override_address: `override::global_address`; override_attribute: `override::global_dim` | `[tmap, global_address, {tensor_size...}, {coords...}], {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.5 |
| `cp.api.kind.action.unit.dim.level.src{.load_mode}.priority.override_address.override_attribute` | **Decode only:** api: `async`; kind: `bulk`; action: `prefetch`; unit: `tensor`; dim: `1d`; level: `L2`; src: `global`; load_mode: (omitted), `tile`; priority: `L2::evict_last`; override_address: `override::global_address`; override_attribute: `override::global_dim` | `[tmap, global_address, {tensor_size...}, {coords...}]` | event | Decode only: execution is rejected | none | §9.7.10.28.5.5 |
| `cp.api.kind.action.unit.dim.level.src{.load_mode}{.cache}.override_address.override_attribute` | **Decode only:** api: `async`; kind: `bulk`; action: `prefetch`; unit: `tensor`; dim: `2d`, `3d`, `4d`, `5d`; level: `L2`; src: `global`; load_mode: (omitted), `tile`; cache: (omitted), `L2::cache_hint`; override_address: `override::global_address`; override_attribute: `override::global_dim_stride` | `[tmap, global_address, {tensor_size...}, {lower_stride...}, upper_stride, {coords...}], {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.5 |
| `cp.api.kind.action.unit.dim.level.src{.load_mode}.priority.override_address.override_attribute` | **Decode only:** api: `async`; kind: `bulk`; action: `prefetch`; unit: `tensor`; dim: `2d`, `3d`, `4d`, `5d`; level: `L2`; src: `global`; load_mode: (omitted), `tile`; priority: `L2::evict_last`; override_address: `override::global_address`; override_attribute: `override::global_dim_stride` | `[tmap, global_address, {tensor_size...}, {lower_stride...}, upper_stride, {coords...}]` | event | Decode only: execution is rejected | none | §9.7.10.28.5.5 |
| `cp.api.kind.unit.dim.dst.src{.load_mode}.completion{.cache}` | **With semantics:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `1d`, `2d`, `3d`, `4d`, `5d`; dst: `global`; src: `shared::cta`; load_mode: (omitted), `tile`, `tile::scatter4`; completion: `bulk_group`; cache: (omitted), `L2::cache_hint` | `[tmap, {coords...}], [src_mem], {cache_policy}` | event | Core semantics | [THREAD-TENSOR-STORE](async.md#thread-tensor-store) | §9.7.10.28.5.3 |
| `cp.api.kind.unit.dim.dst.src.load_mode.completion{.cache}` | **Decode only:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `3d`, `4d`, `5d`; dst: `global`; src: `shared::cta`; load_mode: `im2col_no_offs`, `im2col_no_offs::w`; completion: `bulk_group`; cache: (omitted), `L2::cache_hint` | `[tmap, {coords...}], [src_mem], {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.3 |
| `cp.api.kind.unit.dim.dst.src{.load_mode}.completion{.cache}.override_address` | **Decode only:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `1d`, `2d`, `3d`, `4d`, `5d`; dst: `global`; src: `shared::cta`; load_mode: (omitted), `tile`, `tile::scatter4`; completion: `bulk_group`; cache: (omitted), `L2::cache_hint`; override_address: `override::global_address` | `[tmap, global_address, {coords...}], [src_mem], {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.3 |
| `cp.api.kind.unit.dim.dst.src.load_mode.completion{.cache}.override_address` | **Decode only:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `3d`, `4d`, `5d`; dst: `global`; src: `shared::cta`; load_mode: `im2col_no_offs`, `im2col_no_offs::w`; completion: `bulk_group`; cache: (omitted), `L2::cache_hint`; override_address: `override::global_address` | `[tmap, global_address, {coords...}], [src_mem], {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.3 |
| `cp.api.kind.unit.dim.dst.src{.load_mode}.completion{.cache}.override_address.override_attribute` | **Decode only:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `1d`; dst: `global`; src: `shared::cta`; load_mode: (omitted), `tile`; completion: `bulk_group`; cache: (omitted), `L2::cache_hint`; override_address: `override::global_address`; override_attribute: `override::global_dim` | `[tmap, global_address, {tensor_size...}, {coords...}], [src_mem], {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.3 |
| `cp.api.kind.unit.dim.dst.src{.load_mode}.completion{.cache}.override_address.override_attribute` | **Decode only:** api: `async`; kind: `bulk`; unit: `tensor`; dim: `2d`, `3d`, `4d`, `5d`; dst: `global`; src: `shared::cta`; load_mode: (omitted), `tile`; completion: `bulk_group`; cache: (omitted), `L2::cache_hint`; override_address: `override::global_address`; override_attribute: `override::global_dim_stride` | `[tmap, global_address, {tensor_size...}, {lower_stride...}, upper_stride, {coords...}], [src_mem], {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.3 |
| `cp.api.kind.action{.read}` | **With semantics:** api: `async`; kind: `bulk`; action: `wait_group`; read: (omitted), `read`, `sync_restrict::proxy::async` | `group` | event | Core semantics | [THREAD-TENSOR-STORE](async.md#thread-tensor-store) | §9.7.10.28.6.2 |
| `cp.api.cop.dst.src{.cache}{.prefetch}` | **With semantics:** api: `async`; cop: `ca`; dst: `shared`, `shared::cta`; src: `global`; cache: (omitted), `L2::cache_hint`; prefetch: (omitted), `L2::128B`, `L2::256B`, `L2::64B` | `[dst_mem], [src_mem], cp_size, {cache_policy}` | event | Core semantics | [THREAD-CP-ASYNC](async.md#thread-cp-async) | §9.7.10.28.3.1 |
| `cp.api.cop.dst.src{.cache}{.prefetch}` | **With semantics:** api: `async`; cop: `ca`; dst: `shared`, `shared::cta`; src: `global`; cache: (omitted), `L2::cache_hint`; prefetch: (omitted), `L2::128B`, `L2::256B`, `L2::64B` | `[dst_mem], [src_mem], cp_size, ignore_src, {cache_policy}` | event | Core semantics | [THREAD-CP-ASYNC](async.md#thread-cp-async) | §9.7.10.28.3.1 |
| `cp.api.cop.dst.src{.cache}{.prefetch}` | **With semantics:** api: `async`; cop: `ca`; dst: `shared`, `shared::cta`; src: `global`; cache: (omitted), `L2::cache_hint`; prefetch: (omitted), `L2::128B`, `L2::256B`, `L2::64B` | `[dst_mem], [src_mem], cp_size, src_size, {cache_policy}` | event | Core semantics | [THREAD-CP-ASYNC](async.md#thread-cp-async) | §9.7.10.28.3.1 |
| `cp.api.cop.dst.src{.cache}{.prefetch}` | **With semantics:** api: `async`; cop: `cg`; dst: `shared`, `shared::cta`; src: `global`; cache: (omitted), `L2::cache_hint`; prefetch: (omitted), `L2::128B`, `L2::256B`, `L2::64B` | `[dst_mem], [src_mem], cp_size, {cache_policy}` | event | Core semantics | [THREAD-CP-ASYNC](async.md#thread-cp-async) | §9.7.10.28.3.1 |
| `cp.api.cop.dst.src{.cache}{.prefetch}` | **With semantics:** api: `async`; cop: `cg`; dst: `shared`, `shared::cta`; src: `global`; cache: (omitted), `L2::cache_hint`; prefetch: (omitted), `L2::128B`, `L2::256B`, `L2::64B` | `[dst_mem], [src_mem], cp_size, ignore_src, {cache_policy}` | event | Core semantics | [THREAD-CP-ASYNC](async.md#thread-cp-async) | §9.7.10.28.3.1 |
| `cp.api.cop.dst.src{.cache}{.prefetch}` | **With semantics:** api: `async`; cop: `cg`; dst: `shared`, `shared::cta`; src: `global`; cache: (omitted), `L2::cache_hint`; prefetch: (omitted), `L2::128B`, `L2::256B`, `L2::64B` | `[dst_mem], [src_mem], cp_size, src_size, {cache_policy}` | event | Core semantics | [THREAD-CP-ASYNC](async.md#thread-cp-async) | §9.7.10.28.3.1 |
| `cp.api.action` | **With semantics:** api: `async`; action: `commit_group` | none | local | Core semantics | [THREAD-CP-ASYNC](async.md#thread-cp-async) | §9.7.10.28.3.2 |
| `cp.api.target.action{.noinc}{.space}.type` | **With semantics:** api: `async`; target: `mbarrier`; action: `arrive`; noinc: (omitted), `noinc`; space: (omitted), `shared`, `shared::cta`; type: `b64` | `[addr]` | event | Core semantics | [THREAD-CP-ASYNC](async.md#thread-cp-async) | §9.7.15.16.18 |
| `cp.api.action` | **With semantics:** api: `async`; action: `wait_all` | none | event | Core semantics | [THREAD-CP-ASYNC](async.md#thread-cp-async) | §9.7.10.28.3.3 |
| `cp.api.action` | **With semantics:** api: `async`; action: `wait_group` | `group` | event | Core semantics | [THREAD-CP-ASYNC](async.md#thread-cp-async) | §9.7.10.28.3.3 |
| `cp.op.api.kind{.sem}{.scope}.dst.src.completion.redop.type` | **With semantics:** op: `reduce`; api: `async`; kind: `bulk`; sem: (omitted), `relaxed`; scope: (omitted), `cluster`, `cta`; dst: `shared::cluster`; src: `shared::cta`; completion: `mbarrier::complete_tx::bytes`; redop: `add`, `and`, `dec`, `inc`, `max`, `min`, `or`, `xor`; type: `b32`, `s32`, `u32`, `u64` | `[dst_mem], [src_mem], size, [mbar]` | event | Core semantics | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.10.28.4.2 |
| `cp.op.api.kind{.sem}{.scope}.dst.src.completion{.cache}.redop{.noftz}.type` | **With semantics:** op: `reduce`; api: `async`; kind: `bulk`; sem: (omitted), `relaxed`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; dst: `global`; src: `shared::cta`; completion: `bulk_group`; cache: (omitted), `L2::cache_hint`; redop: `add`, `and`, `dec`, `inc`, `max`, `min`, `or`, `xor`; noftz: (omitted), `noftz`; type: `b32`, `b64`, `bf16`, `f16`, `f32`, `f64`, `s32`, `s64`, `u32`, `u64` | `[dst_mem], [src_mem], size, {cache_policy}` | event | Core semantics | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.10.28.4.2 |
| `cp.op.api.kind{.sem}{.scope}.dst.src.completion{.cache}.redop.noftz.type` | **With semantics:** op: `reduce`; api: `async`; kind: `bulk`; sem: (omitted), `relaxed`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; dst: `global`; src: `shared::cta`; completion: `bulk_group`; cache: (omitted), `L2::cache_hint`; redop: `add`; noftz: `noftz`; type: `f32` | `[dst_mem], [src_mem], size, {cache_policy}` | event | Core semantics | [THREAD-TMA](mbarrier.md#thread-tma) | §9.7.10.28.4.2 |
| `cp.op.api.kind.unit.dim.dst.src.redop{.load_mode}.completion{.cache}` | **With semantics:** op: `reduce`; api: `async`; kind: `bulk`; unit: `tensor`; dim: `1d`, `2d`, `3d`, `4d`, `5d`; dst: `global`; src: `shared::cta`; redop: `add`, `and`, `dec`, `inc`, `max`, `min`, `or`, `xor`; load_mode: (omitted), `tile`; completion: `bulk_group`; cache: (omitted), `L2::cache_hint` | `[tmap, {coords...}], [src_mem], {cache_policy}` | event | Core semantics | [THREAD-TENSOR-STORE](async.md#thread-tensor-store) | §9.7.10.28.5.4 |
| `cp.op.api.kind.unit.dim.dst.src.redop.load_mode.completion{.cache}` | **Decode only:** op: `reduce`; api: `async`; kind: `bulk`; unit: `tensor`; dim: `3d`, `4d`, `5d`; dst: `global`; src: `shared::cta`; redop: `add`, `and`, `dec`, `inc`, `max`, `min`, `or`, `xor`; load_mode: `im2col_no_offs`, `im2col_no_offs::w`; completion: `bulk_group`; cache: (omitted), `L2::cache_hint` | `[tmap, {coords...}], [src_mem], {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.4 |
| `cp.op.api.kind.unit.dim.dst.src.redop{.load_mode}.completion{.cache}.override_address` | **Decode only:** op: `reduce`; api: `async`; kind: `bulk`; unit: `tensor`; dim: `1d`, `2d`, `3d`, `4d`, `5d`; dst: `global`; src: `shared::cta`; redop: `add`, `and`, `dec`, `inc`, `max`, `min`, `or`, `xor`; load_mode: (omitted), `tile`; completion: `bulk_group`; cache: (omitted), `L2::cache_hint`; override_address: `override::global_address` | `[tmap, global_address, {coords...}], [src_mem], {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.4 |
| `cp.op.api.kind.unit.dim.dst.src.redop.load_mode.completion{.cache}.override_address` | **Decode only:** op: `reduce`; api: `async`; kind: `bulk`; unit: `tensor`; dim: `3d`, `4d`, `5d`; dst: `global`; src: `shared::cta`; redop: `add`, `and`, `dec`, `inc`, `max`, `min`, `or`, `xor`; load_mode: `im2col_no_offs`, `im2col_no_offs::w`; completion: `bulk_group`; cache: (omitted), `L2::cache_hint`; override_address: `override::global_address` | `[tmap, global_address, {coords...}], [src_mem], {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.4 |
| `cp.op.api.kind.unit.dim.dst.src.redop{.load_mode}.completion{.cache}.override_address.override_attribute` | **Decode only:** op: `reduce`; api: `async`; kind: `bulk`; unit: `tensor`; dim: `1d`; dst: `global`; src: `shared::cta`; redop: `add`, `and`, `dec`, `inc`, `max`, `min`, `or`, `xor`; load_mode: (omitted), `tile`; completion: `bulk_group`; cache: (omitted), `L2::cache_hint`; override_address: `override::global_address`; override_attribute: `override::global_dim` | `[tmap, global_address, {tensor_size...}, {coords...}], [src_mem], {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.4 |
| `cp.op.api.kind.unit.dim.dst.src.redop{.load_mode}.completion{.cache}.override_address.override_attribute` | **Decode only:** op: `reduce`; api: `async`; kind: `bulk`; unit: `tensor`; dim: `2d`, `3d`, `4d`, `5d`; dst: `global`; src: `shared::cta`; redop: `add`, `and`, `dec`, `inc`, `max`, `min`, `or`, `xor`; load_mode: (omitted), `tile`; completion: `bulk_group`; cache: (omitted), `L2::cache_hint`; override_address: `override::global_address`; override_attribute: `override::global_dim_stride` | `[tmap, global_address, {tensor_size...}, {lower_stride...}, upper_stride, {coords...}], [src_mem], {cache_policy}` | event | Decode only: execution is rejected | none | §9.7.10.28.5.4 |
| `prefetch{.space}{.level}{.evict}.tensormap` | **With semantics:** space: (omitted), `param`; level: (omitted); evict: (omitted); tensormap: `tensormap`<br>**Decode only:** space: `const` | `[addr]` | event | Core semantics (2 of 3)<br>Decode only (1 of 3): execution is rejected | [THREAD-TENSORMAP-PREFETCH](threads.md#thread-tensormap-prefetch) | §9.7.10.16 |
| `red.async.sem.scope{.space}.completion.op.type` | **With semantics:** sem: `relaxed`; scope: `cluster`; space: (omitted), `shared::cluster`; completion: `mbarrier::complete_tx::bytes`; op: `add`, `and`, `dec`, `inc`, `max`, `min`, `or`, `xor`; type: `b32`, `s32`, `u32`, `u64` | `[addr], value, [mbar]` | event | Core semantics | [THREAD-ASYNC-STORE](async.md#thread-async-store) | §9.7.15.7 |
| `red.async{.mmio}.sem.scope{.space}.op.type` | **With semantics:** mmio: (omitted); sem: `release`; scope: `gpu`, `sys`; space: (omitted), `global`; op: `add`; type: `s32`, `s64`, `u32`, `u64`<br>**Decode only:** mmio: `mmio` | `[addr], value` | event | Core semantics (16 of 24)<br>Decode only (8 of 24): execution is rejected | [THREAD-ASYNC-STORE](async.md#thread-async-store) | §9.7.15.7 |
| `st.async{.weak}{.space}.completion.type` | **With semantics:** weak: (omitted), `weak`; space: (omitted), `shared::cluster`; completion: `mbarrier::complete_tx::bytes`; type: `b128`, `b32`, `b64`, `f32`, `f64`, `s32`, `s64`, `u32`, `u64` | `[addr], b, [mbar]` | event | Core semantics | [THREAD-ASYNC-STORE](async.md#thread-async-store) | §9.7.10.12 |
| `st.async{.mmio}.sem.scope{.space}.type` | **With semantics:** mmio: (omitted); sem: `release`; scope: `gpu`, `sys`; space: (omitted), `global`; type: `b16`, `b32`, `b64`, `b8`, `f32`, `f64`, `s16`, `s32`, `s64`, `s8`, `u16`, `u32`, `u64`, `u8`<br>**Decode only:** mmio: `mmio` | `[addr], b` | event | Core semantics (56 of 84)<br>Decode only (28 of 84): execution is rejected | [THREAD-ASYNC-STORE](async.md#thread-async-store) | §9.7.10.12 |
| `st.async{.weak}{.space}.completion.vec.type` | **With semantics:** weak: (omitted), `weak`; space: (omitted), `shared::cluster`; completion: `mbarrier::complete_tx::bytes`; vec: `v2`, `v4`; type: `b32`, `b64`, `f32`, `f64`, `s32`, `s64`, `u32`, `u64` | `[addr], {b...}, [mbar]` | event | Core semantics | [THREAD-ASYNC-STORE](async.md#thread-async-store) | §9.7.10.12 |
| `tensormap.cp_fenceproxy.dst.src.proxy.sem.scope.sync.aligned` | **Decode only:** dst: `global`; src: `shared::cta`; proxy: `tensormap::generic`; sem: `release`; scope: `cluster`, `cta`, `gpu`, `sys`; sync: `sync`; aligned: `aligned` | `[dst_mem], [src_mem], 128` | event | Decode only: execution is rejected | none | §9.7.15.17 |
| `tensormap.replace.mode.field{.space}.width.type` | **Decode only:** mode: `tile`; field: `global_address`; space: (omitted), `global`, `shared::cta`; width: `b1024`; type: `b64` | `[addr], new_val` | event | Decode only: execution is rejected | none | §9.7.10.29 |
| `tensormap.replace.mode.field{.space}.width.type` | **Decode only:** mode: `tile`; field: `box_dim`, `element_stride`, `global_dim`; space: (omitted), `global`, `shared::cta`; width: `b1024`; type: `b32` | `[addr], ord, new_val` | event | Decode only: execution is rejected | none | §9.7.10.29 |
| `tensormap.replace.mode.field{.space}.width.type` | **Decode only:** mode: `tile`; field: `elemtype`; space: (omitted), `global`, `shared::cta`; width: `b1024`; type: `b32` | `[addr], new_val` | event | Decode only: execution is rejected | none | §9.7.10.29 |
| `tensormap.replace.mode.field{.space}.width.type` | **Decode only:** mode: `tile`; field: `fill_mode`; space: (omitted), `global`, `shared::cta`; width: `b1024`; type: `b32` | `[addr], new_val` | event | Decode only: execution is rejected | none | §9.7.10.29 |
| `tensormap.replace.mode.field{.space}.width.type` | **Decode only:** mode: `tile`; field: `interleave_layout`; space: (omitted), `global`, `shared::cta`; width: `b1024`; type: `b32` | `[addr], new_val` | event | Decode only: execution is rejected | none | §9.7.10.29 |
| `tensormap.replace.mode.field{.space}.width.type` | **Decode only:** mode: `tile`; field: `rank`; space: (omitted), `global`, `shared::cta`; width: `b1024`; type: `b32` | `[addr], new_val` | event | Decode only: execution is rejected | none | §9.7.10.29 |
| `tensormap.replace.mode.field{.space}.width.type` | **Decode only:** mode: `tile`; field: `global_stride`; space: (omitted), `global`, `shared::cta`; width: `b1024`; type: `b64` | `[addr], ord, new_val` | event | Decode only: execution is rejected | none | §9.7.10.29 |
| `tensormap.replace.mode.field{.space}.width.type` | **Decode only:** mode: `tile`; field: `swizzle_mode`; space: (omitted), `global`, `shared::cta`; width: `b1024`; type: `b32` | `[addr], new_val` | event | Decode only: execution is rejected | none | §9.7.10.29 |
| `tensormap.replace.mode.field{.space}.width.type` | **Decode only:** mode: `tile`; field: `swizzle_mode`; space: (omitted), `global`, `shared::cta`; width: `b1024`; type: `b32` | `[addr], new_val` | event | Decode only: execution is rejected | none | §9.7.10.29 |

### Tcgen05

The forms listed in PROG-ISA-SYNC-FORMS decode to their own constructors of `Op`; `Op.rule` (PROG-INSTR-RULE) names the rule of each.

Entries: 28 with Core semantics, 52 decode only, 0 rejected.

| Instruction | Modifiers | Operands | Kind | Status | Rule | Manual |
|---|---|---|---|---|---|---|
| `tcgen05.action.cta_group.sync.aligned{.space}.type` | **With semantics:** action: `alloc`; cta_group: `cta_group::1`, `cta_group::2`; sync: `sync`; aligned: `aligned`; space: `shared::cta`; type: `b32`<br>**Decode only:** space: (omitted) | `[dst], ncols` | event | Core semantics (2 of 4)<br>Decode only (2 of 4): execution is rejected | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.7.1 |
| `tcgen05.action.exclusive.cta_group.sync.aligned{.space}.type` | **Decode only:** action: `alloc`; exclusive: `exclusive`; cta_group: `cta_group::1`, `cta_group::2`; sync: `sync`; aligned: `aligned`; space: (omitted), `shared::cta`; type: `b32` | `[dst], ncols` | event | Decode only: execution is rejected | none | §9.7.18.7.1 |
| `tcgen05.action.cta_group.completion{.space}.type` | **With semantics:** action: `commit`; cta_group: `cta_group::1`, `cta_group::2`; completion: `mbarrier::arrive::one`; space: `shared::cluster`; type: `b64`<br>**Decode only:** space: (omitted) | `[mbar]` | event | Core semantics (2 of 4)<br>Decode only (2 of 4): execution is rejected | [THREAD-TC-COMMIT](tcgen05.md#thread-tc-commit) | §9.7.18.12.1 |
| `tcgen05.action.cta_group.completion{.space}.multicast.type` | **With semantics:** action: `commit`; cta_group: `cta_group::1`, `cta_group::2`; completion: `mbarrier::arrive::one`; space: `shared::cluster`; multicast: `multicast::cluster`; type: `b64`<br>**Decode only:** space: (omitted) | `[mbar], mask` | event | Core semantics (2 of 4)<br>Decode only (2 of 4): execution is rejected | [THREAD-TC-COMMIT](tcgen05.md#thread-tc-commit) | §9.7.18.12.1 |
| `tcgen05.action.cta_group.completion{.space}.multicast.type` | **With semantics:** action: `commit`; cta_group: `cta_group::1`, `cta_group::2`; completion: `mbarrier::arrive::one`; space: `shared::cluster`; multicast: `multicast::cluster::16b`; type: `b64`<br>**Decode only:** space: (omitted); multicast: `multicast::cluster::32b` | `[mbar], cta_mask` | event | Core semantics (2 of 8)<br>Decode only (6 of 8): execution is rejected | [THREAD-TC-COMMIT](tcgen05.md#thread-tc-commit) | §9.7.18.12.1 |
| `tcgen05.action.cta_group.completion.sync_restrict{.space}.type` | **Decode only:** action: `commit`; cta_group: `cta_group::1`, `cta_group::2`; completion: `mbarrier::arrive::one`; sync_restrict: `sync_restrict::shared::read::mma::a`; space: (omitted), `shared::cluster`; type: `b64` | `[mbar]` | event | Decode only: execution is rejected | none | §9.7.18.12.1 |
| `tcgen05.action.cta_group.completion.sync_restrict{.space}.multicast.type` | **Decode only:** action: `commit`; cta_group: `cta_group::1`, `cta_group::2`; completion: `mbarrier::arrive::one`; sync_restrict: `sync_restrict::shared::read::mma::a`; space: (omitted), `shared::cluster`; multicast: `multicast::cluster`, `multicast::cluster::16b`, `multicast::cluster::32b`; type: `b64` | `[mbar], cta_mask` | event | Decode only: execution is rejected | none | §9.7.18.12.1 |
| `tcgen05.action.cta_group.shape{.multicast}{.dst_fmt}{.src_fmt}` | **With semantics:** action: `cp`; cta_group: `cta_group::1`, `cta_group::2`; shape: `128x128b`, `128x256b`, `32x128b`, `4x256b`, `64x128b`; multicast: (omitted), `warpx2::01_23`, `warpx2::02_13`, `warpx4`; dst_fmt: (omitted), `b8x16`; src_fmt: (omitted), `b4x16_p64`, `b6x16_p32` | `[taddr], s_desc` | event | Core semantics | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.9.2 |
| `tcgen05.action.cta_group.sync.aligned.type` | **With semantics:** action: `dealloc`; cta_group: `cta_group::1`, `cta_group::2`; sync: `sync`; aligned: `aligned`; type: `b32` | `taddr, ncols` | event | Core semantics | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.7.1 |
| `tcgen05.action.exclusive.cta_group.sync.aligned.type` | **Decode only:** action: `dealloc`; exclusive: `exclusive`; cta_group: `cta_group::1`, `cta_group::2`; sync: `sync`; aligned: `aligned`; type: `b32` | `taddr, ncols` | event | Decode only: execution is rejected | none | §9.7.18.7.1 |
| `tcgen05.action` | **With semantics:** action: `fence::after_thread_sync`, `fence::before_thread_sync` | none | event | Core semantics | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.11.1 |
| `tcgen05.action.sync.aligned.shape.num{.pack}.type` | **With semantics:** action: `ld`; sync: `sync`; aligned: `aligned`; shape: `16x128b`, `16x256b`, `16x64b`, `32x32b`; num: `x1`, `x128`, `x16`, `x2`, `x32`, `x4`, `x64`, `x8`; pack: (omitted), `pack::16b`; type: `b32` | `{r...}, [taddr]` | event | Core semantics | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.8.3 |
| `tcgen05.action.red.sync.aligned.shape.num.redop{.abs}{.nan}.type` | **With semantics:** action: `ld`; red: `red`; sync: `sync`; aligned: `aligned`; shape: `32x32b`; num: `x128`, `x16`, `x2`, `x32`, `x4`, `x64`, `x8`; redop: `max`, `min`; abs: (omitted), `abs`; nan: (omitted), `NaN`; type: `f32`, `s32`, `u32` | `{r...}, redval, [taddr]` | event | Core semantics | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.8.3 |
| `tcgen05.action.red.spcompress.sync.aligned.shape.num.rowop.spfactor{.abs}{.nan}.type.idxsize` | **Decode only:** action: `ld`; red: `red`; spcompress: `spcompress`; sync: `sync`; aligned: `aligned`; shape: `32x32b`; num: `x128`, `x16`, `x32`, `x4`, `x64`, `x8`; rowop: `max`, `min`; spfactor: `sp::2:4`; abs: (omitted), `abs`; nan: (omitted), `NaN`; type: `f32`; idxsize: `b2` | `{mdata...}, {cdata...}, redval, [taddr]` | event | Decode only: execution is rejected | none | §9.7.18.8.3 |
| `tcgen05.action.red.sync.aligned.shape.num.redop{.abs}{.nan}.type` | **With semantics:** action: `ld`; red: `red`; sync: `sync`; aligned: `aligned`; shape: `16x32bx2`; num: `x128`, `x16`, `x2`, `x32`, `x4`, `x64`, `x8`; redop: `max`, `min`; abs: (omitted), `abs`; nan: (omitted), `NaN`; type: `f32`, `s32`, `u32` | `{r...}, redval, [taddr], imm_half_splitoff` | event | Core semantics | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.8.3 |
| `tcgen05.action.spcompress.sync.aligned.shape.num.rowop.spfactor{.abs}.type.idxsize` | **Decode only:** action: `ld`; spcompress: `spcompress`; sync: `sync`; aligned: `aligned`; shape: `32x32b`; num: `x128`, `x16`, `x32`, `x4`, `x64`, `x8`; rowop: `max`, `min`; spfactor: `sp::2:4`; abs: (omitted), `abs`; type: `f32`; idxsize: `b2` | `{mdata...}, {cdata...}, [taddr]` | event | Decode only: execution is rejected | none | §9.7.18.8.3 |
| `tcgen05.action.sync.aligned.shape.num{.pack}.type` | **With semantics:** action: `ld`; sync: `sync`; aligned: `aligned`; shape: `16x32bx2`; num: `x1`, `x128`, `x16`, `x2`, `x32`, `x4`, `x64`, `x8`; pack: (omitted); type: `b32`<br>**Decode only:** pack: `pack::16b` | `{r...}, [taddr], imm_half_splitoff` | event | Core semantics (8 of 16)<br>Decode only (8 of 16): execution is rejected | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.8.3 |
| `tcgen05.action.cta_group.kind.ashift.collector_b` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::f16`, `kind::f8f6f4`, `kind::tf32`, `kind::ti16`; ashift: `ashift`; collector_b: `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], [a_tmem], b_desc, idesc, {disable_output_lane...}, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind.ashift.collector_b` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::f16`, `kind::f8f6f4`, `kind::tf32`, `kind::ti16`; ashift: `ashift`; collector_b: `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], [a_tmem], b_desc, idesc, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind.block_scale.block_size{.collector_a}{.collector_b}` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::mxf4`, `kind::mxf4nvf4`, `kind::mxf8f6f4`; block_scale: `block_scale`; block_size: `block16`, `block32`; collector_a: (omitted), `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use`; collector_b: (omitted), `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], a_desc, b_desc, idesc, [sfa_tmem], [sfb_tmem], enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind.block_scale.block_size{.collector_a}{.collector_b}` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::mxf4`, `kind::mxf4nvf4`, `kind::mxf8f6f4`; block_scale: `block_scale`; block_size: `block16`, `block32`; collector_a: (omitted), `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use`; collector_b: (omitted), `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], [a_tmem], b_desc, idesc, [sfa_tmem], [sfb_tmem], enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind.block_scale.collector_a{.collector_b}` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::mxf4`, `kind::mxf8f6f4`; block_scale: `block_scale`; collector_a: `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use`; collector_b: (omitted), `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], a_desc, b_desc, idesc, [sfa_tmem], [sfb_tmem], enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind.block_scale.collector_a{.collector_b}` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::mxf4`, `kind::mxf8f6f4`; block_scale: `block_scale`; collector_a: `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use`; collector_b: (omitted), `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], [a_tmem], b_desc, idesc, [sfa_tmem], [sfb_tmem], enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind.block_scale.decompress{.block_size}{.collector_a}{.collector_b}` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::mxf8f6f4`; block_scale: `block_scale`; decompress: `decompress::lut::b`; block_size: (omitted), `block32`; collector_a: (omitted), `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use`; collector_b: (omitted), `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], a_desc, b_compressed_desc, [b_decompress_metadata], idesc, [sfa_tmem], [sfb_tmem], enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind.block_scale.decompress{.block_size}{.collector_a}{.collector_b}` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::mxf8f6f4`; block_scale: `block_scale`; decompress: `decompress::lut::b`; block_size: (omitted), `block32`; collector_a: (omitted), `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use`; collector_b: (omitted), `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], [a_tmem], b_compressed_desc, [b_decompress_metadata], idesc, [sfa_tmem], [sfb_tmem], enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind.block_scale.scale_vec` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::mxf4`, `kind::mxf4nvf4`, `kind::mxf8f6f4`; block_scale: `block_scale`; scale_vec: `scale_vec::1X`, `scale_vec::2X`, `scale_vec::4X` | `[d_tmem], a_desc, b_desc, idesc, [sfa_tmem], [sfb_tmem], enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind.block_scale.scale_vec` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::mxf4`, `kind::mxf4nvf4`, `kind::mxf8f6f4`; block_scale: `block_scale`; scale_vec: `scale_vec::1X`, `scale_vec::2X`, `scale_vec::4X` | `[d_tmem], [a_tmem], b_desc, idesc, [sfa_tmem], [sfb_tmem], enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind.collector_a.collector_b` | **With semantics:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::f16`, `kind::f8f6f4`, `kind::tf32`; collector_a: `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use`; collector_b: `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use`<br>**Decode only:** kind: `kind::ti16` | `[d_tmem], a_desc, b_desc, idesc, {disable_output_lane...}, enable_input_d` | event | Core semantics (96 of 128)<br>Decode only (32 of 128): execution is rejected | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind.collector_a.collector_b` | **With semantics:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::f16`, `kind::f8f6f4`, `kind::tf32`; collector_a: `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use`; collector_b: `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use`<br>**Decode only:** kind: `kind::ti16` | `[d_tmem], a_desc, b_desc, idesc, enable_input_d` | event | Core semantics (96 of 128)<br>Decode only (32 of 128): execution is rejected | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind{.ashift}.collector_a.collector_b` | **With semantics:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::f16`, `kind::f8f6f4`, `kind::tf32`; ashift: (omitted); collector_a: `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use`; collector_b: `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use`<br>**Decode only:** kind: `kind::ti16`; ashift: `ashift` | `[d_tmem], [a_tmem], b_desc, idesc, {disable_output_lane...}, enable_input_d` | event | Core semantics (96 of 192)<br>Decode only (96 of 192): execution is rejected | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind{.ashift}.collector_a.collector_b` | **With semantics:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::f16`, `kind::f8f6f4`, `kind::tf32`; ashift: (omitted); collector_a: `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use`; collector_b: `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use`<br>**Decode only:** kind: `kind::ti16`; ashift: `ashift` | `[d_tmem], [a_tmem], b_desc, idesc, enable_input_d` | event | Core semantics (96 of 192)<br>Decode only (96 of 192): execution is rejected | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind.decompress{.collector_a}{.collector_b}` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::f8f6f4`; decompress: `decompress::lut::b`; collector_a: (omitted), `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use`; collector_b: (omitted), `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], a_desc, b_compressed_desc, [b_decompress_metadata], idesc, {disable_output_lane...}, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind.decompress{.collector_a}{.collector_b}` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::f8f6f4`; decompress: `decompress::lut::b`; collector_a: (omitted), `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use`; collector_b: (omitted), `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], a_desc, b_compressed_desc, [b_decompress_metadata], idesc, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind.decompress{.collector_a}{.collector_b}` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::f8f6f4`; decompress: `decompress::lut::b`; collector_a: (omitted), `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use`; collector_b: (omitted), `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], [a_tmem], b_compressed_desc, [b_decompress_metadata], idesc, {disable_output_lane...}, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind.decompress{.collector_a}{.collector_b}` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::f8f6f4`; decompress: `decompress::lut::b`; collector_a: (omitted), `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use`; collector_b: (omitted), `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], [a_tmem], b_compressed_desc, [b_decompress_metadata], idesc, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.sp.cta_group.kind.ashift.collector_b` | **Decode only:** action: `mma`; sp: `sp`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::f16`, `kind::f8f6f4`, `kind::tf32`, `kind::ti16`; ashift: `ashift`; collector_b: `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], [a_tmem], b_desc, [sp_meta_tmem], idesc, {disable_output_lane...}, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.2 |
| `tcgen05.action.sp.cta_group.kind.ashift.collector_b` | **Decode only:** action: `mma`; sp: `sp`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::f16`, `kind::f8f6f4`, `kind::tf32`, `kind::ti16`; ashift: `ashift`; collector_b: `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], [a_tmem], b_desc, [sp_meta_tmem], idesc, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.2 |
| `tcgen05.action.sp.cta_group.kind.block_scale.collector_a{.collector_b}` | **Decode only:** action: `mma`; sp: `sp`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::mxf8f6f4`; block_scale: `block_scale`; collector_a: `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use`; collector_b: (omitted), `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], a_desc, b_desc, [sp_meta_tmem], idesc, [sfa_tmem], [sfb_tmem], enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.2 |
| `tcgen05.action.sp.cta_group.kind.block_scale.collector_a{.collector_b}` | **Decode only:** action: `mma`; sp: `sp`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::mxf8f6f4`; block_scale: `block_scale`; collector_a: `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use`; collector_b: (omitted), `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], [a_tmem], b_desc, [sp_meta_tmem], idesc, [sfa_tmem], [sfb_tmem], enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.2 |
| `tcgen05.action.sp.cta_group.kind.collector_a.collector_b` | **Decode only:** action: `mma`; sp: `sp`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::f16`, `kind::f8f6f4`, `kind::tf32`, `kind::ti16`; collector_a: `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use`; collector_b: `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], a_desc, b_desc, [sp_meta_tmem], idesc, {disable_output_lane...}, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.2 |
| `tcgen05.action.sp.cta_group.kind.collector_a.collector_b` | **Decode only:** action: `mma`; sp: `sp`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::f16`, `kind::f8f6f4`, `kind::tf32`, `kind::ti16`; collector_a: `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use`; collector_b: `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], a_desc, b_desc, [sp_meta_tmem], idesc, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.2 |
| `tcgen05.action.sp.cta_group.kind{.ashift}.collector_a.collector_b` | **Decode only:** action: `mma`; sp: `sp`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::f16`, `kind::f8f6f4`, `kind::tf32`, `kind::ti16`; ashift: (omitted), `ashift`; collector_a: `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use`; collector_b: `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], [a_tmem], b_desc, [sp_meta_tmem], idesc, {disable_output_lane...}, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.2 |
| `tcgen05.action.sp.cta_group.kind{.ashift}.collector_a.collector_b` | **Decode only:** action: `mma`; sp: `sp`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::f16`, `kind::f8f6f4`, `kind::tf32`, `kind::ti16`; ashift: (omitted), `ashift`; collector_a: `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use`; collector_b: `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], [a_tmem], b_desc, [sp_meta_tmem], idesc, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.2 |
| `tcgen05.action.sp.cta_group.kind` | **Decode only:** action: `mma`; sp: `sp`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::ti16` | `[d_tmem], a_desc, b_desc, [sp_meta_tmem], idesc, {disable_output_lane...}, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.2 |
| `tcgen05.action.sp.cta_group.kind.collector_b` | **Decode only:** action: `mma`; sp: `sp`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::ti16`; collector_b: `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], a_desc, b_desc, [sp_meta_tmem], idesc, {disable_output_lane...}, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.2 |
| `tcgen05.action.sp.cta_group.kind.collector_b` | **Decode only:** action: `mma`; sp: `sp`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::ti16`; collector_b: `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], a_desc, b_desc, [sp_meta_tmem], idesc, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.2 |
| `tcgen05.action.sp.cta_group.kind` | **Decode only:** action: `mma`; sp: `sp`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::ti16` | `[d_tmem], a_desc, b_desc, [sp_meta_tmem], idesc, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.2 |
| `tcgen05.action.sp.cta_group.kind` | **Decode only:** action: `mma`; sp: `sp`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::ti16` | `[d_tmem], [a_tmem], b_desc, [sp_meta_tmem], idesc, {disable_output_lane...}, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.2 |
| `tcgen05.action.sp.cta_group.kind.collector_b` | **Decode only:** action: `mma`; sp: `sp`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::ti16`; collector_b: `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], [a_tmem], b_desc, [sp_meta_tmem], idesc, {disable_output_lane...}, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.2 |
| `tcgen05.action.sp.cta_group.kind.collector_b` | **Decode only:** action: `mma`; sp: `sp`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::ti16`; collector_b: `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], [a_tmem], b_desc, [sp_meta_tmem], idesc, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.2 |
| `tcgen05.action.sp.cta_group.kind` | **Decode only:** action: `mma`; sp: `sp`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::ti16` | `[d_tmem], [a_tmem], b_desc, [sp_meta_tmem], idesc, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.2 |
| `tcgen05.action.cta_group.kind{.collector_a}` | **With semantics:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::f16`, `kind::f8f6f4`, `kind::i8`, `kind::tf32`; collector_a: (omitted), `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use` | `[d_tmem], a_desc, b_desc, idesc, {disable_output_lane...}, enable_input_d` | event | Core semantics | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind{.collector_a}` | **With semantics:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::f16`, `kind::f8f6f4`, `kind::i8`, `kind::tf32`; collector_a: (omitted), `collector::a::discard`, `collector::a::fill`, `collector::a::lastuse`, `collector::a::use` | `[d_tmem], a_desc, b_desc, idesc, enable_input_d` | event | Core semantics | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::ti16` | `[d_tmem], a_desc, b_desc, idesc, {disable_output_lane...}, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind.collector_b` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::ti16`; collector_b: `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], a_desc, b_desc, idesc, {disable_output_lane...}, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind.collector_b` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::ti16`; collector_b: `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], a_desc, b_desc, idesc, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::ti16` | `[d_tmem], a_desc, b_desc, idesc, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::ti16` | `[d_tmem], [a_tmem], b_desc, idesc, {disable_output_lane...}, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind.collector_b` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::ti16`; collector_b: `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], [a_tmem], b_desc, idesc, {disable_output_lane...}, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind.collector_b` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::ti16`; collector_b: `collector::b::discard`, `collector::b::fill`, `collector::b::lastuse`, `collector::b::use` | `[d_tmem], [a_tmem], b_desc, idesc, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind` | **Decode only:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::ti16` | `[d_tmem], [a_tmem], b_desc, idesc, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind` | **With semantics:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::f16`, `kind::f8f6f4`, `kind::i8`, `kind::tf32` | `[d_tmem], [a_tmem], b_desc, idesc, {disable_output_lane...}, enable_input_d` | event | Core semantics | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.10.10.1 |
| `tcgen05.action.cta_group.kind` | **With semantics:** action: `mma`; cta_group: `cta_group::1`, `cta_group::2`; kind: `kind::f16`, `kind::f8f6f4`, `kind::i8`, `kind::tf32` | `[d_tmem], [a_tmem], b_desc, idesc, enable_input_d` | event | Core semantics | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.10.10.1 |
| `tcgen05.action.ws.sp.cta_group.kind{.collector_b}` | **Decode only:** action: `mma`; ws: `ws`; sp: `sp`; cta_group: `cta_group::1`; kind: `kind::ti16`; collector_b: (omitted), `collector::b0::discard`, `collector::b0::fill`, `collector::b0::lastuse`, `collector::b0::use`, `collector::b1::discard`, `collector::b1::fill`, `collector::b1::lastuse`, `collector::b1::use`, `collector::b2::discard`, `collector::b2::fill`, `collector::b2::lastuse`, `collector::b2::use`, `collector::b3::discard`, `collector::b3::fill`, `collector::b3::lastuse`, `collector::b3::use` | `[d_tmem], a_desc, b_desc, [sp_meta_tmem], idesc, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.4 |
| `tcgen05.action.ws.sp.cta_group.kind{.collector_b}` | **Decode only:** action: `mma`; ws: `ws`; sp: `sp`; cta_group: `cta_group::1`; kind: `kind::ti16`; collector_b: (omitted), `collector::b0::discard`, `collector::b0::fill`, `collector::b0::lastuse`, `collector::b0::use`, `collector::b1::discard`, `collector::b1::fill`, `collector::b1::lastuse`, `collector::b1::use`, `collector::b2::discard`, `collector::b2::fill`, `collector::b2::lastuse`, `collector::b2::use`, `collector::b3::discard`, `collector::b3::fill`, `collector::b3::lastuse`, `collector::b3::use` | `[d_tmem], a_desc, b_desc, [sp_meta_tmem], idesc, enable_input_d, zero_col_mask` | event | Decode only: execution is rejected | none | §9.7.18.10.10.4 |
| `tcgen05.action.ws.sp.cta_group.kind{.collector_b}` | **Decode only:** action: `mma`; ws: `ws`; sp: `sp`; cta_group: `cta_group::1`; kind: `kind::ti16`; collector_b: (omitted), `collector::b0::discard`, `collector::b0::fill`, `collector::b0::lastuse`, `collector::b0::use`, `collector::b1::discard`, `collector::b1::fill`, `collector::b1::lastuse`, `collector::b1::use`, `collector::b2::discard`, `collector::b2::fill`, `collector::b2::lastuse`, `collector::b2::use`, `collector::b3::discard`, `collector::b3::fill`, `collector::b3::lastuse`, `collector::b3::use` | `[d_tmem], [a_tmem], b_desc, [sp_meta_tmem], idesc, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.4 |
| `tcgen05.action.ws.sp.cta_group.kind{.collector_b}` | **Decode only:** action: `mma`; ws: `ws`; sp: `sp`; cta_group: `cta_group::1`; kind: `kind::ti16`; collector_b: (omitted), `collector::b0::discard`, `collector::b0::fill`, `collector::b0::lastuse`, `collector::b0::use`, `collector::b1::discard`, `collector::b1::fill`, `collector::b1::lastuse`, `collector::b1::use`, `collector::b2::discard`, `collector::b2::fill`, `collector::b2::lastuse`, `collector::b2::use`, `collector::b3::discard`, `collector::b3::fill`, `collector::b3::lastuse`, `collector::b3::use` | `[d_tmem], [a_tmem], b_desc, [sp_meta_tmem], idesc, enable_input_d, zero_col_mask` | event | Decode only: execution is rejected | none | §9.7.18.10.10.4 |
| `tcgen05.action.ws.cta_group.kind{.collector_b}` | **With semantics:** action: `mma`; ws: `ws`; cta_group: `cta_group::1`; kind: `kind::f16`, `kind::f8f6f4`, `kind::i8`, `kind::tf32`; collector_b: (omitted), `collector::b0::discard`, `collector::b0::fill`, `collector::b0::lastuse`, `collector::b0::use`, `collector::b1::discard`, `collector::b1::fill`, `collector::b1::lastuse`, `collector::b1::use`, `collector::b2::discard`, `collector::b2::fill`, `collector::b2::lastuse`, `collector::b2::use`, `collector::b3::discard`, `collector::b3::fill`, `collector::b3::lastuse`, `collector::b3::use` | `[d_tmem], a_desc, b_desc, idesc, enable_input_d, zero_col_mask` | event | Core semantics | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.10.10.3 |
| `tcgen05.action.ws.cta_group.kind{.collector_b}` | **With semantics:** action: `mma`; ws: `ws`; cta_group: `cta_group::1`; kind: `kind::f16`, `kind::f8f6f4`, `kind::i8`, `kind::tf32`; collector_b: (omitted), `collector::b0::discard`, `collector::b0::fill`, `collector::b0::lastuse`, `collector::b0::use`, `collector::b1::discard`, `collector::b1::fill`, `collector::b1::lastuse`, `collector::b1::use`, `collector::b2::discard`, `collector::b2::fill`, `collector::b2::lastuse`, `collector::b2::use`, `collector::b3::discard`, `collector::b3::fill`, `collector::b3::lastuse`, `collector::b3::use` | `[d_tmem], a_desc, b_desc, idesc, enable_input_d` | event | Core semantics | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.10.10.3 |
| `tcgen05.action.ws.cta_group.kind{.collector_b}` | **Decode only:** action: `mma`; ws: `ws`; cta_group: `cta_group::1`; kind: `kind::ti16`; collector_b: (omitted), `collector::b0::discard`, `collector::b0::fill`, `collector::b0::lastuse`, `collector::b0::use`, `collector::b1::discard`, `collector::b1::fill`, `collector::b1::lastuse`, `collector::b1::use`, `collector::b2::discard`, `collector::b2::fill`, `collector::b2::lastuse`, `collector::b2::use`, `collector::b3::discard`, `collector::b3::fill`, `collector::b3::lastuse`, `collector::b3::use` | `[d_tmem], a_desc, b_desc, idesc, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.3 |
| `tcgen05.action.ws.cta_group.kind{.collector_b}` | **Decode only:** action: `mma`; ws: `ws`; cta_group: `cta_group::1`; kind: `kind::ti16`; collector_b: (omitted), `collector::b0::discard`, `collector::b0::fill`, `collector::b0::lastuse`, `collector::b0::use`, `collector::b1::discard`, `collector::b1::fill`, `collector::b1::lastuse`, `collector::b1::use`, `collector::b2::discard`, `collector::b2::fill`, `collector::b2::lastuse`, `collector::b2::use`, `collector::b3::discard`, `collector::b3::fill`, `collector::b3::lastuse`, `collector::b3::use` | `[d_tmem], a_desc, b_desc, idesc, enable_input_d, zero_col_mask` | event | Decode only: execution is rejected | none | §9.7.18.10.10.3 |
| `tcgen05.action.ws.cta_group.kind{.collector_b}` | **Decode only:** action: `mma`; ws: `ws`; cta_group: `cta_group::1`; kind: `kind::ti16`; collector_b: (omitted), `collector::b0::discard`, `collector::b0::fill`, `collector::b0::lastuse`, `collector::b0::use`, `collector::b1::discard`, `collector::b1::fill`, `collector::b1::lastuse`, `collector::b1::use`, `collector::b2::discard`, `collector::b2::fill`, `collector::b2::lastuse`, `collector::b2::use`, `collector::b3::discard`, `collector::b3::fill`, `collector::b3::lastuse`, `collector::b3::use` | `[d_tmem], [a_tmem], b_desc, idesc, enable_input_d` | event | Decode only: execution is rejected | none | §9.7.18.10.10.3 |
| `tcgen05.action.ws.cta_group.kind{.collector_b}` | **Decode only:** action: `mma`; ws: `ws`; cta_group: `cta_group::1`; kind: `kind::ti16`; collector_b: (omitted), `collector::b0::discard`, `collector::b0::fill`, `collector::b0::lastuse`, `collector::b0::use`, `collector::b1::discard`, `collector::b1::fill`, `collector::b1::lastuse`, `collector::b1::use`, `collector::b2::discard`, `collector::b2::fill`, `collector::b2::lastuse`, `collector::b2::use`, `collector::b3::discard`, `collector::b3::fill`, `collector::b3::lastuse`, `collector::b3::use` | `[d_tmem], [a_tmem], b_desc, idesc, enable_input_d, zero_col_mask` | event | Decode only: execution is rejected | none | §9.7.18.10.10.3 |
| `tcgen05.action.ws.cta_group.kind{.collector_b}` | **With semantics:** action: `mma`; ws: `ws`; cta_group: `cta_group::1`; kind: `kind::f16`, `kind::f8f6f4`, `kind::i8`, `kind::tf32`; collector_b: (omitted), `collector::b0::discard`, `collector::b0::fill`, `collector::b0::lastuse`, `collector::b0::use`, `collector::b1::discard`, `collector::b1::fill`, `collector::b1::lastuse`, `collector::b1::use`, `collector::b2::discard`, `collector::b2::fill`, `collector::b2::lastuse`, `collector::b2::use`, `collector::b3::discard`, `collector::b3::fill`, `collector::b3::lastuse`, `collector::b3::use` | `[d_tmem], [a_tmem], b_desc, idesc, enable_input_d, zero_col_mask` | event | Core semantics | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.10.10.3 |
| `tcgen05.action.ws.cta_group.kind{.collector_b}` | **With semantics:** action: `mma`; ws: `ws`; cta_group: `cta_group::1`; kind: `kind::f16`, `kind::f8f6f4`, `kind::i8`, `kind::tf32`; collector_b: (omitted), `collector::b0::discard`, `collector::b0::fill`, `collector::b0::lastuse`, `collector::b0::use`, `collector::b1::discard`, `collector::b1::fill`, `collector::b1::lastuse`, `collector::b1::use`, `collector::b2::discard`, `collector::b2::fill`, `collector::b2::lastuse`, `collector::b2::use`, `collector::b3::discard`, `collector::b3::fill`, `collector::b3::lastuse`, `collector::b3::use` | `[d_tmem], [a_tmem], b_desc, idesc, enable_input_d` | event | Core semantics | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.10.10.3 |
| `tcgen05.action.cta_group.sync.aligned` | **With semantics:** action: `relinquish_alloc_permit`; cta_group: `cta_group::1`, `cta_group::2`; sync: `sync`; aligned: `aligned` | none | event | Core semantics | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.7.1 |
| `tcgen05.action.cta_group.shift_dir` | **With semantics:** action: `shift`; cta_group: `cta_group::1`, `cta_group::2`; shift_dir: `down` | `[taddr]` | event | Core semantics | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.9.3 |
| `tcgen05.action.sync.aligned.shape.num{.unpack}.type` | **With semantics:** action: `st`; sync: `sync`; aligned: `aligned`; shape: `16x128b`, `16x256b`, `16x64b`, `32x32b`; num: `x1`, `x128`, `x16`, `x2`, `x32`, `x4`, `x64`, `x8`; unpack: (omitted), `unpack::16b`; type: `b32` | `[taddr], {r...}` | event | Core semantics | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.8.4 |
| `tcgen05.action.sync.aligned.shape.num{.unpack}.type` | **With semantics:** action: `st`; sync: `sync`; aligned: `aligned`; shape: `16x32bx2`; num: `x1`, `x128`, `x16`, `x2`, `x32`, `x4`, `x64`, `x8`; unpack: (omitted); type: `b32`<br>**Decode only:** unpack: `unpack::16b` | `[taddr], imm_half_splitoff, {r...}` | event | Core semantics (8 of 16)<br>Decode only (8 of 16): execution is rejected | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.8.4 |
| `tcgen05.action.sync.aligned` | **With semantics:** action: `wait::ld`, `wait::st`; sync: `sync`; aligned: `aligned` | none | event | Core semantics | [THREAD-TC](tcgen05.md#thread-tc) | §9.7.18.8.5 |

### Cluster launch control

The forms listed in PROG-ISA-SYNC-FORMS decode to their own constructors of `Op`; `Op.rule` (PROG-INSTR-RULE) names the rule of each.

Entries: 3 with Core semantics, 1 decode only, 0 rejected.

| Instruction | Modifiers | Operands | Kind | Status | Rule | Manual |
|---|---|---|---|---|---|---|
| `clusterlaunchcontrol.action.query.dtype.type` | **With semantics:** action: `query_cancel`; query: `get_first_ctaid::x`, `get_first_ctaid::y`, `get_first_ctaid::z`; dtype: `b32`; type: `b128` | `d, response` | local | Core semantics | [THREAD-CLC-QUERY](clc.md#thread-clc-query) | §9.7.15.19 |
| `clusterlaunchcontrol.action.query.vec.dtype.type` | **Decode only:** action: `query_cancel`; query: `get_first_ctaid`; vec: `v4`; dtype: `b32`; type: `b128` | `{d...}, response` | local | Decode only: an `Assumption.localRule` may give it a meaning | none | §9.7.15.19 |
| `clusterlaunchcontrol.action.query.ptype.type` | **With semantics:** action: `query_cancel`; query: `is_canceled`; ptype: `pred`; type: `b128` | `p, response` | local | Core semantics | [THREAD-CLC-QUERY](clc.md#thread-clc-query) | §9.7.15.19 |
| `clusterlaunchcontrol.action.async_{.space}.completion{.multicast}.type` | **With semantics:** action: `try_cancel`; async_: `async`; space: `shared::cta`; completion: `mbarrier::complete_tx::bytes`; multicast: (omitted), `multicast::cluster::all`; type: `b128`<br>**Decode only:** space: (omitted) | `[addr], [mbar]` | event | Core semantics (2 of 4)<br>Decode only (2 of 4): execution is rejected | [THREAD-CLC-QUERY](clc.md#thread-clc-query) | §9.7.15.18 |

### Other instructions

`setmaxnreg` decodes to its own constructor of `Op` (PROG-ISA-SYNC-FORMS), whose rule is THREAD-SETMAXNREG. `createpolicy`, `nanosleep`, `pmevent` and `griddepcontrol` decode to `MiscInstr` (PROG-ISA-MISC), and `MiscInstr.rule` names THREAD-CACHE-POLICY for `createpolicy` and THREAD-NO-EFFECT for the others.

Entries: 8 with Core semantics, 0 decode only, 0 rejected.

| Instruction | Modifiers | Operands | Kind | Status | Rule | Manual |
|---|---|---|---|---|---|---|
| `createpolicy.kind.level.type` | **With semantics:** kind: `cvt`; level: `L2`; type: `b64` | `cache_policy, access_property` | local | Core semantics | [THREAD-CACHE-POLICY](threads.md#thread-cache-policy) | §9.7.10.21 |
| `createpolicy.kind.pri{.sec}.type` | **With semantics:** kind: `fractional`; pri: `L2::evict_first`, `L2::evict_last`, `L2::evict_normal`, `L2::evict_unchanged`; sec: (omitted), `L2::evict_first`, `L2::evict_unchanged`; type: `b64` | `cache_policy, fraction` | local | Core semantics | [THREAD-CACHE-POLICY](threads.md#thread-cache-policy) | §9.7.10.21 |
| `createpolicy.kind.pri{.sec}.type` | **With semantics:** kind: `fractional`; pri: `L2::evict_first`, `L2::evict_last`, `L2::evict_normal`, `L2::evict_unchanged`; sec: (omitted), `L2::evict_first`, `L2::evict_unchanged`; type: `b64` | `cache_policy` | local | Core semantics | [THREAD-CACHE-POLICY](threads.md#thread-cache-policy) | §9.7.10.21 |
| `createpolicy.kind{.space}.pri{.sec}.type` | **With semantics:** kind: `range`; space: (omitted), `global`; pri: `L2::evict_first`, `L2::evict_last`, `L2::evict_normal`, `L2::evict_unchanged`; sec: (omitted), `L2::evict_first`, `L2::evict_unchanged`; type: `b64` | `cache_policy, [addr], primary_size, total_size` | event | Core semantics | [THREAD-CACHE-POLICY](threads.md#thread-cache-policy) | §9.7.10.21 |
| `griddepcontrol.action` | **With semantics:** action: `launch_dependents`, `wait` | none | event | Core semantics | [THREAD-NO-EFFECT](threads.md#thread-no-effect) | §9.7.15.14 |
| `nanosleep.type` | **With semantics:** type: `u32` | `t` | local | Core semantics | [THREAD-NO-EFFECT](threads.md#thread-no-effect) | §9.7.21.2 |
| `pmevent{.mask}` | **With semantics:** mask: (omitted), `mask` | `a` | local | Core semantics | [THREAD-NO-EFFECT](threads.md#thread-no-effect) | §9.7.21.3 |
| `setmaxnreg.action.sync.aligned.type` | **With semantics:** action: `dec`, `inc`; sync: `sync`; aligned: `aligned`; type: `u32` | `nreg` | event | Core semantics | [THREAD-SETMAXNREG](threads.md#thread-setmaxnreg) | §9.7.21.5 |

### Warp-level matrix instructions

Decoded to `MatrixInstr` (PROG-ISA-MATRIX); `spcompress` and `spdecompress` have no representation and decode to `Op.unmodeled`. `MatrixInstr.rule` names THREAD-MATRIX for `ldmatrix`, `stmatrix` and `movmatrix` and THREAD-MMA-SYNC for `mma` and `mma.sp`. The floating MMA forms have no Core arithmetic; a kernel assumption gives it (ASM-IDEAL).

Entries: 18 with Core semantics, 3 decode only, 0 rejected.

| Instruction | Modifiers | Operands | Kind | Status | Rule | Manual |
|---|---|---|---|---|---|---|
| `ldmatrix.sync.aligned.shape.num{.trans}{.space}.type` | **With semantics:** sync: `sync`; aligned: `aligned`; shape: `m8n8`; num: `x1`, `x2`, `x4`; trans: (omitted), `trans`; space: (omitted), `shared`, `shared::cta`; type: `b16` | `{r...}, [p]` | event | Core semantics | [THREAD-MATRIX](barriers.md#thread-matrix) | §9.7.16.5.15 |
| `ldmatrix.sync.aligned.shape.num{.trans}{.space}.dst_fmt.src_fmt` | **With semantics:** sync: `sync`; aligned: `aligned`; shape: `m16n16`, `m8n16`; num: `x1`, `x2`, `x4`; trans: (omitted), `trans`; space: (omitted), `shared`, `shared::cta`; dst_fmt: `b8x16`; src_fmt: `b4x16_p64`, `b6x16_p32` | `{r...}, [p]` | event | Core semantics | [THREAD-MATRIX](barriers.md#thread-matrix) | §9.7.16.5.15 |
| `ldmatrix.sync.aligned.shape.num.trans{.space}.type` | **With semantics:** sync: `sync`; aligned: `aligned`; shape: `m16n16`; num: `x1`, `x2`; trans: `trans`; space: (omitted), `shared`, `shared::cta`; type: `b8` | `{r...}, [p]` | event | Core semantics | [THREAD-MATRIX](barriers.md#thread-matrix) | §9.7.16.5.15 |
| `ldmatrix.sync.aligned.shape.num{.space}.dtype.ctype` | **Decode only:** sync: `sync`; aligned: `aligned`; shape: `m8n16`; num: `x1`, `x2`, `x4`; space: (omitted), `shared`, `shared::cta`; dtype: `s8`; ctype: `s4` | `{r...}, [p]` | event | Decode only: execution is rejected | none | §9.7.16.5.15 |
| `mma.sync.aligned.shape.alayout.blayout.dtype.atype.btype.ctype` | **With semantics:** sync: `sync`; aligned: `aligned`; shape: `m16n8k16`, `m16n8k32`, `m16n8k4`, `m16n8k8`, `m8n8k4`; alayout: `col`, `row`; blayout: `col`, `row`; dtype: `f32`; atype: `bf16`, `e4m3`, `e5m2`, `f16`, `tf32`; btype: `bf16`, `e4m3`, `e5m2`, `f16`, `tf32`; ctype: `f32` | `{d...}, {a...}, {b...}, {c...}` | local | Core semantics | [THREAD-MMA-SYNC](barriers.md#thread-mma-sync) | §9.7.16.5.14 |
| `mma.sync.aligned.shape.alayout.blayout.dtype.atype.btype.ctype` | **With semantics:** sync: `sync`; aligned: `aligned`; shape: `m16n8k16`, `m16n8k32`, `m16n8k8`, `m8n8k4`; alayout: `col`, `row`; blayout: `col`, `row`; dtype: `f16`; atype: `e4m3`, `e5m2`, `f16`; btype: `e4m3`, `e5m2`, `f16`; ctype: `f16` | `{d...}, {a...}, {b...}, {c...}` | local | Core semantics | [THREAD-MMA-SYNC](barriers.md#thread-mma-sync) | §9.7.16.5.14 |
| `mma.sync.aligned.shape.alayout.blayout.dtype.atype.btype.ctype` | **With semantics:** sync: `sync`; aligned: `aligned`; shape: `m8n8k4`; alayout: `col`, `row`; blayout: `col`, `row`; dtype: `f32`; atype: `f16`; btype: `f16`; ctype: `f16` | `{d...}, {a...}, {b...}, {c...}` | local | Core semantics | [THREAD-MMA-SYNC](barriers.md#thread-mma-sync) | §9.7.16.5.14 |
| `mma.sync.aligned.shape.alayout.blayout.dtype.atype.btype.ctype{.rnd}` | **With semantics:** sync: `sync`; aligned: `aligned`; shape: `m16n8k16`, `m16n8k4`, `m16n8k8`, `m8n8k4`; alayout: `row`; blayout: `col`; dtype: `f64`; atype: `f64`; btype: `f64`; ctype: `f64`; rnd: (omitted), `rm`, `rn`, `rp`, `rz` | `{d...}, {a...}, {b...}, {c...}` | local | Core semantics | [THREAD-MMA-SYNC](barriers.md#thread-mma-sync) | §9.7.16.5.14 |
| `mma.sync.aligned.shape.alayout.blayout{.satfinite}.dtype.atype.btype.ctype{.bitop}{.popc}` | **With semantics:** sync: `sync`; aligned: `aligned`; shape: `m16n8k128`, `m16n8k16`, `m16n8k256`, `m16n8k32`, `m16n8k64`, `m8n8k128`, `m8n8k16`, `m8n8k32`; alayout: `row`; blayout: `col`; satfinite: (omitted), `satfinite`; dtype: `s32`; atype: `b1`, `s4`, `s8`, `u4`, `u8`; btype: `b1`, `s4`, `s8`, `u4`, `u8`; ctype: `s32`; bitop: (omitted), `and`, `xor`; popc: (omitted), `popc` | `{d...}, {a...}, {b...}, {c...}` | local | Core semantics | [THREAD-MMA-SYNC](barriers.md#thread-mma-sync) | §9.7.16.5.14 |
| `mma.spvariant.sync.aligned.shape.alayout.blayout.dtype.atype.btype.ctype` | **With semantics:** spvariant: `sp`, `sp::ordered_metadata`; sync: `sync`; aligned: `aligned`; shape: `m16n8k16`, `m16n8k8`; alayout: `row`; blayout: `col`; dtype: `f32`; atype: `bf16`, `f16`, `tf32`; btype: `bf16`, `f16`, `tf32`; ctype: `f32` | `{d...}, {a...}, {b...}, {c...}, e, f` | local | Core semantics | [THREAD-MMA-SYNC](barriers.md#thread-mma-sync) | §9.7.16.6.3 |
| `mma.spvariant.sync.aligned.shape.alayout.blayout.dtype.atype.btype.ctype` | **With semantics:** spvariant: `sp`, `sp::ordered_metadata`; sync: `sync`; aligned: `aligned`; shape: `m16n8k64`; alayout: `row`; blayout: `col`; dtype: `f32`; atype: `e4m3`, `e5m2`; btype: `e4m3`, `e5m2`; ctype: `f32` | `{d...}, {a...}, {b...}, {c...}, e, f` | local | Core semantics | [THREAD-MMA-SYNC](barriers.md#thread-mma-sync) | §9.7.16.6.3 |
| `mma.spvariant.sync.aligned.shape.alayout.blayout.dtype.atype.btype.ctype` | **With semantics:** spvariant: `sp`, `sp::ordered_metadata`; sync: `sync`; aligned: `aligned`; shape: `m16n8k16`; alayout: `row`; blayout: `col`; dtype: `f16`; atype: `f16`; btype: `f16`; ctype: `f16` | `{d...}, {a...}, {b...}, {c...}, e, f` | local | Core semantics | [THREAD-MMA-SYNC](barriers.md#thread-mma-sync) | §9.7.16.6.3 |
| `mma.spvariant.sync.aligned.shape.alayout.blayout.dtype.atype.btype.ctype` | **With semantics:** spvariant: `sp`, `sp::ordered_metadata`; sync: `sync`; aligned: `aligned`; shape: `m16n8k32`; alayout: `row`; blayout: `col`; dtype: `f16`; atype: `f16`; btype: `f16`; ctype: `f16` | `{d...}, {a...}, {b...}, {c...}, e, f` | local | Core semantics | [THREAD-MMA-SYNC](barriers.md#thread-mma-sync) | §9.7.16.6.3 |
| `mma.spvariant.sync.aligned.shape.alayout.blayout{.satfinite}.dtype.atype.btype.ctype` | **With semantics:** spvariant: `sp`, `sp::ordered_metadata`; sync: `sync`; aligned: `aligned`; shape: `m16n8k128`, `m16n8k64`; alayout: `row`; blayout: `col`; satfinite: (omitted), `satfinite`; dtype: `s32`; atype: `s4`, `s8`, `u4`, `u8`; btype: `s4`, `s8`, `u4`, `u8`; ctype: `s32` | `{d...}, {a...}, {b...}, {c...}, e, f` | local | Core semantics | [THREAD-MMA-SYNC](barriers.md#thread-mma-sync) | §9.7.16.6.3 |
| `mma.spvariant.sync.aligned.shape.alayout.blayout{.satfinite}.dtype.atype.btype.ctype` | **With semantics:** spvariant: `sp`, `sp::ordered_metadata`; sync: `sync`; aligned: `aligned`; shape: `m16n8k32`, `m16n8k64`; alayout: `row`; blayout: `col`; satfinite: (omitted), `satfinite`; dtype: `s32`; atype: `s4`, `s8`, `u4`, `u8`; btype: `s4`, `s8`, `u4`, `u8`; ctype: `s32` | `{d...}, {a...}, {b...}, {c...}, e, f` | local | Core semantics | [THREAD-MMA-SYNC](barriers.md#thread-mma-sync) | §9.7.16.6.3 |
| `mma.spvariant.sync.aligned.shape.alayout.blayout.dtype.atype.btype.ctype` | **With semantics:** spvariant: `sp`, `sp::ordered_metadata`; sync: `sync`; aligned: `aligned`; shape: `m16n8k16`, `m16n8k32`; alayout: `row`; blayout: `col`; dtype: `f32`; atype: `bf16`, `f16`, `tf32`; btype: `bf16`, `f16`, `tf32`; ctype: `f32` | `{d...}, {a...}, {b...}, {c...}, e, f` | local | Core semantics | [THREAD-MMA-SYNC](barriers.md#thread-mma-sync) | §9.7.16.6.3 |
| `movmatrix.sync.aligned.shape.trans.type` | **With semantics:** sync: `sync`; aligned: `aligned`; shape: `m8n8`; trans: `trans`; type: `b16` | `d, a` | local | Core semantics | [THREAD-MATRIX](barriers.md#thread-matrix) | §9.7.16.5.17 |
| `spcompress.elemsize.idxsize.spfactor.num` | **Decode only:** elemsize: `b16`, `b8`; idxsize: `b2`, `b4`; spfactor: `sp::2:4`; num: `x1`, `x16`, `x2`, `x32`, `x4`, `x64`, `x8` | `{mdata...}, {cdata...}, {data...}, spdesc` | local | Decode only: an `Assumption.localRule` may give it a meaning | none | §9.7.10.31 |
| `spdecompress.elemsize.idxsize.spfactor.num` | **Decode only:** elemsize: `b16`, `b8`; idxsize: `b2`, `b4`; spfactor: `sp::1:16`, `sp::1:2`, `sp::1:4`, `sp::1:8`, `sp::2:16`, `sp::2:4`, `sp::2:8`, `sp::4:16`, `sp::4:8`; num: `x1`, `x16`, `x2`, `x32`, `x4`, `x64`, `x8` | `{data...}, {mdata...}, {cdata...}` | local | Decode only: an `Assumption.localRule` may give it a meaning | none | §9.7.10.32 |
| `stmatrix.sync.aligned.shape.num{.trans}{.space}.type` | **With semantics:** sync: `sync`; aligned: `aligned`; shape: `m8n8`; num: `x1`, `x2`, `x4`; trans: (omitted), `trans`; space: (omitted), `shared`, `shared::cta`; type: `b16` | `[p], {r...}` | event | Core semantics | [THREAD-MATRIX](barriers.md#thread-matrix) | §9.7.16.5.16 |
| `stmatrix.sync.aligned.shape.num.trans{.space}.type` | **With semantics:** sync: `sync`; aligned: `aligned`; shape: `m16n8`; num: `x1`, `x2`, `x4`; trans: `trans`; space: (omitted), `shared`, `shared::cta`; type: `b8` | `[p], {r...}` | event | Core semantics | [THREAD-MATRIX](barriers.md#thread-matrix) | §9.7.16.5.16 |

### Without a representation

The grammar recognizes these entries and the decoder gives them `Op.unmodeled`, which has no rule. The `multimem` operations access every memory location a multimem address points to across devices; the model executes one grid on one device and has no multimem addresses, so these operations stay without semantics.

Entries: 0 with Core semantics, 23 decode only, 0 rejected.

| Instruction | Modifiers | Operands | Kind | Status | Rule | Manual |
|---|---|---|---|---|---|---|
| `multimem.cp.api.kind{.sem}{.scope}.dst.src.completion{.cp_mask}{.type}` | **Decode only:** api: `async`; kind: `bulk`; sem: (omitted), `relaxed`, `weak`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; dst: `global`; src: `shared::cta`; completion: `bulk_group`; cp_mask: (omitted), `cp_mask`; type: (omitted), `b128` | `[dst_mem], [src_mem], size, {byte_mask}` | event | Decode only: execution is rejected | none | §9.7.10.28.4.4 |
| `multimem.cp.op.api.kind{.sem}{.scope}.dst.src.completion.redop{.noftz}.type` | **Decode only:** op: `reduce`; api: `async`; kind: `bulk`; sem: (omitted), `relaxed`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; dst: `global`; src: `shared::cta`; completion: `bulk_group`; redop: `add`, `and`, `dec`, `inc`, `max`, `min`, `or`, `xor`; noftz: (omitted), `noftz`; type: `b32`, `b64`, `bf16`, `f16`, `f32`, `f64`, `s32`, `s64`, `u32`, `u64` | `[dst_mem], [src_mem], size` | event | Decode only: execution is rejected | none | §9.7.10.28.4.5 |
| `multimem.cp.op.api.kind{.sem}{.scope}.dst.src.completion.redop.noftz.type` | **Decode only:** op: `reduce`; api: `async`; kind: `bulk`; sem: (omitted), `relaxed`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; dst: `global`; src: `shared::cta`; completion: `bulk_group`; redop: `add`; noftz: `noftz`; type: `f32` | `[dst_mem], [src_mem], size` | event | Decode only: execution is rejected | none | §9.7.10.28.4.5 |
| `multimem.ld_reduce{.sem}{.scope}{.space}.op.type` | **Decode only:** sem: (omitted), `acquire`, `relaxed`, `weak`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`; op: `add`, `and`, `max`, `min`, `or`, `xor`; type: `b32`, `b64`, `s32`, `s64`, `u32`, `u64` | `d, [addr]` | event | Decode only: execution is rejected | none | §9.7.10.15 |
| `multimem.ld_reduce{.sem}{.scope}{.space}.op{.acc}.type` | **Decode only:** sem: (omitted), `acquire`, `relaxed`, `weak`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`; op: `add`, `max`, `min`; acc: (omitted), `acc::f32`; type: `bf16x2`, `f16x2`, `f32`, `f64` | `d, [addr]` | event | Decode only: execution is rejected | none | §9.7.10.15 |
| `multimem.ld_reduce{.sem}{.scope}{.space}.op{.acc}.vec.type` | **Decode only:** sem: (omitted), `acquire`, `relaxed`, `weak`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`; op: `add`, `max`, `min`; acc: (omitted), `acc::f32`; vec: `v2`, `v4`, `v8`; type: `bf16`, `bf16x2`, `f16`, `f16x2`, `f32` | `{d...}, [addr]` | event | Decode only: execution is rejected | none | §9.7.10.15 |
| `multimem.red{.sem}{.scope}{.space}.op.type` | **Decode only:** sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`; op: `add`, `and`, `max`, `min`, `or`, `xor`; type: `b32`, `b64`, `s32`, `s64`, `u32`, `u64` | `[addr], b` | event | Decode only: execution is rejected | none | §9.7.10.15 |
| `multimem.red{.sem}{.scope}{.space}.op.type` | **Decode only:** sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`; op: `add`; type: `bf16x2`, `f16x2`, `f32`, `f64` | `[addr], b` | event | Decode only: execution is rejected | none | §9.7.10.15 |
| `multimem.red{.sem}{.scope}{.space}.op.vec.type` | **Decode only:** sem: (omitted), `relaxed`, `release`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`; op: `add`; vec: `v2`, `v4`, `v8`; type: `bf16`, `bf16x2`, `f16`, `f16x2`, `f32` | `[addr], {b...}` | event | Decode only: execution is rejected | none | §9.7.10.15 |
| `multimem.red.async.sem.scope{.space}.op.type` | **Decode only:** sem: `release`; scope: `gpu`, `sys`; space: (omitted), `global`; op: `add`; type: `s32`, `u32`, `u64` | `[addr], value` | event | Decode only: execution is rejected | none | §9.7.15.8 |
| `multimem.st{.sem}{.scope}{.space}.type` | **Decode only:** sem: (omitted), `relaxed`, `release`, `weak`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`; type: `b32`, `b64`, `s32`, `s64`, `u32`, `u64` | `[addr], b` | event | Decode only: execution is rejected | none | §9.7.10.15 |
| `multimem.st{.sem}{.scope}{.space}.type` | **Decode only:** sem: (omitted), `relaxed`, `release`, `weak`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`; type: `bf16x2`, `f16x2`, `f32`, `f64` | `[addr], b` | event | Decode only: execution is rejected | none | §9.7.10.15 |
| `multimem.st{.sem}{.scope}{.space}.vec.type` | **Decode only:** sem: (omitted), `relaxed`, `release`, `weak`; scope: (omitted), `cluster`, `cta`, `gpu`, `sys`; space: (omitted), `global`; vec: `v2`, `v4`, `v8`; type: `bf16`, `bf16x2`, `f16`, `f16x2`, `f32` | `[addr], {b...}` | event | Decode only: execution is rejected | none | §9.7.10.15 |
| `multimem.st.async.sem.scope{.space}.type` | **Decode only:** sem: `release`; scope: `gpu`, `sys`; space: (omitted), `global`; type: `b16`, `b32`, `b64`, `b8`, `f32`, `f64`, `s16`, `s32`, `s64`, `s8`, `u16`, `u32`, `u64`, `u8` | `[addr], b` | event | Decode only: execution is rejected | none | §9.7.10.13 |
| `fabric.action{.submitop}` | **Decode only:** action: `submit`; submitop: (omitted), `op_restrict::fetching` | none | event | Decode only: execution is rejected | none | §9.7.11.5.5 |
| `fabric.action.api.dst.completion.sem.scope.type` | **Decode only:** action: `try_get`; api: `async`; dst: `shared::cta`; completion: `mbarrier::complete_tx::bytes.mbarrier::report::fabric`; sem: `relaxed`; scope: `sys`; type: `b128` | `[dst_mem], [src_le_id, src_data_off], size, [mbar]` | event | Decode only: execution is rejected | none | §9.7.11.5.1 |
| `fabric.action.api.multimem.dst.completion.sem.scope.redop.type.sync` | **Decode only:** action: `try_pullred`; api: `async`; multimem: `multimem`; dst: `shared::cta`; completion: `mbarrier::complete_tx::bytes.mbarrier::report::fabric`; sem: `relaxed`; scope: `sys`; redop: `add`, `and`, `max`, `min`, `or`, `xor`; type: `b32`, `b64`, `bf16`, `f16`, `f32`, `s32`, `s64`, `u32`, `u64`; sync: `sync` | `[dst_mem], [src_le_id, src_data_off], size, [mbar], 0xFFFFFFFF` | event | Decode only: execution is rejected | none | §9.7.11.5.4 |
| `fabric.action.api{.multimem}.src.completion.sem.scope.type` | **Decode only:** action: `try_put`; api: `async`; multimem: (omitted), `multimem`; src: `shared::cta`; completion: `mbarrier::complete_tx::16B.mbarrier::report::fabric`; sem: `relaxed`; scope: `sys`; type: `b128` | `[dst_le_id, dst_data_off], [src_mem], size, [mbar]` | event | Decode only: execution is rejected | none | §9.7.11.5.2 |
| `fabric.action.api{.multimem}.src.completion.sem.scope.type` | **Decode only:** action: `try_put`; api: `async`; multimem: (omitted), `multimem`; src: `shared::cta`; completion: `mbarrier::complete_tx::16B.mbarrier::report::fabric.counted::bytes`; sem: `relaxed`; scope: `sys`; type: `b128` | `[dst_le_id, dst_data_off, dst_counter_off], [src_mem], size, [mbar]` | event | Decode only: execution is rejected | none | §9.7.11.5.2 |
| `fabric.action.api{.multimem}.src.completion.cp_mask.sem.scope.type` | **Decode only:** action: `try_put`; api: `async`; multimem: (omitted), `multimem`; src: `shared::cta`; completion: `mbarrier::complete_tx::16B.mbarrier::report::fabric`; cp_mask: `cp_mask`; sem: `relaxed`; scope: `sys`; type: `b128` | `[dst_le_id, dst_data_off], [src_mem], size, [mbar], byte_mask` | event | Decode only: execution is rejected | none | §9.7.11.5.2 |
| `fabric.action.api{.multimem}.src.completion.sem.scope.redop.type` | **Decode only:** action: `try_red`; api: `async`; multimem: (omitted), `multimem`; src: `shared::cta`; completion: `mbarrier::complete_tx::16B.mbarrier::report::fabric`; sem: `relaxed`; scope: `sys`; redop: `add`, `and`, `max`, `min`, `or`, `xor`; type: `b32`, `b64`, `bf16`, `f16`, `f32`, `f64`, `s32`, `s64`, `u32`, `u64` | `[dst_le_id, dst_data_off], [src_mem], size, [mbar]` | event | Decode only: execution is rejected | none | §9.7.11.5.3 |
| `fabric.action.api{.multimem}.src.completion.sem.scope.redop.type` | **Decode only:** action: `try_red`; api: `async`; multimem: (omitted), `multimem`; src: `shared::cta`; completion: `mbarrier::complete_tx::16B.mbarrier::report::fabric.counted::bytes`; sem: `relaxed`; scope: `sys`; redop: `add`, `and`, `max`, `min`, `or`, `xor`; type: `b32`, `b64`, `bf16`, `f16`, `f32`, `f64`, `s32`, `s64`, `u32`, `u64` | `[dst_le_id, dst_data_off, dst_counter_off], [src_mem], size, [mbar]` | event | Decode only: execution is rejected | none | §9.7.11.5.3 |
| `fabric.action.waitop` | **Decode only:** action: `wait`; waitop: `sync_restrict::reads` | none | event | Decode only: execution is rejected | none | §9.7.11.5.6 |

### Special registers

One row for each special register of PROG-ISA-SREG, with the numbered registers of one prefix in one row. The status comes from `Tests/Source/IsaCoverage.lean`: a register is rejected when the decoder accepts no `mov` of its width from it, and otherwise it has the rule that `SReg.rule` names, which THREAD-SREG proves to be exactly the registers that `sregValue` gives a value (`sregValue_isSome`). The value column is `SReg.kind`. A register that decodes without semantics is `noRule` when an instruction reads it.

Registers: 87 with Core semantics, 16 decode only, 2 rejected.

| Register | Status | Value | Rule |
|---|---|---|---|
| `%tid.x` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%tid.y` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%tid.z` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%ntid.x` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%ntid.y` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%ntid.z` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%ctaid.x` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%ctaid.y` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%ctaid.z` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%nctaid.x` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%nctaid.y` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%nctaid.z` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%clusterid.x` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%clusterid.y` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%clusterid.z` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%nclusterid.x` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%nclusterid.y` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%nclusterid.z` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%cluster_ctaid.x` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%cluster_ctaid.y` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%cluster_ctaid.z` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%cluster_nctaid.x` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%cluster_nctaid.y` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%cluster_nctaid.z` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%laneid` | Core semantics | the thread's lane in its warp | [THREAD-SREG](threads.md#thread-sreg) |
| `%warpid` | Core semantics | changes while the thread runs; each read is an event with an open value | [THREAD-SREG](threads.md#thread-sreg) |
| `%nwarpid` | Core semantics | fixed before launch, unconstrained (`Launch.sregInit`) | [THREAD-SREG](threads.md#thread-sreg) |
| `%smid` | Core semantics | changes while the thread runs; each read is an event with an open value | [THREAD-SREG](threads.md#thread-sreg) |
| `%nsmid` | Core semantics | fixed before launch, unconstrained (`Launch.sregInit`) | [THREAD-SREG](threads.md#thread-sreg) |
| `%gridid` | Core semantics | fixed before launch, unconstrained (`Launch.sregInit`) | [THREAD-SREG](threads.md#thread-sreg) |
| `%is_explicit_cluster` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%cluster_ctarank` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%cluster_nctarank` | Core semantics | the thread's position in the launch | [THREAD-SREG](threads.md#thread-sreg) |
| `%lanemask_eq` | Core semantics | the thread's lane in its warp | [THREAD-SREG](threads.md#thread-sreg) |
| `%lanemask_le` | Core semantics | the thread's lane in its warp | [THREAD-SREG](threads.md#thread-sreg) |
| `%lanemask_lt` | Core semantics | the thread's lane in its warp | [THREAD-SREG](threads.md#thread-sreg) |
| `%lanemask_ge` | Core semantics | the thread's lane in its warp | [THREAD-SREG](threads.md#thread-sreg) |
| `%lanemask_gt` | Core semantics | the thread's lane in its warp | [THREAD-SREG](threads.md#thread-sreg) |
| `%clock` | Core semantics | changes while the thread runs; each read is an event with an open value | [THREAD-SREG](threads.md#thread-sreg) |
| `%clock_hi` | Core semantics | changes while the thread runs; each read is an event with an open value | [THREAD-SREG](threads.md#thread-sreg) |
| `%clock64` | Core semantics | changes while the thread runs; each read is an event with an open value | [THREAD-SREG](threads.md#thread-sreg) |
| `%globaltimer` | Core semantics | changes while the thread runs; each read is an event with an open value | [THREAD-SREG](threads.md#thread-sreg) |
| `%globaltimer_lo` | Core semantics | changes while the thread runs; each read is an event with an open value | [THREAD-SREG](threads.md#thread-sreg) |
| `%globaltimer_hi` | Core semantics | changes while the thread runs; each read is an event with an open value | [THREAD-SREG](threads.md#thread-sreg) |
| `%reserved_smem_offset_begin` | Core semantics | fixed before launch, unconstrained (`Launch.sregInit`) | [THREAD-SREG](threads.md#thread-sreg) |
| `%reserved_smem_offset_end` | Core semantics | fixed before launch, unconstrained (`Launch.sregInit`) | [THREAD-SREG](threads.md#thread-sreg) |
| `%reserved_smem_offset_cap` | Core semantics | fixed before launch, unconstrained (`Launch.sregInit`) | [THREAD-SREG](threads.md#thread-sreg) |
| `%total_smem_size` | Core semantics | fixed before launch, unconstrained (`Launch.sregInit`) | [THREAD-SREG](threads.md#thread-sreg) |
| `%aggr_smem_size` | Core semantics | fixed before launch, unconstrained (`Launch.sregInit`) | [THREAD-SREG](threads.md#thread-sreg) |
| `%dynamic_smem_size` | Core semantics | fixed before launch, unconstrained (`Launch.sregInit`) | [THREAD-SREG](threads.md#thread-sreg) |
| `%current_graph_exec` | Core semantics | fixed before launch, unconstrained (`Launch.sregInit`) | [THREAD-SREG](threads.md#thread-sreg) |
| `%perctamemoryoffset` | Rejected at decoding: %perctamemoryoffset without .minperctamemory | none | none |
| `%perctamemorysize` | Rejected at decoding: %perctamemorysize without .minperctamemory | none | none |
| `%locality_domain_id` | Core semantics | fixed before launch, unconstrained (`Launch.sregInit`) | [THREAD-SREG](threads.md#thread-sreg) |
| `%locality_domain_supplemental_sm` | Core semantics | fixed before launch, unconstrained (`Launch.sregInit`) | [THREAD-SREG](threads.md#thread-sreg) |
| `%pm0–%pm7` | Decode only: an `Assumption.localRule` may give it a meaning | none | none |
| `%pm0_64–%pm7_64` | Decode only: an `Assumption.localRule` may give it a meaning | none | none |
| `%envreg0–%envreg31` | Core semantics | fixed before launch, unconstrained (`Launch.sregInit`) | [THREAD-SREG](threads.md#thread-sreg) |
| `%reserved_smem_offset_0–%reserved_smem_offset_1` | Core semantics | fixed before launch, unconstrained (`Launch.sregInit`) | [THREAD-SREG](threads.md#thread-sreg) |

### Not decoded

These instructions are recognized by name and rejected before decoding.

| Instruction | Reason | Manual |
|---|---|---|
| `wgmma` | out of scope: wgmma | §9.7.17.5.2, §9.7.17.7.1, §9.7.17.7.2, §9.7.17.7.3 |
