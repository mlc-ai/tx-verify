# Assumptions a kernel may declare

What a kernel may assume beyond the core rules, and what each kind of assumption makes the model trust. The core leaves some instructions without a rule and rejects some programs that real code relies on; a kernel can still be proved when it declares an assumption, and every assumption it declares appears in its theorem. Each assumption is built from one of the constructors in this chapter and is scoped to the instruction forms or the sites (`pc`) the kernel names. The first group of rules is the interface every assumption has, and each later rule is one constructor. Concepts come first, then the rules.

Generated from the Lean comments of `Core/` and `Assumption/` by `Tools/coredoc.py`. Every entry links to the Lean source it was generated from. [All chapters](README.md).

## Contents

- [Concepts](#concepts)
  - [The interface of an assumption](#the-interface-of-an-assumption)
    - [`Assumption`](#c-assumption)
  - [Exact real arithmetic](#exact-real-arithmetic)
    - [`Assumption.IdealScope`](#c-assumption-idealscope)
    - [`Assumption.FloatForm`](#c-assumption-floatform)
    - [`Assumption.execIdealFloat`](#c-assumption-execidealfloat)
    - [`Assumption.execIdealMma`](#c-assumption-execidealmma)
    - [`Assumption.idealRmw`](#c-assumption-idealrmw)
  - [Approximate instructions read as exact](#approximate-instructions-read-as-exact)
    - [`Assumption.ApproxForm`](#c-assumption-approxform)
    - [`Assumption.execApproxExact`](#c-assumption-execapproxexact)
  - [Code templates read as exact functions](#code-templates-read-as-exact-functions)
    - [`Assumption.SegShape`](#c-assumption-segshape)
    - [`Assumption.SegTemplate`](#c-assumption-segtemplate)
    - [`Assumption.execSegment`](#c-assumption-execsegment)
  - [Readings at named sites](#readings-at-named-sites)
    - [`Assumption.execPairEven`](#c-assumption-execpaireven)
    - [`Assumption.ldConsumedAt`](#c-assumption-ldconsumedat)
    - [`Assumption.commitPerformedAt`](#c-assumption-commitperformedat)
- [Rules](#rules)
  - [The interface of an assumption](#the-interface-of-an-assumption)
    - [the interface of a kernel assumption](#asm-interface) (`ASM-INTERFACE`)
  - [Arithmetic read as exact](#arithmetic-read-as-exact)
    - [ideal-real floating arithmetic, for the forms a kernel names](#asm-ideal) (`ASM-IDEAL`)
    - [approximate instructions read as exact, for the forms a kernel names](#asm-approx) (`ASM-APPROX`)
    - [a straight-line code template read as an exact function, at named sites](#asm-segment) (`ASM-SEGMENT`)
      - [ideal arithmetic and hardware error](#open-num) (`OPEN-NUM`)
  - [Memory and synchronization](#memory-and-synchronization)
    - [ld.global.nc at named sites reads launch content](#asm-nc) (`ASM-NC`)
    - [CTA-scoped mbarrier synchronization reaches the cluster, at named sites](#asm-mbar-scope) (`ASM-MBAR-SCOPE`)
    - [a `tcgen05.ld` whose registers are all consumed is complete](#asm-tcld-dataflow) (`ASM-TCLD-DATAFLOW`)
    - [a commit's arrive-on precedes the next commit's, at named sites](#asm-commit-order) (`ASM-COMMIT-ORDER`)
    - [a request at a named site need not follow a warpgroup synchronization](#asm-setmaxnreg-sync) (`ASM-SETMAXNREG-SYNC`)
  - [Addresses and control flow](#addresses-and-control-flow)
    - [clearing bit 24 of a shared window address names the even CTA of the pair](#asm-peer-bit) (`ASM-PEER-BIT`)
    - [lanes of a warp spinning on one poll stay converged and agree](#asm-poll-agree) (`ASM-POLL-AGREE`)

## Concepts

The definitions a reader needs to follow the rules: the interface of an assumption and the semantics the constructors give to the instructions they select. Each text is the Lean doc comment, and each entry links to its Lean source.

### The interface of an assumption

The fields through which an assumption refines the core.

<a id="c-assumption"></a>
#### `Assumption`

*structure*

A kernel's own assumption: a statement of what is assumed about the hardware, and the hooks
through which it refines the core (ASM-INTERFACE).

- `name`
- `statement`: What is assumed about the hardware, with the evidence for it.
- `localRule`: A rule for the local operations and states it selects, in place of the core's rule; `none` keeps the core's rule.
- `mmaRule`: Numerical interpretation of one floating MMA result cell. Inputs are the observed operand bytes and an independently justified old accumulator; this grants no visibility.
- `rmwRule`: Numerical interpretation of one floating element of an atomic read-modify-write (`atom`, `red`) or of a tensor reduction: the operation, the element type, the old value in memory and the operand. This grants no visibility.
- `matrixMmaRule`: Numerical interpretation of one floating result element of a warp-level `mma` or `mma.sp` with element types `t`: the A elements of its row, the B elements of its column, paired in order, and its C element. This grants no visibility.
- `ncLoads`: The sites (`pc`) where `ld.global.nc` is allowed (the core has no rule for it).
- `wf`: Extra conditions on possible executions, e.g. what an `nc` read returns.
- `ub`: Extra undefined behaviour, e.g. writing bytes an `nc` read reads.
- `clusterScopeMbar`: The sites (`pc`) whose `.cta`-scoped mbarrier release arrivals and acquire waits synchronize at cluster scope.
- `segmentRule`: At the thread's `pc`, `some r` takes the straight-line code from there as one local step with outcome `r` (the state after it, or a fault), before the instruction rules (THREAD-LOCAL).
- `tcLdWait`: The `tcgen05.ld` sites (`pc`) followed by an implicit `tcgen05.wait::ld` (THREAD-RUN).
- `tcStWaitLd`: The `tcgen05.st` sites preceded by an implicit `tcgen05.wait::ld` (THREAD-RUN).
- `commitInOrder`: The `tcgen05.commit` sites whose arrive-on completes before the arrive-on of the issuing thread's next commit at the same rank (ERR-SHARED-LIFETIME).
- `storeReadsBeforeExit`: The tensor-store sites whose source reads complete before the issuing thread exits (ERR-SHARED-LIFETIME).
- `uniPoll`: The guarded `bra.uni` sites (`pc`) after a poll whose executions by two lanes of a warp are not compared when both polls are of one mbarrier, whatever their parities (ERR-NONUNIFORM-GUARD).
- `regSyncExempt`: The `setmaxnreg` request sites (`pc`) that are exempt from the requirement that the previous request of the warpgroup is ordered before them (ERR-SETMAXNREG).

[Lean source: `Core/Data/Types.lean` L501-L552](../../Core/Data/Types.lean#L501-L552)

### Exact real arithmetic

The forms an ideal-real assumption covers and the exact operations it gives them.

<a id="c-assumption-idealscope"></a>
#### `Assumption.IdealScope`

*structure*

What an ideal-real assumption covers: floating instruction forms, MMA kinds and the elements
of `atom`, `red` and tensor reductions (operation, element type).

- `float`
- `mma`
- `rmw`
- `warpMma`: Warp-level `mma` and `mma.sp` element types (DEP-WARP-MMA).

[Lean source: `Assumption/IdealReal.lean` L232-L239](../../Assumption/IdealReal.lean#L232-L239)

<a id="c-assumption-floatform"></a>
#### `Assumption.FloatForm`

*inductive*

A decoded floating instruction form: one per `Op` constructor and format, and only `.rn`
for the constructors that keep their rounding modifier.

- `add`: `add{.rnd}{.ftz}.<fmt>`
- `mul`: `mul{.rnd}{.ftz}.<fmt>`
- `neg`: `neg{.ftz}.<fmt>` on one lane.
- `fma`: `fma.rnd{.ftz}.<fmt>`
- `mulF32x2`: `mul{.rnd}{.ftz}.f32x2`
- `subRn`: `sub{.rn}{.ftz}.<fmt>`: round to nearest, written or by default; other roundings are no form.
- `addRnF32x2`: `add{.rn}{.ftz}.f32x2`
- `subRnF32x2`: `sub{.rn}{.ftz}.f32x2`
- `fmaRnF32x2`: `fma.rn{.ftz}.f32x2`
- `min`: `min{.ftz}.<fmt>` with two or three sources
- `max`: `max{.ftz}.<fmt>` with two or three sources
- `setp`: `setp.CmpOp{.ftz}.<fmt>`, ordered and unordered `CmpOp`, with no infinite constant operand
- `setpInf`: `setp.CmpOp{.ftz}.<fmt>` with an infinite constant operand (`0fFF800000`, `0f7F800000`)
- `cvtF32F16`: `cvt.f32.f16`
- `cvtRnF16x2F32`: `cvt.rn.f16x2.f32`

[Lean source: `Assumption/IdealReal.lean` L120-L155](../../Assumption/IdealReal.lean#L120-L155)

<a id="c-assumption-execidealfloat"></a>
#### `Assumption.execIdealFloat`

*def*

Floating-point arithmetic, comparisons and conversions of the forms `FloatForm.ofOp` selects,
over the extended reals, whatever the rounding modifier. Each operand is read by `readEReal`. The
rule declines (`none`) on a NaN operand and on `∞ - ∞` and `0 · ∞`, so the Core rule applies
there. A real result is a payload, an infinite result the bits of that infinity.

[Lean source: `Assumption/IdealReal.lean` L324-L384](../../Assumption/IdealReal.lean#L324-L384)

<a id="c-assumption-execidealmma"></a>
#### `Assumption.execIdealMma`

*def*

Ideal arithmetic only. The caller must establish the byte observations and, when
accumulating, the old D value through the execution's TMEM rules. Disabled accumulation
does not read D. Transposition is already reflected in operand-address selection; `.ws` with
M < 128 reads one A row per D lane (`TcMma.operandRow`). `kind::f16` and `kind::tf32` are
floating; integer kinds have exact Core arithmetic.

[Lean source: `Assumption/IdealReal.lean` L447-L463](../../Assumption/IdealReal.lean#L447-L463)

<a id="c-assumption-idealrmw"></a>
#### `Assumption.idealRmw`

*def*

Floating elements of `atom`, `red` and tensor reductions (THREAD-ATOMIC-OP), over the reals:
add, and min and max, of `.f16`, `.bf16` and `.f32` elements.

[Lean source: `Assumption/IdealReal.lean` L386-L401](../../Assumption/IdealReal.lean#L386-L401)

### Approximate instructions read as exact

The approximate forms and the exact functions they are read as.

<a id="c-assumption-approxform"></a>
#### `Assumption.ApproxForm`

*inductive*

A decoded approximate instruction form.

- `div`: `div.approx{.ftz}.<fmt>`
- `rsqrt`: `rsqrt.approx{.ftz}.<fmt>`
- `ex2`: `ex2.approx{.ftz}.<fmt>`
- `rcp`: `rcp.approx{.ftz}.<fmt>`

[Lean source: `Assumption/ApproxExact.lean` L60-L70](../../Assumption/ApproxExact.lean#L60-L70)

<a id="c-assumption-execapproxexact"></a>
#### `Assumption.execApproxExact`

*def*

The exact functions of the approximate instructions on finite operands; `none` (the Core rule
applies) when an operand is infinite or NaN.

[Lean source: `Assumption/ApproxExact.lean` L100-L117](../../Assumption/ApproxExact.lean#L100-L117)

### Code templates read as exact functions

A reviewed straight-line template, its shapes and the step that replaces an instance of it.

<a id="c-assumption-segshape"></a>
#### `Assumption.SegShape`

*structure*

One shape of a template: its instructions, its (input, output) slot pairs, its constant
slots with their values, and whether it defines the constants (or reuses them).

- `body`
- `io`
- `consts`
- `defines`

[Lean source: `Assumption/SegmentExact.lean` L141-L147](../../Assumption/SegmentExact.lean#L141-L147)

<a id="c-assumption-segtemplate"></a>
#### `Assumption.SegTemplate`

*structure*

A reviewed template: the text quoted in the statement, its shapes and the exact function
each output is read as.

- `text`
- `shapes`
- `fn`

[Lean source: `Assumption/SegmentExact.lean` L152-L157](../../Assumption/SegmentExact.lean#L152-L157)

<a id="c-assumption-execsegment"></a>
#### `Assumption.execSegment`

*def*

The effect of one instance: reusing shapes check their constants; every written register is
cleared, then the constants of a defining shape and each output (the exact function of its
input's `f32` number) are set; execution continues after the instance.

[Lean source: `Assumption/SegmentExact.lean` L187-L205](../../Assumption/SegmentExact.lean#L187-L205)

### Readings at named sites

The step, the static check and the execution condition of the site-scoped hardware readings.

<a id="c-assumption-execpaireven"></a>
#### `Assumption.execPairEven`

*def*

The step of `and.b32 d, a, -16777217` at a selected site: the `.shared::cluster` address of
byte `a` in the even CTA of the pair.

[Lean source: `Assumption/PairEven.lean` L59-L67](../../Assumption/PairEven.lean#L59-L67)

<a id="c-assumption-ldconsumedat"></a>
#### `Assumption.ldConsumedAt`

*def*

The `tcgen05.ld` at `pc` has all its destination registers consumed by computing
instructions before the thread's next instruction other than a local one or a `tcgen05.ld`,
on a straight path.

[Lean source: `Assumption/TcLdDataflow.lean` L136-L144](../../Assumption/TcLdDataflow.lean#L136-L144)

<a id="c-assumption-commitperformedat"></a>
#### `Assumption.commitPerformedAt`

*def*

At the commit sites `sites`: when the arrive-on at rank `r` of the issuing thread's next
commit is performed, so is the selected commit's at rank `r`.

[Lean source: `Assumption/CommitOrder.lean` L53-L59](../../Assumption/CommitOrder.lean#L53-L59)

## Rules

Each rule is a contract block of the Lean source and describes one constructor. Its statement says what an assumption built from it makes the model trust, at which instructions or sites, and where it applies, which change to the program would make it unnecessary. The source cites the PTX ISA 9.5 text and the outside evidence it rests on, and the direction says how it relates to that text. The fields that reviewers check against the Lean bodies are collected under Details for reviewers.

### The interface of an assumption

The fields of an assumption and the hooks through which a constructor selects instructions or sites.

<a id="asm-interface"></a>
#### the interface of a kernel assumption (`ASM-INTERFACE`)

*Rule* · [Lean comment: `Core/Data/Types.lean` L452-L498](../../Core/Data/Types.lean#L452-L498)

A kernel states its own assumptions, each of which refines what the core leaves undefined or adds a condition. An assumption can supply a rule for the instructions it selects in place of the core's, allow `ld.global.nc` at chosen sites, supply floating-point arithmetic for MMAs and reductions, add undefined behaviour, restrict the executions, or add the synchronization and ordering that its hooks select. Each of these is declared in the kernel's theorem.

Source:

- 

Direction: `interface` (the entry defines an extension interface)

Lean definitions: [`Assumption`](../../Core/Data/Types.lean#L501-L552) ([concept](#c-assumption))

<details>
<summary>Details for reviewers</summary>

- none (per-kernel trust, listed in each theorem)

**Effect:** An assumption refines what the core leaves undefined, and each kernel declares its own, scoped to what its proof relies on. Its fields differ in risk: `localRule` replaces the core's rule for the instructions and states it selects (THREAD-LOCAL), which is the trust class of `segmentRule`, and receives the thread state, so it can be limited to instruction forms or sites; it returns `none` for every other instruction, which keeps the core's rule; `ncLoads` allows `ld.global.nc` at the sites (`pc`) it selects; `mmaRule` supplies only floating MMA arithmetic, with no memory ordering or accumulator-provenance guarantee; `matrixMmaRule` supplies only the floating arithmetic of one result element of a warp-level `mma` or `mma.sp` (DEP-WARP-MMA); `rmwRule` supplies only the floating arithmetic of one element of an `atom`, a `red` or a tensor reduction (THREAD-ATOMIC-OP), with no ordering or source; `ub` adds undefined behaviour, which is only stricter; `wf` removes executions, which can make a theorem vacuous, so every use of `wf` must be justified in the assumption's own contract. `clusterScopeMbar` adds synchronization: at the sites (`pc`) it selects, `.cta`-scoped mbarrier release arrivals and acquire waits are treated as `.cluster`-scoped (THREAD-RUN), which adds `baseCausality` edges the ISA does not guarantee and so can make a theorem unsound for hardware that does not provide them. Further hooks are off unless an assumption selects a site, and each is consulted through one definition only. `segmentRule` replaces instruction semantics: at a local instruction it may take the straight-line code from there as one local step with its own outcome (THREAD-LOCAL), also over forms the core defines (trust). `tcLdWait` adds ordering: a `tcgen05.ld` at a selected site is followed by an implicit `tcgen05.wait::ld` at the same site (THREAD-RUN, trust). `tcStWaitLd` orders earlier Tensor Memory reads: a selected `tcgen05.st` is preceded by an implicit `tcgen05.wait::ld` at the same site (THREAD-RUN, trust). `commitInOrder` adds ordering: the arrive-on of a `tcgen05.commit` at a selected site completes before the issuing thread's next commit's arrive-on at the same rank starts, an edge of the lifetime order (ERR-SHARED-LIFETIME `LifetimeStep`, trust). `storeReadsBeforeExit` adds a lifetime edge from the shared source read completion of a selected tensor store to its issuer's subsequent exit (ERR-SHARED-LIFETIME, trust). `uniPoll` removes a safety rejection: two executions of a selected `bra.uni` guarded by the predicate of the `mbarrier.try_wait` right before it, by lanes of one warp whose records right before are polls of one mbarrier, are not compared, whatever the polls' parities (ERR-NONUNIFORM-GUARD `PollAgreeExempt`, trust). `regSyncExempt` removes a safety rejection: a `setmaxnreg` request at a selected site is not required to follow the previous request of its warpgroup in the base causality order (ERR-SETMAXNREG, the fourth clause of `SetMaxNReg.UnsafeAt`, trust); the direction, count, warpgroup and same-ordinal checks stay.

</details>

### Arithmetic read as exact

Floating instructions, approximate instructions and whole code templates read as exact real functions. The distance between these exact results and the hardware's is left open.

<a id="asm-ideal"></a>
#### ideal-real floating arithmetic, for the forms a kernel names (`ASM-IDEAL`)

*Rule* · [Lean comment: `Assumption/IdealReal.lean` L21-L103](../../Assumption/IdealReal.lean#L21-L103)

For the floating instruction forms, MMA kinds and atomic and reduction elements a kernel names, the model computes each result as the exact real number of the operation, without rounding, overflow or subnormal values, and in place of the Core rule. An infinite operand of a floating instruction form is read as that infinity, and the Core rule applies to a NaN operand, `∞ - ∞` and `0 · ∞`.

Source:

- 

Direction: `not-conservative` (the mathematical result differs from hardware results as explained by its OPEN entry)

Lean definitions: [`Assumption.floatFmtText`](../../Assumption/IdealReal.lean#L116-L118), [`Assumption.FloatForm`](../../Assumption/IdealReal.lean#L120-L155) ([concept](#c-assumption-floatform)), [`Assumption.isInfConst`](../../Assumption/IdealReal.lean#L157-L160), [`Assumption.FloatForm.ofOp`](../../Assumption/IdealReal.lean#L162-L192), [`Assumption.FloatForm.text`](../../Assumption/IdealReal.lean#L194-L210), [`Assumption.f8f6f4Text`](../../Assumption/IdealReal.lean#L212-L213), [`Assumption.mmaKindText`](../../Assumption/IdealReal.lean#L215-L221), [`Assumption.rmwText`](../../Assumption/IdealReal.lean#L223-L230), [`Assumption.IdealScope`](../../Assumption/IdealReal.lean#L232-L239) ([concept](#c-assumption-idealscope)), [`Assumption.IdealScope.text`](../../Assumption/IdealReal.lean#L252-L254), [`Assumption.readEReal`](../../Assumption/IdealReal.lean#L256-L270), [`Assumption.readEReal.ofDatum`](../../Assumption/IdealReal.lean#L265-L270), [`Assumption.readERealOpnd`](../../Assumption/IdealReal.lean#L272-L279), [`Assumption.readERealPair`](../../Assumption/IdealReal.lean#L281-L293), [`Assumption.addEReal`](../../Assumption/IdealReal.lean#L295-L297), [`Assumption.mulEReal`](../../Assumption/IdealReal.lean#L299-L301), [`Assumption.erealValue`](../../Assumption/IdealReal.lean#L303-L308), [`Assumption.erealCompare`](../../Assumption/IdealReal.lean#L310-L314), [`Assumption.bindRead`](../../Assumption/IdealReal.lean#L316-L322), [`Assumption.execIdealFloat`](../../Assumption/IdealReal.lean#L324-L384) ([concept](#c-assumption-execidealfloat)), [`Assumption.idealRmw`](../../Assumption/IdealReal.lean#L386-L401) ([concept](#c-assumption-idealrmw)), [`Assumption.idealMmaElement`](../../Assumption/IdealReal.lean#L412-L427), [`Assumption.idealMmaDot`](../../Assumption/IdealReal.lean#L429-L437), [`Assumption.idealMmaAccumulator`](../../Assumption/IdealReal.lean#L439-L445), [`Assumption.tf32Value`](../../Assumption/IdealReal.lean#L403-L410), [`Assumption.execIdealMma`](../../Assumption/IdealReal.lean#L447-L463) ([concept](#c-assumption-execidealmma)), [`Assumption.dtypeText`](../../Assumption/IdealReal.lean#L241-L245), [`Assumption.warpMmaText`](../../Assumption/IdealReal.lean#L247-L250), [`Assumption.idealWarpElem`](../../Assumption/IdealReal.lean#L465-L475), [`Assumption.idealWarpMma`](../../Assumption/IdealReal.lean#L477-L487), [`Assumption.idealReal`](../../Assumption/IdealReal.lean#L489-L504)

<details>
<summary>Details for reviewers</summary>

- Explicit numerical interpretation
- §9.7.3, §9.7.10.24 (the hardware operations this reading idealizes)
- §9.7.3.3
- §9.7.3.4
- §9.7.3.6 (`.f32x2`): "d[i] = fA[i] + fB[i];"
- §9.7.3.6 (`.f32x2`): "d[i] = fA[i] - fB[i];"
- §9.7.3.6 (`.f32x2`): "d[i] = fA[i] * fB[i] + fC[i];"
- §9.7.3.6 (rounding modifiers): ".rn mantissa LSB rounds to nearest even"
- §9.7.3.6 (rounding modifiers): ".rm mantissa LSB rounds toward negative infinity"
- §9.7.3.11
- §9.7.3.12: "Store the maximum of a , b and optionally c in d ."
- §9.7.7.2
- §9.3.1.2: "If both operands are numeric values (not NaN ), then these comparisons have the same
    result as their ordered counterparts."
- §4.5.2 (`0f` constants are IEEE 754 single-precision bit patterns)

**Effect:** `idealReal name scope why` replaces, for exactly the forms in `scope`, floating arithmetic and conversion (`float`, one `FloatForm` per instruction form, `FloatForm.ofOp`), floating MMA (`mma`, by `kind`) and the floating elements of `atom`, `red` and tensor reductions (`rmw`, by operation and element type, THREAD-ATOMIC-OP) with exact real operations. A kernel assumption's local rule is consulted before the Core rule and replaces it for the instructions it selects (THREAD-LOCAL), so a selected form has the ideal result although Core has a rule for it. `add`, `mul` and `fma` are exact for every rounding modifier. A floating instruction form reads each operand in the extended reals (`readEReal`): a payload of the format is its number, every other value the datum THREAD-NUM's `classify` reads, with either zero `0` and an infinity `⊥` or `⊤` (`0fFF800000` and `0f7F800000` included). The operation is the extended-real one: `min`/`max` of two or three values are the minimum and maximum, and `setp` is the comparison (`erealCompare`), where an unordered comparison equals its ordered counterpart since no operand is NaN (§9.3.1.2). The rule declines, and the Core rule (THREAD-FLOAT, THREAD-CVT) gives the result, when an operand is NaN or the operation is `∞ - ∞` (`addEReal`) or `0 · ∞` (`mulEReal`), which have no extended-real value. A real result is the payload `.float fmt x` and an infinite result the bits of that infinity (`erealValue`). The reading has one zero: a `-0` operand reads as `0` and a zero result is the payload `+0`, where the Core rule may give `-0` (`x - x` under `.rm`, `cvt.f32.f16` of `-0`). `setpInf` is the form of a `setp` with an infinite constant operand; it computes as `setp`, and a scope that names `setp` but not `setpInf` leaves such an instruction to the Core rule. The assumption changes the values the selected instructions produce. When an integer or bit instruction reads such a result it reads the bits of its encoding (`FloatFmt.encode`, THREAD-BITS), so control flow, addresses and loop bounds that depend on floating-point bits are determined by the ideal values, and all four conclusions (safe, progress, terminates, result) hold for the ideal machine. A `.f32x2` operand is split into its two 32-bit halves, §9.7.3: "fA[0] = a[0:31]; fA[1] = a[32:63];" (`readERealPair`). Results are payloads `.float fmt x`, whose bits (read by integer instructions, or stored and reloaded) are given by THREAD-BITS, with the reading EXT-FLOAT-BITS when `x` is not representable in `fmt`. A floating MMA (`kind::f16`, `kind::tf32`, `kind::f8f6f4`) is the exact dot product over `kind.k` elements read by `TcMma.elementBytes`, with A row `TcMma.operandRow`. An element of `kind::f8f6f4` has a value only for the 8-bit types E4M3 and E5M2 (the byte as that format). An MMA with a 6- or 4-bit operand type keeps `noRule` under every scope (EXT-TCFIG) and needs a dedicated assumption. A warp-level `mma` or `mma.sp` whose element types are in `warpMma` has each D element the exact sum of the products of its A and B elements plus C (`idealWarpMma`, DEP-WARP-MMA). MMA, warp-level MMA and atomic or reduction elements are read by `valFloat` (THREAD-NUM), so an infinite or NaN element is `badValue`. A `.tf32` element is read by `tf32Value`, and an MMA with an `.f64` element keeps `noRule`: the assumption gives `.f64` elements no value, although `.f64` is a payload format (THREAD-BITS). The statement is generated from the scope and lists every form it covers.

</details>

<a id="asm-approx"></a>
#### approximate instructions read as exact, for the forms a kernel names (`ASM-APPROX`)

*Rule* · [Lean comment: `Assumption/ApproxExact.lean` L21-L57](../../Assumption/ApproxExact.lean#L21-L57)

For the approximate instruction forms a kernel names (`div.approx`, `rsqrt.approx`, `ex2.approx`, `rcp.approx`), the model takes each result to be the exact real value of the function the instruction approximates, ignoring its error bound and the flushing of tiny results to zero, for finite operands. A divisor of zero or a `rsqrt` argument that is not positive is undefined behaviour, and an infinite or NaN operand takes the Core rule.

Source:

- 

Direction: `not-conservative` (the mathematical result differs from hardware results as explained by its OPEN entry)

Lean definitions: [`Assumption.ApproxForm`](../../Assumption/ApproxExact.lean#L60-L70) ([concept](#c-assumption-approxform)), [`Assumption.ApproxForm.ofOp`](../../Assumption/ApproxExact.lean#L72-L84), [`Assumption.ApproxForm.text`](../../Assumption/ApproxExact.lean#L86-L92), [`Assumption.readFinite`](../../Assumption/ApproxExact.lean#L94-L98), [`Assumption.execApproxExact`](../../Assumption/ApproxExact.lean#L100-L117) ([concept](#c-assumption-execapproxexact)), [`Assumption.approxExact`](../../Assumption/ApproxExact.lean#L119-L127)

<details>
<summary>Details for reviewers</summary>

- §9.7.3.8 (div.approx.f32: bounded ulp error)
- §9.7.3.16 (rsqrt.approx.f32: bounded relative error)
- §9.7.3.21 (ex2): "Raise 2 to the power a ."
- §9.7.3.21 (ex2): "The maximum ulp error is 2 ulp from correctly rounded result across the full
    range of inputs."
- §9.7.3.21 (ex2): "ex2.ftz.f32 flushes subnormal inputs and results to sign-preserving zero."
- §9.7.3.13 (rcp): "Compute 1/a , store result in d ."
- §9.7.3.13 (rcp): "The maximum ulp error is 1 across the full range of inputs."

**Effect:** The core gives these approximations only the special values of their tables (THREAD-FLOAT-APPROX). `approxExact name forms why` gives each form listed in `forms` one exact real value on finite operands, through the field `localRule`, which is consulted before the Core rule (THREAD-LOCAL): `div.approx` the exact real `a / b`, `rsqrt.approx` the exact `1 / sqrt a`, `ex2.approx` the exact `2 ^ a` (`Real.rpow`) and `rcp.approx` the exact `1 / a`. The result is undefined unless the divisor of `div` and `rcp` is nonzero and the `rsqrt` argument positive, so the ideal result exists; this is stricter than the Core table, which gives `rcp(±0) = ±∞`. On an infinite or NaN operand the rule declines and the Core table gives the result (`ex2(-∞) = +0`). The constructor sets no `wf` and no `ub`. The statement is generated from the forms and lists every form it covers.

</details>

<a id="asm-segment"></a>
#### a straight-line code template read as an exact function, at named sites (`ASM-SEGMENT`)

*Rule* · [Lean comment: `Assumption/SegmentExact.lean` L23-L67](../../Assumption/SegmentExact.lean#L23-L67)

At the sites a kernel names where the code matches a reviewed straight-line template, the model executes the whole template as one step that gives each output the exact value of the template's real function of its input. The template, its function and the approximations the reading ignores are part of the kernel's assumption.

Source:

- 

Direction: `not-conservative` (the mathematical result differs from hardware results as explained by its OPEN entry)

Lean definitions: [`Assumption.SegInstr`](../../Assumption/SegmentExact.lean#L70-L91), [`Assumption.SegInstr.bind`](../../Assumption/SegmentExact.lean#L93-L133), [`Assumption.SegInstr.writes`](../../Assumption/SegmentExact.lean#L135-L139), [`Assumption.SegShape`](../../Assumption/SegmentExact.lean#L141-L147) ([concept](#c-assumption-segshape)), [`Assumption.SegShape.writes`](../../Assumption/SegmentExact.lean#L149-L150), [`Assumption.SegTemplate`](../../Assumption/SegmentExact.lean#L152-L157) ([concept](#c-assumption-segtemplate)), [`Assumption.SegMatch`](../../Assumption/SegmentExact.lean#L159-L164), [`Assumption.matchBody`](../../Assumption/SegmentExact.lean#L166-L178), [`Assumption.SegTemplate.matchAt`](../../Assumption/SegmentExact.lean#L180-L184), [`Assumption.execSegment`](../../Assumption/SegmentExact.lean#L187-L205) ([concept](#c-assumption-execsegment)), [`Assumption.segmentExact`](../../Assumption/SegmentExact.lean#L207-L218)

<details>
<summary>Details for reviewers</summary>

- §9.7.3.3 (`add.f32x2`): ".rm mantissa LSB rounds toward negative infinity"
- §9.7.3.6 (`fma.f32x2`)
- §9.7.3.12 (max)
- §9.7.9.8 (shl)
- §9.7.1.1 (add)
- §9.7.10.3
- §9.7.10.4 (mov)
- CuTeDSL `cute/math` software `exp2` (the source of the template)

**Effect:** `segmentExact K name T sites why` reads the code at the selected sites as one local step, through the field `segmentRule`, which is consulted before the instruction rules (THREAD-LOCAL). At a thread state whose `pc` is in `sites`, between instructions, the instructions of kernel `K` from that `pc` must match one of the template's shapes exactly: every instruction unguarded and of the given form, and its registers a one-to-one assignment of the shape's slots (`matchBody`), so that no two slots share a register. The step then writes each output slot with `.float .f32 (T.fn x)` for the `f32` number `x` its input slot holds (THREAD-NUM). It sets the constant slots of a defining shape to the values Core's moves of those literals produce. It leaves the constant slots of a reusing shape as they are (which must hold those values, otherwise the step faults). It clears every other register the instructions write (a later read of one is `uninitialized`). It continues after the last instruction. At a site where the code does not match, or between the events of one instruction, the hook selects nothing and Core's rules apply. A path that enters the instructions after the first one is not affected: only the first `pc` selects the reading. The statement is generated from the template's text and the sites and lists every site it covers. The constructor sets no `wf` and no `ub`.

</details>

<a id="open-num"></a>
##### ideal arithmetic and hardware error (`OPEN-NUM`)

*Open issue* · [Lean comment: `Assumption/IdealReal.lean` L105-L113](../../Assumption/IdealReal.lean#L105-L113)

Under ASM-IDEAL and ASM-APPROX, a kernel's results are those of the exact real computation. How far the hardware's results can be from them is a separate numerical question that the model leaves open.

<details>
<summary>Details for reviewers</summary>

**Effect:** Results are the ideal real computation for the forms a kernel's assumptions name.

</details>

### Memory and synchronization

Loads outside the memory model, synchronization across the CTAs of a cluster, and the completion and order of `tcgen05` operations.

<a id="asm-nc"></a>
#### ld.global.nc at named sites reads launch content (`ASM-NC`)

*Rule* · [Lean comment: `Assumption/NcReadOnly.lean` L19-L48](../../Assumption/NcReadOnly.lean#L19-L48)

At the `ld.global.nc` sites a kernel names, the model trusts that the load returns the launch content of the bytes it reads, and a write of those bytes by any operation of the kernel is undefined behaviour. A kernel that reads such data with a plain `ld.global` does not need this assumption.

Source:

- 

Direction: `trust` (a trusted fact supplies a guarantee: a kernel's own, explicitly declared assumption, or a fact about the toolchain or the launch that holds for every kernel (EXT-ISA, EXT-LAUNCH))

Lean definitions: [`Assumption.ncReadOnly`](../../Assumption/NcReadOnly.lean#L51-L62)

<details>
<summary>Details for reviewers</summary>

- §8.1 (the memory model does not apply to ld.global.nc)
- §9.7.10.9 (ld.global.nc)
- CUDA `__ldg` / `const __restrict__` contract

**Effect:** The core has no rule for `ld.global.nc`. `ncReadOnly name sites why` sets three fields, each for exactly the sites (`pc`) in `sites`: * `ncLoads`: allows the load there, as a read outside the memory model (no `baseCausality`, no reads-from, no races). * `wf` (**removes executions**): an `nc` read at one of the sites returns the launch content of every byte whose launch content is known, using the same fixed `X.initial` choice for unspecified allocated bytes as ordinary reads. Executions where it returns anything else are not possible. * `ub` (only stricter): undefined if any byte an `nc` read at one of the sites reads is written by any issued ordinary or asynchronous operation of the execution, in any order. The statement is generated from the sites and lists every site it covers.

**Evidence:** Data that no thread writes during the kernel is read-only for the texture path.

</details>

<a id="asm-mbar-scope"></a>
#### CTA-scoped mbarrier synchronization reaches the cluster, at named sites (`ASM-MBAR-SCOPE`)

*Rule* · [Lean comment: `Assumption/ClusterScopeMbar.lean` L18-L53](../../Assumption/ClusterScopeMbar.lean#L18-L53)

At the mbarrier sites a kernel names, the model treats `.cta`-scoped release arrivals and acquire waits as `.cluster`-scoped, so an arrival on a peer CTA's mbarrier synchronizes with the threads of that CTA that wait on it. A kernel that writes `.release.cluster` and `.acquire.cluster` at these sites does not need this assumption.

Source:

- 

Direction: `trust` (a trusted fact supplies a guarantee: a kernel's own, explicitly declared assumption, or a fact about the toolchain or the launch that holds for every kernel (EXT-ISA, EXT-LAUNCH))

Lean definitions: [`Assumption.siteText`](../../Assumption/ClusterScopeMbar.lean#L56-L57), [`Assumption.clusterScopeMbarAt`](../../Assumption/ClusterScopeMbar.lean#L59-L65)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.16.16 (arrive): "If the .scope qualifier is not specified then it defaults to .cta"
- §9.7.15.16.16 (.scope): "the set of threads that directly observe the memory synchronizing
    effect"
- §9.7.15.16.19 (try_wait: same default)
- CuTeDSL `cute/arch/mbar.py` `mbarrier_arrive`

**Effect:** The ISA gives a `.cta`-scoped release arrival on a peer CTA's mbarrier no synchronizing effect for the waiting thread of that CTA, so the core (MEM-MBAR-SYNCHRONIZES) adds no `baseCausality` edge. Production code nevertheless hands off data this way: CUTLASS `ClusterBarrier::arrive` (`include/cutlass/arch/barrier.h`), DeepGEMM, ThunderKittens and Triton/Gluon remote arrivals use the default `.cta` scope. `clusterScopeMbarAt name sites why` sets one field, `clusterScopeMbar`, which adds synchronization: at exactly the sites (`pc`) in `sites`, `.cta`-scoped release arrivals and acquire waits, including the default `try_wait.parity`, are treated as `.cluster`-scoped (THREAD-RUN `widenMbarScope`). Relaxed operations and every other site are unchanged. Same-CTA pairs gain no new edge. Peer-CTA pairs on the same object in one cluster synchronize. The statement is generated from the sites and lists every site it covers.

**Evidence:** NVIDIA's CuTeDSL keeps `.cta` as the default for remote arrivals. Its source comment, which is not PTX text, states: “Remote CTA arrivals should be cluster-scoped for formal cross-CTA memory-model ordering. Keep the historical CTA default because existing retry-sync protocols rely only on the barrier count and current hardware/compiler behavior”. This is a statement about current hardware and compilers. The ISA does not guarantee it. A kernel that uses `.release.cluster` / `.acquire.cluster` for its peer-CTA handoffs does not need this assumption.

</details>

<a id="asm-tcld-dataflow"></a>
#### a `tcgen05.ld` whose registers are all consumed is complete (`ASM-TCLD-DATAFLOW`)

*Rule* · [Lean comment: `Assumption/TcLdDataflow.lean` L19-L59](../../Assumption/TcLdDataflow.lean#L19-L59)

At the `tcgen05.ld` sites a kernel names where a static check finds every loaded register read before the thread's next memory, barrier or `tcgen05` event, the model trusts the load to be complete, as if a `tcgen05.wait::ld` followed it. A kernel that issues `tcgen05.wait::ld` after these loads does not need this assumption.

Source:

- 

Direction: `trust` (a trusted fact supplies a guarantee: a kernel's own, explicitly declared assumption, or a fact about the toolchain or the launch that holds for every kernel (EXT-ISA, EXT-LAUNCH))

Lean definitions: [`Assumption.opndReg`](../../Assumption/TcLdDataflow.lean#L62-L65), [`Assumption.opndRegs`](../../Assumption/TcLdDataflow.lean#L67-L68), [`Assumption.addrOperands`](../../Assumption/TcLdDataflow.lean#L70-L76), [`Assumption.localReads`](../../Assumption/TcLdDataflow.lean#L78-L86), [`Assumption.localWrites`](../../Assumption/TcLdDataflow.lean#L88-L98), [`Assumption.isMove`](../../Assumption/TcLdDataflow.lean#L100-L108), [`Assumption.scanConsumed`](../../Assumption/TcLdDataflow.lean#L110-L134), [`Assumption.ldConsumedAt`](../../Assumption/TcLdDataflow.lean#L136-L144) ([concept](#c-assumption-ldconsumedat)), [`Assumption.tcLdDataflowAt`](../../Assumption/TcLdDataflow.lean#L146-L156)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.6.4.5: "For tcgen05.ld , an intra-thread ordering through true register dependency will
    be respected regardless of the presence or absence of other forms of synchronization. This
    form of register dependency does not imply any other form of ordering."
- §9.7.18.6.4.5: "To enforce such memory orderings and avoiding anti-dependency hazards around
    tcgen05.ld , tcgen05.wait::ld must be used."
- §9.7.18.8.5: "Instruction tcgen05.wait::ld causes the executing thread to block until all
    prior tcgen05.ld operations issued by the executing thread have completed."

**Effect:** `tcLdDataflowAt K name sites why` selects, at exactly the sites (`pc`) in `sites` where the static check `ldConsumedAt K` holds, the hook `tcLdWait` (THREAD-RUN). The load is followed at the same `pc` by an implicit `tcgen05.wait::ld`, which then orders it by Core's own rules. The check follows the code from the load on, while no branch and no guarded instruction occur, until every destination register (the loaded registers, and `redval` of `tcgen05.ld.red`) has been read by a local instruction other than a move (`mov`, `pack`, `unpack`, a `cvt` with a rule, `selp`, `slct`: a move passes the dependency on to its destinations), with no destination's value overwritten before then. It fails if the thread first reaches an instruction that is neither local nor a `tcgen05.ld`, so the implicit wait claims nothing beyond the next memory, barrier or `tcgen05` event of the thread. Placing the wait right after the load also claims completion before the intervening loads, which no rule uses (load completion matters only against writes and releases). A site where the check fails keeps Core's semantics. The constructor sets no `wf` and no `ub`. The statement is generated from the sites and lists every site it covers.

</details>

<a id="asm-commit-order"></a>
#### a commit's arrive-on precedes the next commit's, at named sites (`ASM-COMMIT-ORDER`)

*Rule* · [Lean comment: `Assumption/CommitOrder.lean` L19-L50](../../Assumption/CommitOrder.lean#L19-L50)

At the `tcgen05.commit` sites a kernel names, the model trusts that the commit's mbarrier arrive-on at each target CTA completes before the arrive-on of the issuing thread's next commit at that CTA starts. A kernel that waits for the mbarrier signal of each such commit does not need this assumption.

Source:

- 

Direction: `trust` (a trusted fact supplies a guarantee: a kernel's own, explicitly declared assumption, or a fact about the toolchain or the launch that holds for every kernel (EXT-ISA, EXT-LAUNCH))

Lean definitions: [`Assumption.commitPerformedAt`](../../Assumption/CommitOrder.lean#L53-L59) ([concept](#c-assumption-commitperformedat)), [`Assumption.commitOrderAt`](../../Assumption/CommitOrder.lean#L61-L70)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.12.1: "Makes the mbarrier object track the completion of all prior async-tcgen05
    operations initiated by the executing thread."
- ERR-SHARED-LIFETIME

**Effect:** `commitOrderAt name sites why` selects, at exactly the sites (`pc`) in `sites`, the hook `commitInOrder` (ASM-INTERFACE). The arrive-on of a commit at a selected site, at each target rank, completes before the arrive-on at the same rank of the issuing thread's next commit starts. The edge is part of the lifetime order only (ERR-SHARED-LIFETIME `LifetimeStep`): a proof that the next arrive-on completes before an exit then shows the same of this one. The same hardware order makes a selected commit's arrive-on performed at a rank whenever the next commit's arrive-on at that rank is. The assumption's `wf` is that constraint (`commitPerformedAt`), and it removes the executions in which the next commit's arrive-on is performed while the selected one's never is. A kernel whose proof of progress builds executions must show the constraint of the executions it builds. The constructor sets no `ub`. The statement is generated from the sites and lists every site it covers.

</details>

<a id="asm-setmaxnreg-sync"></a>
#### a request at a named site need not follow a warpgroup synchronization (`ASM-SETMAXNREG-SYNC`)

*Rule* · [Lean comment: `Assumption/SetMaxNRegSync.lean` L20-L49](../../Assumption/SetMaxNRegSync.lean#L20-L49)

At the `setmaxnreg` request sites a kernel names, the model trusts that the request is legal although no synchronization of its warpgroup orders the previous requests of the warpgroup before it. The direction and count of the request, the containment of its warpgroup in the CTA and the agreement of the requests with one ordinal are still checked. A kernel that synchronizes its warpgroup between two `setmaxnreg` requests does not need this assumption.

Source:

- 

Direction: `trust` (a trusted fact supplies a guarantee: a kernel's own, explicitly declared assumption, or a fact about the toolchain or the launch that holds for every kernel (EXT-ISA, EXT-LAUNCH))

Lean definitions: [`Assumption.setMaxNRegSyncAt`](../../Assumption/SetMaxNRegSync.lean#L52-L60)

<details>
<summary>Details for reviewers</summary>

- §9.7.21.5: "After executing a setmaxnreg instruction, all warps in the warpgroup must
    synchronize explicitly before executing subsequent setmaxnreg instructions."
- ERR-SETMAXNREG

**Effect:** `setMaxNRegSyncAt name sites why` selects, at exactly the sites (`pc`) in `sites`, the hook `regSyncExempt` (ASM-INTERFACE). The fourth clause of `SetMaxNReg.UnsafeAt` (a thread of the previous request of the warpgroup is not ordered before the request by `baseCausality`) does not apply to a request at a selected site. Direction, count, warpgroup and ordinal agreement are checked as in `SetMaxNReg.Unsafe`. The constructor sets no `wf` and no `ub` and adds no ordering; with no site selected `SetMaxNReg.UnsafeAt` is `SetMaxNReg.Unsafe` (`unsafeAt_noExempt`). The statement is generated from the sites and lists every site it covers.

</details>

### Addresses and control flow

An address computed from the hardware encoding, and the agreement of the lanes of a warp on a poll.

<a id="asm-peer-bit"></a>
#### clearing bit 24 of a shared window address names the even CTA of the pair (`ASM-PEER-BIT`)

*Rule* · [Lean comment: `Assumption/PairEven.lean` L19-L53](../../Assumption/PairEven.lean#L19-L53)

At the `and.b32 d, a, -16777217` sites a kernel names, the model reads the result as the `.shared::cluster` address of the same byte in the even CTA of the executing CTA's pair, which relies on the hardware encoding of cluster shared addresses. A kernel that computes this address with `mapa` does not need this assumption.

Source:

- 

Direction: `trust` (a trusted fact supplies a guarantee: a kernel's own, explicitly declared assumption, or a fact about the toolchain or the launch that holds for every kernel (EXT-ISA, EXT-LAUNCH))

Lean definitions: [`Assumption.peerBitMask`](../../Assumption/PairEven.lean#L56-L57), [`Assumption.execPairEven`](../../Assumption/PairEven.lean#L59-L67) ([concept](#c-assumption-execpaireven)), [`Assumption.pairEvenAt`](../../Assumption/PairEven.lean#L69-L83)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.28.5.3: "When .cta_group::2 is specified, the mbarrier object mbar can be in shared
    memory of either the same CTA as the shared memory destination dstMem or in its peer-CTA"
- §5.1.7: "The addresses in the .shared::cta window also fall within the .shared::cluster window."
- §9.7.10.26 (mapa)
- CUTLASS `Sm100MmaPeerBitMask` (0xFEFFFFFF, `include/cute/arch/copy_sm100_tma.hpp`)

**Effect:** `pairEvenAt K name sites why` reads one instruction as one local step, through the field `segmentRule` (THREAD-LOCAL). Core's `and.b32` would give the integer `a & 0xFEFFFFFF`. It selects exactly the sites (`pc`) in `sites` where kernel `K` has the unguarded instruction `and.b32 d, a, -16777217`. The register `a` must hold an integer `x` below `2 ^ 24` (a `.shared::cta` window address of the executing CTA) in a launch with an even cluster size, and `d` receives the `.shared::cluster` address of byte `x` of the even CTA of the executing CTA's pair (its peer of rank `rank / 2 * 2`, and for the even CTA itself its own byte). Otherwise the step faults (`badValue`). A site whose instruction has another form is not affected. The constructor sets no `wf` and no `ub`. The statement is generated from the sites and lists every site it covers.

</details>

<a id="asm-poll-agree"></a>
#### lanes of a warp spinning on one poll stay converged and agree (`ASM-POLL-AGREE`)

*Rule* · [Lean comment: `Assumption/PollAgree.lean` L18-L60](../../Assumption/PollAgree.lean#L18-L60)

At the guarded `bra.uni` sites a kernel names that branch on the result of an `mbarrier.try_wait`, the model trusts that the lanes of a warp polling one mbarrier get the same result, and it does not compare their branches. A kernel that branches on the poll with a plain `bra`, or votes the result across the warp before the `bra.uni`, does not need this assumption.

Source:

- 

Direction: `trust` (a trusted fact supplies a guarantee: a kernel's own, explicitly declared assumption, or a fact about the toolchain or the launch that holds for every kernel (EXT-ISA, EXT-LAUNCH))

Lean definitions: [`Assumption.pollAgreeAt`](../../Assumption/PollAgree.lean#L63-L72)

<details>
<summary>Details for reviewers</summary>

- §9.7.14.3: "bra.uni is guaranteed to be non-divergent, i.e. all active threads in a warp that
    are currently executing this instruction have identical values for the guard predicate and
    branch target"
- §9.7.15.16.19: "Suspended thread resumes execution when the specified phase completes OR before
    the phase completes following a system-dependent time limit"
- §3.2: "A schedule optimizer determines how to group active threads from the same warp together
    into SIMT units"
- ERR-NONUNIFORM-GUARD

**Effect:** `pollAgreeAt name sites why` selects, at exactly the sites (`pc`) in `sites`, the hook `uniPoll` (ASM-INTERFACE). Two executions there are not compared when the instruction at the site is a `bra.uni` guarded by the predicate that the `mbarrier.try_wait` right before it writes and both lanes' records right before are that poll's events on one mbarrier, whatever their parities. `PollAgreeExempt` checks the instruction form: a selected site that holds any other instruction, or a `bra.uni` that does not follow such a poll, is not exempted. Polls of different objects are still compared. If lanes can execute the branch together with different poll results, that is undefined behaviour that the theorem does not report. The constructor adds no constraint on executions and sets no `wf` and no `ub`. The statement is generated from the sites and lists every site it covers.

</details>
