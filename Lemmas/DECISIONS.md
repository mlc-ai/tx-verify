<!-- SPDX-License-Identifier: Apache-2.0 -->

# Proof library decisions

Decisions about the generic proof library (`Lemmas/`, `Tactics/`, `Tools/`, `tests/`) taken while
building the role-machine abstraction: role fragments, glue, ghost ledger, `followed`, sources and
protocol declarations. Each entry states the decision and its reason.

## Fragments, glue, ledger and `followed`

- **Per-state obligations.** `Fragment.Ok F` is `∀ d, F.OkAt d`, and `OkAt` collects the five
  obligations of one state (step, shape, stop condition, `ref_next`, `ref_safe`). A kernel proves
  them one site family at a time, and the first fragment of a glue owes them only at its states
  that are not exits (`Fragment.glue_ok`). A structure with five fields quantified over all states
  could not express the second point.
- **The machine's invariant is a hypothesis of every obligation.** `ref_next`, `ref_safe` and
  `stop_iff` take `code.inv d`, as `Code.Shape` does: the invariant holds at every followed state,
  so the hypothesis costs nothing at the use sites and lets a machine keep facts there.
- **Return kinds read the event.** `RetKind.accepts k e` constrains the value `recv e` that the
  event returns: the rebuilt bytes of a read, the received value of a shuffle. A vector load whose
  bytes split over several registers has no single returned value; its site uses `.any` until a
  kernel needs more.
- **`followed` takes the first state's `Ref` per thread.** `Frame.followed` concludes for one
  thread from that thread's `J g (C g).init`, so a reference invariant may be false for threads
  that are not launched. `tracked_of_followed` asks it for launched threads only.
- **Bad events stay generic.** `Frame.StepGood` is "does not stop, successor satisfies `J`"; the
  stronger "does not die except after an event that ends the thread" is a field of
  `Fragment.OkAt` (`ref_next`) and is used only by the fragment corollaries
  (`Frame.thread_noUb`). The never-stops theorem therefore applies to machines that are not
  fragments.
- **The source obligation after `noBad`.** Once no event is bad, the source obligation holds at
  every event fired from a `Ref` state, so the fragment corollaries are proved per thread
  (`thread_followed`, `thread_noUb`) and lifted (`followed_of_sources`, `noUb_of_sources`).
- **`Code.counted`, `Code.glue` and `Fragment.glue` are reducible.** Their state types are a
  product and a sum; reducibility lets `simp` and `rfl` see `some none` at both types as equal.
- **`Frame.count_eq` lives in `Lemmas/Kernel/Counted.lean`**, next to `Frame.stateAt`; the
  construction itself is in `Lemmas/Flow/Counted.lean`, which does not import the frame.
- **G6.** "A maximal execution of a safe kernel is complete" is each kernel's progress goal, not a
  library lemma. The library gives `maximal_consistent`, `Complete.exit_last`, `exit_state` and
  `exit_ev`; the poll extension already exists (`Frame.poll_consistent`).
- **Test bed for L1.** `AddOne` is restated on `Fragment` (`frag`, `frag_ok`); its undefined
  behaviour field is proved by `Frame.thread_noUb` instead of a first-stop analysis. The file
  shrank by three lines.
- **A machine may die after undefined behaviour.** `ref_next` asks `next d e = none → Ends e`
  (an exit or undefined behaviour), not `e.kind = .exit`: a machine whose transition gives `none`
  for every event other than its site's expected kind (the usual `| _ => none`) would otherwise owe
  a false statement at the undefined-behaviour alternative of a shape. `ref_safe` excludes that
  alternative under `Ref`, so `thread_noUb` still concludes that a dead machine died at an exit.

## Shapes, stops and `ref_next` by tactic (L2)

- **`site_shape` dispatches on the instruction's class** and applies one inversion lemma per
  class (`shape_shfl`, `shape_vote`, `shape_ld`, `shape_wait`, `shape_arrive`,
  `shape_tensorStore`, `shape_bulkCommit`, `shape_bulkWait`, `shape_setMaxReg`, `shape_exit`).
  Each concludes `P e` from `P` of the event it names, so the role's shape table is reached by
  unification and `shape_close` (witnesses and alternatives) instead of per-site text.
- **Side goals in two passes.** Operand reads, the site's sub-step, assumption checks and the
  role's address goals are closed first; only then are the shape goals closed. A shape goal
  closed first would fix the location metavariable of a read by unification with the table's
  term instead of the code's.
- **Operand reads use the value table directly**: `regs_of_factsFrom` rewrites a register to its
  table entry under the hypothesis `r ∈ live`, discharged by `lit_mem`. Library names inside the
  tactic macros are fully qualified (`PTX.effAddr`): an unqualified `effAddr` resolved to the
  lemma `PTX.Proof.ControlAgree.effAddr` in a kernel that opens `PTX.Proof`.
- **No new keyword that is a common identifier.** The value lemmas of `site_shape` are given after
  `reg_vals`, and `tmpl_unfold h f` takes no `to`: every atom of a syntax rule becomes a token,
  and a first version with `vals` broke every file that names a variable `vals`.
- **The template is unfolded to its class's template function** (`tmpl_unfold`) with
  `withCanUnfoldPred`, so the unifier never has to unfold `eventTmpl` against a lemma whose
  template arguments are metavariables.
- The Epilogue's `Shape.lean` keeps its statement and `Ev`; it went from 432 lines and 96 s (159 s
  measured on the loaded host before the change) to 228 lines and about 9 s including `ret` and
  `stop_iff`.

## Sources (L3)

- **Launch input**: the per-byte fact comes from each kernel's own read-only assumption (its
  sites and regions are kernel data, so there is no library constructor); the library gives the
  step from bytes to the returned value (`read_value_of_bytes`).
- **Protected read**: `read_byte_of_source` (promoted from Inkling `FootSrc`) is pure model
  reasoning. Risk R4, checked on paper: the classification of the actual source of a read needs
  the writer's footprint. For a writer ordered before the read (base causality), `noBad` gives
  its thread followed up to the write, so its shape table names the bytes. For a writer that is
  concurrent with the read, the footprint is available from the shapes alone only when the
  writer's machine cannot stop before the write; a machine that stops on a returned value's kind
  (a word read seeing a typed float's bytes) cannot exclude that without race freedom, which is
  what is being proved. So R4 materializes for kind stops on reads of shared memory written by
  other roles. The way out the plan names stands: stratify, first proving that such reads return
  words (their writers' footprints by an order that contains rf only for input bytes, as
  Inkling's `InputRfAcyclic` does), then the content. Inkling's base word and FlashMLA's
  coordinates are reads of this kind; the library lemma takes the classification as a premise
  and leaves the stratification to the kernel.
- **Warp collective**: the generic content of the Epilogue's `votes_le`/`shfls_le` is `coll_le`
  (the order of two collective kinds along a lane, from the kernel's position fact), and of its
  double induction is `coll_induction`. The source lanes' sameness of site (the Epilogue's
  `shfl_same`, `vote_same`) and the exit exclusion stay with the kernel, as they read its `Ref`.
  The Epilogue's `Warp.lean` cannot reach the plan's 250 lines with these alone: its private
  `stateAt` (an offset of five events) blocks `Frame.followed`, and the per-site `expect`
  (120 lines) and `vote_bits` (115 lines) read `Fits`; both shrink only once lane T1 moves the
  role onto glue (T1a) and states `Ref` per site.

## Protocol declarations (L4)

- `RingDecl` is a sum of the pair declaration (`PairTmaRing.Decl`, unchanged, so GEMM and FA4
  are not touched) and a single-CTA declaration (`SingleTmaRing.Decl`): one empty barrier shared
  by an arrival thread and a copy thread, `n` copies of `bytes` per use, a preload `δ ≤ 1` per
  slot (the preloading arrival and copies are events of other threads, unguarded by the
  producers' polls), the parity offset `1 - δ` of the producers' polls, and the scope of the
  polls' acquire as a parameter. `SingleTmaRing.Hyp` is Inkling's `Kv.Hyp` with the eight copies,
  their bytes and the CTA scope made parameters, so `Kv.Hyp` is its instance at `n = 8`,
  `bytes = 8192`, `sc = .cta`.
- **Budgets over ghost counters**: the declarations' budget fields are inequalities between
  counts of a thread's events; `Frame.budget_of_counts` turns a budget that the reference
  invariant states over ghost counts (`Code.counted`) into the trace inequality.
- Unit hand-off (`MbarRing.Unit.Gate`) and named-barrier (`NamedBar.Sources`) records are not
  restated as declarations: their remaining hypotheses are dependency paths and barrier
  membership, not counts, so a declaration would only rename the existing structures. Their
  count hypotheses are met by `budget_of_counts`.

## Generator and static checks (L5)

- `Tools/machine_gen.py` generates value-table entries for the registers a declared straight-line
  stretch assigns once, in the vocabulary `Lemmas/Flow/Arith32.lean`, from the PTX only;
  `tests/test_machine_gen.py` checks every declaration under `Tests/Gen/` and `Kernels/*/Gen/`
  for freshness. The Epilogue test (`Tests/Gen/epilogue_up.json`) regenerates the first scan
  round's `up` partial sums and tile count, and `Tests/Gen/EpilogueUpCheck.lean` shows by `rfl`
  that they are the hand table's entries. The whole Epilogue table is not regenerated: its
  64-bit address forms (`addrU`, `addrS`) and its loop-state registers are declared terms, and
  replacing `Machine.lean`'s table is lane T1's file.
- Static checks (`closedFrom`, `sitesFrom`, `classFreeFrom`, with `closed_get`,
  `classFree_get`) are `Bool` folds over the decoded code (`Lemmas/Kernel/CodeCheck.lean`). The
  closure soundness theorem over all event templates is not written (risk R9): role membership
  of a thread's events comes from the glued machine.

## Promotions (L6)

- From tml-fa4 Proof2 (branch `p4b-epilogue-wire`): `Code.fired_tmpl` (`Proof2/Lib/FiredTmpl.lean`)
  is in `Lemmas/Flow/Ledger.lean` next to `Code.Shape.fired`; `Code.fired_pc`,
  `fires_wait_exact` and `fires_arrive_exact` were already there. The branch should delete its
  `Proof2/Lib/FiredTmpl.lean` when it takes this one (the names would clash).
- From the tml-fa4 MMA warp (branch `tmlfa4-mma-proof2`): the register-value inversion lemmas of
  `Proof2/Lib/Shape.lean` are `Lemmas/Flow/Step/ShapeRegs.lean`, and the continuations of
  `Proof2/Lib/Steps.lean` are `Lemmas/Flow/IssueNext.lean`; `advances` now tries them, and
  `issue_step` is in `Step/SiteCases.lean`. The branch should delete both `Proof2/Lib` files when
  it takes these. Not done: `seg_sym` passing a guarded event instruction whose guard the start
  facts give as false (recorded as a gap by that lane).
- `seg_sym`'s `decideBool` (reported by lane B1 through `p4b-epilogue-wire`): a successful
  decision now keeps its state, so the auxiliary declarations of its proof survive; a decision
  whose proof contains an elaboration error placeholder counts as no decision (the walk then
  splits on the condition), so an error no longer passes silently.

## Stratified `followed` (L3b)

- R4 materialized (see "Sources"), so the library proves `followed` in stages
  (`Lemmas/Kernel/FollowedStages.lean`, `followed_stages`): stage `i` has its own invariant and
  its own order with an induction principle, and its step may use every earlier stage's
  invariant at every followed state of every thread. Kernels state their stages (typically:
  kinds of the reads of a class, along an order with the input reads-from edges; then contents,
  along base causality) and get every stage's invariant at every state (`followed_stages_all`),
  instead of re-deriving the composition. `followedAt_and` joins two stages of one thread.
- Not tested on the output warp: on `p4b-epilogue-wire` (head `1cf120e2a`) the role still has its
  private `stateAt` with the five-event offset, which `Frame.followed` does not cover; the test
  waits for lane T1's glue (T1a). The output warp needs one stage only (its reads are launch
  inputs and its other values are collectives), so the stratification is for Inkling's base word
  and FlashMLA's coordinates.

## `seg_sym` and guarded event instructions

- The walk passes a guarded event instruction whose guard the walked state gives as false (a
  local skip in Core's rule), and cuts before one whose guard is no literal, deciding it as a
  branch's predicate (a hypothesis in context, else by cases), then passes it on the false side.
  Requested by the tml-fa4 MMA lane and by the Inkling lane (whose `pred_facts`/`pred_split`
  work around it); not exercised by a kernel on this branch, so those lanes check it on theirs.

## Unit hand-off and named-barrier declarations

- Not added. Inkling's uses (`Protocol/SOHandoff.lean`, 206 lines, through `MbarRing.Unit.Gate`
  and `UnitHandoff`; `Protocol/BarOne.lean`, 81 lines, through `NamedBar.Sources`) and FlashMLA's
  (`Progress/NamedBarrier.lean`, 210 lines, through `NamedBar.Sources`; `Protocol/IndexRing.lean`
  has its own ring `Sources`) instantiate the library structures in a few lines each; the rest of
  those files is kernel reasoning (which lane polls which phase, the dependency path of each
  gate). A declaration over the same fields would rename the structures without removing lines.
  The count hypotheses inside them are met by `Frame.budget_of_counts` once the roles keep ghost
  counts.

## Promotions (second round)

- From `tmlfa4-mma-proof2`: `Code.step_alloc`, `Code.step_allocWr` (the two events of
  `tcgen05.alloc` on lane 0) as `Lemmas/Flow/Step/Alloc.lean`. Its `Proof2/Lib/Steps.lean` also
  has the continuations and `issue_step`, promoted in the first round.
- From `f1-ink-thread`: `Proof/Lib/StopReason.lean` (`Code.StopsFor`, `next_ne_none`, the
  `stops_*` lemmas, `stops_site`, `stops_cases`) as `Lemmas/Flow/Step/StopReason.lean`, and
  `Proof/Lib/SiteIte.lean` (`ite_cases`, `seg_pre`, the `lands_auto` rule for successors that are
  an `if`) as `Lemmas/Flow/Step/SiteIte.lean`. `SiteIte` stays a separate module, so the extended
  `lands_auto` applies only where it is imported, as on the branch.
- `tmlfa4-corr-proof2` carries copies of the MMA lane's `Proof2/Lib` files; `lane-F` has no
  `Lib` folder yet. Each branch deletes its `Lib` copies when it takes `lane-L`.

## Floating-point steps in `seg_sym` (rule steps)

- **One mechanism for every rule an assumption gives a local instruction.** When the walk meets a
  floating instruction or a conversion that Core's rule does not evaluate on the walked values
  (exact reals, `.float .f32 x`) and some assumption of the kernel's list selects it, the walk cuts
  there and takes the step as a piece `pc → pc + 1` (`Seg.rule1`, `Lemmas/Flow/Step/RuleStep.lean`).
  The piece's proof finds the first assumption of the list whose rule is not `none` at that state
  (the ones before it are shown to give none by evaluation, `execLocalRule_cons_none`), unfolds
  its rule up to the operations on extended reals, and evaluates it by `simp` with the operands'
  facts. The same code covers the ideal-arithmetic rule (`mul.rn.f32x2`, `setp` against a
  constant, `fma`, `max`, …), the approximate-as-exact rule (`rcp.approx`, `ex2.approx`) and a
  kernel's own rule (the tml-fa4 `lg2`), with no rule written per instruction or per kernel. Core's
  step is still used wherever it evaluates, so segments that `seg_sym` proved before take the same
  path.
- **Normal forms.** Reals stay the operations the code performs (`x * s`, `x⁻¹` for `1 / x`);
  a comparison stays `erealCompare cmp ↑x ↑y`; a 32-bit constant is its rational value as a real
  numeral (`readEReal_lit` decodes the pattern and checks `f32Value n = some q` by evaluation).
  Tables state values in these forms.
- **Conditions of a rule** (a reciprocal of zero faults; `lg2` declines on a nonpositive input)
  are decided by the hypotheses about reals in context, restated as comparisons of reals
  (`realFacts`: a case split's `erealCompare … = true` becomes `x ≠ 0`). A condition no hypothesis
  decides stops `seg_sym` with the condition named; it is not split, because the declining branch
  falls to Core's approximate tables, which no table can state. For the tml-fa4 LSE this means the
  machine needs the sign of the row sum in context (a successor `if`, or a state field).
- **`selp` on values that are not words** (a floating `selp` between a payload and a constant) is a
  case split on the predicate, the walk continuing on each side, instead of an `if` value: a rule
  step cannot read a value that is an `if`.
- **`sym_close`** unfolds a table definition whose body is an `if` (`fRecip`) to decide it, and
  uses the restated real facts (`restate` runs `realFacts` first).
- Measured on the tml-fa4 correction warps (pending step files of `wt-corr2`, on lane-L): the
  rescale chunk's landing (8 packed multiplications) 36 s for the file, about 0.33 s per rule step;
  the scale comparison 7 s; the reciprocal with its `selp` split 18 s; a final chunk 13 s. The
  pending `StepsRescale`/`StepsFinalData` still fail for a reason in the kernel's tactics:
  `corr_rld`/`corr_fld` use named holes `?st ?c` / `?st ?j`, which `site_cases` shares between the
  site cases, so every case after the first gets the first case's site (errors "event instruction
  at 8065 before 8039", "synthetic hole has already been defined").

## Loops in `seg_sym` walks (risk R2)

- Cause of the tml-fa4 correction scan's `total` site not finishing: the scheduler loop's exit
  test `ctaid + 1 ≤ ctaid` (signed 32-bit, after the last group) was not decided, so the walk took
  the back edge on one side of the split and unrolled the loop with growing terms (9, 11, 13,
  15 s per round). The output warp decides the same test with its `sym_decide` rule
  `cta_succ_le`, stated for its CTA term `ctaW`; the correction warps read `%ctaid.x` themselves,
  under the launch with explicit parameters, so their CTA term is a different expression and the
  rule did not apply. It is not the size of the term: decisions by hypotheses (`cheapDefEq`, 1.1 s
  over 110 calls) and `sym_decide` attempts (0.2 s) were measured small.
- Fix in the library: the walk stops with an error naming the predicate when it comes back to a
  branch on an undecided predicate a second time (or to any branch a 64th time), instead of
  unrolling. `explicitParams_ctaidOf` and `explicitParams_block` (`Lemmas/Flow/LaunchParams.lean`)
  restate the CTA index under the explicit-parameter launch as `L`'s, for the kernel's decision
  lemma. With a `sym_decide` rule for the test the `total` site of the first pass checks in 74 s
  (six successor leaves); without one it now fails in about a minute with the predicate.
- Not done: replacing `explicitParams L ps` by `L` in the walk's facts. The two CTA terms are not
  equal by `rfl` at the elaborator (only after `unfold explicitParams`), so a table on `L` would
  need a proof per value.

## Single-CTA ring results (`Lemmas/Protocol/SingleTmaRing/`)

- The Inkling KV ring's results (`RingKvItems`, `RingKvAttr`, `RingKvOrder`, `RingKvPoll`,
  `KvFacts`, `KvFaults`) are in the library over `SingleTmaRing.Slot` and `Hyp`, as `Items`,
  `Attribution`, `Order`, `Poll`, `RingFacts` and `Faults`, with the eight copies, their 8192 bytes,
  the 65536-byte arrival and the CTA scope of the polls made the slot's `n`, `bytes`, `tx` and the
  scope `sc` of `Hyp`. The kinds of items are `Kind S = Fin (S.n + 1)`; the preloading copy of kind
  `k ≠ 0` is `pCp ⟨k - 1, _⟩`.
- **`Slot.Fits`** (`0 < n`, `0 < bytes`, `2 · tx ≤ MBarrier.limit`) is a premise of the results
  that need it, not a field of `Hyp`: a phase's transaction count fixes its number of copies only
  when a copy has a byte (`fullF_card`), the copy thread owns a kind only when there is a copy
  (`ring`), and the operand and counter range checks of `Faults` hold for any slot whose counter
  stays within one use either side of zero. The Inkling instance (`n = 8`, `bytes = 8192`) meets it
  by evaluation. Keeping it out of `Hyp` leaves `Decl.hyp` and lane I's `Kv.Hyp` instance as they
  are.
- Not moved: the KV-specific files (`RingKvFoot`, `RingKvMma`, `RingKvPreload`, `KvRecords`,
  `KvInit`, `KvAll`), which read the loader's and the MMA warp's code. Lane I deletes the six
  ported files and imports these instead (task I3).

## Promotions (third round)

- From `tmlfa4-corr-proof2` (`Proof2/Lib/TcSteps.lean`): `fires_barArrive_next`,
  `fires_tcWaitSt_next`, `fires_tcSt_next`, `holds_setRegs_live`, `Code.step_issueAt`,
  `Code.step_tcLd`, `Code.step_tcLdLoad`, `Code.step_tcLdWait`, unchanged, as
  `Lemmas/Flow/Step/TcSteps.lean`. `advances` tries `bar.arrive` and `tcgen05.wait::st` where the
  module is imported (two `macro_rules`; a new module, so no other file is rebuilt). `site_step` has
  no class for `tcgen05.ld`: the role applies `step_tcLd` or the two sub-step lemmas in an override,
  as the correction warps do; a class would need the role's successor as a function of the loaded
  values, which `site_step` cannot guess.
- From `lane-F` (`Proof/Lib/Ledger.lean`): `Code.after_none_eq`, `Code.counted_after_map`,
  `Code.trace_counted`, `Code.ledger`, `ringUses` and its lemmas, appended to
  `Lemmas/Flow/Counted.lean`; (`Proof/Lib/UbStopAt.lean`): `Code.ub_stopped_at`, appended to
  `Lemmas/Flow/UbStop.lean`.
- `tmlfa4-corr-proof2` and `lane-F` delete their `Lib` copies when they take `lane-L` (the names
  clash).

## `site_shape`: more classes and a hook

- `site_shape` dispatches, besides its first classes, on `bar.sync` (immediate id), `bar.sync id,
  n`, `bar.warp.sync -1`, `elect.sync`, `mbarrier.init`, proxy fences, `tcgen05.commit`, tensor
  copies and stores, with the inversion lemmas of `Lemmas/Flow/Step/ShapeClasses.lean`, written
  from the library's `fires_*` facts. The Inkling lemmas named for promotion
  (`fires_elect_full`, `fires_warpBar_full`, `fires_barSync_imm`/`fires_barSync1`,
  `fires_mbInit_at`) are special cases: `shape_elect` takes any mask, `shape_barSync` any
  immediate id.
- **Extensible by a hook, not by editing the dispatch.** `shape_inv hf` is a tactic syntax whose
  rules kernels and library modules add with `macro_rules` (`refine my_shape hf ?_ …`).
  `site_shape` tries the class's own lemma and then the hook, and closes the side goals and the
  shape goals of either in the same way. A lemma with the wrong operand form (a `tcgen05.mma`,
  a multicast copy) thus falls through to the kernel's rule instead of failing.
- Lemmas whose instructions may fault take the undefined-behaviour alternative (`hub`), from
  `shape_cont`: an instruction other than an exit that does not continue fired undefined
  behaviour (`fires_none_ends`, `fires_exit_op`).
- `tcgen05.mma` has no lemma: its event names the operand descriptors the issue reads, which a
  kernel states in its own terms; a kernel adds it through the hook.
- Not exercised on this branch: the Epilogue's `Shape.lean` checks unchanged (9 s); the new
  classes wait for Inkling I2 and the tml-fa4 MMA lane.

## Vector loads in `site_cases` (FlashMLA `Wg1Tma` step 4)

- `step_ldv_mid` and `step_ldv_last` (`Lemmas/Flow/Step/LoadVec.lean`) are the load counterparts
  of `step_vec_mid`/`step_vec_last`, for a machine that records the values it reads: an element
  before the last moves to a state one sub-step later whose accumulator has the value read; the
  last writes every destination with the accumulated values and continues with facts the role
  states (`F' v`, established from the site's facts by `hF`, for instance with
  `holds_setRegs_live`). Bytes that do not rebuild fault the thread, so the machine owes `none`
  there, as for `step_load`. They are not wired into `site_step`'s automatic dispatch: the
  successor's accumulator and the last element's facts are the role's design, so a role applies
  them in an override. A new module, so no file is rebuilt.
- `Code.ub_stopped_at` (lane-F item) is promoted with the ledger lemmas (third round above).

## FlashMLA F3 requests (D-F3-SCOPE, not done)

- **Register frame.** For the registers a local segment does not read, the frame exists:
  `run_footprint`/`seg_footprint` (`Lemmas/Flow/Footprint.lean`) evaluate a segment on the facts
  of the registers it reads and carry every other fact (`holds_transfer`), whatever those
  registers hold. For the registers it reads no generic lemma can exist: Core's integer, move and
  conversion rules depend on the value's kind (a pointer, a payload, a pair), so a machine that
  records arbitrary values needs, per segment, either the kinds in its `Ref` or the stratified
  `followed_stages` (first: reads of an area return words; then their contents), which is in the
  library (L3b). Nothing new is needed for the stratification; its use is the kernel's.
- **Non-finite inputs as a code rule.** Planned shape: a `DeadFrom` piece for a floating step
  whose selected rule declines on the operands under a hypothesis in context (a NaN half, say)
  and whose Core rule faults (`rnd = none` has no rule): `rule_step` already falls through a
  declining rule to the next assumption; when the list is exhausted, Core's step evaluated to
  `.error f` gives `DeadFrom` by `Machine.dead_of_ub`. It needs the operand's finiteness as a
  decidable case (a word's class), which `seg_sym`'s walk would split on like a branch predicate.
  Not written in this round.

## Requests of the tml-fa4 loader (fourth round)

- **The sink destination of an unpack.** `mov.b64 {_, %r}, %rd` writes through `setDst` with
  `none` for the sink. `seg_fp`'s register frame now reduces `setDst` (with `setReg`), so a
  segment through such an unpack keeps the facts of the registers it does not write. `seg_sym`'s
  walk evaluates `execLocal` and needed no change. Checked on the loader's used-K read (`uk`):
  the piece from pc 481 to 500 through the unpack at pc 493 now closes.
- **Local loops in `seg_sym`.** The walk counts the local steps it takes, every round of a local
  loop included, and closes each piece with that length (`refine ⟨n, ?_⟩`) instead of
  `seg_auto`'s search, which took the four shortest path lengths and so missed a loop that runs
  more rounds than that. A loop whose predicate the walked state decides (the loader's page-size
  shift loop at pc 398–401, three rounds for page size 16) is now walked like straight code; one
  whose predicate stays symbolic is still cut and decided at the branch, as before. The loader's
  `seg_cut` (`Loader/Base.lean`) is `Seg.comp_ex` with the end table's facts at the cut, and is
  no longer needed for this loop.
- **Divisions in the walk.** A `div` whose operands the walked state gives as literals is
  evaluated like any local step; only one that does not evaluate is cut and decided. The cut's
  lemmas (`Seg.div_ok`, `DeadFrom.div`) now take any integer kind and width (they were signed
  32-bit only, and the walk used them for an unsigned division too).
- **Decided predicates in `seg_fp`.** After a case split on a predicate, the piece's start facts
  hold its literal value in front of its symbolic one, and the end facts still name the symbolic
  one. `seg_fp` closes such a fact with the hypothesis of the split (`pred_hyp`) before the
  role's value tactic; that tactic's `rfl` first tried to evaluate the symbolic comparison, which
  on the loader's used-K read did not finish in four minutes.
- Checked on the loader's used-K read (`uk`): the walk passes the shift loop (a first piece of 51
  steps), the unsigned division at pc 411, seven `selp` splits and the unpack at pc 493, and
  reaches the end of the segment. The restatement of the end facts then fails on the loader's
  table: its page index `pgIdx (row0 …)` is not equal by evaluation to the code's
  multiply-high form as the walk computes it (`sym_close: the values differ`). That is the
  table's form, for the loader lane.
- **Loads in `site_step`: extension and vector elements.** `site_step`'s load class tries, after
  `step_load` and `step_load_sel`, three new combinators (`Step/LoadVec.lean`): `step_load_ext`, a
  scalar load located by `accessLoc` (`.local`, `locSpace? = none`) whose value Core extends
  (`ld.local.s32` into a 64-bit register): the machine's successor reads the rebuilt value, the
  register receives `extendLoaded` of it, and a value with no bit pattern faults (the machine owes
  `some none` there, `hext`); `step_ldv_mid_sel` and `step_ldv_last_sel`, the elements of a vector
  load with the successor a function of the value read, which may stop on it (the loader's
  `word32`). The last element's facts are `vecFacts` (each destination's value, then the other
  facts), written out by `vec_facts_norm` for `seg_fp`. `fires_accessLoad` is the continuation of
  a load located by `accessLoc`; `extendLoaded_bits` evaluates the extension of a word.
- **Why these are wired in now** (the third round left `step_ldv_mid`/`_last` to overrides): an
  override cannot name the site's instruction before `site_cases` has split the site, because the
  combinator's `gd`/`a` are fixed by the code lookup; the softmax lane's draft failed for that
  reason (`cases b <;> fin_cases c <;> code_lookup` inside one goal cannot assign one metavariable
  per site). In `site_step` the site is literal, so the lookup fixes them.
- Checked on the loader: the first K packet's address load (`lw .prime false 0`, both elements:
  the middle one moves to sub-step 1 with the word in the accumulator, the last one lands on the
  first shuffle's table) checks with no override, 7 s for both and the pointer round's page load
  below. The pointer round's page load (`ptP .prime false 0`, `ld.local.s32`) reaches its segment
  with the extended value `MemExt.extendBits (.sign 64) 32 x` as the register's fact; the segment
  then needs the pointer loop's table, which the loader has not written yet.
- **`cp.async` in `advances`.** The continuations of a `cp.async` copy,
  `cp.async.commit_group` and `cp.async.mbarrier.arrive` (`fires_cpAsync_next`,
  `fires_cpAsyncCommit_next`, `fires_cpAsyncArrive_next`, from the loader's
  `Proof2/Lib/CpAsyncSteps.lean`, unchanged) are in `Lemmas/Flow/IssueNext.lean`, and `advances`
  tries them. The loader deletes `Proof2/Lib/CpAsyncSteps.lean` and its import when it takes this
  branch (the names clash), and its packet files need no `load_issue` override: the first V
  packet's 64 states (32 copies) check with plain `load_sites` (221 s on the loaded host).
- **`site_shape` for the loader's classes.** New inversion lemmas (`Step/ShapeClasses.lean`):
  `shape_cpAsync` (the copy event of the non-bulk group, from the two addresses and the source
  size, or undefined behaviour), `shape_cpAsyncCommit`, `shape_cpAsyncArrive` (a `.shared`
  address), `shape_accessLd` and `shape_accessSt` (a load or store located by `accessLoc`, a
  `.local` one: a read or write of its footprint `accessAcc`, or undefined behaviour). The
  dispatch picks them by the instruction; `shape_ld` stays for directly located loads.
- `site_acc [vals]` closes the side goals these need from the site's facts: `accessAcc`/
  `accessLoc`, `mbarLoc`, a shared effective address and a `cp.async` source size, with
  closed Boolean conditions decided by evaluation. What it leaves is the role's: the alignment of
  a launch base (`L.localBase`, `L.sharedBase`) and a bound on a symbolic source size.
- Expect-tx arrivals (`mbarrier.arrive.expect_tx` with a state destination), tensor copies with a
  cache hint, `setmaxnreg` and commits were covered already (`shape_arrive`, `shape_cpTensor`,
  `shape_setMaxReg`); checked on the loader's `ta 0`, `tc 0 0`, `setmax`, `commit` states.
- **Two fixes.** `shape_store` took the kind before the `Fires` hypothesis, so
  `apply shape_store hf` never applied and every store fell through to the hook: the hypothesis is
  now first, as in the other lemmas (no use outside the library). `site_shape_step` now closes
  only the propositional goals with the shape tactic; a goal for a value of a lemma's implicit
  argument (a location, a size) is assigned by them, and closing it on its own failed with
  "simp made no progress".
- Checked on the loader with a test table (`Ev2`, existential shapes): `setmax`, `commit`,
  `tc 0 0` close completely; `cp`, `arrive`, `ta`, `pgSt`, `ptP`, `lw` reach exactly the role's
  facts named above (the shared base's value at `cp` is `ent 1083` in today's table).
- **Promotions (fourth round).** From `p4b-epilogue-wire`: `Code.glue_fired`, `glue_next_inr`
  (`Lemmas/Flow/Glue.lean`), `Code.counted_fired` (`Lemmas/Flow/Counted.lean`),
  `Frame.followedOn`, `followedAtOn_of_lex` (`Lemmas/Kernel/Followed.lean`), and the word lemmas
  of `Proof2/Lib/Word.lean` as `Lemmas/Flow/Arith32Word.lean` in namespace `PTX.Flow.Arith32` (a
  module of its own: it needs `Flow.divQ` from `Step/SegSym.lean`, which `Arith32` does not
  import). From `tmlfa4-mma-proof2`: `elect_leader`, `elect_winner` as
  `Lemmas/Kernel/ElectSource.lean`. All unchanged in statement. The branches delete their
  `Proof2/Lib` copies when they take lane-L (the names clash); `p4b-epilogue-wire` imports
  `Lemmas.Flow.Arith32Word` where it imported `Proof2.Lib.Word`.
- The correction and softmax branches' `Proof2/Lib/TcSteps.lean` is the third round's promoted
  file; nothing new to promote there.

## Requests of the tml-fa4 softmax lane (fourth round)

- **The implicit wait of `tcgen05.st`** (the delayed first P store): `Code.step_tcStWait` (sub-step
  0: the wait for the thread's Tensor Memory loads, staying at the instruction at sub-step 1 with
  the same facts) and `Code.step_tcStStore` (sub-step 1: the store, continuing at the next
  instruction), with `fires_tcStTmpl_next`, in `Lemmas/Flow/Step/TcSteps.lean`. They are
  overrides: a site's two sub-steps are the role's states.
- **`step_ldv_mid` as an override** (draft `StepsBiasLoad.lean.draft`): `hc` was proved by
  `cases b <;> fin_cases c <;> code_lookup` inside one goal, but `gd` and `a` are metavariables
  shared by all goals of the `refine`, one term for every site, so no case split inside one goal
  can assign them. Split the site first (`cases b <;> fin_cases c`, then the `refine` per site), or
  let `site_step` take the element: its load class now tries `step_ldv_mid_sel` and
  `step_ldv_last_sel` (third item of the loader's requests), whose `hmid` closes `pc`, `sub`, `acc`
  and `facts` of the successor by `rfl` at a literal site.
- **Empty simp lists in quotations.** A quoted `simp only [$ls,*, x]` with an empty `$ls` is
  malformed (`unsupportedSyntax`, and inside `try` it silently does nothing), while
  `[x, $ls,*]` is fine. Every library macro now puts the spliced list last (`next_simp`, the
  `site_step` cases, `stop_close`, `site_read`, `site_acc`, `site_shape_step`, `stop_cases`,
  `ref_cases`, `or_shl32`'s closer); simp's lemma order does not matter. Kernel macros of the same
  form (`soft_sites`, `corr_sites`) should do the same.
- **The masked maximum (129 float `selp`s on mask bits): not done this round.** Each `selp`
  chooses a score or the immediate `-inf` (`0fFF800000`, which a register holds as bits, not as a
  `.float` value) on one bit of the mask word `0xffffffff >> s`; the walk splits each one, so the
  chain is exponential. A conditional value per element (`if c then .float x else .bits 32
  0xff800000`) removes the split but not the next one: the `max.f32` fold's ideal rule gives a
  `.float` value only on a finite result, so its result depends on whether any bit is set. The
  piece that fits is one `Seg` lemma for the whole stretch, stated with the mask as one number:
  from facts `m = 0xffffffff >> s` and the scores `x i`, the end facts give each selected register
  `maskSel m i (x i)` and the fold's register the maximum over `{i | testBit m i}` (finite when
  `s < 32`), proved by induction over the chain's pairs with the pattern of the code read off the
  decoded instructions (four instructions per element: `and`, `setp`, an optional unpack, `selp`).
  It needs the fold's rule in `Assumption.readEReal` terms and a check that the chain's
  instructions have that pattern; recorded for the next round.

## Family entries of `site_cases` and `site_shape` (fifth round)

- **Why.** Inkling's I2b measurement (its `DECISIONS.md`, "Task I2, continued") found that
  `site_shape` splits every `Fin` field of a site constructor before an override can act, so a
  family that a hand proof covers with one theorem (one `decide +kernel` over its members) became
  64 or 128 separate sites, and the check time rose above the hand proof's.
- **What.** Both tactics take `families [.c i j => proof, …]` after `except`. The constructor `c`
  (a dot name, or a name whose last components match) is split off its site type like any other,
  but its `Fin`, `Bool` and enumeration fields stay variables; they are renamed `i j` (`_` keeps a
  field anonymous) and the family's one goal is closed by `proof`, which may mention them. In
  `site_cases` the proof may be a `StepAt` or a `StepOk` proof, as for an override. `skip_by`
  runs first, as at a site. An entry that names no site is an error, and the goals a family's
  proof leaves are returned after the sites'.
- The splitting is `splitSitesFam` (`Step/SiteCases.lean`); `splitSites` is unchanged for
  `stop_cases`, `ref_cases` and the ledger tactics, which have no overrides.
- `families` is a new keyword (no identifier of that name in the repository; `family` is one, in
  tml-fa4's old tree, so it was not used).
- Checked by `Tests/Flow/SiteFamily.lean` on the tml-fa4 output warp: the eight `.store st b`
  sites and the two `.ready st` sites are each one goal closed by the warp's family theorems
  (`stepAt_store`, `stepAt_ready`, `shapeAt_write`), in both tactics.

## Stores, loads and commits in `site_shape` (fifth round)

- **`shape_st`**: an element of a weak store located by its address register (`storeTmpl`). It
  names the write's footprint (`loc.at (w / 8 * j)`, `w / 8` bytes, element `j`, from the
  effective address `loc`), and its bytes as `storeValue w v` of the value `v` the source operand
  reads; the alternative is undefined behaviour. `shape_store` (any store, nothing named) stays as
  the fallback the dispatch tries next.
- **`shape_ldNc`**: a `.nc` load so located (a non-coherent read of the element, when an
  assumption admits `.nc` at the instruction). `shape_ld`'s read now also gives the length of the
  returned bytes (`bs.length = w / 8`); a table that does not state it is unaffected (`intros`).
- **`shape_accessLd`, `shape_accessSt`** take `hT : memTmpl … a = accessTmpl … a` instead of
  `locSpace? = none`, which `rfl` proves for any literal access that `memTmpl` gives to
  `accessTmpl`: also a `.shared` variable (`ld.shared [global_smem]`, Inkling's `ld0`), which the
  old premise excluded. `shape_accessSt` names the value as `shape_st` does.
- **`shape_tcCommitOne`**: `tcgen05.commit` without a mask (the addressed CTA alone,
  `2 ^ rankOfCta`), at the target `TcCommit.resolve` gives; the resolution is the role's goal
  (Inkling: `resolve_unit`).
- **Dispatch.** `shapeLemmas` returns the lemmas of a class in order, and `site_shape_step` tries
  each (with its template unfolding) before the hook: a weak load or store whose address is a
  register goes to `shape_ld`/`shape_ldNc`/`shape_st`, every other load or store to the
  `accessTmpl` lemmas, then `shape_store`.
- **`shape_close`** closes `True`, a hypothesis, and conjunctions (right side first, so that an
  event equation fixes the witnesses before a side fact such as `storeValue … = .ok v'` is closed
  from the hypotheses; then left side first). This is the Inkling `Lib/Shape.lean` rule.
- After the template of a load or store is unfolded, `DType.width` is evaluated in `hf`, so the
  width is a numeral in the event's byte count and in a store's `storeValue` (a table's
  `storeValue 32 …` then matches the hypothesis). The shape goals themselves are simplified with
  the role's `unfolding` only: a first version added `Nat.add_zero` and numeral arithmetic there,
  which rewrote `sharedBase + 0` and broke Inkling's `sb_toNat`, a role lemma stated for the
  code's form.
- `site_shape` reports the underlying error of a failing site (it reported only the site), also
  for a runtime error (heartbeats, recursion depth), which `tryCatchRuntimeEx` catches.
- **Runtime errors are not caught by `first`/`try`**, and an error whose message is the runtime
  one is taken for one (Lean recognizes them by the message). Round 4's `site_acc`, tried before
  the role's address tactic, broke Inkling I2b's loader table this way: on the poll's mbarrier
  address its `decide := true` evaluation reached the recursion limit, and its closing `rfl`
  spent 4.9 s per attempt unfolding the conditional of a symbolic alignment. Fixes:
  `try_rt tac` (an ordinary failure, with its own message, in place of a runtime error) around
  `site_read`, `site_acc` and the two `decide`s of `site_shape_step`; `site_acc` ends with
  `with_reducible rfl` (the goal is then `.ok X = .ok ?acc`); and a few logic lemmas in its simp
  set. `decide := true` stays: without it `site_acc` left `1 = 8` and
  `CacheHints.globalOnly {}` in the common start's `ld0`. With these the I2b loader table checks
  again (it failed with the committed lane-L library before this round).
- A role's address tactic that applies a location lemma to a goal of another location function
  (`apply mbarLoc_b32_ok` on `mbarClusterLoc … = .ok ?m`) makes the unifier unfold both
  definitions: on Inkling's MMA commits 5.8 s per site and then the heartbeat limit. Such
  alternatives belong under `with_reducible apply`. `site_acc` does not unfold `mbarClusterLoc`
  (it reached the recursion limit on two of the MMA commit addresses).
- Checked on branch ink-i2b (scratch merge, not committed there): the MMA warp's four commits
  without their overrides (`mm_commit_at`) close by `shape_tcCommitOne` once `mm_addr` has
  `exact resolve_unit hu _` first and the two location lemmas under `with_reducible`
  (`EvWMma` 15.8 s, the file with overrides 16.6 s; on a host at load 120, 36.5 s against
  32–33 s); the common start's `ld0` without its
  override closes by `shape_accessLd` with two role facts in `reg_vals` (`wrapAddr` of the shared
  base is the base, the base is a multiple of 4, and `Site.sub`), 2.8–2.9 s against 2.6 s; an
  epilogue store `stO 5` closes by `shape_st` against a table `∃ v', storeValue 32 (d.word 5) =
  .ok v' ∧ e.kind = .wr (wordAcc ⟨.global, 0, (oAddr + 20) % M64⟩) v'.toBytes ∨ ub`, with the
  address normalized by `BitVec.ofInt_ofNat`, `BitVec.add_zero`, `BitVec.toNat_ofNat`,
  `Nat.reducePow`, `Nat.mod_mod` in `unfolding`. A family theorem over `stO k` for symbolic `k`
  still needs the code lookup over all members (`decide +kernel`), which `site_shape_step` cannot
  do; it can now call `shape_st` instead of its own inversion.

## `SingleTmaRing` ordered copies (fifth round)

- `Lemmas/Protocol/SingleTmaRing/Ordered.lean`: `copy_cp_of_pos`, `commit_of_later_copy`,
  `copies_chain`, the single-CTA counterparts of `PairTmaRing/Ordered.lean`, over
  `SingleTmaRing.Slot`/`Hyp` (any scope, `n` copies per use, premise `S.Fits` where the
  attribution results need it). From Inkling's `SxRingChain`, with its eight copies per use as
  `S.n`.
- Checked: Inkling's `Ring.Kv.copies_chain` (main) is `SingleTmaRing.copies_chain hX H.toS
  S.fits …` with the same arguments, by `exact` (a scratch file, not committed). Lane I replaces
  `SxRingChain` by that wrapper (I3).
- Order of this round: the masked-maximum `Seg` piece (third item of the brief) is not done
  before this one; see its entry below.

## Promotions (fifth round)

- **Inkling `Proof/Lib/Shape.lean` (ink-i2b)** into `Step/ShapeClasses.lean`, unchanged in
  statement: `OrUb`, `OrUb.of_some`, `shape_tcAlloc`, `shape_tcAllocWr`, `shape_tcRelinquish`,
  `mbarLoc_b32_ok`; the hook rule for the three inversions is in `Step/SiteShape.lean` (it passes
  the site's `hat.2.1`, since the sub-step selects the lemma). Its `shape_close` rule is replaced
  by the library's conjunction handling (second item of this round). Lane I deletes
  `Proof/Lib/Shape.lean` when taking lane-L (the names clash).
- **Inkling `Proof/Lib/KvSingle.lean` (main)**: nothing generic is left in it. Every theorem is
  stated in the KV slot's own definitions and proved by the library theorem at `H.toS`; the four
  generic lemmas it restates (`okPolls_take_le`, `commits_tcAsync_succ`, `tcAsync_lt`,
  `scopesMeet`) are already `SingleTmaRing`'s.
- **tml-fa4 `Proof2/Lib/UbLast.lean` (p4b-epilogue-wire)** as `Lemmas/Kernel/UbLast.lean`
  (`Run.ub_last`, `ub_last`; a module of its own, since `UbStop` cannot import
  `Lemmas.Kernel.Frame`). The branch deletes its copy and imports this one.
- **tml-fa4 correction lane's `Proof2/Lib/ShapeTc.lean` and `ShapeBar.lean`
  (tmlfa4-corr-proof2, recorded there for promotion)** as `Lemmas/Flow/Step/ShapeTc.lean`:
  `shape_tcLd`, `shape_tcLdLoad`, `shape_tcLdWait`, `shape_tcSt`, `shape_tcWaitSt`,
  `shape_tcWaitLd`, `shape_barSyncNR`, `shape_barArriveImm`, `shape_ldAny`. `site_shape` now
  tries `shape_barSyncNR` after `shape_barSyncN` and `shape_barArriveImm` for `bar.arrive`, so
  the branch's hook rule for `shape_barSyncNR` is no longer needed; the Tensor Memory lemmas and
  `shape_ldAny` stay hook rules of the kernel (which fits depends on its assumptions and the
  sub-step). The branch deletes both files.
- **`seg_pre` rules are global** (Inkling lane-I notes, ink-steps): `macro_rules` of a tactic are
  tried in every file that imports them, the most recently imported first, so a rule that never
  fails (`word_subst`) shadows another role's (`mma_pre`) when both are imported. No library
  change is needed: `scoped macro_rules` in the role's namespace makes a rule active only where
  that namespace is open (checked on a scratch file: with two roles' scoped rules imported, each
  applies only under its `open`, and with neither open the default `skip` runs). `SiteIte.lean`'s
  docstring says so; the same holds for `lands_auto` rules. The kernels change their rules to
  `scoped`.

## The masked maximum (third item of the fifth round): not done

- Not attempted in code this round; tasks 4 and 5 were done first so that the round's context was
  not spent on one item. The analysis of the code, for the next round:
- The stretch (pc range around PTX lines 4436–4980 of `full_p16_s1.ptx`) has four mask words
  `w_k = 0xffffffff >> max(32 k - c, 0)` (`shr.u32` of `-1`, inline asm), `k = 1 … 4`, and for each
  word 32 elements: bit 0 by `and.b32 r, w, 1; setp.ne.b32 p, r, 0; selp.f32 d, x, -inf, p`,
  bits 1 to 30 by `and.b32 r, w, 2^i; setp.eq.b32 p, r, 0; selp.f32 d, -inf, x, p`, bit 31 by
  `setp.gt.s32 p, w, -1; selp.f32 d, -inf, x, p`, with an unpack `mov.b64 {x0, x1}, %rd` before
  every even element. Then a fold of four accumulators: `max.f32` of two operands for the first
  eight elements, then three-operand `max.f32` chains. So the pattern differs by bit position and
  the fold is a tree, not a single chain.
- A linear route instead of one large `Seg` lemma: (1) a floating `selp` whose predicate fact is a
  symbolic Boolean writes the conditional value `bif p then a else b` instead of splitting (the
  predicate's own fact, from the `and`/`setp`, is `testBit w i` or its negation, by evaluation);
  (2) `max.f32` on operands that are each a `.float` or the bits of `-inf` has the outcome
  `maxE vs` (`Lemmas/Flow/MaxCore.lean`), which faults on none of them, so the step writes the
  value of `maxE vs` as one fact (a `Value` function of the operand values) without deciding
  whether any bit is set; (3) the closed form "the maximum over the set bits, `-inf` if none" is a
  pure lemma about those nested values, stated in `Ref` by the kernel lane. Each step is local, so
  the walk is linear in the 129 selects and the 64 maxima. (1) changes `seg_sym`'s handling of
  floating `selp` (round 3 splits it, and the correction lane relies on the split), so it must be
  an opt-in rule (a `seg_pre`-like hook or a lemma the role passes), not a default.

## Correction lane requests (fifth round, tmlfa4-corr-proof2 "Correction, round 2")

- **Closer order.** `site_shape_step` tries the role's `addr_by` before the two `decide`s (after
  `site_read` and `site_acc`), so a side goal the role closes is not first evaluated by `decide`
  on symbolic terms. Epilogue `Shape.lean` 10 s and FA4 `StoreShape.lean` 2 s unchanged; the
  loader scratch test's output is unchanged.
- **`shape_store` argument order**: already fixed in round 4 (`hf` first), and plain weak stores
  now go to `shape_st` first (second item of this round).
- **`ShapeTc.lean`, `ShapeBar.lean`**: promoted (promotions of this round).
- **Not done this round:** `seg_sym` stepping Core's own rule on zero, negative, infinite and
  NaN `f32` values (today a value outside an assumption's rule stops the walk), and a return
  value and return kind for Tensor Memory loads (`RetKind` has no Tensor Memory case). Both are
  needed before the Correction fragment's `stop_iff`/`Fragment.Ok` can hold; recorded for the
  next round.

## The masked maximum by conditional values (sixth round)

- **Opt-in, not default.** A role opts in with `scoped macro_rules | `(tactic| sym_selp_value) =>
  `(tactic| skip)` in its namespace (the hook fails by default, so the correction lane's case split
  on floating `selp` is unchanged). With it, a `selp` whose operands are not words writes
  `if c = true then a else b`, as one step by `Seg.selpV` (operands of any kind of the type's
  width, such as a written infinity, whose byte count `seg_fp` cannot evaluate; it needs the
  kernel's `sym_local_none`), else by `Seg.selv_pos`/`Seg.selv_neg` with both sides by `seg_auto`;
  a constant operand is its 32-bit pattern (`selpValue`).
- **Reading conditional values.** A rule step reads a source whose value is a payload, a constant
  pattern (finite or infinite: `readLit?`, `readEReal_f32_ninf`/`pinf`), a value an ideal rule
  wrote (`readEReal_erealValue_f32`), or a conditional of such values (`readEReal_ite`) as one
  extended real, through `readERealOpnd_regs_read`, so the `max.f32` fold over 128 masked scores is
  one rule step per instruction and writes `erealValue .f32 (max …)` of the readings. Pairs: a join
  of two such values reads as their pair (`pairRead_join`, the join checked to be a pair by
  evaluation) and a closed join of two constant halves by its halves (`pairReadProof?`).
  A rule's own condition still stops the walk ("depends on the condition"): `rfl` is tried first
  so a conditional inside a value does not count as one.
- **Steps on conditional operands** (`condStep`): where the rule step does not evaluate and a
  source holds a conditional, the step is taken on each side of its first condition
  (`Seg.facts_eq` substitutes the side into the facts), recursively; a side without conditionals
  and without a rule step is Core's rule evaluated on the side's values, which are then constant
  patterns (the `-∞` lanes). The written value is `if c = true then v₁ else v₀`. The walk also cuts
  at a local step that writes one register and reads a conditional (a pack). Exact products and
  sums with one infinite operand (`mulEReal_bot_pos` …, `addEReal_bot_coe` …) are in the rule
  simp set; a sign the context does not give stops the walk.
- **Closed form**: `Lemmas/Flow/MaskMax.lean` (`maskMax n c x` = the maximum over `i < n` with
  `c i`, `maskMax_succ`, `maskMax_le_iff`, `le_maskMax`, `maskMax_eq_bot_iff`, and
  `ones_shr_testBit`: bit `i` of `0xffffffff >>> s` is `i + s < 32`). Restating the fold's
  `erealValue (max …)` tree and the code's mask predicates (`compare .ne .b 32 (w &&& 2^i) 0`
  over `w = if s ≥ 32 then 0 else -1 >>> s`) into these is the softmax lane's `Ref` work.
- **Measured** (tml-fa4 code, explicit start facts: the count register and the 64 score pairs at
  pc 3872, `lean`, loaded host): the 128 selects and the 64-step fold up to the named-barrier
  arrival (pc 4397) in one `seg_sym` call, linear: about 4 to 6 s per select (growing with the
  facts) and 1.5 to 3 s per fold step; the selects alone took 12 min. Splitting the stretch into
  per-word lemmas (`Seg.comp_ex`) lets them check in parallel. Tests:
  `Tests/Flow/SelpValue.lean` (two selects, a fold step with its value, packs and a packed `fma`
  with `-∞` lanes, 15 s).
- **Not done in round 6**: a step on a conditional that writes two registers (the unpack
  `mov.b64 {a, b}` after each packed `fma` of the exponent): `condStep` handled one destination.
  Done in round 7 (next section).

## Return kinds for real payloads and Tensor Memory loads (sixth round)

- `RetKind.real fmt` accepts a payload `.float fmt x` only (no NaN); `recvAll e` is the list of
  values an event returns: the elements of a Tensor Memory load (`.tc (.ld _ vals _)`), else
  `recv e`. `RetKind.accepts k e` is now `∀ v ∈ recvAll e, k.acceptsVal v` (`accepts_recv`,
  `accepts_tcLd`); `stop_cases` unfolds it. With these the correction machine's stops on a
  statistics word that is not a real and on a Tensor Memory element that is not an `f32` real are
  stops on the return kind (`ret = .real .f32`), which `stop_iff` states.
- Core's own rules on non-real values: the walk now follows `-∞` and `+∞` operands (ideal rule on
  the infinity, or Core's rule on a constant pattern after a side split) and the conditional
  values above. Still not followed: a symbolic real payload outside a kernel rule's condition
  (the LSE's `lg2.approx` of a row sum `rs ≤ 0`): Core reads the payload's encoding, and its result
  (`-∞` for zero and negative subnormals under `.ftz`, NaN for negative normals) depends on the
  encoding of `rs`, for which the library has no lemma; and a symbolic word whose class (NaN,
  infinite, finite) is unknown. Both need an outcome value (`okVal (coreFloat …)`) with a no-fault
  lemma per instruction form; not written. The LSE positivity stays a content stop for now.

## Faulting floating steps as `DeadFrom` (sixth round, FlashMLA D-F3-SCOPE)

- `DeadFrom.local_error`: a local instruction whose step faults from every state with the facts
  kills the thread. `seg_sym` on a `DeadFrom` goal, at a floating step no rule step takes, tries it
  with the kernel's hook `sym_fault` (default: fails), which proves the fault: the kernel's rules
  decline on the facts (for FlashMLA, `pairValue` is `none` on a non-finite half) and Core has no
  rule (`mul.bf16x2` has no rounding modifier, `FloatInstr.lane` is `none`; `coreFloat_add_error`
  is the pattern for `add`). Test: an opaque NaN operand of tml-fa4's `add.f32` at pc 5005
  (`Tests/Flow/SelpValue.lean`).
- Register frame: unchanged from item 8 above. Every local step writes only its destinations
  (`execLocalA_frame` with `RulesFrame A`, `Lemmas/Register/RegisterFrame.lean`) and a segment's
  result is a function of the facts of the registers it reads (`run_footprint`, which takes the
  run on `override F R` for every `R`); what F3 lacks is not a frame but Core's behaviour on
  values of unknown kind, which the stratified `followed_stages` (first: reads of the area return
  words) addresses.

## Promotions (sixth round)

- Requests recorded in the kernels' `DECISIONS.md` since round 5: the tml-fa4 startup's
  `seg_prefetch` and `st_close` (`Proof2/Startup/Steps.lean`). The other candidates named there
  (`glue_fired`, `followedOn`, `Word.lean`, `Elect.lean`, `UbLast.lean`, `ShapeTc`/`ShapeBar`,
  Inkling's `Shape.lean`) were promoted in rounds 4 and 5; no `Proof*/Lib` file on main is left
  except Inkling's `KvSingle.lean` (wrappers only).
- `Seg.prefetchTensorMap` (`Lemmas/Flow/Step/SegSym.lean`): a tensor-map prefetch as a one-step
  segment from its register's parameter pointer, the launch's object declaration and the
  assumptions' silence; the startup's `seg_prefetch` is this lemma with `Pre.maps`.
- `sym_close` rewrites by an `explicitParams L ps = L` hypothesis in context when the goal
  mentions the explicit launch (a special register read under it), so `seg_fp`'s restating step
  closes such values without a role tactic; the startup's `st_close` is then `sym_close`, and the
  CTA index need not be stated under the explicit launch.

## Requests of the tml-fa4 loader (sixth round, tmlfa4-loader-proof2)

- **Runtime errors as failures.** `try_rt` moved to `Lemmas/Flow/TryRt.lean` (with the loader's
  name `catch_rt` as a synonym; the loader deletes `Proof2/Lib/CatchRuntime.lean`) and is used by
  `seg_fp` (the whole evaluation), `seg_auto` (each length tried), `sym_close` (its first
  `rfl`), `seg_close` (`rfl`, `close_fact`, `decide +kernel`), `site_norm` (a `change` whose check
  runs away is skipped), `lands_auto` (sub-step `rfl`, each segment tactic) and every alternative
  of `site_step`, so an evaluation that reaches the recursion or heartbeat limit (`w + 4294967294`
  on a free word) lets the next alternative run.
- **`sym_decide` budget**: the option `seg_sym.decideHeartbeats` (units of `maxHeartbeats`,
  default 20000; it was a fixed 400 in those units), set per file with `set_option`.
- **`opaque_decide`**: not promoted. It decides a branch from a hypothesis about the loader's own
  opaque conditions (`geW`, `ltZ`) by their unfolding lemmas, which are the kernel's; the generic
  part (a hypothesis whose left side unifies with the branch condition) is already
  `decideBool`'s hypothesis search.
- **Full-mask votes** (lane T1's workaround): `Lemmas/Kernel/FullVote.lean`, `voteWith m e` (a
  ballot or mode vote with member mask `m`) with `voteWith_vote`, `voteWith_voteMode` for any
  mask, `voteWith_vote_ne` and `voteWith_of_none`; tml-fa4's `isFullVote` is
  `voteWith (2 ^ 32 - 1)`, and its value on a vote is the lemma, not an evaluation of the literal.

## Steps on conditional values with several destinations (seventh round)

- **`condStep` over destinations.** A local step that reads a conditional value and does not
  evaluate is cut whatever the number of registers it writes (`SymCtl.rule ds srcs ruled`); each
  side of the first condition is taken by the same means and each destination gets
  `if c = true then v₁ else v₀`, or `v₁` when the two sides agree (the unpack of a lane that does
  not depend on the condition). A side without conditionals is one piece by `Seg.writes`: the
  writes `(d₁, v₁), …, (dₖ, vₖ)` in Core's order (`setRegsL`; an unpack writes its low half
  first), facts `(dₖ, vₖ) :: … :: (d₁, v₁) :: F`, keys checked by `freshKeys`, and the step proved
  by evaluation on `override F R`: Core's rule where the kernel's `sym_local_none` gives
  `NoRuleAt` (`execLocalA_core`), else the assumptions' rules evaluated as they stand (an
  approximation's rule that declines on `-∞`, a move no assumption selects); `seg_auto` only if
  both fail. `Seg.facts_eq` restates start and end facts by one equation of the pair (one `simp`
  pass, the start facts inside the end facts once).
- **Rule steps only where a rule may apply.** The cut records whether an assumption may give the
  instruction a rule (`hasRule` at the cut, `ruled`); a pack or an unpack no assumption selects
  is not tried as a rule step on every side.
- **A bug that made the walk exponential** (no soundness issue): `ruleStepProof` restated the real
  facts of the context (`realFacts`) as `have`s on the caller's goal, so every successful rule
  step doubled the hypotheses that the next one restated (the walk stalled at the third packed
  `fma` of the exponent with a single `0 < s` in context). The restatement now lives on the rule
  step's own goal; register facts (`Holds`) are not restated.
- **Cheaper pieces.** A source's fact is found by its position (`mem_idx`, the lookup checked by
  evaluation) instead of `fact_mem`'s walk down the list; at a cut whose state is still the start
  state the facts are the start facts as they stand, and a register that keeps its start value is
  not re-normalized (`stateFacts … start fresh`); `normVal` evaluates closed values to their
  constructors (Core's `+0` for `ex2.approx` of `-∞` is then `.float .f32 0`, which the
  probability pack's conversion rule reads as a finite real).
- **Error recovery off where a failure must fall through**: `Seg.writes`, `Seg.selpV` and
  `DeadFrom.local_error` are tried under `Tactic.withoutRecover`; before, a failing `by` block
  inside the `exact` was reported as an error of the whole proof instead of reaching the fallback
  (the final `selp` of the masked maximum hit `simp`'s step limit there, on the byte count of the
  fold's value; that byte count is now `erealValue_f32_bytes` first).
- **Measured** (tml-fa4 code, `lean` on scratch files, shared host under load; per-step times are
  the walk's, from `SEG_SYM_LOG`):
  - Masked maximum, pc 3872 → 4397 (start facts: the count register and the 64 score pairs), one
    `seg_sym` call: passes; walk 439 s, file 605 s (imports and the kernel's check of the proof
    term included), 26 GB. The 128 selects with their mask arithmetic take 404 s (about 1 s each
    at the start, 4 s at the end: the integer pieces between two selects go through `seg_fp`
    with all live facts), the 65 fold steps 28 s (0.4 s each), the final `setp`/`selp` 1.3 s.
    Round 6: 4 to 6 s per select, 1.5 to 3 s per fold step, the final `selp` failing.
  - Exponent stretch, pc 4399 → 4826 (the first `tcgen05.st`; start facts: the scale `s > 0`, its
    negation, the selected maximum as a real, and the 128 scores as conditionals on abstract mask
    bits `c i`): passes; walk 1271 s, file 1622 s, 27 GB. The 64 pack/`fma`/unpack triples
    (4400 → 4594) 350 s, 1.8 s per instruction rising from 1.3 to 2.1; the 128 `ex2.approx`
    1.5 s each; the probability packs and the packs of their pairs (4626 → 4818) 727 s, a pack
    of four conditions (16 sides) about 15 s; the eight final unpacks about 18 s each. Before the
    fixes above the walk stalled at the third `fma` (pc 4409).
  - Not covered by the two runs: pc 4398, `neg.f32` of the scale word (`.bits 32 (paramW …)`):
    Core's rule decodes the pattern, which is not a literal, and no assumption takes `neg`; the
    softmax lane proves that one step by hand (Core's `neg` of a word whose `f32Value` the `Pre`
    gives) or lane L adds reading a word through such a hypothesis. And the restatement between
    the runs (the masked maximum's end facts, with the mask predicates on the count register and
    the selected value `if p then erealValue (max …) else 0`, into the exponent's start facts) is
    the softmax lane's `Ref` work (`Lemmas/Flow/MaskMax.lean`). Scratch files:
    `.lake/own/libL/r7/` (`M2.lean`, `E2.lean`, `E4.lean`, logs `*.log`).

## `site_shape`: a class lemma whose goals fail falls through (seventh round)

- The correction lane recorded a regression of round 5 (`tmlfa4-corr-proof2`, "Correction,
  round 3"): `site_shape` applied `shape_st` to the final stage's `st.shared.v4` stores, whose
  element a symbolic sub-step selects, and the side goal `srcs[k]? = some _` then failed, so the
  stores needed overrides. `site_shape_step` now tries each lemma of the class together with its
  side and shape goals and goes on to the next lemma (`shape_store` after `shape_st`) or the
  role's `shape_inv` hook when they fail; if the hook fails too, the first lemma's error is
  reported. The correction lane can drop the `corr_sst` overrides once it takes this round
  (not checked here: the branch's `Shape` files are not on lane L).

## `lg2.approx` of a row sum `rs ≤ 0` (seventh round, reassessed)

- Not done in round 7 either; recorded what it takes. `FloatFmt.encode_eq` (Core) gives the sign
  bit of a payload's pattern as `x < 0`, so `+0` is the pattern of `rs = 0` and every `rs < 0`
  encodes to a negative class: `-0`, a negative subnormal, a negative normal or `-∞` (rounding a
  large magnitude). Core's `lg2.approx.ftz` table sends `+0`, `-0` and the flushed negative
  subnormals to `-∞` and the negative normals and `-∞` to NaN, so the step does not fault and
  writes one of two values. A Core-rule step there needs (1) a lemma that `classify .f32` of
  `.float .f32 x` for `x < 0` is one of the four negative classes (from `encode_eq` and the
  decoder's sign field), (2) the step's value as a conditional on the class (`if` the pattern is a
  negative normal or `-∞` then NaN else `-∞`), whose condition no hypothesis decides, and (3) the
  correction machine's next steps on that value (the LSE's `mul`/`add` and its store), which then
  read a NaN or an infinity. That is a new reading class in `seg_sym`, not a lemma; the LSE
  positivity stays a content stop.

## Promotions (seventh round)

- Requests recorded in the kernels' `DECISIONS.md` since round 6 (branches `tmlfa4-t4`,
  `tmlfa4-softmax-proof2`; `p4b-epilogue-wire`, `tmlfa4-corr-proof2` and `tmlfa4-loader-proof2`
  name none beyond those promoted before):
  - `Frame.pollsOn_of_shapeAt`, `Frame.pollsOn_of_shape` (`tmlfa4-t4` `Proof2/Lib/PollsOn.lean`)
    → `Lemmas/Kernel/Progress/PollsOn.lean`, a module of its own rather than `Poll.lean`, which
    would otherwise import the site-machine layer (`Lemmas.Kernel.Frame`, `Lemmas.Flow.Ledger`).
  - `fires_wait_reg_al` (`tmlfa4-t4` `Proof2/Lib/WaitReg.lean`) → `Lemmas/Flow/Step/ShapeRegs.lean`;
    `fires_wait_reg` is now its weakening.
  - `Frame.exists_of_count` (generic form of `tmlfa4-t4`'s `Common/Frame.lean` lemma, over any
    counted machine family) → `Lemmas/Kernel/Counted.lean`.
  - `AllocT`, `allocT` (`tmlfa4-t4` `Mma/Warp.lean`) → `Lemmas/Flow/Step/Alloc.lean` (three unused
    `simp` arguments dropped).
  - `holds_setRegs_frame` (`tmlfa4-softmax-proof2` `Proof2/Lib/SetRegsFrame.lean`) →
    `Lemmas/Flow/Step/TcSteps.lean`, beside `holds_setRegs_live`.
- The branches delete their copies when they take lane L (same names in `PTX.Frame`/`PTX.Flow`;
  `allocT` would be ambiguous under `open PTX.Flow`). `isColl_vote` is not promoted: `voteWith`
  (`Lemmas/Kernel/FullVote.lean`, round 6) replaces it.

## Reads of the thread's own local memory (seventh round, coordinator request for lane T1)

- `Lemmas/Kernel/Source/Local.lean`, beside the protected read: `local_read_byte_of_last_store`
  (a byte of a `ld.local` is the byte of the thread's last `st.local` that covers it, a wider
  store included) and `local_read_of_last_store` (a load with that store's footprint returns its
  bytes). The store is before the load in the thread's trace, so in program order; the frame is
  that every other store of the thread covering the byte is before the store or after the load.
  They wrap `local_read_byte_of_last_write` (`Lemmas/Protocol/LocalMemory.lean`), whose
  ownership premise is now the named property `LocalOwned X`: every write of a `.local` location
  is an event of the location's owner thread.
- On the thread side `accessLoc_local_owner` gives the owner from Core's access rule (every
  `.local` location an access of thread `g` names is `g`'s). `LocalOwned` itself is not derived
  from `Consistent` here: that needs, besides the thread's write templates, that no asynchronous
  write (tensor loads and stores, linear copies, `st.async`/`red.async`, CLC responses) has a
  `.local` destination, which is an enumeration of Core's issue templates. tml-fa4 has it as the
  old tree's `localWriteOwner` (`Proof/GlobalWrites.lean`, from the kernel's code checks), whose
  statement is `LocalOwned X` for the frozen code; lane T1 passes
  `fun w a bs l hw hl hc => localWriteOwner hX hw hl hc`. A generic derivation is open.

## The fragment interface as library (Phase 2, item 2)

- **What a kernel declares.** `Lemmas/Flow/Roles.lean` is the kernel-independent part of tml-fa4's
  `Proof2/Common/Roles.lean` and `Sound.lean`: `RoleDecl` (region and exits; `RoleDecl.closed` and
  `RoleDecl.sites` are the `CodeCheck` folds), the stub fragment `Code.stop` with `stop_steps`
  (from the decidable `StubSite K pc`: an unguarded event instruction), the roles with stubs
  `Code.withStubs R pcOf : ι ⊕ E → Code` (migrated role `i`, or the stub of entry `r`), the gated
  exits `Code.gatedExit enterOf sel` (`sel r d = some i` enters role `i`, `none` the stub; the gate
  is a test inside `sel`), the thread machine `Code.roleThread` (glue plus ledger), its hand-off
  reduction `handoff_gated` (one hand-off per migrated role plus "an exit state sits at its entry's
  first pc") and `roleThread_sound`. A new kernel declares `ι`, `E`, `pcOf`, `enterOf`, `sel`, the
  role fragments and their hand-offs; it proves no glue or stub lemma.
- **Role index as a sum.** tml-fa4's `Role` has the stubs as one constructor (`stub r`); the library
  uses `ι ⊕ E`, so it needs no kernel inductive. The two are equivalent; the sum keeps `withStubs`
  and `roleThread_stub` (a stub stops at its first event, `rfl`) generic.
- **Frame facts and the assembly.** `Lemmas/Kernel/Roles.lean`: `Frame.count_all`,
  `Frame.ub_zero` (any counted family; the class that counts undefined behaviour is a premise), and
  `Frame.followedAt_sel` (the `good_migrated` pattern: each role's `good` on its threads assembles
  into the family's following with the invariant the thread index selects; it is `Iff.rfl`, kept
  as the documented interface).
- **The collective source.** `Lemmas/Kernel/Source/WarpColl.lean` generalizes tml-fa4's
  `Proof2/Common/Frame.lean` (order) and `Proof2/Common/Coll.lean` (`shfl_src`, `vote_src`, branch
  `p4b-epilogue-wire`) to any sound machine family `C` and invariant `J`: `Frame.isColl`
  (shuffles and `voteWith (2 ^ 32 - 1)`), `collUpTo` (the measure), `countColl`, `InWarp` (Core's
  warp index `g % L.block / 32`), `lane_facts` (premise `L.block % 32 = 0` only), `GoodUpTo`,
  `upTo_of_lt`, `upTo_of_prev`, `good_state`, `shfl_src`, `vote_src`.
- **Checked on tml-fa4** (scratch files `.lake/own/libL/r8/T2.lean`, `T3.lean`, not committed
  because they would couple `Tests/` to kernel files that lane T1 is editing): on main's
  `Proof2/Common/Frame.lean`, `isColl = Frame.isColl`, `μ X = Frame.collUpTo X` and
  `GoodUpTo J X w n ↔ Frame.GoodUpTo (thread p L) J X w n` hold by `rfl`/`Iff.rfl` (the kernel's
  `isFullVote` is `voteWith (2 ^ 32 - 1)` unfolded), and `upTo_of_prev`, `good_state`,
  `lane_facts`, `ub_zero`, `stop`/`stop_steps` (pc 179 by `kernel_rfl`) are one-line instances;
  on `p4b-epilogue-wire`'s `Common/Coll.lean`, `shfl_src` and `vote_src` (155 lines with their
  proofs) are `Frame.shfl_src (by rw [hp.block]) hX hg hw he hcs IH hV hE` and the `vote_src`
  analogue, with their statements unchanged.
- **How tml-fa4 switches (lane T1).** In `Common/Frame.lean` replace `isColl`, `μ`, `countColl`,
  `isShfl_not_vote`, `InWarp`, `lane_facts`, `GoodUpTo`, `upTo_of_prev`, `good_state`, `count_all`,
  `ub_zero` by the library's (`abbrev`s or direct uses; the statements above are definitionally the
  kernel's), and `Common/Coll.lean`'s proofs by the one-line instances. `Common/Roles.lean` may keep
  its `Role` inductive (only `stop` and `stop_steps` are then replaced: `stop L g pc` is
  `Code.stop kernel Assumptions.all L g pc` by `rfl`) or move to `Code.roleThread` with
  `ι := {epilogue, mma, correction, loader b}` and `E := Startup.Entry`; the latter replaces
  `exit`, `glued`, `thread`, `startup_steps`' exit case, `stop_steps`, the stub branches of `handoff`
  and `thread_sound` (about 60 lines) but renames the role states (`.inr ⟨.inl i, d⟩`), which every
  upper-layer file matches on; the choice is lane T1's. The other kernels (Inkling, FlashMLA, FA4,
  GEMM) start their Phase 3 trees on `Code.roleThread` directly.

## Progress templates for glued thread machines (Phase 2, item 3)

- `Lemmas/Kernel/Progress/Glued.lean`, from tml-fa4's `Proof2/Progress` (main): `Sched.gluedTime`
  and `Sched.gluedTimed` (the time of a glued, counted state from the first fragment's table and
  the roles' tables, each reading the ghost counts; tml-fa4's `time`/`timed` with `startTime` and
  `roleTime`), `Sched.passTime` and `passSched` with `passTime_sched` (a scan state is on the
  schedule `base + 2 n` at a collective and earlier otherwise: the time premise of
  `Sched.collSched_of`, so `Sched.lag_of_sched` gives a collective class's lag once the counts are
  the ledger's), `ub_count_zero` (no undefined behaviour in the execution: the ledger's count of it
  is zero at every state; MmaPoll's lemma for any counted family), `okPolls_count` (a poll parity's
  count from the ledger; MmaPoll's `okPolls_eq`) and `shfl_le_collUpTo` (StartAll's `shfl_le_μ`).
- Already generic before this round and not duplicated: `Sched.collSched_of`, `lag_of_sched`,
  `mbar_at_steps`, `bar_sync_steps`, `Frame.pollsOn_of_shape` (round 7), `fires_wait_reg_al`.
- Not promoted: `OutputColl`'s `warpColl_eq`/`time_sched` (they read the output warp's `Fits`),
  `StartAll`'s `start_noBad`/`bar_before` (the startup's `StartAt`), the phase constants (`cmax`,
  `bmax`, `scanBase`): kernel data.
- Checked on tml-fa4 (scratch `.lake/own/libL/r8/T2.lean`): `Progress.passTime = Sched.passTime`
  by `rfl`; `MmaPoll.ub_count_zero` is `Sched.ub_count_zero (C := glued p L)
  (cls := fun g => cls L g) (c := .ub)` with a two-line class fact. tml-fa4 switches by deleting
  `passTime`, `ub_count_zero`, `okPolls_eq`, `shfl_le_μ` and using the library names (lane T4 /
  T1); `timed` may become `Sched.gluedTimed`, which is `⟨thread p L, time p L⟩` up to the names.

## Promotions (eighth round)

- Requests recorded in the kernels' `DECISIONS.md` since round 7:
  - `tmlfa4-loader-proof2` (also on `p4b-epilogue-wire`) `Proof2/Lib/ShapeAsync.lean`
    (`shape_cpAsyncN`, `shape_cpTensorAt`, `mbarLoc_bits`, `mbarLoc_reg`, `trunc_add_mod8`) →
    `Lemmas/Flow/Step/ShapeAsync.lean`, unchanged.
  - FlashMLA (`flashmla-f3`, D-F3) `Proof/Lib/WordRead.lean`: the generic part
    (`wordOf`, `readBits_word`, `readBits_noWord`, `readBits_imm`, `not_ptr_of_word`) →
    `Lemmas/Flow/WordRead.lean` in `PTX.Flow`; the dequantizer's step lemmas (`execLocalA_prmt_*`,
    `_cvtLow_*`, `_shr_*`, the `mul.bf16x2` facts) read the kernel's assumptions and stay. The
    named `holds_of_mem` is the library's `holds_mem`.
  - Inkling (`ink-iface`) `Proof/Lib/Count.lean` (`stateAt_inv`, `count_closed`) →
    `Lemmas/Kernel/CountClosed.lean`; its helper `countP_take_succ` is `countP_take_succ_ite`
    here (the name `countP_take_succ` is used unqualified by the ring files under another
    namespace).
- The branches delete their copies when they take lane L (same names in `PTX.Flow`/`PTX.Frame`;
  FlashMLA's names are in its own namespace but would be ambiguous under `open PTX.Flow`).
- Second part (modules many kernels import, so in a commit of their own):
  - `tmlfa4-softmax-proof2` `Proof2/Lib/ShapeTcWait.lean` (`shape_tcStWait`, `shape_tcStStore`,
    `shape_barArriveR`) → `Lemmas/Flow/Step/ShapeTc.lean`; `site_shape` tries `shape_barArriveR`
    after `shape_barArriveImm` for `bar.arrive` (registers for the id and count).
  - `tmlfa4-loader-proof2`/`p4b-epilogue-wire` `Proof2/Lib/ShapeInit.lean` (`shape_mbInitAny`) →
    `Lemmas/Flow/Step/ShapeClasses.lean`; `site_shape` tries it after `shape_mbInit` for
    `mbarrier.init` (a lemma whose goals fail falls through since round 7), so the branches'
    `shape_inv` rule for it can be dropped with their copy.

## Word arithmetic by rewriting, and site families in `stop_cases`/`ref_cases` (Phase 2, item 1)

- **`w32_norm` (`Lemmas/Flow/Arith32Norm.lean`).** The per-site word arithmetic of a closed-form
  proof (tml-fa4 Epilogue `Select.lean`: 808 lines) is mostly `rw [op_W (by omega) (by omega) …]`
  with the bound facts restated per rewrite. `w32_norm [lemmas] at loc` is `simp` with every word
  lemma of `Arith32Word` (additions, `addi`, subtractions, products, `mad`, the minimum, the shifts,
  comparisons with words and with immediates of the `.b`, `.u` and `.s` kinds) and discharger
  `omega`: the bounds are stated once as `have`s and each rewrite whose bounds `omega` proves from
  the context fires; one that does not is left in place (no error). New lemmas take immediates as
  integers with `0 ≤ n` (`i32_int`, `addi_int`, `shrs_int`, `shru_int`, `scmpi_*_W`), so literal
  immediates (`8 : Int`) and cast ones (`((k : Nat) : Int)`) are both rewritten (`Int.reduceToNat`,
  `Int.toNat_natCast` in the set). Products of two numbers are atoms for `omega`, so a bound such
  as `x ≤ x * heads` or a distributed sum is a `have` the proof states (as the hand proofs do).
- **Measured on `Select.lean`** (scratch `.lake/own/libL/r8/W2.lean`, same statements): `tilesOf_W`
  26 → 7 lines, `A_succ_W` 30 → 24, `predv_iff` 38 → 33, `reads_iff` 8 → 5, `lw_eq_b` 8 → 3;
  each checks in the time of the original (file under 5 s including imports). Lane T1 can apply it across `Select.lean` and the `fits_*`
  arithmetic of `Next.lean`; its kernel-specific word lemmas (`lw_eq_b`, `lw_gt_u`, `lw_ne_b`) are
  `scmpi_eq_b_W`, `scmpi_gt_u_W`, `scmpi_ne_b_W` with `lw ℓ = W ℓ`.
- **Generated value tables and the word arithmetic.** `Tools/machine_gen.py` already regenerates the
  output warp's scan entries in this vocabulary (`Tests/Gen/EpilogueUpCheck.lean`: `rfl`-equal to
  `partials` and `tilesOf`). With `w32_norm` a generated entry's closed form is proved by stating
  the bounds and one call, the same as for a hand-written entry, so the generator needs no closed-
  form output; a role that imports a generated table instead of hand-written defs keeps its
  `Select`-style lemmas unchanged. The generator was not changed this round.
- **`unsplit [c, …]` in `stop_cases` and `ref_cases`** (`Lemmas/Flow/Step/SiteShape.lean`): the
  sites of the named constructors are one goal each with their fields as variables, as `families`
  in `site_cases`, when the transition does not depend on the fields' values. The token is
  `unsplit` (not `keep`: a token that is a common identifier breaks files that use it, see L2).
  Measured on tml-fa4's MMA warp `Shape.lean` (`stop_iff`, scratch copies `MmaShapeA/B.lean`): with
  `unsplit [qk, pv, ce, cm, sh, wt]` the file checks in 6.9 s instead of 11.8 s. `ref_cases` is not
  used by any kernel yet (the Epilogue's `Next.lean` states `fits_next`/`next_ne` per site family on
  its own `Fits`, not on `Fragment.OkAt`); a role that restates its `ref_next` on `Fragment.OkAt`
  gets the per-site reduction and `unsplit` for its families.

## `LocalOwned` from `Consistent` (Phase 2, item 4)

- `Lemmas/Kernel/Source/LocalOwned.lean`: `Frame.localOwned (hX : Consistent L K A mem0 X) :
  LocalOwned X` for every kernel, so the local read source needs no ownership premise
  (`Frame.local_read_byte`, `Frame.local_read`: the round-7 lemmas with `localOwned hX` passed;
  the round-7 forms with the premise are unchanged, so no user changes).
- **Thread writes** (`fires_write_local_owner`, `fires_rmw_local_owner`, over every instruction):
  a write event comes from a store template (`fires_write_tmpl`, `fires_write_op`): a direct
  store (`storeTmpl`, `releaseStoreTmpl`) has no rule in local memory (`effAddr` of `.local`
  fails, `effAddr_not_local`); every other store (`accessTmpl`, `st.bulk`) locates its bytes by
  `accessLoc`, whose `.local` locations are the thread's own (`accessAcc_local_owner` from
  round 7's `accessLoc_local_owner`); a `movmatrix` store and a Tensor Memory allocation's address
  store write shared memory. An `atom`/`red` (`atomTmpl`, the only template that fires `.rmw`,
  `fires_rmw_op`) locates its element by `accessLoc` too.
- **Asynchronous writes**, by Core's issue templates: a linear copy (`fires_bulk_op`: `cp.async`,
  `cp.async.bulk`, `st.async`/`red.async`) has a destination from `effAddr` of a shared or global
  space, `sharedEffAddr` (also a multicast's peer CTA) or `asyncStoreLoc`, which checks shared or
  global (`fires_copy_dst`; the element footprints of an element-wise copy are in the
  destination's space, `copy_elem_space`); a tensor load's tile is at its shared base, which the
  issue's route check asks to be shared (`fires_tensorIssue_base`, `TensorRoute`); a tensor store
  writes global memory (`Execution.store_writeLoc_global`); a CLC response is at its buffer from
  `effAddr` of `.shared` (`fires_clcIssue_response`). No Core change and no assumption.
- tml-fa4's `localWriteOwner` (old tree, from the kernel's code checks) is no longer needed by the
  new tree: lane T1 passes `localOwned hX` (or uses `local_read`/`local_read_byte`).

## Floating steps on a word whose number a `Pre` hypothesis gives (Phase 2, item 5)

- **The case.** tml-fa4's softmax negates the scale word at pc 4398 (`neg.f32 %r170, %r6072`):
  the register holds `.bits 32 x` (the launch word), Core's `neg` classifies the operand through
  its pattern, which does not evaluate on a symbolic `x`, and no assumption takes `neg`. The
  kernel's `Pre` gives the pattern's number (`scales : f32Value p.scaleLog2Bits = some s`, `0 < s`).
- **Library.** `Lemmas/Flow/FloatWord.lean`: `classify_word_f32` (a word whose binary32 number is
  `s ≠ 0` classifies as `.fin s`), `bitsAsFloat_word_f32` (it reads as the real `s`),
  `execLocal_negWord`/`execLocal_absWord` (Core writes the payload `-s` / `|s|`); in `SegSym.lean`
  the pieces `Seg.negWord`/`Seg.absWord` and the walk's `SymCtl.word`: at a `neg.f32`/`abs.f32`
  (no modifier) that does not evaluate, `seg_sym` looks for a hypothesis `f32Value e = some s` in
  context whose `e` is the source word's number (`x.toNat`, up to definitional unfolding), cuts,
  and takes the step by the piece (`s ≠ 0` from a hypothesis `s ≠ 0`, `0 < s` or `s < 0`; the
  role's `sym_local_none` must give `NoRuleAt` for the instruction, as for every Core step).
  Test: `Tests/Flow/FloatWord.lean` (tml-fa4 pc 4398, the negation of the scale word, one
  `seg_sym` call, 1.8 s).
- **What the role states.** The hypothesis in the word's form, once, before the walk (for tml-fa4:
  `f32Value (word).toNat = some s` from `Pre.scales` and `Pre.values`, the word being `< 2 ^ 32`).
- **Not covered.** A word read by an instruction that an assumption gives a rule (a `mul`/`fma` of
  the scale word itself under the ideal rules): the rule steps read operands through the
  assumption's `valFloat`, which needs the same reading inside `ruleStepProof`; not needed by the
  measured stretches (the softmax multiplies by the negated payload, a `.float` fact), recorded as
  the next extension (`bitsAsFloat_word_f32` is the lemma it would use).

## Merge of main with batch 21 (Phase 2, round 9 start)

- origin/main 0b44fb35f carries round 8 up to 2b5d67625 (squashed) and lane T1's safety split.
  Main's `Kernels/TmlFa4Fwd/Proof2/Lib/ShapeInit.lean` (`shape_mbInitAny` with a `shape_inv` rule)
  is deleted in the merge and `Proof2/Startup/Shape.lean` no longer imports it: 731ce134d promoted
  the lemma to `Lemmas/Flow/Step/ShapeClasses.lean` and `site_shape` tries it after `shape_mbInit`
  (same name in `PTX.Flow`, so keeping both would not build). Strict build of the merge rc=0
  (9876 jobs, 39 statement and axiom checks).

## Reading a launch word as its float in packs and rule steps (Phase 2, softmax request (a), item 4)

- **The case.** tml-fa4's softmax holds the exponent scale as the launch word
  `.bits 32 (paramW S)` (registers 7132, 7133). Besides the negation at pc 4398 (round 8), pc 4402
  packs it twice (`mov.b64 %rd738, {%r6072, %r6072}`) into the multiplier of all 64
  `fma.rn.f32x2` of the exponent stretch. Core's pack joins two words into one 64-bit word
  (`joinValue`: `.bits 64 (w ||| w <<< 32)`), and the packed `fma`'s ideal rule reads its halves
  through `classify` (`readERealPair`, `splitValue`), which does not evaluate on a symbolic `w`.
- **The hypothesis.** One form for every reading: `classify .f32 (.bits 32 w) = .ok (.fin s)` in
  context (from `Pre` by `classify_word`, or `classify_word_f32` from `f32Value w.toNat = some s`
  and `s ≠ 0`; a hypothesis in the `f32Value` form is converted by `wordHyp?` when `s ≠ 0`,
  `0 < s` or `s < 0` is in context too).
- **Library** (`Lemmas/Flow/FloatWord.lean`): `classify_word` (the softmax's
  `Proof2/Lib/FloatWord.lean`, promoted: a launch word `truncBits 32 n` whose number is `s ≠ 0`),
  `classify_bits32_mod` (`classify .f32` of a word reads only its low 32 bits),
  `readEReal_bits_fin` (the assumptions' reading of such a word is `s`), `pairRead_bits_or` and
  `pairRead_join_bits` (two joined words read as the pair of their readings when the low word fits
  in 32 bits; `truncBits_toNat_lt` gives that bound for a launch word), `execLocal_negWord` and
  `execLocal_absWord` now take the `classify` hypothesis (the round-8 forms took `f32Value` and
  `s ≠ 0`; their only user was `Seg.negWord`/`Seg.absWord`, not on main).
- **`seg_sym`** (`RuleStep.lean`): `erealRead?` reads a symbolic `.bits 32 w` through such a
  hypothesis (`wordHyp?`), so an assumption-ruled `mul`/`fma`/`add` that reads the word itself is
  a rule step (item 4 of this round); `pairReadProof?` reads a packed operand
  `.bits 64 (a ||| b <<< 32)` or `joinValue (.bits 32 a) (.bits 32 b)` whose words read that way
  (`wordPairProof?`), with the low word's bound by `word32Bound?` (a `truncBits 32` term, or a
  hypothesis `a.toNat < 2 ^ 32`). The `neg`/`abs` pieces use the same hypothesis search.
- **Tests and measurements.** `Tests/Flow/FloatWord.lean`: pcs 4399 → 4408 (the scaled
  maximum, the packs and two packed `fma`s whose multiplier is the word packed twice, their
  unpacks; 6 s with imports), an assumption-ruled `mul.f32` reading a word directly, and the
  negation of round 8 with its `f32Value` hypothesis (converted by `wordHyp?`). The softmax
  exponent stretch from the state the machine holds (scratch `.lake/own/libL/r10/E6.lean`,
  `E7.lean`: register 7132 as the launch word `.bits 32 (truncBits 32 (BitVec.ofNat 64 S))`, the
  `classify` hypothesis, `0 < (s : ℝ)`, the negated scale and row maximum as payloads, the 128
  scores as conditionals on abstract mask bits), one `seg_sym` call each: pcs 4399 → 4594 (the 64
  pack/`fma`/unpack triples) pass, 364 s and 10 GB for the file on the loaded host (round 7's run
  with the register as a payload: 350 s for the triples' walk); pcs 4399 → 4826 (the whole
  stretch to the first `tcgen05.st`) pass, walk 1276 s, file 1587 s, 27 GB (round 7 from a payload:
  walk 1271 s, file 1622 s, 27 GB). The reading costs nothing measurable; the stretch's split into
  files (softmax lane) is unchanged.
- **What the role states.** `classify .f32 (.bits 32 (paramW S)) = .ok (.fin s)` once before the
  walk (`classify_word hS h0 h32`), and `0 < (s : ℝ)` where a product with an infinite score is
  taken (the masked lanes).
- **Migration.** The softmax branch deletes its `Proof2/Lib/FloatWord.lean` when it takes lane L
  (same name `classify_word` in `PTX.Flow`); its `neg_scale` (pc 4398 by hand) can be one `seg_sym`
  call with the `classify` hypothesis in context.

## A return kind for packed pairs (Phase 2, softmax request (b))

- **The case.** tml-fa4's softmax loads its bias as `.bf16x2` words from shared memory that the
  loader's copies of the input filled: each element is the `bf16` payload of an unmasked bias
  element or the bits of the masked one (`.bits 16 0xFF80`, the Spec's `biasValue`). Core's
  `rebuild` returns two such 2-byte values as `.pair lo hi`, and two masked elements (both stored
  as bits) as one merged word `.bits 32 _` (`rebuildBits`).
- **`RetKind.packed fmt`** (`Lemmas/Flow/Fragment.lean`): accepts exactly the values
  `packedVal fmt` admits: a pair of two elements (`packedElem fmt`: a payload of `fmt`, its NaN, or
  a word of the format's width) or one word of twice that width. Both are Booleans, so a machine
  may test `packedVal fmt v` in its transition and `stop_cases` closes `stop_iff` by evaluation, as
  for the other kinds. Test: `Tests/Flow/FloatWord.lean` (a word of an unmasked and a masked bias
  element, and a word of two masked ones).
- No user of `RetKind` matches on its constructors, so the new constructor changes no kernel.

## Loads and stores whose undefined behaviour keeps its condition (Phase 2, item 2, lane T1)

- `shape_ld` and `shape_st` conclude `P e` from `P` of the read (write) and from `∀ f, P ⟨pc, .ub f⟩`,
  so a shape table built with them admits undefined behaviour at every load and store whatever the
  address, and `ref_safe` cannot be proved from `Ref`.
- `shape_ldM` (`Lemmas/Flow/Step/SiteShape.lean`) and `shape_stM` (`ShapeClasses.lean`) keep the
  condition: the load's undefined behaviour is `.misaligned` and only when Core's `elemAcc` fails
  (`w / 8 = 0` or the address not a multiple of `w / 8 * ds.length`); the store's is `.misaligned`
  under the same condition (over its sources) or the fault of `storeValue` when the source does not
  convert. A role's table states, for example,
  `e = ⟨pc, .rd …⟩ ∨ (loc.addr % n ≠ 0 ∧ e = ⟨pc, .ub .misaligned⟩)`, and `ref_safe` follows from
  the alignment in `Ref`.
- `site_shape` tries `shape_ld` first and then `shape_ldM` (and `shape_st`, `shape_stM`,
  `shape_store` for stores): a table that admits any undefined behaviour at the site is closed as
  before, and one that admits only the misaligned case falls through to the new lemma (a class
  lemma whose goals fail falls through since round 7). No existing table changes.
- `shape_close` introduces the condition of such an alternative (`intro`) before closing it, so the
  goal `cond → Ev d ⟨pc, .ub .misaligned⟩` is closed from a table alternative `cond ∧ e = …` by the
  same search. Not exercised by a kernel table yet (lane T1 states its loads'
  and stores' alignment when it proves `ref_safe`); the build of every kernel's shape files is
  unchanged with it.

## Safety by class over a role table (Phase 2, items 1 and 3)

- **The role table** (`Lemmas/Kernel/Safety/Table.lean`). A kernel's thread machines `C` (the
  glued roles) with a `RoleTable`: the invariant `J g d` of the role a state belongs to (tml-fa4's
  `RefAll`; false at stubs and at roles not followed yet) and the shape table `Ev g d`.
  `RoleTable.Ok T S` collects the three per-state obligations the classes need, each at a state
  satisfying `J`, for the threads `S`: `shape` (`Code.ShapeAt` unfolded, from `site_shape`),
  `safe` (`ref_safe`) and `death` (the `none` conjunct of `ref_next`). `RoleTable.Followed T X S`
  is "every state of a thread of `S` satisfies `J`" (`FollowedAt` at every position: the output of
  `followed_of_sources`, or of a kernel's `good_migrated` for its migrated warps).
- **Shape alone or all three.** `RoleTable.ShapeOk` is the shape obligation alone; `Ok` extends
  it with `safe` and `death`. An event that is no undefined behaviour is fired from a followed
  state with its shape by `ShapeOk` alone (`ev_of_ne_ub`, `forall_kind`: a dead machine fires only
  undefined behaviour), and every frame below is stated for kinds that exclude undefined behaviour
  (`forall_rel`), so a kernel uses the frames before its roles' `ref_safe` is proved (tml-fa4 today:
  `migrated_fires` takes the same "no undefined behaviour" premise). Only `noUb`, `noHasUb`, `dead`
  and `ev` for every event need `Ok`.
- **What follows for every event of a thread of `S`** (once, generic): it is fired from a followed
  state with that state's shape (`RoleTable.ev`), the machine is dead only after an exit
  (`RoleTable.dead`), no event is undefined behaviour (`RoleTable.noUb`), a per-shape condition
  holds of every event (`RoleTable.forall_ev`), and the instruction at the state's site fires it
  (`RoleTable.ins`, `RoleTable.sites`, for an event that is no undefined behaviour, from `ShapeOk`:
  tml-fa4's `migrated_fires` and its evaluated check over the reachable sites, for any table).
- **Why a table rather than `Fragment`.** The glued thread machine of a kernel (`Code.roleThread`,
  or tml-fa4's own `Role` glue) is not one `Fragment`: its states are the startup's, each role's
  and the stubs'. The table asks exactly the fragment obligations the classes use, per state of
  the glued machine, so a kernel states it by cases on the role of the state from its roles'
  `Shape`, `ref_safe` and `ref_next` facts (the stubs and unfollowed roles have `J = False` and owe
  nothing). The `Expect`/source part stays where it is (`followed_of_sources`), since it is what
  makes `Followed` true, not a class.
- **The table of a thread machine with roles** (`Lemmas/Kernel/Safety/Roles.lean`): for
  `Code.roleThread`, `roleJ JP JR` and `roleEv EvP EvR` read the first fragment's or the selected
  role's invariant and shape table (with the ledger's counts) and are empty at a stub;
  `roleThread_shape`, `roleThread_safe` and `roleThread_death` reduce the three obligations of
  `RoleTable.Ok` to one fact per fragment (the first fragment's shape only at its states that are
  not exits). A kernel on `Code.roleThread` therefore declares `JP`, `JR`, `EvP`, `EvR` and proves
  per fragment what it already proves for `Fragment.OkAt` (`shape`, `ref_safe`, the death clause).
- **Classes** (`Lemmas/Kernel/Safety/Classes.lean`), each one theorem from the table plus one
  per-shape fact (all but `noHasUb` from `ShapeOk`):
  - ERR-UNDEFINED-INSTRUCTION: `RoleTable.noHasUb` (`safe` and `death` only), for a table that
    follows every launched thread.
  - **Write frame** (item 3): `WriteOf e a` is the footprint an event writes, itself or through the
    operation it issues (a store, an atomic with a result, a linear copy's destination or element,
    a byte of a tensor load's tile or of a tensor store's box, a CLC response in a target CTA);
    `memWrites_writeOf`: every `MemWrites` of the execution (thread and asynchronous) is a `WriteOf`
    of its issuing event (by cases on Core's definition, no assumption). `RoleTable.write_frame`:
    a frame `W g a` stated per shape holds of every write issued by a thread of `S`;
    `RoleTable.noWriteIn`: no write covers a region no frame covers (a kernel's read-only input
    assumption's condition).
  - **Object frame**: `MbarOf`, `usesMbar_mbarOf`, `RoleTable.mbar_frame` (every `UsesMbar` is an
    object its event names), the basis of ERR-MBAR-UNINITIALIZED and the object lifetimes.
  - **Tensor Memory frame**: `TmemOf`, `tmemAccess_tmemOf`, `RoleTable.tmem_frame` (every
    `Tmem.Pair.Access` cell is one its event names), the basis of the Tensor Memory classes.
  - ERR-UNALLOCATED-ACCESS: `RoleTable.noUnalloc`, for a table that follows every launched
    thread, from three per-shape facts: the thread access footprints (`AccessOf`), the footprints
    of the asynchronous operations a shape issues (`AsyncOf`: an MMA's or `tcgen05.cp`'s shared
    bytes, a tensor load's, store's or prefetch's bytes, a CLC response, a linear copy's source,
    destination and elements, a bulk prefetch; `asyncFootprint_asyncOf` reads every
    `AsyncFootprint` off its issue event by cases on Core's definition) and the object frame
    inside the allocation.
  - ERR-TENSOR-FILL-VALUE and ERR-TENSOR-LARGE-OOB for roles that issue no tensor load:
    `RoleTable.noTensorIssue`, `noTensorUnsafe`, `noTensorBacking` (tml-fa4's `migrated_noTensor`
    by the per-shape fact instead of the sites check; both routes are available).
- **Not done as a class lemma** (each needs an order between the frame's writers and readers, not
  only the frame): ERR-DATA-RACE and ERR-MIXED-SIZE (the write frame plus the hand-off order of
  each region), the Tensor Memory resource/release/access/race classes (the Tensor Memory frame
  plus the allocation and hand-off order), ERR-SHARED-LIFETIME (last shared access before the
  exit), ERR-OBJECT-LIFETIME and ERR-MBAR-UNINITIALIZED (object frame plus the startup's
  publication), ERR-BARRIER-MISMATCH/ERR-CTA-BARRIER (named-barrier declaration),
  ERR-ALIGNED-MISMATCH/ERR-NONUNIFORM-GUARD (collective source on two lanes), ERR-SETMAXNREG.
  The frames are the per-shape half of each; the order half is the protocol layer (plan G7).
- **Checked on tml-fa4** (scratch `.lake/own/libL/r10/T9.lean`, not committed: it would couple
  `Tests/` to files lane T1 edits): main's `migrated_fires` is one call of `RoleTable.sites` with
  `T := ⟨RefAll p L, fun _ _ _ => True⟩` (no shape claim, so `ShapeOk` is trivial), `S` the
  migrated warps, `Followed` from `good_migrated`, the sites `migratedSites` and `pc_mem`; the file
  checks in 3 s.
- **How tml-fa4 uses it (lane T1).** `T := ⟨RefAll-by-role, Ev-by-role⟩` over `thread p L`,
  `S := fun g => 8 ≤ warpIndex L g ≤ 13` (the migrated warps; the loader and softmax warps join
  when followed), `Followed` from `good_migrated` (`good_state` gives the `FollowedAt` form).
  `migrated_fires` is `RoleTable.sites` with `migratedSites`; `migrated_noTensor` is
  `RoleTable.noTensorIssue` or the sites check; the field `noUb` becomes `RoleTable.noHasUb` once
  every warp is in `S` (until then, `RoleTable.noUb` for the migrated warps); `noInputWrite` is
  `RoleTable.noWriteIn` with each role's write frame (its stores' and copies' destinations from the
  shape tables) once every writing warp is in `S`.

## Promotions (Phase 2, item 5)

- Requests since round 8 (kernels' `DECISIONS.md` and the lanes' `Lib` folders; `p4b-epilogue-wire`
  and `tmlfa4-loader-proof2` name none beyond those promoted in round 8; FlashMLA has no new
  candidate):
  - tml-fa4 softmax (`tmlfa4-softmax-proof2`) `Proof2/Lib/FloatWord.lean` (`classify_word`) →
    `Lemmas/Flow/FloatWord.lean`, with the readings of request (a) (section above).
  - tml-fa4 softmax `Proof2/Lib/Counter32.lean` (loop counters on 32-bit words: `i32_addi`,
    `toSigned_r32`, `i32_toSigned`, `ne_m1`, `ne_0`, `scmpi_lt1`, `neg_eq`, the `toNat` forms,
    `sub32_swap`, the parity flip `xor_par`) → `Lemmas/Flow/Counter32.lean`, unchanged, namespace
    `PTX.Flow.Arith32`. No library module imports it: the MMA warp (`Mma/Ref.lean`) and the
    correction warps (`Correction/RefStep.lean`) on main keep private copies of `i32_addi`,
    `toSigned_r32`, `ne_m1` and the MMA file opens `PTX.Flow.Arith32`, so importing it there would
    make those names ambiguous. Each of those files switches by deleting its copies and importing
    the module; the softmax branch deletes its `Lib` copy.
  - Inkling pilot (worktree of `inkling-proof2`, not committed yet) `Proof2/Lib/Transfer.lean`
    (`Code.stepAt_map`: the step obligation along a map of states between two machines of one
    thread, for a machine whose sites are regrouped into families) → `Lemmas/Flow/Transfer.lean`,
    unchanged apart from its header. The pilot deletes its copy when it takes lane L (same name in
    `PTX.Flow`).
  - tml-fa4 lane T1's `migrated_fires` for any role table: `RoleTable.sites` (section "Safety by
    class over a role table").

## `Counter32` on main's tml-fa4 warps (Phase 2, item 4)

- tml-fa4's MMA warp (`Proof2/Mma/Ref.lean`) and correction warps (`Proof2/Correction/RefStep.lean`)
  import `Lemmas/Flow/Counter32.lean` and no longer keep their copies of `i32_addi`, `toSigned_r32`
  and `ne_m1`. `neg32_eq` stays in each file under its kernel name (it states the lemma for the
  kernel's abbreviation `neg32`) and is proved by the library's `neg_eq`. The correction file opens
  only the three names it uses (`open PTX.Flow.Arith32 (…)`), since it does not open the
  namespace; `CorrWarp/Fits.lean` opens the namespace and now resolves the names to the library.
- Branches that carry other copies (the softmax lane's `Proof2/Lib/Counter32.lean`) delete them
  when they merge main.

## The hand-off order and the classes on it (Phase 2, item 1, first part)

- **One form for every declared hand-off** (`Lemmas/Kernel/Safety/Handoff.lean`, `Frame.Handoff L X
  pair up uq`): for a pair `g ⇝ h`, an event of `g` whose producer use `up` is below the consumer
  use `uq` of an event of `h` happens before it (base causality). Uses are counts of the threads'
  events before the event, which a role's ledger keeps as fields of its states (`Frame.count_eq`),
  so a kernel turns a role-table state into a use by its ledger and the order into
  `baseCausality` by the declaration, with no protocol reasoning per region. Chosen over one
  structure per synchronization kind because every consumer (the region orders below, progress)
  needs only this shape, and hand-offs then compose (`Handoff.comp`).
- **Instances.** `Handoff.of_unit`: an mbarrier unit hand-off (`MbarRing.UnitHandoff`: rings of unit
  objects, `UnitRing`, `UnitGate`, `ObservedSync`; and the pair/single TMA rings' empty barriers,
  whose hypotheses `RingDecl.hyp` derives) with arrivals and successful polls less the offset as
  the uses. `Handoff.of_bar`: a named barrier whose participants arrive by either form, to its
  `bar.sync` participants, with the barrier's arrivals up to and including the event (producer)
  and before it (consumer) as the uses; it uses the library's `bar.arrive`-capable lemmas
  (`Sources.member_arrival_any`, `Sources.arrive_sync_baseCausality`), not the `NoBarArrive` ones,
  so tml-fa4's statistics barriers (softmax `bar.arrive`, correction `bar.sync`) are instances. Its
  premises are the participants' schedule: `bar.sync` only for the consumers, at most `N` arrivals
  per participant and exactly `N` for one that exits (a role fact at the exit site; it replaces
  `member_arrival`'s per-lane `hexited`). A CTA barrier is the named barrier `0` of every warp.
- **Not given as instances**: Tensor Memory commit/fence pairs and async-proxy fences order an
  asynchronous operation with a thread event (`modelCausality` through `ProxyBefore`,
  `ObservedCompletionBefore`, `AsyncChain`), not two thread events, so they are not `Handoff`s.
  They enter a region's order as the `later` field of `ItemOrder` below, from the existing protocol
  results (`StagingHandoff.Publish`/`Release` for a proxy fence and a tensor store, the ring
  libraries' copy/MMA orders); the Tensor Memory classes are not done (below).
- **Regions.** `ItemOrder L X R item` (accesses of the region numbered by items; conflicting
  accesses of one item ordered one way or the other; an earlier item's visible to a later one's)
  gives `ConflictsOrdered` (`ItemOrder.ordered`) for any access kinds; it generalises
  `StagingHandoff.Ring` (thread accesses and tensor-store reads only). For a region of thread
  accesses, `ConflictsOrdered.of_handoff` needs only the hand-off and the items: across items by the
  hand-off, within an item one thread's accesses by program order (`po_of_overlap`). ERR-DATA-RACE
  and ERR-MIXED-SIZE follow from regions covering every byte (`ConflictsOrdered.or`, `no_race`,
  `no_mixed`, as before).
- **The access frame** (`Classes.lean`): `intent_issuer` (every `Intent`, thread or asynchronous, is
  named by its issuing event: `AccessOf` or `AsyncOf`) and `RoleTable.intent_at` (that event is
  fired from a followed state with its shape, at its position): a region's accessors and their items
  are read off the issuing states. `RoleTable.forall_at` (`Table.lean`) is the positional form of
  `forall_kind`, for conditions that read the trace before the event (a use, an ordinal).
- **Schedules** (`Lemmas/Kernel/Safety/Schedule.lean`): ERR-BARRIER-MISMATCH
  (`noBarMismatch_of_schedule`, `RoleTable.noBarMismatch`), ERR-ALIGNED-MISMATCH
  (`noAlignedMismatch_of_schedule`, both clauses) and ERR-SETMAXNREG (`noSetMaxNReg_of_schedule`;
  `noSetMaxNReg_of_first` for threads with one request) from a function giving the operands of a
  thread's `k`-th event of the kind, equal within the group, plus the per-class count facts
  (exit totals for the aligned exit clause, monotone counts and Core's group clause for requests).
  The positional premises are what `RoleTable.forall_at` produces from per-state facts with the
  ordinal as a ledger count. Stated positionally (not only on a role table) because a kernel
  whose table does not follow every thread yet keeps the other threads' events as a premise, and
  the classes compare events of two threads.
- **Tested on tml-fa4** (scratch `.lake/own/libL/r11/T10.lean`, not committed: it imports old-tree
  files that the switch deletes): `Handoff.of_bar` on the statistics barrier `3 + w` with the old
  tree's `statsBarrierSources`/`statsBarrierShape` (the schedule premises left as hypotheses: they
  are the correction and softmax roles' facts); `ConflictsOrdered.of_handoff` over it; and
  `RoleTable.intent_at` on the migrated warps' table (every access a lane of warps 8 to 13 issues
  comes from a `RefAll` state at a migrated site). Each checks in seconds. The schedules are not
  instantiated: main's glued table has no per-role shape claims yet (`Ev = True`), so no barrier or
  request operands per state exist to give `B`/`R`/`P`.
- **Not done in this part**: ERR-NONUNIFORM-GUARD (`WarpDivergent` compares local walks, `Walk`
  visits, not events; it needs the machine's local segments related to Core's `Walk`), the Tensor
  Memory classes (resource, release, access lifetime, race: the Tensor Memory frame plus the
  allocation's publication and the commit/wait order of MMA writes, which are asynchronous–thread
  orders), ERR-SHARED-LIFETIME and ERR-MBAR-UNINITIALIZED / ERR-OBJECT-LIFETIME (the startup's
  publication through the CTA barrier as a `Handoff` from the initializing lanes; the classes'
  Core forms `SharedFinished`, `InitPublished` were not reduced to it in this round).

## Progress at a declared hand-off (Phase 2, item 2)

- **The blocker of a declared wait is an earlier producer** (`Lemmas/Kernel/Progress/Handoff.lean`).
  A hand-off on an mbarrier `m` (offset `δ`) gets a schedule `τ` against the kernel's time table
  (`Sched.Lag`): a waiter at a poll of `m` after `n` successful polls is no earlier than `τ n`
  (`wait`); a producer with `c` arrivals is earlier than `τ (c + δ)` (`early`); a producer that exits
  has made `U` arrivals and a waiter polls with fewer than `U + δ` successful polls (`exit`,
  `bound`). These are the per-role lag facts: each is one inequality of a role's time table at its
  states, read through its ledger (`Lag.prod_of_states` for the producer, from its states;
  `Lag.wait_of_count` for the waiter, from its ledger class). With them a short producer is a
  blocker (`Lag.blk`: not exited, earlier), and the object's declaration supplies the short
  producer when the poll fails: `Lag.pollBlocked_gate` for a gated unit object
  (`MbarRing.Unit.Gate`, through `Gate.blocked` and `unitsOf_eq_arrivals`), `Lag.pollBlocked_reach`
  for a unit object whose producers' arrivals follow the waiter's polls (`Unit.Obj.reach_short`);
  `Lag.steps_gate` is the descent step (`mbarAt_of`, `mbar_at_steps`).
- **Why a schedule `τ` rather than a pairwise time comparison**: the producer's and the waiter's
  tables are different roles' (`gluedTime` reads each role's table), and the only thing they share
  is the hand-off's use number; `τ` is the one function both compare against, so each role states
  its fact alone, and a kernel's progress at the wait is its time table, the object declaration, the
  waiter's `PollsOn` (`Frame.pollsOn_of_shapeAt` from its shape table) and the two lag facts.
- **Tested on tml-fa4** (scratch `.lake/own/libL/r11/T11.lean`): the output warp's ready poll is a
  `PollBlocked` thread from the ready barrier's `Gate` and a `Lag` (both as hypotheses: the gate is
  plan T3, which needs the correction warps followed), with `PollsOn` from main's
  `ready_pollsOn`, so main's premise `ReadyLag` reduces to these; the waiter's lag fact for
  `τ 0 ≤ tailBase p + 2 + 8 st` follows from main's `Out.time_ready` and the ledger in a few lines.
- **Not covered**: transaction objects (a TMA ring's full barrier, blocked by an outstanding copy:
  the asynchronous obligation's rank, `rank_async_lt`, already handles it) and named-barrier waits
  (`Progress/Bar.lean` has the barrier's own blocker lemma; its lag facts are the same `τ` form but
  were not restated here).

## Pilot and lane requests (Phase 2, item 3)

- **FlashMLA pilot (`flashmla-proof2`, its `Proof2/Lib/Steps.lean`: shuffles with a validity
  predicate, `.nc` loads, arrivals with a branching successor).** `site_step` now handles these
  itself. A shuffle whose second destination is a predicate and a load whose access is `.nc` are
  classes of their own, chosen from the instruction (`stepClass`), so the other combinators of the
  class are not tried first (on the pilot's sites those failing attempts cost minutes on a loaded
  host): `step_shfl_valid`, and `step_nc_sel`, `step_nc_first`, `step_nc_last_sel`. An arrival
  tries `step_arrive_sel` after `step_arrive` (the combinator, an arrival whose successor
  is any outcome including a dead thread, is in `Lemmas/Flow/Step/SiteCases.lean` because it
  names `DeadFrom`). The tactic bodies are the pilot's `shflv_step`, `nc_step`, `ncf_step`,
  `ncl_step`, `arr_step`, with the role's `trans` list in place of their per-site lists (a role whose
  `.nc` pair needs further unfolding lists those definitions in `trans`; `ncl_step`'s two extra
  lists become `trans`). `nc_load_ok` is a library macro. `seg_pre` (the role's segment hook) is now
  declared in `SiteCases.lean` (same namespace, so the name and every role's `scoped macro_rules`
  are unchanged; `SiteIte.lean` keeps the `lands_auto` rule that runs it), since the dead outcomes
  of these cases run it. The pilot deletes `Code.step_arrive_sel`, `nc_load_ok` and the five
  tactics from its `Lib/Steps.lean` and drops the overrides.
- **FlashMLA G1 (by-value parameter objects): `Flow.explicitObject L name decl fields`**
  (`Lemmas/Flow/ParamObject.lean`): the launch with an object's declaration and the little-endian
  bytes of the fields `(offset, value, width)` written out, `fieldBytes`, `leByteOf`, and
  `explicitObject_eq` (back to the launch from the declaration and the bytes). It is the pilot's
  `objL`/`objL_eq` with the field list as a parameter; the pilot's `objL L P` becomes
  `explicitObject L (param "0") (scalarsParam, P.param0Base) (p0fields P)` and `p0fields_ok` is
  the premise of `explicitObject_eq`.
- **FlashMLA G4 (wide and 64-bit forms): `Lemmas/Flow/Arith32Wide.lean`** (namespace
  `PTX.Flow.Arith32`, the pilot's `Lib/Arith.lean` plus tml-fa4's loader forms `mul64`, `zext`,
  `shrur`). Imported by no library module, as `Counter32`: tml-fa4's MMA warp has its own `neg32`
  (the `sub.s32 0, x` form, while this `neg32` is `neg.s32`'s) and its loader machine its own
  `r64`, `add64`, `sext`, `mulhi`, `mulWide`; a kernel that imports the module deletes its copies.
  Migration for tml-fa4's loader (owned by the loader lane): delete its 64-bit block and import
  the module.
- **Softmax lane (`tmlfa4-softmax-proof2`, `Proof2/Lib/UbFree.lean`): `Lemmas/Flow/UbFree.lean`**,
  unchanged apart from two names: its `elect_imm_ok` is the library's (`TmplOkSync.lean`, same
  statement, imported), and `effAddr_global` is `effAddr_global_bits` (the name
  `PTX.Proof.effAddr_global` exists with another statement; a file opening both namespaces would
  see two). The lane deletes its copy and renames its uses.
- **Inkling pilot (`inkling-proof2`)**: no request beyond `Transfer` (promoted in round 9). Its
  startup proves the second barrier and the shuffle by hand; its notes give the reason (a guard or
  a branch on a launch value the evaluation needs as a literal), not a missing library piece, so
  nothing was added.
- **FlashMLA G2 (alloc), G3, G9** (D-P2-GAPS). `site_step` has a class for `tcgen05.alloc`
  (`step_allocWr` for the write sub-step, else `step_alloc`; the lane-dependent successor is
  evaluated with the lane condition in `next_simp`). G3: `Code.step_load_dead`
  (`Step/Combinators.lean`): a load whose successor may be `none`, a thread that dies by its
  local steps after the load (the startup's read-back that reaches `trap`), as `step_shfl_dead`;
  `site_step` tries it after `step_load_sel`, so such a site's machine returns `none` (M1) instead
  of `some none`. G9: `lands_auto` (both the library rule and `SiteIte`'s) proves the successor's
  accumulator like its sub-step, by `rfl` or by splitting the successor's `if`s.
- **FlashMLA G6**: `shape_mbInitAny` was promoted in round 8 (731ce134d, `ShapeClasses.lean`);
  the pilot deletes `Lib/ShapeInit.lean` when it merges lane L.
- **Tested** in a temporary worktree (lane L plus `flashmla-proof2` plus the pilot's uncommitted
  index files, removed afterwards): the startup's steps (`Startup/Steps.lean`) check without the
  shuffle override (13 s on a host at load 200+). The index step files fail as they did in the
  pilot's work tree (its D-P2-MEASURE items 1–3: a cut point's predicate registers, the pair load's
  successor segment, the arrival's dead outcome before a division), so they do not test these
  cases yet; the `.nc` pair's successor segment fails there with the same `lands_auto: segment`.
- **FlashMLA G1 (`ld.param` of a by-value object through a register)**: `seg_sym` (its entry and
  `sym_close`) treats a context hypothesis `explicitObject L name decl fields = L` (or
  `explicitParams` of one, or the other way round) as it treated `explicitParams L ps = L`
  (`isExplicitLaunch`): it evaluates under the explicit launch (`Seg.launch_ex`,
  `DeadFrom.launch`), where the `ld.param` through the pointer register reads the written-out
  bytes. The pilot states one such hypothesis per role (from `explicitObject_eq` and `Pre`) instead
  of its scoped `seg_pre` rules.
- **`seg_sym` walks a site's preamble once** (the pilot's 460–690 s per step): the walk from a
  start (pc, facts, launch, dead mode) to its first symbolic point and the proof of that piece are
  kept for the file (`segWalkCache`, `segPieceCache`, `meta initialize` references). A later
  `seg_sym` from the same start (the next successor of the same site, which `site_step` splits
  into separate goals) reuses the walk when its own end was not on the walked path and the walk's
  facts are in scope, and reuses the piece's proof when its statement is the same and its free
  variables are in scope; nothing is trusted (the reused proof is checked like any other, and a
  walk that ended at a point that used a hypothesis, `SymCtl.word`, is not kept). Measured on the
  pilot's head step (test worktree): the second successor reuses the 1844→1845 and 1845→2334
  walks and pieces (8.3 s for the first walk, a few ms reused).
- **FlashMLA G5 and Inkling L-a: one role-layer extension, a dispatcher whose roles may return
  to it** (`Lemmas/Flow/LoopGlue.lean`, `Lemmas/Flow/Roles.lean`). `Code.loopGlue P R exit back`
  is `Code.glue` with returns: from a role's state that `back i` maps to a state `p` of the
  dispatcher `P` (the code jumped back to the dispatch loop's head) the machine runs `P` again from
  `p`, which may select another role; the dispatcher's states carry the round (`back` chooses
  `p`, so a role passes what it knows). `loopGlue_steps`/`loopGlue_sound` need `P`'s steps at its
  non-exit states, the roles' at their non-returning states, the hand-off at `P`'s exits, the
  hand-off at the returns (`Back`) and that no role's first state returns. `Code.roleLoop P R pcOf
  enterOf sel back` adds the gates and stubs of `roleThread` (stubs are `Code.stopAt`: invariant
  "the pc is an unguarded event instruction", so an entry's pc may depend on the launch; the check
  is in the hand-off, `hstub`), without a ledger, as a role of `roleThread` (whose ledger counts
  every event); `roleLoop_steps` is its obligation. Both pilots are instances: FlashMLA's
  warpgroup 1 is a `roleLoop` at the shared entry 1842 with `back` everywhere `none` (its first
  fragment follows the code's dispatch on the shuffled word, M1, so the pilot's stop on the word at
  1843 goes and the startup's reference invariant fixes the sub-role), Inkling's workers are a
  `roleLoop` whose dispatch fragment runs twice (role byte, then the exit byte) with `back` at the
  roles' jumps to pc 2337 (no copy of the dispatch fragment per round). `Code.glue` and
  `roleThread` are unchanged (tml-fa4 builds on them).
- **FlashMLA G8 (barrier with a register operand)**: `shape_barSyncR` (`ShapeTc.lean`, `bar.sync a`
  with the barrier read from any operand, no count); `site_shape` tries it after `shape_barSync`.
  The mbarrier poll's `internal exception #5` at the index's `wt` was not reproduced here (the
  index shape file is the pilot's uncommitted work); `shape_wait` is the class lemma it reaches.
- **FlashMLA G7** is a usage constraint, not a gap: a cut point takes the live registers' values
  from the end state's table, so the table covers the registers live at cut points of every path
  into the site, and a branch condition must be written as the code's term for `ite_cases`'
  hypothesis to decide it.
- **`stops_site`** (`StopReason.lean`) maps the new classes: the validity shuffle to the shuffle
  case, `.nc` loads and `tcgen05.alloc` to `stops_any`.
- **Inkling L-b/L-f** (`Lemmas/Flow/Transfer.lean`): `Code.stepAt_map` was promoted in round 9;
  `Code.atD_map` and `Code.fired_map` (the pilot's `fired_old` for any map keeping pc, facts,
  sub-step, accumulator and invariant) are added, so a regrouped machine's fired events are the
  flat machine's and its per-site shape lemmas apply.
- **Inkling L-g, followed up to a stub** (`Lemmas/Kernel/FollowedUntil.lean`): `followedUntil` and
  `followedUntilOn` (with `Q`, as `followedOn`): states of a set `S` (the stubs' states) owe no
  step, and a thread is followed with `J` at every position before which it has not been at a
  state of `S` (`Before`); `J` may include `S`, so the stub's own state is reached with `J`. The
  source obligation is `followed`'s with bad events outside `S` (`BadS`). With `S` empty
  (`before_of_empty`) it is `followed`; no machine changes.
- **Inkling L-d** (`site_norm`): a closed `Nat` or `Bool` term built from a `Fin` literal
  (`elPc i` at a literal `i`, a test of `k.val`) becomes its literal when it reduces to one (other
  terms are left as before).
- **Not done (recorded for the pilots)**: L-c (family equations of a transported successor: a
  `site_cases` mode proving a family's successor form once; the per-member evaluation stays the
  route), L-e (`machine_gen.py` beyond 32-bit forms: the vocabulary for 64-bit, `cvt`, division and
  16-bit forms now exists in `Lemmas/Flow/Arith32Wide.lean`; the generator does not emit it nor
  guarded instructions and branches yet), L-h (launch-input address facts for the block-table and
  query loads, and a protected-read source for the base word from the allocation's written word:
  both need statements about Inkling's addresses or Core's allocation result that are not generic
  library lemmas yet; the old `Interface.baseWordRead_of` stays until then), FlashMLA G8's poll
  shape (not reproduced).

## FlashMLA pilot, round 2 (D-P2-GAPS G5, G7, G10–G13)

- **G5, the dispatch word at pc 1843, without a content stop.** The stop belongs to no fragment:
  in `Code.roleLoop P R pcOf enterOf sel back` (warpgroup 1 at the shared entry 1842) the first
  fragment `P` covers the shared entry up to the code's dispatch (pcs 1842–1849: `setmaxnreg`, the
  warp-index shuffle that records the word, the dispatch tests) and follows every value of the word
  (M1: `P.next` never compares it); its exit states are the dispatch targets, and the word only
  selects the edge: `enterOf d` is the target pc the code branched to, `sel r d` the sub-role at
  that target (the index fragment at its entry, the MMA fragment at its entry, …), and a target with
  no migrated sub-role is a stub (`Code.stopAt`). So every fragment stops only on kinds
  (`Fragment.stop_iff` holds for `P` and for the index fragment, whose first state is after the
  dispatch), and the choice of fragment by the word is an edge of the fragment graph. That a lane
  of warp 7 goes to the index fragment and not to a stub is the startup's and the collective
  source's fact (lane 0 sends the warp index), used in the hand-off and in `followed`; while some
  target is still a stub, `followedUntil` (states of the stubs owe nothing) is the form, as for
  Inkling's softmax stub.
- **G7**: the documentation of `seg_sym` now says what it does: a cut point's facts are the
  walked state's values (the code's terms from the start facts), not the end's table. And
  `decideBool` tries, after the cheap check, a budgeted `isDefEq` at default transparency against
  hypotheses whose left side has the predicate's head (a tenth of `seg_sym.decideHeartbeats`), so
  a condition the role writes through its own abbreviation (`eqz64`) decides the code's
  `compare .eq .b 64 …` term.
- **G10**: `Code.step_arrive_fix` (successor written as `C.next d ⟨0, .exit⟩`, so `split` sees the
  transition's `if`s instead of a unified `Bool.rec`); `site_step` uses it for an arrival with a
  branching successor, with `split_ifs` before `split`.
- **G11, dead outcomes**: `dead_cut q H using tac` (`SegSym.lean`): dead states through a cut at
  `q` with a table's facts there (an ordinary segment to `q`, then the death). In `site_step` every
  dead outcome goes through `dead_close` = the role's hook `site_dead (seg)` (default: fail;
  `scoped macro_rules` per role, as `seg_pre`), else `seg_pre` and `seg_sym`; at a `.nc` pair the
  hook is tried while the transition is still folded (before the role's lemmas unfold it), which is
  the pilot's "late-unfold list" without a second list: `ix_dead` becomes the role's `site_dead`.
- **G12**: the transition's hypothesis is simplified with `↓reduceIte, ite_true, ite_false` in
  the arrival and `.nc` pair cases (an `if True` left by `simp` no longer reaches `split`).
- **G13**: besides the per-file cache (the second and later successors reuse the walk and the
  piece, round 10), `seg_cut q H using tac` cuts a segment once at a table's facts (the pilot's
  `pre_seg` + `Seg.comp_ex`): needed when the preamble's computed terms (bytes read through
  `explicitObject`) are not the terms the rest's conditions are written in.
- **A performance bug in the cache, fixed**: its scope check used `Expr.hasAnyFVar`, which walks a
  proof term as a tree; a cached proof is a DAG with much sharing, and tml-fa4's Epilogue
  `StepsTiles` stalled at the first reuse (over 30 minutes against 181–281 s). It now uses
  `collectFVars` (each shared subterm visited once); the same file then reuses the cached walk and
  piece at the next successor.

## Phase 2, round 11

- **Inkling L-h, the protected read over a role table** (`Lemmas/Kernel/Source/ProtectedRead.lean`).
  A load of a word that one declared writer `w` stored before a declared hand-off returns the
  stored bytes (`RoleTable.protected_read`), on top of `read_of_last_write`. The kernel declares:
  the order of `w` before the read at every byte (`modelCausality`: a `Frame.Handoff`'s base
  causality, program order, or Core's allocation-result order for the base word's lane), and one
  classification per shape (`RoleTable.WriteClass`): a write whose footprint meets the read's
  bytes, fired from a state of the table, is a thread write (`ThreadWrite`: a store or an atomic
  with a result) and is `w`, before `w` or after the read in base causality. The library turns the
  per-shape classification into the classification of every actual write of the bytes
  (`RoleTable.write_class`, `RoleTable.write_class_async`: an asynchronous write's issuing event
  is no thread write, `memWrites_async_issuer`). Writes of threads outside `S` (roles not migrated
  yet: Inkling's workers while they are stubs) are the kernel's (`hout`), and the table's
  following is needed only at the write positions (`hfa`), so a kernel inside its own following
  induction takes it from an earlier stage of `followed_stages` (an invariant that does not depend
  on the value read), as R4 requires; `protected_read_of_followed` is the form for a table that
  follows `S` everywhere. Instances waiting in Inkling: the base word (writer the allocation's
  store, order Core's `AllocResultBefore` for lane 0 or the second CTA barrier), the role byte and
  the `(num_pre, num_iters)` pair (writer the prologue's stores, order the dispatch barrier), the
  softmax's S/P/O words.
- **The allocation's word is not part of L-h**: the value the allocation's store writes is
  `Consistent.alloc512_result` (`Lemmas/Tmem/Alloc512.lean`, from a fault-free allocator history,
  `tmemNoFault_of_safe`), given the allocation's request record in the CTA's history. The record
  is `covered_record` of `Lemmas/Tmem/PairProtocol.lean` for `cta_group::2` warps; Inkling's
  allocation is `cta_group::1`, whose copy (`Proof/Protocol/TmemAlloc.lean`'s `covered_record`
  over `Tmem1Ops`) is kernel-local. Promoting the `cta_group::1` copy is recorded as a candidate,
  not done: no kernel asked for it.
- **Launch inputs** (`Lemmas/Kernel/Source/Launch.lean`): `LaunchReads mem0 X sites` is the one
  form of the kernels' read-only input assumptions over an input region `R` (`wf` of tml-fa4's
  `inputReadOnly` is it by definition with its `InputByte`; Inkling's, which names no region, by
  `LaunchReads.of_forall`), `LaunchReads.bytes`/`.value` read a launch value at a
  known address (the read's length from `Consistent`), and `elem_addr_lt`/`elem_addr_mod` say that
  an element of an array inside the 64-bit space does not wrap. The closed form of a block-table
  or query address stays the kernel's (its register table and gate): it is a fact about the
  kernel's address arithmetic, not a library one.
- Tested on Inkling's code (scratch `wt-libL/.lake/own/libL/r12/T12.lean`): Inkling's
  `inputReadOnly.wf` is `LaunchReads` (`hX.asm` and `of_forall`), tml-fa4's is by `rfl`, Proof2's `input_word` is
  `LaunchReads.bytes` in three lines, and Proof2's `BaseRead` statement for one read follows from
  `protected_read_of_followed` with the allocation's store writing the zero word.
- **Packed payloads with a masked pattern** (tml-fa4 softmax request, its DECISIONS "The bias
  words need a return kind"; `Lemmas/Flow/MaskedPack.lean`). One generic return kind,
  `RetKind.packedWith fmt p` (`packedWithVal`): a pair of two elements each accepted by `p`, or a
  word of twice the format's width whose two halves, as an unpack splits it (`splitValue`), are.
  The bias instance is `p = maskedElem .bf16 0xFF80` (a `bf16` payload or the mask; two masked
  halves rebuild into the merged word `0xFF80FF80`, which the kind accepts through its halves).
  A machine records each element as `Option ℝ` (`maskedReal`, `maskedPair`; `maskedValue` writes
  it back), and the two reading steps evaluate on every accepted value: the unpack
  (`exec_unpack_masked`: the two recorded elements, low half first) and the widening of one half
  (`exec_widenBf_negInf`: Core's rule widens the mask to `f32` negative infinity when no
  assumption selects the instruction; `coreWidenBf`, `execLocal_widenBf_core`,
  `classify_negInf_bf16`). A kernel assumption that rereads finite payloads (tml-fa4's
  `bf16Convert`) declines on the mask (`readFinite_negInf`) and reads a payload as itself
  (`readFinite_float`); `maskedWiden` is the widened register's value. `packedWith` was chosen over
  a `bf16`-and-mask constructor so that another format or mask is the same kind. Tested on
  tml-fa4's code (scratch `r12/T13.lean`): the unpack at pc 3505 and the widening at pc 3593 have
  the library's instruction forms, `bf16Convert` declines on the mask and writes the payload, and
  the kind accepts a payload/mask pair and the merged mask word and rejects another word.
  Step-file times (performance rule, `lake env lean`, three in parallel): before Epilogue
  `StepsTiles` 126.8 s, Mma 121.0 s, Correction 188.8 s (load about 95); after 101.0 s, 95.1 s,
  158.0 s (load about 45): no slowdown.
- **The remaining safety classes over a role table** (item 2). Each class is reduced to the
  frames of `Safety/Classes.lean`, the hand-offs of `Safety/Handoff.lean` and one fact per shape,
  with the part a frame cannot give left as a named premise:
  * **ERR-MBAR-UNINITIALIZED** (`Safety/Init.lean`): `RoleTable.noMbarUninit` (per state, a
    published initialization of each object a non-initializing event names; other threads'
    uses are the kernel's, `hout`) and `RoleTable.noMbarUninit_of_handoff`: the kernel names the
    initialization `ini g m` of every object of a thread's object frame (an `mbarrier.init` of a
    thread that hands off to `g`) and states per state that the use's consumer use is above the
    initialization's producer use (with `Handoff.of_bar` of the startup's CTA barrier: the
    initializer's barrier count `0`, the user's count before the use positive).
  * **ERR-NONUNIFORM-GUARD** (`Safety/Guard.lean`): the positions that are not poll branches
    (`WarpDivergentAt U`, which `not_warpDivergent_polls'`/`synced'` split off) from
    group-uniform values: `not_warpDivergentAt_of_value` (every record of a walk at a position of
    `U` has the guard value `G pc g` and the index `I pc g`, equal on a uniform group, so any two
    records agree, ordered or not) and `not_warpDivergentAt_of_inv` (the same from an invariant of
    every step, `Walk.inv`). Not on the role table: a guarded uniform instruction that is skipped
    fires no event, and a `bra.uni` is a local step, so the guard's value is a fact about the
    thread's states between events, which the machine abstraction does not state (its `AtD` is
    at sites). Recorded: a role-table form needs the segment layer's facts at the guarded pcs.
  * **ERR-SHARED-LIFETIME** (`Safety/Lifetime.lean`): `noSharedLifetime_of_own` for kernels whose
    CTAs use only their own shared memory: the other-CTA arm is empty by the own-CTA frame
    (`hown`, from `RoleTable.intent_at` and `mbar_frame`), every thread use is finished by
    program order before its thread's exit (`sharedUse_thread_event`: no shared use is an
    exit), and asynchronous uses are the kernel's completion chains (`hasync`, the lemmas of
    `ExitChain.lean`).
  * **ERR-TMEM-RACE** (`Safety/Tmem.lean`): `TmemItemOrder` (accesses numbered by items read off
    the issuing state's counts) gives `WritesSafe` and `ReadsSafe`; `RoleTable.tmemWrite_at`,
    `raceRead_at` (every write and race read of a cell is a `tcgen05` event fired from a followed
    state with its shape) are where the item is read. The orders across items (`WriteBefore`,
    `ReadBefore`: observed commits, `tcgen05.wait`, pipelined pairs) are the kernel's Tensor
    Memory hand-offs; a library form of "commit observed by a wait whose thread hands off" is not
    done (it needs `DoneBefore`'s chain, which T3's hand-offs will name).
  * **Not done**: ERR-OBJECT-LIFETIME (`TmaUnsafe`: object records, faults, accesses of object
    bytes) beyond the existing frames, ERR-TMEM-ACCESS-LIFETIME / RESOURCE / NOT-RELEASED (the
    allocation's lifetime: tml-fa4's MMA warp's `Mma.Startup`/`Mma.Ref` are the instance; a
    library statement needs the allocator history lemmas of `Lemmas/Tmem` over a role table),
    ERR-TMEM-READ-SOURCE and ERR-TC-MMA (values, by the kernels' assumptions).
  * **The instruction table** (`Safety/InsTable.lean`, lane T1's `migrated_fires` request for any
    role table): `RoleTable.ofIns C J`, whose shape is "the instruction at the site fires it"
    (`ofIns_shapeOk` by definition), so the frames and classes apply to roles whose shape tables
    are not stated, with per-instruction facts and `RoleTable.sites`.
  * Tested: on tml-fa4's migrated roles (scratch `r12/T15.lean`: `RoleTable.ofIns (thread p L)
    (RefAll p L)` over warps 8 to 13 with `good_migrated` as the following; `noMbarUninit`
    reduces to the per-state publication, a Tensor Memory write of a migrated lane is fired from a
    followed state (`tmemWrite_at`), `noSharedLifetime_of_own` instantiates). tml-fa4 has no
    guarded uniform instruction other than its poll branches (`pollGuardsOk` evaluates to true), so
    the guard lemma is tested on Inkling (scratch `r12/T14.lean`): the old tree's
    `Wq.not_divergentAt` (30 lines) is `not_warpDivergentAt_of_value` with its invariant `GOk`
    in 15.
- **Promotions requested since round 10** (item 4), each file moved with its statements
  unchanged:
  * Inkling `Proof2/Lib/Kill.lean` → `Lemmas/Flow/Kill.lean` (`Code.killAt`, `Code.StepAt.kill`,
    `plainLoad`, `dead_of_load_error`); `Proof2/Lib/SharedSym.lean` →
    `Lemmas/Flow/SharedSym.lean` (`memTmpl_sharedSym`, `fires_ldv_sharedSym`);
    `Proof2/Lib/NotVote.lean` → `Lemmas/Flow/NotVote.lean` (`fires_vote_op`, beside
    `NotShfl.lean`); `Proof2/Lib/SegPieces.lean` → `Lemmas/Flow/SegPieces.lean` in `PTX.Flow`
    with the names `run_guardSkip`, `run_braNot`, `run_brxIdx`, `Seg.guardSkip`, `Seg.braNot`,
    `Seg.brxIdx`: the old tree's `WorkerBase` declares `Seg.skip`, `Seg.bra_neg`, `Seg.brx` in
    `PTX.Flow`, so the promoted names differ and a module may import both.
  * tml-fa4 `Proof2/Lib/LocalSrc.lean` → `Lemmas/Kernel/Source/LocalSrc.lean`
    (`Frame.local_read_src`, `WordByte`, `rebuild_word4`); lane T1's `Proof2/Lib/NoUb.lean` →
    `Lemmas/Kernel/Safety/NoUb.lean` (`Frame.noUb_of_followed`); `Proof2/Lib/WordBound.lean` →
    `Lemmas/Flow/WordBound.lean` (bounds of the code's 32-bit words).
  * No library module imports them, and no kernel on main does yet: a kernel that keeps its own
    copy (same names) deletes it when it imports the library's, as for earlier promotions.
  * Already in the library: T4's `fires_wait_reg_al` (`Step/ShapeRegs.lean`) and `PollsOn`
    (`Progress/PollsOn.lean`); Inkling's `Lib/Sink.lean` is gone from its branch
    (`followedUntil`).

## Pilot requests during round 11

- **FlashMLA G3' (`step_load_dead`'s death case)**: `dead_close` now puts the branch hypotheses a
  `split` leaves as `¬ (b = true)` into `b = false` (`Bool.not_eq_true`, the form `seg_sym`
  decides a predicate by) and reduces the start facts `(r, v) :: dropReg r (C.facts d)` with
  `drop_norm`, as `lands_auto` does for a successor. Every dead outcome of `site_step` goes through
  `dead_close`, so the change applies to the shuffle, `.nc` and arrival deaths too.
- **FlashMLA G11' (`site_dead` at the wrong unfolding depth)**: `site_step` and `site_cases` take an
  optional `dead_trans [lemmas]`: the lemmas that unfold the transition in a dead outcome (default:
  `trans`). A role whose `site_dead` needs part of the transition folded (FlashMLA's
  `Index.dead_body`, which needs the block's `body` folded) lists only the outer definitions. The
  arrival's dead outcome now tries `site_dead` before any unfolding as well, as the `.nc` pair did.
  The role-given list was chosen over trying `site_dead` after each single unfolding step: the
  latter multiplies the hook's attempts by the length of `trans` at every dead outcome of every
  role.
- Not tested on the pilot's own cases (its stop at startup pc 92 and its local `ncl_step`/`arr_step`
  are in its branch; switching them is the pilot's step). Regression: the strict build of every
  kernel on main, and the three tml-fa4 step files of the performance rule.
- **FlashMLA `zext16w`**: `Arith32Wide.zext16w` (`cvt.u32.u16` of a register that already holds a
  16-bit word, Core's evaluation there) and `zext16_eq_zext16w` (the two forms agree on a 16-bit
  word); the pilot deletes its copy when it imports them.
- **Inkling L-i, following along a state map** (`Lemmas/Kernel/StateMap.lean`): `StepMap C' C φ`
  (first state to first state, successors to successors, stops and deaths included),
  `stateAt_map` (the state of `C` is the image of the state of `C'`), `stateAt_map_some`,
  `followedAt_map` (a thread `C'` follows with `J'` is followed by `C` with the image of `J'`),
  and the instance `StepMap.counted` (forgetting a ghost ledger). Tested on tml-fa4 (scratch
  `r12/T16.lean`): the migrated lanes followed by the counted `thread p L` are followed by
  `glued p L`.
- **Inkling L-j, the guard class under `pollAgree`** (`Safety/Guard.lean`,
  `not_warpDivergent_pollAgree`): when an assumption selects every poll branch with `uniPoll`,
  every disagreeing pair at a poll branch whose polls use one object is exempt, so the premises
  are the guard positions (`¬ WarpDivergentAt U`, from `not_warpDivergentAt_of_value`) and
  `PollObjUniform` (one object per poll position across a warp), with no order between the lanes.
  Tested on Inkling (scratch `r12/T17.lean`: with its `Wq.lane_ok` and `Wq.not_divergentAt` the
  lemma leaves `PollObjUniform` and the selection of every poll branch; checking the selection by
  evaluation over the whole code did not finish in 19 minutes, so it is a premise in the test). For polls whose object changes with the round (Inkling's rings),
  `PollObjUniform` does not hold and `not_warpDivergent_synced'` with `PollSynced` (polls of one
  position at different objects ordered) stays the route; deriving `PollSynced` from a ring's
  hand-off is not done.
- **Inkling L-k, L-l**: the Tensor Memory race classes (`Safety/Tmem.lean`) and the mbarrier
  initialization (`Safety/Init.lean`) of item 2 above.
- **Lane T1 (1), `shape_ldM`'s condition and `site_shape`'s error** (a library bug): the shape goals
  are first simplified by `MemAccess.regs`, `List.filterMap_cons/_nil`, `id_eq` and the list
  lengths, so a misalignment condition `loc.addr % (w / 8 * ds.length) ≠ 0` with `ds` the literal
  instruction's registers becomes `addr % 4 ≠ 0` and meets the table's condition; and when every
  inversion lemma of a site fails, `site_shape` reports each lemma with its error (it reported the
  first one's, `internal exception #5` from `try_rt`).
- **FlashMLA G14 (`.nc` read whose element index stayed `t.sub`)**: the side goal `t.sub = j` of
  `shape_ld`/`shape_ldM`/`shape_ldNc` is closed first by `rw [hat.2.1]; site_norm; rfl`, so `j` is
  the site's literal sub-step rather than a projection of the state (or `t.sub` itself, which a
  later alternative assigned by `rfl`). Same family as (1): an unreduced term in a shape goal.
- **Lane T1 (3), `mbarrier.init` with a register count**: `shape_mbInitR` (`ShapeClasses.lean`, the
  aligned object at the address register with the count register's word), tried by `site_shape`
  between `shape_mbInit` and `shape_mbInitAny`.
- **Lane T1 (2), the zero row-sum path (HIGH)**: `rule_step` (the step of a floating instruction at
  a cut, `RuleStep.lean`) now (a) decides the conditions a rule's body still branches on from the
  hypotheses in context (`ruleDecideConds`: `assumption` or `linarith` on a goal of its own, then
  `if_pos`/`if_neg`; tml-fa4's `lg2` rule `if 0 < x` on a row sum that a hypothesis makes `0`
  declines), and (b) when every assumption declines, takes Core's rule through the hook
  `rule_core` (scoped `macro_rules`, as `seg_pre`), whose library rule is `lg2.approx` of a payload
  that a hypothesis makes zero (`Lemmas/Flow/Lg2Core.lean`: `lg2I`, `execLocal_lg2_core`,
  `execLocal_lg2_regs`, `classify_f32_zero`, `coreFloat_lg2_zero`, `coreFloat_lg2_eq_zero`,
  `exec_lg2_zero`: Core's table gives `f32` `-inf` on `+0`). The `fma` and `mul` that read the
  infinity under `idealArith` were already in `rule_step`'s simp set (`readEReal_lit`,
  `mulEReal_bot_pos`, `addEReal_bot_coe`).
- **Inkling L-m, the first `n` instances of a barrier** (`Handoff.of_bar_upTo`): `of_bar` with the
  consumer's use capped at `n` (`min (uses before the event) n`) and, of the barrier's schedule,
  only that a participant that exits has arrived at least `n` times; `of_bar`'s bound over whole
  traces (`hN`) and its exact exit count are gone. The barrier's `NamedBar.Sources` and `Shape`
  (every event of the barrier has its count and is a participant's) are still asked of the whole
  execution: they are facts of the code's barrier instructions, which the instruction table or a
  coarse stage gives without the word.
  Tested in a temporary worktree (lane T1's `54d9bb895` with its saved `zero-sum.patch` and this
  library, removed afterwards): `rule_step` now decides the `lg2` rule's condition at 9075 from the
  sign hypotheses and declines on a zero sum. Two things remain there, recorded for lane T1: the
  branch `¬ (0 ≤ rs0 ∧ 0 ≤ rs1) ∧ 0 ≤ rs1` leaves `0 < rs1` undecided (`rs1` may be `0` or
  positive: the patch does not split it), and the three zero cases at `fdone 1 1` still fail inside
  `site_step` with `internal exception #5` (a runtime error that `try_rt` turns into a failure),
  so their remaining step is not located yet; the next run with this library shows it.
- Step-file times for these tactic changes (performance rule, `lake env lean`, three in parallel):
  before Epilogue `StepsTiles` 105.0 s, Mma 97.4 s, Correction 155.5 s (load about 52); after
  96.0 s, 89.5 s, 141.4 s (load about 17): no slowdown.
- **Inkling L-e, the value-table generator beyond 32-bit forms** (`Tools/machine_gen.py`): the
  generator writes `Lemmas/Flow/Arith32Wide.lean`'s vocabulary for 64-bit `add` (register or
  immediate), `mul.lo`, `shl` and `mov`, `mul.wide.{s,u}32` (immediate or register),
  `cvt.s64.s32`/`cvt.u64.u32`/`cvt.u32.u16`/`cvt.s32.s8`, `mul.hi.s32` by an immediate, `div.u32`,
  `max.s32`, `or.b32`, `neg.s32`, shifts by a register, 16-bit literals and `xor` with 1; an entry
  has its instruction's width (`.bits 64`, `.bits 16`, the `cvts8` value). A guarded instruction
  whose destination the stretch assigns once writes `sel` of its guard, the new value and the
  register's value before the stretch (declared under `before`). Branches still stop it: a table
  mirrors one straight-line path, and a stretch across a branch has a value per path, which the
  role's table states per site (recorded, not done). Tested: unit tests of every new form
  (`tests/test_machine_gen.py`), and against a kernel: `Tests/Gen/loader_setup.json` generates
  the tml-fa4 loader setup's two stretches (pcs 415–418 and 423–484, from the PTX alone) and
  `Tests/Gen/LoaderSetupCheck.lean` shows by `rfl` that every register of the loader's
  hand-written `Loader.setup` (the page-table and K/V base addresses by `mul.lo.s64`, `shl.b64`,
  `add.s64` and `cvt.s64.s32`, the head division by `mul.hi.s32`, the block counts by signed
  shifts, `min.s32`, `max.s32`) is the generated entry. Inkling's flat prologue table can be
  regenerated from the PTX where its stretches are straight-line.
- **Inkling L-c (family equations of a transported successor)**: not done this round (the
  requests above came first); recorded as before.

## Phase 2, round 12

- **The zero row-sum path (lane T1, priority 1).** Found with `try_rt`'s caught errors (an
  instrumented copy in a temporary worktree): "internal exception #5" is Lean's `abortTactic`,
  which an elaboration throws after logging an error under error recovery; `try_rt` restored the
  state and so dropped the log. Along the walk 9056→9073 (and 9074→9077 for the second sum):
  * `lg2.approx` at 9061/9075: the kernel's `lg2` rule declines on zero (round 11's condition
    decision), and the Core fallback `rule_core` failed because its `refine` left the lemma's
    implicit value as a natural metavariable (`execLocal_lg2_regs (v := ?val) ?hr` now) and its
    `case hr => assumption` ran under error recovery (the library rule is `rule_core_lg2`, a
    `first` whose alternatives throw instead of logging);
  * the `fma` at 9062/9076 left `↑(scale · rm) + ⊥` and the `mul` at 9063/9077 read the result
    back as `FVal.toValue .f32 (.inf true)`: `rule_step`'s simp set now has `coe_add_bot`,
    `coe_add_top`, `addEReal_coe_bot/_top`, the signed `mulEReal_{bot,top}_{pos,neg}` with a
    discharger (`assumption`, `norm_num`, `positivity`), and the `f32` infinities as the bit
    literals `readEReal_f32_ninf/_pinf` read (`erealValue_f32_bot/_top`);
  * the condition decision used deprecated `if_pos`/`if_neg` (warnings, so a strict build of a
    kernel that reaches them fails) and, for `setp.ne.f32` at 9074, a `simp` with `eq_true pf`
    that looped; it now rewrites with `ite_eq_left`/`ite_eq_right` (`dite_eq_left/_right`), and
    the proof search ends in `fail` so that no alternative runs under error recovery.
  * the three `fdone 1 1` zero cases then showed (with the reporting below) two more steps: a
    fact `0 = v.rs1` of the role's case split, restated by `realFacts` as a simp lemma, rewrote
    every numeral `0` of the rule's body into `v.rs1` (`realFacts` now restates an equation with
    a numeral on the left as `x = 0`); and the table's LSE value `if erealCompare .ne ↑rs ↑0 then
    … else -inf` left a branch whose condition only the real facts refute: `sym_close` now
    refutes such a branch by the comparison as a real (in)equality and `linarith`, and
    `sym_decide` has the same rule for a decision.
  * **Reporting.** `try_rt` reports the errors an aborted elaboration logged (it reported
    "internal exception #5" and dropped them); `site_step`'s class alternatives run through
    `first_report`, which runs each alternative without error recovery and, when all fail,
    reports every alternative's error (the one meant for the site was hidden behind the last
    alternative's). `step_arrive_fix`'s instruction is a goal of its own (`refine'` and `case hc`)
    instead of a `by` inside the term.
  * **Roles extend `rule_step`'s simplification** with the hook `rule_simp` (scoped
    `macro_rules`, as `seg_pre`), run after the library's lemmas.
  * **Confirmed** in a temporary worktree (lane T1's `8b827e315` with its saved `zero-sum.patch`,
    the `rs1 = 0` split added to `stepAt_lse`'s branch `0 ≤ rs1`, and this library):
    `Proof2/Correction/StepsLse.lean` builds, every zero case included (665 s on the loaded host,
    against the audit's 60 s rule: a target of the reflection redesign below). What lane T1
    applies: the patch with the split (its `zero-sum2.patch` has it) on this library; the
    `EReal.add_bot`/`mulEReal_bot_pos` lemmas it passes by `using` are now in `rule_step`'s own
    simp set and can be dropped.
- **`Frame.noUb_of_followed` replaced** by lane T1's `noUb_of_followed_live`
  (`Safety/NoUb.lean`): the `live` obligation only at events that are no undefined behaviour.
  `stv_off_ok` promoted (`Lemmas/Flow/StoreOff.lean`).
- **ERR-OBJECT-LIFETIME** (`Safety/Object.lean`): `noTmaUnsafe_of_first` (no invalidation, each
  object initialized first once without fault, the initialization published to every other
  record's issue, other records fault-free, no access of object bytes, no `cp.async` overlap or
  unallocated masked range) and `noTmaUnsafe_of_noCopy`; `RoleTable.noObjectAccess` gives the
  access part from the access and object frames.
- **ERR-TMEM-RESOURCE, ERR-TMEM-NOT-RELEASED for `cta_group::1`**: Inkling's
  `Proof/Protocol/TmemAlloc.lean` promoted as `Lemmas/Tmem/Tmem1Protocol.lean` (`PTX.Tmem.One`;
  tml-fa4's allocation is `cta_group::1` too, pcs 1909/2763/2766), and
  `RoleTable.tmem1Facts` (`Safety/TmemAlloc.lean`) derives its facts from per-state facts of a
  role table; `tmem1_safe` gives both classes. ERR-TMEM-ACCESS-LIFETIME is not done.
- **PollSynced from rounds**: already in the library (`Lemmas/Flow/PollRounds.lean`,
  `PollSynced.of_rounds`); what a ring needs is `PollRoundsMet` (two lanes' polls in different
  rounds ordered), which follows from a per-round warp collective's witness edges
  (`DepStep.of_witness`); that derivation is not done this round.
- **Inkling's two-group barrier hand-off** (`BarFirst.lean`, `BarEarly*.lean`) promoted:
  `Lemmas/Protocol/NamedBarEarly.lean`, `NamedBarEarlyMember.lean`,
  `Lemmas/Kernel/Safety/HandoffEarly.lean` (`Handoff.of_barEarly`).
- **Generator branches** (`Tools/machine_gen.py`): a stretch follows one path; an unguarded branch
  jumps, a guarded one goes the declared way (`"branches": {"<pc>": true}`), and an undeclared
  guarded branch, an indexed branch, a loop or a path leaving the stretch stops it.
- **Inkling L-c**: `fin_family` (`Lemmas/Flow/Step/Family.lean`): a family form `∀ k, …` proved
  member by member (`fin_cases`, then `rfl`, `site_norm`, or the role's lemmas).
- **Done before lane L2 took them** (G15, G16, G17, G19, G20): `site_acc` closes an alignment
  branch by `omega` from a fact in context; `step_nc_*` accept die-or-stop on bytes that do not
  rebuild; `Arith32WordWide.lean` (`max32_W`, `neg32_W`, `sub32_W_mod`, `and_negpow`,
  `andi_W_negpow`, `slot_update_W`); the arrival successor's false branches
  (`Bool.false_eq_true`, `contradiction`). G19: lane L2's `NotMbarAt`/`Code.fired_notMbar_at`
  (over the existing `arriveOp`/`waitOp` classifiers) is kept and lane L's `NotMbar.lean`
  (a second classifier, `Op.isMbarAW`) removed at the merge of laneL2: one classifier.

## Round 12: runs checked against stated values (reflection evaluator)

- **Design** (`Lemmas/Flow/OutLit.lean`, `Tools/out_gen.py`): a straight-line run of local
  instructions is proved piece by piece by `SegD.outs_lit`, the existing `SegD.outs` (one
  soundness proof, `OutRun.lean`; no new trust) with literal facts at both ends. The generator
  reads the PTX and writes, per written register, a `def` with the term the code computes (in
  terms of the values `V` at the start of the run: the run is a template over its start values),
  the facts at every cut (every 32 instructions) as lists of those defs, and per piece the proof:
  item by item the code lemma `Flow.code_<pc>` and the role lemmas the declaration names (segment
  freedom and the assumptions' reading, each by a literal side condition closed by `rfl`), the
  reads, requirements and coverage as Boolean checks by `kernel_rfl`, and the end facts by
  `kernel_rfl` (evaluation of the items over the start facts against the stated terms). Each
  piece is checked from its own start facts only; `SegD.comp` composes them. No step searches.
- **What stays with the role**: the condition of each piece (`oCond`: no outcome faults; the run
  is dead otherwise), the equalities of the stated terms to mathematical forms (the result layer),
  and moving the start facts to its table's (`SegD.of_lookup`).
- **A role's own reading**: runs are lists of `XItem` (`OutRun.lean`): an `OItem`, or
  `XItem.fn op d srcs f`, any local instruction with one destination whose outcome on its
  sources' values the assumptions give as `f` (its `Rule`: for every value function agreeing with
  the sources' registers, the local step is `f` of their values). tml-fa4's `bf16Convert` reading
  of `cvt.rn.bf16x2.f32` at the probability-pack sites is such an `f`. Not a constructor of
  `OItem`: FA4's `rule_pc` proves every `OItem`'s reading outside its segment sites, which an
  arbitrary `f` would break. The step and run proofs are `XItem.step`/`xRun`/`SegD.xouts`;
  `OItem.step`, `oRun` and `SegD.outs` are now their instances on `.base` items (statements
  unchanged), so there is one run proof.
- **Measured** on tml-fa4's exponent stretch, pcs 4399–4825 (427 instructions: the scale product,
  64 packed `fma`, 128 `ex2.approx.ftz`, 64 `bf16x2` conversions, 170 moves; test
  `Tests/Gen/Out/Expo.lean` from `Tests/Gen/Out/expo.json`, readings in `ExpoRules.lean`):
  14 pieces, the file builds in 16 s in the strict build (`lake env lean` 18 s wall, peak
  resident 3.7 GB of which about 3.2 GB is the imports), sequentially 0.2–1.5 s per piece
  (1.4–1.5 s for full 32-instruction pieces), 0.02 s for the composition. The same stretch by
  `seg_sym` (round 7 scratch) took about 1,300 s. First version: 3.5 s of each piece's 5 s was the
  elaborator evaluating the Boolean list checks; they are kernel checks now.
- **Not done**: per-lane templates over a family index (the run is already a template over its
  start values, and at 1.5 s per 32 instructions the per-piece cost is no longer the bottleneck);
  the audit's per-pc step lemmas for every instruction kind in site-machine segments (items 1, 4,
  5, 6, 8, 10 for `seg_fp`/`sym_close`/`seg_auto`/`next_simp`/`rule_step`/`realFacts`). The
  pieces here are the pattern for them: stated successor values, checked by evaluation, composed.

## Round 12 (lane L2): the kernel pilots' requests G15–G20 and a segment step in `seg_sym`

- **G19 (a ledger needs no shape at the sites that are not mbarrier operations)**. The library
  already inverted an arrival and a poll from the instruction (`NotArrive`/`NotWait`,
  `eventTmpl_notArrive`/`eventTmpl_notWait`, `arrivesOn_of_arriveOp`, `okPoll_of_notPoll`). Added:
  the classifier of polls `waitOp` (`NotWait.lean`, beside `NotArrive`'s `arriveOp`) with
  `waitOp_ne`; `okPoll_of_waitOp` (`Polls.lean`, `arriveOp`'s counterpart); the site-level
  `NotMbarAt K pc` (`∀ ins, K.code[pc]? = some ins → arriveOp ins.op = false ∧
  waitOp ins.op = false`) and `Code.fired_notMbar_at`/`Code.fired_notMbar` (`Ledger.lean`):
  from a followed state's event and a pc-level classifier, no shape, both counts are `false`.
  A kernel proves `NotMbarAt` once per instruction form (`intro ins hc; rw [code_<pc>] at hc;
  obtain rfl := Option.some.inj hc; exact ⟨rfl, rfl⟩`), as it proves `NoRuleAt`. Tested on the
  tml-fa4 output warp (`Tests/Flow/MbarFree.lean`): the `.nc` load at pc 2953 and the tensor
  store at pc 2963 are `NotMbarAt`, so no event fired at their `.q0`/`.store 0 0` sites is an
  arrival or a poll; pc 2958 (`mbarrier.try_wait`, the `.ready 0` site) is not `NotMbarAt`.
  The arrival and poll counts are `arrivesOn`/`okPoll`, so a kernel whose ledger counts the
  events of other kinds still states its sites; the lemma is for the arrival and poll ledgers
  (the pilot's `Cls` with `ready s`/`free s`).

### A kernel-assumption segment (`swExp2`) as one step of `seg_sym` (item 6)

The pilots need `seg_sym` to take a kernel-assumption segment (`Assumptions.swExp2` at tml-fa4's
softmax pcs 7090, 7121, …, FA4's software `exp2`) as **one** step, as the old `SoftmaxExponent`
lemmas do, instead of walking its 31 instructions with Core's rules (which gives the bit pattern
and loses the exact `2 ^ x` reading).

**The segment's values cannot be computed by the walk.** `execSwExp2`/`execSegment` read the
lanes through `readReg`, so their result depends on the registers' *values*; the walk's symbolic
state has opaque `R r` for registers it does not know, so `whnf` cannot reach the `Exec.ok` the
walk would need (probed: `execSwExp2` reduces on literal lanes but not on the walk's state). The
old proofs state the lanes' numbers and prove the step from them (`softwareExponentValues`), and
that statement is irreducibly part of the kernel's proof.

**Design: the kernel states the piece, the walk glues it.** Two `Seg`-level lemmas
(`Lemmas/Flow/Segment.lean`):

* `Seg.segStep` — the instruction form: `K.code[pc]? = some ⟨none, op⟩`, `op.isLocal`, and, for
  every state at `pc` whose registers satisfy `F`, the step is an `ok` at `b` with the facts `G`.
  This is the form a kernel uses when it has the step's `execLocalA`-level proof.
* `Seg.segRunStep` — the run form: for every such state, `run K A L g 1 ⟨pc, R, cf, 0, [], none⟩
  = some u` with `u` at `b` (sub/acc/fault reset) and the facts `G` in `u.regs`. This is the form
  the old `SoftmaxExponent` lemmas produce (`softwareExponentValues` gives exactly such a `run`
  equation), so a kernel writes one such statement per segment site.

`seg_sym` (`Lemmas/Flow/Step/SegSym.lean`) then takes it as a step of its walk:

* `SymCtl.seg b G hstep` — the walk's cut for a segment step, with the stop `b`, the facts `G`
  there, and the hypothesis `hstep` that proves the piece.
* `segHyps` — the segment steps the local context states, scanned **once per walk** into a map
  from start pc to `(stop, facts, proof)`: a hypothesis `∃ n, Seg K A L g n pc F b G`. The walk
  checks the map at each instruction, so the cost is one context scan per walk and no per-step
  unfolding of the kernel's assumptions. The map is not consulted per step on the assumptions'
  `segmentRule`s: evaluating a rule (a template match on the code) is what the walk cannot do for
  the segment's values anyway, and a kernel that states no piece keeps the walk it had.

If a piece is stated for a pc the walk reaches, the walk cuts there; if a kernel *does* have a
segment assumption at a site and states no piece, the walk takes the instructions as before (and
the kernel's `seg_sym`/`seg_fp` fails on the facts it cannot read, with no library error).

At the cut, the walk splits with `Seg.comp_ex` (`DeadFrom.of_seg` in dead mode) at the stop `b`,
proves the piece `q → b` by the hypothesis, and continues the walk at `b` with the facts `G`. The
hypothesis's start facts must be the walk's facts at `q` (definitional equality; the error names
both when they differ). A segment cut is not cached (`SymCtl.seg` in the keep list) since its proof
term may mention local hypotheses.

**Test** (`Tests/Flow/SegStep.lean`): the software `exp2` instance at tml-fa4 pc 7090 —
`cuteExp2Define`, the defining 31-instruction shape, its 35 slot registers and stop 7121 — as
`seg7090`: the two lane inputs (`.float .f32 0` at %r5564, `.float .f32 1` at %r5565) to the exact
exponents (1 at %r5128, 2 at %r5131), proven with `Seg.segRunStep` and the old
`Softmax.softwareExponentValues` (the run equation), `hMatch` by `rfl`. Then
`example : ∃ n, Seg kernel Assumptions.all l g n 7090 inF 7121 outG := by have hseg := seg7090 l g;
seg_sym …` closes by taking that piece — checked in scratch that **without** the hypothesis the
same goal fails (`seg_fp: cannot read the facts outG`: the walk reduces the 31 instructions to
Core's bit-level facts, not the lanes' exponents), so the step the assumption takes is what proves
the goal.

**Not done (recorded)**: a segment step *without* a hypothesis (the walk computing `swExp2Lane` of
unknown inputs) is not possible in the current symbolic states; a kernel gets this by stating the
piece, which is also where the lane numbers live. `seg_sym` does not use a segment rule to *decide*
branch conditions or to cut at a segment's *prefix*.


## Round 13: segment checks that read stated values (audit items 1, 4, 5, 6, 8, 10; G23)

Measured first (tml-fa4 `Loader/StepsRowsWarmKH.lean`, 16 sites, profile and `SEG_SYM_LOG`/
`SEG_FP_REPORT`): the time was not in evaluating the code. It was in the elaborator re-deriving
facts the tactics had already computed: (1) assembling `seg_footprint` made the elaborator unify
the start facts with `Fexp` (whose values `evalTable` had read off the table) and the end facts
with their split form, unfolding the role's tables (about 9 s each, two per segment); (2)
`restate` closed every live register of the table by `fact_mem` (a linear search with
unification per entry) and `sym_close`, whose first step is a full `rfl` that unfolds the table
again (8–12 s per site); (3) a segment that the evaluation cannot take (a loop's back edge)
still had its frame values proved before the evaluation failed (3.5–5.5 s per attempt).

- **`seg_fp` assembles its lemma as a term** (`Footprint.lean`): `seg_footprint` applied to the
  computed arguments, with the run and the frame values as goals, assigned without the
  elaborator's check; the kernel checks the application once (the tables unfolded there). The
  start facts' proof is unified with the run's start state first and its pending arguments are
  synthesized (an implicit argument the elaborator would have inferred from the goal); a proof
  with holes left fails the segment. The
  frame values are proved after the evaluation, so a segment the evaluation cannot take fails
  before them.
- **`sym_close` reads the stated value first**: when the computed term is the table's entry
  (`evalTable`), the equation is `Eq.refl` checked by the kernel; the case analysis and the
  elaborator's `rfl` are only for the rest.
- **`restate` builds the table's facts as a term** (`SegSym.lean`): each live register's fact of
  the walked state found by position, its value compared with the table's entry after reducing
  projections of constructors (`projNorm`; the walked state reads a field as `v.11`, the table as
  `V.slot v`), `Eq.refl` checked by the kernel when they agree, `sym_close` otherwise (5 of
  about 40 registers in the measured site).
- **Measured** (before = lane-L 680855e73, after = this commit, the same file in both trees at
  the same time, CPU seconds since the host load was 80–490): `StepsRowsWarmKH.lean`
  655.6 s → 229.4 s (wall 878 → 441 s, peak memory 10.8 → 6.8 GB); one of its sites alone
  38.8 s → 19.8 s (measured together before the projection step was added); `Correction/Shape.lean` 620 → 627 s (no change: its cost is `site_shape`,
  lane L2's item 3). FlashMLA's files are on its branch and were not measured here.
- **Not done**: generated per-pc step lemmas (`step_<pc>` with literal successor states) and
  generated `val_<pc>_<r>`/`next_<site>`/`rule_<pc>`: in the measured site the evaluation itself
  (`eval`, 0.3 s per segment) is no longer the cost; the walk (about 5 s for 5 instructions,
  `stateReg`/`normVal` over the fact list, audit §6.3) and the remaining `seg_fp` piece (about
  4 s) are; a structural register lookup in the walk was tried and showed no measurable change at
  this load, so it was not kept. `seg_auto` still tries a segment the evaluation cannot take
  (now failing before the frame values); a generated length/path table would remove the attempt.

### Round 13, second step: no doomed evaluations, membership by position

Measured on FlashMLA's `Proof2/Index/StepsLen.lean` (the two `.nc` length loads, four
successors each; `SEG_SYM_LOG` and `SEG_FP_REPORT` with failure times): 14 `seg_fp` attempts on
segments through a symbolic branch failed after 8–32 s each, about 290 s of 476 s CPU. They came
from `lands_auto`, which tried `seg_auto` (and, in `SiteIte`'s rule, `ite_cases` + `seg_auto`
again) before `seg_sym`; the evaluation runs until the symbolic branch stops it. The walk itself
costs milliseconds per instruction here.

- **`lands_auto` walks first** (both rules, `SiteCases.lean` and `SiteIte.lean`): `seg_sym`'s walk
  decides the length of a segment without symbolic control (one `seg_fp` at that length) or where
  it must be cut, before any evaluation; `seg_auto` (and `ite_cases`) remain as fallbacks for a
  segment the walk cannot take. No evaluation is started that a symbolic branch would stop, so a
  generated length table is not needed for this.
- **`fact_mem` finds a fact by position** (`fact_mem_pos`, `RuleStep.lean`): the fact of the
  register in the explicit facts, appends or the table part (`mem_factsFrom`), as a term the
  kernel checks; the value is assigned when it is a hole, compared (`projNorm`) when given; the
  old search remains the fallback. `projNorm` moved to `Footprint.lean`.
- `seg_fp` reports the time of a failed attempt; `sym_mark "…"` writes a line to the
  `SEG_SYM_LOG` timing log (used in `lands_auto`).
- **Measured** (before = 19b5d2e36, the same file in both trees at the same time, CPU s, host
  load ≈200): FlashMLA `Index/StepsLen.lean` 453.0 → 58.8 s (wall 810 → 350 s);
  `Wg1/Head.lean` 358.8 → 98.3 s (wall 857 → 757 s); tml-fa4 `StepsTiles` Epilogue/Mma/Correction
  108.9/102.5/156.7 → 42.7/36.3/98.9 s; `Loader/StepsRowsWarmKH.lean` 232.5 → 230.1 s (its
  segments needed `seg_sym` already).
- **Not done**: generated per-pc step lemmas, per-register values, `next_<site>`/`rule_<pc>`. In
  the files measured the walk (milliseconds per instruction in StepsLen; about 5 s per KH site)
  and the pieces' `seg_fp` evaluations (a 33-instruction piece 6.5 s) are now the cost; a
  generated step lemma per pc would replace the evaluation of the pieces.

## Round 14: the kernel lanes' requests (item 1)

The local versions were read on the kernel branches (Inkling `inkling-proof2` de6cddd73, FlashMLA
`flashmla-proof2` 2a62fc618); where a lane has a generic local lemma it is promoted unchanged up
to imports and names, so the lane replaces its file by an import.

- **L-q** (`Lemmas/Order/ReadSame.lean`): Inkling's `Proof2/Lib/ReadSame.lean` as is:
  `read_byte_of_writers`, `read_of_writers`, `read_byte_of_writers_hidden` (a read of a byte that a
  class of writes all give one value, one of them visible, every other covering write after the
  read, or before the visible write).
- **L-p** (`Lemmas/Kernel/Safety/HandoffExits.lean`): Inkling's `Handoff.of_bar_exits` (the form
  that holds: per passed `bar.sync`, every exiting participant of its CTA made the arrival of its
  ordinal; no cap on the instances). The consumer-side reading of the request (a participant that
  exits before the completion) is what the kernel proves to obtain `hexits`, so no second form.
- **L-r, per-instance thread groups of an early barrier** (`Lemmas/Protocol/NamedBarPhase.lean`,
  `NamedBarPhaseKeys.lean`, `Lemmas/Kernel/Safety/HandoffPhased.lean`): Inkling's `BarLanePhase`,
  `BarLaneKeys`, `BarEarlyPhased` (`PhSources`, `D_arrival_key`, `D_member_arrival`,
  `Handoff.of_barPhased`), on the library's `NamedBarEarly` and `HandoffEarly` (already promoted
  in round 12 from the same files).
- **L-o** (`Lemmas/Kernel/Safety/GuardKey.lean`): the instance form is a key per poll (`EvId →
  Nat`, the kernel's choice: the pass of the loop from the machine state, or a count on the trace).
  "Equal counts of polls at the position" is not used as the instance: a wait loop retries its
  poll, so the count of polls is not a function of the pass. `PollObjAt key` (equal keys, one
  object) and `PollKeyOrdered key` (different keys and objects at a poll branch, ordered) replace
  `PollObjUniform` in `not_warpDivergent_pollAgree_key`; `PollObjAt.of_uniform` is the constant
  key; `PollKeyOrdered.of_roundsMet` takes the round (`pollRound`) as key and `PollRoundsMet`,
  which `PollRoundsMet.of_collectives` (since 2026-11-15) derives from per-round warp collectives:
  this is the `PollRoundsMet` item of round 12, which needed no new lemma.
- **L-n, the class-events-from-sites pattern** (`Lemmas/Kernel/Safety/ClassPcs.lean`):
  `RoleTable.class_pcs` (an event of a class that one kind of instruction fires is fired from a
  followed state whose site is at a position of that kind, `OpPcsFast`), the instances
  `RoleTable.res_pcs` (resource events) and `RoleTable.exit_pcs` (`isRetOp`), and `site_pcs`
  (`∀ s : Site, s.pc ∈ pcs → s ∈ [..]` by cases and `decide +kernel`, Inkling's `site_cls` with
  every constructor parameter quantified). Test `Tests/Flow/SitePcs.lean`.
- **G25** (`shape_ldNcM`, `ShapeClasses.lean`): FlashMLA's lemma as is. It is not added to
  `site_shape`'s class list: its `.nc` premise (`A.any (·.ncLoads t.pc)`) is the role's, and an
  extra alternative would cost every failing `.nc` site an attempt.
- **G22** (`ref_cases … helpers [h, …]`, `NextOk`, `NextOk.mono`, `NextOk.ref_next`): a site whose
  transition evaluates to a helper's result is closed by the first helper lemma `… → NextOk R'
  (helper …)` that applies (premises by the role's tactic), `R'` giving `Ref` by `exact`, `.1` or
  the role's tactic; otherwise the three-way split as before. FlashMLA's `Good` (`o ≠ none ∧ o ≠
  some none ∧ ∀ d', o = some (some d') → Ref d' ∧ …`) unfolds to `NextOk` with a stronger
  invariant, so its helper lemmas apply unchanged. Test `Tests/Flow/RefHelpers.lean` (one site by
  a helper, one by the split). No kernel uses `ref_cases` yet, so no check time changes.
- **ERR-TMEM-ACCESS-LIFETIME, `cta_group::1`** (`Lemmas/Tmem/Tmem1Access.lean`):
  `Tmem.One.no_access_unsafe` over `Tmem1Ops` of warp `w`, from three per-access facts: the cell is
  of the thread's CTA below column 512; lane 0 of warp `w` of the CTA allocated before the access
  and went on; the access completes before every deallocation of its CTA. The generic part of
  Inkling's first-tree `TmemAccess.lean` (allocation recorded and covering, release = the CTA's
  deallocation); the completion orders stay the kernel's (its MMA commit and waits).
- **Not done here**: FlashMLA G26/G27/G28 (`out_gen` kinds) go with item 2 (per-pc step lemmas
  for every local instruction kind), since a per-pc lemma for each instruction is what an
  `out_gen` item would be.

## Round 14: association lists read once (item 2, first measurement)

Profiled before writing step lemmas (one tml-fa4 `Loader/StepsRowsWarmKH` site, `SEG_SYM_LOG`,
`SEG_FP_REPORT`, the Lean profiler): of 11 s in `seg_sym`, the walk's steps took 3–9 ms each and
`seg_fp`'s evaluation of the run 263 ms; 3.6 s went to `symStart` and `startCells` before the walk
(about 31 ms per live register, 58 registers, twice), about 2 s to `seg_fp`'s explicit read facts,
and most of `restate`'s `sym_close` time to the same thing: `evalTable` looking a register up in
the value table, whose association list `lookupWalk` walked from its head with `whnfD` at every
lookup (quadratic in the table per segment). So the evaluation of instructions was not the cost
in this file.

- **`lookupWalk` reads a list's entries once** (`assocEntries`, `assocCache`, `Footprint.lean`):
  the first lookup in an association list term walks its whole spine and records every literal
  key's first entry; later lookups in the same term (every register of every segment of the
  file) are hash lookups. A list whose spine or keys are not literal, or whose term has a
  metavariable, is walked as before; a cached entry is used only where the list's free variables
  are assumptions (no `let`) of the local context whose types agree with those recorded with the
  entry (theorems elaborated in parallel may reuse an id). Entries are returned as written, so terms and proofs are unchanged.
- **A budget the cache exposed**: tml-fa4's `Loader/StepsArrPrime` failed with the cache: in
  `seg_fp`'s pointwise frame check (`valProofPointwise`), one side was the table function applied
  to the register (`valCut … 7506`, which `evalTable` does not unfold), compared with the entry by
  `sameValue`, whose second attempt has a budget (2,000,000 heartbeats). It had passed only
  because the repeated list walks had filled Lean's reduction cache (12.3 s in that check). Both
  sides are now unfolded to their lookups first (`unfoldAt`, as `valProofTables` does), so entries
  are compared: 0.18 s there, and no budget is near.
- **Measured** (CPU s, same tree, library oleans swapped, load 230–350): `Loader/StepsRowsWarmKH`
  229.5 → 64.3; `StepsTiles` Epilogue/Mma/Correction 39.0/33.7/86.6 → 37.2/31.8/82.5 (perf rule:
  faster); FlashMLA `Index/StepsLen` 46.8 → 44.5, `Wg1/Head` 79.2 → 76.5 (explicit facts, no
  table); Softmax `StepsScanLoop` 94.3 → 79.5, `StepsBiasCtl` 58.5 → 53.5; `Correction/Shape`
  492.9 → 484.9 (its cost is `site_shape`, lane L2's item 3).
- In FlashMLA's `Wg1/Head` the remaining cost is the branch decisions of `seg_sym` (about 25 s:
  `decideBool` against the hypotheses, 0.9–2 s each, repeated per successor), the `ld.param` walk
  step at pc 2332 (6.7 s, Core's parameter read evaluated by `whnfD`) and piece evaluations
  (7.9 s, 4.4 s of it one 33-instruction piece): the step lemmas of the next commit address the
  last two.

## Round 14: `max.f32` of two or three sources in generated runs (softmax request (a))

The bias round of tml-fa4's softmax folds the products with the maximum before it by
`max.f32 d, a, b, c` (pcs 5536–5665, with `mov.b64` unpacks between and one two-source `max` at
5664). The library has its outcome (`Lemmas/Flow/MaxCore.lean`: `maxE`, `exec_maxE2`,
`exec_maxE3`, the ideal result or the Core rule's where the ideal rule declines).

- **As `fn` items, not new `OItem` constructors**: FA4's first tree matches on `OItem`
  exhaustively (`FactsSoftShape.oTyVals`, `SoftmaxSteps/ArithBase.rule_pc`), so a constructor
  would break a kernel lane's files. `XItem.fn (maxOp d srcs) d srcs maxE` is the item;
  `XItem.max2_rule` and `XItem.max3_rule` (`OutRun.lean`) give its rule from the kernel's ideal
  reading of `max.f32` (`IdealAt`, `DeclineAt`).
- **`Tools/out_gen.py`** reads `max.f32` with two or three register sources natively: item kind
  `max2` or `max3`, whose rule the declaration names (`rules.max2`, `rules.max3`), value
  `okVal (.bits 32 0) (maxE [..])`.
- **Fixture** `Tests/Gen/Out/max.json` → `Tests/Gen/Out/Max.lean`: tml-fa4's pcs 5536–5665 (65
  three-source and one two-source `max`, 64 unpacks), five pieces, the final maximum `%r3500`;
  readings `rule_max2`, `rule_max3` in `Tests/Gen/Out/ExpoRules.lean` (`forms` now also covers
  `.max .f32`). Checked in 6.3 s. Freshness by `tests/test_out_gen.py` (as every declaration under
  `Tests/Gen/Out`), and `test_max_items` for the items.

## Round 14: a template segment whose lanes may be `-∞` (softmax request (b))

`Seg.segTwo` takes a two-lane instance of a `segmentExact` template and reads the lanes as
numbers (`valFloat`), so it needs finite inputs, and it is stated for the library's
`segmentExact` assumption. tml-fa4's `swExp2` is `segmentExact` with its own `segmentRule`
(`execSwExp2`): `execSegment`'s register effect with the lane reader `swExp2Lane`, which also
gives `0` for the `-∞` encoding (a masked bias half; the assumption's text states it). So neither
the `-∞` lanes nor, strictly, the finite ones go through `Seg.segTwo` for this kernel.

- **`execSegmentLane lane m t`** (`Lemmas/Flow/SegLane.lean`): `execSegment`'s effect with a lane
  reader `lane : Value → Exec ℝ`; tml-fa4's `execSwExp2 m t = execSegmentLane swExp2Lane m t` by
  definition. `execSegmentLane_two`: two lanes read as `y₀`, `y₁` give the outputs
  `.float .f32 y₀`, `.float .f32 y₁`.
- **`Seg.segLaneTwo`**: the piece for any assumption `a` whose segment on states at `pc` is
  `execSegmentLane lane m` (`hrule`, one `simp` and `rfl` for the kernel), from facts whose input
  lanes the reader accepts (`-∞` with `swExp2Lane_negInf`, a number `x` with the template's
  `fn x`). Its end facts are `segValsY m o₀ o₁ y₀ y₁` (`segVals m fn … = segValsY m … (fn x₀)
  (fn x₁)` by definition), with `Seg.segTwo`'s frame and coverage premises.
- **Test** `Tests/Flow/SegLane.lean`: the instance of pc 7090 (`matched7090`, copied from
  `Tests/Flow/SegStep.lean`, whose definitions are private to that module) with both lane inputs
  `-∞`: one piece from 7090 to 7121 with outputs `0`, `0` on `Assumptions.all` (as
  `[idealArith, approx, lg2, bf16Convert] ++ swExp2 :: …`).
**G15, G16, G20: dropped in favour of lane L's own versions.** This lane had ported lane L's
hunks (`fc8c0ee12`) before main carried them; the merge of origin/main `0fc855655` takes main's
`Step/SiteCases.lean`, `Step/Record.lean` and `Step/SiteShape.lean` unchanged (lane L's versions
are the same changes plus its zero-sum work), so no duplicate remains. One hunk of the port was
wrong and silently fell back through `try_rt`: it made the `.load` class's `step_load` `herr` case
disjunctive, but `step_load` (unlike the `.nc` lemmas) still takes a single `= none`; main's
`SiteCases.lean` has the single form, which is what this lane now uses.

## Round 13 (lane L2): the check-cost audit's items 2, 3 and 7

Measured on this host with `lake env lean <file>` (elaboration only, the imports' oleans warm),
user CPU; the host was shared and loaded (100–350), so the same file's wall time moves ±20 %.

| file | before | after | change |
|---|---:|---:|---|
| `Correction/Shape.lean` (`site_shape` and `site_cases`, item 2) | 802.1 s | 644.1 s | −20 % |
| `Correction/StepsTiles.lean` (`site_cases`, item 2) | 148.1 s | 153.3 s | +3 % (noise; its one site is a 32-element store, not the enumeration) |
| `Mma/StepsTiles.lean` | 104.3 s | 103.0 s | no change |
| `Common/Roles.lean` (item 7, `lit_mem`) | 135.6 s | 160.4 s | **+18 %, reverted** |

**Item 2 (per-site dispatch instead of `site_cases` + `skip_by (simp at hs)`)**: `familySites`
(`Lemmas/Flow/Step/SiteCases.lean`, the splitter both `site_cases` and `site_shape` call) now runs
`substSiteEqs` first: a site variable that a hypothesis of the context fixes by an equation
(`hs : s = .tiles false`, the form the step and shape theorems are stated with) is substituted, so
the site is literal and the split produces **one** goal instead of one per constructor of the site
type (tml-fa4's Loader has 566, its Correction 263) — no enumeration of the discarded constructors,
no default `simp at hs` per discarded goal. It fires where a theorem fixes the site (checked by
`dbg_trace` on `Correction/StepsTiles`: 1 → 0 variables to split); where the hypothesis is a
disjunction (`Correction/Shape`'s `shapeAt_start`) or the kernel already `rcases`d to a literal
(`Loader/StepsRowsWarmKH`) it does nothing, and the previous behaviour is kept. The shape files gain
because their per-theorem `simp at hs` over ~200–500 discarded goals is gone (−20 % on
`Correction/Shape`); the single-site step files do not, because their cost is the one real site's
segment (items 1/5 of the audit, lane L's redesign), not the enumeration.

**Item 3 (search-free `site_shape`)**: **reverted**, with the evidence. Two forms were tried.
(a) Narrowing the per-goal chain by a class guard on constant occurrence (`shape_has [..]`) is
unsound here — a per-goal class guard on constant occurrence (`shape_has [..]`) is unsound here: some
shape goals are closed by `site_norm` + `rfl` through a `TState` proj-ection or by `site_acc` on a
goal that mentions none of the class's unfolded constants (`Site.arr 0` at pc 7752 leaves
`List.any Assumptions.all (fun a => clusterScopeMbar a (TState.pc …)) = false`, which the original
chain closes and a class-guarded chain does not), so a guard has to be as wide as the union of the
methods' simp sets, and saves nothing on the goals it does reach. (b) Removing
`simp (config := { decide := true })` from `site_acc` — which looked like a pure win (`Correction/Shape`
644 → 580 s user, 10 % of the item's total) — **breaks `Kernels/TmlFa4Fwd/Proof2/Loader/ShapeSites.lean`**
(`site_shape: at Site.pgSt Per.prime 0: at pc 506 every inversion lemma failed`, `shape_store` aborting
inside `simp`), so it is not a library-only change: a store site's alignment side condition is
discharged by the `Decidable` attempt and would have to be named first. Both are recorded as not
taken; the whole of item 3 is `site_cases`' substitution (item 2) below, which is what the 20 % is.
Recorded as not done: the audit's structural form of item 3 — one *generated* shape lemma per site
class with its side conditions instantiated (`exact shape_<site> hf`) and per-(pc, register)
`Flow.val_<pc>_<r>` lemmas so `site_read` is one `rw`. Both need a generator (`Tools/value_table.py`
would emit the value lemmas from the decode) and are the audit's own recommendation; the per-goal
work here shows where the cost is *not*.

**Item 7 (`decide +kernel` over literal pc tables)**: measured, **not taken**. `lit_mem`
(`Lemmas/Flow/Footprint.lean`, membership by position: `List.mem_of_getElem?` at the entry's index)
replaces `decide +kernel` on `Loader.site_mem`/`Epilogue.site_mem` etc. and is *slower* on this
shape (135.6 → 160.4 s user on `Common/Roles.lean`): both forms must unfold the 380-entry list
literal for each of the ~560 site goals, and `lit_mem` additionally builds the list expression and
checks it against the goal, so the kernel's `List.elem` walk that `decide +kernel` does is not the
cost. `Tests/Flow/SiteLit.lean` keeps the position proofs as the tool for *small* lists (a startup
site, a single checked pc) and the equation-substitution test. The real fix, recorded: state the
region's sites per constructor (`pc_<ctor> : (Site.<ctor> …).pc = <literal>`, generated from the
decode) and prove `s.pc ∈ sites` from a *small* list per constructor family instead of one 380- or
566-entry list for all of them.

## Round 14 (lane L2): the FlashMLA warpgroup-2 requests G21–G24, G8', G13 and G17

Taken as `machine-plan-status.md` numbered them for lane L2 (the FlashMLA lane renumbers them
G27–G30); the walk's *internals* stay lane L's (audit items 1/4/5/6/8/10), so every hook here is an
alternative at an existing extension point, not a rewrite of `condStep`/`ruleStepProof`/`sym_close`.

**G21, a segment whose first no-rule step is a float op** (`Lemmas/Flow/Step/SegSym.lean`):
`DeadFrom.of_step` and `DeadFrom.of_step_local_error`. The walk's fault path already applied
`DeadFrom.local_error` to a *single* instruction whose step faults (`sym_fault`); what a `cvt` +
`mul.bf16x2` sequence needs is the step before the fault: a floating `cvt.rn.bf16x2.ue8m0x2` has no
Core rule, so the walk cannot compute its value and cannot reach the `mul` that faults on the pair
it produces. The role states the step (`Seg.segStep`'s hypothesis: the value the `cvt` writes and
the facts it leaves) through `DeadFrom.of_step`, and the fault of the next instruction
(`pairValue = none` in FlashMLA's terms) through `of_step_local_error`; both are the library's
`DeadFrom.of_seg`/`Seg.segStep`/`local_error` composed, so nothing about the walk changes. Symbolic
evaluation of the `cvt` *inside* the walk remains open: it is the same seam as G22, and lane L's
audit item 1 (per-pc step lemmas) is where it lands.

**G22, `sym_rule`** (`Lemmas/Flow/Step/RuleStep.lean`): a `macro_rules` hook (default: fail, naming
it) tried by `ruleStepProof` when `ruleSimp` + `ruleDecideConds` leave conditions of the rule open.
A rule whose premise is a *hypothesis* — that a pair is finite, that a scale byte is not a NaN
pattern, FlashMLA's `ChunkOk` decomposition — never meets the walk's `cheapDefEq`, because the walk
judges a rule by comparing its value with the fact's value; the role now closes the remaining
conditions itself, and the rule is taken. Additive: only reached where the existing path leaves
goals.

**G23, `sym_decide_rw`** (`Lemmas/Flow/Step/SegSym.lean`): `sym_decide`'s chain gains the hook after
`assumption` (`symm; assumption`) and before `linarith` — a decision whose hypothesis matches only
after the machine's abbreviations are unfolded (`simp only [skipLoop, padded, scmpi, scmp, r32, i32,
compare] at *`, the rewrite FlashMLA found by hand). FlashMLA's other branch-predicate request
(G29 there) is void: their `qUtccp`/`free` exits are now successors holding an `if`, which
`site_cases` splits itself.

**G24, `scmpi` = the code's `setp`** (`Lemmas/Flow/Arith32.lean`): `scmpi_eq_setp`, a `rfl`
equation between `scmpi c k x n` and `compare c k 32 (truncBits 32 x) (truncBits 32 (BitVec.ofInt 64
n))` — the term the walk recomputes from Core's rule. A machine's `scmpi` abbreviation and the walk's
term differ only by the expansion of `r32`/`i32`, and `cheapDefEq` can time out on a large
immediate's `BitVec.ofInt`; a role rewrites by the equation instead (or uses it in a `sym_decide_rw`
set). Test: `Tests/Flow/SymHooks.lean` (the three hooks' default failure, a role's replacement
consumed, `DeadFrom.of_step_local_error` applied, and the `scmpi` equation).

**G8', `shape_barSyncN_block`** (`Lemmas/Flow/Step/ShapeTc.lean`): the named barrier whose count
operand holds the block's size — `barTmpl` then omits the count (`.bar id none .sync`) and
`shape_barSyncNR`'s `hnb` excludes it. Ported from FlashMLA's `Index/Shape.lean`; `site_shape` tries
it third in the `barSyncN` class (`SiteShape.lean`, after the immediates and the count-carrying
registers), so a `barrier.sync %r, %r` on the block's own count has a shape.

**G13, a cut in `lands_auto` at a shared prefix**: not a new combinator — the mechanism is item 6's
(`Seg.segStep`/`Seg.segRunStep` + `seg_sym` taking a `∃ n, Seg K A L g n pc F b G` hypothesis as one
step of its walk, `Lemmas/Flow/Segment.lean` + `Step/SegSym.lean`, tested on tml-fa4's software
`exp2` in `Tests/Flow/SegStep.lean`). A prefix proved once (FlashMLA's `pre_seg` over pcs
1844–2356) is exactly such a hypothesis: the walk cuts there, continues with the segment's stated
facts, and does not re-walk the prefix per successor. What stays with the role is stating the
prefix's end facts (its value table). Recorded rather than duplicated: an automatic cut in
`lands_auto` would have to guess which hypothesis is the prefix, and `segHyps` already keys them by
start pc.

**G17, `w32k_norm`/`w32k_close` promoted** (`Lemmas/Flow/Arith32WordW.lean`): FlashMLA's
`Proof2/Lib/Word.lean` body, minus the two lemmas the library already had with the same names
(`max32_W`, `neg32_W` — `Arith32WordWide.lean`'s forms are kept, the callers' names still resolve):
`andi_W_neg`/`andi_W_neg64`/`andi_W_neg4`, the wrapping `add32_Wm`/`sub32_Wm`/`addi_Wm`,
`addi64_eq`, `add64_W`, `shl64_2_W`, `sext_W`, `mulWide_u_W`/`mulWideR_s_W`, `eq_W`,
`andi_W_low`/`andi_W_31`, `shl_W`/`shl1_W`, `or32_W_64`, and the two macros. Test:
`Tests/Flow/WordW.lean` (rounded-down lengths, the signed maximum, `w32k_close` on a ring slot, and
the block-count barrier's shape).

**machine_gen's requests (G21 there: `zext16w`, named registers, header wrap, more opcodes, folded
table terms)**: not taken in this round, recorded. `zext16w` needs the generator to track which
registers a 16-bit instruction wrote (a `narrow` set beside `bits`/`preds`, and `cvt.u32.u16` then
emitting `zext16w` — the library has `zext16_eq_zext16w`), but changing the emitted term changes
`Kernels/*/Gen/*.lean` on **other lanes'** trees, whose freshness tests would then fail until they
regenerate; that is a cross-lane change, not a library one. Named registers, `ld.param`/`setp.eq.b64`/
`selp.b16` and folded table terms are the same class (they change the declaration language or the
terms the kernels' tables are written with) — the FlashMLA lane already works around each by hand.

## Round 14: Softmax and Inkling promotions (frame regions on a slice, `seg_jmp`, poll meeting)

From tml-fa4's Softmax lane (branch `tmlfa4-softmax-proof2` bf0ef646d), promoted as they are, with
the same names in `PTX.Flow`:

- `Lemmas/Flow/RunFrame.lean` (`noJump`, `frameB`, `tau_frame`, `run_frame`, `SegD.frame`) and
  `Lemmas/Flow/RegionFrame.lean` (`regionB`, `regionB_at`, `tau_region`, `region_frame`,
  `SegD.frameR`, `Code.StepAt.lift`, the event frame lemmas): the facts a segment or a site's step
  does not touch, from a Boolean check of the code (the lane's `Proof2/Lib/RunFrame.lean`,
  `RegionFrame.lean`, which `RegionSlice` needs).
- `Lemmas/Flow/RegionSlice.lean` (`regionOk`, `regionS`, `regionB_of_S`): `regionB` evaluated
  `K.code[lo + i]?` from the head of the code for every position; `regionS` walks the slice
  `(K.code.drop lo).take (hi + 1 - lo)` once (the lane measured one chain 546 s → 95 s).
- `Lemmas/Flow/SegJump.lean` (`seg_jmp`): an unguarded `bra` as one step that keeps every fact.
- Test `Tests/Flow/RegionSlice.lean`: `regionB` of tml-fa4's pcs 4352–4397 by `regionB_of_S` and
  `decide +kernel`; `seg_jmp` at pc 519.
- The kernel copies are on the lane's branch, not yet on main; when main has them, the lane's
  files import these modules and the copies are deleted (the names are the same, so a module must
  not import both meanwhile).
- From Inkling (branch `inkling-proof2` 7d9e62f09), in `PTX.Flow` with the same names:
  `Lemmas/Flow/PollMeet.lean` (`count_after`, `pos_before`, `meet_shfl`, `meet_elect`: of two
  lanes of a warp, the one with fewer collectives of a kind before its event reaches the next one
  after it, which is one instance with the other's, so `PollBefore`; this is what
  `PollKeyOrdered` of `GuardKey.lean` asks when the key is a collective count) and
  `Lemmas/Flow/SameCount.lean` (`same_count`: two events of a thread satisfying `p` with as many
  `p`-events before them are one). `PollMeet` needs only the library (its import of Inkling's
  `Lib/Elect` was unused).

## Round 14: one step lemma per program counter (item 2)

`Tools/step_gen.py` reads a kernel's decoded program (`Data/Decoded.lean`, the instruction terms
`Tools/code_table.py` reads) and writes, for each local instruction of the declared ranges
(integer, floating, move, conversion, branch, `ld.param`; guarded or not; no special-register
operand), `step_<pc> : PcLocal K A L g pc ins` (`Lemmas/Flow/PcStep.lean`): a state at `pc`
without a fault steps by `stepIns A L g t ins` — the guard, then the instruction's local rule
(`execLocalRule`: an assumption's rule, else Core's). Each is proved once from `code_<pc>`
(`PcLocal.of_code`: locality by `rfl`, no segment at `pc` by `seg_free_pc` or the declared
tactic; `exclude` lists pcs where a segment starts). One-click: `python Tools/step_gen.py
decl.json`, freshness by `--check` in `tests/test_step_gen.py` for every `Tests/Gen/Step/*.json`
and `Kernels/*/Gen/Step/*.json`.

- **Use** (`seg_fp`, `Footprint.lean`): when every pc of a piece's single path has its lemma
  (`<kernel prefix>.Flow.step_<pc>` in the environment, stated for the goal's assumptions), the
  run is the chain `run_succ_local` of the lemmas, each step's successor `whnfD` of `stepIns` on
  the state and its equation checked by the kernel (`Eq.refl`); no code lookup, guard read in
  `out` or segment search is evaluated, and the elaborator does not unify `run … = some ?t`.
  Otherwise (a pc without a lemma, a step that does not evaluate) the piece is evaluated as
  before; `SEG_FP_REPORT` names the reason.
- **Form decided against**: a lemma whose successor is a literal term in the operands per
  instruction kind (a template per op in the generator). It would reimplement Core's value
  semantics in Python per kind (integers, pointers, floats under assumptions), and the profile
  showed the per-instruction value evaluation is milliseconds; the cost was the code lookup,
  `out`'s dispatch and the unification of the whole run. `stepIns` keeps Core's (and the
  assumptions') semantics as the statement.
- **`decideBool` tries every hypothesis up to reducible unfolding first** (`SegSym.lean`), then
  the default-transparency comparisons as before, so a matching hypothesis later in the context is
  not preceded by budgeted failing comparisons against the earlier ones.
- **Measured** (CPU s, FlashMLA with lemmas for all 3,227 local pcs generated into a scratch
  module and imported by scratch copies of the files; same tree, load 220–310): `Wg1/Head` 166.0
  (neither) → 148.7 (decision order only) / 146.8 (chain only) → 121.3 (both); `Index/StepsLen`
  103.4 → 92.3 / 73.3 → 65.3. `seg_fp`'s run evaluation in those files: 17.4 s → 3.2 s (Head),
  28.6 s → 4.7 s (StepsLen). Perf rule (tml-fa4, no step lemmas: the chain declines at the first
  pc): StepsTiles Epilogue/Mma/Correction 38.5/32.7/89.5 → 41.0/34.6/84.2, `StepsRowsWarmKH`
  70.0 → 70.2, Softmax `StepsBiasCtl` 56.3 → 58.7 (within ±7%, load 60–220). The 3,227 lemmas
  check in about 30 s wall (1,250 s CPU in parallel parts of 64): a kernel declares the ranges its
  segments use rather than the whole code.
- **Fixture** `Tests/Gen/Step/flashmla_index.json` → `FlashMlaIndex.lean` (FlashMLA pcs
  2356–2409, 54 lemmas), `Tests/Gen/Step/FlashMlaIndexUse.lean` (a piece at pc 2358 whose proof is
  checked to contain `run_succ_local`).
- **Not done**: kernel declarations (`Kernels/<K>/Gen/Step/*.json` and the import of the output
  where `seg_fp` runs) are the kernel lanes'; `seg_sym`'s walk still evaluates `ld.param` by
  `whnfD` (FlashMLA pc 2332, 6.7 s); FlashMLA G27/G28 as `out_gen` items (float kinds with kernel
  readings, immediates) are not added: with step lemmas a floating stretch is chained by `seg_fp`
  with the assumptions' rules, so a role can state its values without generated item terms.

## Round 14: a pending `cp.async` arrive-on as a blocker (lane T1 request)

`Sched.Blk` (`Progress/Poll.lean`), `BlockerBy` and `Lagging` (`Progress/Rank.lean`) list the open
asynchronous obligations that block a waiter: commit, MMA, tensor copy, tensor store. Lane T1's
loader can exit with a pending `cp.async.mbarrier.arrive.noinc` (its arrive-on obligation); the
first tree excluded that by maximality, the descent has no maximality there (T1's e74daba96,
`Kernels/TmlFa4Fwd/DECISIONS.md`). `.arriveOn` (`Descent.Obl`: some `AsyncArrive` not yet
`X.async.arrived`) is now in the list; it ranks 1 (`rank`), below every thread at time at least
2 (`rank_async_lt`), and stays open when a failed poll is appended (`obl_failedPoll`: the poll
adds no `asyncArrive` event and does not change `X.async`, so the case is the event lookup through
`get_failedPoll`). The disjunction is appended last, so existing proofs of the other cases keep
their positions.

## Round 14: a one-CTA TMA unit object (lane T1 request)

`Lemmas/Protocol/TmaUnit.lean` (`MbarRing.TmaUnitSource`, `TmaUnitObject`,
`TmaUnitObject.noInval`, `TmaUnitObject.of_issues`): lane T1's `Proof2/Lib/TmaUnit.lean`
(63d610174) as is, with the same names. An mbarrier object of one CTA initialized with count 1
whose records are its initialization, polls, one producer arrival per use with the use's
transaction bytes (`mbarrier.arrive.expect_tx`, count 1, release) and the completions of the
tensor copies naming it; `of_issues` derives this from the issues that name the object (no
invalidation, no `cp.async` arrive-on, no bulk copy, commit or CLC completion on it).
`PairTmaRing` is the `cta_group::2` pair ring and does not fit. It is not generalized beyond
count 1 here: the only instance (tml-fa4's Q stages) has count 1, and a count parameter would
change the statement T1 uses. Test `Tests/Protocol/TmaUnit.lean`. T1's copy is on its branch,
not on main; T1 switches its import to `Lemmas.Protocol.TmaUnit` and deletes the copy when it
merges this tip.

## Round 14: step-lemma declarations for tml-fa4's slow ranges

`Kernels/TmlFa4Fwd/Gen/Step/softmax.json` → `Kernels/TmlFa4Fwd/Gen/StepSoftmax.lean` (pcs of the
softmax control pieces: 3111–3370, 3429–3582, 5110–5272, 5683, 6527–6559, 6680–6731, 7622–7739),
and `correction.json` → `StepCorrection.lean` (the correction role's code, 7746–9205); 1,892
lemmas, checked in 9.5 s wall (55 s CPU). The kernel term is `PTX.Kernels.TmlFa4Fwd.kernel` (the
machines' `kernel`, so `seg_fp` finds `PTX.Kernels.TmlFa4Fwd.Flow.step_<pc>`); no segment at a pc by
the kernel's `Proof2.Epilogue.segFree` (the ranges contain no software-`exp2` site). The softmax
ranges are the union of the pieces `seg_fp` checks in `StepsScan*`, `StepsScore`, `StepsSelect`,
`StepsBias{Ctl,Load,Load2}` (read off `SEG_FP_REPORT`, intervals merged across gaps up to 16).
Measured with scratch copies that import the output (CPU s, load ≈300): Softmax `StepsScanFirst`
84.3 → 52.7, `StepsScore` 190.2 → 66.7; Correction `StepsTiles` 129.8 → 38.0, `StepsRescale` 414.0 →
276.4 (run evaluation 15.0/49.7/40.7/75.2 s → chains of 1.8/1.2/0.9/3.1 s). The step files are not
switched here: a file uses the lemmas by importing `Kernels.TmlFa4Fwd.Gen.StepSoftmax` or
`…StepCorrection`.

## Round 14: Lean options in generated runs (tml-fa4 bias lane request)

`Tools/out_gen.py` takes an optional `"options"` object in a declaration and writes one
`set_option <name> <value>` per entry after `noncomputable section` (the bias lane's reading
`rule_widen` decides `biasWidenSites.contains pc = true` by `rfl`, which exceeded the default
`maxRecDepth` for pcs late in the list). Declarations without it generate the same file as before
(`expo.json`, `max.json` fresh). Test `test_options` in `tests/test_out_gen.py`.

## Round 14: the no-increment ring bound (lane T1 request, tml-fa4's K/V ring)

`Lemmas/Protocol/NoIncRing.lean`, the counterpart of `PairTmaRing/CommitBound.lean` for a ring of
one CTA whose full barrier `F` completes each use by `n` no-increment arrive-ons
(`NoIncObject X F n`) and whose empty barrier `E` is completed by one consumer's commits:

- `NoIncObject.phase_mul_le_units`: `n · phase(F) ≤ arrivalUnits(F)` (the accounting with no
  increments and expected count `n`);
- `NoIncObject.units_le_sum`: `arrivalUnits(F) ≤ ∑ a, arrive-ons of producer a on F`, when every
  arrive-on on `F` is a producer's (`prod : Fin P → Nat` injective; each unit is one arrive-on's
  record, records with distinct ids; `length_eq_sum_fibres` splits the records by thread);
- `commitObj_phase_le_commits`: `phase(E) ≤` consumer `c`'s commits to `E`, for a unit object
  without increments that no thread arrives on, when `c` issues every commit targeting `E`, each
  naming `E` and with one target rank on it;
- `full_phase_le_commits`: with the producers' arrive-ons at most their successful polls of `E`
  plus `d` (the kernel's per-lane count, T1's `arrAt`/`acqAt`) and those polls at most
  `phase(E) + 1` (`okPolls_le_phase`), `phase(F) ≤ commits + 1 + d`.

The statement takes the kernel's facts as premises rather than a `Hyp` record: the objects
(`kvObj`, `emptyObj`) and the per-lane counts are already separate kernel theorems. Also
promoted: `Lemmas/Protocol/PollLe.lean` (`MbarRing.okPolls_le_phase`, T1's `Proof2/Lib/PollLe.lean`
as is). Test `Tests/Protocol/NoIncRing.lean` (the composition in the K/V ring's shape, 64
arrive-ons per use). T1's `PollLe` copy is on its branch; T1 switches its import and deletes it
at the merge.

## Round 14: a thread's counted events bounded by a measure (G1, library half)

`Lemmas/Kernel/CountBound.lean`: `Frame.counts_le_measure` (the counted events, `Event.counts`, of
a followed thread's prefix are at most the measure of its state) and `Frame.counts_le_of_measure`
(at most `B + 1` over the whole trace, for a measure `μ` with `μ init = 0`, `μ ≤ B` under the
invariant, never decreasing along a step and increasing at every counted event, when the machine
dies only at its last event). This is the per-thread premise of `terminates_of_count`.

What tml-fa4's `terminates` on Proof2 still needs (recorded, not done here): the thread machine's
ledger has `Cls.all` (every event, failed polls included, so not bounded) but no class for
`Event.counts`, and no role's reference invariant bounds a total event count. So G1 needs, per
role of `Proof2.thread` (startup, output, MMA, correction, loader, softmax), a measure of its
states — its loop counters (the closed forms of `RefCounts`/`RefQ` and the site families'
indices) weighted above the site's position in the loop body — with the step property for every
transition (a case analysis like `ref_next`'s, the failed polls returning to their own state),
and the glue's measure as the startup's plus a role offset. The softmax role's invariant is not
complete on Proof2 yet, so its part waits for that lane.

### Lane L, 2026-11-22: count-bound step context, released steps, no-increment ring order

- `Frame.counts_le_measure`/`counts_le_of_measure` take the run index, state and trace event in the
  step obligation (a role's measure may use `ub_zero` or the event's shape). Strict generalization.
- `Lemmas/Kernel/Progress/Released.lean` replaces a kernel's `NextFacts.fire` by `Frame.end_at`:
  the next event's kind is computed from the instruction (`opKind`), so the per-kernel site-kind
  table and its decision are not needed. Kinds needing a partner or a kernel fact (`Rest`: polls,
  warp collectives, register requests, allocations, unclassified) stay with the kernel. The
  execution facts are a structure (`NextEnv`) so a kernel proves them once.
- `Lemmas/Protocol/NoIncRingOrder.lean` states the RAW/WAR steps from a pinned phase rather than
  a no-increment version of SingleTmaRing's item framework: the K/V ring has 32 producer lanes per
  use, which SingleTmaRing's one-copy-thread `Hyp` does not model; the phase of a lane's arrive-on
  is the kernel's count argument (`kv_bound_lane`).

## Lane 1b (phase 1), 2026-11-22: one set of thread-fact lemmas, the blockers of `Sched.Lag`

- **One set of thread-fact lemmas.** `Lemmas/Kernel/Safety/StateInv.lean` replaces
  `Lemmas/Kernel/SmallInv.lean` (no users), tml-fa4's `Proof2/Lib/StateInv.lean` and
  `Proof2/Lib/EndState.lean`. One induction over the run (`small_inv`, a fact kept by the writing
  transitions with a frame table for the others); `RoleTable.stateInv` is its instance with every
  transition writing, `RoleTable.roleInv` the role form of `stateInv`; `Ledger.rel_step` the form-A
  ledger relation. The end of a trace: `end_state`, `end_countP` (moved), `RoleTable.end_ref`
  (the last followed state satisfies the table's invariant), `RoleTable.end_ledger` (with a ghost
  ledger, the whole trace's count of a class without the exit is the ledger's), and
  `RoleTable.live_of_ok` (the liveness premise from the table's death obligation). Test
  `Tests/Kernel/StateInv.lean`.
- **`Sched.Lag` counts any producer event.** The structure takes the producers' counted events
  `cnt` (`arrivesOn m`, `MbarRing.arriveOnTo m`, `commitsTo m0`); `exit` is weakened to "an exited
  producer made at least `U`"; `wait` and `bound` no longer take `PollsOn` (a kernel puts the
  waiter's position into `cons`). `Lag` had no users, so nothing else changed.
- **The blockers of the other object kinds** (`Lemmas/Kernel/Progress/HandoffBlockers.lean`):
  no-increment objects (`Lag.blk_noInc`/`pollBlocked_noInc`, over the promoted
  `Lemmas/Protocol/NoIncBlocker.lean` with `MbarRing.arr_recorded`), commit objects
  (`Lag.blk_notify`/`pollBlocked_notify`, over `Notify.Obj.blocker` and the reuse paths
  `Notify.Reach`), one-CTA TMA unit objects (`blk_tmaUnit` with the lag of a short producer from
  the kernel, `Lag.blk_tmaUnit` with the arrival schedule; over the promoted
  `Lemmas/Protocol/TmaUnitBlock.lean`, which adds `arrivals_le_units`, `notified_rec`,
  `issues_le_completions` and `short`). The copy case of a TMA unit object is not a `Lag` field:
  its shortness (`copies < n · (phase + 1)`) is not linear in the waiter's polls for `n > 1`, so
  the kernel states that lag itself. Test `Tests/Progress/HandoffBlockers.lean`.
- `ElectOrd.elections_le` (`Lemmas/Order/ElectLe.lean`, from tml-fa4's `elect_le`): with full-mask
  elections no lane is ahead of another lane of its warp in elections. `Flow.Code.glue_inl_some`,
  `glue_inr_some` (`Lemmas/Flow/GlueStep.lean`): the steps of a glued machine, for measures.
- Not done in this round: the reuse paths from chains (review item 2). FA4 proves its four reuse
  paths jointly by well-founded induction along the dependency order (`TmemReach*.lean`): the
  observation step of one object needs the paths of the object it gates on. A generic form needs
  a joint statement over a finite family of objects with their gates; it is the next library item.
- **Progress templates promoted from FA4** (review item 12, three of six): `Sched.reg_steps`
  (`Lemmas/Kernel/Progress/Reg.lean`, register requests; `warp_mate` needs only
  `L.block % 32 = 0`), `Sched.tc_steps` (`TcColl.lean`, warp-collective `tcgen05` events),
  `Sched.barGroup_sync_steps`/`barGroup_arrive_steps` (`BarGroup.lean`, named barriers whose
  events have participant groups). Each takes the kernel's facts as premises in the form FA4's
  `RegWaitFacts`, `TcWaitFacts`, `BarWaitFacts` state them, on the kernel's `Sched.Timed` machine
  (no FA4 type). Test `Tests/Progress/Collectives.lean` (one dispatcher over the four blocked
  kinds). FA4 keeps its copies until phase 3 instantiates the library there. Not promoted yet:
  `WarpColl` (it reads FA4's `nextKind`/`NextFacts` state classification), `Async`,
  `CollectiveTmem`.
- **Reuse paths of a family of objects** (review item 2): `Lemmas/Protocol/ReachJoint.lean`.
  `Reach.joint` is the one induction along the dependency order over `Reach.nodes` (thread events
  and commit notifications) for any family of goals; the goals `UnitAt`/`NotifyAt` export as
  `Unit.Reach`/`Notify.Reach` (`unit_reach`, `notify_reach`); inside the step a poll that
  precedes the node observes the unit of its use (`unit_content`, `notify_content`, on
  `Multi.Obs.content_of_reach`); `poll_guard`, `commit_notify`, `notify_rec` are the edges. The
  form is FA4's `TmemReach` with its kernel facts taken out: the kernel's step is its route facts
  only. The chain sketch of the review (`Notify.Reach.of_chain` from one second object) is not a
  separate lemma: the observation of the second object needs that object's paths, so a chain is
  a step of the joint induction, not a premise-free lemma. Test `Tests/Protocol/ReachJoint.lean`:
  a commit object and a unit object that gate each other (S-full with a P-ready-like object) get
  both reuse paths from the two route facts, 60 lines.
- **Tensor Memory race by writer kinds** (item 6): `Lemmas/Tcgen05/TmemRace.lean`
  (`TcMma.writesSafe_of`, `readsSafe_of`, `mm_of_po`, `ss_of_po`), the kernel-free part of FA4's
  `TcMmaWrites`/`TcMmaReads`; the kernel keeps only the cross-role MMA/store orders and the read
  orders. Test `Tests/Tc/TmemRace.lean`. The `TcRegions` record of the review sketch is not
  added: the region map only feeds the kernel's order premises, so it stays with them.
- **Tensor Memory read sources** (item 7): already in the library (`Lemmas/Tcgen05/TmemWriters.lean`:
  `Chain` with `readSource`, `accSource`, `stable`, `lastWrote`, the last writer of a cell's write
  table as the source of a load register or accumulator read). FA4's `TcLoads` adds only a
  dispatch over its roles. Nothing new written.
- **Mbarrier users from a role table** (item 8): `RoleTable.table_use`/`table_noUse`
  (`Lemmas/Kernel/Safety/TableUse.lean`): per-site literal tables of offsets and use kinds, one
  `decide` check per object family. The kernel supplies `site`, `sites`, `uses` and `hev` (from
  its shape tables, 1a's `Common/View.lean`/S6). Test `Tests/Kernel/TableUse.lean`.
- **A ring region's conflicts folded by uses** (item 9): `ConflictsOrdered.of_ring`
  (`Lemmas/Protocol/RingRegion.lean`): from the access classification (writers and readers of the
  region) and four use facts (RAW, WAR, same-use writers are one, writer/writer across uses).
  `NoIncObject.copy_before_read`/`read_before_copy` and `SingleTmaRing.copy_read_order` supply the
  RAW/WAR facts. Test `Tests/Protocol/RingRegion.lean` (with the rest of memory, `¬ Race`).
- **Shared lifetime from observations** (item 10): already in the library. A commit's arrive-on, a
  copy or an MMA finishes before its target CTA's exit when a thread of that CTA observes it
  before exiting: `CompletedBefore.of_observed`, `of_observesMma`, `SharedFinished.of_thread`
  (`Lemmas/Kernel/SharedLifetime.lean`), with the observation from `Notify.Obj.observes` /
  `Unit.Obj.handoff` and the reuse paths of `ReachJoint`. FA4's `LifetimeCommit` (436 lines) is its
  per-object exit facts (which thread of the target CTA polls which object before exiting), which
  stay kernel facts. Nothing new written.
- **Places** (item 11): `Lemmas/Flow/Places.lean` (`Places.passed`, `passed_move`,
  `passed_rmove`, and the list lemmas `countP_or_eq`, `countP_congr'`, `countP_split`), generic in
  the site type, `before`, `inRound` and the site's pc. tml-fa4's `Correction/Ref.lean` and
  `Softmax/Ref.lean` keep their copies until their next placed class: switching them changes
  their `passed` definition and re-checks every module above the role's reference invariant.
  `Places.kth` (the `k`-th event of a class at a passed point) is not written: no remaining
  premise uses it yet (D6's `tcgen05` schedule would, through W.d). Test `Tests/Flow/Places.lean`.
- **Asynchronous obligations** (item 12, fourth template): `Lemmas/Kernel/Progress/Async.lean`
  (`Sched.tensor_steps`, `store_steps`, `mma_steps`, `bulk_steps`, `arriveOn_steps`,
  `syncGuarded_of`, `StoreSources`), from FA4's `Progress/Async.lean` with FA4's code facts as
  premises. tml-fa4's `cp.async` arrive-ons need their own drain case (open). Test
  `Tests/Progress/Async.lean`.
- Not promoted (item 12): `WarpColl` reads FA4's classification of a thread's next event
  (`nextKind`, `NextFacts`, `WarpCollFacts`); a generic form needs that classification as a
  parameter of `Sched.Timed`, which is a design change of the progress interface, not a port.
  `CollectiveTmem` is FA4's `cta_group::2` pair protocol (`TmemWarpOps … 12`, `Tmem.Pair`);
  tml-fa4 is one CTA, so its Tensor Memory waits need the one-CTA form, not this port.
- **Warp collectives with a next-event classification** (item 12, fifth template, the progress
  interface change): `Lemmas/Kernel/Progress/WarpColl.lean`. Instead of extending `Sched.Timed`
  with a field, the classification is a parameter `AtColl : ∀ g, (M.code g).D → Prop` of the
  facts structure `Sched.WarpCollFacts M X key AtColl` (shape, last, exit, lag, FA4's fields with
  `nextKind d = .warp` replaced by `AtColl g d`), and `Sched.warpColl_steps` steps a released
  pending thread at such a state. This keeps `Timed` unchanged for every kernel; a kernel takes
  `AtColl` from its role tables (for tml-fa4: `RestAt` at a shuffle, election, vote or warp
  barrier site). FA4-only premises became hypotheses: `hlaunch`/`hcl` (no cancellation), `happ`
  (the assumptions on appended collective lanes), `hubx` (a lane reaching undefined behaviour is a
  counted extension). Test `Tests/Progress/WarpColl.lean`.
- **The `cp.async` drain is not written.** The library's copy completion step
  (`consistent_finishCopyRecord_initial`, `Lemmas/Step/CopyFinish*.lean`, about 1,400 lines) is for
  copies that complete through an mbarrier (`spec.completion = .mbarrier`). tml-fa4's ordinary
  `cp.async` copies complete by their group and the `cp.async.mbarrier.arrive.noinc` arrive-ons
  record on the K/V barriers separately, so the drain needs two new extension steps (write an
  ordinary copy's bytes; perform an arrive-on once the thread's earlier copies are done) with their
  consistency proofs, the size of the existing bulk drain.
- **The `cp.async` drain, planned (not written).** Two extension steps, mirroring the bulk drain:
  (a) *ordinary copy write*: a `cp.async` copy (`completion = .asyncGroup`) with
  `writeBytes = none` is completed by `Execution.finishCopy` without an object record (the bulk
  version `finishCopyRecord` adds the mbarrier record); its consistency reuses
  `CopyFinishMemory`/`CopyFinishVisibility` with the source premise of `BulkSources` (tml-fa4: the
  read-only K/V input bytes) and `AsyncCopy.WellFormed` for a group completion; (b) *arrive-on*: a
  `cp.async.mbarrier.arrive.noinc` with `arrived = false`, whose tracked copies are all written
  (`ArriveOk`, `TracksCpAsync`, so after (a) for each of them), sets `arrived` and appends its
  `.arrive 1 0` record with the object's checked reply (`Step.checkedRecord`, as
  `finishCopyRecord_arriveOk`), keeping `ObjectsOk` (`MatchesObject` at
  `Core/MBarrier/AsyncMBarrier.lean:90`). Then `Maximal.copy_written` and `Maximal.arrived` by the
  `not_grows` argument of `Maximal.bulk_notified`, under `Assumption.WfStep` (in-order) rather than
  `WfFree`.
- **`Sched.LagShort`** (`Lemmas/Kernel/Progress/Handoff.lean`, lane 1a request): `Lag` whose
  `early` fact is required only of a producer short of some waiter's waited use (counted events
  plus `δ` at most the waiter's successful polls). A lane that keeps issuing after its last counted
  event (tml-fa4's K/V drain lanes) need not be earlier than the schedule. `Lag.short` converts;
  `LagShort.blk`, `LagShort.blk_noInc`, `LagShort.pollBlocked_noInc` are the blockers, and the
  `Lag` versions are now one-line wrappers. The other `Lag` blockers keep their form (they reach
  `early` only through `blk`); a kernel that needs them for `LagShort` adds the same wrapper.
