-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorThread
public import Core.Async.CpAsync
public import Core.Async.AsyncStore
public import Core.Clc.ClcThread
public import Core.Sync.Barrier
public import Core.Sync.Shuffle
public import Core.Sync.Vote
public import Core.Sync.Redux
public import Core.Sync.Match
public import Core.Sync.ActiveMask
public import Core.Sync.Elect
public import Core.Sync.WarpBarrier
public import Core.Sync.Matrix
public import Core.Thread.SetMaxNReg
public import Core.Thread.Fence
public import Core.Tc.TcCommitThread
public import Core.Tc.TcThread

@[expose] public section

/-!
# Thread semantics: what one thread can do

What one thread does, as a function of the values its reads and shuffles return. Nothing here
mentions memory, other threads, or time.
-/

namespace PTX

noncomputable section

/-! ## THREAD-RUN — the traces of one thread
Statement: A thread starts at the first instruction with no registers set and executes the
  instruction at its source position. A false guard skips the instruction and a local instruction
  updates the thread's registers. Any other instruction performs an event whose returned values stay
  open. A pending fault, a source position outside the code or a failing local rule performs an
  event of undefined behaviour, and so does `trap`, which no assumption replaces, while `ret` and
  `exit` end the thread. The thread can perform exactly the finite event sequences that this
  construction yields, with no global scheduling order.

Defs: skip, widenMbarScope, Tmpl.thenWaitLd, tcLdTmpl, tcStTmpl, warpTmpl, localSregTmpl, eventTmpl,
  RuleId.tmpl, eventTmpl_rule, eventTmpl_tcLd_noWait, eventTmpl_tcSt_noWait, eventTmpl_tcSt_wait,
  eventTmpl_tcSt_afterWait, Out, out, Fires, Tau, EStep, Run, Produces

Source:
- §8.9.1 (program order)
- §9.3 (predicated execution)
- §9.7.14.6 (ret): "A return instruction executed in a top-level entry routine will terminate thread
    execution."
- §9.7.14.7 (exit): "Ends execution of a thread."
- §9.7.21.4 (trap): "Abort execution and generate an interrupt to the host CPU."

Direction: stricter

Applies: Local instruction and event traces

Premises: Instruction guards, local rules and event templates apply from the initial thread state.

Effect: Thread trace constraint in Consistent.thr; no global scheduling order. `ret` and `exit` end
  the thread (`.exit`); the decoder accepts only `.entry` kernels and no `call`, so every `ret` is
  in the top-level entry routine. `trap` is a `ub` event with its own reason `trap`: it aborts the
  kernel, so no execution that reaches it is accepted (stricter), and no kernel assumption can
  replace it because assumptions replace only `noRule` of a local instruction (THREAD-LOCAL). An
  `Op.unmodeled` event instruction and an event instruction whose family rule is none are a `ub`
  event with `noRule` (`eventTmpl`, `memTmpl`, `warpTmpl`).
  A read of special registers that change while the thread runs (`Tmpl.sreg`, THREAD-SREG) is
  instantiated with any value below each register's bound; the instruction's local rule then runs
  with these values, and its fault becomes the thread's pending fault.
  An atomic read-modify-write (`Tmpl.rmw`) is instantiated with any bytes read: its event records
  them and the bytes written, and when the operation has no result for them the event writes nothing
  and the thread's next event is `ub` with the operation's fault (THREAD-ATOMIC).
  `out t` is the outcome of the instruction at `t.pc`: a local step (`tau`), or the event it
  performs, as a template. A false guard skips the instruction; a pending fault, a `pc` outside the
  code, or a failing local rule is a `ub` event. `Run t l o` says that from `t` the thread can
  perform exactly the events `l`, with any returned values recorded in them, and is then in state
  `o` (`none`: it exited or performed `ub`). `Run` is inductive with no fuel, so a thread that loops
  locally forever performs no further event. A `pc` outside the code is a `ub` event although the
  ISA states no behaviour for it (stricter), and `widenMbarScope` is the identity unless a kernel
  assumption selects ASM-MBAR-SCOPE for the instruction's site (trust). A `tcgen05.ld` at a site a
  kernel assumption selects with `tcLdWait` (ASM-INTERFACE) is followed, at the same `pc`, by the
  event of a `tcgen05.wait::ld` (`tcLdTmpl`), as if that instruction came next (trust); at every
  other site `tcLdTmpl` is THREAD-TC's rule (`eventTmpl_tcLd_noWait`). A `tcgen05.st` selected by
  `tcStWaitLd` (ASM-INTERFACE) issues an implicit load wait at sub-step zero, then its original
  store at the same pc with sub-step reset on completion. A kernel assumption may also take a
  straight-line segment as one local step (THREAD-LOCAL).
-/

/-- Skip the instruction (guard false). -/
def skip (t : TState) : TState := { t with pc := t.pc + 1, sub := 0, acc := [] }

/-- At a site `pc` an assumption selects with `clusterScopeMbar`, `.cta`-scoped mbarrier
release arrivals and acquire waits take cluster scope. Relaxed operations and every other event
are unchanged. At any other site this is the identity. -/
def widenMbarScope (A : List Assumption) (pc : Nat) (m : Tmpl) : Tmpl :=
  if A.any (·.clusterScopeMbar pc) then
    match m with
    | .arrive l tx t count true .cta => .arrive l tx t count true .cluster
    | .wait l parity k true .cta => .wait l parity k true .cluster
    | other => other
  else m

/-- A `tcgen05.ld` template that continues at `pc` with sub-step 1; other templates unchanged. -/
def Tmpl.thenWaitLd (pc : Nat) : Tmpl → Tmpl
  | .tcLd a n shape k => .tcLd a n shape fun vals => { k vals with pc := pc, sub := 1 }
  | m => m

/-- A `tcgen05.ld` at a site an assumption selects with `tcLdWait`: the load (sub-step 0)
continues at the same `pc` with sub-step 1, which performs `tcgen05.wait::ld` and reads no
operand (a destination may be the address register). At any other site this is `tcTmpl`. -/
def tcLdTmpl (A : List Assumption) (L : Launch) (g : Nat) (t : TState) (op : Op) : Tmpl :=
  if A.any (·.tcLdWait t.pc) then
    if t.sub = 0 then (tcTmpl L g t op).thenWaitLd t.pc else .tc .waitLd { next t with sub := 0 }
  else tcTmpl L g t op

/-- Optionally precede a Tensor Memory store by a real load wait. The wait retains the
instruction's operands and pc. The store proceeds from sub-step one with its usual operands. -/
def tcStTmpl (A : List Assumption) (L : Launch) (g : Nat) (t : TState)
    (ta : Nat) (ss : List Opnd) (sh : TcShape) : Tmpl :=
  if A.any (·.tcStWaitLd t.pc) then
    if t.sub = 0 then
      if L.block % 32 = 0 then .tc .waitLd { t with sub := 1 } else .ub .noRule
    else tcTmpl L g { t with sub := 0 } (.tcSt ta ss sh)
  else tcTmpl L g t (.tcSt ta ss sh)

/-- The event of a warp collective with a rule (`WarpInstr.rule`): THREAD-SHFL, THREAD-VOTE,
THREAD-REDUX, THREAD-MATCH, THREAD-ACTIVEMASK, THREAD-ELECT or THREAD-WARP-BAR; every other
collective has no rule. -/
def warpTmpl (L : Launch) (g : Nat) (t : TState) (w : WarpInstr) : Tmpl :=
  match w.rule, w.kind, w.dsts, w.srcs, w.mask with
  | some .threadShfl, .shfl m, some d :: p, [a, b, c], some mask =>
    shflTmpl L g t m d p.head?.join a b c mask
  | some .threadVote, .vote .ballot neg, [some d], [.reg a], some mask =>
    voteTmpl L g t d a neg mask
  | some .threadVote, .vote mode neg, [some d], [.reg a], some mask =>
    voteModeTmpl L g t mode d a neg mask
  | some .threadRedux, .redux op _ _, [some d], [a], some mask =>
    reduxTmpl L g t op (w.ty == some (.int .s 32)) d a mask
  | some .threadMatch, .match_ all, d :: p, [a], some mask =>
    matchTmpl L g t all (if w.ty == some (.int .b 64) then 64 else 32) d p.head?.join a mask
  | some .threadActivemask, .activemask, [some d], [], none => activemaskTmpl t d
  | some .threadElect, .elect, [d, some p], [], some mask => electTmpl L g t d p mask
  | some .threadWarpBar, .barWarp, [], [], some mask => warpBarTmpl L g t mask
  | _, _, _, _, _ => .ub .noRule

/-- The event of an integer, move or conversion instruction that reads a special register whose
value changes while the thread runs: THREAD-SREG's read under the local rules THREAD-INT,
THREAD-MOVE and THREAD-CVT, and no rule otherwise. -/
def localSregTmpl (A : List Assumption) (L : Launch) (g : Nat) (t : TState) : RuleId → Op → Tmpl
  | .threadInt, op | .threadMove, op | .threadCvt, op => sregTmpl A L g t op
  | _, _ => .ub .noRule

/-- The event of a non-local instruction. -/
def eventTmpl (A : List Assumption) (L : Launch) (g : Nat) (t : TState) : Op → Tmpl
  | .mem a => memTmpl A L g t a
  | .warp w => warpTmpl L g t w
  | .matrix m => matrixTmpl L g t m
  | .barSync a _ => barTmpl L g t a none .sync
  | .barSyncN a b _ => barTmpl L g t a (some b) .sync
  | .barArrive a b _ => barTmpl L g t a (some b) .arrive
  | .cluster op => .cluster op (next t)
  | .setMaxReg inc n => SetMaxNReg.tmpl t inc n
  | op@(.cpTensor ..) => tensorTmpl L g t op
  | op@(.prefetchTensor ..) | op@(.prefetchBulk ..) => tensorPrefetchTmpl L g t op
  | op@(.cpAsync ..) | op@.cpAsyncCommit | op@(.cpAsyncWait ..) | op@(.cpAsyncArrive ..) =>
    cpAsyncTmpl L g t op
  | .asyncStore s => asyncStoreTmpl L g t s
  | op@(.cpTensorStore ..) | op@.bulkCommit | op@(.bulkWait ..) => tensorStoreTmpl L g t op
  | op@(.clcTryCancel ..) | op@(.clcQuery ..) => clcTmpl L g t op
  | .ret | .exit => .exit
  | .trap => .ub .trap
  | op@(.int _) | op@(.move _) | op@(.cvt _) => match op.rule with
    | some r => localSregTmpl A L g t r op
    | none => .ub .noRule
  | op@(.fence ..) => fenceTmpl L g t op
  | op@(.mbarInit ..) | op@(.mbarInval ..) | op@.fenceMbarInit
  | op@(.mbarArrive ..)
  | op@(.mbarWait ..) | op@(.cpBulk ..) => widenMbarScope A t.pc (tmaTmpl L g t op)
  | op@(.tcCommit ..) => tcCommitTmpl L g t op
  | op@(.tcLd ..) => tcLdTmpl A L g t op
  | .tcSt ta ss sh => tcStTmpl A L g t ta ss sh
  | op@(.tcAlloc ..) | op@(.tcDealloc ..) | op@(.tcRelinquish ..) | op@(.tcMma ..)
  | op@.tcFenceBefore | op@.tcFenceAfter | op@.tcWaitLd
  | op@.tcWaitSt | op@(.tcCp ..) | op@(.tcShift ..) => tcTmpl L g t op
  | _ => .ub .noRule

/-- The event template that rule `r` gives an instruction: the template function of the contract
entry `r` names. A local rule gives no event. -/
def RuleId.tmpl (A : List Assumption) (L : Launch) (g : Nat) (t : TState) : RuleId → Op → Tmpl
  | r, op@(.int _) | r, op@(.move _) | r, op@(.cvt _) => localSregTmpl A L g t r op
  | .threadAccess, .mem a | .threadAtomic, .mem a => memTmpl A L g t a
  | .threadShfl, .warp w | .threadVote, .warp w | .threadRedux, .warp w | .threadMatch, .warp w
  | .threadActivemask, .warp w | .threadElect, .warp w
  | .threadWarpBar, .warp w => warpTmpl L g t w
  | .threadMatrix, .matrix m | .threadMma, .matrix m => matrixTmpl L g t m
  | .threadBar, .barSync a _ => barTmpl L g t a none .sync
  | .threadBar, .barSyncN a b _ => barTmpl L g t a (some b) .sync
  | .threadBar, .barArrive a b _ => barTmpl L g t a (some b) .arrive
  | .clusterBarrier, .cluster op => .cluster op (next t)
  | .threadSetMaxNReg, .setMaxReg inc n => SetMaxNReg.tmpl t inc n
  | .threadTensorIssue, op => tensorTmpl L g t op
  | .threadTensorPrefetch, op => tensorPrefetchTmpl L g t op
  | .threadTensorStore, op => tensorStoreTmpl L g t op
  | .threadClc, op => clcTmpl L g t op
  | .threadTma, op => widenMbarScope A t.pc (tmaTmpl L g t op)
  | .threadCpAsync, op => cpAsyncTmpl L g t op
  | .threadAsyncStore, .asyncStore s => asyncStoreTmpl L g t s
  | .threadFence, op => fenceTmpl L g t op
  | .threadTcCommit, op => tcCommitTmpl L g t op
  | .threadTc, op@(.tcLd ..) => tcLdTmpl A L g t op
  | .threadTc, .tcSt ta ss sh => tcStTmpl A L g t ta ss sh
  | .threadTc, op => tcTmpl L g t op
  | .threadRun, .ret | .threadRun, .exit => .exit
  | .threadRun, .trap => .ub .trap
  | _, _ => .ub .noRule

/-- Closes `ub = t` where `t` reduces to `ub`, through `widenMbarScope` when present. -/
local macro "tmaUb" : tactic =>
  `(tactic| first | rfl | (simp only [RuleId.tmpl, widenMbarScope, tmaTmpl]; split <;> rfl))

/-- The event of an instruction is the template of the rule `Op.rule` names, and `ub noRule` when
it names none. -/
theorem eventTmpl_rule (A : List Assumption) (L : Launch) (g : Nat) (t : TState) (op : Op) :
    eventTmpl A L g t op = match op.rule with
      | some r => r.tmpl A L g t op
      | none => .ub .noRule := by
  cases op
  case mem a =>
    simp only [eventTmpl, Op.rule]
    cases h : a.rule with
    | none => simp only [memTmpl, h, reduceCtorEq, ↓reduceIte]
    | some r =>
      cases r <;> simp only [RuleId.tmpl, memTmpl, h, Option.some.injEq, reduceCtorEq, ↓reduceIte]
        <;> tmaUb
  case warp w =>
    simp only [eventTmpl, Op.rule]
    cases h : w.rule with
    | none => simp only [warpTmpl, h]
    | some r => cases r <;> simp only [RuleId.tmpl, warpTmpl, h] <;> tmaUb
  case tcMma m =>
    simp only [eventTmpl, Op.rule, tcTmpl]
    cases h : m.rule with
    | none => simp only [mmaTmpl, h]
    | some r =>
      have hr : r = .threadTc := by
        revert h; unfold TcMmaInstr.rule; split <;> simp_all
      subst hr; rfl
  case int i =>
    simp only [eventTmpl, Op.rule]
    cases i.rule <;> rfl
  case move m =>
    simp only [eventTmpl, Op.rule]
    cases m.rule <;> rfl
  case cvt c =>
    simp only [eventTmpl, Op.rule]
    cases c.rule <;> rfl
  case matrix m =>
    simp only [eventTmpl, Op.rule]
    cases h : m.rule with
    | none => simp only [matrixTmpl, h]; split <;> rfl
    | some r => cases r <;> first | rfl | (simp only [RuleId.tmpl, matrixTmpl, h]; split <;> tmaUb)
  all_goals first
    | rfl
    | (simp only [eventTmpl, Op.rule]; split <;> (try rfl); rename_i r _; cases r <;> tmaUb)

/-- At a site no assumption selects with `tcLdWait`, a `tcgen05.ld` is THREAD-TC's rule. -/
theorem eventTmpl_tcLd_noWait {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {ds : List Nat} {ta : Nat} {shape : TcShape} {red : Option TcLdRed}
    (h : A.any (·.tcLdWait t.pc) = false) :
    eventTmpl A L g t (.tcLd ds ta shape red) = tcTmpl L g t (.tcLd ds ta shape red) := by
  simp only [eventTmpl, tcLdTmpl, h, Bool.false_eq_true, ↓reduceIte]

/-- Existing assumptions preserve the store template when they select no prior wait. -/
theorem eventTmpl_tcSt_noWait {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {ta : Nat} {ss : List Opnd} {sh : TcShape}
    (h : A.any (·.tcStWaitLd t.pc) = false) :
    eventTmpl A L g t (.tcSt ta ss sh) = tcTmpl L g t (.tcSt ta ss sh) := by
  simp only [eventTmpl, tcStTmpl, h, Bool.false_eq_true, ↓reduceIte]

/-- At sub-step zero, a selected store issues its load wait without changing pc or registers. -/
theorem eventTmpl_tcSt_wait {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {ta : Nat} {ss : List Opnd} {sh : TcShape}
    (h : A.any (·.tcStWaitLd t.pc) = true) (hs : t.sub = 0) (hb : L.block % 32 = 0) :
    eventTmpl A L g t (.tcSt ta ss sh) = .tc .waitLd { t with sub := 1 } := by
  simp only [eventTmpl, tcStTmpl, h, hs, hb, ↓reduceIte]

/-- After the selected wait, the store uses the original operands and resets the sub-step. -/
theorem eventTmpl_tcSt_afterWait {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {ta : Nat} {ss : List Opnd} {sh : TcShape}
    (h : A.any (·.tcStWaitLd t.pc) = true) (hs : t.sub ≠ 0) :
    eventTmpl A L g t (.tcSt ta ss sh) = tcTmpl L g { t with sub := 0 } (.tcSt ta ss sh) := by
  simp only [eventTmpl, tcStTmpl, h, hs, ↓reduceIte]

/-- Outcome of the instruction at `t.pc`. -/
inductive Out where
  | tau (t : TState)
  | ev (e : Tmpl)

/-- The outcome of the instruction at the thread's source position: a local step, or the template
of the event it performs (a fault, a pc outside the code and a failing local rule give an
undefined-behaviour event). -/
def out (K : Kernel) (A : List Assumption) (L : Launch) (g : Nat) (t : TState) : Out :=
  match t.fault with
  | some f => .ev (.ub f)
  | none =>
    match K.code[t.pc]? with
    | none => .ev (.ub .pcOutOfRange)
    | some ins =>
      match guardHolds t ins.guard with
      | .error f => .ev (.ub f)
      | .ok false => .tau (skip t)
      | .ok true =>
        if ins.op.isLocal then
          match execLocalA A L g t ins.op with
          | .ok t' => .tau t'
          | .error f => .ev (.ub f)
        else .ev (eventTmpl A L g t ins.op)

/-- Event `e` instantiates template `m` at source position `pc`; `o` is the next state
(`none` after `exit` or `ub`). -/
def Fires (pc : Nat) : Tmpl → Event → Option TState → Prop
  | .setMaxReg inc n t, e, o => ∃ inst, e = ⟨pc, .setMaxReg inc n inst⟩ ∧ o = some t
  | .warpBar mask t, e, o => ∃ inst, e = ⟨pc, .warpBar mask inst⟩ ∧ o = some t
  | .elect mask k, e, o => ∃ inst leader, e = ⟨pc, .elect mask inst leader⟩ ∧ o = some (k leader)
  | .read a k, e, o => ∃ bs, bs.length = a.size ∧ e = ⟨pc, .rd a bs⟩ ∧ o = some (k bs)
  | .readNC a k, e, o => ∃ bs, bs.length = a.size ∧ e = ⟨pc, .nc a bs⟩ ∧ o = some (k bs)
  | .write a bs t, e, o => e = ⟨pc, .wr a bs⟩ ∧ o = some t
  | .rmw a f k, e, o => ∃ old, old.length = a.size ∧ e = ⟨pc, .rmw a old (f old).toOption⟩ ∧
      o = some (match f old with
        | .ok _ => k old
        | .error fault => { k old with fault := some fault })
  | .bar id t count mode, e, o => e = ⟨pc, .bar id count mode⟩ ∧ o = some t
  | .tensorStore addr s t, e, o => e = ⟨pc, .tensorStore addr s⟩ ∧ o = some t
  | .bulkCommit t, e, o => e = ⟨pc, .bulkCommit⟩ ∧ o = some t
  | .bulkWait mode n t, e, o => e = ⟨pc, .bulkWait mode n⟩ ∧ o = some t
  | .tensorIssue addr s t, e, o => e = ⟨pc, .tensorIssue addr s⟩ ∧ o = some t
  | .clcIssue s targets t, e, o => e = ⟨pc, .clcIssue s targets⟩ ∧ o = some t
  | .clcQuery q r t, e, o => e = ⟨pc, .clcQuery q r⟩ ∧ o = some t
  | .cluster op t, e, o => e = ⟨pc, .cluster op⟩ ∧ o = some t
  | .shfl m a b c k, e, o => ∃ recv ok, e = ⟨pc, .shfl m a b c recv ok⟩ ∧ o = some (k recv ok)
  | .vote mask a k, e, o => ∃ ballot, e = ⟨pc, .vote mask a ballot⟩ ∧ o = some (k ballot)
  | .voteMode mode mask a k, e, o => ∃ r, e = ⟨pc, .voteMode mode mask a r⟩ ∧ o = some (k r)
  | .redux op signed mask a k, e, o =>
    ∃ r, e = ⟨pc, .redux op signed mask a r⟩ ∧ o = some (k r)
  | .match_ all wide mask a k, e, o =>
    ∃ r p, e = ⟨pc, .match_ all wide mask a r p⟩ ∧ o = some (k r p)
  | .activemask k, e, o => ∃ r, e = ⟨pc, .activemask r⟩ ∧ o = some (k r)
  | .matrix op own k, e, o => ∃ recv, e = ⟨pc, .matrix op own recv⟩ ∧ o = some (k recv)
  | .exit, e, o => e = ⟨pc, .exit⟩ ∧ o = none
  | .ub f, e, o => e = ⟨pc, .ub f⟩ ∧ o = none
  | .mbInit m c t, e, o => e = ⟨pc, .mbInit m c⟩ ∧ o = some t
  | .mbInval m t, e, o => e = ⟨pc, .mbInval m⟩ ∧ o = some t
  | .fenceMbarInit t, e, o => e = ⟨pc, .fenceMbarInit⟩ ∧ o = some t
  | .fence sem scope t, e, o => e = ⟨pc, .fence sem scope⟩ ∧ o = some t
  | .fenceProxy k scope t, e, o => e = ⟨pc, .fenceProxy k scope⟩ ∧ o = some t
  | .arrive m tx t count release scope, e, o =>
    e = ⟨pc, .arrive m tx count release scope⟩ ∧ o = some t
  | .copy s t, e, o => e = ⟨pc, .copy s⟩ ∧ o = some t
  | .bulkPrefetch a t, e, o => e = ⟨pc, .bulkPrefetch a⟩ ∧ o = some t
  | .asyncCommit t, e, o => e = ⟨pc, .asyncCommit⟩ ∧ o = some t
  | .asyncWait n t, e, o => e = ⟨pc, .asyncWait n⟩ ∧ o = some t
  | .asyncArrive m noinc t, e, o => e = ⟨pc, .asyncArrive m noinc⟩ ∧ o = some t
  | .wait m q k acquire scope, e, o =>
    ∃ ok, e = ⟨pc, .wait m q ok acquire scope⟩ ∧ o = some (k ok)
  | .tc k t, e, o => e = ⟨pc, .tc k⟩ ∧ o = some t
  | .tcAllocStore dst t, e, o =>
    ∃ col, col < 2 ^ 16 ∧
      e = ⟨pc, .wr { loc := dst, size := 4 } (Value.bits 32 (BitVec.ofNat 64 col)).toBytes⟩ ∧
      o = some t
  | .tcLd a n shape k, e, o =>
    ∃ vals, vals.length = n ∧ e = ⟨pc, .tc (.ld a vals shape)⟩ ∧ o = some (k vals)
  | .tensorPrefetch addr s t, e, o => e = ⟨pc, .tensorPrefetch addr s⟩ ∧ o = some t
  | .sreg reads k, e, o =>
    ∃ vals, List.Forall₂ (fun v r => v < r.2) vals reads ∧
      e = ⟨pc, .sreg (reads.map Prod.fst) vals⟩ ∧ o = some (k vals)

section
variable (K : Kernel) (A : List Assumption) (L : Launch) (g : Nat)

/-- A local step: the thread moves from `t` to `t'` without performing an event. -/
def Tau (t t' : TState) : Prop := out K A L g t = .tau t'

/-- The thread in state `t` performs event `e` and is then in state `o`. -/
def EStep (t : TState) (e : Event) (o : Option TState) : Prop :=
  ∃ m, out K A L g t = .ev m ∧ Fires t.pc m e o

/-- From `t`, the thread can perform exactly the events `l` and is then in state `o`. -/
inductive Run : TState → List Event → Option TState → Prop
  | nil (t : TState) : Run t [] (some t)
  | step {t t1 t2 : TState} {e : Event} {rest : List Event} {o : Option TState} :
      Relation.ReflTransGen (Tau K A L g) t t1 → EStep K A L g t1 e (some t2) →
      Run t2 rest o → Run t (e :: rest) o
  | last {t t1 : TState} {e : Event} :
      Relation.ReflTransGen (Tau K A L g) t t1 → EStep K A L g t1 e none → Run t [e] none

/-- Thread `g` can produce the trace `l` from its initial state. -/
def Produces (l : List Event) : Prop := ∃ o, Run K A L g {} l o

end

end

end PTX
