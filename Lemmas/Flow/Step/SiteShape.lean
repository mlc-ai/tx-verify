-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.SiteCases
public import Lemmas.Flow.Ledger
public import Lemmas.Flow.ShflOps
public import Lemmas.Flow.Fragment
public import Lemmas.Flow.Step.ShapeClasses
public import Lemmas.Flow.Step.ShapeTc

@[expose] public section

/-! # Shape tables by case analysis

A proof tool for the shape table of a site machine (`Code.Shape`, `Lemmas/Flow/Ledger.lean`), one
state at a time (`Code.ShapeAt`, `Code.Shape.of_at`). Nothing here is specific to a kernel.

* One inversion lemma per class of event instruction says which event it fires, in terms of the
  values its operands read: `shape_shfl`, `shape_vote`, `shape_ld` (a scalar or vector element
  load, or its undefined behaviour), `shape_wait`, `shape_arrive`, `shape_tensorStore`,
  `shape_bulkCommit`, `shape_bulkWait`, `shape_setMaxReg`, `shape_exit`, and those of
  `Step/ShapeClasses.lean` (named barriers, warp barriers, elections, `mbarrier.init`, proxy
  fences, `tcgen05.commit`, tensor copies, stores, `cp.async` copies, commits and arrivals, loads
  and stores located by `accessLoc`). Each concludes `P e` from `P` of the event it
  names, so it applies to any goal about `e`. A class beyond these is added by a rule of the hook
  `shape_inv hf` (`macro_rules`), which `site_shape` tries when the instruction has no lemma of
  its own or its lemma does not apply.
* `site_read [vals]` closes an operand read `readBits L g t w o = .ok ?v` (also `readValue`,
  `readPred`) from the site's facts: a register's value is the value table's entry
  (`regs_of_factsFrom`), simplified by the role's value lemmas `vals`, and the result fixes `?v`.
* `shape_close` closes a goal `Ev d ⟨pc, k⟩` whose shape names the event up to existential
  witnesses and alternatives.
* `site_shape x … except [site => proof, …] families [.c i … => proof, …] skip_by (tac)
  unfolding [Ev, …] reg_vals [lemmas] addr_by (tac)` splits the site variables like
  `site_cases` (a `families` entry keeps its constructor's fields whole and proves the family
  once), and at each site reads the
  instruction, applies the inversion lemma of its class, closes the operand reads by
  `site_read`, the other side conditions (addresses, launch facts) by the role's `addr_by`, and
  the shape by `shape_close` after unfolding `Ev` with `unfolding`.
* `stop_cases x … unsplit [c, …] skip_by (tac) unfolding [Ev, …] trans [ret, lemmas]` proves the
  stop condition of `Fragment.OkAt` (the machine stops exactly on a returned value of another kind
  than the return-kind table `ret` gives) by evaluating the transition on each shape.
* `ref_cases x … unsplit [c, …] skip_by (tac) unfolding [Ev, …] trans [lemmas] using (tac)`
  reduces the `ref_next` obligation of `Fragment.OkAt` the same way and leaves the role's reasoning
  about `Ref` and `Expect` to its tactic.
* In both, the sites of a constructor named in `unsplit` are one goal with its fields as variables
  (a family whose transition does not depend on the fields' values), instead of one per value. -/

namespace PTX.Flow
open PTX PTX.Proof
open Lean Meta Elab Tactic

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The shape obligation of one state: every event fired at its site has its shape. -/
def Code.ShapeAt (C : Code K A L g) (Ev : C.D → Event → Prop) (d : C.D) : Prop :=
  ∀ {t : TState} {ins : Instr} {e : Event} {o : Option TState}, C.AtD d t → C.inv d →
    K.code[C.pc d]? = some ins → Fires (C.pc d) (eventTmpl A L g t ins.op) e o → Ev d e

theorem Code.Shape.of_at {C : Code K A L g} {Ev : C.D → Event → Prop}
    (h : ∀ d, C.ShapeAt Ev d) : C.Shape Ev :=
  fun hat hi hc hf => h _ hat hi hc hf

/-- A register's value at a concrete state is its value table's entry. -/
theorem regs_of_factsFrom {R : Nat → Option Value} {live : List Nat} {val : Nat → Value}
    (h : Holds R (factsFrom live val)) {r : Nat} (hr : r ∈ live) : R r = some (val r) :=
  holds_mem h (mem_factsFrom hr)

variable {t : TState} {pc : Nat} {e : Event} {o : Option TState} {P : Event → Prop}

/-- A full-mask shuffle of a 4-byte value. -/
theorem shape_shfl {mode : ShflMode} {d : Nat} {p : Option Nat} {a b c mask : Opnd}
    {av : Value} {bv cv m : BitVec 64} (hf : Fires pc (shflTmpl L g t mode d p a b c mask) e o)
    (ha : readValue L g t 32 a = .ok av) (hb : readBits L g t 32 b = .ok bv)
    (hc : readBits L g t 32 c = .ok cv) (hm : readBits L g t 32 mask = .ok m)
    (hfull : m.toNat = 2 ^ 32 - 1) (hav : av.bytes = 4) (hblk : L.block % 32 = 0)
    (hP : ∀ recv ok, P ⟨pc, .shfl mode av bv.toNat cv.toNat recv ok⟩) : P e := by
  obtain ⟨recv, ok, rfl⟩ := fires_shflTmpl hm ha hb hc hfull hblk hav hf
  exact hP recv ok

/-- A full-mask ballot. -/
theorem shape_vote {d a : Nat} {neg : Bool} {mask : Opnd} {m : BitVec 64} {pv : Bool}
    (hf : Fires pc (voteTmpl L g t d a neg mask) e o) (hp : readPred L g t (.reg a) = .ok pv)
    (hm : readBits L g t 32 mask = .ok m) (hfull : m.toNat = 2 ^ 32 - 1)
    (hblk : L.block % 32 = 0) (hP : ∀ b, P ⟨pc, .vote (2 ^ 32 - 1) (pv != neg) b⟩) : P e := by
  obtain ⟨b, rfl⟩ := fires_voteTmpl hm hp hfull hblk hf
  exact hP b

/-- An element of a load: a read of the element's `w / 8` bytes at the effective address, or
undefined behaviour (a misaligned address). -/
theorem shape_ld {sp : Space} {w : Nat} {ds : List Nat} {base : Nat} {off : Int} {loc : Loc}
    {j : Nat} (hf : Fires pc (loadTmpl A L g t sp false w ds base off) e o)
    (hea : effAddr L g t sp base off = .ok loc) (hs : t.sub = j)
    (hrd : ∀ bs : List (Option Byte), bs.length = w / 8 →
      P ⟨pc, .rd { loc := loc.at (w / 8 * j), size := w / 8, elem := j } bs⟩)
    (hub : ∀ f, P ⟨pc, .ub f⟩) : P e := by
  simp only [loadTmpl, hea, hs, elemAcc, bind, Except.bind, Bool.false_eq_true, ↓reduceIte]
    at hf
  split_ifs at hf
  · simp only [throw, throwThe, MonadExceptOf.throw, Fires] at hf
    obtain ⟨rfl, -⟩ := hf
    exact hub _
  · simp only [pure, Except.pure, Fires] at hf
    obtain ⟨bs, hl, rfl, -⟩ := hf
    exact hrd bs hl

/-- `shape_ld` with the misalignment condition kept: an element of a load located by its address
register reads its `w / 8` bytes, and is undefined behaviour only when its access is misaligned
(Core's `elemAcc`: a zero width, or an address that is not a multiple of the whole access). A
role whose reference invariant gives the alignment discharges its `ref_safe` at the site. -/
theorem shape_ldM {sp : Space} {w : Nat} {ds : List Nat} {base : Nat} {off : Int} {loc : Loc}
    {j : Nat} (hf : Fires pc (loadTmpl A L g t sp false w ds base off) e o)
    (hea : effAddr L g t sp base off = .ok loc) (hs : t.sub = j)
    (hrd : ∀ bs : List (Option Byte), bs.length = w / 8 →
      P ⟨pc, .rd { loc := loc.at (w / 8 * j), size := w / 8, elem := j } bs⟩)
    (hub : w / 8 = 0 ∨ loc.addr % (w / 8 * ds.length) ≠ 0 → P ⟨pc, .ub .misaligned⟩) : P e := by
  simp only [loadTmpl, hea, hs, elemAcc, bind, Except.bind, Bool.false_eq_true, ↓reduceIte]
    at hf
  split_ifs at hf with hm
  · simp only [throw, throwThe, MonadExceptOf.throw, Fires] at hf
    obtain ⟨rfl, -⟩ := hf
    exact hub hm
  · simp only [pure, Except.pure, Fires] at hf
    obtain ⟨bs, hl, rfl, -⟩ := hf
    exact hrd bs hl

/-- A poll of an mbarrier at a site where no assumption widens its scope. -/
theorem shape_wait {p base : Nat} {off : Int} {par : Opnd} {acq : Bool} {sc : MbarScope}
    {m : Loc} {q : BitVec 64}
    (hf : Fires pc (eventTmpl A L g t (.mbarWait p base off par acq sc)) e o)
    (hA : A.any (·.clusterScopeMbar t.pc) = false) (hq : readBits L g t 32 par = .ok q)
    (hm : mbarLoc L g t base off = .ok m) (hP : ∀ ok, P ⟨pc, .wait m (q.toNat % 2) ok acq sc⟩) :
    P e := by
  obtain ⟨ok, hk⟩ := fires_wait_exact hA hm hq hf
  obtain ⟨epc, k⟩ := e
  have := fires_pc hf
  simp only at hk this
  subst hk this
  exact hP ok

/-- An arrival on an mbarrier at a site where no assumption widens its scope. -/
theorem shape_arrive {base : Nat} {off : Int} {tx count : Opnd} {rel : Bool} {sc : MbarScope}
    {st : Option Nat} {m : Loc} {b n : BitVec 64}
    (hf : Fires pc (eventTmpl A L g t (.mbarArrive base off tx count false rel sc st)) e o)
    (hA : A.any (·.clusterScopeMbar t.pc) = false) (hb : readBits L g t 32 tx = .ok b)
    (hn : readBits L g t 32 count = .ok n) (hm : mbarLoc L g t base off = .ok m)
    (hP : P ⟨pc, .arrive m b.toNat n.toNat rel sc⟩) : P e := by
  have hk := fires_arrive_exact hA hm hb hn hf
  obtain ⟨epc, k⟩ := e
  have := fires_pc hf
  simp only at hk this
  subst hk this
  exact hP

/-- A tensor store: its event, or undefined behaviour. -/
theorem shape_tensorStore {map : Opnd} {cs : List Opnd} {src : Nat} {off : Int}
    {policy : Option Opnd} {mode : TensorMode} {reduce : Option AtomOp}
    (hf : Fires pc (tensorStoreTmpl L g t (.cpTensorStore map cs src off policy mode reduce)) e o)
    (hts : ∀ a s, P ⟨pc, .tensorStore a s⟩) (hub : ∀ f, P ⟨pc, .ub f⟩) : P e := by
  simp only [tensorStoreTmpl, bind, Except.bind, pure, Except.pure] at hf
  cases hsp : tensorStoreSpec L g t map cs src off policy mode reduce with
  | error f =>
    simp only [hsp, ofExec, Fires] at hf
    obtain ⟨rfl, -⟩ := hf
    exact hub f
  | ok q =>
    obtain ⟨a, s⟩ := q
    simp only [hsp, ofExec, Fires] at hf
    obtain ⟨rfl, -⟩ := hf
    exact hts a s

/-- A bulk-group commit. -/
theorem shape_bulkCommit (hf : Fires pc (tensorStoreTmpl L g t .bulkCommit) e o)
    (hP : P ⟨pc, .bulkCommit⟩) : P e := by
  simp only [tensorStoreTmpl, Fires] at hf
  rw [hf.1]
  exact hP

/-- A wait for bulk groups. -/
theorem shape_bulkWait {mode : BulkGroup.WaitMode} {n : Nat}
    (hf : Fires pc (tensorStoreTmpl L g t (.bulkWait mode n)) e o)
    (hP : P ⟨pc, .bulkWait mode n⟩) : P e := by
  simp only [tensorStoreTmpl, Fires] at hf
  rw [hf.1]
  exact hP

/-- A `setmaxnreg` of a legal count. -/
theorem shape_setMaxReg {inc : Bool} {n : Nat} (hf : Fires pc (SetMaxNReg.tmpl t inc n) e o)
    (hn : SetMaxNReg.validCount n = true) (hP : ∀ inst, P ⟨pc, .setMaxReg inc n inst⟩) : P e := by
  simp only [SetMaxNReg.tmpl, hn, ↓reduceIte, Fires] at hf
  obtain ⟨inst, rfl, -⟩ := hf
  exact hP inst

/-- The exit (`ret` or `exit`). -/
theorem shape_exit (hf : Fires pc Tmpl.exit e o) (hP : P ⟨pc, .exit⟩) : P e := by
  simp only [Fires] at hf
  rw [hf.1]
  exact hP

end

/-- `site_read [vals]`: an operand read from the site's facts `hF` (in context as `hF`). -/
syntax "site_read " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

set_option hygiene false in
macro_rules
  | `(tactic| site_read [$vs,*]) => `(tactic| first
      | rfl
      | (simp (disch := lit_mem) only [PTX.readBits, PTX.readValue, PTX.readPred, PTX.readReg,
          PTX.effAddr, PTX.Flow.regs_of_factsFrom hF, Option.getD_some, Option.getD_none,
          bind, Except.bind, pure, Except.pure, $vs,*]
         try rfl))

/-- `site_acc [vals]`: the footprint `accessAcc L g t a = .ok ?acc` of an access located by
`accessLoc` (a `.local` load or store), a `cp.async` source size or an mbarrier's location, from
the site's facts `hF` and sub-step `hat`. -/
syntax "site_acc " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

set_option hygiene false in
macro_rules
  | `(tactic| site_acc [$vs,*]) => `(tactic| (
      simp (config := { decide := true }) (disch := lit_mem) only [PTX.accessAcc,
        PTX.accessLoc, PTX.cpAsyncSourceSize, PTX.MemAccess.strongLocOk, PTX.mbarLoc,
        PTX.effAddr, PTX.sharedEffAddr, PTX.readBits, PTX.readReg,
        PTX.Flow.regs_of_factsFrom hF, hat.2.1, PTX.DType.width, PTX.elemAcc,
        PTX.MemAccess.semAcc, Option.getD_some, Option.getD_none, bind, Except.bind, pure,
        Except.pure, Functor.map, Except.map, Nat.reduceDiv, Nat.reduceMul, ↓reduceIte,
        decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq, reduceCtorEq, Bool.or_eq_true,
        Bool.and_eq_true, eq_self_iff_true, not_true_eq_false, not_false_eq_true, true_or,
        or_true, false_or, or_false, and_true, true_and, $vs,*]
      -- an alignment test the evaluation leaves on a symbolic base (an mbarrier at the shared
      -- base plus an offset): its failing branch by `omega` from an alignment fact in context
      -- (the base's alignment from `Pre`, which the role states as a hypothesis)
      try (split_ifs <;> first | (exfalso; omega) | skip)
      try with_reducible rfl))

/-- `shape_close`: a goal naming one event up to witnesses, conjunctions and alternatives, with
the condition of an alternative introduced as a hypothesis (`shape_ldM`). A conjunction's right
side is tried first, so that an event equation there fixes the witnesses
before a side fact (a store's `storeValue … = .ok v'`) is closed from the hypotheses; then its
left side first. -/
syntax "shape_close" : tactic
macro_rules
  | `(tactic| shape_close) => `(tactic| first
      | rfl
      | exact True.intro
      | assumption
      | (intro; shape_close)
      | (apply Exists.intro; shape_close)
      | (apply And.intro <;> [skip; shape_close] <;> shape_close)
      | (apply And.intro <;> shape_close)
      | (left; shape_close)
      | (right; shape_close))

/-- `shape_inv hf`: apply the inversion lemma of an instruction class `site_shape` does not know
to the goal `P e`, from `hf : Fires pc (eventTmpl …) e o`. A kernel or a library module adds a
rule with `macro_rules` (`refine my_shape hf ?_ …`); `site_shape` then closes the side goals and
the shape goals as for its own lemmas. By default it fails. -/
syntax "shape_inv " ident : tactic
macro_rules | `(tactic| shape_inv $_) => `(tactic| fail "shape_inv: no inversion lemma")

set_option hygiene false in
/-- The two sub-steps of `tcgen05.alloc` (the sub-step selects the lemma, so the site's `hat.2.1`
is passed) and `tcgen05.relinquish_alloc_permit`. -/
macro_rules
  | `(tactic| shape_inv $hf) => `(tactic| first
      | apply PTX.Flow.shape_tcAlloc $hf hat.2.1
      | apply PTX.Flow.shape_tcAllocWr $hf hat.2.1
      | apply PTX.Flow.shape_tcRelinquish $hf)

/-- The inversion lemmas of the instruction at `pc`, by its class, in the order they are tried,
each with the template function its hypothesis names (`none`: the hypothesis names `eventTmpl`
itself). -/
meta def shapeLemmas (K code : Expr) (pc : Nat) : MetaM (List (Name × Option Name)) := do
  let some ins ← instrAt K code pc | throwError "site_shape: no instruction at {pc}"
  let op ← whnfD ((← whnfD ins).getArg! 1)
  if op.isAppOfArity ``PTX.Op.barSyncN 3 then
    return [(``PTX.Flow.shape_barSyncN, none), (``PTX.Flow.shape_barSyncNR, none),
      (``PTX.Flow.shape_barSyncN_block, none)]
  if op.isAppOfArity ``PTX.Op.barSync 2 then
    return [(``PTX.Flow.shape_barSync, none), (``PTX.Flow.shape_barSyncR, none)]
  if op.isAppOfArity ``PTX.Op.barArrive 3 then
    return [(``PTX.Flow.shape_barArriveImm, none), (``PTX.Flow.shape_barArriveR, none)]
  if op.isAppOfArity ``PTX.Op.mbarInit 3 then
    return [(``PTX.Flow.shape_mbInit, none), (``PTX.Flow.shape_mbInitR, none),
      (``PTX.Flow.shape_mbInitAny, none)]
  if op.isAppOfArity ``PTX.Op.mem 1 then
    let a := op.appArg!
    let k ← whnfD (← mkAppM ``PTX.MemAccess.kind #[a])
    -- located by its address register (`memTmpl`'s direct rule) and weak: `loadTmpl` or
    -- `storeTmpl`; every other load or store goes to `accessTmpl` (`.local`, a `.shared`
    -- variable)
    let sp ← whnfD (← mkAppM ``PTX.MemAccess.locSpace? #[a])
    let base ← whnfD (← mkAppM ``PTX.Addr.base #[← mkAppM ``PTX.MemAccess.addr #[a]])
    let sem ← whnfD (← mkAppM ``PTX.MemAccess.sem #[a])
    let nc ← whnfD (← mkAppM ``PTX.MemAccess.nc #[a])
    let direct := sp.isAppOfArity ``Option.some 2 && base.isAppOfArity ``PTX.AddrBase.reg 2 &&
      sem.isConstOf ``PTX.Sem.weak
    if k.isConstOf ``PTX.MemKind.load then
      return if !direct then [(``PTX.Flow.shape_accessLd, none)]
        else if nc.isConstOf ``Bool.true then [(``PTX.Flow.shape_ldNc, some ``PTX.loadTmpl)]
        else [(``shape_ld, some ``PTX.loadTmpl), (``shape_ldM, some ``PTX.loadTmpl)]
    if k.isConstOf ``PTX.MemKind.store then
      return if direct then
          [(``PTX.Flow.shape_st, some ``PTX.storeTmpl),
            (``PTX.Flow.shape_stM, some ``PTX.storeTmpl), (``PTX.Flow.shape_store, none)]
        else [(``PTX.Flow.shape_accessSt, none), (``PTX.Flow.shape_store, none)]
    return [(``PTX.Flow.shape_store, none)]
  return [← shapeLemma K code pc]
where shapeLemma (K code : Expr) (pc : Nat) : MetaM (Name × Option Name) := do
  let some ins ← instrAt K code pc | throwError "site_shape: no instruction at {pc}"
  let ins ← whnfD ins
  let op ← whnfD (ins.getArg! 1)
  let some c := op.getAppFn.constName? | throwError "site_shape: unknown instruction {op}"
  if c == ``PTX.Op.mbarWait then return (``shape_wait, none)
  if c == ``PTX.Op.mbarArrive then return (``shape_arrive, none)
  if c == ``PTX.Op.ret || c == ``PTX.Op.exit then return (``shape_exit, some ``PTX.Tmpl.exit)
  if c == ``PTX.Op.setMaxReg then return (``shape_setMaxReg, some ``PTX.SetMaxNReg.tmpl)
  if c == ``PTX.Op.cpTensorStore then return (``shape_tensorStore, some ``PTX.tensorStoreTmpl)
  if c == ``PTX.Op.bulkCommit then return (``shape_bulkCommit, some ``PTX.tensorStoreTmpl)
  if c == ``PTX.Op.bulkWait then return (``shape_bulkWait, some ``PTX.tensorStoreTmpl)
  if c == ``PTX.Op.warp then
    let kind ← whnfD (← mkAppM ``PTX.WarpInstr.kind #[op.appArg!])
    match kind.getAppFn.constName? with
    | some ``PTX.WarpKind.shfl => return (``shape_shfl, some ``PTX.shflTmpl)
    | some ``PTX.WarpKind.vote => return (``shape_vote, some ``PTX.voteTmpl)
    | _ => pure ()
  if c == ``PTX.Op.barSync then return (``PTX.Flow.shape_barSync, none)
  if c == ``PTX.Op.barSyncN then return (``PTX.Flow.shape_barSyncN, none)
  if c == ``PTX.Op.mbarInit then return (``PTX.Flow.shape_mbInit, none)
  if c == ``PTX.Op.tcCommit then
    let mk ← whnfD (op.getArg! 3)
    return if mk.isAppOfArity ``Option.none 1 then (``PTX.Flow.shape_tcCommitOne, none)
      else (``PTX.Flow.shape_tcCommit, none)
  if c == ``PTX.Op.cpTensor then return (``PTX.Flow.shape_cpTensor, none)
  if c == ``PTX.Op.fence then return (``PTX.Flow.shape_fenceProxy, some ``PTX.Tmpl.fenceProxy)
  if c == ``PTX.Op.cpAsync then return (``PTX.Flow.shape_cpAsync, none)
  if c == ``PTX.Op.cpAsyncCommit then return (``PTX.Flow.shape_cpAsyncCommit, none)
  if c == ``PTX.Op.cpAsyncArrive then return (``PTX.Flow.shape_cpAsyncArrive, none)
  if c == ``PTX.Op.warp then
    let kind ← whnfD (← mkAppM ``PTX.WarpInstr.kind #[op.appArg!])
    match kind.getAppFn.constName? with
    | some ``PTX.WarpKind.barWarp => return (``PTX.Flow.shape_warpBar, none)
    | some ``PTX.WarpKind.elect => return (``PTX.Flow.shape_elect, none)
    | _ => pure ()
  throwError "site_shape: no inversion lemma for the instruction at {pc}: {op}"

/-- `tmpl_unfold hf f`: unfold the template of `hf : Fires pc m e o` until its head is `f`. -/
elab "tmpl_unfold " h:ident ppSpace f:ident : tactic => withMainContext do
  let decl ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars decl.type
  unless ty.isAppOfArity ``PTX.Fires 4 do throwError "tmpl_unfold: expected Fires pc m e o"
  let m := ty.getArg! 1
  let f ← realizeGlobalConstNoOverloadWithInfo f
  let m' ← withCanUnfoldPred (fun _ ci => pure (ci.name != f)) (whnfD m)
  unless m'.getAppFn.isConstOf f do
    throwError "tmpl_unfold: the template does not unfold to {f}: {m'}"
  let ty' := mkApp4 (ty.getAppFn) (ty.getArg! 0) m' (ty.getArg! 2) (ty.getArg! 3)
  let g ← (← getMainGoal).replaceLocalDeclDefEq decl.fvarId ty'
  replaceMainGoal [g]

/-- The machine and program counter of a goal `C.ShapeAt Ev d`. -/
meta def shapeAtPc (ty : Expr) : MetaM (Expr × Nat) := do
  let ty ← whnfR (← instantiateMVars ty)
  unless ty.isAppOfArity ``Code.ShapeAt 7 do
    throwError "site_shape: expected C.ShapeAt Ev d, got {ty}"
  let C := ty.getArg! 4
  let d := ty.getArg! 6
  let pc ← natValue (← mkAppM ``Code.pc #[C, d])
  return (ty.getArg! 0, pc)

/-- `site_shape_step unfolding [Ev, …] reg_vals [lemmas] addr_by (tac)`: the shape obligation of a
literal site. -/
syntax "site_shape_step " "unfolding " "[" Lean.Parser.Tactic.simpLemma,* "]"
  " reg_vals " "[" Lean.Parser.Tactic.simpLemma,* "]" " addr_by " "(" tacticSeq ")" : tactic

set_option hygiene false in
elab_rules : tactic
  | `(tactic| site_shape_step unfolding [$us,*] reg_vals [$vs,*] addr_by ($addr:tacticSeq)) =>
    withMainContext do
    let (K, pc) ← shapeAtPc (← getMainTarget)
    let code ← mkAppM ``PTX.Kernel.code #[K]
    let lemmas ← try shapeLemmas K code pc catch _ => pure []
    evalTactic (← `(tactic| (
      intro t ins e o hat hi hc hf
      try have hF : Holds t.regs (PTX.Flow.factsFrom _ _) := hat.2.2.2.2
      obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup)))))
    -- the side goals of the applied lemma, then the shape goals (the sub-step `t.sub = j` as the
    -- site's literal, so that an element index is the literal, not a projection of the state);
    -- a goal for a value of a lemma's implicit argument (a location, a size) is assigned by them
    -- and is not closed on its own
    let finish : TacticM Unit := do
      evalTactic (← `(tactic| (
        all_goals try first
          | try_rt (rw [hat.2.1]; site_norm; rfl)
          | exact hat.2.1
          | try_rt (site_read [$vs,*]; done)
          | try_rt (site_acc [$vs,*]; done)
          | (($addr); done)
          | try_rt (rw [hat.1]; decide)
          | try_rt decide)))
      let gs ← getGoals
      let props ← gs.filterM fun g => do Meta.isProp (← g.getType)
      setGoals props
      -- a misalignment condition (`shape_ldM`, `shape_stM`) names the literal instruction's
      -- registers (`MemAccess.regs`): reduce their count so that it meets the table's condition
      evalTactic (← `(tactic| all_goals try simp only [PTX.MemAccess.regs,
        List.filterMap_cons, List.filterMap_nil, id_eq, List.length_cons, List.length_nil]))
      evalTactic (← `(tactic| all_goals (intros; simp only [Bool.bne_false, $us,*]; shape_close)))
      let rest ← (gs.filter (!props.contains ·)).filterM fun g => do return !(← g.isAssigned)
      setGoals ((← getGoals) ++ rest)
    -- the class's lemmas in order, each with its side and shape goals (a store lemma does not
    -- fit every memory instruction: `shape_st` needs the stored element, which a symbolic
    -- sub-step of a vector store does not select), else a rule of the hook
    let mut errs : Array MessageData := #[]
    for (lem, tgt) in lemmas do
      let s ← saveState
      try
        if let some f := tgt then
          evalTactic (← `(tactic| tmpl_unfold hf $(mkIdent f)))
          -- a load's or store's width is the access's `elem.width`: a numeral from here on, in
          -- the event's byte count and in a store's `storeValue`
          evalTactic (← `(tactic| try dsimp only [PTX.DType.width] at hf))
        evalTactic (← `(tactic| apply $(mkIdent lem):ident hf))
        finish
        return
      catch e =>
        s.restore
        errs := errs.push m!"{lem}: {e.toMessageData}"
    -- the hook; if it has no rule either, every attempt's failure is reported with its lemma
    try
      evalTactic (← `(tactic| shape_inv hf))
      finish
    catch e =>
      if errs.isEmpty then throw e
      let all := errs.push m!"shape_inv: {e.toMessageData}"
      throwError m!"site_shape: at pc {pc} every inversion lemma failed:" ++
        indentD (MessageData.joinSep all.toList Format.line)

/-- `site_shape x … except [site => proof, …] families [.c i … => proof, …] skip_by (tac)
unfolding [Ev, …] reg_vals [lemmas] addr_by (tac)`: the shape obligations `C.ShapeAt Ev d` of all
sites of the variables `x …`. A `families` entry keeps the fields of its constructor unsplit,
names them `i …`, and proves the family's one goal with its proof (as in `site_cases`). -/
syntax "site_shape " (ppSpace colGt ident)+ (" except " "[" siteOverride,* "]")?
  (" families " "[" siteOverride,* "]")?
  (" skip_by " "(" tacticSeq ")")? " unfolding " "[" Lean.Parser.Tactic.simpLemma,* "]"
  " reg_vals " "[" Lean.Parser.Tactic.simpLemma,* "]" " addr_by " "(" tacticSeq ")" : tactic

elab_rules : tactic
  | `(tactic| site_shape $xs* $[except [$ovs,*]]? $[families [$fms,*]]?
      $[skip_by ($skip:tacticSeq)]?
      unfolding [$us,*] reg_vals [$vs,*] addr_by ($addr:tacticSeq)) => withMainContext do
    let fvs ← xs.toList.mapM fun x => do return (← getLocalDeclFromUserName x.getId).fvarId
    let (gs, famOut) ← familySites fms skip (← getMainGoal) fvs fun prf => do
      evalTactic (← `(tactic| exact $prf))
    let ovs : Array (TSyntax `term × TSyntax `term) := match ovs with
      | some o => o.getElems.map fun ov => (⟨ov.raw[0]⟩, ⟨ov.raw[2]⟩)
      | none => #[]
    let mut unused := ovs.map (·.1)
    let mut out := []
    for g in gs do
      setGoals [g]
      evalTactic (← `(tactic| try dsimp only [Fin.reduceFinMk, Fin.isValue]))
      if let some skip := skip then
        evalTactic (← `(tactic| try (($skip); done)))
        if (← getUnsolvedGoals).isEmpty then continue
      let g ← getMainGoal
      let site ← g.withContext do goalSite (← g.getType)
      let mut chosen := none
      if let some site := site then
        for (p, prf) in ovs do
          let hit ← g.withContext do withNewMCtxDepth do
            let pe ← Term.elabTerm p (← inferType site)
            Term.synthesizeSyntheticMVarsNoPostponing
            isDefEq pe site
          if hit then
            chosen := some prf
            unused := unused.filter (· != p)
            break
      -- a runtime error (heartbeats, recursion depth) is reported with its site as well
      let tac ← match chosen with
        | some prf => `(tactic| exact $prf)
        | none => `(tactic| site_shape_step unfolding [$us,*] reg_vals [$vs,*] addr_by ($addr))
      tryCatchRuntimeEx (evalTactic tac)
        fun e => throwError "site_shape: at {site}: {e.toMessageData}"
      out := out ++ (← getUnsolvedGoals)
    unless unused.isEmpty do throwError "site_shape: overrides of no site: {unused}"
    setGoals (out ++ famOut)

/-- `shape_destruct h`: split a shape hypothesis `h` into its cases: alternatives become goals,
existential witnesses and conjuncts are named, and an equation with a variable side is
substituted (the event's kind, once the event is destructed). -/
meta partial def shapeDestruct (g : MVarId) (h : FVarId) : MetaM (List MVarId) := g.withContext do
  let ty ← whnfR (← instantiateMVars (← h.getType))
  if ty.isAppOfArity ``Or 2 then
    let gs ← g.cases h
    return (← gs.toList.mapM fun sg => do
      let some f := sg.fields[0]? | return [sg.mvarId]
      shapeDestruct sg.mvarId f.fvarId!).flatten
  if ty.isAppOfArity ``Exists 2 || ty.isAppOfArity ``And 2 then
    let gs ← g.cases h
    let some sg := gs[0]? | return []
    let some f := sg.fields[1]? | return [sg.mvarId]
    return ← shapeDestruct sg.mvarId f.fvarId!
  if let some (_, a, b) := ty.eq? then
    if a.isFVar || b.isFVar then
      try return [← subst g h] catch _ => return [g]
  return [g]

elab "shape_destruct " h:ident : tactic => withMainContext do
  let fv := (← getLocalDeclFromUserName h.getId).fvarId
  replaceMainGoal (← shapeDestruct (← getMainGoal) fv)

/-- `splitSites` that keeps the fields of the constructors whose last names are in `keep` whole:
one goal per such constructor, with its fields as variables (a family of sites that the script
proves at once, when the transition does not depend on the fields' values). -/
meta partial def splitSitesKeep (keep : Array Name) (g : MVarId) (xs : List FVarId) :
    MetaM (List MVarId) := do
  match xs with
  | [] => return [g]
  | x :: rest =>
    g.withContext do
    let ty ← whnfR (← instantiateMVars (← x.getType))
    if ty.isAppOfArity ``Fin 1 || ty.isConstOf ``Bool then
      let gs ← Lean.Elab.Tactic.finCasesAt g x
      return (← gs.mapM fun g => splitSitesKeep keep g rest).flatten
    if ← isSiteType ty then
      let subs ← g.cases x
      let mut out := []
      for sg in subs do
        let fs := sg.fields.toList.filterMap fun e => if e.isFVar then some e.fvarId! else none
        if keep.any (fun c => c.isSuffixOf (sg.ctorName.getD .anonymous)) then
          out := out ++ (← splitSitesKeep keep sg.mvarId rest)
        else
          out := out ++ (← splitSitesKeep keep sg.mvarId (fs ++ rest))
      return out
    throwError "site_cases: {Expr.fvar x} is neither a site, a Fin nor a Bool"

/-- `stop_cases x … unsplit [c, …] skip_by (tac) unfolding [Ev, …] trans [lemmas]`: the stop
condition `∀ {e}, C.inv d → Ev d e → (C.next d e = some none ↔ ¬ (ret d).accepts e)` of every
site of `x …` (the `stop_iff` field of `Fragment.OkAt`). At each site the shape hypothesis is
unfolded with `unfolding` and destructed, the event's kind substituted, the transition evaluated
with the role's transition lemmas `trans` and the returned value's kind read by `recv`; the cases
on the returned value are closed by `simp_all`. -/
syntax "stop_cases " (ppSpace colGt ident)+ (" unsplit " "[" ident,* "]")?
  (" skip_by " "(" tacticSeq ")")?
  " unfolding " "[" Lean.Parser.Tactic.simpLemma,* "]"
  " trans " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

set_option hygiene false in
elab_rules : tactic
  | `(tactic| stop_cases $xs* $[unsplit [$ks,*]]? $[skip_by ($skip:tacticSeq)]? unfolding [$us,*]
      trans [$ls,*]) =>
    withMainContext do
    let fvs ← xs.toList.mapM fun x => do return (← getLocalDeclFromUserName x.getId).fvarId
    let kept : Array Name := match ks with
      | some ks => ks.getElems.map (·.getId)
      | none => #[]
    let gs ← splitSitesKeep kept (← getMainGoal) fvs
    let mut out := []
    for g in gs do
      setGoals [g]
      evalTactic (← `(tactic| try dsimp only [Fin.reduceFinMk, Fin.isValue]))
      if let some skip := skip then
        evalTactic (← `(tactic| try (($skip); done)))
        if (← getUnsolvedGoals).isEmpty then continue
      let site ← (← getMainGoal).withContext do goalSite (← (← getMainGoal).getType)
      try
        evalTactic (← `(tactic| (
          intro ⟨pc, k⟩ _ hev
          simp only [$us,*] at hev
          shape_destruct hev
          all_goals
            simp only [PTX.Flow.RetKind.accepts, PTX.Flow.RetKind.acceptsVal,
              PTX.Flow.recvAll, PTX.Flow.recv, Option.toList_some, Option.toList_none,
              List.mem_singleton, List.not_mem_nil, false_imp_iff, implies_true, forall_eq,
              List.forall_mem_cons, ↓reduceIte, Option.some.injEq, reduceCtorEq, not_forall,
              exists_prop, forall_eq', Option.map_some, Option.map_none, $ls,*]
            try (repeat' split) <;> simp_all)))
      catch e =>
        logError m!"stop_cases: at {site}"
        throw e
      out := out ++ (← getUnsolvedGoals)
    setGoals out

/-- A successor that is not a stop or a death and satisfies `R`: what a role's helper lemma proves
of the result of a helper function of its transition (`ref_cases … helpers [..]`). -/
def NextOk {D : Type} (R : D → Prop) (o : Option (Option D)) : Prop :=
  o ≠ none ∧ o ≠ some none ∧ ∀ d', o = some (some d') → R d'

theorem NextOk.mono {D : Type} {R R' : D → Prop} {o : Option (Option D)} (h : NextOk R' o)
    (hw : ∀ d, R' d → R d) : NextOk R o :=
  ⟨h.1, h.2.1, fun d' hd => hw d' (h.2.2 d' hd)⟩

/-- The three conclusions of `ref_next` from a successor that is `NextOk`. -/
theorem NextOk.ref_next {D : Type} {R : D → Prop} {o : Option (Option D)} {e : Event}
    (h : NextOk R o) : o ≠ some none ∧ (o = none → Ends e) ∧ ∀ d', o = some (some d') → R d' :=
  ⟨h.2.1, fun hn => absurd hn h.1, h.2.2⟩

/-- `ref_cases x … unsplit [c, …] skip_by (tac) unfolding [Ev, …] trans [lemmas] using (tac)`: the
`ref_next` obligation of `Fragment.OkAt` at every site of `x …`: under `Ref` and `Expect`, an event
of the site's shape does not stop the machine, kills the thread only at an exit, and leads to a
state satisfying `Ref`. At each site the shape hypothesis `hev` is unfolded and destructed, the
event's kind substituted, and each of the three conclusions is reduced by evaluating the
transition `hn` with `trans` and splitting on its conditions; the cases that remain are closed by
the role's tactic, with `hJ : Ref d` and `hE : Expect d e` in context.

With `helpers [h, …]` (FlashMLA request G22), a site whose transition evaluates (by `trans`) to the
result of a helper function is first tried as one goal: the successor is `NextOk` by the first
helper lemma `h : … → NextOk R' (helper …)` that applies (its premises closed by the role's tactic),
and `R'` gives `Ref` (by `exact`, `.1`, or the role's tactic). Only when no helper applies are the
three conclusions split as above. -/
syntax "ref_cases " (ppSpace colGt ident)+ (" unsplit " "[" ident,* "]")?
  (" skip_by " "(" tacticSeq ")")?
  " unfolding " "[" Lean.Parser.Tactic.simpLemma,* "]"
  " trans " "[" Lean.Parser.Tactic.simpLemma,* "]" (" helpers " "[" term,* "]")?
  " using " "(" tacticSeq ")" : tactic

set_option hygiene false in
elab_rules : tactic
  | `(tactic| ref_cases $xs* $[unsplit [$ks,*]]? $[skip_by ($skip:tacticSeq)]? unfolding [$us,*]
      trans [$ls,*] $[helpers [$hs,*]]? using ($tac:tacticSeq)) => withMainContext do
    let hs : Array Term := match hs with
      | some hs => hs.getElems
      | none => #[]
    -- the helper path: one goal per site, closed by a helper lemma, or fails
    let helperTac : TSyntax ``Lean.Parser.Tactic.tacticSeq ← if hs.isEmpty then `(tacticSeq| fail)
      else do
      let alts ← hs.mapM fun h => `(tacticSeq| (apply $h <;> ($tac)))
      `(tacticSeq| (
        apply PTX.Flow.NextOk.ref_next
        apply PTX.Flow.NextOk.mono
        · try simp only [$ls,*]
          first $[| $alts]*
        · intro _ h
          first | exact h | exact h.1 | ($tac)))
    let fvs ← xs.toList.mapM fun x => do return (← getLocalDeclFromUserName x.getId).fvarId
    let kept : Array Name := match ks with
      | some ks => ks.getElems.map (·.getId)
      | none => #[]
    let gs ← splitSitesKeep kept (← getMainGoal) fvs
    let mut out := []
    for g in gs do
      setGoals [g]
      evalTactic (← `(tactic| try dsimp only [Fin.reduceFinMk, Fin.isValue]))
      if let some skip := skip then
        evalTactic (← `(tactic| try (($skip); done)))
        if (← getUnsolvedGoals).isEmpty then continue
      let site ← (← getMainGoal).withContext do goalSite (← (← getMainGoal).getType)
      try
        evalTactic (← `(tactic| (
          intro ⟨pc, k⟩ hi hJ hE hev
          simp only [$us,*] at hev
          shape_destruct hev
          all_goals first
            | (($helperTac); done)
            | (
            refine ⟨fun hn => ?_, fun hn => ?_, fun d' hn => ?_⟩
            all_goals
              simp only [↓reduceIte, Option.some.injEq, reduceCtorEq, $ls,*] at hn
              try (repeat' split at hn)
              all_goals first
                | (cases hn; done)
                | (simp at hn; done)
                | rfl
                | exact Or.inl ⟨_, rfl⟩
                | exact Or.inr rfl
                | (subst hn; ($tac))
                | ($tac)))))
      catch e =>
        logError m!"ref_cases: at {site}"
        throw e
      out := out ++ (← getUnsolvedGoals)
    setGoals out

end PTX.Flow
