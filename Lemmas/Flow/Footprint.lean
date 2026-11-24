-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Register.RegisterFrame
public import Lemmas.Flow.Facts
public import Lemmas.Flow.Bits
public import Lemmas.Flow.TryRt
public import Lemmas.Flow.PcStep
public meta import Lean

@[expose] public section

/-! # Register facts on a footprint

Proof tools for site machines, whose states give every live register a value from a table.
They keep the cost of a step proportional to what the step touches, not to the table.

* `seg_fp h using tac` proves a local segment: it reads the segment's instructions from the
  generated lookups, evaluates the code with only the facts of the registers the segment
  reads (`run_footprint`), checks only the registers it writes, and carries every other fact
  over (`holds_transfer`). `tac` closes each equation of a written register's value, after
  `ty_eval` has evaluated the instruction types in it.
* `frame_fp hS, hframe` does the same for an event that writes registers.
* Two value tables are compared entry by entry, once, for a symbolic register (`OffEq`,
  `lookup_offEq`): a changed entry must be written or dead.
* `lit_mem` proves membership facts of literal register lists by position, and
  `table_decide` closes other closed facts of the generated tables.

Registers are numeric ids; the kernel compares two only where a proof needs them to differ. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- Register facts at an explicit vector cursor, including an empty accumulator at a scalar
boundary. Local control proofs may carry the cursor unchanged without assuming a scalar boundary. -/
abbrev AtVector (t : TState) (pc : Nat) (F : List (Nat × Value)) (sub : Nat)
    (acc : List Value) : Prop :=
  t.pc = pc ∧ t.sub = sub ∧ t.acc = acc ∧ t.fault = none ∧ Holds t.regs F

/-- Evaluate a segment with the read facts and explicit input and output vector cursors. -/
theorem run_footprint_vector {K : Kernel} {A : List Assumption} {L : Launch} {g n s b : Nat}
    {t0 : TState} {F0 F G : List (Nat × Value)} {W : List Nat}
    {sub0 sub1 : Nat} {acc0 acc1 : List Value}
    (h0 : AtVector t0 s F0 sub0 acc0) (hF : Holds t0.regs F)
    (h : ∀ R, ∃ t, run K A L g n ⟨s, override F R, t0.cf, sub0, acc0, none⟩ = some t ∧ t.pc = b ∧
      t.sub = sub1 ∧ t.acc = acc1 ∧ t.fault = none ∧ Holds t.regs G ∧
      ∀ r, r ∉ W → t.regs r = override F R r) :
    ∃ t, run K A L g n t0 = some t ∧ AtVector t b G sub1 acc1 ∧
      ∀ r, r ∉ W → t.regs r = t0.regs r := by
  obtain ⟨pc, R, cf, sub, acc, fault⟩ := t0
  obtain ⟨hpc, hsub, hacc, hf, -⟩ := h0
  simp only at hpc hsub hacc hf hF
  subst hpc hsub hacc hf
  obtain ⟨t, hr, h1, h2, h3, h4, h5, h6⟩ := h R
  rw [override_eq hF] at hr h6
  exact ⟨t, hr, ⟨h1, h2, h3, h4, h5⟩, h6⟩

/-- Evaluate a segment with the read facts `F` only: the end state is a state of `G`, and
registers outside `W` keep their values. -/
theorem run_footprint {K : Kernel} {A : List Assumption} {L : Launch} {g n s b : Nat}
    {t0 : TState} {F0 F G : List (Nat × Value)} {W : List Nat}
    (h0 : At t0 s F0) (hF : Holds t0.regs F)
    (h : ∀ R, ∃ t, run K A L g n ⟨s, override F R, t0.cf, 0, [], none⟩ = some t ∧ t.pc = b ∧
      t.sub = 0 ∧ t.acc = [] ∧ t.fault = none ∧ Holds t.regs G ∧
      ∀ r, r ∉ W → t.regs r = override F R r) :
    ∃ t, run K A L g n t0 = some t ∧ At t b G ∧ ∀ r, r ∉ W → t.regs r = t0.regs r :=
  run_footprint_vector (sub0 := 0) (sub1 := 0) (acc0 := []) (acc1 := []) h0 hF h

/-- The facts of the registers a segment reads, from the facts of its start state. -/
theorem holds_select {R : Nat → Option Value} {ex : List (Nat × Value)}
    {liveS rs : List Nat} {v : Nat → Value} (h : Holds R (ex ++ factsFrom liveS v))
    (hs : ∀ r ∈ rs, r ∈ liveS) : Holds R (ex ++ factsFrom rs v) := by
  rw [holds_append] at h ⊢
  exact ⟨h.1, holds_factsFrom_mono h.2 hs⟩

/-- The facts of a segment's end state. A written register that is live at the end is among
the checked ones (`Wc`); another live register keeps its value, which is a fact of the start
state: an explicit one (`E`) or the table's. -/
theorem holds_transfer {R R' : Nat → Option Value} {ex exT : List (Nat × Value)}
    {liveS liveT W Wc E : List Nat} {v v' : Nat → Value}
    (hS : Holds R (ex ++ factsFrom liveS v)) (hW : Holds R' (exT ++ factsFrom Wc v'))
    (hframe : ∀ r, r ∉ W → R' r = R r) (hWc : ∀ r ∈ W, r ∈ Wc ∨ r ∉ liveT)
    (hcov : ∀ r ∈ liveT, r ∈ W ∨ r ∈ liveS ∨ r ∈ E) (hE : ∀ r ∈ E, (r, v' r) ∈ ex)
    (hval : ∀ r ∈ liveT, r ∉ W → r ∉ E → v' r = v r) :
    Holds R' (exT ++ factsFrom liveT v') := by
  rw [holds_append] at hS hW ⊢
  refine ⟨hW.1, holds_of_pointwise fun r hr => ?_⟩
  by_cases hw : r ∈ W
  · rcases hWc r hw with h | h
    · exact holds_mem hW.2 (mem_factsFrom h)
    · exact absurd hr h
  · rw [hframe r hw]
    by_cases he : r ∈ E
    · exact holds_mem hS.1 (hE r he)
    · rcases hcov r hr with h | h | h
      · exact absurd h hw
      · rw [hval r hr hw he]
        exact holds_mem hS.2 (mem_factsFrom h)
      · exact absurd h he

/-- The end state's register facts, with the vector cursors given by the actual local steps. -/
theorem seg_footprint_vector {K : Kernel} {A : List Assumption} {L : Launch} {g n s b : Nat}
    {t0 : TState} {ex exT Fexp : List (Nat × Value)} {liveS liveT rs W Wc E : List Nat}
    {v v' : Nat → Value} {sub0 sub1 : Nat} {acc0 acc1 : List Value}
    (h0 : AtVector t0 s (ex ++ factsFrom liveS v) sub0 acc0) (hsub : ∀ r ∈ rs, r ∈ liveS)
    (hexp : Holds t0.regs (ex ++ factsFrom rs v) → Holds t0.regs Fexp)
    (hrun : ∀ R, ∃ t, run K A L g n ⟨s, override Fexp R, t0.cf, sub0, acc0, none⟩ = some t ∧
      t.pc = b ∧
      t.sub = sub1 ∧ t.acc = acc1 ∧ t.fault = none ∧ Holds t.regs (exT ++ factsFrom Wc v') ∧
      ∀ r, r ∉ W → t.regs r = override Fexp R r)
    (hWc : ∀ r ∈ W, r ∈ Wc ∨ r ∉ liveT)
    (hcov : ∀ r ∈ liveT, r ∈ W ∨ r ∈ liveS ∨ r ∈ E) (hE : ∀ r ∈ E, (r, v' r) ∈ ex)
    (hval : ∀ r ∈ liveT, r ∉ W → r ∉ E → v' r = v r) :
    ∃ t, run K A L g n t0 = some t ∧ AtVector t b (exT ++ factsFrom liveT v') sub1 acc1 := by
  obtain ⟨t, hr, hat, hfr⟩ := run_footprint_vector h0 (hexp (holds_select h0.2.2.2.2 hsub)) hrun
  exact ⟨t, hr, hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1,
    holds_transfer h0.2.2.2.2 hat.2.2.2.2 hfr hWc hcov hE hval⟩

/-- A segment evaluated on its footprint, with the end state's facts. -/
theorem seg_footprint {K : Kernel} {A : List Assumption} {L : Launch} {g n s b : Nat}
    {t0 : TState} {ex exT Fexp : List (Nat × Value)} {liveS liveT rs W Wc E : List Nat}
    {v v' : Nat → Value}
    (h0 : At t0 s (ex ++ factsFrom liveS v)) (hsub : ∀ r ∈ rs, r ∈ liveS)
    (hexp : Holds t0.regs (ex ++ factsFrom rs v) → Holds t0.regs Fexp)
    (hrun : ∀ R, ∃ t, run K A L g n ⟨s, override Fexp R, t0.cf, 0, [], none⟩ = some t ∧
      t.pc = b ∧
      t.sub = 0 ∧ t.acc = [] ∧ t.fault = none ∧ Holds t.regs (exT ++ factsFrom Wc v') ∧
      ∀ r, r ∉ W → t.regs r = override Fexp R r)
    (hWc : ∀ r ∈ W, r ∈ Wc ∨ r ∉ liveT)
    (hcov : ∀ r ∈ liveT, r ∈ W ∨ r ∈ liveS ∨ r ∈ E) (hE : ∀ r ∈ E, (r, v' r) ∈ ex)
    (hval : ∀ r ∈ liveT, r ∉ W → r ∉ E → v' r = v r) :
    ∃ t, run K A L g n t0 = some t ∧ At t b (exT ++ factsFrom liveT v') :=
  seg_footprint_vector (sub0 := 0) (sub1 := 0) (acc0 := []) (acc1 := [])
    h0 hsub hexp hrun hWc hcov hE hval

/-- Two value tables with the same keys whose values agree except at keys satisfying `P`. -/
def OffEq (P : Nat → Prop) : List (Nat × Value) → List (Nat × Value) → Prop
  | [], [] => True
  | p :: l, q :: l' => p.1 = q.1 ∧ (P p.1 ∨ p.2 = q.2) ∧ OffEq P l l'
  | _, _ => False

theorem OffEq.refl {P : Nat → Prop} : ∀ l : List (Nat × Value), OffEq P l l
  | [] => trivial
  | _ :: l => ⟨rfl, Or.inr rfl, OffEq.refl l⟩

/-- A common front part of two tables needs no comparison. -/
theorem offEq_append_left {P : Nat → Prop} (A : List (Nat × Value))
    {B' B : List (Nat × Value)} (h : OffEq P B' B) : OffEq P (A ++ B') (A ++ B) := by
  induction A with
  | nil => exact h
  | cons a A ih => exact ⟨rfl, Or.inr rfl, ih⟩

/-- Such tables give a key that does not satisfy `P` the same value. -/
theorem lookup_offEq {P : Nat → Prop} : ∀ {l l' : List (Nat × Value)}, OffEq P l l' →
    ∀ r, ¬ P r → l.lookup r = l'.lookup r
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim
  | (k, a) :: l, (k', b) :: l', ⟨hk, hv, hl⟩, r, hr => by
    simp only at hk hv
    subst hk
    simp only [List.lookup]
    cases hrk : r == k with
    | false => exact lookup_offEq hl r hr
    | true =>
      have : r = k := eq_of_beq hrk
      subst this
      rcases hv with h | h
      · exact absurd h hr
      · rw [h]

/-- Every element of a list satisfies `P`, as a conjunction (proved element by element). -/
def AllP (P : Nat → Prop) : List Nat → Prop
  | [] => True
  | x :: xs => P x ∧ AllP P xs

theorem forall_mem_of_allP {P : Nat → Prop} : ∀ {l : List Nat}, AllP P l → ∀ r ∈ l, P r
  | [], _, _, h => absurd h List.not_mem_nil
  | _ :: _, ⟨hx, hxs⟩, _, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact hx
    · exact forall_mem_of_allP hxs _ h

end

open Lean Meta Elab Tactic

/-- The value of a register id literal (a numeral). -/
meta def regLit? (e : Expr) : Option Nat := e.nat? <|> e.rawNatLit?

/-- A fact list as `extras ++ factsFrom live val`: the explicit facts in front, then the
table part (found by unfolding). -/
meta partial def splitFacts (e : Expr) : MetaM (Array Expr × Option (Expr × Expr)) := do
  let e ← instantiateMVars e
  if e.isAppOfArity ``List.cons 3 then
    let (ex, tbl) ← splitFacts (e.getArg! 2)
    return (#[e.getArg! 1] ++ ex, tbl)
  if e.isAppOfArity ``PTX.Flow.factsFrom 2 then
    return (#[], some (e.getArg! 0, e.getArg! 1))
  if e.isAppOfArity ``List.nil 1 then return (#[], none)
  match ← unfoldDefinition? e with
  | some e' => splitFacts e'.headBeta
  | none => throwError "seg_fp: cannot read the facts {e}"

/-- The register ids of a closed list of registers. -/
meta partial def regList (e : Expr) : MetaM (Array Nat) := do
  let e ← whnfD e
  if e.isAppOfArity ``List.cons 3 then
    let h ← whnfD (e.getArg! 1)
    let some s := regLit? h | throwError "seg_fp: not a register id {h}"
    return #[s] ++ (← regList (e.getArg! 2))
  if e.isAppOfArity ``List.nil 1 then return #[]
  throwError "seg_fp: not a list literal {e}"

/-- A natural number literal, by evaluation. -/
meta def natValue (e : Expr) : MetaM Nat := do
  let e' ← whnfD (← instantiateMVars e)
  if let some n := e'.nat? <|> e'.rawNatLit? then return n
  let e'' ← reduce e' (explicitOnly := false) (skipTypes := true) (skipProofs := true)
  if let some n := e''.nat? <|> e''.rawNatLit? then return n
  throwError "seg_fp: not a number {e}"

meta structure SegInstr where
  succ : List Nat
  reads : Array Nat
  writes : Array Nat
  /-- A guarded instruction may leave its destinations unwritten. -/
  guarded : Bool

/-- The instruction at `pc`: from the kernel's generated lookup lemma `Flow.code_<pc>` when
there is one, else by evaluating the code. -/
meta def instrAt (K code : Expr) (pc : Nat) : MetaM (Option Expr) := do
  if let some k := K.getAppFn.constName? then
    let lemmaName := k.getPrefix ++ `Flow ++ Name.mkSimple s!"code_{pc}"
    if let some info := (← getEnv).find? lemmaName then
      if let some (_, _, rhs) := info.type.eq? then
        if rhs.isAppOfArity ``Option.some 2 then return some (rhs.getArg! 1)
  let o ← whnfD (← mkAppM ``GetElem?.getElem? #[code, mkNatLit pc])
  if o.isAppOfArity ``Option.some 2 then return some (o.getArg! 1)
  return none

/-- The successors, reads and writes of the instruction at `pc` (none past the code). -/
meta def segInstr (K code : Expr) (pc : Nat) : MetaM (Option SegInstr) := do
  let some ins ← instrAt K code pc | return none
  let ins ← whnfD ins
  unless ins.isAppOfArity ``PTX.Instr.mk 2 do throwError "seg_fp: instruction {pc} is {ins}"
  let guard ← whnfD (ins.getArg! 0)
  let op ← instantiateMVars (ins.getArg! 1)
  let opW ← whnfD op
  let writes ← regList (← mkAppM ``PTX.Proof.writesRegs #[op])
  let guardRegs : Array Nat ←
    if guard.isAppOfArity ``Option.some 2 then
      let p ← whnfD (← mkAppM ``Prod.fst #[guard.getArg! 1])
      pure (match regLit? p with | some s => #[s] | none => #[])
    else pure #[]
  -- a register named once, as a destination, is only written; any other mention is a read
  let mut reads := #[]
  let occs ← regList (← mkAppM ``PTX.Proof.opRegs #[op])
  for r in occs do
    if reads.contains r then continue
    if occs.count r > writes.count r then reads := reads.push r
  for r in guardRegs do
    unless reads.contains r do reads := reads.push r
  let succ ←
    if opW.isAppOfArity ``PTX.Op.bra 2 then
      let t ← natValue (opW.getArg! 0)
      pure (if guardRegs.isEmpty then [t] else [pc + 1, t])
    else pure [pc + 1]
  return some { succ, reads, writes, guarded := !guardRegs.isEmpty }

/-- The instructions of a segment, read once. -/
meta abbrev SegM := StateRefT (Std.HashMap Nat (Option SegInstr)) MetaM

meta def segInstrM (K code : Expr) (pc : Nat) : SegM (Option SegInstr) := do
  if let some i := (← get)[pc]? then return i
  let i ← segInstr K code pc
  modify (·.insert pc i)
  return i

/-- The paths of `n` instructions from `s` that end at `b`. -/
meta partial def segPaths (K code : Expr) (s n b : Nat) : SegM (List (List Nat)) := do
  if n = 0 then return if s = b then [[]] else []
  let some i ← segInstrM K code s | return []
  let mut out := []
  for t in i.succ do
    for p in ← segPaths K code t (n - 1) b do
      out := (s :: p) :: out
  return out

/-- The registers a path reads before surely writing them, and those it may write. A guarded
instruction may skip its write, so its destinations are also read. -/
meta def footprint (K code : Expr) (path : List Nat) : SegM (Array Nat × Array Nat) := do
  let mut reads := #[]
  let mut sure := #[]
  let mut writes := #[]
  for pc in path do
    let some i ← segInstrM K code pc | throwError "seg_fp: no instruction at {pc}"
    for r in i.reads ++ (if i.guarded then i.writes else #[]) do
      unless sure.contains r || reads.contains r do reads := reads.push r
    for w in i.writes do
      unless writes.contains w do writes := writes.push w
      unless i.guarded || sure.contains w do sure := sure.push w
  return (reads, writes)

meta def mkRegList (xs : Array Nat) : MetaM Expr :=
  mkListLit (mkConst ``Nat) (xs.toList.map mkNatLit)

/-- A proof of `r ∈ l` for a list literal `l`, by its position: the kernel walks to the
position and compares no register ids. -/
meta def memProof (r : Nat) (l : List Nat) : MetaM Expr := do
  let some i := l.idxOf? r | throwError "seg_fp: {r} is not in the list"
  let lE ← mkListLit (mkConst ``Nat) (l.map mkNatLit)
  -- built directly: unifying the statement would walk the list in the elaborator as well
  let str := mkConst ``Nat
  let some' := mkApp2 (mkConst ``Option.some [.zero]) str (mkNatLit r)
  return mkApp5 (mkConst ``List.mem_of_getElem? [.zero]) str lE (mkNatLit i) (mkNatLit r)
    (mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkApp (mkConst ``Option [.zero]) str) some')

/-- A proof of `AllP P l` from a proof of `P x` for each element. -/
meta def allPProof (xs : List Nat) (each : Nat → MetaM Expr) : MetaM Expr := do
  let mut acc := mkConst ``True.intro
  for x in xs.reverse do
    let px ← each x
    acc ← mkAppM ``And.intro #[px, acc]
  return acc

/-- A proof of `∀ r ∈ l, r ∈ m`. -/
meta def subsetProof (l m : List Nat) : MetaM Expr := do
  let mE ← mkListLit (mkConst ``Nat) (m.map mkNatLit)
  let lE ← mkListLit (mkConst ``Nat) (l.map mkNatLit)
  let P ← withLocalDeclD `r (mkConst ``Nat) fun r => do
    mkLambdaFVars #[r] (← mkAppM ``Membership.mem #[mE, r])
  let all ← allPProof l (fun x => memProof x m)
  mkAppOptM ``PTX.Flow.forall_mem_of_allP #[some P, some lE, some all]

/-- Whether two values are the same: syntactically up to projections, or by an evaluation
that stays small (a comparison that runs away counts as different). -/
meta def sameValue (a b : Expr) : MetaM Bool := withNewMCtxDepth do
  if ← withReducible (isDefEq a b) then return true
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxRecDepth := 512, maxHeartbeats := 2000000 })
      (withCurrHeartbeats (isDefEq a b)))
    (fun _ => pure false)

meta def regListE (xs : List Nat) : MetaM Expr :=
  mkListLit (mkConst ``Nat) (xs.map mkNatLit)

meta def memE (l r : Expr) : MetaM Expr := mkAppM ``Membership.mem #[l, r]

/-- `∀ r ∈ l, P r` from a proof of `P x` (of exactly that type, after beta) for each element. -/
meta def forallMem (l : List Nat) (P : Expr) (each : Nat → MetaM Expr) : MetaM Expr := do
  let all ← allPProof l fun x => do
    mkExpectedTypeHint (← each x) (P.beta #[mkNatLit x])
  mkAppOptM ``PTX.Flow.forall_mem_of_allP #[some P, some (← regListE l), some all]

/-- A proof of `∀ r ∈ l, r ∈ w ∨ r ∈ m ∨ r ∈ e`. -/
meta def coverProof (l w m e : List Nat) : MetaM Expr := do
  let (wE, mE, eE) := (← regListE w, ← regListE m, ← regListE e)
  let P ← withLocalDeclD `r (mkConst ``Nat) fun r => do
    mkLambdaFVars #[r] (mkOr (← memE wE r) (mkOr (← memE mE r) (← memE eE r)))
  forallMem l P fun x => do
    let (pw, pm, pe) := (← memE wE (mkNatLit x), ← memE mE (mkNatLit x), ← memE eE (mkNatLit x))
    if w.contains x then
      return mkApp3 (mkConst ``Or.inl) pw (mkOr pm pe) (← memProof x w)
    if m.contains x then
      return mkApp3 (mkConst ``Or.inr) pw (mkOr pm pe)
        (mkApp3 (mkConst ``Or.inl) pm pe (← memProof x m))
    if e.contains x then
      return mkApp3 (mkConst ``Or.inr) pw (mkOr pm pe)
        (mkApp3 (mkConst ``Or.inr) pm pe (← memProof x e))
    throwError "seg_fp: {x} is live at the end, but the segment does not write it and the \
      start state has no fact of it"

/-- A proof of `∀ r ∈ w, r ∈ wc ∨ r ∉ liveT`: a written register is checked or dead. -/
meta def checkedProof (w wc liveT : List Nat) : MetaM Expr := do
  let (wcE, tE) := (← regListE wc, ← regListE liveT)
  let P ← withLocalDeclD `r (mkConst ``Nat) fun r => do
    mkLambdaFVars #[r] (mkOr (← memE wcE r) (mkNot (← memE tE r)))
  forallMem w P fun x => do
    let (pc, pt) := (← memE wcE (mkNatLit x), mkNot (← memE tE (mkNatLit x)))
    if wc.contains x then return mkApp3 (mkConst ``Or.inl) pc pt (← memProof x wc)
    return mkApp3 (mkConst ``Or.inr) pc pt (← mkDecideProof pt)

/-- A proof of `a ∈ [a₀, …]` for the element at position `i`. -/
meta def memAt (α : Expr) (xs : List Expr) (i : Nat) : MetaM Expr := do
  let u ← getDecLevel α
  match xs, i with
  | x :: rest, 0 => return mkApp3 (mkConst ``List.Mem.head [u]) α x (← mkListLit α rest)
  | x :: rest, i + 1 =>
    let some a := xs[i + 1]? | throwError "seg_fp: position out of range"
    return mkApp5 (mkConst ``List.Mem.tail [u]) α a x (← mkListLit α rest) (← memAt α rest i)
  | [], _ => throwError "seg_fp: position out of range"

/-- A proof of `∀ r ∈ e, (r, v' r) ∈ ex`: the explicit start facts of the registers `e`. -/
meta def extraProof (e : List Nat) (exKeys : List Nat) (ex : List Expr) (v' : Expr) :
    MetaM Expr := do
  let pairTy ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``PTX.Value]
  let exE ← mkListLit pairTy ex
  let P ← withLocalDeclD `r (mkConst ``Nat) fun r => do
    mkLambdaFVars #[r] (← memE exE (← mkAppM ``Prod.mk #[r, mkApp v' r]))
  forallMem e P fun x => do
    let some i := exKeys.idxOf? x | throwError "seg_fp: no explicit fact of {x}"
    memAt pairTy ex i

/-- The cells of a table, as written. -/
meta partial def tableCells (l : Expr) : MetaM (Array (Expr × Expr × Expr)) := do
  let l ← whnfD l
  if l.isAppOfArity ``List.nil 1 then return #[]
  unless l.isAppOfArity ``List.cons 3 do throwError "seg_fp: not a table {l}"
  let p ← whnfD (l.getArg! 1)
  unless p.isAppOfArity ``Prod.mk 4 do throwError "seg_fp: not a table entry {p}"
  return #[(l.getArg! 1, p.getArg! 2, p.getArg! 3)] ++ (← tableCells (l.getArg! 2))

/-- A proof of `OffEq P T' T`, where `P k` is `k ∈ W ∨ k ∈ E ∨ k ∉ liveT`: every entry whose
value changed is written, explicit, or dead. -/
meta partial def offEqProof (P : Expr) (T' T : Expr) (w e liveT : List Nat) : MetaM Expr := do
  -- a common front part is skipped
  if T'.isAppOfArity ``HAppend.hAppend 6 && T.isAppOfArity ``HAppend.hAppend 6 then
    if ← withNewMCtxDepth (withReducible (isDefEq (T'.getArg! 4) (T.getArg! 4))) then
      let rest ← offEqProof P (T'.getArg! 5) (T.getArg! 5) w e liveT
      return ← mkExpectedTypeHint
        (← mkAppOptM ``PTX.Flow.offEq_append_left #[some P, some (T.getArg! 4), none, none,
          some rest])
        (← mkAppM ``PTX.Flow.OffEq #[P, T', T])
  let (wE, eE, tE) := (← regListE w, ← regListE e, ← regListE liveT)
  let cs' ← tableCells T'
  let cs ← tableCells T
  unless cs'.size == cs.size do throwError "seg_fp: value tables of different lengths"
  let mut acc := mkConst ``True.intro
  let mut accTy := mkConst ``True
  for i in (List.range cs.size).reverse do
    let (_, k', a') := cs'[i]!
    let (_, k, a) := cs[i]!
    let some ks := regLit? (← whnfD k') | throwError "seg_fp: table key {k'}"
    unless regLit? (← whnfD k) == some ks do throwError "seg_fp: tables differ at key {ks}"
    let key := mkNatLit ks
    let pk := P.beta #[key]
    let eqv ← mkEq a' a
    -- a written, explicit or dead register needs no comparison: the values usually differ there,
    -- and a failing comparison unfolds both (seconds per site)
    let free := w.contains ks || e.contains ks || !liveT.contains ks
    let same ← if free then withNewMCtxDepth (withReducible (isDefEq a' a)) else sameValue a' a
    let pv ←
      if same then
        pure (mkApp3 (mkConst ``Or.inr) pk eqv (← mkEqRefl a'))
      else
        let (pw, pe, pt) := (← memE wE key, ← memE eE key, mkNot (← memE tE key))
        let h ←
          if w.contains ks then pure (mkApp3 (mkConst ``Or.inl) pw (mkOr pe pt) (← memProof ks w))
          else if e.contains ks then
            pure (mkApp3 (mkConst ``Or.inr) pw (mkOr pe pt)
              (mkApp3 (mkConst ``Or.inl) pe pt (← memProof ks e)))
          else if !liveT.contains ks then
            pure (mkApp3 (mkConst ``Or.inr) pw (mkOr pe pt)
              (mkApp3 (mkConst ``Or.inr) pe pt (← mkDecideProof pt)))
          else throwError "seg_fp: the value of {ks} changes ({a} to {a'}), but it is live at \
            the end and the segment does not write it"
        pure (mkApp3 (mkConst ``Or.inl) pk eqv h)
    let keq ← mkEqRefl key
    let hereTy := mkOr pk eqv
    let restTy := mkAnd hereTy accTy
    acc := mkApp4 (mkConst ``And.intro) (← mkEq key key) restTy keq
      (mkApp4 (mkConst ``And.intro) hereTy accTy pv acc)
    accTy := mkAnd (← mkEq key key) restTy
  mkExpectedTypeHint acc (← mkAppM ``PTX.Flow.OffEq #[P, T', T])

/-- The tables looked up at `r` in an expression, in order of occurrence. -/
meta def lookupsOf (r e : Expr) : Array Expr := Id.run do
  let rec go (e : Expr) (acc : Array Expr) : Array Expr :=
    if e.isAppOfArity ``List.lookup 5 && e.getArg! 3 == r then acc.push (e.getArg! 4)
    else match e with
      | .app f a => go a (go f acc)
      | .lam _ t b _ => go b (go t acc)
      | .forallE _ t b _ => go b (go t acc)
      | .letE _ t v b _ => go b (go v (go t acc))
      | .mdata _ b => go b acc
      | .proj _ _ b => go b acc
      | _ => acc
  return go e #[]

/-- The value a register key has in an association list, by walking the list's spine and comparing
literal keys; the entry is returned as written. -/
meta partial def lookupWalkRaw (key : Nat) (l : Expr) : MetaM (Option (Option Expr)) := do
  let l ← whnfD l
  if l.isAppOfArity ``List.nil 1 then return some none
  unless l.isAppOfArity ``List.cons 3 do return none
  let p ← whnfD (l.getArg! 1)
  unless p.isAppOfArity ``Prod.mk 4 do return none
  let some k := regLit? (← whnfD (p.getArg! 2)) | return none
  if k == key then return some (some (p.getArg! 3))
  lookupWalkRaw key (l.getArg! 2)

/-- Every entry of an association list with literal keys (the first of a key), by walking its
spine once; `none` when the spine or a key is not literal. -/
meta partial def assocEntries (l : Expr) (acc : Std.HashMap Nat Expr := {}) :
    MetaM (Option (Std.HashMap Nat Expr)) := do
  let l ← whnfD l
  if l.isAppOfArity ``List.nil 1 then return some acc
  unless l.isAppOfArity ``List.cons 3 do return none
  let p ← whnfD (l.getArg! 1)
  unless p.isAppOfArity ``Prod.mk 4 do return none
  let some k := regLit? (← whnfD (p.getArg! 2)) | return none
  assocEntries (l.getArg! 2) (acc.insertIfNew k (p.getArg! 3))

/-- The association lists `lookupWalk` has read in this file, by the list's term, with the
types of its free variables: all entries, read once (a table is looked up for every live register
of every segment). -/
meta initialize assocCache :
    IO.Ref (Std.HashMap Expr (Array (FVarId × Expr) × Option (Std.HashMap Nat Expr))) ←
  IO.mkRef {}

/-- The free variables of `e` with their types, when each is an assumption (not a `let`) of the
local context. Theorems elaborated in parallel may reuse a free variable's id, so a cached term
is reused only where its free variables are the same assumptions of the same types. -/
meta def fvarSig (e : Expr) : MetaM (Option (Array (FVarId × Expr))) := do
  unless e.hasFVar do return some #[]
  let lctx ← getLCtx
  let mut out := #[]
  for f in (Lean.collectFVars {} e).fvarSet.toList do
    let some d := lctx.find? f | return none
    if d.isLet then return none
    out := out.push (f, ← instantiateMVars d.type)
  return some out

/-- `lookupWalkRaw` through `assocCache`: the list's entries are read once per list term. -/
meta def lookupWalk (key : Nat) (l : Expr) : MetaM (Option (Option Expr)) := do
  let l ← instantiateMVars l
  if l.hasMVar || l.hasLooseBVars then return ← lookupWalkRaw key l
  let some sig ← fvarSig l | return ← lookupWalkRaw key l
  if sig.any (·.2.hasMVar) then return ← lookupWalkRaw key l
  let cached := match (← assocCache.get)[l]? with
    | some (sig', m) => if sig' == sig then some m else none
    | none => none
  let m ← match cached with
    | some m => pure m
    | none => do
      let m ← assocEntries l
      assocCache.modify (·.insert l (sig, m))
      pure m
  match m with
  | some m => return some m[key]?
  | none => lookupWalkRaw key l

/-- The value a register has in a value table, as the table writes it: unfold the table's
`valueOf`/`value` and its pattern matches, look keys up by `lookupWalk`, and stop at the
entry. -/
meta partial def evalTable (e : Expr) (fuel : Nat := 64) : MetaM Expr := do
  if fuel = 0 then return e
  let e ← whnfCore e
  let f := e.getAppFn
  let some c := f.constName? | return e
  if c == ``Option.getD && e.getAppNumArgs == 3 then
    let o ← evalTable (e.getArg! 1) (fuel - 1)
    if o.isAppOfArity ``Option.some 2 then return o.getArg! 1
    if o.isAppOfArity ``Option.none 1 then return ← evalTable (e.getArg! 2) (fuel - 1)
    return e
  if c == ``List.lookup && e.getAppNumArgs == 5 then
    let some key := regLit? (← whnfD (e.getArg! 3)) | return e
    let some r ← lookupWalk key (e.getArg! 4) | return e
    return match r with
      | some v => mkApp2 (mkConst ``Option.some (f.constLevels!.drop 1)) (e.getArg! 1) v
      | none => mkApp (mkConst ``Option.none (f.constLevels!.drop 1)) (e.getArg! 1)
  let last := c.components.getLast?.map (·.toString)
  if (last.map (·.startsWith "value")).getD false || (← isMatcher c) then
    match ← unfoldDefinition? e with
    | some e' => return ← evalTable e' (fuel - 1)
    | none => return e
  return e


/-- A term with its projections of constructor applications reduced (`{ site := s, v := v }.v`
is `v`): the form in which a walked term and a table's are compared. -/
meta def projNorm (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    if let .proj _ _ s := x then
      let s' ← whnfR s
      if s'.isApp && s'.getAppFn.isConst then
        let x' ← whnfCore (x.updateProj! s')
        return if x' == x then .continue else .visit x'
      return .continue
    let some n := x.getAppFn.constName? | return .continue
    let some info ← getProjectionFnInfo? n | return .continue
    if info.fromClass || x.getAppNumArgs != info.numParams + 1 then return .continue
    -- a projection function as its primitive projection
    match ← unfoldDefinition? x with
    | some x' => return .visit x'.headBeta
    | none => return .continue)

/-- Unfold the value functions applied to `r` in an expression, down to their tables. -/
meta def unfoldAt (r e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun x => do
    let some c := x.getAppFn.constName? | return .continue
    if c == ``List.lookup || c == ``Option.getD || x.getAppNumArgs == 0 then return .continue
    unless x.appArg! == r do return .continue
    match ← unfoldDefinition? x with
    | some x' => return .visit x'.headBeta
    | none => return .continue)

/-- `∀ r ∈ liveT, r ∉ W → r ∉ E → v' r = v r` from the tables the two value functions look
`r` up in (`offEqProof`). -/
meta def valProofTables (v' v : Expr) (w e liveT : List Nat) : MetaM Expr := do
  let (wE, eE, tE) := (← regListE w, ← regListE e, ← regListE liveT)
  withLocalDeclD `r (mkConst ``Nat) fun r => do
  withLocalDeclD `hl (← memE tE r) fun hl => do
  withLocalDeclD `hw (mkNot (← memE wE r)) fun hw => do
  withLocalDeclD `he (mkNot (← memE eE r)) fun he => do
    let goal ← mkEq (mkApp v' r) (mkApp v r)
    let e' ← unfoldAt r (mkApp v' r).headBeta
    let e0 ← unfoldAt r (mkApp v r).headBeta
    let ts' := lookupsOf r e'
    let ts := lookupsOf r e0
    unless ts'.size == ts.size do throwError "seg_fp: value functions of different shapes"
    let P ← withLocalDeclD `k (mkConst ``Nat) fun k => do
      mkLambdaFVars #[k] (mkOr (← memE wE k) (mkOr (← memE eE k) (mkNot (← memE tE k))))
    let hP ← withLocalDeclD `h (P.beta #[r]) fun h => do
      let pw ← memE wE r
      let pe ← memE eE r
      let pt := mkNot (← memE tE r)
      let inner ← withLocalDeclD `h2 (mkOr pe pt) fun h2 => do
        mkLambdaFVars #[h2] (mkApp6 (mkConst ``Or.elim) pe pt (mkConst ``False) h2 he
          (← withLocalDeclD `h3 pt fun h3 => do mkLambdaFVars #[h3] (mkApp h3 hl)))
      mkLambdaFVars #[h] (mkApp6 (mkConst ``Or.elim) pw (mkOr pe pt) (mkConst ``False) h hw inner)
    let mut cur := e'
    let mut proof ← mkEqRefl e'
    for i in [0:ts.size] do
      if ← withNewMCtxDepth (withReducible (isDefEq ts'[i]! ts[i]!)) then continue
      let H ← offEqProof P ts'[i]! ts[i]! w e liveT
      let step ← mkAppM ``PTX.Flow.lookup_offEq #[H, r, hP]
      let lhs ← mkAppM ``List.lookup #[r, ts'[i]!]
      let rhs ← mkAppM ``List.lookup #[r, ts[i]!]
      let motive ← withLocalDeclD `X (← inferType lhs) fun X => do
        mkLambdaFVars #[X] (cur.replace fun s => if s == lhs then some X else none)
      proof ← mkEqTrans proof (← mkCongrArg motive step)
      cur := motive.beta #[rhs]
    unless ← withNewMCtxDepth (withReducible (isDefEq cur e0)) do
      throwError "seg_fp: the value functions differ outside their tables"
    mkLambdaFVars #[r, hl, hw, he] (← mkExpectedTypeHint proof goal)

/-- The same statement register by register: each live register that is neither written nor
explicit has the same value in both tables, by evaluation. -/
meta def valProofPointwise (v' v : Expr) (w e liveT : List Nat) : MetaM Expr := do
  let (wE, eE) := (← regListE w, ← regListE e)
  let P ← withLocalDeclD `r (mkConst ``Nat) fun r => do
    mkLambdaFVars #[r] (← mkArrow (mkNot (← memE wE r)) (← mkArrow (mkNot (← memE eE r))
      (← mkEq (mkApp v' r) (mkApp v r))))
  forallMem liveT P fun x => do
    let key := mkNatLit x
    let (nw, ne) := (mkNot (← memE wE key), mkNot (← memE eE key))
    let eq ← mkEq (mkApp v' key) (mkApp v key)
    withLocalDeclD `hw nw fun hw => do
    withLocalDeclD `he ne fun he => do
      if w.contains x then
        return ← mkLambdaFVars #[hw, he] (← mkAbsurd eq (← memProof x w) hw)
      if e.contains x then
        return ← mkLambdaFVars #[hw, he] (← mkAbsurd eq (← memProof x e) he)
      -- the table functions applied to the key unfolded to their lookups first, so that the
      -- entries are compared, not the functions (`sameValue` has a budget)
      let a' ← evalTable (← unfoldAt key (mkApp v' key).headBeta)
      let a ← evalTable (← unfoldAt key (mkApp v key).headBeta)
      unless ← sameValue a' a do
        throwError "seg_fp: the value of {x} changes ({a} to {a'}), but it is live at the \
          end and the segment does not write it"
      mkLambdaFVars #[hw, he] (← mkExpectedTypeHint (← mkEqRefl (mkApp v key)) eq)

/-- A proof of `∀ r ∈ liveT, r ∉ W → r ∉ E → v' r = v r`: by definition when the two value
functions are the same, else from their tables, else register by register. -/
meta def valProof (v' v : Expr) (w e liveT : List Nat) : MetaM (String × Expr) := do
  if ← withNewMCtxDepth (withReducible (isDefEq v' v)) then
    let tE ← regListE liveT
    let (wE, eE) := (← regListE w, ← regListE e)
    let pr ← withLocalDeclD `r (mkConst ``Nat) fun r => do
      withLocalDeclD `hl (← memE tE r) fun hl => do
      withLocalDeclD `hw (mkNot (← memE wE r)) fun hw => do
      withLocalDeclD `he (mkNot (← memE eE r)) fun he => do
        mkLambdaFVars #[r, hl, hw, he]
          (← mkExpectedTypeHint (← mkEqRefl (mkApp v r)) (← mkEq (mkApp v' r) (mkApp v r)))
    return ("same", pr)
  tryCatchRuntimeEx (return ("tables", ← valProofTables v' v w e liveT)) fun ex => do
    if (← IO.getEnv "SEG_FP_REPORT").isSome then
      IO.eprintln s!"  values: tables failed: {(← ex.toMessageData.toString).take 300}"
    return ("pointwise", ← valProofPointwise v' v w e liveT)

/-- `List.lookup r l` for a literal register `r` and a list with literal register keys, in one step
(by definition). -/
simproc_decl lookupLit (List.lookup _ _) := fun e => do
  unless e.isAppOfArity ``List.lookup 5 do return .continue
  let some key := regLit? (← whnfD (e.getArg! 3)) | return .continue
  let some r ← lookupWalk key (e.getArg! 4) | return .continue
  let β := e.getArg! 1
  let res ← match r with
    | some v => mkAppOptM ``Option.some #[β, v]
    | none => mkAppOptM ``Option.none #[β]
  return .done { expr := res }


/-- `pred_hyp`: close `Value.pred a = Value.pred b` where one side is a Boolean literal and a
hypothesis in context gives the other side that value (`c = lit`, or `¬ c = true` for `false`),
the hypothesis's side the same term up to reducible unfolding. The fact of a predicate that a
case split decided is checked this way, without evaluating the predicate's symbolic value. -/
elab "pred_hyp" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some (_, lhs, rhs) := ty.consumeMData.eq? | throwError "pred_hyp: not an equation"
  unless lhs.isAppOfArity ``PTX.Value.pred 1 && rhs.isAppOfArity ``PTX.Value.pred 1 do
    throwError "pred_hyp: not an equation of predicate values"
  let (a, b) := (lhs.getArg! 0, rhs.getArg! 0)
  let lit? (e : Expr) : Option Bool :=
    if e.isConstOf ``Bool.true then some true
    else if e.isConstOf ``Bool.false then some false else none
  -- `c = lit` from the context, as a proof
  let decide (c : Expr) (lit : Bool) : MetaM (Option Expr) := do
    let litE := mkConst (if lit then ``Bool.true else ``Bool.false)
    let same (x : Expr) : MetaM Bool := withNewMCtxDepth do
      if x == c then return true
      withReducible (isDefEq x c)
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let t := (← instantiateMVars d.type).consumeMData
      if let some (_, x, y) := t.eq? then
        if y == litE && (← same x) then return some d.toExpr
      if !lit && t.isAppOfArity ``Not 1 then
        if let some (_, x, y) := t.appArg!.consumeMData.eq? then
          if y.isConstOf ``Bool.true && (← same x) then
            return some (← mkAppM ``Iff.mpr #[← mkAppOptM ``Bool.eq_false_iff #[some x], d.toExpr])
    return none
  let pf? ← match lit? a, lit? b with
    | some la, none => do
      -- `pred la = pred b` from `b = la`
      let some h ← decide b la | pure none
      pure (some (← mkCongrArg (mkConst ``PTX.Value.pred) (← mkEqSymm h)))
    | none, some lb => do
      let some h ← decide a lb | pure none
      pure (some (← mkCongrArg (mkConst ``PTX.Value.pred) h))
    | _, _ => pure none
  let some pf := pf? | throwError "pred_hyp: no hypothesis decides the predicate"
  goal.assign (← mkExpectedTypeHint pf ty)
  replaceMainGoal []

/-- The step lemma `step_<pc>` of the kernel `K` (next to its code lemmas, `Flow.step_<pc>`), as a
term of type `PcLocal K A L g pc ins`, with its instruction `ins`; none when the kernel has no such
lemma or it is stated for other assumptions. -/
meta def stepLemma (K A L g : Expr) (pc : Nat) : MetaM (Option (Expr × Expr)) := do
  let some k := K.getAppFn.constName? | return none
  let name := k.getPrefix ++ `Flow ++ Name.mkSimple s!"step_{pc}"
  let some info := (← getEnv).find? name | return none
  let pf := mkAppN (mkConst name) #[L, g]
  let ty ← instantiateForall info.type #[L, g]
  unless ty.isAppOfArity ``PTX.Flow.PcLocal 6 do return none
  unless ty.getArg! 0 == K && ty.getArg! 1 == A do return none
  return some (pf, ty.getArg! 5)

/-- The run of a piece as a chain of step lemmas (`run_succ_local`): from the state `t0`, along
`path`, each state's successor is the local rule of the lemma's instruction, evaluated on the
state (`whnfD`); the proof term reads no code, guard or segment, and the kernel checks each step's
evaluation once. The end state and the proof of `run K A L g n t0 = some tn`, or none when a
program counter of the path has no lemma or a step does not evaluate to a state at the path's
next program counter. -/
meta def stepChain (K A L g t0 : Expr) (path : List Nat) (b : Nat) :
    MetaM (Option (Expr × Expr)) := do
  let mut t := t0
  let mut steps : Array (Expr × Expr × Expr × Expr × Nat) := #[]
  let pcs := path.toArray
  for i in [0:pcs.size] do
    let pc := pcs[i]!
    let why (m : String) : MetaM (Option (Expr × Expr)) := do
      if (← IO.getEnv "SEG_FP_REPORT").isSome then IO.eprintln s!"  chain: pc {pc}: {m}"
      return none
    let some (h, op) ← stepLemma K A L g pc | return ← why "no step lemma"
    let r ← whnfD (mkAppN (mkConst ``PTX.Flow.stepIns) #[A, L, g, t, op])
    unless r.isAppOfArity ``Option.some 2 do return ← why "the step does not evaluate"
    let t' := r.getArg! 1
    let next := if i + 1 < pcs.size then pcs[i + 1]! else b
    let q ← try natValue (mkApp (mkConst ``PTX.TState.pc) t') catch _ =>
      return ← why "the next program counter does not evaluate"
    unless q == next do return ← why s!"the step goes to {q}, not {next}"
    steps := steps.push (t, t', h, op, pc)
    t := t'
  let tn := t
  let stTy := mkConst ``PTX.TState
  let optTy := mkApp (mkConst ``Option [0]) stTy
  let mut prf := mkApp2 (mkConst ``Eq.refl [1]) optTy (mkApp2 (mkConst ``Option.some [0]) stTy tn)
  let mut n := 0
  let faultTy := mkApp (mkConst ``Option [0]) (mkConst ``PTX.Fault)
  let noFault := mkApp (mkConst ``Option.none [0]) (mkConst ``PTX.Fault)
  for (ti, ti', h, op, pc) in steps.reverse do
    let someT := mkApp2 (mkConst ``Option.some [0]) stTy ti'
    prf := mkAppN (mkConst ``PTX.Flow.run_succ_local)
      #[K, A, L, g, mkNatLit pc, mkNatLit n, op, ti, ti', tn, h,
        mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit pc),
        mkApp2 (mkConst ``Eq.refl [1]) faultTy noFault,
        mkApp2 (mkConst ``Eq.refl [1]) optTy someT, prf]
    n := n + 1
  return some (tn, prf)

/-- The run of a piece by step lemmas (`stepChain`), on a goal `∃ t, run K A L g n t0 = some t ∧
rest` along the single path `path` to `b`: the goal's witness is the chain's end state and its
`rest` is left as the main goal. False (and the goal unchanged) when the chain does not apply. -/
meta def chainRun (K A L g : Expr) (path : List Nat) (b : Nat) : TacticM Bool := do
  let g0 ← getMainGoal
  g0.withContext do
  let ty ← instantiateMVars (← g0.getType)
  let some (_, body) := ty.app2? ``Exists | return false
  let .lam bn bty body bi := body | return false
  let some (eqE, _) := body.app2? ``And | return false
  let some (_, runE, _) := eqE.app3? ``Eq | return false
  unless runE.isAppOfArity ``PTX.run 6 do return false
  let t0 := runE.getArg! 5
  if t0.hasLooseBVars then return false
  let some (tn, prf) ← stepChain K A L g t0 path b | return false
  let rest := (body.getArg! 1).instantiate1 tn
  let restM ← mkFreshExprSyntheticOpaqueMVar rest
  let andPf := mkApp4 (mkConst ``And.intro) ((body.getArg! 0).instantiate1 tn) rest prf restM
  g0.assign (mkApp4 (mkConst ``Exists.intro [1]) bty (.lam bn bty body bi) tn andPf)
  replaceMainGoal [restM.mvarId!]
  return true

/-- `seg_fp h using tac`: prove `∃ t', run K A L g n t0 = some t' ∧ At t' b G` from
`h : At t0 s F` by evaluating the segment on its footprint. `tac` closes each equation
between a computed and a stated value of a written register, after `ty_eval` has evaluated the
instruction types in it. -/
syntax "seg_fp_core " term:max " using " tacticSeq : tactic

meta def reportFailure (e : Exception) (t0 : Nat := 0) : TacticM Unit := do
  if (← IO.getEnv "SEG_FP_REPORT").isSome then
    IO.eprintln s!"seg_fp failed after {(← IO.monoMsNow) - t0} ms: \
      {(← e.toMessageData.toString).take 700}"

elab_rules : tactic
  | `(tactic| seg_fp_core $h using $vals) => withMainContext do
  let tStart ← IO.monoMsNow
  tryCatchRuntimeEx (do
   try
      let goal := (← instantiateMVars (← getMainTarget)).consumeMData
      let some (_, body) := goal.app2? ``Exists | throwError "seg_fp: goal is not ∃ t', … : {goal}"
      let .lam _ _ body _ := body.consumeMData | throwError "seg_fp: goal is not ∃ t', …"
      let some (eqE, atE) := body.consumeMData.app2? ``And | throwError "seg_fp: goal is not … ∧ …"
      let some (_, runE, _) := eqE.app3? ``Eq | throwError "seg_fp: expected run … = some t'"
      unless runE.isAppOfArity ``PTX.run 6 do throwError "seg_fp: expected run, got {runE}"
      let #[K, A, L, g, nE, _] := runE.getAppArgs | throwError "seg_fp: run arguments"
      let useVector := atE.isAppOfArity ``PTX.Flow.AtVector 5
      unless useVector || atE.isAppOfArity ``PTX.Proof.At 3 do
        throwError "seg_fp: expected At or AtVector, got {atE}"
      let bE := atE.getArg! 1
      let G := atE.getArg! 2
      let hE ← elabTerm h none
      -- the term goes into the assembled proof: its state is the run's (which determines the
      -- implicit arguments the elaborator would infer from the goal), its pending arguments are
      -- synthesized now
      let hTy0 ← instantiateMVars (← inferType hE)
      let t0Goal := runE.getArg! 5
      if hTy0.hasExprMVar && hTy0.getAppNumArgs ≥ 1 && !t0Goal.hasLooseBVars then
        discard <| isDefEq (hTy0.getArg! 0) t0Goal
      Term.synthesizeSyntheticMVarsNoPostponing
      let hE ← instantiateMVars hE
      if hE.hasExprMVar then throwError "seg_fp: the start facts' proof {hE} has holes"
      let hTy ← instantiateMVars (← inferType hE)
      unless if useVector then hTy.isAppOfArity ``PTX.Flow.AtVector 5
          else hTy.isAppOfArity ``PTX.Proof.At 3 do
        throwError "seg_fp: input and output must both use At or both use AtVector"
      let sE := hTy.getArg! 1
      let F0 := hTy.getArg! 2
      let n ← natValue nE
      let s ← natValue sE
      let b ← natValue bE
      let code ← mkAppM ``PTX.Kernel.code #[K]
      let (paths, reads, writes) ← (do
        let paths ← segPaths K code s n b
        let (r, w) ← match paths with
          | [p] => footprint K code p
          | [] => throwError "seg_fp: no path of {n} instructions from {s} to {b}"
          | p :: ps => do
            let fp ← footprint K code p
            for q in ps do
              unless (← footprint K code q) == fp do
                throwError "seg_fp: paths from {s} to {b} differ in footprint"
            pure fp
        pure (paths, r, w) : SegM _).run' {}
      let (exS, tblS) ← splitFacts F0
      let (exT, tblT) ← splitFacts G
      let zero ← mkAppM ``PTX.Proof.b32 #[mkNatLit 0]
      let constV ← withLocalDeclD `r (mkConst ``Nat) fun r => mkLambdaFVars #[r] zero
      let nilS ← regListE []
      let (liveS, v) := tblS.getD (nilS, (tblT.map (·.2)).getD constV)
      let (liveT, v') := tblT.getD (nilS, v)
      let liveSs ← regList liveS
      let liveTs ← regList liveT
      let mut exKeys := #[]
      for p in exS do
        let some k := regLit? (← whnfD (← mkAppM ``Prod.fst #[p])) |
          throwError "seg_fp: explicit fact {p}"
        exKeys := exKeys.push k
      -- an explicit end fact of a register the segment does not write is a start fact
      let mut allReads := reads
      for p in exT do
        if let some k := regLit? (← whnfD (← mkAppM ``Prod.fst #[p])) then
          unless writes.contains k || allReads.contains k do allReads := allReads.push k
      let reads := allReads.filter liveSs.contains
      -- written registers that are live at the end are checked; live registers that are
      -- neither written nor in the start table come from the explicit start facts
      let checked := writes.filter liveTs.contains
      let extra := liveTs.filter fun r => !writes.contains r && !liveSs.contains r
      let liveS ← mkRegList liveSs
      let liveT ← mkRegList liveTs
      let pairTy ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``PTX.Value]
      let exSE ← mkListLit pairTy exS.toList
      let exTE ← mkListLit pairTy exT.toList
      let readsE ← mkRegList reads
      let mut explicitReads := #[]
      for r in reads do
        let val ← evalTable (mkApp v (mkNatLit r))
        explicitReads := explicitReads.push (← mkAppM ``Prod.mk #[mkNatLit r, val])
      let fExp ← mkListLit pairTy (exS.toList ++ explicitReads.toList)
      let writesE ← mkRegList writes
      let report := (← IO.getEnv "SEG_FP_REPORT").isSome
      let timed {α} (label : String) (x : TacticM α) : TacticM α := do
        let t0 ← IO.monoMsNow
        let a ← x
        if report then IO.eprintln s!"seg_fp {s}→{b}: {label} {(← IO.monoMsNow) - t0} ms"
        return a
      if report then
        IO.eprintln
          s!"seg_fp {s}→{b}: reads {reads} writes {writes} checked {checked} extra {extra}"
        IO.eprintln s!"  Fexp {(← ppExpr fExp).pretty.take 600}"
      let subPr ← subsetProof reads.toList liveSs.toList
      let chkPr ← checkedProof writes.toList checked.toList liveTs.toList
      let covPr ← coverProof liveTs.toList writes.toList liveSs.toList extra.toList
      let exPr ← extraProof extra.toList exKeys.toList exS.toList v'
      let saved ← saveState
      let errors := fun (log : MessageLog) => log.toList.filter (·.severity == .error)
      let before := (errors (← Core.getMessageLog)).length
      let step (label : String) (tac : TSyntax `tactic) : TacticM Unit :=
        timed label (evalTactic tac)
      -- the lemma applied to its arguments as terms: every argument has its parameter's type
      -- up to unfolding the tables (the facts `F0`, `G` and `Fexp` against their split forms),
      -- which the kernel checks once; elaborating the application would have the elaborator
      -- unfold the tables at every segment
      let valM ← timed "assemble" do
        let goal ← getMainGoal
        let t0 := hTy.getArg! 0
        let tblArgs := #[K, A, L, g, nE, sE, bE, t0, exSE, exTE, fExp, liveS, liveT, readsE,
          writesE, ← mkRegList checked, ← mkRegList extra, v, v']
        let vecArgs := if useVector then
          #[hTy.getArg! 3, atE.getArg! 3, hTy.getArg! 4, atE.getArg! 4] else #[]
        let lemName := if useVector then ``PTX.Flow.seg_footprint_vector
          else ``PTX.Flow.seg_footprint
        let regsTy ← mkAppM ``PTX.Proof.Holds
          #[← mkAppM ``PTX.TState.regs #[t0], ← mkAppM ``HAppend.hAppend
            #[exSE, ← mkAppM ``PTX.Flow.factsFrom #[readsE, v]]]
        let hexp := mkApp (mkConst ``id [Level.zero]) regsTy
        let pre := tblArgs ++ vecArgs ++ #[hE, subPr, hexp]
        let runTy ← instantiateForall (← inferType (mkConst lemName)) pre
        let .forallE _ runTy _ _ := runTy | throwError "seg_fp: the lemma's run argument"
        let runM ← mkFreshExprSyntheticOpaqueMVar runTy `run
        -- the frame's values (`hval`) are proved after the evaluation, which is where a
        -- segment the evaluation cannot take fails
        let valTy ← instantiateForall (← inferType (mkConst lemName))
          (pre ++ #[runM, chkPr, covPr, exPr])
        let .forallE _ valTy _ _ := valTy | throwError "seg_fp: the lemma's value argument"
        let valM ← mkFreshExprMVar valTy
        goal.assign (mkAppN (mkConst lemName) (pre ++ #[runM, chkPr, covPr, exPr, valM]))
        replaceMainGoal [runM.mvarId!]
        pure valM
      -- the run: by the step lemmas when every program counter of the path has one, else by
      -- evaluating the run
      evalTactic (← `(tactic| intro R))
      let chained ← timed "chain" do
        if useVector || paths.length != 1 then pure false
        else if ← chainRun K A L g (paths.headD []) b then
          evalTactic (← `(tactic| refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩))
          pure true
        else pure false
      unless chained do
        step "eval" (← `(tactic| refine ⟨_, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩))
      step "written-holds" (← `(tactic| focus
        holds_facts))
      let nFacts := (← getGoals).length - 1
      for _ in [0:nFacts] do
        if report then
          IO.eprintln
            s!"  goal: {(← ppExpr (← instantiateMVars (← getMainTarget))).pretty.take 400}"
        step "written-vals" (← `(tactic| · first | pred_hyp | (ty_eval <;> ($vals))))
      step "frame" (← `(tactic| ·
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [PTX.setDst, PTX.setReg, PTX.next, PTX.skip, Function.update_apply, hr,
          ite_false]
        try (($vals) <;> (simp only [PTX.setDst, PTX.setReg, PTX.next, PTX.skip,
          Function.update_apply, hr, ite_false]) <;> rfl)))
      let new := (errors (← Core.getMessageLog)).drop before
      if let some m := new.head? then
        let text ← m.data.toString
        saved.restore (restoreInfo := true)
        throwError "seg_fp failed (pc {s} → {b}, {n} steps): {text}"
      let (how, valPr) ← timed "values" (try valProof v' v writes.toList extra.toList liveTs.toList
        catch e => saved.restore (restoreInfo := true); throw e)
      if report then IO.eprintln s!"seg_fp {s}→{b}: values by {how}"
      valM.mvarId!.assign valPr

   catch e =>
      reportFailure e tStart
      throw e)
    (fun e => do reportFailure e tStart; throw e)

/-- `frame_fp hS, hframe` proves the facts `Holds R' (exT ++ factsFrom liveT v')` of a state
whose registers agree with those of a state with facts `hS : Holds R (ex ++ factsFrom liveS v)`
outside the registers `W` (`hframe : ∀ r, r ∉ W → R' r = R r`): for an event that writes
registers. It leaves the facts of the written registers that are live. -/
syntax "frame_fp " term:max ", " term:max : tactic

elab_rules : tactic
  | `(tactic| frame_fp $hS, $hframe) => withMainContext do
    let goal := (← instantiateMVars (← getMainTarget)).consumeMData
    unless goal.isAppOfArity ``PTX.Proof.Holds 2 do throwError "frame_fp: goal is not Holds"
    let hSE ← elabTerm hS none
    let hSTy ← instantiateMVars (← inferType hSE)
    unless hSTy.isAppOfArity ``PTX.Proof.Holds 2 do throwError "frame_fp: {hS} is not Holds"
    let hfE ← elabTerm hframe none
    let .forallE _ _ (.forallE _ prem _ _) _ ← instantiateMVars (← inferType hfE) |
      throwError "frame_fp: expected ∀ r, r ∉ W → R' r = R r"
    let notMem := prem.consumeMData
    unless notMem.isAppOfArity ``Not 1 && (notMem.getArg! 0).isAppOfArity ``Membership.mem 5 do
      throwError "frame_fp: expected ∀ r, r ∉ W → R' r = R r"
    let writes ← regList ((notMem.getArg! 0).getArg! 3)
    let (exS, tblS) ← splitFacts (hSTy.getArg! 1)
    let (exT, tblT) ← splitFacts (goal.getArg! 1)
    let some (liveS, v) := tblS | throwError "frame_fp: the start facts have no table"
    let some (liveT, v') := tblT | throwError "frame_fp: the end facts have no table"
    let liveSs ← regList liveS
    let liveTs ← regList liveT
    let mut exKeys := #[]
    for p in exS do
      let some k := regLit? (← whnfD (← mkAppM ``Prod.fst #[p])) |
        throwError "frame_fp: explicit fact {p}"
      exKeys := exKeys.push k
    let checked := writes.filter liveTs.contains
    let extra := liveTs.filter fun r => !writes.contains r && !liveSs.contains r
    let pairTy ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``PTX.Value]
    let stx (e : Expr) := Term.exprToSyntax e
    let tChk ← stx (← checkedProof writes.toList checked.toList liveTs.toList)
    let tCov ← stx (← coverProof liveTs.toList writes.toList liveSs.toList extra.toList)
    let tEx ← stx (← extraProof extra.toList exKeys.toList exS.toList v')
    let (how, valPr) ← valProof v' v writes.toList extra.toList liveTs.toList
    if (← IO.getEnv "SEG_FP_REPORT").isSome then
      IO.eprintln s!"frame_fp: writes {writes} checked {checked} extra {extra}, values by {how}"
    let tVal ← stx valPr
    let (tex, texT) := (← stx (← mkListLit pairTy exS.toList),
      ← stx (← mkListLit pairTy exT.toList))
    let (tlS, tlT) := (← stx (← mkRegList liveSs), ← stx (← mkRegList liveTs))
    let (tW, tWc, tE) := (← stx (← mkRegList writes), ← stx (← mkRegList checked),
      ← stx (← mkRegList extra))
    let (tv, tv') := (← stx v, ← stx v')
    evalTactic (← `(tactic|
      refine PTX.Flow.holds_transfer (ex := $tex) (exT := $texT) (liveS := $tlS) (liveT := $tlT)
        (W := $tW) (Wc := $tWc) (E := $tE) (v := $tv) (v' := $tv')
        $hS ?_ $hframe $tChk $tCov $tEx $tVal))

/-- `lit_mem` proves a membership fact of literal register lists (after evaluation):
`a ∈ l`, or `∀ r ∈ l', r ∈ l`. The proof names the position of each register, so the kernel
compares no register ids. -/
elab "lit_mem" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty := (← instantiateMVars (← goal.getType)).consumeMData
  let mem? (e : Expr) : Option (Expr × Expr) :=
    if e.isAppOfArity ``Membership.mem 5 then some (e.getArg! 3, e.getArg! 4) else none
  let proof ←
    if let some (l, a) := mem? ty then
      let some x := regLit? (← whnfD a) | throwError "lit_mem: not a literal {a}"
      memProof x (← regList l).toList
    else if let .forallE _ _ (.forallE _ prem concl _) _ := ty then
      let some (l', _) := mem? prem | throwError "lit_mem: expected ∀ r ∈ l', r ∈ l"
      let some (l, _) := mem? concl | throwError "lit_mem: expected ∀ r ∈ l', r ∈ l"
      subsetProof (← regList l').toList (← regList l).toList
    else throwError "lit_mem: expected a ∈ l or ∀ r ∈ l', r ∈ l"
  goal.assign (← mkExpectedTypeHint proof ty)
  replaceMainGoal []

/-- `code_at h` turns `h : K.code[i]? = some ins`, for a closed index `i`, into `h : ins = I`
with the instruction `I` at `i`, from the kernel's generated lookup `Flow.code_<i>`. The kernel
checks only that the index evaluates to the lemma's literal. -/
elab "code_at " h:ident : tactic => withMainContext do
  let hE ← elabTerm h none
  let ty ← instantiateMVars (← inferType hE)
  let some (_, lhs, _) := ty.consumeMData.eq? | throwError "code_at: {h} is not an equation"
  unless lhs.isAppOfArity ``GetElem?.getElem? 7 do throwError "code_at: expected K.code[i]?"
  let xs := lhs.getArg! 5
  let i := lhs.getArg! 6
  unless xs.isAppOfArity ``PTX.Kernel.code 1 do throwError "code_at: expected K.code[i]?"
  let some k := xs.appArg!.getAppFn.constName? | throwError "code_at: the kernel is not a constant"
  let n ← natValue i
  let lemmaName := k.getPrefix ++ `Flow ++ Name.mkSimple s!"code_{n}"
  let some info := (← getEnv).find? lemmaName | throwError "code_at: no lookup {lemmaName}"
  let some (_, _, rhsLit) := info.type.eq? | throwError "code_at: {lemmaName} is not an equation"
  let lem ← mkExpectedTypeHint (mkConst lemmaName) (← mkEq lhs rhsLit)
  let pf ← mkAppM ``Option.some.inj #[← mkEqTrans (← mkEqSymm lem) hE]
  let g ← getMainGoal
  let (_, g) ← g.note h.getId pf
  replaceMainGoal [g]

/-- A closed fact about generated tables: a membership fact of literal register lists by
position (`lit_mem`), anything else by kernel evaluation. -/
macro "table_decide" : tactic => `(tactic| first | lit_mem | decide +kernel)

/-- `seg_fp_core` with the recursion depth that evaluating code at a large pc needs. -/
macro "seg_fp " h:term:max " using " vals:tacticSeq : tactic =>
  `(tactic| try_rt (set_option maxRecDepth 100000 in seg_fp_core $h using $vals))

/-- Close an equation between a computed and a stated register value: the same term, a joined
or parameter value, an integer, predicate or float (`close_fact` with the given lemmas), or a
closed equation the kernel evaluates. -/
syntax "seg_close" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| seg_close $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| first
      | try_rt (with_reducible rfl)
      | (show PTX.joinValue _ _ = _; simp [PTX.joinValue, PTX.Value.bytes])
      | (show PTX.Value.ptr _ _ (.param _) 0 = _; simp)
      | try_rt (close_fact [$extra,*])
      | try_rt (decide +kernel))

end PTX.Flow
