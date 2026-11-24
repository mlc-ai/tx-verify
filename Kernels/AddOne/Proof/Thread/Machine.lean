-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.AddOne.Spec
public import Kernels.AddOne.Flow.Sites
public import Kernels.AddOne.Flow.Code
public import Lemmas.Flow.Code
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Next
public import Lemmas.Flow.Local
public import Lemmas.Flow.Async
public import Lemmas.Flow.Scalars
public import Lemmas.Flow.MemTmpl

@[expose] public section

/-! # `add_one`: the site machine of a thread

Thread `g` loads `A[g]`, adds 1 to the loaded value, stores the sum to `A[g]` and exits. The
states are the event instructions (`Site`); the store carries the sum. The sum is what the
`add.s32` rule computes from the loaded value (`incr`); a load whose bytes rebuild to no value,
or whose value the addition rejects, makes the thread fault (the machine stops). The register
facts at each site are the generated live registers valued by one table (`values`). -/

namespace PTX.Kernels.AddOne.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The event instructions of a thread. -/
inductive Site where
  | load
  /-- The store of the sum. -/
  | store (w : Value)
  | exit

def Site.pc : Site → Nat
  | .load => Flow.load_0 | .store _ => Flow.store_0 | .exit => Flow.exit_0

/-- The instruction between the load and the store: `add.s32 %r3, %r2, 1`. -/
def addI : IntInstr := ⟨.add, .int .s 32, false, [some 3], [.reg 2, .imm 1]⟩

def addOp : Op := .int addI

/-- The sum the addition computes from the loaded value `v` (THREAD-INT), or its fault. -/
def incr (L : Launch) (g : Nat) (v : Value) : Exec Value := do
  let t ← execInt L g (setReg {} 2 v) addI
  readReg t 3

/-- **The addition of a 32-bit word** `y` is the word `y + 1`, modulo `2 ^ 32`. -/
theorem incr_word (L : Launch) (g : Nat) (y : BitVec 32) : incr L g (word y) = .ok (word (y + 1)) :=
    by
  simp only [incr, addI, DType.width, execInt, readValue, readBits, readReg, setReg, word, PTX.next,
    Function.update_self, pure, Except.pure, bind, Except.bind]
  congr 3
  apply BitVec.eq_of_toNat_eq
  have h1 : (BitVec.ofInt 64 1).toNat = 1 := by decide
  have h1' : (1 : BitVec 32).toNat = 1 := rfl
  have hy := y.isLt
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, h1, h1']
  omega

/-- The value of every register a thread uses at a site. -/
def values (A g : Nat) (s : Site) : List (Nat × Value) :=
  [(6, b64 (A + 4 * g)), (3, match s with | .store w => w | _ => b32 0)]

def valueOf (A g : Nat) (s : Site) (r : Nat) : Value :=
  ((values A g s).lookup r).getD (b32 0)

def factsAt (A g pc : Nat) (s : Site) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf A g s)

abbrev facts (A g : Nat) (s : Site) : List (Nat × Value) :=
  factsAt A g s.pc s

/-- The successor after event `e`. A load whose bytes rebuild to no value, or whose value the
addition rejects, faults the thread; so does a store of a value that is not one 4-byte word. -/
def next (L : Launch) (g : Nat) : Site → Event → Option (Option Site)
  | .load, e => match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => match incr L g v with
        | .ok w => some (some (.store w))
        | .error _ => none
      | .error _ => none
    | _ => none
  | .store _, e => match e.kind with
    | .wr .. => some (some .exit)
    | _ => none
  | .exit, _ => none

/-- The code machine of thread `g`. -/
def code (L : Launch) (A g : Nat) : Code kernel [] L g where
  D := Site
  init := .load
  pc := Site.pc
  facts := facts A g
  inv := fun _ => True
  next := next L g

macro "ao_values" : tactic =>
  `(tactic| simp only [valueOf, values, List.lookup_cons, Nat.reduceBEq, Option.getD_some,
    PTX.Flow.lookupLit, Option.getD_none])

/-- Evaluate a segment of the thread from `h` and close the facts of its end state. -/
syntax "ao_seg" term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| ao_seg $h $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| seg_fp $h using
        try ao_values
        all_goals seg_close [$extra,*])

variable {L : Launch} {A : Nat} {x : Nat → BitVec 32} {mem0 : Mem0} {g : Nat}

def ps (A : Nat) : List (String × Nat) := [("add_one_param_0", A)]

theorem params (hpre : Pre L A x mem0) : explicitParams L (ps A) = L :=
  explicitParams_eq (by
    intro p v hm
    simp only [ps, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact hpre.param0)

set_option maxHeartbeats 4000000 in
/-- **The opening code** reaches the load with the address of `A[g]`. -/
theorem start (hpre : Pre L A x mem0) (hg : g < L.threads) :
    ∃ t, Relation.ReflTransGen (Tau kernel [] L g) {} t ∧
      At t (code L A g).init.pc (facts A g (code L A g).init) := by
  have hp := params hpre
  obtain ⟨_, hgr, hbl, _, hrA, _, hone⟩ := hpre
  have hgb : g < L.block := by simpa [Launch.threads, hgr] using hg
  have hmod : g % L.block = g := Nat.mod_eq_of_lt hgb
  have htid := Launch.oneDim_tidOf hone.1 g
  obtain ⟨t, hr, ht⟩ : ∃ t, run kernel [] (explicitParams L (ps A)) g 5 {} = some t ∧
      At t Site.load.pc (facts A g .load) := by
    seg_fp at_init using
      try ao_values
      all_goals (simp only [hp]; rw [htid, hmod]; show Value.bits _ _ = _; norm_bits [Dim3.get])
  rw [hp] at hr
  exact ⟨t, run_rtg hr, ht⟩

/-- The addition after the load computes `incr` of the loaded value. -/
theorem out_add {t : TState} {v : Value} (hpc : t.pc = Flow.load_0 + 1) (hf : t.fault = none)
    (h2 : t.regs 2 = some v) :
    out kernel [] L g t = match incr L g v with
      | .ok w => .tau (PTX.next (setReg t 3 w))
      | .error f => .ev (.ub f) := by
  have hc : kernel.code[Flow.load_0 + 1]? = some ⟨none, addOp⟩ := rfl
  have hr : addI.rule = some .threadInt := rfl
  simp only [out, hf, hpc, hc, guardHolds, addOp, Op.isLocal, execLocalA_nil, execLocal_int hr]
  cases v <;> simp [incr, addI, DType.width, Op.varyingSregs, Opnd.varying?, execInt,
    readValue, readBits, readReg, setReg, h2, PTX.next, pure, Except.pure, bind, Except.bind, throw,
    throwThe, MonadExceptOf.throw]
  all_goals first
    | rfl
    | (generalize Value.bitPattern _ = p; cases p <;> rfl)
    | (cases ‹PtrTarget› <;> first
        | rfl
        | (generalize offsetPointer _ (.ptr _ _ _ _) _ = p
           cases p with | ok => rfl | error f => cases f <;> rfl))

/-- The instruction at each site performs an event and has no guard. -/
theorem site_ok (s : Site) : ∃ ins, kernel.code[s.pc]? = some ins ∧ ins.op.isLocal = false ∧
    Code.GuardTrue (facts A g s) ins.guard := by
  cases s with
  | load => exact ⟨_, Flow.code_load_0, rfl, trivial⟩
  | store _ => exact ⟨_, Flow.code_store_0, rfl, trivial⟩
  | exit => exact ⟨_, Flow.code_exit_0, rfl, trivial⟩

/-- What a step of the machine owes. -/
abbrev Step (L : Launch) (A g : Nat) (s : Site) (u : TState) (e : Event) : Prop :=
  ((code L A g).next s e = some none ∨ ∃ d' t', (code L A g).next s e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel [] L g) u t' ∧ (code L A g).Good (some d') t') ∨
    ((code L A g).next s e = none ∧ Machine.Dead (K := kernel) (A := []) (L := L) (g := g) u)

/-- Every site's event reaches its successor's facts. -/
theorem step {s : Site} {t u : TState} {e : Event} {ins : Instr}
    (h : At t s.pc (facts A g s)) (hc : kernel.code[s.pc]? = some ins)
    (hf : Fires s.pc (eventTmpl [] L g t ins.op) e (some u)) : Step L A g s u e := by
  cases s with
  | load =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
    obtain ⟨a, bs, rfl, rfl⟩ := fires_load rfl rfl hf
    cases hv : rebuild 3 bs with
    | error f =>
      exact .inr ⟨by simp [code, next, hv],
        Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
    | ok v =>
      rw [show MemAccess.regs _ = [2] from rfl, afterLoad_ok h.2.1 h.2.2.1 hv]
      have h6 : t.regs 6 = some (b64 (A + 4 * g)) := by
        have hl : Flow.live Site.load.pc = [6] := by decide +kernel
        have := h.2.2.2.2
        simp only [facts, factsAt, hl, Flow.factsFrom, List.map_cons, List.map_nil] at this
        exact this.1
      have hout := out_add (L := L) (g := g)
        (t := { setReg t 2 v with pc := t.pc + 1, sub := 0, acc := [] }) (v := v)
        (by simp [h.1, Site.pc]) h.2.2.2.1 (by simp [setReg])
      cases hw : incr L g v with
      | error f =>
        rw [hw] at hout
        exact .inr ⟨by simp [code, next, hv, hw], Machine.dead_of_ub hout⟩
      | ok w =>
        rw [hw] at hout
        refine .inl (.inr ⟨.store w, _, by simp [code, next, hv, hw], .single hout, ?_, trivial⟩)
        have hl : Flow.live Flow.store_0 = [3, 6] := by decide +kernel
        refine ⟨by simp [PTX.next, setReg, h.1, Site.pc, code], rfl, rfl, h.2.2.2.1, ?_⟩
        show Holds _ (factsAt A g Flow.store_0 (.store w))
        simp only [factsAt, hl, Flow.factsFrom, List.map_cons, List.map_nil]
        ao_values
        simp [PTX.next, setReg, Function.update, h6]
  | store w =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_0)
    obtain ⟨a, bs, rfl, rfl⟩ := fires_st rfl hf
    have hl : Flow.live Site.exit.pc = [] := by decide +kernel
    refine .inl
      (.inr ⟨.exit, _, by simp [code, next], .refl, ⟨?_, by simp [afterStore, h.2.1]; rfl, h.2.2.1,
      h.2.2.2.1, ?_⟩, trivial⟩)
    · simp [afterStore, h.2.1, h.1]
      rfl
    · show Holds _ (factsAt A g Site.exit.pc .exit)
      simp only [factsAt, hl, Flow.factsFrom, List.map_nil]
      trivial
  | exit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    simp [eventTmpl, Fires] at hf

/-- **Every launched thread is simulated by its code machine.** -/
theorem sound (hpre : Pre L A x mem0) (hg : g < L.threads) : (code L A g).Sound where
  start := by
    obtain ⟨t, hr, ht⟩ := start hpre hg
    exact ⟨t, hr, ht, trivial⟩
  steps := fun s => ⟨fun _ => site_ok s, fun ins h _ hc hf => step h hc hf⟩

end

end PTX.Kernels.AddOne.Proof
