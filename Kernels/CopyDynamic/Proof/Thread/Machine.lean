-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.CopyDynamic.Spec
public import Kernels.CopyDynamic.Flow.Sites
public import Kernels.CopyDynamic.Flow.Code
public import Lemmas.Flow.Code
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Next
public import Lemmas.Flow.Local
public import Lemmas.Flow.Async
public import Lemmas.Flow.Scalars
public import Lemmas.Flow.MemTmpl

@[expose] public section

/-! # `copy_dynamic`: the site machine of a thread

A thread `g < N` loads `A[g]`, stores the loaded word to `B[g]` and exits; every other thread
exits. The states are the event instructions (`Site`); the store carries the value the load's
bytes rebuild to, and a load whose bytes rebuild to no value makes the thread fault (the machine
stops). The register facts at each site are the generated live registers valued by one table
(`values`). -/

namespace PTX.Kernels.CopyDynamic.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The event instructions of a thread. -/
inductive Site where
  | load
  /-- The store of the value the load returned. -/
  | store (v : Value)
  | exit

def Site.pc : Site → Nat
  | .load => Flow.load_0 | .store _ => Flow.store_0 | .exit => Flow.exit_0

/-- The value of every register a thread uses at a site or at the branch. -/
def values (A B N g : Nat) (s : Site) : List (Nat × Value) :=
  [(1, .pred (decide (N ≤ g))), (3, b32 g), (10, b64 A), (11, b64 B), (13, b64 B),
   (14, b64 (4 * g)), (15, b64 (A + 4 * g)), (16, b64 (B + 4 * g)),
   (8, match s with | .store v => v | _ => b32 0)]

def valueOf (A B N g : Nat) (s : Site) (r : Nat) : Value :=
  ((values A B N g s).lookup r).getD (b32 0)

def factsAt (A B N g pc : Nat) (s : Site) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf A B N g s)

abbrev facts (A B N g : Nat) (s : Site) : List (Nat × Value) :=
  factsAt A B N g s.pc s

/-- The successor after event `e`. A load whose bytes rebuild to no value faults the thread, and so
does a store of a value that is not one 4-byte word. -/
def next : Site → Event → Option (Option Site)
  | .load, e => match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => some (some (.store v))
      | .error _ => none
    | _ => none
  | .store _, e => match e.kind with
    | .wr .. => some (some .exit)
    | _ => none
  | .exit, _ => none

/-- The code machine of thread `g`. -/
def code (L : Launch) (A B N g : Nat) : Code kernel [] L g where
  D := Site
  init := if g < N then .load else .exit
  pc := Site.pc
  facts := facts A B N g
  inv := fun _ => True
  next := next

macro "cd_values" : tactic =>
  `(tactic| simp only [valueOf, values, List.lookup_cons, Nat.reduceBEq, Option.getD_some,
    PTX.Flow.lookupLit, Option.getD_none])

/-- Evaluate a segment of the thread from `h` and close the facts of its end state. -/
syntax "cd_seg" term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| cd_seg $h $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| seg_fp $h using
        try cd_values
        all_goals seg_close [$extra,*])

variable {L : Launch} {A B N : Nat} {x : Nat → Value} {mem0 : Mem0} {g : Nat}

def ps (A B N : Nat) : List (String × Nat) :=
  [("copy_dynamic_param_0", A), ("copy_dynamic_param_1", B), ("copy_dynamic_param_2", N)]

theorem params (hpre : Pre L A B N x mem0) : explicitParams L (ps A B N) = L :=
  explicitParams_eq (by
    intro p v hm
    simp only [ps, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [hpre.param0, hpre.param1, hpre.param2])

set_option maxHeartbeats 4000000 in
/-- The opening code reaches the branch with the thread's index and the comparison with `N`. -/
theorem seg_branch (hpre : Pre L A B N x mem0) (hg : g < L.threads) :
    ∃ t, run kernel [] L g 8 {} = some t ∧ At t 8 (factsAt A B N g 8 .load) := by
  have hp := params hpre
  have hone := hpre.oneDimLaunch
  obtain ⟨_, _, _, hN, hT, hbl, _, _, hrA, hrB, _, _, _, _⟩ := hpre
  have htid := Launch.oneDim_tidOf hone.1 g
  have hcta := Launch.oneDim_ctaidOf hone.1 (g / L.block)
  have hsum : g / L.block * L.block + g % L.block = g := Nat.div_add_mod' g L.block
  have hnx : L.ntid.x = L.block := by rw [hone.1.1]
  have hg32 : g < 2 ^ 32 := by omega
  have hgm : g % 2 ^ 32 = g := Nat.mod_eq_of_lt hg32
  have hbm : L.block % 2 ^ 32 = L.block := Nat.mod_eq_of_lt hbl
  have hcm : g / L.block % 2 ^ 32 = g / L.block :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self g L.block) hg32)
  have htm : g % L.block % 2 ^ 32 = g % L.block :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le g L.block) hg32)
  have hpm : g / L.block * L.block % 2 ^ 32 = g / L.block * L.block :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self g L.block) hg32)
  have hsm : (g / L.block * L.block + g % L.block) % 2 ^ 32 = g := by rw [hsum, hgm]
  obtain ⟨t, hr, ht⟩ : ∃ t, run kernel [] (explicitParams L (ps A B N)) g 8 {} = some t ∧
      At t 8 (factsAt A B N g 8 .load) := by
    -- The geometry facts (`htid`, `hcta`, `hnx`) rewrite `%ctaid`/`%ntid`/`%tid`,
    -- `truncBits_idem` and `trunc_mad` collapse the product's nested truncations to
    -- `(cta * ntid + tid) % 2 ^ 32`, and the `…m` facts are the 32-bit truncations of
    -- its parts, which `omega` cannot derive (the product is nonlinear).
    seg_fp at_init using
      try cd_values
      all_goals seg_close
        [hp, sregValue, truncBits_idem, trunc_mad, Nat.div_add_mod', Dim3.get, hsum, hgm, hbm,
          hcm, htm, hpm, hsm, hnx, htid, hcta, hg, hT, hbl, hN, hrA, hrB]
  rw [hp] at hr
  exact ⟨t, hr, ht⟩

/-- The facts at the branch. -/
theorem factsAt_branch :
    factsAt A B N g 8 .load = [(1, .pred (decide (N ≤ g))), (3, b32 g), (10, b64 A), (11, b64 B)] :=
      by
  have hl : Flow.live 8 = [1, 3, 10, 11] := by decide +kernel
  simp only [factsAt, hl, Flow.factsFrom, List.map_cons, List.map_nil]
  cd_values

set_option maxHeartbeats 4000000 in
/-- **The opening code** reaches the load on a thread `g < N` and the exit elsewhere. -/
theorem start (hpre : Pre L A B N x mem0) (hg : g < L.threads) :
    ∃ t, Relation.ReflTransGen (Tau kernel [] L g) {} t ∧
      At t (code L A B N g).init.pc (facts A B N g (code L A B N g).init) := by
  obtain ⟨t, hr, ht⟩ := seg_branch hpre hg
  rw [factsAt_branch] at ht
  have hrA := hpre.rangeA
  have hrB := hpre.rangeB
  have hT := hpre.threads32
  by_cases hgN : g < N
  · simp only [decide_eq_false (show ¬ N ≤ g by omega)] at ht
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel [] L g 5 t = some t' ∧
        At t' Site.load.pc (facts A B N g .load) := by
      cd_seg ht
    exact ⟨t', run_rtg (run_comp hr hr'), by simpa [code, hgN] using ht'⟩
  · simp only [decide_eq_true (show N ≤ g by omega)] at ht
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel [] L g 1 t = some t' ∧
        At t' Site.exit.pc (facts A B N g .exit) := by
      cd_seg ht
    exact ⟨t', run_rtg (run_comp hr hr'), by simpa [code, hgN] using ht'⟩

/-- The instruction at each site performs an event and has no guard. -/
theorem site_ok (s : Site) : ∃ ins, kernel.code[s.pc]? = some ins ∧ ins.op.isLocal = false ∧
    Code.GuardTrue (facts A B N g s) ins.guard := by
  cases s with
  | load => exact ⟨_, Flow.code_load_0, rfl, trivial⟩
  | store _ => exact ⟨_, Flow.code_store_0, rfl, trivial⟩
  | exit => exact ⟨_, Flow.code_exit_0, rfl, trivial⟩

/-- What a step of the machine owes. -/
abbrev Step (L : Launch) (A B N g : Nat) (s : Site) (u : TState) (e : Event) : Prop :=
  ((code L A B N g).next s e = some none ∨ ∃ d' t', (code L A B N g).next s e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel [] L g) u t' ∧ (code L A B N g).Good (some d') t') ∨
    ((code L A B N g).next s e = none ∧ Machine.Dead (K := kernel) (A := []) (L := L) (g := g) u)

set_option maxHeartbeats 4000000 in
/-- Every site's event reaches its successor's facts. -/
theorem step {s : Site} {t u : TState} {e : Event} {ins : Instr}
    (h : At t s.pc (facts A B N g s)) (hc : kernel.code[s.pc]? = some ins)
    (hf : Fires s.pc (eventTmpl [] L g t ins.op) e (some u)) : Step L A B N g s u e := by
  cases s with
  | load =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
    obtain ⟨a, bs, rfl, rfl⟩ := fires_load rfl rfl hf
    cases hv : rebuild 3 bs with
    | error f =>
      exact .inr ⟨by simp [code, next, hv],
        Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
    | ok v =>
      refine .inl (.inr ?_)
      rw [show MemAccess.regs _ = [8] from rfl, afterLoad_ok h.2.1 h.2.2.1 hv]
      have h1 : At { setReg t 8 v with pc := t.pc + 1, sub := 0, acc := [] }
          (Site.load.pc + 1) ((8, v) :: facts A B N g .load) :=
        ⟨by rw [h.1], rfl, rfl, h.2.2.2.1, by simp [setReg],
          holds_update h.2.2.2.2 (not_mem_factsFrom (by table_decide))⟩
      obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel [] L g 1 _ = some t' ∧
          At t' (Site.store v).pc (facts A B N g (.store v)) := by
        cd_seg h1
      exact ⟨.store v, t', by simp [code, next, hv], run_rtg hr, ht', trivial⟩
  | store v =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_0)
    obtain ⟨a, bs, rfl, rfl⟩ := fires_st rfl hf
    have hl : Flow.live Site.exit.pc = [] := by decide +kernel
    refine .inl
      (.inr ⟨.exit, _, by simp [code, next], .refl, ⟨?_, by simp [afterStore, h.2.1]; rfl, h.2.2.1,
      h.2.2.2.1, ?_⟩, trivial⟩)
    · simp [afterStore, h.2.1, h.1]
      rfl
    · show Holds _ (factsAt A B N g Site.exit.pc .exit)
      simp only [factsAt, hl, Flow.factsFrom, List.map_nil]
      trivial
  | exit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    simp [eventTmpl, Fires] at hf

/-- **Every launched thread is simulated by its code machine.** -/
theorem sound (hpre : Pre L A B N x mem0) (hg : g < L.threads) : (code L A B N g).Sound where
  start := by
    obtain ⟨t, hr, ht⟩ := start hpre hg
    exact ⟨t, hr, ht, trivial⟩
  steps := fun s => ⟨fun _ => site_ok s, fun ins h _ hc hf => step h hc hf⟩

end

end PTX.Kernels.CopyDynamic.Proof
