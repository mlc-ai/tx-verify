-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.CopyLdg.Spec
public import Kernels.CopyLdg.Assumptions
public import Kernels.CopyLdg.Flow.Sites
public import Kernels.CopyLdg.Flow.Code
public import Kernels.CopyLdg.Proof.Support.Addresses
public import Lemmas.Flow.Code
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Next
public import Lemmas.Flow.Async
public import Lemmas.Flow.Local
public import Lemmas.Flow.Final
public import Lemmas.Flow.Scalars
public import Lemmas.Flow.MemTmpl

@[expose] public section

/-! # `copy_ldg`: the site machine of a thread

A thread with `g < N` reads `A[g]` with `ld.global.nc`, stores the word it got to `B[g]` and
exits; every other thread exits at once. The states are the event instructions (`Site`); the
register facts at each are the generated live registers valued by one table (`values`). A
load whose bytes do not rebuild to a value faults the thread, and the machine stops. -/

namespace PTX.Kernels.CopyLdg.Proof
open PTX PTX.Proof PTX.Flow

local notation "Nc" => [Assumptions.ncInput]

noncomputable section

/-- The event instructions of a thread. -/
inductive Site where
  | load
  /-- The store of the word the load returned. -/
  | store (v : Value)
  | exit

def Site.pc : Site → Nat
  | .load => Flow.load_0
  | .store _ => Flow.store_0
  | .exit => Flow.exit_0

/-- The register the load writes and the store reads. -/
abbrev dataReg : Nat := 8

/-- The `nc` read of `A[g]` returning `bs`, the write of `v` to `B[g]`, and the exit. -/
def ncE (A g : Nat) (bs : List (Option Byte)) : Event :=
  ⟨Flow.load_0, .nc { loc := gA A g, size := 4 } bs⟩
def wrE (B g : Nat) (v : Value) : Event :=
  ⟨Flow.store_0, .wr { loc := gB B g, size := 4 } v.toBytes⟩
def exE : Event := ⟨Flow.exit_0, .exit⟩

/-- The `ld.global.nc.f32 %r1, [%rd5]` of the load site. -/
abbrev ldAcc : MemAccess :=
  { kind := .load, space := some .global, sem := .weak, elem := .float .f32, nc := true,
    addr := { base := .reg 12 64 }, dsts := [some 8] }

/-- The `st.global.b32 [%rd7], %r1` of the store site. -/
abbrev stAcc : MemAccess :=
  { kind := .store, space := some .global, sem := .weak, elem := .int .b 32,
    addr := { base := .reg 15 64 }, srcs := [.reg 8] }

/-- The value of every register a thread uses. -/
def values (A B N g : Nat) (s : Site) : List (Nat × Value) :=
  [(10, b64 A), (11, b64 B), (3, b32 g), (1, .pred (decide (N ≤ g))),
   (12, b64 (A + 4 * g)), (13, b64 B), (14, b64 (4 * g)), (15, b64 (B + 4 * g)),
   (8, match s with | .store v => v | _ => b32 0)]

def valueOf (A B N g : Nat) (s : Site) (r : Nat) : Value :=
  ((values A B N g s).lookup r).getD (b32 0)

def factsAt (A B N g pc : Nat) (s : Site) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf A B N g s)

abbrev facts (A B N g : Nat) (s : Site) : List (Nat × Value) :=
  factsAt A B N g s.pc s

/-- The successor after event `e`: the read's word, the store, the exit. A load whose bytes
do not rebuild stops the machine, and so does the exit. -/
def next : Site → Event → Option (Option Site)
  | .load, e => match e.kind with
    | .nc _ bs => match rebuild 3 bs with
      | .ok v => some (some (.store v))
      | .error _ => none
    | _ => none
  | .store _, e => match e.kind with
    | .wr .. => some (some .exit)
    | _ => none
  | .exit, _ => none

/-- The code machine of thread `g`. A thread below `N` runs the copy; a state of the copy
is reached only below `N`. -/
def code (L : Launch) (A B N g : Nat) : Code kernel Nc L g where
  D := Site
  init := if g < N then .load else .exit
  pc := Site.pc
  facts := facts A B N g
  inv := fun s => match s with
    | .exit => True
    | .store v => g < N ∧ v.bytes = 4
    | .load => g < N
  next := next

macro "ldg_values" : tactic =>
  `(tactic| simp only [valueOf, values, List.lookup_cons, Nat.reduceBEq, Option.getD_some,
    PTX.Flow.lookupLit, Option.getD_none])

/-- Evaluate a segment of the thread from `h` and close the facts of its end state. -/
syntax "ldg_seg" term:max term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| ldg_seg $h $hpre $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      have hrA := ($hpre).rangeA
      have hrB := ($hpre).rangeB
      have hN := ($hpre).n32
      seg_fp $h using
        try ldg_values
        all_goals seg_close [$extra,*]))

variable {L : Launch} {A B N : Nat} {x : Nat → Value} {mem0 : Mem0} {g : Nat}

def ps (A B N : Nat) : List (String × Nat) :=
  [("copy_ldg_param_0", A), ("copy_ldg_param_1", B), ("copy_ldg_param_2", N)]

theorem params (hpre : Pre L A B N x mem0) : explicitParams L (ps A B N) = L :=
  explicitParams_eq (by
    intro p v hm
    simp only [ps, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [hpre.param0, hpre.param1, hpre.param2])

/-- Before the `bra`: the registers it and the code after it read. -/
theorem at_branch {t : TState} (h : At t 8 (factsAt A B N g 8 .load)) :
    At t 8 [(1, .pred (decide (N ≤ g))), (3, b32 g), (10, b64 A), (11, b64 B)] := by
  have hl : Flow.live 8 = [1, 3, 10, 11] := by decide +kernel
  have he : factsAt A B N g 8 .load =
      [(1, .pred (decide (N ≤ g))), (3, b32 g), (10, b64 A), (11, b64 B)] := by
    simp only [factsAt, hl, Flow.factsFrom, List.map_cons, List.map_nil]
    ldg_values
  exact he ▸ h

set_option maxHeartbeats 4000000 in
/-- The opening code reaches the load below `N` and the exit elsewhere. -/
theorem start (hpre : Pre L A B N x mem0) (hg : g < L.threads) :
    ∃ t, Relation.ReflTransGen (Tau kernel Nc L g) {} t ∧
      At t (code L A B N g).init.pc (facts A B N g (code L A B N g).init) := by
  have hT := hpre.threads32
  have hbl := hpre.block32
  have hN := hpre.n32
  have hrA := hpre.rangeA
  have hrB := hpre.rangeB
  have hpL := params hpre
  have hone := hpre.oneDimLaunch
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
  obtain ⟨t, hr, ht⟩ : ∃ t, run kernel Nc (explicitParams L (ps A B N)) g 8 {} = some t ∧
      At t 8 (factsAt A B N g 8 .load) := by
    -- The geometry facts (`htid`, `hcta`, `hnx`) rewrite `%ctaid`/`%ntid`/`%tid`,
    -- `truncBits_idem` and `trunc_mad` collapse the product's nested truncations to
    -- `(cta * ntid + tid) % 2 ^ 32`, and the `…m` facts are its parts' 32-bit truncations,
    -- which `omega` cannot derive (the product is nonlinear).
    seg_fp at_init using
      try ldg_values
      all_goals seg_close
        [hpL, sregValue, truncBits_idem, trunc_mad, Nat.div_add_mod', Dim3.get, hsum, hgm, hbm,
          hcm, htm, hpm, hsm, hnx, htid, hcta, hg, hT, hbl, hN, hrA, hrB]
  rw [params hpre] at hr
  have hp := at_branch ht
  by_cases hNg : g < N
  · simp only [show ¬ N ≤ g by omega, decide_false] at hp
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Nc L g 4 t = some t' ∧
        At t' Site.load.pc (facts A B N g .load) := by
      ldg_seg hp hpre
    exact ⟨t', run_rtg (run_comp hr hr'), by simpa [code, hNg] using ht'⟩
  · simp only [show N ≤ g by omega, decide_true] at hp
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Nc L g 1 t = some t' ∧
        At t' Site.exit.pc (facts A B N g .exit) := by
      ldg_seg hp hpre
    exact ⟨t', run_rtg (run_comp hr hr'), by simpa [code, hNg] using ht'⟩

/-- The instruction at each site performs an event and has no guard. -/
theorem site_ok (s : Site) : ∃ ins, kernel.code[s.pc]? = some ins ∧ ins.op.isLocal = false ∧
    Code.GuardTrue (facts A B N g s) ins.guard := by
  cases s with
  | load => exact ⟨_, Flow.code_load_0, rfl, trivial⟩
  | store _ => exact ⟨_, Flow.code_store_0, rfl, trivial⟩
  | exit => exact ⟨_, Flow.code_exit_0, rfl, trivial⟩

theorem reg_at {s : Site} {t : TState} {r : Nat} (h : At t s.pc (facts A B N g s))
    (hl : r ∈ Flow.live s.pc) : t.regs r = some (valueOf A B N g s r) :=
  holds_mem h.2.2.2.2 (Flow.mem_factsFrom hl)

/-- The event template of the load: the `nc` read of `A[g]`. -/
theorem tmpl_load (hpre : Pre L A B N x mem0) (hgN : g < N) {t : TState}
    (h : At t Site.load.pc (facts A B N g .load)) :
    eventTmpl Nc L g t (.mem ldAcc) =
      .readNC { loc := gA A g, size := 4 } (afterLoad t [8]) := by
  have hrA := hpre.rangeA
  have h12 : t.regs 12 = some (b64 (A + 4 * g)) := by
    rw [reg_at h (by table_decide)]; ldg_values
  show memTmpl Nc L g t ldAcc = _
  rw [memTmpl_load rfl rfl rfl rfl (by decide)]
  change loadTmpl Nc L g t .global true 32 [8] 12 0 = _
  rw [loadTmpl_global_nc h.2.1 h12 (by omega) (by decide) (by have := hpre.alignA; omega)
    (by simp [Assumptions.ncInput, Assumption.ncReadOnly, h.1, Site.pc, Flow.load_0])]
  rfl

/-- The event template of the store: the write of the loaded word to `B[g]`. The source is a
four-byte word, so `storeValue` writes it unchanged. -/
theorem tmpl_store (hpre : Pre L A B N x mem0) (hgN : g < N) {v : Value} {t : TState}
    (hv : v.bytes = 4) (h : At t (Site.store v).pc (facts A B N g (.store v))) :
    eventTmpl Nc L g t (.mem stAcc) =
      if v.bytes = 4 then .write { loc := gB B g, size := 4 } v.toBytes (afterStore t [.reg 8])
      else .ub .typeMismatch := by
  have hrB := hpre.rangeB
  have h15 : t.regs 15 = some (b64 (B + 4 * g)) := by
    rw [reg_at h (by table_decide)]; ldg_values
  have h8 : t.regs 8 = some v := by rw [reg_at h (by table_decide)]; ldg_values
  show memTmpl Nc L g t stAcc = _
  rw [memTmpl_store rfl rfl rfl rfl (by decide)]
  change storeTmpl L g t .global 32 15 0 [.reg 8] = _
  rw [storeTmpl_global h.2.1 h15 (by omega) (by decide) (by have := hpre.alignB; omega) h8,
    storeValue_of_bytes (by simpa using hv)]
  simp only [hv, ↓reduceIte]
  rfl

/-- What a firing load does: it reads four bytes of `A[g]`. -/
theorem fires_load (hpre : Pre L A B N x mem0) (hgN : g < N) {t : TState} {e : Event}
    {o : Option TState} (h : At t Site.load.pc (facts A B N g .load))
    (hf : Fires Site.load.pc (eventTmpl Nc L g t (.mem ldAcc)) e o) :
    ∃ bs, bs.length = 4 ∧ e = ncE A g bs ∧ o = some (afterLoad t [8] bs) := by
  rw [tmpl_load hpre hgN h] at hf
  obtain ⟨bs, hl, rfl, rfl⟩ := hf
  exact ⟨bs, hl, rfl, rfl⟩

/-- What a firing store of a four-byte word does: it writes it to `B[g]`. -/
theorem fires_store (hpre : Pre L A B N x mem0) (hgN : g < N) {v : Value} {t : TState}
    {e : Event} {o : Option TState} (hv : v.bytes = 4)
    (h : At t (Site.store v).pc (facts A B N g (.store v)))
    (hf : Fires (Site.store v).pc (eventTmpl Nc L g t (.mem stAcc)) e o) :
    e = wrE B g v ∧ o = some (afterStore t [.reg 8]) := by
  rw [tmpl_store hpre hgN hv h] at hf
  simp only [hv, ↓reduceIte] at hf
  exact hf

set_option maxHeartbeats 4000000 in
/-- Every site's event reaches its successor's facts. -/
theorem step (hpre : Pre L A B N x mem0) {s : Site} {t u : TState} {e : Event} {ins : Instr}
    (hi : (code L A B N g).inv s) (h : At t s.pc (facts A B N g s))
    (hc : kernel.code[s.pc]? = some ins)
    (hf : Fires s.pc (eventTmpl Nc L g t ins.op) e (some u)) :
    ((code L A B N g).next s e = some none ∨ ∃ d' t', (code L A B N g).next s e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel Nc L g) u t' ∧ (code L A B N g).Good (some d')
        t') ∨
    ((code L A B N g).next s e = none ∧ Machine.Dead (K := kernel) (A := Nc) (L := L) (g :=
      g) u) := by
  cases s with
  | load =>
    have hgN : g < N := hi
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
    obtain ⟨bs, hl, rfl, hu⟩ := fires_load hpre hgN h hf
    obtain rfl := Option.some.inj hu
    cases hv : rebuild 3 bs with
    | error f =>
      exact .inr
        ⟨by simp [code, next, ncE, hv], Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
    | ok v =>
      refine .inl (.inr ?_)
      rw [afterLoad_ok h.2.1 h.2.2.1 hv]
      have h1 : At { setReg t 8 v with pc := t.pc + 1, sub := 0, acc := [] }
          (Site.load.pc + 1) ((8, v) :: facts A B N g .load) :=
        ⟨by rw [h.1], rfl, rfl, h.2.2.2.1, by simp [setReg],
          holds_update h.2.2.2.2 (not_mem_factsFrom (by table_decide))⟩
      obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Nc L g 1 _ = some t' ∧
          At t' (Site.store v).pc (facts A B N g (.store v)) := by
        ldg_seg h1 hpre
      exact ⟨.store v, t', by simp [code, next, ncE, hv], run_rtg hr, ht', hgN,
        rebuild_bytes_of_length hv hl⟩
  | store v =>
    obtain ⟨hgN, hbv⟩ := hi
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_0)
    obtain ⟨rfl, hu⟩ := fires_store hpre hgN hbv h hf
    obtain rfl := Option.some.inj hu
    have hl : Flow.live Site.exit.pc = [] := by decide +kernel
    refine .inl
      (.inr ⟨.exit, _, by simp [code, next, wrE], .refl, ⟨?_, by simp [afterStore, h.2.1]; rfl,
      h.2.2.1, h.2.2.2.1, ?_⟩, trivial⟩)
    · simp [afterStore, h.2.1, h.1]
      rfl
    · show Holds _ (factsAt A B N g Site.exit.pc .exit)
      simp only [factsAt, hl, Flow.factsFrom, List.map_nil]
      trivial
  | exit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    simp [eventTmpl, Fires] at hf

/-- Every thread of a launch satisfying the precondition is simulated by its code machine. -/
theorem sound (hpre : Pre L A B N x mem0) (hg : g < L.threads) : (code L A B N g).Sound where
  start := by
    obtain ⟨t, hr, ht⟩ := start hpre hg
    refine ⟨t, hr, ht, ?_⟩
    by_cases hgN : g < N <;> simp [code, hgN]
  steps := fun s => ⟨fun _ => site_ok s, fun ins h hi hc hf => step hpre hi h hc hf⟩

end
end PTX.Kernels.CopyLdg.Proof
