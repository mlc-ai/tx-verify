-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmaCopy.Spec
public import Kernels.TmaCopy.Flow.Sites
public import Kernels.TmaCopy.Flow.Code
public import Lemmas.Flow.Code
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Next
public import Lemmas.Flow.Async
public import Lemmas.Flow.Local
public import Lemmas.Flow.Final
public import Lemmas.Flow.TmaTmpl

@[expose] public section

/-! # `tma_copy`: the site machine of a thread

Thread 0 initializes the mbarrier, fences, arms it for 16 bytes, issues the bulk copy, polls
until the phase completes, reads the first word of the buffer and stores it to `B`; every
other thread exits. The states are the event instructions (`Site`); the store carries the value
the load's bytes rebuild to, and a load whose bytes rebuild to no value makes the thread fault
(the machine stops). The register facts at each site are the generated live registers valued by
one table (`values`). At each site the instruction's template is fixed (`tmpl_init`, …,
`tmpl_exit`). -/

namespace PTX.Kernels.TmaCopy.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The mbarrier object, `buf`, and the global footprints. -/
def mbar (S : Nat) : Loc := ⟨.shared, 0, S + 16⟩
def buf (S : Nat) : Loc := ⟨.shared, 0, S⟩
def gA (A : Nat) : Loc := ⟨.global, 0, A⟩
def gB (B : Nat) : Loc := ⟨.global, 0, B⟩

/-- The event instructions of a thread. -/
inductive Site where
  | init | fence | arrive | bulk | wait | load
  /-- The store of the word the load returned. -/
  | store (v : Value)
  | exit

def Site.pc : Site → Nat
  | .init => Flow.mbarInit_0 | .fence => Flow.fenceProxy_0 | .arrive => Flow.mbarArrive_0
  | .bulk => Flow.bulkCopy_0 | .wait => Flow.mbarWait_0 | .load => Flow.load_0
  | .store _ => Flow.store_0 | .exit => Flow.exit_0

/-- The value of every register a thread uses. -/
def values (L : Launch) (A B g : Nat) (s : Site) : List (Nat × Value) :=
  [(4, b32 g), (1, .pred (decide (g ≠ 0))), (14, b64 A), (15, b64 B),
   (16, b64 A), (17, b64 B), (5, b32 (L.sharedBase + 16)), (6, b32 L.sharedBase),
   (7, match s with | .store v => v | _ => b32 0)]

def valueOf (L : Launch) (A B g : Nat) (s : Site) (r : Nat) : Value :=
  ((values L A B g s).lookup r).getD (b32 0)

def factsAt (L : Launch) (A B g pc : Nat) (s : Site) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf L A B g s)

abbrev facts (L : Launch) (A B g : Nat) (s : Site) : List (Nat × Value) :=
  factsAt L A B g s.pc s

/-- The successor after event `e`. A load whose bytes do not rebuild faults the thread, and so
does a store of a value that is not one 4-byte word; nothing follows the exit. -/
def next : Site → Event → Option (Option Site)
  | .init, _ => some (some .fence)
  | .fence, _ => some (some .arrive)
  | .arrive, _ => some (some .bulk)
  | .bulk, _ => some (some .wait)
  | .wait, e => match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then .load else .wait))
    | _ => none
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
def code (L : Launch) (A B g : Nat) : Code kernel [] L g where
  D := Site
  init := if g = 0 then .init else .exit
  pc := Site.pc
  facts := facts L A B g
  inv := fun _ => True
  next := next

macro "tma_values" : tactic =>
  `(tactic| simp only [valueOf, values, List.lookup_cons, Nat.reduceBEq, Option.getD_some,
    PTX.Flow.lookupLit, Option.getD_none])

/-- Evaluate a segment of the thread from `h` and close the facts of its end state. -/
syntax "tma_seg" term:max term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| tma_seg $h $hpre $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      have hbase := ($hpre).sharedRange
      seg_fp $h using
        try tma_values
        all_goals seg_close [$extra,*]))

variable {L : Launch} {A B : Nat} {x : Value} {mem0 : Mem0} {g : Nat}

theorem thread_lt_block (hpre : Pre L A B x mem0) (hg : g < L.threads) : g < L.block := by
  have := hpre.grid; unfold Launch.threads at hg; rw [this] at hg; omega

theorem at_init : At ({} : TState) 0 [] := ⟨rfl, rfl, rfl, rfl, by simp [Holds]⟩

def ps (A B : Nat) : List (String × Nat) := [("tma_copy_param_0", A), ("tma_copy_param_1", B)]

theorem params (hpre : Pre L A B x mem0) : explicitParams L (ps A B) = L :=
  explicitParams_eq (by
    intro p v hm
    simp only [ps, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [hpre.param0, hpre.param1])

/-- Before the thread-0 branch: its predicate. -/
theorem at_branch {t : TState} (h : At t 2 (factsAt L A B g 2 .init)) :
    At t 2 [(1, .pred (decide (g ≠ 0)))] := by
  have hl : Flow.live 2 = [1] := by decide +kernel
  have hv : valueOf L A B g .init 1 = .pred (decide (g ≠ 0)) := by tma_values
  have he : factsAt L A B g 2 .init = [(1, .pred (decide (g ≠ 0)))] := by
    simp only [factsAt, hl, Flow.factsFrom, List.map_cons, List.map_nil, hv]
  exact he ▸ h

set_option maxHeartbeats 4000000 in
/-- The opening code reaches the initialization on thread 0 and the exit elsewhere. -/
theorem start (hpre : Pre L A B x mem0) (hg : g < L.threads) :
    ∃ t, Relation.ReflTransGen (Tau kernel [] L g) {} t ∧
      At t (code L A B g).init.pc (facts L A B g (code L A B g).init) := by
  have hgb := thread_lt_block hpre hg
  have hb := hpre.block
  obtain ⟨t, hr, ht⟩ : ∃ t, run kernel [] L g 2 {} = some t ∧
      At t 2 (factsAt L A B g 2 .init) := by
    have htid := Launch.oneDim_tidOf hpre.oneDimLaunch.1 g
    have hg32 : g < 2 ^ 32 := by have := hpre.block.2; omega
    -- `%tid` is the launch's `tidOf`, so the thread-index fact with the block size reduces the
    -- branch predicate to the thread number.
    seg_fp at_init using
      try tma_values
      all_goals
        rw [htid]
        show Value.pred _ = _
        norm_cmp [Dim3.get, Nat.mod_eq_of_lt hgb, truncBits_ofNat hg32 (by decide)]
  have hp := at_branch ht
  by_cases hg0 : g = 0
  · subst hg0
    simp only [ne_eq, not_true_eq_false, decide_false] at hp
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel [] (explicitParams L (ps A B)) 0 7 t = some t' ∧
        At t' Site.init.pc (facts L A B 0 .init) := by
      tma_seg hp hpre [explicitParams]
    rw [params hpre] at hr'
    exact ⟨t', run_rtg (run_comp hr hr'), by simpa [code] using ht'⟩
  · simp only [ne_eq, hg0, not_false_eq_true, decide_true] at hp
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel [] L g 1 t = some t' ∧
        At t' Site.exit.pc (facts L A B g .exit) := by
      tma_seg hp hpre
    exact ⟨t', run_rtg (run_comp hr hr'), by simpa [code, hg0] using ht'⟩

/-- The instruction at each site performs an event and has no guard. -/
theorem site_ok (s : Site) : ∃ ins, kernel.code[s.pc]? = some ins ∧ ins.op.isLocal = false ∧
    Code.GuardTrue (facts L A B g s) ins.guard := by
  cases s with
  | init => exact ⟨_, Flow.code_mbarInit_0, rfl, trivial⟩
  | fence => exact ⟨_, Flow.code_fenceProxy_0, rfl, trivial⟩
  | arrive => exact ⟨_, Flow.code_mbarArrive_0, rfl, trivial⟩
  | bulk => exact ⟨_, Flow.code_bulkCopy_0, rfl, trivial⟩
  | wait => exact ⟨_, Flow.code_mbarWait_0, rfl, trivial⟩
  | load => exact ⟨_, Flow.code_load_0, rfl, trivial⟩
  | store _ => exact ⟨_, Flow.code_store_0, rfl, trivial⟩
  | exit => exact ⟨_, Flow.code_exit_0, rfl, trivial⟩

/-- What a step of the machine owes. -/
abbrev Step (L : Launch) (A B g : Nat) (s : Site) (u : TState) (e : Event) : Prop :=
  ((code L A B g).next s e = some none ∨ ∃ d' t', (code L A B g).next s e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel [] L g) u t' ∧ (code L A B g).Good (some d') t') ∨
    ((code L A B g).next s e = none ∧ Machine.Dead (K := kernel) (A := []) (L := L) (g := g) u)

/-- An advancing event moves to the next site, which is the next instruction. -/
theorem step_adv {s s' : Site} {t u : TState} {e : Event} {ins : Instr}
    (h : At t s.pc (facts L A B g s)) (hadv : AdvancesOp ins.op)
    (hf : Fires s.pc (eventTmpl [] L g t ins.op) e (some u)) (hn : next s e = some (some s'))
    (hseg : ∀ t1, At t1 (s.pc + 1) (facts L A B g s) →
      ∃ t', run kernel [] L g 0 t1 = some t' ∧ At t' s'.pc (facts L A B g s')) :
    Step L A B g s u e := by
  obtain rfl := fires_next hadv hf
  obtain ⟨t', hr, ht'⟩ := hseg _ (At.next h)
  exact .inl (.inr ⟨s', t', hn, run_rtg hr, ht', trivial⟩)

set_option maxHeartbeats 4000000 in
/-- Every site's event reaches its successor's facts. -/
theorem step (hpre : Pre L A B x mem0) {s : Site} {t u : TState} {e : Event} {ins : Instr}
    (h : At t s.pc (facts L A B g s)) (hc : kernel.code[s.pc]? = some ins)
    (hf : Fires s.pc (eventTmpl [] L g t ins.op) e (some u)) : Step L A B g s u e := by
  have hbase := hpre.sharedRange
  cases s with
  | init =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarInit_0)
    exact step_adv h (by exact trivial) hf rfl fun t1 h1 => by tma_seg h1 hpre
  | fence =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_0)
    exact step_adv h (by exact trivial) hf rfl fun t1 h1 => by tma_seg h1 hpre
  | arrive =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_0)
    exact step_adv h (by exact trivial) hf rfl fun t1 h1 => by tma_seg h1 hpre
  | bulk =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bulkCopy_0)
    exact step_adv h (by rfl) hf rfl fun t1 h1 => by tma_seg h1 hpre
  | wait =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_0)
    rw [← h.1] at hf
    obtain ⟨m, par, ok, sc, rfl, rfl⟩ := fires_wait hf
    have h1 := At.set (r := 2) (v := .pred ok) h
      (not_mem_factsFrom (by table_decide))
    refine .inl (.inr ?_)
    cases ok
    · obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel [] L g 1 _ = some t' ∧
          At t' Site.wait.pc (facts L A B g .wait) := by tma_seg h1 hpre
      exact ⟨.wait, t', rfl, run_rtg hr, ht', trivial⟩
    · obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel [] L g 1 _ = some t' ∧
          At t' Site.load.pc (facts L A B g .load) := by tma_seg h1 hpre
      exact ⟨.load, t', rfl, run_rtg hr, ht', trivial⟩
  | load =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
    obtain ⟨a, bs, rfl, rfl⟩ := fires_load rfl rfl hf
    cases hv : rebuild 3 bs with
    | error f =>
      exact .inr ⟨by simp [code, next, hv],
        Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
    | ok v =>
      refine .inl (.inr ?_)
      rw [show MemAccess.regs _ = [7] from rfl, afterLoad_ok h.2.1 h.2.2.1 hv]
      have h1 : At { setReg t 7 v with pc := t.pc + 1, sub := 0, acc := [] }
          (Site.load.pc + 1) ((7, v) :: facts L A B g .load) :=
        ⟨by rw [h.1], rfl, rfl, h.2.2.2.1, by simp [setReg],
          holds_update h.2.2.2.2 (not_mem_factsFrom (by table_decide))⟩
      obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel [] L g 0 _ = some t' ∧
          At t' (Site.store v).pc (facts L A B g (.store v)) := by tma_seg h1 hpre
      exact ⟨.store v, t', by simp [code, next, hv], run_rtg hr, ht', trivial⟩
  | store v =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_0)
    obtain ⟨a, bs, rfl, rfl⟩ := fires_st rfl hf
    have hl : Flow.live Site.exit.pc = [] := by decide +kernel
    refine .inl (.inr ⟨.exit, _, by simp [code, next], .refl,
      ⟨?_, by simp [afterStore, h.2.1]; rfl, h.2.2.1,
      h.2.2.2.1, ?_⟩, trivial⟩)
    · simp [afterStore, h.2.1, h.1]
      rfl
    · show Holds _ (factsAt L A B g Site.exit.pc .exit)
      simp only [factsAt, hl, Flow.factsFrom, List.map_nil]
      trivial
  | exit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    simp [eventTmpl, Fires] at hf

/-- Every thread of a launch satisfying the precondition is simulated by its code machine. -/
theorem sound (hpre : Pre L A B x mem0) (hg : g < L.threads) : (code L A B g).Sound where
  start := by
    obtain ⟨t, hr, ht⟩ := start hpre hg
    exact ⟨t, hr, ht, trivial⟩
  steps := fun s => ⟨fun _ => site_ok s, fun ins h _ hc hf => step hpre h hc hf⟩

theorem reg_at {s : Site} {t : TState} {r : Nat} (h : At t s.pc (facts L A B g s))
    (hl : r ∈ Flow.live s.pc) : t.regs r = some (valueOf L A B g s r) :=
  holds_mem h.2.2.2.2 (Flow.mem_factsFrom hl)

section
variable {t : TState} (hpre : Pre L A B x mem0)
include hpre

omit hpre in
theorem r2_of {s : Site} (h : At t s.pc (facts L A B 0 s)) (hl : 5 ∈ Flow.live s.pc) :
    t.regs 5 = some (b32 (L.sharedBase + 16)) := by
  rw [reg_at h hl]; cases s <;> tma_values

theorem tmpl_init (h : At t Site.init.pc (facts L A B 0 .init)) :
    (code L A B 0).tmpl (some .init) t = .mbInit (mbar L.sharedBase) 1 (PTX.next t) := by
  have hS := hpre.sharedRange
  simp only [Code.tmpl, code, Site.pc, Flow.code_mbarInit_0, eventTmpl]
  rw [show Op.mbarInit 5 0 (.imm 1) = .mbarInit 5 0 (.imm ((1 : Nat) : Int)) from rfl]
  rw [show ∀ p m, widenMbarScope [] p m = m from fun _ _ => rfl, tma_mbarInit (r2_of h
    (by table_decide)) (by omega) (by have := hpre.sharedAlign; omega) (by decide) (by decide),
    Nat.zero_div]
  rfl

omit hpre in
theorem tmpl_fence :
    (code L A B 0).tmpl (some .fence) t =
      .fenceProxy (.async (some (.shared .cta))) none (PTX.next t) := by
  simp only [Code.tmpl, code, Site.pc, Flow.code_fenceProxy_0, eventTmpl]
  rfl

theorem tmpl_arrive (h : At t Site.arrive.pc (facts L A B 0 .arrive)) :
    (code L A B 0).tmpl (some .arrive) t = .arrive (mbar L.sharedBase) 16 (PTX.next t) := by
  have hS := hpre.sharedRange
  simp only [Code.tmpl, code, Site.pc, Flow.code_mbarArrive_0, eventTmpl]
  rw [show Op.mbarArrive 5 0 (.imm 16) = .mbarArrive 5 0 (.imm ((16 : Nat) : Int))
    from rfl]
  rw [show ∀ p m, widenMbarScope [] p m = m from fun _ _ => rfl, tma_arrive (r2_of h
    (by table_decide)) (by omega) (by have := hpre.sharedAlign; omega) (by decide), Nat.zero_div]
  rfl

theorem tmpl_bulk (h : At t Site.bulk.pc (facts L A B 0 .bulk)) :
    (code L A B 0).tmpl (some .bulk) t =
      .copy (bulkSpec { loc := gA A, size := 16 } { loc := buf L.sharedBase, size := 16 }
        (.mbarrier (mbar L.sharedBase)) .whole none) (PTX.next t) := by
  have hS := hpre.sharedRange
  have hS16 := hpre.sharedAlign
  have h3 : t.regs 6 = some (b32 L.sharedBase) := by
    rw [reg_at h (by table_decide)]; tma_values
  have hd3 : t.regs 16 = some (b64 A) := by rw [reg_at h (by table_decide)]; tma_values
  simp only [Code.tmpl, code, Site.pc, Flow.code_bulkCopy_0, eventTmpl]
  rw [show Op.cpBulk (BulkCopy.mk .globalToCta 6 0 16 0 (.imm 16) (some (5, 0)) none none
    none none none none) = Op.cpBulk (BulkCopy.mk .globalToCta 6 0 16 0
    (.imm ((16 : Nat) : Int)) (some (5, 0)) none none none none none none) from rfl]
  rw [show ∀ p m, widenMbarScope [] p m = m from fun _ _ => rfl, tma_cpBulk h3 (by omega) hd3
    (by have := hpre.rangeA; omega) (r2_of h (by table_decide)) (by omega) (by omega)
    (by decide) (by decide) (by decide) hS16 hpre.alignA
    (by simp only [bulkRangeOk, bulkSpaceEnd]; have := hpre.rangeA; omega), Nat.zero_div]
  rfl

theorem tmpl_wait (h : At t Site.wait.pc (facts L A B 0 .wait)) :
    (code L A B 0).tmpl (some .wait) t =
      .wait (mbar L.sharedBase) 0 (fun ok => PTX.next (setReg t 2 (.pred ok))) := by
  have hS := hpre.sharedRange
  simp only [Code.tmpl, code, Site.pc, Flow.code_mbarWait_0, eventTmpl]
  rw [show ∀ p m, widenMbarScope [] p m = m from fun _ _ => rfl, tma_tryWait (r2_of h
    (by table_decide)) (by omega) (by have := hpre.sharedAlign; omega), Nat.zero_div]
  rfl

theorem tmpl_load (h : At t Site.load.pc (facts L A B 0 .load)) :
    (code L A B 0).tmpl (some .load) t =
      .read { loc := buf L.sharedBase, size := 4 } (afterLoad t [7]) := by
  have hS := hpre.sharedRange
  have h3 : t.regs 6 = some (b32 L.sharedBase) := by
    rw [reg_at h (by table_decide)]; tma_values
  simp only [Code.tmpl, code, Site.pc, Flow.code_load_0, eventTmpl]
  rw [memTmpl_load rfl rfl rfl rfl (by decide)]
  change loadTmpl [] L 0 t .shared false 32 [7] 6 0 = _
  rw [loadTmpl_shared h.2.1 h3 (by omega) (by decide) (by have := hpre.sharedAlign; omega),
    Nat.zero_div]
  rfl

theorem tmpl_store {v : Value} (h : At t (Site.store v).pc (facts L A B 0 (.store v))) :
    (code L A B 0).tmpl (some (.store v)) t =
      match storeValue 32 v with
      | .error f => .ub f
      | .ok v' => .write { loc := gB B, size := 4 } v'.toBytes (afterStore t [.reg 7]) := by
  have hd4 : t.regs 17 = some (b64 B) := by rw [reg_at h (by table_decide)]; tma_values
  have h4 : t.regs 7 = some v := by rw [reg_at h (by table_decide)]; tma_values
  simp only [Code.tmpl, code, Site.pc, Flow.code_store_0, eventTmpl]
  rw [memTmpl_store rfl rfl rfl rfl (by decide)]
  change storeTmpl L 0 t .global 32 17 0 [.reg 7] = _
  rw [storeTmpl_global h.2.1 hd4 (by have := hpre.rangeB; omega) (by decide)
    (by have := hpre.alignB; omega) h4]
  rfl

end

theorem tmpl_exit {t : TState} : (code L A B g).tmpl (some .exit) t = .exit := by
  simp only [Code.tmpl, code, Site.pc, Flow.code_exit_0, eventTmpl]

end

end PTX.Kernels.TmaCopy.Proof
