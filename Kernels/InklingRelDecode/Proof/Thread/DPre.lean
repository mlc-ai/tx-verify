-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DStartAll
public import Lemmas.Flow.NotShfl
public import Lemmas.Flow.NotClc

@[expose] public section

/-!
# The common start up to the broadcast, for any base word

`DPre.code` follows a default-partition thread (warps 0 to 3) from its first event to its first
shuffle, the broadcast of the warp index (pc 17), for every value the load of the base word
(pc 13) returns. It is the common start's machine `DStart.code` without the register `%r2`: the
code from pc 14 to 17 does not read `%r2`, so the machine need not know the loaded word. At the
broadcast it stops following the thread (`some none`); a load whose bytes rebuild to no value
faults the thread (`none`).

It is not the machine of any thread of the proof (that is `DComp.code`, whose common start stops
following a thread whose base word has no room for the 512 columns). It is used only to show that
lane 0 of a warp of the default partition, whatever word it loaded, makes the broadcast as its
first shuffle and with its warp index as operand, and does not exit before it
(`Interface.dpre_first_shfl`, `dpre_not_exited0`).

* `DPre.pre_fires`: the events of the sites other than the broadcast are neither shuffles nor
  exits;
* `DPre.shfl_fires`: the event of the broadcast is a full-warp `shfl.sync.idx` whose operand is
  the thread's warp index;
* `DPre.sound`: the machine is sound.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.DPre
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.DStart (Site D AtS Inv valueOf factsAt table asms)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

variable {L : Launch} {g : Nat} {Q : Params} {d : D} {t u : TState} {e : Event} {ins : Instr}

/-- The registers live at `pc` other than `%r2`, with the common start's values. -/
def factsP (L : Launch) (g : Nat) (Q : Params) (pc : Nat) : List (Nat × Value) :=
  Flow.factsFrom ((Flow.live pc).filter (· ≠ 463)) (valueOf L g Q (b32 0))

/-- The invariant: the common start's, with the base word 0 (the machine does not record it). -/
def PInv (L : Launch) (g : Nat) (Q : Params) (d : D) : Prop := Inv L g Q ⟨d.site, b32 0⟩

/-- The abstract successor: the common start's, except that every loaded base word is followed
(and forgotten) and the broadcast stops the machine. -/
def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .ld0 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok _ => some (some ⟨.bar1, b32 0⟩)
      | .error _ => none
    | _ => none
  | .shfl => some none
  | .toProA => some none
  | _ => DStart.next L g ⟨d.site, b32 0⟩ e

/-- The common start up to the broadcast as a code machine. -/
@[reducible] def code (L : Launch) (g : Nat) (Q : Params) : Flow.Code kernel asms L g where
  D := D
  init := DStart.D.start L g
  pc := (·.site.pc)
  facts := fun d => factsP L g Q d.site.pc
  sub := (·.site.sub)
  inv := PInv L g Q
  next := next L g

theorem factsP_sub {pc : Nat} : ∀ r ∈ (Flow.live pc).filter (· ≠ 463), r ∈ Flow.live pc := by
  intro r hr
  exact (List.mem_filter.mp hr).1

/-- The common start's facts at base word 0 give the machine's. -/
theorem holds_of_full {pc : Nat} (h : Holds t.regs (factsAt L g Q (b32 0) pc)) :
    Holds t.regs (factsP L g Q pc) :=
  holds_factsFrom_mono h factsP_sub

/-- Before the load the two machines' facts are the same (`%r2` is not live). -/
theorem full_of_pre {pc : Nat} (hl : 463 ∉ Flow.live pc) (h : Holds t.regs (factsP L g Q pc)) :
    Holds t.regs (factsAt L g Q (b32 0) pc) := by
  refine holds_factsFrom_mono h ?_
  intro r hr
  exact List.mem_filter.mpr ⟨hr, by simp only [ne_eq, decide_eq_true_eq]; rintro rfl; exact hl hr⟩

/-- The conclusion of a step of the machine. -/
def PStep (L : Launch) (g : Nat) (Q : Params) (d : D) (e : Event) (u : TState) : Prop :=
  (next L g d e = some none ∨
    ∃ d' t', next L g d e = some (some d') ∧ Relation.ReflTransGen (Tau kernel asms L g) u t' ∧
      (code L g Q).Good (some d') t') ∨
  (next L g d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u)

/-- A step of the common start before the load is one of this machine. -/
theorem pstep_of_step {s : Site} (hs : s = .alloc ∨ s = .allocWr ∨ s = .bar0)
    (h : DStart.Step L g Q ⟨s, b32 0⟩ e u) : PStep L g Q ⟨s, b32 0⟩ e u := by
  have hn : next L g ⟨s, b32 0⟩ e = DStart.next L g ⟨s, b32 0⟩ e := by
    rcases hs with rfl | rfl | rfl <;> rfl
  rcases h with (h | ⟨d', t', h1, h2, h3, h4⟩) | ⟨h1, h2⟩
  · exact Or.inl (Or.inl (hn ▸ h))
  · have htm : d'.w = b32 0 := by
      rcases hs with rfl | rfl | rfl <;> simp only [DStart.next] at h1 <;>
        (try split at h1) <;> simp only [Option.some.injEq] at h1 <;> subst h1 <;> rfl
    obtain ⟨s', tm'⟩ := d'
    simp only at htm
    subst htm
    exact Or.inl (Or.inr ⟨⟨s', b32 0⟩, t', hn ▸ h1, h2,
      ⟨⟨h3.1, h3.2.1, h3.2.2.1, h3.2.2.2.1, holds_of_full h3.2.2.2.2⟩, h4⟩⟩)
  · exact Or.inr ⟨hn ▸ h1, h2⟩

/-- `shr.u32 %r3, %r1, 5` (pc 16) without `%r2`. -/
theorem seg_shr (ha : ProA.ArgsOk L g (DStart.inh L g Q (ProA.shW (b32 0)))) :
    Seg kernel asms L g 1 16 (factsP L g Q 16) 17 (factsP L g Q 17) := by
  intro t h
  have h128 : g % L.block < 128 := ha.tid
  unfold factsP at h ⊢
  seg_fp h using
    try simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some, DStart.warpOf]
    all_goals seg_close [DStart.warpOf]

/-- The machine's concrete state of `d`. -/
def PAt (L : Launch) (g : Nat) (Q : Params) (d : D) (t : TState) : Prop :=
  t.pc = d.site.pc ∧ t.sub = d.site.sub ∧ t.acc = [] ∧ t.fault = none ∧
    Holds t.regs (factsP L g Q d.site.pc)

theorem pat_iff {d : D} {t : TState} : (code L g Q).AtD d t ↔ PAt L g Q d t := Iff.rfl

/-- The common start's concrete state at base word 0 before the load is the machine's, and
conversely. -/
theorem ats_of_pat {s : Site} (hs : s = .alloc ∨ s = .allocWr ∨ s = .bar0 ∨ s = .ld0)
    (h : PAt L g Q ⟨s, b32 0⟩ t) : AtS L g Q ⟨s, b32 0⟩ t := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, full_of_pre ?_ h.2.2.2.2⟩
  rcases hs with rfl | rfl | rfl | rfl <;> decide +kernel

/-- **The load of the base word**: every rebuilt value is followed to the second barrier. -/
theorem step_ld0 (hi : PInv L g Q ⟨.ld0, tm⟩) (h : PAt L g Q ⟨.ld0, tm⟩ t)
    (hc : kernel.code[(Site.ld0).pc]? = some ins)
    (hf : Fires (Site.ld0).pc (eventTmpl asms L g t ins.op) e (some u)) :
    PStep L g Q ⟨.ld0, tm⟩ e u := by
  obtain ⟨a, ha1, ha2, ha3, ha4, ha5⟩ : ∃ a : MemAccess, kernel.code[13]? = some ⟨none, .mem a⟩ ∧
      a.kind = .load ∧ a.nc = false ∧ a.ext = .same ∧ a.regs = [463] :=
    ⟨_, Flow.code_13, rfl, rfl, rfl, rfl⟩
  obtain rfl := Option.some.inj (hc.symm.trans ha1)
  obtain ⟨r, bs, rfl, rfl⟩ := fires_load ha2 ha3 hf ha4
  cases hv : rebuild 3 bs with
  | error f =>
    exact Or.inr ⟨by simp [next, hv], Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
  | ok v =>
    rw [ha5, afterLoad_ok h.2.1 h.2.2.1 hv]
    refine Or.inl (Or.inr ⟨⟨.bar1, b32 0⟩, _, by simp [next, hv], .refl, ?_, ?_⟩)
    · refine ⟨by simp [h.1, DStart.Site.pc], rfl, rfl, h.2.2.2.1, holds_of_pointwise fun r hr => ?_⟩
      obtain ⟨hr14, hr4⟩ := List.mem_filter.mp hr
      have hr4' : r ≠ 463 := by simpa using hr4
      have hl : r ∈ Flow.live 13 := by
        have : ∀ r ∈ Flow.live 14, r = 463 ∨ r ∈ Flow.live 13 := by decide +kernel
        exact (this r hr14).resolve_left hr4'
      have hm : r ∈ (Flow.live 13).filter (· ≠ 463) :=
        List.mem_filter.mpr ⟨hl, by simpa using hr4'⟩
      have h1 := holds_mem h.2.2.2.2 (Flow.mem_factsFrom hm)
      simp only [setReg, Function.update_of_ne hr4']
      exact h1
    · exact ⟨hi.args, by simp⟩

/-- The register `%p3` of a thread outside warp 0 is false. -/
theorem p3_false (hl : ¬ g % L.block < 32) : (3, Value.pred false) ∈ factsP L g Q 14 := by
  have hm : (3 : Nat) ∈ (Flow.live 14).filter (· ≠ 463) := by decide +kernel
  have := Flow.mem_factsFrom (val := valueOf L g Q (b32 0)) hm
  have hv : valueOf L g Q (b32 0) 3 = Value.pred false := by simp [valueOf, table, hl]
  rw [hv] at this
  exact this

/-- **The second barrier**: warp 0 goes on to the relinquishment, the other warps skip it and
run `shr.u32` to the broadcast. -/
theorem step_bar1 (hi : PInv L g Q ⟨.bar1, tm⟩) (h : PAt L g Q ⟨.bar1, tm⟩ t)
    (hc : kernel.code[(Site.bar1).pc]? = some ins)
    (hf : Fires (Site.bar1).pc (eventTmpl asms L g t ins.op) e (some u)) :
    PStep L g Q ⟨.bar1, tm⟩ e u := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_1)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSync _ _) from trivial) hf
  have h0 : At t 14 (factsP L g Q 14) := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  by_cases hl : g % L.block < 32
  · refine Or.inl (Or.inr ⟨⟨.relinq, b32 0⟩, _, by simp [next, DStart.next, hl], .refl, ?_, ?_⟩)
    · have := (At.next h0)
      refine ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1,
        holds_factsFrom_mono this.2.2.2.2 ?_⟩
      intro r hr
      obtain ⟨hr1, hr2⟩ := List.mem_filter.mp hr
      refine List.mem_filter.mpr ⟨?_, hr2⟩
      revert r
      decide +kernel
    · exact ⟨hi.args, fun _ => hl⟩
  · have hA : Seg kernel asms L g 1 15 (factsP L g Q 14) 16 (factsP L g Q 14) :=
      Seg.skip Flow.code_15 (p3_false hl) (by simp)
    have hB := seg_shr (L := L) (g := g) (Q := Q) hi.args
    have hC : Seg kernel asms L g 1 16 (factsP L g Q 14) 17 (factsP L g Q 17) :=
      hB.weaken_start fun _ hR => holds_factsFrom_mono hR (by decide +kernel)
    obtain ⟨t', hr, ht'⟩ := (Seg.comp hA hC) (PTX.next t) (At.next h0)
    exact Or.inl (Or.inr ⟨⟨.shfl, b32 0⟩, t', by simp [next, DStart.next, hl], run_rtg hr,
      ⟨ht'.1, ht'.2.1, ht'.2.2.1, ht'.2.2.2.1, ht'.2.2.2.2⟩,
      ⟨hi.args, by simp⟩⟩)

/-- **The relinquishment** (warp 0), then `shr.u32` to the broadcast. -/
theorem step_relinq (hi : PInv L g Q ⟨.relinq, tm⟩) (h : PAt L g Q ⟨.relinq, tm⟩ t)
    (hc : kernel.code[(Site.relinq).pc]? = some ins)
    (hf : Fires (Site.relinq).pc (eventTmpl asms L g t ins.op) e (some u)) :
    PStep L g Q ⟨.relinq, tm⟩ e u := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemRelinquish_0)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.tcRelinquish _) from trivial) hf
  have h0 : At t 15 (factsP L g Q 15) := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  have hB := seg_shr (L := L) (g := g) (Q := Q) hi.args
  have hC : Seg kernel asms L g 1 16 (factsP L g Q 15) 17 (factsP L g Q 17) :=
    hB.weaken_start fun _ hR => holds_factsFrom_mono hR (by decide +kernel)
  obtain ⟨t', hr, ht'⟩ := hC (PTX.next t) (At.next h0)
  exact Or.inl (Or.inr ⟨⟨.shfl, b32 0⟩, t', by simp [next, DStart.next], run_rtg hr,
    ⟨ht'.1, ht'.2.1, ht'.2.2.1, ht'.2.2.2.1, ht'.2.2.2.2⟩,
    ⟨hi.args, by simp⟩⟩)

/-- Every site is an event instruction whose guard holds by its facts. -/
theorem site_ok (hi : PInv L g Q d) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (factsP L g Q d.site.pc) ins.guard := by
  obtain ⟨ins, hc, hl, hg⟩ := DStart.site_ok hi
  refine ⟨ins, hc, hl, ?_⟩
  cases hgd : ins.guard with
  | none => trivial
  | some pn =>
    rw [hgd] at hg
    obtain ⟨p, neg⟩ := pn
    simp only [Code.GuardTrue] at hg ⊢
    simp only [DStart.facts, factsAt, Flow.factsFrom, List.mem_map, Prod.mk.injEq] at hg
    obtain ⟨r, hr, rfl, hv⟩ := hg
    have hne : r ≠ 463 := by
      rintro rfl
      simp [valueOf, table, b32, PTX.Flow.lookupLit] at hv
    have hm := Flow.mem_factsFrom (val := valueOf L g Q (b32 0))
      (live := (Flow.live d.site.pc).filter (· ≠ 463))
      (List.mem_filter.mpr ⟨hr, decide_eq_true hne⟩)
    rw [hv] at hm
    exact hm

theorem next_tm (s : Site) (tm : Value) (e : Event) :
    next L g ⟨s, tm⟩ e = next L g ⟨s, b32 0⟩ e := by
  cases s <;> rfl

/-- Every event fired at a state steps to its successor. -/
theorem step (hi : PInv L g Q d) (h : PAt L g Q d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : PStep L g Q d e u := by
  obtain ⟨s, tm⟩ := d
  have hn := next_tm (L := L) (g := g) s tm e
  have hpre : ∀ (hs : s = .alloc ∨ s = .allocWr ∨ s = .bar0),
      DStart.Step L g Q ⟨s, b32 0⟩ e u → PStep L g Q ⟨s, tm⟩ e u := by
    intro hs hst
    have := pstep_of_step hs hst
    unfold PStep at this ⊢
    rw [hn]
    exact this
  have hat : ∀ (hs : s = .alloc ∨ s = .allocWr ∨ s = .bar0 ∨ s = .ld0), AtS L g Q ⟨s, b32 0⟩ t :=
    fun hs => ats_of_pat hs ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  cases s
  · exact hpre (.inl rfl) (DStart.step_alloc rfl hi (hat (.inl rfl)) hc hf)
  · exact hpre (.inr (.inl rfl)) (DStart.step_allocWr rfl hi (hat (.inr (.inl rfl))) hc hf)
  · exact hpre (.inr (.inr rfl)) (DStart.step_bar0 rfl hi (hat (.inr (.inr (.inl rfl)))) hc hf)
  · exact step_ld0 hi h hc hf
  · exact step_bar1 hi h hc hf
  · exact step_relinq hi h hc hf
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inl rfl)

/-- Every state satisfies the code machine's obligation. -/
theorem stepAt (d : D) : (code L g Q).StepAt d where
  site hi := site_ok hi
  step := by
    intro t e u ins h hi hc hf
    exact step hi h hc hf

/-- **The machine is sound** for every thread of the default partition. -/
theorem sound {mem0 : Mem0} (hpre : Pre Q L mem0) (hg : g < L.threads) (hw : g % L.block < 128) :
    (code L g Q).Sound where
  start := by
    obtain ⟨t, hr, ht, hi⟩ := DStart.start hpre hg hw
    have h0 : (DStart.D.start L g).w = b32 0 := by unfold DStart.D.start; split <;> rfl
    refine ⟨t, hr, ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ?_⟩, ?_⟩
    · have := ht.2.2.2.2
      unfold DStart.facts at this
      rw [h0] at this
      exact holds_of_full this
    · show Inv L g Q ⟨(DStart.D.start L g).site, b32 0⟩
      rw [← h0]
      exact hi
  steps := stepAt

/-- **The events of the sites other than the broadcast are neither shuffles nor exits.** -/
theorem pre_fires {s : Site} (hs : s ≠ .shfl) {t : TState} {e : Event} {o : Option TState}
    (hc : kernel.code[s.pc]? = some ins)
    (hf : Fires s.pc (eventTmpl asms L g t ins.op) e o) :
    Execution.isShfl e = false ∧ e.kind ≠ .exit := by
  have hop : ins.op.isShfl = false ∧ ins.op ≠ .ret ∧ ins.op ≠ .exit := by
    cases s <;> simp only [DStart.Site.pc, ne_eq, not_true_eq_false] at hc hs
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
      exact ⟨rfl, by simp, by simp⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
      exact ⟨rfl, by simp, by simp⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_0)
      exact ⟨rfl, by simp, by simp⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
      exact ⟨rfl, by simp, by simp⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_1)
      exact ⟨rfl, by simp, by simp⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemRelinquish_0)
      exact ⟨rfl, by simp, by simp⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_0)
      exact ⟨rfl, by simp, by simp⟩
  refine ⟨?_, ?_⟩
  · cases hs' : Execution.isShfl e
    · rfl
    · have := fires_shfl_op hf hs'
      rw [hop.1] at this
      cases this
  · intro hk
    rcases fires_exit_op hf hk with h | h
    · exact hop.2.1 h
    · exact hop.2.2 h

/-- **The broadcast of the warp index**: a full-warp `shfl.sync.idx` from lane 0 whose operand is
the thread's warp index. -/
theorem shfl_fires {tm : Value} (h : PAt L g Q ⟨.shfl, tm⟩ t)
    (hc : kernel.code[(Site.shfl).pc]? = some ins)
    (hf : Fires (Site.shfl).pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ recv ok, e = ⟨(Site.shfl).pc, .shfl .idx (b32 (g % L.block / 32)) 0 31 recv ok⟩ := by
  have hpc : (Site.shfl).pc = 17 := rfl
  have hr : t.regs 464 = some (b32 (g % L.block / 32)) := by
    have hm : (464 : Nat) ∈ (Flow.live 17).filter (· ≠ 463) := by decide +kernel
    have := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g Q (b32 0)) hm)
    rw [this]
    rfl
  rw [hpc] at hc hf ⊢
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0)
  obtain ⟨av, bv, cv, recv, ok, he, -⟩ := fires_shfl (p := none) hf
  have hsh : Execution.isShfl e = true := by rw [he]; rfl
  exact fires_shfl_idx (p := none) hr hf hsh

/-- **The broadcast's shuffle event**, for any continuation: its operand is the warp index. -/
theorem shfl_fires_any {tm : Value} {o : Option TState} (h : PAt L g Q ⟨.shfl, tm⟩ t)
    (hc : kernel.code[(Site.shfl).pc]? = some ins)
    (hf : Fires (Site.shfl).pc (eventTmpl asms L g t ins.op) e o)
    (hsh : Execution.isShfl e = true) :
    ∃ recv ok, e = ⟨(Site.shfl).pc, .shfl .idx (b32 (g % L.block / 32)) 0 31 recv ok⟩ := by
  have hpc : (Site.shfl).pc = 17 := rfl
  have hr : t.regs 464 = some (b32 (g % L.block / 32)) := by
    have hm : (464 : Nat) ∈ (Flow.live 17).filter (· ≠ 463) := by decide +kernel
    have := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g Q (b32 0)) hm)
    rw [this]
    rfl
  rw [hpc] at hc hf ⊢
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0)
  exact fires_shfl_idx (p := none) hr hf hsh

/-- The broadcast's event is no exit. -/
theorem shfl_not_exit {o : Option TState} (hc : kernel.code[(Site.shfl).pc]? = some ins)
    (hf : Fires (Site.shfl).pc (eventTmpl asms L g t ins.op) e o) : e.kind ≠ .exit := by
  intro hk
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0)
  rcases fires_exit_op hf hk with h1 | h1 <;> cases h1

/-- A successor of the machine is never the hand-off site, and is never from the broadcast. -/
theorem next_site {d d' : D} {e : Event} (h : next L g d e = some (some d')) :
    d'.site ≠ .toProA ∧ d.site ≠ .shfl := by
  obtain ⟨s, tm⟩ := d
  obtain ⟨pc, k⟩ := e
  cases s <;> simp only [next, DStart.next] at h <;> (repeat' split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> simp

/-- Only the broadcast and the hand-off stop the machine. -/
theorem stop_site {d : D} {e : Event} (h : next L g d e = some none) :
    d.site = .shfl ∨ d.site = .toProA := by
  obtain ⟨s, tm⟩ := d
  obtain ⟨pc, k⟩ := e
  cases s <;> simp only [next, DStart.next] at h <;> (try simp) <;>
    (repeat' split at h) <;> simp_all

end
end PTX.Kernels.InklingRelDecode.Proof.DPre
