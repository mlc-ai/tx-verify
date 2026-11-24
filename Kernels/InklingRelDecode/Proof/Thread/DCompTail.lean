-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmAll
public import Kernels.InklingRelDecode.Proof.Thread.BrAll
public import Kernels.InklingRelDecode.Proof.Thread.EpiAll

@[expose] public section

/-!
# The softmax region's exit and its obligations, without the composed thread

The parts of the default-partition machine that name only the softmax region, the bridge and the
epilogue: the events that end the loop (`leaves`), the numbers the loop hands the bridge
(`exitIn`), and `SmObligations` with the region's `Code.StepAt` at every site (`smStepAt`). They
are kept apart from `DCompBase` (the composed states, which also name the common start and the
prologue), so that a thread machine glued from other startup and prologue fragments (`Proof2`)
reuses them without importing the old common start.

## `SmObligations`

* `score`: the `Code.StepAt` of `Sm.code` at every site of the score stage (`ScoreSite`). It is
  discharged site by site by the step lemmas of the softmax region's proof (`step_waitLd`,
  `step_shfl5`, ..., `step_stO`); the site's instruction and guard (`Code.StepAt.site`) go with
  them (`SmDischarge.stepAt_score`).
* `exit`: the link from the region's last event to the bridge. After an event that ends the
  loop (`leaves`) the thread runs local steps to pc 2560 with `Sm.factsAt L g 2560 d`, and the
  numbers the bridge reads are in range (`Br.In.Ok`). It is discharged by the runs of `SmExit`
  (`SmDischarge.exit_of_slack`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.DComp
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The assumptions every site machine of the kernel evaluates under. -/
abbrev asms : List Assumption := Assumptions.all

/-- An event that reads a `bf16` number (a bias word the machine follows). -/
def bf16Read : Kind → Prop
  | .rd _ bs => match rebuild 3 bs with
    | .ok x => Sm.isBf16 x = true
    | .error _ => False
  | _ => False

/-- An arrival. -/
def isArrive : Kind → Prop
  | .arrive .. => True
  | _ => False

/-- **Event `e` at `d` ends the loop**: the event leads to the loop test of pc 1049 to 1050 (the
`Sm.afterSetup` of `Sm.next`) and the test finds the loop counter at `num_iters`
(`@%p91 bra 2560`). The four events that lead to the test are the `bar.sync 1` of pc 575 (a lane
whose preloads are masked), the last preload, the `bar.sync` of pc 1012 (a thread other than
thread 0) and the arrival of pc 1013. -/
def leaves (L : Launch) (g : Nat) (d : Sm.D) (e : Event) : Prop :=
  match d.site with
  | .bar0 => Sm.act0 d.e (g % L.block) = false ∧ d.e.r26 = d.i
  | .pre j => j.val + 1 = 64 ∧ bf16Read e.kind ∧ d.e.r26 = d.i
  | .bar21 => g % L.block ≠ 0 ∧ d.e.r26 = d.i + 1
  | .arrive => isArrive e.kind ∧ d.e.r26 = d.i + 1
  | _ => False

/-- **The state the softmax region hands the bridge** (`Br.In`): the 19 registers live at
pc 2560, read off the region's table at `d` (`Sm.valuesS`, `Sm.valuesP`). -/
def exitIn (L : Launch) (g : Nat) (d : Sm.D) : Br.In where
  p3 := decide (g % L.block < 32)
  rv := Sm.rowValid d.e (g % L.block)
  tid := g % L.block
  tm := d.e.tm
  w := g % L.block / 32
  c0 := (d.e.tm + 256) % 2 ^ 32
  mb := (L.sharedBase + 213328) % 2 ^ 32
  a := d.e.ntok
  b := d.e.split
  c := Sm.tokOf (g % L.block)
  dd := d.e.qs
  e := (d.e.kvh + Sm.remOf (g % L.block)) % 2 ^ 32
  d0 := Sm.half (g % L.block) * 64
  ob := d.e.rd75
  lb := d.e.rd76
  l := d.l
  sc := .float .f32 (d.e.sc * log2eF32)
  mx := d.m
  n := d.e.r25


variable {L : Launch} {g : Nat}

/-! ### The obligations -/

/-- The sites of the softmax region's score stage: from the wait for the S-tile load (pc 1298) to
the O rescale's last store, the sites whose step lemmas the region's proof does not have yet. -/
def ScoreSite : Sm.Site → Prop
  | .waitLd | .shfl5 | .shfl6 | .bar22 | .shfl7 | .shfl8 | .shfl9 | .shfl10 | .store10 | .bar23
  | .ldL | .shfl11 | .waitO | .ldO | .waitLdO | .bar24 | .stO => True
  | _ => False

/-- **What the softmax region owes the default-partition thread machine.** -/
structure SmObligations (Q : Params) (L : Launch) (mem0 : Mem0) (g : Nat) : Prop where
  /-- The `Code.StepAt` of the region at every site of the score stage. -/
  score : Pre Q L mem0 → ∀ d : Sm.D, ScoreSite d.site → (Sm.code Sm.asms L g d).StepAt d
  /-- The exit link: after an event that ends the loop the thread reaches pc 2560 with the
  region's facts, and the bridge's numbers are in range. -/
  exit : Pre Q L mem0 → ∀ {d : Sm.D} {e : Event} {t u : TState} {ins : Instr},
    Sm.Inv L g d → (Sm.code Sm.asms L g d).AtD d t → kernel.code[d.site.pc]? = some ins →
    Fires d.site.pc (eventTmpl Sm.asms L g t ins.op) e (some u) → leaves L g d e →
    (exitIn L g d).Ok ∧ ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u t' ∧
      At t' 2560 (Sm.factsAt L g 2560 d)

/-! ### The bridge's input is the region's table -/

/-- **The registers live at pc 2560, in the bridge's table and in the region's.** -/
theorem exitFacts_eq (d : Sm.D) : Br.exitFacts (exitIn L g d) = Sm.factsAt L g 2560 d := by
  unfold Br.exitFacts Br.bfacts Sm.factsAt Flow.factsFrom
  have hl : Flow.live 2560 = [3, 175, 462, 463, 464, 478, 486, 491, 496, 497, 498, 533, 610,
      624, 1914, 1915, 1956, 2023, 2024] := by decide +kernel
  rw [hl]
  rfl

/-! ### The sites the region has step lemmas for -/

theorem valueOf_p173 (d : Sm.D) : Sm.valueOf L g d 172 = .pred true := by
  rw [Sm.valueOf_X d (Or.inl rfl)]
  rfl

theorem valueOf_p178 (d : Sm.D) (hT : g % L.block % 128 = 0) :
    Sm.valueOf L g d 177 = .pred true := by
  sm_vals
  simp [hT]

/-- A `Code.StepAt` of the region from the site's instruction and guard and the step lemma. -/
theorem stepAt_of_step (d : Sm.D)
    (hsite : Sm.Inv L g d → ∃ ins, kernel.code[d.site.pc]? = some ins ∧
      ins.op.isLocal = false ∧ Code.GuardTrue (Sm.facts L g d) ins.guard)
    (hstep : ∀ {t : TState} {e : Event} {u : TState} {ins : Instr}, Sm.Inv L g d →
      At t d.site.pc (Sm.facts L g d) → kernel.code[d.site.pc]? = some ins →
      Fires d.site.pc (eventTmpl Sm.asms L g t ins.op) e (some u) → Sm.Step L g d e u) :
    (Sm.code Sm.asms L g d).StepAt d where
  site := hsite
  step := by
    intro t e u ins h hi hc hf
    rcases hstep hi h hc hf with (hn | ⟨d', t', hn, hr, ha, hi'⟩) | ⟨hn, hd⟩
    · exact .inl (.inl hn)
    · exact .inl (.inr ⟨d', t', hn, hr, ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2⟩, hi'⟩)
    · exact .inr ⟨hn, hd⟩

/-- The instruction at the site's pc, performing an event whose guard is none. -/
theorem site_mk {d : Sm.D} {pc : Nat} {ins : Instr} (hpc : d.site.pc = pc)
    (hc : kernel.code[pc]? = some ins) (hl : ins.op.isLocal = false)
    (hg : Code.GuardTrue (Sm.facts L g d) ins.guard) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (Sm.facts L g d) ins.guard :=
  ⟨ins, hpc ▸ hc, hl, hg⟩

/-- **The softmax region's `Code.StepAt` at every site**: the existing step lemmas, and for the
score stage the obligation. -/
theorem smStepAt {Q : Params} {mem0 : Mem0} (hpre : Pre Q L mem0) (hso : SmObligations Q L mem0 g)
    (d : Sm.D) : (Sm.code Sm.asms L g d).StepAt d := by
  by_cases hsc : ScoreSite d.site
  · exact hso.score hpre d hsc
  cases hs : d.site with
  | setMaxReg =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_setMaxReg_1 rfl trivial)
      fun hi h hc hf => Sm.step_setMaxReg hi hs h hc hf
  | bar0 =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_bar_19 rfl trivial)
      fun hi h hc hf => Sm.step_bar0 hi hs h hc hf
  | pre j =>
    refine stepAt_of_step d (fun hi => Sm.site_ok_pre hi hs) fun hi h hc hf => ?_
    by_cases hj : j.val + 1 < 64
    · exact Sm.step_pre hi hs hj h hc hf
    · exact Sm.step_pre_last hi hs hj h hc hf
  | nxt j =>
    exact stepAt_of_step d (fun hi => Sm.site_ok_nxt hi hs)
      fun hi h hc hf => Sm.step_nxt hi hs h hc hf
  | waitS =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_mbarWait_0 rfl trivial)
      fun hi h hc hf => Sm.step_waitS hi hs h hc hf
  | shfl4 =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_shfl_4 rfl trivial)
      fun hi h hc hf => Sm.step_shfl4 hi hs h hc hf
  | ldS =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_tmemLoad_0 rfl trivial)
      fun hi h hc hf => Sm.step_ldS hi hs h hc hf
  | shfl12 =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_shfl_12 rfl trivial)
      fun hi h hc hf => Sm.step_shfl12 hi hs h hc hf
  | waitStO =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_tmemWait_3 rfl trivial)
      fun hi h hc hf => Sm.step_waitStO hi hs h hc hf
  | bar20 =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_bar_20 rfl trivial)
      fun hi h hc hf => Sm.step_bar20 hi hs h hc hf
  | tmemSt =>
    refine stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_tmemStore_0 rfl ?_)
      fun hi h hc hf => Sm.step_tmemSt hi hs h hc hf
    show (172, Value.pred (!false)) ∈ Sm.factsAt L g d.site.pc d
    have hm := Flow.mem_factsFrom (val := Sm.valueOf L g d)
      (show 172 ∈ Flow.live 1009 by decide +kernel)
    rw [valueOf_p173] at hm
    rw [show d.site.pc = 1009 by rw [hs]; rfl]
    exact hm
  | tmemWait =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_tmemWait_0 rfl trivial)
      fun hi h hc hf => Sm.step_tmemWait hi hs h hc hf
  | bar21 =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_bar_21 rfl trivial)
      fun hi h hc hf => Sm.step_bar21 hi hs h hc hf
  | arrive =>
    refine stepAt_of_step d (fun hi => site_mk (by rw [hs]; rfl) Flow.code_mbarArrive_3 rfl ?_)
      fun hi h hc hf => Sm.step_arrive hi hs h hc hf
    have hT : g % L.block % 128 = 0 := by
      rw [Nat.mod_eq_of_lt hi.tid, hi.lead hs]
    show (177, Value.pred (!false)) ∈ Sm.factsAt L g d.site.pc d
    have hm := Flow.mem_factsFrom (val := Sm.valueOf L g d)
      (show 177 ∈ Flow.live 1013 by decide +kernel)
    rw [valueOf_p178 d hT] at hm
    rw [show d.site.pc = 1013 by rw [hs]; rfl]
    exact hm
  | _ => exact absurd (by rw [hs]; exact trivial) hsc

end
end PTX.Kernels.InklingRelDecode.Proof.DComp
