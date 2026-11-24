-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Isa.Tmpl
public import Kernels.Fp16Gemm8192.Proof.Thread.Mma
public import Kernels.Fp16Gemm8192.Proof.Thread.Cluster
public import Lemmas.Flow.Local
public import Lemmas.Flow.Tc
public import Lemmas.Flow.Pointer
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Definitions and helper facts of `MmaSteps`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Mma
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000

/-- The continuation of a step of this role: the thread leaves the role, or steps to `d'` at
`t'` by a run of `Tau` (the conclusion of each step lemma). -/
syntax "mma_cont " term:max term:max term:max term:max term:max : term
macro_rules
  | `(mma_cont $L $g $d $e $u) => `(next $L $g $d $e = some none ∨ ∃ d' t', next $L $g $d $e =
    some (some d') ∧
      Relation.ReflTransGen (Tau kernel [Assumptions.idealArith,
        Assumptions.clusterMbar, Assumptions.pollAgree] $L $g) $u t' ∧
      At t' d'.site.pc (facts $L $g d') ∧ Inv d')


/-- The value of `r` in state `d`, with the registers of `ex` valued as given: the predicates
a branch tests, which the value table does not give. -/
def valueX (L : Launch) (g : Nat) (d : D) (ex : List (Nat × Value)) (r : Nat) : Value :=
  (ex.lookup r).getD (valueOf L g d r)

/-- The facts at `pc` under `valueX`. -/
def factsX (L : Launch) (g pc : Nat) (d : D) (ex : List (Nat × Value)) :
    List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueX L g d ex)

/-- Evaluate an MMA segment from `h` and close its end facts: as `mma_seg`, with the site
and literal comparisons of the value table simplified first. -/
syntax "mseg" term:max term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| mseg $h $hpre $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      have hbase := ($hpre).sharedRange
      unfold sharedBytes at hbase
      seg_fp $h using
        try simp only [valueX]
        try mma_values
        try simp only [Fin.reduceFinMk, Fin.reduceEq, Site.full.injEq, Fin.isValue,
          false_and, true_and, and_false, and_true, ↓reduceIte, reduceCtorEq, $extra,*]
        all_goals seg_close [Launch.oneDim_ctaidOf ($hpre).oneDimLaunch.1,
          Launch.oneDim_clusterCtaidOf ($hpre).oneDimLaunch.1,
          Launch.oneDim_rankOfCta ($hpre).oneDimLaunch.1, Dim3.get, ($hpre).cluster,
          Loader.none32, descC, $extra,*]))

/-- The predicate each slot's full poll writes. -/
def slotPred : Fin 4 → Nat
  | 0 => 1006 | 1 => 1011 | 2 => 1016 | 3 => 1021

theorem slotPred_not_live : ∀ s : Fin 4, slotPred s ∉ Flow.live (Site.full s).pc := by
  intro s
  fin_cases s <;> table_decide

theorem facts_ne {L : Launch} {g pc : Nat} {d : D} {r : Nat} (hr : r ∉ Flow.live pc) :
    ∀ p ∈ factsAt L g pc d, p.1 ≠ r := by
  intro p hp he
  simp only [factsAt, Flow.factsFrom, List.mem_map] at hp
  obtain ⟨r', hr', rfl⟩ := hp
  exact hr (he ▸ hr')

/-- The local instructions between the MMA at `s`, `j` and the next event. -/
def mmaGap (s j : Fin 4) : Nat :=
  if j.val = 3 then (if s.val = 0 then 2 else 1) else if s.val = 0 ∧ j.val < 2 then 2 else 3

/-- The site after the MMA at `s`, `j`: the slot's next MMA, or its commit. -/
def mmaNext (s j : Fin 4) : Site :=
  if h : j.val + 1 < 4 then .mma s ⟨j.val + 1, h⟩ else .commit s

theorem mmaNext_ne_full (s j k : Fin 4) : (mmaNext s j = Site.full k) = False := by
  unfold mmaNext
  split <;> simp

theorem next_mma (s j : Fin 4) (w q fp ap cp : Nat) (resp : Value) (x : Nat) (L : Launch) (g : Nat)
    (e : Event) : next L g ⟨.mma s j, w, q, fp, ap, cp, resp, x⟩ e =
      some (some ⟨mmaNext s j, w, q, fp, ap, cp, resp, x⟩) := by
  simp only [next, mmaNext]
  split_ifs <;> rfl

theorem code_mma (s j : Fin 4) : ∃ ad bd en, kernel.code[(Site.mma s j).pc]? =
    some ⟨none, .tcMma
      { group := .two, ws := false, kind := .f16, d := 861, a := .smem ad, bdesc := bd,
        idesc := .reg 862, mask := List.replicate 8 (.reg 863), enableD := en }⟩ := by
  fin_cases s <;> fin_cases j
  · exact ⟨_, _, _, Flow.code_mma_0⟩
  · exact ⟨_, _, _, Flow.code_mma_1⟩
  · exact ⟨_, _, _, Flow.code_mma_2⟩
  · exact ⟨_, _, _, Flow.code_mma_3⟩
  · exact ⟨_, _, _, Flow.code_mma_4⟩
  · exact ⟨_, _, _, Flow.code_mma_5⟩
  · exact ⟨_, _, _, Flow.code_mma_6⟩
  · exact ⟨_, _, _, Flow.code_mma_7⟩
  · exact ⟨_, _, _, Flow.code_mma_8⟩
  · exact ⟨_, _, _, Flow.code_mma_9⟩
  · exact ⟨_, _, _, Flow.code_mma_10⟩
  · exact ⟨_, _, _, Flow.code_mma_11⟩
  · exact ⟨_, _, _, Flow.code_mma_12⟩
  · exact ⟨_, _, _, Flow.code_mma_13⟩
  · exact ⟨_, _, _, Flow.code_mma_14⟩
  · exact ⟨_, _, _, Flow.code_mma_15⟩

/-- The phase flip of a trip's full-barrier parity, as the code computes it. -/
theorem flip_mma : ∀ cp < 2,
    truncBits 32 (BitVec.ofNat 64 cp) ^^^ truncBits 32 (BitVec.ofInt 64 1) =
    BitVec.ofNat 64 (1 - cp) := by
  table_decide

theorem code_commit (s : Fin 4) : ∃ base mask, kernel.code[(Site.commit s).pc]? =
    some ⟨none, .tcCommit .two base 0 mask⟩ := by
  fin_cases s
  · exact ⟨_, _, Flow.code_tcCommit_0⟩
  · exact ⟨_, _, Flow.code_tcCommit_1⟩
  · exact ⟨_, _, Flow.code_tcCommit_2⟩
  · exact ⟨_, _, Flow.code_tcCommit_3⟩

theorem factsX_ne {L : Launch} {g pc : Nat} {d : D} {ex : List (Nat × Value)} {r : Nat}
    (hr : r ∉ Flow.live pc) : ∀ p ∈ factsX L g pc d ex, p.1 ≠ r := by
  intro p hp he
  simp only [factsX, Flow.factsFrom, List.mem_map] at hp
  obtain ⟨r', hr', rfl⟩ := hp
  exact hr (he ▸ hr')

/-- The abstract ack pointer: the leader CTA's copy of the acknowledgement barrier. -/
abbrev ackPtr (L : Launch) (g : Nat) : Value :=
  .ptr 32 false (.shared (g / L.block) (2 * ((g / L.block) / 2)))
      (BitVec.ofNat 64 (L.sharedBase + 128))

/-- The response's status is read: the response value, by its first-CTA claim. -/
theorem resp_of {L : Launch} {g : Nat} {d : D} {t : TState} {r : ClcResponse}
    (h : At t d.site.pc (facts L g d)) (hlive : 975 ∈ Flow.live d.site.pc)
    (hr : readValue L g t 128 (.reg 975) = .ok (.clc r)) : d.resp = .clc r := by
  have hreg : t.regs 975 = some d.resp :=
    holds_mem h.2.2.2.2 (List.mem_map.mpr ⟨975, hlive, by mma_values⟩)
  simp only [readValue, readReg, hreg, pure, Except.pure] at hr
  exact Except.ok.inj hr

/-- Each site is an instruction whose guard holds in its facts. -/
theorem site_ok {L : Launch} {g : Nat} (d : D) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (facts L g d) ins.guard := by
  obtain ⟨site, w, q, fp, ap, cp, resp, x⟩ := d
  cases site with
  | elect => exact ⟨_, Flow.code_elect_3, rfl, trivial⟩
  | clcWait => exact ⟨_, Flow.code_mbarWait_15, rfl, trivial⟩
  | clcLoad => exact ⟨_, Flow.code_loadAcquire_2, rfl, trivial⟩
  | clcStatus => exact ⟨_, Flow.code_clcQuery_4, rfl, trivial⟩
  | clcFirst =>
    refine ⟨_, Flow.code_clcQuery_5, rfl, ?_⟩
    have hm := Flow.mem_factsFrom (val := valueOf L g ⟨.clcFirst, w, q, fp, ap, cp, resp, x⟩)
      (show 1003 ∈ Flow.live Site.clcFirst.pc by table_decide)
    have hv : valueOf L g ⟨.clcFirst, w, q, fp, ap, cp, resp, x⟩ 1003 = .pred true := by
      mma_values
      simp
    show (1003, Value.pred true) ∈ facts L g ⟨.clcFirst, w, q, fp, ap, cp, resp, x⟩
    exact hv ▸ hm
  | clcFence => exact ⟨_, Flow.code_fenceProxy_3, rfl, trivial⟩
  | ack =>
    refine ⟨_, Flow.code_mbarArrive_11, rfl, ?_⟩
    have hm := Flow.mem_factsFrom (val := valueOf L g ⟨.ack, w, q, fp, ap, cp, resp, x⟩)
      (show 1004 ∈ Flow.live Site.ack.pc by table_decide)
    have hv : valueOf L g ⟨.ack, w, q, fp, ap, cp, resp, x⟩ 1004 = .pred true := by
      mma_values
    show (1004, Value.pred true) ∈ facts L g ⟨.ack, w, q, fp, ap, cp, resp, x⟩
    exact hv ▸ hm
  | accWait => exact ⟨_, Flow.code_mbarWait_16, rfl, trivial⟩
  | full s =>
    fin_cases s
    · exact ⟨_, Flow.code_mbarWait_17, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarWait_18, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarWait_19, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarWait_20, rfl, trivial⟩
  | mma s j =>
    obtain ⟨ad, bd, en, hc⟩ := code_mma s j
    exact ⟨_, hc, rfl, trivial⟩
  | commit s =>
    obtain ⟨base, mask, hc⟩ := code_commit s
    exact ⟨_, hc, rfl, trivial⟩
  | accCommit => exact ⟨_, Flow.code_tcCommit_4, rfl, trivial⟩
  | exitArrive => exact ⟨_, Flow.code_clusterArrive_1, rfl, trivial⟩
  | exitWait => exact ⟨_, Flow.code_clusterWait_1, rfl, trivial⟩
  | exit => exact ⟨_, Flow.code_exit_0, rfl, trivial⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof.Mma
