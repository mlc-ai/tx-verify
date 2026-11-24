-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Mma
public import Lemmas.Flow.Local
public import Lemmas.Flow.Async
public import Lemmas.Flow.Tc
public import Lemmas.Flow.Alloc
public import Lemmas.Flow.MemTmpl
public import Lemmas.Flow.Pointer
public import Mathlib.Tactic.FinCases
public import Lemmas.Flow.SignedBits
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.Join
public import Lemmas.Flow.BitForms
public import Lemmas.Flow.Step.SiteCases

@[expose] public section

/-! Definitions and helper facts of the MMA warp's step lemmas. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000

/-- A concrete state of the abstract state `d`: at its site's instruction and sub-step, with
its facts. -/
def AtS (L : Launch) (g : Nat) (t : TState) (d : D) : Prop :=
  t.pc = d.site.pc ∧ t.sub = d.site.sub ∧ t.acc = [] ∧ t.fault = none ∧
    Holds t.regs (facts L g d)

theorem atS_of_at {L : Launch} {g : Nat} {t : TState} {d : D} (hs : d.site.sub = 0)
    (h : At t d.site.pc (facts L g d)) : AtS L g t d :=
  ⟨h.1, hs ▸ h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem at_of_atS {L : Launch} {g : Nat} {t : TState} {d : D} (hs : d.site.sub = 0)
    (h : AtS L g t d) : At t d.site.pc (facts L g d) :=
  ⟨h.1, hs ▸ h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- The continuation of a step of this role: the thread stops following (`some none`), or
steps to `d'` at `t'` by a run of `Tau`. -/
syntax "mma_cont " term:max term:max term:max term:max term:max : term
macro_rules
  | `(mma_cont $L $g $d $e $u) => `(next $L $g $d $e = some none ∨ ∃ d' t', next $L $g $d $e =
    some (some d') ∧
      Relation.ReflTransGen (Tau kernel asms $L $g) $u t' ∧
      AtS $L $g t' d' ∧ Inv $L $g d')

theorem facts_ne {L : Launch} {g pc : Nat} {d : D} {r : Nat} (hr : r ∉ Flow.live pc) :
    ∀ p ∈ factsAt L g pc d, p.1 ≠ r := by
  intro p hp he
  simp only [factsAt, Flow.factsFrom, List.mem_map] at hp
  obtain ⟨r', hr', rfl⟩ := hp
  exact hr (he ▸ hr')

theorem kvPar_lt (L : Launch) (i u : Nat) : kvPar L i u < 2 := Nat.mod_lt _ (by decide)

theorem pPar_lt (L : Launch) (i t : Nat) : pPar L i t < 2 := Nat.mod_lt _ (by decide)

theorem pPar_next {L : Launch} {i t : Nat} (h : t + 1 = trips L) :
    pPar L (i + 1) 0 = 1 - pPar L i t := by
  simp only [pPar, pBase]
  rw [Nat.mul_succ]
  omega

theorem kvBase_succ (L : Launch) (i : Nat) : kvBase L (i + 1) = kvBase L i + 2 * trips L := by
  simp only [kvBase]
  ring

theorem pPar_succ (L : Launch) (i t : Nat) : pPar L i (t + 1) = 1 - pPar L i t := by
  simp only [pPar]
  omega

/-! ### The shape under the precondition -/

theorem pre_sk {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) : skOf L = P.sk :=
  skOf_eq hpre

/-- The item count as the code reads it (`Common.totOf`, a 64-bit word) is the schedule's,
which `Pre` bounds below `2^31`. -/
theorem pre_tot {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    totOf L = P.items := by
  have hr := hpre.scheduleRange
  rw [totOf_eq hpre]
  omega

theorem pre_clusters {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    clusters L = P.clusters := by
  simp only [clusters, hpre.grid, hpre.cluster]
  omega

/-- `%nclusterid.x` is the number of clusters. -/
theorem pre_nclusterid {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) (cta : Nat) :
    (L.nclusteridOf cta).get .x = P.clusters := by
  rw [Launch.oneDim_nclusteridOf hpre.oneDimLaunch.1, ← pre_clusters hpre]
  rfl

theorem work_zero (L : Launch) (g : Nat) : work L g 0 = clusterOf L g := by
  simp [work]

theorem work_succ (L : Launch) (g i : Nat) : work L g (i + 1) = work L g i + clusters L := by
  simp only [work]
  ring

theorem kvBase_zero (L : Launch) : kvBase L 0 = 0 := by simp [kvBase]

theorem pBase_zero (L : Launch) : pBase L 0 = 0 := by simp [pBase]

theorem pre_trips {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    trips L = (P.sk + 127) / 128 := by
  simp only [trips, pre_sk hpre]

theorem trips_pos {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    0 < trips L := by
  have := hpre.skPos
  rw [pre_trips hpre]
  omega

theorem shape_bounds {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) : clusterOf L g < P.clusters ∧ rank L g < 2 := by
  have hone := hpre.oneDimLaunch.1
  have hb := hpre.block
  have hgr := hpre.grid
  have hc := hpre.cluster
  simp only [Launch.threads] at hg
  simp only [clusterOf, ctaOf, rank, Launch.oneDim_clusterOfCta hone, hc, hb]
  rw [hgr, hb] at hg
  constructor
  · apply Nat.div_lt_of_lt_mul
    apply Nat.div_lt_of_lt_mul
    rwa [Nat.mul_comm 512]
  · omega

/-- `mma_seg` with the shape facts of the precondition in context: the sizes as the
parameters give them and their bounds. -/
syntax "mma_seg_s" term:max term:max term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| mma_seg_s $h $hpre $hg $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      have hsh := shape_bounds $hpre $hg
      have htot := pre_tot $hpre
      have hclu := pre_clusters $hpre
      have htr := pre_trips $hpre
      have hsr := ($hpre).scheduleRange
      have hskr := ($hpre).skRange
      have hskp := ($hpre).skPos
      have hskd := ($hpre).skDiv128
      have hbase := ($hpre).sharedRange
      unfold sharedBytes at hbase
      seg_fp $h using
        try simp only [$extra,*]
        try mma_values
        all_goals first
          | join_close [desc, descHi, qLo, kLo, vLo, qLow, $extra,*]
          | seg_close [pre_tot $hpre, pre_clusters $hpre, pre_nclusterid $hpre, pre_trips $hpre,
              pre_sk $hpre, ($hpre).cluster, ($hpre).grid, work_zero, kvSlot, kvPar, kvBase_zero,
              pBase_zero, $extra,*]
          | norm_signed [pre_tot $hpre, pre_clusters $hpre, pre_nclusterid $hpre, pre_trips $hpre,
              pre_sk $hpre, ($hpre).cluster, ($hpre).grid, work_zero, kvSlot, kvPar, kvBase_zero,
              pBase_zero, $extra,*]))

/-- An operation that is neither an ideal-arithmetic form nor an approximate form gets no rule
from the kernel's assumptions: it steps by the Core rule. -/
theorem asms_localRule_none {op : Op} (hf : Assumption.FloatForm.ofOp op = none)
    (ha : Assumption.ApproxForm.ofOp op = none) (L : Launch) (g : Nat) (t : TState) :
    ∀ a ∈ asms, a.localRule L g t op = none := by
  simp [asms, Assumptions.all, Assumptions.idealArith, Assumptions.clusterMbar, Assumptions.approx,
    Assumptions.swExp2, Assumptions.peerBit, Assumptions.tcLd, Assumptions.commitOrder,
    Assumptions.pollAgree, Assumption.idealReal, Assumption.clusterScopeMbarAt,
    Assumption.approxExact, Assumption.segmentExact, Assumption.pairEvenAt,
    Assumption.tcLdDataflowAt, Assumption.commitOrderAt, Assumption.pollAgreeAt, hf, ha]

/-- No assumption of the kernel names a branch. -/
theorem asms_bra_none (L : Launch) (g : Nat) {pc target : Nat} {uni : Bool} :
    ∀ t : TState, t.pc = pc → ∀ a ∈ asms, a.localRule L g t (.bra target uni) = none :=
  fun t _ => asms_localRule_none (by simp [Assumption.FloatForm.ofOp])
    (by simp [Assumption.ApproxForm.ofOp]) L g t

/-- A conditional branch on a predicate fact keeps every register fact (`Seg.bra` under the
kernel's assumptions). -/
theorem seg_bra {L : Launch} {g pc target p : Nat} {uni pick : Bool} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨some (p, false), .bra target uni⟩)
    (hp : (p, Value.pred pick) ∈ F)
    (hA : Assumption.SegFreePc asms pc := by seg_free_pc) :
    Seg kernel asms L g 1 pc F (if pick then target else pc + 1) F :=
  Seg.bra hc hp (asms_bra_none L g) hA

/-! ### The role as a code machine -/

/-- The table with a wrap predicate (register `p`) fixed to `b`. -/
def valueSel (L : Launch) (g : Nat) (d : D) (p : Nat) (b : Bool) (r : Nat) : Value :=
  ([(p, .pred b)].lookup r).getD (valueOf L g d r)

/-- At the deallocation the carried address is a bit value, which the deallocation reads (the
hand-off poll continues to it only then). -/
def BaseOk (d : D) : Prop := d.site = .dealloc → d.base.regBits.isSome = true

theorem baseOk_afterCommit {L : Launch} {g : Nat} {d : D} (c : Fin 12) :
    BaseOk (afterCommit L g d c) := by
  intro h
  fin_cases c <;> simp [afterCommit] at h <;> split_ifs at h

/-- The MMA role as a code machine. -/
@[reducible] def code (A : List Assumption) (L : Launch) (g : Nat) (pro : Nat → Value) :
    Flow.Code kernel A L g where
  D := D
  init := ⟨.setMaxReg, 0, 0, b32 0, pro⟩
  pc := (·.site.pc)
  facts := facts L g
  sub := (·.site.sub)
  inv := fun d => Inv L g d ∧ BaseOk d
  next := next L g

/-- A step of a site that does not change the carried address and does not enter the
deallocation, from its proof on the role's own terms (`mma_cont`). -/
theorem stepOk_of {L : Launch} {g : Nat} {pro : Nat → Value} {d : D}
    (hb : ∀ {e d'}, next L g d e = some (some d') → BaseOk d')
    (h : ∀ {t e u ins}, Inv L g d → AtS L g t d → kernel.code[d.site.pc]? = some ins →
      Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u) →
      mma_cont L g d e u ∨
        (next L g d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u)) :
    (code asms L g pro).StepOk d := by
  constructor
  intro t e u ins ha hi hc hf
  rcases h hi.1 ha hc hf with (hn | ⟨d', t', hn, hr, ht, hi'⟩) | ⟨hn, hd⟩
  · exact .inl (.inl hn)
  · exact .inl (.inr ⟨d', t', hn, hr, ht, hi', hb hn⟩)
  · exact .inr ⟨hn, hd⟩

/-- The role's segments: `mma_seg_s` with the simp lemmas of the asm blocks and broadcasts. -/
macro "mma_close" hpre:term:max hg:term:max : tactic =>
  `(tactic| (intro t h; mma_seg_s h $hpre $hg [kvSlot, kLo, vLo, land16383, lor65536, jOf,
    leadOf, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, shflVal, qLo]))

/-- A successor in the same part of the item, or outside the items, other than the
deallocation keeps the invariant. -/
macro "mma_inv" : tactic => `(tactic| first
  | exact fun hi => ⟨⟨hi.1.t, fun _ => hi.1.i trivial, hi.1.trip⟩, nofun⟩
  | exact fun hi => ⟨⟨hi.1.t, nofun, hi.1.trip⟩, nofun⟩)

/-- `site_cases` with the role's transition lemmas, segment, invariant and guard tactics. -/
syntax "mma_cases " term:max term:max (ppSpace colGt ident)*
  (" except " "[" siteOverride,* "]")? : tactic
macro_rules
  | `(tactic| mma_cases $hpre $hg $xs* $[except [$ovs,*]]?) => do
    let ovs := (ovs.map (·.getElems)).getD #[]
    if xs.isEmpty then
      `(tactic| site_step trans [next, afterCommit] seg_by (mma_close $hpre $hg)
        inv_by (mma_inv) guard_by (mma_values; rfl))
    else
      `(tactic| site_cases $xs* except [$ovs,*] trans [next, afterCommit]
        seg_by (mma_close $hpre $hg) inv_by (mma_inv) guard_by (mma_values; rfl))

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
