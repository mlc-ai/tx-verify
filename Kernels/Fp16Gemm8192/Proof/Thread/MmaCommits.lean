-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.MmaDiscipline
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaEvents
public import Kernels.Fp16Gemm8192.Proof.Interface
public import Lemmas.Flow.TraceInduction
public import Lemmas.Flow.Polls
public import Lemmas.Flow.NotCommit
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # The MMA warps' commits and their specifications

An MMA thread commits to slot `s`'s empty barrier in its own CTA once for each trip that uses
slot `s`, after its four MMAs, and commits to its accumulator-full barrier after its last trip.
The prologue commits to nothing. These facts give each commit's specification (`Mma.accSpec`,
with `Mma.commitSpec` in `MmaEvents`) and tell which sites commit at all. The counts of the
commits are in `MmaCounts`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000


/-- Slot `s`'s empty barrier in thread `g`'s CTA. -/
abbrev emptyAt (L : Launch) (g : Nat) (s : Fin 4) : Loc :=
  ⟨.shared, g / L.block, L.sharedBase + 40 + 8 * s.val⟩

theorem emptyAt_eq_iff {L : Launch} {g : Nat} {s s' : Fin 4} :
    emptyAt L g s = emptyAt L g s' ↔ s = s' := by
  constructor
  · intro h
    have h' := congrArg Loc.addr h
    simp only at h'
    exact Fin.ext (by omega)
  · rintro rfl
    rfl

/-- The accumulator-full barrier of the MMA warp of parity `w % 2` is not an empty barrier. -/
theorem accLoc_ne_emptyAt (L : Launch) (g w : Nat) (s : Fin 4) :
    (⟨.shared, g / L.block, L.sharedBase + 8 * (w % 2) + 72⟩ : Loc) ≠ emptyAt L g s := by
  intro h
  have h' := congrArg Loc.addr h
  simp only at h'
  have := s.isLt
  omega

theorem commitsTo_of_commitSpec {L : Launch} {g : Nat} {e : Event} {s s' : Fin 4}
    (hk : e.kind = .tc (.commit (Mma.commitSpec L g s'))) :
    commitsTo (emptyAt L g s) e = decide (s' = s) := by
  rw [commitsTo_of_kind hk]
  exact decide_eq_decide.mpr emptyAt_eq_iff

namespace Prologue

/-- The prologue's `init` instructions are not Tensor Core commits (decided on the code). -/
theorem init_commitOp : ∀ i : Fin 18,
    (kernel.code[(Site.init i).pc]?).map (fun ins => commitOp ins.op) ≠ some true := by
  table_decide

/-- No prologue instruction is a Tensor Core commit. -/
theorem code_commitOp (s : Site) {ins : Instr} (hc : kernel.code[s.pc]? = some ins) :
    commitOp ins.op = false := by
  cases s with
  | shfl => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0); rfl
  | elect => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_0); rfl
  | init i =>
    have h := init_commitOp i
    rw [hc] at h
    simpa using h
  | alloc => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0); rfl
  | allocWrite => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0); rfl
  | warpBar => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_warpBar_0); rfl
  | fence => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_0); rfl
  | fenceInit => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceMbarInit_0); rfl
  | arrive => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterArrive_0); rfl
  | wait => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_0); rfl
  | setMaxReg => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_0); rfl
  | roleElect => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_1); rfl

/-- A prologue event fires no commit event. -/
theorem notCommit_fires {L : Launch} {g : Nat} {t : TState} (s : Site) {ins : Instr} {e : Event}
    {o : Option TState} (hc : kernel.code[s.pc]? = some ins)
    (hf : Fires s.pc (eventTmpl Prod L g t ins.op) e o) : ∀ sp, e.kind ≠ .tc (.commit sp) :=
  fires_notCommit (eventTmpl_notCommit (commitOp_ne (code_commitOp s hc))) hf

end Prologue

namespace Mma

/-- Whether the MMA thread's site commits to an mbarrier: a slot's commit or the accumulator
commit. -/
def Site.commits : Site → Bool
  | .commit _ | .accCommit => true
  | _ => false

/-- Whether the MMA thread has polled slot `s`'s full barrier in the current trip and not yet
committed for it: the MMAs and the commit of slot `s`. -/
def pendingCommit (m : D) (s : Fin 4) : Bool := match m.site with
  | .mma s' _ | .commit s' => decide (s' = s)
  | _ => false


/-- The instruction at a site that is not a commit is not a Tensor Core commit. -/
theorem code_commitOp (s : Site) (hs : s.commits = false) {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins) : commitOp ins.op = false := by
  cases s with
  | elect => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_3); rfl
  | clcWait => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_15); rfl
  | clcLoad => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_loadAcquire_2); rfl
  | clcStatus => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_4); rfl
  | clcFirst => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_5); rfl
  | clcFence => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_3); rfl
  | ack => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_11); rfl
  | accWait => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_16); rfl
  | full s =>
    rw [code_full_ops s] at hc
    cases hc
    rfl
  | mma s j =>
    obtain ⟨ad, bd, en, hc'⟩ := code_mma s j
    obtain rfl := Option.some.inj (hc.symm.trans hc')
    rfl
  | commit _ => simp [Site.commits] at hs
  | accCommit => simp [Site.commits] at hs
  | exitArrive => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterArrive_1); rfl
  | exitWait => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_1); rfl
  | exit => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0); rfl

/-- An MMA site that is not a commit fires no commit event. -/
theorem notCommit_fires {L : Launch} {g : Nat} {t : TState} (s : Site) (hs : s.commits = false)
    {ins : Instr} {e : Event} {o : Option TState} (hc : kernel.code[s.pc]? = some ins)
    (hf : Fires s.pc (eventTmpl Prod L g t ins.op) e o) : ∀ sp, e.kind ≠ .tc (.commit sp) :=
  fires_notCommit (eventTmpl_notCommit (commitOp_ne (code_commitOp s hs hc))) hf

/-- The accumulator commit's specification: the accumulator-full barrier of the warp's parity
`w % 2` in the thread's CTA, mask 3, over the thread's cluster. -/
def accSpec (L : Launch) (g w : Nat) : TcCommit.Spec :=
  ⟨.two, ⟨.shared, g / L.block, L.sharedBase + 8 * (w % 2) + 72⟩, 3, (g / L.block) / 2 * 2, 2⟩

set_option maxHeartbeats 4000000 in
/-- The accumulator commit resolves to `accSpec`. -/
theorem accCommit_spec {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}
    {o : Option TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hs : d.site = .accCommit) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    e = ⟨d.site.pc, .tc (.commit (accSpec L g d.w))⟩ := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcCommit_4)
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hcta := cta_lt hpre hg
  have hb : t.regs 872 = some (b32 (L.sharedBase + 8 * (w % 2) + 72)) :=
    (show valueOf L g ⟨.accCommit, w, q, fp, ap, cp, r, x⟩ 872 =
      b32 (L.sharedBase + 8 * (w % 2) + 72) by mma_values) ▸
      holds_mem h.2.2.2.2
        (Flow.mem_factsFrom (show 872 ∈ Flow.live Site.accCommit.pc by table_decide))
  have hv : t.regs 45 = some (.bits 16 (BitVec.ofNat 64 3)) :=
    (show valueOf L g ⟨.accCommit, w, q, fp, ap, cp, r, x⟩ 45 =
      .bits 16 (BitVec.ofNat 64 3) by mma_values) ▸
      holds_mem h.2.2.2.2
        (Flow.mem_factsFrom (show 45 ∈ Flow.live Site.accCommit.pc by table_decide))
  have hk : readBits L g t 16 (.reg 45) = .ok (truncBits 16 (BitVec.ofNat 64 3)) := by
    simp [readBits, readReg, hv, bind, Except.bind, pure, Except.pure]
  have hm := mbarClusterLoc_b32 (L := L) (g := g) hb (by omega) (by omega)
  have hv' := hpre.oneDimLaunch
  refine (fires_tcCommit_at hg hm hk ?_ hf).1
  simp [accSpec, TcCommit.resolve, clusterOfCta_eq hpre, clusterStart_eq hpre,
    clusterSizeOf_eq hpre, Launch.oneDimLaunch_clusterGridValid hv', hcta, truncBits]

/-- The accumulator commit notifies the accumulator-full barrier of its warp's parity. -/
theorem accCommit_event {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}
    {o : Option TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hs : d.site = .accCommit) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ sp, e = ⟨d.site.pc, .tc (.commit sp)⟩ ∧
      sp.mbar = ⟨.shared, g / L.block, L.sharedBase + 8 * (d.w % 2) + 72⟩ :=
  ⟨_, accCommit_spec hpre hg hs h hc hf, rfl⟩

end Mma

end
end PTX.Kernels.Fp16Gemm8192.Proof
