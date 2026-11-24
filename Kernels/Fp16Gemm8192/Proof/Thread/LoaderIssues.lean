-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderArrivals
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderEvents
public import Lemmas.Flow.TraceInduction
public import Lemmas.Flow.NotTensor

@[expose] public section

/-! # The loader's tensor issues on the full barriers

Block `b` of a loader trip issues three tensor loads (`j : Fin 3`) on slot `b % 4`; each load is
a `tensorIssue` event whose completion barrier is the `mbar` of its `TensorCopy.Spec`, the full
barrier of the slot in the cluster's leader CTA. Along a loader's run, the tensor issues on each
full barrier plus the loads it still has to issue there never exceed three times its successful
polls of the matching empty barrier (`LoaderTasks.Counts`). So each successful poll of slot `s`'s
empty barrier is followed by at most three tensor issues on slot `s`'s full barrier
(`InputRing.issue_budget`, in `LoaderTasks`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000


namespace Loader

/-- The loads of block `b` are the tensor copies of the code at `(Site.load b j).pc`; each
completes on the mbarrier named by block `b`'s register. -/
theorem code_load_op : ∀ (b : Fin 8) (j : Fin 3), ∃ dst map cs,
    kernel.code[(Site.load b j).pc]? =
      some ⟨none, .cpTensor true true dst 0 map cs (arriveBase b) 0 none .tile⟩
  | 0, 0 => ⟨_, _, _, Flow.code_tensorCopy_0⟩
  | 0, 1 => ⟨_, _, _, Flow.code_tensorCopy_1⟩
  | 0, 2 => ⟨_, _, _, Flow.code_tensorCopy_2⟩
  | 1, 0 => ⟨_, _, _, Flow.code_tensorCopy_3⟩
  | 1, 1 => ⟨_, _, _, Flow.code_tensorCopy_4⟩
  | 1, 2 => ⟨_, _, _, Flow.code_tensorCopy_5⟩
  | 2, 0 => ⟨_, _, _, Flow.code_tensorCopy_6⟩
  | 2, 1 => ⟨_, _, _, Flow.code_tensorCopy_7⟩
  | 2, 2 => ⟨_, _, _, Flow.code_tensorCopy_8⟩
  | 3, 0 => ⟨_, _, _, Flow.code_tensorCopy_9⟩
  | 3, 1 => ⟨_, _, _, Flow.code_tensorCopy_10⟩
  | 3, 2 => ⟨_, _, _, Flow.code_tensorCopy_11⟩
  | 4, 0 => ⟨_, _, _, Flow.code_tensorCopy_12⟩
  | 4, 1 => ⟨_, _, _, Flow.code_tensorCopy_13⟩
  | 4, 2 => ⟨_, _, _, Flow.code_tensorCopy_14⟩
  | 5, 0 => ⟨_, _, _, Flow.code_tensorCopy_15⟩
  | 5, 1 => ⟨_, _, _, Flow.code_tensorCopy_16⟩
  | 5, 2 => ⟨_, _, _, Flow.code_tensorCopy_17⟩
  | 6, 0 => ⟨_, _, _, Flow.code_tensorCopy_18⟩
  | 6, 1 => ⟨_, _, _, Flow.code_tensorCopy_19⟩
  | 6, 2 => ⟨_, _, _, Flow.code_tensorCopy_20⟩
  | 7, 0 => ⟨_, _, _, Flow.code_tensorCopy_21⟩
  | 7, 1 => ⟨_, _, _, Flow.code_tensorCopy_22⟩
  | 7, 2 => ⟨_, _, _, Flow.code_tensorCopy_23⟩

theorem loadBase_live : ∀ (b : Fin 8) (j : Fin 3),
    arriveBase b ∈ Flow.live (Site.load b j).pc := by
  table_decide

set_option maxHeartbeats 4000000 in
/-- The load at block `b`, part `j`, is a tensor issue whose completion barrier is slot
`b % 4`'s full barrier in the cluster's leader CTA. -/
theorem load_event {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads) (b : Fin 8) (j : Fin 3)
    (hs : d.site = .load b j) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    ∃ addr spec, e = ⟨d.site.pc, .tensorIssue addr spec⟩ ∧
      spec.mbar = InputRing.fullLoc L ((g / L.block) / 2) (InputRing.slotOf b) := by
  obtain ⟨s, m, n, q, cp, r, x⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  obtain ⟨dst, map, cs, hc'⟩ := code_load_op b j
  rw [hc'] at hc
  cases hc
  obtain ⟨addr, spec, rfl, hm⟩ := fires_cpTensor_mbar (A := Prod) hf
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hcta := cta_lt hpre hg
  have hb := (arriveBase_value L g _ b) ▸
    holds_mem h.2.2.2.2 (Flow.mem_factsFrom (loadBase_live b j))
  have hmb := mbarClusterLoc_ptr hb hg (by rw [hpre.grid] at hcta ⊢; omega)
    (by simp only [clusterOfCta_eq hpre]; omega) (by omega) (by omega)
  refine ⟨addr, spec, rfl, ?_⟩
  exact Except.ok.inj (hm.symm.trans hmb)

/-- Whether the loader's site is a tensor load. -/
def Site.isLoad : Site → Bool
  | .load _ _ => true
  | _ => false

/-- The loads of the current batch still to be issued on slot `s`. -/
def remaining (l : D) (s : Fin 4) : Nat := match l.site with
  | .load b j => if InputRing.slotOf b = s then 3 - j.val else 0
  | _ => 0

/-- A loader site that is not a load runs an instruction that is not a tensor copy (decided on
the code). -/
theorem code_tensorOp (s : Site) (hs : s.isLoad = false) {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins) : tensorOp ins.op = false := by
  cases s with
  | wait b =>
    rw [code_wait_ops b] at hc
    cases hc
    rfl
  | load b j => simp [Site.isLoad] at hs
  | arrive b =>
    rw [code_arrive_ops b] at hc
    cases hc
    rfl
  | clcWait =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_8)
    rfl
  | clcLoad =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_loadAcquire_0)
    rfl
  | clcStatus =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_0)
    rfl
  | clcFirst =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_1)
    rfl
  | clcFence =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_1)
    rfl
  | ack =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_8)
    rfl
  | drain i =>
    rw [code_drain_ops i] at hc
    cases hc
    rfl
  | exitArrive =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterArrive_1)
    rfl
  | exitWait =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_1)
    rfl
  | exit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    rfl

/-- A loader event fired at a site that is not a load is not a tensor issue. -/
theorem issuesTo_nonLoad {L : Launch} {g : Nat} {t : TState} {s : Site} {m : Loc} {e : Event}
    {ins : Instr} {o : Option TState} (hs : s.isLoad = false)
    (hc : kernel.code[s.pc]? = some ins) (hfire : Fires s.pc (eventTmpl Prod L g t ins.op) e o) :
    issuesTo m e = false :=
  issuesTo_notTensor (fires_notTensor (eventTmpl_notTensor (code_tensorOp s hs hc)) hfire)

set_option maxHeartbeats 4000000 in
/-- A tensor issue on slot `s`'s full barrier comes from a load of slot `s` that the loader still
has to issue. -/
theorem issue_pending {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) {l : D} {e : Event} {t : TState} {ins : Instr} {o : Option TState}
    (hat : At t l.site.pc (facts L g l)) (hc : kernel.code[l.site.pc]? = some ins)
    (hfire : Fires l.site.pc (eventTmpl Prod L g t ins.op) e o) {s : Fin 4}
    (hk : issuesTo (fullOf L g s) e = true) : 1 ≤ remaining l s := by
  obtain ⟨site, m, n, q, cp, r, x⟩ := l
  by_cases hl : site.isLoad = false
  · rw [issuesTo_nonLoad hl hc hfire] at hk
    cases hk
  · have hl' : site.isLoad = true := by simpa using hl
    obtain ⟨b, j, rfl⟩ : ∃ b j, site = .load b j := by
      cases site <;> first | exact ⟨_, _, rfl⟩ | simp [Site.isLoad] at hl'
    cases o with
    | none =>
      rw [issuesTo_notTensor (fires_none_notTensor hfire)] at hk
      cases hk
    | some u =>
      obtain ⟨addr, spec, rfl, hmb⟩ := load_event hpre hg b j rfl hat hc hfire
      simp only [issuesTo_tensorIssue, hmb, fullOf, fullLoc_eq_iff, decide_eq_true_eq] at hk
      have hj := j.isLt
      simp only [remaining, hk]
      simp only [↓reduceIte]
      omega

end Loader

namespace Prologue

/-- The prologue's `init` instructions are not tensor copies (decided on the code). -/
theorem init_tensorOp : ∀ i : Fin 18,
    (kernel.code[(Site.init i).pc]?).map (fun ins => tensorOp ins.op) ≠ some true := by
  table_decide

/-- No prologue instruction is a tensor copy. -/
theorem code_tensorOp (s : Site) {ins : Instr} (hc : kernel.code[s.pc]? = some ins) :
    tensorOp ins.op = false := by
  cases s with
  | shfl => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0); rfl
  | elect => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_0); rfl
  | init i =>
    have h := init_tensorOp i
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

end Prologue

end
end PTX.Kernels.Fp16Gemm8192.Proof
