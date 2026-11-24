-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderDiscipline
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderEvents
public import Lemmas.Flow.Polls
public import Lemmas.Order.CausalThreadCount
public import Lemmas.Flow.TraceInduction
public import Lemmas.Flow.NotArrive

@[expose] public section

/-! # The loader's arrivals on the full barriers

The loader arrives on slot `s`'s full barrier of its cluster's leader CTA once for each block
of a trip that uses slot `s`, after it polled slot `s`'s empty barrier for that block. Along
its run, the arrivals on each full barrier, plus one for the batch the loader is on
(`Loader.pending`), never exceed its successful polls of the matching empty barrier
(`LoaderTasks.Counts`). So every arrival is preceded by a successful poll that no earlier
arrival has consumed (`InputRing.arrival_budget`, in `LoaderTasks`). -/


namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000


/-- Slot `s`'s full barrier of thread `g`'s cluster. -/
abbrev Loader.fullOf (L : Launch) (g : Nat) (s : Fin 4) : Loc :=
  InputRing.fullLoc L ((g / L.block) / 2) s

theorem fullLoc_eq_iff {L : Launch} {c : Nat} {s s' : Fin 4} :
    InputRing.fullLoc L c s = InputRing.fullLoc L c s' ↔ s = s' := by
  constructor
  · intro h
    have h' := congrArg Loc.addr h
    simp only [InputRing.fullLoc] at h'
    exact Fin.ext (by omega)
  · rintro rfl
    rfl

/-- The leader CTA's acknowledgement barrier is not a full barrier. -/
theorem ackLoc_ne_fullOf (L : Launch) (g : Nat) (s : Fin 4) :
    (⟨.shared, 2 * ((g / L.block) / 2), L.sharedBase + 128⟩ : Loc) ≠ Loader.fullOf L g s := by
  intro h
  have h' := congrArg Loc.addr h
  simp only [Loader.fullOf, InputRing.fullLoc] at h'
  have := s.isLt
  omega

namespace Loader

/-- Whether the loader's site is an arrival on a full barrier or the acknowledgement. -/
def Site.arrives : Site → Bool
  | .arrive _ | .ack => true
  | _ => false

/-- Whether the loader has polled slot `s`'s empty barrier in the current batch and not yet
arrived on its full barrier: the loads and the arrival of a batch on slot `s`. -/
def pending (l : D) (s : Fin 4) : Bool := match l.site with
  | .load b _ | .arrive b => decide (InputRing.slotOf b = s)
  | _ => false

/-- The loads' instructions are not mbarrier arrivals (decided on the code). -/
theorem load_arriveOp : ∀ (b : Fin 8) (j : Fin 3),
    (kernel.code[(Site.load b j).pc]?).map (fun ins => arriveOp ins.op) ≠ some true := by
  table_decide

/-- A loader site that is not an arrival runs an instruction that is not an mbarrier arrival. -/
theorem code_arriveOp (s : Site) (hs : s.arrives = false) {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins) : arriveOp ins.op = false := by
  cases s with
  | wait b =>
    rw [code_wait_ops b] at hc
    cases hc
    rfl
  | load b j =>
    have h := load_arriveOp b j
    rw [hc] at h
    simpa using h
  | arrive b => simp [Site.arrives] at hs
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
  | ack => simp [Site.arrives] at hs
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

/-- The events of a loader site that is not an arrival fire no arrival. -/
theorem notArrive_fires {L : Launch} {g : Nat} {t : TState} (s : Site) (hs : s.arrives = false)
    {ins : Instr} {e : Event} {o : Option TState} (hc : kernel.code[s.pc]? = some ins)
    (hf : Fires s.pc (eventTmpl Prod L g t ins.op) e o) :
    ∀ (l : Loc) (tx c : Nat) (rel : Bool) (sc : MbarScope), e.kind ≠ .arrive l tx c rel sc :=
  fires_notArrive (eventTmpl_notArrive (arriveOp_ne (code_arriveOp s hs hc))) hf

set_option maxHeartbeats 4000000 in
/-- The acknowledgement arrives on the leader CTA's acknowledgement barrier. -/
theorem ack_event {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState} {o :
    Option TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hs : d.site = .ack) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ (tx c : Nat) (rel : Bool) (sc : MbarScope),
      e = ⟨d.site.pc, .arrive ⟨.shared, 2 * ((g / L.block) / 2), L.sharedBase + 128⟩ tx c rel sc⟩ :=
        by
  obtain ⟨s, m, n, q, cp, r, x⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_8)
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hcta := cta_lt hpre hg
  have hv : t.regs 819 = some (.ptr 32 false (.shared (g / L.block) (2 * ((g / L.block) / 2)))
      (BitVec.ofNat 64 (L.sharedBase + 128))) :=
    (show valueOf L g ⟨.ack, m, n, q, cp, r, x⟩ 819 = .ptr 32 false
        (.shared (g / L.block) (2 * ((g / L.block) / 2))) (BitVec.ofNat 64 (L.sharedBase + 128)) by
        loader_values) ▸
      holds_mem h.2.2.2.2 (Flow.mem_factsFrom (show 819 ∈ Flow.live Site.ack.pc by table_decide))
  have hm := mbarClusterLoc_ptr hv hg (by rw [hpre.grid] at hcta ⊢; omega)
    (by simp only [clusterOfCta_eq hpre]; omega) (by omega) (by omega)
  obtain ⟨rel', sc', he, -⟩ := fires_arrive_at (cluster := true) (by simpa using hm)
    (show readBits L g t 32 (.imm 0) = .ok (truncBits 32 (BitVec.ofInt 64 0)) by
      simp [readBits, pure, Except.pure])
    (show readBits L g t 32 (.imm 1) = .ok (truncBits 32 (BitVec.ofInt 64 1)) by
      simp [readBits, pure, Except.pure]) hf
  exact ⟨_, _, rel', sc', he⟩

set_option maxHeartbeats 4000000 in
/-- At a loader's arrival on slot `s`'s full barrier, the loader's batch is on slot `s`. -/
theorem arrive_pending {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) {l : D} {e : Event} {t : TState} {ins : Instr} {o : Option TState}
    (hat : At t l.site.pc (facts L g l)) (hc : kernel.code[l.site.pc]? = some ins)
    (hfire : Fires l.site.pc (eventTmpl Prod L g t ins.op) e o) {s : Fin 4} {tx c : Nat}
    {rel : Bool} {sc : MbarScope} (hk : e.kind = .arrive (Loader.fullOf L g s) tx c rel sc) :
    pending l s = true := by
  obtain ⟨site, m, n, q, cp, r, x⟩ := l
  cases site with
  | wait b => exact absurd hk (notArrive_fires (.wait b) rfl hc hfire _ _ _ _ _)
  | load b j => exact absurd hk (notArrive_fires (.load b j) rfl hc hfire _ _ _ _ _)
  | arrive b =>
    cases o with
    | none => exact absurd hk (fires_none_notArrive hfire _ _ _ _ _)
    | some u =>
      obtain ⟨rel', sc', rfl⟩ := arrive_event hpre hg b rfl hat hc hfire
      have h1 : PTX.Kind.arrive (InputRing.fullLoc L ((g / L.block) / 2) (InputRing.slotOf b))
          98304 1 rel' sc' = PTX.Kind.arrive (Loader.fullOf L g s) tx c rel sc := hk
      simp only [pending, decide_eq_true_eq]
      exact fullLoc_eq_iff.mp (PTX.Kind.arrive.inj h1).1
  | clcWait => exact absurd hk (notArrive_fires .clcWait rfl hc hfire _ _ _ _ _)
  | clcLoad => exact absurd hk (notArrive_fires .clcLoad rfl hc hfire _ _ _ _ _)
  | clcStatus => exact absurd hk (notArrive_fires .clcStatus rfl hc hfire _ _ _ _ _)
  | clcFirst => exact absurd hk (notArrive_fires .clcFirst rfl hc hfire _ _ _ _ _)
  | clcFence => exact absurd hk (notArrive_fires .clcFence rfl hc hfire _ _ _ _ _)
  | ack =>
    cases o with
    | none => exact absurd hk (fires_none_notArrive hfire _ _ _ _ _)
    | some u =>
      obtain ⟨tx', c', rel', sc', rfl⟩ := ack_event hpre hg rfl hat hc hfire
      have h1 : PTX.Kind.arrive (⟨.shared, 2 * ((g / L.block) / 2), L.sharedBase + 128⟩ : Loc)
          tx' c' rel' sc' = PTX.Kind.arrive (Loader.fullOf L g s) tx c rel sc := hk
      exact absurd (PTX.Kind.arrive.inj h1).1 (ackLoc_ne_fullOf L g s)
  | drain i => exact absurd hk (notArrive_fires (.drain i) rfl hc hfire _ _ _ _ _)
  | exitArrive => exact absurd hk (notArrive_fires .exitArrive rfl hc hfire _ _ _ _ _)
  | exitWait => exact absurd hk (notArrive_fires .exitWait rfl hc hfire _ _ _ _ _)
  | exit => exact absurd hk (notArrive_fires .exit rfl hc hfire _ _ _ _ _)

end Loader

namespace Prologue

/-- The prologue's `init` instructions are not mbarrier arrivals (decided on the code). -/
theorem init_arriveOp : ∀ i : Fin 18,
    (kernel.code[(Site.init i).pc]?).map (fun ins => arriveOp ins.op) ≠ some true := by
  table_decide

/-- No prologue instruction is an mbarrier arrival. -/
theorem code_arriveOp (s : Site) {ins : Instr} (hc : kernel.code[s.pc]? = some ins) :
    arriveOp ins.op = false := by
  cases s with
  | shfl => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0); rfl
  | elect => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_0); rfl
  | init i =>
    have h := init_arriveOp i
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
