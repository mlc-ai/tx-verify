-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Scheduler
public import Kernels.Fp16Gemm8192.Proof.Thread.Cluster
public import Lemmas.Flow.Local
public import Lemmas.Flow.Tc

public import Lemmas.Flow.RoundTrip

@[expose] public section

/-! # The CLC scheduler's events The scheduler's sites as steps of the abstract machine: the
election, the acknowledgement and cancellation request on the leader CTA, the arrival and poll of
the CLC response, its read, queries and fence, the acknowledgement, and the common exit. Each step
follows the instructions of its site to the next site, evaluating the local code by segments. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Scheduler
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The continuation of a scheduler step: the thread leaves the role, or steps to `d'` at `t'`
by a run of `Tau` (the conclusion of each step lemma). -/
syntax "sched_cont " term:max term:max term:max term:max term:max : term
macro_rules
  | `(sched_cont $L $g $d $e $u) => `(next $L $g $d $e = some none ∨ ∃ d' t', next $L $g $d $e =
    some (some d') ∧
      Relation.ReflTransGen (Tau kernel [Assumptions.idealArith,
        Assumptions.clusterMbar, Assumptions.pollAgree] $L $g) $u t' ∧
      At t' d'.site.pc (facts $L $g d') ∧ Inv d')


theorem facts_set {L : Launch} {g pc : Nat} {d : D} {r : Nat} (hr : r ∉ Flow.live pc) :
    ∀ p ∈ factsAt L g pc d, p.1 ≠ r := by
  intro p hp he
  simp only [factsAt, Flow.factsFrom, List.mem_map] at hp
  obtain ⟨r', hr', rfl⟩ := hp
  exact hr (he ▸ hr')

theorem resp_of {L : Launch} {g : Nat} {d : D} {t : TState} {r : ClcResponse}
    (h : At t d.site.pc (facts L g d)) (hlive : 971 ∈ Flow.live d.site.pc)
    (hr : readValue L g t 128 (.reg 971) = .ok (.clc r)) : d.resp = .clc r := by
  have hreg : t.regs 971 = some d.resp :=
    holds_mem h.2.2.2.2 (List.mem_map.mpr ⟨971, hlive, by simp only [valueOf, values,
      List.lookup_cons, Nat.reduceBEq, Option.getD_some]⟩)
  simp only [readValue, readReg, hreg, pure, Except.pure] at hr
  exact Except.ok.inj hr

/-- Each scheduler site is an event instruction whose guard holds. -/
theorem site_ok {L : Launch} {g : Nat} (d : D) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (facts L g d) ins.guard := by
  obtain ⟨s, ap, cp, resp, x⟩ := d
  cases s with
  | elect => exact ⟨_, Flow.code_elect_2, rfl, trivial⟩
  | ackWait => exact ⟨_, Flow.code_mbarWait_13, rfl, trivial⟩
  | tryCancel => exact ⟨_, Flow.code_clcIssue_0, rfl, trivial⟩
  | arriveTx => exact ⟨_, Flow.code_mbarArrive_9, rfl, trivial⟩
  | clcWait => exact ⟨_, Flow.code_mbarWait_14, rfl, trivial⟩
  | clcLoad => exact ⟨_, Flow.code_loadAcquire_1, rfl, trivial⟩
  | clcStatus => exact ⟨_, Flow.code_clcQuery_2, rfl, trivial⟩
  | clcFirst =>
    refine ⟨_, Flow.code_clcQuery_3, rfl, ?_⟩
    have hm := Flow.mem_factsFrom (val := valueOf L g ⟨.clcFirst, ap, cp, resp, x⟩)
      (show 998 ∈ Flow.live Site.clcFirst.pc by table_decide)
    have hv : valueOf L g ⟨.clcFirst, ap, cp, resp, x⟩ 998 = .pred true := by
      simp only [valueOf, values, List.lookup_cons, Nat.reduceBEq, Option.getD_some]
      simp
    show (998, Value.pred true) ∈ facts L g ⟨.clcFirst, ap, cp, resp, x⟩
    exact hv ▸ hm
  | clcFence => exact ⟨_, Flow.code_fenceProxy_2, rfl, trivial⟩
  | ack =>
    refine ⟨_, Flow.code_mbarArrive_10, rfl, ?_⟩
    have hm := Flow.mem_factsFrom (val := valueOf L g ⟨.ack, ap, cp, resp, x⟩)
      (show 999 ∈ Flow.live Site.ack.pc by table_decide)
    have hv : valueOf L g ⟨.ack, ap, cp, resp, x⟩ 999 = .pred true := by
      simp only [valueOf, values, List.lookup_cons, Nat.reduceBEq, Option.getD_some]
    show (999, Value.pred true) ∈ facts L g ⟨.ack, ap, cp, resp, x⟩
    exact hv ▸ hm
  | exitArrive => exact ⟨_, Flow.code_clusterArrive_1, rfl, trivial⟩
  | exitWait => exact ⟨_, Flow.code_clusterWait_1, rfl, trivial⟩
  | exit => exact ⟨_, Flow.code_exit_0, rfl, trivial⟩

/-- The cluster arrival of the exit. -/
theorem step_exitArrive {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .exitArrive) (hi : Inv d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    sched_cont L g d e u := by
  obtain ⟨s, ap, cp, resp, x⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterArrive_1)
  obtain rfl := fires_next (show AdvancesOp (.cluster _) from trivial) hf
  right
  refine ⟨⟨.exitWait, ap, cp, resp, x⟩, _, by simp [next], .refl, ?_,
    ⟨hi.1, hi.2, hi.3⟩⟩
  exact At.mono (At.next h) (Flow.holds_factsFrom_mono (live := Flow.live Site.exitArrive.pc)
    (live' := Flow.live Site.exitWait.pc) h.2.2.2.2 (by table_decide))

/-- The cluster wait of the exit, then the branch past warp 0's deallocation. -/
theorem step_exitWait {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .exitWait) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    sched_cont L g d e u := by
  obtain ⟨s, ap, cp, resp, x⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_1)
  obtain rfl := fires_next (show AdvancesOp (.cluster _) from trivial) hf
  right
  obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 1 (PTX.next t) = some t' ∧
      At t' Site.exit.pc (facts L g ⟨.exit, ap, cp, resp, x⟩) := by
    sched_seg (At.next h) hpre
  exact ⟨⟨.exit, ap, cp, resp, x⟩, t', by simp [next], run_rtg hr, ht',
    ⟨hi.1, hi.2, hi.3⟩⟩


/-- The rank test of the next task's loop head: `%cluster_ctaid.x` of a one-dimensional cluster of
two CTAs is the low bit of the CTA index. -/
theorem rank_test {L : Launch} {g : Nat} (h : L.OneDim) (hc : L.clusterSize.val = 2) :
    Value.pred
      (compare Cmp.ne IType.b 32
        (truncBits 32 (truncBits 32 (BitVec.ofNat 64 ((L.clusterCtaidOf (g / L.block)).get Dim.x))))
        (truncBits 32 (BitVec.ofInt 64 0))) =
    Value.pred (decide (g / L.block % 2 ≠ 0)) := by
  norm_cmp [Launch.oneDim_clusterCtaidOf h (g / L.block), Launch.oneDim_rankOfCta h (g / L.block),
    hc, Dim3.get]

/-- The loop head after the rank branch at the end of the election or the acknowledgement:
the leader CTA polls the acknowledgement barrier, the other CTA arrives on its CLC barrier. -/
theorem loop_head {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}
    (hpre : Pre P L mem0)
    (h : At t Flow.bra_415 [(23, .pred (decide ((g / L.block) % 2 ≠ 0))), (48, b32 10),
      (880, b32 d.cp), (881, b32 d.ap)]) :
    ∃ k t', run kernel Prod L g k t = some t' ∧
      At t' (loopHead L g).pc (facts L g ⟨loopHead L g, d.ap, d.cp, d.resp, d.x⟩) := by
  obtain ⟨u, hr, hu⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_415
    (decide ((g / L.block) % 2 ≠ 0)) h (holds_mem h.2.2.2.2 List.mem_cons_self)
    (prod_localRule_bra L g _ _ _)
  by_cases hl : (g / L.block) % 2 = 0
  · have hd : decide ((g / L.block) % 2 ≠ 0) = false := by simp [hl]
    rw [hd] at hu
    simp only [Bool.false_eq_true, ↓reduceIte] at hu
    have hlh : loopHead L g = .ackWait := by simp [loopHead, Loader.leader, hl]
    simp only [hlh]
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 3 u = some t' ∧
        At t' Site.ackWait.pc (facts L g ⟨.ackWait, d.ap, d.cp, d.resp, d.x⟩) := by
      sched_seg hu hpre
    exact ⟨1 + 3, t', run_comp hr hr', ht'⟩
  · have hd : decide ((g / L.block) % 2 ≠ 0) = true := by simp [hl]
    rw [hd] at hu
    simp only [↓reduceIte] at hu
    have hlh : loopHead L g = .arriveTx := by simp [loopHead, Loader.leader, hl]
    simp only [hlh]
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 3 u = some t' ∧
        At t' Site.arriveTx.pc (facts L g ⟨.arriveTx, d.ap, d.cp, d.resp, d.x⟩) := by
      sched_seg hu hpre
    exact ⟨1 + 3, t', run_comp hr hr', ht'⟩

/-- The election: the elected lane goes to the loop head of the task; any other lane leaves
through the cluster arrival of the exit. -/
theorem step_elect {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .elect) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    sched_cont L g d e u := by
  obtain ⟨s, ap, cp, resp, x⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_2)
  obtain ⟨mk, inst, leader, rfl, rfl⟩ := fires_elect hf
  simp only [Option.elim]
  right
  have h1 := At.set (r := 994) (v := .pred (laneOf L g == leader)) h
    (not_mem_factsFrom (live := Flow.live Site.elect.pc) (by table_decide))
  cases hb : (laneOf L g == leader)
  · rw [hb] at h1
    obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 4
        (PTX.next (setReg t 994 (.pred false))) = some t3 ∧
        At t3 Site.exitArrive.pc (facts L g ⟨.exitArrive, ap, cp, resp, x⟩) := by
      sched_seg h1 hpre
    have hne : ¬ laneOf L g = leader := by simpa using hb
    exact ⟨⟨.exitArrive, ap, cp, resp, x⟩, t3, by simp [next, hne], run_rtg hr3, ht3,
      ⟨hi.1, hi.2, hi.3⟩⟩
  · rw [hb] at h1
    obtain ⟨t5, hr5, ht5⟩ : ∃ t5, run kernel Prod L g 7
        (PTX.next (setReg t 994 (.pred true))) = some t5 ∧
        At t5 Flow.bra_415 [(23, .pred (decide ((g / L.block) % 2 ≠ 0))), (48, b32 10),
          (880, b32 0), (881, b32 1)] := by
      sched_seg h1 hpre [sregValue, rank_test hpre.oneDimLaunch.1 hpre.cluster]
    obtain ⟨k, t', hk, ht'⟩ := loop_head (d := ⟨.ackWait, 1, 0, resp, x⟩) hpre ht5
    have hl' : laneOf L g = leader := by simpa using hb
    exact ⟨⟨loopHead L g, 1, 0, resp, x⟩, t', by simp [next, hl'], run_rtg (run_comp hr5 hk),
      ht', ⟨Nat.one_lt_two, Nat.zero_lt_two, hi.3⟩⟩


/-- The parity flip `x ^ 1` on a bounded value, as the code computes it. -/
theorem flip_bits : ∀ a < 2, truncBits 32 (BitVec.ofNat 64 a) ^^^ truncBits 32 (BitVec.ofInt 64 1) =
    BitVec.ofNat 64 (1 - a) := by
  table_decide

/-- The acknowledgement poll: a failed poll returns to it; a successful one flips the
acknowledgement parity and requests the next CTA. -/
theorem step_ackWait {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .ackWait) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    sched_cont L g d e u := by
  obtain ⟨s, ap, cp, resp, x⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_13)
  rw [← h.1] at hf
  obtain ⟨mb, parity, ok, sc, rfl, rfl⟩ := fires_wait hf
  have h1 := At.set (r := 995) (v := .pred ok) h
    (not_mem_factsFrom (live := Flow.live Site.ackWait.pc) (by table_decide))
  right
  cases ok with
  | false =>
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 2
        (PTX.next (setReg t 995 (.pred false))) = some t' ∧
        At t' Site.ackWait.pc (facts L g ⟨.ackWait, ap, cp, resp, x⟩) := by
      sched_seg h1 hpre
    exact ⟨⟨.ackWait, ap, cp, resp, x⟩, t', by simp [next], run_rtg hr, ht',
      ⟨hi.1, hi.2, hi.3⟩⟩
  | true =>
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 4
        (PTX.next (setReg t 995 (.pred true))) = some t' ∧
        At t' Site.tryCancel.pc (facts L g ⟨.tryCancel, 1 - ap, cp, resp, x⟩) := by
      sched_seg h1 hpre [flip_bits ap hi.1]
    exact ⟨⟨.tryCancel, 1 - ap, cp, resp, x⟩, t', by simp [next], run_rtg hr, ht',
      ⟨show 1 - ap < 2 by omega, hi.2, hi.3⟩⟩

/-- The request for the next CTA, issued by the leader; the response arrives on the CLC
barrier of the CTA. -/
theorem step_tryCancel {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .tryCancel) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    sched_cont L g d e u := by
  obtain ⟨s, ap, cp, resp, x⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcIssue_0)
  obtain rfl := fires_clcTryCancel hf
  right
  obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 3 (PTX.next t) = some t' ∧
      At t' Site.arriveTx.pc (facts L g ⟨.arriveTx, ap, cp, resp, x⟩) := by
    sched_seg (At.next h) hpre
  exact ⟨⟨.arriveTx, ap, cp, resp, x⟩, t', by simp [next], run_rtg hr, ht',
    ⟨hi.1, hi.2, hi.3⟩⟩

/-- The arrival on the CLC barrier, expecting the response. -/
theorem step_arriveTx {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .arriveTx) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    sched_cont L g d e u := by
  obtain ⟨s, ap, cp, resp, x⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_9)
  obtain rfl := fires_next (by exact trivial) hf
  right
  obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 1 (PTX.next t) = some t' ∧
      At t' Site.clcWait.pc (facts L g ⟨.clcWait, ap, cp, resp, x⟩) := by
    sched_seg (At.next h) hpre
  exact ⟨⟨.clcWait, ap, cp, resp, x⟩, t', by simp [next], run_rtg hr, ht',
    ⟨hi.1, hi.2, hi.3⟩⟩

/-- The CLC response poll: a failed poll returns to it; a successful one flips the CLC parity
and reads the response. -/
theorem step_clcWait {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .clcWait) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    sched_cont L g d e u := by
  obtain ⟨s, ap, cp, resp, x⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_14)
  rw [← h.1] at hf
  obtain ⟨mb, parity, ok, sc, rfl, rfl⟩ := fires_wait hf
  have h1 := At.set (r := 996) (v := .pred ok) h
    (not_mem_factsFrom (live := Flow.live Site.clcWait.pc) (by table_decide))
  right
  cases ok with
  | false =>
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 2
        (PTX.next (setReg t 996 (.pred false))) = some t' ∧
        At t' Site.clcWait.pc (facts L g ⟨.clcWait, ap, cp, resp, x⟩) := by
      sched_seg h1 hpre
    exact ⟨⟨.clcWait, ap, cp, resp, x⟩, t', by simp [next], run_rtg hr, ht',
      ⟨hi.1, hi.2, hi.3⟩⟩
  | true =>
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 3
        (PTX.next (setReg t 996 (.pred true))) = some t' ∧
        At t' Site.clcLoad.pc (facts L g ⟨.clcLoad, ap, 1 - cp, resp, x⟩) := by
      sched_seg h1 hpre [flip_bits cp hi.2]
    exact ⟨⟨.clcLoad, ap, 1 - cp, resp, x⟩, t', by simp [next], run_rtg hr, ht',
      ⟨hi.1, show 1 - cp < 2 by omega, hi.3⟩⟩


/-- The response read: a response value reaches the status query. -/
theorem step_clcLoad {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}
    {t u : TState} {e : Event} (_hpre : Pre P L mem0) (hs : d.site = .clcLoad) (hi : Inv d)
    (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc (eventTmpl Prod L g t
      (.mem { kind := .load, space := some (.shared .cta), sem := .acquire,
              scope := some .cta, elem := .int .b 128, addr := ⟨.reg 640 32, 0⟩,
              dsts := [some 970] })) e (some u)) :
    (next L g d e = some none ∨
      ∃ d' t', next L g d e = some (some d') ∧
        Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧
          Inv d') ∨
    (next L g d e = none ∧ Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) u) := by
  obtain ⟨s, ap, cp, resp, x⟩ := d
  simp only at hs h hf hi ⊢
  subst hs
  obtain ⟨a, bs, rfl, rfl⟩ := fires_load rfl rfl hf
  have hr := Flow.response_step (K := kernel) (A := Prod) (L := L) (g := g) (bs := bs)
    (pc := Site.clcLoad.pc) (by decide) Flow.code_437 Flow.code_438 Flow.code_439 h.1 h.2.1
    h.2.2.1 h.2.2.2.1 prod_noUnpack128 prod_noPack128
  cases hq : Flow.responseOf bs with
  | none => exact .inr ⟨by simp [next, hq], hr.2 (Flow.responseOf_none.mp hq)⟩
  | some rr =>
    obtain ⟨t', hl, hpc, hsub, hacc, hf', hd, hframe⟩ := hr.1 rr (Flow.responseOf_some.mp hq)
    refine .inl (.inr ⟨⟨.clcStatus, ap, cp, .clc rr, x⟩, t', by simp [next, hq], hl,
      ⟨by rw [hpc]; rfl, hsub, hacc, hf', ?_⟩, ⟨hi.1, hi.2, hi.3⟩⟩)
    frame_fp h.2.2.2.2, hframe
    refine ⟨?_, trivial⟩
    rw [hd]
    simp only [valueOf, values, List.lookup_cons, Nat.reduceBEq, Option.getD_some]

/-- The status query: a cancelling response reaches the first-CTA query, any other the fence. -/
theorem step_clcStatus {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}
    {t u : TState} {e : Event} (hpre : Pre P L mem0) (hs : d.site = .clcStatus) (hi : Inv d)
    (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc (eventTmpl Prod L g t
      (.clcQuery .isCanceled 997 (.reg 971))) e (some u)) :
    sched_cont L g d e u := by
  obtain ⟨s, ap, cp, resp, x⟩ := d
  simp only at hs h hf ⊢
  subst hs
  obtain ⟨r, v, hr, hq, rfl, rfl⟩ := fires_clcQuery hf
  have hresp := resp_of (d := ⟨.clcStatus, ap, cp, resp, x⟩) h
    (show 971 ∈ Flow.live Site.clcStatus.pc by table_decide) hr
  simp only at hresp
  subst hresp
  simp only [clcQueryValue] at hq
  cases hq
  right
  have h1 := At.set (r := 997) (v := .pred r.firstCta.isSome) h
    (facts_set (show 997 ∉ Flow.live Site.clcStatus.pc by table_decide))
  have hix : Inv ⟨.clcFirst, ap, cp, .clc r, Loader.none32⟩ :=
    ⟨hi.1, hi.2, by show Loader.none32 < 2 ^ 32; decide⟩
  cases hc : r.firstCta with
  | some c =>
    rw [hc] at h1
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 3
        (PTX.next (setReg t 997 (.pred true))) = some t' ∧
        At t' Site.clcFirst.pc (facts L g ⟨.clcFirst, ap, cp, .clc r, Loader.none32⟩) := by
      sched_seg h1 hpre
    exact ⟨⟨.clcFirst, ap, cp, .clc r, Loader.none32⟩, t', by simp [next, hc], run_rtg hr',
      ht', hix⟩
  | none =>
    rw [hc] at h1
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 4
        (PTX.next (setReg t 997 (.pred false))) = some t' ∧
        At t' Site.clcFence.pc (facts L g ⟨.clcFence, ap, cp, .clc r, Loader.none32⟩) := by
      sched_seg h1 hpre
    exact ⟨⟨.clcFence, ap, cp, .clc r, Loader.none32⟩, t', by simp [next, hc], run_rtg hr',
      ht', ⟨hix.1, hix.2, hix.3⟩⟩

/-- The first-CTA query records the claimed CTA and reaches the fence. -/
theorem step_clcFirst {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}
    {t u : TState} {e : Event} (hpre : Pre P L mem0) (hs : d.site = .clcFirst) (hi : Inv d)
    (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc (eventTmpl Prod L g t
      (.clcQuery (.first .x) 641 (.reg 971))) e (some u)) :
    sched_cont L g d e u := by
  obtain ⟨s, ap, cp, resp, x⟩ := d
  simp only at hs h hf ⊢
  subst hs
  obtain ⟨r, v, hr, hq, rfl, rfl⟩ := fires_clcQuery hf
  have hresp := resp_of (d := ⟨.clcFirst, ap, cp, resp, x⟩) h
    (show 971 ∈ Flow.live Site.clcFirst.pc by table_decide) hr
  simp only at hresp
  subst hresp
  obtain ⟨⟨cx, cy, cz⟩, hc⟩ : ∃ c, r.firstCta = some c := by
    cases hc : r.firstCta with
    | none => simp [clcQueryValue, hc] at hq
    | some c => exact ⟨c, rfl⟩
  simp only [clcQueryValue, hc, pure, Except.pure] at hq
  cases hq
  right
  have hx : cx.toNat < 2 ^ 32 := cx.isLt
  have h0 : At t Site.clcFirst.pc (Flow.factsFrom ((Flow.live Site.clcFirst.pc).erase 641)
      (valueOf L g ⟨.clcFirst, ap, cp, .clc r, x⟩)) :=
    At.mono h (Flow.holds_factsFrom_mono (live := Flow.live Site.clcFirst.pc) h.2.2.2.2
      (by table_decide))
  have h1 := At.set (r := 641) (v := .bits 32 (BitVec.ofNat 64 cx.toNat)) h0
    (not_mem_factsFrom (by table_decide))
  obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 0
      (PTX.next (setReg t 641 (.bits 32 (BitVec.ofNat 64 cx.toNat)))) = some t' ∧
      At t' Site.clcFence.pc (facts L g ⟨.clcFence, ap, cp, .clc r, cx.toNat⟩) := by
    sched_seg h1 hpre [b32]
  exact ⟨⟨.clcFence, ap, cp, .clc r, cx.toNat⟩, t', by simp [next, hc], run_rtg hr', ht',
    ⟨hi.1, hi.2, hx⟩⟩

/-- The leader CTA's acknowledgement barrier, as `mapa` returns it. -/
abbrev ackPtr (L : Launch) (g : Nat) : Value :=
  .ptr 32 false (.shared (g / L.block) (2 * ((g / L.block) / 2)))
      (BitVec.ofNat 64 (L.sharedBase + 128))

/-- The fence reaches the acknowledgement. The `mapa` of the acknowledgement barrier to the
leader CTA is one local step: its result depends on the launch's cluster layout. -/
theorem step_clcFence {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}
    {t u : TState} {e : Event} (hpre : Pre P L mem0) (hg : g < L.threads) (hs : d.site = .clcFence)
    (hi : Inv d) (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc (eventTmpl Prod L g t (.fence (.proxy (.async (some (.shared .cta))))))
      e (some u)) :
    sched_cont L g d e u := by
  obtain ⟨s, ap, cp, resp, x⟩ := d
  simp only at hs h hf hi ⊢
  subst hs
  have hadv : AdvancesOp (.fence (.proxy (.async (some (.shared .cta))))) := trivial
  obtain rfl := fires_next hadv hf
  right
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hx : L.sharedBase + 128 < 2 ^ 32 := by omega
  obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel Prod L g 2 (PTX.next t) = some t1 ∧
      At t1 (Site.clcFence.pc + 3) [(643, b32 (L.sharedBase + 128)), (644, b32 0),
        (48, b32 10), (641, b32 x), (880, b32 cp), (881, b32 ap)] := by
    sched_seg (At.next h) hpre
  have hl : readSharedAddress L g t1 32 false true (.reg 643) =
      .ok ⟨.shared, g / L.block, L.sharedBase + 128⟩ :=
    readSharedAddress_bits (holds_mem ht1.2.2.2.2 List.mem_cons_self) (Or.inl rfl) hg
      (cta_lt hpre hg) hx
  have h598 : t1.regs 644 = some (b32 0) := holds_mem ht1.2.2.2.2 (by simp)
  have hr : readBits L g t1 32 (.reg 644) = .ok 0 := by
    simp [readBits, readReg, h598, b32, truncBits, bind, Except.bind, pure, Except.pure]
  have hr2 : run kernel Prod L g 1 t1 = some (PTX.next (setReg t1 645 (ackPtr L g))) :=
    run_local (A := Prod) (L := L) (g := g) Flow.code_447 rfl ht1
      (exec_mapa hl hr (map_zero hpre hg _)
        (hL := prod_localRule_none (by simp [Assumption.FloatForm.ofOp]) L g t1))
  have ht2 := At.set (r := 645) (v := ackPtr L g) ht1 (by simp)
  obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 2
      (PTX.next (setReg t1 645 (ackPtr L g))) = some t3 ∧
      At t3 Site.ack.pc (facts L g ⟨.ack, ap, cp, resp, x⟩) := by
    sched_seg ht2 hpre
  exact ⟨⟨.ack, ap, cp, resp, x⟩, t3, by simp [next], run_rtg (run_comp (run_comp hr1 hr2) hr3),
    ht3, ⟨hi.1, hi.2, hi.3⟩⟩


/-- The acknowledgement: with no claimed CTA the thread leaves through the exit; otherwise the
rank branch of the next task's loop head follows. -/
theorem step_ack {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .ack) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    sched_cont L g d e u := by
  obtain ⟨s, ap, cp, resp, x⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_10)
  obtain rfl := fires_next (by exact trivial) hf
  right
  have h1 := At.next h
  by_cases hnone : x = Loader.none32
  · subst hnone
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 3 (PTX.next t) = some t' ∧
        At t' Site.exitArrive.pc (facts L g ⟨.exitArrive, ap, cp, resp, Loader.none32⟩) := by
      sched_seg h1 hpre
    exact ⟨⟨.exitArrive, ap, cp, resp, Loader.none32⟩, t', by simp [next], run_rtg hr, ht',
      ⟨hi.1, hi.2, hi.3⟩⟩
  · have hx : x < 2 ^ 32 := hi.3
    obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel Prod L g 1 (PTX.next t) = some t1 ∧
        At t1 Flow.bra_452 [(24, .pred (decide (x = Loader.none32))), (48, b32 10),
          (880, b32 cp), (881, b32 ap)] := by
      sched_seg h1 hpre
    obtain ⟨u2, hr2, hu2⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_452
      (decide (x = Loader.none32)) ht1 (holds_mem ht1.2.2.2.2 List.mem_cons_self)
      (prod_localRule_bra L g _ _ _)
    rw [show decide (x = Loader.none32) = false by simp [hnone]] at hu2
    simp only [Bool.false_eq_true, ↓reduceIte] at hu2
    obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 3 u2 = some t3 ∧
        At t3 Flow.bra_415 [(23, .pred (decide ((g / L.block) % 2 ≠ 0))), (48, b32 10),
          (880, b32 cp), (881, b32 ap)] := by
      sched_seg hu2 hpre [sregValue, rank_test hpre.oneDimLaunch.1 hpre.cluster]
    obtain ⟨k, t', hk, ht'⟩ := loop_head (d := ⟨.ack, ap, cp, resp, x⟩) hpre ht3
    exact ⟨⟨loopHead L g, ap, cp, resp, x⟩, t', by simp [next, hnone],
      run_rtg (run_comp (run_comp (run_comp hr1 hr2) hr3) hk), ht', ⟨hi.1, hi.2, hi.3⟩⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof.Scheduler
