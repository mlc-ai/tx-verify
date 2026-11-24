-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOutFacts
public import Kernels.Fp16Gemm8192.Proof.Thread.ClusterOpsStep
public import Kernels.Fp16Gemm8192.Proof.Thread.RegStep
public import Kernels.Fp16Gemm8192.Proof.Thread.TmemStep
public import Lemmas.Flow.EndSite

@[expose] public section

/-! # Each thread's cluster barrier arrivals

Every thread arrives on the cluster barrier twice: in the prologue, and at its role's exit
(decided on the code). Along a thread's run its arrivals count its state's phase
(`ThreadD.clPhase`): none before the prologue's arrival, one until the exit's arrival, two
after it (`clusterInv`). The same run invariant counts a thread's cluster operations (`clOps`,
`Thread/ClusterOps.lean`), its register requests (`regOps`):
one, right after the prologue's cluster wait (`reg_step`), and its paired Tensor Memory
operations (`tmemOps`, `tmem_step`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- Whether an instruction arrives on the cluster barrier. -/
def clArriveOp : Op → Bool
  | .cluster (.arrive ..) => true
  | _ => false

/-- The kernel's cluster arrivals are at its two cluster arrival sites (decided on the code). -/
theorem kernel_clArrive_pcs : OpPcs kernel.code clArriveOp Flow.clusterArrive.toList = true :=
  OpPcsFast.opPcs (by decide +kernel)

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- A cluster arrival fires at the prologue's arrival or a role's exit arrival. -/
theorem clArrive_site {d : ThreadD} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[(code L g).pc d]? = some ins)
    (hf : Fires ((code L g).pc d) (eventTmpl Prod L g t ins.op) e o) (h : isClArrive e = true) :
    (code L g).pc d = Flow.clusterArrive_0 ∨ (code L g).pc d = Flow.clusterArrive_1 := by
  unfold isClArrive at h
  split at h
  · rename_i rel al hk
    have hop := fires_cluster_op hf hk
    have hpc := OpPcs.mem kernel_clArrive_pcs hc (by rw [hop]; rfl)
    simpa [Flow.clusterArrive] using hpc
  · cases h

set_option hygiene false in
/-- One role's cluster phase step, for `cluster_step`: its next state `d''` (from `nextOf`) keeps
the phase at a non-arrival, and an arrival steps it by one. `fl` and `tl` unfold the role's `next`
at a non-arrival and at an arrival, and `pcs` is the role's site pc (with hygiene off, the names
are those of `cluster_step`). -/
macro "cl_phase_role " nextOf:ident " [" fl:Lean.Parser.Tactic.simpLemma,*
  "]" " [" tl:Lean.Parser.Tactic.simpLemma,* "]" pcs:Lean.Parser.Tactic.simpLemma : tactic =>
  `(tactic| (
  obtain ⟨d'', hn', rfl⟩ := $nextOf hn
  change kernel.code[site.pc]? = some ins at hc
  change isClArrive e = true → site.pc = Flow.clusterArrive_0 ∨ site.pc = Flow.clusterArrive_1 at hA
  cases ha : isClArrive e
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    cases site
    case exitArrive =>
      exfalso
      code_at hc
      subst hc
      simp [isClArrive, harr _ rfl] at ha
    all_goals simp only [$fl,*] at hn'
    all_goals clear hc hf harr hA
    clc_sweep hn'
    all_goals simp only [ThreadD.clPhase] at hq ⊢
  · have hp := hA ha
    cases site
    case exitArrive =>
      code_at hc
      subst hc
      simp only [$tl,*] at hn'
      subst hn'
      simp [ThreadD.clPhase] at hq ⊢
    all_goals exfalso
    all_goals clear * - hp
    all_goals revert hp
    all_goals simp only [$pcs]
    all_goals decide +revert))

set_option maxHeartbeats 8000000 in
theorem cluster_step {d d' : ThreadD} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    {pre : List Event} (hc : kernel.code[(code L g).pc d]? = some ins)
    (hf : Fires ((code L g).pc d) (eventTmpl Prod L g t ins.op) e o)
    (hn : (code L g).next d e = some (some d')) (hq : clArrives pre = d.clPhase) :
    clArrives (pre ++ [e]) = d'.clPhase := by
  have hA := clArrive_site hc hf
  have hsnoc : clArrives (pre ++ [e]) = clArrives pre + (if isClArrive e then 1 else 0) := by
    simp [clArrives, List.countP_append]
  rw [hsnoc, hq]
  -- at an arrival site the event is the arrival
  have harr : ∀ (cop : ClusterOp), ins.op = .cluster cop → e.kind = .cluster cop := by
    intro cop hop
    rw [hop] at hf
    simp only [eventTmpl, Fires] at hf
    rw [hf.1]
  rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
      ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
  · change Prologue.next L g ⟨site, w⟩ e = some (some d') at hn
    change kernel.code[site.pc]? = some ins at hc
    change isClArrive e = true → site.pc = Flow.clusterArrive_0 ∨ site.pc =
      Flow.clusterArrive_1 at hA
    cases ha : isClArrive e
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      cases site
      case arrive =>
        exfalso
        code_at hc
        subst hc
        simp [isClArrive, harr _ rfl] at ha
      all_goals simp only [Prologue.next, Prologue.afterInits, Prologue.afterElect,
        Prologue.consStart, Prologue.schedStart, Prologue.mmaStart, Prologue.loaderStart,
        Prologue.loaderIdle] at hn
      all_goals clear hc hf harr hA
      clc_sweep hn
      all_goals simp only [ThreadD.clPhase] at hq ⊢
    · have hp := hA ha
      cases site
      case arrive =>
        code_at hc
        subst hc
        simp only [Prologue.next, Option.some.injEq] at hn
        subst hn
        simp [ThreadD.clPhase] at hq ⊢
      all_goals exfalso
      all_goals clear * - hp
      all_goals revert hp
      all_goals simp only [Prologue.Site.pc]
      all_goals decide +revert
  · cl_phase_role next_of_loader [Loader.next, Loader.endOfTrip] [Loader.next,
    Option.some.injEq] Loader.Site.pc
  · cl_phase_role next_of_mma [Mma.next, Mma.endOfTrip] [Mma.next, Option.some.injEq] Mma.Site.pc
  · cl_phase_role next_of_sched [Scheduler.next, Scheduler.loopHead] [Scheduler.next,
    Option.some.injEq] Scheduler.Site.pc
  · cl_phase_role next_of_cons [Consumer.next] [Consumer.next, Option.some.injEq] Consumer.Site.pc

theorem ExitWaited.snoc {es : List Event} (h : ExitWaited es) (e : Event) :
    ExitWaited (es ++ [e]) := by
  obtain ⟨j, pc, al, hj, hc⟩ := h
  have hl : j < es.length := (List.getElem?_eq_some_iff.mp hj).1
  refine ⟨j, pc, al, by rw [List.getElem?_append_left hl]; exact hj, ?_⟩
  rw [List.take_append_of_le_length hl.le]
  exact hc

set_option hygiene false in
/-- One role's exit wait step, for `waited_step`: its next state `d''` (from `nextOf`) is an exit
only after the role's exit wait, and `fl` unfolds the role's `next` at the other sites. -/
macro "wt_role " nextOf:ident " [" fl:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  obtain ⟨d'', hn', rfl⟩ := $nextOf hn
  change kernel.code[site.pc]? = some ins at hc
  cases site
  case exitWait =>
    code_at hc
    subst hc
    exact hwait _ rfl rfl
  all_goals exfalso
  all_goals clear hc hf hwait hw hq
  all_goals simp only [$fl,*] at hn'
  clc_sweep hn'
  all_goals simp_all [ThreadD.afterWait]))

set_option maxHeartbeats 8000000 in
theorem waited_step {d d' : ThreadD} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    {pre : List Event} (hc : kernel.code[(code L g).pc d]? = some ins)
    (hf : Fires ((code L g).pc d) (eventTmpl Prod L g t ins.op) e o)
    (hn : (code L g).next d e = some (some d')) (hq : clArrives pre = d.clPhase)
    (hw : d.afterWait → ExitWaited pre) : d'.afterWait → ExitWaited (pre ++ [e]) := by
  intro hd'
  have hwait : ∀ (al : Bool), ins.op = .cluster (.wait al) → d.clPhase = 2 →
      ExitWaited (pre ++ [e]) := by
    intro al hop hph
    rw [hop] at hf
    simp only [eventTmpl, Fires] at hf
    refine ⟨pre.length, e.pc, al, ?_, ?_⟩
    · rw [List.getElem?_append_right (le_refl _), Nat.sub_self, hf.1]
      rfl
    · rw [List.take_left' rfl, hq, hph]
  by_cases hp : d.afterWait
  · exact (hw hp).snoc e
  rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
      ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
  · change Prologue.next L g ⟨site, w⟩ e = some (some d') at hn
    exfalso
    clear hc hf hwait hw hq hp
    rcases d' with p' | (l' | m' | s' | c')
    · exact hd'
    · rcases Prologue.next_loader hn with rfl | rfl <;>
        simp [ThreadD.afterWait, Prologue.loaderStart, Prologue.loaderIdle] at hd'
    · rcases Prologue.next_mma hn with h | h <;> simp [ThreadD.afterWait, h] at hd'
    · rw [Prologue.next_sched hn] at hd'
      simp [ThreadD.afterWait, Prologue.schedStart] at hd'
    · rw [Prologue.next_cons hn] at hd'
      simp [ThreadD.afterWait, Prologue.consStart] at hd'
  · wt_role next_of_loader [Loader.next, Loader.endOfTrip]
  · wt_role next_of_mma [Mma.next, Mma.endOfTrip]
  · wt_role next_of_sched [Scheduler.next, Scheduler.loopHead]
  · wt_role next_of_cons [Consumer.next]

/-- A cluster arrival releases, at the prologue's arrival or a role's exit arrival. -/
theorem arrive_facts {d : ThreadD} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[(code L g).pc d]? = some ins)
    (hf : Fires ((code L g).pc d) (eventTmpl Prod L g t ins.op) e o) {rel al : Bool}
    (hk : e.kind = .cluster (.arrive rel al)) : rel = true ∧ d.clPhase ≤ 1 := by
  have hp := clArrive_site hc hf (by simp [isClArrive, hk])
  have hop := fires_cluster_op hf hk
  refine ⟨?_, ?_⟩
  · rcases hp with hp | hp <;> rw [hp] at hc
    · rw [Flow.code_clusterArrive_0] at hc
      cases hc
      simp only [Op.cluster.injEq, ClusterOp.arrive.injEq] at hop
      exact hop.1.symm
    · rw [Flow.code_clusterArrive_1] at hc
      cases hc
      simp only [Op.cluster.injEq, ClusterOp.arrive.injEq] at hop
      exact hop.1.symm
  · clear hc hf hk hop
    rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
        ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
    all_goals change site.pc = _ ∨ site.pc = _ at hp
    all_goals (cases site <;> first
      | (simp [ThreadD.clPhase]; done)
      | (exfalso; clear * - hp; revert hp; decide +revert))

/-- An exit is at a role's exit site, after its exit wait. -/
theorem exit_facts {d : ThreadD} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[(code L g).pc d]? = some ins)
    (hf : Fires ((code L g).pc d) (eventTmpl Prod L g t ins.op) e o) (hk : e.kind = .exit) :
    d.clPhase = 2 ∧ d.afterWait := by
  have hp := ret_pc hc (fires_exit_op hf hk)
  clear hc hf hk
  rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
      ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
  all_goals change site.pc ∈ _ at hp
  all_goals (cases site <;> first
    | (simp [ThreadD.clPhase, ThreadD.afterWait]; done)
    | (exfalso; clear * - hp; revert hp; decide +revert))

/-- The cluster counts, the register requests and the paired Tensor Memory operations along a
thread's run (`w0`: whether the thread is in warp 0). -/
def ClInv (w0 : Bool) (d : ThreadD) (es : List Event) : Prop :=
  clArrives es = d.clPhase ∧ (d.afterWait → ExitWaited es) ∧ clOps es = d.clOps ∧
    regOps es = d.regOps ∧ TmemInv w0 d es

theorem clusterInv (hpre : Pre P L mem0) (hg : g < L.threads) {es : List Event}
    (htr : (code L g).toMachine.Trace (some (code L g).init) es) :
    ∀ j d, (code L g).toMachine.after (some (code L g).init) (es.take j) = some (some d) →
      ClInv (decide (g % L.block / 32 = 0)) d (es.take j) := by
  refine Code.run_inv (sound hpre hg) htr (ClInv (decide (g % L.block / 32 = 0)))
    ⟨rfl, fun h => h.elim, rfl, rfl, fun _ => rfl, fun _ => rfl⟩ ?_
  intro d d' pre e t ins o hq hat hinv hc hf hn
  exact ⟨cluster_step hc hf hn hq.1, waited_step hc hf hn hq.1 hq.2.1, clOp_step hc hf hn hq.2.2.1,
    reg_step hc hf hn hq.2.2.2.1, tmem_step hat hc hf hn hq.2.2.2.2⟩

/-- A thread's register requests along an execution count its state's. -/
theorem reg_ops_facts {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {k : Nat} {d : ThreadD}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) = some (some d)) :
    regOps ((X.tr g).take k) = d.regOps :=
  (clusterInv hpre hg (Frame.trace (fun _ => sound hpre) hX hg) k _ hσ).2.2.2.1

/-- A thread's cluster barrier events along an execution: its arrivals so far count its state's
phase; an arrival releases and is its first or second; an exit follows its exit wait, after its
second arrival. -/
theorem cluster_facts {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {e : Event} (he : X.get (g, k) = some e) {d : ThreadD}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) = some (some d)) :
    clArrives ((X.tr g).take k) = d.clPhase ∧
    (∀ rel al, e.kind = .cluster (.arrive rel al) → rel = true ∧ d.clPhase ≤ 1) ∧
    (e.kind = .exit → d.clPhase = 2 ∧ ExitWaited ((X.tr g).take k)) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hi := clusterInv hpre hg htr k _ hσ
  refine ⟨hi.1, fun rel al hk => arrive_facts hc hfire hk, fun hk => ?_⟩
  obtain ⟨h1, h2⟩ := exit_facts hc hfire hk
  exact ⟨h1, hi.2.1 h2⟩

/-- A state after its exit wait has made all four cluster operations. -/
theorem afterWait_clOps {d : ThreadD} (h : d.afterWait) : d.clOps = 4 := by
  rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
      ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
  all_goals (cases site <;> simp_all [ThreadD.afterWait, ThreadD.clOps])

/-- A state at a cluster operation is at that operation's site. -/
theorem pc_of_atCluster {d : ThreadD} (h : d.AtCluster) :
    (code L g).pc d = (clEvent d.clOps).pc := by
  rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
      ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
  all_goals simp only [ThreadD.AtCluster] at h
  all_goals rcases h with rfl | rfl <;> rfl

/-- The `n`-th cluster operation is the operation at its site. -/
theorem code_clEvent (n : Nat) : ∃ op, clEvent n = ⟨(clEvent n).pc, .cluster op⟩ ∧
    kernel.code[(clEvent n).pc]? = some ⟨none, .cluster op⟩ := by
  rcases n with _ | _ | _ | n
  · exact ⟨_, rfl, Flow.code_clusterArrive_0⟩
  · exact ⟨_, rfl, Flow.code_clusterWait_0⟩
  · exact ⟨_, rfl, Flow.code_clusterArrive_1⟩
  · exact ⟨_, rfl, Flow.code_clusterWait_1⟩

/-- **A thread at a cluster operation can perform it.** -/
theorem cluster_fire (hpre : Pre P L mem0) (hg : g < L.threads) {es : List Event} {d : ThreadD}
    {t : TState} (hσ : (code L g).toMachine.after (some (code L g).init) es = some (some d))
    (hat : d.AtCluster) (hr : Run kernel Prod L g {} es (some t)) :
    ∃ t1 u, Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 (clEvent d.clOps) (some u) := by
  obtain ⟨t1, hl, hgood⟩ := Code.end_site (sound hpre hg) hr hσ
  have hout := Code.site_out (sound hpre hg) hgood
  obtain ⟨op, hev, hc⟩ := code_clEvent d.clOps
  have hpc := pc_of_atCluster (L := L) (g := g) hat
  rw [Code.tmpl, hpc, hc] at hout
  dsimp only at hout
  have htpc : t1.pc = (clEvent d.clOps).pc := hgood.1.1.trans hpc
  refine ⟨t1, next t1, hl, _, hout, ?_⟩
  rw [htpc, hev]
  exact ⟨rfl, rfl⟩

/-- A thread's cluster operations along an execution: they count its state's operations; an
operation is the state's count's operation, at a cluster site; an exit follows all four. -/
theorem clOps_facts {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {d : ThreadD}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) = some (some d)) :
    clOps ((X.tr g).take k) = d.clOps ∧ ∀ e, X.get (g, k) = some e →
      (isCluster e = true → e = clEvent d.clOps ∧ d.AtCluster) ∧ (e.kind = .exit → d.clOps = 4) :=
        by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  refine ⟨(clusterInv hpre hg htr k _ hσ).2.2.1, fun e he => ?_⟩
  obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  exact ⟨fun h => clOp_event hc hfire h, fun hk => afterWait_clOps (exit_facts hc hfire hk).2⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof
