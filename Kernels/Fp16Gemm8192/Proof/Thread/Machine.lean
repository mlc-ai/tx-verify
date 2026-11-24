-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.PrologueDispatch
public import Kernels.Fp16Gemm8192.Proof.Thread.PrologueEntry
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderWait
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderSteps
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderTask
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderClc
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaSteps
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaEvents
public import Kernels.Fp16Gemm8192.Proof.Thread.SchedulerSteps
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerStart
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEntry
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEpilogue

@[expose] public section

/-! # A thread of the kernel as a site machine

Every thread runs the prologue and is then followed in its role (loader, MMA, scheduler or
consumer) through its tasks to the exit; a value a role cannot use makes the thread fault,
and the machine stops (`none`). The
machine's obligations (`Flow.Code.Sound`) are the step lemmas of the prologue and the
loader; `Flow.Code.Sound.machine` turns them into a simulation of the thread's code. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000


namespace Loader

/-- The cluster arrival of the exit. -/
theorem step_exitArrive {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .exitArrive) (hi : Inv d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    ∃ d' t', next L g d e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧
        Inv d' := by
  obtain ⟨s, m, n, q, cp, r, x⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterArrive_1)
  obtain rfl := fires_next (show AdvancesOp (.cluster _) from trivial) hf
  refine ⟨⟨.exitWait, m, n, q, cp, r, x⟩, _, by simp [next], .refl, ?_,
    ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6⟩⟩
  exact At.mono (At.next h) (Flow.holds_factsFrom_mono (live := Flow.live Site.exitArrive.pc)
    (live' := Flow.live Site.exitWait.pc) h.2.2.2.2 (by table_decide))

set_option maxHeartbeats 10000000 in
/-- The cluster wait of the exit, then the branch past warp 0's deallocation. -/
theorem step_exitWait {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .exitWait) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    ∃ d' t', next L g d e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧
        Inv d' := by
  obtain ⟨s, m, n, q, cp, r, x⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_1)
  obtain rfl := fires_next (show AdvancesOp (.cluster _) from trivial) hf
  obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 1 (PTX.next t) = some t' ∧
      At t' Site.exit.pc (facts L g ⟨.exit, m, n, q, cp, r, x⟩) := by
    loader_seg (At.next h) hpre
  exact ⟨⟨.exit, m, n, q, cp, r, x⟩, t', by simp [next], run_rtg hr, ht',
    ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6⟩⟩

/-- Each loader site is an event instruction whose guard holds. -/
theorem site_ok {L : Launch} {g : Nat} (d : D) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (facts L g d) ins.guard := by
  obtain ⟨s, m, n, q, cp, r, x⟩ := d
  cases s with
  | wait b =>
    obtain ⟨base, par, hc⟩ := code_wait b
    exact ⟨_, hc, rfl, trivial⟩
  | load b j =>
    obtain ⟨ins, hc, hg, -, hl⟩ := code_advances ⟨.load b j, b, j, .inl rfl⟩
    exact ⟨ins, hc, hl, by simp [hg, Code.GuardTrue]⟩
  | arrive b =>
    obtain ⟨ins, hc, hg, -, hl⟩ := code_advances ⟨.arrive b, b, 0, .inr rfl⟩
    exact ⟨ins, hc, hl, by simp [hg, Code.GuardTrue]⟩
  | clcWait =>
    obtain ⟨base, par, hc⟩ := code_taskWait .clcWait (.inl rfl)
    exact ⟨_, hc, rfl, trivial⟩
  | drain i =>
    obtain ⟨base, par, hc⟩ := code_taskWait (.drain i) (.inr ⟨i, rfl⟩)
    exact ⟨_, hc, rfl, trivial⟩
  | clcLoad => exact ⟨_, Flow.code_loadAcquire_0, rfl, trivial⟩
  | clcStatus => exact ⟨_, Flow.code_clcQuery_0, rfl, trivial⟩
  | clcFirst =>
    refine ⟨_, Flow.code_clcQuery_1, rfl, ?_⟩
    have hm := Flow.mem_factsFrom (val := valueOf L g ⟨.clcFirst, m, n, q, cp, r, x⟩)
      (show 988 ∈ Flow.live Site.clcFirst.pc by table_decide)
    have hv : valueOf L g ⟨.clcFirst, m, n, q, cp, r, x⟩ 988 = .pred true := by
      simp only [valueOf, extra, List.lookup_cons, Nat.reduceBEq, Option.getD_some]
      simp
    show (988, Value.pred true) ∈ facts L g ⟨.clcFirst, m, n, q, cp, r, x⟩
    exact hv ▸ hm
  | clcFence => exact ⟨_, Flow.code_fenceProxy_1, rfl, trivial⟩
  | ack =>
    refine ⟨_, Flow.code_mbarArrive_8, rfl, ?_⟩
    have hm := Flow.mem_factsFrom (val := valueOf L g ⟨.ack, m, n, q, cp, r, x⟩)
      (show 989 ∈ Flow.live Site.ack.pc by table_decide)
    have hv : valueOf L g ⟨.ack, m, n, q, cp, r, x⟩ 989 = .pred true := by
      simp only [valueOf, extra, List.lookup_cons, Nat.reduceBEq, Option.getD_some]
    show (989, Value.pred true) ∈ facts L g ⟨.ack, m, n, q, cp, r, x⟩
    exact hv ▸ hm
  | exitArrive => exact ⟨_, Flow.code_clusterArrive_1, rfl, trivial⟩
  | exitWait => exact ⟨_, Flow.code_clusterWait_1, rfl, trivial⟩
  | exit => exact ⟨_, Flow.code_exit_0, rfl, trivial⟩

end Loader

namespace Prologue

/-- Each prologue site is an unguarded event instruction. -/
theorem site_ok (s : Site) :
    ∃ ins, kernel.code[s.pc]? = some ins ∧ ins.op.isLocal = false ∧ ins.guard = none := by
  cases s with
  | shfl => exact ⟨_, Flow.code_shfl_0, rfl, rfl⟩
  | elect => exact ⟨_, Flow.code_elect_0, rfl, rfl⟩
  | init i =>
    fin_cases i
    all_goals first
      | exact ⟨_, Flow.code_mbarInit_0, rfl, rfl⟩ | exact ⟨_, Flow.code_mbarInit_1, rfl, rfl⟩
      | exact ⟨_, Flow.code_mbarInit_2, rfl, rfl⟩ | exact ⟨_, Flow.code_mbarInit_3, rfl, rfl⟩
      | exact ⟨_, Flow.code_mbarInit_4, rfl, rfl⟩ | exact ⟨_, Flow.code_mbarInit_5, rfl, rfl⟩
      | exact ⟨_, Flow.code_mbarInit_6, rfl, rfl⟩ | exact ⟨_, Flow.code_mbarInit_7, rfl, rfl⟩
      | exact ⟨_, Flow.code_mbarInit_8, rfl, rfl⟩ | exact ⟨_, Flow.code_mbarInit_9, rfl, rfl⟩
      | exact ⟨_, Flow.code_mbarInit_10, rfl, rfl⟩ | exact ⟨_, Flow.code_mbarInit_11, rfl, rfl⟩
      | exact ⟨_, Flow.code_mbarInit_12, rfl, rfl⟩ | exact ⟨_, Flow.code_mbarInit_13, rfl, rfl⟩
      | exact ⟨_, Flow.code_mbarInit_14, rfl, rfl⟩ | exact ⟨_, Flow.code_mbarInit_15, rfl, rfl⟩
      | exact ⟨_, Flow.code_mbarInit_16, rfl, rfl⟩ | exact ⟨_, Flow.code_mbarInit_17, rfl, rfl⟩
  | alloc => exact ⟨_, Flow.code_tmemAlloc_0, rfl, rfl⟩
  | allocWrite => exact ⟨_, Flow.code_tmemAlloc_0, rfl, rfl⟩
  | warpBar => exact ⟨_, Flow.code_warpBar_0, rfl, rfl⟩
  | fence => exact ⟨_, Flow.code_fenceProxy_0, rfl, rfl⟩
  | fenceInit => exact ⟨_, Flow.code_fenceMbarInit_0, rfl, rfl⟩
  | arrive => exact ⟨_, Flow.code_clusterArrive_0, rfl, rfl⟩
  | wait => exact ⟨_, Flow.code_clusterWait_0, rfl, rfl⟩
  | setMaxReg => exact ⟨_, Flow.code_setMaxReg_0, rfl, rfl⟩
  | roleElect => exact ⟨_, Flow.code_elect_1, rfl, rfl⟩

end Prologue

namespace Loader

/-- A loader arrives on a full barrier only on its cluster's leader CTA. -/
def ArriveLead (L : Launch) (g : Nat) (d : D) : Prop := ∀ b, d.site = .arrive b → leader L g = true

theorem next_arriveLead {L : Launch} {g : Nat} {d d' : D} {e : Event} (hal : ArriveLead L g d)
    (hn : next L g d e = some (some d')) : ArriveLead L g d' := by
  intro b hb
  obtain ⟨s, m, n, q, cp, r, x⟩ := d
  unfold next at hn
  repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try (unfold endOfTrip at hn; split_ifs at hn))
  all_goals (try subst hn)
  all_goals (try (simp only [Option.map_eq_some_iff, Option.some.injEq] at hn; obtain ⟨_, -, rfl⟩ :=
    hn))
  all_goals simp_all

end Loader

namespace Mma

/-- The MMA thread resets its K block before releasing the response and keeps it until the
first full poll. -/
def QReset (d : D) : Prop := (d.site = .ack ∨ d.site = .accWait) → d.q = 0

theorem next_qReset {L : Launch} {g : Nat} {d d' : D} {e : Event} (hq : QReset d)
    (hn : next L g d e = some (some d')) : QReset d' := by
  unfold QReset at hq ⊢
  intro hs'
  unfold next at hn
  split at hn
  all_goals try (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
  all_goals (repeat' (first | split_ifs at hn | split at hn))
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try (unfold endOfTrip at hn; split_ifs at hn))
  all_goals (try subst hn)
  all_goals (try (simp only [Option.map_eq_some_iff, Option.some.injEq] at hn; obtain ⟨_, -, rfl⟩ :=
    hn))
  all_goals simp_all

/-- Outside the common exit, an MMA thread runs on its cluster's leader CTA. -/
def Lead (L : Launch) (g : Nat) (d : D) : Prop :=
  d.site = .exitArrive ∨ d.site = .exitWait ∨ d.site = .exit ∨ g / L.block % 2 = 0

theorem next_lead {L : Launch} {g : Nat} {d d' : D} {e : Event} (hl : Lead L g d)
    (hn : next L g d e = some (some d')) : Lead L g d' := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := d
  rcases hl with h | h | h | h
  · simp only at h
    subst h
    simp only [next, Option.some.injEq] at hn
    subst hn
    exact .inr (.inl rfl)
  · simp only at h
    subst h
    simp only [next, Option.some.injEq] at hn
    subst hn
    exact .inr (.inr (.inl rfl))
  · simp only at h
    subst h
    simp [next] at hn
  · exact .inr (.inr (.inr h))

end Mma

namespace Scheduler

/-- The scheduler's acknowledgement poll and cancellation request run on its cluster's leader
CTA only (`loopHead`). -/
def Lead (L : Launch) (g : Nat) (d : D) : Prop :=
  d.site = .ackWait ∨ d.site = .tryCancel → Loader.leader L g = true

theorem next_lead {L : Launch} {g : Nat} {d d' : D} {e : Event} (hl : Lead L g d)
    (hn : next L g d e = some (some d')) : Lead L g d' := by
  intro hs
  obtain ⟨site, ap, cp, r, x⟩ := d
  cases site
  all_goals simp only [next] at hn
  all_goals repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try (simp only [Option.map_eq_some_iff, Option.some.injEq] at hn; obtain ⟨_, -, rfl⟩ :=
    hn))
  all_goals (try subst hn)
  all_goals (try simp only [loopHead] at hs)
  all_goals (try split at hs)
  all_goals simp_all [Lead]

end Scheduler

/-- Only a group's first consumer thread acknowledges the CLC response (`Consumer.next` at
`.clcBar`). -/
def Consumer.AckFirst (L : Launch) (g : Nat) (d : Consumer.D) : Prop :=
  d.site = .ack → Consumer.first L g = true

theorem Consumer.next_ackFirst {L : Launch} {g : Nat} {d d' : Consumer.D} {e : Event}
    (hn : Consumer.next L g d e = some (some d')) : Consumer.AckFirst L g d' := by
  intro hs
  obtain ⟨site, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases site
  all_goals simp only [Consumer.next] at hn
  all_goals repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try (simp only [Option.map_eq_some_iff, Option.some.injEq] at hn; obtain ⟨_, -, rfl⟩ :=
    hn))
  all_goals (try subst hn)
  all_goals simp_all

/-- The prologue enters the scheduler at its start. -/
theorem Prologue.next_sched {L : Launch} {g : Nat} {p : Prologue.D} {e : Event}
    {sd : Scheduler.D} (hn : Prologue.next L g p e = some (some (.inr (.sched sd)))) :
    sd = Prologue.schedStart := by
  unfold Prologue.next at hn
  repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq, Sum.inr.injEq,
    Prologue.Role.sched.injEq] at hn)
  all_goals (try subst hn)
  all_goals simp_all [Prologue.schedStart]

/-- The prologue enters the consumers at their start. -/
theorem Prologue.next_cons {L : Launch} {g : Nat} {p : Prologue.D} {e : Event} {c : Consumer.D}
    (hn : Prologue.next L g p e = some (some (.inr (.cons c)))) : c = Prologue.consStart := by
  unfold Prologue.next at hn
  repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq, Sum.inr.injEq,
    Prologue.Role.cons.injEq] at hn)
  all_goals (try subst hn)
  all_goals simp_all [Prologue.consStart]

/-- A thread's abstract states: the prologue, then its role. -/
abbrev ThreadD := Prologue.D ⊕ Prologue.Role

/-- A thread of the kernel as a code machine. Reducible, so that its states are `ThreadD` to
`simp`: the layers above speak of a thread's state through `Frame.stateAt (code L)`. -/
@[reducible] def code (L : Launch) (g : Nat) : Flow.Code kernel Prod L g where
  D := ThreadD
  init := .inl ⟨.shfl, 0⟩
  pc := fun
    | .inl p => p.site.pc
    | .inr (.loader l) => l.site.pc
    | .inr (.mma m) => m.site.pc
    | .inr (.sched s) => s.site.pc
    | .inr (.cons c) => c.site.pc
  facts := fun
    | .inl p => Prologue.facts L g p
    | .inr (.loader l) => Loader.facts L g l
    | .inr (.mma m) => Mma.facts L g m
    | .inr (.sched s) => Scheduler.facts L g s
    | .inr (.cons c) => Consumer.facts L g c
  sub := fun | .inl p => Prologue.sub p | .inr (.cons c) => c.site.sub | .inr _ => 0
  acc := fun _ => []
  inv := fun
    | .inl p => Prologue.Inv p
    | .inr (.loader l) => Loader.Inv l ∧ Loader.ArriveLead L g l
    | .inr (.mma m) => Mma.Inv m ∧ Mma.QReset m ∧ Mma.Lead L g m
    | .inr (.sched s) => Scheduler.Inv s ∧ Scheduler.Lead L g s
    | .inr (.cons c) => Consumer.Inv c ∧ Consumer.tidOf L g < 256 ∧ Consumer.AckFirst L g c
  next := fun d e => match d with
    | .inl p => Prologue.next L g p e
    | .inr (.loader l) => (Loader.next L g l e).map (Option.map (.inr ∘ .loader))
    | .inr (.mma m) => (Mma.next L g m e).map (Option.map (.inr ∘ .mma))
    | .inr (.sched s) => (Scheduler.next L g s e).map (Option.map (.inr ∘ .sched))
    | .inr (.cons c) => (Consumer.next L g c e).map (Option.map (.inr ∘ .cons))

/-- The conclusion of a role's step lemma. -/
abbrev RoleStep {D : Type} (next : D → Event → Option (Option D)) (facts : D → List (Nat × Value))
    (pc : D → Nat) (Inv : D → Prop) (L : Launch) (g : Nat) (d : D) (e : Event) (u : TState) : Prop
      :=
  next d e = some none ∨ ∃ d' t', next d e = some (some d') ∧
    Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ At t' (pc d') (facts d') ∧ Inv d'

abbrev ThreadStep (L : Launch) (g : Nat) (d : ThreadD) (e : Event) (u : TState) : Prop :=
  (code L g).next d e = some none ∨ ∃ d' t', (code L g).next d e = some (some d') ∧
    Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ (code L g).Good (some d') t'

theorem of_loader {L : Launch} {g : Nat} {l : Loader.D} {e : Event} {u : TState}
    (hal : Loader.ArriveLead L g l) (h : RoleStep (Loader.next L g) (Loader.facts L g) (·.site.pc)
      Loader.Inv L g l e u ∨
      (Loader.next L g l e = none ∧ Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) u)) :
    ThreadStep L g (.inr (.loader l)) e u ∨
      ((code L g).next (.inr (.loader l)) e = none ∧
        Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) u) := by
  rcases h with (hn | ⟨d', t', hn, hr, ha, hi⟩) | ⟨hn, hd⟩
  · exact .inl (.inl (by simp [code, hn]))
  · exact .inl (.inr ⟨.inr (.loader d'), t', by simp [code, hn], hr, ha, hi,
      Loader.next_arriveLead hal hn⟩)
  · exact .inr ⟨by simp [code, hn], hd⟩

theorem of_mma {L : Launch} {g : Nat} {m : Mma.D} {e : Event} {u : TState} (hq : Mma.QReset m)
    (hl : Mma.Lead L g m)
    (h : RoleStep (Mma.next L g) (Mma.facts L g) (·.site.pc) Mma.Inv L g m e u ∨
      (Mma.next L g m e = none ∧ Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) u)) :
    ThreadStep L g (.inr (.mma m)) e u ∨
      ((code L g).next (.inr (.mma m)) e = none ∧
        Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) u) := by
  rcases h with (hn | ⟨d', t', hn, hr, ha, hi⟩) | ⟨hn, hd⟩
  · exact .inl (.inl (by simp [code, hn]))
  · exact .inl (.inr ⟨.inr (.mma d'), t', by simp [code, hn], hr, ha, hi, Mma.next_qReset hq hn,
      Mma.next_lead hl hn⟩)
  · exact .inr ⟨by simp [code, hn], hd⟩

theorem of_sched {L : Launch} {g : Nat} {s : Scheduler.D} {e : Event} {u : TState}
    (hl : Scheduler.Lead L g s) (h : RoleStep (Scheduler.next L g) (Scheduler.facts L g) (·.site.pc)
      Scheduler.Inv L g s e u ∨
      (Scheduler.next L g s e = none ∧ Machine.Dead (K := kernel) (A := Prod) (L := L) (g :=
        g) u)) :
    ThreadStep L g (.inr (.sched s)) e u ∨
      ((code L g).next (.inr (.sched s)) e = none ∧
        Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) u) := by
  rcases h with (hn | ⟨d', t', hn, hr, ha, hi⟩) | ⟨hn, hd⟩
  · exact .inl (.inl (by simp [code, hn]))
  · exact .inl (.inr ⟨.inr (.sched d'), t', by simp [code, hn], hr, ha, hi,
      Scheduler.next_lead hl hn⟩)
  · exact .inr ⟨by simp [code, hn], hd⟩

/-- Only a store's element writes lead to a later element of a store. -/
theorem Consumer.next_sub {L : Launch} {g : Nat} {d d' : Consumer.D} {e : Event}
    (hs : ∀ k i el, d.site ≠ .store k i el) (hn : Consumer.next L g d e = some (some d')) :
    d'.site.sub = 0 := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  unfold Consumer.next at hn
  simp only at hn hs
  split at hn
  all_goals (repeat' (first | split_ifs at hn | split at hn))
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try subst hn)
  all_goals (try (simp only [Option.map_eq_some_iff, Option.some.injEq] at hn; obtain ⟨_, -, rfl⟩ :=
    hn))
  all_goals simp_all [Consumer.Site.sub]

/-- A consumer step in the form of `step_store`. -/
theorem of_consS {L : Launch} {g : Nat} {c : Consumer.D} {e : Event} {u : TState}
    (ht : Consumer.tidOf L g < 256)
    (h : Consumer.next L g c e = some none ∨ ∃ d' t', Consumer.next L g c e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ Consumer.AtS L g t' d' ∧ Consumer.Inv d') :
    ThreadStep L g (.inr (.cons c)) e u := by
  rcases h with hn | ⟨d', t', hn, hr, ⟨h1, h2, h3, h4, h5⟩, hi⟩
  · exact .inl (by simp [code, hn])
  · exact .inr ⟨.inr (.cons d'), t', by simp [code, hn], hr, ⟨h1, h2, h3, h4, h5⟩, hi, ht,
      Consumer.next_ackFirst hn⟩

/-- A consumer step at a site other than a store. -/
theorem of_cons {L : Launch} {g : Nat} {c : Consumer.D} {e : Event} {u : TState}
    (hs : ∀ k i el, c.site ≠ .store k i el)
    (ht : Consumer.tidOf L g < 256)
    (h : RoleStep (Consumer.next L g) (Consumer.facts L g) (·.site.pc) Consumer.Inv L g c e u) :
    ThreadStep L g (.inr (.cons c)) e u := by
  apply of_consS ht
  rcases h with hn | ⟨d', t', hn, hr, ⟨h1, h2, h3, h4, h5⟩, hi⟩
  · exact .inl hn
  · exact .inr ⟨d', t', hn, hr, ⟨h1, by rw [h2, Consumer.next_sub hs hn], h3, h4, h5⟩, hi⟩

/-- A consumer step at a site other than a store that may lead to a dead state. -/
theorem of_consD {L : Launch} {g : Nat} {c : Consumer.D} {e : Event} {u : TState}
    (hs : ∀ k i el, c.site ≠ .store k i el) (ht : Consumer.tidOf L g < 256)
    (h : RoleStep (Consumer.next L g) (Consumer.facts L g) (·.site.pc) Consumer.Inv L g c e u ∨
      (Consumer.next L g c e = none ∧ Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) u)) :
    ThreadStep L g (.inr (.cons c)) e u ∨
      ((code L g).next (.inr (.cons c)) e = none ∧
        Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) u) := by
  rcases h with h | ⟨hn, hd⟩
  · exact .inl (of_cons hs ht h)
  · exact .inr ⟨by simp [code, hn], hd⟩

theorem of_prologue {L : Launch} {g : Nat} {p : Prologue.D} {e : Event} {u : TState}
    (h : Prologue.Step L g p u e) : ThreadStep L g (.inl p) e u := by
  rcases h with hn | ⟨d', t', hn, hr, hg⟩
  · exact .inl hn
  · refine .inr ⟨d', t', hn, hr, ?_⟩
    rcases d' with p' | (l | m | s | c)
    · exact hg
    · exact hg
    · exact ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2⟩
    · refine ⟨hg.1, hg.2, fun hs => ?_⟩
      rw [Prologue.next_sched hn] at hs
      simp [Prologue.schedStart] at hs
    · refine ⟨hg.1, hg.2.1, hg.2.2, fun hs => ?_⟩
      rw [Prologue.next_cons hn] at hs
      simp [Prologue.consStart] at hs

theorem at_of_atD {L : Launch} {g : Nat} {p : Prologue.D} {t : TState}
    (hs : p.site ≠ .allocWrite) (h : (code L g).AtD (.inl p) t) :
    At t p.site.pc (Prologue.facts L g p) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, ?_, ?_, h4, h5⟩
  · simpa [code, Prologue.sub, hs] using h2
  · simpa [code] using h3

theorem Mma.slotPred_eq : ∀ s : Fin 4, Mma.fullPred s = Mma.slotPred s := by decide

set_option maxHeartbeats 8000000 in
/-- Every thread of a launch satisfying the precondition is simulated by its code machine. -/
theorem sound {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) : (code L g).Sound where
  start := by
    obtain ⟨t, hr, ht⟩ := Prologue.start (g := g) hpre
    exact ⟨t, hr, ht, ⟨by decide⟩⟩
  steps := by
    intro d
    constructor
    · intro _
      rcases d with p | (l | m | s | c)
      · obtain ⟨ins, hc, hl, hgd⟩ := Prologue.site_ok p.site
        exact ⟨ins, hc, hl, by simp [hgd, Code.GuardTrue]⟩
      · exact Loader.site_ok l
      · exact Mma.site_ok m
      · exact Scheduler.site_ok s
      · exact Consumer.site_ok c
    · intro t e u ins h hi hc hf
      rcases d with p | (l | m | s | c)
      · refine .inl ?_
        have hc : kernel.code[p.site.pc]? = some ins := hc
        have hf : Fires p.site.pc (eventTmpl Prod L g t ins.op) e (some u) := hf
        have hi : Prologue.Inv p := hi
        apply of_prologue
        obtain ⟨s, w⟩ := p
        cases s with
        | shfl => exact Prologue.step_shfl hpre hg rfl (at_of_atD (by simp) h) hc hf
        | elect => exact Prologue.step_elect hpre hg rfl hi (at_of_atD (by simp) h) hc hf
        | init i => exact Prologue.step_init hpre hg i rfl hi (at_of_atD (by simp) h) hc hf
        | alloc => exact Prologue.step_alloc rfl hi (at_of_atD (by simp) h) hc hf
        | allocWrite => exact Prologue.step_allocWrite rfl hi h hc hf
        | warpBar => exact Prologue.step_warpBar rfl hi (at_of_atD (by simp) h) hc hf
        | fence => exact Prologue.step_fence rfl hi (at_of_atD (by simp) h) hc hf
        | fenceInit => exact Prologue.step_fenceInit rfl hi (at_of_atD (by simp) h) hc hf
        | arrive => exact Prologue.step_arrive rfl hi (at_of_atD (by simp) h) hc hf
        | wait => exact Prologue.step_wait hpre rfl hi (at_of_atD (by simp) h) hc hf
        | setMaxReg => exact Prologue.step_setMaxReg hpre rfl hi (at_of_atD (by simp) h) hc hf
        | roleElect => exact Prologue.step_roleElect hpre hg rfl (at_of_atD (by simp) h) hc hf
      · have hc : kernel.code[l.site.pc]? = some ins := hc
        have hf : Fires l.site.pc (eventTmpl Prod L g t ins.op) e (some u) := hf
        obtain ⟨hi, hal⟩ : Loader.Inv l ∧ Loader.ArriveLead L g l := hi
        apply of_loader hal
        have h' : At t l.site.pc (Loader.facts L g l) := h
        obtain ⟨s, m, n, q, cp, r, x⟩ := l
        cases s with
        | wait b =>
          obtain ⟨base, par, hc'⟩ := Loader.code_wait b
          rw [hc'] at hc
          cases hc
          exact .inl (.inr (Loader.step_wait hpre b hi h' hf))
        | load b j =>
          by_cases hj : j.val + 1 < 3
          · exact .inl (.inr (Loader.step_load hpre b j hj hi h' hc hf))
          · have h2 : j = 2 := Fin.ext (by show j.val = 2; omega)
            subst h2
            exact .inl (.inr (Loader.step_lastLoad hpre b hi h' hc hf))
        | arrive b => exact .inl (.inr (Loader.step_arrive hpre b hi h' hc hf))
        | clcWait =>
          obtain ⟨base, par, hc'⟩ := Loader.code_taskWait .clcWait (.inl rfl)
          rw [hc'] at hc
          cases hc
          exact .inl (.inr (Loader.step_taskWait hpre (.inl rfl) hi h' hf))
        | drain i =>
          obtain ⟨base, par, hc'⟩ := Loader.code_taskWait (.drain i) (.inr ⟨i, rfl⟩)
          rw [hc'] at hc
          cases hc
          exact .inl (.inr (Loader.step_taskWait hpre (.inr ⟨i, rfl⟩) hi h' hf))
        | clcLoad =>
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_loadAcquire_0)
          exact Loader.step_clcLoad hpre rfl hi h' hf
        | clcStatus =>
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_0)
          exact .inl (.inr (Loader.step_clcStatus hpre rfl hi h' hf))
        | clcFirst =>
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_1)
          exact .inl (.inr (Loader.step_clcFirst hpre rfl hi h' hf))
        | clcFence =>
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_1)
          exact .inl (.inr (Loader.step_clcFence hpre hg rfl hi h' hf))
        | ack =>
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_8)
          exact .inl (.inr (Loader.step_ack hpre rfl hi h' (by exact trivial) hf))
        | exitArrive => exact .inl (.inr (Loader.step_exitArrive rfl hi h' hc hf))
        | exitWait => exact .inl (.inr (Loader.step_exitWait hpre rfl hi h' hc hf))
        | exit =>
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
          simp [eventTmpl, Fires] at hf
      · have hc : kernel.code[m.site.pc]? = some ins := hc
        have hf : Fires m.site.pc (eventTmpl Prod L g t ins.op) e (some u) := hf
        obtain ⟨hi, hq, hl⟩ : Mma.Inv m ∧ Mma.QReset m ∧ Mma.Lead L g m := hi
        apply of_mma hq hl
        have h' : At t m.site.pc (Mma.facts L g m) := h
        obtain ⟨s, w, q, fp, ap, cp, r, x⟩ := m
        cases s with
        | elect => exact .inl (Mma.step_elect hpre rfl hi h' hc hf)
        | clcWait =>
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_15)
          exact .inl (Mma.step_clcWait hpre rfl hi h' hf)
        | clcLoad =>
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_loadAcquire_2)
          exact Mma.step_clcLoad hpre rfl hi h' hf
        | clcStatus =>
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_4)
          exact .inl (Mma.step_clcStatus hpre rfl hi h' hf)
        | clcFirst =>
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_5)
          exact .inl (Mma.step_clcFirst hpre rfl hi h' hf)
        | clcFence =>
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_3)
          exact .inl (Mma.step_clcFence hpre hg rfl hi h' hf)
        | ack =>
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_11)
          exact .inl (Mma.step_ack hpre rfl hi h' (by exact trivial) hf)
        | accWait =>
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_16)
          exact .inl (Mma.step_accWait hpre rfl hi (hq (.inr rfl)) h' hf)
        | full s =>
          rw [Mma.code_full_ops s, Mma.slotPred_eq s] at hc
          cases hc
          exact .inl (Mma.step_full hpre s rfl hi h' hf)
        | mma s j => exact .inl (Mma.step_mma hpre s j rfl hi h' hc hf)
        | commit s => exact .inl (Mma.step_commit hpre s rfl hi h' hc hf)
        | accCommit =>
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcCommit_4)
          exact .inl (Mma.step_accCommit hpre rfl hi h' hf)
        | exitArrive => exact .inl (Mma.step_exitArrive rfl hi h' hc hf)
        | exitWait => exact .inl (Mma.step_exitWait hpre rfl hi h' hc hf)
        | exit =>
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
          simp [eventTmpl, Fires] at hf
      · have hc : kernel.code[s.site.pc]? = some ins := hc
        have hf : Fires s.site.pc (eventTmpl Prod L g t ins.op) e (some u) := hf
        obtain ⟨hi, hl⟩ : Scheduler.Inv s ∧ Scheduler.Lead L g s := hi
        apply of_sched hl
        have h' : At t s.site.pc (Scheduler.facts L g s) := h
        obtain ⟨site, ap, cp, r, x⟩ := s
        cases site with
        | elect => exact .inl (Scheduler.step_elect hpre rfl hi h' hc hf)
        | ackWait => exact .inl (Scheduler.step_ackWait hpre rfl hi h' hc hf)
        | tryCancel => exact .inl (Scheduler.step_tryCancel hpre rfl hi h' hc hf)
        | arriveTx => exact .inl (Scheduler.step_arriveTx hpre rfl hi h' hc hf)
        | clcWait => exact .inl (Scheduler.step_clcWait hpre rfl hi h' hc hf)
        | clcLoad =>
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_loadAcquire_1)
          exact Scheduler.step_clcLoad hpre rfl hi h' hf
        | clcStatus =>
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_2)
          exact .inl (Scheduler.step_clcStatus hpre rfl hi h' hf)
        | clcFirst =>
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_3)
          exact .inl (Scheduler.step_clcFirst hpre rfl hi h' hf)
        | clcFence =>
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_2)
          exact .inl (Scheduler.step_clcFence hpre hg rfl hi h' hf)
        | ack => exact .inl (Scheduler.step_ack hpre rfl hi h' hc hf)
        | exitArrive => exact .inl (Scheduler.step_exitArrive rfl hi h' hc hf)
        | exitWait => exact .inl (Scheduler.step_exitWait hpre rfl hi h' hc hf)
        | exit =>
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
          simp [eventTmpl, Fires] at hf
      · have hc : kernel.code[c.site.pc]? = some ins := hc
        have hf : Fires c.site.pc (eventTmpl Prod L g t ins.op) e (some u) := hf
        obtain ⟨hi, hw, -⟩ : Consumer.Inv c ∧ Consumer.tidOf L g < 256 ∧
          Consumer.AckFirst L g c := hi
        obtain ⟨hpc, hsub, hacc, hflt, hreg⟩ := h
        obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := c
        cases s with
        | store k i el =>
          exact .inl (of_consS hw
            (Consumer.step_store rfl hi ⟨hpc, hsub, hacc, hflt, hreg⟩ hc hf))
        | exit =>
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
          simp [eventTmpl, Fires] at hf
        | _ =>
          have h' := And.intro hpc (And.intro hsub (And.intro hacc (And.intro hflt hreg)))
          refine of_consD (by intro _ _ _ h; cases h) hw ?_
          first
            | exact Consumer.step_clcLoad hpre rfl hi h' hc hf
            | exact Consumer.step_ldBase hpre rfl hi h' hc hf
            | exact Consumer.step_loadWait hpre hg hw _ rfl hi h' hc hf
            | refine .inl ?_
              first
                | exact Consumer.step_setMaxReg hpre hg hw rfl hi h' hc hf
                | exact Consumer.step_clcWait hpre rfl hi h' hc hf
                | exact Consumer.step_clcStatus hpre rfl hi h' hc hf
                | exact Consumer.step_clcFirst hpre rfl hi h' hc hf
                | exact Consumer.step_clcFence hpre rfl hi h' hc hf
                | exact Consumer.step_clcBar hpre hg rfl hi h' hc hf
                | exact Consumer.step_ack hpre rfl hi h' hc hf
                | exact Consumer.step_accWait hpre rfl hi h' hc hf
                | exact Consumer.step_load _ rfl hi h' hc hf
                | exact Consumer.step_accArrive hpre rfl hi h' hc hf
                | exact Consumer.step_drain rfl hi h' hc hf
                | exact Consumer.step_barA rfl hi h' hc hf
                | exact Consumer.step_barB hpre rfl hi h' hc hf
                | exact Consumer.step_fence hpre hw rfl hi h' hc hf
                | exact Consumer.step_tma hpre rfl hi h' hc hf
                | exact Consumer.step_commit hpre rfl hi h' hc hf
                | exact Consumer.step_finalDrain hpre hw rfl hi h' hc hf
                | exact Consumer.step_exitArrive rfl hi h' hc hf
                | exact Consumer.step_exitWait rfl hi h' hc hf
                | exact Consumer.step_relinquish hpre rfl hi h' hc hf
                | exact Consumer.step_dealloc rfl hi h' hc hf

end
end PTX.Kernels.Fp16Gemm8192.Proof
