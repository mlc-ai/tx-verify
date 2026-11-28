-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Export.Next
public import Kernels.InklingRelDecode.Proof.Common.Occurs
public import Kernels.InklingRelDecode.Proof.Common.WarpColl
public import Lemmas.Quiet.Progress.ReleasedG
import Kernels.InklingRelDecode.Proof.Common.InitPc
import Kernels.InklingRelDecode.Proof.Common.Sound
import Kernels.InklingRelDecode.Proof.Common.Export.Tmem
import Kernels.InklingRelDecode.Proof.Startup.Export.AllocSteps
import Kernels.InklingRelDecode.Proof.Lib.AssumptionStep
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Lemmas.Quiet.Progress.IssueG
import Lemmas.Quiet.Kernel.FrameTrackedU
import all Kernels.InklingRelDecode.Proof.Common.Follow
import all Kernels.InklingRelDecode.Proof.Common.Time

@[expose] public section

/-! # A pending released lane steps by the class of its next instruction

The lane's state is taken privately from `Follow`. A plain read, a poll and a warp collective
are the caller's (`hread`, `hpoll`, `hwarp`), stated of the lane's run; every other class is the
library's step. A first event of a launched lane is the allocation or the first barrier. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Descent

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The next instruction of a pending lane: its run, the local steps, the instruction there. -/
structure PendAt (L : Launch) (X : Execution) (g : Nat) (t1 : TState) (ins : Instr) : Prop where
  run : ∃ t, Run kernel Assumptions.all L g {} (X.tr g) (some t) ∧ TauTo L g t t1
  code : kernel.code[t1.pc]? = some ins
  out : out kernel Assumptions.all L g t1 = .ev (eventTmpl Assumptions.all L g t1 ins.op)

private def restOk (ins : Instr) : Bool :=
  (opKind ins.op != .reg || Sched.regOp ins.op) &&
  (opKind ins.op != .alloc || Sched.allocOp ins.op) &&
  (opKind ins.op != .other || ins.op.isLocal || Sched.tcStoreOp ins.op)

private theorem restOk_all : kernel.code.all restOk = true := by decide +kernel

private theorem restOk_at {pc : Nat} {ins : Instr} (h : kernel.code[pc]? = some ins) :
    restOk ins = true :=
  List.all_eq_true.mp restOk_all _ (List.mem_of_getElem? h)

private theorem code_11 : ∀ ins, kernel.code[11]? = some ins → Sched.allocOp ins.op = true := by
  decide +kernel

private theorem code_11' : ∀ ins, kernel.code[11]? = some ins → opKind ins.op ≠ .store := by
  decide +kernel

private theorem code_12 : ∀ ins, kernel.code[12]? = some ins → opKind ins.op = .bar := by
  decide +kernel

variable (hc : NextEnvG L kernel Assumptions.all m X) (hpd : Frame.Pending L X g)
  (hrel : Step.Released L X g)

include hc hpd hrel in
theorem pend_fault_step {t t1 : TState} {f : Fault} (hl : TauTo L g t t1)
    (hrun : Run kernel Assumptions.all L g {} (X.tr g) (some t))
    (hne : X.tr g ≠ [] ∨ Step.Launched L X g)
    (hout : out kernel Assumptions.all L g t1 = .ev (.ub f)) :
    Sched.Steps (schedule Q L) m X (.thread g) :=
  .inl (Step.plain_counted_extension hc.max.1 hpd.1 hne hrel hrun hl (o := none)
    ⟨_, hout, rfl, rfl⟩ trivial rfl nofun nofun nofun rfl
    (hc.max.1.tmemPairResult.snoc_not_wr nofun) (hc.snoc_wf rfl))

include hc hpd hrel in
/-- The lane's first event (empty trace): the allocation (pc 11) or the first barrier (pc 12). -/
private theorem first_step (hp : Pre Q L m) (hlaunch : Step.Launched L X g)
    (hzero : ∀ {cta : Nat} {r : Tmem.Pair.Requests}, r ∈ X.tmemHistory cta →
      ∀ n col, r.action = .alloc n col → col = 0)
    {d : (thread Q L g).D} (hσ : Frame.stateAt (thread Q L) X g (X.tr g).length = some (some d))
    (hnil : X.tr g = []) {t t1 : TState} {ins : Instr}
    (hrun : Run kernel Assumptions.all L g {} (X.tr g) (some t)) (hl : TauTo L g t t1)
    (hins : kernel.code[(thread Q L g).pc d]? = some ins)
    (hout : out kernel Assumptions.all L g t1 = .ev (eventTmpl Assumptions.all L g t1 ins.op)) :
    Sched.Steps (schedule Q L) m X (.thread g) := by
  have hd : d = (thread Q L g).init := by
    rw [hnil, List.length_nil, Frame.stateAt_zero] at hσ
    exact (Option.some.inj (Option.some.inj hσ)).symm
  have hpc : (thread Q L g).pc d = 11 ∨ (thread Q L g).pc d = 12 := hd ▸ init_pc
  rcases hpc with hpc | hpc
  · exact Sched.alloc_next_stepsUG (M := schedule Q L) hc.wf hc.max hc.noUb
      (fun _ hg => thread_sound hp hg) hpd hσ (.inr hlaunch) hrel
      (fun i hi => code_11 i (by
        have h : kernel.code[(thread Q L g).pc d]? = some i := hi
        rwa [hpc] at h)) hzero
  · rw [hpc] at hins
    rcases tmpl_kind (A := Assumptions.all) (L := L) (g := g) (t := t1) ins.op with ⟨f, hf⟩ | hk
    · rw [hf] at hout
      exact pend_fault_step hc hpd hrel hl hrun (.inr hlaunch) hout
    rw [code_12 ins hins] at hk
    obtain ⟨id, u, c, md, hm⟩ := hk
    rw [hm] at hout
    exact .inl (Step.barArrival_counted_extension hc.max.1 hpd.1 (.inr hlaunch) hrel
      (hc.snoc_wf rfl) hrun hl (o := some u) ⟨_, hout, rfl, rfl⟩)

include hc hpd in
/-- The event a pending store is about to perform, when the lane's last event is the request of
an allocation by lane 0, is the allocation's own (pc 11): no store follows the request. -/
private theorem last_not_store (hp : Pre Q L m) (hf : Follow Q L X) {t t1 : TState}
    (hrun : Run kernel Assumptions.all L g {} (X.tr g) (some t)) (hl : TauTo L g t t1)
    {a : Acc} {bs : List Byte} {u : TState}
    (hout : out kernel Assumptions.all L g t1 = .ev (.write a bs u)) {ins : Instr}
    (hins : kernel.code[t1.pc]? = some ins) (hk : opKind ins.op = .store) {pc n : Nat} {grp dst}
    (hget : X.get (g, (X.tr g).length - 1) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩) :
    laneOf L g ≠ 0 := by
  intro h0
  have hX := hc.max.1
  have hlen : 0 < (X.tr g).length := (List.getElem?_eq_some_iff.mp hget).1.pos
  have hub := hc.noUb
  have nu : Frame.NoUbBefore X g (X.tr g).length := fun j _ e he f hf' =>
    hub ⟨(g, j), e.pc, f, by obtain ⟨pc, kd⟩ := e; simp only at hf'; subst hf'; exact he⟩
  have hn : Occurs L X g ((X.tr g).length - 1 + 1) ⟨t1.pc, .wr a bs⟩ :=
    .inr ⟨hpd.1, by omega, by rwa [Nat.sub_add_cancel hlen], t, t1, _, u, hrun, hl, hout,
      rfl, rfl⟩
  have h11 : t1.pc = 11 := Startup.Export.alloc_next_pc hp hX hf hget h0 hn (fun _ => nofun)
  exact code_11' ins (by rwa [h11] at hins) hk

include hc hpd hrel in
private theorem next_at (hp : Pre Q L m) (hf : Follow Q L X)
    (hread : ∀ {t t1 : TState} {a k}, X.tr g ≠ [] →
      Run kernel Assumptions.all L g {} (X.tr g) (some t) → TauTo L g t t1 →
      out kernel Assumptions.all L g t1 = .ev (.read a k) →
      Sched.Steps (schedule Q L) m X (.thread g))
    (hpoll : ∀ {t1 ins}, PendAt L X g t1 ins → opKind ins.op = .wait →
      Sched.Steps (schedule Q L) m X (.thread g) ∨ ∃ pc, FailsAt L m X g pc)
    (hwarp : ∀ {d : ((schedule Q L).code g).D},
      Frame.stateAt (schedule Q L).code X g (X.tr g).length = some (some d) → CollAt Q L g d →
      Sched.Steps (schedule Q L) m X (.thread g))
    {d : (thread Q L g).D} (hσ : Frame.stateAt (thread Q L) X g (X.tr g).length = some (some d)) :
    Sched.Steps (schedule Q L) m X (.thread g) ∨ ∃ pc, FailsAt L m X g pc := by
  have hX := hc.max.1
  have hC : ∀ g < L.threads, (thread Q L g).SoundU := fun _ hg => thread_sound hp hg
  have hlaunch : Step.Launched L X g := fun ⟨_, _, _, ⟨_, hi⟩⟩ => (Lib.no_clc hX hi).elim
  have hzero : ∀ {cta : Nat} {r : Tmem.Pair.Requests}, r ∈ X.tmemHistory cta →
      ∀ n col, r.action = .alloc n col → col = 0 := fun hr n col h =>
    (Tmem.One.alloc_zero hX (Export.tmem_ops hp hX hf) hr n col h).2
  obtain ⟨t, hrun⟩ := Frame.run_some hX hc.noUb hpd
  rcases Frame.end_atU hC hpd.1 hrun hσ with ⟨t1, ins, hl, hat, hi, hins, hout⟩ | ⟨u, f, hl, hout⟩
  case inr => exact .inl (pend_fault_step hc hpd hrel hl hrun (.inr hlaunch) hout)
  have hpc : t1.pc = (thread Q L g).pc d := hat.1
  have hins' : kernel.code[t1.pc]? = some ins := by rwa [hpc]
  have hone : ∀ i, kernel.code[(thread Q L g).pc d]? = some i → i = ins := fun i h =>
    Option.some.inj (h.symm.trans hins)
  by_cases hnil : X.tr g = []
  · exact .inl (first_step hc hpd hrel hp hlaunch hzero hσ hnil hrun hl hins hout)
  have hne : X.tr g ≠ [] := hnil
  rcases tmpl_kind (A := Assumptions.all) (L := L) (g := g) (t := t1) ins.op with ⟨f, hf⟩ | hkt
  · rw [hf] at hout
    exact .inl (pend_fault_step hc hpd hrel hl hrun (.inl hne) hout)
  have hrs := restOk_at hins
  have hat' : PendAt L X g t1 ins := ⟨⟨t, hrun, hl⟩, hins', hout⟩
  have hloc : ins.op.isLocal = false := by
    obtain ⟨i2, h2, hl2, -⟩ := ((thread_sound hp hpd.1).steps d).site hi
    rw [hins] at h2
    cases h2
    exact hl2
  have hlast : ∀ i, kernel.code[(thread Q L g).pc d]? = some i → opKind i.op = .store →
      ∀ pc grp dst n, X.get (g, (X.tr g).length - 1) =
        some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ → laneOf L g ≠ 0 := by
    intro i hi hk pc grp dst n hget
    rw [hone i hi] at hk
    rw [hk] at hkt
    obtain ⟨a, bs, u, hm, -⟩ := hkt
    rw [hm] at hout
    exact last_not_store hc hpd hp hf hrun hl hout hins' hk hget
  have hexit : ∀ i, kernel.code[(thread Q L g).pc d]? = some i → opKind i.op = .exit →
      ∀ pc r, ∀ a ∈ Assumptions.all, a.wf L m (X.snoc g ⟨pc, .exit⟩ r) := fun _ _ _ _ _ a ha =>
    Lib.assumptions_step _ _ hX le_snoc (Execution.notifiedInOrder_of_eq rfl)
      (Execution.noNewRead_snoc (e := ⟨_, .exit⟩) rfl) a ha
  cases hkd : opKind ins.op
  case wait => exact hpoll hat' hkd
  case warp => exact .inl (hwarp hσ ⟨ins, hins, hkd⟩)
  case read =>
    rw [hkd] at hkt
    obtain ⟨a, k, hm⟩ := hkt
    rw [hm] at hout
    exact .inl (hread hne hrun hl hout)
  case reg =>
    refine .inl (Sched.reg_next_stepsUG (M := schedule Q L) hc.wf hc.max hc.noUb hC hpd hσ hne
      hrel fun i h => ?_)
    rw [hone i h]
    simpa [restOk, hkd] using hrs
  case alloc =>
    refine .inl (Sched.alloc_next_stepsUG (M := schedule Q L) hc.wf hc.max hc.noUb hC hpd hσ
      (.inl hne) hrel (fun i h => ?_) hzero)
    rw [hone i h]
    simpa [restOk, hkd] using hrs
  case other =>
    refine .inl (Sched.tcStore_next_stepsUQ (M := schedule Q L) hc.wf hc.max hc.noUb hC hpd hσ
      hne hrel fun i h => ?_)
    rw [hone i h]
    simpa [restOk, hkd, hloc] using hrs
  all_goals
    refine .inl (Descent.released_stepsUG (o := .thread g) (rank := Sched.rank (schedule Q L))
      hc hpd hne hrel hC hσ (fun i h => by rw [hone i h, hkd]; rfl)
      (fun i h => by rw [hone i h, hkd]; nofun) hlast hexit)

include hc hpd hrel in
/-- **A pending released lane of a maximal execution steps, or its next event is a failed
poll.** A plain read, a poll and a warp collective are the caller's. -/
theorem pend_step (hp : Pre Q L m) (hf : Follow Q L X)
    (hread : ∀ {t t1 : TState} {a k}, X.tr g ≠ [] →
      Run kernel Assumptions.all L g {} (X.tr g) (some t) → TauTo L g t t1 →
      out kernel Assumptions.all L g t1 = .ev (.read a k) →
      Sched.Steps (schedule Q L) m X (.thread g))
    (hpoll : ∀ {t1 ins}, PendAt L X g t1 ins → opKind ins.op = .wait →
      Sched.Steps (schedule Q L) m X (.thread g) ∨ ∃ pc, FailsAt L m X g pc)
    (hwarp : ∀ {d : ((schedule Q L).code g).D},
      Frame.stateAt (schedule Q L).code X g (X.tr g).length = some (some d) → CollAt Q L g d →
      Sched.Steps (schedule Q L) m X (.thread g)) :
    Sched.Steps (schedule Q L) m X (.thread g) ∨ ∃ pc, FailsAt L m X g pc := by
  have hG := hf g hpd.1 (X.tr g).length
  cases hs : Frame.stateAt (thread Q L) X g (X.tr g).length with
  | none =>
    exact .inl (Descent.dead_steps_inOrderUQ hc.wf hc.max hc.noUb
      (fun _ hg => thread_sound hp hg) hpd hs hrel)
  | some o =>
    cases o with
    | none => exact absurd hs hG.1
    | some d => exact next_at hc hpd hrel hp hf hread hpoll hwarp hs

end PTX.Kernels.InklingRelDecode.Proof
