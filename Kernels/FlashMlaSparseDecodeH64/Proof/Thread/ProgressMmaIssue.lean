-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressPoll
public import Lemmas.Kernel.NextReads
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaDataTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingCommitEvents
import Lemmas.Step.Issue
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressArrival
import Lemmas.Step.TcLoad

public section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-! # Single-thread Tensor Core issue steps of the MMA role -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof MBarrier AsyncCopy

/-- The MMA role's copies, multiply-accumulates, commits and acquire fences. -/
inductive MmaIssueSite : Wg1Mma.Site → Prop where
  | queryCopy (k : Fin 16) : MmaIssueSite (.qCopy k)
  | qk (k : Fin 16) : MmaIssueSite (.qkMma k)
  | pv (k : Fin 8) : MmaIssueSite (.pvMma k)
  | commit {s : Wg1Mma.Site} :
      s = .qCopyCommit ∨ s = .qkCommit ∨ s = .pvCommit → MmaIssueSite s
  | fence {s : Wg1Mma.Site} :
      s = .qFence ∨ s = .qCopyFence ∨ s = .kvFence ∨ s = .soFence → MmaIssueSite s

private theorem mma_issue_template {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : Wg1Mma.D} {t : TState} {ins : Instr}
    (hpre : Pre P L mem0) (hg : g < L.threads) (hd : MmaIssueSite d.site)
    (ha : (Wg1Mma.code P L g).AtD d t) (hc : kernel.code[d.site.pc]? = some ins) :
    ∃ k : TcKind, eventTmpl Assumptions.all L g t ins.op = .tc k (PTX.next t) ∧
      isTcColl ⟨t.pc, .tc k⟩ = false := by
  rcases d with ⟨s, i⟩
  cases hd with
  | queryCopy chunk =>
    exact ⟨_, MmaDataTrace.qCopy_template hpre hg i chunk ha hc, rfl⟩
  | qk chunk =>
    exact ⟨_, MmaDataTrace.qkMma_template hpre hg i chunk ha hc, rfl⟩
  | pv chunk =>
    exact ⟨_, MmaDataTrace.pvMma_template hpre hg i chunk ha hc, rfl⟩
  | commit h =>
    obtain ⟨sp, hTmpl, _, _⟩ := RingCommitEvents.commit_template hpre hg h ha hc
    exact ⟨.commit sp, hTmpl, rfl⟩
  | fence h =>
    change s = .qFence ∨ s = .qCopyFence ∨ s = .kvFence ∨ s = .soFence at h
    have hCode : kernel.code[s.pc]? = some ⟨none, .tcFenceAfter⟩ := by
      rcases h with h | h | h | h
      · rw [h]; exact Flow.code_tcFence_5
      · rw [h]; exact Flow.code_tcFence_6
      · rw [h]; exact Flow.code_tcFence_7
      · rw [h]; exact Flow.code_tcFence_8
    obtain rfl := Option.some.inj (hc.symm.trans hCode)
    exact ⟨.fenceAfter, rfl, rfl⟩

section
variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat} {d : Wg1Mma.D}
    (hpre : Pre P L mem0) (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hord : ReadsOrdered L X) (hsg : SyncGuarded L kernel X)
    (hnr : ∀ e tag a bs, X.get e = some ⟨tag, .wr a bs⟩ → a.release = false)
    (hnrmw : ∀ e tag a old new, X.get e = some ⟨tag, .rmw a old new⟩ → a.release = false)
    (hnf : ∀ e sem scope, ¬ X.ThreadFence e sem scope) (hub : ¬ HasUb X) (hp : Frame.Pending L X g)
    (hrel : PTX.Step.Released L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.mma d)))
include hpre hs hX hord hsg hnr hnrmw hnf hub hp hrel hσ

/-- The released MMA lane can append its actual single-thread Tensor Core issue event. -/
theorem mma_issue_extension (hd : MmaIssueSite d.site) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hne : X.tr g ≠ [] := by
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hσ
    cases hσ
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hTau, ha, _, hc, hout⟩ := Frame.end_at hs hp.1 hRun hσ
  obtain ⟨k, hTmpl, hColl⟩ := mma_issue_template hpre hp.1 hd ha hc
  let ev : Event := ⟨u.pc, .tc k⟩
  have hStep : EStep kernel Assumptions.all L g u ev (some (PTX.next u)) := by
    rw [hTmpl] at hout
    exact ⟨_, hout, rfl, rfl⟩
  have hAsms := Interface.all_wf_snoc_of_not_nc (g := g) (event := ev)
    (rf := fun _ => none) hX (by simp [ev]) (by simp [ev])
  exact PTX.Step.tc_counted_extension_reads hX hord hp.1 hne hrel hRun hTau hStep hColl
    hAsms (hsg.snoc hnr hnrmw hnf nofun nofun nofun nofun)

omit hpre hs hX hord hsg hnr hnrmw hnf hub hp hrel hσ in
/-- The MMA lane's next query load issues its actual TMA tile and descriptor. -/
theorem mma_query_load_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg1Mma.D} {tile : Fin 8} (hpre : Pre P L mem0)
    (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hord : ReadsOrdered L X) (hsg : SyncGuarded L kernel X)
    (hnr : ∀ e tag a bs, X.get e = some ⟨tag, .wr a bs⟩ → a.release = false)
    (hnrmw : ∀ e tag a old new, X.get e = some ⟨tag, .rmw a old new⟩ → a.release = false)
    (hnf : ∀ e sem scope, ¬ X.ThreadFence e sem scope)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.mma d)))
    (hd : d.site = .qLoad tile) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hne : X.tr g ≠ [] := by
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hσ
    cases hσ
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hTau, ha, _, hc, hout⟩ := Frame.end_at hs hp.1 hRun hσ
  have hD : d = ⟨.qLoad tile, d.i⟩ := by cases d; simp_all
  rw [hD] at ha hc
  have hTmpl := MmaDataTrace.qLoad_template hpre hp.1 d.i tile ha hc
  let ev : Event := ⟨u.pc, .tensorIssue (P.param1Base + Wg1Mma.qMapOff)
    (MmaDataTrace.queryTmaSpec P L g tile)⟩
  have hStep : EStep kernel Assumptions.all L g u ev (some (PTX.next u)) := by
    rw [hTmpl] at hout
    exact ⟨_, hout, rfl, rfl⟩
  exact PTX.Step.issue_counted_extension_reads hX hord hp.1 hne hrel hRun hTau hStep
    (.inl ⟨_, _, rfl⟩)
    (Interface.all_wf_snoc_of_not_nc hX nofun (fun h => by cases h))
    (hsg.snoc hnr hnrmw hnf (ev := ev) nofun nofun nofun (by
      intro tag m par acq sc h
      cases congrArg Event.kind h))

omit hpre hs hX hord hsg hnr hnrmw hnf hub hp hrel hσ in
private theorem query_arrival_template {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : Wg1Mma.D} {t : TState} {ins : Instr} (hpre : Pre P L mem0)
    (hd : d.site = .qArrive) (ha : (Wg1Mma.code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins) :
    eventTmpl Assumptions.all L g t ins.op =
      .arrive ⟨.shared, ctaOf L g, L.sharedBase + 222776⟩ 65536 (PTX.next t) 1 true .cta := by
  have hpc : d.site.pc = 1929 := by rw [hd]; rfl
  rw [hpc] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_3)
  have hb : t.regs 811 = some (b32 (L.sharedBase + 222776)) := by
    simpa [Wg1Mma.valueOf, Wg1Mma.values, lookupLit, Option.getD_some, Wg1Mma.qTmaAddr_eq] using
      Wg1Mma.atD_reg ha (r := 811) hpc (by decide +kernel)
  have ht : t.regs 827 = some (b32 65536) := by
    simpa [Wg1Mma.valueOf, Wg1Mma.values, lookupLit, Option.getD_some] using
      Wg1Mma.atD_reg ha (r := 827) hpc (by decide +kernel)
  have hAddr : mbarLoc L g t 811 0 = .ok ⟨.shared, ctaOf L g, L.sharedBase + 222776⟩ :=
    mbarLoc_b32 hb (by have := sharedBase_lt hpre; omega)
      (Wg2.sharedAddr_align hpre (by decide : 222776 % 8 = 0))
  have hTx := readBits_b32 (L := L) (g := g) ht (by decide)
  have hScope : Assumptions.all.any (·.clusterScopeMbar t.pc) = false := rfl
  simp only [eventTmpl, widenMbarScope, hScope, Bool.false_eq_true, ↓reduceIte, tmaTmpl,
    hAddr, hTx, pure, Except.pure, bind, Except.bind, ofExec, mbarStateDest]
  rfl

/-- The released MMA lane can record the query TMA's actual 65536-byte expectation. -/
theorem mma_query_arrival_extension (hd : d.site = .qArrive) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hne : X.tr g ≠ [] := by
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hσ
    cases hσ
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hTau, ha, _, hc, hout⟩ := Frame.end_at hs hp.1 hRun hσ
  change (Wg1Mma.code P L g).AtD d u at ha
  change kernel.code[d.site.pc]? = some ins at hc
  have ht := query_arrival_template hpre hd ha hc
  rw [ht] at hout
  exact role_arrival_extension hX hord hsg hnr hnrmw hnf hp.1 hne hrel hRun hTau hout
end

/-- Either optional length load can read its four launch bytes at the actual address. -/
theorem mma_length_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg1Mma.D} (hpre : Pre P L mem0)
    (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.mma d)))
    (hd : d.site = .loadTopk ∨ d.site = .loadExtra) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hne : X.tr g ≠ [] := by
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hσ
    cases hσ
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hTau, ha, _, hc, hout⟩ := Frame.end_at hs hp.1 hRun hσ
  change (Wg1Mma.code P L g).AtD d u at ha
  change kernel.code[d.site.pc]? = some ins at hc
  rcases hd with h | h
  · have hCode : d.site.pc = 1876 := by rw [h]; rfl
    rw [hCode] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_15)
    have h := Wg1Mma.atD_at ha
    change At u d.site.pc (Wg1Mma.factsAt P L g d.site.pc d) at h
    rw [hCode] at h
    rw [Wg1Mma.event_loadTopk hpre h] at hout
    exact nc_extension hX hp.1 (.inl hne) hrel hRun hTau hout
  · have hCode : d.site.pc = 1886 := by rw [h]; rfl
    rw [hCode] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_16)
    have h := Wg1Mma.atD_at ha
    change At u d.site.pc (Wg1Mma.factsAt P L g d.site.pc d) at h
    rw [hCode] at h
    rw [Wg1Mma.event_loadExtra hpre h] at hout
    exact nc_extension hX hp.1 (.inl hne) hrel hRun hTau hout

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
