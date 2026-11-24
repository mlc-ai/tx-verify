-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Safety.Aligned
public import Lemmas.Flow.NotAsyncArrive

@[expose] public section

/-!
# Every mbarrier an instruction names is one of the twelve

`Regions.MbarPlaced`: each mbarrier operand of an event is `EvD.Bar.loc L cta b` of a barrier `b`
and a launched CTA. Initializations, arrivals, commits, tensor copies and polls fire from the
states the interface classifies (`init_event_state`, `arrive_event_state`, `mma_event_state`,
`copy_event_state`, `wait_event_state`), with the barrier in their shapes (the loader's and the
MMA warp's names are the default partition's, by `rfl`). The kernel has no `mbarrier.inval`, no
`cp.async.mbarrier.arrive`, no linear copy and no cancellation request. The one poll without an
event shape is the softmax region's `o_done` poll (`Sm.Site.waitO`); `OdoneWait` is its barrier.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The `o_done` poll names `o_done` of its CTA**: the softmax region's poll at `waitO`, for
which the thread layer has no event shape (a row of "thread-layer gaps"). -/
def OdoneWait (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc q : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope} {d : Sm.D},
    St Q L X g k = some (some (.d (.sm d))) → d.site = .waitO →
    X.get (g, k) = some ⟨pc, .wait m q ok acq sc⟩ → m = EvD.Bar.loc L (g / L.block) .oDone

theorem kernel_noInval : kernel.code.all (fun ins => !invalOp ins.op) = true := by
  decide +kernel

theorem kernel_noAsyncArrive : kernel.code.all (fun ins => !asyncArriveOp ins.op) = true := by
  decide +kernel

/-- **The kernel has no `mbarrier.inval`.** -/
theorem no_inval (hX : Consistent L kernel asms mem0 X) :
    ∀ {i : EvId} {pc : Nat} {m : Loc}, X.get i ≠ some ⟨pc, .mbInval m⟩ :=
  fun he => no_kind_of_code hX invalOp (fun k => ∃ m, k = .mbInval m)
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_mbInval_op hf hk)
    kernel_noInval he ⟨_, rfl⟩

/-- **The kernel has no `cp.async.mbarrier.arrive`.** -/
theorem no_asyncArrive (hX : Consistent L kernel asms mem0 X) :
    ∀ {i : EvId} {pc : Nat} {m : Loc} {n : Bool}, X.get i ≠ some ⟨pc, .asyncArrive m n⟩ :=
  fun he => no_kind_of_code hX asyncArriveOp (fun k => ∃ m n, k = .asyncArrive m n)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => fires_asyncArrive_op hf hk)
    kernel_noAsyncArrive he ⟨_, _, rfl⟩

theorem cta_lt_grid (hpre : Pre Q L mem0) {g : Nat} (hg : g < L.threads) : g / L.block < L.grid :=
  (unitCta_of_pre hpre hg).cta

/-- A commit event's target is the barrier its `commitSpec` names. -/
theorem commit_target_bar {g : Nat} {d : Mma.D} {pc : Nat} {s : TcCommit.Spec}
    (hsh : MmShape L g d ⟨pc, .tc (.commit s)⟩) {rank : Fin 16} {m : Loc}
    (htg : TcCommit.target s rank = some m) :
    ∃ b : EvD.Bar, m = b.loc L (g / L.block) := by
  unfold MmShape at hsh
  cases hs : d.site <;> simp only [hs] at hsh
  all_goals first
    | (simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at hsh
       obtain ⟨-, rfl⟩ := hsh
       unfold TcCommit.target at htg
       split at htg
       · rename_i hr
         simp only [commitSpec, Option.some.injEq] at htg hr
         have hr0 : rank.val = 0 := by omega
         subst htg
         first
           | (refine ⟨.sReady ⟨d.i % 2, Nat.mod_lt _ (by omega)⟩, ?_⟩
              simp only [hr0]
              rfl)
           | (refine ⟨.kvEmpty ⟨(d.i - 1) % 3, Nat.mod_lt _ (by omega)⟩, ?_⟩
              simp only [hr0]
              rfl)
           | (refine ⟨.oDone, ?_⟩
              simp only [hr0]
              rfl)
           | (refine ⟨.oFinal, ?_⟩
              simp only [hr0]
              rfl)
       · cases htg)
    | (exfalso; simp [QkIssue, PvIssue] at hsh)

/-- The loader's arrival names `kv_ready` of its CTA. -/
theorem ld_arrive_bar {g : Nat} {d : Loader.D} {pc tx c : Nat} {r : Bool} {sc : MbarScope}
    {m : Loc} (hsh : LdShape Q L g d ⟨pc, .arrive m tx c r sc⟩) :
    ∃ b : EvD.Bar, m = b.loc L (g / L.block) := by
  unfold LdShape at hsh
  cases hs : d.site <;> simp only [hs] at hsh
  all_goals first
    | (simp at hsh; done)
    | (simp only [Event.mk.injEq, Kind.arrive.injEq] at hsh
       exact ⟨.kvReady ⟨d.i % 3, Nat.mod_lt _ (by omega)⟩, hsh.2.1⟩)

/-- The loader's poll names `kv_empty` of its CTA. -/
theorem ld_wait_bar {g : Nat} {d : Loader.D} {pc q : Nat} {ok acq : Bool} {sc : MbarScope}
    {m : Loc} (hsh : LdShape Q L g d ⟨pc, .wait m q ok acq sc⟩) :
    ∃ b : EvD.Bar, m = b.loc L (g / L.block) := by
  unfold LdShape at hsh
  cases hs : d.site <;> simp only [hs] at hsh
  all_goals first
    | (simp at hsh; done)
    | (simp only [Event.mk.injEq, Kind.wait.injEq] at hsh
       obtain ⟨-, -, hm, -⟩ := hsh
       exact ⟨.kvEmpty ⟨d.i % 3, Nat.mod_lt _ (by omega)⟩, hm⟩)

/-- The loader's tensor copy completes on `kv_ready` of its CTA. -/
theorem ld_copy_bar {g : Nat} {d : Loader.D} {pc a : Nat} {s : TensorCopy.Spec}
    (hsh : LdShape Q L g d ⟨pc, .tensorIssue a s⟩) :
    ∃ b : EvD.Bar, s.mbar = b.loc L (g / L.block) := by
  unfold LdShape at hsh
  cases hs : d.site <;> simp only [hs] at hsh
  all_goals first
    | (simp at hsh; done)
    | (obtain ⟨b, -, hev⟩ := hsh
       simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hev
       obtain ⟨-, -, rfl⟩ := hev
       exact ⟨.kvReady ⟨d.i % 3, Nat.mod_lt _ (by omega)⟩, rfl⟩)

/-- The MMA warp's polls name `kv_ready` and `p_ready` of its CTA. -/
theorem mm_wait_bar {g : Nat} {d : Mma.D} {pc q : Nat} {ok acq : Bool} {sc : MbarScope}
    {m : Loc} (hs : d.site = .kvWait ∨ d.site = .pWait)
    (hsh : MmShape L g d ⟨pc, .wait m q ok acq sc⟩) :
    ∃ b : EvD.Bar, m = b.loc L (g / L.block) := by
  unfold MmShape at hsh
  rcases hs with hs | hs <;> simp only [hs] at hsh <;>
    obtain ⟨ok', hev⟩ := hsh <;> simp only [Event.mk.injEq, Kind.wait.injEq] at hev
  · exact ⟨.kvReady ⟨d.i % 3, Nat.mod_lt _ (by omega)⟩, hev.2.1⟩
  · exact ⟨.pReady ⟨(d.i - 1) % 2, Nat.mod_lt _ (by omega)⟩, hev.2.1⟩

/-- **Every mbarrier an instruction names is one of the kernel's twelve**, of a launched CTA,
given the barrier of the `o_done` poll. -/
theorem mbarPlaced_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (ho : OdoneWait Q L X) : MbarPlaced L X := by
  intro e m hu
  obtain ⟨g, k⟩ := e
  rcases hu with ⟨tx, count, rel, sc, pc, he⟩ | ⟨s, ⟨pc, he⟩, -⟩ | ⟨noinc, pc, he⟩ |
    ⟨s, rank, hcm, htg⟩ | ⟨pc, q, ok, acq, sc, he⟩ | ⟨pc, he⟩ | ⟨address, s, ⟨pc, he⟩, rfl⟩ |
    ⟨s, targets, c, ⟨pc, he⟩, -⟩ | ⟨count, pc, he⟩
  · have hg := Frame.lt_of_get hX he
    have hc := cta_lt_grid hpre hg
    rcases arrive_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he
      ⟨m, tx, count, rel, sc, rfl⟩ with
      ⟨d, -, j, -, -, hev⟩ | ⟨d, -, -, -, hev⟩ | ⟨d, P, -, -, hsh⟩
    · simp only [Event.mk.injEq, Kind.arrive.injEq] at hev
      exact ⟨_, _, hc, hev.2.1⟩
    · simp only [Event.mk.injEq, Kind.arrive.injEq] at hev
      exact ⟨_, _, hc, hev.2.1⟩
    · obtain ⟨b, hb⟩ := ld_arrive_bar hsh
      exact ⟨b, _, hc, hb⟩
  · exact absurd he (no_copy hX)
  · exact absurd he (no_asyncArrive hX)
  · obtain ⟨pc, he⟩ := hcm
    have hg := Frame.lt_of_get hX he
    have hc := cta_lt_grid hpre hg
    obtain ⟨d, P, -, hsh⟩ := mma_event_state hpre hX hf.sound hf.tracked hg he (.inr ⟨s, rfl⟩)
    obtain ⟨b, hb⟩ := commit_target_bar hsh htg
    exact ⟨b, _, hc, hb⟩
  · have hg := Frame.lt_of_get hX he
    have hc := cta_lt_grid hpre hg
    rcases wait_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨m, q, ok, acq, sc, rfl⟩ with
      ⟨d, hσ, ⟨hs, ok', hev⟩ | hs⟩ | ⟨d, P, -, -, hsh⟩ | ⟨d, P, -, hs, hsh⟩ | ⟨d, -, -, ok', hev⟩
    · simp only [Event.mk.injEq, Kind.wait.injEq] at hev
      exact ⟨_, _, hc, hev.2.1⟩
    · exact ⟨.oDone, _, hc, ho hσ hs he⟩
    · obtain ⟨b, hb⟩ := ld_wait_bar hsh
      exact ⟨b, _, hc, hb⟩
    · obtain ⟨b, hb⟩ := mm_wait_bar hs hsh
      exact ⟨b, _, hc, hb⟩
    · simp only [Event.mk.injEq, Kind.wait.injEq] at hev
      exact ⟨_, _, hc, hev.2.1⟩
  · exact absurd he (no_inval hX)
  · have hg := Frame.lt_of_get hX he
    have hc := cta_lt_grid hpre hg
    rcases copy_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨address, s, rfl⟩ with
      ⟨d, -, i, -, -, a', s', hev, -, -, h3, -⟩ | ⟨d, P, -, hsh⟩
    · simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hev
      obtain ⟨-, -, rfl⟩ := hev
      exact ⟨_, _, hc, h3⟩
    · obtain ⟨b, hb⟩ := ld_copy_bar hsh
      exact ⟨b, _, hc, hb⟩
  · exact absurd he (no_clc hX)
  · have hg := Frame.lt_of_get hX he
    have hc := cta_lt_grid hpre hg
    obtain ⟨d, -, i, -, -, hev⟩ := init_event_state hpre hX hf.sound hf.tracked hg he
      ⟨m, count, rfl⟩
    simp only [Event.mk.injEq, Kind.mbInit.injEq] at hev
    exact ⟨_, _, hc, hev.2.1⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Safety
