-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueNonzeroTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueRoles
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Lemmas.Flow.TauFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Proof

noncomputable section

private def dispatchPcs : List Nat :=
  [174, 175, 176, 177, 178, 179, 1901, 1902, 1903, 1904, 1905, 1906, 1907, 2768, 2769,
    3099, 3100, 3101, 3102, 7742, 7743, 7744, 7745, 7746, 9205]

private def dispatchWrites : List Nat :=
  [1072, 1706, 60, 7170, 1178, 263, 264, 7203, 7228, 437, 7247, 5867, 681, 7277]

private theorem dispatchCode {pc : Nat} (hp : pc ∈ dispatchPcs) :
    ∃ i, kernel.code[pc]? = some i ∧ Assumptions.coreOp i.op = true ∧
      pc ∉ Assumptions.swExp2Sites ∧ pc ∉ Assumptions.tcLdDataflowSites ∧
      pc ∉ Assumptions.delayedTmemSites ∧
      ((i.guard = none ∧ i.op.isLocal = false) ∨
        (pc + 1 ∈ dispatchPcs ∧ nextPc i.op pc ∈ dispatchPcs ∧
          (∀ q, ¬ BrxTarget i.op q) ∧ writesRegs i.op ⊆ dispatchWrites)) := by
  simp only [dispatchPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨_, Flow.code_174, rfl, by decide, by decide, by decide, .inr ?_⟩
    exact ⟨by decide, by decide, fun _ h => h, by table_decide⟩
  · refine ⟨_, Flow.code_175, rfl, by decide, by decide, by decide, .inr ?_⟩
    exact ⟨by decide, by decide, fun _ h => h, by table_decide⟩
  · refine ⟨_, Flow.code_176, rfl, by decide, by decide, by decide, .inr ?_⟩
    exact ⟨by decide, by decide, fun _ h => h, by table_decide⟩
  · refine ⟨_, Flow.code_177, rfl, by decide, by decide, by decide, .inr ?_⟩
    exact ⟨by decide, by decide, fun _ h => h, by table_decide⟩
  · refine ⟨_, Flow.code_178, rfl, by decide, by decide, by decide, .inr ?_⟩
    exact ⟨by decide, by decide, fun _ h => h, by table_decide⟩
  · refine ⟨_, Flow.code_179, rfl, by decide, by decide, by decide, .inl ⟨rfl, rfl⟩⟩
  · refine ⟨_, Flow.code_1901, rfl, by decide, by decide, by decide, .inr ?_⟩
    exact ⟨by decide, by decide, fun _ h => h, by table_decide⟩
  · refine ⟨_, Flow.code_1902, rfl, by decide, by decide, by decide, .inr ?_⟩
    exact ⟨by decide, by decide, fun _ h => h, by table_decide⟩
  · refine ⟨_, Flow.code_1903, rfl, by decide, by decide, by decide, .inr ?_⟩
    exact ⟨by decide, by decide, fun _ h => h, by table_decide⟩
  · refine ⟨_, Flow.code_1904, rfl, by decide, by decide, by decide, .inr ?_⟩
    exact ⟨by decide, by decide, fun _ h => h, by table_decide⟩
  · refine ⟨_, Flow.code_1905, rfl, by decide, by decide, by decide, .inr ?_⟩
    exact ⟨by decide, by decide, fun _ h => h, by table_decide⟩
  · refine ⟨_, Flow.code_1906, rfl, by decide, by decide, by decide, .inr ?_⟩
    exact ⟨by decide, by decide, fun _ h => h, by table_decide⟩
  · refine ⟨_, Flow.code_1907, rfl, by decide, by decide, by decide, .inl ⟨rfl, rfl⟩⟩
  · refine ⟨_, Flow.code_2768, rfl, by decide, by decide, by decide, .inr ?_⟩
    exact ⟨by decide, by decide, fun _ h => h, by table_decide⟩
  · refine ⟨_, Flow.code_2769, rfl, by decide, by decide, by decide, .inl ⟨rfl, rfl⟩⟩
  · refine ⟨_, Flow.code_3099, rfl, by decide, by decide, by decide, .inr ?_⟩
    exact ⟨by decide, by decide, fun _ h => h, by table_decide⟩
  · refine ⟨_, Flow.code_3100, rfl, by decide, by decide, by decide, .inr ?_⟩
    exact ⟨by decide, by decide, fun _ h => h, by table_decide⟩
  · refine ⟨_, Flow.code_3101, rfl, by decide, by decide, by decide, .inr ?_⟩
    exact ⟨by decide, by decide, fun _ h => h, by table_decide⟩
  · refine ⟨_, Flow.code_3102, rfl, by decide, by decide, by decide, .inl ⟨rfl, rfl⟩⟩
  · refine ⟨_, Flow.code_7742, rfl, by decide, by decide, by decide, .inr ?_⟩
    exact ⟨by decide, by decide, fun _ h => h, by table_decide⟩
  · refine ⟨_, Flow.code_7743, rfl, by decide, by decide, by decide, .inr ?_⟩
    exact ⟨by decide, by decide, fun _ h => h, by table_decide⟩
  · refine ⟨_, Flow.code_7744, rfl, by decide, by decide, by decide, .inr ?_⟩
    exact ⟨by decide, by decide, fun _ h => h, by table_decide⟩
  · refine ⟨_, Flow.code_7745, rfl, by decide, by decide, by decide, .inr ?_⟩
    exact ⟨by decide, by decide, fun _ h => h, by table_decide⟩
  · refine ⟨_, Flow.code_7746, rfl, by decide, by decide, by decide, .inl ⟨rfl, rfl⟩⟩
  · refine ⟨_, Flow.code_9205, rfl, by decide, by decide, by decide, .inl ⟨rfl, rfl⟩⟩


private theorem dispatchReplayFrame {l : Launch} {g n : Nat} {t u : TState}
    (hr : run kernel [] l g n t = some u) (ht : t.pc ∈ dispatchPcs) :
    run kernel Assumptions.all l g n t = some u ∧
      ∀ r ∉ dispatchWrites, u.regs r = t.regs r := by
  obtain ⟨hRun, _, hKeep⟩ :=
    run_core_region (kept := fun r => r ∉ dispatchWrites)
      (fun hs => by
        obtain ⟨_, hc, hOp, hSeg, hLd, hSt, _⟩ := dispatchCode hs
        exact Assumptions.out_all_eq_nil hSeg hLd hSt hc hOp)
      (fun hs he => by
        obtain ⟨i, hc, _, _, _, _, hStep⟩ := dispatchCode hs
        rcases hStep with ⟨hGuard, hIsEvent⟩ | ⟨hPc, hTarget, hBrx, hWrites⟩
        · obtain ⟨guard, op⟩ := i
          change guard = none at hGuard
          subst guard
          exact (tau_core_not_event hc hIsEvent he).elim
        · rcases tau_core_frame hc he with rfl | hLocal
          · exact ⟨hPc, fun _ _ => rfl⟩
          · have ht := hLocal.pc.elim (fun h => h.symm ▸ hTarget) (fun h => (hBrx _ h).elim)
            exact ⟨ht, fun r h => hLocal.regs r (fun hw => h (hWrites hw))⟩)
      hr ht
  exact ⟨hRun, hKeep⟩

/-- From the common barrier's continuation, the exact local dispatch is available in the full
instruction model for every warp, independently of any later trace. -/
theorem dispatchRunFromCommon {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (warp : Fin 16) {g : Nat} (hg : g < l.threads) {t : TState}
    (ht : At t 174 [(1062, b32 warp.val), (2535, b32 l.sharedBase)]) :
    ∃ u, run kernel Assumptions.all l g (dispatchSteps warp) t = some u ∧
      At u (dispatchParamPc warp) [(1062, b32 warp.val), (1072, b32 (g / l.block)),
        (2535, b32 l.sharedBase)] := by
  obtain ⟨u, hr, hu⟩ := dispatchRoles hp warp g hg t ht
  have hpc : t.pc ∈ dispatchPcs := by rw [ht.1]; decide
  exact ⟨u, (dispatchReplayFrame hr hpc).1, hu⟩

private theorem dispatchReplay {p : Params} {l : Launch} {g n : Nat} {t u : TState}
    (hr : run kernel [] l g n t = some u) (ht : t.pc ∈ dispatchPcs)
    (hf : Holds t.regs (nonzeroBarrierFacts p l g)) :
    run kernel Assumptions.all l g n t = some u ∧ Holds u.regs (nonzeroBarrierFacts p l g) := by
  obtain ⟨hRun, hKeep⟩ := dispatchReplayFrame hr ht
  refine ⟨hRun, ?_⟩
  have hDisjoint : List.Disjoint ((nonzeroBarrierFacts p l g).map Prod.fst) dispatchWrites := by
    change List.Disjoint [1062, 2535, 1063, 1064, 1065, 1066, 1067, 1068, 6495, 2390, 1069,
      1070, 6497, 1071, 1, 7492, 7493, 7494, 7495, 1663, 1664, 7496, 7497, 7498, 7499, 7500,
      7501, 7502, 7503, 7504, 7505, 7291, 7290, 7289, 7506, 7292, 7293, 7294, 7295, 1665]
      dispatchWrites
    intro r hr hw
    simp only [dispatchWrites, List.mem_cons, List.not_mem_nil, or_false] at hr hw
    omega
  generalize hF : nonzeroBarrierFacts p l g = F at hf hDisjoint ⊢
  clear hF
  induction F with
  | nil => trivial
  | cons pair rest ih =>
    exact ⟨(hKeep pair.1 (fun h => hDisjoint (by simp) h)).trans hf.1,
      ih hf.2 (fun r h => hDisjoint (by simp [h]))⟩

/-- Dispatch a nonzero warp's actual completed trace to its first role parameter read. -/
theorem nonzeroRoleEntry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    {g : Nat} (hg : g < l.threads) (hWarp : 0 < warpIndex l g) :
    let warp : Fin 16 := ⟨warpIndex l g, warpIndex_lt hp g⟩
    ∃ t, At t (dispatchParamPc warp) ((1072, b32 (g / l.block)) :: nonzeroBarrierFacts p l g) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop 5) none := by
  dsimp only
  obtain ⟨u, hu, _, _, hRun⟩ := nonzeroAfterCommonBarrier hp hX hComplete hg hWarp
  have hFacts := hu.2.2.2.2
  let warp : Fin 16 := ⟨warpIndex l g, warpIndex_lt hp g⟩
  obtain ⟨v, hv, hV⟩ := dispatchRoles hp warp g hg u (hu.mono ⟨hFacts.1, hFacts.2.1, trivial⟩)
  obtain ⟨hSteps, hKeep⟩ := dispatchReplay hv (by rw [hu.1]; decide) hFacts
  exact ⟨v, hV.mono ⟨hV.2.2.2.2.2.1, hKeep⟩, hRun.after_local (run_rtg hSteps)⟩


/-- A finite nonzero lane trace with an event after the common barrier
reaches its role's parameter initialization. -/
theorem nonzeroRoleEntryPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hWarp : 0 < warpIndex l g) (hLen : 5 < (X.tr g).length) :
    let warp : Fin 16 := ⟨warpIndex l g, warpIndex_lt hp g⟩
    ∃ t o, At t (dispatchParamPc warp) ((1072, b32 (g / l.block)) :: nonzeroBarrierFacts p l g) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop 5) o := by
  dsimp only
  obtain ⟨u, o, hu, _, _, hRun⟩ := nonzeroCommonPrefix hp hX hg hWarp hLen.le
  have hFacts := hu.2.2.2.2
  let warp : Fin 16 := ⟨warpIndex l g, warpIndex_lt hp g⟩
  obtain ⟨v, hv, hV⟩ := dispatchRoles hp warp g hg u (hu.mono ⟨hFacts.1, hFacts.2.1, trivial⟩)
  obtain ⟨hSteps, hKeep⟩ := dispatchReplay hv (by rw [hu.1]; decide) hFacts
  have hSuffix : (X.tr g).drop 5 ≠ [] := by
    intro h
    exact Nat.not_le_of_lt hLen (List.drop_eq_nil_iff.mp h)
  exact ⟨v, o, hV.mono ⟨hV.2.2.2.2.2.1, hKeep⟩,
    hRun.after_local_nonempty (run_rtg hSteps) hSuffix⟩

/-- Replay dispatch while retaining the initial trace and its local continuation. -/
theorem nonzeroRoleEntryFromPrefix {p : Params} {l : Launch} {m : Mem0}
    {g : Nat} {s : TState} (hp : Pre p l m) (hg : g < l.threads)
    (hStart : At s 174 (nonzeroBarrierFacts p l g)) :
    let warp : Fin 16 := ⟨warpIndex l g, warpIndex_lt hp g⟩
    ∃ t, At t (dispatchParamPc warp)
        ((1072, b32 (g / l.block)) :: nonzeroBarrierFacts p l g) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t := by
  dsimp only
  have hFacts := hStart.2.2.2.2
  let warp : Fin 16 := ⟨warpIndex l g, warpIndex_lt hp g⟩
  obtain ⟨v, hv, hV⟩ :=
    dispatchRoles hp warp g hg s (hStart.mono ⟨hFacts.1, hFacts.2.1, trivial⟩)
  obtain ⟨hSteps, hKeep⟩ := dispatchReplay hv (by rw [hStart.1]; decide) hFacts
  exact ⟨v, hV.mono ⟨hV.2.2.2.2.2.1, hKeep⟩, run_rtg hSteps⟩

end
end PTX.Kernels.TmlFa4Fwd.Prologue
