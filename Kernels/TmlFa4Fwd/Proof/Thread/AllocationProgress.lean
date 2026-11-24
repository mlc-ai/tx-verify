-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RegisterProgress
public import Kernels.TmlFa4Fwd.Proof.AllocationBarrierRelease
public import Kernels.TmlFa4Fwd.Proof.MmaStartup
public import Lemmas.Step.TcLoad

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation
open PTX PTX.Flow PTX.Proof Prologue Mma Epilogue

noncomputable section

private theorem directEntrySite (w : Fin 16) (h : w.val < 12) :
    registerHintPc w + 1 ∈ allocationEntrySites := by
  have hPc : registerHintPc w + 1 = if w.val < 8 then 3103 else 7747 := by
    simp only [registerHintPc, dispatchParamPc]
    split_ifs <;> omega
  rw [hPc]
  split <;> decide

/-- Issue the named allocation barrier whenever the recorded predecessor can return. -/
theorem requireArrival {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g pos : Nat} (hg : g < l.threads) {u : TState} {o : Option TState}
    (hPos : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hSite : u.pc ∈ allocationEntrySites) (hFault : u.fault = none)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some u))
    (hTail : Run kernel Assumptions.all l g u ((X.tr g).drop pos) o)
    (hReleased : pos = (X.tr g).length → Step.Released l X g) :
    X.IsBarrier (g, pos) 2 (some 416) u.pc := by
  have hOut := allocationEntryTemplate (g := g) hp.block hSite hFault
  have hLt : pos < (X.tr g).length := by
    by_contra! hLe
    have hLen : pos = (X.tr g).length := Nat.le_antisymm hBound hLe
    have hStarted : X.tr g ≠ [] := by intro h; rw [h, List.length_nil] at hLen; omega
    rw [List.take_of_length_le hLe] at hPrefix
    exact hMax.not_grows (Step.bar_counted_extension hMax.1 hg (.inl hStarted) (hReleased hLen)
      (Assumptions.wfStep.quiet hMax.1 le_snoc rfl
        (Execution.noNewRead_snoc rfl)) hPrefix .refl ⟨_, hOut, rfl, rfl⟩)
  have hNext : Next kernel Assumptions.all l g u u (.bar 2 (next u) (some 416) .sync) :=
    ⟨.refl, hOut⟩
  obtain ⟨_, _, hGet, ⟨rfl, _⟩, _⟩ := hNext.continuing_at_nonempty
    (by rintro _ ⟨_, h⟩; cases h) hTail
    (fun hNil => (Nat.not_le_of_lt hLt) (List.drop_eq_nil_iff.mp hNil))
  exact hGet

/-- The softmax and correction participants of the allocation rendezvous have arrived. -/
theorem directParticipantsArrive {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g < 12) :
    ∃ j site, site ∈ allocationEntrySites ∧ X.IsBarrier (g, j) 2 (some 416) site := by
  obtain ⟨pos, u, _, e, _, _, _, he, hk, _, hu, hPrefix, hTail⟩ :=
    Register.requestReturn hp hMax hg
  have hSite : u.pc ∈ allocationEntrySites := hu.1.symm ▸ directEntrySite _ hw
  exact ⟨pos + 1, u.pc, hSite, requireArrival hp hMax hg (by omega) (len_of_get he)
    hSite hu.2.2.2.1 hPrefix hTail (Register.releasedAfterRequest hp hMax he hk)⟩

private theorem allocatorNext {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) {g : Nat}
    {u : TState} (hu : At u 1908 [(1062, b32 12), (2535, b32 l.sharedBase)]) :
    ∃ t, At t 1909 [(2451, b32 512), (1062, b32 12), (2535, b32 l.sharedBase)] ∧
      Next kernel Assumptions.all l g u t
        (.tc (.resource .one (some (allocationSlot l g)) (.alloc 512))
          (if laneOf l g = 0 then {t with sub := 1} else next t)) := by
  let t := next (setReg u 2451 (b32 512))
  have hStep : run kernel [] l g 1 u = some t := by
    exact run_local Flow.code_1908 rfl hu rfl
  have ht := hu.set (v := b32 512) (r := 2451) (by
    intro pair hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp)
  change At t 1909 _ at ht
  have hLoc := schedulerLocalTransport (A := Assumptions.all) (lo := 1908) (len := 1)
    rfl (fun hlo hhi => startupOut_eq_nil (by omega) (by omega)) hStep
    (by rw [hu.1]) (by rw [hu.1])
  have hBase : t.regs 2535 = some (b32 l.sharedBase) := ht.2.2.2.2.2.2.1
  have hCols : t.regs 2451 = some (b32 512) := ht.2.2.2.2.1
  refine ⟨t, ht, run_rtg hLoc, ?_⟩
  rw [allocationTemplate hp ht.1 ht.2.2.2.1 hBase hCols, ht.2.1]
  rfl

/-- Every lane of the allocator warp issued the same startup allocation request. -/
theorem allocatorIssues {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12) :
    ∃ t o, At t 1909 [(2451, b32 512), (1062, b32 12), (2535, b32 l.sharedBase)] ∧
      X.get (g, 6) = some
        ⟨1909, .tc (.resource .one (some (allocationSlot l g)) (.alloc 512))⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take 7)
        (some (if laneOf l g = 0 then {t with sub := 1} else next t)) ∧
      Run kernel Assumptions.all l g (if laneOf l g = 0 then {t with sub := 1} else next t)
        ((X.tr g).drop 7) o := by
  obtain ⟨pos, u, o, e, inc, n, inst, he, hk, hPos, hu, hPrefix, hTail⟩ :=
    Register.requestReturn hp hMax hg
  have hU : At u 1908 [(1062, b32 12), (2535, b32 l.sharedBase)] := by
    simpa [hw, registerHintPc, dispatchParamPc] using hu
  obtain ⟨t, ht, hNext⟩ := allocatorNext hp (g := g) hU
  let k := TcKind.resource .one (some (allocationSlot l g)) (.alloc 512)
  let after := if laneOf l g = 0 then {t with sub := 1} else next t
  have hStep : EStep kernel Assumptions.all l g t ⟨t.pc, .tc k⟩ (some after) :=
    ⟨_, hNext.stop, rfl, rfl⟩
  have hLt : pos + 1 < (X.tr g).length := by
    by_contra! hLe
    have hLen : pos + 1 = (X.tr g).length := Nat.le_antisymm (len_of_get he) hLe
    have hStarted : X.tr g ≠ [] := by intro h; rw [h, List.length_nil] at hLen; omega
    have hRel := Register.releasedAfterRequest hp hMax he hk hLen
    rw [List.take_of_length_le hLe] at hPrefix
    exact hMax.not_grows (Step.tccoll_counted_extension hMax.1 hg (.inl hStarted) hRel
      hPrefix hNext.steps hStep rfl (hMax.1.tmemPairResult.snoc_not_wr nofun)
      (hMax.1.tcRead_snoc_tc nofun) (Assumptions.wfStep.quiet hMax.1 le_snoc rfl
        (Execution.noNewRead_snoc rfl)))
  obtain ⟨q, _, hGet, ⟨rfl, hAfter⟩, hRest⟩ := hNext.continuing_at_nonempty
    (by rintro _ ⟨_, h⟩; cases h) hTail
    (fun hNil => (Nat.not_le_of_lt hLt) (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hAfter
  have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (pos + 1 + 1))
      (some after) := by
    rw [List.take_succ_eq_append_getElem hLt]
    have hEq : (X.tr g)[pos + 1] = ⟨t.pc, .tc k⟩ := by
      change (X.tr g)[pos + 1]? = some ⟨t.pc, .tc k⟩ at hGet
      rwa [List.getElem?_eq_getElem hLt, Option.some.injEq] at hGet
    rw [hEq]
    exact hPrefix.snoc hNext.steps hStep
  have hEq := hPos (by omega)
  subst pos
  exact ⟨t, o, ht, ht.1 ▸ hGet, hPast, hRest⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Allocation
