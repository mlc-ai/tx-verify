-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSchedulerShuffleProgress
public import Kernels.TmlFa4Fwd.Proof.MmaFirstScanTrace

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Mma (firstSchedulerPos firstDownTemplate loadHeadsWord
  firstSchedulerTilesWithCta)

noncomputable section

/-- The actual initial down shuffle gives each lane its first group's scan operand,
zero for a lane without a request. -/
theorem firstScanCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hProtected : DrainCuQProtected p X) :
    let pos := firstSchedulerPos p (laneOf l g)
    ∃ s t o, pos + 1 ≤ (X.tr g).length ∧
      ((X.tr g).take (pos + 1)).countP Execution.isShfl = 5 ∧
      (pos + 1 = (X.tr g).length → Step.Released l X g) ∧
      At t 1960 [(7196, b32 (groupLaneTiles p 0 (laneOf l g))),
        (1180, b32 (laneOf l g)), (7139, b32 p.heads), (1072, b32 (g / l.block)),
        (337,.pred (!decide (laneHasRequest (laneOf l g) p.batch)))] ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos + 1)) (some s) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t ∧
      Run kernel Assumptions.all l g s ((X.tr g).drop (pos + 1)) o := by
  dsimp only
  let lane := laneOf l g
  let pos := firstSchedulerPos p lane
  let sent := b32 (drainCuQ p lane)
  let received := b32 (drainCuQ p (shflSource .down lane 1 31).1)
  let ok := (shflSource .down lane 1 31).2
  obtain ⟨t, u, o, hBound, hCount, _, hu, hPrefix, hl, hTail⟩ :=
    schedulerDownCursorFramed hp hMax hg hw hProtected
  obtain ⟨j, e, he, hk, hj⟩ := initialSchedulerShuffled hp hMax hg hw hProtected
  have hU : At u 1941 [(7193, sent)] := hu.mono ⟨hu.2.2.2.2.1, trivial⟩
  have hn : Next kernel Assumptions.all l g t u
      (.shfl .down sent 1 31 (fun v _ => next (setReg u 2456 v))) :=
    ⟨hl, firstDownTemplate hp hU⟩
  have hLen : pos < (X.tr g).length := by
    by_contra! hLe
    have hExact : pos = (X.tr g).length := Nat.le_antisymm hBound hLe
    change ((X.tr g).take pos).countP Execution.isShfl = 4 at hCount
    have hFull : (X.tr g).countP Execution.isShfl = 4 := by simpa [hExact] using hCount
    have hMore : 4 < (X.tr g).countP Execution.isShfl := Step.ShflK.lt_count hj
    omega
  obtain ⟨_, _, hGet, ⟨recv, flag, rfl, hSome⟩, hRest⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_, _, _, h⟩; cases h) hTail
    (fun hNil => (Nat.not_le_of_lt hLen) (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hSome
  have hNumber : X.ShflK (g,pos) 4 := ⟨⟨_, _, _, _, _, _, _, hGet⟩, hCount⟩
  have hJ := shfl_index_unique hj hNumber
  subst j
  have hKind := congrArg Event.kind (Option.some.inj (hGet.symm.trans he))
  have ⟨_, _, _, _, hRecv, hFlag⟩ := Kind.shfl.inj (hKind.trans hk)
  subst recv
  subst flag
  let s := next (setReg u 2456 received)
  have hStep : EStep kernel Assumptions.all l g u
      ⟨u.pc, .shfl .down sent 1 31 received ok⟩ (some s) :=
    ⟨_, hn.stop, received, ok, rfl, rfl⟩
  have hRun : Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some s) := by
    rw [List.take_succ_eq_append_getElem hLen]
    have hEvent : (X.tr g)[pos] = ⟨u.pc, .shfl .down sent 1 31 received ok⟩ := by
      change (X.tr g)[pos]? = _ at hGet
      rwa [List.getElem?_eq_getElem hLen, Option.some.injEq] at hGet
    rw [hEvent]
    exact hPrefix.snoc hn.steps hStep
  have hAt : At s 1942 [(2456, received), (7193, sent), (1180, b32 lane), (7203, b32 p.batch),
      (1072, b32 (g / l.block))] :=
    hu.set (by
      intro pair hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl
      · exact (by decide : 7193 ≠ 2456)
      · exact (by decide : 1180 ≠ 2456)
      · exact (by decide : 7203 ≠ 2456)
      · exact (by decide : 1072 ≠ 2456))
  have hArgs : At s 1942
      [(2456, received), (7193, sent), (1180, b32 lane), (7203, b32 p.batch)] :=
    hAt.mono ⟨hAt.2.2.2.2.1, hAt.2.2.2.2.2.1, hAt.2.2.2.2.2.2.1, hAt.2.2.2.2.2.2.2.1, trivial⟩
  obtain ⟨n, v, hv, ht, hCta⟩ := firstSchedulerTilesWithCta hp g (Nat.mod_lt _ (by decide)) hArgs
  have hCta' : v.regs 1072 = some (b32 (g / l.block)) := hCta.trans hAt.2.2.2.2.2.2.2.2.1
  have ht' : At v 1959
      [(7196, b32 (groupLaneTiles p 0 lane)), (1180, b32 lane), (1072, b32 (g / l.block)),
        (337,.pred (!decide (laneHasRequest lane p.batch)))] :=
    ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, hCta', ht.2.2.2.2.2.2.1, trivial⟩
  have hHeads := loadHeadsWord hp (g := g) ht.1 ht.2.2.2.1
  have hScan := ht'.set (r := 7139) (v := b32 p.heads) (by
    intro pair hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact (by decide : 7196 ≠ 7139)
    · exact (by decide : 1180 ≠ 7139)
    · exact (by decide : 1072 ≠ 7139)
    · exact (by decide : 337 ≠ 7139))
  have hAfterCount : ((X.tr g).take (pos + 1)).countP Execution.isShfl = 5 := by
    rw [List.take_add_one, show (X.tr g)[pos]? = _ from hGet]
    simp only [Option.toList_some, List.countP_append, List.countP_singleton]
    change ((X.tr g).take pos).countP Execution.isShfl + 1 = 5
    rw [hCount]
  have hReady : pos + 1 = (X.tr g).length → Step.Released l X g :=
    releasedIfLast hGet (by intro h; cases h)
  exact ⟨s, _, o, hLen, hAfterCount, hReady,
    hScan.mono ⟨hScan.2.2.2.2.2.1, hScan.2.2.2.2.2.2.1, hScan.2.2.2.2.1,
      hScan.2.2.2.2.2.2.2.1, hScan.2.2.2.2.2.2.2.2.1, trivial⟩,
    hRun, run_rtg (run_comp hv hHeads), hRest⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Allocation
