-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaInitialScoreIssue
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryCredits
import Kernels.TmlFa4Fwd.Proof.MmaPoll
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.MBarrier Prologue Epilogue
open Thread.Output (queryObject)

noncomputable section

/-- The second query-ready pointer and its initialized parity. -/
def openingSecondQueryWaitFrame (l : Launch) : List (Nat × Value) :=
  [(2563,b32 0),(2562,b32 (l.sharedBase+8))]

private theorem openingSecondQueryWaitSetup {l : Launch} {g : Nat} {s : TState}
    {F : List (Nat × Value)} (hKeep : ∀ pair ∈ F, pair.1 ≠ 2563)
    (hs : At s 2209 (openingQueryAfterScoreFrame l ++ F)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u 2210 (openingSecondQueryWaitFrame l ++ F) := by
  have hSeg : Seg kernel [] l g 1 2209 (openingQueryAfterScoreFrame l)
      2210 (openingSecondQueryWaitFrame l) := by
    intro t ht
    dsimp [openingQueryAfterScoreFrame,openingSecondQueryWaitFrame] at ht ⊢
    seg_fp ht using rfl
  obtain ⟨hBase,hF⟩ := (holds_append ..).mp hs.2.2.2.2
  obtain ⟨u,hu,hU⟩ := hSeg s (hs.mono hBase)
  have hStep : Tau kernel [] l g s u := by
    apply tauStep_iff.mp
    unfold run at hu
    cases h : tauStep kernel [] l g s <;> simp_all [run]
  have hCode := Flow.code_2209
  rw [← hs.1] at hCode
  have hF' : Holds u.regs F := by
    apply holdsSchedulerFrame (regs := F.map Prod.fst) hF
    · intro r hr
      obtain ⟨pair,hm,rfl⟩ := List.mem_map.mp hr
      exact tau_core_regs hCode hStep (by simpa [writesRegs] using hKeep pair hm)
    · exact fun _ h => List.mem_map_of_mem h
  exact ⟨u,run_rtg (localRun (by decide) (by decide) hs.1 rfl hu),
    hU.mono ((holds_append ..).mpr ⟨hU.2.2.2.2,hF'⟩)⟩

/-- The opening MMA warp has made its second query acquisition. -/
def OpeningSecondQueryMmaAcquiredWithFrame (l : Launch) (X : Execution) (g shuffles votes : Nat)
    (ends : Nat → Option TState) (F : List (Nat × Value)) : Prop :=
  ∃ cur : SchedulerWarpReached l X g 2213 (fun _ => openingSecondQueryWaitFrame l ++ F)
      shuffles votes ends,
    ∀ lane < 32, ∃ e,
      let th := warpLane l g lane
      X.get (th,cur.pos lane-1) = some e ∧
      e.kind = .wait (queryObject l (th/l.block) 1) 0 true true .cta

private theorem waitPrefixKeepsCount {events rest : List Event} {n pos : Nat}
    {fail ok : Event} (hTrace : events.drop pos = List.replicate n fail ++ ok::rest)
    (pred : Event → Bool) (hFail : pred fail = false) (hOk : pred ok = false) :
    ((events.take (pos+n+1)).countP pred) = (events.take pos).countP pred := by
  let polls := List.replicate n fail ++ [ok]
  have hLen : polls.length = n+1 := by simp [polls]
  have hNew : events.drop pos = polls ++ rest := by
    rw [hTrace]
    simp [polls]
  rw [Nat.add_assoc,← hLen,List.take_add,hNew,List.take_append_length,List.countP_append]
  simp [polls,List.countP_append,List.countP_replicate,hFail,hOk]

/-- A ready Q1 barrier is acquired by all real lanes after the opening score commit. -/
theorem openingSecondQueryAcquireFromWarpWithFrame {p : Params} {l : Launch} {m : Mem0}
    {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) {g shuffles votes : Nat}
    (hg : g < l.threads) {ends : Nat → Option TState}
    {F : List (Nat × Value)} (hKeep : ∀ pair ∈ F, pair.1 ≠ 2563)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ (waitSite 2).result)
    (hReached : Nonempty (SchedulerWarpReached l X g 2209
      (fun _ => openingQueryAfterScoreFrame l ++ F) shuffles votes ends))
    (hReady : let log := X.objects (queryObject l (g/l.block) 1)
      ∃ s, stateBefore log log.length = some s ∧ s.phase = 1) :
    OpeningSecondQueryMmaAcquiredWithFrame l X g shuffles votes ends F := by
  obtain ⟨cur⟩ := hReached
  obtain ⟨start⟩ := cur.advanceLocal (pc' := 2210)
    (G := fun _ => openingSecondQueryWaitFrame l ++ F)
    (fun lane hl => openingSecondQueryWaitSetup (g := warpLane l g lane) hKeep
      (cur.checkpoint lane hl))
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hBounds : l.sharedBase+8 < 2^32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase+8)%8 = 0 := by have := hp.shared.1; omega
  have hEach (lane : Nat) (hl : lane < 32) : ∃ q before state,
      let th := warpLane l g lane
      X.get (th,q) = some ⟨2210,.wait (queryObject l (th/l.block) 1) 0 true true .cta⟩ ∧
      Run kernel Assumptions.all l th {} ((X.tr th).take (q+1)) (some before) ∧
      Run kernel Assumptions.all l th before ((X.tr th).drop (q+1)) (ends lane) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l th) before state ∧
      At state 2213 (openingSecondQueryWaitFrame l ++ F) ∧
      ((X.tr th).take (q+1)).countP Execution.isShfl = shuffles ∧
      ((X.tr th).take (q+1)).countP isFullWarpVote = votes := by
    let th := warpLane l g lane
    have hSame := (Step.sameWarp_lane hBlock hg hl).1
    have hPhase : let log := X.objects ⟨.shared,th/l.block,l.sharedBase+8⟩
        ∃ s, stateBefore log log.length = some s ∧ s.phase%2 ≠ 0%2 := by
      obtain ⟨s,hState,hP⟩ := hReady
      have hCta : th/l.block = g/l.block := hSame.1.2.2.symm
      rw [hCta]
      exact ⟨s,hState,by rw [hP]; decide⟩
    obtain ⟨n,v,u,hGet,hPast,hRest,hLocal,hAt,hTrace⟩ :=
      waitOfMaximalWithTrace hMax hSame.1.2.1 2 (phase := 0) hBounds hAlign (by decide)
        (F := openingSecondQueryWaitFrame l ++ F) (by
          intro pair hm
          rcases List.mem_append.mp hm with hL | hR
          · simp [openingSecondQueryWaitFrame,waitSite] at hL ⊢
            rcases hL with rfl | rfl <;> exact of_decide_eq_true rfl
          · exact hFresh pair hR)
        (by simp [openingSecondQueryWaitFrame,waitSite])
        (by simp [openingSecondQueryWaitFrame,waitSite])
        (fun {_ _} _ _ _ => hPhase) (start.positive lane hl) (start.bounded lane hl)
        (start.released lane hl) (start.checkpoint lane hl) (start.recorded lane hl)
        (start.continuation lane hl) (start.localSteps lane hl)
    exact ⟨start.pos lane+n,v,u,hGet,hPast,hRest,hLocal,hAt,
      (waitPrefixKeepsCount hTrace Execution.isShfl rfl rfl).trans (start.ordinals.shfl lane hl),
      (waitPrefixKeepsCount hTrace isFullWarpVote rfl rfl).trans (start.ordinals.vote lane hl)⟩
  let _ : Inhabited TState := ⟨{}⟩
  choose! q before state hGet hPast hRest hLocal hFrame hS hV using hEach
  refine ⟨⟨⟨fun lane => q lane+1,before,state,⟨hS,hV⟩,hRest,hLocal,hFrame⟩,
    fun _ _ => Nat.succ_pos _,fun lane hl => len_of_get (hGet lane hl),
    fun lane hl => releasedIfLast (hGet lane hl) (by intro h; cases h),hPast⟩,?_⟩
  intro lane hl
  exact ⟨_,by simpa only [Nat.add_sub_cancel] using hGet lane hl,rfl⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
