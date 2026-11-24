-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OutputDrainEntryProgress
import Kernels.TmlFa4Fwd.Proof.EpilogueDrainPrepare
import Kernels.TmlFa4Fwd.Proof.EpilogueDrainRounds
import Kernels.TmlFa4Fwd.Proof.EpilogueDrainFold
import Kernels.TmlFa4Fwd.Proof.EpilogueDrainGroup

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

/-- The guard words are stable across either copy of the drain's up-scan. -/
def drainUpGuards (later : Bool) (lane : Nat) : List (Nat × Value) :=
  List.ofFn fun stage : Fin 5 =>
    (drainScanGuardReg later stage,.pred (drainScanGuard stage lane))

private theorem guardFramed (later : Bool) (lane : Nat) (stage : Fin 5) :
    (drainScanGuardReg later stage,.pred (drainScanGuard stage lane)) ∈ drainUpGuards later lane :=
  List.mem_ofFn.mpr ⟨stage,rfl⟩

private theorem upGuardFresh (later : Bool) (stage guard : Fin 5) :
    drainScanGuardReg later guard ∉
      [drainScanDst later stage,drainScanDst later stage+1,drainScanSum later stage] := by
  decide +revert

private theorem upSavedFresh (later : Bool) (stage : Fin 5) :
    ∀ r ∈ drainRoundPersistent, r ∉
      [drainScanDst later stage,drainScanDst later stage+1,drainScanSum later stage] := by
  decide +revert

/-- The next up shuffle consumes the exact lane window, with all scheduler words still live. -/
def outputDrainUpFrame (p : Params) (first : Nat) (later : Bool) (stage : Fin 5)
    (lane : Nat) (F : List (Nat × Value)) : List (Nat × Value) :=
  (drainScanSrc later stage,b32 (prefixWindow (groupLaneTiles p first) (2^stage.val) lane)) ::
    (drainUpGuards later lane ++ F)

private theorem drainUpBounds (later : Bool) (stage : Fin 5) :
    3009 ≤ drainScanPc later stage ∧ drainScanPc later stage+2 < 3099 := by decide +revert

/-- Follow an actual up shuffle and its two local additions in any maximal trace. -/
theorem SchedulerWarpReached.drainUpStep {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first shuffles votes : Nat} (hg : g < l.threads) (hf : first ≤ p.batch)
    (later : Bool) (stage : Fin 5)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hF : ∀ lane < 32, ∀ item ∈ F lane, item.1 ∈ drainRoundPersistent)
    (cur : SchedulerWarpReached l X g (drainScanPc later stage)
      (fun lane => outputDrainUpFrame p first later stage lane (F lane)) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g (drainScanPc later stage+3)
      (fun lane => (drainScanSum later stage,
        b32 (prefixWindow (groupLaneTiles p first) (2*2^stage.val) lane)) ::
          (drainUpGuards later lane ++ F lane)) (shuffles+1) votes ends) := by
  let input := fun lane => b32 (prefixWindow (groupLaneTiles p first) (2^stage.val) lane)
  let source := fun lane => (shflSource .up lane (2^stage.val) 0).1
  let saved := fun lane => drainUpGuards later lane ++ F lane
  have hSaved (lane : Nat) (hl : lane < 32) (item : Nat × Value) (hm : item ∈ saved lane) :
      item.1 ∉ [drainScanDst later stage,drainScanDst later stage+1,drainScanSum later stage] := by
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨guard,rfl⟩ := List.mem_ofFn.mp hm
      exact upGuardFresh later stage guard
    · exact upSavedFresh later stage item.1 (hF lane hl item hm)
  have hFresh (lane : Nat) (hl : lane < 32) (item : Nat × Value)
      (hm : item ∈ outputDrainUpFrame p first later stage lane (F lane)) :
      item.1 ≠ drainScanDst later stage := by
    rcases List.mem_cons.mp hm with rfl | hm
    · exact (by decide : ∀ (later : Bool) (stage : Fin 5),
        drainScanSrc later stage ≠ drainScanDst later stage) later stage
    · exact fun he => hSaved lane hl item hm (by simp [he])
  have hModel {s : TState} (hgLo : drainScanPc later stage ≤ s.pc)
      (hgHi : s.pc ≤ drainScanPc later stage+2) {thread : Nat} :
      out kernel Assumptions.all l thread s = out kernel [] l thread s := by
    have hRange := drainUpBounds later stage
    exact epilogue_out_all_eq_nil (.inl ⟨by omega,by omega⟩)
  obtain ⟨arrived⟩ := cur.consumeShuffle hp hMax hg .up input (fun _ => 2^stage.val) (fun _ => 0)
    hFresh (by
      intro lane hl
      have hu := cur.checkpoint lane hl
      exact (hModel (by rw [hu.1]) (by rw [hu.1]; omega)).trans
        (drainScanTemplate hp later stage _ _ _ hu.1 hu.2.2.2.1 hu.2.2.2.2.1))
  apply arrived.advanceLocal
  intro lane hl
  have hu := arrived.checkpoint lane hl
  have hA := hu.2.2.2.2
  have hWidth : 2^stage.val < 32 := Nat.pow_lt_pow_right (by decide) stage.isLt
  have hSrc : source lane < 32 := by
    dsimp only [source]
    rw [shflSource_up hWidth]
    split
    · exact (Nat.sub_le _ _).trans_lt hl
    · exact hl
  have hLeft := hp.groupWindow_signed hf hl (2^stage.val)
  have hRight := hp.groupWindow_signed hf hSrc (2^stage.val)
  have hSum : prefixWindow (groupLaneTiles p first) (2^stage.val) lane +
      prefixWindow (groupLaneTiles p first) (2^stage.val) (source lane) < 2^32 := by omega
  have hGuard := holds_mem hA.2.2 (List.mem_append_left (F lane) (guardFramed later lane stage))
  obtain ⟨v,hr,hv⟩ :=
    (drainScanFold later stage l (warpLane l g lane) (groupLaneTiles p first) hl hSum).apply
    (hu.mono ⟨hGuard,hA.2.1,hA.1,trivial⟩)
  obtain ⟨a,b,ha,hb,hwa,hwb,hStraight,hBrx⟩ := drainFoldCode later stage
  rw [← hu.1] at ha
  have hCode : kernel.code[(arrived.state lane).pc+1]? = some b := by
    rw [hu.1]
    exact hb
  have hActual := run_two_core_transport (A := Assumptions.all) ha (hStraight _) hBrx (fun h => by
      rw [hu.1] at h
      exact hModel (by omega) (by omega)) hr
  have hKeep : Holds v.regs (saved lane) := by
    apply holdsSchedulerFrame (regs := (saved lane).map Prod.fst) hA.2.2
    · intro r hm
      obtain ⟨item,hItem,hKey⟩ := List.mem_map.mp hm
      rw [← hKey]
      have hNo := hSaved lane hl item hItem
      exact run_two_core_frame ha hCode (hStraight _) hBrx hr item.1
        (by rw [hwa]; simpa using fun e => hNo (by simp [e]))
        (by rw [hwb]; simpa using fun e => hNo (by simp [e]))
    · exact fun item hm => List.mem_map_of_mem hm
  exact ⟨v,run_rtg hActual,hv.mono ⟨hv.2.2.2.2.1,hKeep⟩⟩

/-- Lane words preserved until the first drain scan selects its terminal request interval. -/
def firstDrainScanSaved (p : Params) (cta lane : Nat) : List (Nat × Value) :=
  [(7138,b32 p.heads),(1072,b32 cta),(1062,b32 13),(1201,b32 lane),
    (7147,b32 p.batch),(7506,b64 p.cuQBase),(7232,b32 (groupLaneTiles p 0 lane))]

private theorem firstDrainScanSavedRegs (p : Params) (cta lane : Nat) :
    ∀ item ∈ firstDrainScanSaved p cta lane, item.1 ∈ drainRoundPersistent := by
  intro item h
  simp only [firstDrainScanSaved,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl

private theorem firstDrainScanPrepared {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2991
      (fun lane => (2401,b32 (drainCuQ p (if lane+1 < 32 then lane+1 else lane))) ::
        firstDrainFrame p l g lane) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g (drainScanPc false 0)
      (fun lane => outputDrainUpFrame p 0 false 0 lane (firstDrainScanSaved p (g/l.block) lane))
        shuffles votes ends) := by
  apply cur.advanceLocal
  intro lane hl
  let thread := warpLane l g lane
  have hSame := Step.sameWarp_lane (by rw [hp.block]) hg hl
  have hLane : laneOf l thread = lane := hSame.2
  have hCta : warpLane l g lane / l.block = g / l.block := hSame.1.1.2.2.symm
  have ht := cur.checkpoint lane hl
  have hFacts : At (cur.state lane) 2991 [(7229,b32 (drainCuQ p lane)),
      (2401,b32 (drainCuQ p (shflSource .down lane 1 31).1)),
      (268,.pred (!decide (laneHasRequest lane p.batch))),(1201,b32 lane)] := by
    apply ht.mono
    have hFrame := ht.2.2.2.2
    refine ⟨hFrame.2.1,?_,hFrame.2.2.2.2.2.1,hFrame.2.2.2.1,trivial⟩
    simpa only [shflSource_down_one,apply_ite Prod.fst] using hFrame.1
  obtain ⟨_,u,hLocal,hu,hGuard,hSaved⟩ :=
    drainFirstPrepared hp thread (cur.state lane) (hLane.symm ▸ hl)
      (by simpa only [hLane] using hFacts)
  rw [hLane] at hu hGuard
  have hAllGuards : Holds u.regs (drainUpGuards false lane) := by
    exact ⟨hGuard 0,hGuard 1,hGuard 2,hGuard 3,hGuard 4,trivial⟩
  have hTail := ht.2.2.2.2
  have hRegs : Holds u.regs (firstDrainScanSaved p (g/l.block) lane) := by
    refine ⟨(hSaved _ (by decide)).trans
      (holds_mem hTail (by simp [firstDrainFrame,outputDrainFrame])),
      (hSaved _ (by decide)).trans (holds_mem hTail (by simp [firstDrainFrame,outputDrainFrame,
        schedulerStartupFrame,hCta])),
      (hSaved _ (by decide)).trans (holds_mem hTail (by simp [firstDrainFrame,outputDrainFrame,
        schedulerStartupFrame])),
      (hSaved _ (by decide)).trans (holds_mem hTail (by simp [firstDrainFrame,outputDrainFrame])),
      (hSaved _ (by decide)).trans (holds_mem hTail (by simp [firstDrainFrame,outputDrainFrame])),
      (hSaved _ (by decide)).trans (holds_mem hTail (by simp [firstDrainFrame,outputDrainFrame])),
      hu.2.2.2.2.1,trivial⟩
  have hContrib := hu.2.2.2.2.1
  refine ⟨u,run_rtg hLocal,hu.mono ⟨?_,(holds_append ..).mpr ⟨hAllGuards,hRegs⟩⟩⟩
  change u.regs 7232 = some (b32 (prefixWindow (groupLaneTiles p 0) 1 lane))
  rwa [prefixWindow_one]

theorem drainUpsOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first shuffles votes : Nat} (hg : g < l.threads) (hf : first ≤ p.batch) (later : Bool)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hF : ∀ lane < 32, ∀ item ∈ F lane, item.1 ∈ drainRoundPersistent)
    (cur : SchedulerWarpReached l X g (drainScanPc later 0)
      (fun lane => outputDrainUpFrame p first later 0 lane (F lane)) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g (drainScanPc later 4+3)
      (fun lane => (drainScanSum later 4,
        b32 (prefixWindow (groupLaneTiles p first) 32 lane)) ::
          (drainUpGuards later lane ++ F lane)) (shuffles+5) votes ends) := by
  cases later
  · obtain ⟨a⟩ := cur.drainUpStep hp hMax hg hf false 0 hF
    obtain ⟨b⟩ := a.drainUpStep hp hMax hg hf false 1 hF
    obtain ⟨c⟩ := b.drainUpStep hp hMax hg hf false 2 hF
    obtain ⟨d⟩ := c.drainUpStep hp hMax hg hf false 3 hF
    exact d.drainUpStep hp hMax hg hf false 4 hF
  · obtain ⟨a⟩ := cur.drainUpStep hp hMax hg hf true 0 hF
    obtain ⟨b⟩ := a.drainUpStep hp hMax hg hf true 1 hF
    obtain ⟨c⟩ := b.drainUpStep hp hMax hg hf true 2 hF
    obtain ⟨d⟩ := c.drainUpStep hp hMax hg hf true 3 hF
    exact d.drainUpStep hp hMax hg hf true 4 hF

/-- The output warp consumes the initial drain down shuffle and all five up-scan rounds. -/
theorem firstOutputDrainScanOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hCuQ : DrainCuQProtected p X)
    (hDrain : OutputWritebackDrained p l X g) :
    ∃ shuffles ends, Nonempty (SchedulerWarpReached l X g 3024
      (fun lane => (7233,b32 (prefixWindow (groupLaneTiles p 0) 32 lane)) ::
        (drainUpGuards false lane ++ firstDrainScanSaved p (g/l.block) lane))
      (shuffles+6) 1 ends) := by
  obtain ⟨shuffles,ends,⟨down⟩⟩ := outputDrainDownOfMaximal hp hMax hg hCuQ hDrain
  obtain ⟨ready⟩ := firstDrainScanPrepared hp hg down
  exact ⟨shuffles,ends,drainUpsOfMaximal hp hMax hg (Nat.zero_le _) false
    (fun lane _ => firstDrainScanSavedRegs p (g/l.block) lane) ready⟩

set_option maxHeartbeats 4000000 in
/-- The first drain group either selects the CTA or reaches the next group's actual entry. -/
theorem firstOutputDrainRouteOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hCuQ : DrainCuQProtected p X)
    (hDrain : OutputWritebackDrained p l X g) :
    ∃ shuffles ends,
      if g/l.block < tilePrefix p (min p.batch 31) * p.heads then
        Nonempty (SchedulerWarpReached l X g 3086 (drainFinishFacts p 0 (g/l.block))
          (shuffles+7) 1 ends)
      else
        Nonempty (SchedulerWarpReached l X g 3032 (drainNextFacts p l g 0 (g/l.block))
          (shuffles+7) 1 ends) := by
  let cta := g/l.block
  let count := tilePrefix p (min p.batch 31)
  let contribute := fun lane => groupLaneTiles p 0 lane
  let sum := fun lane => prefixWindow contribute 32 lane
  let F := fun lane => (7233,b32 (sum lane)) ::
    (drainUpGuards false lane ++ firstDrainScanSaved p cta lane)
  obtain ⟨shuffles,ends,⟨scan⟩⟩ := firstOutputDrainScanOfMaximal hp hMax hg hCuQ hDrain
  have hFresh (lane : Nat) (_ : lane < 32) (item : Nat × Value) (hm : item ∈ F lane) :
      item.1 ≠ 7234 := by
    rcases List.mem_cons.mp hm with rfl | h
    · exact of_decide_eq_true rfl
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨stage,rfl⟩ := List.mem_ofFn.mp h
        exact (by decide : ∀ s : Fin 5, drainScanGuardReg false s ≠ 7234) stage
      · have hm := firstDrainScanSavedRegs p cta lane item h
        exact fun he => (of_decide_eq_true rfl : 7234 ∉ drainRoundPersistent) (he ▸ hm)
  obtain ⟨all⟩ := scan.consumeShuffle (dst := 7234) hp hMax hg .idx
    (fun lane => b32 (sum lane)) (fun _ => 31) (fun _ => 31) hFresh (by
      intro lane hl
      have ht := scan.checkpoint lane hl
      have hModel : out kernel Assumptions.all l (warpLane l g lane) (scan.state lane) =
          out kernel [] l (warpLane l g lane) (scan.state lane) :=
        epilogue_out_all_eq_nil (.inl (by rw [ht.1]; decide))
      exact hModel.trans (drainGroupTotalTemplate hp false _ _ _ ht.1 ht.2.2.2.1 ht.2.2.2.2.1))
  have hCount' := groupTiles_eq p (Nat.zero_le p.batch) (show 32 ≤ 32 by decide)
  have hCount : sum 31 = count := by
    rw [show sum 31 = drainPrefix p 0 31 from prefixWindow_warp _ (by decide)]
    change tilePrefix p 0 + drainPrefix p 0 31 = count at hCount'
    simpa [tilePrefix] using hCount'
  have hFit : count * p.heads < 2^31 := hp.prefixWork_signed (Nat.min_le_left _ _)
  have hCountSigned : count < 2^31 := by
    have h := hp.groupWindow_signed (Nat.zero_le p.batch) (show 31 < 32 by decide) 32
    change sum 31 < 2^31 at h
    rwa [hCount] at h
  have hCTA : cta < 2^31 := (NamedBar.cta_lt hg).trans hp.grid.2.2
  have hPrep (lane : Nat) (hl : lane < 32) :
      At (all.state lane) 3025 (drainFirstRouteInputs p l (warpLane l g lane)
        count (drainPrefix p 0 lane) (contribute lane) cta) := by
    have hlane : laneOf l (warpLane l g lane) = lane :=
      (Step.sameWarp_lane (by rw [hp.block]) hg hl).2
    have ht := all.checkpoint lane hl
    have hSrc : sum (shflSource .idx lane 31 31).1 = count := by
      rw [shflSource_idx lane (by decide),hCount]
    have hSum : sum lane = drainPrefix p 0 lane := prefixWindow_warp _ hl
    have hPre := ht.2.2.2.2
    have hFixed : Holds (all.state lane).regs (firstDrainScanSaved p cta lane) :=
      ((holds_append ..).mp hPre.2.2).2
    rw [drainFirstRouteInputs,hlane]
    exact ht.mono ⟨hSrc ▸ hPre.1,hFixed.1,hFixed.2.1,
      hSum ▸ hPre.2.1,hFixed.2.2.2.2.2.2.1,hFixed.2.2.1,hFixed.2.2.2.1,
      hFixed.2.2.2.2.1,hFixed.2.2.2.2.2.1,trivial⟩
  refine ⟨shuffles,ends,?_⟩
  change if cta < count * p.heads then _ else _
  by_cases hFound : cta < count * p.heads
  · rw [ite_eq_left hFound]
    apply all.advanceLocal (pc' := 3086) (G := drainFinishFacts p 0 cta)
    intro lane hl
    rcases drainFirstRouteLocal hp hCountSigned hCTA hFit (hPrep lane hl) with
      ⟨_,u,hu,hLocal,_⟩ | ⟨hNo,_⟩
    · have hTotalPrefix : drainPrefix p 0 31 = count := by
        change prefixWindow contribute 32 31 = count at hCount
        rwa [prefixWindow_warp contribute (show 31 < 32 by decide)] at hCount
      refine ⟨u,hLocal,?_⟩
      simp only [drainFinishFacts,hTotalPrefix,Nat.zero_add]
      exact hu
    · omega
  · rw [ite_eq_right hFound]
    apply all.advanceLocal (pc' := 3032) (G := drainNextFacts p l g 0 cta)
    intro lane hl
    rcases drainFirstRouteLocal hp hCountSigned hCTA hFit (hPrep lane hl) with
      ⟨hYes,_⟩ | ⟨_,u,hu,hLocal,_⟩
    · omega
    · exact ⟨u,hLocal,hu⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
