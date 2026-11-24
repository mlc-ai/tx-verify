-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPair
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderValueCopyProgress
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.AsyncCopy Prologue Epilogue

private theorem vPacketBroadcastOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads)
    (pair : Fin 16) (bases : Nat → Nat) (F : Nat → List (Nat × Value))
    (hFresh : ∀ lane < 32, ∀ fact ∈ F lane,
      fact.1 ≠ vPacketShflDst pair 0 ∧ fact.1 ≠ vPacketShflDst pair 1)
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g (vPacketShufflePc pair)
      (fun lane => primingVReloadWords (vPacketSlot pair) (bases lane) ++ F lane)
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g (vPacketShufflePc pair + 2)
      (fun lane => [(vPacketShflDst pair 0, b32 (bases (vPacketSender pair lane) % 2 ^ 32)),
        (vPacketShflDst pair 1, b32 (bases (vPacketSender pair lane) / 2 ^ 32))] ++
        (primingVReloadWords (vPacketSlot pair) (bases lane) ++ F lane))
        (shuffles + 2) votes ends) := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hSelect : vPacketSelect pair < 8 := Nat.mod_lt _ (by decide)
  let lo := fun lane => b32 (bases lane % 2 ^ 32)
  let hi := fun lane => b32 (bases lane / 2 ^ 32)
  have hReg {lane : Nat} {f : Nat × Value}
      (hm : f ∈ primingVReloadWords (vPacketSlot pair) (bases lane)) (word : Fin 2) :
      f.1 ≠ vPacketShflDst pair word := by
    fin_cases pair <;> fin_cases word <;>
      simp [primingVReloadWords, primingVPointerReload, vPacketSlot,
        vPacketShflDst, vPacketShflLow] at hm ⊢ <;>
      (rcases hm with rfl | rfl <;> simp only [Nat.reduceEqDiff, not_false_eq_true])
  obtain ⟨first⟩ := cur.consumeShuffle (dst := vPacketShflDst pair 0) hp hMax hg .idx lo
    (fun _ => vPacketSelect pair) (fun _ => 6175)
    (by
      intro lane hl fact hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hReg hm 0
      · exact (hFresh lane hl fact hm).1)
    (by
      intro lane hl
      have ht := cur.checkpoint lane hl
      apply primingPointerWordTemplate hBlock hSelect
        (by rw [ht.1]; fin_cases pair <;> decide)
        (by rw [ht.1]; fin_cases pair <;> decide) ht.2.2.2.1
      · rw [ht.1, ← Nat.add_zero (vPacketShufflePc pair)]
        exact vPacketShuffleCode pair 0
      · exact ht.2.2.2.2.1)
  obtain ⟨second⟩ := first.consumeShuffle (dst := vPacketShflDst pair 1) hp hMax hg .idx hi
    (fun _ => vPacketSelect pair) (fun _ => 6175)
    (by
      intro lane hl fact hm
      rcases List.mem_cons.mp hm with rfl | hm
      · change vPacketShflDst pair 0 ≠ vPacketShflDst pair 1
        simp [vPacketShflDst]
      · rcases List.mem_append.mp hm with hm | hm
        · exact hReg hm 1
        · exact (hFresh lane hl fact hm).2)
    (by
      intro lane hl
      have ht := first.checkpoint lane hl
      apply primingPointerWordTemplate hBlock hSelect
        (by rw [ht.1]; fin_cases pair <;> decide)
        (by rw [ht.1]; fin_cases pair <;> decide) ht.2.2.2.1
      · rw [ht.1]
        exact vPacketShuffleCode pair 1
      · rw [vPacketSrcHi]
        exact ht.2.2.2.2.2.2.1)
  apply second.advanceLocal
  intro lane hl
  have hSender : (shflSource .idx lane (vPacketSelect pair) 6175).1 = vPacketSender pair lane := by
    simpa only [vPacketSender, pointerBroadcastLane] using
      congrArg Prod.fst (kv_shuffle_source ⟨lane, hl⟩ (⟨vPacketSelect pair, hSelect⟩ : Fin 8))
  have ht := second.checkpoint lane hl
  exact ⟨second.state lane, .refl, ht.mono
    ⟨by simpa only [lo, hSender] using ht.2.2.2.2.2.1,
     by simpa only [hi, hSender] using ht.2.2.2.2.1, ht.2.2.2.2.2.2⟩⟩

/-- A maximal loader records both broadcasts and the paired V copies. -/
theorem primingVPairOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) (pair : Fin 16)
    (tid bases bytes : Nat → Nat) {F : Nat → List (Nat × Value)}
    (hBases : ∀ lane < 32, bases lane < 2 ^ 64 ∧ bases lane % 16 = 0)
    (hBytes : ∀ lane < 32, bytes lane ≤ 16)
    (hFrame : ∀ lane < 32, PrimingVPairFrame l pair (bases lane) (tid lane) (bytes lane) (F lane))
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g (vPacketShufflePc pair)
      (fun lane => primingVReloadWords (vPacketSlot pair) (bases lane) ++ F lane)
      shuffles votes ends) :
    ∃ next : SchedulerWarpReached l X g (vCopyPc pair + 2)
        (fun lane => vPacketResultFrame pair (bases lane) (tid lane) (F lane))
        (shuffles + 2) votes ends,
      ∀ lane < 32, ∀ upper : Bool,
        let thread := warpLane l g lane
        X.get (thread, next.pos lane - 2 + if upper then 1 else 0) =
          some ⟨vCopyPc pair + if upper then 1 else 0,
            .copy (vPacketCopySpec l thread (tid lane) (bases (vPacketSender pair lane))
              (bytes lane) pair upper)⟩ := by
  let carry := fun lane => primingVReloadWords (vPacketSlot pair) (bases lane) ++ F lane
  let rowBase := fun lane => bases (vPacketSender pair lane)
  let src := fun lane => (rowBase lane + 2 * kvCopyColumn (tid lane) false) % 2 ^ 64
  let spec := fun lane upper => vPacketCopySpec l (warpLane l g lane) (tid lane) (rowBase lane)
    (bytes lane) pair upper
  let events : Nat → List Event := fun lane =>
    [⟨vCopyPc pair, .copy (spec lane false)⟩, ⟨vCopyPc pair + 1, .copy (spec lane true)⟩]
  obtain ⟨broadcast⟩ := vPacketBroadcastOfMaximal hp hMax hg pair bases F
    (fun lane hl => (hFrame lane hl).shuffles) cur
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have step (lane : Nat) (hl : lane < 32) : ∃ u,
      let thread := warpLane l g lane
      let i := broadcast.pos lane
      (X.tr thread).drop i = events lane ++ (X.tr thread).drop (i + 2) ∧
      Run kernel Assumptions.all l thread {} ((X.tr thread).take (i+2)) (some u) ∧
      Run kernel Assumptions.all l thread u ((X.tr thread).drop (i+2)) (ends lane) ∧
      At u (vCopyPc pair+2) (vPacketResultFrame pair (bases lane) (tid lane) (F lane)) ∧
      i+2 ≤ (X.tr thread).length ∧
      (i+2 = (X.tr thread).length → Step.Released l X thread) := by
    obtain ⟨hBase, hAligned⟩ := hBases _ (vPacketSender_lt pair hl)
    have hs := broadcast.checkpoint lane hl
    have hCarry : Holds (broadcast.state lane).regs (carry lane) := hs.2.2.2.2.2.2
    have hData : Holds (broadcast.state lane).regs (F lane) :=
      ((holds_append _ (primingVReloadWords (vPacketSlot pair) (bases lane)) (F lane)).mp hCarry).2
    have hInput : At (broadcast.state lane) (vPacketShufflePc pair + 2)
        (vPacketAddrInputs pair (rowBase lane) (tid lane)) :=
      hs.mono ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.1, holds_mem hData (hFrame lane hl).column, trivial⟩
    obtain ⟨t, ht, hT⟩ := vPacketAddress l (warpLane l g lane) pair hBase
      (broadcast.state lane) hInput
    obtain ⟨htA, hKeep⟩ := loaderLinear (regs := (carry lane).map Prod.fst)
      (by fin_cases pair <;> decide) (by fin_cases pair <;> decide) hs.1
      (hFrame lane hl).preserved
      (by fin_cases pair <;> (set_option maxRecDepth 100000 in kernel_rfl)) ht
    have hReg : Holds t.regs (carry lane) :=
      holdsSchedulerFrame hCarry hKeep (fun _ hm => List.mem_map_of_mem hm)
    have hFrame' := ((holds_append _ (primingVReloadWords (vPacketSlot pair) (bases lane))
      (F lane)).mp hReg).2
    have hCopy : At t (vCopyPc pair) (vCopyFacts l (tid lane) (src lane) (bytes lane) pair) :=
      hT.mono ⟨holds_mem hFrame' (hFrame lane hl).destination, hT.2.2.2.2.1,
        holds_mem hFrame' (hFrame lane hl).count, trivial⟩
    have hAlign : src lane % 16 = 0 := by
      unfold src
      rw [Nat.mod_mod_of_dvd _ (show 16 ∣ (2 : Nat) ^ 64 by decide)]
      simp [kvCopyColumn, Nat.add_mod, show rowBase lane % 16 = 0 from hAligned]
      omega
    let thread := warpLane l g lane
    have hActor : thread < l.threads := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
    obtain ⟨hLo,hHi,hPast,hTail⟩ := vCopyPairOfMaximal hp hMax (g := thread)
      hActor (Nat.mod_lt _ (by decide)) hAlign (hBytes lane hl) pair hCopy
      ((broadcast.localSteps lane hl).trans (run_rtg htA))
      (broadcast.recorded lane hl) (broadcast.continuation lane hl)
      (broadcast.positive lane hl) (broadcast.bounded lane hl) (broadcast.released lane hl)
    have hIndex : broadcast.pos lane+2 = (broadcast.pos lane+1)+1 := by omega
    refine ⟨next (next t),?_,hPast,hTail,?_,?_,?_⟩
    · have hlo := List.getElem?_eq_some_iff.mp hLo
      have hhi := List.getElem?_eq_some_iff.mp hHi
      rw [List.drop_eq_getElem_cons hlo.1, hlo.2, List.drop_eq_getElem_cons hhi.1, hhi.2,hIndex]
      rfl
    · have hResult : Holds t.regs (vPacketResultFrame pair (bases lane) (tid lane) (F lane)) :=
        ⟨hT.2.2.2.2.2.1, hReg⟩
      simpa only [Nat.add_assoc] using (hT.mono hResult).next.next
    · rw [hIndex]
      exact len_of_get hHi
    · rw [hIndex]
      exact releasedIfLast hHi (by intro h; cases h)
  let _ : Nonempty TState := ⟨broadcast.state 0⟩
  choose! u hTrace hPast hRun hAt hBound hRelease using step
  have hCount := broadcast.ordinals.advance events (fun lane hl => ⟨_, hTrace lane hl⟩)
    (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨⟨⟨fun lane => broadcast.pos lane+2,u,u,hCount,hRun,fun _ _ => .refl,hAt⟩,
    fun lane hl => (broadcast.positive lane hl).trans_le (Nat.le_add_right _ _),
    hBound,hRelease,hPast⟩,fun lane hl upper => ?_⟩
  dsimp only
  rw [Nat.add_sub_cancel]
  change (X.tr (warpLane l g lane))[broadcast.pos lane + (if upper then 1 else 0)]? = _
  rw [← List.getElem?_drop, hTrace lane hl]
  cases upper <;> rfl


end PTX.Kernels.TmlFa4Fwd.Loader
