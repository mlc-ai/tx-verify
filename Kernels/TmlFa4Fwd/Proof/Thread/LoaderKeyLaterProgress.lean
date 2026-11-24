-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderKeyCopyProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKPacket
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue Prologue

noncomputable section

private theorem primingKLaterBroadcastOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch tile warp shuffles votes : Nat} (hg : g < l.threads)
    (bases : Nat → Nat) (j : Fin 15)
    {ends : Nat → Option TState}
    (cur : Epilogue.SchedulerWarpReached l X g (kCopyPc (primingKLaterPair j) - 5)
      (fun lane => primingKPairPredicate p batch tile warp j lane ::
        primingKLaterFrame p l batch tile warp bases j lane) shuffles votes ends) :
    Nonempty (Epilogue.SchedulerWarpReached l X g (kCopyPc (primingKLaterPair j) - 3)
      (fun lane =>
        let base := bases (pointerBroadcastLane lane + primingKBroadcastSlot j)
        (primingKBroadcastReg j, b32 (base % 2 ^ 32)) ::
        (primingKBroadcastReg j + 1, b32 (base / 2 ^ 32)) ::
        primingKPairPredicate p batch tile warp j lane ::
          primingKLaterFrame p l batch tile warp bases j lane) (shuffles + 2) votes ends) := by
  let F := fun lane => primingKPairPredicate p batch tile warp j lane ::
    primingKLaterFrame p l batch tile warp bases j lane
  let reg := primingKBroadcastReg j
  let sender := fun lane => (shflSource .idx lane (primingKBroadcastSlot j) 6175).1
  have hFresh (lane : Nat) (word : Fin 2) : ∀ pair ∈ F lane, pair.1 ≠ reg + word.val := by
    intro pair hm
    have hJ := j.isLt
    have hW := word.isLt
    simp only [F, primingKPairPredicate, primingKLaterFrame,
      primingKSourceFrame, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h <;>
      rw [h] <;> simp only [reg, primingKBroadcastReg, primingKLaterPair, primingKPointerReg] <;>
      split_ifs <;> omega
  have hEvent0 (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) = .ev
        (.shfl .idx (b32 (bases lane % 2 ^ 32)) (primingKBroadcastSlot j) 6175
          (fun v _ => next (setReg (cur.state lane) reg v))) := by
    have ht := cur.checkpoint lane hl
    apply primingPointerWordTemplate (by rw [hp.block]) (Nat.mod_lt _ (by decide))
      (by rw [ht.1]; fin_cases j <;> decide) (by rw [ht.1]; fin_cases j <;> decide) ht.2.2.2.1
    · rw [ht.1]; exact primingKLaterShuffleCode j 0
    · exact holds_lookup ht.2.2.2.2 (by fin_cases j <;> rfl)
  obtain ⟨first⟩ := cur.consumeShuffle hp hMax hg .idx (fun lane => b32 (bases lane % 2 ^ 32))
    (fun _ => primingKBroadcastSlot j) (fun _ => 6175) (fun lane _ => hFresh lane 0) hEvent0
  have hFresh1 (lane : Nat) (_ : lane < 32) :
      ∀ pair ∈ (reg, b32 (bases (sender lane) % 2 ^ 32)) :: F lane, pair.1 ≠ reg + 1 := by
    intro pair hm
    rcases List.mem_cons.mp hm with rfl | hm
    · simp
    · exact hFresh lane 1 pair hm
  have hEvent1 (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (warpLane l g lane) (first.state lane) = .ev
        (.shfl .idx (b32 (bases lane / 2 ^ 32)) (primingKBroadcastSlot j) 6175
          (fun v _ => next (setReg (first.state lane) (reg + 1) v))) := by
    have ht := first.checkpoint lane hl
    apply primingPointerWordTemplate (by rw [hp.block]) (Nat.mod_lt _ (by decide))
      (by rw [ht.1]; fin_cases j <;> decide) (by rw [ht.1]; fin_cases j <;> decide) ht.2.2.2.1
    · rw [ht.1]; exact primingKLaterShuffleCode j 1
    · exact holds_lookup ht.2.2.2.2 (by fin_cases j <;> rfl)
  obtain ⟨second⟩ := first.consumeShuffle hp hMax hg .idx (fun lane => b32 (bases lane / 2 ^ 32))
    (fun _ => primingKBroadcastSlot j) (fun _ => 6175) hFresh1 hEvent1
  have hPc : kCopyPc (primingKLaterPair j) - 5 + 1 + 1 =
      kCopyPc (primingKLaterPair j) - 3 := by fin_cases j <;> decide
  apply second.advanceLocal
  intro lane hl
  let src : Fin 8 := ⟨primingKBroadcastSlot j, Nat.mod_lt _ (by decide)⟩
  have hFrom : sender lane = pointerBroadcastLane lane + primingKBroadcastSlot j := by
    simpa only [sender, src, pointerBroadcastLane, Nat.add_assoc] using
      congrArg Prod.fst (kv_shuffle_source ⟨lane, hl⟩ src)
  have ht := second.checkpoint lane hl
  refine ⟨second.state lane, .refl, ht.1.trans hPc, ht.2.1, ht.2.2.1, ht.2.2.2.1, ?_⟩
  have hZero : (0 : Fin 2).val = 0 := rfl
  exact ⟨by simpa only [sender, hFrom, hZero, Nat.add_zero] using ht.2.2.2.2.2.1,
    by simpa only [sender, hFrom] using ht.2.2.2.2.1, ht.2.2.2.2.2.2⟩

/-- A reached K mask and broadcast record both actual vectors of the selected row. -/
theorem primingKCopyAfterMaskOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch tile warp shuffles votes : Nat} (hg : g < l.threads)
    (bases : Nat → Nat) (hBases : ∀ lane < 32, bases lane < 2 ^ 64 ∧ bases lane % 16 = 0)
    (j : Fin 15) {ends : Nat → Option TState} :
    let pair := primingKLaterPair j
    let F := primingKLaterFrame p l batch tile warp bases j
    Epilogue.SchedulerWarpReached l X g (kCopyPc pair - 5)
      (fun lane => primingKPairPredicate p batch tile warp j lane :: F lane) shuffles votes ends →
    ∃ next : Epilogue.SchedulerWarpReached l X g (kCopyPc pair + 2) F (shuffles + 2) votes ends,
      (∀ lane < 32, 2 ≤ next.pos lane) ∧ ∀ lane < 32, ∀ upper : Bool,
        let tid := 32 * warp + lane
        let src := (bases (pointerBroadcastLane lane + primingKBroadcastSlot j) +
          2 * kvCopyColumn tid false) % 2 ^ 64
        let size := kvCopySize (p.kLength batch) tile tid pair
        X.get (warpLane l g lane, next.pos lane - 2 + if upper then 1 else 0) =
          some ⟨kCopyPc pair + if upper then 1 else 0,
            .copy (kCopySpec l (warpLane l g lane) 0 tid src size pair upper)⟩ := by
  dsimp only
  intro checking
  let F := primingKLaterFrame p l batch tile warp bases j
  let pair := primingKLaterPair j
  let tid := fun lane => 32 * warp + lane
  let source := fun lane => bases (pointerBroadcastLane lane + primingKBroadcastSlot j)
  let addr := fun lane => (source lane + 2 * kvCopyColumn (tid lane) false) % 2 ^ 64
  let size := fun lane => kvCopySize (p.kLength batch) tile (tid lane) pair
  obtain ⟨broadcast⟩ := primingKLaterBroadcastOfMaximal hp hMax hg bases j checking
  let events : Nat → List Event := fun lane => [
    ⟨kCopyPc pair, .copy (kCopySpec l (warpLane l g lane) 0 (tid lane)
      (addr lane) (size lane) pair false)⟩,
    ⟨kCopyPc pair + 1, .copy (kCopySpec l (warpLane l g lane) 0 (tid lane)
      (addr lane) (size lane) pair true)⟩]
  have step (lane : Nat) (hl : lane < 32) : ∃ u,
      (X.tr (warpLane l g lane)).drop (broadcast.pos lane) =
        events lane ++ (X.tr (warpLane l g lane)).drop (broadcast.pos lane + 2) ∧
      Run kernel Assumptions.all l (warpLane l g lane) {}
        ((X.tr (warpLane l g lane)).take (broadcast.pos lane+2)) (some u) ∧
      Run kernel Assumptions.all l (warpLane l g lane) u
        ((X.tr (warpLane l g lane)).drop (broadcast.pos lane+2)) (ends lane) ∧
      At u (kCopyPc pair+2) (F lane) ∧
      broadcast.pos lane+2 ≤ (X.tr (warpLane l g lane)).length ∧
      (broadcast.pos lane+2 = (X.tr (warpLane l g lane)).length →
        Step.Released l X (warpLane l g lane)) := by
    have hSender : pointerBroadcastLane lane + primingKBroadcastSlot j < 32 := by
      have := j.isLt
      have hSlot : primingKBroadcastSlot j < 8 := Nat.mod_lt _ (by decide)
      unfold pointerBroadcastLane
      omega
    obtain ⟨hBase, hAlign⟩ := hBases _ hSender
    let live := decide (kvCopyRow tile (tid lane) pair < p.kLength batch)
    have ht := broadcast.checkpoint lane hl
    obtain ⟨u, hu, hU⟩ := primingKLaterAddress l (warpLane l g lane) (tid := tid lane)
      hBase j live (broadcast.state lane) (ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1,
        holds_lookup ht.2.2.2.2 (by fin_cases j <;> rfl), ht.2.2.2.2.2.2.1, trivial⟩)
    obtain ⟨huA, keep⟩ := loaderLinear (regs := (F lane).map Prod.fst)
      (by fin_cases j <;> decide) (by fin_cases j <;> decide) ht.1
      (by fin_cases j <;> (set_option maxRecDepth 100000 in kernel_rfl))
      (by fin_cases j <;> (set_option maxRecDepth 100000 in kernel_rfl)) hu
    have hFrame := Epilogue.holdsSchedulerFrame ht.2.2.2.2.2.2.2 keep
      (fun _ hm => List.mem_map_of_mem hm)
    have hDst : u.regs (kCopyDstReg pair) = some
        (b32 (kvCopyAddress l.sharedBase 0 (tid lane) (pair.val % 2) false)) := by
      by_cases he : pair.val % 2 = 0
      · rw [kCopyDstReg, ite_eq_left he, he]
        exact holds_lookup hFrame (by fin_cases j <;> rfl)
      · have ho : pair.val % 2 = 1 := by omega
        rw [kCopyDstReg, ite_eq_right he, ho]
        exact holds_lookup hFrame (by fin_cases j <;> rfl)
    have hAt : At u (kCopyPc pair) (kCopyFacts l 0 (tid lane) (addr lane) (size lane) pair) := by
      have hSize : size lane = (if live then 16 else 0) := by simp [size, kvCopySize, live]
      rw [hSize]
      exact hU.mono ⟨hDst, hU.2.2.2.2⟩
    have hAddr : addr lane % 16 = 0 := by
      unfold addr
      rw [Nat.mod_mod_of_dvd _ (show 16 ∣ (2 : Nat) ^ 64 by decide)]
      simp [source, kvCopyColumn, Nat.add_mod, hAlign]
      omega
    have hBlock : l.block%32 = 0 := by rw [hp.block]
    have hActor := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
    obtain ⟨hLo,hHi,hPast,hTail⟩ := kCopyPairOfMaximal hp hMax (g := warpLane l g lane)
      hActor (by decide) (Nat.mod_lt _ (by decide)) hAddr (kvCopySize_le ..) pair hAt
      ((broadcast.localSteps lane hl).trans (run_rtg huA)) (broadcast.recorded lane hl)
      (broadcast.continuation lane hl) (broadcast.positive lane hl) (broadcast.bounded lane hl)
      (broadcast.released lane hl)
    have hStop : broadcast.pos lane+2 = broadcast.pos lane+1+1 := by omega
    refine ⟨next (next u),?_,hPast,hTail,?_,?_,?_⟩
    · have lo := List.getElem?_eq_some_iff.mp hLo
      have hi := List.getElem?_eq_some_iff.mp hHi
      rw [List.drop_eq_getElem_cons lo.1,lo.2,List.drop_eq_getElem_cons hi.1,hi.2,hStop]
      rfl
    · simpa only [Nat.add_assoc] using hAt.next.next.mono hFrame
    · rw [hStop]; exact len_of_get hHi
    · rw [hStop]; exact releasedIfLast hHi (by intro h; cases h)
  let _ : Nonempty TState := ⟨broadcast.state 0⟩
  choose! u hTrace hPast hRun hAt hBound hRelease using step
  have hCounts := broadcast.ordinals.advance events (fun lane hl => ⟨_, hTrace lane hl⟩)
    (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨⟨⟨fun lane => broadcast.pos lane+2,u,u,hCounts,hRun,fun _ _ => .refl,hAt⟩,
    fun lane hl => (broadcast.positive lane hl).trans_le (Nat.le_add_right _ _),
    hBound,hRelease,hPast⟩,fun _ _ => Nat.le_add_left _ _,fun lane hl upper => ?_⟩
  dsimp only
  rw [Nat.add_sub_cancel]
  change (X.tr (warpLane l g lane))[broadcast.pos lane + (if upper then 1 else 0)]? = _
  rw [← List.getElem?_drop, hTrace lane hl]
  cases upper <;> rfl

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch tile warp shuffles votes : Nat}
    (hg : g < l.threads) (hLen : p.kLength batch < 2 ^ 31) (hTile : 128 * tile + 7 < 2 ^ 31)
    (bases : Nat → Nat) (hBases : ∀ lane < 32, bases lane < 2 ^ 64 ∧ bases lane % 16 = 0)
include hp hMax hg hLen hTile bases hBases

/-- A pair with an immediately preceding mask uses the shared broadcast and copy step. -/
theorem primingKMaskedPairOfMaximal (j : Fin 15) (hSkip : j.val ≠ 7) {ends : Nat → Option TState} :
    let pair := primingKLaterPair j
    let F := primingKLaterFrame p l batch tile warp bases j
    Epilogue.SchedulerWarpReached l X g (primingKPredicatePc pair) F shuffles votes ends →
    ∃ next : Epilogue.SchedulerWarpReached l X g (kCopyPc pair + 2) F (shuffles + 2) votes ends,
      (∀ lane < 32, 2 ≤ next.pos lane) ∧ ∀ lane < 32, ∀ upper : Bool,
        let tid := 32 * warp + lane
        let src := (bases (pointerBroadcastLane lane + primingKBroadcastSlot j) +
          2 * kvCopyColumn tid false) % 2 ^ 64
        let size := kvCopySize (p.kLength batch) tile tid pair
        X.get (warpLane l g lane, next.pos lane - 2 + if upper then 1 else 0) =
          some ⟨kCopyPc pair + if upper then 1 else 0,
            .copy (kCopySpec l (warpLane l g lane) 0 tid src size pair upper)⟩ := by
  dsimp only
  intro cur
  let F := primingKLaterFrame p l batch tile warp bases j
  let pair := primingKLaterPair j
  let tid := fun lane => 32 * warp + lane
  have hShape : ∀ i : Fin 15, i.val ≠ 7 →
      174 ≤ primingKPredicatePc (primingKLaterPair i) ∧
      primingKPredicatePc (primingKLaterPair i) + 1 ≤ 1906 ∧
      primingKPredicatePc (primingKLaterPair i) + 1 = kCopyPc (primingKLaterPair i) - 5 := by
    decide
  obtain ⟨hLow, hHigh, hPredicate⟩ := hShape j hSkip
  obtain ⟨checking⟩ := cur.advanceLocal (pc' := kCopyPc pair - 5)
    (G := fun lane => primingKPairPredicate p batch tile warp j lane :: F lane) (fun lane hl => by
      have ht := cur.checkpoint lane hl
      have hRow : kvCopyRow tile (tid lane) 0 < 2 ^ 31 := by unfold tid kvCopyRow; omega
      obtain ⟨u, hu, hU⟩ := primingKLaterMaskForAll (l := l) (g := warpLane l g lane) hLen hRow
        j (cur.state lane)
        (ht.mono ⟨holds_lookup ht.2.2.2.2 (by fin_cases j <;> rfl), trivial⟩)
      obtain ⟨huA, keep⟩ := loaderLinear (regs := (F lane).map Prod.fst) hLow hHigh ht.1
        (by
          fin_cases j <;> first | (exact (hSkip rfl).elim) |
            (set_option maxRecDepth 100000 in kernel_rfl)) (by simp) hu
      have hFrame := Epilogue.holdsSchedulerFrame ht.2.2.2.2 keep
        (fun _ hm => List.mem_map_of_mem hm)
      exact ⟨u, run_rtg huA, hU.1.trans hPredicate, hU.2.1, hU.2.2.1, hU.2.2.2.1,
        hU.2.2.2.2.1, hFrame⟩)
  exact primingKCopyAfterMaskOfMaximal hp hMax hg bases hBases j checking

/-- One later group before the first K pointer reload boundary. -/
theorem primingKFirstHalfPairOfMaximal (j : Fin 7) {ends : Nat → Option TState} :
    let pair := primingKFirstHalfPair j
    let F := primingKPacketFrame p l batch tile warp bases
    Epilogue.SchedulerWarpReached l X g (primingKPredicatePc pair) F shuffles votes ends →
    ∃ next : Epilogue.SchedulerWarpReached l X g (kCopyPc pair + 2) F (shuffles + 2) votes ends,
      (∀ lane < 32, 2 ≤ next.pos lane) ∧ ∀ lane < 32, ∀ upper : Bool,
        let tid := 32 * warp + lane
        let src := (bases (pointerBroadcastLane lane + pair.val) +
          2 * kvCopyColumn tid false) % 2 ^ 64
        let size := kvCopySize (p.kLength batch) tile tid pair
        X.get (warpLane l g lane, next.pos lane - 2 + if upper then 1 else 0) =
          some ⟨kCopyPc pair + if upper then 1 else 0,
            .copy (kCopySpec l (warpLane l g lane) 0 tid src size pair upper)⟩ := by
  dsimp only
  intro cur
  let step : Fin 15 := ⟨j.val, by omega⟩
  have hStep : step.val < 7 := j.isLt
  have hRegister : primingKPointerReg step = 1853 := ite_eq_left hStep
  have hFrame : primingKLaterFrame p l batch tile warp bases step =
      primingKPacketFrame p l batch tile warp bases := by
    funext lane
    simp only [primingKLaterFrame, primingKPacketFrame, primingKSourceInputs, hRegister,
      List.cons_append, List.nil_append]
  have hPair : primingKLaterPair step = primingKFirstHalfPair j := rfl
  have hSlot : primingKBroadcastSlot step = (primingKFirstHalfPair j).val := by
    exact Nat.mod_eq_of_lt (by have := j.isLt; change j.val + 1 < 8; omega)
  have hc := primingKMaskedPairOfMaximal hp hMax (batch := batch) (tile := tile) (warp := warp)
    (shuffles := shuffles) (votes := votes) (ends := ends) hg hLen hTile
    bases hBases step (by omega)
  rw [hPair, hFrame, hSlot] at hc
  exact hc cur

/-- Iterating the checked pair step reaches every cursor through the second-slot boundary. -/
theorem primingKFirstHalfOfMaximal {ends : Nat → Option TState}
    (first : Epilogue.SchedulerWarpReached l X g 552
      (primingKPacketFrame p l batch tile warp bases) shuffles votes ends) {j : Nat} (hj : j ≤ 7) :
    Nonempty (Epilogue.SchedulerWarpReached l X g (552 + 8 * j)
      (primingKPacketFrame p l batch tile warp bases) (shuffles + 2 * j) votes ends) := by
  induction j with
  | zero => exact ⟨first⟩
  | succ j ih =>
    obtain ⟨cur⟩ := ih (by omega)
    let prev : Fin 7 := ⟨j, by omega⟩
    have hPrev : primingKPredicatePc (primingKFirstHalfPair prev) = 552 + 8 * j := by
      change 550 + 8 * (j + 1) + (if j + 1 < 8 then 0 else 1) -
        (if j + 1 = 8 then 7 else 6) = 552 + 8 * j
      split_ifs <;> omega
    obtain ⟨next, _⟩ := primingKFirstHalfPairOfMaximal hp hMax hg hLen hTile bases hBases prev
      (hPrev.symm ▸ cur)
    have hNext : kCopyPc (primingKFirstHalfPair prev) + 2 = 552 + 8 * (j + 1) := by
      change 550 + 8 * (j + 1) + (if j + 1 < 8 then 0 else 1) + 2 = 552 + 8 * (j + 1)
      split_ifs <;> omega
    have hShuffles : shuffles + 2 * j + 2 = shuffles + 2 * (j + 1) := by omega
    exact ⟨hNext ▸ hShuffles ▸ next⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
