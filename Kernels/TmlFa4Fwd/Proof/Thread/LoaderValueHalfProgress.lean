-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPacket
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderValuePairProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.AsyncCopy Prologue Epilogue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch tile warp shuffles votes : Nat}
include hp hMax

private theorem vPairNextOfMaximal (hg : g < l.threads) (pair : Fin 16) (bases residual : Nat → Nat)
    (hBases : ∀ lane < 32, bases lane < 2 ^ 64 ∧ bases lane % 16 = 0) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (vPacketShufflePc pair)
      (fun lane => primingVReloadWords (vPacketSlot pair) (bases lane) ++
        vPairCarry (p := p) (l := l) (batch := batch) (tile := tile) (warp := warp)
          pair residual lane) shuffles votes ends) :
    ∃ next : SchedulerWarpReached l X g (vCopyPc pair + 2)
        (fun lane => primingVReloadWords (vPacketSlot pair) (bases lane) ++
          vPacketCarry p l batch tile warp lane residual) (shuffles + 2) votes ends,
      ∀ lane < 32, ∀ upper : Bool,
        let thread := warpLane l g lane
        let tid := 32 * warp + lane
        X.get (thread, next.pos lane - 2 + if upper then 1 else 0) =
          some ⟨vCopyPc pair + if upper then 1 else 0,
            .copy (vPacketCopySpec l thread tid (bases (vPacketSender pair lane))
              (vPacketBytes p batch tile tid pair) pair upper)⟩ := by
  obtain ⟨next, hNext⟩ := primingVPairOfMaximal hp hMax hg pair (fun lane => 32 * warp + lane) bases
    (fun lane => vPacketBytes p batch tile (32 * warp + lane) pair) hBases
    (fun _ _ => kvCopySize_le ..)
    (fun lane _ => vPairFrame p l batch tile warp lane pair (bases lane) residual) cur
  obtain ⟨ready, hPos,hBefore⟩ := next.toSchedulerWarpAt.advanceLocalPreserving
    (pc' := vCopyPc pair + 2)
    (G := fun lane => primingVReloadWords (vPacketSlot pair) (bases lane) ++
      vPacketCarry p l batch tile warp lane residual) (by
    intro lane hl
    have hs := next.checkpoint lane hl
    have h := (holds_append _ (primingVReloadWords (vPacketSlot pair) (bases lane)) _).mp
      hs.2.2.2.2.2
    have hTail : Holds (next.state lane).regs (vPacketFrame p l batch tile warp lane residual) := by
      by_cases hZero : pair.val = 0
      · simpa [vPairCarry, hZero] using h.2
      · have hb : Holds (next.state lane).regs
            (vPacketCarry p l batch tile warp lane residual) := by
          simpa [vPairCarry, hZero] using h.2
        exact hb.2
    exact ⟨next.state lane, .refl, hs.mono ((holds_append ..).mpr ⟨h.1, hs.2.2.2.2.1, hTail⟩)⟩)
  exact ⟨next.reframe ready hPos hBefore, hPos.symm ▸ hNext⟩

private theorem vPacketAfterHeadOfMaximal (hg : g < l.threads) (slot : Fin 2)
    (bases residual : Nat → Nat) (hBases : ∀ lane < 32, bases lane < 2 ^ 64 ∧ bases lane % 16 = 0)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g ((primingVPointerReload slot).pc + 1)
      (fun lane => primingVReloadWords slot (bases lane) ++
        if slot.val = 0 then vPacketFrame p l batch tile warp lane residual
        else vPacketCarry p l batch tile warp lane residual) shuffles votes ends) :
    ∃ next : SchedulerWarpReached l X g (vHalfHeadPc slot)
        (vHalfFrame p l batch tile warp slot bases residual) (shuffles + 2) votes ends,
      VPacketPairIssued p l X g batch tile warp (vHalfPair slot 0) bases
        (fun lane => next.pos lane - 2) := by
  let pair := vHalfPair slot 0
  have hPc : (primingVPointerReload slot).pc + 1 = vPacketShufflePc pair := by
    fin_cases slot <;> decide
  have hf : (fun lane => primingVReloadWords slot (bases lane) ++
        if slot.val = 0 then vPacketFrame p l batch tile warp lane residual
        else vPacketCarry p l batch tile warp lane residual) =
      (fun lane => primingVReloadWords (vPacketSlot pair) (bases lane) ++
        vPairCarry (p := p) (l := l) (batch := batch) (tile := tile) (warp := warp)
          pair residual lane) := by
    funext lane
    change _ = primingVReloadWords (vPacketSlot (vHalfPair slot 0)) (bases lane) ++
      vPairCarry (p := p) (l := l) (batch := batch) (tile := tile) (warp := warp)
        (vHalfPair slot 0) residual lane
    rw [vHalfSlot]
    fin_cases slot <;> simp [vPairCarry, vHalfPair]
  obtain ⟨next, hNext⟩ := vPairNextOfMaximal hp hMax hg pair bases residual hBases (hf ▸ hPc ▸ cur)
  have hFrame : (fun lane => primingVReloadWords (vPacketSlot pair) (bases lane) ++
      vPacketCarry p l batch tile warp lane residual) =
      vHalfFrame p l batch tile warp slot bases residual := by
    funext lane
    rw [vHalfSlot]
    rfl
  obtain ⟨after, hPos,hBefore⟩ := next.toSchedulerWarpAt.advanceLocalPreserving
    (pc' := vHalfHeadPc slot)
    (G := vHalfFrame p l batch tile warp slot bases residual) (by
      intro lane hl
      exact ⟨next.state lane, .refl, by rw [← hFrame]; exact next.checkpoint lane hl⟩)
  refine ⟨next.reframe after hPos hBefore,?_⟩
  change VPacketPairIssued p l X g batch tile warp pair bases (fun lane => after.pos lane - 2)
  rw [hPos]
  exact hNext

private theorem vHalfTailOfMaximal (hg : g < l.threads) (slot : Fin 2) (bases residual : Nat → Nat)
    (hBases : ∀ lane < 32, bases lane < 2 ^ 64 ∧ bases lane % 16 = 0) {ends : Nat → Option TState}
    (start : SchedulerWarpReached l X g (vHalfHeadPc slot)
      (vHalfFrame p l batch tile warp slot bases residual) shuffles votes ends) {n : Nat}
    (hn : n ≤ 7) :
    ∃ _last : SchedulerWarpReached l X g (vHalfHeadPc slot + 6 * n)
        (vHalfFrame p l batch tile warp slot bases residual) (shuffles + 2 * n) votes ends,
      ∃ pos : Fin 8 → Nat → Nat, ∀ j : Fin 8, 0 < j.val → j.val ≤ n →
        VPacketPairIssued p l X g batch tile warp (vHalfPair slot j) bases (pos j) := by
  induction n with
  | zero =>
    refine ⟨start, fun _ _ => 0, fun j hPos hj => ?_⟩
    omega
  | succ n ih =>
    obtain ⟨cur, pos, hPos⟩ := ih (by omega)
    let j : Fin 8 := ⟨n + 1, by omega⟩
    let pair := vHalfPair slot j
    have hPc : vHalfHeadPc slot + 6 * n = vPacketShufflePc pair := by
      have hSlots : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
      rcases hSlots slot with rfl | rfl
      · change 812 + 6 * n = 810 + 6 * (0 + (n + 1)) +
          (if 0 + (n + 1) < 8 then 0 else 1) - (if 0 + (n + 1) = 0 then 5 else 4)
        rw [Nat.zero_add, ite_eq_left (by omega), ite_eq_right (by omega)]
        omega
      · change 861 + 6 * n = 810 + 6 * (8 + (n + 1)) +
          (if 8 + (n + 1) < 8 then 0 else 1) - (if 8 + (n + 1) = 0 then 5 else 4)
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        omega
    have hOut : vCopyPc pair + 2 = vHalfHeadPc slot + 6 * (n + 1) := by
      have hSlot := slot.isLt
      change 810 + 6 * (8 * slot.val + (n + 1)) +
        (if 8 * slot.val + (n + 1) < 8 then 0 else 1) + 2 =
        (810 + 6 * (8 * slot.val + 0) + (if 8 * slot.val + 0 < 8 then 0 else 1)) + 2 +
        6 * (n + 1)
      split_ifs <;> omega
    have hPair : pair.val ≠ 0 := by change 8 * slot.val + (n + 1) ≠ 0; omega
    have hFrame1 : vHalfFrame p l batch tile warp slot bases residual =
        (fun lane => primingVReloadWords (vPacketSlot pair) (bases lane) ++
          vPairCarry (p := p) (l := l) (batch := batch) (tile := tile) (warp := warp)
            pair residual lane) := by
      funext lane
      rw [vHalfSlot]
      simp [vHalfFrame, vPairCarry, hPair]
    obtain ⟨next, hNext⟩ := vPairNextOfMaximal hp hMax hg pair bases residual hBases
      (hFrame1 ▸ hPc ▸ cur)
    have hFrame2 : (fun lane => primingVReloadWords (vPacketSlot pair) (bases lane) ++
        vPacketCarry p l batch tile warp lane residual) =
        vHalfFrame p l batch tile warp slot bases residual := by
      funext lane
      rw [vHalfSlot]
      rfl
    have hShuffles : shuffles + 2 * n + 2 = shuffles + 2 * (n + 1) := by omega
    refine ⟨hShuffles ▸ hFrame2 ▸ hOut ▸ next,
      fun i => if i = j then fun lane => next.pos lane - 2 else pos i, ?_⟩
    intro i hi hn'
    by_cases hij : i = j
    · subst i
      change VPacketPairIssued p l X g batch tile warp pair bases
        (if j = j then fun lane => next.pos lane - 2 else pos j)
      rw [ite_eq_left (Eq.refl j)]
      exact hNext
    · have hv : i.val ≠ j.val := fun e => hij (Fin.ext e)
      simpa only [ite_eq_right hij] using hPos i hi (by dsimp [j] at hv; omega)

/-- A reached loader records all eight copy pairs from one saved V pointer slot. -/
theorem vPacketHalfOfMaximal (hg : g < l.threads) (slot : Fin 2) (bases residual : Nat → Nat)
    (hBases : ∀ lane < 32, bases lane < 2 ^ 64 ∧ bases lane % 16 = 0) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g ((primingVPointerReload slot).pc + 1)
      (fun lane => primingVReloadWords slot (bases lane) ++
        if slot.val = 0 then vPacketFrame p l batch tile warp lane residual
        else vPacketCarry p l batch tile warp lane residual) shuffles votes ends) :
    ∃ _last : SchedulerWarpReached l X g (vHalfHeadPc slot + 42)
        (vHalfFrame p l batch tile warp slot bases residual) (shuffles + 16) votes ends,
      ∃ pos : Fin 8 → Nat → Nat, ∀ j : Fin 8,
        VPacketPairIssued p l X g batch tile warp (vHalfPair slot j) bases (pos j) := by
  obtain ⟨head, hHead⟩ := vPacketAfterHeadOfMaximal hp hMax hg slot bases residual hBases cur
  obtain ⟨last, pos, hTail⟩ :=
    vHalfTailOfMaximal hp hMax hg slot bases residual hBases head (n := 7) (by decide)
  have hOrd : shuffles + 2 + 2 * 7 = shuffles + 16 := by omega
  refine ⟨hOrd ▸ last, fun j => if j = 0 then fun lane => head.pos lane - 2 else pos j, ?_⟩
  intro j
  by_cases hj : j = 0
  · subst j
    exact hHead
  · have hVal : j.val ≠ 0 := fun he => hj (Fin.ext he)
    have := j.isLt
    simpa only [ite_eq_right hj] using hTail j (by omega) (by omega)

end PTX.Kernels.TmlFa4Fwd.Loader
