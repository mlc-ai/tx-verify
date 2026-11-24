-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSecondPrefix
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKLaterPrefixShuffle

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- A packet pair selects one of the two saved K row pointers for its source lane. -/
def primingKPairBases (p : Params) (batch head tile warp : Nat) (pair : Fin 16)
    (lane : Nat) : Nat :=
  primingKRowPointer p batch head (primingLaneRow tile (32 * warp + lane) + 64 * (pair.val / 8))

private theorem traceAfter {X : Execution} {g i j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hle : i ≤ j) : (X.tr g).drop i ≠ [] := by
  intro h
  exact Nat.not_le_of_lt (List.getElem?_eq_some_iff.mp he).1
    ((List.drop_eq_nil_iff.mp h).trans hle)

set_option maxRecDepth 100000 in
/-- Either saved K pointer reaches the actual pair broadcast with the exact tail predicate. -/
theorem primingKPairOperandsInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g batch head tile warp lane index rank stored : Nat}
    {s : TState} {ending : Option TState}
    (hWarp : 14 ≤ Prologue.warpIndex l g) (hb : batch < p.batch) (hh : head < p.kvHeads)
    (hTile : 128 * tile + 127 < 2 ^ 31)
    (hs : At s 544 (primingKSourceInputs p l batch tile warp
      (primingKPairBases p batch head tile warp 0) lane))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hRank : ((X.tr g).take index).countP Execution.isShfl = rank)
    {a : Acc} {bs : List (Option Byte)} (hFirst : X.get (g, stored) = some ⟨543, .rd a bs⟩)
    (hSaved : PrimingCellValue X g stored 534 (sourceScratchAccess l g 1)
      (b64 (primingKPairBases p batch head tile warp 8 lane)).toBytes)
    (i : Fin 15) {j : Nat} {target : Event} (he : X.get (g, j) = some target) (hBefore : index ≤ j)
    (hLater : kCopyPc (primingKLaterPair i) - 5 < target.pc ∨
      (Execution.isShfl target = true ∧
        rank + 2 * (i.val + 1) ≤ ((X.tr g).take j).countP Execution.isShfl))
    (hSafe : ∀ f, target.kind ≠ .ub f) :
    let pair := primingKLaterPair i
    let F := primingKLaterFrame p l batch tile warp (primingKPairBases p batch head tile warp pair)
      i lane
    ∃ t pos stop, pos ≤ j ∧
      At t (kCopyPc pair - 5) (primingKPairPredicate p batch tile warp i lane :: F) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) stop ∧
      ((X.tr g).take pos).countP Execution.isShfl = rank + 2 * (i.val + 1) := by
  let pair := primingKLaterPair i
  let F := primingKLaterFrame p l batch tile warp
    (primingKPairBases p batch head tile warp pair) i lane
  have hPairSite : primingKPredicatePc pair ≤ kCopyPc pair - 5 := by fin_cases i <;> decide
  by_cases hLow : i.val < 7
  · let firstHalf : Fin 7 := ⟨i.val, hLow⟩
    have hPair : primingKFirstHalfPair firstHalf = pair := rfl
    have hFirst : pair.val / 8 = 0 := by
      change (i.val + 1) / 8 = 0
      omega
    have hFrame : F = primingKPacketFrame p l batch tile warp
        (primingKPairBases p batch head tile warp 0) lane := by
      simp [F, primingKLaterFrame, primingKPacketFrame, primingKSourceInputs, primingKPointerReg,
        hLow, primingKPairBases, hFirst]
    obtain ⟨v, pos, stop, hPos, hv, hvRun, hvRank⟩ :=
      primingKLaterFirstHalfPrefixReady hs hr hRank firstHalf he hBefore
        (hLater.imp_left (fun h => by rw [hPair]; exact hPairSite.trans h.le)) hSafe
    have hvAt : At v (primingKPredicatePc pair) F := by rwa [hFrame, ← hPair]
    obtain ⟨u, hu, huAt⟩ := primingKLaterLaneMask hp (g := g) hb hTile i (by omega) hvAt
    exact ⟨u, pos, stop, hPos, huAt, hvRun.after_local_nonempty hu (traceAfter he hPos), hvRank⟩
  have hHigh : 7 ≤ i.val := by omega
  have hPC : 610 ≤ kCopyPc pair - 5 := by
    fin_cases i <;> first | contradiction | decide
  have hNext : 609 < target.pc ∨ (Execution.isShfl target = true ∧
        rank + 16 ≤ ((X.tr g).take j).countP Execution.isShfl) :=
    hLater.imp (fun h => (by decide : 609 < 610).trans (hPC.trans_lt h))
      (fun ⟨hShfl, hCount⟩ => ⟨hShfl, by omega⟩)
  obtain ⟨v, pos, stop, hPos, hv, hvRun, hvRank⟩ :=
    primingKSecondPointerInPrefix hp hX hWarp hb hh hTile hs hr hRank hFirst hSaved
      he hBefore hNext hSafe
  have hSlot : pair.val / 8 = 1 := by have := i.isLt; change (i.val + 1) / 8 = 1; omega
  have hFrame : Holds v.regs F := by
    have hLowWord : v.regs 1871 = some (b32 (primingKPairBases p batch head tile warp pair lane %
        2 ^ 32)) := by
      simpa only [primingKPairBases, hSlot, Nat.mul_one] using hv.2.2.2.2.1
    have hHighWord : v.regs 1872 = some (b32 (primingKPairBases p batch head tile warp pair lane /
        2 ^ 32)) := by
      simpa only [primingKPairBases, hSlot, Nat.mul_one] using hv.2.2.2.2.2.1
    have hBase : Holds v.regs (primingKSourceFrame p l batch tile warp lane) :=
      hv.2.2.2.2.2.2.2.2.2.2
    exact ⟨hv.2.2.2.2.2.2.2.1, by
      simpa only [primingKPointerReg, ite_eq_right hLow] using hLowWord, by
      simpa only [primingKPointerReg, ite_eq_right hLow] using hHighWord, hBase⟩
  by_cases hEight : i.val = 7
  · have hi : i = 7 := Fin.ext hEight
    subst i
    exact ⟨v, pos, stop, hPos, hv.mono ⟨hv.2.2.2.2.2.2.1, hFrame⟩, hvRun, hvRank⟩
  let cut := primingKPredicatePc pair
  have hRange : 610 ≤ cut ∧ cut ≤ 1901 := by
    fin_cases i <;> first | contradiction | decide
  have hCount : loaderShuffleTail cut 610 = 2 * (i.val - 7) := by
    fin_cases i <;> first | contradiction | (set_option maxRecDepth 100000 in kernel_rfl)
  have hReach : cut ≤ target.pc ∨ (Execution.isShfl target = true ∧
      ((X.tr g).take pos).countP Execution.isShfl + loaderShuffleTail cut 610 ≤
      ((X.tr g).take j).countP Execution.isShfl) := by
    rw [hvRank, hCount]
    exact hLater.imp (fun h => hPairSite.trans h.le)
      (fun ⟨hShfl, hOrdinal⟩ => ⟨hShfl, by omega⟩)
  have hTarget : ∃ ins, kernel.code[cut]? = some ins ∧ loaderVector ins.op = false := by
    have hCode : (kernel.code[cut]?).any (fun ins => !loaderVector ins.op) = true := by
      fin_cases i <;> first | contradiction | (set_option maxRecDepth 100000 in kernel_rfl)
    cases hGet : kernel.code[cut]? with
    | none => simp [hGet] at hCode
    | some ins => exact ⟨ins, rfl, by simpa [hGet] using hCode⟩
  obtain ⟨w, passed, stop', _, hw, hwRun, hwRank, hwOrder⟩ :=
    prefixCountedShuffleCut (F := F) ⟨by decide, hRange⟩ (by
      intro branch
      fin_cases i <;> first | contradiction | (set_option maxRecDepth 100000 in kernel_rfl)) (by
      fin_cases i <;> first | contradiction | (set_option maxRecDepth 100000 in kernel_rfl))
      hTarget (hv.mono hFrame) hvRun he hPos hReach hSafe
  obtain ⟨u, hu, huAt⟩ := primingKLaterLaneMask hp (g := g) hb hTile i hEight hw
  refine ⟨u, pos + passed.length, stop', hwOrder, huAt,
    hwRun.after_local_nonempty hu (traceAfter he hwOrder), ?_⟩
  rw [hwRank, hvRank, hCount]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Loader
