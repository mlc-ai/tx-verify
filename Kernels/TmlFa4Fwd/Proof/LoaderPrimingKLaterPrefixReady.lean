-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKPacket
import Kernels.TmlFa4Fwd.Flow.Code.Part008

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

private theorem primingKColumnBytes (l : Launch) (g tid : Nat) :
    Seg kernel [] l g 1 547 [(1082, b32 (kvCopyColumn tid false))]
      548 [(7547, b64 (2 * kvCopyColumn tid false))] := by
  have hCol : kvCopyColumn tid false < 2 ^ 32 := by
    have := Nat.mod_lt tid (by decide : 0 < 8)
    simp [kvCopyColumn]
    omega
  intro t ht
  seg_fp ht using norm_bits [Nat.mod_eq_of_lt hCol]

variable {p : Params} {l : Launch} {X : Execution} {g batch tile warp lane index rank : Nat}
    {bases : Nat → Nat} {s : TState} {ending : Option TState}
    (hs : At s 544 (primingKSourceInputs p l batch tile warp bases lane))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
include hs hr

theorem primingKColumnFrameInPrefix (hRank : ((X.tr g).take index).countP Execution.isShfl = rank)
    {j : Nat} {target : Event} (he : X.get (g, j) = some target) (hBefore : index ≤ j)
    (hLater : 547 ≤ target.pc ∨ (Execution.isShfl target = true ∧
      rank + 2 ≤ ((X.tr g).take j).countP Execution.isShfl)) (hSafe : ∀ f, target.kind ≠ .ub f) :
    ∃ t pos stop, pos ≤ j ∧
      At t 548 (primingKPacketFrame p l batch tile warp bases lane) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) stop ∧
      ((X.tr g).take pos).countP Execution.isShfl = rank + 2 := by
  let F := primingKSourceInputs p l batch tile warp bases lane
  let G := primingKPacketFrame p l batch tile warp bases lane
  have hCount : loaderShuffleTail 547 544 = 2 := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hWitness : 547 ≤ target.pc ∨ (Execution.isShfl target = true ∧
      ((X.tr g).take index).countP Execution.isShfl + loaderShuffleTail 547 544 ≤
      ((X.tr g).take j).countP Execution.isShfl) := by simpa only [hRank, hCount] using hLater
  obtain ⟨t, init, stop, _, ht, htRun, htRank, htOrder⟩ :=
    prefixCountedShuffleCut (F := F) (by decide) (by
      intro branch
      set_option maxRecDepth 100000 in kernel_rfl) (by
      set_option maxRecDepth 100000 in kernel_rfl)
      ⟨_, Flow.code_547, rfl⟩ hs hr he hBefore hWitness hSafe
  have hInput : At t 547 [(1082, b32 (kvCopyColumn (32 * warp + lane) false))] :=
    ht.mono ⟨holds_lookup ht.2.2.2.2 rfl, trivial⟩
  obtain ⟨v, hv, hvNext⟩ := primingKColumnBytes l g (32 * warp + lane) t hInput
  obtain ⟨hvA, hKeep⟩ := loaderLinear (regs := F.map Prod.fst)
    (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hvAt : At v 548 G := hvNext.mono
    ⟨hvNext.2.2.2.2.1, holdsSchedulerFrame ht.2.2.2.2 hKeep
      (fun _ h => List.mem_map_of_mem h)⟩
  have hNonempty : (X.tr g).drop (index + init.length) ≠ [] := by
    intro hNil
    exact Nat.not_le_of_lt (List.getElem?_eq_some_iff.mp he).1
      ((List.drop_eq_nil_iff.mp hNil).trans htOrder)
  have hvRun := htRun.after_local_nonempty (run_rtg hvA) hNonempty
  exact ⟨v, _, stop, htOrder, hvAt, hvRun, by rw [htRank, hRank, hCount]⟩

/-- Recover a later first-half K predicate from the first saved pointer.
A peer can use a matching shuffle ordinal as its downstream witness. -/
theorem primingKLaterFirstHalfPrefixReady
    (hRank : ((X.tr g).take index).countP Execution.isShfl = rank) (pair : Fin 7) {j : Nat}
    {target : Event} (he : X.get (g, j) = some target) (hBefore : index ≤ j)
    (hLater : primingKPredicatePc (primingKFirstHalfPair pair) ≤ target.pc ∨
      (Execution.isShfl target = true ∧
        rank + 2 * (pair.val + 1) ≤ ((X.tr g).take j).countP Execution.isShfl))
    (hSafe : ∀ f, target.kind ≠ .ub f) :
    ∃ u k stop, k ≤ j ∧
      At u (primingKPredicatePc (primingKFirstHalfPair pair))
        (primingKPacketFrame p l batch tile warp bases lane) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop k) stop ∧
      ((X.tr g).take k).countP Execution.isShfl = rank + 2 * (pair.val + 1) := by
  let G := primingKPacketFrame p l batch tile warp bases lane
  let cut := primingKPredicatePc (primingKFirstHalfPair pair)
  have hRange : 548 ≤ cut ∧ cut ≤ 1901 := by fin_cases pair <;> decide
  obtain ⟨v, pos, _, htOrder, hvAt, hvRun, htRank⟩ :=
    primingKColumnFrameInPrefix hs hr hRank he hBefore
      (hLater.imp (fun h => by change cut ≤ target.pc at h; omega)
        (fun ⟨hM, hO⟩ => ⟨hM, by omega⟩)) hSafe
  have hCount : loaderShuffleTail cut 548 = 2 * pair.val := by
    fin_cases pair <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hFinal : cut ≤ target.pc ∨ (Execution.isShfl target = true ∧
      ((X.tr g).take pos).countP Execution.isShfl + loaderShuffleTail cut 548 ≤
      ((X.tr g).take j).countP Execution.isShfl) := by
    rw [htRank, hCount]
    exact hLater.imp_right (fun ⟨hM, hO⟩ => ⟨hM, by omega⟩)
  have hTarget : ∃ ins, kernel.code[cut]? = some ins ∧ loaderVector ins.op = false := by
    have hCode : (kernel.code[cut]?).any (fun ins => !loaderVector ins.op) = true := by
      fin_cases pair <;> (set_option maxRecDepth 100000 in kernel_rfl)
    cases hGet : kernel.code[cut]? with
    | none => simp [hGet] at hCode
    | some ins => exact ⟨ins, rfl, by simpa [hGet] using hCode⟩
  obtain ⟨w, passed, stop', _, hw, hwRun, hwRank, hwOrder⟩ :=
    prefixCountedShuffleCut (F := G) ⟨by decide, hRange⟩ (by
      intro branch
      fin_cases pair <;> (set_option maxRecDepth 100000 in kernel_rfl)) (by
      fin_cases pair <;> (set_option maxRecDepth 100000 in kernel_rfl)) hTarget
      hvAt hvRun he htOrder hFinal hSafe
  refine ⟨w, pos + passed.length, stop', hwOrder, hw, hwRun, ?_⟩
  rw [hwRank, htRank, hCount]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Loader
