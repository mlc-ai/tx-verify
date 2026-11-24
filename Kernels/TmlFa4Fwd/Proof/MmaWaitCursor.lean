-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaPoll
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- A poll cursor records the success event's exact trace index and resumes with the original
frame. Its preceding attempts are failed observations at the same address and phase. -/
theorem waitAt {l : Launch} {X : Execution} {g pos addr phase : Nat} {t : TState}
    {F : List (Nat × Value)} (i : Fin 14) (hAddr : addr < 2 ^ 32) (hAlign : addr % 8 = 0)
    (hPhase : phase < 2) (hFresh : ∀ pair ∈ F, pair.1 ≠ (waitSite i).result)
    (hBase : ((waitSite i).base, b32 addr) ∈ F)
    (hPar : ((waitSite i).phase, b32 phase) ∈ F) (ht : At t (waitSite i).pc F)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    let ev : Bool → Event := fun ok =>
      ⟨(waitSite i).pc, .wait ⟨.shared, g / l.block, addr⟩ phase ok true .cta⟩
    ∃ n u, X.get (g, pos + n) = some (ev true) ∧
      (∀ j < n, X.get (g, pos + j) = some (ev false)) ∧
      At u ((waitSite i).pc + 3) F ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + n + 1)) none := by
  dsimp only
  obtain ⟨n, u, rest, hPrefix, hu, hRest⟩ :=
    waitTrace i hAddr hAlign hPhase hFresh hBase hPar ht hr
  let ev : Bool → Event := fun ok =>
    ⟨(waitSite i).pc, .wait ⟨.shared, g / l.block, addr⟩ phase ok true .cta⟩
  change (X.tr g).drop pos = List.replicate n (ev false) ++ (ev true :: rest) at hPrefix
  refine ⟨n, u, ?_, ?_, hu, ?_⟩
  · change (X.tr g)[pos + n]? = some (ev true)
    rw [← List.getElem?_drop, hPrefix, List.getElem?_append_right (by simp)]
    simp
  · intro j hj
    change (X.tr g)[pos + j]? = some (ev false)
    rw [← List.getElem?_drop, hPrefix, List.getElem?_append_left (by simpa using hj)]
    simp [hj]
  · have hRun : (X.tr g).drop (pos + n + 1) = rest := by
      rw [Nat.add_assoc, ← List.drop_drop, hPrefix]
      have hNil : (List.replicate n (ev false)).drop (n + 1) = [] :=
        List.drop_eq_nil_of_le (by simp)
      rw [List.drop_append, hNil, List.length_replicate, Nat.add_sub_cancel_left]
      rfl
    exact hRun.symm ▸ hRest

end
end PTX.Kernels.TmlFa4Fwd.Mma
