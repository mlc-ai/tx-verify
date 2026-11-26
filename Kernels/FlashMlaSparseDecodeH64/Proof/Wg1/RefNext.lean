-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Ref
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Shape

@[expose] public section

/-! # The head's reference invariant is kept by every step

`hrefNext`: from a head state with `HRef` (with `sh` shuffles before it), an event of its shape
leads to a state with `HRef` at the shuffle count bumped by the event. The shuffle's word is a
premise (`hrecv`): lane 0 of the warp sent the launch's warp word (`warpW`), the head's shuffle
being the warp's third, the instance after the startup's two (`Common/Recv.lean`'s argument with
the head's state at the source). With it the dispatch goes to the launch's warp's exit: in
warpgroup 1 (warps 4 to 7) the word `4` to the MMA exit, `5` to the TMA exit, `6` to the idle
exit, `7` to the index exit. The idle code has no invariant. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **The head's invariant is kept by every head step.** -/
theorem hrefNext (hp : Pre P L m) {s s' : Site} {e : Event} {sh : Nat} (hR : HRef L g s sh)
    (hev : Ev L g s e) (hs : succ s e = some (some s'))
    (hrecv : ∀ a r ok, e.kind = .shfl .idx a 0 31 r ok → r = w32 (warpW L g)) :
    HRef L g s' (sh + if Execution.isShfl e then 1 else 0) := by
  obtain ⟨pc, kd⟩ := e
  cases s with
  | smr =>
    obtain ⟨inst, hk⟩ := hev
    simp only at hk
    subst hk
    simp only [succ, Option.some.injEq] at hs
    subst hs
    obtain ⟨h2, hw⟩ := hR
    simp [HRef, Execution.isShfl, h2, hw]
  | hsh =>
    obtain ⟨r, ok, hk⟩ := hev
    simp only at hk
    subst hk
    obtain ⟨h2, hw⟩ := hR
    have hr := hrecv _ r ok rfl
    subst hr
    have hlt : warpOf L g < 2 ^ 32 := by have := warpOf_lt (g := g) hp; omega
    have h4 : 4 ≤ warpOf L g ∧ warpOf L g < 8 := by
      simp only [wgOf, warpOf] at hw ⊢
      omega
    have e7 : scmpi .eq .b (warpW L g) 7 = decide (warpOf L g = 7) :=
      scmpi_eq_b_W hlt (by decide) (by decide)
    have e5 : scmpi .eq .b (warpW L g) 5 = decide (warpOf L g = 5) :=
      scmpi_eq_b_W hlt (by decide) (by decide)
    have e4 : scmpi .ne .b (warpW L g) 4 = decide (warpOf L g ≠ 4) :=
      scmpi_ne_b_W hlt (by decide) (by decide)
    simp only [succ, dispatch, e7, e5, e4, decide_eq_true_eq] at hs
    simp only [Execution.isShfl, ↓reduceIte, h2]
    split_ifs at hs with h7 h5 h4' <;> simp only [Option.some.injEq] at hs <;>
      subst hs <;> simp only [HRef] <;> omega
  | _ => simp [succ] at hs

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1
