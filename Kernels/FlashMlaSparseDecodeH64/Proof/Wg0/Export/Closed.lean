-- SPDX-License-Identifier: Apache-2.0
-- domain: complete
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Poll

@[expose] public section

/-! # Every store of the exchange belongs to a closed block

A lane of warpgroup 0 that exits does so past the epilogue's code (pc 3611). A store at pc 566
leaves the block's pcs only through the arrival at pc 1122 (`w0_loop_stays`), so a lane that
exits has a closing event after each of its stores at pc 566 (`w0_closed_of_exit`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}

/-- **The exit of a lane of warpgroup 0 is at pc 3611.** -/
theorem w0_exit_pc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L y < 4) {k pc : Nat}
    (hx : X.get (y, k) = some ⟨pc, .exit⟩) (h103 : 103 ≤ pc) : pc = 3611 := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw hx (fun _ h => by cases h)
  have h := state_role hJ hi
  rw [← hpc] at h
  simp only at h
  cases h with
  | wg0 d n hR _ hpcd _ =>
    obtain ⟨-, hK⟩ : Wg0.Ev P L y (warpW L y) d ⟨pc, .exit⟩ := hev
    have hs := Wg0.evK_exit hK rfl
    rw [hpcd, hs]
    rfl
  | startup _ _ _ _ _ _ hr => omega
  | head _ _ _ _ _ _ hw' => simp only [warp] at hw hw'; omega
  | idle _ _ _ hw' => simp only [warp] at hw; simp only [warpOf, tidOf] at hw'; omega
  | index _ _ _ hw' => simp only [warp] at hw hw'; omega
  | mma _ _ _ _ _ hw' => simp only [warp] at hw hw'; omega
  | tma _ _ _ _ _ hw' => simp only [warp] at hw hw'; omega
  | dequant _ _ _ hw' => simp only [warp] at hw hw'; omega

/-- **Every event of a block's pcs (566 to 1121) of a lane that exits has a closing event after
it** (an event at pc 1122): the pcs of the block stay at most 1121 until then, and the exit is
past them. -/
theorem w0_closed_of_exit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L y < 4) (hv : W0Trace P X y) {pcx : Nat}
    (hlast : (X.tr y).getLast? = some ⟨pcx, .exit⟩) (h103 : 103 ≤ pcx) :
    ∀ j f, X.get (y, j) = some f → 566 ≤ f.pc → f.pc ≤ 1121 →
      ∃ K c, j < K ∧ X.get (y, K) = some c ∧ c.pc = 1122 := by
  intro j f hf hpc1 hpc2
  rw [List.getLast?_eq_getElem?] at hlast
  have hxy : X.get (y, (X.tr y).length - 1) = some ⟨pcx, .exit⟩ := hlast
  have hpx := w0_exit_pc hp hX hFw hw hxy h103
  have hjl : j < (X.tr y).length := (List.getElem?_eq_some_iff.mp hf).1
  by_contra hno
  push Not at hno
  have hst := Wg0.w0_loop_stays hp hX hFw hw hv hf hpc1 hpc2
    ((X.tr y).length - 1 - j) (f' := ⟨pcx, .exit⟩) (by
      have : j + ((X.tr y).length - 1 - j) = (X.tr y).length - 1 := by omega
      rw [this]; exact hxy) (fun _ h => by cases h)
    (fun q hq ev hev => by
      rcases Nat.eq_zero_or_pos q with rfl | hq0
      · rw [Nat.add_zero, hf] at hev
        cases hev
        omega
      · exact hno (j + q) ev (by omega) hev)
  simp only at hst
  omega

/-- **A lane that exits has a next event after every event that is not the exit.** -/
theorem w0_not_last (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L y < 4) {pcx j : Nat} {f : Event}
    (hlast : (X.tr y).getLast? = some ⟨pcx, .exit⟩) (h103 : 103 ≤ pcx)
    (hf : X.get (y, j) = some f) (hne : f.pc ≠ 3611) : ∃ e', X.get (y, j + 1) = some e' := by
  rw [List.getLast?_eq_getElem?] at hlast
  have hxy : X.get (y, (X.tr y).length - 1) = some ⟨pcx, .exit⟩ := hlast
  have hpx := w0_exit_pc hp hX hFw hw hxy h103
  have hjl : j < (X.tr y).length := (List.getElem?_eq_some_iff.mp hf).1
  have hj : j + 1 < (X.tr y).length := by
    by_contra hge
    have hj' : j = (X.tr y).length - 1 := by omega
    rw [hj'] at hf
    rw [hxy] at hf
    cases hf
    exact hne hpx
  exact ⟨_, (List.getElem?_eq_getElem hj : (X.tr y)[j + 1]? = _)⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
