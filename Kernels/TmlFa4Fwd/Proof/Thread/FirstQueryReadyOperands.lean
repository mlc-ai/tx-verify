-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MbarOperands
import Kernels.TmlFa4Fwd.Proof.MmaFirstReadyParity

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX

/-- Each opening query buffer is polled at parity zero. -/
theorem openingQueryReadyPollParity {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {i : EvId} {site q : Nat} {target : Loc} {ok acq : Bool} {scope : MbarScope}
    (he : X.get i = some ⟨site,.wait target q ok acq scope⟩)
    (hTarget : target.addr = l.sharedBase+8*stage.val) : q = 0 := by
  obtain ⟨g,index⟩ := i
  have outside {offsets : List Nat}
      (audit : offsets.all (fun off => decide (off ≠ 8*stage.val)) = true)
      (h : ∃ off ∈ offsets, target = ⟨.shared,g/l.block,l.sharedBase+off⟩) : False := by
    obtain ⟨off,ho,hLoc⟩ := h
    have hAddr : target.addr = l.sharedBase+off := congrArg Loc.addr hLoc
    exact (of_decide_eq_true (List.all_eq_true.mp audit off ho)) (by omega)
  rcases actualWaitRoleSites hX he with h | h | h | h | h
  · rcases List.mem_append.mp h with hFixed | hRing
    · exact (outside (by fin_cases stage <;> decide)
        (Loader.loaderFixedWaitAddress hp hX he hFixed)).elim
    · exact (outside (by fin_cases stage <;> decide)
        (Loader.loaderRingWaitAddress hp hX he hRing)).elim
  · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
    have hSites : ∀ j : Fin 14, (Mma.waitSite j).pc = (if stage = 0 then 2141 else 2210) ∨
        (Mma.waitSite j).pc ∈ [2294,2352,2545] ∨
        ((Mma.waitSite j).pc ∈ [2141,2145,2210,2297,2335,2419,2450,2548,2586,2595,2626] ∧
          Mma.fixedMmaWaitOffset (Mma.waitSite j).pc ≠ 8*stage.val) := by
      fin_cases stage <;> decide
    rcases hSites j with hFirst | hRing | ⟨hFixed,hPositive⟩
    · rw [hFirst] at he
      fin_cases stage
      · exact (Mma.firstQueryPollShape hp hX he).2.1
      · exact (Mma.secondQueryPollShape hp hX he).2.1
    · obtain ⟨slot,hLoc⟩ := Mma.mmaRingWaitAddress hp hX he hRing
      have hAddr : target.addr = l.sharedBase+(8*slot.val+32) := congrArg Loc.addr hLoc
      have hStage := stage.isLt
      omega
    · have hLoc := Mma.mmaFixedWaitAddress hp hX he hFixed
      have hAddr : target.addr = l.sharedBase+Mma.fixedMmaWaitOffset (Mma.waitSite j).pc :=
        congrArg Loc.addr hLoc
      exact (hPositive (Nat.add_left_cancel (hAddr.symm.trans hTarget))).elim
  · exact (outside (by fin_cases stage <;> decide) (OutputWarp.waitAddress hp hX he
      (by simpa using h))).elim
  · exact (outside (by fin_cases stage <;> decide) (Softmax.softmaxWaitAddress hp hX he h)).elim
  · exact (outside (by fin_cases stage <;> decide)
      (Correction.correctionWaitAddress hp hX he h)).elim

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {site q : Nat} {target : Loc}
    {ok acq : Bool} {scope : MbarScope} (he : X.get i = some ⟨site,.wait target q ok acq scope⟩)
include hp hX he

/-- Every poll of the initial query-ready object is an acquire at parity zero. -/
theorem firstQueryReadyPollParity (hTarget : target.addr = l.sharedBase) : q = 0 :=
  openingQueryReadyPollParity hp hX 0 he (by simpa using hTarget)

/-- Every poll of the opening second-query object is an acquire at parity zero. -/
theorem secondQueryReadyPollParity (hTarget : target.addr = l.sharedBase+8) : q = 0 :=
  openingQueryReadyPollParity hp hX 1 he (by simpa using hTarget)

end PTX.Kernels.TmlFa4Fwd
