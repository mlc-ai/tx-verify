-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Barrier
public import Kernels.TmlFa4Fwd.Proof.PollSafety
public import Lemmas.Flow.NotClc
public import Lemmas.Step.CtaBarFinishExit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Flow PTX.Proof

noncomputable section

private theorem beforeCommonNoBar :
    (kernel.code.take 173).all (fun ins => !barOp ins.op) = true := by
  decide +kernel

private theorem noBarBeforeCommon {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) {e : EvId} {pc id : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get e = some ⟨pc, .bar id cnt mode⟩) (hPc : pc < 173) : False := by
  rcases get_source hX he with ⟨_, hu⟩ | ⟨_, ins, _, _, hc, hf⟩
  · cases hu
  have hTake : (kernel.code.take 173)[pc]? = some ins := by
    rwa [List.getElem?_take_of_lt hPc]
  have hm := List.all_eq_true.mp beforeCommonNoBar ins (List.mem_of_getElem? hTake)
  rw [fires_bar_op hf rfl] at hm
  cases hm

private theorem nonzeroEarlierCommon {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (hFence : X.get (g, 3) = some ⟨172, .fenceMbarInit⟩) : EarlierEvents X g 4 173 := by
  intro k hk e he
  interval_cases k
  · rw [firstSharedValue hp hX g hg he]
    exact (show 25 < 173 by decide)
  · rw [secondWarpValue hp hX g hg he]
    exact (show 34 < 173 by decide)
  · rw [thirdWarpValue hp hX g hg he]
    exact (show 35 < 173 by decide)
  · rw [hFence] at he
    obtain rfl := Option.some.inj he.symm
    exact (show 172 < 173 by decide)

theorem commonBarrierOrdinal {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) {g n : Nat} (hEarlier : EarlierEvents X g n 173) :
    ((X.tr g).take n).countP (Execution.isBarId 0) = 0 := by
  apply List.countP_eq_zero.mpr
  intro e hm
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
  have hLt : k < n :=
    lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hk).choose (List.length_take_le _ _)
  rw [List.getElem?_take_of_lt hLt] at hk
  have hPc : e.pc < 173 := hEarlier k hLt e hk
  rcases e with ⟨pc, kind⟩
  cases kind <;> simp [Execution.isBarId] at *
  rename_i id cnt mode
  exact (noBarBeforeCommon hX (e := (g, k)) (id := id) (cnt := cnt) (mode := mode) hk hPc).elim

/-- Every lane posts generation zero of the common CTA synchronization. The number of earlier
records differs between the initializing lane and the other lanes. -/
theorem commonBarrierAllArrive {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) :
    ∃ n, X.get (g, n) = some ⟨173, .bar 0 none .sync⟩ ∧
      ((X.tr g).take n).countP (Execution.isBarId 0) = 0 := by
  by_cases hWarp : warpIndex l g = 0
  · obtain ⟨n, hf, hb, hEarlier⟩ := warp0BarrierArrives hp hMax hg hWarp
    exact ⟨n + 1, hb, commonBarrierOrdinal hMax.1 (hEarlier.succ hf rfl)⟩
  · obtain ⟨hf, hb⟩ := nonzeroBarrierArrives hp hMax hg (by omega)
    exact ⟨4, hb, commonBarrierOrdinal hMax.1 (nonzeroEarlierCommon hp hMax.1 hg hf)⟩

/-- The startup barrier uses all sixteen warps of its CTA and the PTX implicit count. -/
theorem commonBarrierShape {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) :
    NamedBar.Shape l none (Finset.range 16) 0 := by
  refine ⟨by decide, ?_, ?_, by decide⟩
  · rw [hp.block]
    simp [CtaBarrier.target, CtaBarrier.warps]
  · intro w hw
    rw [hp.block]
    exact Finset.mem_range.mp hw

end
end PTX.Kernels.TmlFa4Fwd.Prologue
