-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Obj
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Tmem

@[expose] public section

/-! # The K/V ring's counts by slot at an MMA

At an MMA of a lane of warp 12, the lane's polls of the full barrier of slot `s` are the ring uses
before `kvPolls` that fall on the slot, and its commits to the slot's empty barrier those before
`kvRels` (`mma_kv_slots`): use `t` falls on slot `t mod 3`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- **The polls and the commits of slot `s` before an MMA.** -/
theorem mma_kv_slots (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g = 12) {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (hi : X.MmaIssue (g, k) d sp acc mask) (s : Fin 3) :
    okPolls (obj L g (32 + 8 * s.val)) ((X.tr g).take k) = (Tm.kvPolls L X g k + 2 - s.val) / 3 ∧
      ((X.tr g).take k).countP (commitsTo (obj L g (56 + 8 * s.val))) =
        (Tm.kvRels L X g k + 2 - s.val) / 3 := by
  obtain ⟨e, dd, n, he, hσ, hJ, -, hs⟩ := mma_state hp hX hw hi
  have hwon := win_states hX k dd n hσ (by rcases hs with ⟨b, j, h⟩ | ⟨b, j, h⟩ <;> rw [h] <;> rfl)
  obtain ⟨r, w, hQ, -⟩ := hJ
  obtain ⟨ha, hc⟩ := counts_at hσ hQ hwon
  have h1 : Tm.kvPolls L X g k = ringAcq dd.site.ord r := by
    unfold Tm.kvPolls
    rw [ha, ha, ha, acqAt_kv]
  have h2 : Tm.kvRels L X g k = ringRel dd.site.ord r := by
    unfold Tm.kvRels
    rw [hc, hc, hc, commitAt_kv]
  have e1 : okPolls (obj L g (32 + 8 * s.val)) ((X.tr g).take k) = acqAt dd.site.ord r
      (32 + 8 * s.val) := ha _
  have e2 : ((X.tr g).take k).countP (commitsTo (obj L g (56 + 8 * s.val))) =
      commitAt dd.site.ord r (56 + 8 * s.val) := hc _
  rw [e1, e2, h1, h2]
  fin_cases s <;> simp [acqAt, commitAt, ringCount]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
