-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Floats
public import Lemmas.Flow.Shuffle

@[expose] public section

/-! # Every shuffle returns its own source value

Every shuffle of the kernel is a full-warp `shfl.sync.idx` from lane 0 (`FloatFacts.shfl_form`).
A lane's `n`-th shuffle receives the source value of lane 0's `n`-th shuffle (DEP-WARP-SHUFFLE,
`ShflOk`), since lane 0 does not exit before it (`FloatFacts.shfl_live`); the source values of the
`n`-th shuffles of a warp's lanes are equal (`FloatFacts.shfl_uniform`), so the lane receives its
own source value (`shfl_own`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof

noncomputable section

namespace Floats

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}

/-- **Every shuffle returns its own source value.** -/
theorem shfl_own (hX : Consistent L K A mem0 X) (hf : FloatFacts L X) {g k pc b c : Nat}
    {md : ShflMode} {a recv : Value} {ok : Bool} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .shfl md a b c recv ok⟩) : recv = a := by
  obtain ⟨rfl, rfl, rfl⟩ := hf.shfl_form hg he
  have hk : X.ShflK (g, k) (((X.tr g).take k).countP Execution.isShfl) :=
    ⟨⟨_, _, _, _, _, _, _, he⟩, rfl⟩
  obtain ⟨-, hsource⟩ := hX.shfl g k _ pc .idx a 0 31 recv ok he hk
  have hsrc : shflSource .idx (laneOf L g) 0 31 = (0, true) := by simp [shflSource]
  rw [hsrc] at hsource
  simp only [Nat.add_zero] at hsource
  obtain ⟨hw, -⟩ := Flow.laneZero_sameWarp (NamedBar.block_pos_of_thread_lt hg) hg
  rcases hsource with ⟨j, pc', b', c', r', o', hpeer, hepeer⟩ | hx
  · exact (hf.shfl_uniform hw hk hpeer he hepeer).symm
  · exact absurd hx (hf.shfl_live hg hk)

end Floats

end
end PTX.Kernels.FlashAttn4Fwd.Proof
