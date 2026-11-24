-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueDispatch
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.SegChain
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The first role-specific parameter read after the common CTA barrier. -/
def dispatchParamPc (warp : Fin 16) : Nat :=
  if 14 ≤ warp.val then 178 else
  if warp.val = 13 then 2768 else
  if warp.val = 12 then 1906 else
  if warp.val < 8 then 3101 else 7745

/-- The decoded local path from the common barrier to the first role parameter read. -/
def dispatchSteps (warp : Fin 16) : Nat :=
  if 14 ≤ warp.val then 4 else
  if warp.val = 13 then 7 else
  if warp.val = 12 then 9 else
  if warp.val < 8 then 11 else 14

private theorem ctaWord {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (hg : g < l.threads) :
    truncBits 32 (BitVec.ofNat 64 ((l.ctaidOf (g / l.block)).get .x)) =
      BitVec.ofNat 64 (g / l.block) := by
  have hcta : (l.ctaidOf (g / l.block)).get .x = g / l.block :=
    Option.some.inj (sregValue_oneDim hp.cluster.2.2 g).2.2.1
  have hblock : 0 < l.block := by rw [hp.block]; decide
  have hgrid : g / l.block < l.grid :=
    (Nat.div_lt_iff_lt_mul hblock).2 (show g < l.grid * l.block from hg)
  have hCta32 : g / l.block < 2 ^ 32 := by have := hp.grid.2.2; omega
  rw [hcta, truncBits_ofNat hCta32 (by decide)]

private def Dispatch (l : Launch) (g : Nat) (warp : Fin 16) : Prop :=
  Seg kernel [] l g (dispatchSteps warp) 174 [(1062, b32 warp.val), (2535, b32 l.sharedBase)]
    (dispatchParamPc warp) [(1062, b32 warp.val), (1072, b32 (g / l.block)),
      (2535, b32 l.sharedBase)]

private theorem dispatchLow {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (warp : Fin 8) (g : Nat) (hg : g < l.threads) :
    Dispatch l g ⟨warp.val, by have := warp.isLt; omega⟩ := by
  have hcta := ctaWord hp hg
  unfold Dispatch
  fin_cases warp <;> intro t ht <;>
    simp [dispatchSteps, dispatchParamPc] at ht ⊢ <;>
    seg_fp ht using simp only [b32, hcta]

private theorem dispatchHigh {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (warp : Fin 8) (g : Nat) (hg : g < l.threads) :
    Dispatch l g ⟨warp.val + 8, by have := warp.isLt; omega⟩ := by
  have hcta := ctaWord hp hg
  unfold Dispatch
  fin_cases warp <;> intro t ht <;>
    simp [dispatchSteps, dispatchParamPc] at ht ⊢ <;>
    seg_fp ht using simp only [b32, hcta]

/-- The common post-barrier dispatch sends each of the sixteen warps to its own role entry. -/
theorem dispatchRoles {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (warp : Fin 16) (g : Nat) (hg : g < l.threads) :
    Seg kernel [] l g (dispatchSteps warp) 174 [(1062, b32 warp.val), (2535, b32 l.sharedBase)]
      (dispatchParamPc warp) [(1062, b32 warp.val), (1072, b32 (g / l.block)),
        (2535, b32 l.sharedBase)] := by
  change Dispatch l g warp
  by_cases hlt : warp.val < 8
  · exact dispatchLow hp ⟨warp.val, hlt⟩ g hg
  · have hlo : 8 ≤ warp.val := by omega
    have hhi : warp.val - 8 < 8 := by have := warp.isLt; omega
    have he : (⟨warp.val - 8 + 8, by omega⟩ : Fin 16) = warp :=
      Fin.ext (Nat.sub_add_cancel hlo)
    rw [← he]
    exact dispatchHigh hp ⟨warp.val - 8, hhi⟩ g hg

end

end PTX.Kernels.TmlFa4Fwd.Prologue
