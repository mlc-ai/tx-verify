-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.ScNum

@[expose] public section

/-!
# `NumPreRead`: the loader's read of `num_pre`

The sibling of `NumWordRead` (`ScNum.lean`) for the first element of the loader's vector load
(`Loader.Site.ld0`, the four bytes at `sharedBase + 212992` of the thread's CTA), from the second
tree's read of the pair (`Proof2.pair_read`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The loader's state at the first element of its vector load. -/
def NumPreReader : TSt → Prop
  | .w (.loader d _) => d.site = .ld0
  | _ => False

/-- **The `num_pre` word's read** returns the 32-bit `num_pre` of the reading thread's CTA: a
four-byte read of `global_smem + 212992` by the loader's `ld0`. -/
def NumPreRead (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc : Nat} {a : Acc} {bs : List (Option Byte)} {s : TSt},
    X.get (g, k) = some ⟨pc, .rd a bs⟩ → St Q L X g k = some (some s) → NumPreReader s →
      a.loc = ⟨.shared, g / L.block, L.sharedBase + 212992⟩ → a.size = 4 →
      bs = (b32 (ProA.numPre Q (ProA.cta L g .z) (ProA.cta L g .x))).toBytes.map some

/-- **`NumPreRead`**, from the second tree's read of the pair (`Proof2.pair_read`). -/
theorem numPreRead_of_p2 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) :
    NumPreRead Q L X := by
  intro g k pc a bs s hget hσ hr hloc hsz
  have hlk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp hget).1
  have hnotd : ¬ s.isD := by
    cases s with
    | d s => exact hr.elim
    | w s => exact fun h => h
  have hw : 128 ≤ g % L.block := by
    have := (cls_inv k s hlk.le hσ).not.mp hnotd
    omega
  have hloc' : a.loc = ⟨.shared, g / L.block, L.sharedBase + 212992 + 4 * (0 : Fin 2).val⟩ := by
    rw [hloc]; simp
  exact Proof2.pair_read hpre hX hget hw 0 hloc' hsz

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
