-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Lk5Final
public import Kernels.InklingRelDecode.Proof.Protocol.Lk5WStore

@[expose] public section

/-!
# The scratch load of the softmax region rebuilds

`Sm.next` at `ldL` is `none` where the four bytes the load returned do not rebuild. In iteration
`i` the load reads the bytes of the word the warp stored (`ldL_bytes`), which is the bytes of the
value of a number, so they rebuild. The premises are those of `scratchIt_of_store`, and the
decisions of the earlier iterations (`decAgree_of_it`) that `ScratchIt` of those gives.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Sm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The load of the scratch word at `ldL` returns bytes that rebuild**, given the scratch words
of every iteration. -/
theorem ldL_rebuild (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hz : Rs.SmBaseZero Q L X)
    (hI : ∀ i, ScratchIt Q L X i) {g k : Nat} {d : Sm.D} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hs : d.site = .ldL) : ∃ ac bs x, e.kind = .rd ac bs ∧ rebuild 3 bs = .ok x := by
  have hD : ∀ c j, DecAgree Q L X c j := decAgree_every hpre hX hf hI
  have hW := storeWord_all hpre hX hf hz (g / L.block) d.i
  have hr : g % L.block % 4 < 4 := Nat.mod_lt _ (by omega)
  obtain ⟨w, hw, hv⟩ := hW _ hr
  have hB : B0At Q L X (g / L.block) d.i := B0N.b0At_of hpre hX hf (fun j _ => hD _ j)
  have hP : ∀ j ≤ d.i, B0Pos Q L X (g / L.block) j :=
    fun j _ => B0N.b0Pos_of hpre hX hf (fun j' _ => hD _ j')
  obtain ⟨ac, bs, hev, hbs⟩ := ldL_bytes hpre hX hf hR hB hP hr
    (fun hg' hc hr' hσ' hs' hi' => hv hg' hc hr' hσ' hs' hi') hg rfl rfl (event_le he) he hσ hs rfl
  refine ⟨ac, bs, erealValue .f32 w, by rw [hev], ?_⟩
  rw [hbs]
  exact (erealValue_store w).2

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
