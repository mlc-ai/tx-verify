-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmEntryBase
public import Kernels.InklingRelDecode.Proof.Thread.EvSBiasSpec

@[expose] public section

/-!
# The prologue's tie: `entOf` satisfies `EntMeans`

`EvSBiasSpec.EntMeans P r s kvh e` lists what the entry numbers of the softmax region mean for the
launch. The numbers the prologue produces, `SmEntry.entOf P L g dt` (`SmEntryBase`: from
`ProBSpec.exit_spec`, the CTA's coordinates, the loaded words and the launch's parameters), have
that meaning for the thread's request `ctaid.z`, split `ctaid.x` and KV head `ctaid.y`: the fields
are `entOf`'s own definitions, except `strRel` and `rel`, which are the parameter words
(`SmEntry.entOf_params`).

The softmax machine keeps `D.e` unchanged (`Sm.next` only ever replaces the site and the loop
state), so this is the meaning of `d.e` in every state that starts from `d0 (entOf …)`; that
`next` keeps `e` is not stated here (see the row of "thread-layer gaps" in the development notes).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {dt : ProA.Dat}

/-- **The prologue's numbers mean what `EntMeans` says**, for the thread's request, split and KV
head. -/
theorem entOf_means (hpre : Pre P L mem0) (ha : ProA.ArgsOk L g dt.pro) :
    EntMeans P (ProA.cta L g .z) (ProA.cta L g .x) (ProA.cta L g .y) (SmEntry.entOf P L g dt) := by
  obtain ⟨-, hstr, -, hrel, -, -⟩ := SmEntry.entOf_params hpre ha
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hstr, hrel⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
