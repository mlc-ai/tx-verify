-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.LpEvents

@[expose] public section

/-!
# The prologue's events on the KV ring

A slot `s` of the ring of CTA `c` that the prologue preloads (`s < num_pre`) has one arrival on
`kv_ready s` by the prologue (thread 0 of the CTA at the site `arr s`) and eight copies completing
on it (the sites `ptc (4 s) … ptc (4 s + 3)`, each by the elected lane of warps 0 and 1). `PreSlot`
names these events, as `Ring.Kv.Hyp` needs them (`pArr`, `pCp`): every arrival and every copy on
`kv_ready s` at a prologue state is one of them, and the slot is preloaded. It speaks only of the
events that happened, so it holds on every prefix of a run.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lp
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty)

noncomputable section

/-- The number of blocks the prologue preloads in CTA `c`. -/
def npOf (Q : Params) (L : Launch) (c : Nat) : Nat :=
  ProA.numPre Q ((L.ctaidOf c).get .z) ((L.ctaidOf c).get .x)

theorem npOf_eq (Q : Params) (L : Launch) (g : Nat) :
    npOf Q L (g / L.block) = ProA.numPre Q (ProA.cta L g .z) (ProA.cta L g .x) := rfl

/-- **The prologue's arrival `pArr` and copies `pCp` on slot `s` of CTA `c`.** -/
structure PreSlot (Q : Params) (L : Launch) (X : Execution) (c s : Nat) (pArr : EvId)
    (pCp : Fin 8 → EvId) : Prop where
  /-- An arrival on `kv_ready s` at a prologue state is `pArr`, and the slot is preloaded. -/
  arr : ∀ {g k pc tx cnt : Nat} {rel : Bool} {sc : MbarScope} {d : ProA.D},
    X.get (g, k) = some ⟨pc, .arrive (kvReady L c s) tx cnt rel sc⟩ →
    St Q L X g k = some (some (.d (.pro d))) → (g, k) = pArr ∧ s < npOf Q L c
  /-- A copy completing on `kv_ready s` at a prologue state is one of the `pCp`, and the slot is
  preloaded. -/
  cp : ∀ {g k pc a : Nat} {sp : TensorCopy.Spec} {d : ProA.D},
    X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar = kvReady L c s →
    St Q L X g k = some (some (.d (.pro d))) → (∃ i, (g, k) = pCp i) ∧ s < npOf Q L c
  /-- The events are of default-partition threads of the CTA. -/
  arr_thr : pArr.1 / L.block = c ∧ pArr.1 % L.block < 128
  cp_thr : ∀ i, (pCp i).1 / L.block = c ∧ (pCp i).1 % L.block < 128
  /-- The eight copies are distinct events. -/
  cp_inj : Function.Injective pCp

/-- **The prologue's events on every slot of every CTA.** -/
def PreRing (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ c < L.grid, ∀ s < 3, ∃ pArr pCp, PreSlot Q L X c s pArr pCp

end
end PTX.Kernels.InklingRelDecode.Proof.Lp
