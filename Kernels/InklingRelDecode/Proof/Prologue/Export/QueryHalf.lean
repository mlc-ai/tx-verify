-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.QueryCoord
import Kernels.InklingRelDecode.Proof.Prologue.QueryInput
import Kernels.InklingRelDecode.Proof.Prologue.Export.QueryReadAddress
import Lemmas.Kernel.Source.Launch

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow PTX.Proof

/-- **A query load returns a bf16 number**: the element of the query tensor it reads. -/
public theorem query_half {Q L m X g k pc a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k) = some ⟨pc,.rd a bs⟩) {j : Fin 64} (site : pc = 388 + 2 * j.val) :
    rebuild 3 bs = .ok (Value.float .bf16 (Lib.qElem Q L g j.val)) := by
  obtain ⟨r, hr, tok, ht, head, hh, d, hd, rfl, rfl, rfl, rfl, loc, size⟩ :=
    query_read hp hX hf (.inl he) site
  have ro := Frame.LaunchReads.of_forall (hX.asm _ (show Assumptions.inputReadOnly ∈
    Assumptions.all by simp [Assumptions.all]))
  refine Frame.LaunchReads.value hX ro he ?_ (by rw [size]; rfl)
    (fun _ _ => trivial) (fun j' hj' => ?_) (by decide : 0 < 2) rfl
  · have : ∀ j : Fin 64, Assumptions.inputReadSites.contains (388 + 2 * j.val) = true := by
      decide +kernel
    rw [site]
    exact this j
  · rw [loc]
    exact hp.qInput _ hr _ ht _ hh _ hd j' hj'
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
