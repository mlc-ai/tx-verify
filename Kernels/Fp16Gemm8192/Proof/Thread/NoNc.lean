-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.RingUsers
public import Lemmas.Flow.NotNc

@[expose] public section

/-! # The kernel performs no non-coherent read

The kernel's assumptions allow no non-coherent load, so no event of a followed thread is a
non-coherent read (`no_nc`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

/-- No event of a followed thread is a non-coherent read. -/
theorem no_nc {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat} {e : Event}
    {d : ThreadD} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some d)) {a : Acc} {bs : List (Option Byte)} :
    e.kind ≠ .nc a bs := by
  obtain ⟨t, ins, o, -, -, -, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  exact fires_not_nc (prod_noNc _) hfire

end

end PTX.Kernels.Fp16Gemm8192.Proof
