-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemInstruction
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.W0Hq

@[expose] public section

/-! # The validity of warpgroup 0's trace

`Safe.W0TraceValid` states that the words of warpgroup 0's loop are valid, in a followed
execution without undefined behaviour. It is proved from the joint induction `Safe.w0Joint`: the
trace of a lane is valid through its last event. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **The words of warpgroup 0's loop are valid.** -/
theorem Safe.w0TraceValid (hp : Pre P L mem0) : Safe.W0TraceValid P L mem0 :=
  ⟨fun X hX hFw hnu g hg => by
    cases hn : (X.tr g).length with
    | zero =>
      have : X.tr g = [] := List.length_eq_zero_iff.mp hn
      rw [W0Trace, this]
      exact w0Valid_nil P.scale
    | succ m =>
      have hm : m < (X.tr g).length := by omega
      have hev : X.get (g, m) = some (X.tr g)[m] := List.getElem?_eq_getElem hm
      have h := ((Safe.w0Joint hp (Inputs.of_pre hp) hX hFw (g, m) _ hev).1.1).valid hg
        fun _ he => noUb_kind hnu he
      have ht : (X.tr g).take (m + 1) = X.tr g := by rw [← hn]; exact List.take_length
      rw [W0Trace, ← ht]
      exact h⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
