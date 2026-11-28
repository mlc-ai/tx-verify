-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ParamLoad
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.ParamLoad

@[expose] public section

/-! # FlashMLA's `ld.param` step from the library's

FlashMLA's kernel-local `seg_ldParam0` (`Proof/Lib/ParamLoad.lean`) is the library's
`Flow.seg_ldParam` with `param_0`'s object (`Pre.param0Object`), its fields (`p0fields_ok`), no
segments, and the kernel's lemma that no assumption reads an `ld.param` off the pointer sites. -/

namespace PTX.Tests.ParamLoad
open PTX PTX.Kernels.FlashMlaSparseDecodeH64 PTX.Kernels.FlashMlaSparseDecodeH64.Proof

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem seg_ldParam0' (hp : Pre P L m) {pc w off d x : Nat} {ty : DType}
    {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨none, .mem (Flow.paramLoad ty off 2991 d)⟩)
    (hf : (off, x, w / 8) ∈ p0fields P L)
    (hrp : (2991, .ptr 64 false (.param (param "0")) 0) ∈ F)
    (hd : ∀ q ∈ F, q.1 ≠ d) (hsz : off + w / 8 ≤ 304)
    (hal : 0 < w / 8 ∧ off % (w / 8) = 0 ∧ 8 % (w / 8) = 0) (hw128 : w ≠ 128)
    (h1 : pc ∉ paramAdds) (h2 : pc ∉ prefetchTensorMapSites)
    (hw : ty.width = w) (hr : (Flow.paramLoad ty off 2991 d).rule = some .threadMove) :
    Flow.Seg kernel asms L g 1 pc F (pc + 1)
      ((d, .bits w (BitVec.ofNat 64 (Flow.leNat x 0 (w / 8)))) :: F) :=
  Flow.seg_ldParam hc hp.param0Object (fun j hj => by simpa using p0fields_ok hp _ hf j hj) hrp hd
    hsz hal hw128 noSegments.segFreePc
    (fun _ ht => asms_localRule_ldParam (by rw [ht]; exact h1) (by rw [ht]; exact h2)) hw hr

end PTX.Tests.ParamLoad
