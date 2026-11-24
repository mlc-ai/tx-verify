-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPack
public import Kernels.TmlFa4Fwd.Proof.LoaderPointerReload
import Kernels.TmlFa4Fwd.Flow.Code.Part012
import Kernels.TmlFa4Fwd.Flow.Code.Part013

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- Both initial V source slots use the same lane-local vector reload. -/
def primingVPointerReload : Fin 2 → SavedPointerReload
  | 0 => ⟨804, 7292, 0, 1927, 1928⟩
  | 1 => ⟨854, 7292, 8, 1945, 1946⟩

def primingVReloadWords (slot : Fin 2) (base : Nat) : List (Nat × Value) :=
  [((primingVPointerReload slot).lowReg, b32 (base % 2 ^ 32)),
   ((primingVPointerReload slot).highReg, b32 (base / 2 ^ 32))]

def primingVReloadEvents (l : Launch) (g base : Nat) (slot : Fin 2) : List Event :=
  let site := primingVPointerReload slot
  [⟨site.pc, .rd (site.word g l.localBase 0) (pointerReadBytes base 0)⟩,
   ⟨site.pc, .rd (site.word g l.localBase 1) (pointerReadBytes base 1)⟩]

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem primingVFirstReloadPrep {l : Launch} {g word : Nat} :
    Seg kernel [] l g 1 803 [(1089, b32 word)] 804 [] := by
  intro s hs
  seg_fp hs using rfl

end
end PTX.Kernels.TmlFa4Fwd.Loader
