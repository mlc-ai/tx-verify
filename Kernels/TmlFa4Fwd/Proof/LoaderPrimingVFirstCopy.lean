-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVReload
public import Kernels.TmlFa4Fwd.Proof.LoaderVCopies
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSource
import Kernels.TmlFa4Fwd.Flow.Code.Part012

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue AsyncCopy

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

theorem primingVSourceLoc {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {page head row tid g bytes : Nat} (hPage : page < p.pages) (hh : head < p.kvHeads)
    (pair : Fin 16) (upper : Bool) :
    let base := (p.vLayout.loc page head (row % 16) 0).addr
    let src := (base + 2 * kvCopyColumn tid false) % 2 ^ 64
    (vCopySpec l g tid src bytes pair upper).src.loc =
      p.vLayout.loc page head (row % 16) (kvCopyColumn tid upper) := by
  dsimp only
  let base := (p.vLayout.loc page head (row % 16) 0).addr
  let col := kvCopyColumn tid upper
  let loc := p.vLayout.loc page head (row % 16) col
  have hCol : col < 128 := by
    have h := kvCopyColumn_byte_lt (lane := tid) upper (byte := 0) (by decide)
    change kvCopyColumn tid upper < 128
    omega
  have hMem := hp.ranges (p.vLayout.region p.pages p.kvHeads) (by simp [Params.inputRegions])
  have hRegion := CacheLayout.loc_copy_in_region (c := p.vLayout) hPage hh
    (Nat.mod_lt row (by decide : 0 < 16)) (d := col) (byte := 0) (by omega)
  have hAddr : loc.addr < 2 ^ 64 := by
    simpa [loc, Loc.at] using hRegion.2.2.2.trans_le hMem
  have hSum : base + 2 * kvCopyColumn tid false + (if upper then 128 else 0) = loc.addr := by
    cases upper <;> simp [base, loc, col, CacheLayout.loc, kvCopyColumn, globalLoc] <;> omega
  have hLower : base + 2 * kvCopyColumn tid false < 2 ^ 64 := by omega
  change globalLoc (((base + 2 * kvCopyColumn tid false) % 2 ^ 64 +
    (if upper then 128 else 0)) % 2 ^ 64) = loc
  rw [Nat.mod_eq_of_lt hLower, hSum, Nat.mod_eq_of_lt hAddr]
  rfl

end
end PTX.Kernels.TmlFa4Fwd.Loader
