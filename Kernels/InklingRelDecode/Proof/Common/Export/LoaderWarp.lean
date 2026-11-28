-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Occurs
import Kernels.InklingRelDecode.Proof.Common.OccursSite
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import all Kernels.InklingRelDecode.Proof.Common.Follow

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Proof

/-- An event strictly inside the loader routine comes from the loader warp: the MMA
fragment has no site there. -/
public theorem loader_warp_occ {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (hF : Follow Q L X) (he : Occurs L X g k e) (hu : ∀ f, e.kind ≠ .ub f)
    (hl : 2344 < e.pc) (hh : e.pc < 2422) : g % L.block / 32 = 6 := by
  have hg := he.lt hX
  obtain ⟨σ,hs,hpc,-⟩ := he.site hp hX hF hu
  have hi := (hF g hg k).2 σ hs (prefix_ub_zero hs (he.noUb hX))
  obtain ⟨w,x,r,s,n,rfl⟩ := (hpc ▸ state_role σ).worker hl (by omega) (by omega)
  cases r with
  | loader => exact hi.2.1
  | mma =>
    exfalso
    change e.pc = (Mma.code L g (dispatchRegs Q L g w x) w).pc s at hpc
    change e.pc = s.site.pc at hpc
    rw [hpc] at hl hh
    generalize s.site = site at hl hh
    revert hl hh
    cases site <;> first | decide | (rename_i j; fin_cases j <;> decide)

public theorem loader_warp {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (hF : Follow Q L X) (he : X.get (g,k) = some e) (hu : ∀ f, e.kind ≠ .ub f)
    (hl : 2344 < e.pc) (hh : e.pc < 2422) : g % L.block / 32 = 6 :=
  loader_warp_occ hp hX hF (.inl he) hu hl hh

end PTX.Kernels.InklingRelDecode.Proof.Export
