-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Iface.GlobalReads
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Occurs
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Loader.PageAddr
import Kernels.InklingRelDecode.Proof.Lib.Coordinates

namespace PTX.Kernels.InklingRelDecode.Proof.Loader.Export
open PTX PTX.Flow PTX.Proof Arith32

/-- A block-table load of the loader reads input bytes. -/
public theorem page_address {Q L m X g k pc a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (warp : g % L.block / 32 = 6) (he : Occurs L X g k ⟨pc,.rd a bs⟩)
    (site : pc = 2382 ∨ pc = 2399) : Iface.InputAcc Q a := by
  have hg := he.lt hX
  obtain ⟨w,x,d,t,ins,o,hat,hpc,hc,fire,hr,_⟩ := loader_occ hp hX hf warp he
    (by simp) (by change 2344 < pc; omega) (by change pc < 2422; omega)
  change pc = d.site.pc at hpc
  subst hpc
  obtain ⟨-, s, -, -, -, hs, rfl⟩ := page_acc hp hg hat hc fire rfl hr site
  have hz := (Lib.coordinate_bounds hp hg).2.2
  have hb := hp.bRange
  refine ⟨rfl, rfl, fun j hj => ?_⟩
  right; right; right; right; right
  refine ⟨_, hz, s, hs, j, hj, ?_⟩
  rw [Nat.mul_comm Q.strideBt]
  rfl

end PTX.Kernels.InklingRelDecode.Proof.Loader.Export
