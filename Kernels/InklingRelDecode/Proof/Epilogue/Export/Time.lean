-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Time
public import Kernels.InklingRelDecode.Proof.Lib.Slots
import Kernels.InklingRelDecode.Proof.Common.NextState
import Kernels.InklingRelDecode.Proof.Common.EndTime

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
open PTX PTX.Sched

public theorem final_wait_time {Q L m X g l q ok ac sc} (hp : Pre Q L m) (hf : Follow Q L X)
    (hn : NextEv L kernel Assumptions.all m X g ⟨2565,.wait l q ok ac sc⟩) :
    threadTime (schedule Q L) X g = Lib.Slots.finalWait := by
  obtain ⟨s,hs,inv,pc,_⟩ := next_state hp hf hn (fun _ => nofun)
  change 2565 = _ at pc
  obtain ⟨w,ent,d,n,rfl⟩ := (pc ▸ state_role s).epilogue (by decide : 2565≤2565)
    (by decide) inv.1
  rw [epilogue_end hs]
  obtain ⟨site,v⟩ := d
  have only (s : Site) : 2565=s.pc → s=.wait := by
    cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
  obtain rfl := only site pc
  exact Epilogue.final_wait_time v

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
