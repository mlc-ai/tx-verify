-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Proof.Common.RankOrder
import Kernels.InklingRelDecode.Proof.Epilogue.Ledger
import Lemmas.Kernel.Safety.TableU

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
open PTX PTX.Flow PTX.Frame

private theorem wait_rank {Q L m X g k obj p ok ac sc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g,k)=some ⟨2565,.wait obj p ok ac sc⟩) :
    ∃ d, stateAt (thread Q L) X g k=some (some d) ∧ threadRank d=75 := by
  have hg := lt_of_get hX get
  obtain ⟨s,hs,_⟩ := good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX get (by simp) ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have pc := event_pcU (fun g hg => thread_sound hp hg) hX get hs (by simp)
  have inv := (reached_table hf hg (noUbBefore_of_get hX get) hs).1
  obtain ⟨w,ent,d,n,rfl⟩ := (pc ▸ state_role s).epilogue (by decide : 2565≤2565)
    (by decide : 2565<2853) inv
  obtain ⟨site,v⟩ := d
  have eq : site=.wait := by
    by_contra ne
    exact final_only _ ne pc.symm
  subst site
  exact ⟨_,hs,rfl⟩

/-- A waiting epilogue lane has never passed the final poll, even if it already tried it. -/
public theorem final_first {Q L m X g k obj p ok ac sc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (get : X.get (g,k)=some ⟨2565,.wait obj p ok ac sc⟩) :
    pollRound 2565 ((X.tr g).take k)=0 := by
  obtain ⟨d,hs,rank⟩ := wait_rank hp hX hf get
  apply no_earlier_at_rank hp hX hf words get hs rank
  rintro j ⟨pc,kd⟩ first use
  cases kd <;> simp [okPollAt] at use
  rename_i l q ok ac sc
  cases ok <;> simp at use
  subst pc
  exact ⟨rfl,wait_rank hp hX hf first⟩

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
