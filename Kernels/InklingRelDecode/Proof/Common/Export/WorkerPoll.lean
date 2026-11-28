-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Common.History
import Kernels.InklingRelDecode.Proof.Lib.StaticPoll
import all Kernels.InklingRelDecode.Proof.Common.Follow

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow

public theorem worker_poll_pc {Q L m X g k p obj q ok a sc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hw : 6≤g%L.block/32) (he : X.get (g,k)=some ⟨p,.wait obj q ok a sc⟩) :
    (g%L.block/32=6 ∧ p=2374) ∨ (g%L.block/32=7 ∧ (p=2462 ∨ p=2510)) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (fun g h => thread_sound hp h) hX he
    (fun _ _ h => by cases h) (hf g hg k)
  have eq := Frame.event_pcU (fun g h => thread_sound hp h) hX he hs (fun _ => nofun)
  change p=_ at eq
  have place := eq ▸ state_role s
  have hist := Frame.noUbBefore_of_get hX he
  have sites := (Lib.poll_site hX he).1
  simp only [Lib.pollSites,List.mem_cons,List.not_mem_nil,or_false] at sites
  by_cases sm : 574<p ∧ p<2331
  · obtain ⟨_,_,_,_,rfl⟩ := place.softmax sm.1 sm.2
    have low := data_lane hp hX hf hg hist hs
    omega
  by_cases ep : p=2565
  · obtain ⟨_,_,_,_,rfl⟩ := place.epilogue (by omega) (by omega) (reached_table hf hg hist hs).1
    have low := data_lane hp hX hf hg hist hs
    omega
  rcases (show p=2374 ∨ p=2462 ∨ p=2510 by omega) with rfl|rest
  · obtain ⟨_,_,_,_,_,st,_⟩ := loader_state hp hX hf he (fun _ => nofun)
      (by decide : 2344<2374) (by decide : 2374<2422)
    exact .inl ⟨(reached_table hf hg hist st).2.1,rfl⟩
  · obtain ⟨_,_,_,_,_,st,_⟩ := mma_state hp hX hf he (fun _ => nofun)
      (by change 2422<p; omega) (by change p<2557; omega)
    exact .inr ⟨(reached_table hf hg hist st).2.1,rest⟩

end PTX.Kernels.InklingRelDecode.Proof.Export
