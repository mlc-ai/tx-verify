-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Lemmas.Flow.PollRounds
public import Lemmas.Order.ElectOrdinal
import Kernels.InklingRelDecode.Proof.Common.PrologueEvent
import Kernels.InklingRelDecode.Proof.Common.WorkerBalance
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Lib.CollectiveAt
import Lemmas.Flow.NotBulk

namespace PTX.Kernels.InklingRelDecode.Proof.Loader.Export
open PTX PTX.Flow PTX.Proof

private theorem elect_region {L m X g k pc mask inst lane}
    (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k) = some ⟨pc,.elect mask inst lane⟩) :
    (27<pc ∧ pc<574) ∨ (2344<pc ∧ pc<2557 ∧ pc≠2422) := by
  have checked : kernel.code.zipIdx.all (fun (i,p) => !electOp i.op ||
    (27<p && p<574) || (2344<p && p<2557 && p != 2422)) = true := by decide +kernel
  obtain ⟨_,bad⟩|⟨t,ins,o,_,hc,fire⟩ := get_source hX he
  · cases bad
  have src := List.all_eq_true.mp checked (ins,pc) (List.mem_zipIdx_iff_getElem?.mpr hc)
  cases yes : electOp ins.op
  · exact (fires_notElect (eventTmpl_notElect yes) fire _ _ _ rfl).elim
  · simpa [yes,and_assoc] using src

private theorem loop_of_elect (s : Site) : Lib.canElect s.pc = true → s.inLoop = true := by
  cases s <;> repeat' (rename_i i; revert i)
  all_goals decide +kernel

/-- An election at ordinal t is in successful empty-poll round t / 4 + 1. -/
public theorem election_round {Q L m X g k pc mask inst lane} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (warp : g%L.block/32=6) (he : X.get (g,k)=some ⟨pc,.elect mask inst lane⟩) :
    pollRound 2374 ((X.tr g).take k)=((X.tr g).take k).countP isElectEv/4+1 := by
  rcases elect_region hX he with ⟨lo,hi⟩|⟨lo,hi,nentry⟩
  · obtain ⟨_,_,_,_,_,_,_,_,_,_,hw,_⟩ := prologue_event hp hX hf he (by simp) lo hi
    omega
  · obtain ⟨w,x,r,d,n,hs,inv⟩ := worker_event hp hX hf he (by simp) lo hi nentry
    cases r with
    | mma =>
      have other : g%L.block/32=7 := inv.1
      omega
    | loader =>
      obtain ⟨_,_,_,_,_,hc,fire⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg)
        hX he hs (by simp)
      have enabled : Lib.canElect d.site.pc=true := by
        cases h : Lib.canElect d.site.pc
        · cases (Lib.collective_at hc fire).election h
        · rfl
      have range (s : Site) : Lib.canElect s.pc=true → 1≤owed s ∧ owed s≤4 := by
        cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
      have ⟨_,_⟩ := range d.site enabled
      have bal := loader_balance hp hX hf (Frame.lt_of_get hX he) warp
        (Frame.noUbBefore_of_get hX he) hs
      have cn : n .elect=((X.tr g).take k).countP isElectEv := fcount hs _
      have cr : n (.poll 2374)=pollRound 2374 ((X.tr g).take k) := fcount hs _
      omega

/-- When the preload covers the split, no thread in warp 6 runs an election.
This remains true through the final event of an exited CTA. -/
public theorem no_election_of_preloaded {Q L m X g} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (warp : g%L.block/32=6)
    (full : Q.numIters ((L.ctaidOf (g/L.block)).get .z) ((L.ctaidOf (g/L.block)).get .x)
      ≤ Iface.preloadCount Q L (g/L.block)) (k pc mask inst lane) :
    X.get (g,k) ≠ some ⟨pc,.elect mask inst lane⟩ := by
  intro he
  rcases elect_region hX he with ⟨lo,hi⟩|⟨lo,hi,nentry⟩
  · obtain ⟨_,_,_,_,_,_,_,_,_,_,hw,_⟩ := prologue_event hp hX hf he (by simp) lo hi
    omega
  · obtain ⟨w,x,r,d,n,hs,inv⟩ := worker_event hp hX hf he (by simp) lo hi nentry
    cases r with
    | mma =>
      have other : g%L.block/32=7 := inv.1
      omega
    | loader =>
      obtain ⟨t,ins,o,_,_,hc,fire⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg)
        hX he hs (by simp)
      have enabled : Lib.canElect d.site.pc = true := by
        cases h : Lib.canElect d.site.pc
        · cases (Lib.collective_at hc fire).election h
        · rfl
      obtain ⟨_,ref,_⟩ := inv
      obtain ⟨j,lo,hi,_⟩ := ref_loop ref (loop_of_elect d.site enabled)
      exact (Nat.not_lt_of_ge full) (lo.trans_lt hi)

end PTX.Kernels.InklingRelDecode.Proof.Loader.Export
