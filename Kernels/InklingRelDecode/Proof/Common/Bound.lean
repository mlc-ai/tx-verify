-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.DataRank
public import Kernels.InklingRelDecode.Proof.Common.WorkerRank
public import Kernels.InklingRelDecode.Proof.Startup.Measure
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame

def launchRank := 75+softMaxRank+4*574

noncomputable def threadRank {Q L g} : (thread Q L g).D → Nat
  | (.inl d,_) => launchRank+Startup.measure d.site
  | (.inr ⟨.inl (.prologue _),s⟩,_) => dataRank s
  | (.inr ⟨.inl (.dispatch ..),s⟩,_) => workerRank s
  | _ => 0

private theorem start_le {Q L g n} (s : Startup.D) :
    threadRank (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) ≤ launchRank+Startup.measure s.site := by
  obtain ⟨s,t,x,w⟩ := s
  cases s <;> try exact Nat.le_refl _
  rename_i r
  cases r with
  | dp =>
    change 75+softMaxRank+(4*574-_)≤launchRank+0
    unfold launchRank
    omega
  | worker =>
    change Dispatch.callBound+12+2≤launchRank+0
    decide +kernel

theorem rank_next {Q L m X g k d dn ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (he : X.get (g,k)=some ev) (hs : stateAt (thread Q L) X g k=some (some d))
    (hi : (thread Q L g).inv d) (move : (thread Q L g).next d ev=some (some dn)) :
    threadRank dn+ev.counts.toNat≤threadRank d := by
  obtain ⟨s,n⟩ := d
  obtain ⟨sn,nn⟩ := dn
  obtain ⟨sub,_⟩ := Code.counted_next_some move
  rcases s with d|⟨r,s⟩
  · obtain ⟨d',step,rfl⟩ := Code.glue_inl_some sub
    have le := Startup.measure_next step
    have land := start_le (Q := Q) (L := L) (g := g) (n := nn) d'
    have cnt : ev.counts.toNat≤1 := by cases ev.counts <;> decide
    change _≤launchRank+Startup.measure d.site
    omega
  · obtain ⟨_,step,rfl⟩ := Code.glue_inr_some sub
    rcases r with (r|r)
    · cases r with
      | dispatch => exact worker_rank_next hp hX hf words he hs hi step
      | prologue => exact data_rank_next hi step
    · cases step

theorem initial_rank {Q L g} : threadRank (thread Q L g).init≤launchRank+7 := by
  apply Nat.le_trans (start_le (Startup.init L g))
  unfold Startup.init
  split <;> decide +revert +kernel

end PTX.Kernels.InklingRelDecode.Proof
