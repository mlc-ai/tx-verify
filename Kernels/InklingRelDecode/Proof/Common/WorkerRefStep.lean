-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.WorkerReads
public import Kernels.InklingRelDecode.Proof.Common.WorkerBalance

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame PTX.Proof

/-- One step under a worker call. The poll counts are the outer, continuously
counted ledger, including on the last step before returning to dispatch. -/
theorem worker_ref_step {Q L m X g k w x i d dn n ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (bytes : CountBytes Q L X)
    (he : X.get (g,k)=some ev) (hu : ∀ f, ev.kind≠.ub f)
    (hs : stateAt (thread Q L) X g k=some (some (workerState w x i d n)))
    (ok : workerInv Q L g w x (.inr ⟨i,d⟩) n)
    (move : (workerFrag Q L g w x i).next d ev=some (some dn)) :
    workerInv Q L g w x (.inr ⟨i,dn⟩) (Code.bump cls n ev) := by
  have hg := lt_of_get hX he
  have bound := Lib.blocksOf_lt hp hg
  have pc := event_pcU (fun g hg => thread_sound hp hg) hX he hs hu
  cases i with
  | loader r =>
    obtain ⟨warp,ref,polls,pages,r0⟩ := ok
    have range : Iface.preloadCount Q L (g/L.block) ≤ iterCount Q L (g/L.block) :=
      (Nat.min_le_right ..).trans (Nat.min_le_right ..)
    have val := loader_response hp hX bytes he hs
    change iterCount Q L (g/L.block)<2^31 at bound
    have update := Loader.polls_next bound range ref move pc
    refine ⟨warp,Loader.ref_next bound range ref val move,?_,
      Loader.pageRef_next pages (loader_page_response hp hX he hs ref) move,r0⟩
    rw [update,←polls]
    rfl
  | mma r =>
    obtain ⟨warp,ref,first,second,fin,r0⟩ := ok
    obtain ⟨_,_,_,_,inv,_,_⟩ := fired_siteU (fun g hg => thread_sound hp hg) hX he hs hu
    have val := fun site a bs v kind hw => mma_response hp hX bytes he hs site
      (a := a) (bs := bs) (v := v) kind hw
    have update := Mma.polls_next inv.1 move
    rw [mma_poll_receipt _ _ pc] at update
    refine ⟨warp,Mma.ref_next ref val move,?_,?_,?_,r0⟩
    · rw [update]
      change n (.poll 2462) + (if okPollAt 2462 ev then 1 else 0) =
        (Mma.polls d).1 + (okPollAt 2462 ev).toNat
      rw [first]
      cases okPollAt 2462 ev <;> rfl
    · rw [update]
      change n (.poll 2510) + (if okPollAt 2510 ev then 1 else 0) =
        (Mma.polls d).2 + (okPollAt 2510 ev).toNat
      rw [second]
      cases okPollAt 2510 ev <;> rfl
    · have step := Mma.fin_next (L := L) (g := g) move
      change n (.atPc 2550) + (if ev.pc == 2550 then 1 else 0) +
        (n (.atPc 2551) + (if ev.pc == 2551 then 1 else 0)) = _
      rw [step, pc]
      cases h1 : (d.site.pc == 2550) <;> cases h2 : (d.site.pc == 2551) <;> simp <;> omega

end PTX.Kernels.InklingRelDecode.Proof
