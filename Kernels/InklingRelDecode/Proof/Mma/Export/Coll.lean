-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.WorkerBalance

namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX PTX.Flow

/-- The shuffle ordinal before either wait, as a function of the poll's own round
and the split length. The first shuffle belongs to Startup. -/
public theorem poll_shuffles {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hw : g%L.block/32=7) (he : X.get (g,k)=some e) (hu : ∀ f,e.kind≠.ub f)
    (pc : e.pc=2462 ∨ e.pc=2510) :
    let es := (X.tr g).take k
    let r := pollRound e.pc es
    let c := L.ctaidOf (g/L.block)
    es.countP Execution.isShfl = if e.pc=2462 then 1+r+(r-1)
      else 1+min (r+2) (Q.numIters (c.get .z) (c.get .x))+r := by
  obtain ⟨w,x,r,d,n,hs,inv⟩ := worker_event hp hX hf he hu (by omega) (by omega) (by omega)
  cases r with
  | loader => have wrong : g%L.block/32=6 := inv.1; omega
  | mma =>
    obtain ⟨_,ref,hq,hp',-⟩ := inv
    have hg := Frame.lt_of_get hX he
    have bal := mma_balance hp hX hf hg hw (Frame.noUbBefore_of_get hX he) hs
    have eq := Frame.event_pcU (fun g h => thread_sound hp h) hX he hs hu
    obtain ⟨_,_,_,_,hi,_,_⟩ := Frame.fired_siteU (fun g h => thread_sound hp h) hX he hs hu
    have loop : Inv d := hi.1
    have cn := (fcount hs .shfl).symm
    change ((X.tr g).take k).countP Execution.isShfl = n .shfl at cn
    obtain ⟨s,i,v⟩ := d
    have only (s : Site) : (s.pc=2462 → s=.kvWait) ∧ (s.pc=2510 → s=.pWait) := by
      cases s <;> first | decide | (rename_i j; revert j; decide +kernel)
    change e.pc=s.pc at eq
    dsimp only
    rcases pc with pc|pc
    · obtain rfl := (only s).1 (eq ▸ pc)
      simp only [pc,↓reduceIte]
      have cnt := (fcount hs (.poll 2462)).symm.trans hq
      change pollRound 2462 _=i at cnt
      change n .shfl+0=1+n (.poll 2462)+n (.poll 2510) at bal
      change n (.poll 2462)=i at hq
      change n (.poll 2510)=i-1 at hp'
      rw [cn,cnt]; omega
    · obtain rfl := (only s).2 (eq ▸ pc)
      simp only [pc,show (2510=2462) = False by decide,↓reduceIte]
      have cnt := (fcount hs (.poll 2510)).symm.trans hp'
      change pollRound 2510 _=i-1 at cnt
      have limit := ref_count ref rfl
      change low v = _ at limit
      have pos : 0 < i := loop.1
      change n (.poll 2462)=min (i+1) (low v) at hq
      change n (.poll 2510)=i-1 at hp'
      change n .shfl+0=1+n (.poll 2462)+n (.poll 2510) at bal
      rw [limit] at hq
      change n (.poll 2462)=min (i+1) (Q.numIters _ _) at hq
      rw [cn,cnt]; omega

/-- A KV-empty commit is past the ready broadcast for each ready poll in its prefix. -/
public theorem empty_shuffles {Q L m X g k sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (warp : g%L.block/32=7) (he : X.get (g,k)=some ⟨2546,.tc (.commit sp)⟩) :
    let es := (X.tr g).take k
    let r := pollRound 2462 es
    1+r+(r-1) ≤ es.countP Execution.isShfl := by
  obtain ⟨_,_,i,d,n,hs,inv⟩ := worker_event hp hX hf he (by simp)
    (by decide : 2344<2546) (by decide : 2546<2557) (by decide : 2546≠2422)
  cases i with
  | loader =>
    have wrong : g%L.block/32=6 := inv.1
    omega
  | mma =>
    obtain ⟨_,_,ready,prob,-⟩ := inv
    have bal := mma_balance hp hX hf (Frame.lt_of_get hX he) warp
      (Frame.noUbBefore_of_get hX he) hs
    have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
    have only (s : Site) : 2546=s.pc → s=.pvCommit1 := by
      cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
    obtain ⟨s,i,v⟩ := d
    obtain rfl := only s pc
    change n (.poll 2462)=min (i+1) (low v) at ready
    change n (.poll 2510)=i at prob
    change n .shfl+0=1+n (.poll 2462)+n (.poll 2510) at bal
    have rd := fcount hs (.poll 2462)
    change n (.poll 2462)=pollRound 2462 _ at rd
    have sh := fcount hs .shfl
    change n .shfl=((X.tr g).take k).countP Execution.isShfl at sh
    dsimp only
    omega

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export
