-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteOrder
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.StoreMma
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaDone
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.BlockCounts
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LastBar
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
import Lemmas.Kernel.Frame
import Lemmas.Kernel.Safety.TableU
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.PeerBar
import Kernels.InklingRelDecode.Proof.Common.Export.TcOperand
import Kernels.InklingRelDecode.Proof.Common.Export.TcCount
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues

@[expose] public section

/-! # A PV MMA and a rescale store are ordered

The PV MMA of block `b - 1` and the rescale store of round `r`: if `b ≤ r` the lane zero's output
poll of the round (before the round's rendezvous, which the store follows) observes a done commit
after the MMA; otherwise the MMA lane's poll of the probability slot observes the publication that
follows the store. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.MbarRing PTX.TcMma Protocol.Scalar

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A PV MMA and a rescale store are ordered.** -/
theorem pv_store_order (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) : PvStoreOrder L X := by
  intro x y pc d a s acc mask vals sh hx pv hy cta
  obtain ⟨g,k⟩ := x
  obtain ⟨t,sk⟩ := y
  simp only at cta
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  have hg := Frame.lt_of_get hX hx
  obtain ⟨b,-,q1,bpos,-,-,warp,-⟩ := Mma.Export.pv_block hp hX hf base hx pv
  obtain ⟨lead,-⟩ := mma_leader hp hX hf hx
  simp only at lead warp
  have pvl : pc ∈ [2530,2533,2535,2537,2539,2541,2543,2545] := by
    obtain ⟨j,rfl⟩ := pv
    fin_cases j <;> decide
  have hbl : 0 < L.block := by rw [hp.block]; decide
  have hc : g/L.block < L.grid := (Nat.div_lt_iff_lt_mul hbl).2 hg
  have hz : g/L.block*L.block < L.threads := by simp only [Launch.threads,hp.block] at *; omega
  have cz : g/L.block*L.block/L.block = g/L.block := by simp [hp.block]
  have lp : g/L.block*L.block%L.block < 128 := by rw [Nat.mul_mod_left]; omega
  have lt := Export.tc_data_lane hp hX hf hy (by rfl)
  have tc : isTcColl ⟨2328,.tc (.st a vals sh)⟩ = true := rfl
  obtain ⟨r,w,s1,-,s3,-⟩ := Export.st_round hp hX hf base hy tc (.inr rfl)
  have lent : sk < (X.tr t).length := (List.getElem?_eq_some_iff.mp hy).1
  rcases Nat.lt_or_ge r b with big | small
  · refine .inr ?_
    have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp hx).1
    have cnt := Protocol.Scalar.count rows hg (Object.prob (MbarRow.slot2 r)) k
    change okPolls ((Object.prob (MbarRow.slot2 r)).loc L (g/L.block)) ((X.tr g).take k) =
      (Object.prob (MbarRow.slot2 r)).visits (pollRound 2510 ((X.tr g).take k)) at cnt
    rw [q1] at cnt
    have vis : (Object.prob (MbarRow.slot2 r)).visits b = (b+2-1-r%2)/2 := rfl
    have := store_before_mma hp hX hf safe base rows init words hc hy (.inr rfl) lt
      (by rw [cta]) s1 (k := k) (by rw [lead]; exact hk) (by
        rw [lead]; rw [cnt,vis]; omega)
    rw [lead] at this
    exact this
  · refine .inl ?_
    have nu : ∀ i ev, i < sk → X.get (t,i) = some ev → ∀ f, ev.kind ≠ .ub f :=
      fun i ev hi get => Frame.noUbBefore_of_get hX hy i hi ev get
    simp only [show (2328 = 1009) = False from by decide,ite_false] at s3
    obtain ⟨jb,pcb,cb,hjb,hbar,hpcb,hmand⟩ := last_bar hX hp.block (t := t) nu (by omega)
    obtain ⟨ir,r1,r2,r3⟩ := bar_round_facts hp hX hf hbar hpcb
    have bp : barPos pcb ≤ 3 := by unfold barPos; split_ifs <;> omega
    have ir_r : ir = r := by omega
    subst ir_r
    obtain ⟨ib,cb',hb2,ord,p1,p2⟩ := peer_bar hp hX hf safe (t := t) (h := g/L.block*L.block)
      hpcb hbar (by omega) lt lp (by rw [cz,cta])
    have cnt := Protocol.Scalar.count rows hz Object.done ib
    change okPolls (Object.done.loc L (g/L.block*L.block/L.block))
      ((X.tr (g/L.block*L.block)).take ib) = Object.done.visits
      (pollRound 2239 ((X.tr (g/L.block*L.block)).take ib)) at cnt
    rw [cz,p2,r2] at cnt
    have vis : Object.done.visits ir = ir := by simp [Object.visits,Object.width,Object.index]
    obtain ⟨j,pcj,pj,acq,scj,hjib,hw,hq⟩ := MbarRing.UnitHandoff.exists_poll
      (m := Object.done.loc L (g/L.block)) (h := g/L.block*L.block)
      (f := ib) (c := ir-1) (by rw [cnt,vis]; omega)
    have few := pv_commits_before hp hX hf rows words (c := g/L.block) hg hx pvl warp q1
    have po : baseCausality L X (g/L.block*L.block,j) (t,sk) :=
      Protocol.Shared.scratch_handoff hp hX hb2 hbar (by rw [cz,cta]) lp lt ord hjib hjb lent
    exact mma_done_before hp hX hf rows init words hc (o := Object.done)
      (Or.inr rfl) hw hq hx lead.symm (by dsimp only; omega) po

end PTX.Kernels.InklingRelDecode.Proof.Tmem
