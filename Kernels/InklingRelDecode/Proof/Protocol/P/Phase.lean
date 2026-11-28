-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.P.DoneBudget
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.Publication
import Kernels.InklingRelDecode.Proof.Softmax.Export.ArrivalCredit
import Kernels.InklingRelDecode.Proof.Lib.IssueCount
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarArrivals
import Lemmas.Protocol.PollLe
import Lemmas.Protocol.NotifyBlocker

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.P
open PTX PTX.Flow PTX.Sched PTX.MbarRing Scalar

/-- Lane zero's arrivals on a probability slot are bounded by a tag of the arrival's ordinal
among its publications. -/
theorem arrivals_le {Q L X c s y n} (rows : MbarRows Q L X) (hy : y<L.threads)
    (bound : ∀ k tx cnt rel sc,
      X.get (y,k)=some ⟨1013,.arrive ((Object.prob s).loc L c) tx cnt rel sc⟩ →
      s.val=((X.tr y).take k).countP (fun a => a.pc==1013)%2 →
      ((X.tr y).take k).countP (fun a => a.pc==1013)/2<n) :
    arrivals ((Object.prob s).loc L c) (X.tr y)≤n := by
  let p (e : Event) := e.pc==1013
  let num (k : Nat) := ((X.tr y).take k).countP p
  apply Lib.count_le_tags (fun k => num k/2)
  · intro k e he use
    obtain ⟨tx,n,rel,sc,eq,slot⟩ := arrival_event rows hy he use
    exact bound k tx n rel sc (eq ▸ he) slot
  · intro k j e f he ue hf uf eq
    obtain ⟨_,_,_,_,tag,pos⟩ := arrival_event rows hy he ue
    obtain ⟨_,_,_,_,tag',pos'⟩ := arrival_event rows hy hf uf
    change s.val=num k%2 at pos
    change s.val=num j%2 at pos'
    have tags : num k=num j := by change num k/2=num j/2 at eq; omega
    have a := nthEv_eq (p := p) he (by simp [tag,p])
    have b := nthEv_eq (p := p) hf (by simp [tag',p])
    exact a.symm.trans ((congrArg (nthEv X p y) tags).trans b)

/-- The publisher can be ahead by one P arrival globally: each later publication
requires its own completed poll on the output of the preceding PV. -/
theorem arrival_bound {Q L m X c g s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (followed : ∀ Y, Consistent L kernel Assumptions.all m Y → Follow Q L Y)
    (rows : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows Q L Y)
    (init : Mbar.InitRows L X) (words : RoleBytes L X) (wait : Waiting L m X (.prob s) c g) :
    arrivals ((Object.prob s).loc L c) (X.tr (c*L.block)) ≤
      (Object.prob s).visits (pollRound 2510 (X.tr g)+1) := by
  have budget := done_count hp hX followed rows words wait
  obtain ⟨q,sc,hn⟩ := wait
  obtain ⟨Y,hY,_,get⟩ := id hn
  have hg := hn.lt
  obtain ⟨cta,_,_,_⟩ := wait_obj (rows Y hY) hg get
  have hc : c<L.grid := by rw [←cta]; apply Nat.div_lt_of_lt_mul; simpa [Launch.threads,
    Nat.mul_comm] using hg
  let y := c*L.block
  have cy : y/L.block=c := by simp [y,hp.block]
  have hy : y<L.threads := by simp only [y,hp.block,Launch.threads] at *; omega
  have obj := notification hp hX (followed X hX) (rows X hX) init (c := c) (.inr rfl)
  have live := Mbar.next_published hp hX hn (by decide : Export.afterInit 2510=true) (10 : Fin 12)
  change X.objects (Object.done.loc L (g/L.block))≠[] at live
  rw [cta] at live
  obtain ⟨st,state⟩ := Unit.final_of_init hX obj.init obj.noInval live
  have poll := okPolls_le_phase (g := y) hX obj.δ_le (obj.pclean hX) obj.noInval
    (fun _ _ _ _ _ he => obj.parity he) state
  have cap := obj.phase_le_commit_count hX state
  apply arrivals_le (rows X hX) hy
  intro k tx n rel sc get slot
  have cnt := (Softmax.Export.arrival_polls hp hX (followed X hX) get).1
  have ord := Scalar.count (rows X hX) hy Object.done k
  change okPolls (Object.done.loc L (y/L.block)) ((X.tr y).take k)=
    (pollRound 2239 ((X.tr y).take k)+1-1-0)/1 at ord
  simp only [Nat.add_sub_cancel,Nat.sub_zero,Nat.div_one,cy] at ord
  have mono := countP_take_mono (okPoll (Object.done.loc L c)) (X.tr y)
    (List.getElem?_eq_some_iff.mp get).1.le
  rw [List.take_length] at mono
  change okPolls _ ((X.tr y).take k)≤okPolls _ (X.tr y) at mono
  rw [ord,cnt] at mono
  change ((X.tr y).take k).countP (fun a => a.pc==1013)/2<
    (pollRound 2510 (X.tr g)+1+2-1-s.val)/2
  omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.P
