-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.P.Phase
public import Kernels.InklingRelDecode.Proof.Common.Export.Publication
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.Publication
import Kernels.InklingRelDecode.Proof.Lib.OneProducer

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.P
open PTX PTX.Flow PTX.Sched PTX.MbarRing Scalar MbarRow

/-- A thread that has succeeded in `r` PV polls has seen `r` published probability blocks: lane
zero has made an arrival whose ordinal is at least `r-1`. -/
theorem polls_arrive {Q L m X z k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (rows : MbarRows Q L X)
    (init : Mbar.InitRows L X) (free : ∀ l, ∀ r ∈ X.objects l, r.fault=none)
    (he : X.get (z,k)=some e) (nu : ∀ f, e.kind≠.ub f) (site : Export.afterInit e.pc)
    (pos : 0<pollRound 2510 ((X.tr z).take k)) :
    ∃ i l tx cnt rel sc, X.get (z/L.block*L.block,i)=some ⟨1013,.arrive l tx cnt rel sc⟩ ∧
      pollRound 2510 ((X.tr z).take k)≤((X.tr (z/L.block*L.block)).take i).countP
        (fun a => a.pc==1013)+1 := by
  by_contra none
  push Not at none
  have hz := Frame.lt_of_get hX he
  let c := z/L.block
  let r := pollRound 2510 ((X.tr z).take k)
  let s : Fin 2 := ⟨(r+1)%2,by omega⟩
  have hc : c<L.grid := Nat.div_lt_of_lt_mul (by simpa [Launch.threads,Nat.mul_comm] using hz)
  have hy : c*L.block<L.threads := by simp only [Launch.threads,hp.block] at *; omega
  have cnt := Scalar.count rows hz (Object.prob s) k
  change okPolls ((Object.prob s).loc L c) ((X.tr z).take k)=(Object.prob s).visits r at cnt
  have obj := probability hX rows init (c := c) s
  have offset (u : Fin 2) : initOffset ⟨7+2*u.val,by have := u.isLt; omega⟩=Iface.pReady u := by
    fin_cases u <;> rfl
  have live := Mbar.event_published hp hX he nu site ⟨7+2*s.val,by have := s.isLt; omega⟩
  rw [offset s] at live
  obtain ⟨st,state⟩ := Unit.final_of_init hX obj.init obj.noInval live
  have poll := obj.okPolls_le hX z state
  have ceiling := Lib.unit_phase_le hX obj (free _) state
  have mono := countP_take_mono (okPoll ((Object.prob s).loc L c)) (X.tr z)
    (List.getElem?_eq_some_iff.mp he).1.le
  rw [List.take_length] at mono
  change okPolls _ ((X.tr z).take k)≤okPolls _ (X.tr z) at mono
  have upper : arrivals ((Object.prob s).loc L c) (X.tr (c*L.block))≤(r-s.val)/2 := by
    apply arrivals_le (rows) hy
    intro j tx n rel sc get slot
    have : ((X.tr (c*L.block)).take j).countP (fun a => a.pc==1013)+1<r :=
      none j _ tx n rel sc get
    change s.val=_%2 at slot
    change _/2<(r-s.val)/2
    omega
  have : (Object.prob s).visits r=(r+2-1-s.val)/2 := rfl
  have sv : s.val=(r+1)%2 := rfl
  omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.P
