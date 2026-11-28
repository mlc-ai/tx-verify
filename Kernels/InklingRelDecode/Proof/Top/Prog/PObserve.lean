-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.P.Phase
public import Kernels.InklingRelDecode.Proof.Top.Prog.ScalarLag
import Kernels.InklingRelDecode.Proof.Lib.OneProducer
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.Publication

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.P
open PTX PTX.Flow PTX.Sched PTX.MbarRing Scalar MbarRow

theorem wait_blk {Q L m X g l q sc} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hu : ¬HasUb X) (followed : ∀ Y, Consistent L kernel Assumptions.all m Y → Follow Q L Y)
    (rows : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows Q L Y)
    (init : Mbar.InitRows L X) (words : RoleBytes L X) (free : ∀ r ∈ X.objects l, r.fault=none)
    (hn : NextEv L kernel Assumptions.all m X g ⟨2510,.wait l q false true sc⟩) :
    WaitBlk (schedule Q L) X g l q := by
  have hg := hn.lt
  obtain ⟨Y,hY,pref,get⟩ := id hn
  let c := g/L.block
  let r := pollRound 2510 (X.tr g)
  let s := slot2 r
  let o := Object.prob s
  have addr := wait_pc (rows Y hY) hg (.prob 0) get
  change l=(Object.prob (slot2 (pollRound 2510 ((Y.tr g).take _)))).loc L c at addr
  rw [pref] at addr
  subst l
  have wait : Waiting L m X o c g := ⟨q,sc,hn⟩
  have par := parity (rows Y hY) hg get
  rw [pref] at par
  have n := count (rows Y hY) hg o (X.tr g).length
  simp only [roundAt,pref] at n
  change okPolls (o.loc L c) (X.tr g)=o.visits r at n
  have hc : c<L.grid := Nat.div_lt_of_lt_mul (by simpa [Launch.threads,Nat.mul_comm] using hg)
  have obj := probability hX (rows X hX) init (c := c) s
  let idx : Fin 12 := ⟨7+2*s.val,by have := s.isLt; omega⟩
  have offset (u : Fin 2) : initOffset ⟨7+2*u.val,by have := u.isLt; omega⟩=Iface.pReady u := by
    fin_cases u <;> rfl
  have live := Mbar.next_published hp hX hn (by decide) idx
  rw [show initOffset idx=Iface.pReady s from offset s] at live
  obtain ⟨st,state⟩ := Unit.final_of_init hX obj.init obj.noInval live
  refine ⟨st,state,fun blocked => ?_⟩
  have upper := arrival_bound hp hX followed rows init words wait
  have one : o.visits (r+1)≤o.visits r+1 := by
    change (r+1+2-1-s.val)/2≤(r+2-1-s.val)/2+1
    omega
  have ceiling := Lib.unit_phase_le hX obj free state
  change arrivals (o.loc L c) _≤o.visits (r+1) at upper
  change st.phase≤arrivals (o.loc L c) (X.tr (c*L.block)) at ceiling
  change q=okPolls (o.loc L c) (X.tr g)%2 at par
  change st.phase%2=q%2 at blocked
  have phase : st.phase≤okPolls (o.loc L c) (X.tr g) := by omega
  obtain ⟨a,short⟩ := obj.blocked hX state
  have issued := Unit.arrivals_le_unitRec hX free (c*L.block)
  obtain ⟨_,clock⟩ := Scalar.lag hp hX (followed X hX) words hu hc rows o
  have hy : c*L.block<L.threads := by simp only [Launch.threads,hp.block] at *; omega
  apply clock.blk hX hu hg wait (poll_floor hp (followed X hX) (by decide) hn).1
    (y := c*L.block) rfl hy (by rw [Nat.mul_div_cancel _ (hp.block ▸ by decide : 0<L.block)])
  exact (issued.trans short).trans phase

end PTX.Kernels.InklingRelDecode.Proof.Protocol.P
