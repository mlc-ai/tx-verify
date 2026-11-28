-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.P.Arrived
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.PeerRound

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.P
open PTX PTX.Flow

/-- A thread that has succeeded in `r` PV polls has seen `r` published probability blocks, so
every data lane of its CTA has polled `r` scores and `r-1` outputs. -/
theorem peers_ahead {Q L m X z k e g} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (rows : MbarRows Q L X)
    (init : Mbar.InitRows L X) (safe : ¬Race L X) (free : ∀ l, ∀ r ∈ X.objects l, r.fault=none)
    (he : X.get (z,k)=some e) (nu : ∀ f, e.kind≠.ub f) (site : Export.afterInit e.pc)
    (pos : 0<pollRound 2510 ((X.tr z).take k)) (lg : g%L.block<128) (cta : g/L.block=z/L.block) :
    pollRound 2510 ((X.tr z).take k)≤pollRound 1257 (X.tr g) ∧
      pollRound 2510 ((X.tr z).take k)≤pollRound 2239 (X.tr g)+1 := by
  obtain ⟨i,l,tx,n,rel,sc,arr,bound⟩ := polls_arrive hp hX rows init free he nu site pos
  have lx : z/L.block*L.block%L.block<128 := by rw [Nat.mul_mod_left]; omega
  have := Shared.peer_polls hp hX hf safe arr lx lg (by rw [cta, Nat.mul_div_cancel _
    (by rw [hp.block]; decide)])
  dsimp only at this
  omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.P
