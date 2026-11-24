-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.WySoft

@[expose] public section

/-!
# Who blocks the MMA warp's poll of `p_ready`

`p_ready b` is a unit object of thread 0 of the CTA (`SO.pObj`: one producer, offset 0), polled by
the lanes of the MMA warp with the reuse paths `Mbar.pReach`. When its final phase has the parity
of a lane's successful polls of it, the phase is those polls and thread 0 has made no more
arrivals on it than the phase (`MbarRing.Unit.Obj.reach_short`, no record faulting:
`Mbar.p_faultFree`): `mma_p_blocked`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (pReady)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **A thread at an MMA-warp state is a lane of its CTA's MMA warp.** -/
theorem mma_lane (hW : RoleWarps Q L X) (hg : g < L.threads) {d : Mma.D} {P : Loader.Pro}
    (hσ : St Q L X g (X.tr g).length = some (some (.w (.mma d P)))) :
    Hs.MmaOf L (g / L.block) g := by
  have h := roleWarp_inv hW _ _ le_rfl hσ
  simp only [RoleWarp, Ledger.roleWarp] at h
  exact ⟨hg, rfl, h⟩

/-- **Who blocks an MMA lane's poll of `p_ready b`.** When the object's final phase has the
parity of the lane's successful polls of it, thread 0 of the CTA has made no more arrivals on it
than those polls. -/
theorem mma_p_blocked (P : Sr.SrPkg L kernel asms mem0 X) (hX : Consistent L kernel asms mem0 X)
    {c : Nat} (hc : c < L.grid) {h : Nat} (hh : P.Mma c h) {b : Nat} (hb : b < 2)
    {before : MBarrier.State}
    (hs : MBarrier.stateBefore (X.objects (pReady L c b)) (X.objects (pReady L c b)).length =
      some before)
    (hpar : before.phase % 2 = okPolls (pReady L c b) (X.tr h) % 2) :
    arrivals (pReady L c b) (X.tr (P.p0 c)) ≤ okPolls (pReady L c b) (X.tr h) := by
  have H := P.ctx c hc
  obtain ⟨hph, a, ha⟩ := MbarRing.Unit.Obj.reach_short hX (SO.pObj hX H.facts hb)
    (Mbar.pReach H hb hh) (Mbar.p_faultFree H hb) hs (Nat.zero_le _) (by simpa using hpar)
  omega

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
