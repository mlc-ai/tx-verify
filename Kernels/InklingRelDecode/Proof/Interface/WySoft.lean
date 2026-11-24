-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.WyPoll
public import Kernels.InklingRelDecode.Proof.Interface.HsLayer
public import Kernels.InklingRelDecode.Proof.Interface.LockBar0
public import Kernels.InklingRelDecode.Proof.Protocol.RdSmCount
public import Kernels.InklingRelDecode.Proof.Protocol.IpLifeCommit
public import Kernels.InklingRelDecode.Proof.Protocol.IpMmaThread
public import Kernels.InklingRelDecode.Proof.Protocol.HsParity
public import Lemmas.Protocol.NotifyBlocker

@[expose] public section

/-!
# Who blocks the softmax region's polls of `s_ready` and `o_done`

Both objects are commit objects of the CTA's committing MMA lane `cm` (`SO.sObj`, `SO.oObj`:
`MbarRing.Notify.Obj`, offset 0). A softmax thread at its poll of `s_ready (i % 2)` has `i / 2`
successful polls of it (`Rd.sm_cnt`, `smPolled`), and at its poll of `o_done` it has `i - 1`
(`smOPolled`, `OdoneOk`): the poll's parity is that of its successful polls (`soft_parity`). When
the object's final phase has that parity, the committing lane has made no more commits to it than
the thread's successful polls, or some commit's notification is undelivered (`soft_blocked`, from
`MbarRing.Notify.Obj.blocker` with the reuse paths `Mbar.sReach`, `Mbar.oReach` and the faults
`Mbar.s_faultFree`, `Mbar.o_faultFree` of the handshake package).

The epilogue's poll of `o_final` is the thread's first (`Hs.epi_cnt`), with parity 0; `o_final`
is a commit object of the committing lane, which commits to it at most once (`IpMma.final_first`),
so its reuse paths are empty and `Notify.Obj.blocker` applies with no successful poll: when the
final phase is even, the lane has made no commit to `o_final`, or a notification is undelivered
(`epi_poll_blocked`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady oDone)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **A commit of the kernel targets the barrier it names.** -/
theorem commit_target_self (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k pc : Nat} {sp : TcCommit.Spec}
    (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩) :
    ∃ rank, TcCommit.target sp rank = some sp.mbar := by
  obtain ⟨d, P, -, h⟩ := Hs.commit_state hpre hX hf he
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
    exact ⟨⟨0, by omega⟩, by rw [Life.target_commitSpec_zero]; rfl⟩

/-- **The poll of a softmax thread has the parity of its successful polls.** -/
theorem soft_parity (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) {d : Sm.D}
    (hσ : St Q L X g (X.tr g).length = some (some (.d (.sm d)))) {m : Loc} {par : Nat}
    (h : PollAt L g (.d (.sm d)) m par) :
    ((∃ b, b < 2 ∧ m = sReady L (g / L.block) b) ∨ m = oDone L (g / L.block)) ∧
      okPolls m (X.tr g) % 2 = par % 2 := by
  have hc := (Rd.sm_cnt hpre hX hf hg _ le_rfl _ hσ).2 d rfl
  have hc1 := hc.s
  have hc2 := hc.o
  rw [List.take_length] at hc1 hc2
  rcases h with ⟨hs, rfl, rfl⟩ | ⟨hs, rfl, rfl⟩
  · refine ⟨.inl ⟨_, Nat.mod_lt _ (by omega), rfl⟩, ?_⟩
    rw [hc1 _ (Nat.mod_lt _ (by omega))]
    simp only [SO.smPolled, hs, SO.below2]
    omega
  · refine ⟨.inr rfl, ?_⟩
    have h1 := hc.ok hs
    rw [hc2]
    simp only [SO.smOPolled, hs]
    omega

/-- **Who blocks a softmax thread's poll of `s_ready b` or `o_done`.** When the object's final
phase has the parity of the thread's successful polls, the committing lane has made no more
commits to it than those polls, or a commit's notification is undelivered. -/
theorem soft_blocked (P : Sr.SrPkg L kernel asms mem0 X) (hpre : Pre Q L mem0)
    (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X) {c : Nat}
    (hc : c < L.grid) {h : Nat} (hh : Sr.SoftOf L c h) {m : Loc}
    (hm : (∃ b, b < 2 ∧ m = sReady L c b) ∨ m = oDone L c) {before : MBarrier.State}
    (hs : MBarrier.stateBefore (X.objects m) (X.objects m).length = some before)
    (hpar : before.phase % 2 = okPolls m (X.tr h) % 2) :
    (X.tr (P.cm c)).countP (commitsTo m) ≤ okPolls m (X.tr h) ∨ Descent.Obl L X .commit := by
  have H := P.ctx c hc
  have htgt : ∀ {i pc : Nat} {sp : TcCommit.Spec},
      X.get (P.cm c, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = m →
        ∃ rank, TcCommit.target sp rank = some m := by
    intro i pc sp he hmb
    obtain ⟨rank, hr⟩ := commit_target_self hpre hX hf he
    exact ⟨rank, hmb ▸ hr⟩
  rcases hm with ⟨b, hb, rfl⟩ | rfl
  · have hk := MbarRing.Notify.Obj.blocker hX (SO.sObj hX H.facts hb) (Mbar.sReach H hb hh)
      (Mbar.s_faultFree H hb) htgt hs (by simpa using hpar) (Nat.zero_le _)
    rcases hk.2 with h1 | h1
    · exact .inl (by have := hk.1; omega)
    · exact .inr h1
  · have O := SO.oObj hX H.facts H.opar
    have hb := MbarRing.Notify.Obj.blocker hX O (Mbar.oReach H hh) (Mbar.o_faultFree H) htgt hs
      (by simpa using hpar) (Nat.zero_le _)
    rcases hb.2 with h1 | h1
    · exact .inl (by have := hb.1; omega)
    · exact .inr h1

/-- **Who blocks a softmax thread at its poll**: the committing lane of its CTA has made no more
commits to the polled object than the thread's successful polls of it, or a commit's notification
is undelivered. -/
theorem soft_poll_blocked (P : Sr.SrPkg L kernel asms mem0 X) (hpre : Pre Q L mem0)
    (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads)
    {d : Sm.D} (hσ : St Q L X g (X.tr g).length = some (some (.d (.sm d)))) {m : Loc}
    {par : Nat} (h : PollAt L g (.d (.sm d)) m par) {before : MBarrier.State}
    (hs : MBarrier.stateBefore (X.objects m) (X.objects m).length = some before)
    (hpar : before.phase % 2 = par % 2) :
    (X.tr (P.cm (g / L.block))).countP (commitsTo m) ≤ okPolls m (X.tr g) ∨
      Descent.Obl L X .commit := by
  have hgrid : g / L.block < L.grid := by
    unfold Launch.threads at hg
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  obtain ⟨hm, hp⟩ := soft_parity hpre hX hf hg hσ h
  have h128 : g % L.block < 128 := (cls_inv _ _ le_rfl hσ).mp trivial
  exact soft_blocked P hpre hX hf hgrid ⟨hg, rfl, h128⟩ hm hs (by omega)

/-- **Who blocks an epilogue thread at its poll of `o_final`**: the committing lane of its CTA has
made no commit to `o_final`, or a commit's notification is undelivered. -/
theorem epi_poll_blocked (P : Sr.SrPkg L kernel asms mem0 X) (hpre : Pre Q L mem0)
    (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X)
    (hg : g < L.threads) {d : Epi.D}
    (hσ : St Q L X g (X.tr g).length = some (some (.d (.epi d)))) {m : Loc} {par : Nat}
    (h : PollAt L g (.d (.epi d)) m par) {before : MBarrier.State}
    (hs : MBarrier.stateBefore (X.objects m) (X.objects m).length = some before)
    (hpar : before.phase % 2 = par % 2) :
    (X.tr (P.cm (g / L.block))).countP (commitsTo m) = 0 ∨ Descent.Obl L X .commit := by
  have hgrid : g / L.block < L.grid := by
    unfold Launch.threads at hg
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  obtain ⟨hw, rfl, rfl⟩ := h
  set c := g / L.block with hc
  have H := P.ctx c hgrid
  obtain ⟨-, hcmc⟩ := (P.lane c hgrid).cm_ok
  have hone : ∀ {i pc : Nat} {sp : TcCommit.Spec},
      X.get (P.cm c, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = EvW.oFinal L c →
        ((X.tr (P.cm c)).take i).countP (commitsTo (EvW.oFinal L c)) = 0 := by
    intro i pc sp he hm
    have := IpMma.final_first hpre hX hf hR he (by rw [hcmc]; exact hm)
    rwa [hcmc] at this
  have O := SO.fObj hX H.facts
  have hReach : MbarRing.Notify.Reach L kernel asms X (EvW.oFinal L c) (P.cm c)
      (EvW.oFinal L c) 0 g :=
    MbarRing.Notify.Reach.of_records O fun i rank hrec j hj => by
      obtain ⟨r, hr, hid, -⟩ := hrec
      obtain ⟨pc, sp, hy, ht, -⟩ := Mbar.notify_rec hX hr hid
      have hm := (Hs.commit_target hpre hX hf hy ht).1
      rw [hone hy hm] at hj
      omega
  have htgt : ∀ {i pc : Nat} {sp : TcCommit.Spec},
      X.get (P.cm c, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = EvW.oFinal L c →
        ∃ rank, TcCommit.target sp rank = some (EvW.oFinal L c) := by
    intro i pc sp he hmb
    obtain ⟨rank, hr⟩ := commit_target_self hpre hX hf he
    exact ⟨rank, hmb ▸ hr⟩
  have hcnt : okPolls (EvW.oFinal L c) (X.tr g) = 0 := by
    have := Hs.epi_cnt hpre hX hf hg _ le_rfl _ hσ
    rw [List.take_length] at this
    rw [this]
    simp [Hs.fCnt, SO.epiPolled, hw]
  have hb := MbarRing.Notify.Obj.blocker hX O hReach (Mbar.f_faultFree hX H.facts hone) htgt hs
    (by rw [hcnt]; simpa using hpar) (Nat.zero_le _)
  rcases hb.2 with h1 | h1
  · exact .inl (by have := hb.1; rw [hcnt] at this; omega)
  · exact .inr h1

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
