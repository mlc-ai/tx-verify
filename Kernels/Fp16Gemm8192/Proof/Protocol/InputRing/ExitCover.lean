-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Pairs
public import Kernels.Fp16Gemm8192.Proof.Protocol.Exit.Order
public import Kernels.Fp16Gemm8192.Proof.Protocol.Exit.ClusterAll
public import Lemmas.TensorStore.TensorExecution
public import Lemmas.Kernel.SharedLifetime
public import Kernels.Fp16Gemm8192.Proof.Protocol.Elected

@[expose] public section

/-! # The input ring's exit coverage

Once a thread of a cluster has exited, every thread of the cluster has made its exit arrival
(`ClusterExitAll`). So the elected lane of the leader CTA's MMA warp 8 has reached its exit arrival,
where it has polled each slot's full barrier 32 times per successful response poll, and its latest
response read claims no CTA (`ThreadFacts.mma_exit_tasks`). A loader at a load is in a task its
earlier response reads all claimed, with at most 32 empty polls per task on each slot
(`ThreadFacts.loader_load_tasks`); the responses of the cluster agree (`AllResponsesAgree`), so the
loader's task is before the MMA thread's last one. The MMA thread has then polled the load's slot
at least once more than the load's production, and that poll observes the load's completion
(`copy_observed`). The poll comes before the MMA thread's exit arrival, so it
happens before every exit of the cluster (`ExitOrder`): the load's writes and notification finish
before the exit of any thread of an exited CTA it targets (`tensorExitFinished`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace InputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A state outside the exit stage has made at most one cluster arrival. -/
theorem clPhase_le_of_exitOff {d : ThreadD} (h : d.exitOff = none) : d.clPhase ≤ 1 := by
  rcases d with ⟨site, _⟩ | (⟨site, _⟩ | ⟨site, _⟩ | ⟨site, _⟩ | ⟨site, _⟩) <;>
    cases site <;> simp_all [ThreadD.exitOff, ThreadD.clPhase, Loader.exitOff, Mma.exitOff,
      Scheduler.exitOff, Consumer.exitOff]

/-- The last event of an exited thread is an exit event. -/
theorem exit_get {h pc : Nat} (hlast : (X.tr h).getLast? = some ⟨pc, .exit⟩) :
    X.get (h, (X.tr h).length - 1) = some ⟨pc, .exit⟩ := by
  change (X.tr h)[(X.tr h).length - 1]? = _
  rw [← List.getLast?_eq_getElem?]
  exact hlast

/-- **An elected MMA lane past its exit arrival.** Once a thread of cluster `c` has exited, warp 8
of the leader CTA has a lane elected by its warp, with both its cluster arrivals. -/
theorem elected_mma (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {hx px : Nat} (hhx : hx < L.threads)
    (hlast : (X.tr hx).getLast? = some ⟨px, .exit⟩) :
    ∃ M jM pcM maskM instM, M < L.threads ∧ M / L.block = 2 * (hx / L.block / 2) ∧
      M % L.block / 32 = 8 ∧ X.Elect (M, jM) pcM maskM instM (laneOf L M) ∧
      clArrives (X.tr M) = 2 := by
  have hb := hpre.block
  have hce := clusterExitAll hpre hX ht
  set c := hx / L.block / 2 with hc
  have hgx : hx / L.block < L.grid := by
    have : hx < L.grid * L.block := hhx
    exact (Nat.div_lt_iff_lt_mul (by omega)).mpr this
  have hc2 : 2 * c + 1 ≤ L.grid := by omega
  set h0 := 2 * c * L.block + 256 with hh0
  have hh0t : h0 < L.threads := by
    change _ < L.grid * L.block
    rw [hh0, hb]
    omega
  have hh0c : h0 / L.block = 2 * c := by rw [hh0, hb]; omega
  have hh0w : h0 % L.block / 32 = 8 := by rw [hh0, hb]; omega
  have hsame : ∀ g, g / L.block / 2 = c →
      L.clusterOfCta (g / L.block) = L.clusterOfCta (hx / L.block) := by
    intro g hg
    simp only [clusterOfCta_eq hpre]
    omega
  have h02 : clArrives (X.tr h0) = 2 := hce hx px hhx hlast h0 hh0t (hsame h0 (by omega))
  by_cases hel : ∃ j pc mask inst leader, X.Elect (h0, j) pc mask inst leader
  · obtain ⟨j, pc, mask, inst, leader, hE⟩ := hel
    obtain ⟨M, jM, hM, ⟨⟨-, -, hcta⟩, hwarp⟩, hE'⟩ := elected_of_elect hpre hX hE
    exact ⟨M, jM, pc, mask, inst, hM, by omega, by omega, hE',
      hce hx px hhx hlast M hM (hsame M (by omega))⟩
  · exfalso
    obtain ⟨d, hσ, hoff, -⟩ := ht.mma_unelected hh0t (by omega) (.inl hh0w)
      (fun j pc mask inst leader h => hel ⟨j, pc, mask, inst, leader, h⟩)
    have h1 := ht.cl_phase hh0t hσ
    have h2 := clPhase_le_of_exitOff hoff
    omega

/-- **The exit arrival of an MMA lane.** A thread of warp 8 or 9 with both its cluster arrivals
makes the second at an MMA state at its exit arrival, with one arrival before it. -/
theorem exit_arrival (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {M : Nat}
    (hM : M < L.threads) (hMw : M % L.block / 32 = 8 ∨ M % L.block / 32 = 9)
    (h2 : clArrives (X.tr M) = 2) :
    ∃ ka m, ka < (X.tr M).length ∧ Frame.stateAt (code L) X M ka = some (some (.inr (.mma m))) ∧
      m.site = .exitArrive ∧ clArrives ((X.tr M).take ka) = 1 ∧
      ∃ ea, X.get (M, ka) = some ea ∧ isClArrive ea = true := by
  obtain ⟨ka, ea, hea, harr, hcnt⟩ := MbarRing.Slot.exists_nth_countP isClArrive
    (xs := X.tr M) (c := 1) (by unfold clArrives at h2; omega)
  have hlt := (List.getElem?_eq_some_iff.mp hea).1
  obtain ⟨rel, al, hk⟩ := ClusterTrace.isArr_kind harr
  have he : X.get (M, ka) = some ea := hea
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by rintro pc f rfl; cases hk)
  have hph := (ht.cluster hM he hσ).1
  have hc1 : clArrives ((X.tr M).take ka) = 1 := hcnt
  rw [hc1] at hph
  obtain ⟨hev, hat⟩ := ((ht.cl_ops hM hσ).2 ea he).1 (by simp [isCluster, hk])
  rcases d with p | (l | m | sd | cs)
  · exfalso
    simp only [ThreadD.AtCluster] at hat
    rcases hat with h | h
    · simp [ThreadD.clPhase, h] at hph
    · simp only [ThreadD.clOps, h, clEvent] at hev
      rw [hev] at hk
      cases hk
  · have := ht.role_warp hM hlt.le hσ
    simp only [roleWarp] at this
    omega
  · simp only [ThreadD.AtCluster] at hat
    rcases hat with h | h
    · exact ⟨ka, m, hlt, hσ, h, hc1, ea, he, harr⟩
    · simp [ThreadD.clPhase, h] at hph
  · have := ht.role_warp hM hlt.le hσ
    simp only [roleWarp] at this
    omega
  · have := ht.role_warp hM hlt.le hσ
    simp only [roleWarp] at this
    omega

/-- **A tensor load is observed before every exit of its cluster.** Once a thread of the load's
cluster has exited, a successful full poll of the elected MMA lane observes the load's completion,
and that poll happens before every exit in the cluster. -/
theorem issue_observed (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hag : AllResponsesAgree L X) {gl kl pc a : Nat}
    {sp : TensorCopy.Spec} (hel : X.get (gl, kl) = some ⟨pc, .tensorIssue a sp⟩) {hx px : Nat}
    (hhx : hx < L.threads) (hlast : (X.tr hx).getLast? = some ⟨px, .exit⟩)
    (hxc : hx / L.block / 2 = gl / L.block / 2) :
    ∃ w ws, AsyncObserved X (gl, kl) (.notify .load) w true ws ∧ ∀ f pcf, X.get f =
      some ⟨pcf, .exit⟩ →
      f.1 / L.block / 2 = gl / L.block / 2 →
        Relation.TransGen (DepStep L kernel X) (.thread w, true) (.thread f, false) := by
  have hb := hpre.block
  have hgl := Frame.lt_of_get hX hel
  set c := gl / L.block / 2 with hc
  obtain ⟨dl, hσl⟩ := Frame.event_state ht.sound hX ht.tracked hel (by simp)
  obtain ⟨l, bb, jj, rfl, hsite, hmb, -, -, hcount⟩ := ht.tensor_issue hgl hel hσl rfl
  set s := slotOf bb with hs
  have hml : sp.mbar = (slot L c s).full 0 := by rw [hmb, fullLoc_bar]; rfl
  obtain ⟨hE, hclaims⟩ := ht.loader_load_tasks hgl hσl hsite
  -- the elected MMA lane of warp 8 and its exit arrival
  obtain ⟨M, jM, pcM, maskM, instM, hM, hMc, hMw, hMel, hM2⟩ := elected_mma hpre hX ht hhx hlast
  rw [hxc] at hMc
  obtain ⟨ka, m, hkal, hσa, hsa, hka1, -⟩ := exit_arrival hX ht hM (.inl hMw) hM2
  obtain ⟨hfull, hclaimless, hzero, -⟩ := ht.mma_exit_tasks hM hσa hsa
  set RM := okPolls (Bar.loc L (M / L.block) ⟨.clc, 0, true⟩) ((X.tr M).take ka) with hRM
  set Rl := okPolls (Bar.loc L (gl / L.block) ⟨.clc, 0, true⟩) ((X.tr gl).take kl) with hRl
  have hpos : 0 < RM := by
    by_contra h0
    rcases hzero (by omega) with h | ⟨j, pcj, mask, inst, lane, -, hEj, hne⟩
    · simp only [Loader.leader, decide_eq_false_iff_not] at h
      omega
    · have hj := ht.elect_once hM hMel hEj
      subst hj
      have h := hMel.symm.trans hEj
      simp only [Option.some.injEq, Event.mk.injEq, Kind.elect.injEq] at h
      exact hne h.2.2.2.symm
  obtain ⟨jm, pcm, pm, acqm, scm, pcr, ra, bs, rr, hjm, hwm, hrm, hram, hresp, hncl, hcntm⟩ :=
    hclaimless hpos
  -- the loader's task is before the MMA lane's last
  have hlt : Rl < RM := by
    by_contra hge
    obtain ⟨jl, pcl, pl, acql, scl, hjl, hwl, hcl'⟩ := MbarRing.Poll.exists_nth (X := X) (g := gl)
      (k := kl) (m := Bar.loc L (gl / L.block) ⟨.clc, 0, true⟩) (n := RM - 1) (by omega)
    obtain ⟨pcr2, src2, bs2, rr2, hr2, hf2, hresp2, hcl2⟩ := hclaims jl pcl pl acql scl hjl hwl
    have hbs := hag c gl M jl jm pcl pcm pl pm pcr2 pcr acql acqm scl scm src2 ra bs2 bs rfl
      (by omega) hwl hwm (by omega) hr2 hf2 hrm hram
    rw [hbs, hresp] at hresp2
    obtain rfl := Option.some.inj hresp2
    exact hncl hcl2
  -- the load's production is below the MMA lane's full polls
  have hfo : Loader.fullOf L gl s = (slot L c s).full 0 := by
    rw [show Loader.fullOf L gl s = fullLoc L c s from rfl, fullLoc_bar]; rfl
  rw [hfo] at hcount
  have hfM : (⟨.shared, M / L.block, L.sharedBase + 8 + 8 * s.val⟩ : Loc) =
      (slot L c s).full 0 := by
    rw [hMc, show (slot L c s).full 0 = fullLoc L c s from (fullLoc_bar L c s).symm]; rfl
  have hFM := hfull s
  rw [hfM] at hFM
  have hEs := hE s
  set n := ((X.tr gl).take kl).countP (issuesTo ((slot L c s).full 0)) / 3 with hn
  have hjj := jj.isLt
  have hpolls : n + 1 ≤ okPolls ((slot L c s).full 0) ((X.tr M).take ka) := by
    have : n + 1 = okPolls (Loader.emptyOf L gl s) ((X.tr gl).take kl) := by omega
    rw [hFM]
    nlinarith
  obtain ⟨jp, pcp, pp, acqp, scp, hjp, hwp, hcp⟩ := MbarRing.Poll.exists_nth (X := X)
    (n := n) hpolls
  have hcons : consumerThread L c 0 M = true := by
    simp only [consumerThread, decide_eq_true_eq]
    exact ⟨hMc, by simpa using hMw⟩
  have hMeq := consumerOf_eq hX ht hcons hwp
  have hwp' := hwp
  rw [hMeq] at hwp' hcp
  have hTO := copy_observed hpre hX ht (b := 0) hel hml hwp' (hcp.trans hn)
  rw [← hMeq] at hTO
  refine ⟨(M, jp), _, hTO, fun f pcf hf hfc => ?_⟩
  -- the poll is before the exit arrival, so before every exit of the cluster
  obtain ⟨dp, hσp⟩ := Frame.event_state ht.sound hX ht.tracked hwp (by simp)
  have hph1 : dp.clPhase ≤ 1 := by
    have h1 := (ht.cluster hM hwp hσp).1
    have hmono := ((List.take_prefix_take_left (l := X.tr M) (show jp ≤ ka by omega)).sublist
      ).countP_le (p := isClArrive)
    change clArrives _ ≤ clArrives _ at hmono
    omega
  have hf1 := Frame.lt_of_get hX hf
  exact exitEnables hpre hX ht hwp hσp hph1 hf
    ⟨hM, hf1, by simp only [clusterOfCta_eq hpre]; omega⟩

/-- The notification of a tensor load, recorded before a wait that precedes an event in the
dependency order, finishes before it. -/
theorem notify_waits {i w f : EvId} {ws : MbarScope}
    (hTO : AsyncObserved X i (.notify .load) w true ws)
    (hen : Relation.TransGen (DepStep L kernel X) (.thread w, true) (.thread f, false)) :
    CompletedBefore L kernel Prod X (.async i (.notify .load)) (.thread f, false) := by
  obtain ⟨o, -, -, -, -, hwo⟩ := hTO.tensor
  exact CompletedBefore.of_before hwo.before hen

/-- **The input ring's exit coverage.** -/
theorem tensorExitFinished (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hag : AllResponsesAgree L X) : TensorExitFinished L X := by
  have hb := hpre.block
  -- a CTA of the load's cluster that has exited has an exit, after the load's observation
  have key : ∀ i address s T, X.TensorIssue i address s → CtaExited L X T → T < L.grid →
      T / 2 = i.1 / L.block / 2 →
      ∃ o, X.tensor i = some o ∧ o.spec = s ∧ o.effects.notified = true ∧
        (∀ slot, ∃ v, o.effects.write slot = some v) ∧
        ∃ finish pcx, finish.1 < L.threads ∧ finish.1 / L.block = T ∧
          X.get finish = some ⟨pcx, .exit⟩ ∧
          CompletedBefore L kernel Prod X (.async i (.notify .load)) (.thread finish, false) := by
    intro i address s T hi hex hT hTc
    obtain ⟨pc, hel⟩ := hi
    set g0 := T * L.block with hg0
    have hg0t : g0 < L.threads := by
      change _ < L.grid * L.block
      rw [hg0, hb]
      omega
    have hg0c : g0 / L.block = T := by rw [hg0, hb]; omega
    obtain ⟨pcx, hlast⟩ := hex g0 hg0t hg0c
    obtain ⟨w, ws, hTO, hall⟩ :=
      issue_observed (gl := i.1) (kl := i.2) hpre hX ht hag hel hg0t hlast
      (by rw [hg0c]; exact hTc)
    have hfx := exit_get hlast
    have hhb := hall _ pcx hfx (by simp only; rw [hg0c]; exact hTc)
    have hTO' := hTO
    obtain ⟨o, mA, ho, ⟨pc', hiss⟩, hnot, -⟩ := hTO'.tensor
    have hspec : o.spec = s := by
      have h := Option.some.inj (hiss.symm.trans hel)
      simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at h
      exact h.2.2
    obtain ⟨o', ho', hw⟩ := PTX.AsyncObserved.all_writes hX.tensor hTO
    rw [ho] at ho'
    obtain rfl := Option.some.inj ho'
    exact ⟨o, ho, hspec, hnot, hw, _, pcx, hg0t, hg0c, hfx, notify_waits hTO hhb⟩
  -- the issue's CTAs: its loader's, and the leader CTA of its cluster
  have hsrc : ∀ i address s, X.TensorIssue i address s →
      i.1 / L.block < L.grid ∧ s.sharedBase.cta = i.1 / L.block ∧
        s.mbar.cta = 2 * (i.1 / L.block / 2) := by
    intro i address s ⟨pc, hel⟩
    have hg := Frame.lt_of_get hX hel
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hel (by simp)
    obtain ⟨l, b, j, -, -, hmb, ⟨base, cls, origin, hsp, -⟩, -⟩ :=
      ht.tensor_issue hg hel hσ rfl
    refine ⟨(Nat.div_lt_iff_lt_mul (by omega)).mpr hg, by rw [hsp]; rfl, by rw [hmb]; rfl⟩
  constructor
  · intro i address s hi hex
    obtain ⟨hgr, hcta, -⟩ := hsrc i address s hi
    rw [hcta] at hex ⊢
    obtain ⟨o, ho, hspec, hnot, hw, finish, pcx, hft, hfc, hfx, hchain⟩ :=
      key i address s _ hi hex hgr rfl
    subst hspec
    intro x y z hsl
    obtain ⟨slot, hslot⟩ := Option.isSome_iff_exists.mp hsl
    obtain ⟨v, hv⟩ := hw slot
    have hwp : X.AsyncPresent i (.write (.load x y z)) := ⟨o, slot, v, ho, hslot, hv⟩
    have hnp : X.AsyncPresent i (.notify .load) := ⟨o, ho, hnot⟩
    refine ⟨hwp, finish, pcx, hft, hfc, hfx, ?_⟩
    exact CompletedBefore.of_stage hchain hnp (.inr ⟨rfl, rfl, rfl, rfl, hwp, hnp⟩)
  · intro i address s hi hex
    obtain ⟨hgr, -, hmc⟩ := hsrc i address s hi
    rw [hmc] at hex ⊢
    obtain ⟨o, ho, -, hnot, -, finish, pcx, hft, hfc, hfx, hchain⟩ :=
      key i address s _ hi hex (by omega) (by omega)
    exact ⟨⟨o, ho, hnot⟩, finish, pcx, hft, hfc, hfx, hchain⟩

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
