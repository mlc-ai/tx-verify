-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.WqAll
public import Kernels.InklingRelDecode.Proof.Progress.WtAll
public import Kernels.InklingRelDecode.Proof.Progress.WuAll

@[expose] public section

/-!
# The key time along a thread's trace

Along a thread's trace the key time `kx` of its states does not fall, and it rises at every step
out of a synchronizing state (`kx_mono`), when the trace ends at a synchronizing state:

* a step out of a state that is not synchronizing keeps it (`kx_silent`);
* a step out of a synchronizing state raises the time (`time_lt_sy`): its event is counted (a
  failed poll is fired only at a poll, `wait_event_state`, which is not a synchronizing position),
  so `Wt.time_lt_of_next` applies, but at the dispatch, whose successor is a role's first state in
  the first round and the exit in the later one (`phase_inv`, `late_inv`, `dispatch_time`), and
  at the bad path, which no thread reaches (`not_bad`);
* a state is timed at most its key time (`time_le_kx`), below it when it is not synchronizing.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wq
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

section
variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
include hpre hX hS ht

/-- **The event of a synchronizing state is counted**: a failed poll is fired at a poll. -/
theorem counts_of_sy {g k : Nat} {e : Event} {s : TSt} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some s)) (hsy : tSy s) :
    e.counts = true := by
  cases hc : e.counts
  · exfalso
    have hk : ∃ l p ok acq sc, e.kind = .wait l p ok acq sc := by
      obtain ⟨pc, kd⟩ := e
      cases kd with
      | wait l p ok acq sc => exact ⟨l, p, ok, acq, sc, rfl⟩
      | _ => simp [Event.counts] at hc
    obtain ⟨w1, w2, w3, w4, w5, w6⟩ := PTX.Kernels.InklingRelDecode.Proof.Lk.wait_notSy
    rcases wait_event_stateW hpre hX hS ht hg he hk with
        ⟨d, hσ', hs⟩ | ⟨d, P, hσ', hs, -⟩ | ⟨d, P, hσ', hs, -⟩ | ⟨d, hσ', hs, -⟩
    · rw [hσ] at hσ'
      cases hσ'
      have hsy' : PTX.Kernels.InklingRelDecode.Proof.Lk.syAt d.site.pc 0 = true := hsy
      rcases hs with ⟨hs, -⟩ | hs <;> rw [hs] at hsy' <;> simp_all
    · rw [hσ] at hσ'
      cases hσ'
      have hsy' : PTX.Kernels.InklingRelDecode.Proof.Lk.wSy (.loader d P) = true := hsy
      obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
      simp only at hs
      subst hs
      simp [PTX.Kernels.InklingRelDecode.Proof.Lk.wSy,
        PTX.Kernels.InklingRelDecode.Proof.Lk.isLdRole, WComp.pc, WComp.sub, Loader.sub, w3] at hsy'
    · rw [hσ] at hσ'
      cases hσ'
      have hsy' : PTX.Kernels.InklingRelDecode.Proof.Lk.wSy (.mma d P) = true := hsy
      obtain ⟨site, i, n, tm, pro⟩ := d
      simp only at hs
      rcases hs with rfl | rfl <;>
        simp [PTX.Kernels.InklingRelDecode.Proof.Lk.wSy,
          PTX.Kernels.InklingRelDecode.Proof.Lk.isLdRole, WComp.pc, WComp.sub, w4, w5] at hsy'
    · rw [hσ] at hσ'
      cases hσ'
      have hsy' : PTX.Kernels.InklingRelDecode.Proof.Lk.syAt d.site.pc 0 = true := hsy
      rw [hs] at hsy'
      simp_all
  · rfl

/-- **A step out of a synchronizing state raises the time.** -/
theorem time_lt_sy (hR : RoleReads L X) {g k : Nat} {e : Event} {s t : TSt}
    (hg : g < L.threads) (he : (X.tr g)[k]? = some e) (hσ : St Q L X g k = some (some s))
    (hσ' : St Q L X g (k + 1) = some (some t)) (hsy : tSy s) : Wt.time g s < Wt.time g t := by
  have he' : X.get (g, k) = some e := he
  have hn := next_of_st_succ he hσ hσ'
  obtain ⟨u, ins, o, -, hI, -, -⟩ := Frame.fired_site hS hX he' hσ
  have hnb := Wt.not_bad hpre hX hS hR he' hσ
  by_cases hl : ∃ P, s = .w (.worker ⟨.ldRole, P⟩)
  · obtain ⟨P, rfl⟩ := hl
    obtain ⟨u', hu', rfl⟩ := next_w_inv hn
    obtain ⟨a, bs, hek, hcases, hph⟩ := Ledger.dispatch_role hu'
    obtain ⟨hk1, hk2⟩ := PTX.Kernels.InklingRelDecode.Proof.Lk.dispatch_time hu'
    have hk : k + 1 ≤ (X.tr g).length := by
      have := (List.getElem?_eq_some_iff.mp he).1
      omega
    obtain ⟨hto, tt, hrq, -, -, hkind1, hkind2, htt⟩ := phase_inv hpre hX hS hR (k + 1) _ hk hσ'
    have hlate := (Wu.late_inv hpre hX hS hR k _ (by omega) hσ).2 P .ldRole
      (Or.inr (Or.inr rfl)) rfl
    have hrq1 : rqN X g (k + 1) = rqN X g k := by
      unfold rqN
      rw [countP_take_succ _ he]
      obtain ⟨pc, kd⟩ := e
      simp only at hek
      subst hek
      simp [SetMaxNReg.isRequest]
    have htph : tPh (.w u') = (1, 1) := hph
    rw [htph] at hrq
    show Wt.workerT ⟨.ldRole, P⟩ < Wt.wcompT u'
    rcases hcases with ⟨-, hw2⟩ | ⟨i, -, -, hw1⟩ | ⟨i, -, -, hw0⟩
    · rw [hk2 hw2]
      simp only [Wt.workerT]
      split_ifs <;> wt_omega
    · have ht0 := hkind1 hw1
      subst ht0
      have hnl : ¬ Worker.late P := by
        rw [hlate]
        omega
      rw [hk1 hw1]
      simp only [Wt.workerT, hnl, ↓reduceIte]
      omega
    · exact absurd hw0 (by simpa [tTo] using hto)
  · have hc := counts_of_sy hpre hX hS ht hg he' hσ hsy
    exact Wt.time_lt_of_next hI (fun P h => hl ⟨P, h⟩) hnb hn hc

omit hpre in
/-- **A state is timed at most its key time, and below it when it is not synchronizing**, given a
synchronizing state at or after it. -/
theorem time_le_kx {g k k' : Nat} {s : TSt} (hg : g < L.threads) (hkk : k ≤ k')
    (hk' : k' ≤ (X.tr g).length) (hσ : St Q L X g k = some (some s))
    (hy : IsSy (kernelSkel Q L) X g k') :
    Wt.time g s ≤ kx L g s ∧ (¬ tSy s → Wt.time g s < kx L g s) := by
  by_cases hsy : tSy s
  · rw [kx_sy hsy]
    exact ⟨le_rfl, fun h => absurd hsy h⟩
  · -- the first synchronizing state after `k`
    have hex : ∃ j, k ≤ j ∧ j ≤ k' ∧ IsSy (kernelSkel Q L) X g j := ⟨k', hkk, le_rfl, hy⟩
    classical
    obtain ⟨j, hj, hmin⟩ : ∃ j, (k ≤ j ∧ j ≤ k' ∧ IsSy (kernelSkel Q L) X g j) ∧
        ∀ i, k ≤ i → i < j → ¬ IsSy (kernelSkel Q L) X g i := by
      have hs := Nat.find_spec hex
      exact ⟨Nat.find hex, hs, fun i h1 h2 hi =>
        Nat.find_min hex h2 ⟨h1, le_trans h2.le hs.2.1, hi⟩⟩
    obtain ⟨hkj0, hjk, sj, hsj, hsyj⟩ := hj
    have hkj : k < j := by
      rcases Nat.lt_or_ge k j with h | h
      · exact h
      · exfalso
        have : j = k := by omega
        rw [this, hσ] at hsj
        cases hsj
        exact hsy hsyj
    have hkey := chain (kernelSkel Q L) ht hg hσ j (by omega) (by omega) hmin sj hsj
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e :=
      ⟨_, List.getElem?_eq_getElem (show k < (X.tr g).length by omega)⟩
    obtain ⟨-, -, -, -, hI, -, -⟩ := Frame.fired_site hS hX (show X.get (g, k) = some e from he) hσ
    have hcls : s.isD ↔ sj.isD := by
      rw [cls_inv k s (by omega) hσ, cls_inv j sj (by omega) hsj]
    have := kx_lt (h := g) hsy hI hsyj hcls hkey.symm
    exact ⟨this.le, fun _ => this⟩

/-- **Along a trace that ends at a synchronizing state the key time does not fall, and it rises
after a synchronizing state.** -/
theorem kx_mono (hR : RoleReads L X) {g : Nat} (hg : g < L.threads) {d : TSt}
    (hd : St Q L X g (X.tr g).length = some (some d)) (hsyd : tSy d) :
    ∀ j k, j ≤ k → k ≤ (X.tr g).length → ∀ {s t : TSt}, St Q L X g j = some (some s) →
      St Q L X g k = some (some t) →
      kx L g s ≤ kx L g t ∧ (tSy s → j < k → kx L g s < kx L g t) := by
  intro j k hjk
  induction k, hjk using Nat.le_induction with
  | base =>
    intro _ s t hs ht'
    rw [hs] at ht'
    cases ht'
    exact ⟨le_rfl, fun _ h => absurd h (lt_irrefl _)⟩
  | succ k hjk ih =>
    intro hk s t hs ht'
    obtain ⟨u, hu⟩ := Frame.stateAt_live (C := code L Q) ht hg ht' (show k ≤ k + 1 by omega)
    have hu' : St Q L X g k = some (some u) := hu
    obtain ⟨h1, h2⟩ := ih (by omega) hs hu'
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hstep : kx L g u ≤ kx L g t ∧ (tSy u → kx L g u < kx L g t) := by
      by_cases hsu : tSy u
      · have hlt := time_lt_sy hpre hX hS ht hR hg he hu' ht' hsu
        have hle := (time_le_kx hX hS ht hg (k := k + 1) (k' := (X.tr g).length) hk le_rfl
          ht' ⟨d, hd, hsyd⟩).1
        rw [kx_sy hsu]
        exact ⟨by omega, fun _ => by omega⟩
      · have := kx_silent hsu (next_of_st_succ he hu' ht')
        exact ⟨this.ge, fun h => absurd h hsu⟩
    refine ⟨le_trans h1 hstep.1, fun hs' _ => ?_⟩
    rcases Nat.lt_or_ge j k with hjk' | hjk'
    · exact lt_of_lt_of_le (h2 hs' hjk') hstep.1
    · have hjk'' : j = k := by omega
      subst hjk''
      rw [hs] at hu'
      cases hu'
      exact lt_of_le_of_lt h1 (hstep.2 hs')

end

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wq
