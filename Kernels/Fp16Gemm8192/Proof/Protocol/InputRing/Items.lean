-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Joint
public import Lemmas.Protocol.PairTmaRing.Items

@[expose] public section

/-! # The items of an input ring slot

Slot `s` of cluster `c` as a pair TMA ring slot (`pslot`, `PairTmaRing.Slot`): two producers,
the loaders of the cluster's two CTAs (`producerOf`), each polling its CTA's empty barrier; two
consumers, the MMA threads of the leader CTA (`consumerOf`), polling the full barrier; three
copies of 16384 bytes per loader and use. The thread layer gives the slot's hypotheses
(`hyp`, `PairTmaRing.Hyp`): the sources of its records (`bar_source`), the leader loader's
arrivals and the loaders' issues within their budgets (`arrival_producer`, `issue_producer`),
the MMA threads' commit notifications within theirs (`notify_consumer`), the initialization
(`first_record`), the poll parities, the spins, the polls' acquire scope and the cluster. The
ring's facts are the generic ones of `pslot` under `hyp` (`PairTmaRing`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace InputRing

/-- Slot `s` of cluster `c` as a pair TMA ring slot. -/
def pslot (L : Launch) (X : Execution) (c : Nat) (s : Fin 4) : PairTmaRing.Slot 2 where
  full := (slot L c s).full 0
  empty := (slot L c s).empty
  prod := producerOf L X c s
  cons := consumerOf L X c s
  n := 3
  bytes := 16384

theorem pslot_tx (L : Launch) (X : Execution) (c : Nat) (s : Fin 4) :
    (pslot L X c s).tx = 98304 := by
  simp only [PairTmaRing.Slot.tx, pslot]

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The producers and consumers -/

theorem producerOf_inj (hpre : Pre P L mem0) {c : Nat} {s : Fin 4} {a a' : Fin 2}
    (h : producerOf L X c s a = producerOf L X c s a') : a = a' := by
  have h1 := producerOf_thread (X := X) hpre c s a
  have h2 := producerOf_thread (X := X) hpre c s a'
  rw [h] at h1
  simp only [producerThread, decide_eq_true_eq] at h1 h2
  exact Fin.ext (by omega)

theorem consumerOf_inj (hpre : Pre P L mem0) {c : Nat} {s : Fin 4} {b b' : Fin 2}
    (h : consumerOf L X c s b = consumerOf L X c s b') : b = b' := by
  have h1 := consumerOf_thread (X := X) hpre c s b
  have h2 := consumerOf_thread (X := X) hpre c s b'
  rw [h] at h1
  simp only [consumerThread, decide_eq_true_eq] at h1 h2
  exact Fin.ext (by omega)

/-- A tensor issue on slot `s`'s full barrier is a loader's of cluster `c`, after more successful
polls of its CTA's empty barrier than its earlier issues there over three. -/
theorem issue_facts (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {c : Nat}
    {s : Fin 4} {g k pc a : Nat} {sp : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩) (hm : sp.mbar = (slot L c s).full 0) :
    g < L.threads ∧ g / L.block / 2 = c ∧
      producerThread L c ⟨g / L.block % 2, Nat.mod_lt _ (by decide)⟩ g = true ∧
      ((X.tr g).take k).countP (issuesTo ((slot L c s).full 0)) + 1 ≤
        3 * okPolls ((slot L c s).empty ⟨g / L.block % 2, Nat.mod_lt _ (by decide)⟩)
          ((X.tr g).take k) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  obtain ⟨hby, hcta, -⟩ := (ht.ring_event hg he hσ).tensor a sp ⟨.input, s.val, true⟩ (2 * c) rfl
    hm s.isLt
  obtain ⟨l, rfl⟩ := hby
  have hc : g / L.block / 2 = c := by omega
  have hprod := loader_producer ht (idx_le he) hg hσ hc
  have hib := ht.issue_budget (b := ⟨.input, s.val, true⟩) (cta := 2 * c) hg he hσ
    (by simp only [issuesTo, hm, slot, decide_true]) s.isLt
  have hloc : (slot L c s).empty ⟨g / L.block % 2, Nat.mod_lt _ (by decide)⟩ =
      (Bar.partner ⟨.input, s.val, true⟩).loc L (g / L.block) := by
    simp only [slot, Bar.partner, Bool.not_true, Bar.loc, Loc.mk.injEq, and_true, true_and]
    omega
  refine ⟨hg, hc, hprod, ?_⟩
  rw [hloc]
  exact hib

/-- A tensor issue on slot `s`'s full barrier is producer `a`'s, for the rank `a` of its CTA. -/
theorem issue_producer (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {c : Nat}
    {s : Fin 4} {g k pc al : Nat} {sp : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩) (hm : sp.mbar = (slot L c s).full 0) :
    ∃ a : Fin 2, g = producerOf L X c s a ∧ g / L.block = 2 * c + a.val ∧
      ((X.tr g).take k).countP (issuesTo ((slot L c s).full 0)) + 1 ≤
        3 * okPolls ((slot L c s).empty a) ((X.tr g).take k) := by
  obtain ⟨-, hc, hprod, hib⟩ := issue_facts hX ht he hm
  obtain ⟨j', pc', p', acq', sc', -, he'⟩ := exists_okPoll (X := X) (g := g) (k := k)
    (m := (slot L c s).empty ⟨g / L.block % 2, Nat.mod_lt _ (by decide)⟩) (by omega)
  refine ⟨_, producerOf_eq hX ht hprod he', by simp only; omega, hib⟩

/-- An arrival on slot `s`'s full barrier is the leader loader's, with one unit expecting the
tile's bytes, after more successful polls of its CTA's empty barrier than its earlier arrivals. -/
theorem arrival_producer (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {c : Nat}
    {s : Fin 4} {r : Record Ref} (hr : r ∈ X.objects ((slot L c s).full 0)) {n tx : Nat}
    (ha : r.action = .arrive n tx) :
    n = 1 ∧ tx = 98304 ∧ ∃ j pc rel sc, r.id = .thread (producerOf L X c s 0, j) ∧
      X.get (producerOf L X c s 0, j) =
        some ⟨pc, .arrive ((slot L c s).full 0) 98304 1 rel sc⟩ ∧
      arrivals ((slot L c s).full 0) ((X.tr (producerOf L X c s 0)).take j) + 1 ≤
        okPolls ((slot L c s).empty 0) ((X.tr (producerOf L X c s 0)).take j) := by
  cases full_src hX ht hr with
  | init ha' => rw [ha] at ha'; cases ha'
  | poll _ _ ha' => rw [ha] at ha'; cases ha'
  | copy _ _ _ ha' => rw [ha] at ha'; cases ha'
  | notify _ _ _ _ _ hby => exact absurd hby (by simp [Bar.commitBy])
  | clc _ _ _ _ _ hby => exact absurd hby (by simp [Bar.clcBy])
  | @arrive g j pc rel sc d hid he ha' hσ hby hcta =>
    rw [ha] at ha'
    simp only [Action.arrive.injEq] at ha'
    obtain ⟨rfl, rfl⟩ := ha'
    obtain ⟨⟨l, rfl⟩, hlead⟩ := hby
    simp only [Bar.arriveCta, Bar.arriveLeader, ↓reduceIte] at hcta
    have hg := Frame.lt_of_get hX he
    have hprod := loader_producer ht (idx_le he) hg hσ (c := c) (by omega)
    have h0 : (⟨g / L.block % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = 0 := Fin.ext hlead
    rw [h0] at hprod
    have hab := ht.arrival_budget (b := ⟨.input, s.val, true⟩) hg he hσ rfl s.isLt
    have hloc : (Bar.gate ⟨.input, s.val, true⟩).loc L (g / L.block) = (slot L c s).empty 0 := by
      simp only [slot, Bar.gate, Fin.val_zero, Nat.add_zero]
      congr 1
      omega
    rw [hloc] at hab
    simp only [Bar.gateSlack] at hab
    obtain ⟨j', pc', p', acq', sc', -, he'⟩ := exists_okPoll (X := X) (g := g) (k := j)
      (m := (slot L c s).empty 0) (by omega)
    have hg' := producerOf_eq hX ht hprod he'
    subst hg'
    exact ⟨rfl, rfl, j, pc, rel, sc, hid, he, hab⟩

/-- A notification of consumer `b` to producer `a` on slot `s`'s empty barrier is of a commit of
`b`'s thread to the slot's empty barrier, notifying the producer's rank. -/
theorem notification_commit (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {c : Nat} {s : Fin 4} {a b : Fin 2} {x : Record Ref}
    (hx : x ∈ X.objects ((slot L c s).empty a)) (hn : (slot L c s).notification a b x = true) :
    ∃ jc pc sp, x.id = .async (consumerOf L X c s b, jc) (.tcNotify ⟨a.val, by omega⟩) ∧
      X.get (consumerOf L X c s b, jc) = some ⟨pc, .tc (.commit sp)⟩ ∧
      sp.mbar = (slot L c s).empty 0 ∧
      TcCommit.target sp ⟨a.val, by omega⟩ = some ((slot L c s).empty a) := by
  obtain ⟨i, rank, hid, hcons, hrank, -⟩ := notification_facts hn
  cases empty_src hX ht hx with
  | init _ _ hid' => rw [hid] at hid'; cases hid'
  | poll hid' => rw [hid] at hid'; cases hid'
  | arrive hid' => rw [hid] at hid'; cases hid'
  | copy hid' => rw [hid] at hid'; cases hid'
  | clc hid' => rw [hid] at hid'; cases hid'
  | @notify h k pc sp rank' dd hid' he htg ha' hσ hby hlead hrank' hcta hmb =>
    rw [hid] at hid'
    cases hid'
    simp only [consumerThread, decide_eq_true_eq] at hcons
    have hg := Frame.lt_of_get hX he
    have hcb := ht.commit_budget (b := ⟨.input, s.val, false⟩) hg he hσ rfl htg s.isLt
    have hfull : (Bar.partner ⟨.input, s.val, false⟩).loc L (h / L.block) =
        (slot L c s).full 0 := by
      simp only [slot, Bar.partner, Bool.not_false, hcons.1]
    rw [hfull] at hcb
    obtain ⟨j', pc', p', acq', sc', -, he'⟩ := exists_okPoll (X := X) (g := h) (k := k)
      (m := (slot L c s).full 0) (by omega)
    have hh := consumerOf_eq hX ht (by simpa [consumerThread] using hcons) he'
    have hr : rank = ⟨a.val, Nat.lt_of_lt_of_le a.isLt (by decide)⟩ := Fin.ext hrank
    rw [hr] at hid htg
    refine ⟨k, pc, sp, by rw [hid, ← hh], by rw [← hh]; exact he, ?_, ?_⟩
    · rw [hmb]; simp only [slot, hcons.1, Nat.add_zero, Fin.val_zero]
    · rw [htg]; simp only [slot, Bar.loc, hcta, hcons.1]

/-- An arrival on producer `a`'s empty barrier of slot `s` is a unit notification of consumer
`b`'s commit to the slot, after more successful full polls of `b`'s thread than its earlier
commits there. -/
theorem notify_consumer (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {c : Nat} {s : Fin 4} {a : Fin 2} {r : Record Ref}
    (hr : r ∈ X.objects ((slot L c s).empty a)) {n tx : Nat} (ha : r.action = .arrive n tx) :
    n = 1 ∧ tx = 0 ∧ ∃ (b : Fin 2) (j pc : Nat) (sp : TcCommit.Spec),
      r.id = .async (consumerOf L X c s b, j) (.tcNotify (PairTmaRing.rankOf a)) ∧
      X.get (consumerOf L X c s b, j) = some ⟨pc, .tc (.commit sp)⟩ ∧
      sp.mbar = (slot L c s).empty 0 ∧
      TcCommit.target sp (PairTmaRing.rankOf a) = some ((slot L c s).empty a) ∧
      ((X.tr (consumerOf L X c s b)).take j).countP (commitsTo ((slot L c s).empty 0)) + 1 ≤
        okPolls ((slot L c s).full 0) ((X.tr (consumerOf L X c s b)).take j) := by
  cases empty_src hX ht hr with
  | init ha' => rw [ha] at ha'; cases ha'
  | poll _ _ ha' => rw [ha] at ha'; cases ha'
  | arrive _ _ _ _ hby => exact absurd hby (by simp [Bar.arriveBy])
  | copy _ _ _ _ _ hby => exact absurd hby (by simp [Bar.copyBy])
  | clc _ _ _ _ _ hby => exact absurd hby (by simp [Bar.clcBy])
  | @notify g k pc sp rank d hid he htg ha' hσ hby hlead hrank hcta hmb =>
    rw [ha] at ha'
    simp only [Action.arrive.injEq] at ha'
    obtain ⟨rfl, rfl⟩ := ha'
    obtain ⟨mm, rfl⟩ := hby
    have hg := Frame.lt_of_get hX he
    have hw := ht.role_warp hg (idx_le he) hσ
    simp only [roleWarp] at hw
    have ha2 := a.isLt
    let b : Fin 2 := ⟨g % L.block / 32 - 8, by omega⟩
    have hcons : consumerThread L c b g = true := by
      simp only [consumerThread, decide_eq_true_eq]
      refine ⟨by omega, ?_⟩
      show g % L.block / 32 = 8 + (g % L.block / 32 - 8)
      omega
    have hcb := ht.commit_budget (b := ⟨.input, s.val, false⟩) hg he hσ rfl htg s.isLt
    have hfull : (Bar.partner ⟨.input, s.val, false⟩).loc L (g / L.block) =
        (slot L c s).full 0 := by
      simp only [slot, Bar.partner, Bool.not_false, Bar.loc, Loc.mk.injEq, and_true, true_and]
      omega
    rw [hfull] at hcb
    obtain ⟨j', pc', p', acq', sc', -, he'⟩ := exists_okPoll (X := X) (g := g) (k := k)
      (m := (slot L c s).full 0) (by omega)
    have hgb := consumerOf_eq hX ht hcons he'
    have hrk : rank = PairTmaRing.rankOf a := Fin.ext (by simp only [PairTmaRing.rankOf]; omega)
    subst hrk
    have hmb' : sp.mbar = (slot L c s).empty 0 := by
      rw [hmb]; simp only [slot, Bar.loc, Fin.val_zero, Nat.add_zero, Loc.mk.injEq, and_true,
        true_and]; omega
    have htg' : TcCommit.target sp (PairTmaRing.rankOf a) = some ((slot L c s).empty a) := by
      rw [htg]; rfl
    rw [hmb'] at hcb
    rw [hgb] at hid he hcb
    exact ⟨rfl, rfl, b, k, pc, sp, hid, he, hmb', htg', hcb⟩

/-! ### The slot's hypotheses -/

/-- **The hypotheses of slot `s` of cluster `c`.** -/
theorem hyp (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    (c : Nat) (s : Fin 4) : PairTmaRing.Hyp L kernel Prod X (pslot L X c s) where
  n_pos := Nat.zero_lt_succ _
  bytes_pos := Nat.zero_lt_succ _
  nc_pos := Nat.zero_lt_succ _
  tx_le := by rw [pslot_tx]; decide
  prod_inj _ _ h := producerOf_inj hpre h
  cons_inj _ _ h := consumerOf_inj hpre h
  full_src r hr := by
    cases full_src hX ht hr with
    | init ha => exact .init ha
    | poll hid he ha => exact .poll hid he ha
    | arrive _ _ ha =>
      obtain ⟨-, -, j, pc, rel, sc, hid, he, hb⟩ := arrival_producer hX ht hr ha
      rw [← pslot_tx L X c s] at he
      exact .arrive hid he (by rw [ha, pslot_tx]; rfl) hb
    | copy hid he hm ha => exact .copy hid he hm ha
    | notify _ _ _ _ _ hby => exact absurd hby (by simp [Bar.commitBy])
    | clc _ _ _ _ _ hby => exact absurd hby (by simp [Bar.clcBy])
  empty_src a r hr := by
    cases empty_src hX ht hr with
    | init ha => exact .init ha
    | poll hid he ha => exact .poll hid he ha
    | notify _ _ _ ha =>
      obtain ⟨-, -, b, j, pc, sp, hid, he, hm, htg, hb⟩ := notify_consumer hX ht hr ha
      exact .notify hid he hm htg ha hb
    | arrive _ _ _ _ hby => exact absurd hby (by simp [Bar.arriveBy])
    | copy _ _ _ _ _ hby => exact absurd hby (by simp [Bar.copyBy])
    | clc _ _ _ _ _ hby => exact absurd hby (by simp [Bar.clcBy])
  issue he hm := by
    obtain ⟨a, hg, -, hib⟩ := issue_producer hX ht he hm
    exact ⟨a, hg, hib⟩
  full_init r hr := by
    obtain ⟨r0, h0, hid0, ha0, hf0⟩ :=
      first_record hpre hX ht (b := ⟨.input, s.val, true⟩) s.isLt hr
    refine ⟨r0, h0, ha0, hf0, fun q hq ⟨n, ha⟩ => hX.record_eq hq (List.mem_of_getElem? h0) ?_⟩
    rw [(init_source hX ht (b := ⟨.input, s.val, true⟩) s.isLt hq ha).1, hid0]
  empty_init a r hr := by
    obtain ⟨r0, h0, hid0, ha0, hf0⟩ :=
      first_record hpre hX ht (b := ⟨.input, s.val, false⟩) s.isLt hr
    refine ⟨r0, h0, ha0, hf0, fun q hq ⟨n, ha⟩ => hX.record_eq hq (List.mem_of_getElem? h0) ?_⟩
    rw [(init_source hX ht (b := ⟨.input, s.val, false⟩) s.isLt hq ha).1, hid0]
  full_noInval := objects_noInval hX ht _
  empty_noInval _ := objects_noInval hX ht _
  full_parity he := by
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    exact ht.poll_parity (b := ⟨.input, s.val, true⟩) (cta := 2 * c) (Frame.lt_of_get hX he) he
      hσ rfl s.isLt
  empty_parity {a} _ _ _ _ _ _ he := by
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    exact ht.poll_parity (b := ⟨.input, s.val, false⟩) (cta := 2 * c + a.val)
      (Frame.lt_of_get hX he) he hσ rfl s.isLt
  spins := by
    intro w pc m q acq sc he
    obtain ⟨g, k⟩ := w
    exact ht.wait_spins (Frame.lt_of_get hX he) he
  full_acq he := by
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    exact (ht.sync_flags (Frame.lt_of_get hX he) he hσ).1 _ _ _ _ _ rfl
  empty_acq he := by
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    exact (ht.sync_flags (Frame.lt_of_get hX he) he hσ).1 _ _ _ _ _ rfl
  cluster a b := by
    have h1 := producerOf_thread (X := X) hpre c s a
    have h2 := consumerOf_thread (X := X) hpre c s b
    simp only [producerThread, consumerThread, decide_eq_true_eq] at h1 h2
    simp only [pslot, clusterOfCta_eq hpre, h1.1, h2.1]
    omega

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
