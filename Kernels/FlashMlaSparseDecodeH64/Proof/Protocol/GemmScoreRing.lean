-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmActualObjects
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingScoreReleaseCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxQkParity
public import Lemmas.Protocol.PairTmaRing.Attribution

@[expose] public section

/-! # The QK and probability handoff ring -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing

open PTX AsyncCopy MBarrier PTX.Flow PTX.MbarRing MachineTracking

noncomputable section

set_option maxRecDepth 4096

abbrev qk (L : Launch) (cta : Nat) (slot : Fin 2) : Loc :=
  Object.qkDone.loc L cta slot

abbrev score (L : Launch) (cta : Nat) (slot : Fin 2) : Loc :=
  Object.soReady.loc L cta slot

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Before issuing QK for this use the MMA lane observed the previous uses' probabilities. -/
private theorem guard_qk_issue_of_state {cta issuer n i tag : Nat} {slot : Fin 2}
    {sp : TcCommit.Spec} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) {d : Wg1Mma.D} (hc : ctaOf L issuer = cta)
    (hb : d.i % 2 = slot.val) (hd : d.site = .qkCommit)
    (hst : Frame.stateAt (Machine.code P L) X issuer i = some (some (.mma d)))
    (he : X.get (issuer, i) = some ⟨tag, .tc (.commit sp)⟩) (h1 : 1 ≤ n)
    (hn : n ≤ ((X.tr issuer).take i).countP (commitsTo (qk L cta slot))) :
    Resumes kernel X (issuer, Poll.nth X (score L cta slot) issuer (n - 1))
      (issuer, i) := by
  have hg := Frame.lt_of_get hX he
  have trace := (hs issuer hg).produces (hX.thr issuer hg)
  have hp := Wg1MmaGemmTrace.composed_count_here hpre hg .score trace hst hb
  have ha := Wg1MmaGemmTrace.composed_count_here hpre hg .qk trace hst hb
  simp only [hd, Wg1MmaGemmTrace.completed, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at ha hp
  change PTX.Flow.okPolls (score L (ctaOf L issuer) slot) ((X.tr issuer).take i) = _ at hp
  change ((X.tr issuer).take i).countP (commitsTo (qk L (ctaOf L issuer) slot)) = _ at ha
  rw [hc] at hp ha
  have hcount : n - 1 + 1 ≤ PTX.Flow.okPolls (score L cta slot) ((X.tr issuer).take i) := by
    omega
  exact Poll.guard (fun _ _ _ _ _ _ hw => RingSpins.successful_poll hX hw)
    (PTX.len_of_get he) hcount

/-- Before issuing QK for this use the MMA lane observed the previous uses' probabilities. -/
theorem guard_qk_issue {cta issuer n i tag : Nat} {slot : Fin 2} {sp : TcCommit.Spec}
    {rank : Fin 16} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (issuer, i) = some ⟨tag, .tc (.commit sp)⟩)
    (htgt : TcCommit.target sp rank = some (qk L cta slot)) (h1 : 1 ≤ n)
    (hn : n ≤ ((X.tr issuer).take i).countP (commitsTo (qk L cta slot))) :
    Resumes kernel X (issuer, Poll.nth X (score L cta slot) issuer (n - 1))
      (issuer, i) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, hc, d, hb, hd, hst⟩ := notification hpre hX (hs issuer hg) ht he rfl htgt
  have hd : d.site = .qkCommit := by
    rcases hd with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · cases h
  exact guard_qk_issue_of_state hpre hX hs hc hb hd hst he h1 hn

/-- Before issuing QK for this use the MMA lane observed the previous uses' probabilities. -/
theorem guard_actual_qk_issue {cta issuer n i tag : Nat} {slot : Fin 2} {sp : TcCommit.Spec}
    {rank : Fin 16} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (issuer, i) = some ⟨tag, .tc (.commit sp)⟩)
    (htgt : TcCommit.target sp rank = some (qk L cta slot)) (h1 : 1 ≤ n)
    (hn : n ≤ ((X.tr issuer).take i).countP (commitsTo (qk L cta slot))) :
    Resumes kernel X (issuer, Poll.nth X (score L cta slot) issuer (n - 1))
      (issuer, i) := by
  obtain ⟨_, hc, d, hb, hd, hst⟩ := actual_notification hpre hX hs he rfl htgt
  have hd : d.site = .qkCommit := by
    rcases hd with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · cases h
  exact guard_qk_issue_of_state hpre hX (fun g hg => (hs g hg).machine) hc hb hd hst he h1 hn

/-- The QK guard for a notification already present in the counted ring. -/
theorem guard_qk {L : Launch} {X : Execution}
    {cta issuer n : Nat} {slot : Fin 2} {x : Fin 1 × Nat} {selected : Nat → Prop}
    (F : Notify.Obj X (qk L cta slot) issuer (qk L cta slot) 0 selected)
    (guard : ∀ {i tag : Nat} {sp : TcCommit.Spec} {rank : Fin 16},
      X.get (issuer, i) = some ⟨tag, .tc (.commit sp)⟩ →
      TcCommit.target sp rank = some (qk L cta slot) →
      1 ≤ n → n ≤ ((X.tr issuer).take i).countP (commitsTo (qk L cta slot)) →
      Resumes kernel X (issuer, Poll.nth X (score L cta slot) issuer (n - 1)) (issuer, i))
    (hx : x ∈ Notify.S X (qk L cta slot) issuer (qk L cta slot)) (h1 : 1 ≤ n) (hn : n ≤ x.2) :
    Resumes kernel X (issuer, Poll.nth X (score L cta slot) issuer (n - 1))
      (issuer, Notify.cm X issuer (qk L cta slot) x.2) := by
  obtain ⟨_, _, _, he, _, htgt, hu⟩ := F.S_rec hx
  exact guard he htgt h1 (hu.symm ▸ hn)

/-- A QK commit issues this counted QK-completion notification. -/
theorem issue_qk {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta issuer : Nat} {slot : Fin 2} {x : Fin 1 × Nat} {selected : Nat → Prop}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (F : Notify.Obj X (qk L cta slot) issuer (qk L cta slot) 0 selected)
    (hx : x ∈ Notify.S X (qk L cta slot) issuer (qk L cta slot)) :
    Relation.ReflTransGen (DepStep L kernel X)
      (.thread (issuer, Notify.cm X issuer (qk L cta slot) x.2), false)
      (Notify.it X (qk L cta slot) issuer (qk L cta slot) x.2, false) := by
  obtain ⟨⟨k, r, hr, hid, _, _⟩, _, sp, he, _, htarget, _⟩ := F.S_rec hx
  have hp := object_record_present hX.tma (List.mem_of_getElem? hr)
  rw [hid] at hp
  exact .single (.inr (.inl ⟨rfl, rfl, _, _, rfl, rfl, ⟨_, he⟩, hp, trivial⟩))

/-- An actual score-ready arrival follows its own and all earlier QK acquires. -/
theorem guard_score_arrival {cta i j tag : Nat} {slot : Fin 2} {lane : Fin 128} {scope : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (softmax L cta lane, i) = some ⟨tag, .arrive (score L cta slot) 0 1 true scope⟩)
    (hj : j ≤ PTX.Flow.arrivals (score L cta slot) ((X.tr (softmax L cta lane)).take i)) :
    Resumes kernel X (softmax L cta lane, Poll.nth X (qk L cta slot) (softmax L cta lane) j)
      (softmax L cta lane, i) := by
  let g := softmax L cta lane
  have hg := Frame.lt_of_get hX he
  obtain ⟨⟨hc, d, hb, hd, hst⟩, _, _, _, _⟩ := arrival hpre hX (hs g hg) ht he rfl
  obtain ⟨ha, hp⟩ := Wg0GemmTrace.composed_score_counts hpre
    ((hs g hg).produces (hX.thr g hg)) hst hd
  rw [hc, hb] at ha hp
  change PTX.Flow.arrivals (score L cta slot) ((X.tr g).take i) = d.block / 2 at ha
  change PTX.Flow.okPolls (qk L cta slot) ((X.tr g).take i) = d.block / 2 + 1 at hp
  rw [ha] at hj
  have hcount : j + 1 ≤ PTX.Flow.okPolls (qk L cta slot) ((X.tr g).take i) := by
    omega
  exact Poll.guard (fun _ _ _ _ _ _ hw => RingSpins.successful_poll hX hw)
    (PTX.len_of_get he) hcount

/-- An actual score-ready arrival follows its own and all earlier QK acquires. -/
theorem guard_actual_score_arrival {cta i j tag : Nat} {slot : Fin 2} {lane : Fin 128}
    {scope : MbarScope} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (softmax L cta lane, i) = some ⟨tag, .arrive (score L cta slot) 0 1 true scope⟩)
    (hj : j ≤ PTX.Flow.arrivals (score L cta slot) ((X.tr (softmax L cta lane)).take i)) :
    Resumes kernel X (softmax L cta lane, Poll.nth X (qk L cta slot) (softmax L cta lane) j)
      (softmax L cta lane, i) := by
  obtain ⟨_, _, _, _, hScope, _⟩ := actual_gemm_arrival hpre hX hs he rfl
  subst scope
  have hp := qk_successes_before_actual_score hpre hX hs he rfl
  have hcount : j + 1 ≤ PTX.Flow.okPolls (qk L cta slot) ((X.tr (softmax L cta lane)).take i) :=
    Nat.le_trans (Nat.add_le_add_right hj 1) hp
  exact Poll.guard (fun _ _ _ _ _ _ hw => RingSpins.successful_poll hX hw)
    (PTX.len_of_get he) hcount

/-- Probability publication follows its own QK acquire and all earlier QK acquires in the slot. -/
theorem guard_score {L : Launch} {X : Execution}
    {cta j : Nat} {slot : Fin 2} {y : Fin 128 × Nat}
    (E : Unit.History X (score L cta slot) 128 (softmax L cta))
    (guard : ∀ {lane : Fin 128} {i tag : Nat} {scope : MbarScope},
      X.get (softmax L cta lane, i) = some ⟨tag, .arrive (score L cta slot) 0 1 true scope⟩ →
      j ≤ PTX.Flow.arrivals (score L cta slot) ((X.tr (softmax L cta lane)).take i) →
      Resumes kernel X (softmax L cta lane, Poll.nth X (qk L cta slot) (softmax L cta lane) j)
        (softmax L cta lane, i))
    (hy : y ∈ Unit.S X (score L cta slot) (softmax L cta)) (hj : j ≤ y.2) :
    Resumes kernel X (softmax L cta y.1, Poll.nth X (qk L cta slot) (softmax L cta y.1) j)
      (Unit.it X (score L cta slot) (softmax L cta) y.1 y.2) := by
  obtain ⟨_, ⟨_, _, he⟩, hu⟩ := E.S_rec hy
  apply guard he
  exact hu.symm ▸ hj

/-- Each slot rings once per QK notification and the subsequent 128 probability publications. -/
def scoreRingOfHistories {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta issuer : Nat} {slot : Fin 2} {selected : Nat → Prop}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (F : Notify.Obj X (qk L cta slot) issuer (qk L cta slot) 0 selected)
    (E : Unit.History X (score L cta slot) 128 (softmax L cta))
    (hF : ∀ lane : Fin 128, selected (softmax L cta lane))
    (hE : SelectedAlternates (objectThreadSelected issuer) (X.objects (score L cta slot)) 0)
    (guardQk : ∀ {i tag : Nat} {sp : TcCommit.Spec} {rank : Fin 16},
      X.get (issuer, i) = some ⟨tag, .tc (.commit sp)⟩ →
      TcCommit.target sp rank = some (qk L cta slot) →
      ∀ {n}, 1 ≤ n → n ≤ ((X.tr issuer).take i).countP (commitsTo (qk L cta slot)) →
        Resumes kernel X (issuer, Poll.nth X (score L cta slot) issuer (n - 1)) (issuer, i))
    (guardScore : ∀ {lane : Fin 128} {i tag : Nat} {scope : MbarScope},
      X.get (softmax L cta lane, i) = some ⟨tag, .arrive (score L cta slot) 0 1 true scope⟩ →
      ∀ {j}, j ≤ PTX.Flow.arrivals (score L cta slot) ((X.tr (softmax L cta lane)).take i) →
        Resumes kernel X (softmax L cta lane, Poll.nth X (qk L cta slot) (softmax L cta lane) j)
          (softmax L cta lane, i)) :
    Items.Ring L kernel Assumptions.all X 1 128 1 (fun _ => 1) where
  owner _ := 0
  ownF _ _ := 0
  wE _ n := (issuer, Poll.nth X (score L cta slot) issuer (n - 1))
  opF _ _ u := (issuer, Notify.cm X issuer (qk L cta slot) u)
  itF _ _ u := Notify.it X (qk L cta slot) issuer (qk L cta slot) u
  wF b j := (softmax L cta b, Poll.nth X (qk L cta slot) (softmax L cta b) j)
  cm := Unit.it X (score L cta slot) (softmax L cta)
  note b _ u := .thread (Unit.it X (score L cta slot) (softmax L cta) b u)
  SF _ := Notify.S X (qk L cta slot) issuer (qk L cta slot)
  phF _ := Notify.ph X (qk L cta slot) issuer (qk L cta slot)
  SE _ := Unit.S X (score L cta slot) (softmax L cta)
  phE _ := Unit.ph X (score L cta slot) (softmax L cta)
  oF b n := Unit.obsOf X (qk L cta slot) (softmax L cta b) n
  oE _ n := Unit.obsOf X (score L cta slot) issuer (n - 1)
  cover _ a := ⟨0, Subsingleton.elim _ _⟩
  guardP _ _ hx _ h1 hn := guard_qk F (fun he ht => guardQk he ht) hx h1 hn
  issueF _ _ hx := issue_qk hX F hx
  guardM _ _ hy _ hj := guard_score E (fun he => guardScore he) hy hj
  issue _ _ _ := .refl
  obsF b _ hw _ hx hph :=
    F.observed hX (Nat.zero_le _) (Poll.nth_present.mp hw) hx hph (hF b)
  obsE _ _ _ hw _ hy hph :=
    E.observed hX (by decide) hE (Nat.zero_le _) (Poll.nth_present.mp hw) hy hph
  fullF b _ hw :=
    F.card_phase hX (Nat.zero_le _) (Poll.nth_present.mp hw) (hF b)
  fullE _ _ _ hw :=
    E.card_phase hX (by decide) hE (Nat.zero_le _) (Poll.nth_present.mp hw)
  ltF b _ _ hj hw := by
    have hcount := Poll.nth_present.mp hw
    exact ⟨Poll.nth_present.mpr (Nat.lt_trans hj hcount),
      Poll.observed_lt hX (by decide) (F.pclean hX) F.noInval (F.alt hX _ (hF b))
        (Nat.zero_le _) hj hcount⟩
  ltE _ n n' hn hj hw := by
    have hcount := Poll.nth_present.mp hw
    have hlt : n - 1 < n' - 1 := by omega
    exact ⟨Poll.nth_present.mpr (Nat.lt_trans hlt hcount),
      Poll.observed_lt hX (by decide) (E.pclean hX) E.noInval hE
        (Nat.zero_le _) hlt hcount⟩

/-- The QK and probability ring of a fully tracked execution. -/
def scoreRing {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta issuer : Nat} {slot : Fin 2}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hmma : MmaIssuer P L X cta issuer) :
    Items.Ring L kernel Assumptions.all X 1 128 1 (fun _ => 1) :=
  let E := score_obj (slot := slot) hpre hX hs ht (cta := cta)
  scoreRingOfHistories hX (qk_obj hpre hX hs ht hmma) E.history
    (fun _ => trivial) (E.alt hX issuer)
    (fun he htgt => guard_qk_issue hpre hX hs ht he htgt)
    (fun he => guard_score_arrival hpre hX hs ht he)

/-- The handoffs between the elected MMA lane and softmax lanes follow from the actual history. -/
def actualScoreRing {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta issuer : Nat} {slot : Fin 2}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : MmaIssuer P L X cta issuer) (hw : warpOf L issuer = 4) :
    Items.Ring L kernel Assumptions.all X 1 128 1 (fun _ => 1) :=
  scoreRingOfHistories hX
    (actual_qk_obj_of_parity (slot := slot) hpre hX hs hmma
      (selected := fun _ => True) (by
        intro g i tag p acq sc _ he
        exact actual_qk_alternates hpre hX hs he))
    (actual_score_history hpre hX hs) (fun _ => trivial)
    (actual_score_alternates hpre hX hs hw)
    (fun he htgt => guard_actual_qk_issue hpre hX hs he htgt)
    (fun he => guard_actual_score_arrival hpre hX hs he)

/-- A CTA's elected issuer can always be chosen inside warp four. -/
theorem exists_issuer_in_warp {cta : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) :
    ∃ issuer, MmaIssuer P L X cta issuer ∧ warpOf L issuer = 4 := by
  obtain ⟨leader, hLeader⟩ := Wg1MmaLeader.cta_issuer (cta := cta) hpre hX
    (fun g hg => (hs g hg).machine)
  refine ⟨cta * L.block + 128 + leader.val, hLeader, ?_⟩
  have := leader.isLt
  simp only [warpOf, tidOf_eq hpre, hpre.block]
  omega

/-- The softmax poll observes the QK completion of the same block. -/
theorem acquire_qk {cta issuer j tag parity u : Nat} {slot : Fin 2} {sc : MbarScope}
    {lane : Fin 128} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hmma : MmaIssuer P L X cta issuer)
    (he : X.get (softmax L cta lane, j) = some ⟨tag, .wait (qk L cta slot) parity true true sc⟩)
    (hu : PTX.Flow.okPolls (qk L cta slot) ((X.tr (softmax L cta lane)).take j) = u) :
    Witness L X (Notify.it X (qk L cta slot) issuer (qk L cta slot) u)
      (softmax L cta lane, j) := by
  let R := scoreRing (slot := slot) hpre hX hs ht hmma
  have hj : Poll.nth X (qk L cta slot) (softmax L cta lane) u = j := by
    rw [← hu]
    exact Poll.nth_eq he
  have hp : X.RefPresent (.thread (R.wF lane u)) := by
    change X.RefPresent (.thread (softmax L cta lane, Poll.nth X (qk L cta slot)
      (softmax L cta lane) u))
    rw [hj]
    exact ⟨_, he⟩
  have hw := (R.observes_full hX.depAcyclic hp 0).2
  change Witness L X (Notify.it X (qk L cta slot) issuer (qk L cta slot) u)
    (softmax L cta lane, Poll.nth X (qk L cta slot) (softmax L cta lane) u) at hw
  rwa [hj] at hw


end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing
