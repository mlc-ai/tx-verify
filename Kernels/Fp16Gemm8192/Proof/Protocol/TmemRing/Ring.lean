-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.Records

@[expose] public section

/-! # The accumulator ring as a ring of items

Buffer `j` of cluster `c` is an `MbarRing.Items.Ring` with one producer, 256 consumers, two
full objects and one kind of item per full object. The producer's operation of use `s` is its
commit to the buffer's full barrier with `s` earlier ones (`commitAt`); the item of full
barrier `k` is that commit's notification of rank `k` (`notifyRef`), reached from the commit
by its issue. Consumer `b`'s operation of use `t` is its arrival on the empty barrier with `t`
earlier ones (`arriveAt`), which is itself its notification. The polls are the threads'
successful polls by count (`prodPoll`, `consPoll`). The counted items are the fault-free
records (`fullItems`, `emptyItems`), and the object facts are read from each barrier's own
history. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace TmemRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The position of the producer's commit to the buffer's full barrier with `s` earlier ones. -/
def commitAt (L : Launch) (X : Execution) (c : Nat) (j : Fin 2) (s : Nat) : Nat :=
  nthEv X (commitsTo ((slot L c j).full 0)) (producer L X c j) s

/-- The position of consumer `b`'s arrival on the empty barrier with `t` earlier ones. -/
def arriveAt (L : Launch) (X : Execution) (c : Nat) (j : Fin 2) (b : Fin 256) (t : Nat) : Nat :=
  nthEv X (arrivesOn ((slot L c j).empty 0)) (consumerOf L c j b) t

/-- The producer's successful empty poll with `n` earlier ones. -/
def prodPoll (L : Launch) (X : Execution) (c : Nat) (j : Fin 2) (n : Nat) : EvId :=
  (producer L X c j, MbarRing.Poll.nth X ((slot L c j).empty 0) (producer L X c j) n)

/-- Consumer `b`'s successful full poll with `t` earlier ones. -/
def consPoll (L : Launch) (X : Execution) (c : Nat) (j : Fin 2) (b : Fin 256) (t : Nat) : EvId :=
  (consumerOf L c j b,
    MbarRing.Poll.nth X ((slot L c j).full ((slot L c j).owner b)) (consumerOf L c j b) t)

/-- The notification of rank `k` of the producer's commit of use `s`. -/
def notifyRef (L : Launch) (X : Execution) (c : Nat) (j k : Fin 2) (s : Nat) : Ref :=
  .async (producer L X c j, commitAt L X c j s) (.tcNotify ⟨k.val, by omega⟩)

/-- Consumer `b`'s arrival of use `t`. -/
def arriveRef (L : Launch) (X : Execution) (c : Nat) (j : Fin 2) (b : Fin 256) (t : Nat) : Ref :=
  .thread (consumerOf L c j b, arriveAt L X c j b t)

open Classical in
/-- The counted notifications of full barrier `k`: those with a fault-free record. -/
def fullItems (L : Launch) (X : Execution) (c : Nat) (j k : Fin 2) : Finset (Fin 1 × Nat) :=
  (Finset.univ ×ˢ Finset.range ((X.tr (producer L X c j)).length + 1)).filter
    (fun x => ∃ r ∈ X.objects ((slot L c j).full k), r.id = notifyRef L X c j k x.2 ∧
      r.fault = none)

/-- A bound on the consumers' trace lengths. -/
@[irreducible] def consBound (L : Launch) (X : Execution) (c : Nat) (j : Fin 2) : Nat :=
  Finset.univ.sup (fun b : Fin 256 => (X.tr (consumerOf L c j b)).length)

theorem len_le_consBound (L : Launch) (X : Execution) (c : Nat) (j : Fin 2) (b : Fin 256) :
    (X.tr (consumerOf L c j b)).length ≤ consBound L X c j := by
  unfold consBound
  exact Finset.le_sup (f := fun b : Fin 256 => (X.tr (consumerOf L c j b)).length)
    (Finset.mem_univ b)

/-- The consumers. -/
@[irreducible] def allCons : Finset (Fin 256) := Finset.univ

theorem mem_allCons (b : Fin 256) : b ∈ allCons := by
  unfold allCons
  exact Finset.mem_univ b

theorem card_allCons : allCons.card = 256 := by
  unfold allCons
  rw [Finset.card_univ, Fintype.card_fin]

open Classical in
/-- The counted arrivals of the empty barrier: those with a fault-free record. -/
def emptyItems (L : Launch) (X : Execution) (c : Nat) (j : Fin 2) : Finset (Fin 256 × Nat) :=
  (allCons ×ˢ Finset.range (consBound L X c j + 1)).filter
    (fun y => ∃ r ∈ X.objects ((slot L c j).empty 0), r.id = arriveRef L X c j y.1 y.2 ∧
      r.fault = none)

theorem fullItems_mem {c : Nat} {j k : Fin 2} {x : Fin 1 × Nat} :
    x ∈ fullItems L X c j k → ∃ r ∈ X.objects ((slot L c j).full k),
      r.id = notifyRef L X c j k x.2 ∧ r.fault = none := by
  classical
  intro hx
  exact (Finset.mem_filter.mp hx).2

theorem emptyItems_mem {c : Nat} {j : Fin 2} {y : Fin 256 × Nat} :
    y ∈ emptyItems L X c j → ∃ r ∈ X.objects ((slot L c j).empty 0),
      r.id = arriveRef L X c j y.1 y.2 ∧ r.fault = none := by
  classical
  intro hy
  exact (Finset.mem_filter.mp hy).2

/-- A notification's action is a unit arrival without bytes. -/
theorem notify_action (hX : Consistent L kernel Prod mem0 X) {m : Loc} {r : Record Ref}
    (hr : r ∈ X.objects m) {i : EvId} {rank : Fin 16} (hid : r.id = .async i (.tcNotify rank)) :
    r.action = .arrive 1 0 := by
  have h := ((hX.tma.2.2.1 m).2.1 r hr).1
  rw [hid] at h
  simp only [objectAction] at h
  cases hg : X.get i with
  | none => simp [hg] at h
  | some ev =>
    obtain ⟨pc, k⟩ := ev
    cases k with
    | tc k' =>
      cases k' with
      | commit s =>
        by_cases hc : TcCommit.target s rank = some m ∧ rank ∈ X.tcNotified i
        · simp only [hg, hc, and_self, ↓reduceIte, Option.some.injEq] at h
          exact h.symm
        · simp [hg, hc] at h
      | _ => simp [hg] at h
    | _ => simp [hg] at h

/-- A fault-free arrival on full barrier `k` is a counted notification. -/
theorem fullItems_of_record (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j k : Fin 2} {r : Record Ref}
    (hr : r ∈ X.objects ((slot L c j).full k)) (hf : r.fault = none)
    (ha : r.action = .arrive 1 0) :
    ∃ x ∈ fullItems L X c j k, r.id = notifyRef L X c j k x.2 := by
  classical
  obtain ⟨jc, pc, sp, hid, he, hmb, -, -⟩ := notify_record hpre hX ht hr ha
  have hp : commitsTo ((slot L c j).full 0) ⟨pc, .tc (.commit sp)⟩ = true := by
    simp [commitsTo, hmb]
  set s := ((X.tr (producer L X c j)).take jc).countP (commitsTo ((slot L c j).full 0))
  have hs : commitAt L X c j s = jc := nthEv_eq he hp
  have hid' : r.id = notifyRef L X c j k s := by rw [hid, notifyRef, hs]
  refine ⟨(0, s), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,
    Finset.mem_range.mpr ?_⟩, r, hr, hid', hf⟩, hid'⟩
  have h1 : s ≤ ((X.tr (producer L X c j)).take jc).length := List.countP_le_length
  have h2 := len_of_get he
  simp only [List.length_take] at h1
  change s < _
  omega

/-- A counted notification is of the producer's commit of its use, which notified it. -/
theorem fullItems_commit (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j k : Fin 2} {x : Fin 1 × Nat}
    (hx : x ∈ fullItems L X c j k) :
    ∃ pc sp, X.get (producer L X c j, commitAt L X c j x.2) = some ⟨pc, .tc (.commit sp)⟩ ∧
      TcCommit.target sp ⟨k.val, by omega⟩ = some ((slot L c j).full k) ∧
      (⟨k.val, by omega⟩ : Fin 16) ∈ X.tcNotified (producer L X c j, commitAt L X c j x.2) ∧
      ((X.tr (producer L X c j)).take (commitAt L X c j x.2)).countP
        (commitsTo ((slot L c j).full 0)) = x.2 := by
  obtain ⟨r, hr, hid, -⟩ := fullItems_mem hx
  obtain ⟨jc, pc, sp, hid', he, -, htg, hnot⟩ := notify_record hpre hX ht hr
    (notify_action hX hr hid)
  rw [hid, notifyRef] at hid'
  simp only [Ref.async.injEq, Prod.mk.injEq, true_and] at hid'
  rw [← hid'.1] at he hnot
  exact ⟨pc, sp, he, htg, hnot, (nthEv_spec_of_get he).2⟩

/-- A fault-free arrival on the empty barrier is a counted arrival. -/
theorem emptyItems_of_record (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {r : Record Ref}
    (hr : r ∈ X.objects ((slot L c j).empty 0)) (hf : r.fault = none)
    (ha : r.action = .arrive 1 0) :
    ∃ y ∈ emptyItems L X c j, r.id = arriveRef L X c j y.1 y.2 := by
  classical
  obtain ⟨b, ka, pc, rel, sc, hid, he⟩ := empty_arrival hpre hX ht hr ha
  have hp : arrivesOn ((slot L c j).empty 0) ⟨pc, .arrive ((slot L c j).empty 0) 0 1 rel sc⟩ =
      true := by simp [sourceArrive]
  set t := ((X.tr (consumerOf L c j b)).take ka).countP (arrivesOn ((slot L c j).empty 0))
  have hs : arriveAt L X c j b t = ka := nthEv_eq he hp
  have hid' : r.id = arriveRef L X c j b t := by rw [hid, arriveRef, hs]
  refine ⟨(b, t), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨mem_allCons _,
    Finset.mem_range.mpr ?_⟩, r, hr, hid', hf⟩, hid'⟩
  have h1 : t ≤ ((X.tr (consumerOf L c j b)).take ka).length := List.countP_le_length
  have h2 := len_of_get he
  have h3 := len_le_consBound L X c j b
  simp only [List.length_take] at h1
  change t < _
  omega

/-- A counted arrival is consumer `b`'s arrival on the empty barrier of its use. -/
theorem emptyItems_arrive (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {y : Fin 256 × Nat}
    (hy : y ∈ emptyItems L X c j) :
    ∃ pc rel sc, X.get (consumerOf L c j y.1, arriveAt L X c j y.1 y.2) =
        some ⟨pc, .arrive ((slot L c j).empty 0) 0 1 rel sc⟩ ∧
      arrivals ((slot L c j).empty 0)
        ((X.tr (consumerOf L c j y.1)).take (arriveAt L X c j y.1 y.2)) = y.2 := by
  obtain ⟨r, hr, hid, -⟩ := emptyItems_mem hy
  have h := ((hX.tma.2.2.1 _).2.1 r hr).1
  rw [hid, arriveRef] at h
  obtain ⟨e, he⟩ : ∃ e, X.get (consumerOf L c j y.1, arriveAt L X c j y.1 y.2) = some e := by
    cases hg : X.get (consumerOf L c j y.1, arriveAt L X c j y.1 y.2) with
    | none => simp [objectAction, hg] at h
    | some e => exact ⟨e, rfl⟩
  obtain ⟨hp, hc⟩ := nthEv_spec_of_get he
  obtain ⟨pc, kind⟩ := e
  cases kind with
  | arrive m tx cnt rel sc =>
    have hm : m = (slot L c j).empty 0 := by simpa [sourceArrive] using hp
    subst hm
    have hg := Frame.lt_of_get hX he
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    obtain ⟨-, -, rfl, rfl⟩ := (ht.ring_event hg he hσ).arrive ⟨.acc, j.val, false⟩ (2 * c) _ _ _ _
      rfl j.isLt
    exact ⟨pc, rel, sc, he, hc⟩
  | _ => simp [sourceArrive] at hp


/-! ### The barriers' histories -/

/-- A non-initialization record of an accumulator barrier has a state before it. -/
theorem acc_state (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {j : Fin 2} {f : Bool} {cta i : Nat} {r : Record Ref}
    (hi : (X.objects (Bar.loc L cta ⟨.acc, j.val, f⟩))[i]? = some r)
    (hni : ∀ n, r.action ≠ .init n) :
    ∃ s, stateBefore (X.objects (Bar.loc L cta ⟨.acc, j.val, f⟩)) i = some s := by
  rcases acc_init hpre hX ht hi with ⟨⟨n, hn⟩, -, -⟩ | h
  · exact absurd hn (hni n)
  · exact h

/-- Glue from one history: a fault-free arrival in the phase a successful poll observed is
observed by the poll. -/
theorem observed_of_ids (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {m : Loc}
    {i k : Nat}
    {d w : Record Ref} (hi : (X.objects m)[i]? = some d) (hdf : d.fault = none)
    (hda : d.action = .arrive 1 0) (hs : ∃ s, stateBefore (X.objects m) i = some s)
    (hk : (X.objects m)[k]? = some w) (hww : w.reply.waited = some true)
    (ho : ∃ q, observedAt (X.objects m) k = some q)
    (hp : MbarRing.Poll.phaseOf X m d.id = MbarRing.Poll.observedOf X m w.id) :
    MbarObserved X d.id w.id := by
  obtain ⟨s, hs⟩ := hs
  obtain ⟨q, ho⟩ := ho
  have h1 := MbarRing.Poll.phaseOf_eq hX hi (q := s.phase) (by simp [phaseAt, hs])
  have h2 := MbarRing.Poll.observedOf_eq hX hk ho
  rw [h1, h2] at hp
  exact hX.observed_of_phase (objects_noInval hX ht _) hi hdf (by rw [hda]; trivial) hk hww
      (by simp [phaseAt, hs, hp]) ho

/-- The arrivals of an accumulator barrier are unit arrivals. -/
theorem acc_unit (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {j : Fin 2}
    {f : Bool} {cta : Nat} :
    ∀ (i : Nat) (r : Record Ref) (n tx : Nat),
      (X.objects (Bar.loc L cta ⟨.acc, j.val, f⟩))[i]? = some r → r.fault = none →
      r.action = .arrive n tx → n = 1 ∧ tx = 0 := by
  intro i r n tx hi _ ha
  rcases acc_record_cases hX ht (List.mem_of_getElem? hi) with ⟨_, h⟩ | ⟨_, _, h⟩ | h <;>
    rw [h] at ha <;> cases ha
  exact ⟨rfl, rfl⟩

/-- Consumer `b`'s successful full polls alternate parity with offset `0`. -/
theorem cons_alt (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (c : Nat) (j : Fin 2) (b : Fin 256) :
    SelectedAlternates (objectThreadSelected (consumerOf L c j b))
      (X.objects ((slot L c j).full ((slot L c j).owner b))) 0 :=
  MbarRing.Poll.alternates hX (poll_clean hpre hX ht (cta := 2 * c + b.val / 128) (f := true))
    (fun k pc p acq sc he => by
      have hg := Frame.lt_of_get hX he
      obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
      exact ht.poll_parity (b := ⟨.acc, j.val, true⟩) (cta := 2 * c + b.val / 128) hg he hσ rfl
        j.isLt)

/-- The producer's successful empty polls alternate parity with offset `1`. -/
theorem prod_alt (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (c : Nat) (j : Fin 2) :
    SelectedAlternates (objectThreadSelected (producer L X c j))
      (X.objects ((slot L c j).empty 0)) 1 :=
  MbarRing.Poll.alternates hX (poll_clean hpre hX ht (cta := 2 * c) (f := false))
    (fun k pc p acq sc he => by
      have hg := Frame.lt_of_get hX he
      obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
      exact ht.poll_parity (b := ⟨.acc, j.val, false⟩) (cta := 2 * c) hg he hσ rfl j.isLt)

/-- The record of consumer `b`'s successful full poll with `t` earlier ones. -/
theorem consPoll_record (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {b : Fin 256} {t : Nat}
    (h : t < okPolls ((slot L c j).full ((slot L c j).owner b)) (X.tr (consumerOf L c j b))) :
    ∃ k w, (X.objects ((slot L c j).full ((slot L c j).owner b)))[k]? = some w ∧
      w.id = .thread (consPoll L X c j b t) ∧ w.reply.waited = some true ∧ w.fault = none ∧
      selectedBefore (objectThreadSelected (consumerOf L c j b))
        (X.objects ((slot L c j).full ((slot L c j).owner b))) k = t :=
  let ⟨k, w, _, hk, hid, _, hww, hwf, hsel⟩ :=
    MbarRing.Poll.record hX (poll_clean hpre hX ht (cta := 2 * c + b.val / 128) (f := true)) h
  ⟨k, w, hk, hid, hww, hwf, hsel⟩

/-- The record of the producer's successful empty poll with `n` earlier ones. -/
theorem prodPoll_record (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {n : Nat}
    (h : n < okPolls ((slot L c j).empty 0) (X.tr (producer L X c j))) :
    ∃ k w, (X.objects ((slot L c j).empty 0))[k]? = some w ∧
      w.id = .thread (prodPoll L X c j n) ∧ w.reply.waited = some true ∧ w.fault = none ∧
      selectedBefore (objectThreadSelected (producer L X c j))
        (X.objects ((slot L c j).empty 0)) k = n :=
  let ⟨k, w, _, hk, hid, _, hww, hwf, hsel⟩ :=
    MbarRing.Poll.record hX (poll_clean hpre hX ht (cta := 2 * c) (f := false)) h
  ⟨k, w, hk, hid, hww, hwf, hsel⟩

/-! ### The ring -/

/-- **Buffer `j` of cluster `c` as a ring of items.** -/
def ring (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    (c : Nat) (j : Fin 2) : MbarRing.Items.Ring L kernel Prod X 1 256 2 (fun _ => 1) where
  owner := (slot L c j).owner
  ownF _ _ := 0
  wE _ n := prodPoll L X c j n
  opF _ _ s := (producer L X c j, commitAt L X c j s)
  itF f _ s := notifyRef L X c j f s
  wF b t := consPoll L X c j b t
  cm b t := (consumerOf L c j b, arriveAt L X c j b t)
  note b _ t := arriveRef L X c j b t
  SF f := fullItems L X c j f
  phF f x := MbarRing.Poll.phaseOf X ((slot L c j).full f) (notifyRef L X c j f x.2)
  SE _ := emptyItems L X c j
  phE _ y := MbarRing.Poll.phaseOf X ((slot L c j).empty 0) (arriveRef L X c j y.1 y.2)
  oF b t := MbarRing.Poll.observedOf X ((slot L c j).full ((slot L c j).owner b))
    (.thread (consPoll L X c j b t))
  oE _ n := MbarRing.Poll.observedOf X ((slot L c j).empty 0) (.thread (prodPoll L X c j n))
  cover _ _ := ⟨0, Subsingleton.elim _ _⟩
  guardP f x hx n _ hn := by
    obtain ⟨pc, sp, he, htg, -, hc⟩ := fullItems_commit hpre hX ht hx
    exact commit_guard hpre hX ht he htg (by rw [hc]; exact hn)
  issueF f x hx := by
    obtain ⟨pc, sp, he, -, hnot, -⟩ := fullItems_commit hpre hX ht hx
    exact .single (DepStep.issue ⟨_, he⟩ hnot (by simp) (by simp) (by simp) (by simp))
  guardM _ y hy t htj := by
    obtain ⟨pc, rel, sc, he, hc⟩ := emptyItems_arrive hX ht hy
    exact arrive_guard hpre hX ht he (by rw [hc]; exact htj)
  issue _ _ _ := .refl
  obsF b t hw x hx hp := by
    obtain ⟨r, hr, hid, hf⟩ := fullItems_mem hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
    have hda := notify_action hX hr hid
    obtain ⟨k, w, hk, hwid, hww, -, -⟩ := consPoll_record hpre hX ht
      ((MbarRing.Poll.nth_present (X := X)).mp hw)
    obtain ⟨st, -, -, ho⟩ := MbarRing.Poll.observed_some (X.objects_checked hX _)
        (objects_noInval hX ht _) (δ := 0)
      (by omega) (cons_alt hpre hX ht c j b) hk (objectThreadSelected_iff.mpr ⟨_, hwid⟩) hww
      (Nat.zero_le _)
    have := observed_of_ids hX ht hi hf hda
      (acc_state hpre hX ht (cta := 2 * c + b.val / 128) (f := true) hi
        (by intro n h; rw [hda] at h; cases h)) hk hww ⟨_, ho⟩ (by rw [hid, hwid]; exact hp)
    rw [hid, hwid] at this
    exact Witness.of_mbarObserved this
  obsE _ n hn hw y hy hp := by
    obtain ⟨r, hr, hid, hf⟩ := emptyItems_mem hy
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
    have hda : r.action = .arrive 1 0 := by
      obtain ⟨pc, rel, sc, he, -⟩ := emptyItems_arrive hX ht hy
      have h := ((hX.tma.2.2.1 _).2.1 r hr).1
      rw [hid, arriveRef] at h
      simp [objectAction, he] at h
      exact h.symm
    obtain ⟨k, w, hk, hwid, hww, -, hsel⟩ := prodPoll_record hpre hX ht
      ((MbarRing.Poll.nth_present (X := X)).mp hw)
    obtain ⟨st, -, -, ho⟩ := MbarRing.Poll.observed_some (X.objects_checked hX _)
        (objects_noInval hX ht _) (δ := 1)
      (by omega) (prod_alt hpre hX ht c j) hk (objectThreadSelected_iff.mpr ⟨_, hwid⟩) hww
      (by omega)
    have := observed_of_ids hX ht hi hf hda
      (acc_state hpre hX ht (cta := 2 * c) (f := false) hi
        (by intro n h; rw [hda] at h; cases h)) hk hww ⟨_, ho⟩ (by rw [hid, hwid]; exact hp)
    rw [hid, hwid] at this
    exact Witness.of_mbarObserved this
  fullF b t hw := by
    classical
    obtain ⟨k, w, hk, hwid, hww, -, -⟩ := consPoll_record hpre hX ht
      ((MbarRing.Poll.nth_present (X := X)).mp hw)
    obtain ⟨st, hst, hpos, ho⟩ := MbarRing.Poll.observed_some (X.objects_checked hX _)
        (objects_noInval hX ht _) (δ := 0)
      (by omega) (cons_alt hpre hX ht c j b) hk (objectThreadSelected_iff.mpr ⟨_, hwid⟩) hww
      (Nat.zero_le _)
    have hcard :=
      (X.objects_checked hX ((slot L c j).full ((slot L c j).owner b))).card_unit_arrivals_phase
      (objects_noInval hX ht _) (n := 1) (q := st.phase - 1)
      (fun i r n tx hi hf ha => (acc_unit (cta := 2 * c + b.val / 128) (f := true) hX ht i r n tx
        hi hf ha).1)
      (fun i s _ hs => expected_eq (cta := 2 * c + b.val / 128) (f := true) hpre hX ht i s hs)
      (incrementsBefore_zero hX ht _) (List.getElem?_eq_some_iff.mp hk).1.le hst (by omega)
    obtain ⟨i, hiP⟩ := Finset.card_pos.mp (by rw [hcard]; omega)
    obtain ⟨r, tx, hi, ha, hf, hph⟩ := (Finset.mem_filter.mp hiP).2
    have htx := (acc_unit (cta := 2 * c + b.val / 128) (f := true) hX ht i r 1 tx hi hf ha).2
    subst htx
    obtain ⟨x, hx, hid⟩ := fullItems_of_record hpre hX ht (List.mem_of_getElem? hi) hf ha
    refine Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩⟩
    show MbarRing.Poll.phaseOf X _ (notifyRef L X c j _ x.2) =
      MbarRing.Poll.observedOf X _ (.thread (consPoll L X c j b t))
    rw [← hid, ← hwid, MbarRing.Poll.phaseOf_eq hX hi hph, MbarRing.Poll.observedOf_eq hX hk ho]
  fullE _ n hn hw := by
    classical
    obtain ⟨k, w, hk, hwid, hww, -, hsel⟩ := prodPoll_record hpre hX ht
      ((MbarRing.Poll.nth_present (X := X)).mp hw)
    obtain ⟨st, hst, hpos, ho⟩ := MbarRing.Poll.observed_some (X.objects_checked hX _)
        (objects_noInval hX ht _) (δ := 1)
      (by omega) (prod_alt hpre hX ht c j) hk (objectThreadSelected_iff.mpr ⟨_, hwid⟩) hww
      (by omega)
    have hcard := (X.objects_checked hX ((slot L c j).empty 0)).card_unit_arrivals_phase
        (objects_noInval hX ht ((slot L c j).empty 0))
      (n := 256) (q := st.phase - 1)
      (fun i r n tx hi hf ha => (acc_unit (cta := 2 * c) (f := false) hX ht i r n tx
        hi hf ha).1)
      (fun i s _ hs => expected_eq (cta := 2 * c) (f := false) hpre hX ht i s hs)
      (incrementsBefore_zero hX ht _) (List.getElem?_eq_some_iff.mp hk).1.le hst (by omega)
    refine (le_of_eq hcard.symm).trans (card_positions_le
      (X.objects_checked hX ((slot L c j).empty 0)) _
      (fun y => arriveRef L X c j y.1 y.2) _ (fun i hiP => ?_))
    obtain ⟨r, tx, hi, ha, hf, hph⟩ := (Finset.mem_filter.mp hiP).2
    have htx := (acc_unit (cta := 2 * c) (f := false) hX ht i r 1 tx hi hf ha).2
    subst htx
    obtain ⟨y, hy, hid⟩ := emptyItems_of_record hpre hX ht (List.mem_of_getElem? hi) hf ha
    refine ⟨r, hi, y, Finset.mem_filter.mpr ⟨hy, ?_⟩, hid⟩
    show MbarRing.Poll.phaseOf X _ (arriveRef L X c j y.1 y.2) =
      MbarRing.Poll.observedOf X _ (.thread (prodPoll L X c j n))
    rw [← hid, ← hwid, MbarRing.Poll.phaseOf_eq hX hi hph, MbarRing.Poll.observedOf_eq hX hk ho]
  ltF b t t' hlt hw := by
    have h := (MbarRing.Poll.nth_present (X := X)).mp hw
    exact ⟨(MbarRing.Poll.nth_present (X := X)).mpr (by omega),
      MbarRing.Poll.observed_lt hX (δ := 0) (by omega)
        (poll_clean hpre hX ht (cta := 2 * c + b.val / 128) (f := true)) (objects_noInval hX ht _)
        (cons_alt hpre hX ht c j b) (Nat.zero_le _) hlt h⟩
  ltE _ n n' h1 hlt hw := by
    have h := (MbarRing.Poll.nth_present (X := X)).mp hw
    exact ⟨(MbarRing.Poll.nth_present (X := X)).mpr (by omega),
      MbarRing.Poll.observed_lt hX (δ := 1) (by omega)
        (poll_clean hpre hX ht (cta := 2 * c) (f := false)) (objects_noInval hX ht _)
        (prod_alt hpre hX ht c j) h1 hlt h⟩

end TmemRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
