-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.PairTmaRing.Hyp
public import Lemmas.Protocol.MbarRingItems

@[expose] public section

/-! # The items of a pair TMA ring slot

A proof tool. Slot `S` as a slot of `MbarRing.Items.Ring`: two producers `prod a`, each polling
its CTA's empty barrier `empty a`; `nc` consumers `cons b` polling the full barrier. A phase of
`full` is completed by items of `1 + 2 n` kinds (`Kind S.n`): the leader producer's arrival
(kind `0`) and the `n` copies of each producer (kinds `copyKind S.n a j`). The item of kind `k`
and use `u` is the producer's event with `kIdx k u` earlier events of its kind (`opF`), and its
record on `full` is that event's (the arrival) or its copy's notification (`itF`). Consumer
`b`'s commit of use `t` is its commit with `t` earlier commits (`cm`), whose notification of
`empty a` is `note`.

Under `Hyp`, a record of `full` that arrives is the leader producer's (`arrival_producer`), one
that completes bytes a producer's copy's (`completion_producer`), and an arrival of `empty a`
a consumer's commit notification (`notify_consumer`). So each fault-free arrival or completion
of `full` is a counted item (`full_item`), and each fault-free arrival of `empty a` a counted
notification (`empty_item`). -/

namespace PTX.PairTmaRing

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {nc : Nat}

/-! ### The slot's items -/

/-- The events of kind `k`: arrivals on, or copies completing on, the full barrier. -/
def kPred (S : Slot nc) (k : Kind S.n) : Event → Bool :=
  if k.val = 0 then arrivesOn S.full else issuesTo S.full

/-- The producer's event of the item of kind `k` and use `u`. -/
def opF (X : Execution) (S : Slot nc) (k : Kind S.n) (u : Nat) : EvId :=
  (S.prod (kOwner S.n k), nthEv X (kPred S k) (S.prod (kOwner S.n k)) (kIdx S.n k u))

/-- The record of the item of kind `k` and use `u` on the full barrier. -/
def itF (X : Execution) (S : Slot nc) (k : Kind S.n) (u : Nat) : Ref :=
  if k.val = 0 then .thread (opF X S k u) else .async (opF X S k u) (.notify .load)

/-- Producer `a`'s successful poll of its empty barrier with `n` earlier ones. -/
def wE (X : Execution) (S : Slot nc) (a : Fin 2) (n : Nat) : EvId :=
  (S.prod a, MbarRing.Poll.nth X (S.empty a) (S.prod a) n)

/-- Consumer `b`'s successful poll of the full barrier with `j` earlier ones. -/
def wF (X : Execution) (S : Slot nc) (b : Fin nc) (j : Nat) : EvId :=
  (S.cons b, MbarRing.Poll.nth X S.full (S.cons b) j)

/-- Consumer `b`'s commit to the slot with `t` earlier ones. -/
def cm (X : Execution) (S : Slot nc) (b : Fin nc) (t : Nat) : EvId :=
  (S.cons b, nthEv X (commitsTo (S.empty 0)) (S.cons b) t)

/-- Consumer `b`'s notification of `empty a` by its commit of use `t`. -/
def note (X : Execution) (S : Slot nc) (b : Fin nc) (a : Fin 2) (t : Nat) : Ref :=
  .async (cm X S b t) (.tcNotify (rankOf a))

/-- A bound on the uses of the slot's items. -/
def useBound (X : Execution) (S : Slot nc) : Nat :=
  (X.tr (S.prod 0)).length + (X.tr (S.prod 1)).length + ∑ b, (X.tr (S.cons b)).length + 1

open Classical in
/-- The counted items of the full barrier: those with a fault-free record of their action. -/
def SF (X : Execution) (S : Slot nc) : Finset (Kind S.n × Nat) :=
  (Finset.univ ×ˢ Finset.range (useBound X S)).filter fun x =>
    ∃ r ∈ X.objects S.full, r.id = itF X S x.1 x.2 ∧ r.fault = none ∧
      (x.1.val = 0 → r.action = .arrive 1 S.tx) ∧ (x.1.val ≠ 0 → r.action = .completeTx S.bytes)

open Classical in
/-- The counted notifications of `empty a`: those with a fault-free record. -/
def SE (X : Execution) (S : Slot nc) (a : Fin 2) : Finset (Fin nc × Nat) :=
  (Finset.univ ×ˢ Finset.range (useBound X S)).filter fun y =>
    ∃ r ∈ X.objects (S.empty a), r.id = note X S y.1 a y.2 ∧ r.fault = none ∧
      r.action = .arrive 1 0

/-- The phase of a full barrier item. -/
def phF (X : Execution) (S : Slot nc) (x : Kind S.n × Nat) : Nat :=
  MbarRing.Poll.phaseOf X S.full (itF X S x.1 x.2)

/-- The phase of a notification of `empty a`. -/
def phE (X : Execution) (S : Slot nc) (a : Fin 2) (y : Fin nc × Nat) : Nat :=
  MbarRing.Poll.phaseOf X (S.empty a) (note X S y.1 a y.2)

/-- The completed phase of `full` observed by consumer `b`'s poll with `j` earlier ones. -/
def oF (X : Execution) (S : Slot nc) (b : Fin nc) (j : Nat) : Nat :=
  MbarRing.Poll.observedOf X S.full (.thread (wF X S b j))

/-- The completed phase of `empty a` observed by producer `a`'s poll with `n` earlier ones. -/
def oE (X : Execution) (S : Slot nc) (a : Fin 2) (n : Nat) : Nat :=
  MbarRing.Poll.observedOf X (S.empty a) (.thread (wE X S a n))

variable {X : Execution} {S : Slot nc}

theorem itF_zero (u : Nat) :
    itF X S ⟨0, by omega⟩ u = .thread (S.prod 0, nthEv X (arrivesOn S.full) (S.prod 0) u) := by
  simp [itF, opF, kOwner, kIdx, kPred]

theorem itF_ne {k : Kind S.n} (hk : k.val ≠ 0) (u : Nat) : itF X S k u =
    .async (S.prod (kOwner S.n k), nthEv X (issuesTo S.full) (S.prod (kOwner S.n k))
      (kIdx S.n k u)) (.notify .load) := by
  simp [itF, opF, kPred, hk]

theorem opF_ne {k : Kind S.n} (hk : k.val ≠ 0) (u : Nat) : opF X S k u =
    (S.prod (kOwner S.n k), nthEv X (issuesTo S.full) (S.prod (kOwner S.n k)) (kIdx S.n k u)) := by
  simp [opF, kPred, hk]

theorem opF_zero (u : Nat) :
    opF X S ⟨0, by omega⟩ u = (S.prod 0, nthEv X (arrivesOn S.full) (S.prod 0) u) := by
  simp [opF, kOwner, kIdx, kPred]

theorem kPred_zero : kPred S ⟨0, by omega⟩ = arrivesOn S.full := by simp [kPred]

theorem kPred_ne {k : Kind S.n} (hk : k.val ≠ 0) : kPred S k = issuesTo S.full := by
  simp [kPred, hk]

/-! ### The producers and consumers -/

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}

/-- A copy issue completing on the full barrier is producer `a`'s, within its budget. -/
theorem issue_producer (H : Hyp L K A X S) {g k pc al : Nat} {sp : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩) (hm : sp.mbar = S.full) :
    ∃ a, g = S.prod a ∧ ((X.tr g).take k).countP (issuesTo S.full) + 1 ≤
      S.n * okPolls (S.empty a) ((X.tr g).take k) :=
  H.issue he hm

/-- An arrival on the full barrier is the leader producer's, with one unit expecting the use's
bytes, after more successful polls of its empty barrier than its earlier arrivals. -/
theorem arrival_producer (H : Hyp L K A X S) {r : Record Ref} (hr : r ∈ X.objects S.full)
    {n tx : Nat} (ha : r.action = .arrive n tx) :
    n = 1 ∧ tx = S.tx ∧ ∃ j pc rel sc, r.id = .thread (S.prod 0, j) ∧
      X.get (S.prod 0, j) = some ⟨pc, .arrive S.full S.tx 1 rel sc⟩ ∧
      arrivals S.full ((X.tr (S.prod 0)).take j) + 1 ≤
        okPolls (S.empty 0) ((X.tr (S.prod 0)).take j) := by
  cases H.full_src r hr with
  | init ha' => rw [ha] at ha'; cases ha'
  | poll _ _ ha' => rw [ha] at ha'; cases ha'
  | copy _ _ _ ha' => rw [ha] at ha'; cases ha'
  | arrive hid he ha' hb =>
    rw [ha] at ha'
    simp only [Action.arrive.injEq] at ha'
    obtain ⟨rfl, rfl⟩ := ha'
    exact ⟨rfl, rfl, _, _, _, _, hid, he, hb⟩

/-- A completion on the full barrier is the notification of a copy issue of producer `a`, of one
copy's bytes. -/
theorem completion_producer (H : Hyp L K A X S) {r : Record Ref} (hr : r ∈ X.objects S.full)
    {n : Nat} (ha : r.action = .completeTx n) :
    n = S.bytes ∧ ∃ (a : Fin 2) (j pc al : Nat) (sp : TensorCopy.Spec),
      r.id = .async (S.prod a, j) (.notify .load) ∧
      X.get (S.prod a, j) = some ⟨pc, .tensorIssue al sp⟩ ∧ sp.mbar = S.full ∧
      ((X.tr (S.prod a)).take j).countP (issuesTo S.full) + 1 ≤
        S.n * okPolls (S.empty a) ((X.tr (S.prod a)).take j) := by
  cases H.full_src r hr with
  | init ha' => rw [ha] at ha'; cases ha'
  | poll _ _ ha' => rw [ha] at ha'; cases ha'
  | arrive _ _ ha' => rw [ha] at ha'; cases ha'
  | copy hid he hm ha' =>
    rw [ha] at ha'
    cases ha'
    obtain ⟨a, rfl, hib⟩ := H.issue he hm
    exact ⟨rfl, a, _, _, _, _, hid, he, hm, hib⟩

/-- An arrival on producer `a`'s empty barrier is a unit notification of consumer `b`'s commit,
after more successful full polls of `b` than its earlier commits. -/
theorem notify_consumer (H : Hyp L K A X S) {a : Fin 2} {r : Record Ref}
    (hr : r ∈ X.objects (S.empty a)) {n tx : Nat} (ha : r.action = .arrive n tx) :
    n = 1 ∧ tx = 0 ∧ ∃ (b : Fin nc) (j pc : Nat) (sp : TcCommit.Spec),
      r.id = .async (S.cons b, j) (.tcNotify (rankOf a)) ∧
      X.get (S.cons b, j) = some ⟨pc, .tc (.commit sp)⟩ ∧ sp.mbar = S.empty 0 ∧
      TcCommit.target sp (rankOf a) = some (S.empty a) ∧
      ((X.tr (S.cons b)).take j).countP (commitsTo (S.empty 0)) + 1 ≤
        okPolls S.full ((X.tr (S.cons b)).take j) := by
  cases H.empty_src a r hr with
  | init ha' => rw [ha] at ha'; cases ha'
  | poll _ _ ha' => rw [ha] at ha'; cases ha'
  | notify hid he hm htg ha' hb =>
    rw [ha] at ha'
    simp only [Action.arrive.injEq] at ha'
    obtain ⟨rfl, rfl⟩ := ha'
    exact ⟨rfl, rfl, _, _, _, _, hid, he, hm, htg, hb⟩

/-! ### Records as items -/

private theorem le_useBound_prod (a : Fin 2) {j : Nat} {e : Event}
    (he : X.get (S.prod a, j) = some e) : j < useBound X S := by
  have h2 := len_of_get he
  have := a.isLt
  unfold useBound
  rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> simp only at h2 <;> omega

private theorem le_useBound_cons (b : Fin nc) {j : Nat} {e : Event}
    (he : X.get (S.cons b, j) = some e) : j < useBound X S := by
  have h2 := len_of_get he
  have := Finset.single_le_sum (f := fun b => (X.tr (S.cons b)).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
  simp only at h2 this
  unfold useBound
  omega

/-- A fault-free arrival or completion of the full barrier is a counted item. -/
theorem full_item (H : Hyp L K A X S) {r : Record Ref} (hr : r ∈ X.objects S.full)
    (hf : r.fault = none) (hu : (∃ n tx, r.action = .arrive n tx) ∨ ∃ n, r.action = .completeTx n) :
    ∃ x ∈ SF X S, r.id = itF X S x.1 x.2 ∧ ((∃ n tx, r.action = .arrive n tx) ↔ x.1.val = 0) := by
  classical
  rcases hu with ⟨n, tx, ha⟩ | ⟨n, ha⟩
  · obtain ⟨rfl, rfl, j, pc, rel, sc, hid, he, -⟩ := arrival_producer H hr ha
    have hp : arrivesOn S.full ⟨pc, .arrive S.full S.tx 1 rel sc⟩ = true := by
      simp [arrivesOn, sourceArrive]
    have hit : itF X S ⟨0, by omega⟩ (arrivals S.full ((X.tr (S.prod 0)).take j)) = r.id := by
      rw [itF_zero, hid]
      unfold arrivals
      rw [nthEv_eq he hp]
    have hlt : arrivals S.full ((X.tr (S.prod 0)).take j) < useBound X S := by
      have h1 := countP_take_le_length (arrivesOn S.full) (X.tr (S.prod 0)) j
      have := le_useBound_prod (S := S) 0 he
      unfold arrivals
      omega
    refine ⟨(⟨0, by omega⟩, arrivals S.full ((X.tr (S.prod 0)).take j)),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr hlt⟩,
        r, hr, hit.symm, hf, fun _ => ha, fun h => absurd rfl h⟩, hit.symm, ?_⟩
    simp [ha]
  · obtain ⟨rfl, a, j, pc, al, sp, hid, he, hm, -⟩ := completion_producer H hr ha
    have hn := H.n_pos
    set I := ((X.tr (S.prod a)).take j).countP (issuesTo S.full)
    have hp : issuesTo S.full ⟨pc, .tensorIssue al sp⟩ = true := by simp [issuesTo, hm]
    have hk := copyKind_ne a (I % S.n) (Nat.mod_lt _ hn)
    have hit : itF X S (copyKind S.n a (I % S.n) (Nat.mod_lt _ hn)) (I / S.n) = r.id := by
      rw [itF_ne hk, kOwner_copyKind, kIdx_copyKind, hid, Nat.div_add_mod, nthEv_eq he hp]
    have hlt : I / S.n < useBound X S := by
      have h1 := countP_take_le_length (issuesTo S.full) (X.tr (S.prod a)) j
      have h3 : I / S.n ≤ I := Nat.div_le_self _ _
      have := le_useBound_prod a he
      omega
    refine ⟨(copyKind S.n a (I % S.n) (Nat.mod_lt _ hn), I / S.n),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr hlt⟩,
        r, hr, hit.symm, hf, fun h => absurd h hk, fun _ => ha⟩, hit.symm, ?_⟩
    simp only [ha, reduceCtorEq, exists_false, false_iff]
    exact hk

/-- A fault-free arrival of producer `a`'s empty barrier is a counted notification. -/
theorem empty_item (H : Hyp L K A X S) {a : Fin 2} {r : Record Ref}
    (hr : r ∈ X.objects (S.empty a)) (hf : r.fault = none) {n tx : Nat}
    (ha : r.action = .arrive n tx) : n = 1 ∧ ∃ y ∈ SE X S a, r.id = note X S y.1 a y.2 := by
  classical
  obtain ⟨rfl, rfl, b, j, pc, sp, hid, he, hm, -, -⟩ := notify_consumer H hr ha
  set t := ((X.tr (S.cons b)).take j).countP (commitsTo (S.empty 0))
  have hp : commitsTo (S.empty 0) ⟨pc, .tc (.commit sp)⟩ = true := by simp [commitsTo, hm]
  have hit : note X S b a t = r.id := by
    rw [hid]
    simp only [note, cm, t]
    rw [nthEv_eq he hp]
  have hlt : t < useBound X S := by
    have h1 := countP_take_le_length (commitsTo (S.empty 0)) (X.tr (S.cons b)) j
    have := le_useBound_cons b he
    omega
  exact ⟨rfl, (b, t), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,
    Finset.mem_range.mpr hlt⟩, r, hr, hit.symm, hf, ha⟩, hit.symm⟩

end
end PTX.PairTmaRing
