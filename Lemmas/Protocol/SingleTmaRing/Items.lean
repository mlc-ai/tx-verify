-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.SingleTmaRing.Hyp
public import Lemmas.Protocol.PairTmaRing.Order

@[expose] public section

/-! # The items of a slot of a single-CTA TMA ring

A proof tool (generalized from the Inkling KV ring, `n` copies of `bytes` bytes per use and
polls acquiring at scope `sc`). A phase of the full barrier is completed by `n + 1` items
(`Kind S`): kind 0 the arrival, kind `1 + i` the `i`-th copy of the use. The item of kind `k`
and use `u` is the event `opF k u`: the preloading events (`pArr`, `pCp i`) for `δ = 1`, `u = 0`;
else the producer thread's event of its kind with `kIdx S k (u - δ)` earlier events of that kind.
The polls are numbered as the uses they wait for: `wE a n` is producer `a`'s successful poll of
`empty` with `n - δ` earlier ones (for the use `n ≥ 1`), `wF b j` the consumer's successful poll
of `full` with `j` earlier ones.

Under `Hyp`, a record of `full` that arrives is the arrival thread's (`ap`) or the preloading
arrival; one that completes bytes is a copy of the copy thread (`cp`) or a preloading copy; an
arrival of `empty` is the consumer's commit notification (`notify_source`). So each fault-free
arrival or completion of `full` is a counted item (`full_item`) and each fault-free arrival of
`empty` a counted notification (`empty_item`); a counted item's event is its producer's, after
more successful polls of `empty` than its use (`SF_op`). -/

namespace PTX.SingleTmaRing
open PTX PTX.Flow AsyncCopy
open PTX.MBarrier hiding okPolls

noncomputable section

/-- A use has a copy, a copy a byte, and twice a use's bytes fit the barrier's transaction counter
(the counter ranges over one use's bytes either side of zero): the transaction count of a phase
then fixes its number of copies, and no operand or counter is out of range. -/
def Slot.Fits (S : Slot) : Prop := 0 < S.n ∧ 0 < S.bytes ∧ 2 * S.tx ≤ MBarrier.limit

theorem Slot.Fits.bytes_le {S : Slot} (h : S.Fits) : S.bytes ≤ S.tx := by
  unfold Slot.tx
  exact Nat.le_mul_of_pos_left _ h.1

theorem Slot.Fits.tx_lt {S : Slot} (h : S.Fits) : S.tx < 2 ^ 32 := by
  have := h.2.2; unfold MBarrier.limit at this; omega

theorem Slot.Fits.bytes_lt {S : Slot} (h : S.Fits) : S.bytes < 2 ^ 32 :=
  lt_of_le_of_lt h.bytes_le h.tx_lt

/-- The kinds of items of a phase of the full barrier: the arrival and the `n` copies. -/
abbrev Kind (S : Slot) : Type := Fin (S.n + 1)

/-- The loader thread of kind `k`: lane 0 arrives, the elected lane copies. -/
def kOwner {m : Nat} (k : Fin (m + 1)) : Fin 2 := if k.val = 0 then 0 else 1

/-- The events of kind `k`. -/
def kPred (S : Slot) (k : Kind S) : Event → Bool :=
  if k.val = 0 then arrivesOn S.full else issuesTo S.full

/-- The loader thread's count of earlier events of kind `k` at its `m`-th use. -/
def kIdx (S : Slot) (k : Kind S) (m : Nat) : Nat := if k.val = 0 then m else S.n * m + (k.val - 1)

/-- The event of the item of kind `k` and use `u`. -/
def opF (X : Execution) (S : Slot) (k : Kind S) (u : Nat) : EvId :=
  if S.δ = 1 ∧ u = 0 then
    (if h : k.val = 0 then S.pArr else S.pCp ⟨k.val - 1, by have := k.isLt; omega⟩)
  else (S.prod (kOwner k), nthEv X (kPred S k) (S.prod (kOwner k)) (kIdx S k (u - S.δ)))

/-- The record of the item of kind `k` and use `u` on the full barrier. -/
def itF (X : Execution) (S : Slot) (k : Kind S) (u : Nat) : Ref :=
  if k.val = 0 then .thread (opF X S k u) else .async (opF X S k u) (.notify .load)

/-- Producer `a`'s successful poll of the empty barrier for use `n ≥ 1`. -/
def wE (X : Execution) (S : Slot) (a : Fin 2) (n : Nat) : EvId :=
  (S.prod a, MbarRing.Poll.nth X S.empty (S.prod a) (n - S.δ))

/-- The consumer's successful poll of the full barrier with `j` earlier ones. -/
def wF (X : Execution) (S : Slot) (_b : Fin 1) (j : Nat) : EvId :=
  (S.cm, MbarRing.Poll.nth X S.full S.cm j)

/-- The consumer's commit to the slot with `t` earlier ones. -/
def cmE (X : Execution) (S : Slot) (_b : Fin 1) (t : Nat) : EvId :=
  (S.cm, nthEv X (commitsTo S.empty) S.cm t)

/-- The notification of the empty barrier by the commit with `t` earlier ones. -/
def note (X : Execution) (S : Slot) (b : Fin 1) (_a : Fin 2) (t : Nat) : Ref :=
  .async (cmE X S b t) (.tcNotify rank0)

/-- A bound on the uses of the slot's items. -/
def useBound (X : Execution) (S : Slot) : Nat :=
  (X.tr S.ap).length + (X.tr S.cp).length + (X.tr S.cm).length + 2

open Classical in
/-- The counted items of the full barrier: those with a fault-free record of their action. -/
def SF (X : Execution) (S : Slot) : Finset (Kind S × Nat) :=
  (Finset.univ ×ˢ Finset.range (useBound X S)).filter fun x =>
    ∃ r ∈ X.objects S.full, r.id = itF X S x.1 x.2 ∧ r.fault = none ∧
      (x.1.val = 0 → r.action = .arrive 1 S.tx) ∧
      (x.1.val ≠ 0 → r.action = .completeTx S.bytes)

open Classical in
/-- The counted notifications of the empty barrier: those with a fault-free record. -/
def SE (X : Execution) (S : Slot) : Finset (Fin 1 × Nat) :=
  (Finset.univ ×ˢ Finset.range (useBound X S)).filter fun y =>
    ∃ r ∈ X.objects S.empty, r.id = note X S y.1 0 y.2 ∧ r.fault = none ∧
      r.action = .arrive 1 0

/-- The phase of a full barrier item. -/
def phF (X : Execution) (S : Slot) (x : Kind S × Nat) : Nat :=
  MbarRing.Poll.phaseOf X S.full (itF X S x.1 x.2)

/-- The phase of a notification of the empty barrier. -/
def phE (X : Execution) (S : Slot) (y : Fin 1 × Nat) : Nat :=
  MbarRing.Poll.phaseOf X S.empty (note X S y.1 0 y.2)

/-- The completed phase of `full` observed by the consumer's poll with `j` earlier ones. -/
def oF (X : Execution) (S : Slot) (b : Fin 1) (j : Nat) : Nat :=
  MbarRing.Poll.observedOf X S.full (.thread (wF X S b j))

/-- The completed phase of `empty` observed by producer `a`'s poll for use `n`. -/
def oE (X : Execution) (S : Slot) (a : Fin 2) (n : Nat) : Nat :=
  MbarRing.Poll.observedOf X S.empty (.thread (wE X S a n))

/-! ### Items -/

variable {X : Execution} {S : Slot} {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {sc : MbarScope}



theorem kOwner_zero {m : Nat} : kOwner (⟨0, by omega⟩ : Fin (m + 1)) = 0 := by simp [kOwner]

theorem kOwner_of_zero {k : Kind S} (hk : k.val = 0) : kOwner k = 0 := by simp [kOwner, hk]

theorem kOwner_ne {k : Kind S} (hk : k.val ≠ 0) : kOwner k = 1 := by simp [kOwner, hk]

theorem prod_zero : S.prod 0 = S.ap := by simp [Slot.prod]

theorem prod_one : S.prod 1 = S.cp := by simp [Slot.prod]

theorem kPred_zero : kPred S ⟨0, by omega⟩ = arrivesOn S.full := by simp [kPred]

theorem kPred_ne {k : Kind S} (hk : k.val ≠ 0) : kPred S k = issuesTo S.full := by simp [kPred, hk]

theorem kIdx_zero (m : Nat) : kIdx S ⟨0, by omega⟩ m = m := by simp [kIdx]

theorem kIdx_ne {k : Kind S} (hk : k.val ≠ 0) (m : Nat) : kIdx S k m = S.n * m + (k.val - 1) := by
  simp [kIdx, hk]

/-- The prologue's items are of use 0. -/
theorem opF_pre_zero (h : S.δ = 1) : opF X S ⟨0, by omega⟩ 0 = S.pArr := by
  simp [opF, h]

theorem opF_pre_ne {k : Kind S} (hk : k.val ≠ 0) (h : S.δ = 1) :
    opF X S k 0 = S.pCp ⟨k.val - 1, by have := k.isLt; omega⟩ := by
  simp [opF, h, hk]

/-- The loader's items. -/
theorem opF_ld {k : Kind S} {u : Nat} (h : ¬ (S.δ = 1 ∧ u = 0)) :
    opF X S k u = (S.prod (kOwner k), nthEv X (kPred S k) (S.prod (kOwner k))
      (kIdx S k (u - S.δ))) := by
  simp [opF, h]

/-! ### The sources of the records -/

/-- An arrival on the full barrier is the loader's lane-0 arrival or the prologue's. -/
theorem arrival_source (H : Hyp L K A X S sc) {r : Record Ref} (hr : r ∈ X.objects S.full)
    {n tx : Nat} (ha : r.action = .arrive n tx) :
    n = 1 ∧ tx = S.tx ∧
      ((∃ j pc rel sc, r.id = .thread (S.ap, j) ∧
        X.get (S.ap, j) = some ⟨pc, .arrive S.full S.tx 1 rel sc⟩ ∧
        arrivals S.full ((X.tr S.ap).take j) + 1 ≤ okPolls S.empty ((X.tr S.ap).take j)) ∨
      (S.δ = 1 ∧ r.id = .thread S.pArr ∧
        ∃ pc rel sc, X.get S.pArr = some ⟨pc, .arrive S.full S.tx 1 rel sc⟩)) := by
  cases H.full_src r hr with
  | init ha' => rw [ha] at ha'; cases ha'
  | poll _ _ ha' => rw [ha] at ha'; cases ha'
  | copy _ _ _ ha' _ => rw [ha] at ha'; cases ha'
  | preCopy _ _ _ _ ha' => rw [ha] at ha'; cases ha'
  | arrive hid he ha' hb =>
    rw [ha] at ha'
    simp only [Action.arrive.injEq] at ha'
    obtain ⟨rfl, rfl⟩ := ha'
    exact ⟨rfl, rfl, .inl ⟨_, _, _, _, hid, he, hb⟩⟩
  | preArrive hδ hid he ha' =>
    rw [ha] at ha'
    simp only [Action.arrive.injEq] at ha'
    obtain ⟨rfl, rfl⟩ := ha'
    exact ⟨rfl, rfl, .inr ⟨hδ, hid, _, _, _, he⟩⟩

/-- A completion on the full barrier is a copy of the loader's elected lane, within its budget,
or one of the prologue's eight. -/
theorem completion_source (H : Hyp L K A X S sc) {r : Record Ref} (hr : r ∈ X.objects S.full)
    {n : Nat} (ha : r.action = .completeTx n) :
    n = S.bytes ∧
      ((∃ j pc al sp, r.id = .async (S.cp, j) (.notify .load) ∧
        X.get (S.cp, j) = some ⟨pc, .tensorIssue al sp⟩ ∧ sp.mbar = S.full ∧
        ((X.tr S.cp).take j).countP (issuesTo S.full) + 1 ≤
          S.n * okPolls S.empty ((X.tr S.cp).take j)) ∨
      (S.δ = 1 ∧ ∃ (i : Fin S.n) (pc al : Nat) (sp : TensorCopy.Spec),
        r.id = .async (S.pCp i) (.notify .load) ∧
        X.get (S.pCp i) = some ⟨pc, .tensorIssue al sp⟩ ∧ sp.mbar = S.full)) := by
  cases H.full_src r hr with
  | init ha' => rw [ha] at ha'; cases ha'
  | poll _ _ ha' => rw [ha] at ha'; cases ha'
  | arrive _ _ ha' _ => rw [ha] at ha'; cases ha'
  | preArrive _ _ _ ha' => rw [ha] at ha'; cases ha'
  | copy hid he hm ha' hb =>
    rw [ha] at ha'
    cases ha'
    exact ⟨rfl, .inl ⟨_, _, _, _, hid, he, hm, hb⟩⟩
  | preCopy hδ hid he hm ha' =>
    rw [ha] at ha'
    cases ha'
    exact ⟨rfl, .inr ⟨hδ, _, _, _, _, hid, he, hm⟩⟩

/-- An arrival on the empty barrier is a unit notification of the MMA lane's commit. -/
theorem notify_source (H : Hyp L K A X S sc) {r : Record Ref} (hr : r ∈ X.objects S.empty)
    {n tx : Nat} (ha : r.action = .arrive n tx) :
    n = 1 ∧ tx = 0 ∧ ∃ (j pc : Nat) (sp : TcCommit.Spec),
      r.id = .async (S.cm, j) (.tcNotify rank0) ∧
      X.get (S.cm, j) = some ⟨pc, .tc (.commit sp)⟩ ∧ sp.mbar = S.empty ∧
      TcCommit.target sp rank0 = some S.empty ∧
      ((X.tr S.cm).take j).countP (commitsTo S.empty) + 1 ≤
        okPolls S.full ((X.tr S.cm).take j) := by
  cases H.empty_src r hr with
  | init ha' => rw [ha] at ha'; cases ha'
  | poll _ _ ha' => rw [ha] at ha'; cases ha'
  | notify hid he hm htg ha' hb =>
    rw [ha] at ha'
    simp only [Action.arrive.injEq] at ha'
    obtain ⟨rfl, rfl⟩ := ha'
    exact ⟨rfl, rfl, _, _, _, hid, he, hm, htg, hb⟩

/-! ### Records as items -/

private theorem lt_useBound_ap {j : Nat} {e : Event} (he : X.get (S.ap, j) = some e) :
    j + 1 < useBound X S := by
  have := len_of_get he
  simp only at this
  unfold useBound
  omega

private theorem lt_useBound_cp {j : Nat} {e : Event} (he : X.get (S.cp, j) = some e) :
    j + 1 < useBound X S := by
  have := len_of_get he
  simp only at this
  unfold useBound
  omega

private theorem lt_useBound_cm {j : Nat} {e : Event} (he : X.get (S.cm, j) = some e) :
    j + 1 < useBound X S := by
  have := len_of_get he
  simp only at this
  unfold useBound
  omega

/-- A fault-free arrival or completion of the full barrier is a counted item. -/
theorem full_item (H : Hyp L K A X S sc) {r : Record Ref} (hr : r ∈ X.objects S.full)
    (hf : r.fault = none) (hu : (∃ n tx, r.action = .arrive n tx) ∨ ∃ n, r.action = .completeTx n) :
    ∃ x ∈ SF X S, r.id = itF X S x.1 x.2 ∧ ((∃ n tx, r.action = .arrive n tx) ↔ x.1.val = 0) := by
  classical
  have hδ := H.δ_le
  rcases hu with ⟨n, tx, ha⟩ | ⟨n, ha⟩
  · obtain ⟨rfl, rfl, hs⟩ := arrival_source H hr ha
    rcases hs with ⟨j, pc, rel, sc, hid, he, hab⟩ | ⟨hδ1, hid, pc, rel, sc, he⟩
    · have hp : arrivesOn S.full ⟨pc, .arrive S.full S.tx 1 rel sc⟩ = true := by
        simp [arrivesOn, sourceArrive]
      set a := arrivals S.full ((X.tr S.ap).take j) with ha'
      have hnz : ¬ (S.δ = 1 ∧ a + S.δ = 0) := fun h => by omega
      have hit : itF X S ⟨0, by omega⟩ (a + S.δ) = r.id := by
        rw [hid]
        simp only [itF, ↓reduceIte]
        rw [opF_ld hnz, kOwner_zero, prod_zero, kPred_zero, kIdx_zero, Nat.add_sub_cancel]
        simp only [ha']
        unfold arrivals
        rw [nthEv_eq he hp]
      have hlt : a + S.δ < useBound X S := by
        have h1 := countP_take_le_length (arrivesOn S.full) (X.tr S.ap) j
        have := lt_useBound_ap he
        unfold arrivals at ha'
        omega
      refine ⟨(⟨0, by omega⟩, a + S.δ),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,
          Finset.mem_range.mpr hlt⟩, r, hr, hit.symm, hf, fun _ => ha, fun h => absurd rfl h⟩,
        hit.symm, ?_⟩
      simp [ha]
    · have hit : itF X S ⟨0, by omega⟩ 0 = r.id := by
        rw [hid]
        simp only [itF, ↓reduceIte]
        rw [opF_pre_zero hδ1]
      have hlt : 0 < useBound X S := by unfold useBound; omega
      refine ⟨(⟨0, by omega⟩, 0),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,
          Finset.mem_range.mpr hlt⟩, r, hr, hit.symm, hf, fun _ => ha, fun h => absurd rfl h⟩,
        hit.symm, ?_⟩
      simp [ha]
  · obtain ⟨rfl, hs⟩ := completion_source H hr ha
    rcases hs with ⟨j, pc, al, sp, hid, he, hm, hib⟩ | ⟨hδ1, i, pc, al, sp, hid, he, hm⟩
    · set I := ((X.tr S.cp).take j).countP (issuesTo S.full) with hI
      have hp : issuesTo S.full ⟨pc, .tensorIssue al sp⟩ = true := by simp [issuesTo, hm]
      have hn0 : 0 < S.n := by
        rcases Nat.eq_zero_or_pos S.n with h0 | h0
        · rw [h0] at hib; omega
        · exact h0
      have hmod := Nat.mod_lt I hn0
      let k : Kind S := ⟨I % S.n + 1, by omega⟩
      have hk0 : k.val ≠ 0 := by simp [k]
      have hnz : ¬ (S.δ = 1 ∧ I / S.n + S.δ = 0) := fun h => by
        rw [h.1] at h; exact absurd h.2 (Nat.succ_ne_zero _)
      have hit : itF X S k (I / S.n + S.δ) = r.id := by
        rw [hid]
        simp only [itF, hk0, ↓reduceIte]
        rw [opF_ld hnz, kOwner_ne hk0, prod_one, kPred_ne hk0, kIdx_ne hk0, Nat.add_sub_cancel]
        have : S.n * (I / S.n) + (k.val - 1) = I := by
          simp only [k, Nat.add_sub_cancel]
          exact Nat.div_add_mod I S.n
        rw [this, hI, nthEv_eq he hp]
      have hlt : I / S.n + S.δ < useBound X S := by
        have h1 := countP_take_le_length (issuesTo S.full) (X.tr S.cp) j
        have h3 : I / S.n ≤ I := Nat.div_le_self _ _
        have := lt_useBound_cp he
        omega
      refine ⟨(k, I / S.n + S.δ),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,
          Finset.mem_range.mpr hlt⟩, r, hr, hit.symm, hf, fun h => absurd h hk0, fun _ => ha⟩,
        hit.symm, ?_⟩
      simp only [ha, reduceCtorEq, exists_false]
    · let k : Kind S := ⟨i.val + 1, by omega⟩
      have hk0 : k.val ≠ 0 := by simp [k]
      have hit : itF X S k 0 = r.id := by
        rw [hid]
        simp only [itF, hk0, ↓reduceIte]
        rw [opF_pre_ne hk0 hδ1]
        have hi : (⟨k.val - 1, by have := k.isLt; omega⟩ : Fin S.n) = i :=
          Fin.ext (by simp [k])
        rw [hi]
      have hlt : 0 < useBound X S := by unfold useBound; omega
      refine ⟨(k, 0),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,
          Finset.mem_range.mpr hlt⟩, r, hr, hit.symm, hf, fun h => absurd h hk0, fun _ => ha⟩,
        hit.symm, ?_⟩
      simp only [ha, reduceCtorEq, exists_false]

/-- A fault-free arrival of the empty barrier is a counted notification. -/
theorem empty_item (H : Hyp L K A X S sc) {r : Record Ref} (hr : r ∈ X.objects S.empty)
    (hf : r.fault = none) {n tx : Nat} (ha : r.action = .arrive n tx) :
    n = 1 ∧ ∃ y ∈ SE X S, r.id = note X S y.1 0 y.2 := by
  classical
  obtain ⟨rfl, rfl, j, pc, sp, hid, he, hm, -, -⟩ := notify_source H hr ha
  set t := ((X.tr S.cm).take j).countP (commitsTo S.empty)
  have hp : commitsTo S.empty ⟨pc, .tc (.commit sp)⟩ = true := by simp [commitsTo, hm]
  have hit : note X S 0 0 t = r.id := by
    rw [hid]
    simp only [note, cmE, t]
    rw [nthEv_eq he hp]
  have hlt : t < useBound X S := by
    have h1 := countP_take_le_length (commitsTo S.empty) (X.tr S.cm) j
    have := lt_useBound_cm he
    omega
  exact ⟨rfl, (0, t), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,
    Finset.mem_range.mpr hlt⟩, r, hr, hit.symm, hf, ha⟩, hit.symm⟩

/-! ### The counted items' events -/

/-- A counted arrival item is the prologue's (use 0 of a preloaded slot), or the loader's, after
more successful polls of `empty` than its use less the preloaded use. -/
theorem item_arrival (H : Hyp L K A X S sc) {x : Kind S × Nat} (hk : x.1.val = 0) {r : Record Ref}
    (hr : r ∈ X.objects S.full) (hid : r.id = itF X S x.1 x.2)
    (ha : r.action = .arrive 1 S.tx) :
    (S.δ = 1 ∧ x.2 = 0 ∧ ∃ pc rel sc,
      X.get (opF X S x.1 x.2) = some ⟨pc, .arrive S.full S.tx 1 rel sc⟩) ∨
    (¬ (S.δ = 1 ∧ x.2 = 0) ∧ ∃ j pc rel sc, opF X S x.1 x.2 = (S.ap, j) ∧
      X.get (S.ap, j) = some ⟨pc, .arrive S.full S.tx 1 rel sc⟩ ∧
      ((X.tr S.ap).take j).countP (arrivesOn S.full) = x.2 - S.δ ∧
      x.2 - S.δ + 1 ≤ okPolls S.empty ((X.tr S.ap).take j)) := by
  obtain ⟨-, -, hs⟩ := arrival_source H hr ha
  have hit : itF X S x.1 x.2 = .thread (opF X S x.1 x.2) := by simp [itF, hk]
  rw [hit] at hid
  have hk0 : x.1 = ⟨0, by omega⟩ := Fin.ext hk
  by_cases hpz : S.δ = 1 ∧ x.2 = 0
  · left
    have h1' : opF X S x.1 x.2 = S.pArr := by
      rw [hk0]; simp [opF, hpz.1, hpz.2]
    refine ⟨hpz.1, hpz.2, ?_⟩
    rcases hs with ⟨j, pc, rel, sc, hid', he, hb⟩ | ⟨hδ, hid', pc, rel, sc, he⟩
    · exfalso
      rw [hid', h1'] at hid
      simp only [Ref.thread.injEq] at hid
      exact (H.pre_ne hpz.1).1 (by rw [← hid])
    · rw [h1']
      exact ⟨pc, rel, sc, he⟩
  · right
    refine ⟨hpz, ?_⟩
    have h2 : opF X S x.1 x.2 = (S.ap, nthEv X (arrivesOn S.full) S.ap (x.2 - S.δ)) := by
      rw [opF_ld hpz, hk0, kOwner_zero, prod_zero, kPred_zero, kIdx_zero]
    rcases hs with ⟨j, pc, rel, sc, hid', he, hb⟩ | ⟨hδ, hid', pc, rel, sc, he⟩
    · rw [hid', h2] at hid
      simp only [Ref.thread.injEq, Prod.mk.injEq, true_and] at hid
      subst hid
      have hc := (nthEv_spec_of_get he).2
      refine ⟨_, pc, rel, sc, h2, he, hc, ?_⟩
      unfold arrivals at hb
      rw [hc] at hb
      exact hb
    · exfalso
      rw [hid', h2] at hid
      simp only [Ref.thread.injEq] at hid
      exact (H.pre_ne hδ).1 (by rw [hid])

/-- A counted copy item is the prologue's (use 0 of a preloaded slot), or the loader's elected
lane's, within its budget. -/
theorem item_completion (H : Hyp L K A X S sc) {x : Kind S × Nat} (hk : x.1.val ≠ 0)
    {r : Record Ref} (hr : r ∈ X.objects S.full) (hid : r.id = itF X S x.1 x.2)
    (ha : r.action = .completeTx S.bytes) :
    (S.δ = 1 ∧ x.2 = 0 ∧ ∃ pc al sp, X.get (opF X S x.1 x.2) = some ⟨pc, .tensorIssue al sp⟩ ∧
      sp.mbar = S.full) ∨
    (¬ (S.δ = 1 ∧ x.2 = 0) ∧ ∃ j pc al sp, opF X S x.1 x.2 = (S.cp, j) ∧
      X.get (S.cp, j) = some ⟨pc, .tensorIssue al sp⟩ ∧ sp.mbar = S.full ∧
      ((X.tr S.cp).take j).countP (issuesTo S.full) = S.n * (x.2 - S.δ) + (x.1.val - 1) ∧
      x.2 - S.δ + 1 ≤ okPolls S.empty ((X.tr S.cp).take j)) := by
  obtain ⟨-, hs⟩ := completion_source H hr ha
  have hit : itF X S x.1 x.2 = .async (opF X S x.1 x.2) (.notify .load) := by simp [itF, hk]
  rw [hit] at hid
  by_cases hpz : S.δ = 1 ∧ x.2 = 0
  · left
    have h1' : opF X S x.1 x.2 =
        S.pCp ⟨x.1.val - 1, by have := x.1.isLt; omega⟩ := by
      simp [opF, hpz.1, hpz.2, hk]
    refine ⟨hpz.1, hpz.2, ?_⟩
    rcases hs with ⟨j, pc, al, sp, hid', he, hm, hb⟩ | ⟨hδ, i, pc, al, sp, hid', he, hm⟩
    · exfalso
      rw [hid', h1'] at hid
      simp only [Ref.async.injEq, and_true] at hid
      exact (H.pre_ne hpz.1).2 _ (congrArg Prod.fst hid).symm
    · rw [hid', h1'] at hid
      simp only [Ref.async.injEq, and_true] at hid
      rw [h1', ← hid]
      exact ⟨pc, al, sp, he, hm⟩
  · right
    refine ⟨hpz, ?_⟩
    have h2 : opF X S x.1 x.2 =
        (S.cp, nthEv X (issuesTo S.full) S.cp (S.n * (x.2 - S.δ) + (x.1.val - 1))) := by
      rw [opF_ld hpz, kOwner_ne hk, prod_one, kPred_ne hk, kIdx_ne hk]
    rcases hs with ⟨j, pc, al, sp, hid', he, hm, hb⟩ | ⟨hδ, i, pc, al, sp, hid', he, hm⟩
    · rw [hid', h2] at hid
      simp only [Ref.async.injEq, Prod.mk.injEq, and_true] at hid
      obtain ⟨-, hj⟩ := hid
      subst hj
      have hc := (nthEv_spec_of_get he).2
      refine ⟨_, pc, al, sp, h2, he, hm, hc, ?_⟩
      rw [hc] at hb
      have hxk := x.1.isLt
      exact Nat.lt_of_mul_lt_mul_left (a := S.n) (by omega)
    · exfalso
      rw [hid', h2] at hid
      simp only [Ref.async.injEq, and_true] at hid
      exact (H.pre_ne hδ).2 i (congrArg Prod.fst hid)

/-- The record of a counted item, and its event: the loader's event of its kind with the item's
count of earlier ones, after more successful polls of `empty` than the item's use less the
preloaded use; or the prologue's, for use 0 of a preloaded slot. -/
theorem SF_op (H : Hyp L K A X S sc) {x : Kind S × Nat} (hx : x ∈ SF X S) :
    (∃ (i : Nat) (r : Record Ref), (X.objects S.full)[i]? = some r ∧ r.id = itF X S x.1 x.2 ∧
      r.fault = none ∧ (x.1.val = 0 → r.action = .arrive 1 S.tx) ∧
      (x.1.val ≠ 0 → r.action = .completeTx S.bytes)) ∧
    (∃ e, X.get (opF X S x.1 x.2) = some e) ∧
    (S.δ = 1 ∧ x.2 = 0 ∨ ∃ j, opF X S x.1 x.2 = (S.prod (kOwner x.1), j) ∧
      x.2 - S.δ + 1 ≤ okPolls S.empty ((X.tr (S.prod (kOwner x.1))).take j)) := by
  obtain ⟨-, r, hr, hid, hf, h0, h1⟩ := Finset.mem_filter.mp hx
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  refine ⟨⟨i, r, hi, hid, hf, h0, h1⟩, ?_⟩
  by_cases hk : x.1.val = 0
  · rcases item_arrival H hk hr hid (h0 hk) with ⟨hδ, hu, pc, rel, sc, he⟩ |
      ⟨hpz, j, pc, rel, sc, hop, he, -, hb⟩
    · exact ⟨⟨_, he⟩, .inl ⟨hδ, hu⟩⟩
    · refine ⟨⟨_, by rw [hop]; exact he⟩, .inr ⟨j, ?_, ?_⟩⟩
      · rw [hop, kOwner_of_zero hk, prod_zero]
      · rw [kOwner_of_zero hk, prod_zero]
        exact hb
  · rcases item_completion H hk hr hid (h1 hk) with ⟨hδ, hu, pc, al, sp, he, -⟩ |
      ⟨hpz, j, pc, al, sp, hop, he, -, -, hb⟩
    · exact ⟨⟨_, he⟩, .inl ⟨hδ, hu⟩⟩
    · refine ⟨⟨_, by rw [hop]; exact he⟩, .inr ⟨j, ?_, ?_⟩⟩
      · rw [hop, kOwner_ne hk, prod_one]
      · rw [kOwner_ne hk, prod_one]
        exact hb

/-- The kind predicate holds of the item's event. -/
theorem SF_pred (H : Hyp L K A X S sc) {x : Kind S × Nat} (hx : x ∈ SF X S) {e : Event}
    (he : X.get (opF X S x.1 x.2) = some e) : kPred S x.1 e = true := by
  obtain ⟨-, r, hr, hid, hf, h0, h1⟩ := Finset.mem_filter.mp hx
  by_cases hk : x.1.val = 0
  · rcases item_arrival H hk hr hid (h0 hk) with ⟨hδ, hu, pc, rel, sc, he'⟩ |
      ⟨hpz, j, pc, rel, sc, hop, he', -, -⟩
    · rw [he'] at he
      cases he
      simp [kPred, hk, arrivesOn, sourceArrive]
    · rw [hop, he'] at he
      cases he
      simp [kPred, hk, arrivesOn, sourceArrive]
  · rcases item_completion H hk hr hid (h1 hk) with ⟨hδ, hu, pc, al, sp, he', hm⟩ |
      ⟨hpz, j, pc, al, sp, hop, he', hm, -, -⟩
    · rw [he'] at he
      cases he
      simp [kPred, hk, issuesTo, hm]
    · rw [hop, he'] at he
      cases he
      simp [kPred, hk, issuesTo, hm]

end
end PTX.SingleTmaRing
