-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.CpAsyncPhase
public import Lemmas.Protocol.MbarCommitObj
public import Lemmas.Protocol.CountNth
public import Lemmas.Flow.NotCommit
public import Lemmas.Protocol.PollLe
public import Lemmas.Protocol.BarTable
public import Lemmas.Order.WaitOrderEnables

@[expose] public section

/-! # A one-CTA ring whose full barrier counts no-increment arrive-ons, bounded by commits

A proof tool, the counterpart of `PairTmaRing/CommitBound.lean` for a ring of one CTA whose full
barrier `F` completes each use by `n` `cp.async.mbarrier.arrive.noinc` arrive-ons
(`MbarRing.NoIncObject X F n`) instead of thread arrivals, and whose empty barrier `E` is
completed by a consumer's Tensor Core commits alone (lane T1's request for tml-fa4's K/V ring).

* `NoIncObject.phase_mul_le_units`: `n` times the full barrier's phase is at most its arrival
  units (no increments, so every completed phase holds `n` units);
* `NoIncObject.units_le_sum`: its arrival units are at most the producers' arrive-ons on it, when
  every arrive-on on it is a producer's (each unit is the record of one arrive-on event);
* `commitObj_phase_le_commits`: the empty barrier's phase is at most the consumer's commits to
  it, when the consumer issues every commit that targets it, each with one target;
* `full_phase_le_commits`: from the producers' arrive-ons bounded by their successful polls of
  the empty barrier plus `d` (the kernel's per-lane count), and those polls by the empty
  barrier's phase plus one (`okPolls_le_phase`), the full barrier's phase is at most the
  consumer's commits plus `d + 1`. -/

namespace PTX.MbarRing

open AsyncCopy MBarrier Flow

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- An event that is a no-increment arrive-on of `m`. -/
def arriveOnTo (m : Loc) (e : Event) : Bool :=
  match e.kind with
  | .asyncArrive m' true => decide (m' = m)
  | _ => false

theorem arriveOnTo_of {m : Loc} {e : Event} {pc : Nat} (h : e = ⟨pc, .asyncArrive m true⟩) :
    arriveOnTo m e = true := by
  subst h; simp [arriveOnTo]

/-- A list's length is the sum, over the indices of an injective `prod`, of the lengths of its
fibres under `own`, when every element's `own` is some `prod a`. -/
theorem length_eq_sum_fibres {α : Type} {P : Nat} (prod : Fin P → Nat)
    (hinj : Function.Injective prod) (own : α → Nat) :
    ∀ l : List α, (∀ x ∈ l, ∃ a, own x = prod a) →
      l.length = ∑ a, (l.filter (fun x => decide (own x = prod a))).length
  | [], _ => by simp
  | x :: l, h => by
    rw [List.length_cons, length_eq_sum_fibres prod hinj own l
      (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    obtain ⟨a0, ha0⟩ := h x List.mem_cons_self
    have hc : ∀ a, ((x :: l).filter (fun y => decide (own y = prod a))).length =
        (l.filter (fun y => decide (own y = prod a))).length + if a0 = a then 1 else 0 := by
      intro a
      by_cases e : a0 = a
      · subst e; simp [ha0]
      · have : own x ≠ prod a := fun h' => e (hinj (ha0.symm.trans h'))
        simp [this, e]
    simp only [hc, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- The thread of a record's reference. -/
def refThread : Ref → Nat
  | .thread i => i.1
  | .async i _ => i.1

/-- The event index of a record's reference. -/
def refIndex : Ref → Nat
  | .thread i => i.2
  | .async i _ => i.2

namespace NoIncObject

variable {m : Loc} {n : Nat}

/-- **`n` times the phase is at most the arrival units.** -/
theorem phase_mul_le_units (hX : Consistent L K A mem0 X) (o : NoIncObject X m n) {st : State}
    (hst : stateBefore (X.objects m) (X.objects m).length = some st) :
    n * st.phase ≤ arrivalUnits (X.objects m) := by
  have hch := X.objects_checked hX m
  obtain ⟨hp, hacc⟩ := (hch.accounted o.noInval le_rfl).2 st hst
  simp only [unitsBefore, List.take_length] at hacc
  rw [o.noIncrement] at hp hacc
  have he := PairTmaRing.expected_of_init hX o.init o.noInval hst
  rw [he] at hp hacc
  have : n * (st.phase + 1) = n * st.phase + n := Nat.mul_succ _ _
  omega

/-- **The arrival units are at most the producers' arrive-ons**, when every arrive-on on the
object is one of the producers `prod`. -/
theorem units_le_sum (hX : Consistent L K A mem0 X) (o : NoIncObject X m n) {P : Nat}
    (prod : Fin P → Nat) (hinj : Function.Injective prod)
    (hsrc : ∀ i, X.AsyncArrive i m true → ∃ a, i.1 = prod a) :
    arrivalUnits (X.objects m) ≤ ∑ a, (X.tr (prod a)).countP (arriveOnTo m) := by
  classical
  have hunit : ∀ r ∈ X.objects m, ∀ c tx, r.fault = none → r.action = .arrive c tx → c = 1 := by
    intro r hr c tx _ ha
    cases o.source r hr with
    | init h | poll h => rw [ha] at h; cases h
    | arriveOn _ _ _ h => rw [ha] at h; cases h; rfl
  rw [arrivalUnits_eq_length hunit]
  set xs := (X.objects m).filter countedArrive
  have hnd : xs.Nodup := (List.Nodup.of_map _ (hX.tma.2.2.1 m).1.1).filter _
  -- every counted record is a producer's arrive-on
  have hrec : ∀ x ∈ xs, ∃ a j pc, x.id = .async (prod a, j) .arriveOn ∧
      X.get (prod a, j) = some ⟨pc, .asyncArrive m true⟩ := by
    intro x hx
    obtain ⟨hxm, hxc⟩ := List.mem_filter.mp hx
    obtain ⟨-, c', tx, ha⟩ := countedArrive_iff.mp hxc
    cases o.source x hxm with
    | init h | poll h => rw [ha] at h; cases h
    | @arriveOn i hid hi _ _ =>
      obtain ⟨a, ha'⟩ := hsrc i hi
      obtain ⟨pc, he⟩ := hi
      obtain ⟨i1, i2⟩ := i
      simp only at ha'
      subst ha'
      exact ⟨a, i2, pc, hid, he⟩
  rw [length_eq_sum_fibres prod hinj (fun x => refThread x.id) xs (fun x hx => by
    obtain ⟨a, j, pc, hid, -⟩ := hrec x hx
    exact ⟨a, by simp [hid, refThread]⟩)]
  refine Finset.sum_le_sum fun a _ => ?_
  have hle := MbarRing.Slot.length_le_countP_take
    (xs.filter (fun x => decide (refThread x.id = prod a))) (hnd.filter _) (X.tr (prod a))
    (arriveOnTo m) (X.tr (prod a)).length (fun x => refIndex x.id) ?_ ?_
  · rw [List.take_length] at hle
    exact hle
  · intro x hx
    obtain ⟨hxs, hxa⟩ := List.mem_filter.mp hx
    obtain ⟨a', j, pc, hid, he⟩ := hrec x hxs
    have : prod a' = prod a := by simpa [hid, refThread] using hxa
    rw [this] at he
    simp only [hid, refIndex]
    refine ⟨len_of_get he, ?_⟩
    change (X.get (prod a, j)).any _ = true
    rw [he]
    simp [arriveOnTo]
  · intro x hx y hy hxy
    obtain ⟨hxs, hxa⟩ := List.mem_filter.mp hx
    obtain ⟨hys, hya⟩ := List.mem_filter.mp hy
    obtain ⟨a1, j1, -, hid1, -⟩ := hrec x hxs
    obtain ⟨a2, j2, -, hid2, -⟩ := hrec y hys
    have h1 : prod a1 = prod a := by simpa [hid1, refThread] using hxa
    have h2 : prod a2 = prod a := by simpa [hid2, refThread] using hya
    have hj : j1 = j2 := by simpa [hid1, hid2, refIndex] using hxy
    have hid : x.id = y.id := by rw [hid1, hid2, h1, h2, hj]
    exact hX.record_eq (List.mem_of_mem_filter hxs) (List.mem_of_mem_filter hys) hid

end NoIncObject

/-- **The phase of an object completed by one consumer's commits is at most its commits to
it**: no thread arrives on it and no `cp.async.mbarrier.arrive` names it, so every counted
arrival is a commit's notification; the consumer `c` issues every commit that targets it, each
naming it as its barrier and with one target rank on it. -/
theorem commitObj_phase_le_commits (hX : Consistent L K A mem0 X) {m : Loc}
    (hu : UnitTx (X.objects m) 0) (hni : NoInval (X.objects m))
    (harr : ∀ {g i pc tx cnt : Nat} {rel : Bool} {sc : MbarScope},
      X.get (g, i) ≠ some ⟨pc, .arrive m tx cnt rel sc⟩)
    (hcpa : ∀ {i : EvId} {pc : Nat} {m' : Loc} {noinc : Bool},
      X.get i = some ⟨pc, .asyncArrive m' noinc⟩ → m' ≠ m)
    (c : Nat)
    (hby : ∀ {i : EvId} {pc : Nat} {sp : TcCommit.Spec} {rank : Fin 16},
      X.get i = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp rank = some m →
        i.1 = c ∧ sp.mbar = m ∧ ∀ rank', TcCommit.target sp rank' = some m → rank' = rank)
    {st : State} (hst : stateBefore (X.objects m) (X.objects m).length = some st) :
    st.phase ≤ (X.tr c).countP (commitsTo m) := by
  classical
  have hch := X.objects_checked hX m
  have hinc : incrementsBefore (X.objects m) (X.objects m).length = 0 :=
    Blocker.noIncrement_of_no_cpAsyncArrive hX hcpa
  obtain ⟨hp, hacc⟩ := (hch.accounted hni le_rfl).2 st hst
  simp only [unitsBefore, List.take_length] at hacc
  rw [hinc, hu.expected _ st hst] at hp hacc
  have hunit : ∀ r ∈ X.objects m, ∀ c' tx, r.fault = none → r.action = .arrive c' tx → c' = 1 :=
    fun r hr c' tx hf ha => (hu.arrive r hr hf c' tx ha).1
  rw [arrivalUnits_eq_length hunit] at hacc
  set xs := (X.objects m).filter countedArrive
  have hnd : xs.Nodup := (List.Nodup.of_map _ (hX.tma.2.2.1 m).1.1).filter _
  have hrec : ∀ x ∈ xs, ∃ j pc sp rank, x.id = .async (c, j) (.tcNotify rank) ∧
      X.get (c, j) = some ⟨pc, .tc (.commit sp)⟩ ∧ TcCommit.target sp rank = some m := by
    intro x hx
    obtain ⟨hxm, hxc⟩ := List.mem_filter.mp hx
    obtain ⟨-, c', tx, ha⟩ := countedArrive_iff.mp hxc
    cases record_source hX.tma.2.2.1 hxm with
    | arrive _ he _ => exact (harr he).elim
    | increment _ he _ => exact (hcpa he rfl).elim
    | arriveOn _ he hm _ _ => exact (hcpa he hm).elim
    | @commit i pc sp rank hid he ht _ =>
      obtain ⟨hi, -, -⟩ := hby he ht
      obtain ⟨i1, i2⟩ := i
      simp only at hi
      subst hi
      exact ⟨i2, pc, sp, rank, hid, he, ht⟩
    | init _ _ ha' | inval _ _ ha' | wait _ _ ha' | tensor _ _ _ ha' | bulk _ _ _ _ ha'
    | clc _ _ _ _ ha' => rw [ha] at ha'; cases ha'
  have hle := MbarRing.Slot.length_le_countP_take xs hnd (X.tr c) (commitsTo m)
    (X.tr c).length (fun x => refIndex x.id) ?_ ?_
  · rw [List.take_length] at hle
    omega
  · intro x hx
    obtain ⟨j, pc, sp, rank, hid, he, ht⟩ := hrec x hx
    simp only [hid, refIndex]
    refine ⟨len_of_get he, ?_⟩
    change (X.get (c, j)).any _ = true
    rw [he]
    simp [commitsTo, (hby he ht).2.1]
  · intro x hx y hy hxy
    obtain ⟨j1, pc1, sp1, r1, hid1, he1, ht1⟩ := hrec x hx
    obtain ⟨j2, pc2, sp2, r2, hid2, he2, ht2⟩ := hrec y hy
    have hj : j1 = j2 := by simpa [hid1, hid2, refIndex] using hxy
    rw [← hj, he1] at he2
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at he2
    obtain ⟨-, hsp⟩ := he2
    rw [← hsp] at ht2
    have hr : r2 = r1 := (hby he1 ht1).2.2 r2 ht2
    have hid : x.id = y.id := by rw [hid1, hid2, hr, hj]
    exact hX.record_eq (List.mem_of_mem_filter hx) (List.mem_of_mem_filter hy) hid

/-- **The full barrier's phase is at most the consumer's commits plus `d + 1`.** The full
barrier `F` is a no-increment object of count `n > 0` whose arrive-ons are the producers'
(`prod`, `n` distinct threads); each producer's arrive-ons on `F` are at most its successful
polls of the empty barrier `E` plus `d`, and those polls at most `E`'s phase plus one
(`okPolls_le_phase`); `E`'s phase is at most consumer `c`'s commits to it
(`commitObj_phase_le_commits`). -/
theorem full_phase_le_commits (hX : Consistent L K A mem0 X) {F E : Loc} {n d c : Nat}
    (o : NoIncObject X F n) (hn : 0 < n) (prod : Fin n → Nat) (hinj : Function.Injective prod)
    (hsrc : ∀ i, X.AsyncArrive i F true → ∃ a, i.1 = prod a)
    {stE : State} (hlane : ∀ a, (X.tr (prod a)).countP (arriveOnTo F) ≤
      Flow.okPolls E (X.tr (prod a)) + d)
    (hpoll : ∀ a, Flow.okPolls E (X.tr (prod a)) ≤ stE.phase + 1)
    (hE : stE.phase ≤ (X.tr c).countP (commitsTo E))
    {stF : State} (hst : stateBefore (X.objects F) (X.objects F).length = some stF) :
    stF.phase ≤ (X.tr c).countP (commitsTo E) + 1 + d := by
  have h1 := o.phase_mul_le_units hX hst
  have h2 := o.units_le_sum hX prod hinj hsrc
  have h3 : ∑ a, (X.tr (prod a)).countP (arriveOnTo F) ≤
      ∑ _a : Fin n, ((X.tr c).countP (commitsTo E) + 1 + d) :=
    Finset.sum_le_sum fun a _ => by have := hlane a; have := hpoll a; omega
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h3
  have h4 : n * stF.phase ≤ n * ((X.tr c).countP (commitsTo E) + 1 + d) := by omega
  exact Nat.le_of_mul_le_mul_left h4 hn

end
end PTX.MbarRing
