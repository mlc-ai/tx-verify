-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Protocol.Mma
public import Lemmas.Protocol.ObjectIndex
public import Lemmas.Protocol.ObjectSource

@[expose] public section

/-! # `tc_gemm`: the mbarrier operations

Every mbarrier operation is on `bar0` or `bar1` (`object_action_cases`). On `bar0`: thread 0's
initialization and its arrival expecting 4352 bytes, the two copies' complete-tx of 4096 and 256
bytes, thread 0's polls (`CopyAction`). On `bar1`: thread 0's initialization, the commit's
arrive-on at rank 0, every thread's polls (`MmaAction`). -/

namespace PTX.Kernels.TcGemm.Proof
open PTX PTX.Proof AsyncCopy MBarrier
noncomputable section
variable {L : Launch} {A B D S : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
  {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}

/-- Source-derived operations on the operand-copy barrier. -/
def CopyAction (X : Execution) (P : Nat → Par) (id : Ref) (act : Action) : Prop :=
  (id = .thread (0, 2) ∧ act = .init 1) ∨
  (id = .thread (0, 5) ∧ act = .arrive 1 4352) ∨
  (id = .async (0, 6) (.notify .copy) ∧ act = .completeTx 4096 ∧
    (X.async.copies (0, 6)).notified = true) ∨
  (id = .async (0, 7) (.notify .copy) ∧ act = .completeTx 256 ∧
    (X.async.copies (0, 7)).notified = true) ∨
  (∃ j ok, hd 0 < j ∧ j ≤ hd 0 + 1 + (P 0).n0 ∧
    id = .thread (0, j) ∧ act = .pollParity 0 ok ∧ (ok = true ↔ j = hd 0 + 1 + (P 0).n0))

/-- Source-derived operations on the MMA completion barrier. -/
def MmaAction (X : Execution) (P : Nat → Par) (id : Ref) (act : Action) : Prop :=
  (id = .thread (0, 3) ∧ act = .init 1) ∨
  (id = .async (0, hd 0 + 3 + (P 0).n0) (.tcNotify 0) ∧ act = .arrive 1 0 ∧
    (0 : Fin 16) ∈ X.tcNotified (0, hd 0 + 3 + (P 0).n0)) ∨
  (∃ g < 128, ∃ j ok, tl g (P g) ≤ j ∧ j ≤ tl g (P g) + (P g).n1 ∧
    id = .thread (g, j) ∧ act = .pollParity 0 ok ∧ (ok = true ↔ j = tl g (P g) + (P g).n1))

section
variable (hW : Wit A B D S X P m u)
include hW

/-- No object history invalidates its object. -/
theorem Wit.objects_noInval (hX : Consistent L kernel [] mem0 X) (mb : Loc) :
    NoInval (X.objects mb) :=
  AsyncCopy.objects_noInval hX.tma.2.2.1
    (fun e _ ⟨_, h⟩ => by obtain ⟨g, j⟩ := e; exact hW.no_inval h) mb

theorem object_action_cases {mb : Loc} {id : Ref} {act : Action}
    (ha : objectAction X X.async mb id = some act) :
    (mb = bar0 S ∧ CopyAction X P id act) ∨ (mb = bar1 S ∧ MmaAction X P id act) := by
  cases id with
  | thread e =>
    obtain ⟨g, j⟩ := e
    unfold objectAction at ha
    cases he : X.get (g, j) with
    | none => simp [he] at ha
    | some ev =>
      obtain ⟨pc, kind⟩ := ev
      cases kind <;> simp only [he] at ha
      all_goals try contradiction
      case mbInval mb' => exact (hW.no_inval he).elim
      case asyncArrive mb' noinc => exact (hW.no_asyncArrive he).elim
      case mbInit mb' n =>
        obtain ⟨_, _, rfl, rfl, hc⟩ := hW.mbInit he
        split_ifs at ha with hm
        cases ha
        rcases hc with ⟨rfl, hm'⟩ | ⟨rfl, hm'⟩
        · exact .inl ⟨hm.symm.trans hm', .inl ⟨rfl, rfl⟩⟩
        · exact .inr ⟨hm.symm.trans hm', .inl ⟨rfl, rfl⟩⟩
      case arrive mb' tx count rel sc =>
        obtain ⟨_, _, rfl, rfl, hm', rfl, rfl⟩ := hW.arrive he
        split_ifs at ha with hm
        cases ha
        exact .inl ⟨hm.symm.trans hm', .inr (.inl ⟨rfl, rfl⟩)⟩
      case wait mb' parity ok acq sc =>
        obtain ⟨hg, _, rfl, hc⟩ := hW.wait he
        split_ifs at ha with hm
        cases ha
        rcases hc with ⟨rfl, hlo, hhi, hm', hok⟩ | ⟨hlo, hhi, hm', hok⟩
        · exact .inl ⟨hm.symm.trans hm', .inr (.inr (.inr (.inr
            ⟨j, ok, hlo, hhi, rfl, rfl, hok⟩)))⟩
        · exact .inr ⟨hm.symm.trans hm', .inr (.inr
            ⟨g, hg, j, ok, hlo, hhi, rfl, rfl, hok⟩)⟩
  | async e p =>
    obtain ⟨g, j⟩ := e
    cases p <;> simp only [objectAction] at ha
    all_goals try contradiction
    case notifyCopy =>
      cases hs : issuedBy X (g, j) with
      | none => simp [hs] at ha
      | some spec =>
        obtain ⟨pc, he⟩ := issuedBy_some.mp hs
        obtain ⟨_, _, rfl, hc⟩ := hW.bulk he
        simp only [hs] at ha
        change (if spec.completion = .mbarrier mb ∧ (X.async.copies (0, j)).notified = true then
          some (.completeTx spec.dst.size) else none) = some act at ha
        split_ifs at ha with hn
        cases ha
        rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have hm : bar0 S = mb := by simpa [specA, bulkSpec] using hn.1
          exact .inl ⟨hm.symm, .inr (.inr (.inl ⟨rfl, rfl, hn.2⟩))⟩
        · have hm : bar0 S = mb := by simpa [specB, bulkSpec] using hn.1
          exact .inl ⟨hm.symm, .inr (.inr (.inr (.inl ⟨rfl, rfl, hn.2⟩)))⟩
    case tcNotify rank =>
      cases he : X.get (g, j) with
      | none => simp [he] at ha
      | some ev =>
        obtain ⟨pc, kind⟩ := ev
        cases kind <;> simp only [he] at ha
        all_goals try contradiction
        rename_i tk
        cases tk <;> try { exact (Option.some_ne_none _ ha.symm).elim }
        rename_i s
        obtain ⟨_, _, rfl, rfl, rfl⟩ := hW.commit he
        change (if TcCommit.target (commitSpec S) rank = some mb ∧
          rank ∈ X.tcNotified (0, hd 0 + 3 + (P 0).n0) then
          some (.arrive 1 0) else none) = some act at ha
        split_ifs at ha with hn
        cases ha
        obtain ⟨rfl, rfl⟩ := commitSpec_target hn.1
        exact .inr ⟨rfl, .inr (.inl ⟨rfl, rfl, hn.2⟩)⟩

    case arriveOn =>
      cases he : X.get (g, j) with
      | none => simp [he] at ha
      | some ev =>
        obtain ⟨pc, kind⟩ := ev
        cases kind <;> simp only [he] at ha
        all_goals try contradiction
        exact (hW.no_asyncArrive he).elim
    case notifyLoad =>
      cases he : X.get (g,j) with
      | none => simp [he] at ha
      | some ev =>
        obtain ⟨pc,kind⟩ := ev
        have hk := hW.tcBulk _ _ _ he
        cases kind <;> simp_all [Kind.isTcBulk]
    case notifyCta =>
      cases he : X.get (g,j) with
      | none => simp [he] at ha
      | some ev =>
        obtain ⟨pc,kind⟩ := ev
        have hk := hW.tcBulk _ _ _ he
        cases kind <;> simp_all [Kind.isTcBulk]

end
section
variable (hX : Consistent L kernel [] mem0 X) (hW : Wit A B D S X P m u)
include hX hW

omit hX in
/-- A real object instruction is in the source prefix, before any trailing fault. -/
theorem object_thread_index {mb : Loc} {e : EvId} {act : Action}
    (ha : objectAction X X.async mb (.thread e) = some act) : e.1 < 128 ∧ e.2 < m e.1 := by
  obtain ⟨ev, he⟩ := objectAction_present ha
  obtain ⟨hg, ⟨hj, _⟩ | ⟨_, pc, f, hev, _⟩⟩ := hW.get he
  · exact ⟨hg, hj⟩
  · rw [hev] at he
    simp [objectAction, he] at ha

theorem object_record_issuer_lt {mb : Loc} {r : Record Ref} (hr : r ∈ X.objects mb) :
    r.id.issuer.1 < 128 ∧ r.id.issuer.2 < m r.id.issuer.1 := by
  have ha := ((hX.tma.2.2.1 mb).2.1 r hr).1
  have hp := objectAction_present ha
  cases hid : r.id with
  | thread e =>
    rw [hid] at ha
    simpa [hid, Ref.issuer] using object_thread_index hW ha
  | async e p =>
    rw [hid] at hp
    obtain ⟨ev, he⟩ := asyncPresent_issuer hX.effectValidity hp
    obtain ⟨hg, ⟨hj, _⟩ | ⟨_, pc, f, hev, _⟩⟩ := hW.get he
    · simpa [hid, Ref.issuer] using And.intro hg hj
    · rw [hev] at he
      exact (plain_no_async hX.effectValidity he (by rfl) p hp).elim

theorem object_record_cases {mb : Loc} {r : Record Ref} (hr : r ∈ X.objects mb) :
    (mb = bar0 S ∧ CopyAction X P r.id r.action) ∨
    (mb = bar1 S ∧ MmaAction X P r.id r.action) :=
  object_action_cases hW (((hX.tma.2.2.1 mb).2.1 r hr).1)

theorem copy_record_cases {r : Record Ref} (hr : r ∈ X.objects (bar0 S)) :
    CopyAction X P r.id r.action := by
  rcases object_record_cases hX hW hr with ⟨_, hc⟩ | ⟨hn, _⟩
  · exact hc
  · simp [bar0, bar1] at hn

theorem mma_record_cases {r : Record Ref} (hr : r ∈ X.objects (bar1 S)) :
    MmaAction X P r.id r.action := by
  rcases object_record_cases hX hW hr with ⟨hn, _⟩ | ⟨_, hc⟩
  · simp [bar0, bar1] at hn
  · exact hc

theorem objects_other {mb : Loc} (h0 : mb ≠ bar0 S) (h1 : mb ≠ bar1 S) :
    X.objects mb = [] := by
  cases hl : X.objects mb with
  | nil => rfl
  | cons r rest =>
    rcases object_record_cases hX hW (r := r) (by rw [hl]; simp) with ⟨h, _⟩ | ⟨h, _⟩
    · exact (h0 h).elim
    · exact (h1 h).elim

end
end
end PTX.Kernels.TcGemm.Proof
