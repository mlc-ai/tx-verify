-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderEvents

@[expose] public section

/-! # The loader's counts: one step

`counts_of` builds the ledger after one more event from the ledger before it and the event's
contribution to each count, given field by field; `ledger_step` (`LoaderCountsStep.lean`)
supplies these from the event's shape (`Ev`) and the site's transition, closing each count by
arithmetic (`cnt_arith`). A copy's position among its barrier's copies is the count of the
copies of its use's barrier so far (`copy_fact`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Work

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- At the role's start, before any of its counted events. -/
theorem Ledger.init {es : List Event}
    (h0 : ∀ e ∈ es, ∀ m, okPoll m e = false ∧ arrivesOn m e = false ∧ issuesTo m e = false) :
    Ledger L g ⟨.setMaxReg, 0, 0, 0, 1, 1⟩ es := by
  have hc : ∀ (p : Event → Bool), (∀ e ∈ es, p e = false) → es.countP p = 0 := fun p hp =>
    List.countP_eq_zero.mpr fun e he => by simp [hp e he]
  refine ⟨by simp [kvB, qB], fun s => ?_, fun st => ?_, fun _ s => ?_, fun _ st => ?_,
    fun e he m tx c rel sc hk => ?_, fun _ s => ?_, fun _ st => ?_, fun k e hk a sp hke => ?_,
    fun _ m => ⟨?_, ?_⟩, fun h => by simp at h, fun _ => by simp⟩
  · simp [okPolls, hc _ fun e he => (h0 e he _).1, kvPolled, slotCount]; omega
  · simp [okPolls, hc _ fun e he => (h0 e he _).1, qPolled]
  · simp [arrivals, hc _ fun e he => (h0 e he _).2.1, kvArrived, kvPolled, slotCount]; omega
  · simp [arrivals, hc _ fun e he => (h0 e he _).2.1, qArrived]
  · have := (h0 e he m).2.1
    rw [arrivesOn_arrive (show e = ⟨e.pc, .arrive m tx c rel sc⟩ by rw [← hk])] at this
    simp at this
  · rw [hc _ fun e he => (h0 e he _).2.2]
    have h1 : kvDone L g ⟨.setMaxReg, 0, 0, 0, 1, 1⟩ = 0 := rfl
    have h2 : kvPart ⟨.setMaxReg, 0, 0, 0, 1, 1⟩ = 0 := rfl
    have h3 : (0 + 5 - (s : Nat)) / 6 = 0 := by omega
    simp only [kvIssued, h1, h2, slotCount, ite_self, h3]
  · simp [hc _ fun e he => (h0 e he _).2.2, qIssued]
  · have hm := (h0 e (List.mem_of_getElem? hk) sp.mbar).2.2
    simp [issuesTo, hke] at hm
  · simp [arrivals, hc _ fun e he => (h0 e he _).2.1]
  · simp [hc _ fun e he => (h0 e he _).2.2]

/-- The copy fact of event `e` after the events `pre`: if it is a tensor copy, it is the copy
of a use of an item, and, when every election returned the lane, the copies before it on its
barrier number `CopyId.before`. -/
def CopyFact (L : Launch) (g : Nat) (pre : List Event) (e : Event) : Prop :=
  ∀ a sp, e.kind = .tensorIssue a sp → ∃ c : CopyId, CopyIs L g c a sp ∧
    (ElectLead L g pre → pre.countP (issuesTo sp.mbar) = c.before L)

/-- The copy fact of event `e` for the copy `c`: if it is a tensor copy, it is the copy `c`, and,
when every election returned the lane, the copies before it on its barrier number
`CopyId.before`. -/
def CopyFactOf (L : Launch) (g : Nat) (pre : List Event) (e : Event) (c : CopyId) : Prop :=
  ∀ a sp, e.kind = .tensorIssue a sp → CopyIs L g c a sp ∧
    (ElectLead L g pre → pre.countP (issuesTo sp.mbar) = c.before L)

theorem CopyFactOf.fact {pre : List Event} {e : Event} {c : CopyId}
    (h : CopyFactOf L g pre e c) : CopyFact L g pre e :=
  fun a sp hk => ⟨c, h a sp hk⟩

/-- The ledger after one more event, from its contribution to each count. -/
theorem counts_of {d d' : D} {pre : List Event} {e : Event} (hJ : Ledger L g d pre)
    (hring : d'.s = kvB L g d' % 6 ∧ d'.ph = (kvB L g d' / 6 + 1) % 2 ∧ d'.qp = qB L g d' % 2)
    (hkp : ∀ s : Fin 6, slotCount (kvPolled L g d') s = slotCount (kvPolled L g d) s +
      if okPoll (FBar.loc L (ctaOf L g) (.kvEmpty s)) e then 1 else 0)
    (hqp : ∀ st : Fin 2, qPolled L g d' st = qPolled L g d st +
      if okPoll (FBar.loc L (ctaOf L g) (.qEmpty st)) e then 1 else 0)
    (hka : ElectLead L g (pre ++ [e]) → ∀ s : Fin 6,
      (if rank L g = 0 then slotCount (kvArrived L g d') s else 0) =
        (if rank L g = 0 then slotCount (kvArrived L g d) s else 0) +
          if arrivesOn (FBar.loc L (ctaOf L g) (.kvFull s)) e then 1 else 0)
    (hqa : ElectLead L g (pre ++ [e]) → ∀ st : Fin 2,
      (if rank L g = 0 then qArrived L g d' st else 0) =
        (if rank L g = 0 then qArrived L g d st else 0) +
          if arrivesOn (FBar.loc L (ctaOf L g) (.qFull st)) e then 1 else 0)
    (htx : ∀ m tx c rel sc, e.kind = .arrive m tx c rel sc →
      (tx = 32768 ∧ ∃ s : Fin 6, m = FBar.loc L (ctaOf L g) (.kvFull s)) ∨
        (tx = 65536 ∧ ∃ st : Fin 2, m = FBar.loc L (ctaOf L g) (.qFull st)))
    (hki : ElectLead L g (pre ++ [e]) → ∀ s : Fin 6, kvIssued L g d' s = kvIssued L g d s +
      if issuesTo (FBar.loc L (evenCta L g) (.kvFull s)) e then 1 else 0)
    (hqi : ElectLead L g (pre ++ [e]) → ∀ st : Fin 2, qIssued L g d' st = qIssued L g d st +
      if issuesTo (FBar.loc L (evenCta L g) (.qFull st)) e then 1 else 0)
    (hq : ElectNonLead L g (pre ++ [e]) → ∀ m, arrivesOn m e = false ∧ issuesTo m e = false)
    (hel : (∃ u, d'.site = .arrive u) ∨ (∃ u j, d'.site = .copy u j) ∨ d'.site = .arriveTail →
      ¬ ElectNonLead L g (pre ++ [e]))
    (hst : d'.site = .setMaxReg → d'.i = 0 ∧ d'.t = 0 ∧ d'.s = 0 ∧ d'.ph = 1 ∧ d'.qp = 1)
    (hcp : CopyFact L g pre e) : Ledger L g d' (pre ++ [e]) := by
  obtain ⟨-, hkp0, hqp0, hka0, hqa0, htx0, hki0, hqi0, hcp0, hq0, -, -⟩ := hJ
  refine ⟨hring, fun s => ?_, fun st => ?_, fun hl s => ?_, fun hl st => ?_, ?_, fun hl s => ?_,
    fun hl st => ?_, ?_, fun hn m => ?_, hel, hst⟩
  · rw [okPolls_snoc, hkp0, hkp]
  · rw [okPolls_snoc, hqp0, hqp]
  · rw [arrivals_snoc, hka0 hl.of_snoc, hka hl]
  · rw [arrivals_snoc, hqa0 hl.of_snoc, hqa hl]
  · intro e' he' m tx c rel sc hk
    rcases List.mem_append.mp he' with he' | he'
    · exact htx0 e' he' m tx c rel sc hk
    · rw [List.mem_singleton.mp he'] at hk
      exact htx m tx c rel sc hk
  · rw [issues_snoc, hki0 hl.of_snoc, hki hl]
  · rw [issues_snoc, hqi0 hl.of_snoc, hqi hl]
  · intro k e' hk' a sp hke
    by_cases hk : k < pre.length
    · rw [List.getElem?_append_left hk] at hk'
      obtain ⟨c, hc, hcnt⟩ := hcp0 k e' hk' a sp hke
      refine ⟨c, hc, fun hl => ?_⟩
      rw [List.take_append_of_le_length hk.le] at hl ⊢
      exact hcnt hl
    · rw [List.getElem?_append_right (by omega)] at hk'
      have h0 : k - pre.length = 0 := by
        by_contra hne
        simp [hne] at hk'
      have hkl : k = pre.length := by omega
      subst hkl
      rw [h0] at hk'
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk'
      subst hk'
      rw [List.take_left]
      exact hcp a sp hke
  · obtain ⟨h1, h2⟩ := hq0 hn.of_snoc m
    obtain ⟨h3, h4⟩ := hq hn m
    rw [arrivals_snoc, issues_snoc, h1, h2, h3, h4]
    simp

/-- A KV full barrier's location, as `FBar.loc`. -/
macro "kv_loc" : tactic =>
  `(tactic| first | rfl | (simp only [FBar.loc, FBar.off, Loc.mk.injEq, true_and]; omega))

/-- Close a count equation: unfold the formulas and the barrier locations, then `omega`. -/
syntax "cnt_arith" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| cnt_arith $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      simp (config := { decide := true }) only [kvPolled, kvArrived, kvDone, kvPart, kvIssued,
        qPolled, qArrived, qIssued, kvB, qB, slotCount, FBar.loc, FBar.off, Loc.mk.injEq,
        true_and, and_true, Bool.true_and, Bool.false_and, decide_eq_true_eq, Bool.false_eq_true,
        ↓reduceIte, ↓reduceDIte, Nat.add_zero, Site.elC.injEq, Site.copy.injEq, reduceCtorEq,
        and_false, false_and, or_false, false_or, $extra,*]
      all_goals ((try split_ifs) <;> omega)))

/-- **The copy fact of a copy site**: the event is the copy `CopyIs` of the site's use, item and
trip, and, when every election returned the lane, the copies before it on its barrier number
`CopyId.before` (the barrier's copies so far, `kvIss` and `qIss`). -/
theorem copy_fact {d : D} {u : UseK} {j : Fin 2} {pre : List Event} {e : Event}
    (hJ : Ledger L g d pre) (hi : Inv L g d) (hev : Ev L g d e) (hs : d.site = .copy u j) :
    CopyFactOf L g pre e ⟨u, j, d.i, d.t⟩ := by
  intro a sp hk
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  have hR := hJ.ring
  have hone := hi.one u j (.inr rfl)
  have hs6 : s < 6 := hi.s
  have hev2 := uB_even L i
  obtain ⟨a', sp', hk', hci⟩ := hev
  rw [hk] at hk'
  cases hk'
  have hci := hci hR.1
  refine ⟨hci, fun hl => ?_⟩
  rw [hci.mbar]
  cases u <;> rcases Store.fin2_cases j with rfl | rfl <;>
    simp only [UseK.copies, Fin.isValue, Fin.val_one, Fin.val_zero] at hone <;> (try omega) <;>
    simp only [kvB, qB] at hR <;> have hN1 := ring_next hR.1 hR.2.1 <;>
    simp only [CopyId.bar, CopyId.use] <;> (first | rw [hJ.kvIss hl] | rw [hJ.qIss hl]) <;>
    cnt_arith [CopyId.before, CopyId.round, CopyId.bar, CopyId.use, FBar.copies, Fin.val_zero,
      Fin.val_one, Fin.isValue]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Loader
