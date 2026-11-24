-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.UnitRing
public import Lemmas.Protocol.UnitBlocker

@[expose] public section

/-! # The objects of a unit ring are gated

A proof tool. Both objects of a ring of two unit objects (`Unit.Ring`) are gated unit objects
(`Unit.Gate`), every producer partnered with every consumer, so the blocker of a gated object
(`Gate.blocked`) applies to their pollers.

* `full` (`fullGate`): a producer's arrival of use `s ≥ 1` is guarded by its polls of `empty`
  for the uses `1, …, s`, which every consumer's poll of `full` for use `s - 1` precedes
  (`Items.Ring.reach_op`).
* `empty` (`emptyGate`): a consumer's arrival of use `t` is guarded by its poll of `full` for use
  `t`, which observed the producer's arrival of use `t` (`Items.Ring.observes_full`), which the
  producer's poll of `empty` with `t` earlier ones guards. -/

namespace PTX.MbarRing.Unit

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

namespace Ring

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {full empty : Loc} {np nc : Nat} {prod : Fin np → Nat} {cons : Fin nc → Nat}

/-- The successful poll of `m` by `g` with `n` earlier ones, when it has more. -/
theorem nth_get {m : Loc} {g n : Nat} (h : n < okPolls m (X.tr g)) :
    ∃ pc p acq sc, X.get (g, MbarRing.Poll.nth X m g n) = some ⟨pc, .wait m p true acq sc⟩ ∧
      okPolls m ((X.tr g).take (MbarRing.Poll.nth X m g n)) = n :=
  MbarRing.Poll.nth_spec h

/-- **The full object is gated by the consumers' polls.** -/
theorem fullGate (hX : Consistent L K A mem0 X) (H : Ring L K A X full empty np nc prod cons) :
    Gate L K A X full np prod 0 (fun h => ∃ b, h = cons b) (fun _ h => ∃ b, h = cons b) where
  toObj := H.F
  cover _ hh := ⟨⟨0, H.F.pos⟩, hh⟩
  partner _ := ⟨cons ⟨0, H.E.pos⟩, _, rfl⟩
  gate := by
    intro a h i pc sc ⟨b, hb⟩ he hs
    subst hb
    have hgp := H.gateP he
    obtain ⟨hpres, hpath⟩ := (items hX H).reach_op hX.depAcyclic (a := a)
      (s := arrivals full ((X.tr (prod a)).take i)) (op := (prod a, i))
      (fun n _ hn => MbarRing.Poll.guard H.spins (len_of_get he) (by omega)) b
      (j := arrivals full ((X.tr (prod a)).take i) - 1) (by omega)
    obtain ⟨pcw, p, acq, scw, hw, hq⟩ := nth_get (present.mp hpres)
    exact ⟨_, pcw, p, acq, scw, hw, by omega, hpath⟩
  acq := by
    intro h j pc p acq sc ⟨b, hb⟩ he
    subst hb
    exact H.acqF he
  cta a h := by
    rintro ⟨b, rfl⟩
    exact H.cta a b

/-- **The empty object is gated by the producers' polls.** -/
theorem emptyGate (hX : Consistent L K A mem0 X) (H : Ring L K A X full empty np nc prod cons) :
    Gate L K A X empty nc cons 1 (fun h => ∃ a, h = prod a) (fun _ h => ∃ a, h = prod a) where
  toObj := H.E
  cover _ hh := ⟨⟨0, H.E.pos⟩, hh⟩
  partner _ := ⟨prod ⟨0, H.F.pos⟩, _, rfl⟩
  gate := by
    intro b h i pc sc ⟨a, ha⟩ he _
    subst ha
    set t := arrivals empty ((X.tr (cons b)).take i) with ht
    have hgc := H.gateC he
    -- the consumer's poll of `full` for use `t` observed the producer's arrival of use `t`
    have hn : t < okPolls full (X.tr (cons b)) := by
      have := MbarRing.Poll.okPolls_mono full (X.tr (cons b))
        (show i ≤ (X.tr (cons b)).length from (len_of_get he).le)
      rw [List.take_length] at this
      omega
    obtain ⟨hx, hobs⟩ := (items hX H).observes_full hX.depAcyclic (b := b) (j := t)
      (present.mpr hn) a
    have g2 : Resumes K X (cons b, MbarRing.Poll.nth X full (cons b) t) (cons b, i) :=
      MbarRing.Poll.guard H.spins (len_of_get he) (by omega)
    -- which the producer's poll of `empty` with `t` earlier ones guards
    obtain ⟨-, ⟨pca, sca, hea⟩, hu⟩ := H.F.S_rec hx
    have hb := H.gateP hea
    have hu' : arrivals full ((X.tr (prod a)).take (nthEv X (arrivesOn full) (prod a) t)) = t :=
      hu
    simp only at hb
    rw [hu'] at hb
    obtain ⟨j, pcw, p, acq, scw, -, hw, hjq⟩ := MbarRing.Poll.exists_nth (X := X) (m := empty)
      (g := prod a) (k := nthEv X (arrivesOn full) (prod a) t) (n := t) (by omega)
    have g1 : Resumes K X (prod a, MbarRing.Poll.nth X empty (prod a) t)
        (it X full prod a t) :=
      MbarRing.Poll.guard (m := empty) (g := prod a) (n := t) H.spins (len_of_get hea)
        (by omega)
    have hnth : MbarRing.Poll.nth X empty (prod a) t = j := by
      rw [← hjq, MbarRing.Poll.nth_eq hw]
    rw [hnth] at g1
    refine ⟨j, pcw, p, acq, scw, hw, by omega, ?_⟩
    exact ((Relation.TransGen.single (DepStep.of_resumes L g1)).tail
      (DepStep.of_witness L hobs)).tail (DepStep.of_resumes L g2)
  acq := by
    intro h j pc p acq sc ⟨a, ha⟩ he
    subst ha
    exact H.acqE he
  cta b h := by
    rintro ⟨a, rfl⟩
    have hc := H.cta a b
    exact ⟨hc.2.1, hc.1, hc.2.2.symm⟩

end Ring
end
end PTX.MbarRing.Unit
