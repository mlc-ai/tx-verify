-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.KindRing
public import Lemmas.Protocol.GatedFaults
public import Lemmas.Protocol.NoIncUnits
import Lemmas.Flow.NthEv

@[expose] public section

/-! # The gates of a ring of kinds, and its fault-freedom

A proof tool. In a ring of kinds (`KRing`) an event of a producer after `u + 1` polls of the empty
barrier (`1 ≤ u`) follows, in the dependency order, every consumer's poll of the full barrier with
`u - 1` earlier ones (`gateF`), and an event of a consumer after `t + 1` polls of the full barrier
(`1 ≤ t`) every producer's poll of the empty barrier with `t` earlier ones (`gateE`). Unlike
`KRing.reachF`, the event need not be a counted unit's, so the gates hold of an update before its
record is known to be fault-free: they are the gates of `Unit.Gated` and `Notify.Gated`, and of
the no-increment object (`NoInc.fault_free`). -/

namespace PTX.MbarRing
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

namespace KRing

variable {np nc nk : Nat}

/-- **A producer's event after `u + 2` polls of `E`** follows every consumer's poll of `F` with `u`
earlier ones. -/
theorem gateF (hX : Consistent L K A mem0 X) (R : KRing L K X np nc nk) {a : Fin np} {i u : Nat}
    (hi : i < (X.tr (R.prod a)).length)
    (h : u + 1 + 1 ≤ okPolls R.E ((X.tr (R.prod a)).take i)) (b : Fin nc) :
    Relation.TransGen (DepStep L K X) (.thread (R.cons b, Poll.nth X R.F (R.cons b) u), true)
      (.thread (R.prod a, i), false) := by
  have hg := Poll.guard R.spins hi h
  have hpres : X.RefPresent (.thread (R.prod a, Poll.nth X R.E (R.prod a) (u + 1))) :=
    Round.Slot.present_of_guard hg
  obtain ⟨hyS, hyp⟩ := ((R.ring hX).content_empty hX.depAcyclic (a := a) (n := u) hpres).2 b
  exact ((((Relation.TransGen.single
      (DepStep.of_resumes L ((R.ring hX).guardM a (b, u) hyS u le_rfl))).trans_left
    ((R.ring hX).issue a (b, u) hyS)).tail
    (DepStep.of_witness L ((R.ring hX).obsE a (u + 1) (by omega) hpres (b, u) hyS hyp))).tail
    (DepStep.of_resumes L hg))

/-- **A consumer's event after `t + 1` polls of `F`** follows every producer's poll of `E` with
`t` earlier ones, when `1 ≤ t`. -/
theorem gateE (hX : Consistent L K A mem0 X) (R : KRing L K X np nc nk) {b : Fin nc} {i t : Nat}
    (hi : i < (X.tr (R.cons b)).length)
    (h : t + 1 ≤ okPolls R.F ((X.tr (R.cons b)).take i)) (ht : 1 ≤ t) (a : Fin np) :
    Relation.TransGen (DepStep L K X) (.thread (R.prod a, Poll.nth X R.E (R.prod a) t), true)
      (.thread (R.cons b, i), false) := by
  have hg := Poll.guard R.spins hi h
  have hpres : X.RefPresent (.thread (R.cons b, Poll.nth X R.F (R.cons b) t)) :=
    Round.Slot.present_of_guard hg
  obtain ⟨k, hk⟩ := R.cover a
  obtain ⟨hxS, hxp⟩ := ((R.ring hX).content_full hX.depAcyclic (b := b) (j := t) hpres).2 k
  have hgp := (R.ring hX).guardP 0 (k, t) hxS t ht le_rfl
  have hgp' : Resumes K X (R.prod a, Poll.nth X R.E (R.prod a) t) (R.opF k t) := hk ▸ hgp
  exact ((((Relation.TransGen.single (DepStep.of_resumes L hgp')).trans_left
    ((R.ring hX).issueF 0 (k, t) hxS)).tail
    (DepStep.of_witness L ((R.ring hX).obsF b t hpres (k, t) hxS hxp))).tail
    (DepStep.of_resumes L hg))

end KRing

/-- **A no-increment object is fault-free** when each arrive-on of use `s ≥ 1` follows, in the
dependency order, a successful poll with `s + δ - 1` earlier ones of a selected thread. -/
theorem NoInc.fault_free (hX : Consistent L K A mem0 X) {m : Loc} {N δ : Nat} (hδ : δ ≤ 1)
    {prod : Fin N → Nat} (hinj : Function.Injective prod) (o : NoIncObject X m N)
    (hsrc : ∀ i, X.AsyncArrive i m true → ∃ a, i.1 = prod a) {selected : Nat → Prop}
    (hpar : ∀ {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
      selected g → X.get (g, k) = some ⟨pc, .wait m p true acq sc⟩ →
        p % 2 = (okPolls m ((X.tr g).take k) + δ) % 2)
    (hgate : ∀ {a : Fin N} {i pc : Nat}, X.get (prod a, i) = some ⟨pc, .asyncArrive m true⟩ →
      X.async.arrived (prod a, i) = true → 1 ≤ ((X.tr (prod a)).take i).countP (arriveOnTo m) →
        ∃ h, selected h ∧
        Relation.TransGen (DepStep L K X) (.thread (h, Poll.nth X m h
          (((X.tr (prod a)).take i).countP (arriveOnTo m) - 1 + δ)), true)
          (.async (prod a, i) .arriveOn, false)) :
    ∀ r ∈ X.objects m, r.fault = none := by
  classical
  have hcard : (Finset.univ.image prod).card = N := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  let lab : Ref → Nat × Nat := fun x =>
    (x.issuer.1, ((X.tr x.issuer.1).take x.issuer.2).countP (arriveOnTo m))
  have hrec : ∀ r ∈ X.objects m, ∀ c tx, r.action = .arrive c tx → c = 1 ∧ tx = 0 ∧
      ∃ a i pc, r.id = .async (prod a, i) .arriveOn ∧
        X.get (prod a, i) = some ⟨pc, .asyncArrive m true⟩ ∧
          X.async.arrived (prod a, i) = true := by
    intro r hr c tx ha
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨rfl, rfl, ⟨g, i⟩, hid, ⟨pc, hi⟩, harr⟩ := o.arrive_source hk ha
    obtain ⟨a, hga⟩ := hsrc (g, i) ⟨pc, hi⟩
    simp only at hga
    subst hga
    exact ⟨rfl, rfl, a, i, pc, hid, hi, harr⟩
  refine fault_free_of_selected_gate hX hδ (Finset.univ.image prod) lab
    (by rw [hcard]; exact o.init) o.noInval hpar ?_ ?_ ?_ ?_ ?_
  · intro r hr n ha
    cases o.source r hr with
    | init ha' | poll ha' | arriveOn _ _ _ ha' => rw [ha] at ha'; cases ha'
  · intro r hr ha
    cases o.source r hr with
    | init ha' | poll ha' | arriveOn _ _ _ ha' => rw [ha] at ha'; cases ha'
  · intro r hr c tx ha
    obtain ⟨h1, h2, a, i, pc, hid, -⟩ := hrec r hr c tx ha
    exact ⟨h1, h2, by rw [hid]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)⟩
  · intro r hr r' hr' c tx c' tx' ha ha' hl
    obtain ⟨-, -, a, i, pc, hid, he, -⟩ := hrec r hr c tx ha
    obtain ⟨-, -, a', i', pc', hid', he', -⟩ := hrec r' hr' c' tx' ha'
    rw [hid, hid'] at hl ⊢
    obtain ⟨h1, h2⟩ := Prod.mk.inj hl
    change prod a = prod a' at h1
    obtain rfl := hinj h1
    have : i = i' := nthEv_unique he (arriveOnTo_of rfl) he' (arriveOnTo_of rfl) h2
    rw [this]
  · intro r hr c tx ha hpos
    obtain ⟨-, -, a, i, pc, hid, he, harr⟩ := hrec r hr c tx ha
    rw [hid] at hpos ⊢
    have hpos' : 1 ≤ ((X.tr (prod a)).take i).countP (arriveOnTo m) := hpos
    obtain ⟨h, hsel, hp⟩ := hgate he harr hpos'
    obtain ⟨pc', p, acq, sc, hw, hcnt⟩ := poll_of_path hp
    exact ⟨h, _, pc', p, acq, sc, hsel, hw, by
      rw [hcnt]
      change _ = ((X.tr (prod a)).take i).countP (arriveOnTo m) + δ
      omega, hp⟩

end
end PTX.MbarRing
