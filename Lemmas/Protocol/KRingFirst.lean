-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.KindRing
import Lemmas.Protocol.PairTmaRing.ItemFacts

@[expose] public section

/-! # A ring's empty barrier before a producer's first release

A proof tool for the first use of a slot of `KRing`: the producers poll the empty barrier `E`
with offset 1, so their first poll passes on a fresh barrier. While producer `k` has no
successful poll of `E`, the barrier is still in phase 0 (`KRing.empty_first`): a completed phase
would hold a consumer's arrival, which follows the consumer's successful poll of `F`
(`polE`), which observes producer `k`'s arrival of use 0 (`full_observes`), which follows a
successful poll of `E` by producer `k` (`polF`). -/

namespace PTX.MbarRing

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

namespace KRing

variable {np nc nk : Nat}

/-- **Before producer `k`'s first successful poll of `E` the barrier `E` is in phase 0**, when
`E` is a unit object of the ring's consumers whose items are the ring's. -/
theorem empty_first (hX : Consistent L K A mem0 X) (R : KRing L K X np nc nk)
    (O : Unit.Obj X R.E nc R.cons 1) (hSE : ∀ x ∈ Unit.S X R.E R.cons, x ∈ R.SE) (hnc : 0 < nc)
    (k : Fin nk) (h0 : okPolls R.E (X.tr (R.prod (R.ownF k))) = 0) {st : MBarrier.State}
    (hst : MBarrier.stateBefore (X.objects R.E) (X.objects R.E).length = some st) :
    st.phase = 0 := by
  classical
  by_contra hne
  have hch := X.objects_checked hX R.E
  have hU := hch.card_unit_arrivals_phase O.noInval (n := nc) (q := 0)
    (fun p r c tx hr _ ha => (O.arrive_rec hr ha).1)
    (fun p st' _ hs' => PairTmaRing.expected_of_init hX O.init O.noInval hs') O.noIncrement
    le_rfl hst (by omega)
  obtain ⟨p, hp'⟩ := Finset.card_pos.mp (by rw [hU]; exact hnc)
  obtain ⟨-, r, tx, hr, ha, hf, -⟩ := Finset.mem_filter.mp hp'
  obtain ⟨x, hx, -⟩ := O.rec_S hr hf ha
  obtain ⟨i, -, -, hcnt⟩ := R.polE x (hSE x hx)
  have h4 : okPolls R.F ((X.tr (R.cons x.1)).take i) ≤ okPolls R.F (X.tr (R.cons x.1)) :=
    (List.take_sublist i _).countP_le
  obtain ⟨hS, -⟩ := R.full_observes hX (b := x.1) (u := 0) (by omega) k
  obtain ⟨i', -, -, hc'⟩ := R.polF _ hS
  have h2 : okPolls R.E ((X.tr (R.prod (R.ownF k))).take i') ≤
      okPolls R.E (X.tr (R.prod (R.ownF k))) := (List.take_sublist i' _).countP_le
  simp only at hc'
  omega

end KRing
end
end PTX.MbarRing
