-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.TmaUnitBlock
public import Lemmas.Protocol.MbarUnitTx

@[expose] public section

/-! # The completions of a one-CTA TMA unit object

Counting lemmas beside `Lemmas/Protocol/TmaUnitBlock.lean` (a proof tool, generic over the kernel):
the copies of an object that one thread issues bound its completed transactions
(`completions_le_issues`), and the phase of an object whose arrivals expect `n` copies of `B`
bytes each is at most its completions over `n` (`phase_le`). -/

namespace PTX.MbarRing.TmaUnitObject

open AsyncCopy MBarrier

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {X : Execution} {m : Loc}

/-- **The completed transactions of a one-CTA TMA unit object are at most the copies on it**, when
one thread issues all of them. -/
theorem completions_le_issues {prod : Nat → Prop} (hX : Consistent L K A mem0 X)
    (o : TmaUnitObject X m prod) {z : Nat}
    (hz : ∀ i pc a sp, X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar = m → i.1 = z) :
    completedTxCount (X.objects m) ≤ (X.tr z).countP (Flow.issuesTo m) := by
  classical
  have hnd : ((X.objects m).map Record.id).Nodup := (hX.tma.2.2.1 m).1.1
  have h := countP_take_le_card hnd
    (fun r => match r.action, r.fault with | .completeTx _, none => true | _, _ => false)
    (i := (X.objects m).length)
    ((indicesP (Flow.issuesTo m) (X.tr z)).image
      fun k => Ref.async (z, k) (Part.notify .load)) ?_
  · rw [List.take_length] at h
    exact h.trans (Finset.card_image_le.trans (countP_eq_card _ _).ge)
  · intro k _ r hr hp
    cases o.source r (List.mem_of_getElem? hr) with
    | init ha => simp [ha] at hp
    | poll ha => simp [ha] at hp
    | arrive _ _ _ ha => simp [ha] at hp
    | @tensor i pc a sp hid he hm ha =>
      obtain ⟨g, j⟩ := i
      obtain rfl : g = z := hz _ _ _ _ he hm
      rw [hid]
      rw [Finset.mem_image]
      refine ⟨j, (mem_indicesP_iff _ _ j).mpr ⟨_, he, ?_⟩, rfl⟩
      simp [Flow.issuesTo, hm]

/-- **The phase of a one-CTA TMA unit object** whose arrivals expect `n` copies of `B` bytes: `n`
completions per phase. -/
theorem phase_le {prod : Nat → Prop} (hX : Consistent L K A mem0 X) (o : TmaUnitObject X m prod)
    {st : State} (hs : stateBefore (X.objects m) (X.objects m).length = some st) {n B : Nat}
    (hB : 0 < B)
    (hbytes : ∀ r ∈ X.objects m, r.fault = none → ∀ c tx, r.action = .arrive c tx → tx = n * B)
    (hu : UniformCompletedTx (X.objects m) B) :
    n * st.phase ≤ completedTxCount (X.objects m) := by
  have hck := X.objects_checked hX m
  have hni := o.noInval
  rcases Nat.eq_zero_or_pos st.phase with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  obtain ⟨q, hq, s, s', hsq, hsc, hs', hsc'⟩ :=
    hck.crossing hni le_rfl hs (c := st.phase - 1) (by omega)
  obtain ⟨r, hr⟩ : ∃ r, (X.objects m)[q]? = some r := ⟨_, List.getElem?_eq_getElem hq⟩
  have hb := hck.phase_advance_transaction_bytes hni hr hsq hs' (by omega)
  have hmem : ∀ {x}, x ∈ (X.objects m).take (q + 1) → x ∈ X.objects m := List.mem_of_mem_take
  rw [expectedTxBytes_unit (T := n * B) (fun r hr hf c tx ha => ⟨by
      cases o.source r (hmem hr) with
      | init h | poll h | tensor _ _ _ h => rw [ha] at h; cases h
      | arrive _ _ _ h => rw [ha] at h; cases h; rfl, hbytes r (hmem hr) hf c tx ha⟩),
    completedTxBytes_eq_unit_mul_count (fun r hr => hu r (hmem hr))] at hb
  have hex := PairTmaRing.expected_of_init hX o.init hni hs'
  obtain ⟨hp, hun⟩ := (hck.accounted hni (show q + 1 ≤ (X.objects m).length by omega)).2 s' hs'
  rw [hex] at hp hun
  have hinc : incrementsBefore (X.objects m) (q + 1) = 0 :=
    incrementsBefore_eq_zero _ o.noIncrement _
  rw [hinc] at hp hun
  have hmono : completedTxCount ((X.objects m).take (q + 1)) ≤ completedTxCount (X.objects m) := by
    unfold completedTxCount
    exact (List.take_sublist _ _).countP_le
  have hcu : n * arrivalUnits ((X.objects m).take (q + 1)) =
      completedTxCount ((X.objects m).take (q + 1)) := by
    refine Nat.eq_of_mul_eq_mul_left hB ?_
    rw [← hb]; ring
  have hle : st.phase ≤ arrivalUnits ((X.objects m).take (q + 1)) := by
    simp only [unitsBefore] at hun
    omega
  exact (Nat.mul_le_mul_left n hle).trans (hcu.le.trans hmono)

end
end PTX.MbarRing.TmaUnitObject
