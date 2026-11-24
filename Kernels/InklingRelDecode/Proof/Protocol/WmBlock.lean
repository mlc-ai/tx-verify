-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.WmPhase
public import Lemmas.Protocol.RecordCountPair
public import Lemmas.Protocol.MbarUnitTx

@[expose] public section

/-!
# Who blocks a lane of the MMA warp at its poll of `kv_ready`

`kv_ready s` is a transaction object of count 1: one arrival expecting `8 · 8192` bytes and eight
copies of `8192` bytes per use. A counted item of use `u ≥ 1` follows the consumer's poll for use
`u - 1` (`MbarRing.Items.Ring.reach_op` of `Ring.Kv.ring`), which found phase `u`
(`Ring.Kv.F_found`), so every counted item's use is at most the final phase (`use_le_phase`) and
the completed copies are at most `8 (phase + 1)` (`completed_le`). These are the premises of
`MbarRing.Blocker.tx_short` (`full_short`): with final phase `q`, either the arrival of use `q` is
missing (the arrival units are `q`) or it is in and fewer than `8 (q + 1)` copies completed.

* **The arrival is missing** (`arr_short`): every arrival of the loader's lane 0 leaves a counted
  record, and so does the prologue's arrival of use 0 of a preloaded slot once the loader has
  arrived (`pre_items`: the loader's item of use 1 follows the consumer's poll for use 0, which
  observed all items of use 0). So lane 0 has made at most `q - δ` arrivals.
* **A copy is missing** (`copy_short`): when every tensor copy has been notified (else an open
  `.tensor` obligation), every copy of the loader's copying lane leaves a counted completion, and
  so do the prologue's eight copies of use 0 of a preloaded slot. So the copying lane has issued
  fewer than `8 (q + 1 - δ)` copies.

`mma_kv_blocked` puts this together for a lane of the MMA warp at its poll of `kv_ready (i % 3)`
for a block `i ≥ num_pre` (the final phase is `q = i / 3`, `Wm.full_phase_le`,
`Wm.full_phase_ge`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Wm
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof AsyncCopy
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty)
open PTX.MBarrier hiding okPolls

noncomputable section
set_option maxRecDepth 100000

section
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {S : Ring.Kv.Slot}

/-- **A counted item's use is at most the final phase of the full barrier.** -/
theorem use_le_phase (hX : Consistent L K A mem0 X) (H : Ring.Kv.Hyp L K A X S)
    {x : Ring.Kv.Kind × Nat} (hx : x ∈ Ring.Kv.SF X S) {st : State}
    (hst : stateBefore (X.objects S.full) (X.objects S.full).length = some st) :
    x.2 ≤ st.phase := by
  rcases Nat.eq_zero_or_pos x.2 with h0 | hpos
  · omega
  obtain ⟨hw, -⟩ := (Ring.Kv.ring hX H).reach_op hX.depAcyclic (a := Ring.Kv.kOwner x.1)
    (s := x.2) (op := Ring.Kv.opF X S x.1 x.2)
    (fun n h1 hn => Ring.Kv.guardP H hx h1 hn) 0 (j := x.2 - 1) (by omega)
  have hlt : x.2 - 1 < okPolls S.full (X.tr S.cm) := MbarRing.Poll.nth_present.mp hw
  obtain ⟨i, w, st', hi, -, -, hst', hph, -⟩ := Ring.Kv.F_found hX H (b := 0) hlt
  have hil : i ≤ (X.objects S.full).length := (List.getElem?_eq_some_iff.mp hi).1.le
  obtain ⟨t, ht, hmono⟩ :=
    (X.objects_checked hX S.full).phase_mono H.full_noInval hil le_rfl hst'
  rw [hst] at ht
  cases ht
  omega

/-- The predicate of a completed copy record. -/
def doneCp (r : Record Ref) : Bool :=
  match r.action, r.fault with | .completeTx _, none => true | _, _ => false

/-- **The completed copies of the full barrier are at most eight per completed phase and the
current one.** -/
theorem completed_le (hX : Consistent L K A mem0 X) (H : Ring.Kv.Hyp L K A X S) {st : State}
    (hst : stateBefore (X.objects S.full) (X.objects S.full).length = some st) :
    completedTxCount (X.objects S.full) ≤ 8 * (st.phase + 1) := by
  classical
  have hnd : ((X.objects S.full).map Record.id).Nodup := (X.objects_checked hX S.full).1
  set T := (Ring.Kv.SF X S).filter (fun x => x.1.val ≠ 0 ∧ x.2 ≤ st.phase) with hT
  have h1 := countP_take_le_card hnd doneCp
    (i := (X.objects S.full).length) (T.image (fun x => Ring.Kv.itF X S x.1 x.2))
    (fun k _ r hr hp => by
      have hrm := List.mem_of_getElem? hr
      cases ha : r.action <;> cases hf : r.fault <;> simp only [doneCp, ha, hf] at hp <;>
        try cases hp
      rename_i n
      obtain ⟨x, hx, hid, hk⟩ := Ring.Kv.full_item H hrm hf (.inr ⟨n, ha⟩)
      have hk0 : x.1.val ≠ 0 := fun h => by
        obtain ⟨n', tx', h'⟩ := hk.mpr h
        rw [ha] at h'
        cases h'
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_filter.mpr ⟨hx, hk0, use_le_phase hX H hx hst⟩,
        hid.symm⟩)
  rw [List.take_length] at h1
  have h2 := Finset.card_image_le (s := T) (f := fun x => Ring.Kv.itF X S x.1 x.2)
  have hsub : T ⊆ (Finset.univ.filter (fun k : Ring.Kv.Kind => k.val ≠ 0)) ×ˢ
      Finset.range (st.phase + 1) := by
    intro x hx
    obtain ⟨-, hk, hu⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩,
      Finset.mem_range.mpr (by omega)⟩
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_range] at h3
  have h8 : (Finset.univ.filter (fun k : Ring.Kv.Kind => k.val ≠ 0)).card = 8 := by decide
  rw [h8] at h3
  have hcc : completedTxCount (X.objects S.full) = (X.objects S.full).countP doneCp := rfl
  omega

/-- **`MbarRing.Blocker.tx_short` for the full barrier.** -/
theorem full_short (hX : Consistent L K A mem0 X) (H : Ring.Kv.Hyp L K A X S) {st : State}
    (hst : stateBefore (X.objects S.full) (X.objects S.full).length = some st) :
    arrivalUnits (X.objects S.full) = st.phase ∨
      (arrivalUnits (X.objects S.full) = st.phase + 1 ∧
        completedTxCount (X.objects S.full) < 8 * (st.phase + 1)) := by
  have hbytes : expectedTxBytes (X.objects S.full) =
      8 * Ring.Kv.copyBytes * arrivalUnits (X.objects S.full) := by
    rw [← Ring.Kv.tx_balance]
    exact expectedTxBytes_unit fun r hr _ c tx ha => by
      obtain ⟨h1, h2, -⟩ := Ring.Kv.arrival_source H hr ha
      exact ⟨h1, h2⟩
  exact MbarRing.Blocker.tx_short (X.objects_checked hX S.full) H.full_noInval hst
    (PairTmaRing.expected_of_init hX H.full_init H.full_noInval hst) hbytes
    (fun r hr _ n ha => (Ring.Kv.completion_source H hr ha).1) (completed_le hX H hst)
    (Ring.Kv.full_noIncrement H)

/-- **The items of use 0 of a preloaded slot are counted** once a counted item of a later use
is. -/
theorem pre_items (hX : Consistent L K A mem0 X) (H : Ring.Kv.Hyp L K A X S)
    {x : Ring.Kv.Kind × Nat} (hx : x ∈ Ring.Kv.SF X S) (h1 : 1 ≤ x.2) (k : Ring.Kv.Kind) :
    (k, 0) ∈ Ring.Kv.SF X S := by
  obtain ⟨hw, -⟩ := (Ring.Kv.ring hX H).reach_op hX.depAcyclic (a := Ring.Kv.kOwner x.1)
    (s := x.2) (op := Ring.Kv.opF X S x.1 x.2)
    (fun n h1 hn => Ring.Kv.guardP H hx h1 hn) 0 (j := 0) (by omega)
  exact ((Ring.Kv.ring hX H).observes_full hX.depAcyclic (b := 0) hw k).1

/-- The arrival units of the full barrier are its counted arrival records. -/
theorem units_eq_countP (H : Ring.Kv.Hyp L K A X S) :
    arrivalUnits (X.objects S.full) = (X.objects S.full).countP countedArrive := by
  rw [arrivalUnits_eq_length (fun r hr c tx _ ha => (Ring.Kv.arrival_source H hr ha).1),
    List.countP_eq_length_filter]

/-- An arrival of a thread on the full barrier leaves a counted record. -/
theorem arrive_rec (hX : Consistent L K A mem0 X) (H : Ring.Kv.Hyp L K A X S) {h j pc tx cnt : Nat}
    {rel : Bool} {sc : MbarScope}
    (he : X.get (h, j) = some ⟨pc, .arrive S.full tx cnt rel sc⟩) :
    ∃ r ∈ X.objects S.full, r.id = .thread (h, j) ∧ countedArrive r = true := by
  have hact : objectAction X X.async S.full (Ref.thread (h, j)) = some (.arrive cnt tx) := by
    simp [objectAction, he]
  obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 S.full).2.2 (Ref.thread (h, j)) _ hact
  have hact' := ((hX.tma.2.2.1 S.full).2.1 r hr).1
  rw [hid, hact] at hact'
  have hra : r.action = .arrive cnt tx := (Option.some.inj hact').symm
  exact ⟨r, hr, hid,
    countedArrive_iff.mpr ⟨Ring.Kv.fault_free hX H (.inl rfl) hr, cnt, tx, hra⟩⟩

/-- A notified copy completing on the full barrier leaves a completed record. -/
theorem copy_rec (hX : Consistent L K A mem0 X) (H : Ring.Kv.Hyp L K A X S) {i : EvId}
    {pc al : Nat} {sp : TensorCopy.Spec}
    (he : X.get i = some ⟨pc, .tensorIssue al sp⟩) (hm : sp.mbar = S.full)
    (hn : ∃ obs, X.tensor i = some obs ∧ obs.effects.notified = true) :
    ∃ r ∈ X.objects S.full, r.id = .async i (.notify .load) ∧ doneCp r = true := by
  obtain ⟨obs, hobs, hnot⟩ := hn
  have hact : objectAction X X.async S.full (Ref.async i (.notify .load)) =
      some (.completeTx (TensorTransfer.bytes sp.descriptor)) := by
    simp [objectAction, he, hobs, hm, hnot]
  obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 S.full).2.2 _ _ hact
  have hact' := ((hX.tma.2.2.1 S.full).2.1 r hr).1
  rw [hid, hact] at hact'
  have hra : r.action = .completeTx (TensorTransfer.bytes sp.descriptor) :=
    (Option.some.inj hact').symm
  refine ⟨r, hr, hid, ?_⟩
  simp [doneCp, hra, Ring.Kv.fault_free hX H (.inl rfl) hr]

/-- **The arrival of use `q` is missing**: when the arrival units of the full barrier are `q`
(`q ≥ δ`, and `q ≥ 1` for a preloaded slot), lane 0 of the loader has made at most `q - δ`
arrivals on it. -/
theorem arr_short (hX : Consistent L K A mem0 X) (H : Ring.Kv.Hyp L K A X S) {q : Nat}
    (hu : arrivalUnits (X.objects S.full) = q) (hq : S.δ = 1 → 1 ≤ q) :
    arrivals S.full (X.tr S.ap) + S.δ ≤ q := by
  classical
  have hδ := H.δ_le
  rw [units_eq_countP H] at hu
  by_contra hlt
  push Not at hlt
  have hap : ∀ i, i ∈ indicesP (arrivesOn S.full) (X.tr S.ap) →
      ∃ r ∈ X.objects S.full, r.id = .thread (S.ap, i) ∧ countedArrive r = true := by
    intro i hi
    obtain ⟨e, he, hp⟩ := (mem_indicesP_iff _ _ i).mp hi
    obtain ⟨tx, cnt, rel, sc, hk⟩ := arrivesOn_form hp
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    subst hk
    exact arrive_rec hX H (h := S.ap) (j := i) he
  rcases Nat.eq_zero_or_pos S.δ with h0 | h1
  · have := countP_le_of_records (p := arrivesOn S.full) (es := X.tr S.ap) (q := countedArrive)
      (log := X.objects S.full) (fun i => Ref.thread (S.ap, i))
      (fun i j _ _ h => by simpa using h) hap
    unfold arrivals at hlt
    omega
  · have hδ1 : S.δ = 1 := by omega
    have hq1 := hq hδ1
    -- lane 0's first arrival and the prologue's arrival
    obtain ⟨e0, he0, hp0, -⟩ := nthEv_spec (X := X) (p := arrivesOn S.full) (g := S.ap) (n := 0)
      (by unfold arrivals at hlt; omega)
    obtain ⟨tx, cnt, rel, sc, hk⟩ := arrivesOn_form hp0
    obtain ⟨pc0, kd0⟩ := e0
    simp only at hk
    subst hk
    obtain ⟨r0, hr0, hid0, hc0⟩ := arrive_rec hX H he0
    obtain ⟨hf0, c0, tx0, ha0⟩ := countedArrive_iff.mp hc0
    obtain ⟨x, hx, hidx, hkx⟩ := Ring.Kv.full_item H hr0 hf0 (.inl ⟨c0, tx0, ha0⟩)
    have hx0 : x.1.val = 0 := hkx.mp ⟨c0, tx0, ha0⟩
    have hx1 : 1 ≤ x.2 := by
      by_contra hz
      have hz' : x.2 = 0 := by omega
      have hx0' : x.1 = ⟨0, by omega⟩ := Fin.ext hx0
      have : Ring.Kv.itF X S x.1 x.2 = .thread S.pArr := by
        rw [hx0', hz']
        unfold Ring.Kv.itF
        rw [ite_eq_left rfl, Ring.Kv.opF_pre_zero hδ1]
      rw [this, hid0] at hidx
      exact (H.pre_ne hδ1).1 (by simp only [Ref.thread.injEq] at hidx; rw [← hidx])
    have hpre := pre_items hX H hx hx1 ⟨0, by omega⟩
    obtain ⟨⟨ip, rp, hip, hidp, hfp, hap0, -⟩, -⟩ := Ring.Kv.SF_op H hpre
    have hidp' : rp.id = .thread S.pArr := by
      rw [hidp]
      dsimp only
      unfold Ring.Kv.itF
      rw [ite_eq_left rfl, Ring.Kv.opF_pre_zero hδ1]
    have := countP_le_of_records_pair (p := arrivesOn S.full) (es₁ := X.tr S.ap)
      (es₂ := [⟨pc0, .arrive S.full tx cnt rel sc⟩]) (q := countedArrive)
      (log := X.objects S.full) (fun i => Ref.thread (S.ap, i)) (fun _ => Ref.thread S.pArr)
      (fun i j _ _ h => by simpa using h)
      (fun i j hi hj _ => by
        rw [mem_indicesP_iff] at hi hj
        obtain ⟨_, hi', -⟩ := hi
        obtain ⟨_, hj', -⟩ := hj
        have := (List.getElem?_eq_some_iff.mp hi').1
        have := (List.getElem?_eq_some_iff.mp hj').1
        simp at *
        omega)
      (fun i j _ _ => by
        simp only [ne_eq, Ref.thread.injEq]
        intro h'
        exact (H.pre_ne hδ1).1 (by rw [← h']))
      hap
      (fun _ _ => ⟨rp, List.mem_of_getElem? hip, hidp',
        countedArrive_iff.mpr ⟨hfp, 1, _, hap0 (by rfl)⟩⟩)
    have hc1 :
        [(⟨pc0, .arrive S.full tx cnt rel sc⟩ : Event)].countP (arrivesOn S.full) = 1 := by
      simp [arrivesOn, sourceArrive]
    unfold arrivals at hlt
    omega

/-- **A copy of use `q` is missing**: when the arrival of use `q` is in and fewer than `8 (q + 1)`
copies completed (`q ≥ 1` for a preloaded slot), the loader's copying lane has issued fewer than
`8 (q + 1 - δ)` copies on the full barrier, or a tensor copy's notification is undelivered. -/
theorem copy_short (hX : Consistent L K A mem0 X) (H : Ring.Kv.Hyp L K A X S) {q : Nat}
    (hc : completedTxCount (X.objects S.full) < 8 * (q + 1)) (hq : S.δ = 1 → 1 ≤ q) :
    (X.tr S.cp).countP (issuesTo S.full) + 8 * S.δ < 8 * (q + 1) ∨
      Descent.Obl L X .tensor := by
  classical
  have hδ := H.δ_le
  by_cases hall : ∀ i mapAddress s, X.TensorIssue i mapAddress s →
      ∃ observation, X.tensor i = some observation ∧ observation.effects.notified = true
  swap
  · exact .inr hall
  left
  by_contra hge
  push Not at hge
  have hcnt : completedTxCount (X.objects S.full) = (X.objects S.full).countP doneCp := rfl
  rw [hcnt] at hc
  have hcp : ∀ i, i ∈ indicesP (issuesTo S.full) (X.tr S.cp) →
      ∃ r ∈ X.objects S.full, r.id = .async (S.cp, i) (.notify .load) ∧ doneCp r = true := by
    intro i hi
    obtain ⟨e, he, hp⟩ := (mem_indicesP_iff _ _ i).mp hi
    obtain ⟨pc, kd⟩ := e
    cases kd with
    | tensorIssue al sp =>
      have hm : sp.mbar = S.full := by simpa [issuesTo] using hp
      exact copy_rec hX H he hm (hall _ _ _ ⟨pc, he⟩)
    | _ => simp [issuesTo] at hp
  rcases Nat.eq_zero_or_pos S.δ with h0 | h1
  · have := countP_le_of_records (p := issuesTo S.full) (es := X.tr S.cp) (q := doneCp)
      (log := X.objects S.full) (fun i => Ref.async (S.cp, i) (.notify .load))
      (fun i j _ _ h => by simpa using h) hcp
    omega
  · have hδ1 : S.δ = 1 := by omega
    have hq1 := hq hδ1
    obtain ⟨e0, he0, hp0, -⟩ := nthEv_spec (X := X) (p := issuesTo S.full) (g := S.cp) (n := 0)
      (by omega)
    obtain ⟨pc0, kd0⟩ := e0
    cases kd0 with
    | tensorIssue al sp =>
      have hm : sp.mbar = S.full := by simpa [issuesTo] using hp0
      obtain ⟨r0, hr0, hid0, hd0⟩ := copy_rec hX H he0 hm (hall _ _ _ ⟨pc0, he0⟩)
      have hf0 : r0.fault = none := Ring.Kv.fault_free hX H (.inl rfl) hr0
      obtain ⟨n0, ha0⟩ : ∃ n, r0.action = .completeTx n := by
        unfold doneCp at hd0
        split at hd0
        · exact ⟨_, by assumption⟩
        · cases hd0
      obtain ⟨x, hx, hidx, hkx⟩ := Ring.Kv.full_item H hr0 hf0 (.inr ⟨n0, ha0⟩)
      have hxk : x.1.val ≠ 0 := fun h => by
        obtain ⟨_, _, h'⟩ := hkx.mpr h
        rw [ha0] at h'
        cases h'
      have hx1 : 1 ≤ x.2 := by
        by_contra hz
        have hz' : x.2 = 0 := by omega
        have : Ring.Kv.itF X S x.1 x.2 =
            .async (S.pCp ⟨x.1.val - 1, by have := x.1.isLt; omega⟩) (.notify .load) := by
          rw [hz']
          simp [Ring.Kv.itF, hxk, Ring.Kv.opF_pre_ne hxk hδ1]
        rw [this, hid0] at hidx
        simp only [Ref.async.injEq, and_true] at hidx
        exact (H.pre_ne hδ1).2 _ (by rw [← hidx])
      have hpre : ∀ i : Fin 8, ∃ r ∈ X.objects S.full,
          r.id = .async (S.pCp i) (.notify .load) ∧ doneCp r = true := by
        intro i
        have hk : (⟨i.val + 1, by omega⟩ : Ring.Kv.Kind).val ≠ 0 := by simp
        obtain ⟨⟨ip, rp, hip, hidp, hfp, -, hcp1⟩, -⟩ :=
          Ring.Kv.SF_op H (pre_items hX H hx hx1 ⟨i.val + 1, by omega⟩)
        refine ⟨rp, List.mem_of_getElem? hip, ?_, ?_⟩
        · rw [hidp]
          simp only [Ring.Kv.itF, hk, ↓reduceIte, Ring.Kv.opF_pre_ne hk hδ1]
          congr
        · simp [doneCp, hcp1 hk, hfp]
      have := countP_le_of_records_pair (p := issuesTo S.full) (es₁ := X.tr S.cp)
        (es₂ := List.replicate 8 ⟨pc0, .tensorIssue al sp⟩) (q := doneCp)
        (log := X.objects S.full) (fun i => Ref.async (S.cp, i) (.notify .load))
        (fun i => Ref.async (S.pCp ⟨i % 8, Nat.mod_lt _ (by decide)⟩) (.notify .load))
        (fun i j _ _ h => by simpa using h)
        (fun i j hi hj h => by
          rw [mem_indicesP_iff] at hi hj
          obtain ⟨_, hi', -⟩ := hi
          obtain ⟨_, hj', -⟩ := hj
          have hil := (List.getElem?_eq_some_iff.mp hi').1
          have hjl := (List.getElem?_eq_some_iff.mp hj').1
          simp only [List.length_replicate] at hil hjl
          simp only [Ref.async.injEq, and_true] at h
          have := H.pre_inj hδ1 h
          simp only [Fin.mk.injEq] at this
          rw [Nat.mod_eq_of_lt hil, Nat.mod_eq_of_lt hjl] at this
          exact this)
        (fun i j _ _ => by
          simp only [ne_eq, Ref.async.injEq, and_true]
          intro h'
          exact (H.pre_ne hδ1).2 _ (by rw [← h']))
        hcp
        (fun i _ => hpre _)
      have hc8 : (List.replicate 8 (⟨pc0, .tensorIssue al sp⟩ : Event)).countP
          (issuesTo S.full) = 8 := by
        rw [List.countP_replicate]
        simp [issuesTo, hm]
      omega
    | _ => simp [issuesTo] at hp0

end

section
variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}
  (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X)
include hpre hX hf hR

/-- **Who blocks a lane of the MMA warp at its poll of `kv_ready`.** A lane `g` at its poll of
`kv_ready (i % 3)` at the end of its trace, for a block `i ≥ num_pre`, whose object's final phase
has the poll's parity: lane 0 of the loader has not arrived for block `i`, or the loader's
copying lane has not issued all eight copies of block `i`, or a tensor copy's notification is
undelivered. -/
theorem mma_kv_blocked {S : Ring.Kv.Slot} (H : Ring.Kv.Hyp L kernel asms X S)
    {d : Mma.D} {P : Loader.Pro}
    (hσ : St Q L X g (X.tr g).length = some (some (.w (.mma d P)))) (hw : d.site = .kvWait)
    (hfull : S.full = kvReady L (g / L.block) (d.i % 3))
    (hempty : S.empty = kvEmpty L (g / L.block) (d.i % 3)) (hcw : SameWarp L S.cm g)
    (hδq : S.δ = 1 → 1 ≤ d.i / 3) {st : State}
    (hst : stateBefore (X.objects S.full) (X.objects S.full).length = some st)
    (hpar : st.phase % 2 = d.i / 3 % 2) :
    arrivals S.full (X.tr S.ap) + S.δ ≤ d.i / 3 ∨
      (X.tr S.cp).countP (issuesTo S.full) + 8 * S.δ < 8 * (d.i / 3 + 1) ∨
      Descent.Obl L X .tensor := by
  have hle := full_phase_le hpre hX hf hR H hσ hw hempty hcw hst
  have hge := full_phase_ge hpre hX hf hR H hσ hw hfull hst
  have hph : st.phase = d.i / 3 := by omega
  rcases full_short hX H hst with hu | ⟨-, hc⟩
  · rw [hph] at hu
    exact .inl (arr_short hX H hu hδq)
  · rw [hph] at hc
    exact .inr (copy_short hX H hc hδq)

end

end
end PTX.Kernels.InklingRelDecode.Proof.Wm
