-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Bound
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Time
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
public import Lemmas.Flow.NotRegister

@[expose] public section

/-! # The register requests on the time table

Every warpgroup's first state is its `setmaxnreg` site (warpgroup 0 at pc 103, warpgroup 1's
head at pc 1842, warpgroup 2 at pc 2606), the only states of the warpgroups at the glued measure
`fragBase` (`low_req`: their places are `0`); the startup's states are below it. The glued measure
never falls along a followed thread and rises at every counted event (`Common/Bound.lean`), so:

* `low_or_req`: a state of a prefix is at most at `fragBase`, or the prefix has a request;
* `req_low`: a request is fired at measure `fragBase` and time `regT L g` (`100` for warpgroups 0
  and 1, `132` for warpgroup 2); the state after it is later (`req_after`);
* `req_first`: a request is its thread's first (a second one would be fired at a higher measure);
* `low_time`: a state at most at `fragBase` is no later than `regT L g`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The time of a warp's register request: `100` (warpgroups 0 and 1), `132` (warpgroup 2). -/
def regT (L : Launch) (g : Nat) : Nat := if wgOf L g = 2 then 132 else 100

/-! ### The sites at place 0 -/

theorem wg0_place0 {d : Wg0.Control.D} (h : Wg0.place d = 0) : d.site = Wg0.Site.smr := by
  have h1 : 0 < wg0Blk0 ∧ 0 < wg0EpiBlk0 ∧ 0 < Wg0.endPlace := by decide
  obtain ⟨h1, h2, h3⟩ := h1
  unfold Wg0.place at h
  cases hs : d.site <;> simp only [hs, Wg0.regPlace, Wg0.Site.reg, Wg0.Site.ord, w0ArrL] at h <;>
    first | rfl | omega

theorem deq_place0 {d : Dequant.Control.D} (h : Dequant.place d = 0) :
    d.site = Dequant.Site.smr := by
  have h1 : 0 < deqBlk0 ∧ 0 < Dequant.endPlace := by decide
  unfold Dequant.place at h
  cases hs : d.site <;> simp only [hs] at h <;> first | rfl | omega

theorem wg1_time0 {s : Wg1.Site} (h : Wg1.time s = 0) : s = .smr := by
  cases s <;> simp only [Wg1.time] at h <;> first | rfl | omega

theorem wg0_pc103 {s : Wg0.Site} (h : s.pc = 103) : s = .smr := by
  cases s with
  | sld a k => revert a k h; decide
  | pst k | pld k => revert k h; decide
  | ost c | rld c | rldw c | rst c | rstw c | old c | oldw c | ofpx c | obar c | oel c
    | otma c => revert c h; decide
  | ost2 c k => revert c k h; decide
  | _ => revert h; decide

theorem deq_pc2606 {s : Dequant.Site} (h : s.pc = 2606) : s = .smr := by
  cases s with
  | scale r => revert r h; decide
  | raw r s | store r s => revert r s h; decide
  | _ => revert h; decide

/-- The static check: the `setmaxnreg` instructions are at pcs 103, 1842 and 2606. -/
private theorem smr_code : kernel.code.zipIdx.all (fun x =>
    !setMaxRegOp x.1.op || x.2 == 103 || x.2 == 1842 || x.2 == 2606) = true := by
  decide +kernel

theorem smr_pc {p : Nat} {ins : Instr} (hc : kernel.code[p]? = some ins)
    (hs : setMaxRegOp ins.op = true) : p = 103 ∨ p = 1842 ∨ p = 2606 := by
  have h := List.all_eq_true.mp smr_code (ins, p) (List.mem_zipIdx_iff_getElem?.mpr hc)
  simp only [hs, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h
  omega

/-! ### The measure at the warpgroups' first states -/

theorem init_measure (i : Entry) (n : Cls → Nat) :
    measure P L g (.inr ⟨.inl i, (frag P L g i).init⟩, n) = fragBase := by
  cases i <;> rfl

/-- **A state at most at `fragBase`** is no later than the warp's request. -/
theorem low_time {k : Nat} {σ : (thread P L g).D}
    (hσ : Frame.stateAt (thread P L) X g k = some (some σ)) (hJ : (table P L).J g σ)
    (hm : measure P L g σ ≤ fragBase) : time P L g σ ≤ regT L g := by
  obtain ⟨s, n⟩ := σ
  rcases s with d | ⟨i | r, d⟩
  · have hx : Startup.exitOf d = none := by simpa [startupEnter] using glue_gate hσ
    have := Startup.time_lt hx
    simp only [time, regT]
    split_ifs <;> omega
  · cases i with
    | wg0 =>
      obtain ⟨-, -, -, hw⟩ := hJ
      have h0 : Wg0.place d = 0 := by
        simp only [measure, fragMeasure, wg0Measure, Wg0.measure] at hm
        have : 0 < Wg0.top := by simp only [Wg0.top]; omega
        omega
      have hT : regT L g = 100 := by rw [regT, hw]; rfl
      simp only [time, fragTime, wg0Time, Wg0.time, h0, hT, roleBase]
      omega
    | dequant =>
      obtain ⟨-, -, -, hw⟩ := hJ
      have h0 : Dequant.place d = 0 := by
        simp only [measure, fragMeasure, dequantMeasure, Dequant.measure] at hm
        have : 0 < Dequant.top := by simp only [Dequant.top]; omega
        omega
      have hT : regT L g = 132 := by rw [regT, hw]; rfl
      simp only [time, fragTime, dequantTime, Dequant.time, h0, hT, idleBase, roleBase]
      omega
    | wg1 =>
      obtain ⟨-, -, -, hw⟩ := hJ
      rcases d with s | ⟨j | r, d⟩
      · have hT : regT L g = 100 := by rw [regT, hw]; rfl
        simp only [measure, fragMeasure, wg1Measure, Wg1.measure] at hm
        simp only [time, fragTime, wg1Time, hT, roleBase]
        omega
      · cases j <;> simp only [measure, fragMeasure, wg1Measure] at hm <;> omega
      · simp only [measure, fragMeasure, wg1Measure] at hm
        omega
  · exact hJ.elim

/-- **A state above `fragBase`** is later than the warp's request. -/
theorem high_time {σ : (thread P L g).D} (hJ : (table P L).J g σ)
    (hm : fragBase < measure P L g σ) : regT L g < time P L g σ := by
  obtain ⟨s, n⟩ := σ
  rcases s with d | ⟨i | r, d⟩
  · have := Startup.measure_le d
    simp only [measure, fragBase] at hm
    omega
  · cases i with
    | wg0 =>
      obtain ⟨-, -, -, hw⟩ := hJ
      have h0 : 0 < Wg0.place d := by
        simp only [measure, fragMeasure, wg0Measure, Wg0.measure] at hm
        omega
      have hT : regT L g = 100 := by rw [regT, hw]; rfl
      simp only [time, fragTime, wg0Time, Wg0.time, hT, roleBase]
      omega
    | dequant =>
      obtain ⟨-, -, -, hw⟩ := hJ
      have h0 : 0 < Dequant.place d := by
        simp only [measure, fragMeasure, dequantMeasure, Dequant.measure] at hm
        omega
      have hT : regT L g = 132 := by rw [regT, hw]; rfl
      simp only [time, fragTime, dequantTime, Dequant.time, hT, idleBase, roleBase]
      omega
    | wg1 =>
      obtain ⟨-, -, -, hw⟩ := hJ
      have hT : regT L g = 100 := by rw [regT, hw]; rfl
      rw [hT]
      rcases d with s | ⟨j | r, d⟩
      · simp only [measure, fragMeasure, wg1Measure, Wg1.measure] at hm
        simp only [time, fragTime, wg1Time, roleBase]
        omega
      · cases j <;> simp only [time, fragTime, wg1Time, mmaTime, tmaTime, indexTime, idleBase,
          roleBase] <;> try omega
        cases d <;> simp only [idleTime, Wg1.itime, idleBase, roleBase, endSlot, loopBase,
          stride, blockCap] <;> omega
      · simp only [time, fragTime, wg1Time, idleBase, roleBase]
        omega
  · exact hJ.elim

/-! ### Along the trace -/

/-- A state after an event follows a state before it. -/
theorem prev_state {k : Nat} {e : Event} {σ' : (thread P L g).D} (he : (X.tr g)[k]? = some e)
    (h : Frame.stateAt (thread P L) X g (k + 1) = some (some σ')) :
    ∃ σ, Frame.stateAt (thread P L) X g k = some (some σ) ∧
      (thread P L g).next σ e = some (some σ') := by
  rw [Frame.stateAt_succ he] at h
  cases hk : Frame.stateAt (thread P L) X g k with
  | none => rw [hk] at h; cases h
  | some o =>
    cases o with
    | none => rw [hk] at h; simp [Code.toMachine] at h
    | some σ => rw [hk] at h; exact ⟨σ, rfl, h⟩

/-- **The measure does not fall along the trace.** -/
theorem meas_mono (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
    (hnu : ¬ HasUb X) (hg : g < L.threads) {i : Nat} {σ : (thread P L g).D}
    (hσ : Frame.stateAt (thread P L) X g i = some (some σ)) :
    ∀ j, i + j ≤ (X.tr g).length → ∀ σ', Frame.stateAt (thread P L) X g (i + j) = some (some σ') →
      measure P L g σ ≤ measure P L g σ' := by
  intro j
  induction j with
  | zero =>
    intro _ σ' h
    rw [Nat.add_zero, hσ] at h
    cases h
    exact Nat.le_refl _
  | succ j ih =>
    intro hl σ' h
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[i + j]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨σm, hm, hn⟩ := prev_state he (by rw [← Nat.add_assoc] at h; exact h)
    exact (ih (by omega) σm hm).trans
      (measure_raise hX hFw hg he hm (noUb_kind hnu he) hn).1

/-- **At measure `fragBase` a warpgroup's event is its request.** -/
theorem low_req (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {k : Nat} {e : Event} {σ : (thread P L g).D}
    (he : X.get (g, k) = some e) (hσ : Frame.stateAt (thread P L) X g k = some (some σ))
    (hm : measure P L g σ = fragBase) (hs : ∀ d n, σ ≠ (.inl d, n)) :
    SetMaxNReg.isRequest e = true := by
  obtain ⟨σ0, hσ0, hJ, -, hev, -⟩ := ev_at hp hX hFw he (noUb_kind hnu he)
  rw [hσ] at hσ0
  cases hσ0
  have hreq : ∀ inc n inst, e.kind = .setMaxReg inc n inst → SetMaxNReg.isRequest e = true := by
    intro inc n inst hk
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    subst hk
    rfl
  obtain ⟨s, n⟩ := σ
  rcases s with d | ⟨i | r, d⟩
  · exact absurd rfl (hs d n)
  · cases i with
    | wg0 =>
      have h0 : Wg0.place d = 0 := by
        simp only [measure, fragMeasure, wg0Measure, Wg0.measure] at hm
        have : 0 < Wg0.top := by simp only [Wg0.top]; omega
        omega
      have hsite := wg0_place0 h0
      have hev' : wg0Ev P L g d e := hev
      unfold wg0Ev at hev'
      obtain ⟨-, hk⟩ := hev'
      unfold Wg0.EvK at hk
      rw [hsite] at hk
      obtain ⟨inst, hk⟩ := hk
      exact hreq _ _ _ hk
    | dequant =>
      have h0 : Dequant.place d = 0 := by
        simp only [measure, fragMeasure, dequantMeasure, Dequant.measure] at hm
        have : 0 < Dequant.top := by simp only [Dequant.top]; omega
        omega
      have hsite := deq_place0 h0
      have hev' : Dequant.Ev L g d e := hev
      obtain ⟨-, hk⟩ := hev'
      unfold Dequant.EvK at hk
      rw [hsite] at hk
      obtain ⟨inst, hk⟩ := hk
      exact hreq _ _ _ hk
    | wg1 =>
      rcases d with s | ⟨j | r, d⟩
      · simp only [measure, fragMeasure, wg1Measure, Wg1.measure] at hm
        have hsite := wg1_time0 (by omega : Wg1.time s = 0)
        subst hsite
        have hev' : Wg1.Ev L g .smr e := hev
        obtain ⟨inst, hk⟩ := hev'
        exact hreq _ _ _ hk
      · cases j <;> simp only [measure, fragMeasure, wg1Measure] at hm <;> omega
      · simp only [measure, fragMeasure, wg1Measure] at hm
        omega
  · exact hJ.elim

/-- The count of a prefix does not fall when the prefix grows. -/
theorem count_take_mono (p : Event → Bool) {j k : Nat} (h : j ≤ k) :
    ((X.tr g).take j).countP p ≤ ((X.tr g).take k).countP p := by
  have : (X.tr g).take j = ((X.tr g).take k).take j := by
    rw [List.take_take, Nat.min_eq_left h]
  rw [this]
  exact (List.take_sublist _ _).countP_le

/-- The startup's states and the warpgroups' first states are at most at `fragBase`. -/
theorem enter_measure (d : Startup.D) (n : Cls → Nat) :
    measure P L g (Code.enter (startupCode P L g) (Code.withStubs (frag P L g) Entry.pc)
      (Code.gatedExit (startupEnter P L g) (sel P L g)) d, n) ≤ fragBase := by
  unfold Code.enter
  split
  · rename_i x _
    rcases x with j | r
    · exact (init_measure j _).le
    · exact Nat.le_refl _
  · have := Startup.measure_le d
    simp only [measure, fragBase]
    omega

/-- **A state of a prefix is at most at `fragBase`, or the prefix has a request.** -/
theorem low_or_req (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hg : g < L.threads) :
    ∀ i, i ≤ (X.tr g).length → ∀ σ, Frame.stateAt (thread P L) X g i = some (some σ) →
      measure P L g σ ≤ fragBase ∨ 0 < ((X.tr g).take i).countP SetMaxNReg.isRequest := by
  intro i
  induction i with
  | zero =>
    intro _ σ h
    rw [Frame.stateAt_zero] at h
    cases h
    rw [thread_init]
    left
    exact Nat.le_trans (Startup.measure_le _) (by decide)
  | succ i ih =>
    intro hl σ' h
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[i]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨σ, hσ, hn⟩ := prev_state he h
    have hc : ((X.tr g).take i).countP SetMaxNReg.isRequest ≤
        ((X.tr g).take (i + 1)).countP SetMaxNReg.isRequest := count_take_mono _ (Nat.le_succ i)
    rcases ih (by omega) σ hσ with hlow | hreq
    · by_cases hlow' : measure P L g σ' ≤ fragBase
      · exact .inl hlow'
      right
      have hR := measure_raise hX hFw hg he hσ (noUb_kind hnu he) hn
      have hreq : SetMaxNReg.isRequest e = true := by
        obtain ⟨s, n⟩ := σ
        rcases s with d | ⟨j | r, d⟩
        · -- the startup enters a warpgroup at its first state, or a stub
          exfalso
          rw [next_startup] at hn
          obtain ⟨d', -, hd'⟩ := map_some hn
          subst hd'
          exact hlow' (enter_measure d' _)
        all_goals refine low_req hp hX hFw hnu he hσ ?_ (fun _ _ h => by cases h)
        all_goals have := hR.1
        all_goals (simp only [measure, fragMeasure] at hlow ⊢; try omega)
      have h1 : ((X.tr g).take (i + 1)).countP SetMaxNReg.isRequest =
          ((X.tr g).take i).countP SetMaxNReg.isRequest + 1 := by
        rw [List.take_add_one, he, Option.toList_some, List.countP_append]
        simp [hreq]
      omega
    · exact .inr (by omega)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
