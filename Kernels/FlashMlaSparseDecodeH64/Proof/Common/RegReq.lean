-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.LastTime
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowHead
public import Lemmas.Flow.NotBulk
public import Lemmas.Kernel.Progress.Issue

@[expose] public section

/-! # The register requests' facts for the progress template

From the measure facts (`Common/RegTime.lean`), over a followed consistent execution without
undefined behaviour:

* `req_state`: a request is fired at measure `fragBase`, at pc 103 (warps 0–3), 1842 (warps
  4–7) or 2606 (warps 8–11), from the instruction at its pc (`req_op`);
* `req_first`: a request is its thread's first; `req_after`: the state after it is later than
  `regT`; `req_exit`: an `exit` follows a request; `req_before`: a thread without a request is no
  later than `regT`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **A request is fired by the `setmaxnreg` at its pc.** -/
theorem req_op (hX : Consistent L kernel Assumptions.all m X) {k pc n inst : Nat} {inc : Bool}
    (he : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩) :
    ∃ ins, kernel.code[pc]? = some ins ∧ ins.op = .setMaxReg inc n := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hf
  · exact ⟨ins, hc, fires_setMaxReg_op hf rfl⟩

/-- A state of a later prefix has a state at every earlier prefix. -/
private theorem state_before {i : Nat} :
    ∀ d, i + d ≤ (X.tr g).length → ∀ σ, Frame.stateAt (thread P L) X g (i + d) = some (some σ) →
      ∃ σ', Frame.stateAt (thread P L) X g i = some (some σ') := by
  intro d
  induction d with
  | zero => intro _ σ h; exact ⟨σ, h⟩
  | succ d ih =>
    intro hl σ h
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[i + d]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨σm, hm, -⟩ := prev_state he (by rw [← Nat.add_assoc] at h; exact h)
    exact ih (by omega) σm hm

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hnu : ¬ HasUb X)
include hp hX hFw hnu

omit hp hX hFw hnu in
/-- **A state at a `setmaxnreg` is at measure `fragBase`, at its warpgroup's pc.** -/
private theorem smr_state {σ : (thread P L g).D} {pc n : Nat} {inc : Bool} {ins : Instr}
    (hJ : (table P L).J g σ) (hi : (thread P L g).inv σ) (hpc0 : (thread P L g).pc σ = pc)
    (hc : kernel.code[pc]? = some ins) (hop : ins.op = .setMaxReg inc n) :
    measure P L g σ = fragBase ∧
      ((pc = 103 ∧ warp L g < 4) ∨ (pc = 1842 ∧ 4 ≤ warp L g ∧ warp L g < 8) ∨
        (pc = 2606 ∧ 8 ≤ warp L g ∧ warp L g < 12)) := by
  have hpc3 := smr_pc hc (by rw [hop]; rfl)
  have h := state_role hJ hi
  rw [hpc0] at h
  cases h with
  | startup d n hR hW hx hpc' hr => omega
  | head s n hs hpc' hr hg hw =>
    have hs' : s = .smr := by
      rcases hs with rfl | rfl
      · rfl
      · simp only [Wg1.Site.pc] at hpc'; omega
    subst hs'
    simp only [Wg1.Site.pc] at hpc'
    exact ⟨rfl, .inr (.inl ⟨hpc', hw⟩)⟩
  | idle s n hpc' hw hr hret => have := idle_pc_ge s; omega
  | index d n hR hw hpc' hr => omega
  | mma d n hR hok hl hw hpc' hr => omega
  | tma d n hR hok hl hw hpc' hr => omega
  | dequant d n hR hw hpc' hr =>
    have hs : d.site = .smr := deq_pc2606 (by
      rcases hpc3 with h3 | h3 | h3 <;> rcases hr with hr | hr <;> omega)
    have h3 : pc = 2606 := by rw [hpc', hs]; rfl
    refine ⟨?_, .inr (.inr ⟨h3, hw⟩)⟩
    simp only [measure, fragMeasure, dequantMeasure, Dequant.measure, Dequant.place, hs]
    rfl
  | wg0 d n hR hw hpc' hr =>
    have hs : (d : Wg0.Control.D).site = .smr := wg0_pc103 (by
      rcases hpc3 with h3 | h3 | h3 <;> rcases hr with hr | hr <;> omega)
    have h3 : pc = 103 := by rw [hpc', hs]; rfl
    refine ⟨?_, .inl ⟨h3, hw⟩⟩
    simp only [measure, fragMeasure, wg0Measure, Wg0.measure, Wg0.place, hs, Wg0.regPlace,
      Wg0.Site.reg, Wg0.Site.ord]
    rfl

/-- **A request is fired at measure `fragBase`, at its warpgroup's pc.** -/
theorem req_state {k pc n inst : Nat} {inc : Bool}
    (he : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩) :
    ∃ σ, Frame.stateAt (thread P L) X g k = some (some σ) ∧ measure P L g σ = fragBase ∧
      ((pc = 103 ∧ warp L g < 4) ∨ (pc = 1842 ∧ 4 ≤ warp L g ∧ warp L g < 8) ∨
        (pc = 2606 ∧ 8 ≤ warp L g ∧ warp L g < 12)) := by
  obtain ⟨ins, hc, hop⟩ := req_op hX he
  obtain ⟨σ, hσ, hJ, hi, -, hpc⟩ := ev_at hp hX hFw he (noUb_kind hnu he)
  exact ⟨σ, hσ, smr_state hJ hi hpc.symm hc hop⟩

/-- No request precedes a state at measure `fragBase`. -/
private theorem none_before {k : Nat} {σk : (thread P L g).D} (hg : g < L.threads)
    (hkl : k ≤ (X.tr g).length) (hσk : Frame.stateAt (thread P L) X g k = some (some σk))
    (hmk : measure P L g σk = fragBase) {j pc' : Nat} {inc' : Bool} {n' inst' : Nat}
    (hj : (X.tr g)[j]? = some ⟨pc', .setMaxReg inc' n' inst'⟩) (hjk : j < k) : False := by
  obtain ⟨σj, hσj, hmj, -⟩ := req_state hp hX hFw hnu hj
  obtain ⟨σ1, h1⟩ := state_before (P := P) (X := X) (g := g) (i := j + 1) (k - (j + 1))
    (by omega) σk (by rw [show j + 1 + (k - (j + 1)) = k by omega]; exact hσk)
  obtain ⟨σ0, h0, hn⟩ := prev_state hj h1
  rw [hσj] at h0
  cases h0
  have hR := measure_raise hX hFw hg hj hσj (noUb_kind hnu hj) hn
  have hlt := hR.2 rfl
  have hle := meas_mono hX hFw hnu hg h1 (k - (j + 1)) (by omega) σk
    (by rw [show j + 1 + (k - (j + 1)) = k by omega]; exact hσk)
  omega

/-- **A request is its thread's first.** -/
theorem req_first {k pc n inst : Nat} {inc : Bool}
    (he : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩) :
    ((X.tr g).take k).countP SetMaxNReg.isRequest = 0 := by
  have hg := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨σk, hσk, hmk, -⟩ := req_state hp hX hFw hnu he
  refine List.countP_eq_zero.mpr fun f hf hr => ?_
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hf
  have hjk : j < k := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take_of_lt hjk] at hj
  obtain ⟨pc', kd⟩ := f
  cases kd with
  | setMaxReg inc' n' inst' => exact none_before hp hX hFw hnu hg hk.le hσk hmk hj hjk
  | _ => simp [SetMaxNReg.isRequest] at hr

/-- **A lane at the state of a `setmaxnreg` has made no request.** -/
theorem req_none_at {σ : (thread P L g).D} {ins : Instr}
    (hσ : Frame.stateAt (thread P L) X g (X.tr g).length = some (some σ))
    (hJ : (table P L).J g σ) (hi : (thread P L g).inv σ)
    (hc : kernel.code[(thread P L g).pc σ]? = some ins) (hop : Sched.regOp ins.op = true) :
    ∀ j pc inc n inst, X.get (g, j) ≠ some ⟨pc, .setMaxReg inc n inst⟩ := by
  intro j pc inc n inst hj
  have hg := Frame.lt_of_get hX hj
  have hjl : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨gd, op⟩ := ins
  cases op <;> simp only [Sched.regOp, Bool.false_eq_true] at hop
  obtain ⟨hm, -⟩ := smr_state hJ hi rfl hc rfl
  exact none_before hp hX hFw hnu hg le_rfl hσ hm hj hjl

omit hp hX hnu in
/-- The thread machine moves on from a state at measure `fragBase` that is no startup state. -/
private theorem low_next {σ : (thread P L g).D} {k : Nat} {e : Event}
    (hσ : Frame.stateAt (thread P L) X g k = some (some σ)) (hg : g < L.threads)
    (hm : measure P L g σ = fragBase) (hs : ∀ d n, σ ≠ (.inl d, n)) :
    ∃ σ', (thread P L g).next σ e = some (some σ') := by
  have hJ := (follow_iff.mp hFw g hg k).2 σ hσ
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
      rw [next_frag]
      show ∃ σ', (Wg0.Control.succ P L g (warpW L g) d e).map _ = _
      unfold Wg0.Control.succ
      rw [hsite]
      exact ⟨_, rfl⟩
    | dequant =>
      have h0 : Dequant.place d = 0 := by
        simp only [measure, fragMeasure, dequantMeasure, Dequant.measure] at hm
        have : 0 < Dequant.top := by simp only [Dequant.top]; omega
        omega
      have hsite := deq_place0 h0
      rw [next_frag]
      show ∃ σ', (Dequant.Control.succ P L g d e).map _ = _
      unfold Dequant.Control.succ
      rw [hsite]
      exact ⟨_, rfl⟩
    | wg1 =>
      rcases d with s | ⟨j | r, d⟩
      · simp only [measure, fragMeasure, wg1Measure, Wg1.measure] at hm
        have hsite := wg1_time0 (by omega : Wg1.time s = 0)
        subst hsite
        rw [next_head]
        exact ⟨_, rfl⟩
      · cases j <;> simp only [measure, fragMeasure, wg1Measure] at hm <;> omega
      · simp only [measure, fragMeasure, wg1Measure] at hm
        omega
  · exact hJ.elim

/-- **The state after a request is later than `regT`.** -/
theorem req_after {k pc n inst : Nat} {inc : Bool}
    (he : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩) :
    ∃ σ', Frame.stateAt (thread P L) X g (k + 1) = some (some σ') ∧
      regT L g < time P L g σ' := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨σ, hσ, hm, -⟩ := req_state hp hX hFw hnu he
  have hs : ∀ d n, σ ≠ (.inl d, n) := by
    rintro d n rfl
    have := Startup.measure_le d
    simp only [measure, fragBase] at hm
    omega
  obtain ⟨σ', hn⟩ := low_next hFw hσ hg hm hs (e := ⟨pc, .setMaxReg inc n inst⟩)
  have hσ' : Frame.stateAt (thread P L) X g (k + 1) = some (some σ') := by
    rw [Frame.stateAt_succ (show (X.tr g)[k]? = some _ from he), hσ]
    exact hn
  have hR := measure_raise hX hFw hg he hσ (noUb_kind hnu he) hn
  exact ⟨σ', hσ', high_time ((follow_iff.mp hFw g hg (k + 1)).2 σ' hσ') (by
    have := hR.2 rfl
    omega)⟩

/-- **An `exit` follows a request.** -/
theorem req_exit {k pc : Nat} (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    1 ≤ ((X.tr g).take k).countP SetMaxNReg.isRequest := by
  have hg := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨σ, hσ, hJ, hi, hev, -⟩ := ev_at hp hX hFw he (noUb_kind hnu he)
  rcases low_or_req hp hX hFw hnu hg k hk.le σ hσ with hlow | hreq
  · exfalso
    obtain ⟨s, n⟩ := σ
    rcases s with d | r
    · have hx : Startup.exitOf d = none := by simpa [startupEnter] using glue_gate hσ
      exact (Startup.ev_quiet (hev : Startup.Ev L g d _) hx).2.1 rfl
    · have hm : measure P L g (.inr r, n) = fragBase := by
        rcases r with ⟨i | r, d⟩
        · simp only [measure] at hlow ⊢
          omega
        · rfl
      have := low_req hp hX hFw hnu he hσ hm (fun _ _ h => by cases h)
      simp [SetMaxNReg.isRequest] at this
  · omega

/-- **A thread without a request is no later than `regT`.** -/
theorem req_before (hg : g < L.threads)
    (hno : ∀ j pc inc n inst, X.get (g, j) ≠ some ⟨pc, .setMaxReg inc n inst⟩) :
    Sched.threadTime (timed P L) X g ≤ regT L g := by
  have h0 : ∀ i, ((X.tr g).take i).countP SetMaxNReg.isRequest = 0 := fun i =>
    List.countP_eq_zero.mpr fun f hf hr => by
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take hf)
      obtain ⟨pc, kd⟩ := f
      cases kd with
      | setMaxReg inc n inst => exact hno j pc inc n inst hj
      | _ => simp [SetMaxNReg.isRequest] at hr
  have hlow : ∀ i σ, i ≤ (X.tr g).length → Frame.stateAt (thread P L) X g i = some (some σ) →
      measure P L g σ ≤ fragBase := fun i σ hi hσ => by
    rcases low_or_req hp hX hFw hnu hg i hi σ hσ with h | h
    · exact h
    · rw [h0] at h; omega
  refine time_last (Q := fun t => t ≤ regT L g) (Nat.zero_le _) (fun σ hs => ?_)
    (fun σ f hs hf hn => ?_)
  · exact low_time hs ((follow_iff.mp hFw g hg _).2 σ hs) (hlow _ σ (Nat.le_refl _) hs)
  · obtain ⟨s, n⟩ := σ
    rcases s with d | r
    · have hx : Startup.exitOf d = none := by simpa [startupEnter] using glue_gate hs
      have := Startup.time_lt hx
      simp only [time, regT]
      split_ifs <;> omega
    · exfalso
      have hm := hlow _ _ (Nat.sub_le _ _) hs
      have hm' : measure P L g (.inr r, n) = fragBase := by
        rcases r with ⟨i | r, d⟩
        · simp only [measure] at hm ⊢
          omega
        · rfl
      have := low_req hp hX hFw hnu hf hs hm' (fun _ _ h => by cases h)
      obtain ⟨pc, kd⟩ := f
      cases kd with
      | setMaxReg inc n inst => exact hno _ pc inc n inst hf
      | _ => simp [SetMaxNReg.isRequest] at this

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
