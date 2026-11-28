-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarInit
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Startup
public import Lemmas.Kernel.Progress.NextEv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Bar

@[expose] public section

/-! # Barrier 0 comes first

Under `Follow`, over a launched thread of a consistent execution:

* `bar0_before`: an event past the startup's barrier (pc above 97, no undefined behaviour)
  follows a barrier-0 event of its thread: a state of any role but the startup's has passed it
  (the glued ledger, `state_role`);
* `bar0_next`: the same for a lane's next event (`Sched.NextEv`);
* `bar0_exit`: the thread's `exit` follows a barrier-0 event (no startup event is `exit`,
  `startup_exit`);
* `bar_first`: the startup's barrier event is the thread's first barrier event;
* `bar_later`: every barrier event at pc 103 or later follows a barrier event of its thread. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A state at prefix `k` whose event is past pc 97 has counted a barrier-0 event. -/
private theorem state_bar0 {k : Nat} {e : Event} {σ : (thread P L g).D}
    (hσ : Frame.stateAt (thread P L) X g k = some (some σ)) (hJ : (table P L).J g σ)
    (hi : (thread P L g).inv σ) (hpc' : e.pc = (thread P L g).pc σ) (hpc : 97 < e.pc) :
    0 < ((X.tr g).take k).countP isBar0 := by
  obtain ⟨s, n⟩ := σ
  have hb : n .bar0 = ((X.tr g).take k).countP isBar0 := state_count hσ .bar0
  have h := state_role hJ hi
  rw [← hpc'] at h
  rcases s with d | ⟨i | r, d'⟩
  · cases h
    omega
  · have hJ' : 1 ≤ n .bar0 := by cases i <;> exact hJ.1
    omega
  · exact hJ.elim

/-- **An event past pc 97 follows a barrier-0 event of its thread.** -/
theorem bar0_before (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) (hpc : 97 < e.pc) : 0 < ((X.tr g).take k).countP isBar0 := by
  obtain ⟨σ, hσ, hJ, hi, -, hpc'⟩ := ev_at hp hX hFw he hub
  exact state_bar0 hσ hJ hi hpc' hpc

/-- **A lane whose next event is past pc 97 has a barrier-0 event.** -/
theorem bar0_next (hp : Pre P L m) (hFw : Follow P L X) {e : Event}
    (hn : Sched.NextEv L kernel Assumptions.all m X g e) (hub : ∀ f, e.kind ≠ .ub f)
    (hpc : 97 < e.pc) : 0 < (X.tr g).countP isBar0 := by
  obtain ⟨σ, hσ, hJ, hi, -, hpc'⟩ := next_state hp hFw hn hub
  have h := state_bar0 hσ hJ hi hpc' hpc
  rwa [List.take_length] at h

/-- **A thread's `exit` follows a barrier-0 event of it** (`Inputs.bar0Exit`). -/
theorem bar0_exit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {j pc : Nat} (he : X.get (g, j) = some ⟨pc, .exit⟩) :
    0 < ((X.tr g).take j).countP isBar0 :=
  bar0_before hp hX hFw he (fun _ h => by cases h) (by
    have := startup_exit hp hX hFw he
    simp only
    omega)

/-- A member of a prefix of the trace is an event of it before the prefix's end. -/
private theorem get_of_take {k : Nat} {f : Event} (hf : f ∈ (X.tr g).take k) :
    ∃ j < k, X.get (g, j) = some f := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hf
  rw [List.getElem?_take] at hj
  by_cases hjk : j < k
  · simp only [hjk, ↓reduceIte] at hj
    exact ⟨j, hjk, hj⟩
  · simp [hjk] at hj

/-- A prefix count does not fall along the trace. -/
private theorem count_take_le (p : Event → Bool) {j k : Nat} (h : j ≤ k) :
    ((X.tr g).take j).countP p ≤ ((X.tr g).take k).countP p := by
  have : (X.tr g).take j = ((X.tr g).take k).take j := by
    rw [List.take_take, Nat.min_eq_left h]
  rw [this]
  exact (List.take_sublist _ _).countP_le

/-- **The startup's barrier event is its thread's first barrier event** (`BarInputs.first`). -/
theorem bar_first (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k : Nat} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hat : MbarRow.StartupAt e.pc) (hb : Execution.isBar e = true) :
    ((X.tr g).take k).countP Execution.isBar = 0 := by
  obtain ⟨pc, kd⟩ := e
  have hub : ∀ f, kd ≠ .ub f := by
    rintro f rfl
    simp [Execution.isBar] at hb
  obtain ⟨-, -, -, -, -, h0, -⟩ := startup_at hp hX hFw he hub hat
  have h0' : ((X.tr g).take k).countP isBar0 = 0 := h0
  refine List.countP_eq_zero.mpr fun f hf hbf => ?_
  obtain ⟨j, hj, hfj⟩ := get_of_take hf
  obtain ⟨pcf, kf⟩ := f
  have hubf : ∀ f', kf ≠ .ub f' := by
    rintro f' rfl
    simp [Execution.isBar] at hbf
  by_cases hlo : pcf < 103
  · obtain ⟨-, hk⟩ := barRow_startup hp hX hFw hg hfj hlo hbf
    have hpos : 0 < ((X.tr g).take k).countP isBar0 :=
      List.countP_pos_iff.mpr ⟨_, hf, by simp only [BarRow.Cta] at hk; simp [isBar0, hk]⟩
    omega
  · have := bar0_before hp hX hFw hfj hubf (by simp only; omega)
    have := count_take_le isBar0 hj.le (X := X) (g := g)
    omega

/-- **A barrier event at pc 103 or later follows a barrier event of its thread**
(`BarInputs.later`). -/
theorem bar_later (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k : Nat} {e : Event} (he : X.get (g, k) = some e) (hpc : 103 ≤ e.pc)
    (hb : Execution.isBar e = true) : 0 < ((X.tr g).take k).countP Execution.isBar := by
  have hub : ∀ f, e.kind ≠ .ub f := by
    obtain ⟨pc, kd⟩ := e
    rintro f hk
    simp only at hk
    subst hk
    simp [Execution.isBar] at hb
  refine lt_of_lt_of_le (bar0_before hp hX hFw he hub (by omega)) (List.countP_mono_left ?_)
  intro x _ hx
  obtain ⟨pc, kd⟩ := x
  cases kd <;> simp_all [isBar0, Execution.isBar]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
