-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingRegisterRegion
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxReturnOrigin

@[expose] public section

/-! # Softmax write-address registers retained across actual executions -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The registers supplying the actual shared and generic store base addresses. -/
def softmaxWriteRegs : List Nat := [459, 460, 463, 471, 474, 2991, 3001] ++
  (List.range 8).map (988 + ·) ++ (List.range 8).map (2992 + ·)

/-- The loop and epilogue from the first mask acquire to return. -/
def softmaxWriteRegion (pc : Nat) : Prop := (253 ≤ pc ∧ pc < 1842) ∨ 3611 ≤ pc

instance (pc : Nat) : Decidable (softmaxWriteRegion pc) := by
  unfold softmaxWriteRegion
  infer_instance

set_option maxRecDepth 100000 in
theorem softmax_write_region_closed : controlRegionClosed softmaxWriteRegion = true := by
  decide +kernel

/-- Instruction positions within the softmax body and before exit. -/
def softmaxInBody (pc : Nat) : Bool := decide (253 ≤ pc ∧ pc < 1842)

set_option maxRecDepth 100000 in
private theorem softmax_write_reg_audit {r : Nat} (hr : r ∈ softmaxWriteRegs) :
    registerRegionChecked r softmaxInBody [160, 207, 252] = true := by
  have h : softmaxWriteRegs.all
      (fun r => registerRegionChecked r softmaxInBody [160, 207, 252]) = true := by
    decide +kernel
  exact List.all_eq_true.mp h r hr

/-- Address registers carried by the softmax loop before it exits. -/
def SoftmaxWriteState (regs : Nat → Option Value) (t : TState) : Prop :=
  softmaxWriteRegion t.pc ∧ ∀ r ∈ softmaxWriteRegs, softmaxInBody t.pc = true → t.regs r = regs r

/-- Local steps retain the softmax write bases across the loop. -/
theorem softmax_write_tau {regs : Nat → Option Value} {t u : TState}
    (h : SoftmaxWriteState regs t) (hu : Tau kernel Assumptions.all L g t u) :
    SoftmaxWriteState regs u := by
  refine ⟨control_region_tau softmax_write_region_closed h.1 hu, fun r hr => ?_⟩
  refine register_region_tau (property := (· = regs r)) (softmax_write_reg_audit hr)
    (h.2 r hr) ?_ hu
  intro hPc _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hPc
  rcases hPc with hp | hp | hp <;> have hWithin := h.1 <;>
    simp [hp, softmaxWriteRegion] at hWithin

/-- Memory and synchronization callbacks retain the softmax write bases. -/
theorem softmax_write_event {regs : Nat → Option Value} {t u : TState} {e : Event}
    (h : SoftmaxWriteState regs t) (he : EStep kernel Assumptions.all L g t e (some u)) :
    SoftmaxWriteState regs u := by
  refine ⟨control_region_event softmax_write_region_closed h.1 he, fun r hr => ?_⟩
  exact register_region_event (property := (· = regs r)) (softmax_write_reg_audit hr)
    (register_updates_local (by decide +kernel)) (h.2 r hr) he

private theorem softmax_write_regs_live {d : Wg0.D} (hMask : d.site = .maskReady) :
    ∀ r ∈ softmaxWriteRegs, r ∈ (Flow.live d.site.pc).filter Wg0.tracked.contains := by
  rw [hMask]
  have h : softmaxWriteRegs.all (fun r =>
      decide (r ∈ (Flow.live Wg0.Site.maskReady.pc).filter Wg0.tracked.contains)) = true := by
    decide +kernel
  intro r hr
  exact of_decide_eq_true (List.all_eq_true.mp h r hr)

/-- Recover the concrete suffix from the first mask wait, with its retained write bases. -/
theorem softmax_write_suffix {start : Nat} {d : Wg0.D}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (hg : g < L.threads)
    (hMask : d.site = .maskReady)
    (hState : Frame.stateAt (Machine.code P L) X g start = some (some (.wg0 d)))
    (hEvents : (X.tr g).drop start ≠ []) :
    ∃ t o, SoftmaxWriteState (fun r => some (Wg0.valueOf P L g d r)) t ∧
      t.pc = 264 ∧
      Run kernel Assumptions.all L g t ((X.tr g).drop start) o := by
  obtain ⟨t, o, hGood, hRun⟩ := actual_suffix_from_followed hX hg (hs g hg) hState hEvents
  have ht : (Wg0.code P L g).AtD d t := hGood.1
  have hp := ht.1
  change t.pc = d.site.pc at hp
  rw [hMask] at hp
  refine ⟨t, o, ⟨by rw [hp]; exact .inl (by decide), fun r hr _ => ?_⟩, hp, hRun⟩
  exact Wg0.reg_value ht (softmax_write_regs_live hMask r hr)

/-- The instruction source of a concrete softmax event retains the launch-dependent write
addresses. Neither score bytes nor subsequent control decisions determine those addresses. -/
theorem softmax_write_regs_at_event {start i : Nat} {d : Wg0.D} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hMask : d.site = .maskReady)
    (hState : Frame.stateAt (Machine.code P L) X g start = some (some (.wg0 d)))
    (he : X.get (g, i) = some e) (hi : start ≤ i) :
    ∃ t q, EStep kernel Assumptions.all L g t e q ∧ softmaxWriteRegion t.pc ∧
      (253 ≤ t.pc → t.pc < 1842 → ∀ r ∈ softmaxWriteRegs,
        t.regs r = some (Wg0.valueOf P L g d r)) := by
  let events := (X.tr g).drop start
  have hGet : events[i - start]? = some e := by
    change ((X.tr g).drop start)[i - start]? = _
    rw [List.getElem?_drop, Nat.add_sub_of_le hi]
    exact he
  have hm := List.mem_of_getElem? hGet
  obtain ⟨t, o, hStart, _, hRun⟩ :=
    softmax_write_suffix hX hs (Frame.lt_of_get hX he) hMask hState (List.ne_nil_of_mem hm)
  obtain ⟨u, q, hAt, hSource⟩ :=
    actual_event_invariant softmax_write_tau softmax_write_event hStart hRun hm
  exact ⟨u, q, hSource, hAt.1, fun hLo hHi r hr => hAt.2 r hr (decide_eq_true ⟨hLo, hHi⟩)⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
