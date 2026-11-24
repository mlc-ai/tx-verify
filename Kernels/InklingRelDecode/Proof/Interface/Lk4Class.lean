-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LkBar
public import Kernels.InklingRelDecode.Proof.Interface.ShapeTrace
public import Kernels.InklingRelDecode.Proof.Interface.FootClass
public import Kernels.InklingRelDecode.Proof.Thread.Lk4Class
public import Kernels.InklingRelDecode.Proof.Thread.SwShape
public import Kernels.InklingRelDecode.Proof.Thread.RdShape
public import Lemmas.Flow.NotTcData
public import Lemmas.Flow.Resource

@[expose] public section

/-!
# Warp lockstep: the warp-collective `tcgen05` events

A state is a warp-collective `tcgen05` state (`tcSt`) when it is a state of the common start, the
softmax region or the epilogue at one of the thirteen sites `Thread/Lk4Class.lean` lists. The event
fired from a state is a warp-collective `tcgen05` event (`isTcColl`) exactly when the state is
(`isTcColl_state`): the position is one of the program's (`kernel_collPcs`, from the instruction
the event comes from), and the event of each such site has the shape of its site (the allocation
and the relinquishment of the common start, the softmax region's eight, the epilogue's three; the
second step of the allocation is a store). The states of the class are synchronizing (`tcSt_sy`),
and two synchronizing states of one key are both in the class or both out (`tcKey_class`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Lk (collOp collPcs collPc kernel_collPcs dTc dTc_sy dTc_iff
  wColl_not pro_notColl dstart_coll)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The state's event is a warp-collective `tcgen05` event: the default partition's states at the
sites of the allocation, the permit relinquishment, the softmax region's eight and the epilogue's
three (`PTX.Kernels.InklingRelDecode.Proof.Lk.dTc`); no worker state is. -/
def tcSt : TSt → Bool
  | .d s => dTc s
  | .w _ => false

/-- **A state of the class is synchronizing.** -/
theorem tcSt_sy {s : TSt} (h : tcSt s = true) : tSy s := by
  cases s with
  | d s => exact dTc_sy h
  | w s => simp [tcSt] at h

/-- **A synchronizing state is in the class exactly when its position is a warp-collective
`tcgen05` position.** -/
theorem tcSt_eq_pc {s : TSt} (h : tSy s) : tcSt s = collPc (TSt.pc s) := by
  cases s with
  | d s =>
    have h' : PTX.Kernels.InklingRelDecode.Proof.Lk.dSy s = true := h
    show dTc s = collPc (DComp.pc s)
    cases hc : dTc s
    · cases hp : collPc (DComp.pc s)
      · rfl
      · exact absurd ((dTc_iff h').mpr hp) (by simp [hc])
    · exact ((dTc_iff h').mp hc).symm
  | w s => exact (wColl_not s).symm

/-- **Two synchronizing states of one key are both in the class or both out.** -/
theorem tcKey_class :
    ∀ {g h : Nat} {s s' : TSt}, SameWarp L g h → (kernelSkel Q L).sy s → (kernelSkel Q L).sy s' →
      (kernelSkel Q L).key g s = (kernelSkel Q L).key h s' → tcSt s = tcSt s' := by
  intro g h s s' hw hs hs' hk
  have h1 := (kernelSkel Q L).pc_key (g := g) hs
  have h2 := (kernelSkel Q L).pc_key (g := h) hs'
  have hpc : TSt.pc s = TSt.pc s' := by rw [← h1, ← h2, hk]
  rw [tcSt_eq_pc hs, tcSt_eq_pc hs', hpc]

/-- **A warp-collective `tcgen05` event comes from a warp-collective `tcgen05` position.** -/
theorem coll_pc_of {g : Nat} {s : TSt} {t : TState} {ins : Instr} {o : Option TState} {e : Event}
    (hc : kernel.code[TSt.pc s]? = some ins)
    (hf : Fires (TSt.pc s) (eventTmpl asms L g t ins.op) e o) (hcoll : isTcColl e = true) :
    collPc (TSt.pc s) = true := by
  have hop : collOp ins.op = true := by
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp only [isTcColl, Bool.false_eq_true] at hcoll
    rename_i k
    cases k <;> simp only [Bool.false_eq_true] at hcoll
    · have := fires_resource_op hf (rfl : (⟨pc, .tc (.resource ‹_› ‹_› ‹_›)⟩ : Event).kind = _)
      cases hq : ins.op <;> simp_all [tmemOp, collOp]
    all_goals
      have := fires_tcData_op hf (by simp [isTcData])
      cases hq : ins.op <;> simp_all [tcDataOp, collOp]
  have := OpPcsFast.mem kernel_collPcs hc hop
  simpa [collPc] using this

/-! ### The event fired from a state of the class -/

theorem tc_not_exit {s : TSt} (h : tcSt s = true) : ¬ ExitState s := by
  cases s with
  | w s => simp [tcSt] at h
  | d s =>
    cases s with
    | epi d =>
      intro hx
      have hx' : d.site = .exit := hx
      simp [tcSt, dTc, hx'] at h
    | _ => exact id

/-- **The event of a warp-collective `tcgen05` state is a warp-collective `tcgen05` event.** -/
theorem tc_event (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k : Nat} {e : Event} {s : TSt} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some s)) (hs : tcSt s = true) :
    isTcColl e = true := by
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (tc_not_exit hs)
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hb2 : L.block = 256 := hpre.block
  have hSh := ProA.sharedOk_of_pre hpre
  cases s with
  | w s => simp [tcSt] at hs
  | d s =>
    cases s with
    | pro d => simp [tcSt, dTc] at hs
    | dstart d =>
      have hshape := DStart.shape_of_pre hpre (fired_dstart hF)
      obtain ⟨site, tm⟩ := d
      simp only [tcSt, dTc, decide_eq_true_eq] at hs
      rcases hs with rfl | rfl
      · simp only [DStart.Shape] at hshape
        rw [hshape]
        rfl
      · simp only [DStart.Shape] at hshape
        rw [hshape]
        rfl
    | sm d =>
      have hshape := Sm.shape hb2 hSh (fired_sm hF)
      have hshapeO := Sm.shapeO (fired_sm hF)
      have hw := fun h => Sm.shape_waitLdO hb (fired_sm hF) h
      simp only [tcSt, dTc, decide_eq_true_eq] at hs
      unfold Sm.Shape at hshape
      unfold Sm.ShapeO at hshapeO
      rcases hs with h | h | h | h | h | h | h | h <;> rw [h] at hshape hshapeO
      · obtain ⟨vals, -, he'⟩ := hshape; rw [he']; rfl
      · rw [hshape]; rfl
      · obtain ⟨vals, -, -, -, he'⟩ := hshape; rw [he']; rfl
      · rw [hshape]; rfl
      · obtain ⟨vals, -, he'⟩ := hshapeO; rw [he']; rfl
      · rw [hw h]; rfl
      · obtain ⟨vals, -, -, -, he'⟩ := hshapeO; rw [he']; rfl
      · rw [hshape]; rfl
    | epi d =>
      have hshape := Epi.shape hb (fired_epi hF)
      simp only [tcSt, dTc, decide_eq_true_eq] at hs
      unfold Epi.Shape at hshape
      rcases hs with h | h | h <;> rw [h] at hshape
      · obtain ⟨vals, -, he'⟩ := hshape; rw [he']; rfl
      · rw [hshape]; rfl
      · rw [hshape]; rfl

/-- **A state that is not a warp-collective `tcgen05` state fires no such event.** -/
theorem notTc_event (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k : Nat} {e : Event} {s : TSt} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some s)) (hs : tcSt s = false) :
    isTcColl e = false := by
  obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site hf.sound hX he hσ
  by_contra hcl
  have hcoll : isTcColl e = true := by simpa using hcl
  have hp := coll_pc_of hc hfire hcoll
  cases s with
  | w s => simp [TSt.pc, wColl_not] at hp
  | d s =>
    cases s with
    | pro d =>
      simp only [TSt.pc, DComp.pc, collPc, List.contains_iff_mem] at hp
      exact pro_notColl d.site hp
    | dstart d =>
      simp only [TSt.pc, DComp.pc, collPc, List.contains_iff_mem] at hp
      obtain ⟨site, tm⟩ := d
      rcases dstart_coll site hp with rfl | rfl | rfl
      · simp [tcSt, dTc] at hs
      · obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
        have hshape := DStart.shape_of_pre hpre (fired_dstart hF)
        simp only [DStart.Shape] at hshape
        obtain ⟨col, -, hshape⟩ := hshape
        rw [hshape] at hcoll
        simp [isTcColl] at hcoll
      · simp [tcSt, dTc] at hs
    | sm d =>
      simp only [TSt.pc, DComp.pc, collPc, List.contains_iff_mem] at hp
      obtain ⟨site, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
      rcases Lk.sm_coll site hp with h | h | h | h | h | h | h | h <;> subst h <;>
        simp [tcSt, dTc] at hs
    | epi d =>
      simp only [TSt.pc, DComp.pc, collPc, List.contains_iff_mem] at hp
      obtain ⟨site, pr, o', sk⟩ := d
      rcases Lk.epi_coll site hp with h | h | h <;> subst h <;> simp [tcSt, dTc] at hs

/-- **The event fired from a state is a warp-collective `tcgen05` event exactly when the state
is.** -/
theorem isTcColl_state (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k : Nat} {e : Event} {s : TSt} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some s)) :
    isTcColl e = tcSt s := by
  cases hs : tcSt s
  · exact notTc_event hpre hX hf hg he hσ hs
  · exact tc_event hpre hX hf hg he hσ hs

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
