-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaPvEntry
public import Kernels.TmlFa4Fwd.Proof.MmaWholePrefix
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

def pvCutCode (lo hi : Nat) (keep : List Nat) (i : Instr) : Bool :=
  (keep.all fun r => !(mmaWrites i.op).contains r) &&
    match i.op with
    | .bra dst _ => lo ≤ dst && dst ≤ hi
    | .brx .. => false
    | _ => true

private theorem pvCutStep {l : Launch} {g lo hi : Nat} {s u : TState} {ev : Option Event}
    {F : List (Nat × Value)} (hLo : 1907 ≤ lo) (hHi : hi < 2768)
    (hAudit : ((kernel.code.drop lo).take (hi-lo)).all (pvCutCode lo hi (F.map Prod.fst)) = true)
    (hs : lo ≤ s.pc ∧ s.pc < hi) (hF : Holds s.regs F)
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    (lo ≤ u.pc ∧ u.pc ≤ hi) ∧ Holds u.regs F := by
  have hCore : out kernel Assumptions.all l g s = out kernel [] l g s :=
    out_eq_core (by omega) (by omega)
  have hChecked {i : Instr} (hc : kernel.code[s.pc]? = some i) :
      pvCutCode lo hi (F.map Prod.fst) i = true := by
    have hGet : ((kernel.code.drop lo).take (hi-lo))[s.pc-lo]? = some i := by
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
        Nat.add_sub_of_le hs.1, hc]
    exact List.all_eq_true.mp hAudit i (List.mem_of_getElem? hGet)
  refine ⟨?_, ?_⟩
  · rcases hStep with ⟨_, ht⟩ | ⟨e, _, he⟩
    · have htCore : Tau kernel [] l g s u := by
        unfold Tau at ht ⊢
        rwa [← hCore]
      obtain ⟨i, hc⟩ := tau_core_has_code htCore
      rcases tau_core_frame hc htCore with rfl | h
      · exact ⟨by simp [skip]; omega, by simp [skip]; omega⟩
      have hNext := h.pc
      have hC := (Bool.and_eq_true_iff.mp (hChecked hc)).2
      cases hi : i.op <;> simp only [hi, nextPc, BrxTarget, or_false] at hNext
      case bra target uniform => simpa [hi, hNext] using hC
      case brx => simp [hi] at hC
      all_goals omega
    · have heCore : EStep kernel [] l g s e (some u) := by
        obtain ⟨tm, hOut, hFire⟩ := he
        exact ⟨tm, hCore ▸ hOut, hFire⟩
      rcases (estep_return_pc heCore (fun _ _ _ h => execLocal_frame h)).2 with h | h <;> omega
  · apply Epilogue.holdsSchedulerFrame hF
    · intro r hr
      apply mmaStepReg (by omega) (by omega) _ hStep
      intro i hc
      have hKeep := (Bool.and_eq_true_iff.mp (hChecked hc)).1
      simpa using List.all_eq_true.mp hKeep r hr
    · intro _ h
      exact List.mem_map_of_mem h

section
variable {l : Launch} {g lo hi : Nat} {s : TState} {es : List Event} {vs : List Visit}
    {F : List (Nat × Value)} {e : Event} (hLo : 1907 ≤ lo) (hHi : hi < 2768)
    (hAudit : ((kernel.code.drop lo).take (hi-lo)).all (pvCutCode lo hi (F.map Prod.fst)) = true)
    (hw : Walk kernel Assumptions.all l g s es vs) (hs : lo ≤ s.pc ∧ s.pc ≤ hi)
    (hShape : RoleShape s ∧ s.regs 1062 = some (b32 12))
include hLo hHi hAudit hw hs hShape

/-- A recorded event at the far side of a cut forces a visit to the cut, and the
registers whose decoded writers are absent still have their earlier values. -/
theorem pvWalkCutLengthRanged (hF : Holds s.regs F) (he : e ∈ es) (hLate : hi ≤ e.pc) :
    ∃ u pre tail post, es = pre ++ tail ∧ u.pc = hi ∧
      (RoleShape u ∧ u.regs 1062 = some (b32 12)) ∧ Holds u.regs F ∧
      Walk kernel Assumptions.all l g u tail post ∧ e ∈ tail ∧ post.length ≤ vs.length ∧
      ∀ v ∈ pre, lo ≤ v.pc ∧ v.pc < hi := by
  have advance {t u : TState} {ev : Option Event}
      (hPc : lo ≤ t.pc ∧ t.pc < hi) (hRegs : Holds t.regs F)
      (hShape : RoleShape t ∧ t.regs 1062 = some (b32 12))
      (hStep : WStep kernel Assumptions.all l g t ev u) :
      (lo ≤ u.pc ∧ u.pc ≤ hi) ∧
      (RoleShape u ∧ u.regs 1062 = some (b32 12)) ∧ Holds u.regs F := by
    obtain ⟨hBounds, hFrame⟩ := pvCutStep hLo hHi hAudit hPc hRegs hStep
    exact ⟨hBounds, (mmaCutStep (by omega) (by omega) hStep hShape).2, hFrame⟩
  induction hw with
  | stop => simp at he
  | @tau t u es vs ht hw ih =>
    by_cases h : t.pc = hi
    · exact ⟨t, [], es, _, rfl, h, hShape, hF, .tau ht hw, he, by simp, by simp⟩
    obtain ⟨hPc, hShape, hRegs⟩ :=
      advance ⟨hs.1, by omega⟩ hF hShape (.inl ⟨rfl, ht⟩)
    obtain ⟨v,pre,tail,post,hSplit,hP,hS,hF,hWalk,hE,hLength,hEarly⟩ :=
      ih hPc hShape hRegs he
    exact ⟨v,pre,tail,post,hSplit,hP,hS,hF,hWalk,hE,by simp; omega,hEarly⟩
  | @ev t u v es vs hv hw ih =>
    by_cases h : t.pc = hi
    · exact ⟨t, [], _, _, rfl, h, hShape, hF, .ev hv hw, he, by simp, by simp⟩
    have hEarly : lo ≤ v.pc ∧ v.pc < hi := by have := estep_source_pc hv; omega
    have hMem := (List.mem_cons.mp he).resolve_left (fun hEq => by rw [hEq] at hLate; omega)
    obtain ⟨hPc, hShape, hRegs⟩ :=
      advance ⟨hs.1, by omega⟩ hF hShape (.inr ⟨v, rfl, hv⟩)
    obtain ⟨w, pre, tail, post, hSplit, hPc, hSh, hFr, hW, hE,hLength,hLast⟩ :=
      ih hPc hShape hRegs hMem
    refine ⟨w, v :: pre, tail, post, congrArg (v :: ·) hSplit, hPc, hSh, hFr, hW, hE,
      by simp; omega, ?_⟩
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hm
    · exact hEarly
    · exact hLast u hm
  | @last t v hv =>
    obtain rfl := List.mem_singleton.mp he
    have hEq : t.pc = hi := by have := estep_source_pc hv; omega
    exact ⟨t, [], _, _, rfl, hEq, hShape, hF, .last hv, by simp, by simp, by simp⟩

/-- A recorded event at the far side of a cut forces a visit to the cut, and the
registers whose decoded writers are absent still have their earlier values. -/
theorem pvWalkCutLength (hF : Holds s.regs F) (he : e ∈ es) (hLate : hi ≤ e.pc) :
    ∃ u pre tail post, es = pre ++ tail ∧ u.pc = hi ∧
      (RoleShape u ∧ u.regs 1062 = some (b32 12)) ∧ Holds u.regs F ∧
      Walk kernel Assumptions.all l g u tail post ∧ e ∈ tail ∧ post.length ≤ vs.length ∧
      ∀ v ∈ pre, v.pc < hi := by
  obtain ⟨u,pre,tail,post,hSplit,hPc,hRole,hRegs,hWalk,hFound,hLength,hRange⟩ :=
    pvWalkCutLengthRanged hLo hHi hAudit hw hs hShape hF he hLate
  exact ⟨u,pre,tail,post,hSplit,hPc,hRole,hRegs,hWalk,hFound,hLength,
    fun v hv => (hRange v hv).2⟩

/-- A recorded event at the far side of a cut forces a visit to the cut, and the
registers whose decoded writers are absent still have their earlier values. -/
theorem pvWalkCut (hF : Holds s.regs F) (he : e ∈ es) (hLate : hi ≤ e.pc) :
    ∃ u pre tail post, es = pre ++ tail ∧ u.pc = hi ∧
      (RoleShape u ∧ u.regs 1062 = some (b32 12)) ∧ Holds u.regs F ∧
      Walk kernel Assumptions.all l g u tail post ∧ e ∈ tail ∧
      ∀ v ∈ pre, v.pc < hi := by
  obtain ⟨u,pre,tail,post,hSplit,hPc,hR,hRegs,hWalk,hRemain,_,hEarly⟩ :=
    pvWalkCutLength hLo hHi hAudit hw hs hShape hF he hLate
  exact ⟨u,pre,tail,post,hSplit,hPc,hR,hRegs,hWalk,hRemain,hEarly⟩
end

/-- Reach the actual continuation of an indexed MMA event with its live registers. -/
theorem pvRoleAfterEventFramed {l : Launch} {g index : Nat} {s : TState} {e : Event}
    {es : List Event} {vs : List Visit} {F : List (Nat × Value)}
    (hAudit : ((kernel.code.drop 1907).take (2768-1907)).all
      (fun i => (F.map Prod.fst).all (fun r => !(mmaWrites i.op).contains r)) = true)
    (hw : Walk kernel Assumptions.all l g s es vs) (hs : 1907 ≤ s.pc ∧ s.pc < 2768)
    (hShape : RoleShape s ∧ s.regs 1062 = some (b32 12))
    (hF : Holds s.regs F)
    (he : es[index]? = some e) (hBound : index + 1 < es.length) (hLate : e.pc < 2768) :
    ∃ t u post, EStep kernel Assumptions.all l g t e (some u) ∧
      (RoleShape u ∧ u.regs 1062 = some (b32 12)) ∧ Holds u.regs F ∧
      Walk kernel Assumptions.all l g u (es.drop (index + 1)) post := by
  have frame {t u : TState} {ev : Option Event} (hRange : 1907 ≤ t.pc ∧ t.pc < 2768)
      (hRegs : Holds t.regs F) (step : WStep kernel Assumptions.all l g t ev u) :
      Holds u.regs F := by
    apply Epilogue.holdsSchedulerFrame hRegs
    · intro r hr
      apply mmaStepReg (by omega) hRange.2 _ step
      intro i hc
      have hAt : ((kernel.code.drop 1907).take (2768-1907))[t.pc-1907]? = some i := by
        rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
          Nat.add_sub_of_le hRange.1, hc]
      have hCode := List.all_eq_true.mp hAudit i (List.mem_of_getElem? hAt)
      simpa using List.all_eq_true.mp hCode r hr
    · intro _ h
      exact List.mem_map_of_mem h
  induction hw generalizing index with
  | stop => simp at he
  | @tau t u es vs ht hw ih =>
    obtain ⟨hRange | hExit, hFrame⟩ := mmaCutStep hs.1 hs.2 (.inl ⟨rfl, ht⟩) hShape
    · exact ih hRange hFrame (frame hs hF (.inl ⟨rfl,ht⟩)) he hBound
    · have hRet := mmaEpilogueExitEvents (by simpa using hExit.1) hExit.2 (.inl rfl)
        hFrame.2 hw _ (List.mem_of_getElem? he)
      omega
  | @ev t u v es vs hv hw ih =>
    obtain ⟨hRange, hFrame⟩ := mmaCutStep hs.1 hs.2 (.inr ⟨_, rfl, hv⟩) hShape
    have hRegs := frame hs hF (.inr ⟨_,rfl,hv⟩)
    cases index with
    | zero =>
      obtain rfl := Option.some.inj he
      exact ⟨t, u, _, hv, hFrame, hRegs, hw⟩
    | succ index =>
      have hGet : es[index]? = some e := he
      have hLen : index + 1 < es.length := by simp only [List.length_cons] at hBound; omega
      rcases hRange with h | hExit
      · exact ih h hFrame hRegs hGet hLen
      · have hRet := mmaEpilogueExitEvents (by simpa using hExit.1) hExit.2 (.inl rfl)
          hFrame.2 hw _ (List.mem_of_getElem? hGet)
        omega
  | last => simp at hBound

/-- Reach the actual continuation of an indexed MMA event while retaining the role frame. -/
theorem pvRoleAfterEvent {l : Launch} {g index : Nat} {s : TState} {e : Event}
    {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs) (hs : 1907 ≤ s.pc ∧ s.pc < 2768)
    (hShape : RoleShape s ∧ s.regs 1062 = some (b32 12))
    (he : es[index]? = some e) (hBound : index + 1 < es.length) (hLate : e.pc < 2768) :
    ∃ t u post, EStep kernel Assumptions.all l g t e (some u) ∧
      (RoleShape u ∧ u.regs 1062 = some (b32 12)) ∧
      Walk kernel Assumptions.all l g u (es.drop (index + 1)) post := by
  have hAudit : ((kernel.code.drop 1907).take (2768-1907)).all
      (fun i => ([] : List Nat).all (fun r => !(mmaWrites i.op).contains r)) = true := by
    simp
  obtain ⟨t,u,post,hStep,hFrame,_,hWalk⟩ :=
    pvRoleAfterEventFramed (F := []) hAudit hw hs hShape trivial he hBound hLate
  exact ⟨t,u,post,hStep,hFrame,hWalk⟩

/-- A checkpoint on the path to a later recorded event cannot be faulted. -/
theorem normalBeforeLaterEvent {l : Launch} {g : Nat} {s : TState} {e : Event}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (he : e ∈ es) (hLate : s.pc < e.pc) : s.fault = none := by
  cases hf : s.fault with
  | none => rfl
  | some fault =>
    cases hw with
    | stop => simp at he
    | tau ht _ => simp [Tau, out, hf] at ht
    | ev hv _ =>
      obtain ⟨tm, hout, hFire⟩ := hv
      simp only [out, hf, Out.ev.injEq] at hout
      subst tm
      cases hFire.2
    | last hv =>
      obtain rfl := List.mem_singleton.mp he
      have := estep_source_pc hv
      omega

/-- The next observed event of an eventful checkpoint has its genuine successor. -/
theorem pvWalkEvent {l : Launch} {g : Nat} {s : TState} {target : Event} {tm : Tmpl}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hOut : out kernel Assumptions.all l g s = .ev tm)
    (he : target ∈ es) (hLate : s.pc < target.pc) :
    ∃ u e tail post, es = e :: tail ∧ Fires s.pc tm e (some u) ∧
      EStep kernel Assumptions.all l g s e (some u) ∧
      Walk kernel Assumptions.all l g u tail post ∧ target ∈ tail := by
  cases hw with
  | stop => simp at he
  | tau ht _ => simp [Tau, hOut] at ht
  | @ev t u e es vs hv hw =>
    have hMem := (List.mem_cons.mp he).resolve_left (fun h => by
      rw [h] at hLate
      have := estep_source_pc hv
      omega)
    obtain ⟨tm', hTpl, hFire⟩ := hv
    have hEq := Out.ev.inj (hOut.symm.trans hTpl)
    subst tm'
    exact ⟨u, e, es, vs, rfl, hFire, ⟨_, hTpl, hFire⟩, hw, hMem⟩
  | last hv =>
    obtain rfl := List.mem_singleton.mp he
    have := estep_source_pc hv
    omega

end
end PTX.Kernels.TmlFa4Fwd.Mma
