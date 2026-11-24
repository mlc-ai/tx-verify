-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRingVisits

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

def loaderPipelineCutOp (lower cut branch : Nat) (keep : List Nat) (op : Op) : Bool :=
  keep.all (fun r => !(loaderRingWrites op).contains r) &&
    (match op with
    | .bra target _ => lower ≤ target && (target ≤ cut || branch < target)
    | .brx .. => false
    | _ => true)

private theorem pipelineTargets {lower cut branch pc : Nat} {op : Op}
    (h : (match op with
      | .bra target _ => lower ≤ target && (target ≤ cut || branch < target)
      | .brx .. => false | _ => true) = true) :
    (∀ target, ¬ BrxTarget op target) ∧
      (nextPc op pc = pc + 1 ∨ lower ≤ nextPc op pc ∧
        (nextPc op pc ≤ cut ∨ branch < nextPc op pc)) := by
  cases op <;> simp only [Bool.false_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h
  case bra target uni => exact ⟨by simp [BrxTarget], .inr h⟩
  all_goals exact ⟨by simp [BrxTarget], .inl rfl⟩

theorem pipelineCutStep {l : Launch} {g lower cut branch : Nat} {s u : TState}
    {ev : Option Event} {F : List (Nat × Value)}
    (hLower : 174 ≤ lower) (hLimit : cut ≤ 1901)
    (hPC : lower ≤ s.pc ∧ s.pc < cut)
    (hCode : ((kernel.code.drop lower).take (cut - lower)).all
      (fun ins => loaderPipelineCutOp lower cut branch (F.map Prod.fst) ins.op) = true)
    (hw : WStep kernel Assumptions.all l g s ev u) (hs : RingShape s) (hF : Holds s.regs F) :
    lower ≤ u.pc ∧ (u.pc ≤ cut ∨ branch < u.pc) ∧ RingShape u ∧ Holds u.regs F := by
  have checked {ins : Instr} (hc : kernel.code[s.pc]? = some ins) :
      loaderPipelineCutOp lower cut branch (F.map Prod.fst) ins.op = true := by
    have hGet : ((kernel.code.drop lower).take (cut - lower))[s.pc - lower]? = some ins := by
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hPC.1]
      exact hc
    exact List.all_eq_true.mp hCode ins (List.mem_of_getElem? hGet)
  have hFrame {r : Nat} (hr : r ∈ F.map Prod.fst) :
      ∀ ins, kernel.code[s.pc]? = some ins → r ∉ loaderRingWrites ins.op := by
    intro ins hc
    have h := (Bool.and_eq_true_iff.mp (checked hc)).1
    simpa using List.all_eq_true.mp h r hr
  have hRegs := Epilogue.holdsSchedulerFrame hF
    (fun _ hr => loaderPipelineStepRegs (by omega) (by omega) (hFrame hr) hw)
    (fun _ h => List.mem_map_of_mem h)
  have hNext : lower ≤ u.pc ∧ (u.pc ≤ cut ∨ branch < u.pc) := by
    rcases hw with ⟨-, ht⟩ | ⟨e, -, he⟩
    · have ht' : Tau kernel [] l g s u := by
        unfold Tau at ht ⊢
        rwa [← loaderOutCore (by omega) (by omega)]
      obtain ⟨ins, hc⟩ := tau_core_has_code ht'
      obtain ⟨hNo, hTar⟩ := pipelineTargets (pc := s.pc) (Bool.and_eq_true_iff.mp (checked hc)).2
      rcases tau_core_frame hc ht' with rfl | h
      · change lower ≤ s.pc + 1 ∧ (s.pc + 1 ≤ cut ∨ branch < s.pc + 1)
        omega
      · rw [h.pc.resolve_right (hNo _)]
        rcases hTar with ht | ht
        · rw [ht]
          omega
        · exact ht
    · have he' : EStep kernel [] l g s e (some u) := by
        obtain ⟨tmpl, hout, hf⟩ := he
        exact ⟨tmpl, by rwa [← loaderOutCore (by omega) (by omega)], hf⟩
      rcases (estep_return_pc he' (fun _ _ _ h => execLocal_frame h)).2 with hp | hp <;> omega
  exact ⟨hNext.1, hNext.2, loaderPipelineStepShape (by omega) (by omega) hs hw, hRegs⟩

theorem visitsBeforeBranch {l : Launch} {g branch : Nat} {s : TState}
    (hp : 174 ≤ s.pc ∧ s.pc < 1906) (hb : s.pc < branch) (e : Option Event)
    (vs : List Visit) :
    loaderVisitsAt branch (visit kernel l g s e :: vs) = loaderVisitsAt branch vs := by
  unfold loaderVisitsAt loaderVisits
  rw [List.takeWhile_cons, visit_pc]
  split
  · rw [List.countP_cons, visit_pc]
    simp [hb.ne]
  · rename_i h
    exact (h (decide_eq_true hp)).elim

theorem pipelineStopped {l : Launch} {g branch : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hf : s.fault ≠ none) (hp : 174 ≤ s.pc ∧ s.pc < 1906) (hb : s.pc < branch) :
    loaderVisitsAt branch vs = 0 := by
  cases h : s.fault
  · exact (hf h).elim
  case some f =>
    cases hw with
    | stop => rfl
    | tau ht _ => simp [Tau, out, h] at ht
    | ev hr _ =>
      obtain ⟨tmpl, hout, hF⟩ := hr
      simp only [out, h, Out.ev.injEq] at hout
      subst tmpl
      cases hF.2
    | last _ => rw [visitsBeforeBranch hp hb]; rfl

theorem pipelineAtCut {s : TState} {pc : Nat} {F : List (Nat × Value)}
    (hp : s.pc = pc) (hs : RingShape s) (hF : Holds s.regs F)
    (hf : s.fault = none) (hl : ∃ ins, kernel.code[pc]? = some ins ∧ ins.op.isLocal = true) :
    At s pc F := by
  have hSub : s.sub = 0 := by
    by_contra hBad
    obtain ⟨op, hC, _, hOp⟩ := hs.1.2 (by have := hs.1.1; omega)
    obtain ⟨ins, hCode, hLocal⟩ := hl
    rw [hp, hCode] at hC
    have hop := congrArg Instr.op (Option.some.inj hC)
    change ins.op = op at hop
    rw [hop, hOp] at hLocal
    cases hLocal
  exact ⟨hp, hSub, hs.2 hSub, hf, hF⟩

theorem ringShapeOfAt {s : TState} {pc : Nat} {F : List (Nat × Value)}
    (hs : At s pc F) : RingShape s :=
  ⟨⟨by rw [hs.2.1]; decide, fun h => (Nat.zero_ne_one (hs.2.1.symm.trans h)).elim⟩,
    fun _ => hs.2.2.1⟩

/-- Before a certified pipeline checkpoint, the counted branch is unreachable
except through that checkpoint. An instruction may also leave the counted role
interval, after which there are no visits to its branch. -/
theorem loaderPrefixThroughCounter {l : Launch} {g lower cut branch budget : Nat}
    {s : TState} {es : List Event} {vs : List Visit} {F : List (Nat × Value)}
    (hLo : 174 ≤ lower) (hCut : cut ≤ 1901) (hHi : cut < branch)
    (hTarget : ∃ ins, kernel.code[cut]? = some ins ∧ ins.op.isLocal = true)
    (hCode : ((kernel.code.drop lower).take (cut - lower)).all
      (fun ins => loaderPipelineCutOp lower cut branch
        (F.map Prod.fst) ins.op) = true)
    (onTarget : ∀ {t ts tv}, At t cut F → Walk kernel Assumptions.all l g t ts tv →
      loaderVisitsAt branch tv ≤ budget)
    (hAfter : ∀ {t events visits}, branch < t.pc →
      Walk kernel Assumptions.all l g t events visits → loaderVisitsAt branch visits = 0)
    (hw : Walk kernel Assumptions.all l g s es vs) (hp : lower ≤ s.pc ∧ s.pc ≤ cut)
    (hs : RingShape s) (hF : Holds s.regs F) :
    loaderVisitsAt branch vs ≤ budget := by
  have atCut {t : TState} {events : List Event} {visits : List Visit}
      (hW : Walk kernel Assumptions.all l g t events visits)
      (hp : t.pc = cut) (hs : RingShape t) (hF : Holds t.regs F) :
      loaderVisitsAt branch visits ≤ budget := by
    by_cases hf : t.fault = none
    · exact onTarget (pipelineAtCut hp hs hF hf hTarget) hW
    · rw [pipelineStopped hW hf ⟨by omega, by omega⟩ (hp.trans_lt hHi)]
      exact Nat.zero_le _
  have step {t u : TState} {e : Option Event} {ts : List Event} {tv : List Visit}
      (hW : Walk kernel Assumptions.all l g u ts tv)
      (hFull : Walk kernel Assumptions.all l g t (e.toList ++ ts)
        (visit kernel l g t e :: tv))
      (hpc : lower ≤ t.pc ∧ t.pc ≤ cut) (ht : RingShape t) (hF : Holds t.regs F)
      (hStep : WStep kernel Assumptions.all l g t e u)
      (ih : (lower ≤ u.pc ∧ u.pc ≤ cut) → RingShape u → Holds u.regs F →
        loaderVisitsAt branch tv ≤ budget) :
      loaderVisitsAt branch (visit kernel l g t e :: tv) ≤ budget := by
    by_cases h : t.pc = cut
    · exact atCut hFull h ht hF
    have hc : t.pc < cut := by omega
    rw [visitsBeforeBranch ⟨by omega, by omega⟩ (hc.trans hHi)]
    obtain ⟨hU, hL | hR, hShape, hRegs⟩ := pipelineCutStep hLo hCut ⟨hpc.1, hc⟩ hCode hStep ht hF
    · exact ih ⟨hU, hL⟩ hShape hRegs
    · exact (hAfter hR hW).le.trans (Nat.zero_le _)
  induction hw with
  | stop => exact Nat.zero_le _
  | tau ht hw ih => exact step hw (.tau ht hw) hp hs hF (.inl ⟨rfl, ht⟩) ih
  | ev he hw ih => exact step hw (.ev he hw) hp hs hF (.inr ⟨_, rfl, he⟩) ih
  | last =>
    rw [visitsBeforeBranch ⟨by omega, by omega⟩ (hp.2.trans_lt hHi)]
    exact Nat.zero_le _

/-- Before a certified pipeline checkpoint, the counted branch is unreachable
except through that checkpoint. An instruction may also leave the counted role
interval, after which there are no visits to its branch. -/
theorem loaderPrefixThroughCheckpoint (j : Fin 2) {l : Launch} {g lower cut budget : Nat}
    {s : TState} {es : List Event} {vs : List Visit} {F : List (Nat × Value)}
    (hLo : 174 ≤ lower) (hCut : cut ≤ 1901) (hHi : cut < (ringCounterSite j).branch)
    (hTarget : ∃ ins, kernel.code[cut]? = some ins ∧ ins.op.isLocal = true)
    (hCode : ((kernel.code.drop lower).take (cut - lower)).all
      (fun ins => loaderPipelineCutOp lower cut (ringCounterSite j).branch
        (F.map Prod.fst) ins.op) = true)
    (onTarget : ∀ {t ts tv}, At t cut F → Walk kernel Assumptions.all l g t ts tv →
      loaderVisitsAt (ringCounterSite j).branch tv ≤ budget)
    (hw : Walk kernel Assumptions.all l g s es vs) (hp : lower ≤ s.pc ∧ s.pc ≤ cut)
    (hs : RingShape s) (hF : Holds s.regs F) :
    loaderVisitsAt (ringCounterSite j).branch vs ≤ budget :=
  loaderPrefixThroughCounter hLo hCut hHi hTarget hCode onTarget
    (fun hAfter hWalk => noLaterRingBranchVisits j hWalk hAfter) hw hp hs hF

end
end PTX.Kernels.TmlFa4Fwd.Loader
