-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Adv
import Kernels.InklingRelDecode.Proof.Softmax.Data.Rescale
import Kernels.InklingRelDecode.Gen.TypedLateLane01
import Kernels.InklingRelDecode.Gen.TypedLate01
import Kernels.InklingRelDecode.Flow.Code.Part008
import Kernels.InklingRelDecode.Flow.Code.Part015
import Kernels.InklingRelDecode.Flow.Code.Part035
import Kernels.InklingRelDecode.Flow.Code.Part036
import Lemmas.Flow.Step.TcSteps
import Kernels.InklingRelDecode.Flow.Code.Part034
import Kernels.InklingRelDecode.Gen.StepSoftmax10
import Kernels.InklingRelDecode.Gen.StepSoftmax39
import Lemmas.Flow.IssueNext

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

set_option maxRecDepth 100000

variable {e : Control.Entry} {L : Launch} {g i : Nat} {v : Control.Carry} {w : Data.Vals}

theorem sstep_setMaxReg (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.setMaxReg, i, v⟩, w⟩ ev := by
  refine adv_soft (d := ⟨⟨.setMaxReg, i, v⟩, w⟩) (dn := ⟨⟨.bar0, i, v⟩, w⟩) (p := 574) rfl
    Flow.code_574
    (fun _ hf => by obtain ⟨_, _, h⟩ := hf; exact Option.some.inj h)
    (fun ev => by obtain ⟨_, k⟩ := ev; cases k <;> rfl)
    (fun hi => ⟨hi.entry, hi.thread, hi.bound, fun _ => hi.init (.inl rfl), nofun, nofun, nofun,
      fun _ _ h => absurd rfl h⟩) (by decide +kernel) (by decide +kernel) ?_ ev
  exact SegQ.weaken fun _ h => h

set_option hygiene false in
macro "soft_span " a:num ", " b:num : tactic => `(tactic|
  (change SegQ kernel Assumptions.all L g (QTF lateQt) $a
      (_ ++ factsFrom (Control.ctlLive $a) _) $b (_ ++ factsFrom (Control.ctlLive $b) _)
   simp only [Data.dF, Data.dFS, Data.inRound, Bool.false_eq_true, ↓reduceIte, List.append_nil,
    List.cons_append, List.nil_append]
   late_ctl $a, $b using late_vals))

theorem sstep_bar20 (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.bar20, i, v⟩, w⟩ ev := by
  refine adv_soft (d := ⟨⟨.bar20, i, v⟩, w⟩) (dn := ⟨⟨.tmemSt, i, v⟩, w⟩) (p := 999) rfl
    Flow.code_999 (fun _ => fires_barSyncN_next) (fun ev => by obtain ⟨_, k⟩ := ev; cases k <;> rfl)
    (fun hi => Control.body_inv hi rfl rfl) (by decide +kernel) (by decide +kernel) ?_ ev
  refine SegQ.comp (b := 1008) (G := Data.dF L ⟨⟨.bar20, i, v⟩, w⟩ ++
    factsFrom ((Control.ctlLive 1009).filter (· ∈ Control.ctlLive 1000))
      (Control.valueOf e L g ⟨.bar20, i, v⟩)) ?_ ?_
  · win lw_l01_1000
  · refine SegQ.tauAll _ ?_
    simp only [Data.dF, Data.dFS, Data.inRound, Bool.false_eq_true, ↓reduceIte, List.append_nil,
      List.cons_append, List.nil_append]
    late_ctl 1008, 1009 using late_vals

theorem sstep_tmemSt (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.tmemSt, i, v⟩, w⟩ ev := by
  refine adv_soft (d := ⟨⟨.tmemSt, i, v⟩, w⟩) (dn := ⟨⟨.tmemWait, i, v⟩, w⟩) (p := 1009) rfl
    Flow.code_1009 (fun hp hf => fires_tcSt_next (by rw [hp]; decide +kernel) hf)
    (fun ev => by obtain ⟨_, k⟩ := ev; cases k <;> rfl)
    (fun hi => Control.body_inv hi rfl rfl) (by decide +kernel) (by decide +kernel) ?_ ev
  exact SegQ.weaken fun _ h => h

theorem sstep_tmemWait (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.tmemWait, i, v⟩, w⟩ ev := by
  refine adv_soft (d := ⟨⟨.tmemWait, i, v⟩, w⟩) (dn := ⟨⟨.bar21, i, v⟩, w⟩) (p := 1010) rfl
    Flow.code_1010 (fun _ => fires_tcWaitSt_next)
    (fun ev => by obtain ⟨_, k⟩ := ev; cases k <;> rfl)
    (fun hi => Control.body_inv hi rfl rfl) (by decide +kernel) (by decide +kernel) ?_ ev
  refine SegQ.tauAll _ ?_
  simp only [Data.dF, Data.dFS, Data.inRound, Bool.false_eq_true, ↓reduceIte, List.append_nil,
    List.cons_append, List.nil_append]
  late_ctl 1011, 1012 using late_vals

theorem sstep_bar22 (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.bar22, i, v⟩, w⟩ ev := by
  refine adv_soft (d := ⟨⟨.bar22, i, v⟩, w⟩) (dn := ⟨⟨.shfl7, i, v⟩, w⟩) (p := 2241) rfl
    Flow.code_2241 (fun _ => fires_barSyncN_next)
    (fun ev => by obtain ⟨_, k⟩ := ev; cases k <;> rfl)
    (fun hi => Control.body_inv hi rfl rfl) (by decide +kernel) (by decide +kernel) ?_ ev
  exact SegQ.weaken fun _ h => h

theorem sstep_bar23 (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.bar23, i, v⟩, w⟩ ev := by
  refine adv_soft (d := ⟨⟨.bar23, i, v⟩, w⟩) (dn := ⟨⟨.ldL, i, v⟩, w⟩) (p := 2251) rfl
    Flow.code_2251 (fun _ => fires_barSyncN_next)
    (fun ev => by obtain ⟨_, k⟩ := ev; cases k <;> rfl)
    (fun hi => Control.body_inv hi rfl rfl) (by decide +kernel) (by decide +kernel) ?_ ev
  exact SegQ.weaken fun _ h => h

theorem sstep_stO (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.stO, i, v⟩, w⟩ ev := by
  refine adv_soft (d := ⟨⟨.stO, i, v⟩, w⟩) (dn := ⟨⟨.waitStO, i, v⟩, w⟩) (p := 2328) rfl
    Flow.code_2328 (fun hp hf => fires_tcSt_next (by rw [hp]; decide +kernel) hf)
    (fun ev => by obtain ⟨_, k⟩ := ev; cases k <;> rfl)
    (fun hi => Control.body_inv hi rfl rfl) (by decide +kernel) (by decide +kernel) ?_ ev
  refine SegQ.weaken fun _ hR => holds_of_forall fun p hp => holds_mem hR ?_
  rcases List.mem_append.mp hp with h | h
  · refine List.mem_append_left _ ?_
    simp [Data.dF, Data.dFS, Data.inRound] at h
    exact Data.round_sub_rs2 w _ (by simpa using h)
  · exact List.mem_append_right _ h

theorem sstep_store10 (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.store10, i, v⟩, w⟩ ev := by
  refine Code.StepForQP.ofInv fun hinv => Code.StepForQ.toP _ (Code.vstF (C := Data.code e L g)
    (d := ⟨⟨.store10, i, v⟩, w⟩) (dn := ⟨⟨.bar23, i, v⟩, w⟩) Flow.code_2250 rfl
    (fun ev => by obtain ⟨_, k⟩ := ev; cases k <;> rfl) rfl
    (fun h => (Nat.lt_irrefl 1 h).elim)
    (by change afterF lateQt 2250 [] = true; decide +kernel)
    (fun _ => ⟨rfl, rfl, Control.body_inv hinv rfl rfl,
      seg_adj (fun _ h => h) rfl (by dsimp only; decide +kernel)⟩) ev)

/-- The words of the table of pc 2253 other than the loaded one are those of pc 2252. -/
theorem other_word (e : Control.Entry) (x : Value) {r : Nat} (hr : r ∈ Control.ctlLive 2253)
    (h : r ≠ 1542) :
    Control.valueOf e L g ⟨.shfl11, i, {v with word := x}⟩ r =
      Control.valueOf e L g ⟨.ldL, i, v⟩ r := by
  have free : ∀ r ∈ Control.ctlLive 2253, r = 1542 ∨ r ∉ [1542, 1544, 1534, 1536, 1538, 1540] := by
    decide +kernel
  have off := (free r hr).resolve_left h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at off
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := off
  simp only [Control.valueOf, h1, h2, h3, h4, h5, h6, ↓reduceIte]

theorem sstep_ldL (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.ldL, i, v⟩, w⟩ ev := by
  refine Code.StepForQP.ofInv fun hinv => Code.ldWFP (C := Data.code e L g)
    (d := ⟨⟨.ldL, i, v⟩, w⟩) (f := fun x => ⟨⟨.shfl11, i, {v with word := x}⟩, w⟩)
    (Pv := Dat32) (tr := .dat32) Flow.code_2252 rfl rfl rfl rfl
    ?_ ?_ rfl rfl
    (facts_ne (by dsimp only; decide +kernel) (by dsimp only; decide +kernel))
    (fun x hx => ⟨x, rfl, hx⟩)
    (by change afterF lateQt 2252 _ = true; decide +kernel) (fun x hx => ?_) ev
  · exact fun _ he hpc x bs hk => he.ld hpc x bs hk
  · intro x bs y hy _
    simp [Data.succ, Control.next, Data.record, Lib.loadWord, hy]
    rfl
  · refine ⟨rfl, rfl, Control.body_inv hinv rfl rfl, ?_⟩
    refine SegQ.weaken fun _ hR => holds_of_forall fun q hq => holds_mem hR ?_
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
      change r ∈ Control.ctlLive 2253 at hr
      by_cases h1 : r = 1542
      · subst h1
        exact List.mem_cons_self ..
      · refine List.mem_cons_of_mem _ (List.mem_append_left _ ?_)
        rw [other_word e x hr h1]
        exact mem_factsFrom (by
          have key : ∀ r ∈ Control.ctlLive 2253, r = 1542 ∨ r ∈ Control.ctlLive 2252 := by
            decide +kernel
          exact (key r hr).resolve_left h1)
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ h)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
