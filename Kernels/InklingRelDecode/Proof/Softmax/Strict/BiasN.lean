-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Bias
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.BiasC
import Kernels.InklingRelDecode.Proof.Softmax.Strict.Vals
public import Lemmas.Flow.TypedIntG
import Kernels.InklingRelDecode.Flow.Code
@[expose] public section
/-! # The strict step of the loop's bias loads (pcs 1124 to 1250) -/
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt
set_option maxRecDepth 100000
variable {e : Control.Entry} {L : Launch} {g i : Nat} {v : Control.Carry} {w : Data.Vals}

theorem nxt_ld : ∀ j < 63, ldOk (1124 + 2 * j) 92 (if j = 0 then 332 else 333 + j) = true := by
  decide +kernel

theorem nxt_off : ∀ j < 63,
    (if j = 0 then 332 else 333 + j) ∉ Control.ctlLive (1124 + 2 * j) := by
  decide +kernel

theorem nxt_sub : ∀ j < 63, ∀ r ∈ Control.ctlLive (1124 + 2 * j + 2),
    r ∈ Control.ctlLive (1124 + 2 * j) ∧ r ≠ 334 + j := by
  decide +kernel

/-- **A loop load but the last** continues at the next one. -/
theorem sstep_nxt (j : Fin 64) (hj : j.val + 1 < 64) (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.nxt j, i, v⟩, w⟩ ev := by
  have hj' : j.val < 63 := by omega
  have h1 := nxt_ld j.val hj'
  have h2 := nxt_off j.val hj'
  have h3 := nxt_aft j.val hj'
  have h6 := nxt_nk j.val hj'
  have h4 := nxt_mv j.val hj'
  have h5 := nxt_sub j.val hj'
  apply ld_soft (d := ⟨⟨.nxt j, i, v⟩, w⟩) (p := 1124 + 2 * j.val)
    (r := if j.val = 0 then 332 else 333 + j.val)
    (f := fun y => ⟨⟨.nxt ⟨j.val + 1, hj⟩, i, v⟩, {w with ld := Function.update w.ld j.val y}⟩)
    rfl h1 ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩ ?_ ?_ ?_ h3 h6 (fun y => ?_)
  · exact facts_ne h2 (by
      by_cases h0 : j.val = 0
      · simp [Data.dKeys, Data.inRound, h0]
      · simp [Data.dKeys, Data.inRound, h0]; omega)
  · intro x bs y hy
    simp [Data.succ, Control.next, Data.record, Lib.loadWord, hy, hj, Except.toOption]
  · intro y hi
    refine ⟨hi.entry, hi.thread, hi.bound, (by rintro (h | h) <;> cases h), nofun,
      fun _ _ => hi.nxt j rfl, nofun, fun _ _ _ _ => hi.loop nofun nofun nofun (fun _ => nofun)⟩
  · have e2 : 1124 + 2 * (j.val + 1) = 1124 + 2 * j.val + 2 := by omega
    refine mv_seg (p := 1124 + 2 * j.val) (r := 334 + j.val) (by omega)
      ((fp3_of (a := 1125) (b := 1251) (by decide +kernel)).mono (by omega) (by omega)) h4 ?_ ?_
    · intro q hq
      rcases List.mem_append.mp hq with h | h
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
        exact (h5 r (by rw [← e2]; exact hr)).2
      · have h' : q ∈ [(498, Data.scaleW L), (1914, w.m)] := h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
        rcases h' with rfl | rfl <;> simp <;> omega
    · intro q hq
      rcases List.mem_append.mp hq with h | h
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
        exact List.mem_cons_of_mem _ (List.mem_append_left _
          (mem_factsFrom (h5 r (by rw [← e2]; exact hr)).1))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ h)

theorem nxt_last_ld : ldOk 1250 92 396 = true := by decide +kernel

/-- **The last loop load** continues at the poll. -/
theorem sstep_nxt_last (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.nxt 63, i, v⟩, w⟩ ev := by
  apply ld_soft (d := ⟨⟨.nxt 63, i, v⟩, w⟩) (p := 1250) (r := 396)
    (f := fun y => ⟨⟨.waitS, i, v⟩, {w with ld := Function.update w.ld 63 y}⟩)
    rfl nxt_last_ld (by omega) ?_ ?_ ?_ nxt_last_aft nxt_last_nk (fun y => ?_)
  · exact facts_ne (by dsimp only; decide +kernel) (by dsimp only; decide +kernel)
  · intro x bs y hy
    simp [Data.succ, Control.next, Data.record, Lib.loadWord, hy, Except.toOption]
  · intro y hi
    exact ⟨hi.entry, hi.thread, hi.bound, (by rintro (h | h) <;> cases h), nofun, nofun, nofun,
      fun _ _ _ _ => hi.loop nofun nofun nofun (fun _ => nofun)⟩
  · refine SegQ.laneConv _ (a := 1251) (b := 1257) (F' := Data.dF L ⟨⟨.nxt 63, i, v⟩, w⟩ ++
      factsFrom (Control.ctlLive 1251) (Control.valueOf e L g ⟨.nxt 63, i, v⟩)) (G' := Data.dF L
      ⟨⟨.nxt 63, i, v⟩, w⟩ ++ factsFrom (Control.ctlLive 1257)
      (Control.valueOf e L g ⟨.nxt 63, i, v⟩)) ?_ ?_ ?_
    · intro p hp
      rcases List.mem_append.mp hp with h | h
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ h)
      · exact List.mem_cons_of_mem _ (ctl_in (w := w) (.nxt 63) (q := 1251)
          (by decide +kernel : Site.pc (.nxt 63) = 1250) (by decide +kernel) p h)
    · intro p hp
      obtain h | h := List.mem_append.mp
        (ctl_out (w := {w with ld := Function.update w.ld 63 y}) .waitS
          (by decide +kernel : Site.pc .waitS = 1257) p hp)
      · exact List.mem_append_right _ h
      · exact List.mem_append_left _ (by simpa [Data.dF, Data.dFS, Data.inRound] using h)
    · simp only [Data.dF, Data.dFS, Data.inRound, Bool.false_eq_true, ↓reduceIte, List.append_nil,
        List.cons_append, List.nil_append]
      late_ctl 1251, 1257 using late_vals2

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
