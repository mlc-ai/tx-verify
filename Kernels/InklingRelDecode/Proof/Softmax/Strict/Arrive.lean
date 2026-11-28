-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.RouteD
import Kernels.InklingRelDecode.Proof.Softmax.Steps.LoopRoute
import Kernels.InklingRelDecode.Flow.Code
@[expose] public section
/-! # The strict steps of the arrival at `p_ready` and of the barrier before it -/
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt
set_option maxRecDepth 100000
variable {e : Control.Entry} {L : Launch} {g i : Nat} {v : Control.Carry} {w : Data.Vals}

theorem loopSite_ne (e : Control.Entry) (t i : Nat) : Control.loopSite e t i ≠ .arrive := by
  unfold Control.loopSite
  split
  · decide
  · split <;> decide

/-- **The loop's head and route** from pc 1014 to the site of the next state. -/
theorem head_route (ok : e.Ok) (hi : i < e.limit) (w : Data.Vals) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 1014
      (RF e L g w.m i v 1014) (Control.loopSite e (g % L.block) (i + 1)).pc
      (RF e L g w.m (i + 1) v (Control.loopSite e (g % L.block) (i + 1)).pc) := by
  refine (head_loop i v w (by have := ok.blockWord; have := ok.limitEq; split at this <;> omega)
    (by omega) .arrive).comp ?_
  by_cases h1 : i + 1 = e.limit
  · have hs : Control.loopSite e (g % L.block) (i + 1) = .epilogue := by simp [Control.loopSite, h1]
    rw [hs]
    exact route_to_epi _ ok h1
  · by_cases h2 : Control.nextEnabled e (g % L.block) (i + 1) = true
    · have hs : Control.loopSite e (g % L.block) (i + 1) = .nxt 0 := by
        simp [Control.loopSite, h1, h2]
      rw [hs]
      exact route_to_nxt _ ok (by omega) h1
    · have hs : Control.loopSite e (g % L.block) (i + 1) = .waitS := by
        simp [Control.loopSite, h1, h2]
      rw [hs]
      exact route_to_wait _ ok (by omega) h1 (by simpa using h2)

theorem loopSite_cases (e : Control.Entry) (t i : Nat) : Control.loopSite e t i = .waitS ∨
    Control.loopSite e t i = .nxt 0 ∨ Control.loopSite e t i = .epilogue := by
  unfold Control.loopSite
  split
  · exact .inr (.inr rfl)
  · split
    · exact .inr (.inl rfl)
    · exact .inl rfl

/-- The data facts of a site that follows the loop's head are among the head's. -/
theorem dF_loop (e : Control.Entry) (t i : Nat) (v : Data.Vals) (c : Control.Carry) (j : Nat) :
    ∀ p ∈ Data.dF L ⟨⟨Control.loopSite e t i, j, c⟩, v⟩,
      p ∈ [(498, Data.scaleW L), (1914, v.m)] := by
  intro p hp
  rcases loopSite_cases e t i with h | h | h <;>
    simp [Data.dF, Data.dFS, Data.inRound, h] at hp ⊢ <;> simp [hp]

/-- **The arrival at `p_ready` continues** at the loop's next site. -/
theorem sstep_arrive (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.arrive, i, v⟩, w⟩ ev := by
  refine Code.StepForQP.ofInv fun hinv => ?_
  have lt : i < e.limit := hinv.loop nofun nofun nofun (fun _ => nofun)
  apply adv_soft (d := ⟨⟨.arrive, i, v⟩, w⟩) (dn := ⟨Control.advance e (g % L.block)
    ⟨.arrive, i, v⟩, {w with cur := w.ld, ld := fun _ => Data.dflt}⟩) (p := 1013) rfl
    Flow.code_1013 (fun _ hf => Code.fires_arrive_next hf) (fun ev => ?_)
    (fun hi => Control.loop_inv (i := i + 1) hi.entry hi.thread (by omega)) (by decide +kernel)
    (by decide +kernel) ?_
  · refine SegQ.endIn (head_route hinv.entry lt w) fun p hp => ?_
    rcases List.mem_append.mp hp with h | h
    · exact List.mem_append_left _ (dF_loop e (g % L.block) (i + 1) _ _ _ p h)
    · exact List.mem_append_right _ h
  · simp [Data.succ, Control.next, Data.record, Control.advance, loopSite_ne]

/-- **The barrier before the arrival** continues at the arrival, or past it at the next site. -/
theorem sstep_bar21 (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.bar21, i, v⟩, w⟩ ev := by
  refine Code.StepForQP.ofInv fun hinv => ?_
  have lt : i < e.limit := hinv.loop nofun nofun nofun (fun _ => nofun)
  rcases em (g % L.block % 128 = 0) with lead | lead
  · apply adv_soft (d := ⟨⟨.bar21, i, v⟩, w⟩) (dn := ⟨⟨.arrive, i, v⟩, w⟩) (p := 1012) rfl
      Flow.code_1012 (fun _ => fires_barSyncN_next)
      (fun ev => by simp [Data.succ, Control.next, Data.record, lead])
      (fun hi => ⟨hi.entry, hi.thread, hi.bound, (by rintro (h | h) <;> cases h), nofun, nofun,
        fun _ => lead, fun _ _ _ _ => lt⟩) (by decide +kernel) (by decide +kernel) ?_
    exact SegQ.weaken fun _ h => h
  · apply adv_soft (d := ⟨⟨.bar21, i, v⟩, w⟩) (dn := ⟨Control.advance e (g % L.block)
      ⟨.bar21, i, v⟩, {w with cur := w.ld, ld := fun _ => Data.dflt}⟩) (p := 1012) rfl
      Flow.code_1012 (fun _ => fires_barSyncN_next) (fun ev => ?_)
      (fun hi => Control.loop_inv (i := i + 1) hi.entry hi.thread (by omega))
      (by decide +kernel) (by decide +kernel) ?_
    · have off : (177, Value.pred false) ∈ factsFrom (Control.ctlLive 1013)
          (Control.valueOf e L g ⟨.bar21, i, v⟩) := by
        have : Control.valueOf e L g ⟨.bar21, i, v⟩ 177 = .pred false := by
          simp [Control.valueOf, Control.scalarValue, lead]
        exact this ▸ mem_factsFrom (by decide +kernel)
      refine SegQ.comp (b := 1014) (G := RF e L g w.m i v 1014) (SegQ.tauAll _ (SegQF.skipGS
        (qt := lateQt) Flow.code_1013 (fun _ hR => holds_mem hR (List.mem_append_right _ off))
        rfl (fun _ hR => holds_of_forall fun p hp => holds_mem hR
        (sub_facts (fun _ h => h) (by dsimp only; decide +kernel) p hp))
        (by dsimp only; decide +kernel))) ?_
      refine SegQ.endIn (head_route hinv.entry lt w) fun p hp => ?_
      rcases List.mem_append.mp hp with h | h
      · exact List.mem_append_left _ (dF_loop e (g % L.block) (i + 1) _ _ _ p h)
      · exact List.mem_append_right _ h
    · simp [Data.succ, Control.next, Data.record, Control.advance, lead, loopSite_ne]
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
