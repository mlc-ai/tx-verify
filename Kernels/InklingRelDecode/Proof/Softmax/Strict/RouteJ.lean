-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.RouteU
import Kernels.InklingRelDecode.Flow.Code.Part034
import Lemmas.Flow.StepsQFOa
@[expose] public section
/-! # The strict step of the shuffle that ends the row sum (pc 2234) -/
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt
set_option maxRecDepth 100000
variable {e : Control.Entry} {L : Launch} {g : Nat} {i : Nat} {v : Control.Carry} {w : Data.Vals}

theorem val_169 (e : Control.Entry) (L : Launch) (g : Nat) (d : Control.D) :
    Control.valueOf e L g d 169 = .pred (decide (d.i = 0)) := by
  simp [Control.valueOf, Control.scalarValue]

theorem val_1532 (e : Control.Entry) (L : Launch) (g : Nat) (d : Control.D) :
    Control.valueOf e L g d 1532 = b32 ((d.i + 1) % 2) := by
  simp [Control.valueOf, Control.scalarValue]

theorem xor_parity (i : Nat) :
    Value.bits 32 (truncBits 32 (BitVec.ofNat 64 (i % 2)) ^^^ truncBits 32 (BitVec.ofInt 64 1)) =
      b32 ((i + 1) % 2) := by
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [h, show (i + 1) % 2 = 1 by omega]
    decide
  · rw [h, show (i + 1) % 2 = 0 by omega]
    decide

/-- The facts after the round's shuffle and the comparison with zero. -/
theorem span6_pre (hi : i < 2 ^ 64) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 2235
      (Data.dF L ⟨⟨.shfl6, i, v⟩, w⟩ ++ factsFrom (Control.ctlLive 2235)
        (Control.valueOf e L g ⟨.shfl6, i, v⟩)) 2237
      (Data.dF L ⟨⟨.shfl6, i, v⟩, w⟩ ++ factsFrom (Control.ctlLive 2237)
        (Control.valueOf e L g ⟨.shfl6, i, v⟩)) := by
  refine SegQ.cut (m := 2236) ?_ ?_
  · refine segQ_single (d := 1531) Flow.code_2235 (by decide +kernel)
      (single_late (by decide +kernel)) (sub_facts (fun _ h => h) (by decide +kernel))
      (rf_ne (fun p hp => ?_) (by decide +kernel))
    have : p.1 ∈ Data.dKeys .shfl6 := by
      rw [← Data.dFS_keys L .shfl6 w]
      exact List.mem_map_of_mem hp
    revert this
    simp only [Data.dKeys, Data.inRound]
    simp
    omega
  · refine SegQ.tauAll _ ?_
    simp only [Data.dF, Data.dFS, Data.inRound, Data.alphaFacts, ↓reduceIte, List.cons_append,
      List.nil_append]
    late_ctl 2236, 2237 using
      rw [val_169]
      exact congrArg Value.pred ((cmp_eq64 (a := i) (b := 0) hi (by decide)).trans
        (by simp [eq_comm]))

/-- The first round (counter zero): the branch of pc 2237 goes to the update. -/
theorem span6_zero (hi : i < 2 ^ 64) (h0 : i = 0) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 2235
      (Data.dF L ⟨⟨.shfl6, i, v⟩, w⟩ ++ factsFrom (Control.ctlLive 2235)
        (Control.valueOf e L g ⟨.shfl6, i, v⟩)) 999 (UG e L g .shfl6 i v w) := by
  have h169 : (169, Value.pred true) ∈ factsFrom (Control.ctlLive 2237)
      (Control.valueOf e L g ⟨.shfl6, i, v⟩) := by
    have : Control.valueOf e L g ⟨.shfl6, i, v⟩ 169 = .pred true := by
      rw [val_169]
      simp [h0]
    exact this ▸ mem_factsFrom (by decide +kernel)
  refine span6_pre hi |>.comp (SegQ.comp (b := 949) (G := Data.dF L ⟨⟨.shfl6, i, v⟩, w⟩ ++
    factsFrom (Control.ctlLive 2237) (Control.valueOf e L g ⟨.shfl6, i, v⟩))
    (SegQ.tauAll _ (SegQF.braPS (qt := lateQt) true Flow.code_2237
    (fun _ hR => holds_mem hR (List.mem_append_right _ h169)) (fun t _ ha => Lib.bra_rule t _ ha)
    (segFree (by decide)) (by decide +kernel))) ?_)
  exact SegQ.fromFacts (sub_facts (fun _ h => h) (by decide +kernel)) (upd_tail (Or.inl rfl) w)

/-- The later rounds: the branch falls through and the parity of the next poll is set. -/
theorem span6_pos (hi : i < 2 ^ 64) (hne : i ≠ 0) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 2235
      (Data.dF L ⟨⟨.shfl6, i, v⟩, w⟩ ++ factsFrom (Control.ctlLive 2235)
        (Control.valueOf e L g ⟨.shfl6, i, v⟩)) 2239
      (Data.dF L ⟨⟨.shfl6, i, v⟩, w⟩ ++ factsFrom (Control.ctlLive 2239)
        (Control.valueOf e L g ⟨.shfl6, i, v⟩)) := by
  have h169 : (169, Value.pred false) ∈ factsFrom (Control.ctlLive 2237)
      (Control.valueOf e L g ⟨.shfl6, i, v⟩) := by
    have : Control.valueOf e L g ⟨.shfl6, i, v⟩ 169 = .pred false := by
      rw [val_169]
      simp [hne]
    exact this ▸ mem_factsFrom (by decide +kernel)
  refine span6_pre hi |>.comp (SegQ.comp (b := 2238) (G := Data.dF L ⟨⟨.shfl6, i, v⟩, w⟩ ++
    factsFrom (Control.ctlLive 2237) (Control.valueOf e L g ⟨.shfl6, i, v⟩))
    (SegQ.tauAll _ (SegQF.braPS (qt := lateQt) false Flow.code_2237
    (fun _ hR => holds_mem hR (List.mem_append_right _ h169)) (fun t _ ha => Lib.bra_rule t _ ha)
    (segFree (by decide)) (by decide +kernel))) ?_)
  refine SegQ.fromFacts (F' := Data.dF L ⟨⟨.shfl6, i, v⟩, w⟩ ++
    factsFrom (Control.ctlLive 2238) (Control.valueOf e L g ⟨.shfl6, i, v⟩))
    (sub_facts (fun _ h => h) (by decide +kernel)) ?_
  refine SegQ.tauAll _ ?_
  simp only [Data.dF, Data.dFS, Data.inRound, Data.alphaFacts, ↓reduceIte, List.cons_append,
    List.nil_append]
  late_ctl 2238, 2239 using
    rw [val_1532]
    exact xor_parity i

/-- The facts of the round's shuffle site, from those the span after it starts at. -/
theorem start6 (x : Value) : ∀ p ∈ Data.dF L ⟨⟨.shfl6, i, v⟩, w⟩ ++ factsFrom (Control.ctlLive 2235)
    (Control.valueOf e L g ⟨.shfl6, i, v⟩),
    p ∈ (1530, x) :: (Data.code e L g).facts ⟨⟨.shfl6, i, v⟩, w⟩ := by
  intro p hp
  refine List.mem_cons_of_mem _ ?_
  rcases List.mem_append.mp hp with h | h
  · exact List.mem_append_right _ h
  · exact ctl_in (w := w) (p := 2234) (q := 2235) .shfl6 (by decide +kernel) (by decide +kernel) p h

theorem swap_mem {A B : List (Nat × Value)} {p : Nat × Value} (h : p ∈ A ++ B) : p ∈ B ++ A := by
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_right _ h
  · exact List.mem_append_left _ h

theorem hi64 {d : Control.D} (hinv : Control.Inv e (g % L.block) d) : d.i < 2 ^ 64 := by
  have h1 := hinv.bound
  have h2 := hinv.entry.limitEq
  have h3 := hinv.entry.blockWord
  split at h2 <;> omega

/-- **The shuffle that ends the row sum** continues at the update (first round) or the poll. -/
theorem sstep_shfl6 (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.shfl6, i, v⟩, w⟩ ev := by
  intro t u ins hat hinv hc hQ hw hf hP
  have hr : ∀ q ∈ (Data.code e L g).facts ⟨⟨.shfl6, i, v⟩, w⟩, q.1 ≠ 1530 :=
    facts_ne (by dsimp only; decide +kernel) (by dsimp only; decide +kernel)
  have hbf : ∀ ev' : Event, LWf ev' → ev'.pc = (Data.code e L g).pc ⟨⟨.shfl6, i, v⟩, w⟩ →
      ∀ m av bv cv recv ok, ev'.kind = .shfl m av bv cv recv ok → Dat32 recv :=
    fun _ he hpc m av bv cv recv ok hk =>
      he.bfly (hpc ▸ (by change 2234 ∈ _; decide)) m av bv cv recv ok hk
  have e1 : (Data.code e L g).pc ⟨⟨.shfl6, i, v⟩, w⟩ = 2234 := by
    change Site.pc .shfl6 = 2234
    decide +kernel
  rcases em (i = 0) with h0 | h0
  · have hn : ∀ m av bv cv recv ok, Dat32 recv →
        (Data.code e L g).next ⟨⟨.shfl6, i, v⟩, w⟩ ⟨2234, .shfl m av bv cv recv ok⟩ =
          some (some ⟨⟨.bar20, i, v⟩, updW6 L w av recv⟩) := by
      intro m av bv cv recv ok _
      simp [Data.code, Data.succ, Control.next, Data.record, Data.psOf, h0]
    have e2 : (Data.code e L g).pc ⟨⟨.bar20, i, v⟩, updW L w⟩ = 999 := by
      change Site.pc .bar20 = 999
      decide +kernel
    have key := Code.shflOneFPa (C := Data.code e L g) (qt := lateQt) (Wf := LWf)
      (P := TauAll kernel Assumptions.all L g (LateR' L g))
      (d := ⟨⟨.shfl6, i, v⟩, w⟩) (f := fun a x => ⟨⟨.bar20, i, v⟩, updW6 L w a x⟩) (r := 1530)
      (tr := .dat32) (Pv := Dat32) Flow.code_2234
    refine key hr hbf (fun x hx => ⟨x, rfl, hx⟩) hn rfl rfl
      (by change afterF lateQt 2234 _ = true; decide +kernel)
      (fun _ x hx => ⟨rfl, rfl, Control.body_inv hinv rfl rfl, ?_⟩) ev ins hat hinv hc hQ hw hf hP
    rw [e1, e2]
    exact (SegQ.fromFacts (start6 x) (span6_zero (hi64 hinv) h0)).comp (SegQ.weaken
      fun _ hR => holds_of_forall fun p hp => holds_mem hR
        (swap_mem (ctl_out (w := updW L w) .bar20 (by decide +kernel) p hp)))
  · have hn : ∀ m av bv cv recv ok, Dat32 recv →
        (Data.code e L g).next ⟨⟨.shfl6, i, v⟩, w⟩ ⟨2234, .shfl m av bv cv recv ok⟩ =
          some (some ⟨⟨.waitO, i, v⟩, {w with ps := Lib.psWord av recv}⟩) := by
      intro m av bv cv recv ok _
      simp [Data.code, Data.succ, Control.next, Data.record, Data.psOf, h0]
    have e3 : (Data.code e L g).pc ⟨⟨.waitO, i, v⟩, w⟩ = 2239 := by
      change Site.pc .waitO = 2239
      decide +kernel
    have key := Code.shflOneFPa (C := Data.code e L g) (qt := lateQt) (Wf := LWf)
      (P := TauAll kernel Assumptions.all L g (LateR' L g))
      (d := ⟨⟨.shfl6, i, v⟩, w⟩) (f := fun a x => ⟨⟨.waitO, i, v⟩, {w with ps := Lib.psWord a x}⟩)
      (r := 1530)
      (tr := .dat32) (Pv := Dat32) Flow.code_2234
    refine key hr hbf (fun x hx => ⟨x, rfl, hx⟩) hn rfl rfl
      (by change afterF lateQt 2234 _ = true; decide +kernel)
      (fun a x hx => ⟨rfl, rfl, Control.body_inv hinv rfl rfl, ?_⟩) ev ins hat hinv hc hQ hw hf hP
    rw [e1, e3]
    exact (SegQ.fromFacts (start6 x) (span6_pos (hi64 hinv) h0)).comp (SegQ.weaken
      fun _ hR => holds_of_forall fun p hp => holds_mem hR
        (swap_mem (ctl_out (w := {w with ps := Lib.psWord a x}) .waitO (by decide +kernel) p hp)))
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
