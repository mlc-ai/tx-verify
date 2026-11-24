-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopCounter
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Lemmas.Flow.SegFree

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption

noncomputable section

private theorem selectedLocalFrame {op : Op} {s : TState} {d : Nat} {v : Value}
    (hpc : nextPc op s.pc = s.pc + 1) (hd : d ∈ writesRegs op) :
    LocalFrame op s (next (setReg s d v)) := by
  refine ⟨.inl hpc.symm, rfl, rfl, rfl, ?_⟩
  intro r hr
  exact Function.update_of_ne (by intro h; subst h; exact hr hd) _ _

private theorem bindReadOk {α β : Type} {x : Option (Exec α)} {f : α → Option (Exec β)}
    {u : β} (h : bindRead x f = some (.ok u)) : ∃ v, f v = some (.ok u) := by
  cases x with
  | none => cases h
  | some x =>
    cases x with
    | error e => cases h
    | ok v => exact ⟨v, h⟩

private theorem lg2Frame {l : Launch} {g : Nat} {s u : TState} {op : Op}
    (h : Assumptions.lg2.localRule l g s op = some (.ok u)) :
    LocalFrame op s u := by
  cases op <;> try cases h
  case float f =>
    simp only [Assumptions.lg2, Assumptions.lg2Operands] at h
    split at h
    · rename_i d a
      split at h
      · split at h
        · cases h
        · simp only [bind, Option.bind] at h
          obtain ⟨x, hx⟩ := bindReadOk h
          split at hx
          · obtain rfl := Except.ok.inj (Option.some.inj hx)
            exact selectedLocalFrame rfl (by simp [writesRegs, *])
          · cases hx
      · cases h
    · cases h

private theorem bf16Frame {l : Launch} {g : Nat} {s u : TState} {op : Op}
    (h : Assumptions.bf16Convert.localRule l g s op = some (.ok u)) :
    LocalFrame op s u := by
  cases op <;> try cases h
  case cvt c =>
    simp only [Assumptions.bf16Convert] at h
    split at h
    · rename_i d a hWiden
      have hd : d = c.d := by
        unfold Assumptions.biasWidenOperands at hWiden
        repeat' split at hWiden
        all_goals cases hWiden
        all_goals first | rfl | (congr 1; exact (Op.cvt.inj ‹Op.cvt c = Op.cvt _›).symm)
      split at h
      · cases h
      · obtain ⟨x, hx⟩ := bindReadOk h
        obtain rfl := Except.ok.inj (Option.some.inj hx)
        exact selectedLocalFrame rfl (by simpa [writesRegs] using hd)
    · simp only [Assumptions.probPackOperands] at h
      split at h
      · split at h
        · split at h
          · cases h
          · simp only [bind, Option.bind] at h
            obtain ⟨x, hx⟩ := bindReadOk h
            obtain ⟨y, hy⟩ := bindReadOk hx
            obtain rfl := Except.ok.inj (Option.some.inj hy)
            exact selectedLocalFrame rfl (by simp [writesRegs])
        · cases h
      · cases h

private theorem numericLocalFrame {l : Launch} {g : Nat} {s u : TState} {op : Op}
    (h : execLocalRule Assumptions.numeric l g s op = .ok u) : LocalFrame op s u := by
  unfold execLocalRule at h
  split at h
  · rename_i step hStep
    obtain ⟨a, ha, haStep⟩ := List.exists_of_findSome?_eq_some hStep
    subst step
    simp only [Assumptions.numeric, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact idealReal_frame haStep
    · exact approxExact_frame haStep
    · exact lg2Frame haStep
    · exact bf16Frame haStep
    · cases haStep
  · exact execLocal_frame h

/-- Either the actual local rule keeps the instruction frame or a checked software-exp2
segment has run to its decoded end. -/
theorem scoreExecLocal {l : Launch} {g : Nat} {s u : TState} {op : Op}
    (h : execLocalA Assumptions.all l g s op = .ok u) :
    LocalFrame op s u ∨ ∃ m, s.pc ∈ Assumptions.swExp2Sites ∧
      cuteExp2.matchAt kernel s.pc = some m ∧ Assumptions.execSwExp2 m s = .ok u := by
  rw [Assumptions.execLocalA_all_eq_numeric] at h
  have hfind : (Assumptions.numeric.findSome? fun a => a.segmentRule l g s) =
      Assumptions.swExp2.segmentRule l g s := by
    have hA : Assumptions.idealArith.segmentRule l g s = none := rfl
    have hB : Assumptions.approx.segmentRule l g s = none := rfl
    have hC : Assumptions.lg2.segmentRule l g s = none := rfl
    have hD : Assumptions.bf16Convert.segmentRule l g s = none := rfl
    simp only [Assumptions.numeric, List.findSome?_cons, List.findSome?_nil, hA, hB, hC, hD]
    cases Assumptions.swExp2.segmentRule l g s <;> rfl
  rw [execLocalA, hfind] at h
  by_cases hSite : s.pc ∈ Assumptions.swExp2Sites ∧ s.sub = 0 ∧ s.acc = []
  · have hSegment : Assumptions.swExp2.segmentRule l g s =
        (cuteExp2.matchAt kernel s.pc).map fun m => Assumptions.execSwExp2 m s := by
      simp [Assumptions.swExp2, hSite.1, hSite.2.1, hSite.2.2]
    rw [hSegment] at h
    cases hm : cuteExp2.matchAt kernel s.pc with
    | none => exact .inl (numericLocalFrame (by simpa only [hm, Option.map_none] using h))
    | some m => exact .inr ⟨m, hSite.1, rfl, by simpa only [hm, Option.map_some] using h⟩
  · have hSegment : Assumptions.swExp2.segmentRule l g s = none := by
      simp [Assumptions.swExp2, hSite]
    rw [hSegment] at h
    exact .inl (numericLocalFrame h)

/-- The physical-register destination sites computed by the matched software-exponent template. -/
def scoreSegmentWrites (m : SegMatch CuteSlot) : List Nat :=
  (m.shape.writes.map m.regOf) ++ (m.shape.consts.map fun x => m.regOf x.1) ++
    m.shape.io.map (fun p => m.regOf p.2)

private theorem mapMOutputNames {α : Type} {f : α → Exec (Nat × Value)} {r : Nat}
    {xs : List α} (h : ∀ x ∈ xs, AllOk (fun p => p.1 ≠ r) (f x)) :
    AllOk (fun ys => ∀ p ∈ ys, p.1 ≠ r) (xs.mapM f) := by
  induction xs with
  | nil => change ∀ p ∈ ([] : List (Nat × Value)), p.1 ≠ r; simp
  | cons x xs ih =>
    have hx := h x (List.Mem.head xs)
    have hTail := ih (fun y hy => h y (List.Mem.tail x hy))
    simp only [List.mapM_cons, bind, Except.bind]
    cases he : f x with
    | error f => trivial
    | ok p =>
      rw [he] at hx
      cases ht : xs.mapM f with
      | error f => trivial
      | ok ps =>
        rw [ht] at hTail
        change ∀ q ∈ p :: ps, q.1 ≠ r
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hx
        · exact hTail q hq

/-- The software exponent segment has no event sub-step and keeps registers not written
by the frozen matched template. -/
theorem scoreSegmentFrame {m : SegMatch CuteSlot} {s u : TState}
    (h : Assumptions.execSwExp2 m s = .ok u) :
    u.pc = m.stop ∧ u.sub = 0 ∧ u.fault = s.fault ∧
      ∀ r, r ∉ scoreSegmentWrites m → u.regs r = s.regs r := by
  unfold Assumptions.execSwExp2 at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · contradiction
    rename_i result hr
    obtain rfl := Except.ok.inj h
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro r hKeep
    have hNames : ∀ p ∈ m.shape.io, AllOk (fun q : Nat × Value => q.1 ≠ r)
        (do
          let x ← Assumptions.swExp2Lane (← readReg s (m.regOf p.1))
          pure (m.regOf p.2, Value.float .f32 x)) := by
      intro p hp
      have he : m.regOf p.2 ≠ r := fun he => hKeep (by
        apply List.mem_append_right
        rw [← he]
        exact List.mem_map_of_mem hp)
      apply allOk_bind
      intro x
      apply allOk_bind
      intro y
      exact he
    have hOut := mapMOutputNames hNames
    simp only [bind, Except.bind, pure, Except.pure, SegMatch.regOf] at hOut
    rw [hr] at hOut
    apply segRegs_frame
    · intro x hx hEq
      apply hKeep
      rw [← hEq]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hx))
    · exact hOut
    · intro x hx hEq
      apply hKeep
      rw [← hEq]
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hx))
  · contradiction

end
end PTX.Kernels.TmlFa4Fwd.Softmax
