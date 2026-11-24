-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.CollState
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.CollCommon
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.Migrated
import Kernels.TmlFa4Fwd.Proof.Epilogue.Ideal
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Kernels.TmlFa4Fwd.Proof.Top.Table
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The collective sites of the MMA warp, and their static parts -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (CollTag tagOf)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

/-- **The static part of a collective state of the MMA warp.** -/
def mmaShape (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Sched.CollShape :=
  match σ with
  | (.inr ⟨.mma, .inr ⟨_, d⟩⟩, _) => match d.site with
    | .pre _ => .shfl .idx (truncBits 32 (Epilogue.addi (Epilogue.popc d.v.sc.bal) (-1))).toNat 31
    | .tiles _ => .shfl .idx (truncBits 32 (Epilogue.popc d.v.sc.bal)).toNat 31
    | s => pcShape s.pc
  | σ => pcShape ((thread p L g).pc σ)

private theorem tmplShape_mk {md : ShflMode} {a : Value} {b c : Nat}
    {k : Value → Bool → TState} :
    Sched.tmplShape (.shfl md a b c k) = some (.shfl md b c) := rfl

private def dyn : Mma.Site → Bool
  | .pre _ | .tiles _ => true
  | _ => false

private def allMma : List Mma.Site :=
  [.bar1, .ldAlloc, .bcast, .q0, .q1, .uk] ++
  ([Epilogue.Scan.first, .loop, .second, .loop2].flatMap fun k =>
    [.word k, .down k, .total k] ++ (List.finRange 5).map (.up k)) ++
  ([false, true].flatMap fun l =>
    [.vote l, .pre l, .tiles l, .relinq l, .bar2 l, .dealloc l, .exit l]) ++
  (List.finRange 10).map .wt ++
  (List.finRange 14).map .sh ++ (List.finRange 12).map .ce ++ (List.finRange 12).map .cm ++
  (List.finRange 4).flatMap fun b => [.eq b, .ep b, .mw b false, .mw b true] ++
    (List.finRange 8).map (.qk b) ++ (List.finRange 8).map (.pv b)

private theorem mma_mem (s : Mma.Site) : s ∈ allMma := by
  cases s with
  | bar1 | ldAlloc | bcast | q0 | q1 | uk => simp [allMma]
  | word k | down k | total k => cases k <;> simp [allMma]
  | up k j => cases k <;> simp [allMma]
  | vote l | pre l | tiles l | relinq l | bar2 l | dealloc l | exit l => cases l <;> simp [allMma]
  | wt k | sh k | ce k | cm k => simp [allMma]
  | mw b ld => cases ld <;> simp [allMma]
  | eq b | ep b => simp [allMma]
  | qk b j | pv b j => simp [allMma]

/-- The instruction at a site of the MMA warp. -/
private def insAt (n : Nat) : Option Instr :=
  if n < 2141 then codeFrom 1907 n else if n < 2294 then codeFrom 2141 n
  else if n < 2419 then codeFrom 2294 n else if n < 2545 then codeFrom 2419 n
  else codeFrom 2545 n

private theorem insAt_eq {n : Nat} (h : 1907 ≤ n) : insAt n = kernel.code[n]? := by
  unfold insAt
  split_ifs <;> exact codeFrom_eq (by omega)

private def chk (s : Mma.Site) : Bool :=
  decide (1907 ≤ s.pc) && (
  warpO (insAt s.pc) == s.wcoll && (insAt s.pc).isSome &&
    (!s.wcoll || dyn s || staticO (insAt s.pc)) && (!dyn s ||
      match insAt s.pc with
      | some ins => !ins.op.isLocal && ins.op.isShfl
      | none => false))

private theorem mma_chk1 : (allMma.take 70).all chk = true := by decide +kernel

private theorem mma_chk2 : (allMma.drop 70).all chk = true := by decide +kernel

private theorem mma_chk : allMma.all chk = true := by
  rw [← List.take_append_drop 70 allMma, List.all_append, mma_chk1, mma_chk2]
  rfl

private theorem mma_site (s : Mma.Site) : warpPc s.pc = s.wcoll ∧
    (kernel.code[s.pc]?).isSome = true ∧
    (s.wcoll = true → dyn s = true ∨ staticPc s.pc = true) ∧
    (dyn s = true → ∀ ins, kernel.code[s.pc]? = some ins →
      ins.op.isLocal = false ∧ ins.op.isShfl = true) := by
  have hc := List.all_eq_true.mp mma_chk s (mma_mem s)
  rw [chk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨h0, this⟩ := hc
  rw [insAt_eq h0] at this
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at this
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
  refine ⟨h1, h2, fun hc => ?_, fun hd ins hi => ?_⟩
  · rcases h3 with (h3 | h3) | h3
    · rw [h3] at hc; cases hc
    · exact .inl h3
    · exact .inr h3
  · rcases h4 with h4 | h4
    · rw [h4] at hd; cases hd
    · rw [hi] at h4
      simpa using h4

private theorem start_warp : (∀ j : Fin 3, staticPc (Startup.Site.sh j).pc = true ∧
    warpPc (Startup.Site.sh j).pc = true ∧ (kernel.code[(Startup.Site.sh j).pc]?).isSome = true) ∧
    (∀ pc ∈ [172, 173, 1907, 1909, 1910], warpPc pc = false ∧
      (kernel.code[pc]?).isSome = true) := by
  decide +kernel

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) (hw : Prologue.warpIndex L g = 12)
include hp hX hFw hub hg hw

omit hFw hub in
/-- **A state of the MMA warp is at a collective exactly at its collective sites.** -/
theorem mma_collAt {k : Nat} {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    CollAt p L g σ ↔ mmaAt p L g σ = true := by
  have hR := (Mma.good hp hX (cuQReadsFromLaunch hp hX) hg hw k).2 _ hσ
  obtain ⟨t1, t2⟩ := start_warp
  have off : ∀ σ' : (thread p L g).D, (thread p L g).pc σ' ∈ [172, 173, 1907, 1909, 1910] →
      mmaAt p L g σ' = false → (CollAt p L g σ' ↔ mmaAt p L g σ' = true) := by
    intro σ' hpc hm
    obtain ⟨h1, h2⟩ := t2 _ hpc
    rw [collAt_iff h2, h1, hm]
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
  · obtain ⟨hS, -⟩ := hR
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site <;> simp only [StartAt] at hS
    case sh j =>
      rw [collAt_iff (σ := (.inl ⟨.sh j, x1, x2, x3⟩, n)) (t1 j).2.2]
      exact ⟨fun _ => rfl, fun _ => (t1 j).2.1⟩
    case fence =>
      exact off (.inl ⟨.fence, x1, x2, x3⟩, n) (by show 172 ∈ _; decide) rfl
    case bar =>
      exact off (.inl ⟨.bar, x1, x2, x3⟩, n) (by show 173 ∈ _; decide) rfl
  · rcases d with s | ⟨u, d⟩
    · refine off (.inr ⟨.mma, .inl s⟩, n) ?_ rfl
      show s.pc ∈ _
      cases s <;> decide
    · obtain ⟨h1, h2, -⟩ := mma_site d.site
      rw [collAt_iff (σ := (.inr ⟨.mma, .inr ⟨u, d⟩⟩, n)) h2]
      show warpPc d.site.pc = true ↔ _
      rw [h1]
      rfl

/-- A collective position of the MMA warp is a collective site. -/
theorem mma_isP {k : Nat} {σ : (thread p L g).D}
    (h : Sched.CollPos (Progress.timed p L) X (CollAt p L) g k σ) : mmaAt p L g σ = true := by
  obtain ⟨hσ, ⟨e, he, hc⟩ | ⟨rfl, hc⟩⟩ := h
  · rw [← (mma_event_coll hp hX hFw hub hg hw he hσ).1]; exact hc
  · exact (mma_collAt hp hX hg hw hσ).mp hc

/-- **The static part of a collective state of the MMA warp.** -/
theorem mma_shapeAt {k : Nat} {σ : (thread p L g).D}
    (h : Sched.CollPos (Progress.timed p L) X (CollAt p L) g k σ) :
    Sched.ShapeAt (Progress.timed p L) (mmaShape p L) g σ := by
  have hP := mma_isP hp hX hFw hub hg hw h
  have hσ := h.1
  have hR := (Mma.good hp hX (cuQReadsFromLaunch hp hX) hg hw k).2 _ hσ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
  · obtain ⟨hS, -⟩ := hR
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site <;> simp only [mmaAt, Bool.false_eq_true] at hP
    case sh j => exact shapeAt_static (start_warp.1 j).1 rfl
  · rcases d with s | ⟨u, d⟩
    · cases hP
    have hP' : d.site.wcoll = true := hP
    obtain ⟨-, -, h3, h4⟩ := mma_site d.site
    cases hd : dyn d.site with
    | false =>
      have hst := (h3 hP').resolve_left (by simp [hd])
      refine shapeAt_static (σ := (.inr ⟨.mma, .inr ⟨u, d⟩⟩, n)) hst ?_
      show (match d.site with
        | .pre _ => Sched.CollShape.shfl .idx
            (truncBits 32 (Epilogue.addi (Epilogue.popc d.v.sc.bal) (-1))).toNat 31
        | .tiles _ => .shfl .idx (truncBits 32 (Epilogue.popc d.v.sc.bal)).toNat 31
        | s => pcShape s.pc) = pcShape d.site.pc
      revert hd
      cases d.site <;> simp [dyn]
    | true =>
      have hJ := (goodR hp hX hFw hg k).2 _ hσ
      have hT := table_shape_of hp hFw
      refine ⟨?_, fun t ins hAt hinv hi => ?_⟩
      · show Sched.CollShape.Full (match d.site with
          | .pre _ => Sched.CollShape.shfl .idx
              (truncBits 32 (Epilogue.addi (Epilogue.popc d.v.sc.bal) (-1))).toNat 31
          | .tiles _ => .shfl .idx (truncBits 32 (Epilogue.popc d.v.sc.bal)).toNat 31
          | s => pcShape s.pc)
        revert hd
        cases d.site <;> simp [dyn, Sched.CollShape.Full]
      · obtain ⟨hloc, hsh⟩ := h4 hd ins hi
        refine ⟨hloc, ?_⟩
        have hEv : ∀ e o, Fires ((thread p L g).pc (.inr ⟨.mma, .inr ⟨u, d⟩⟩, n))
            (eventTmpl Assumptions.all L g t ins.op) e o → (∀ f, e.kind ≠ .ub f) →
                Mma.Ev p L g d e :=
          fun e o hf => hT.shape g hg _ _ _ _ _ hJ hAt hinv hi hf
        rcases shfl_tmpl (L := L) (g := g) (t := t) hsh with hu | ⟨md, a, b, c, k', hm⟩
        · exact .inl hu
        · right
          rw [hm] at hEv ⊢
          have := hEv ⟨_, .shfl md a b c (.bits 32 0) false⟩ _ ⟨_, _, rfl, rfl⟩ (fun _ => nofun)
          have hsite : (∃ l, d.site = .pre l) ∨ ∃ l, d.site = .tiles l := by
            revert hd
            cases d.site <;> simp [dyn]
          show Sched.tmplShape _ = some (match d.site with
            | .pre _ => Sched.CollShape.shfl .idx
                (truncBits 32 (Epilogue.addi (Epilogue.popc d.v.sc.bal) (-1))).toNat 31
            | .tiles _ => .shfl .idx (truncBits 32 (Epilogue.popc d.v.sc.bal)).toNat 31
            | s => pcShape s.pc)
          rcases hsite with ⟨l, hsite⟩ | ⟨l, hsite⟩
          all_goals
            simp only [Mma.Ev, hsite, Epilogue.Ev, Mma.Site.toE] at this
            obtain ⟨recv, ok, hk⟩ := this
            simp only [Kind.shfl.injEq] at hk
            obtain ⟨e1, -, e2, e3, -, -⟩ := hk
            rw [tmplShape_mk, e1, e2, e3, hsite]

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Top
