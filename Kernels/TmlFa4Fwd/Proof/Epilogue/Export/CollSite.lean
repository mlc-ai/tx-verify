-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OutputColl
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.CollCommon
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Common.Migrated
import Kernels.TmlFa4Fwd.Proof.Common.NoUb
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Coll
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Kind
import Kernels.TmlFa4Fwd.Proof.Epilogue.Facts
import Kernels.TmlFa4Fwd.Proof.Epilogue.NoUb
import Kernels.TmlFa4Fwd.Proof.Epilogue.Open
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Kernels.TmlFa4Fwd.Proof.Top.Table
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The collective sites of the output warp, and their static parts -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Progress (isP cnt)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

/-- **The static part of a collective state of the output warp**: the choice's two shuffles read
lanes of the ballot, every other collective has immediate operands. -/
def outShape (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Sched.CollShape :=
  match σ with
  | (.inr ⟨.epilogue, d⟩, _) => match d.site with
    | .pre _ => .shfl .idx (truncBits 32 (Epilogue.addi (Epilogue.popc d.bal) (-1))).toNat 31
    | .tiles _ => .shfl .idx (truncBits 32 (Epilogue.popc d.bal)).toNat 31
    | s => pcShape s.pc
  | σ => pcShape ((thread p L g).pc σ)

private theorem tmplShape_mk {md : ShflMode} {a : Value} {b c : Nat}
    {k : Value → Bool → TState} :
    Sched.tmplShape (.shfl md a b c k) = some (.shfl md b c) := rfl

private def dyn : Epilogue.Site → Bool
  | .pre _ | .tiles _ => true
  | _ => false

private theorem out_warp : (.ready 0 :: .ready 1 :: outSites).all (fun s =>
    warpPc s.pc == Progress.Out.coll s && (kernel.code[s.pc]?).isSome &&
    (!Progress.Out.coll s || dyn s || staticPc s.pc) && (!dyn s ||
      match kernel.code[s.pc]? with
      | some ins => !ins.op.isLocal && ins.op.isShfl
      | none => false)) = true := by decide +kernel

private theorem out_mem (s : Epilogue.Site) : s ∈ (.ready 0 :: .ready 1 :: outSites) := by
  cases s with
  | start => simp [outSites]
  | word k | down k | total k => cases k <;> simp [outSites]
  | up k j => cases k <;> simp [outSites]
  | vote l | pre l | tiles l | exit l => cases l <;> simp [outSites]
  | q0 | q1 => simp [outSites]
  | ready st => fin_cases st <;> simp
  | store st b | commit st | drain st | free st => fin_cases st <;> simp [outSites]

private theorem out_site (s : Epilogue.Site) : warpPc s.pc = Progress.Out.coll s ∧
    (kernel.code[s.pc]?).isSome = true ∧
    (Progress.Out.coll s = true → dyn s = true ∨ staticPc s.pc = true) ∧
    (dyn s = true → ∀ ins, kernel.code[s.pc]? = some ins →
      ins.op.isLocal = false ∧ ins.op.isShfl = true) := by
  have := List.all_eq_true.mp out_warp s (out_mem s)
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
    (warpPc 172 = false ∧ warpPc 173 = false) ∧
    (kernel.code[172]?).isSome = true ∧ (kernel.code[173]?).isSome = true := by
  decide +kernel

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hg : g < L.threads)
  (hw : Prologue.warpIndex L g = 13)
include hp hX hFw hg hw

omit hFw in
/-- **A state of the output warp is at a collective exactly at its collective sites.** -/
theorem out_collAt {k : Nat} {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    CollAt p L g σ ↔ isP p L g σ = true := by
  have hR := (Epilogue.good_all hp hX hg hw k).2 _ hσ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
  on_goal 7 => exact hR.elim
  · obtain ⟨hS, -⟩ := hR
    obtain ⟨site, x1, x2, x3⟩ := s
    obtain ⟨t1, ⟨t2, t3⟩, t4, t5⟩ := start_warp
    cases site <;> simp only [StartAt] at hS
    case sh j =>
      rw [collAt_iff (σ := (.inl ⟨.sh j, x1, x2, x3⟩, n)) (t1 j).2.2]
      exact ⟨fun _ => rfl, fun _ => (t1 j).2.1⟩
    case fence =>
      rw [collAt_iff (σ := (.inl ⟨.fence, x1, x2, x3⟩, n)) t4]
      exact ⟨fun h => absurd (t2.symm.trans h) (by simp), fun h => by cases h⟩
    case bar =>
      rw [collAt_iff (σ := (.inl ⟨.bar, x1, x2, x3⟩, n)) t5]
      exact ⟨fun h => absurd (t3.symm.trans h) (by simp), fun h => by cases h⟩
  · obtain ⟨h1, h2, -⟩ := out_site d.site
    rw [collAt_iff (σ := (.inr ⟨.epilogue, d⟩, n)) h2]
    show warpPc d.site.pc = true ↔ _
    rw [h1]
    rfl
  all_goals exact hR.elim

omit hFw in
/-- A collective position of the output warp is a collective site. -/
theorem out_isP {k : Nat} {σ : (thread p L g).D}
    (h : Sched.CollPos (Progress.timed p L) X (CollAt p L) g k σ) : isP p L g σ = true := by
  obtain ⟨hσ, ⟨e, he, hc⟩ | ⟨rfl, hc⟩⟩ := h
  · rw [← Progress.ev_isP hp hX hg hw hσ he]; exact hc
  · exact (out_collAt hp hX hg hw hσ).mp hc

/-- **The static part of a collective state of the output warp.** -/
theorem out_shapeAt {k : Nat} {σ : (thread p L g).D}
    (h : Sched.CollPos (Progress.timed p L) X (CollAt p L) g k σ) :
    Sched.ShapeAt (Progress.timed p L) (outShape p L) g σ := by
  have hP := out_isP hp hX hg hw h
  have hσ := h.1
  have hR := (Epilogue.good_all hp hX hg hw k).2 _ hσ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
  on_goal 7 => exact hR.elim
  · obtain ⟨hS, -⟩ := hR
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site <;> simp only [isP, Bool.false_eq_true] at hP
    case sh j => exact shapeAt_static (start_warp.1 j).1 rfl
  · have hP' : Progress.Out.coll d.site = true := hP
    obtain ⟨-, -, h3, h4⟩ := out_site d.site
    cases hd : dyn d.site with
    | false =>
      have hst := (h3 hP').resolve_left (by simp [hd])
      refine shapeAt_static (σ := (.inr ⟨.epilogue, d⟩, n)) hst ?_
      show (match d.site with
        | .pre _ => Sched.CollShape.shfl .idx
            (truncBits 32 (Epilogue.addi (Epilogue.popc d.bal) (-1))).toNat 31
        | .tiles _ => .shfl .idx (truncBits 32 (Epilogue.popc d.bal)).toNat 31
        | s => pcShape s.pc) = pcShape d.site.pc
      revert hd
      cases d.site <;> simp [dyn]
    | true =>
      have hJ := (goodR hp hX hFw hg k).2 _ hσ
      have hT := table_shape_of hp hFw
      refine ⟨?_, fun t ins hAt hinv hi => ?_⟩
      · show Sched.CollShape.Full (match d.site with
          | .pre _ => Sched.CollShape.shfl .idx
              (truncBits 32 (Epilogue.addi (Epilogue.popc d.bal) (-1))).toNat 31
          | .tiles _ => .shfl .idx (truncBits 32 (Epilogue.popc d.bal)).toNat 31
          | s => pcShape s.pc)
        revert hd
        cases d.site <;> simp [dyn, Sched.CollShape.Full]
      · obtain ⟨hloc, hsh⟩ := h4 hd ins hi
        refine ⟨hloc, ?_⟩
        have hEv : ∀ e o, Fires ((thread p L g).pc (.inr ⟨.epilogue, d⟩, n))
            (eventTmpl Assumptions.all L g t ins.op) e o → (∀ f, e.kind ≠ .ub f) →
            Epilogue.Ev p L g d e :=
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
                (truncBits 32 (Epilogue.addi (Epilogue.popc d.bal) (-1))).toNat 31
            | .tiles _ => .shfl .idx (truncBits 32 (Epilogue.popc d.bal)).toNat 31
            | s => pcShape s.pc)
          rcases hsite with ⟨l, hsite⟩ | ⟨l, hsite⟩
          all_goals
            simp only [Epilogue.Ev, hsite] at this
            obtain ⟨recv, ok, hk⟩ := this
            simp only [Kind.shfl.injEq] at hk
            obtain ⟨e1, -, e2, e3, -, -⟩ := hk
            rw [tmplShape_mk, e1, e2, e3, hsite]
  all_goals exact hR.elim

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Top
