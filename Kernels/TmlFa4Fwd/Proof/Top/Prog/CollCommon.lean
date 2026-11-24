-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Defs
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Issue
public import Kernels.TmlFa4Fwd.Proof.Top.Register
public import Lemmas.Kernel.Progress.Blocked
public import Lemmas.Kernel.Progress.WarpCollPair
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Top.Prog.Entry
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # What every warp's collectives share

The collective sites of the code (`warpPc`), the static part of an instruction with immediate
operands (`pcShape`), and the release of a lane whose last event is its register request when
another lane of its warp is past its own and released (`not_regWait`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

/-- Whether an instruction is a warp collective. -/
def warpO : Option Instr → Bool
  | some ins => decide (Descent.opKind ins.op = .warp)
  | none => false

/-- Whether the instruction at a position is a warp collective. -/
def warpPc (pc : Nat) : Bool := warpO kernel.code[pc]?

/-- A state at a position of the code is at a warp collective when its instruction is one. -/
theorem collAt_iff {σ : (thread p L g).D} (hc : (kernel.code[(thread p L g).pc σ]?).isSome) :
    CollAt p L g σ ↔ warpPc ((thread p L g).pc σ) = true := by
  obtain ⟨ins, hi⟩ := Option.isSome_iff_exists.mp hc
  simp only [CollAt, RestAt, warpPc, warpO, hi, Option.some.injEq, forall_eq', decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨by rw [h]; rfl, h⟩

/-- The static part of the instruction at a position, when its operands are immediates. -/
def pcShape (pc : Nat) : Sched.CollShape :=
  ((kernel.code[pc]?).bind fun ins => opShape ins.op).getD (.shfl .up 0 0)

/-- Whether an instruction has an immediate static part naming the whole warp. -/
def staticO : Option Instr → Bool
  | some ins => match opShape ins.op with
    | some (.shfl ..) => true
    | some (.elect m) | some (.warpBar m) | some (.vote m) => m == 4294967295
    | none => false
  | none => false

/-- Whether the instruction at a position has an immediate static part naming the whole warp. -/
def staticPc (pc : Nat) : Bool := staticO kernel.code[pc]?

/-- The static part at a position with immediate operands. -/
theorem shapeAt_static {S : ∀ g, (thread p L g).D → Sched.CollShape} {σ : (thread p L g).D}
    (hs : staticPc ((thread p L g).pc σ) = true) (hS : S g σ = pcShape ((thread p L g).pc σ)) :
    Sched.ShapeAt (Progress.timed p L) S g σ := by
  unfold staticPc staticO at hs
  split at hs
  swap; · cases hs
  rename_i ins hi
  cases ho : opShape ins.op with
  | none => rw [ho] at hs; cases hs
  | some s =>
    have hSs : S g σ = s := by rw [hS]; simp [pcShape, hi, ho]
    refine ⟨?_, fun t ins' hAt hinv hi' => ?_⟩
    · rw [hSs]
      rw [ho] at hs
      cases s <;> simp_all [Sched.CollShape.Full]
    · have hii : ins' = ins := by
        have : kernel.code[(thread p L g).pc σ]? = some ins' := hi'
        rw [hi] at this
        exact (Option.some.inj this).symm
      subst hii
      refine ⟨?_, ?_⟩
      · cases hop : ins'.op <;> rw [hop] at ho <;> simp only [opShape, reduceCtorEq] at ho
        rfl
      · rw [hSs]
        exact Sched.warpOp_tmpl ho

/-- The template of a shuffle instruction: undefined behaviour or a shuffle. -/
theorem shfl_tmpl {t : TState} {op : Op} (hsh : op.isShfl = true) :
    (∃ f, eventTmpl Assumptions.all L g t op = .ub f) ∨
      ∃ md a b c k, eventTmpl Assumptions.all L g t op = .shfl md a b c k := by
  rcases eventTmpl_opTmpl (A := Assumptions.all) (L := L) (g := g) (t := t) op with hu | hm
  · exact .inl hu
  · right
    cases op <;> simp only [Op.isShfl, Bool.false_eq_true] at hsh
    rename_i w
    obtain ⟨kind, ty, dsts, srcs, mask⟩ := w
    cases kind <;> simp only [Bool.false_eq_true] at hsh
    exact hm

/-- **A lane of a warp past its register request, when another lane is past its own and released,
does not wait for its request.** -/
theorem not_regWait (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hub : ¬ HasUb X) (hs : SameWarp L g h) {i : Role} {d : (frag p L g i).D} {n
        : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (.inr ⟨i, d⟩, n)))
    (hE : ¬ IsEntry i d) (hrel : Step.Released L X g) : ¬ Sched.RegWait L X h := by
  rintro ⟨pc, inc, nn, inst, hreq, hnr⟩
  have hg := hs.1.1
  obtain ⟨j, hj, i', n', hj'⟩ := first_role _ _ _ hσ
  have hin : IsEntry i' (frag p L g i').init := by cases i' <;> first | rfl | trivial
  have hlt : j < (X.tr g).length := by
    rcases Nat.lt_or_eq_of_le hj with h | h
    · exact h
    · exfalso
      rw [h] at hj'
      have := hj'.symm.trans hσ
      simp only [Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq] at this
      obtain ⟨h1, -⟩ := this
      cases h1
      exact hE hin
  obtain ⟨e, he⟩ : ∃ e, X.get (g, j) = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
  have hJ := (goodR' hp hX hg j).2 _ hj'
  obtain ⟨inc', nn', inst', hk⟩ := entry_fires hp hX hj' hin hJ he (by
    obtain ⟨pc,kind⟩ := e; rintro f rfl; exact hub ⟨_,pc,f,he⟩)
  obtain ⟨pc', kd⟩ := e
  simp only at hk
  subst hk
  have hsame := regMatch hp hX (e := (g, j)) (f := (h, (X.tr h).length - 1)) hg hs.1.2.1 hs he
    hreq
  refine hnr (SetMaxNReg.ready_of_sameRequest he hsame ?_)
  rcases Nat.lt_or_ge (j + 1) (X.tr g).length with h1 | h1
  · exact hX.dependency.ready _ (by simp [Returned, he, Kind.resume, h1])
  · obtain rfl : j = (X.tr g).length - 1 := by omega
    exact hrel.ready _ _ he rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Top
