-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Quiet.Progress.ReleasedU
public import Lemmas.Kernel.PlainStep
public import Lemmas.Step.TcLoad

@[expose] public section

/-! # A released thread at an instruction without a class steps under quiet extensions

`Descent.released_stepsUQ` performs the instructions of a class (`Descent.opKind`); the kinds in
`NextKind.Rest` need a partner or a kernel fact. Two families of `.other` instructions need
neither, and step here (`other_next_stepsUQ`):

* a weak `ld.global.nc` under THREAD-ACCESS (`ncLoadOp`): a `readNC` template, performed with the
  launch content of its bytes (`Execution.launchBytes`, as `Execution.NoTma.next_extends`). An
  `nc` read adds a read, so the quiet constraints (`Assumption.WfQuiet`) do not cover it; the
  constraints of the execution with that read appended are a premise (`hnc`), which a kernel's
  read-only constraint gives because the read returns the launch content;
* a `tcgen05` fence, copy or shift (`tcIssueOp`): a Tensor Core event that is no warp collective,
  performed as an MMA issue (`Step.tc_counted_extension_reads`). -/

namespace PTX.Descent
open PTX PTX.Flow MBarrier AsyncCopy
noncomputable section

/-- A weak non-coherent load under THREAD-ACCESS. -/
def ncLoadOp : Op → Bool
  | .mem a => a.kind == .load && a.nc && a.sem == .weak && a.rule == some .threadAccess
  | _ => false

/-- A `tcgen05` fence, copy or shift: an issue that is no warp collective. -/
def tcIssueOp : Op → Bool
  | .tcFenceBefore | .tcFenceAfter | .tcCp .. | .tcShift .. => true
  | _ => false

/-- The instructions without a class that `other_next_stepsUQ` performs. -/
def otherOp (op : Op) : Bool := ncLoadOp op || tcIssueOp op

/-- The Tensor Core events of `tcIssueOp`. -/
def TcIssueKind (k : TcKind) : Prop :=
  k = .fenceBefore ∨ k = .fenceAfter ∨ (∃ s, k = .cp s) ∨ ∃ s, k = .shift s

/-- The templates of `otherOp`: undefined behaviour, a non-coherent read or a Tensor Core issue
that is no warp collective. -/
def OtherTmpl (m : Tmpl) : Prop :=
  (∃ f, m = .ub f) ∨ (∃ a k, m = .readNC a k) ∨ ∃ k u, m = .tc k u ∧ TcIssueKind k

theorem TcIssueKind.not_coll {k : TcKind} (h : TcIssueKind k) (pc : Nat) :
    isTcColl ⟨pc, .tc k⟩ = false := by
  rcases h with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

private theorem ofExec_other {r : Exec Tmpl} (h : ∀ m, r = .ok m → OtherTmpl m) :
    OtherTmpl (ofExec r) := by
  cases r with
  | error f => exact .inl ⟨f, rfl⟩
  | ok m => exact h m rfl

private theorem loadTmpl_nc {sp : Space} {w : Nat} {ds : List Nat} {base : Nat} {off : Int} :
    OtherTmpl (loadTmpl A L g t sp true w ds base off) := by
  unfold loadTmpl
  split
  · exact .inl ⟨_, rfl⟩
  · simp only [↓reduceIte]
    split_ifs
    · exact .inr (.inl ⟨_, _, rfl⟩)
    · exact .inl ⟨_, rfl⟩

private theorem accessTmpl_nc {a : MemAccess} (hk : a.kind = .load) (hnc : a.nc = true) :
    OtherTmpl (accessTmpl A L g t a) := by
  unfold accessTmpl
  simp only [hk, hnc, ↓reduceIte]
  split
  · exact .inl ⟨_, rfl⟩
  · split_ifs
    · exact .inr (.inl ⟨_, _, rfl⟩)
    · exact .inl ⟨_, rfl⟩

/-- **The template of an instruction of `otherOp`.** -/
theorem other_tmpl {op : Op} (h : otherOp op = true) : OtherTmpl (eventTmpl A L g t op) := by
  cases op <;> simp only [otherOp, ncLoadOp, tcIssueOp, Bool.or_false, Bool.false_or,
    Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  case mem a =>
    obtain ⟨⟨⟨hk, hnc⟩, hs⟩, hr⟩ := h
    simp only [eventTmpl, memTmpl, hr]
    split
    · simp only [hk, hs]
      rw [hnc]
      exact loadTmpl_nc
    · rename_i h
      cases h
    · rw [ite_eq_left (rfl : some RuleId.threadAccess = _)]
      exact accessTmpl_nc hk hnc
  all_goals simp only [eventTmpl, tcTmpl]
  · exact .inr (.inr ⟨_, _, rfl, .inl rfl⟩)
  · exact .inr (.inr ⟨_, _, rfl, .inr (.inl rfl)⟩)
  all_goals refine ofExec_other fun m hm => ?_
  all_goals
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hm
    repeat' split at hm
    all_goals first
      | (cases hm; done)
      | (cases hm; exact .inr (.inr ⟨_, _, rfl, .inr (.inr (.inl ⟨_, rfl⟩))⟩))
      | (cases hm; exact .inr (.inr ⟨_, _, rfl, .inr (.inr (.inr ⟨_, rfl⟩))⟩))

variable {K : Kernel} {mem0 : Mem0} {X : Execution}
variable {ι : Sort _} {Obl : Execution → ι → Prop} {rank : Execution → ι → Nat} {o : ι}
variable {C : (g : Nat) → Flow.Code K A L g}

/-- **A released pending thread at an instruction of `otherOp` steps**, when the assumptions'
constraints hold of the execution with a non-coherent read of the launch content appended. -/
theorem other_next_stepsUQ (hc : NextEnvQ L K A mem0 X) (hC : ∀ g < L.threads, (C g).SoundU)
    (hp : Frame.Pending L X g) {d : (C g).D}
    (hσ : Frame.stateAt C X g (X.tr g).length = some (some d)) (hne : X.tr g ≠ [])
    (hrel : Step.Released L X g)
    (hk : ∀ ins, K.code[(C g).pc d]? = some ins → otherOp ins.op = true)
    (hnc : ∀ pc a, ∀ a' ∈ A,
      a'.wf L mem0 (X.snoc g ⟨pc, .nc a (X.launchBytes mem0 a)⟩ (fun _ => none))) :
    Steps L K A mem0 Obl rank X o := by
  have hX := hc.max.1
  obtain ⟨t, hrun⟩ := Frame.run_some hX hc.noUb hp
  rcases Frame.end_atU hC hp.1 hrun hσ with hsite | ⟨u, f, hl, hout⟩
  case inr => exact ub_steps_inOrderQ hc.wf hX hp.1 hne hrel hrun hl hout
  obtain ⟨t1, ins, hl, -, -, hins, hout⟩ := hsite
  rcases other_tmpl (A := A) (L := L) (g := g) (t := t1) (hk ins hins) with
    ⟨f, hf⟩ | ⟨a, k, hf⟩ | ⟨k, u, hf, hkk⟩ <;> rw [hf] at hout
  · exact ub_steps_inOrderQ hc.wf hX hp.1 hne hrel hrun hl hout
  · exact .inl (Step.plain_counted_extension hX hp.1 (.inl hne) hrel hrun hl
      (e := ⟨t1.pc, .nc a (X.launchBytes mem0 a)⟩) (o := some (k (X.launchBytes mem0 a)))
      ⟨_, hout, _, by simp [Execution.launchBytes], rfl, rfl⟩ trivial rfl nofun nofun nofun rfl
      (hX.tmemPairResult.snoc_not_wr nofun) (hnc _ _))
  · exact .inl (Step.tc_counted_extension_reads hX hc.reads hp.1 hne hrel hrun hl
      (o := some u) ⟨_, hout, rfl, rfl⟩ (hkk.not_coll _) (hc.snoc_wf rfl)
      (hc.guard.snoc hc.no_release hc.no_release_rmw hc.no_fence (fun _ _ h => by cases h)
          (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)))

end

end PTX.Descent
