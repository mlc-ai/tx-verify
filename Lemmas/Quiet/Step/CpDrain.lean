-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Quiet.Step.MmaDrainTmemA
public import Lemmas.Quiet.Progress.Async
public import Lemmas.Tcgen05.MmaSources

@[expose] public section

/-! # A maximal execution has completed every `tcgen05.cp`

A proof tool, generic over the kernel (the kernel-independent part of FlashMLA's
`Proof/Progress/QueryCopy.lean`), under `Assumption.WfQuiet`:

* a copy has no completion predecessor: those are MMAs (`cpIssue_completionReady`);
* a copy whose source bytes have not been read finishes, reading each byte from a write every
  other write of the byte is ordered with (`pending_cp_extensionQ`, on `consistent_finishCp`);
* a copy that has read its bytes completes (`started_mma_inOrderQ`);
* so a maximal execution whose pending copies have such sources (`CpSourcesT`) has completed every
  copy (`Maximal.cp_doneQ`), and the MMA obligation steps for a kernel that issues copies and no
  `tcgen05.shift` (`Sched.mma_steps_cpQ`). -/

namespace PTX
open AsyncCopy MmaSources

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {sel : Nat → Bool} {i : EvId} {c : TcCopy.Spec}

/-- A copy issue is no MMA issue. -/
theorem cpIssue_not_mma (hi : X.CpIssue i c) {d : Nat} {s : TcMma.OperandSpec} {a : Bool}
    {ms : List Nat} (hm : X.MmaIssue i d s a ms) : False := by
  obtain ⟨_, h⟩ := hi
  obtain ⟨_, h'⟩ := hm
  rw [h] at h'
  cases h'

/-- The operand bytes of a copy are bytes of A below its source size. -/
theorem cpIssue_footprint_bound (hi : X.CpIssue i c) {isB : Bool} {k : Nat} {l : Loc}
    (h : X.MmaFootprint i isB k l) : isB = false ∧ k < c.ctas.length * c.shape.sourceBytes := by
  rcases h with ⟨_, _, _, _, hm, _⟩ | ⟨c', n, cta, hc, hb, hcta, hdiv, _⟩
  · exact (cpIssue_not_mma hi hm).elim
  · have he := Kind.tc.inj (congrArg Event.kind
      (Option.some.inj (hi.choose_spec.symm.trans hc.choose_spec)))
    obtain rfl := TcKind.cp.inj he
    refine ⟨hb, ?_⟩
    have hlt := (List.getElem?_eq_some_iff.mp hcta).1
    have hp : 0 < c.shape.sourceBytes := by
      cases c.shape <;> simp [TcCpShape.sourceBytes, TcCpShape.rows, TcCpShape.rowBytes]
    apply (Nat.div_lt_iff_lt_mul hp).mp
    exact hdiv ▸ hlt

/-- **A copy has no completion predecessor.** -/
theorem cpIssue_completionReady (hi : X.CpIssue i c) : TcMma.CompletionReady L X i := by
  intro j hj
  obtain ⟨_, _, _, ⟨_, _, _, _, _, _, _, _, _, hm, _⟩, _⟩ := TcMma.completionPrecedes_iff.mp hj
  exact (cpIssue_not_mma hi hm).elim

/-- **A copy whose bytes have not been read finishes**, reading each source byte from a write
every other write of the byte is ordered with, when the Tensor Memory read rule survives its
finish. -/
theorem pending_cp_extensionQ (hA : Assumption.WfQuiet sel L K mem0 A)
    (hX : Consistent L K A mem0 X) (hi : X.CpIssue i c)
    (hn : X.async.mmaOperands i = none) (hd : X.async.mmaDone i = false)
    (hguarded : SyncGuarded L K X)
    (hread : ∀ (v : MmaOperands) (ra rb : Nat → Option Ref),
      TcMma.ReadOk L A (X.finishMma i v ra rb))
    (source : Fin (c.ctas.length * c.shape.sourceBytes) → ByteSource X)
    (hfoot : ∀ k, X.MmaFootprint i false k.val (source k).loc)
    (horder : ∀ k w a bs, X.MemWrites w a bs → a.Covers (source k).loc →
      w = (source k).ref ∨ modelCausality L X (source k).loc w (source k).ref ∨
        modelCausality L X (source k).loc (.async i (.mmaRead false k.val)) w) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  let n := c.ctas.length * c.shape.sourceBytes
  let bytes : (isB : Bool) → Fin (if isB then 0 else n) → ByteSource X
    | false => source
    | true => Fin.elim0
  have hfoot' (isB : Bool) (k : Fin (if isB then 0 else n)) :
      X.MmaFootprint i isB k.val (bytes isB k).loc := by
    cases isB
    · exact hfoot k
    · exact Fin.elim0 k
  have hbound {isB k l} (hf : X.MmaFootprint i isB k l) : k < if isB then 0 else n := by
    obtain ⟨rfl, hlt⟩ := cpIssue_footprint_bound hi hf
    exact hlt
  let v := newOperands bytes
  let ra := newSource bytes false
  let rb := newSource bytes true
  have hle : X.le (X.finishMma i v ra rb) := le_finishMma_unstarted hn
  have hov : Hidden L (X.finishMma i v ra rb) := by
    apply newOperands_hidden hX hguarded bytes hle hd hfoot' (fun _ _ _ => hbound)
    intro isB k w a bs hw hc
    cases isB
    · exact horder k w a bs hw hc
    · exact Fin.elim0 k
  have hlength := (newOperands_lengths bytes).1
  have hempty : v.b = [] := List.length_eq_zero_iff.mp (newOperands_lengths bytes).2
  refine ⟨_, consistent_finishCp hX hi hd (cpIssue_completionReady hi) hlength hempty
    (newOperands_rf hX bytes hle hfoot') (finishMma_noFuture hX hle hd) hov
    (hread v ra rb) (hA.quiet hX hle rfl (Execution.quietExt_of_tr rfl)), hle, ?_⟩
  exact finishMma_size (Frame.lt_of_get hX hi.choose_spec) (len_of_get hi.choose_spec) hd

/-- **The sources of the pending copies**: a copy whose bytes have not been read keeps the Tensor
Memory read rule when it finishes, and each of its source bytes has a write every other write of
the byte is ordered with. -/
def CpSourcesT (L : Launch) (A : List Assumption) (X : Execution) : Prop :=
  ∀ i c, X.CpIssue i c → X.async.mmaOperands i = none → X.async.mmaDone i = false →
    (∀ (v : MmaOperands) (ra rb : Nat → Option Ref), TcMma.ReadOk L A (X.finishMma i v ra rb)) ∧
    ∀ k : Fin (c.ctas.length * c.shape.sourceBytes), ∃ src : ByteSource X,
      X.MmaFootprint i false k.val src.loc ∧ ∀ w a bs, X.MemWrites w a bs → a.Covers src.loc →
        w = src.ref ∨ modelCausality L X src.loc w src.ref ∨
          modelCausality L X src.loc (.async i (.mmaRead false k.val)) w

/-- **A maximal execution has completed every copy** whose pending bytes have sources. -/
theorem Maximal.cp_doneQ (hA : Assumption.WfQuiet sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hsg : SyncGuarded L K X) (hcs : CpSourcesT L A X)
    (hi : X.CpIssue i c) : X.async.mmaDone i = true := by
  classical
  by_contra hd
  rw [Bool.not_eq_true] at hd
  cases hn : X.async.mmaOperands i with
  | none =>
    obtain ⟨hread, hsrc⟩ := hcs i c hi hn hd
    exact hmax.not_grows (pending_cp_extensionQ hA hmax.1 hi hn hd hsg hread
      (fun k => (hsrc k).choose) (fun k => (hsrc k).choose_spec.1)
      (fun k => (hsrc k).choose_spec.2))
  | some v =>
    have hs : X.async.mmaStarted i = true := by simp [Snapshot.mmaStarted, hn]
    exact hmax.not_grows (started_mma_inOrderQ hA hmax.1 hs hd (cpIssue_completionReady hi))

namespace Sched

variable {M : Timed K A L}

/-- **An open MMA obligation steps**, for a kernel that issues `tcgen05.cp` (with sources) and no
`tcgen05.shift`. -/
theorem mma_steps_cpQ (hA : Assumption.WfQuiet sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hsg : SyncGuarded L K X) (hos : OperandSourcesT L X)
    (hap : TcMma.ATmemApart X) (hinj : TcMma.LayoutInjective X) (hcs : CpSourcesT L A X)
    (hsh : ∀ e s, ¬ X.ShiftIssue e s)
    (ho : Descent.Obl L X .mma) : Steps M mem0 X .mma := by
  refine (ho fun i hi => ?_).elim
  rcases hi with ⟨_, _, _, _, hm⟩ | ⟨c, hc⟩ | ⟨s, hs⟩
  · exact Maximal.mma_all_done_tmemAQ hA hmax hsg hos hap hinj hm
  · exact Maximal.cp_doneQ hA hmax hsg hcs hc
  · exact (hsh i s hs).elim

end Sched

end
end PTX
