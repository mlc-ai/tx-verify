-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Lemmas.Kernel.Existence
public import Lemmas.Step.CommitOrderExtend
public import Lemmas.Snoc.PlainAsyncExtend

@[expose] public section

/-!
# The assumptions' constraints on the extensions of the progress layer

The numerical rules and the Tensor Memory completion hooks constrain no execution. The
commit-order constraint survives every extension that performs its commit arrive-ons in order.
The read-only input constraint (`inputReadOnly`) survives every extension that adds no read
(`inputReadOnly_wf_ext`). An extension that appends a read keeps it when the read's bytes have
sources (`NewRead`) and no write of the execution covers an input byte the read reads at a site
(`wf_snoc_read`), or when the read returns the launch bytes (`wf_snoc_launch`).
-/

namespace PTX.Kernels.TmlFa4Fwd.Assumptions
open PTX.Assumption

noncomputable section

/-- No arithmetic, synchronization or input premise restricts the empty execution. -/
theorem empty_wf {l : Launch} {m : Mem0} :
    ∀ a ∈ all, a.wf l m Execution.empty := by
  intro a ha
  simp only [all, numeric, synchronization, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals first
    | trivial
    | (intro g j j' pc sp r h; simp [Execution.get, Execution.empty] at h)
    | (intro e pc a bs h; simp [Execution.get, Execution.empty] at h)

/-- The constraints other than the input reads survive every extension that performs its commit
arrive-ons in order. The numeric rules and TMEM completion hooks are trace-local. -/
private theorem wf_extend_core {l : Launch} {m : Mem0} {X Y : Execution}
    (hX : Consistent l kernel all m X) (hle : X.le Y)
    (hOrdered : X.NotifiedInOrder (fun pc => commitOrderSites.contains pc) Y) :
    ∀ a ∈ numeric ++ synchronization, a.wf l m Y := by
  intro a ha
  have hWf := hX.asm a (List.mem_append_left _ ha)
  simp only [numeric, synchronization, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals first
    | trivial
    | exact Assumption.commitPerformedAt_extend (fun _ h => h) hWf hX.tcCommit hle hOrdered

private theorem mem_all {a : Assumption} (ha : a ∈ all) :
    a ∈ numeric ++ synchronization ∨ a = inputReadOnly :=
  (List.mem_append.mp ha).imp id List.mem_singleton.mp

/-- **An extension that adds no read keeps the input constraint.** -/
theorem inputReadOnly_wf_ext {l : Launch} {m : Mem0} {X Y : Execution}
    (hwf : inputReadOnly.wf l m X) (hr : X.NoNewRead Y) : inputReadOnly.wf l m Y :=
  fun e pc a bs he hs => hwf e pc a bs (hr e _ he rfl) hs

/-- Consistent extensions preserve the assumptions when the selected Q-empty commit follows the
audited arrive-on order and no read is added. -/
theorem wfStep {l : Launch} {m : Mem0} :
    Assumption.WfStep (fun pc => commitOrderSites.contains pc) l kernel m all := by
  intro X Y hX hle hOrdered hr a ha
  rcases mem_all ha with ha | rfl
  · exact wf_extend_core hX hle hOrdered a ha
  · exact inputReadOnly_wf_ext (hX.asm _ ha) hr

/-- **A read whose bytes have sources keeps the constraints**, when at a site no write of the
execution covers an input byte it reads: each such byte then has no write source, so it is the
launch byte. -/
theorem wf_snoc_read {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel all m X) {g pc : Nat} {e : Event}
    {r : Nat → Option AsyncCopy.Ref} {a : Acc} {bs : List (Option Byte)}
    (hread : NewRead l m X g e r a bs)
    (hfresh : inputReadSites.contains pc = true → ∀ k < a.size, InputByte l m (a.loc.at k) →
      ∀ w a' bs', X.MemWrites w a' bs' → ¬ a'.Covers (a.loc.at k)) :
    ∀ q ∈ all, q.wf l m (X.snoc g ⟨pc, .rd a bs⟩ r) := by
  intro q hq
  rcases mem_all hq with hq | rfl
  · exact wf_extend_core hX le_snoc (Execution.notifiedInOrder_of_eq rfl) q hq
  · have hwf := hX.asm _ hq
    intro v pc' a' bs' hv hs
    rw [snoc_get] at hv
    split_ifs at hv
    · simp only [Option.some.injEq, Event.mk.injEq, Kind.rd.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      intro k hk hin c hc
      have hsrc := hread.src k hk
      cases hrk : r k with
      | none =>
        rw [hrk] at hsrc
        simpa [Execution.initialByte] using hsrc _ hc
      | some w =>
        rw [hrk] at hsrc
        obtain ⟨a'', bs'', hw, hcov, -⟩ := hsrc
        exact absurd hcov (hfresh hs k hk hin w a'' bs'' hw)
    · exact hwf v pc' a' bs' hv hs

/-- **A read whose bytes all have the launch content as source keeps the constraints.** -/
theorem wf_snoc_initial {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel all m X) {g pc : Nat} {e : Event} {a : Acc}
    {bs : List (Option Byte)} (hread : NewRead l m X g e (fun _ => none) a bs) :
    ∀ q ∈ all, q.wf l m (X.snoc g ⟨pc, .rd a bs⟩ (fun _ => none)) := by
  intro q hq
  rcases mem_all hq with hq | rfl
  · exact wf_extend_core hX le_snoc (Execution.notifiedInOrder_of_eq rfl) q hq
  · have hwf := hX.asm _ hq
    intro v pc' a' bs' hv hs
    rw [snoc_get] at hv
    split_ifs at hv
    · simp only [Option.some.injEq, Event.mk.injEq, Kind.rd.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      intro k hk _ c hc
      simpa [Execution.initialByte] using hread.src k hk _ hc
    · exact hwf v pc' a' bs' hv hs

/-- **A read that returns the launch bytes keeps the constraints.** -/
theorem wf_snoc_launch {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel all m X) {g pc : Nat} {r : Nat → Option AsyncCopy.Ref}
    {a : Acc} {v : Value} (hSize : a.size = v.bytes) (hLaunch : HasValue m a.loc v) :
    ∀ q ∈ all, q.wf l m (X.snoc g ⟨pc, .rd a (v.toBytes.map some)⟩ r) := by
  intro q hq
  rcases mem_all hq with hq | rfl
  · exact wf_extend_core hX le_snoc (Execution.notifiedInOrder_of_eq rfl) q hq
  · have hwf := hX.asm _ hq
    intro e pc' a' bs' he hs
    rw [snoc_get] at he
    split_ifs at he
    · simp only [Option.some.injEq, Event.mk.injEq, Kind.rd.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      intro k hk _ c hc
      obtain rfl := Option.some.inj (Option.some.inj (hc.symm.trans (hLaunch k (hSize ▸ hk))))
      simp [Value.toBytes, ← hSize, hk]
    · exact hwf e pc' a' bs' he hs

/-- **A read of memory outside global memory keeps the constraints**: it reads no input byte. -/
theorem wf_snoc_nonGlobal {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel all m X) {g pc : Nat} {r : Nat → Option AsyncCopy.Ref}
    {a : Acc} {bs : List (Option Byte)} (hsp : a.loc.space ≠ .global) :
    ∀ q ∈ all, q.wf l m (X.snoc g ⟨pc, .rd a bs⟩ r) := by
  intro q hq
  rcases mem_all hq with hq | rfl
  · exact wf_extend_core hX le_snoc (Execution.notifiedInOrder_of_eq rfl) q hq
  · have hwf := hX.asm _ hq
    intro v pc' a' bs' hv hs
    rw [snoc_get] at hv
    split_ifs at hv
    · simp only [Option.some.injEq, Event.mk.injEq, Kind.rd.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      intro k _ hin
      obtain ⟨_, _, _, _, hc⟩ := hin
      exact absurd hc.1 hsp
    · exact hwf v pc' a' bs' hv hs

/-- **An appended event that is not a read at a site keeps the constraints.** -/
theorem wf_snoc_offsite {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel all m X) {g : Nat} {e : Event} {r : Nat → Option AsyncCopy.Ref}
    (hs : ∀ a bs, e.kind = .rd a bs → inputReadSites.contains e.pc = false) :
    ∀ q ∈ all, q.wf l m (X.snoc g e r) := by
  intro q hq
  rcases mem_all hq with hq | rfl
  · exact wf_extend_core hX le_snoc (Execution.notifiedInOrder_of_eq rfl) q hq
  · have hwf := hX.asm _ hq
    intro v pc' a' bs' hv hsite
    rw [snoc_get] at hv
    split_ifs at hv
    · obtain rfl := Option.some.inj hv
      rw [hs a' bs' rfl] at hsite
      cases hsite
    · exact hwf v pc' a' bs' hv hsite

end
end PTX.Kernels.TmlFa4Fwd.Assumptions
