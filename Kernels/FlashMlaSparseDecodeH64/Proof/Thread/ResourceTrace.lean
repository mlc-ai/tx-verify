-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ResourceEvents
import Lemmas.Flow.TraceInduction

public section

/-! # Each warp-zero thread visits the allocator instructions in program order -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ResourceEvents

open PTX PTX.Proof PTX.Flow Tmem.Pair

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

private def beforeRole (L : Launch) (g : Nat) : Nat :=
  if warpOf L g = 0 then 2 else 0

private def prologueCount (L : Launch) (g n : Nat) : Site → Prop
  | .shfl0 | .shfl1 => n = 0
  | .elect0 | .elect1 | .init _ | .fence | .alloc => n = 0 ∧ warpOf L g = 0
  | .allocStore | .allocRead | .relinquish => n = 1 ∧ warpOf L g = 0
  | .barrier | .handoff _ => n = beforeRole L g

private def counts (L : Launch) (g n : Nat) : Option Machine.ThreadD → Prop
  | some (.prologue s) => prologueCount L g n s
  | some (.wg0 _) => n = beforeRole L g
  | _ => True

private theorem count_append (es : List Event) (e : Event) :
    tmemOps (es ++ [e]) = tmemOps es + if isTmemOp e then 1 else 0 := by
  simp [tmemOps]

private theorem relinquish_event {e : Event} {o : Option TState}
    (hpre : Pre P L mem0)
    (hf : (Machine.machine P L g).Fired (some (.prologue .relinquish)) e o) :
    e.kind = .tc (.resource .one none .relinquish) := by
  obtain ⟨t, _, hf⟩ := hf
  change Fires t.pc (match kernel.code[Flow.tmemRelinquish_0]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  rw [Flow.code_tmemRelinquish_0] at hf
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  simp only [eventTmpl, tcTmpl, hb, ↓reduceIte, pure, Except.pure, ofExec] at hf
  exact congrArg Event.kind hf.1

private theorem alloc_event {s' : Site} {e : Event}
    (hn : next L g .alloc e = some (some s')) : isTmemOp e = true := by
  cases hk : e.kind <;> simp [next, hk] at hn
  case tc k =>
    cases k <;> try simp at hn
    case resource grp dst req =>
      cases req <;> simp_all [isTmemOp]

private theorem no_resource_prologue {s : Site} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0)
    (hf : (Machine.machine P L g).Fired (some (.prologue s)) e o)
    (ha : s ≠ .alloc) (hr : s ≠ .relinquish) : isTmemOp e = false := by
  by_contra h
  obtain ⟨tag, grp, dst, req, rfl⟩ := tmemOp_resource (Bool.eq_true_of_not_eq_false h)
  cases emits hpre hf rfl with
  | alloc => exact ha rfl
  | relinquish => exact hr rfl

private theorem prologue_phase {s s' : Site} {e : Event} {o : Option TState} {n : Nat}
    (hpre : Pre P L mem0)
    (hf : (Machine.machine P L g).Fired (some (.prologue s)) e o)
    (hn : next L g s e = some (some s')) (h : prologueCount L g n s) :
    prologueCount L g (n + if isTmemOp e then 1 else 0) s' := by
  by_cases ha : s = .alloc
  · subst s
    simp only [alloc_event hn, ↓reduceIte]
    cases hk : e.kind <;> simp [next, hk] at hn
    case tc k =>
      cases k <;> try simp at hn
      case resource grp dst req =>
        cases req <;> simp at hn
        split_ifs at hn <;> cases hn <;> simp_all [prologueCount]
  by_cases hr : s = .relinquish
  · subst s
    have hk := relinquish_event hpre hf
    simp only [next, Option.some.injEq] at hn
    subst s'
    simp_all [prologueCount, beforeRole, isTmemOp]
  simp only [no_resource_prologue hpre hf ha hr, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  cases s <;> simp only [next] at hn
  all_goals try contradiction
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp_all [prologueCount, beforeRole]

private theorem no_resource_to_wg0 {d d' : Wg0.D} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0)
    (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e o)
    (hn : Wg0.next P L g d e = some (some d')) : isTmemOp e = false := by
  by_contra h
  obtain ⟨tag, grp, dst, req, rfl⟩ := tmemOp_resource (Bool.eq_true_of_not_eq_false h)
  cases emits hpre hf rfl with
  | dealloc d hSite =>
    simp [Wg0.next, Wg0.nextSite, hSite] at hn

private theorem counts_step {q q' : Option Machine.ThreadD} {e : Event} {o : Option TState}
    {es : List Event}
    (hpre : Pre P L mem0) (h : counts L g (tmemOps es) q)
    (hf : (Machine.machine P L g).Fired q e o)
    (hn : (Machine.machine P L g).next q e = some q') :
    counts L g (tmemOps (es ++ [e])) q' := by
  rw [count_append]
  cases q
  case none =>
    change some none = some q' at hn
    cases hn
    trivial
  case some d =>
    change Machine.next P L g d e = some q' at hn
    cases d
    case prologue s =>
      simp only [Machine.next] at hn
      split at hn
      · rename_i s' hnext
        cases hn
        exact prologue_phase hpre hf hnext h
      · split at hn
        · rename_i w _
          split_ifs at hn
          · fin_cases w <;> cases hn <;> try trivial
            have hMoved : isTmemOp e = false :=
              no_resource_prologue hpre hf (by simp) (by simp)
            simpa [counts, prologueCount, Machine.roleStart, hMoved] using h
          · cases hn
            trivial
        · cases hn
          trivial
      · cases hn
    case wg0 d =>
      simp only [Machine.next] at hn
      split at hn
      · rename_i d' hnext
        cases hn
        have hMoved := no_resource_to_wg0 hpre hf hnext
        simpa [counts, hMoved] using h
      · split_ifs at hn <;> cases hn <;> trivial
      · cases hn
    case head =>
      cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
      simp only [Machine.headStart] at hn
      split_ifs at hn <;> cases hn <;> trivial
    all_goals
      simp only [Machine.next] at hn
      all_goals repeat' split at hn
      all_goals cases hn
      all_goals trivial

/-- The allocating warp has issued both prologue resource operations at its CTA gate. -/
theorem ops_at_gate {X : Execution} {i : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hg : g < L.threads)
    (hw : warpOf L g = 0)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .barrier))) :
    opsAt X g i = 2 := by
  have hTrace := hs.produces (hX.thr g hg)
  have h := hTrace.prefix_induction (fun q es => counts L g (tmemOps es) q) (by rfl)
    (fun _ _ _ _ _ => counts_step hpre) i (some (.prologue .barrier)) hState
  simpa [counts, prologueCount, beforeRole, hw] using h

/-- Every followed resource event belongs to warp zero, with its ordinal and exact request. -/
theorem ordinal {X : Execution} {i tag : Nat} {grp : CtaGroup}
    {dst : Option Loc} {req : Tmem.Request} {d : Machine.ThreadD}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound)
    (he : X.get (g, i) = some ⟨tag, .tc (.resource grp dst req)⟩)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some d)) :
    warpOf L g = 0 ∧ grp = .one ∧ opsAt X g i < 3 ∧ req = (opAct 0 (opsAt X g i)).request := by
  have hTrace := hs.produces (hX.thr g (Frame.lt_of_get hX he))
  have h := hTrace.prefix_induction (fun q es => counts L g (tmemOps es) q) (by rfl)
    (fun _ _ _ _ _ => counts_step hpre) i (some d) hState
  obtain ⟨_, hf⟩ := hTrace.fired_at he hState
  cases emits hpre hf rfl with
  | alloc hgrp hd hr =>
    have h' : opsAt X g i = 0 ∧ warpOf L g = 0 := h
    exact ⟨h'.2, hgrp, by omega, by rw [h'.1]; exact hr⟩
  | relinquish hgrp hd hr =>
    have h' : opsAt X g i = 1 ∧ warpOf L g = 0 := h
    exact ⟨h'.2, hgrp, by omega, by rw [h'.1]; exact hr⟩
  | dealloc d hSite hWarp hgrp hd hr =>
    have h' : opsAt X g i = 2 := by simpa [counts, beforeRole, hWarp] using h
    exact ⟨hWarp, hgrp, by omega, by rw [h']; exact hr⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ResourceEvents
