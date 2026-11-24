-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.UbStop
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # Undefined behaviour is a thread's last event

A proof tool, generic over the kernel (from the tml-fa4 lane's `Proof2/Lib/UbLast.lean`). An
event of kind `ub` is fired only by the `ub` template, which leaves no thread state (`Fires`),
so a run ends with it (`Run.ub_last`), and in a consistent execution no event of a thread
follows one (`ub_last`). A reference invariant may therefore be guarded by "no undefined
behaviour so far": after such an event the thread has no further event whose step it would have
to justify. -/

namespace PTX
open PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **A run ends with its undefined-behaviour event.** -/
theorem Run.ub_last {t : TState} {es : List Event} {o : Option TState}
    (h : Run K A L g t es o) {k pc : Nat} {f : Fault} (hk : es[k]? = some ⟨pc, .ub f⟩) :
    k + 1 = es.length := by
  induction h generalizing k with
  | nil => simp at hk
  | @step t t1 t2 e rest o _ hs _ ih =>
    cases k with
    | zero =>
      exfalso
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      obtain ⟨m, -, hf⟩ := hs
      obtain rfl := fires_ub hf rfl
      exact absurd hf.2 (by simp)
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      simp [← ih hk]
  | last =>
    cases k with
    | zero => rfl
    | succ k => simp at hk

/-- **No event of a thread follows its undefined-behaviour event.** -/
theorem ub_last {mem0 : Mem0} {X : Execution} (hX : Consistent L K A mem0 X) {j k pc : Nat}
    {f : Fault} {e : Event} (hj : X.get (g, j) = some ⟨pc, .ub f⟩) (he : X.get (g, k) = some e) :
    k ≤ j := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hr⟩ := hX.thr g hg
  have h1 := Run.ub_last hr hj
  have h2 := (List.getElem?_eq_some_iff.mp he).1
  change k < (X.tr g).length at h2
  omega

end PTX
