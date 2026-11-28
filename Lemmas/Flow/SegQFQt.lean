-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TypedSingleG

@[expose] public section

/-! # A strict segment under one table by pc

The windows of a typed region (`Tools/typed_gen.py`) each state their own tags at their cuts
(`<window>_qt`). A lane that crosses several windows uses one table `qt` by pc; a window's segment
is a segment under `qt` when `qt` has the window's tags at its two ends, checked by the kernel
(`tagsInF`). -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {a b : Nat}
  {F G : List (Nat × Value)}

/-- The tags `e'` are the tags `e` or among them (equal tables need no check). -/
def QIn (e' e : EnvF) : Prop := e' = e ∨ tagsInF e' e = true

theorem typedF_of_qin {e e' : EnvF} {t : TState} (h : QIn e' e) (ht : TypedF e t) :
    TypedF e' t := by
  rcases h with rfl | h
  · exact ht
  · exact typedF_of_tagsIn h ht

/-- A segment under the tags `w` is one under the table `q` that has `w`'s tags at `a` and `b`. -/
theorem qtf_conv {w q : Nat → EnvF} (h : SegQ K A L g (QTF w) a F b G)
    (ha : QIn (w a) (q a)) (hb : QIn (q b) (w b)) :
    SegQ K A L g (QTF q) a F b G := by
  intro t ht hQ
  have hT : TypedF (w a) t := typedF_of_qin ha (by simpa [QTF, ht.1] using hQ)
  obtain ⟨u, hr, hu, hQu⟩ := h t ht (by simpa [QTF, ht.1] using hT)
  refine ⟨u, hr, hu, ?_⟩
  have : TypedF (q b) u := typedF_of_qin hb (by simpa [QTF, hu.1] using hQu)
  simpa [QTF, hu.1] using this

/-- The same for a segment that keeps a fact `R` of the states the local steps reach. -/
theorem qtfT_conv {w q : Nat → EnvF} {R : TState → Prop}
    (h : SegQ K A L g (fun t => QTF w t ∧ TauAll K A L g R t) a F b G)
    (ha : QIn (w a) (q a)) (hb : QIn (q b) (w b)) :
    SegQ K A L g (fun t => QTF q t ∧ TauAll K A L g R t) a F b G := by
  intro t ht ⟨hQ, hR⟩
  have hT : TypedF (w a) t := typedF_of_qin ha (by simpa [QTF, ht.1] using hQ)
  obtain ⟨u, hr, hu, hQu, hRu⟩ := h t ht ⟨by simpa [QTF, ht.1] using hT, hR⟩
  refine ⟨u, hr, hu, ?_, hRu⟩
  have : TypedF (q b) u := typedF_of_qin hb (by simpa [QTF, hu.1] using hQu)
  simpa [QTF, hu.1] using this

end PTX.Flow.TyG
