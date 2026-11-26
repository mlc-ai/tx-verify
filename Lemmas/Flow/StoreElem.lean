-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StoreValue

@[expose] public section

/-! # The bytes of one element of a weak store

A proof tool. Element `t.sub` of a weak store under THREAD-ACCESS (a vector store is one event per
element) writes exactly the bytes of the value in its source register when the element width is
the value's width (`fires_st_elemBytes`): the event is either undefined behaviour or that write,
whatever the address. The one-source form is `fires_st_srcBytes`. -/

namespace PTX.Flow
open PTX PTX.Proof

/-- **Element `t.sub` of a weak store writes its source's bytes.** -/
theorem fires_st_elemBytes {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {a : MemAccess} {sp : Space} {base w src : Nat} {v : Value} {pc : Nat} {e : Event}
    {o : Option TState} (hr : a.rule = some .threadAccess) (hs : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .store) (hsem : a.sem = .weak)
    (hsrc : a.srcs[t.sub]? = some (.reg src)) (hw : v.bytes = a.elem.width / 8)
    (hv : t.regs src = some v) (hf : Fires pc (eventTmpl A L g t (.mem a)) e o)
    (hu : ∀ f, e.kind ≠ .ub f) : ∃ acc, e.kind = .wr acc v.toBytes := by
  rw [eventTmpl, memTmpl_store hr hs hb hk hsem] at hf
  simp only [storeTmpl, hsrc] at hf
  split at hf
  · rename_i f _
    simp only [Fires] at hf
    exact absurd (by rw [hf.1]) (hu f)
  · simp only [readValue, readReg, hv, bind, Except.bind, pure, Except.pure,
      storeValue_of_bytes hw, Fires] at hf
    exact ⟨_, by rw [hf.1]⟩

end PTX.Flow
