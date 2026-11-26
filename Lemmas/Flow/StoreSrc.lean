-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StoreValue

@[expose] public section

/-! # The bytes of a one-source weak store

A proof tool. A weak store of one source register under THREAD-ACCESS whose element width is the
source value's width writes exactly the source value's bytes, whatever its address
(`fires_st_srcBytes`): its event is either undefined behaviour or that write. -/

namespace PTX.Flow
open PTX PTX.Proof

/-- **A one-source weak store writes its source's bytes.** -/
theorem fires_st_srcBytes {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {a : MemAccess} {sp : Space} {base w src : Nat} {v : Value} {pc : Nat} {e : Event}
    {o : Option TState} (hr : a.rule = some .threadAccess) (hs : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .store) (hsem : a.sem = .weak)
    (hsrc : a.srcs = [.reg src]) (hw : v.bytes = a.elem.width / 8) (hsub : t.sub = 0)
    (hv : t.regs src = some v) (hf : Fires pc (eventTmpl A L g t (.mem a)) e o)
    (hu : ∀ f, e.kind ≠ .ub f) : ∃ acc, e.kind = .wr acc v.toBytes := by
  rw [eventTmpl, memTmpl_store hr hs hb hk hsem] at hf
  simp only [storeTmpl, hsrc, hsub] at hf
  split at hf
  · rename_i f _
    simp only [Fires] at hf
    exact absurd (by rw [hf.1]) (hu f)
  · simp only [List.getElem?_cons_zero, readValue, readReg, hv, bind, Except.bind, pure,
      Except.pure, storeValue_of_bytes hw, Fires] at hf
    exact ⟨_, by rw [hf.1]⟩

end PTX.Flow
