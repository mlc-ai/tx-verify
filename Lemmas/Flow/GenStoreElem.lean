-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StoreElem

@[expose] public section

/-! # The bytes of one element of a generic store

A proof tool. A store under THREAD-ACCESS whose address is not located directly (`locSpace? =
none`: a generic address) is `accessTmpl`; its element `t.sub` writes exactly the bytes of the
value in its source register when the element width is the value's width, or is undefined
behaviour (`fires_gst_elemBytes`), whatever the address. -/

namespace PTX.Flow
open PTX PTX.Proof

/-- **Element `t.sub` of a generic store writes its source's bytes.** -/
theorem fires_gst_elemBytes {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {a : MemAccess} {src : Nat} {v : Value} {pc : Nat} {e : Event}
    {o : Option TState} (hr : a.rule = some .threadAccess) (hl : a.locSpace? = none)
    (hk : a.kind = .store) (hsrc : a.srcs[t.sub]? = some (.reg src))
    (hw : v.bytes = a.elem.width / 8) (hv : t.regs src = some v)
    (hf : Fires pc (eventTmpl A L g t (.mem a)) e o) (hu : ∀ f, e.kind ≠ .ub f) :
    ∃ acc, e.kind = .wr acc v.toBytes := by
  rw [eventTmpl] at hf
  simp only [memTmpl, hr, hl, ite_true] at hf
  simp only [accessTmpl, hk] at hf
  split at hf
  · rename_i f _
    simp only [Fires] at hf
    exact absurd (by rw [hf.1]) (hu f)
  · simp only [hsrc] at hf
    simp only [readValue, readReg, hv, bind, Except.bind, pure, Except.pure,
      storeValue_of_bytes hw] at hf
    simp only [Fires] at hf
    exact ⟨_, by rw [hf.1]⟩

end PTX.Flow
