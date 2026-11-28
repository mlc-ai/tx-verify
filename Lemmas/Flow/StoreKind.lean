-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StoreSrc

@[expose] public section

/-! # The event of a one-source weak store

A proof tool. A weak store of one source register under THREAD-ACCESS fires a write or undefined
behaviour (`fires_st_kind`). -/

namespace PTX.Flow
open PTX PTX.Proof

/-- **A one-source weak store that is not undefined behaviour fires a write.** -/
theorem fires_st_kind {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {a : MemAccess} {sp : Space} {base w src : Nat} {pc : Nat} {e : Event} {o : Option TState}
    (hr : a.rule = some .threadAccess) (hs : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .store) (hsem : a.sem = .weak)
    (hsrc : a.srcs = [.reg src]) (hf : Fires pc (eventTmpl A L g t (.mem a)) e o)
    (hu : ∀ f, e.kind ≠ .ub f) : ∃ acc bs, e.kind = .wr acc bs := by
  rw [eventTmpl, memTmpl_store hr hs hb hk hsem] at hf
  simp only [storeTmpl, hsrc] at hf
  split at hf
  · rename_i f _
    simp only [Fires] at hf
    exact absurd (by rw [hf.1]) (hu f)
  · split at hf
    · simp only [Fires] at hf
      exact absurd (by rw [hf.1]) (hu _)
    · split at hf
      · simp only [Fires] at hf
        exact absurd (by rw [hf.1]) (hu _)
      · simp only [Fires] at hf
        exact ⟨_, _, by rw [hf.1]⟩

end PTX.Flow
