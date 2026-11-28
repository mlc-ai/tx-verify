-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DataStoreVote

@[expose] public section

/-! # The data step of a store of several elements, from a `Reach`

`DataStep.storeE` leaves the last element's step to the successor's state. Its `Reach` form takes
the facts of the state and starts them at the next position. -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **The data step of a store of several elements**: the facts of the successor after the last
element, from a `Reach` at the next position. -/
theorem DataStep.storeR {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {a : MemAccess} (hc : K.code[C'.pc d]? = some ⟨none, .mem a⟩) (hl : (Op.mem a).isLocal = false)
    (hk : a.kind = .store) (ha : C'.acc d = [])
    (hmid : C'.sub d + 1 < a.srcs.length → ∀ e d', C'.next d e = some (some d') →
      ∀ R, Holds R (C'.facts d) → Holds R (dF d'))
    (hR : ∀ e d', C'.next d e = some (some d') → ¬ C'.sub d + 1 < a.srcs.length →
      Reach K A L g (C'.pc d + 1) (C'.facts d) (dF d')) :
    DataStep C' dF d :=
  DataStep.storeE hc hl hk hmid fun _ hm e d' t hn hat =>
    hR e d' hn hm _ ⟨by simp [hat.1], rfl, hat.2.2.1.trans ha, hat.2.2.2.1, hat.2.2.2.2⟩

end
end PTX.Flow.Code
