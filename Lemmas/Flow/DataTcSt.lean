-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DataElems
import Lemmas.Flow.Step.TcSteps

@[expose] public section

/-! # A value machine's data step at a Tensor Memory store

Proof tool, generic over the kernel, beside `DataStep.next` (`Lemmas/Flow/DataElems.lean`):
`DataStep.tcSt`, a `tcgen05.st` that no assumption makes wait for a load continues at
`PTX.next t` with its registers unchanged (`fires_tcSt_next`). -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **The data step of a Tensor Memory store.** -/
theorem DataStep.tcSt {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {ta : Nat} {ss : List Opnd} {sh : TcShape} (hc : K.code[C'.pc d]? = some ⟨none, .tcSt ta ss sh⟩)
    (hw : A.any (·.tcStWaitLd (C'.pc d)) = false)
    (hrun : C'.inv d → ∀ e d' t, C'.next d e = some (some d') → C'.AtD d t →
      (∀ t', Relation.ReflTransGen (Tau K A L g) (PTX.next t) t' → Stops K A L g t' →
        Holds t'.regs (dF d')) ∨ Machine.Dead (K := K) (A := A) (L := L) (g := g) (PTX.next t)) :
    DataStep C' dF d := by
  intro t e u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain rfl := fires_tcSt_next (hat.1 ▸ hw) hf
  exact hrun hi e d' t hn hat

end
end PTX.Flow.Code
