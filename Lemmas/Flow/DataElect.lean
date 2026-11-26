-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DataElems
public import Lemmas.Flow.ElectU

@[expose] public section

/-! # A value machine's data step at an `elect.sync`

`DataStep.elect`: an election into a leader register `r` and a predicate `p`; the successor's
facts follow from the state after the event with both registers set. -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **The data step of an election.** -/
theorem DataStep.elect {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {ty : Option DType} {r p : Nat} {mask : Opnd}
    (hc : K.code[C'.pc d]? = some ⟨none, .warp ⟨.elect, ty, [some r, some p], [], some mask⟩⟩)
    (hrun : C'.inv d → ∀ mk inst ld d' t,
      C'.next d ⟨C'.pc d, .elect mk inst ld⟩ = some (some d') → C'.AtD d t →
      (∀ t', Relation.ReflTransGen (Tau K A L g)
          (PTX.next (setReg (setReg t r (.bits 32 (BitVec.ofNat 64 ld))) p
            (.pred (laneOf L g == ld)))) t' →
        Stops K A L g t' → Holds t'.regs (dF d')) ∨
        Machine.Dead (K := K) (A := A) (L := L) (g := g)
          (PTX.next (setReg (setReg t r (.bits 32 (BitVec.ofNat 64 ld))) p
            (.pred (laneOf L g == ld))))) :
    DataStep C' dF d := by
  intro t e u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨mk, inst, ld, rfl, rfl⟩ := fires_elect hf
  exact hrun hi mk inst ld d' t hn hat

end
end PTX.Flow.Code
