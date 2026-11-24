-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.Table

@[expose] public section

/-! # The instruction table of a role table

A proof tool, generic over the kernel. A kernel whose roles are followed but whose shape tables are
not stated yet (or whose class needs only the instruction at the site) takes as its shape table
the events the instruction at the state's site fires from a concrete state of the state
(`RoleTable.ofIns`). Its shape obligation holds by definition (`RoleTable.ofIns_shapeOk`), so
every frame of `Safety/Classes.lean` and every class of `Safety/` applies with a per-shape fact
read off the instruction (`eventTmpl`), and `RoleTable.sites` with one evaluated check of the code
gives the classes that name an instruction kind (tml-fa4's `migrated_fires`, for any role
table). -/

namespace PTX.Frame

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch}

/-- **The instruction table**: the invariant `J`, and the events the instruction at the state's
site fires from a concrete state of the state. -/
def RoleTable.ofIns (C : (g : Nat) → Code K A L g) (J : ∀ g, (C g).D → Prop) : RoleTable C where
  J := J
  Ev g d e := ∃ t ins o, (C g).AtD d t ∧ K.code[(C g).pc d]? = some ins ∧
    Fires ((C g).pc d) (eventTmpl A L g t ins.op) e o

/-- **The instruction table's shape obligation holds by definition.** -/
theorem RoleTable.ofIns_shapeOk (C : (g : Nat) → Code K A L g) (J : ∀ g, (C g).D → Prop)
    (S : Nat → Prop) : (RoleTable.ofIns C J).ShapeOk S :=
  ⟨fun _ _ _ t ins _ o _ hat _ hc hf => ⟨t, ins, o, hat, hc, hf⟩⟩

end

end PTX.Frame
