-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Ld3
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.InitElection
public import Lemmas.Flow.SegQFam

@[expose] public section

/-! # The span from an election to the initialization it guards -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

/-- A state at the site `s` with the request words, the result of the last election and the
broadcast word. -/
abbrev dS (s : Site) (a y p : Nat) (win : Bool) (bcast : Value) (v : Data.Vals) : Data.D :=
  ⟨⟨s, .bits 32 (BitVec.ofNat 64 a), .bits 32 (BitVec.ofNat 64 y), .bits 32 (BitVec.ofNat 64 p),
    win, bcast⟩, v⟩

-- The guard and the address of the initialization (all but its last instruction).
seg_fam elA (i 12) : ∀ (a y p ld : Nat) (bcast : Value) (v : Data.Vals) (win : Bool),
    SegQ kernel Assumptions.all L g (QT proQt) ((Site.el i).pc + 1)
      ([(41 + Fin.val i, .pred win), (elLeader i, .bits 32 (BitVec.ofNat 64 ld))] ++
        dFacts Q L g w (dS (.el i) a y p win bcast v))
      ((Site.init i).pc - 1)
      (dFactsAt Q L g w (dS (.el i) a y p win bcast v) ((Site.init i).pc - 1)) :=
  intros
  simp only [dS, Site.pc, elPc, initPc, elLeader, Nat.reduceAdd, Nat.reduceMul, Fin.isValue,
    Nat.reduceSub]
  pro_seg

-- The address of the initialization (its last instruction).
seg_fam elB (i 12) : ∀ (a y p : Nat) (bcast : Value) (v : Data.Vals) (win : Bool),
    SegQ kernel Assumptions.all L g (QT proQt) ((Site.init i).pc - 1)
      (dFactsAt Q L g w (dS (.el i) a y p win bcast v) ((Site.init i).pc - 1))
      (Site.init i).pc (dFacts Q L g w (dS (.init i) a y p win bcast v)) :=
  intros
  simp only [dS, Site.pc, initPc, Nat.reduceAdd, Nat.reduceMul, Fin.isValue, Nat.reduceSub]
  pro_seg

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
