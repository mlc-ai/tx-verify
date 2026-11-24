-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.ReadReuse
public import Lemmas.Tcgen05.MmaCompletionFrame

@[expose] public section

/-! An MMA operand read observes the identified generation of a reused TMA tile.
The protocol proves the byte-address match and visibility orders; RF supplies the
value. Copy completion and issue order alone do not assert these premises.
-/
namespace PTX
noncomputable section
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

theorem mma_read_of_tensor_write (hX : Consistent L K A mem0 X)
    {mma copy : EvId} {isB : Bool} {index x y k address : Nat}
    {l : Loc} {observed : Option Byte} {written : Byte} {o : TensorCopy.Observation}
    (hr : X.MmaRead mma isB index l observed)
    (ho : X.tensor copy = some o) (hi : X.TensorIssue copy address o.spec)
    (hl : TensorCopy.writeLoc o.spec x y k = some l)
    (hw : TensorCopy.writeByte o x y k = some written)
    (hv : modelCausality L X l (.async copy (.write (.load x y k)))
      (.async mma (.mmaRead isB index)))
    (horder : ∀ other footprint bytes, X.MemWrites other footprint bytes →
      footprint.Covers l → other = .async copy (.write (.load x y k)) ∨
        modelCausality L X l other (.async copy (.write (.load x y k))) ∨
        modelCausality L X l
            (.async mma (.mmaRead isB index)) other ) : observed = some written := by
  have hwrite : X.MemWrites (.async copy (.write (.load x y k)))
      { loc := l, size := 1 } [written] :=
    ⟨o, address, written, ho, hi, hl, hw, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hcover : ({ loc := l, size := 1 } : Acc).Covers
      (({ loc := l, size := 1 } : Acc).loc.at 0) := by
    simp [Acc.Covers, Loc.InRange, Loc.at]
  have hvalue := read_byte_of_ordered_reuse hX hr.memReads
    (k := 0) (by exact Nat.zero_lt_succ 0) hwrite hcover
    (by simpa only [Loc.at, Nat.add_zero] using hv)
    (by simpa only [Loc.at, Nat.add_zero] using horder)
  simpa [wbyte, Loc.at] using hvalue

end
end PTX
