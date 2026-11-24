-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingControlRegions
import Lemmas.Flow.WriteSpace

@[expose] public section

/-! # Concrete store footprints independent of the stored values -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow

private theorem element_extent {base : Loc} {n count j : Nat} {a : Acc}
    (h : elemAcc base n count j = .ok a) (hj : j < count) :
    a.loc.space = base.space ∧ a.loc.cta = base.cta ∧ base.addr ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ base.addr + n * count := by
  unfold elemAcc at h
  split at h
  · cases h
  · obtain rfl := Except.ok.inj h
    have hj' : n * (j + 1) ≤ n * count := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hj)
    simp only [Loc.at, Nat.mul_add, Nat.mul_one] at hj' ⊢
    exact ⟨trivial, trivial, by omega, by omega⟩

/-- The actual direct store writes a specific element of its declared source vector. -/
theorem direct_store_element {L : Launch} {g pc width reg : Nat} {t : TState} {space : Space}
    {off : Int} {srcs : List Opnd} {base : Loc} {a : Acc} {bytes : List Byte} {o : Option TState}
    (hAddr : effAddr L g t space reg off = .ok base)
    (hf : Fires pc (storeTmpl L g t space width reg off srcs) ⟨pc, .wr a bytes⟩ o) :
    t.sub < srcs.length ∧ a.loc = base.at ((width / 8) * t.sub) ∧ a.size = width / 8 := by
  unfold storeTmpl at hf
  simp only [hAddr, bind, Except.bind] at hf
  split at hf
  · cases hf.1
  · rename_i fp hElem
    split at hf
    · cases hf.1
    · rename_i value hValue
      split at hf
      · cases hf.1
      · have ha := (Kind.wr.inj (congrArg Event.kind hf.1)).1
        subst a
        have hSub := (List.getElem?_eq_some_iff.mp hValue).1
        unfold elemAcc at hElem
        split at hElem
        · cases hElem
        · obtain rfl := Except.ok.inj hElem
          exact ⟨hSub, rfl, rfl⟩

/-- A concrete direct store touches only the declared byte range of its source vector. -/
theorem direct_store_extent {L : Launch} {g pc width reg : Nat} {t : TState} {space : Space}
    {off : Int} {srcs : List Opnd} {base : Loc} {a : Acc} {bytes : List Byte} {o : Option TState}
    (hAddr : effAddr L g t space reg off = .ok base)
    (hf : Fires pc (storeTmpl L g t space width reg off srcs) ⟨pc, .wr a bytes⟩ o) :
    a.loc.space = base.space ∧ base.addr ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ base.addr + (width / 8) * srcs.length := by
  obtain ⟨hSub, hLoc, hSize⟩ := direct_store_element hAddr hf
  have hEnd := Nat.mul_le_mul_left (width / 8) (Nat.succ_le_of_lt hSub)
  rw [hLoc, hSize]
  simp only [Loc.at, Nat.mul_succ] at hEnd ⊢
  exact ⟨trivial, by omega, by omega⟩

/-- A weak generic store also stays within the declared vector range. -/
theorem generic_store_extent {L : Launch} {g pc : Nat} {t : TState} {m : MemAccess}
    {base : Loc} {a : Acc} {bytes : List Byte} {o : Option TState}
    (hKind : m.kind = .store) (hWeak : m.sem = .weak)
    (hLen : m.srcs.length = m.vec)
    (hAddr : accessLoc L g t m = .ok base)
    (hf : Fires pc (accessTmpl Assumptions.all L g t m) ⟨pc, .wr a bytes⟩ o) :
    a.loc.space = base.space ∧ a.loc.cta = base.cta ∧ base.addr ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ base.addr + (m.elem.width / 8) * m.vec := by
  unfold accessTmpl at hf
  rw [hKind, accessAcc_of_weak hWeak] at hf
  simp only [hAddr, bind, Except.bind] at hf
  split at hf
  · cases hf.1
  · rename_i fp hAcc
    have hElem : elemAcc base (m.elem.width / 8) m.vec t.sub = .ok fp := by
      split at hAcc
      · cases hAcc
      · exact hAcc
    split at hf
    · cases hf.1
    · rename_i value hValue
      split at hf
      · cases hf.1
      · have ha := (Kind.wr.inj (congrArg Event.kind hf.1)).1
        subst a
        apply element_extent hElem
        rw [← hLen]
        exact (List.getElem?_eq_some_iff.mp hValue).1

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
