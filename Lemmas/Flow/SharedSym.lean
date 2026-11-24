-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.MemTmpl

@[expose] public section

/-! # A 32-bit load from a shared symbol

A proof tool, generic over the kernel (promoted from Inkling's `Proof2/Lib/SharedSym.lean`, whose
source is the old tree's `EvWBase`).
Element `t.sub` of a 32-bit weak load from `global_smem + o + off` reads four bytes at that
address plus `4 t.sub` (`fires_ldv_sharedSym`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t u : TState} {pc : Nat} {e : Event}

theorem memTmpl_sharedSym {a : MemAccess} {o : Nat}
    (hr : a.rule = some .threadAccess) (hb : a.addr.base = .sharedSym o) :
    memTmpl A L g t a = accessTmpl A L g t a := by
  unfold memTmpl
  rw [hr, hb]
  split <;> simp_all

/-- **A vector load from a shared symbol.** Element `t.sub` of a 32-bit weak load from
`global_smem + o + off` reads four bytes at that address plus `4 t.sub`, as element `t.sub` of
the vector. -/
theorem fires_ldv_sharedSym {a : MemAccess} {o off : Nat}
    (hr : a.rule = some .threadAccess) (hb : a.addr.base = .sharedSym o)
    (ho : a.addr.off = (off : Int)) (hk : a.kind = .load) (hnc : a.nc = false)
    (hsp : a.space = some (.shared .cta)) (hsem : a.sem = .weak)
    (hglob : (a.nc || a.hints.globalOnly || a.vec == 8 ||
      (a.vec == 4 && a.elem.width == 64)) = false)
    (hw : a.elem.width = 32) (hb32 : L.sharedBase + o + off < 2 ^ 32)
    (hf : Fires pc (eventTmpl A L g t (.mem a)) e (some u)) :
    ∃ ac bs, e = ⟨pc, .rd ac bs⟩ ∧
      ac.loc = ⟨.shared, g / L.block, L.sharedBase + o + off + 4 * t.sub⟩ ∧
      ac.size = 4 ∧ ac.elem = t.sub := by
  simp only [eventTmpl, memTmpl_sharedSym hr hb, accessTmpl, hk, hnc] at hf
  rw [accessAcc_of_weak hsem] at hf
  simp only [accessLoc, hsp, hb, pure, Except.pure, bind, Except.bind, hglob, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte] at hf
  split at hf
  · simp [Fires] at hf
  · rename_i ac hE
    simp only [Fires] at hf
    obtain ⟨bs, -, he, -⟩ := hf
    refine ⟨ac, bs, he, ?_⟩
    unfold elemAcc at hE
    split_ifs at hE
    cases hE
    refine ⟨?_, by simp [hw], rfl⟩
    simp only [Loc.at, wrapAddr, ho, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
      BitVec.toNat_ofInt]
    have ho' : ((off : Int) % ((2 ^ 64 : Nat) : Int)).toNat = off := by
      rw [Int.emod_eq_of_lt (by omega) (by omega)]; simp
    simp only [ho', hw]
    simp only [Nat.mod_eq_of_lt (show L.sharedBase + o < 2 ^ 64 by omega)]
    rw [Nat.mod_eq_of_lt (show L.sharedBase + o + off < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt hb32, Nat.mod_eq_of_lt (show L.sharedBase + o + off < 2 ^ 64 by omega)]

end
end PTX.Flow
