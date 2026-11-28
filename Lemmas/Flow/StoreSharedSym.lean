-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SharedSymOk
import Lemmas.Flow.MemTmpl

@[expose] public section

/-! # A weak store to a shared symbol at an aligned address is not undefined behaviour

A proof tool, generic over the kernel: the template of a weak store to a shared variable
(`st.shared [sym + off]`, THREAD-ACCESS) of a source operand that reads as a value of the element's
size is not undefined behaviour when the access is not global-only and its wrapped address is a
multiple of the whole access. The store counterpart of `ldSharedSym_ok`. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat}

theorem stSharedSym_ok {t : TState} {m : MemAccess} {o : Nat} {w : SharedWindow} {os : Opnd}
    (hk : m.kind = .store) (hsem : m.sem = .weak) (hsp : m.space = some (.shared w))
    (hb : m.addr.base = .sharedSym o) (hnc : m.nc = false)
    (hrule : m.rule = some .threadAccess) (hloc : m.locSpace? = none)
    (hglob : (m.hints.globalOnly || m.vec == 8 || (m.vec == 4 && m.elem.width == 64)) = false)
    (hw : m.elem.width / 8 ≠ 0)
    (hal : wrapAddr 32 (BitVec.ofNat 64 (L.sharedBase + o)) m.addr.off %
      (m.elem.width / 8 * m.vec) = 0)
    (hsrc : m.srcs[t.sub]? = some os)
    (hv : ∃ v, readValue L g t m.elem.width os = .ok v ∧ v.bytes = m.elem.width / 8)
    (f : Fault) : eventTmpl A L g t (.mem m) ≠ .ub f := by
  obtain ⟨v, hv, hby⟩ := hv
  simp only [eventTmpl]
  unfold memTmpl
  rw [hrule, hloc]
  simp only [ite_true]
  unfold accessTmpl
  rw [hk, accessAcc_of_weak hsem]
  simp only [accessLoc, hsp, hb, hnc, bind, Except.bind, pure, Except.pure, elemAcc]
  simp only [Bool.false_or, hglob, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hw, hal,
    ne_eq, not_true_eq_false, or_self, hsrc, hv, storeValue_of_bytes hby]
  intro h
  cases h

end
end PTX.Flow
