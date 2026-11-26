-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.GenericShared

@[expose] public section

/-! # A weak load from a shared symbol at an aligned address is not undefined behaviour

A proof tool, generic over the kernel: the template of a weak load of a shared variable
(`ld.shared [sym + off]`, THREAD-ACCESS) is not undefined behaviour when the access is not
global-only and its wrapped address is a multiple of the access size. The converse of
`fires_sym_rd_at`'s undefined-behaviour alternative. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat}

theorem ldSharedSym_ok {t : TState} {m : MemAccess} {o : Nat} {w : SharedWindow}
    (hk : m.kind = .load) (hsem : m.sem = .weak) (hsp : m.space = some (.shared w))
    (hb : m.addr.base = .sharedSym o) (hnc : m.nc = false)
    (hrule : m.rule = some .threadAccess) (hloc : m.locSpace? = none)
    (hglob : (m.hints.globalOnly || m.vec == 8 || (m.vec == 4 && m.elem.width == 64)) = false)
    (hw : m.elem.width / 8 ≠ 0)
    (hal : wrapAddr 32 (BitVec.ofNat 64 (L.sharedBase + o)) m.addr.off %
      (m.elem.width / 8 * m.vec) = 0) (f : Fault) :
    eventTmpl A L g t (.mem m) ≠ .ub f := by
  simp only [eventTmpl]
  unfold memTmpl
  rw [hrule, hloc]
  simp only [ite_true]
  unfold accessTmpl
  rw [hk, accessAcc_of_weak hsem]
  simp only [accessLoc, hsp, hb, hnc, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure,
    Except.pure, elemAcc]
  simp only [Bool.false_or, hglob, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hw, hal,
    ne_eq, not_true_eq_false, or_self]
  intro h
  cases h

end
end PTX.Flow
