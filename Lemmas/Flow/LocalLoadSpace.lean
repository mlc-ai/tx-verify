-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.AccessLocal
public import Lemmas.Protocol.LocalMemory

@[expose] public section

namespace PTX.Flow

/-- A register-addressed local load exposes the exact successful element access. -/
theorem fires_localLoadAccess {l : Launch} {A : List Assumption} {g pc base width : Nat}
    {t : TState} {ma : MemAccess} {a : Acc} {bs : List (Option Byte)} {o : Option TState}
    (hSpace : ma.space = some .local) (hKind : ma.kind = .load)
    (hBase : ma.addr.base = .reg base width)
    (hFire : Fires pc (eventTmpl A l g t (.mem ma)) ⟨pc, .rd a bs⟩ o) :
    accessAcc l g t ma = .ok a := by
  obtain ⟨k, hm⟩ := fires_read_tmpl hFire
  have hDirect : ma.locSpace? = none := by simp [MemAccess.locSpace?, hSpace]
  change memTmpl A l g t ma = .read a k at hm
  simp only [memTmpl, hDirect, hBase] at hm
  split at hm
  · contradiction
  · exact (atomTmpl_noRead hm).elim
  · split at hm
    swap
    · cases hm
    simp only [accessTmpl, hKind] at hm
    split at hm
    · cases hm
    · rename_i acc hAcc
      split at hm
      · split at hm <;> cases hm
      · obtain ⟨rfl, _⟩ := Tmpl.read.inj hm
        exact hAcc

/-- Local address resolution retains issuer identity, including nonzero vector elements. -/
theorem accessAcc_explicitLocal {l : Launch} {g base width : Nat} {t : TState}
    {ma : MemAccess} {a : Acc} (hSpace : ma.space = some .local)
    (hBase : ma.addr.base = .reg base width) (ha : accessAcc l g t ma = .ok a) :
    a.loc.space = .local ∧ a.loc.cta = g := by
  cases hr : readBits l g t width (.reg base) with
  | error f =>
    have hl : accessLoc l g t ma = .error f := by
      simp [accessLoc, hSpace, hBase, hr, bind, Except.bind]
    simp [accessAcc, hl, bind, Except.bind] at ha
  | ok v =>
    rw [accessAcc, accessLoc_local_reg hSpace hBase hr] at ha
    simp only [bind, Except.bind] at ha
    repeat' (first | split at ha | contradiction)
    cases he : elemAcc ⟨.local, g, wrapAddr width v ma.addr.off⟩
        (ma.elem.width / 8) ma.vec t.sub with
    | error f => simp [he] at ha
    | ok a' =>
      have hEq : ma.semAcc a' = a := by simpa [he] using ha
      rw [← hEq, semAcc_loc]
      exact elemAcc_local he

end PTX.Flow
