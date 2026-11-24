-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.LocalLoadSpace

@[expose] public section

namespace PTX.Flow

/-- A register-addressed local store exposes the exact successful element access. -/
theorem fires_localStoreAccess {l : Launch} {A : List Assumption} {g pc base width : Nat}
    {t : TState} {ma : MemAccess} {a : Acc} {bs : List Byte} {o : Option TState}
    (hSpace : ma.space = some .local) (hKind : ma.kind = .store)
    (hBase : ma.addr.base = .reg base width)
    (hFire : Fires pc (eventTmpl A l g t (.mem ma)) ⟨pc, .wr a bs⟩ o) :
    accessAcc l g t ma = .ok a := by
  rcases fires_write_tmpl hFire with ⟨u, hTmpl⟩ | ⟨u, hTmpl, _⟩
  swap
  · have h := memTmpl_isMem (A := A) (L := l) (g := g) (t := t) (a := ma)
    simp only [eventTmpl] at hTmpl
    rw [hTmpl] at h
    exact h.elim
  have hDirect : ma.locSpace? = none := by simp [MemAccess.locSpace?, hSpace]
  change memTmpl A l g t ma = .write a bs u at hTmpl
  simp only [memTmpl, hDirect, hBase] at hTmpl
  split at hTmpl
  · contradiction
  · exact (atomTmpl_noWrite hTmpl).elim
  · split at hTmpl
    swap
    · cases hTmpl
    simp only [accessTmpl, hKind] at hTmpl
    cases ha : accessAcc l g t ma with
    | error f => simp [ha] at hTmpl
    | ok acc =>
      simp only [ha] at hTmpl
      split at hTmpl
      · cases hTmpl
      · split at hTmpl
        · cases hTmpl
        · obtain ⟨rfl, _, _⟩ := Tmpl.write.inj hTmpl
          rfl

/-- A store whose instruction explicitly names a register-based local address writes its
issuing thread's local memory. Its access uses the local-address rule, including stack offsets. -/
theorem fires_localStore {l : Launch} {A : List Assumption} {g pc base width : Nat}
    {t : TState} {ma : MemAccess} {a : Acc} {bs : List Byte} {o : Option TState}
    (hSpace : ma.space = some .local) (hKind : ma.kind = .store)
    (hBase : ma.addr.base = .reg base width)
    (hFire : Fires pc (eventTmpl A l g t (.mem ma)) ⟨pc, .wr a bs⟩ o) :
    a.loc.space = .local ∧ a.loc.cta = g :=
  accessAcc_explicitLocal hSpace hBase (fires_localStoreAccess hSpace hKind hBase hFire)

end PTX.Flow
