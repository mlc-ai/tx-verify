-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.LandsU
public import Lemmas.Flow.Next

@[expose] public section

/-! # A shuffle in a UB-tolerant control machine

`Code.step_shflU`: a shuffle into register `r` with validity predicate `p`, neither named by the
facts, whose machine successor `nv recv ok` is a function of the received value and its validity
(never a fault). A pending stop is followed as such; a continuing successor is reached by a
segment from the facts with the two destinations. `Code.shflAnyU` is the case of a successor that
does not depend on the received word (a data shuffle). -/

namespace PTX.Flow.Code
open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- A shuffle whose successor is a function of the received word and its validity. -/
theorem step_shflU {d : C.D} {nv : Value → Bool → Option (Option C.D)} {mode : ShflMode}
    {ty : Option DType} {r p : Nat} {a b c mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨none, .warp ⟨.shfl mode, ty, [some r, some p], [a, b, c],
      some mask⟩⟩)
    (hr : ∀ q ∈ C.facts d, q.1 ≠ r) (hp : ∀ q ∈ C.facts d, q.1 ≠ p) (hrp : r ≠ p)
    (hn : ∀ m av bv cv recv ok, C.next d ⟨C.pc d, .shfl m av bv cv recv ok⟩ = nv recv ok)
    (hs : C.sub d = 0) (ha : C.acc d = []) (hnn : ∀ recv ok, nv recv ok ≠ none)
    (hl : ∀ recv ok d', nv recv ok = some (some d') → C.sub d' = 0 ∧ C.acc d' = [] ∧
      C.inv d' ∧ SegU K A L g (C.pc d + 1) ((p, .pred ok) :: (r, recv) :: C.facts d)
        (C.pc d') (C.facts d')) : C.StepAtU d where
  site := fun _ => ⟨_, hc0, rfl, trivial⟩
  step := by
    intro t e u ins h _ hc hf
    obtain rfl := Option.some.inj (hc.symm.trans hc0)
    have h0 := at_of_atD h hs ha
    obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := some p) hf
    have h1 : At (setReg t r recv) (C.pc d) ((r, recv) :: C.facts d) :=
      ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1, Function.update_self .., holds_update h0.2.2.2.2 hr⟩
    have hp' : ∀ q ∈ (r, recv) :: C.facts d, q.1 ≠ p := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hrp
      · exact hp q hq
    have hu := At.set (v := .pred ok) h1 hp'
    rw [hn]
    rcases hv : nv recv ok with _ | _ | d'
    · exact absurd hv (hnn recv ok)
    · exact .inl (.inl rfl)
    · obtain ⟨hs', ha', hi, seg⟩ := hl recv ok d' hv
      obtain ⟨s, hl', hs''⟩ := landsU hu seg hi hs' ha'
      exact .inl (.inr ⟨d', s, rfl, hl', hs''⟩)

/-- A data shuffle: any received word goes on to `dn` by a segment. -/
theorem shflAnyU {d dn : C.D} {mode : ShflMode} {ty : Option DType} {r p : Nat}
    {a b c mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨none, .warp ⟨.shfl mode, ty, [some r, some p], [a, b, c],
      some mask⟩⟩)
    (hr : ∀ q ∈ C.facts d, q.1 ≠ r) (hp : ∀ q ∈ C.facts d, q.1 ≠ p) (hrp : r ≠ p)
    (hn : ∀ e, C.next d e = some (some dn)) (hs : C.sub d = 0) (ha : C.acc d = [])
    (hs' : C.sub dn = 0) (ha' : C.acc dn = []) (hi : C.inv dn)
    (seg : ∀ recv ok, SegU K A L g (C.pc d + 1) ((p, .pred ok) :: (r, recv) :: C.facts d)
      (C.pc dn) (C.facts dn)) : C.StepAtU d :=
  step_shflU (nv := fun _ _ => some (some dn)) hc0 hr hp hrp (fun _ _ _ _ _ _ => hn _) hs ha
    (fun _ _ => by simp) (fun recv ok d' h => by
      obtain rfl := Option.some.inj (Option.some.inj h)
      exact ⟨hs', ha', hi, seg recv ok⟩)

end PTX.Flow.Code
