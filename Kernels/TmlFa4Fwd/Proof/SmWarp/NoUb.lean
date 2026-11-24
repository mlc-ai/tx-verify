-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.TmlFa4Fwd.Proof.Common.DataStop
import Kernels.TmlFa4Fwd.Proof.SmWarp.DataEvent

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Common.NoUb
import Kernels.TmlFa4Fwd.Proof.Common.NoUb0
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Lemmas.Kernel.NoUbFirstStop
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src
import Kernels.TmlFa4Fwd.Proof.Softmax.Fragment

@[expose] public section

/-! # No event of a softmax warp is undefined behaviour

`Frame.noUb_of_first_stop` for the lanes of warps 0 to 7 (`noUb`), followed with `Ref` by
`good` given the named premises `NumAll`, `DataStoreSafe` and `SmSrc`. `safe`: at a startup state
the startup's sites (`start_safe`, on warp 0 `start0_safe`); at a role state the fragment's shape
table has no undefined behaviour (`Softmax.shapeS`). `live`: the startup machine dies only on an
event of another kind than its site's; the fragment's machine only on an event that ends the
thread (`Softmax.ok`'s death clause in `ref_next`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {w : Nat}

/-- **No event of a lane of a softmax warp is undefined behaviour.** -/
theorem noUb (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hN : NumAll p L)
    (hD : ∀ g, DataStoreSafe p L g) (hS : SmSrc p L X) (hw8 : w < 8) {g : Nat}
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (f : Fault) : e.kind ≠ .ub f := by
  have followed := good hp hX hw8 hg hw
  have safe : ∀ i σ v, X.get (g,i) = some v →
      Frame.stateAt (threadD p L) X g i = some (some σ) → ∀ f, v.kind ≠ .ub f := by
    intro i ⟨σ,n⟩ v hi hs f
    have hc := control_of_data hp hs
    have hR := (followed i).2 _ hc
    cases σ with
    | inl s =>
      have h1 : StartW L w s n := hR.1
      unfold StartW at h1
      split at h1
      · exact start0_safe hp hX hi hc h1 f
      · exact start_safe hp hX hi hc h1 f
    | inr a =>
      obtain ⟨i,d⟩ := a
      cases i with
      | softmax => exact (data_event hp hX (hD g) hi hs).1.2 f
      | _ => exact hR.elim
  refine Frame.noUb_of_first_stop (C := threadD p L) hX safe ?_ he f
  intro i ⟨σ,n⟩ v hi hs _ loss
  have hc := control_of_data hp hs
  have hR := (followed i).2 _ hc
  have hu := safe i _ v hi hs
  cases σ with
  | inl s =>
    have hn := Frame.next_none_of_stop hi hc (data_start_stop loss) (followed (i+1)).1
    have h1 : StartW L w s n := hR.1
    unfold StartW at h1
    split at h1
    · exact start0_live hp hX hi hc h1 hu hn
    · exact start_live hp hX hi hc h1 hn
  | inr a =>
    obtain ⟨i',d⟩ := a
    cases i' with
    | softmax =>
      obtain ⟨⟨c,hJ,_⟩,_⟩ := hR.2 (ub_zero hX hi hc)
      have hRef := data_ref hJ
      obtain ⟨hev, hinv, hw', _⟩ := data_event hp hX (hD g) hi hs
      obtain ⟨hn, hend, _⟩ := (Softmax.ok hp hg hw' (hN g hg hw') (hD g) (d,c)).ref_next
        (e := v) hinv hRef (hS g i d n c v hi hs hRef) hev
      have stop := data_role_stop loss
      change (codeT p L g).next d v = none ∨ (codeT p L g).next d v = some none at stop
      rw [next_eq hN] at stop
      rcases stop with hd | hd
      · rcases hend (Code.counted_next_eq_none_iff.mpr hd) with ⟨f,hf⟩ | hx
        · exact (hu f hf).elim
        · exact hx
      · exact (hn (Code.counted_next_none_iff.mpr hd)).elim
    | _ => exact hR.elim

/-- **A softmax lane's data machine is alive** up to a position, once its bias and score loads
    before
it returned what the machine follows. -/
theorem alive (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hN : NumAll p L)
    (hD : ∀ g, DataStoreSafe p L g) (hw8 : w < 8) {g : Nat}
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) {K : Nat}
    (hS : ∀ i < K, ∀ d n c e, X.get (g, i) = some e →
      Frame.stateAt (threadD p L) X g i = some (some (.inr ⟨.softmax,d⟩,n)) →
      Softmax.Ref p L g (d, c) → ExpectD p L g d e) :
    ∀ k ≤ K, k < (X.tr g).length → ∃ σ, Frame.stateAt (threadD p L) X g k = some (some σ) := by
  have followed := good hp hX hw8 hg hw
  intro k
  induction k with
  | zero => intro _ _; exact ⟨_, Frame.stateAt_zero⟩
  | succ k ih =>
    intro hkK hlen
    obtain ⟨⟨σ, n⟩, hs⟩ := ih (by omega) (by omega)
    obtain ⟨v, hi⟩ : ∃ v, X.get (g, k) = some v :=
      ⟨_, List.getElem?_eq_getElem (show k < (X.tr g).length by omega)⟩
    by_contra hno
    have loss : (threadD p L g).next (σ, n) v = none ∨
        (threadD p L g).next (σ, n) v = some none := by
      have hst := Frame.stateAt_succ (C := threadD p L) (show (X.tr g)[k]? = some v from hi)
      rw [hs] at hst
      rcases h : (threadD p L g).next (σ, n) v with _ | _ | b
      · exact .inl rfl
      · exact .inr rfl
      · exact (hno ⟨b, hst.trans h⟩).elim
    have hx : v.kind = .exit := by
      have hc := control_of_data hp hs
      have hR := (followed k).2 _ hc
      cases σ with
      | inl s =>
        have hn := Frame.next_none_of_stop hi hc (data_start_stop loss) (followed (k+1)).1
        have h1 : StartW L w s n := hR.1
        have hu : ∀ f, v.kind ≠ .ub f := by
          intro f
          unfold StartW at h1
          split at h1
          · exact start0_safe hp hX hi hc h1 f
          · exact start_safe hp hX hi hc h1 f
        unfold StartW at h1
        split at h1
        · exact start0_live hp hX hi hc h1 hu hn
        · exact start_live hp hX hi hc h1 hn
      | inr a =>
        obtain ⟨i',d⟩ := a
        cases i' with
        | softmax =>
          obtain ⟨⟨c,hJ,_⟩,_⟩ := hR.2 (ub_zero hX hi hc)
          have hRef := data_ref hJ
          obtain ⟨hev, hinv, hw', _⟩ := data_event hp hX (hD g) hi hs
          obtain ⟨hn, hend, _⟩ := (Softmax.ok hp hg hw' (hN g hg hw') (hD g) (d,c)).ref_next
            (e := v) hinv hRef (hS k (by omega) d n c v hi hs hRef) hev
          have stop := data_role_stop loss
          change (codeT p L g).next d v = none ∨ (codeT p L g).next d v = some none at stop
          rw [next_eq hN] at stop
          rcases stop with hd | hd
          · rcases hend (Code.counted_next_eq_none_iff.mpr hd) with ⟨f,hf⟩ | hx
            · exact (hev.2 f hf).elim
            · exact hx
          · exact (hn (Code.counted_next_none_iff.mpr hd)).elim
        | _ => exact hR.elim
    obtain ⟨pc, kd⟩ := v
    simp only at hx
    subst hx
    obtain ⟨r, hr⟩ := hX.thr g hg
    have := Flow.Run.end_last hr hi (.inr rfl)
    omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
