-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderActiveDrain

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow

noncomputable section

/-- Each parsed use has an actual successful gate. Their event indices increase with
the cursor, even when other events occur between packet publications. -/
theorem PacketsBeforeDrain.indexedGates {l : Launch} {g start final : Nat} {es : List Event}
    (h : PacketsBeforeDrain l g start final es) :
    ∃ (index : Nat → Nat) (site : Nat → Fin 4),
      (∀ use, start ≤ use → use < final →
        es[index use]? = some (cursorPoll l g use (site use) true)) ∧
      ∀ u v, start ≤ u → u < v → v < final → index u < index v := by
  induction h with
  | done use =>
    exact ⟨fun _ => 0, fun _ => 0, by intros; omega, by intros; omega⟩
  | @gap use fin pre post hQuiet hTail ih =>
    obtain ⟨index, site, hAt, hLt⟩ := ih
    refine ⟨fun u => pre.length + index u, site, ?_, ?_⟩
    · intro u hLo hHi
      rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      exact hAt u hLo hHi
    · intro u v hLo hBefore hHi
      exact Nat.add_lt_add_left (hLt u v hLo hBefore hHi) _
  | @packet use fin n current mid tail hQuiet hTail ih =>
    obtain ⟨next, picks, hAt, hLt⟩ := ih
    let head := List.replicate n (cursorPoll l g use current false) ++
      [cursorPoll l g use current true] ++ mid ++ [cursorArrival l g use current]
    let index := fun u => if u = use then n else head.length + next u
    let site := fun u => if u = use then current else picks u
    refine ⟨index,site,?_,?_⟩
    · intro u hLo hHi
      by_cases hSame : u = use
      · subst u
        simp only [index,site,ite_true]
        rw [List.append_assoc, List.getElem?_append_right (by simp),
          List.length_replicate, Nat.sub_self]
        rfl
      · have he : List.replicate n (cursorPoll l g use current false) ++
            cursorPoll l g use current true :: mid ++ cursorArrival l g use current :: tail =
            head ++ tail := by
          simp [head, List.append_assoc]
        rw [he]
        simp only [index,site,ite_eq_right hSame]
        rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
        exact hAt u (by omega) hHi
    · intro u v hLo hBefore hHi
      have hNe : v ≠ use := by omega
      by_cases he : u = use
      · simp only [index,ite_eq_right hNe,ite_eq_left he]
        have hLen : n < head.length := by simp [head]
        omega
      · simp only [index,ite_eq_right hNe,ite_eq_right he]
        exact Nat.add_lt_add_left (hLt u v (by omega) hBefore hHi) _

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
