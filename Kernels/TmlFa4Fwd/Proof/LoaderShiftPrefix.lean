-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRingPrefix
public import Kernels.TmlFa4Fwd.Proof.LoaderScratchParent
public import Kernels.TmlFa4Fwd.Proof.LoaderShiftPrelude

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

private theorem shiftCannotReenter :
    loaderBackEdges.all (fun (pc, target) => !(401 < pc && target ≤ 401)) = true := by decide

theorem noLaterShiftBranchVisits {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hp : 401 < s.pc) : loaderVisitsAt 401 vs = 0 := by
  have tailAbove {t u : TState} (hLo : 401 < t.pc) (hHi : t.pc < 1906)
      (h : Tau kernel Assumptions.all l g t u) : 401 < u.pc := by
    by_contra hn
    have hLe : u.pc ≤ 401 := by omega
    have hm := loaderTauBackEdge (by omega) hHi (by omega) h
    have hC := List.all_eq_true.mp shiftCannotReenter _ hm
    simp [hLo, hLe] at hC
  have evAbove {t u : TState} {e : Event} (hLo : 401 < t.pc) (hHi : t.pc < 1906)
      (h : EStep kernel Assumptions.all l g t e (some u)) : 401 < u.pc := by
    have hCore : EStep kernel [] l g t e (some u) := by
      obtain ⟨tmpl, hh, hf⟩ := h
      exact ⟨tmpl, by rwa [← loaderOutCore (by omega) hHi], hf⟩
    rcases (estep_return_pc hCore (fun _ _ _ h => execLocal_frame h)).2 with hs | hs <;> omega
  have prepend {t : TState} (h : 401 < t.pc) (e : Option Event) (tail : List Visit)
      (hTail : t.pc < 1906 → loaderVisitsAt 401 tail = 0) :
      loaderVisitsAt 401 (visit kernel l g t e :: tail) = 0 := by
    unfold loaderVisitsAt loaderVisits
    rw [List.takeWhile_cons, visit_pc]
    split
    · rename_i hh
      have hG : 174 ≤ t.pc ∧ t.pc < 1906 := of_decide_eq_true hh
      rw [List.countP_cons, visit_pc]
      have hNe : t.pc ≠ 401 := by omega
      simpa [loaderVisitsAt, loaderVisits, hNe] using hTail hG.2
    · rfl
  induction hw with
  | stop => rfl
  | tau ht hh ih =>
    exact prepend hp none _ (fun hi => ih (tailAbove hp hi ht))
  | ev he hh ih =>
    exact prepend hp (some _) _ (fun hi => ih (evAbove hp hi he))
  | last => exact prepend hp (some _) [] (fun _ => rfl)

end
end PTX.Kernels.TmlFa4Fwd.Loader
