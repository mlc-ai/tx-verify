-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.Epi
public import Kernels.InklingRelDecode.Proof.Thread.ShapeWordsKeep

@[expose] public section

/-!
# The order of the sites around the early shared stores

The prologue's role-table store (`ProA.Site.st8`) is followed, in the machine, by the sites
`st9_0`, `st9_1` and `bar18`, and no other site leads to these three: `ProA.next_afterSt8` says
that a step into one of them comes from `st8` or from one of them. The epilogue's table store
(`Epi.Site.stTab`) is followed by `bar2`, `bar3`, `dealloc` and `exit`: `Epi.next_afterTab`. So a
default-partition state that is after the store has the store's state somewhere earlier in its
thread's run (`Interface.FootExist`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The prologue sites after the role-table store. -/
def Site.afterSt8 : Site → Bool
  | .st9_0 | .st9_1 | .bar18 => true
  | _ => false

theorem qSite_afterSt8 (L : Launch) (g : Nat) (dt : Dat) (n : Nat) :
    (qSite L g dt n).afterSt8 = false := by
  unfold qSite
  split <;> (repeat' split) <;> rfl

/-- **A step into the sites after the role-table store comes from the store or from them.** -/
theorem next_afterSt8 {L : Launch} {g : Nat} {s : Site} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨s, dt⟩ e = some (some d')) (hs : d'.site.afterSt8 = true) :
    s = .st8 ∨ s.afterSt8 = true := by
  cases s <;> first
    | (right; decide)
    | (left; rfl)
    | (simp only [next] at h
       repeat' split at h
       all_goals first
         | (cases h; done)
         | (simp only [Option.some.injEq] at h
            subst h
            first
              | (simp only [qSite_afterSt8] at hs; cases hs)))

end
end PTX.Kernels.InklingRelDecode.Proof.ProA

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The epilogue sites after the dispatch-table store. -/
def Site.afterTab : Site → Bool
  | .bar2 | .bar3 | .dealloc | .exit => true
  | _ => false

theorem stores_afterTab (d : D) : d.stores.afterTab = false := by
  unfold D.stores
  split_ifs <;> rfl

theorem stNext_afterTab (d : D) (k : Fin 64) : (stNext d k).site.afterTab = false := by
  unfold stNext
  split_ifs <;> rfl

theorem startSk_afterTab (p : Prm) : (D.startSk p).site.afterTab = false := by
  unfold D.startSk D.entry
  rfl

/-- **A step into the sites after the table store comes from the store or from them.** -/
theorem next_afterTab {d d' : D} {e : Event} (h : next d e = some (some d'))
    (hs : d'.site.afterTab = true) : d.site = .stTab ∨ d.site.afterTab = true := by
  obtain ⟨site, pr, o, sk⟩ := d
  cases site <;> first
    | (right; rfl)
    | (left; rfl)
    | (simp only [next] at h
       repeat' split at h
       all_goals first
         | (cases h; done)
         | (simp only [Option.some.injEq] at h
            subst h
            first
              | (simp [Site.afterTab] at hs; done)
              | (simp only [stores_afterTab, stNext_afterTab] at hs; cases hs)))

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
