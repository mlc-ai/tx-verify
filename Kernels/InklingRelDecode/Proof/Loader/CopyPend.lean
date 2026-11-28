-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.ElectBalance
import Kernels.InklingRelDecode.Proof.Loader.RefNext

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow

/-- Whether an event is a tensor copy issue. -/
def tensorEv (e : Event) : Bool := match e.kind with | .tensorIssue .. => true | _ => false

/-- Whether an event is an election won by `lane`. -/
def winnerEv (lane : Nat) (e : Event) : Bool :=
  match e.kind with | .elect _ _ lead => lead == lane | _ => false

def Site.isCopy : Site → Bool | .copy .. => true | _ => false

/-- Copies still owed to the election the lane has won. -/
def Site.pend : Site → Nat | .copy _ false => 2 | .copy _ true => 1 | _ => 0

theorem winner_off (l : Nat) (e : Event) (h : isElectEv e = false) :
    winnerEv l e = false := by
  obtain ⟨p,k⟩ := e
  cases k <;> first | rfl | exact absurd h (by simp [isElectEv])

private theorem finish_pend (d : D) (p : Fin 4) : (finishPair d p).site.pend = 0 := by
  fin_cases p <;> try rfl
  change (if _ then Site.endBar else .poll).pend = 0
  split <;> rfl

/-- Each won election owes two copies, one per issue. -/
theorem pend_next {L g d dn ev} (hn : next L g d ev = some (some dn))
    (el : (¬ ∃ p, d.site = .elect p) → isElectEv ev = false)
    (tn : d.site.isCopy = true → tensorEv ev = true)
    (nt : d.site.isCopy = false → tensorEv ev = false) :
    (tensorEv ev).toNat + dn.site.pend =
      d.site.pend + 2 * (winnerEv (laneOf L g) ev).toNat := by
  obtain ⟨s,i,n,a,b⟩ := d
  by_cases ise : ∃ p, s = .elect p
  · obtain ⟨p,rfl⟩ := ise
    obtain ⟨pc,k⟩ := ev
    cases k with
    | elect mask inst lead =>
      simp only [next] at hn
      split at hn
      · rename_i hl
        cases hn
        simp [tensorEv, winnerEv, Site.pend, ← hl]
      · rename_i hl
        cases hn
        rw [finish_pend]
        simp [tensorEv, winnerEv, Site.pend, Ne.symm hl]
    | _ => cases hn
  · have noel := winner_off (laneOf L g) ev (el ise)
    rw [noel]
    by_cases hc : s.isCopy = true
    · have t1 := tn hc
      obtain ⟨p,u,rfl⟩ : ∃ p u, s = .copy p u := by
        cases s <;> first | exact ⟨_,_,rfl⟩ | exact absurd hc (by simp [Site.isCopy])
      rw [t1]
      cases u <;> cases hn
      · rfl
      · rw [finish_pend]; rfl
    · have hc' : s.isCopy = false := by simpa using hc
      rw [nt hc']
      have z : s.pend = 0 := by
        cases s <;> first | rfl | exact absurd hc' (by simp [Site.isCopy])
      rw [z]
      cases s with
      | copy => simp [Site.isCopy] at hc'
      | elect p => exact (ise ⟨p,rfl⟩).elim
      | poll =>
        simp only [next] at hn
        split at hn <;> try contradiction
        split at hn <;> cases hn <;> rfl
      | first | second => obtain ⟨_,_,_,_,_,rfl⟩ := read_next hn; rfl
      | page u => cases u <;> obtain ⟨_,_,_,_,_,rfl⟩ := read_next hn <;> rfl
      | beginBar | readyBar =>
        simp only [next] at hn; split at hn <;> cases hn <;> rfl
      | dispatch => cases hn
      | _ => cases hn; rfl

/-- A site at a tensor-load position is one of the eight copies. -/
theorem site_of_copyPc (s : Site) (h : s.pc ∈ [2389,2391,2394,2396,2404,2406,2410,2412]) :
    ∃ p u, s = .copy p u := by
  cases s <;> first | exact ⟨_,_,rfl⟩ | (repeat' first | exact absurd h (by decide) |
    (rename_i j; revert j; decide +kernel))

theorem copy_place (p : Fin 4) (u : Bool) :
    owed (.copy p u) = 3 - p.val ∧ (Site.copy p u).pend = (if u then 1 else 2) ∧
      (Site.copy p u).pc = [2389,2394,2404,2410][p.val]! + (if u then 2 else 0) :=
  ⟨rfl, by cases u <;> rfl, rfl⟩

end PTX.Kernels.InklingRelDecode.Proof.Loader
