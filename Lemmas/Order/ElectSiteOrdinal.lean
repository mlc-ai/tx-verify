-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.ElectOrdinal

@[expose] public section

namespace PTX.ElectOrd
open PTX PTX.Flow

/-- Count only elections whose decoded site belongs to the selected subset. -/
def atSites (sites : Nat → Bool) (event : Event) : Bool :=
  isElectEv event && sites event.pc

def siteOrdinal (sites : Nat → Bool) (X : Execution) (g index : Nat) : Nat :=
  ((X.tr g).take index).countP (atSites sites)

private theorem siteOrdinal_succ (sites : Nat → Bool) {X : Execution}
    {g index pc mask inst leader : Nat} (he : X.Elect (g, index) pc mask inst leader)
    (hSite : sites pc = true) :
    siteOrdinal sites X g (index + 1) = siteOrdinal sites X g index + 1 := by
  change (X.tr g)[index]? = some ⟨pc, .elect mask inst leader⟩ at he
  simp [siteOrdinal, List.take_add_one, he, List.countP_append, atSites, isElectEv, hSite]

private theorem siteOrdinal_le {L : Launch} {K : Kernel} {A : List Assumption}
    {m : Mem0} {X : Execution} (hX : Consistent L K A m X)
    (sites : Nat → Bool) {g h : Nat} (hs : SameWarp L h g)
    (hm : ∀ j pc mask inst leader, sites pc = true →
      X.Elect (h, j) pc mask inst leader → electMember mask (laneOf L g)) :
    ∀ n y x, Partner X (h, y) (g, x) → siteOrdinal sites X h y = n →
      n ≤ siteOrdinal sites X g x := by
  intro n
  induction n with
  | zero => intros; omega
  | succ n ih =>
    intro y x hPeer hn
    obtain ⟨y', hEarlier, event, he, hSelected, hPrev⟩ :=
      Flow.exists_nth (atSites sites) (X.tr h) (n := n) (k := y) (by
        change ((X.tr h).take y).countP (atSites sites) = n + 1 at hn
        omega)
    obtain ⟨pc, mask, inst, leader, rfl⟩ :
        ∃ pc mask inst leader, event = ⟨pc, .elect mask inst leader⟩ := by
      obtain ⟨pc, kind⟩ := event
      cases kind <;> simp_all [atSites, isElectEv]
    have hSite : sites pc = true := by simpa [atSites, isElectEv] using hSelected
    have hElection : X.Elect (h, y') pc mask inst leader := he
    obtain ⟨x', hPeer'⟩ := partner hX hs hElection (hm _ _ _ _ _ hSite hElection)
    have hBound := ih y' x' hPeer' hPrev
    have hOrder := mono hX hs hPeer' hPeer hEarlier
    obtain ⟨pc₁, pc₂, mask₁, mask₂, inst₁, lead₁, lead₂, hp₁, hp₂⟩ := hPeer'
    have hSame : pc₁ = pc := by
      have hEqual : X.get (h, y') = some ⟨pc₁, .elect mask₁ inst₁ lead₁⟩ := hp₁
      exact congrArg Event.pc (Option.some.inj (hEqual.symm.trans he))
    obtain ⟨hPc, _, _, _⟩ := hX.elect.2.1 _ _ _ _ _ _ _ _ _ hp₁ hp₂ hs
    have hAdvance := siteOrdinal_succ sites hp₂ (by rwa [← hPc, hSame])
    have hMono := Flow.countP_take_mono (atSites sites) (X.tr g)
      (show x' + 1 ≤ x by omega)
    change siteOrdinal sites X g (x' + 1) ≤ siteOrdinal sites X g x at hMono
    omega

/-- Partner elections have the same ordinal in any common restriction by site, including
one chosen release site. Only the selected earlier elections need mutually naming masks. -/
theorem siteOrdinal_eq {L : Launch} {K : Kernel} {A : List Assumption}
    {m : Mem0} {X : Execution} (hX : Consistent L K A m X)
    (sites : Nat → Bool) {g h y x : Nat} (hs : SameWarp L h g)
    (hmh : ∀ j pc mask inst leader, sites pc = true →
      X.Elect (h, j) pc mask inst leader → electMember mask (laneOf L g))
    (hmg : ∀ j pc mask inst leader, sites pc = true →
      X.Elect (g, j) pc mask inst leader → electMember mask (laneOf L h))
    (hPeer : Partner X (h, y) (g, x)) : siteOrdinal sites X h y = siteOrdinal sites X g x :=
  Nat.le_antisymm (siteOrdinal_le hX sites hs hmh _ _ _ hPeer rfl)
    (siteOrdinal_le hX sites (sameWarp_symm hs) hmg _ _ _ hPeer.symm rfl)

end PTX.ElectOrd
