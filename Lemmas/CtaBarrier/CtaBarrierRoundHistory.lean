-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tmem.CtaPair
public import Lemmas.CtaBarrier.CtaBarrierRounds

@[expose] public section

section
namespace PTX

/-- In a valid cluster grid the CTA group of size one of a CTA holds only that CTA: two CTAs of one
cluster with one rank have the same `%ctaid`, and no two CTAs of a grid have one `%ctaid`. -/
theorem sameCtaGroup_one {L : Launch} (hL : L.clusterGridValid) {a b : Nat}
    (h : SameCtaGroup L .one a b) : a = b := by
  obtain ⟨⟨ha, hb, hcl⟩, hr⟩ := h
  obtain ⟨k, hk, hrk⟩ : ∃ k, k < CtaGroup.one.size ∧
      L.rankOfCta a / CtaGroup.one.size * CtaGroup.one.size + k = L.rankOfCta b := by
    simpa [Launch.ctaGroupRanks] using hr
  have hrank : L.rankOfCta b = L.rankOfCta a := by
    have hs : CtaGroup.one.size = 1 := rfl
    rw [hs, Nat.div_one, Nat.mul_one] at hrk
    omega
  refine hL.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a ha b hb ?_
  simp only [Launch.ctaidOf, Launch.placeOf, Launch.clusterCtaidOf, hcl, hrank]

end PTX
end

section
namespace PTX.CtaBarrier
variable {α : Type}

/-- Count actual collective arrivals, independently of source-event ordinals. -/
def isWarpArrival (warp : Nat) : Record α → Bool
  | .arrival _ w _ _ => w == warp
  | .exit _ _ => false

def arrivals (h : List (Record α)) (warp : Nat) : Nat := h.countP (isWarpArrival warp)

/-- A derived full-CTA protocol. Its premises concern actual checked history
prefixes and must be established from each program's control flow. -/
def FullRounds (rounds : Nat) (h : List (Record α)) : Prop :=
  ∀ xs r ys, h = xs ++ r :: ys → match r with
    | .arrival id warp count _ => id = 0 ∧ count = none ∧ arrivals xs warp < rounds
    | .exit g _ => arrivals xs (g / 32) = rounds

theorem FullRounds.prefix {rounds : Nat} {xs ys : List (Record α)}
    (h : FullRounds rounds (xs ++ ys)) : FullRounds rounds xs := by
  intro a r b hab
  exact h a r (b ++ ys) (by rw [hab]; simp only [List.append_assoc,List.cons_append])

/-- The invariant is derived by replaying actual resource updates. In particular,
`FullRounds` is not an extra execution axiom or a kernel launch precondition. -/
theorem FullRounds.run_state {block rounds : Nat} {h : List (Record α)} {s : State}
    (hp : FullRounds rounds h) (hb : 0 < block) (hr : run block {} h = .ok s) :
    RoundState block rounds (arrivals h) s := by
  classical
  induction h using List.reverseRecOn generalizing s with
  | nil =>
    cases hr
    exact RoundState.initial block rounds
  | @append_singleton xs r ih =>
    obtain ⟨u,hu⟩ := run_prefix hr
    have hs := ih hp.prefix hu
    have hf : r.perform block u = .ok s := by
      rw [run_append,hu] at hr
      cases hf : r.perform block u with
      | error err => simp [run,hf,Except.bind] at hr
      | ok v => simpa only [run,hf,Except.bind,Except.ok.injEq] using hr
    have hh := hp xs r [] (by simp)
    cases r with
    | arrival id warp count lanes =>
      obtain ⟨rfl,rfl,hc⟩ := hh
      simp only [Record.perform] at hf
      split_ifs at hf with hlanes
      · have heq : arrivals (xs ++ [Record.arrival 0 warp none lanes]) =
            increment (arrivals xs) warp := by
          funext w
          by_cases hw : w = warp
          · subst w; simp [arrivals,isWarpArrival,increment]
          · simp [arrivals,isWarpArrival,increment,hw,Ne.symm hw]
        rw [heq]
        exact hs.arrive hb hc hf
    | exit g e =>
      have heq : arrivals (xs ++ [Record.exit g e]) = arrivals xs := by
        funext w; simp [arrivals,isWarpArrival]
      rw [heq]
      exact hs.exit hb hh hf

/-- The generation read from a checked resource is exactly its pre-arrival count
under this protocol. Source-order correspondence is a separate proof obligation. -/
theorem FullRounds.generation {block rounds id phase : Nat} {h : List (Record α)} {e : α}
    (hp : FullRounds rounds h) (hb : 0 < block)
    (hg : GenerationOf block h e id phase) :
    ∃ i warp count lanes g s t,
      h[i]? = some (.arrival id warp count lanes) ∧ At block h i s ∧
      (g,e) ∈ lanes ∧ Record.perform block s (.arrival id warp count lanes) = .ok t ∧
      id = 0 ∧ count = none ∧ arrivals (h.take i) warp = phase := by
  obtain ⟨i,s,warp,count,lanes,g,hi,hs,he,hphase,t,ht⟩ := hg
  have hlt := (List.getElem?_eq_some_iff.mp hi).1
  have hdecomp : h = h.take i ++ (.arrival id warp count lanes) :: h.drop (i+1) := by
    rw [← (List.getElem?_eq_some_iff.mp hi).2]
    rw [← List.drop_eq_getElem_cons hlt]
    exact (List.take_append_drop i h).symm
  obtain ⟨hid,hcount,_⟩ := hp _ _ _ hdecomp
  have hpref : FullRounds rounds (h.take i) := by
    have hh := hp
    rw [hdecomp] at hh
    exact hh.prefix
  have hstate := hpref.run_state hb hs
  refine ⟨i,warp,count,lanes,g,s,t,hi,hs,he,ht,hid,hcount,?_⟩
  subst id; subst count
  simp only [Record.perform] at ht
  split_ifs at ht with hlanes
  · exact (hstate.arrival_generation ht).trans hphase

/-- Select a predicate occurrence by the number of earlier matching elements. -/
theorem countP_index {β : Type} {xs : List β} {p : β → Bool} {n : Nat}
    (hn : n < xs.countP p) :
    ∃ i x, xs[i]? = some x ∧ p x = true ∧ (xs.take i).countP p = n := by
  induction xs generalizing n with
  | nil => simp at hn
  | cons x xs ih =>
    by_cases hx : p x = true
    · cases n with
      | zero => exact ⟨0,x,rfl,hx,rfl⟩
      | succ n =>
        have hn' : n < xs.countP p := by simp only [List.countP_cons,hx,↓reduceIte] at hn; omega
        obtain ⟨i,y,hi,hy,hcount⟩ := ih hn'
        refine ⟨i+1,y,hi,hy,?_⟩
        simp [List.take_succ_cons,hx,hcount]
    · have hf : p x = false := by cases hh : p x <;> simp_all
      have hn' : n < xs.countP p := by simpa [List.countP_cons,hf] using hn
      obtain ⟨i,y,hi,hy,hcount⟩ := ih hn'
      refine ⟨i+1,y,hi,hy,?_⟩
      simp [List.take_succ_cons,hf,hcount]

end PTX.CtaBarrier
end
